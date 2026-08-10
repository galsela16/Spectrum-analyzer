// ==========================================
// גל אנלייזר — App Engine (Complete File)
// ==========================================

function safeAddListener(id, event, fn) {
  const el = document.getElementById(id);
  if (el) el.addEventListener(event, fn);
}

function escapeHtml(s){ return String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c])); }
function stamp(){ const d=new Date(); const p=n=>(''+n).padStart(2,'0'); return d.getFullYear()+p(d.getMonth()+1)+p(d.getDate())+'_'+p(d.getHours())+p(d.getMinutes())+p(d.getSeconds()); }
function download(name, blobUrl){ const a=document.createElement('a'); a.href=blobUrl; a.download=name; document.body.appendChild(a); a.click(); a.remove(); }
function prefSet(k, v){ localStorage.setItem(k, String(v)); }

// ---- Global State & Audio Setup ----
const FMIN=20, FMAX=20000;
let viewMin=20, viewMax=20000;
let curBpo=6;
let ISO=[], BANDS=0, R=1;
let peaks=[], avgBuf=[], snapCurve=null, lastV=[], lastBandDb=[], frozen=false;
let sunMode=false;

const cv = document.getElementById('cv');
const ctx = cv ? cv.getContext('2d') : null;
const dot = document.getElementById('dot');
const idle = document.getElementById('idle');
const errBox = document.getElementById('err');

let audioCtx, analyser, analyserRef=null, source, stream, raf;
let floatData, floatDataRef=null, timeData, timeDataRef=null;
let fftSize=16384;
let running=false, calib=0, floorDb=-85, ceilDb=-15;

const GEQ=[20,25,31.5,40,50,63,80,100,125,160,200,250,315,400,500,630,800,1000,
           1250,1600,2000,2500,3150,4000,5000,6300,8000,10000,12500,16000,20000];

// ---- TF & DSP Variables ----
let tfDelayMs = 0, tfDelaySamples = 0;
let showTfPhase = false, showTfCoh = true;
let tfSwap = false, lastEqCorr = null;
const TF_FFT_N = 2048;
const tfXr = new Float32Array(TF_FFT_N), tfXi = new Float32Array(TF_FFT_N);
const tfYr = new Float32Array(TF_FFT_N), tfYi = new Float32Array(TF_FFT_N);
const tfPxx = new Float32Array(TF_FFT_N / 2), tfPyy = new Float32Array(TF_FFT_N / 2);
const tfPxyRe = new Float32Array(TF_FFT_N / 2), tfPxyIm = new Float32Array(TF_FFT_N / 2);
const tfWin = new Float32Array(TF_FFT_N);
for(let i=0; i<TF_FFT_N; i++) tfWin[i] = 0.5 * (1 - Math.cos((2 * Math.PI * i) / (TF_FFT_N - 1)));

// ---- A/B Comparison State ----
let saveA = null, saveB = null, abMode = 'off';

// ---- Audio Generator State ----
let genType='pink', genOn=false, genGain=null, genSrc=null, genOsc=null;
let genDb=-34, genHz=1000;

// ---- Calibration, Delay & EQ Target ----
let micCalList=[], activeCalId=null, micCal=null;
const CAL_KEY='rta_miccals';
let targetMode='flat';
let eqPositions=[], areas=[], saves=[];
let dlySpeakers=[{name:'רמקול 1 (עוגן)', ms:0},{name:'רמקול 2', ms:0}], dlyAnchor=0;

// ---- Bands Initialization ----
function buildBands(bpo){
  curBpo=bpo; ISO=[];
  const n=Math.max(2,Math.round(Math.log2(viewMax/viewMin)*bpo));
  for(let k=0;k<=n;k++) ISO.push(viewMin*Math.pow(2,k/bpo));
  BANDS=ISO.length; R=Math.pow(2,1/(2*bpo));
  peaks=new Array(BANDS).fill(0); avgBuf=new Array(BANDS).fill(0);
  lastV=new Array(BANDS).fill(0); lastBandDb=new Array(BANDS).fill(-120);
  snapCurve=null; frozen=false;
}
buildBands(6);

// ---- Generator Logic ----
function createPinkNoiseBuffer(ctx){
  const sz = ctx.sampleRate * 3, b = ctx.createBuffer(1, sz, ctx.sampleRate), d = b.getChannelData(0);
  let b0=0,b1=0,b2=0,b3=0,b4=0,b5=0,b6=0;
  for(let i=0;i<sz;i++){
    const w = Math.random()*2 - 1;
    b0 = 0.99886*b0 + w*0.0555179; b1 = 0.99332*b1 + w*0.0750759;
    b2 = 0.96900*b2 + w*0.1538520; b3 = 0.86650*b3 + w*0.3104856;
    b4 = 0.55000*b4 + w*0.5329522; b5 = -0.7616*b5 - w*0.0168980;
    d[i] = (b0+b1+b2+b3+b4+b5+b6+w*0.5362) * 0.11;
    b6 = w * 0.115926;
  }
  return b;
}

function updateGenSound(){
  if(!audioCtx || !genOn) return;
  if(genSrc){ try{ genSrc.stop(); }catch(_){} genSrc=null; }
  if(genOsc){ try{ genOsc.stop(); }catch(_){} genOsc=null; }
  
  const gainVal = Math.pow(10, genDb / 20);
  if(!genGain){ genGain = audioCtx.createGain(); genGain.connect(audioCtx.destination); }
  genGain.gain.setTargetAtTime(gainVal, audioCtx.currentTime, 0.03);

  if(genType === 'pink'){
    genSrc = audioCtx.createBufferSource();
    genSrc.buffer = createPinkNoiseBuffer(audioCtx);
    genSrc.loop = true; genSrc.connect(genGain); genSrc.start();
  } else if(genType === 'sine'){
    genOsc = audioCtx.createOscillator();
    genOsc.frequency.setValueAtTime(genHz, audioCtx.currentTime);
    genOsc.connect(genGain); genOsc.start();
  }
}

safeAddListener('genOnBtn', 'click', function(){
  if(!audioCtx) startAudio();
  genOn = !genOn;
  this.classList.toggle('on', genOn);
  this.textContent = genOn ? '⏹ עצור אות' : '▶ הפעל אות';
  updateGenSound();
});

safeAddListener('genLvl', 'input', e=>{
  genDb = parseFloat(e.target.value);
  const el = document.getElementById('genLvlVal'); if(el) el.textContent = genDb+'dB';
  if(genGain) genGain.gain.setTargetAtTime(Math.pow(10, genDb/20), audioCtx.currentTime, 0.02);
});

// ---- Microphone Calibration Logic ----
function loadCalStore(){
  try { micCalList = JSON.parse(localStorage.getItem(CAL_KEY) || '[]'); } catch(_) { micCalList = []; }
}
function saveCalStore(){ localStorage.setItem(CAL_KEY, JSON.stringify(micCalList)); }

function deriveActiveCal(){
  const active = micCalList.find(c => c.id === activeCalId);
  if(!active || !active.data || !active.data.length){ micCal = null; return; }
  micCal = active.data;
}

safeAddListener('calAdd', 'change', e=>{
  const file = e.target.files[0]; if(!file) return;
  const reader = new FileReader();
  reader.onload = evt => parseAndAddCal(file.name, evt.target.result);
  reader.readAsText(file);
});

function parseAndAddCal(name, text){
  const lines = text.split('\n'); const pts = [];
  lines.forEach(l=>{
    const line = l.trim();
    if(!line || line.startsWith('*') || line.startsWith(';')) return;
    const parts = line.split(/[\s,]+/);
    if(parts.length >= 2){
      const f = parseFloat(parts[0]), db = parseFloat(parts[1]);
      if(!isNaN(f) && !isNaN(db)) pts.push({f, db});
    }
  });
  if(pts.length < 2){ alert('קובץ כיול לא תקין'); return; }
  pts.sort((a,b)=>a.f-b.f);
  const newCal = { id: 'c_'+Date.now(), name: name.replace(/\.[^/.]+$/, ""), data: pts };
  micCalList.push(newCal); activeCalId = newCal.id;
  saveCalStore(); deriveActiveCal(); renderCalList();
}

function renderCalList(){
  const box = document.getElementById('calList'); if(!box) return;
  if(!micCalList.length){ box.innerHTML = '<div class="sub">אין כיולים שמורים.</div>'; return; }
  box.innerHTML = micCalList.map(c=> `
    <div class="calRow ${c.id===activeCalId?'on':''}" data-cid="${c.id}">
      <span class="nm">${escapeHtml(c.name)}</span>
      <span class="sub">${c.data.length} נקודות</span>
      <span class="del" data-del="${c.id}">✕</span>
    </div>
  `).join('');

  box.querySelectorAll('.calRow').forEach(r=>{
    r.addEventListener('click', e=>{
      if(e.target.classList.contains('del')) return;
      activeCalId = r.dataset.cid; saveCalStore(); deriveActiveCal(); renderCalList();
    });
  });
  box.querySelectorAll('.del').forEach(d=>{
    d.addEventListener('click', ()=>{
      micCalList = micCalList.filter(x=>x.id !== d.dataset.del);
      if(activeCalId === d.dataset.del) activeCalId = null;
      saveCalStore(); deriveActiveCal(); renderCalList();
    });
  });
}
loadCalStore(); deriveActiveCal();

// ---- Target Curve & EQ Calculations ----
function setTarget(t){
  targetMode = t;
  document.querySelectorAll('.tgtSeg button').forEach(b=>b.classList.toggle('on', b.dataset.t===t));
  computeAndShow();
}

function getTargetDb(freq){
  if(targetMode === 'house'){
    if(freq < 100) return 3.0;
    if(freq > 2000) return -((Math.log2(freq/2000)) * 1.5);
    return 0;
  }
  return 0; // flat
}

function computeAndShow(){
  if(!eqPositions.length){ lastEqCorr = null; return; }
  const avgDb = new Float32Array(GEQ.length);
  for(let k=0; k<GEQ.length; k++){
    let sum = 0;
    eqPositions.forEach(p => sum += p.db[k]);
    avgDb[k] = sum / eqPositions.length;
  }

  // חישוב offset להערכת קו בסיס
  let refSum = 0, refCnt = 0;
  for(let k=0; k<GEQ.length; k++){
    if(GEQ[k] >= 200 && GEQ[k] <= 4000){ refSum += avgDb[k]; refCnt++; }
  }
  const baseOffset = refCnt ? (refSum / refCnt) : 70;

  const corr = new Float32Array(GEQ.length);
  for(let k=0; k<GEQ.length; k++){
    const target = baseOffset + getTargetDb(GEQ[k]);
    let diff = target - avgDb[k];
    
    // החלת הגבלות בטיחות (Max +4dB Boost, Max -9dB/-4dB Cut)
    if(diff > 4.0) diff = 4.0;
    const maxCut = GEQ[k] <= 500 ? -9.0 : -4.0;
    if(diff < maxCut) diff = maxCut;
    if(cutOnly && diff > 0) diff = 0;

    corr[k] = Math.round(diff * 10) / 10;
  }
  lastEqCorr = corr;
}
// ---- UI Renderers for EQ & Spatial Areas ----
function renderEqList(){
  const box = document.getElementById('eqPosList'); if(!box) return;
  const sub = document.getElementById('eqSub');
  if(sub) sub.textContent = 'מיקומים שנמדדו: ' + eqPositions.length;
  if(!eqPositions.length){ box.innerHTML = '<div class="sub">טרם בוצעו מדידות.</div>'; return; }
  box.innerHTML = eqPositions.map((p, i) => `
    <div class="areaRow">
      <span class="nm">${escapeHtml(p.name)}</span>
      <button data-del-pos="${i}">מחק</button>
    </div>
  `).join('');
  box.querySelectorAll('[data-del-pos]').forEach(b => {
    b.addEventListener('click', () => {
      eqPositions.splice(parseInt(b.dataset.delPos), 1);
      renderEqList(); computeAndShow();
    });
  });
}

safeAddListener('eqMeasBtn', 'click', () => {
  if(!running || !floatData){ alert('הפעל את המיקרופון קודם'); return; }
  const btn = document.getElementById('eqMeasBtn');
  if(btn) btn.textContent = 'מודד... (5ש\')';
  
  const samples = [];
  const timer = setInterval(() => {
    if(!floatData) return;
    analyser.getFloatFrequencyData(floatData);
    const frame = new Float32Array(GEQ.length);
    for(let k=0; k<GEQ.length; k++){
      const nyq = audioCtx.sampleRate / 2;
      const idx = Math.min(floatData.length-1, Math.round(GEQ[k] / nyq * floatData.length));
      frame[k] = floatData[idx] + calib;
    }
    samples.push(frame);
  }, 100);

  setTimeout(() => {
    clearInterval(timer);
    if(btn) btn.textContent = 'מדוד מיקום (5ש\')';
    if(!samples.length) return;
    
    const avg = new Float32Array(GEQ.length);
    for(let k=0; k<GEQ.length; k++){
      let sum = 0; samples.forEach(s => sum += s[k]);
      avg[k] = sum / samples.length;
    }
    eqPositions.push({ name: 'מיקום ' + (eqPositions.length + 1), db: avg });
    renderEqList(); computeAndShow();
  }, 5000);
});

safeAddListener('eqResetBtn', 'click', () => {
  if(confirm('לאפס את כל המדידות במיקומים?')){
    eqPositions = []; renderEqList(); computeAndShow();
  }
});

// ---- A/B Widget & Captures UI Logic ----
let saves = [];
try { saves = JSON.parse(localStorage.getItem('rta_saves') || '[]'); } catch(_) { saves = []; }

function persistSaves(){ localStorage.setItem('rta_saves', JSON.stringify(saves)); }

function renderSaveList(){
  const box=document.getElementById('saveList'); if(!box) return;
  if(!saves.length){ box.innerHTML='<div class="sub">אין מדידות שמורות עדיין.</div>'; return; }
  box.innerHTML=saves.map(s=>{
    const isA = saveA && saveA.id === s.id;
    const isB = saveB && saveB.id === s.id;
    return '<div class="saveRow"><span class="nm" title="'+escapeHtml(s.name)+'">'+escapeHtml(s.name)+
      '</span><button class="abBtn '+(isA?'on-a':'')+'" data-set-a="'+s.id+'">A</button>'+
      '<button class="abBtn '+(isB?'on-b':'')+'" data-set-b="'+s.id+'">B</button>'+
      '<button data-load="'+s.id+'">טען</button><button data-rm="'+s.id+'">מחק</button></div>';
  }).join('');

  box.querySelectorAll('[data-set-a]').forEach(b=>b.addEventListener('click',()=>setAbSlot('A', b.dataset.setA)));
  box.querySelectorAll('[data-set-b]').forEach(b=>b.addEventListener('click',()=>setAbSlot('B', b.dataset.setB)));
  box.querySelectorAll('[data-load]').forEach(b=>b.addEventListener('click',()=>loadSave(b.dataset.load)));
  box.querySelectorAll('[data-rm]').forEach(b=>b.addEventListener('click',()=>{
    const s=saves.find(x=>x.id===b.dataset.rm);
    if(!confirm('למחוק את "'+(s?s.name:'')+'"?')) return;
    if(saveA && saveA.id===s.id) saveA=null;
    if(saveB && saveB.id===s.id) saveB=null;
    saves=saves.filter(x=>x.id!==b.dataset.rm); persistSaves(); updateAbWidget(); renderSaveList();
  }));
}

function setAbSlot(slot, id){
  const s = saves.find(x=>x.id===id); if(!s) return;
  if(slot==='A') saveA = (saveA && saveA.id===id) ? null : s;
  if(slot==='B') saveB = (saveB && saveB.id===id) ? null : s;
  if(saveA || saveB) abMode = slot === 'A' ? 'A' : 'B';
  else abMode = 'off';
  updateAbWidget();
  renderSaveList();
}

function updateAbWidget(){
  const w = document.getElementById('abWidget'); if(!w) return;
  const show = (saveA || saveB);
  w.classList.toggle('show', show);
  if(!show) { abMode='off'; return; }

  const btnA = document.getElementById('abBtnA');
  const btnB = document.getElementById('abBtnB');
  const btnDelta = document.getElementById('abBtnDelta');

  if(btnA){ btnA.style.display = saveA ? 'inline-block' : 'none'; btnA.classList.toggle('on', abMode==='A'); btnA.textContent = saveA ? 'A: '+saveA.name : 'A'; }
  if(btnB){ btnB.style.display = saveB ? 'inline-block' : 'none'; btnB.classList.toggle('on', abMode==='B'); btnB.textContent = saveB ? 'B: '+saveB.name : 'B'; }
  if(btnDelta){ btnDelta.style.display = (saveA && saveB) ? 'inline-block' : 'none'; btnDelta.classList.toggle('on', abMode==='delta'); }
}

safeAddListener('abBtnA', 'click', ()=>{ abMode='A'; updateAbWidget(); });
safeAddListener('abBtnB', 'click', ()=>{ abMode='B'; updateAbWidget(); });
safeAddListener('abBtnDelta', 'click', ()=>{ abMode='delta'; updateAbWidget(); });
safeAddListener('abBtnOff', 'click', ()=>{ abMode='off'; updateAbWidget(); });

safeAddListener('saveNowBtn', 'click', ()=>{
  const nameInput = document.getElementById('saveName');
  const name = (nameInput ? nameInput.value.trim() : '') || ('מדידה ' + (saves.length + 1));
  const newSave = {
    id: 's_' + Date.now(),
    name: name,
    date: new Date().toLocaleDateString('he-IL'),
    positions: eqPositions.slice()
  };
  saves.push(newSave);
  persistSaves();
  if(nameInput) nameInput.value = '';
  renderSaveList();
});

// ---- TF Delay Auto-Finder ----
function computeDelay(r, m, sr){
  const N = Math.min(r.length, m.length, 8192);
  let maxCorr = 0, bestLag = 0;
  for(let lag=0; lag<N/2; lag++){
    let sum = 0;
    for(let i=0; i<N-lag; i++){ sum += r[i] * m[i+lag]; }
    if(sum > maxCorr){ maxCorr = sum; bestLag = lag; }
  }
  const ms = (bestLag / sr) * 1000;
  return { ms, samples: bestLag };
}

function computeComplexTf(micSignal, refSignal){
  const N = TF_FFT_N;
  if(!micSignal || !refSignal || micSignal.length < N) return;
  const alpha = 0.95;

  for(let i=0; i<N; i++){
    const refIdx = Math.max(0, i - tfDelaySamples);
    tfXr[i] = (micSignal[i] || 0) * tfWin[i]; tfXi[i] = 0;
    tfYr[i] = (refSignal[refIdx] || 0) * tfWin[i]; tfYi[i] = 0;
  }

  fft(tfXr, tfXi); fft(tfYr, tfYi);

  for(let k=0; k<N/2; k++){
    const Xr=tfXr[k], Xi=tfXi[k], Yr=tfYr[k], Yi=tfYi[k];
    const pxx = Xr*Xr + Xi*Xi, pyy = Yr*Yr + Yi*Yi;
    const pxyRe = Xr*Yr + Xi*Yi, pxyIm = Xi*Yr - Xr*Yi;

    tfPxx[k] = tfPxx[k] * alpha + pxx * (1 - alpha);
    tfPyy[k] = tfPyy[k] * alpha + pyy * (1 - alpha);
    tfPxyRe[k] = tfPxyRe[k] * alpha + pxyRe * (1 - alpha);
    tfPxyIm[k] = tfPxyIm[k] * alpha + pxyIm * (1 - alpha);
  }
}

function fft(re, im){
  const n = re.length; let j = 0;
  for (let i = 0; i < n - 1; i++) {
    if (i < j) {
      let tr = re[i]; re[i] = re[j]; re[j] = tr;
      let ti = im[i]; im[i] = im[j]; im[j] = ti;
    }
    let k = n >> 1;
    while (k >= 1 && k <= j) { j -= k; k >>= 1; }
    j += k;
  }
  for (let len = 2; len <= n; len <<= 1) {
    let halfLen = len >> 1, angle = -2 * Math.PI / len;
    let wStepRe = Math.cos(angle), wStepIm = Math.sin(angle);
    for (let i = 0; i < n; i += len) {
      let wRe = 1, wIm = 0;
      for (let k = 0; k < halfLen; k++) {
        let pos = i + k, matchPos = pos + halfLen;
        let uRe = re[pos], uIm = im[pos];
        let vRe = re[matchPos] * wRe - im[matchPos] * wIm;
        let vIm = re[matchPos] * wIm + im[matchPos] * wRe;
        re[pos] = uRe + vRe; im[pos] = uIm + vIm;
        re[matchPos] = uRe - vRe; im[matchPos] = uIm - vIm;
        let nextWRe = wRe * wStepRe - wIm * wStepIm;
        wIm = wRe * wStepIm + wIm * wStepRe; wRe = nextWRe;
      }
    }
  }
}

// ---- Main Canvas Rendering ----
function drawRta(){
  if(!ctx || !cv) return;
  const W=cv.clientWidth, H=cv.clientHeight;
  const plotH = H - 36;
  const nyquist = audioCtx ? audioCtx.sampleRate/2 : 22050;

  ctx.clearRect(0,0,W,H);
  ctx.fillStyle = sunMode ? '#f8fafc' : '#0d1117';
  ctx.fillRect(0,0,W,H);

  const xForFreq = f => {
    const lMin = Math.log10(viewMin), lMax = Math.log10(viewMax);
    return Math.max(0, Math.min(W, ((Math.log10(f) - lMin) / (lMax - lMin)) * W));
  };
  const freqForX = x => {
    const lMin = Math.log10(viewMin), lMax = Math.log10(viewMax);
    return Math.pow(10, lMin + (x / W) * (lMax - lMin));
  };
  const norm = db => Math.max(0, Math.min(1, (db - floorDb) / (ceilDb - floorDb)));

  // Grid Lines
  ctx.strokeStyle = sunMode ? 'rgba(0,0,0,0.08)' : 'rgba(255,255,255,0.08)';
  ctx.lineWidth = 1;
  [31.5, 63, 125, 250, 500, 1000, 2000, 4000, 8000, 16000].forEach(f => {
    const x = xForFreq(f);
    ctx.beginPath(); ctx.moveTo(x, 0); ctx.lineTo(x, plotH); ctx.stroke();
    ctx.fillStyle = sunMode ? '#64748b' : '#94a3b8'; ctx.font = '10px Heebo, sans-serif';
    ctx.textAlign = 'center'; ctx.fillText(f >= 1000 ? (f/1000)+'kHz' : f+'Hz', x, H - 12);
  });

  for(let db = floorDb; db <= ceilDb; db += 10){
    const y = plotH - norm(db) * plotH;
    ctx.strokeStyle = sunMode ? 'rgba(0,0,0,0.06)' : 'rgba(255,255,255,0.06)';
    ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke();
    ctx.fillStyle = sunMode ? '#475569' : '#64748b'; ctx.font = '9px Heebo, sans-serif';
    ctx.textAlign = 'left'; ctx.fillText(db + 'dB', 6, y - 2);
  }

  // Phase & Coherence
  if(showTfPhase){
    ctx.beginPath();
    for(let px = 0; px <= W; px += 2){
      const f = freqForX(px);
      const k = Math.min(TF_FFT_N/2 - 1, Math.round(f / nyquist * (TF_FFT_N/2)));
      let pxyRe = 0, pxyIm = 0;
      for(let offset = -1; offset <= 1; offset++){
        const idx = Math.max(0, Math.min(TF_FFT_N/2 - 1, k + offset));
        pxyRe += tfPxyRe[idx]; pxyIm += tfPxyIm[idx];
      }
      const phaseRad = Math.atan2(pxyIm, pxyRe);
      const phaseNorm = 0.5 - (phaseRad / (2 * Math.PI));
      const y = plotH * Math.max(0, Math.min(1, phaseNorm));
      px === 0 ? ctx.moveTo(px, y) : ctx.lineTo(px, y);
    }
    ctx.strokeStyle = 'rgba(34, 197, 94, 0.9)'; ctx.lineWidth = 2; ctx.stroke();
  }

  if(showTfCoh){
    ctx.beginPath(); let prevCoh = 0;
    for(let px = 0; px <= W; px += 2){
      const f = freqForX(px);
      const k = Math.min(TF_FFT_N/2 - 1, Math.round(f / nyquist * (TF_FFT_N/2)));
      let pxx=0, pyy=0, pxyRe=0, pxyIm=0;
      for(let offset = -1; offset <= 1; offset++){
        const idx = Math.max(0, Math.min(TF_FFT_N/2 - 1, k + offset));
        pxx += tfPxx[idx]; pyy += tfPyy[idx]; pxyRe += tfPxyRe[idx]; pxyIm += tfPxyIm[idx];
      }
      const pxySq = pxyRe*pxyRe + pxyIm*pxyIm;
      const rawCoh = Math.max(0, Math.min(1, pxySq / (pxx * pyy + 1e-12)));
      const coh = prevCoh ? (prevCoh * 0.4 + rawCoh * 0.6) : rawCoh; prevCoh = coh;
      const y = plotH - coh * plotH;
      px === 0 ? ctx.moveTo(px, y) : ctx.lineTo(px, y);
    }
    ctx.strokeStyle = 'rgba(239, 68, 68, 0.85)'; ctx.lineWidth = 2; ctx.setLineDash([4, 2]); ctx.stroke(); ctx.setLineDash([]);
  }

  // A/B Delta Drawing
  if(abMode !== 'off'){
    const drawTrace = (s, col, label) => {
      if(!s || !s.positions || !s.positions.length) return;
      const dbArr = s.positions[0].db;
      ctx.strokeStyle = col; ctx.lineWidth = 2; ctx.beginPath();
      for(let k=0; k<GEQ.length; k++){
        const f = GEQ[k]; if(f<ISO[0]||f>ISO[BANDS-1]) continue;
        const x = xForFreq(f), yy = plotH - norm(dbArr[k]) * plotH;
        k===0 ? ctx.moveTo(x,yy) : ctx.lineTo(x,yy);
      }
      ctx.stroke();
      ctx.fillStyle = col; ctx.font = 'bold 11px Heebo, sans-serif'; ctx.textAlign='start';
      ctx.fillText('— ' + label + ': ' + s.name, 10, 20);
    };

    if(abMode === 'A') drawTrace(saveA, '#2f9bff', 'מדידה A');
    if(abMode === 'B') drawTrace(saveB, '#ffa53b', 'מדידה B');

    if(abMode === 'delta' && saveA && saveB && saveA.positions[0] && saveB.positions[0]){
      const dbA = saveA.positions[0].db, dbB = saveB.positions[0].db;
      const midY = plotH / 2;
      ctx.strokeStyle = 'rgba(255,255,255,0.3)'; ctx.setLineDash([3,3]);
      ctx.beginPath(); ctx.moveTo(0, midY); ctx.lineTo(W, midY); ctx.stroke(); ctx.setLineDash([]);
      ctx.strokeStyle = '#39d98a'; ctx.lineWidth = 2.5; ctx.beginPath();
      for(let k=0; k<GEQ.length; k++){
        const f = GEQ[k]; if(f<ISO[0]||f>ISO[BANDS-1]) continue;
        const diff = dbB[k] - dbA[k];
        const x = xForFreq(f), yy = midY - (diff * (plotH / 30));
        k===0 ? ctx.moveTo(x,yy) : ctx.lineTo(x,yy);
      }
      ctx.stroke();
      ctx.fillStyle = '#39d98a'; ctx.font = 'bold 11px Heebo, sans-serif'; ctx.textAlign='start';
      ctx.fillText('— Δ הפרש (B - A)', 10, 20);
    }
  }

  // Live RTA Curve
  if(analyser && floatData){
    if(!frozen) analyser.getFloatFrequencyData(floatData);
    computeComplexTf(floatData, floatDataRef);

    ctx.beginPath();
    ctx.strokeStyle = sunMode ? '#0284c7' : '#3ea6ff'; ctx.lineWidth = 2;
    for(let i = 0; i < floatData.length; i++){
      const f = (i / floatData.length) * nyquist;
      if(f < viewMin || f > viewMax) continue;
      const x = xForFreq(f);
      const y = plotH - norm(floatData[i] + calib) * plotH;
      i === 0 ? ctx.moveTo(x, y) : ctx.lineTo(x, y);
    }
    ctx.stroke();
  }

  // GEQ Dock Drawing
  const dock = document.getElementById('geqDock');
  const eqCanvas = document.getElementById('eqCurveCanvas');
  if(dock && !dock.classList.contains('collapsed') && eqCanvas && lastEqCorr){
    drawGEQ(eqCanvas, GEQ, lastEqCorr);
  }
}

// ---- Loop & Setup ----
function updateLoop(){
  if(!running) return;
  drawRta();
  raf = requestAnimationFrame(updateLoop);
}

async function startAudio(){
  try {
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    stream = await navigator.mediaDevices.getUserMedia({ audio: { echoCancellation: false, noiseSuppression: false, autoGainControl: false } });
    source = audioCtx.createMediaStreamSource(stream);
    
    analyser = audioCtx.createAnalyser();
    analyser.fftSize = fftSize;
    analyser.smoothingTimeConstant = 0.7;
    source.connect(analyser);

    floatData = new Float32Array(analyser.frequencyBinCount);
    timeData = new Float32Array(analyser.fftSize);

    if(stream.getAudioTracks().length > 1){
      analyserRef = audioCtx.createAnalyser();
      analyserRef.fftSize = fftSize;
      floatDataRef = new Float32Array(analyserRef.frequencyBinCount);
      timeDataRef = new Float32Array(analyserRef.fftSize);
    }

    running = true;
    if(idle) idle.style.display = 'none';
    if(dot) dot.classList.add('live');
    const qb = document.getElementById('tfQuickBar');
    if(qb) qb.classList.add('show');

    updateLoop();
  } catch(err) {
    if(errBox){ errBox.style.display='block'; errBox.textContent = 'שגיאה בגישה למיקרופון: ' + err.message; }
  }
}

safeAddListener('startBtn', 'click', startAudio);
safeAddListener('stopBtn', 'click', ()=>{
  if(confirm('האם לאפס את הסשן ולעצור את המיקרופון?')){
    running = false;
    if(raf) cancelAnimationFrame(raf);
    if(audioCtx) audioCtx.close();
    if(dot) dot.classList.remove('live');
    if(idle) idle.style.display = 'flex';
  }
});

// Tab Navigation
document.querySelectorAll('.tab').forEach(t=>{
  t.addEventListener('click', ()=>{
    document.querySelectorAll('.tab').forEach(x=>x.classList.remove('on'));
    document.querySelectorAll('.tabpage').forEach(x=>x.classList.remove('active'));
    t.classList.add('on');
    const target = t.dataset.p;
    const page = document.querySelector(`.tabpage[data-page="${target}"]`);
    if(page) page.classList.add('active');
  });
});

safeAddListener('saveBtn', 'click', ()=>{
  const p = document.getElementById('savePanel');
  if(p){ p.classList.toggle('open'); renderSaveList(); }
});
safeAddListener('saveClose', 'click', ()=>{ const p = document.getElementById('savePanel'); if(p) p.classList.remove('open'); });

safeAddListener('geqShowBtn', 'click', ()=>{
  const dock = document.getElementById('geqDock');
  if(dock){
    const isHidden = dock.style.display === 'none';
    dock.style.display = isHidden ? 'block' : 'none';
    if(isHidden) dock.classList.remove('collapsed');
  }
});
safeAddListener('geqDockToggle', 'click', ()=>{
  const dock = document.getElementById('geqDock');
  if(dock) dock.classList.toggle('collapsed');
});

// Resize Listener
function resize(){
  if (!cv || !ctx) return;
  const r=cv.getBoundingClientRect();
  const dpr=Math.max(1, Math.min(window.devicePixelRatio||1, 2));
  cv.width=Math.round(r.width*dpr); cv.height=Math.round(r.height*dpr);
  ctx.setTransform(dpr,0,0,dpr,0,0);
}
window.addEventListener('resize', resize);

resize();
renderSaveList();
renderCalList();
