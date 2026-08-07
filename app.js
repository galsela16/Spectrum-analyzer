
const FMIN=20, FMAX=20000;
let viewMin=20, viewMax=20000;
let curBpo=6;
let ISO=[], BANDS=0, R=1;
let peaks=[];
let avgBuf=[], snapCurve=null, lastV=[], lastBandDb=[];
function buildBands(bpo){
  curBpo=bpo;
  ISO=[];
  const n=Math.max(2,Math.round(Math.log2(viewMax/viewMin)*bpo));
  for(let k=0;k<=n;k++) ISO.push(viewMin*Math.pow(2,k/bpo));
  BANDS=ISO.length;
  R=Math.pow(2,1/(2*bpo));
  peaks=new Array(BANDS).fill(0);
  avgBuf=new Array(BANDS).fill(0);
  lastV=new Array(BANDS).fill(0);
  lastBandDb=new Array(BANDS).fill(-120);
  snapCurve=null;
  const clr=document.getElementById('freezeBtn'); if(clr){clr.classList.remove('on');clr.textContent='הקפא';}
}
buildBands(6);

const cv = document.getElementById('cv');
const ctx = cv.getContext('2d');
const dot = document.getElementById('dot');
const idle = document.getElementById('idle');
const errBox = document.getElementById('err');
const peakHzEl = document.getElementById('peakHz');
const fbPanel = document.getElementById('fbPanel');
const meterEl = document.getElementById('meter');
const meterFill = document.getElementById('meterFill');
const meterPeak = document.getElementById('meterPeak');
const meterVal = document.getElementById('meterVal');

let audioCtx, analyser, analyserMeter, source, stream, raf;
let analyserRef=null, floatDataRef=null, chReceived=1;
let floatData;
let timeData, timeDataMeter;
const GEQ=[20,25,31.5,40,50,63,80,100,125,160,200,250,315,400,500,630,800,1000,
           1250,1600,2000,2500,3150,4000,5000,6300,8000,10000,12500,16000,20000];
let tfState='idle', tfSwap=false, tfMic=null, tfRef=null, tfDiffSum=null, tfDiffSq=null, tfFrames=0, tfResult=null;
let running=false, mode='rta';
let peakHold=true, fbOn=true, avgOn=false;
let floorDb=-85, ceilDb=-15;
let calib=0;
let fbProm=14;
let lvlPeak=-120, lvlPeakT=0;
let weightMode='Z';
let meterUnit='SPL';
let meterMode='rms';   // 'rms' (smooth average) | 'peak' (catches transients)
let activeInId='';     // device id currently in use (for auto-select)
let weightA=null, weightC=null;
let leqSumP=0, leqN=0, splMax=-120;
let dragging=false, dragX0=0, dragX1=0, cursorX=null;
let genType='pink', genOn=false, genGain=null, genSrc=null, genOsc=null;
let genDb=-34, genHz=1000, targetMode='flat';
let fftSize=32768;   // FFT resolution (accuracy vs speed)
let _pfx=null;   // per-frame prefix-sum of linear power (perf)
let genSweepDur=4, sweepTimer=null, sweepStartT=0;
let pinkComp=false, compChoice=true;
let rt60State='idle', rt60Samples=[], rt60CutT=0, rtRange=10, rt60Timer=null, rtLevel=-6;
let eqMarks=null;
let eqCurveData=null;
let eqMode='graphic', lastEqCorr=null;
let tfMode='graphic';
let eqCh = 1;
const AREA_COLORS=['#2f9bff','#ffa53b','#ff5cc8','#50e68c'];
const AREA_NAMES=['צפון','דרום','מזרח','מערב'];
let areas=[];
let areaState='idle', areaAccum=null, areaFrames=0;
let measState='idle', measAccum=null, measFrames=0;
let eqPositions=[];
let micCalList=[], activeCalId=null, micCal=null;
const CAL_KEY='rta_miccals';
let specCanvas, specCtx;

let fbTrack=new Map();
let fbFrameCounter = 0;
let smoothedDbfs = -120;

function resize(){
  const r=cv.getBoundingClientRect();
  // cap the backing resolution: keep it crisp on small sizes, but don't render millions of
  // extra pixels on a full-screen Retina canvas (that's what slows it down when maximized).
  const MAXW=1800;
  const dpr=Math.max(1, Math.min(window.devicePixelRatio||1, 2, MAXW/Math.max(1,r.width)));
  cv.width=Math.round(r.width*dpr); cv.height=Math.round(r.height*dpr);
  ctx.setTransform(dpr,0,0,dpr,0,0);
  specCanvas=document.createElement('canvas');
  specCanvas.width=Math.max(2,Math.floor(r.width));
  specCanvas.height=Math.max(2,Math.floor(r.height));
  specCtx=specCanvas.getContext('2d');
  specCtx.fillStyle='#0d1117'; specCtx.fillRect(0,0,specCanvas.width,specCanvas.height);
}
window.addEventListener('resize',resize);

document.getElementById('floor').addEventListener('input',e=>{
  floorDb=parseFloat(e.target.value);
  document.getElementById('floorVal').textContent=floorDb+'dB';
});
document.getElementById('smooth').addEventListener('input',e=>{
  const v=parseFloat(e.target.value);
  document.getElementById('smoothVal').textContent=v.toFixed(2);
  if(analyser) analyser.smoothingTimeConstant=v;
});
document.getElementById('cal').addEventListener('input',e=>{
  calib=parseFloat(e.target.value);
  document.getElementById('calVal').textContent=(calib>=0?'+':'')+calib+'dB';
});
document.getElementById('fbSens').addEventListener('input',e=>{
  fbProm = 26 - parseFloat(e.target.value);
  document.getElementById('fbSensVal').textContent = fbProm>=15?'נמוכה':fbProm>=10?'בינונית':'גבוהה';
});
document.getElementById('peakBtn').addEventListener('click',function(){
  peakHold=!peakHold; this.classList.toggle('on',peakHold); peaks.fill(0);
});
document.getElementById('fbBtn').addEventListener('click',function(){
  fbOn=!fbOn; this.classList.toggle('on',fbOn); fbTrack.clear(); fbPanel.innerHTML='';
});
document.getElementById('avgBtn').addEventListener('click',function(){
  avgOn=!avgOn; this.classList.toggle('on',avgOn); if(avgOn) avgBuf.fill(0);
});
document.getElementById('freezeBtn').addEventListener('click',function(){
  if(snapCurve){ snapCurve=null; this.classList.remove('on'); this.textContent='הקפא'; }
  else { snapCurve=lastV.slice(); this.classList.add('on'); this.textContent='נקה הקפאה'; }
});
document.getElementById('pngBtn').addEventListener('click',exportPNG);
document.getElementById('csvBtn').addEventListener('click',exportCSV);

function stamp(){ const d=new Date(); const p=n=>(''+n).padStart(2,'0');
  return d.getFullYear()+p(d.getMonth()+1)+p(d.getDate())+'_'+p(d.getHours())+p(d.getMinutes())+p(d.getSeconds()); }
function download(name, blobUrl){
  const a=document.createElement('a'); a.href=blobUrl; a.download=name;
  document.body.appendChild(a); a.click(); a.remove();
}
function exportPNG(){
  const W=cv.clientWidth,H=cv.clientHeight,dpr=Math.min(window.devicePixelRatio||1,2);
  const off=document.createElement('canvas'); off.width=W*dpr; off.height=H*dpr;
  const o=off.getContext('2d'); o.scale(dpr,dpr);
  o.fillStyle='#0d1117'; o.fillRect(0,0,W,H);
  o.drawImage(cv,0,0,W,H);
  download('rta_'+stamp()+'.png', off.toDataURL('image/png'));
}
function exportCSV(){
  let rows='freq_hz,level_db\n';
  for(let b=0;b<BANDS;b++) rows+=Math.round(ISO[b])+','+lastBandDb[b].toFixed(1)+'\n';
  download('rta_'+stamp()+'.csv', URL.createObjectURL(new Blob([rows],{type:'text/csv'})));
}

document.getElementById('wgtBtn').addEventListener('click',function(){
  weightMode = weightMode==='Z'?'A':weightMode==='A'?'C':'Z';
  this.textContent='dB'+weightMode;
  this.classList.toggle('on', weightMode!=='Z');
  document.getElementById('wLbl').textContent=weightMode;
  leqSumP=0; leqN=0; splMax=-120;
});
document.getElementById('leqBtn').addEventListener('click',()=>{ leqSumP=0; leqN=0; splMax=-120; });
document.querySelectorAll('#unitSeg button').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#unitSeg button').forEach(x=>x.classList.remove('on'));
  this.classList.add('on'); meterUnit=this.dataset.u;
}));
document.getElementById('inSel').addEventListener('change',e=>{ try{localStorage.setItem('rta_inDev',e.target.value);}catch(_){} switchInput(e.target.value); });

function freqForX(px){
  const W=cv.clientWidth;
  const lmin=Math.log(ISO[0]), lmax=Math.log(ISO[BANDS-1]);
  return Math.exp(lmin + Math.max(0,Math.min(1,px/W))*(lmax-lmin));
}
function applyZoom(xa,xb){
  let fa=freqForX(Math.min(xa,xb)), fb=freqForX(Math.max(xa,xb));
  if(fb/fa < 1.2) return;
  viewMin=Math.max(FMIN,fa); viewMax=Math.min(FMAX,fb);
  buildBands(curBpo);
  document.getElementById('zoomBtn').style.display='block';
}
function resetZoom(){
  viewMin=FMIN; viewMax=FMAX; buildBands(curBpo);
  document.getElementById('zoomBtn').style.display='none';
}
cv.addEventListener('pointerdown',e=>{
  if(!running||mode!=='rta') return;
  dragging=true; dragX0=dragX1=e.offsetX;
  try{cv.setPointerCapture(e.pointerId);}catch(_){}
});
cv.addEventListener('pointermove',e=>{ cursorX=e.offsetX; if(dragging) dragX1=e.offsetX; });
cv.addEventListener('pointerleave',()=>{ cursorX=null; });
cv.addEventListener('pointerup',e=>{
  if(!dragging) return; dragging=false;
  if(Math.abs(dragX1-dragX0)>20) applyZoom(dragX0,dragX1);
});
cv.addEventListener('pointercancel',()=>{dragging=false;});
cv.addEventListener('dblclick',()=>{ if(running) resetZoom(); });
document.getElementById('zoomBtn').addEventListener('click',resetZoom);

function makeNoiseBuffer(type){
  const len=Math.floor(audioCtx.sampleRate*2);
  const buf=audioCtx.createBuffer(1,len,audioCtx.sampleRate);
  const d=buf.getChannelData(0);
  if(type==='white'){
    for(let i=0;i<len;i++) d[i]=Math.random()*2-1;
  } else {
    let b0=0,b1=0,b2=0,b3=0,b4=0,b5=0,b6=0;
    for(let i=0;i<len;i++){
      const w=Math.random()*2-1;
      b0=0.99886*b0+w*0.0555179; b1=0.99332*b1+w*0.0750759;
      b2=0.96900*b2+w*0.1538520; b3=0.86650*b3+w*0.3104856;
      b4=0.55000*b4+w*0.5329522; b5=-0.7616*b5-w*0.0168980;
      d[i]=(b0+b1+b2+b3+b4+b5+b6+w*0.5362)*0.11; b6=w*0.115926;
    }
  }
  return buf;
}
function genStop(){
  if(genGain){ try{genGain.gain.cancelScheduledValues(audioCtx.currentTime);
    genGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.05);}catch(_){} }
  if(sweepTimer){ clearTimeout(sweepTimer); sweepTimer=null; }
  const g=genGain, s=genSrc, o=genOsc;
  setTimeout(()=>{
    try{ if(s) s.stop(); }catch(_){}
    try{ if(o) o.stop(); }catch(_){}
    try{ if(g) g.disconnect(); }catch(_){}
  },250);
  genSrc=null; genOsc=null; genGain=null; genOn=false;
  const btn=document.getElementById('genOnBtn'); if(btn){btn.classList.remove('on'); btn.textContent='▶ הפעל אות';}
  syncInlineGenBtns();
  syncPinkComp();
}
function scheduleSweepCycle(){
  if(!genOn || genType!=='sweep' || !genOsc) return;
  const t=audioCtx.currentTime;
  sweepStartT=t;   // for the signal-tint hue tracking
  try{
    genOsc.frequency.cancelScheduledValues(t);
    genOsc.frequency.setValueAtTime(20, t);
    genOsc.frequency.exponentialRampToValueAtTime(20000, t+genSweepDur);
  }catch(_){}
  sweepTimer=setTimeout(scheduleSweepCycle, genSweepDur*1000);
}
function genStart(){
  if(!running||!audioCtx){ alert('קודם הפעל את המיקרופון (כדי שהאודיו יהיה פעיל).'); return; }
  if(audioCtx.state==='suspended') audioCtx.resume();   // safety: ensure output is live
  genStop();
  genGain=audioCtx.createGain(); genGain.gain.value=0;
  if(genType==='sine' || genType==='sweep'){
    genOsc=audioCtx.createOscillator(); genOsc.type='sine';
    genOsc.frequency.value = genType==='sine'? genHz : 20;
    genOsc.connect(genGain); genOsc.start();
  } else {
    genSrc=audioCtx.createBufferSource(); genSrc.buffer=makeNoiseBuffer(genType);
    genSrc.loop=true; genSrc.connect(genGain); genSrc.start();
  }
  genGain.connect(audioCtx.destination);
  const target=Math.pow(10,genDb/20);
  genGain.gain.setTargetAtTime(target,audioCtx.currentTime,0.15);
  genOn=true;
  if(genType==='sweep') scheduleSweepCycle();
  syncInlineGenBtns();
  syncPinkComp();
  const btn=document.getElementById('genOnBtn'); if(btn){btn.classList.add('on'); btn.textContent='⏹ עצור אות';}
}

function syncInlineGenBtns(){
  ['eqGenToggleBtn', 'areaGenToggleBtn', 'gainGenBtn'].forEach(id=>{
    const b = document.getElementById(id);
    if(b){
      b.classList.toggle('on', genOn && genType==='pink');
      b.textContent = (genOn && genType==='pink') ? '⏹ עצור רעש' : '▶ רעש ורוד';
    }
  });
}

function syncPinkComp(){
  const wrap=document.getElementById('genCompWrap');
  if(wrap) wrap.style.display = (genType==='pink') ? 'flex' : 'none';
  pinkComp = (genOn && genType==='pink' && compChoice);
}
function genApplyLevel(){
  if(genGain){ genGain.gain.setTargetAtTime(Math.pow(10,genDb/20),audioCtx.currentTime,0.1); }
}

document.getElementById('genBtn').addEventListener('click',function(){
  const p=document.getElementById('genPanel'); 
  const open=p.classList.toggle('open');
  this.classList.toggle('on',open);
});

document.querySelectorAll('#genType button').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#genType button').forEach(x=>x.classList.remove('on'));
  this.classList.add('on'); genType=this.dataset.t;
  document.getElementById('genFreqWrap').style.display = genType==='sine'?'flex':'none';
  document.getElementById('genSweepWrap').style.display = genType==='sweep'?'flex':'none';
  document.getElementById('genCompWrap').style.display = genType==='pink'?'flex':'none';
  if(genOn) genStart();
  else syncPinkComp();
}));
document.getElementById('genSweep').addEventListener('input',e=>{
  genSweepDur=parseFloat(e.target.value);
  document.getElementById('genSweepVal').textContent=genSweepDur.toFixed(1)+'ש\'';
});
document.getElementById('genLvl').addEventListener('input',e=>{
  genDb=parseFloat(e.target.value);
  const el=document.getElementById('genLvlVal'); el.textContent=genDb+'dB';
  el.style.color = genDb>=-16 ? '#ff3b6b' : (genDb>=-24?'#ffd166':'var(--accent)');
  genApplyLevel();
});
function applyGenHz(hz, from){
  hz=Math.max(20,Math.min(20000, hz||0));
  genHz=hz;
  const slider=document.getElementById('genFreq'), num=document.getElementById('genFreqNum');
  if(from!=='slider') slider.value=Math.min(16000,hz);
  if(from!=='num') num.value=Math.round(hz);
  document.getElementById('genFreqVal').textContent=(genHz>=1000?(genHz/1000).toFixed(genHz%1000?2:1)+'k':genHz)+'Hz';
  if(genOsc) genOsc.frequency.setTargetAtTime(genHz,audioCtx.currentTime,0.02);
}
document.getElementById('genFreq').addEventListener('input',e=>applyGenHz(parseFloat(e.target.value),'slider'));
document.getElementById('genFreqNum').addEventListener('input',e=>applyGenHz(parseFloat(e.target.value),'num'));
document.getElementById('genOnBtn').addEventListener('click',()=>{ genOn?genStop():genStart(); });

['eqGenToggleBtn', 'areaGenToggleBtn', 'gainGenBtn'].forEach(id=>{
  const el = document.getElementById(id);
  if(el){
    el.addEventListener('click', function(){
      if(genOn && genType === 'pink'){
        genStop();
      } else {
        genType = 'pink';
        setGenTypeUI('pink');
        genStart();
      }
    });
  }
});

function setTarget(mode){
  targetMode=mode;
  document.querySelectorAll('.tgtSeg button').forEach(b=>b.classList.toggle('on', b.dataset.t===mode));
  if(eqPositions.length) computeAndShow();
  if(areas.length) suggestAreaEQ();
  if(typeof tfFrames!=='undefined' && tfFrames) tfCompute();
}
document.querySelectorAll('.tgtSeg button').forEach(b=>b.addEventListener('click',function(){ setTarget(this.dataset.t); }));

document.querySelectorAll('.tab').forEach(t=>t.addEventListener('click',function(){
  document.querySelectorAll('.tab').forEach(x=>x.classList.remove('on'));
  this.classList.add('on');
  const p=this.dataset.p;
  document.querySelectorAll('.tabpage').forEach(pg=>pg.classList.toggle('active', pg.dataset.page===p));
}));

document.querySelectorAll('#genCompSeg button').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#genCompSeg button').forEach(x=>x.classList.remove('on'));
  this.classList.add('on'); compChoice=(this.dataset.c==='on'); syncPinkComp();
}));

const eqPanel=document.getElementById('eqPanel');
document.getElementById('eqClose').addEventListener('click',closeModals);
document.getElementById('eqBtn').addEventListener('click',()=>{ showModal(eqPanel); updateEqUI(); });
// unified response tool: single-channel (spatial) ↔ dual-channel (TF)
document.querySelectorAll('.respModeSeg button').forEach(b=>b.addEventListener('click',function(){
  if(this.dataset.rm==='dual'){ showModal(tfPanel); if(typeof tfResult!=='undefined' && tfResult) renderTFList(); }
  else { showModal(eqPanel); updateEqUI(); }
}));
document.querySelectorAll('#eqModeSwitchA button').forEach(b=>b.addEventListener('click',function(){
  if(this.dataset.go==='area'){ openAreas(); }
}));

document.querySelectorAll('#eqChSeg button').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#eqChSeg button').forEach(x=>x.classList.remove('on'));
  this.classList.add('on');
  eqCh = parseInt(this.dataset.ch, 10);
}));

document.getElementById('eqMeasBtn').addEventListener('click',()=>pickSource(measurePosition,5000));
document.querySelectorAll('#eqModeSeg button').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#eqModeSeg button').forEach(x=>x.classList.remove('on'));
  this.classList.add('on'); eqMode=this.dataset.m; renderEqResult();
}));
document.querySelectorAll('#tfModeSeg button').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#tfModeSeg button').forEach(x=>x.classList.remove('on'));
  this.classList.add('on'); tfMode=this.dataset.m; if(tfResult) renderTFList();
}));
document.getElementById('eqResetBtn').addEventListener('click',()=>{ eqPositions=[]; eqMarks=null; document.getElementById('eqList').innerHTML=''; document.getElementById('eqPosList').innerHTML=''; updateEqUI(); });

function updateEqUI(){
  const meas = measState==='measuring';
  document.getElementById('eqSub').textContent = meas ? 'מודד… החזק יציב' : ('מיקומים שנמדדו: '+eqPositions.length);
  document.getElementById('eqMeasBtn').textContent = meas ? 'מודד…' : (eqPositions.length?'מדוד מיקום נוסף':'מדוד מיקום (5ש\')');
  document.getElementById('eqMeasBtn').style.opacity = meas?0.5:1;
}

function targetDb(f){
  if(targetMode==='house') return Math.max(-5,Math.min(6, -1.0*Math.log2(f/250)));
  return 0;
}
function drawGEQ(c, freqs, corr){
  const x=c.getContext('2d');
  const W=c.width=c.clientWidth||360, H=160; c.height=H;
  x.clearRect(0,0,W,H);
  const mid=H/2, pad=18, scale=(H/2-pad)/9;
  const logMin=Math.log(20), logMax=Math.log(20000);
  const X=f=>((Math.log(f)-logMin)/(logMax-logMin))*W;
  x.font='9px monospace';
  [-9,-6,-3,0,3,6,9].forEach(d=>{ const yy=mid-d*scale; x.strokeStyle=d===0?'#4a5768':'#212c38';
    x.beginPath();x.moveTo(0,yy);x.lineTo(W,yy);x.stroke();
    if(d%3===0){ x.fillStyle='#8b97a5'; x.textAlign='left'; x.fillText((d>0?'+':'')+d,2,yy-2); } });
  const pts=[]; for(let k=0;k<freqs.length;k++){ if(corr[k]!=null) pts.push({x:X(freqs[k]), y:mid-corr[k]*scale}); }
  if(pts.length){
    x.beginPath(); x.moveTo(pts[0].x,mid); pts.forEach(p=>x.lineTo(p.x,p.y)); x.lineTo(pts[pts.length-1].x,mid); x.closePath();
    x.fillStyle='rgba(80,230,140,.12)'; x.fill();
    x.beginPath(); pts.forEach((p,i)=>i?x.lineTo(p.x,p.y):x.moveTo(p.x,p.y));
    x.strokeStyle='#50e68c'; x.lineWidth=2.5; x.stroke();
  }
  x.fillStyle='#8b97a5'; x.textAlign='center';
  [31.5,100,500,1000,5000,10000].forEach(f=>{ x.fillText(f>=1000?(f/1000)+'k':f, X(f), H-3); });
}
function micCalAt(f){
  if(!micCal||!micCal.f.length) return 0;
  const F=micCal.f, G=micCal.g;
  if(f<=F[0]) return G[0]; if(f>=F[F.length-1]) return G[G.length-1];
  let i=1; while(i<F.length && F[i]<f) i++;
  const t=(Math.log(f)-Math.log(F[i-1]))/(Math.log(F[i])-Math.log(F[i-1]));
  return G[i-1]+(G[i]-G[i-1])*t;
}
function loadCalStore(){
  try{
    const raw=localStorage.getItem(CAL_KEY);
    if(raw){ const o=JSON.parse(raw); micCalList=o.list||[]; activeCalId=o.active||null; }
  }catch(_){ micCalList=[]; activeCalId=null; }
  deriveActiveCal();
}
function saveCalStore(){
  try{ localStorage.setItem(CAL_KEY, JSON.stringify({list:micCalList, active:activeCalId})); }catch(_){}
}
function deriveActiveCal(){
  const c=micCalList.find(x=>x.id===activeCalId);
  micCal = c ? {f:c.f, g:c.g} : null;
  const nm = c ? ('כיול פעיל: '+c.name) : 'כיול פעיל: ללא';
  const el=document.getElementById('eqCalName'); if(el) el.textContent=nm;
}

function renderCalList(){
  const box=document.getElementById('calList');
  let html='<div class="calRow'+(activeCalId===null?' on':'')+'" data-id=""><span class="nm">ללא כיול</span></div>';
  html+=micCalList.map(c=>'<div class="calRow'+(c.id===activeCalId?' on':'')+'" data-id="'+c.id+'">'+
    '<span class="nm" title="'+c.name+'">'+c.name+'</span><span class="sub">'+c.f.length+' נק\'</span><span class="del" data-del="'+c.id+'" title="מחק">🗑</span></div>').join('');
  box.innerHTML=html;
  box.querySelectorAll('.calRow').forEach(row=>row.addEventListener('click',e=>{
    if(e.target.dataset.del!==undefined) return;
    activeCalId = row.dataset.id || null;
    deriveActiveCal(); saveCalStore(); renderCalList();
    if(eqPositions.length) computeAndShow();
  }));
  box.querySelectorAll('.del').forEach(d=>d.addEventListener('click',e=>{
    e.stopPropagation();
    const id=d.dataset.del;
    micCalList=micCalList.filter(c=>c.id!==id);
    if(activeCalId===id) activeCalId=null;
    deriveActiveCal(); saveCalStore(); renderCalList();
  }));
}

function parseCalText(text, fname){
  text=String(text||'').replace(/^\uFEFF/,'');
  const F=[],G=[];
  const numRe='([+-]?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)';
  const lineRe=new RegExp('^\s*'+numRe+'[\s,;\t]+'+numRe);
  text.split(/\r?\n/).forEach(line=>{
    const m=line.trim().match(lineRe);
    if(m){ const f=parseFloat(m[1]), g=parseFloat(m[2]);
      if(isFinite(f)&&isFinite(g)&&f>0&&f<200000) { F.push(f); G.push(g); } }
  });
  if(F.length>1){
    const id='c'+Date.now();
    micCalList.push({id, name:(fname||'כיול').replace(/\.[^.]+$/,''), f:F, g:G});
    activeCalId=id; deriveActiveCal(); saveCalStore(); renderCalList();
    if(eqPositions.length) computeAndShow();
    return true;
  }
  return false;
}
async function addCalFromFile(file){
  try{
    let text=null;
    if(file.text){ text=await file.text(); }
    if(text==null){ text=await new Promise((res,rej)=>{ const r=new FileReader();
      r.onload=()=>res(r.result); r.onerror=()=>rej(r.error); r.readAsText(file); }); }
    if(!parseCalText(text, file.name)){
      alert('לא זיהיתי נתוני כיול בקובץ.\nהפורמט הצפוי: כל שורה = תדר [רווח/טאב/פסיק] dB. לדוגמה: 1000  -1.5');
    }
  }catch(err){
    alert('לא הצלחתי לקרוא את הקובץ.\nאם הוא ב־iCloud — הורד אותו מקומית קודם, ונסה קובץ בסיומת .txt / .cal / .frd.');
  }
}
const calPanel=document.getElementById('calPanel');
document.getElementById('calBtn').addEventListener('click',()=>{ renderCalList(); showModal(calPanel); });
document.getElementById('gainBtn').addEventListener('click',()=>{ showModal(gainPanel); });
document.getElementById('gainClose').addEventListener('click',closeModals);
(function(){
  const s=document.getElementById('gainOutLvl'), v=document.getElementById('gainOutVal');
  if(s){ s.value=genDb; if(v) v.textContent=genDb+'dB';
    s.addEventListener('input',e=>{ genDb=parseInt(e.target.value,10); if(v) v.textContent=genDb+'dB';
      const gl=document.getElementById('genLvl'), gv=document.getElementById('genLvlVal'); if(gl) gl.value=genDb; if(gv) gv.textContent=genDb+'dB';
      if(genGain) genGain.gain.setTargetAtTime(Math.pow(10,genDb/20),audioCtx.currentTime,0.02);
    });
  }
})();
document.getElementById('calClose').addEventListener('click',closeModals);
document.getElementById('calAdd').addEventListener('change',e=>{ if(e.target.files[0]) addCalFromFile(e.target.files[0]); e.target.value=''; });
document.getElementById('calPasteBtn').addEventListener('click',()=>{
  const t=document.getElementById('calPaste').value;
  if(!t.trim()){ alert('הדבק קודם את תוכן הקובץ.'); return; }
  if(parseCalText(t,'כיול מודבק')) document.getElementById('calPaste').value='';
  else alert('לא זיהיתי נתונים. כל שורה צריכה להיות: תדר [רווח/טאב] dB.');
});
calPanel.addEventListener('dragover',e=>{ e.preventDefault(); calPanel.style.borderColor='var(--accent)'; });
calPanel.addEventListener('dragleave',()=>{ calPanel.style.borderColor=''; });
calPanel.addEventListener('drop',e=>{ e.preventDefault(); calPanel.style.borderColor='';
  const f=e.dataTransfer.files[0]; if(f) addCalFromFile(f); });
document.getElementById('calResetBtn').addEventListener('click',()=>{
  if(!micCalList.length){ return; }
  if(!confirm('לאפס ולמחוק את כל קבצי הכיולים?')) return;
  micCalList=[]; activeCalId=null; deriveActiveCal(); saveCalStore(); renderCalList();
});

const modalBg=document.getElementById('modalBg');
['rtPanel','eqPanel','calPanel','tfPanel','areaPanel','dlyPanel','gainPanel'].forEach(id=>{
  const p=document.getElementById(id); if(p) modalBg.appendChild(p);
});
function showModal(p){ closeModals(); p.classList.add('open'); modalBg.classList.add('show'); }
function closeModals(){
  ['rtPanel','eqPanel','calPanel','tfPanel','areaPanel','dlyPanel','gainPanel'].forEach(id=>document.getElementById(id).classList.remove('open'));
  modalBg.classList.remove('show');
}
modalBg.addEventListener('click',e=>{ if(e.target===modalBg) closeModals(); });
document.addEventListener('keydown',e=>{ if(e.key==='Escape') closeModals(); });

const areaPanel=document.getElementById('areaPanel');
document.querySelectorAll('#eqModeSwitchB button').forEach(b=>b.addEventListener('click',function(){
  if(this.dataset.go==='avg'){ showModal(eqPanel); updateEqUI(); }
}));
function openAreas(){ renderAreaList(); showModal(areaPanel); }
document.getElementById('areaClose').addEventListener('click',closeModals);
document.getElementById('areaMeasBtn').addEventListener('click',()=>pickSource(measureArea,5000));
let pendingMeasureFn=null, pendingDur=5000;
const srcOverlay=document.getElementById('srcOverlay');
function pickSource(fn, dur){
  if(!running){ alert('קודם הפעל את המיקרופון.'); return; }
  pendingMeasureFn=fn; pendingDur=dur||5000; srcOverlay.classList.add('show');
}
srcOverlay.addEventListener('click',e=>{ if(e.target===srcOverlay) srcOverlay.classList.remove('show'); });
document.querySelectorAll('#srcBox button').forEach(b=>b.addEventListener('click',function(){
  srcOverlay.classList.remove('show');
  const src=this.dataset.src; if(src==='cancel'||!pendingMeasureFn) return;
  runWithSource(src, pendingMeasureFn, pendingDur); pendingMeasureFn=null;
}));
function setGenTypeUI(kind){
  document.querySelectorAll('#genType button').forEach(x=>x.classList.toggle('on', x.dataset.t===kind));
  document.getElementById('genFreqWrap').style.display='none';
  document.getElementById('genSweepWrap').style.display = kind==='sweep'?'flex':'none';
  document.getElementById('genCompWrap').style.display = kind==='pink'?'flex':'none';
}
function runWithSource(kind, measureFn, durMs){
  durMs=durMs||5000;
  if(kind==='sweep') durMs=Math.max(durMs, genSweepDur*1000+600);   // ensure a full sweep is captured
  if(kind==='external'){ measureFn(); return; }
  const prevOn=genOn, prevType=genType;
  genType=kind; setGenTypeUI(kind); genStart();
  setTimeout(measureFn, 450);
  setTimeout(()=>{
    if(prevOn){ genType=prevType; setGenTypeUI(prevType); genStart(); }
    else genStop();
  }, 450+durMs+300);
}

document.getElementById('areaEqBtn').addEventListener('click',suggestAreaEQ);
function suggestAreaEQ(){
  if(!areas.length){ alert('מדוד לפחות אזור אחד.'); return; }
  const n=GEQ.length;
  const avg=new Array(n);
  for(let k=0;k<n;k++){ let p=0; areas.forEach(a=>p+=Math.pow(10,a.db[k]/10)); avg[k]=10*Math.log10(p/areas.length+1e-12); }
  const resp=avg.map((d,k)=> d - (micCal?micCalAt(GEQ[k]):0));
  const maxR=Math.max(...resp);
  const rel=GEQ.map((f,k)=> resp[k]>maxR-30 && f>=40 && f<=16000);
  let os=0,on=0; for(let k=0;k<n;k++){ if(rel[k]&&GEQ[k]>=200&&GEQ[k]<=4000){ os+=resp[k]-targetDb(GEQ[k]); on++; } }
  const off=on?os/on:0;
  const corr=GEQ.map((f,k)=> {
    if(!rel[k]) return null;
    const raw = -(resp[k]-targetDb(f)-off);
    const maxBoost = f > 500 ? 1.5 : 4;
    const maxCut = f > 500 ? -4 : -9;
    return Math.max(maxCut, Math.min(maxBoost, raw));
  });
  eqMarks=[]; for(let k=0;k<n;k++){ if(corr[k]!=null && Math.abs(corr[k])>=1.0) eqMarks.push({f:GEQ[k],gain:corr[k],type:corr[k]<0?'cut':'boost'}); }
  eqCurveData={freqs:GEQ.slice(), corr:corr.slice()};
  
  const cv2=document.getElementById('areaEqCanvas'); cv2.style.display='block'; drawGEQ(cv2,GEQ,corr);
  
  let html = '<div class="sub" style="margin-bottom:6px; color:var(--text); font-weight:600;">ממוצע ' + areas.length + ' אזורים · יעד ' + (targetMode==='house'?'House':'שטוח') + ':</div>';
  html += '<div class="tfGrid">';
  for(let k=0; k<GEQ.length; k++){
    const f = GEQ[k];
    const fStr = f >= 1000 ? (f / 1000) + 'k' : f + 'Hz';
    const v = corr[k];
    if(v == null || Math.abs(v) < 0.5){
      html += `<div class="tfItem off"><span class="f">${fStr}</span><span class="g">—</span></div>`;
    } else {
      const cls = v < 0 ? 'cut' : (v > 0 ? 'boost' : '');
      const sign = v > 0 ? '+' : '';
      html += `<div class="tfItem ${cls}"><span class="f">${fStr}</span><span class="g">${sign}${v.toFixed(1)}dB</span></div>`;
    }
  }
  html += '</div>';
  document.getElementById('areaEqList').innerHTML = html;
}

function updateAreaMeasBtn(){
  const b=document.getElementById('areaMeasBtn'), meas=areaState==='measuring';
  b.textContent = meas?'מודד… החזק יציב':'מדוד אזור חדש (5ש\')'; b.style.opacity=meas?.5:1;
}
function measureArea(){
  if(!running){ alert('קודם הפעל את המיקרופון.'); return; }
  if(areas.length>=4){ alert('הגעת ל־4 אזורים — מחק אחד כדי להוסיף.'); return; }
  if(areaState==='measuring') return;
  const srcData = (eqCh === 2 && floatDataRef) ? floatDataRef : floatData;
  areaAccum=new Float64Array(srcData.length); areaFrames=0; areaState='measuring';
  updateAreaMeasBtn();
  setTimeout(()=>{
    const bins=areaAccum.length, nyq=audioCtx.sampleRate/2, R6=Math.pow(2,1/6);
    const db=GEQ.map(fc=>{
      let lo=Math.floor((fc/R6)/nyq*bins), hi=Math.ceil((fc*R6)/nyq*bins);
      lo=Math.max(0,lo);hi=Math.min(bins-1,hi);if(hi<lo)hi=lo;
      let p=0; for(let i=lo;i<=hi;i++) p+=areaAccum[i]/Math.max(1,areaFrames);
      return 10*Math.log10(p+1e-12);
    });
    const idx=areas.length;
    areas.push({name:AREA_NAMES[idx], color:AREA_COLORS[idx], db, show:true});
    areaState='idle'; updateAreaMeasBtn(); renderAreaList();
  },5000);
}
function renderAreaList(){
  const box=document.getElementById('areaList');
  if(!areas.length){ box.innerHTML='<div class="sub">אין אזורים עדיין — מדוד את הראשון.</div>'; return; }
  box.innerHTML=areas.map((a,i)=>
    '<div class="areaRow"><span class="dot" style="background:'+a.color+'"></span>'+
    '<span class="nm">'+a.name+'</span>'+
    '<button data-show="'+i+'" class="'+(a.show?'on':'')+'">'+(a.show?'מוצג':'מוסתר')+'</button>'+
    '<button data-del="'+i+'">מחק</button></div>').join('');
  box.querySelectorAll('[data-show]').forEach(b=>b.addEventListener('click',()=>{
    const i=+b.dataset.show; areas[i].show=!areas[i].show; renderAreaList();
  }));
  box.querySelectorAll('[data-del]').forEach(b=>b.addEventListener('click',()=>{
    areas.splice(+b.dataset.del,1);
    areas.forEach((a,i)=>{ a.color=AREA_COLORS[i]; if(AREA_NAMES.includes(a.name)) a.name=AREA_NAMES[i]; });
    renderAreaList();
  }));
}

const tfPanel=document.getElementById('tfPanel');
document.getElementById('tfClose').addEventListener('click',closeModals);
document.getElementById('tfSwapBtn').addEventListener('click',function(){ tfSwap=!tfSwap; this.classList.toggle('on',tfSwap); });
document.getElementById('tfMeasBtn').addEventListener('click',()=>pickSource(tfMeasure,6000));
document.getElementById('tfCsvBtn').addEventListener('click',tfExportCsv);

function chLevel(arr){ let p=0; for(let i=1;i<arr.length;i++) p+=Math.pow(10,arr[i]/10); return 10*Math.log10(p+1e-12); }
function updateTfLevels(){
  if(!floatDataRef || !analyserRef) return;
  analyser.getFloatTimeDomainData(timeData);
  if(!timeDataRef || timeDataRef.length!==analyserRef.fftSize) timeDataRef=new Float32Array(analyserRef.fftSize);
  analyserRef.getFloatTimeDomainData(timeDataRef);
  setGainEl(document.getElementById('tfMicFill'), document.getElementById('tfMicDb'), levelDb(timeData,2048));
  setGainEl(document.getElementById('tfRefFill'), document.getElementById('tfRefDb'), levelDb(timeDataRef,2048));
  document.getElementById('tfL1').textContent = tfSwap?"כניסה 1 → רפרנס":"כניסה 1 → מיק'";
  document.getElementById('tfL2').textContent = tfSwap?"כניסה 2 → מיק'":"כניסה 2 → רפרנס";
}
function tfMeasure(){
  if(!running||!analyserRef){ alert('הפעל מיקרופון עם כרטיס קול (input סטריאו).'); return; }
  if(tfState==='measuring') return;
  const bins=floatData.length;
  tfMic=new Float64Array(bins); tfRef=new Float64Array(bins); tfDiffSum=new Float64Array(bins); tfDiffSq=new Float64Array(bins); tfFrames=0; tfState='measuring';
  const btn=document.getElementById('tfMeasBtn'); btn.textContent='מודד…'; btn.style.opacity=.5;
  setTimeout(()=>{
    tfState='idle'; btn.textContent='מדוד שוב (6ש\')'; btn.style.opacity=1;
    tfCompute();
  },6000);
}
function tfCompute(){
  if(!tfFrames){ return; }
  const bins=tfMic.length, nyq=audioCtx.sampleRate/2, R6=Math.pow(2,1/6);
  const H=[], refB=[]; let refMax=-999;
  for(let k=0;k<GEQ.length;k++){
    const fc=GEQ[k]; let lo=Math.floor((fc/R6)/nyq*bins), hi=Math.ceil((fc*R6)/nyq*bins);
    lo=Math.max(0,lo);hi=Math.min(bins-1,hi);if(hi<lo)hi=lo;
    let pm=0,pr=0; for(let i=lo;i<=hi;i++){ pm+=tfMic[i]; pr+=tfRef[i]; }
    const micDb=10*Math.log10(pm/tfFrames+1e-12);
    refB[k]=10*Math.log10(pr/tfFrames+1e-12);
    H[k]=micDb-refB[k];
    refMax=Math.max(refMax,refB[k]);
  }
  if(micCal){ for(let k=0;k<GEQ.length;k++) H[k]-=micCalAt(GEQ[k]); }
  const rel=GEQ.map((f,k)=> refB[k]>refMax-25 && f>=40 && f<=16000);
  let os=0,on=0;
  for(let k=0;k<GEQ.length;k++){ if(rel[k]&&GEQ[k]>=200&&GEQ[k]<=4000){ os+=H[k]-targetDb(GEQ[k]); on++; } }
  const offset=on?os/on:0;
  const corr=GEQ.map((f,k)=> {
      if(!rel[k]) return null;
      const raw = -(H[k]-targetDb(f)-offset);
      const maxBoost = f > 500 ? 1.5 : 4;
      const maxCut = f > 500 ? -4 : -9;
      return Math.max(maxCut, Math.min(maxBoost, raw));
  });
  tfResult={corr,H,rel};
  document.getElementById('tfInfo').textContent = on? 'הזז בגרפיק־EQ לפי הערכים (±6dB מקס). מוצגים רק פסים אמינים עם תיקון משמעותי.' :
    'רפרנס חלש/חסר — ודא שערוץ 2 מקבל אות מהמיקסר, או לחץ "החלף ערוצים".';
  renderTFList();
}

function renderTFList(){
  const box = document.getElementById('tfGeqList');
  const cv2 = document.getElementById('tfCanvas');
  if(!tfResult){ box.innerHTML = ''; cv2.style.display = 'none'; return; }
  
  cv2.style.display = 'block'; 
  drawGEQ(cv2, GEQ, tfResult.corr);
  eqCurveData = { freqs: GEQ.slice(), corr: tfResult.corr.slice() };

  if(tfMode==='param'){
    const list=paramFromCorr(tfResult.corr);
    let html='<div class="sub" style="margin-bottom:6px;color:var(--text);font-weight:600;">EQ פרמטרי (יעד '+(targetMode==='house'?'House':'שטוח')+'):</div>';
    if(list.length){
      html+=list.map(s=>{
        const f=s.f>=1000?(s.f/1000).toFixed(2)+'kHz':Math.round(s.f)+'Hz';
        const g=(s.gain>0?'+':'')+s.gain.toFixed(1)+'dB';
        return '<div class="eqRow '+s.type+'"><span class="f">'+f+'</span><span class="g">'+g+'</span><span class="q">Q '+s.q.toFixed(1)+'</span></div>';
      }).join('');
    } else html+='<div class="sub">מאוזן 👌</div>';
    box.innerHTML=html;
    return;
  }

  let html = '<div class="sub" style="margin-bottom:6px; color:var(--text); font-weight:600;">ערכי תיקון לגרפיק-EQ (31 פסים):</div>';
  html += '<div class="tfGrid">';

  for(let k = 0; k < GEQ.length; k++){
    const f = GEQ[k];
    const fStr = f >= 1000 ? (f / 1000) + 'k' : f + 'Hz';
    const v = tfResult.corr[k];

    if(v == null || !tfResult.rel[k]){
      html += `<div class="tfItem off">
                <span class="f">${fStr}</span>
                <span class="g">—</span>
               </div>`;
    } else {
      const cls = v < 0 ? 'cut' : (v > 0 ? 'boost' : '');
      const sign = v > 0 ? '+' : '';
      html += `<div class="tfItem ${cls}">
                <span class="f">${fStr}</span>
                <span class="g">${sign}${v.toFixed(1)}dB</span>
               </div>`;
    }
  }
  
  html += '</div>';
  box.innerHTML = html;
}

function tfExportCsv(){
  if(!tfResult){ alert('קודם מדוד.'); return; }
  let rows='freq_hz,geq_correction_db,measured_db\n';
  GEQ.forEach((f,k)=> rows+=f+','+(tfResult.corr[k]==null?'':tfResult.corr[k].toFixed(1))+','+tfResult.H[k].toFixed(1)+'\n');
  download('tf_geq_'+stamp()+'.csv', URL.createObjectURL(new Blob([rows],{type:'text/csv'})));
}

const dlyPanel=document.getElementById('dlyPanel');
document.getElementById('dlyBtn').addEventListener('click',()=>{ showModal(dlyPanel); });
document.getElementById('dlyClose').addEventListener('click',closeModals);
function resetDelay(){
  dlyState='idle';
  dlySpeakers.forEach((s,i)=>{ s.ms=null; s.name='רמקול '+(i+1); });
  dlyAnchor=0;
  const st=document.getElementById('dlyStatus'); if(st) st.textContent='—';
  renderDlySpk();
}
document.getElementById('dlyReset').addEventListener('click',resetDelay);
document.getElementById('dlyMeasBtn').addEventListener('click',()=>pickSource(measureDelay,2100));

function fft(re,im,inv){
  const n=re.length;
  for(let i=1,j=0;i<n;i++){ let bit=n>>1; for(;j&bit;bit>>=1) j^=bit; j^=bit;
    if(i<j){ const tr=re[i];re[i]=re[j];re[j]=tr; const ti=im[i];im[i]=im[j];im[j]=ti; } }
  for(let len=2;len<=n;len<<=1){
    const ang=(inv?2:-2)*Math.PI/len, wr=Math.cos(ang), wi=Math.sin(ang);
    for(let i=0;i<n;i+=len){ let cwr=1,cwi=0;
      for(let k=0;k<len/2;k++){
        const a=i+k, b=i+k+len/2;
        const vr=re[b]*cwr-im[b]*cwi, vi=re[b]*cwi+im[b]*cwr;
        re[b]=re[a]-vr; im[b]=im[a]-vi; re[a]+=vr; im[a]+=vi;
        const t=cwr*wr-cwi*wi; cwi=cwr*wi+cwi*wr; cwr=t;
      }
    }
  }
  if(inv){ for(let i=0;i<n;i++){ re[i]/=n; im[i]/=n; } }
}

let dlyState='idle', timeDataRef=null;
document.querySelectorAll('#meterModeSeg button').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#meterModeSeg button').forEach(x=>x.classList.remove('on'));
  this.classList.add('on'); meterMode=this.dataset.m;
}));
function levelDb(buf,n){
  const len=buf.length; n=n||len; const start=Math.max(0,len-n);   // most-recent n samples
  if(meterMode==='peak'){ let m=0; for(let i=start;i<len;i++){ const a=Math.abs(buf[i]); if(a>m)m=a; } return 20*Math.log10(m+1e-9); }
  let s=0; for(let i=start;i<len;i++){ const v=buf[i]; s+=v*v; } return 20*Math.log10(Math.sqrt(s/(len-start))+1e-9);
}
function peakDb(buf){ let m=0; for(let i=0;i<buf.length;i++){ const a=Math.abs(buf[i]); if(a>m)m=a; } return 20*Math.log10(m+1e-9); }
function gainClass(db){
  if(db>=-1) return ['clip','קליפ!'];
  if(db>=-8) return ['hi','חזק ('+db.toFixed(0)+')'];
  if(db>=-40) return ['ok','טוב ('+db.toFixed(0)+')'];
  return ['lo','חלש ('+db.toFixed(0)+')'];
}
function setGainEl(fill,lbl,db){
  let s=db;
  if(fill){
    s=fill._sdb; if(s==null||!isFinite(s)) s=db;
    s += (db>s ? 0.55 : 0.035) * (db - s);   // same attack/release as the main meter
    fill._sdb=s;
    fill.style.width=Math.max(2,Math.min(100,(s+60)/60*100))+'%';
  }
  const [cls,txt]=gainClass(s);
  if(fill) fill.className='fill '+cls;
  if(lbl){ lbl.className='gainLbl '+cls; lbl.textContent=txt; }
}
function setGain(id, db){ setGainEl(document.getElementById(id+'Fill'), document.getElementById(id+'Gain'), db); }

function measureDelay(){ runDelayCapture(document.getElementById('dlyMeasBtn'), (res)=>{
  const st=document.getElementById('dlyStatus');
  if(res==null){ st.textContent='לא הצלחתי — ודא שמנגן אות רחב־פס ושכניסה 2 מקבלת רפרנס.'; return; }
  const ms=res.ms, dist=Math.abs(ms)/1000*343;
  st.innerHTML='דיליי ≈ <b>'+ms.toFixed(2)+' ms</b><br><span style="font-size:11px;color:var(--dim)">≈ '+dist.toFixed(2)+' מ\' · '+(ms>=0?'המיק\' מאחר אחרי הרפרנס':'המיק\' מקדים את הרפרנס')+'</span>';
}); }
function runDelayCapture(btn, cb){
  if(!running||!analyserRef||!source){ alert('צריך כרטיס קול עם input סטריאו (מיק\'+רפרנס).'); return; }
  if(dlyState==='measuring') return;
  dlyState='measuring';
  const prevTxt=btn.textContent; btn.textContent='מקליט…'; btn.style.opacity=.5;
  const sr=audioCtx.sampleRate;
  const captureSec = (genOn && genType==='sweep') ? Math.min(10, genSweepDur+0.6) : 2.0;   // cover a full sweep if used
  const want=Math.floor(sr*captureSec);
  const mic=new Float32Array(want), ref=new Float32Array(want); let pos=0;
  let workletNode;
  try {
    workletNode = new AudioWorkletNode(audioCtx, 'recorder-worklet');
  } catch(e) {
    alert('AudioWorklet לא נטען. פתח את האתר דרך שרת (למשל Live Server ב-VSCode) ולא כקובץ מתיקייה.');
    dlyState='idle'; btn.textContent=prevTxt; btn.style.opacity=1;
    return;
  }

  const mute=audioCtx.createGain(); mute.gain.value=0;
  source.connect(workletNode); workletNode.connect(mute); mute.connect(audioCtx.destination);
  
  workletNode.port.onmessage = e => {
    if (pos >= want) return;
    const c0 = e.data.mic, c1 = e.data.ref;
    const len = Math.min(c0.length, want - pos);
    for(let i=0; i<len; i++) { mic[pos]=c0[i]; ref[pos]=c1[i]; pos++; }
  };
  workletNode.port.postMessage({ cmd: 'start' });

  setTimeout(()=>{
    workletNode.port.postMessage({ cmd: 'stop' });
    try{ source.disconnect(workletNode); }catch(_){} try{ workletNode.disconnect(); }catch(_){} try{ mute.disconnect(); }catch(_){}
    dlyState='idle'; btn.textContent=prevTxt; btn.style.opacity=1;
    const m = tfSwap? ref: mic, r = tfSwap? mic: ref;
    cb(computeDelay(r, m, sr));
  }, captureSec*1000+100);
}
// multi-speaker alignment (2/4/6), align to a chosen anchor
let dlySpeakers=[{name:'רמקול 1',ms:null},{name:'רמקול 2',ms:null}];
let dlyAnchor=0;
function setDlyCount(n){
  const cur=dlySpeakers.length;
  if(n>cur){ for(let i=cur;i<n;i++) dlySpeakers.push({name:'רמקול '+(i+1),ms:null}); }
  else if(n<cur){ dlySpeakers=dlySpeakers.slice(0,n); if(dlyAnchor>=n) dlyAnchor=0; }
  renderDlySpk();
}
function renderDlySpk(){
  const box=document.getElementById('dlySpk'); if(!box) return;
  box.innerHTML=dlySpeakers.map((s,i)=>{
    let add='—';
    if(s.ms!=null && dlySpeakers[dlyAnchor] && dlySpeakers[dlyAnchor].ms!=null){
      if(i===dlyAnchor) add='<span style="color:var(--accent)">עוגן</span>';
      else{ const d=dlySpeakers[dlyAnchor].ms - s.ms;
        add = d>=0 ? '<b style="color:var(--accent)">+'+d.toFixed(2)+' ms</b>'
                   : '<span style="color:var(--warn)">'+d.toFixed(2)+' ms (מאוחר מהעוגן)</span>'; }
    }
    return '<div class="calRow" style="gap:6px">'+
      '<span class="dlyAnchor" data-a="'+i+'" title="בחר כעוגן" style="cursor:pointer;font-size:15px;color:'+(i===dlyAnchor?'var(--accent)':'var(--dim)')+'">'+(i===dlyAnchor?'◉':'◎')+'</span>'+
      '<input class="posName" data-i="'+i+'" value="'+(s.name||('רמקול '+(i+1))).replace(/"/g,'&quot;')+'" style="flex:1">'+
      '<span style="min-width:64px;font-size:11px;color:var(--dim)">'+(s.ms==null?'—':s.ms.toFixed(2)+'ms')+'</span>'+
      '<button class="toggle dlyMeasOne" data-i="'+i+'" style="padding:6px 10px;font-size:11px">מדוד</button>'+
      '<span style="min-width:74px;font-size:11px;text-align:end">'+add+'</span>'+
      '</div>';
  }).join('');
  box.querySelectorAll('.dlyAnchor').forEach(a=>a.addEventListener('click',function(){ dlyAnchor=+this.dataset.a; renderDlySpk(); }));
  box.querySelectorAll('.posName').forEach(inp=>inp.addEventListener('change',function(){ const i=+this.dataset.i; if(dlySpeakers[i]) dlySpeakers[i].name=this.value; }));
  box.querySelectorAll('.dlyMeasOne').forEach(b=>b.addEventListener('click',function(){
    const i=+this.dataset.i, btn=this;
    pickSource(()=>runDelayCapture(btn,(res)=>{
      if(res==null){ btn.textContent='נכשל'; setTimeout(()=>btn.textContent='מדוד',1500); return; }
      dlySpeakers[i].ms=res.ms; renderDlySpk();
    }),2100);
  }));
}
document.querySelectorAll('#dlyCountSeg button').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#dlyCountSeg button').forEach(x=>x.classList.remove('on'));
  this.classList.add('on'); setDlyCount(+this.dataset.n);
}));
renderDlySpk();

function computeDelay(ref, mic, sr){
  const L = Math.min(ref.length, mic.length);
  const chunkSize = 8192;
  const hopSize = 4096;
  if(L < chunkSize) return null;

  const numChunks = Math.floor((L - chunkSize) / hopSize) + 1;
  if(numChunks < 1) return null;

  const avgRr = new Float64Array(chunkSize);
  const avgRi = new Float64Array(chunkSize);
  const xr = new Float64Array(chunkSize);
  const xi = new Float64Array(chunkSize);
  const yr = new Float64Array(chunkSize);
  const yi = new Float64Array(chunkSize);

  const win = new Float32Array(chunkSize);
  for(let i = 0; i < chunkSize; i++){
    win[i] = 0.5 * (1 - Math.cos((2 * Math.PI * i) / (chunkSize - 1)));
  }

  let validChunks = 0;
  for(let c = 0; c < numChunks; c++){
    const offset = c * hopSize;
    let eRef = 0, eMic = 0;

    for(let i = 0; i < chunkSize; i++){
      const rVal = ref[offset + i] * win[i];
      const mVal = mic[offset + i] * win[i];
      xr[i] = rVal; xi[i] = 0;
      yr[i] = mVal; yi[i] = 0;
      eRef += rVal * rVal;
      eMic += mVal * mVal;
    }

    if(eRef < 1e-7 || eMic < 1e-7) continue;

    fft(xr, xi, false);
    fft(yr, yi, false);

    for(let k = 0; k < chunkSize; k++){
      const cr = yr[k] * xr[k] + yi[k] * xi[k];
      const ci = yi[k] * xr[k] - yr[k] * xi[k];
      const mag = Math.hypot(cr, ci) + 1e-9;
      avgRr[k] += cr / mag;
      avgRi[k] += ci / mag;
    }
    validChunks++;
  }

  if(validChunks === 0) return null;

  for(let k = 0; k < chunkSize; k++){
    avgRr[k] /= validChunks;
    avgRi[k] /= validChunks;
  }

  fft(avgRr, avgRi, true);

  let best = -1e9, bi = 0;
  for(let k = 0; k < chunkSize; k++){
    if(avgRr[k] > best){
      best = avgRr[k];
      bi = k;
    }
  }

  let lag = bi;
  if(lag > chunkSize / 2) lag -= chunkSize;

  return { ms: (lag / sr) * 1000, samples: lag };
}

function measurePosition(){
  if(!running){ alert('קודם הפעל את המיקרופון.'); return; }
  if(measState==='measuring') return;
  const srcData = (eqCh === 2 && floatDataRef) ? floatDataRef : floatData;
  measAccum=new Float64Array(srcData.length); measFrames=0; measState='measuring';
  updateEqUI();
  setTimeout(()=>{
    const bins=measAccum.length, bd=new Float32Array(bins);
    for(let i=0;i<bins;i++) bd[i]=10*Math.log10(measAccum[i]/Math.max(1,measFrames)+1e-12);
    eqPositions.push({name:'מיקום '+(eqPositions.length+1), data:bd}); measState='idle';
    computeAndShow(); updateEqUI(); renderEqList();
  },5000);
}
function renderEqList(){
  const box=document.getElementById('eqPosList'); if(!box) return;
  if(!eqPositions.length){ box.innerHTML=''; return; }
  box.innerHTML=eqPositions.map((p,i)=>
    '<div class="calRow"><input class="posName" data-i="'+i+'" value="'+(p.name||('מיקום '+(i+1))).replace(/"/g,'&quot;')+'">'+
    '<span class="del" data-del="'+i+'" title="מחק מיקום">🗑</span></div>').join('');
  box.querySelectorAll('.posName').forEach(inp=>inp.addEventListener('change',function(){
    const i=+this.dataset.i; if(eqPositions[i]) eqPositions[i].name=this.value; }));
  box.querySelectorAll('[data-del]').forEach(b=>b.addEventListener('click',function(){
    const i=+this.dataset.del; eqPositions.splice(i,1);
    if(eqPositions.length) computeAndShow(); else { eqMarks=null; eqCurveData=null; document.getElementById('eqList').innerHTML=''; document.getElementById('eqCurveCanvas').style.display='none'; }
    updateEqUI(); renderEqList();
  }));
}
function avgPositions(){
  const bins=eqPositions[0].data.length, out=new Float32Array(bins);
  for(let i=0;i<bins;i++){ let p=0; for(const pos of eqPositions) p+=Math.pow(10,pos.data[i]/10); out[i]=10*Math.log10(p/eqPositions.length+1e-12); }
  return out;
}
function bandDbFromBins(bd,fLo,fHi,nyq,bins){
  let lo=Math.floor(fLo/nyq*bins), hi=Math.ceil(fHi/nyq*bins);
  lo=Math.max(0,lo);hi=Math.min(bins-1,hi);if(hi<lo)hi=lo;
  let p=0; for(let i=lo;i<=hi;i++) p+=Math.pow(10,bd[i]/10);
  return 10*Math.log10(p+1e-12);
}
function computeAndShow(){
  if(!eqPositions.length){ alert('מדוד לפחות מיקום אחד.'); return; }
  const binDb=avgPositions();
  const nyq=audioCtx.sampleRate/2, bins=binDb.length, R6=Math.pow(2,1/6);
  if(micCal){ for(let i=0;i<bins;i++) binDb[i]-=micCalAt(i*nyq/bins); }
  const resp=GEQ.map(fc=> bandDbFromBins(binDb,fc/R6,fc*R6,nyq,bins));
  const maxR=Math.max(...resp);
  const rel=GEQ.map((f,k)=> resp[k]>maxR-30 && f>=40 && f<=16000);
  let os=0,on=0; for(let k=0;k<GEQ.length;k++){ if(rel[k]&&GEQ[k]>=200&&GEQ[k]<=4000){ os+=resp[k]-targetDb(GEQ[k]); on++; } }
  const off=on?os/on:0;
  const corr=GEQ.map((f,k)=> {
    if(!rel[k]) return null;
    const raw = -(resp[k]-targetDb(f)-off);
    const maxBoost = f > 500 ? 1.5 : 4;
    const maxCut = f > 500 ? -4 : -9;
    return Math.max(maxCut, Math.min(maxBoost, raw));
  });
  eqCurveData={freqs:GEQ.slice(), corr:corr.slice()};
  document.getElementById('eqCurveCanvas').style.display='none';
  lastEqCorr=corr;
  renderEqResult();
  showModal(eqPanel);
}
function paramFromCorr(corr){
  const cand=[];
  for(let k=1;k<GEQ.length-1;k++){ const v=corr[k], pv=corr[k-1], nv=corr[k+1];
    if(v==null||pv==null||nv==null) continue;
    const isMax=v>=pv&&v>nv&&v>1, isMin=v<=pv&&v<nv&&v<-1; if(!isMax&&!isMin) continue;
    const half=v/2; let li=k,ri=k;
    if(isMax){ while(li>0&&corr[li]!=null&&corr[li]>half)li--; while(ri<GEQ.length-1&&corr[ri]!=null&&corr[ri]>half)ri++; }
    else     { while(li>0&&corr[li]!=null&&corr[li]<half)li--; while(ri<GEQ.length-1&&corr[ri]!=null&&corr[ri]<half)ri++; }
    const q=Math.max(0.7,Math.min(8, GEQ[k]/Math.max(1,(GEQ[Math.min(GEQ.length-1,ri)]-GEQ[Math.max(0,li)]))));
    cand.push({f:GEQ[k],gain:v,q,type:v<0?'cut':'boost',prom:Math.abs(v)});
  }
  cand.sort((a,b)=>b.prom-a.prom);
  const picked=[]; cand.forEach(c=>{ if(!picked.some(p=>Math.abs(Math.log2(p.f/c.f))<0.66)) picked.push(c); });
  return picked.slice(0,6).sort((a,b)=>a.f-b.f);
}

function renderEqResult(){
  if(!lastEqCorr){ return; }
  const head='<div class="sub" style="margin-bottom:6px; color:var(--text); font-weight:600;">יעד '+(targetMode==='house'?'House':'שטוח')+
    (micCal?' · כיול פעיל':' · ללא כיול')+' · '+eqPositions.length+' מיקומים (' + (eqCh===2?'כניסה 2':'כניסה 1') + '):</div>';
  const box=document.getElementById('eqList');
  if(eqMode==='graphic'){
    let html = head + '<div class="tfGrid">';
    for(let k=0; k<GEQ.length; k++){
      const f = GEQ[k];
      const fStr = f >= 1000 ? (f / 1000) + 'k' : f + 'Hz';
      const v = lastEqCorr[k];
      if(v == null || Math.abs(v) < 0.5){
        html += `<div class="tfItem off"><span class="f">${fStr}</span><span class="g">—</span></div>`;
      } else {
        const cls = v < 0 ? 'cut' : (v > 0 ? 'boost' : '');
        const sign = v > 0 ? '+' : '';
        html += `<div class="tfItem ${cls}"><span class="f">${fStr}</span><span class="g">${sign}${v.toFixed(1)}dB</span></div>`;
      }
    }
    html += '</div>';
    box.innerHTML = html;
  } else {
    const list=paramFromCorr(lastEqCorr);
    let html = head;
    if(list.length){
      html += list.map(s=>{
        const f=s.f>=1000?(s.f/1000).toFixed(2)+'kHz':Math.round(s.f)+'Hz';
        const g=(s.gain>0?'+':'')+s.gain.toFixed(1)+'dB';
        return '<div class="eqRow '+s.type+'"><span class="f">'+f+'</span><span class="g">'+g+'</span><span class="q">Q '+s.q.toFixed(1)+'</span></div>';
      }).join('');
    } else {
      html += '<div class="sub">מאוזן 👌</div>';
    }
    box.innerHTML = html;
  }
}

const rtPanel=document.getElementById('rtPanel'), rtStatus=document.getElementById('rtStatus');
document.getElementById('rtClose').addEventListener('click',closeModals);
document.getElementById('rtRange').addEventListener('input',e=>{
  rtRange=parseFloat(e.target.value);
  document.getElementById('rtRangeVal').textContent=rtRange+'dB';
  if(rt60Samples.length) analyzeRT60();
});
document.getElementById('rtLevel').addEventListener('input',e=>{
  rtLevel=parseInt(e.target.value,10);
  document.getElementById('rtLevelVal').textContent=rtLevel+'dB';
});
document.getElementById('rtRunBtn').addEventListener('click',startRT60);
document.getElementById('rtBtn').addEventListener('click',()=>{
  if(!running||!audioCtx){ alert('קודם הפעל את המיקרופון.'); return; }
  showModal(rtPanel);
  rtStatus.innerHTML='כוונן עוצמה, ואז לחץ "התחל מדידה".';
});
function startRT60(){
  if(!running||!audioCtx){ alert('קודם הפעל את המיקרופון.'); return; }
  if(rt60State==='capture') return;
  rtStatus.innerHTML='מכין… משמיע רעש ורוד';
  const prevGenOn = genOn;
  const restoreType=genType; genType='pink';
  if(!genOn){ genStart(); }
  const boost=rtLevel;   // RT60 playback level (user-set; needs a strong steady state)
  if(genGain) genGain.gain.setTargetAtTime(Math.pow(10,boost/20),audioCtx.currentTime,0.1);
  const prevSmooth=analyser.smoothingTimeConstant; analyser.smoothingTimeConstant=0;  // no smearing of the decay

  setTimeout(()=>{
    rtStatus.innerHTML='מודד דעיכה…';
    rt60Samples=[]; rt60State='capture';
    const nyq=audioCtx.sampleRate/2;
    const bandEdges=RT_BANDS.map(fc=>{ const bins=floatData.length;
      let lo=Math.floor((fc/1.4142)/nyq*bins), hi=Math.ceil((fc*1.4142)/nyq*bins);
      return [Math.max(0,lo),Math.min(bins-1,hi)]; });
    // dedicated high-rate sampler (~100/s), independent of the 30fps draw cap — captures fast decays cleanly
    if(rt60Timer) clearInterval(rt60Timer);
    rt60Timer=setInterval(()=>{
      if(rt60State!=='capture' || !analyser) return;
      analyser.getFloatTimeDomainData(timeData);
      let s2=0, N=Math.min(2048,timeData.length);
      for(let i=timeData.length-N;i<timeData.length;i++){ const v=timeData[i]; s2+=v*v; }
      analyser.getFloatFrequencyData(floatData);
      const bands=bandEdges.map(([lo,hi])=>{ let p=0; for(let i=lo;i<=hi;i++) p+=Math.pow(10,floatData[i]/10); return 10*Math.log10(p+1e-12); });
      rt60Samples.push({t:performance.now(), db:20*Math.log10(Math.sqrt(s2/N)+1e-9), bands});
    },10);
    setTimeout(()=>{
      const t=audioCtx.currentTime;
      if(genGain){ try{ genGain.gain.cancelScheduledValues(t);
        genGain.gain.setValueAtTime(genGain.gain.value,t);
        genGain.gain.linearRampToValueAtTime(0,t+0.005);}catch(_){} }
      rt60CutT=performance.now();
      setTimeout(()=>{
        rt60State='idle'; 
        if(rt60Timer){ clearInterval(rt60Timer); rt60Timer=null; }
        analyser.smoothingTimeConstant=prevSmooth;
        if(!prevGenOn) genStop(); 
        genType=restoreType;
        analyzeRT60();
      },2500);
    },400);
  },1200);
}

const RT_BANDS=[125,250,500,1000,2000,4000];
// analyze one decay series → {rt60, span} or null
function analyzeDecay(series, cutT, needRange){
  const pre=series.filter(x=>x.t<cutT);
  const steady = pre.length? pre.reduce((a,x)=>a+x.db,0)/pre.length : Math.max(...series.map(x=>x.db));
  const post=series.filter(x=>x.t>=cutT).map(x=>({t:(x.t-cutT)/1000, db:x.db}));
  if(post.length<10) return null;
  const tail=post.slice(-Math.max(5,Math.floor(post.length*0.25)));
  const noise=tail.reduce((a,x)=>a+x.db,0)/tail.length;
  const hi=steady-5, lo=noise+5;
  const reg=post.filter(x=>x.db<=hi && x.db>=lo);
  if(reg.length<5 || (hi-lo)<Math.min(8,needRange)) return {rt60:null, span:hi-lo, steady, noise, post};
  let n=reg.length, st=0,sd=0,std=0,stt=0;
  reg.forEach(p=>{ st+=p.t; sd+=p.db; std+=p.t*p.db; stt+=p.t*p.t; });
  const slope=(n*std - st*sd)/(n*stt - st*st);
  const intercept=(sd - slope*st)/n;
  const rt60=-60/slope;
  return { rt60:(slope<0 && rt60>0.05 && rt60<10)?rt60:null, span:hi-lo, steady, noise, post, slope, intercept };
}
function analyzeRT60(){
  const s=rt60Samples;
  if(s.length<20){ rtStatus.innerHTML='מדידה נכשלה — נדגמו רק '+s.length+' דגימות.<br><span style="font-size:11px;color:var(--dim)">ודא שהמיקרופון פעיל ונסה שוב.</span>'; return; }
  const bb=analyzeDecay(s.map(x=>({t:x.t,db:x.db})), rt60CutT, rtRange);
  if(!bb || bb.post.length<10){ rtStatus.innerHTML='מדידה נכשלה — לא נלכדה דעיכה.'; return; }
  // per-octave-band RT60
  let bandsHtml='';
  if(s[0].bands){
    bandsHtml='<div class="tfGrid" style="margin-top:8px">';
    RT_BANDS.forEach((fc,bi)=>{
      const series=s.map(x=>({t:x.t, db:x.bands[bi]}));
      const r=analyzeDecay(series, rt60CutT, rtRange);
      const fStr=fc>=1000?(fc/1000)+'k':fc+'';
      const val=(r&&r.rt60)?r.rt60.toFixed(2)+'ש\'':'—';
      const cls=(r&&r.rt60)?(r.rt60>0.8?'cut':(r.rt60<0.3?'off':'boost')):'off';
      bandsHtml+='<div class="tfItem '+cls+'"><span class="f">'+fStr+'Hz</span><span class="g">'+val+'</span></div>';
    });
    bandsHtml+='</div>';
  }
  if(bb.rt60){
    const approx=bb.span<rtRange;
    rtStatus.innerHTML='RT60 ≈ <b>'+bb.rt60.toFixed(2)+' ש\'</b> <span style="font-size:11px;color:var(--dim)">(רחב־פס · טווח '+bb.span.toFixed(0)+'dB)</span>'+
      (approx?'<br><span style="font-size:10px;color:var(--warn)">משוער — טווח דעיכה קטן</span>':'')+bandsHtml;
    drawRTPlot(bb.post, bb.steady, bb.slope, bb.intercept);
  } else {
    rtStatus.innerHTML='אין דעיכה רחב־פס למדוד ('+(bb.span>0?bb.span.toFixed(0):'0')+'dB).'+
      '<br><span style="font-size:11px;color:var(--dim)">רמת אות: '+bb.steady.toFixed(0)+'dB · רעש רקע: '+bb.noise.toFixed(0)+'dB.<br>'+
      (bb.steady-bb.noise<15?'העלה עוצמת PA (האות קרוב מדי לרעש הרקע).':'הורד "טווח דעיכה נדרש".')+'</span>'+bandsHtml;
    drawRTPlot(bb.post, bb.steady, null, 0);
  }
}
function analyzeRT60_OLD(){
  const s=rt60Samples;
  if(s.length<20){ rtStatus.innerHTML='מדידה נכשלה — נדגמו רק '+s.length+' דגימות.<br><span style="font-size:11px;color:var(--dim)">ודא שהמיקרופון פעיל ונסה שוב.</span>'; return; }
  const pre=s.filter(x=>x.t<rt60CutT);
  const steady = pre.length? pre.reduce((a,x)=>a+x.db,0)/pre.length : Math.max(...s.map(x=>x.db));
  const post=s.filter(x=>x.t>=rt60CutT).map(x=>({t:(x.t-rt60CutT)/1000, db:x.db}));
  if(post.length<10){ rtStatus.innerHTML='מדידה נכשלה — לא נלכדה דעיכה ('+post.length+' דגימות אחרי הניתוק).'; return; }
  const tail=post.slice(-Math.max(5,Math.floor(post.length*0.25)));
  const noise=tail.reduce((a,x)=>a+x.db,0)/tail.length;
  const hi=steady-5, lo=noise+5;
  const reg=post.filter(x=>x.db<=hi && x.db>=lo);
  const needRange=rtRange;
  if(reg.length<5 || (hi-lo)<Math.min(8,needRange)){
    rtStatus.innerHTML='אין דעיכה למדוד ('+(hi-lo>0?(hi-lo).toFixed(0):'0')+'dB בלבד).'+
      '<br><span style="font-size:11px;color:var(--dim)">רמת אות: '+steady.toFixed(0)+'dB · רעש רקע: '+noise.toFixed(0)+'dB.<br>'+
      (steady-noise<15?'העלה עוצמת PA (האות קרוב מדי לרעש הרקע).':'הורד "טווח דעיכה נדרש".')+'</span>';
    drawRTPlot(post, steady, null, 0); return;
  }
  let n=reg.length, st=0,sd=0,std=0,stt=0;
  reg.forEach(p=>{ st+=p.t; sd+=p.db; std+=p.t*p.db; stt+=p.t*p.t; });
  const slope=(n*std - st*sd)/(n*stt - st*st);
  const intercept=(sd - slope*st)/n;
  const rt60 = -60/slope;
  drawRTPlot(post, steady, slope, intercept);
  const approx = (hi-lo) < needRange;
  if(slope<0 && rt60>0.05 && rt60<10)
    rtStatus.innerHTML='RT60 ≈ <b>'+rt60.toFixed(2)+' ש\'</b>'+
      (approx?' <span style="font-size:11px;color:var(--warn)">(משוער · טווח '+(hi-lo).toFixed(0)+'dB)</span>':
              ' <span style="font-size:11px;color:var(--dim)">(טווח '+(hi-lo).toFixed(0)+'dB)</span>');
  else
    rtStatus.innerHTML='לא הצלחתי למדוד — נסה עוצמה גבוהה יותר';
}
function drawRTPlot(post, steady, slope, intercept){
  const c=document.getElementById('rtCanvas'); if(!c) return;
  const x=c.getContext('2d');
  const W=c.width, H=c.height; x.clearRect(0,0,W,H);
  const tMax=Math.max(0.5, post.length?post[post.length-1].t:1);
  const dbMin=steady-65, dbMax=steady+3;
  const X=t=>t/tMax*W, Y=db=>H-(db-dbMin)/(dbMax-dbMin)*H;
  x.strokeStyle='#2b3646'; x.fillStyle='#8b97a5'; x.font='9px monospace';
  for(let d=0;d>=-60;d-=10){ const yy=Y(steady+d); x.globalAlpha=.5;
    x.beginPath();x.moveTo(0,yy);x.lineTo(W,yy);x.stroke(); x.globalAlpha=1; x.fillText(d+'dB',2,yy-2); }
  x.strokeStyle='#2f9bff'; x.lineWidth=1.5; x.beginPath();
  post.forEach((p,i)=>{ i?x.lineTo(X(p.t),Y(p.db)):x.moveTo(X(p.t),Y(p.db)); }); x.stroke();
  if(slope!=null){
    x.strokeStyle='#50e68c'; x.lineWidth=2; x.setLineDash([5,3]); x.beginPath();
    x.moveTo(X(0),Y(intercept)); x.lineTo(X(tMax),Y(intercept+slope*tMax)); x.stroke(); x.setLineDash([]);
  }
}
document.getElementById('res').addEventListener('input',e=>{
  const bpo=Math.max(3,Math.min(24,parseInt(e.target.value,10)));
  document.getElementById('resVal').textContent='1/'+bpo+' אוקטבה';
  buildBands(bpo);
});
function setFft(n){
  fftSize=n;
  if(analyser){
    analyser.fftSize=n; analyserRef.fftSize=n;
    floatData=new Float32Array(analyser.frequencyBinCount);
    floatDataRef=new Float32Array(analyserRef.frequencyBinCount);
    timeData=new Float32Array(analyser.fftSize);
    timeDataRef=new Float32Array(analyserRef.fftSize);
    _pfx=null;
  }
}
document.querySelectorAll('#fftSeg button').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#fftSeg button').forEach(x=>x.classList.remove('on'));
  this.classList.add('on'); setFft(parseInt(this.dataset.n,10));
}));
document.getElementById('mRta').addEventListener('click',()=>setMode('rta'));
document.getElementById('mSpec').addEventListener('click',()=>setMode('spec'));
document.getElementById('startBtn').addEventListener('click',()=>start());
document.getElementById('stopBtn').addEventListener('click',resetSession);
function resetSession(){
  if(audioCtx && audioCtx.state==='suspended') audioCtx.resume();
  const tr = stream && stream.getAudioTracks && stream.getAudioTracks()[0];
  if(running && (!tr || tr.readyState==='ended')){ stop(); start(); return; }
  peaks.fill(0); avgBuf.fill(0); snapCurve=null;
  const fz=document.getElementById('freezeBtn'); fz.classList.remove('on'); fz.textContent='הקפא';
  eqPositions=[]; eqMarks=null; eqCurveData=null; lastEqCorr=null;
  { const pl=document.getElementById('eqPosList'); if(pl) pl.innerHTML=''; const el=document.getElementById('eqList'); if(el) el.innerHTML=''; }
  document.getElementById('eqList').innerHTML=''; document.getElementById('eqCurveCanvas').style.display='none';
  updateEqUI();
  areas=[]; renderAreaList();
  document.getElementById('areaEqCanvas').style.display='none';
  document.getElementById('areaEqList').innerHTML='';
  tfResult=null; document.getElementById('tfGeqList').innerHTML='';
  document.getElementById('tfCanvas').style.display='none';
  resetDelay();
  fbTrack.clear(); fbPanel.innerHTML='';
  leqSumP=0; leqN=0; splMax=-120; lvlPeak=-120;
  targetMode='flat'; document.querySelectorAll('.tgtSeg button').forEach(b=>b.classList.toggle('on', b.dataset.t==='flat'));
  pinkComp=false; compChoice=true; syncPinkComp();
  weightMode='Z'; const wb=document.getElementById('wgtBtn'); wb.textContent='dBZ'; wb.classList.remove('on'); document.getElementById('wLbl').textContent='Z';
  if(viewMin!==FMIN||viewMax!==FMAX){ viewMin=FMIN; viewMax=FMAX; buildBands(curBpo); document.getElementById('zoomBtn').style.display='none'; }
  if(genOn) genStop();
  closeModals();
}

function setMode(m){
  mode=m;
  document.getElementById('mRta').classList.toggle('on',m==='rta');
  document.getElementById('mSpec').classList.toggle('on',m==='spec');
  if(specCtx){specCtx.fillStyle='#0d1117';specCtx.fillRect(0,0,specCanvas.width,specCanvas.height);}
}

function buildWeighting(nyquist,bins){
  weightA=new Float32Array(bins); weightC=new Float32Array(bins);
  for(let i=0;i<bins;i++){
    const f=i*nyquist/bins, f2=f*f;
    const ra=(12194**2*f2*f2)/((f2+20.6**2)*Math.sqrt((f2+107.7**2)*(f2+737.9**2))*(f2+12194**2));
    weightA[i]= f>0 ? 20*Math.log10(ra)+2.00 : -120;
    const rc=(12194**2*f2)/((f2+20.6**2)*(f2+12194**2));
    weightC[i]= f>0 ? 20*Math.log10(rc)+0.06 : -120;
  }
}

async function start(deviceId){
  try{
    const audio = {
      echoCancellation: false,
      noiseSuppression: false,
      autoGainControl: false,
      channelCount: { ideal: 2 }
    };
    if(deviceId && typeof deviceId === 'string') audio.deviceId = { exact: deviceId };
    activeInId = deviceId || '';
    
    stream = await navigator.mediaDevices.getUserMedia({ audio });
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    
    if(outSinkId && typeof audioCtx.setSinkId === 'function'){ 
      try{ await audioCtx.setSinkId(outSinkId); }catch(_){} 
    }
    if(audioCtx.state === 'suspended') await audioCtx.resume();
    try {
      await audioCtx.audioWorklet.addModule('recorder-worklet.js');
    } catch(err) {
      console.warn('AudioWorklet failed to load. Delay measurement might not work without a server.', err);
    }

    source = audioCtx.createMediaStreamSource(stream);
    source.channelCount = 2;
    source.channelCountMode = 'explicit';

    const track = stream.getAudioTracks()[0];
    const settings = track.getSettings ? track.getSettings() : {};
    chReceived = settings.channelCount || source.channelCount || 1;
    const isSafari=/^((?!chrome|android|crios|fxios).)*safari/i.test(navigator.userAgent);
    const ci = document.getElementById('chCount');
    if(ci){
      if(chReceived>=2){ ci.textContent='ערוצים: '+chReceived+' ✓ סטריאו'; ci.style.color='#39d98a'; }
      else { ci.innerHTML='ערוצים: 1 ⚠ מונו — אין ערוץ 2'+(!isSafari?' · לערוץ 2 השתמש ב-Safari':''); ci.style.color='#ff6b8b'; }
    }

    analyser = audioCtx.createAnalyser();
    analyser.fftSize = fftSize;
    analyser.smoothingTimeConstant = parseFloat(document.getElementById('smooth').value);
    analyser.minDecibels = -100; 
    analyser.maxDecibels = -10;

    analyserRef = audioCtx.createAnalyser();
    analyserRef.fftSize = fftSize; 
    analyserRef.smoothingTimeConstant = 0.3;
    analyserRef.minDecibels = -100; 
    analyserRef.maxDecibels = -10;

    analyserMeter = audioCtx.createAnalyser();
    analyserMeter.fftSize = 2048;

    const splitter = audioCtx.createChannelSplitter(2);
    source.connect(splitter);

    splitter.connect(analyser, 0);
    splitter.connect(analyserRef, 1);
    source.connect(analyserMeter);

    floatData = new Float32Array(analyser.frequencyBinCount);
    floatDataRef = new Float32Array(analyserRef.frequencyBinCount);
    timeData = new Float32Array(analyser.fftSize);
    timeDataRef = new Float32Array(analyserRef.fftSize);
    timeDataMeter = new Float32Array(2048);
    
    buildWeighting(audioCtx.sampleRate / 2, analyser.frequencyBinCount);
    resize();
    peaks.fill(0); fbTrack.clear(); fbPanel.innerHTML = ''; lvlPeak = -120;
    leqSumP = 0; leqN = 0; splMax = -120;
    smoothedDbfs = -120;
    running = true; idle.style.display = 'none'; dot.classList.add('live');
    meterEl.style.display = 'flex'; document.getElementById('stats').style.display = 'flex';
    document.getElementById('stopBtn').style.display = '';
    populateInputs();
    draw();
  } catch(e) {
    errBox.style.display = 'block';
    errBox.textContent = 'לא ניתן לגשת למיקרופון: ' + (e.message || e.name) + '. יש לאשר הרשאה ולהריץ מעל HTTPS.';
  }
}

const PRO_RE=/mr18|xr18|x[\s-]?air|midas|behringer|scarlett|focusrite|presonus|motu|rme|audient|zoom|ssl|apollo|universal audio|interface|usb audio|audiobox|steinberg|ur[0-9]|clarett/i;
function pickBestDevice(list, savedId){
  if(savedId && list.some(d=>d.deviceId===savedId)) return savedId;   // remembered choice
  const pro=list.find(d=>PRO_RE.test(d.label||''));                    // guess a pro interface
  if(pro) return pro.deviceId;
  return list[0] ? list[0].deviceId : '';
}
async function populateInputs(){
  try{
    const devs=await navigator.mediaDevices.enumerateDevices();
    const ins=devs.filter(d=>d.kind==='audioinput');
    const sel=document.getElementById('inSel');
    const cur=sel.value;
    sel.innerHTML='';
    ins.forEach((d,i)=>{
      const o=document.createElement('option');
      o.value=d.deviceId; o.textContent=d.label||('מיקרופון '+(i+1));
      sel.appendChild(o);
    });
    const savedIn=localStorage.getItem('rta_inDev');
    const bestIn=pickBestDevice(ins, cur||savedIn);
    if(bestIn) sel.value=bestIn;
    // if the best device isn't the one we're actually using, switch to it once
    if(running && bestIn && bestIn!==activeInId){ switchInput(bestIn); return; }
    const outs=devs.filter(d=>d.kind==='audiooutput');
    const osel=document.getElementById('outSel'); const ocur=osel.value;
    osel.innerHTML='';
    if(!outs.length){ const o=document.createElement('option'); o.textContent='פלט ברירת מחדל'; osel.appendChild(o); }
    outs.forEach((d,i)=>{
      const o=document.createElement('option');
      o.value=d.deviceId; o.textContent=d.label||('פלט '+(i+1));
      osel.appendChild(o);
    });
    const savedOut=localStorage.getItem('rta_outDev');
    if(ocur) osel.value=ocur; else if(savedOut && outs.some(d=>d.deviceId===savedOut)) osel.value=savedOut;
  }catch(e){}
}
let outSinkId=null;
async function applyOutput(deviceId){
  outSinkId=deviceId;
  try{
    if(audioCtx && typeof audioCtx.setSinkId==='function'){ await audioCtx.setSinkId(deviceId||''); return true; }
  }catch(e){}
  return false;
}
document.getElementById('outSel').addEventListener('change',async e=>{
  try{localStorage.setItem('rta_outDev',e.target.value);}catch(_){}
  const ok=await applyOutput(e.target.value);
  if(!ok) alert('הדפדפן לא תומך בבחירת יציאת פלט. הגדר את הפלט ב־macOS: הגדרות → סאונד → פלט.');
});

async function switchInput(deviceId){
  if(!running) return;
  if(raf) cancelAnimationFrame(raf);
  if(stream) stream.getTracks().forEach(t=>t.stop());
  if(audioCtx) await audioCtx.close();
  await start(deviceId);
}

function stop(){
  running=false; if(raf) cancelAnimationFrame(raf);
  analyserRef=null; floatDataRef=null; tfState='idle'; eqCurveData=null;
  genSrc=null; genOsc=null; genGain=null; genOn=false;
  const gb=document.getElementById('genOnBtn'); if(gb){gb.classList.remove('on');gb.textContent='▶ הפעל אות';}
  if(stream) stream.getTracks().forEach(t=>t.stop());
  if(audioCtx) audioCtx.close();
  dot.classList.remove('live'); idle.style.display='flex';
  document.getElementById('stopBtn').style.display='none';
  meterEl.style.display='none'; document.getElementById('stats').style.display='none';
  peakHzEl.textContent='—'; fbPanel.innerHTML='';
  ctx.clearRect(0,0,cv.clientWidth,cv.clientHeight);
}

function norm(db){ return Math.max(0,Math.min(1,(db-floorDb)/(ceilDb-floorDb))); }
function heat(t){
  t=Math.max(0,Math.min(1,t));
  const r=Math.round(255*Math.max(0,Math.min(1,1.3*t-0.35)));
  const g=Math.round(255*Math.max(0,Math.min(1,1.1*t-0.05)));
  const b=Math.round(255*Math.max(0,Math.min(1,0.30+0.70*t)));
  return 'rgb('+r+','+g+','+b+')';
}
function fLabel(f){return f>=1000?(f%1000?(f/1000).toFixed(1):f/1000)+'k':''+f;}

function bandDb(fLo,fHi,nyquist,bins){
  let lo=Math.floor(fLo/nyquist*bins), hi=Math.ceil(fHi/nyquist*bins);
  lo=Math.max(0,lo); hi=Math.min(bins-1,hi); if(hi<lo) hi=lo;
  let p=0;
  for(let i=lo;i<=hi;i++){ p+=Math.pow(10,floatData[i]/10); }
  return 10*Math.log10(p+1e-12);
}

/* התאמת דינמיקת המד: עלייה מהירה לקלט חדש, ודעיכה איטית (Slow Release = 0.035) לתנועה אנלוגית וטבעית */
function updateLevel(){
  if(!analyserMeter) return;
  analyserMeter.getFloatTimeDomainData(timeDataMeter);
  const dbfs = levelDb(timeDataMeter, 2048);

  if (dbfs > smoothedDbfs) {
    smoothedDbfs += (dbfs - smoothedDbfs) * 0.55; // Fast Attack
  } else {
    smoothedDbfs += (dbfs - smoothedDbfs) * 0.035; // Slow & Smooth Decay
  }

  const now=performance.now();
  if(smoothedDbfs>lvlPeak || now-lvlPeakT>1500){ lvlPeak=smoothedDbfs; lvlPeakT=now; }
  const pct=v=>Math.max(0,Math.min(100,(v+60)/60*100));
  meterFill.style.width=pct(smoothedDbfs)+'%';
  meterPeak.style.insetInlineStart=pct(lvlPeak)+'%';
  if(meterUnit==='SPL') meterVal.textContent=(smoothedDbfs+calib).toFixed(0)+' dB SPL≈';
  else meterVal.textContent=smoothedDbfs.toFixed(1)+' dBFS';

  const w = weightMode==='A'?weightA : weightMode==='C'?weightC : null;
  let p=0;
  for(let i=1;i<floatData.length;i++){
    const wdb = w ? w[i] : 0;
    if(wdb<-100) continue;
    p += Math.pow(10,(floatData[i]+wdb)/10);
  }
  const lvl = 10*Math.log10(p+1e-12) + calib;
  leqSumP += p; leqN++;
  const leq = 10*Math.log10(leqSumP/Math.max(1,leqN)+1e-12) + calib;
  if(lvl>splMax) splMax=lvl;
  const unit = calib>0 ? ' dB'+weightMode : '';
  const fmt=x=>x.toFixed(1)+unit;
  document.getElementById('splNow').textContent=fmt(lvl);
  document.getElementById('splLeq').textContent=fmt(leq);
  document.getElementById('splMax').textContent=fmt(splMax);
}

let _lastDraw=0;
function draw(){
  raf=requestAnimationFrame(draw);
  const now=performance.now();
  if(now-_lastDraw < 32) return;   // ~30fps cap — halves the render/compute load, imperceptible on an audio graph
  _lastDraw=now;
  updateSignalTint();
  analyser.getFloatFrequencyData(floatData);
  if(measState==='measuring' && measAccum){
    if(eqCh===2 && analyserRef) analyserRef.getFloatFrequencyData(floatDataRef);
    const srcData = (eqCh === 2 && floatDataRef) ? floatDataRef : floatData;
    for(let i=0;i<srcData.length;i++) measAccum[i]+=Math.pow(10,srcData[i]/10);
    measFrames++;
  }
  if(areaState==='measuring' && areaAccum){
    if(eqCh===2 && analyserRef) analyserRef.getFloatFrequencyData(floatDataRef);
    const srcData = (eqCh === 2 && floatDataRef) ? floatDataRef : floatData;
    for(let i=0;i<srcData.length;i++) areaAccum[i]+=Math.pow(10,srcData[i]/10);
    areaFrames++;
  }
  if(analyserRef && floatDataRef && (tfState==='measuring' || tfPanel.classList.contains('open'))){
    analyserRef.getFloatFrequencyData(floatDataRef);
    if(tfState==='measuring' && tfMic){
      const mic = tfSwap? floatDataRef : floatData;
      const ref = tfSwap? floatData : floatDataRef;
      for(let i=0;i<tfMic.length;i++){
        tfMic[i]+=Math.pow(10,mic[i]/10);
        tfRef[i]+=Math.pow(10,ref[i]/10);
        const diff = mic[i] - ref[i];
        tfDiffSum[i] += diff;
        tfDiffSq[i] += diff * diff;
      }
      tfFrames++;
    }
    if(tfPanel.classList.contains('open')) updateTfLevels();
  }
  if(analyserRef && floatDataRef && dlyPanel.classList.contains('open')){
    analyser.getFloatTimeDomainData(timeData);
    if(!timeDataRef || timeDataRef.length!==analyserRef.fftSize) timeDataRef=new Float32Array(analyserRef.fftSize);
    analyserRef.getFloatTimeDomainData(timeDataRef);
    setGain('dlyMic', levelDb(timeData,2048));
    setGain('dlyRef', levelDb(timeDataRef,2048));
  }
  if(eqPanel.classList.contains('open')){
    const targetData = (eqCh === 2 && timeDataRef) ? timeDataRef : timeData;
    if(eqCh === 2 && analyserRef) analyserRef.getFloatTimeDomainData(timeDataRef);
    else analyser.getFloatTimeDomainData(timeData);
    setGainEl(document.getElementById('eqMicFill'), document.getElementById('eqMicGain'), levelDb(targetData,2048));
  }
  if(gainPanel.classList.contains('open')){
    analyser.getFloatTimeDomainData(timeData);
    const micDb=levelDb(timeData,2048);
    setGainEl(document.getElementById('gainMicFill'), document.getElementById('gainMicGain'), micDb);
    setGainEl(document.getElementById('gainOutFill'), document.getElementById('gainOutGain'), genOn?genDb:-120);
    const tip=document.getElementById('gainTip');
    if(tip){
      let msg, col='var(--dim)';
      if(!genOn) msg='נגן רעש ורוד כדי לבדוק את הרמות.';
      else if(micDb>=-1){ msg='⚠ קליפ! הורד את גיין המיק\' במיקסר.'; col='#ff6b8b'; }
      else if(micDb>=-8){ msg='חזק — אפשר להוריד מעט גיין מיק\'.'; col='#ffd166'; }
      else if(micDb>=-40){ msg='✓ רמה טובה — אפשר למדוד.'; col='#39d98a'; }
      else { msg='חלש — הגבר גיין מיק\' במיקסר או העלה עוצמת PA.'; col='#ffd166'; }
      tip.textContent=msg; tip.style.color=col;
    }
  }
  if(rtPanel.classList.contains('open')){
    analyser.getFloatTimeDomainData(timeData);
    setGainEl(document.getElementById('rtLvlFill'), document.getElementById('rtLvlGain'), levelDb(timeData,2048));
  }
  updateLevel();
  const W=cv.clientWidth,H=cv.clientHeight;
  const nyquist=audioCtx.sampleRate/2, bins=floatData.length;
  const logMin=Math.log(ISO[0]), logMax=Math.log(ISO[BANDS-1]);
  const xForFreq=f=>((Math.log(f)-logMin)/(logMax-logMin))*W;

  if(mode==='rta') drawRta(W,H,nyquist,bins,xForFreq);
  else drawSpec(W,H,nyquist,bins,xForFreq);

  fbFrameCounter++;
  if(fbOn && fbFrameCounter % 4 === 0) detectFeedback(nyquist,bins);
}

function drawRta(W,H,nyquist,bins,xForFreq){
  ctx.clearRect(0,0,W,H);
  // build a prefix-sum of linear power ONCE per frame → each band's energy is O(1)
  // (previously each band re-summed thousands of FFT bins; that was the main CPU cost).
  if(!_pfx || _pfx.length!==bins+1) _pfx=new Float64Array(bins+1);
  { let acc=0; _pfx[0]=0; for(let i=0;i<bins;i++){ acc+=Math.pow(10,floatData[i]*0.1); _pfx[i+1]=acc; } }
  const bandPowDb=(fLo,fHi)=>{
    let lo=Math.floor(fLo/nyquist*bins), hi=Math.ceil(fHi/nyquist*bins);
    lo=Math.max(0,lo); hi=Math.min(bins-1,hi); if(hi<lo)hi=lo;
    return 10*Math.log10((_pfx[hi+1]-_pfx[lo])+1e-12);
  };
  const meterH = (meterEl && meterEl.style.display!=='none') ? 40 : 6;
  const plotH = H - meterH - 16;
  const labelY = H - meterH - 4;
  ctx.strokeStyle='#2b3646'; ctx.fillStyle='#aeb9c7'; ctx.font='11px monospace'; ctx.textAlign='center';
  const lo=ISO[0], hi=ISO[BANDS-1];
  [20,31.5,50,100,200,500,1000,2000,5000,10000,20000].filter(f=>f>=lo&&f<=hi).forEach(f=>{
    const x=xForFreq(f);
    ctx.globalAlpha=.6; ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,plotH);ctx.stroke(); ctx.globalAlpha=1;
    ctx.fillText(fLabel(f)+'Hz',x,labelY);
  });
  [0.25,0.5,0.75].forEach(p=>{ctx.globalAlpha=.3;ctx.strokeStyle='#2b3646';ctx.beginPath();ctx.moveTo(0,plotH*p);ctx.lineTo(W,plotH*p);ctx.stroke();ctx.globalAlpha=1;});

  const bw=W/BANDS, gap=Math.max(0.5,bw*0.12);
  let peakBand=-1,peakVal=0;
  for(let b=0;b<BANDS;b++){
    const fc=ISO[b];
    const rawDb=bandPowDb(fc/R,fc*R);
    lastBandDb[b]=rawDb;
    const compDb = pinkComp ? 3*Math.log2(ISO[b]/1000) : 0;
    let v=norm(rawDb+compDb);
    if(avgOn){ avgBuf[b]=avgBuf[b]*0.9+v*0.1; v=avgBuf[b]; } else { avgBuf[b]=v; }
    lastV[b]=v;
    if(v>peakVal){peakVal=v;peakBand=b;}
    const x=b*bw+gap/2, barW=bw-gap;
    const barH=v*plotH, y=plotH-barH;
    let col= v<0.85?'rgba(62,166,255,'+(0.4+v).toFixed(2)+')' : '#ff3b6b';
    ctx.fillStyle=col; ctx.fillRect(x,y,barW,barH);
    if(peakHold){
      if(v>=peaks[b]) peaks[b]=v; else peaks[b]=Math.max(0,peaks[b]-0.005);
      const py=plotH-peaks[b]*plotH;
      ctx.fillStyle='rgba(255,255,255,.85)'; ctx.fillRect(x,py-2,barW,2);
    }
  }
  if(snapCurve && snapCurve.length===BANDS){
    ctx.strokeStyle='#ffb020'; ctx.lineWidth=2; ctx.beginPath();
    for(let b=0;b<BANDS;b++){
      const x=b*bw+bw/2, yy=plotH-snapCurve[b]*plotH;
      b===0?ctx.moveTo(x,yy):ctx.lineTo(x,yy);
    }
    ctx.stroke();
    ctx.fillStyle='#ffb020'; ctx.font='10px monospace'; ctx.textAlign='start';
    ctx.fillText('הקפאה', 8, 12);
    const peaks=[];
    for(let b=1;b<BANDS-1;b++){
      const v=snapCurve[b];
      if(v>snapCurve[b-1] && v>=snapCurve[b+1] && v>0.35) peaks.push({b,v});
    }
    peaks.sort((a,z)=>z.v-a.v);
    peaks.slice(0,6).forEach(p=>{
      const b=p.b, x=b*bw+bw/2, yy=plotH-p.v*plotH;
      const fc=ISO[b]; let lo=Math.floor((fc/R)/nyquist*bins), hi=Math.ceil((fc*R)/nyquist*bins);
      lo=Math.max(1,lo); hi=Math.min(bins-1,hi); let bMax=-999, bi=lo;
      for(let i=lo;i<=hi;i++){ if(floatData[i]>bMax){bMax=floatData[i];bi=i;} }
      const hz=bi*nyquist/bins;
      const lbl=hz>=1000?(hz/1000).toFixed(2)+'k':Math.round(hz)+'';
      ctx.fillStyle='#ffb020'; ctx.beginPath(); ctx.arc(x,yy,3,0,6.28); ctx.fill();
      ctx.font='10px monospace'; ctx.textAlign='center';
      const tw=ctx.measureText(lbl).width+6;
      ctx.fillStyle='rgba(13,17,23,.9)'; ctx.fillRect(x-tw/2, yy-16, tw, 13);
      ctx.fillStyle='#ffd27a'; ctx.fillText(lbl, x, yy-6);
    });
  }
  if(dragging && Math.abs(dragX1-dragX0)>4){
    const xa=Math.min(dragX0,dragX1), xb=Math.max(dragX0,dragX1);
    ctx.fillStyle='rgba(47,155,255,.15)'; ctx.fillRect(xa,0,xb-xa,plotH);
    ctx.strokeStyle='rgba(47,155,255,.8)'; ctx.lineWidth=1;
    ctx.strokeRect(xa,0,xb-xa,plotH);
  }
  if(targetMode!=='off' && (eqPanel.classList.contains('open')||areaPanel.classList.contains('open'))){
    ctx.strokeStyle='rgba(80,230,140,.8)'; ctx.setLineDash([6,5]); ctx.lineWidth=2; ctx.beginPath();
    for(let b=0;b<BANDS;b++){
      const t=b/(BANDS-1);
      let ty=0.55;
      if(targetMode==='house'){
        ty=0.68-0.22*t;
      }
      const x=b*bw+bw/2, yy=plotH-ty*plotH;
      b===0?ctx.moveTo(x,yy):ctx.lineTo(x,yy);
    }
    ctx.stroke(); ctx.setLineDash([]);
    ctx.fillStyle='rgba(80,230,140,.9)'; ctx.font='10px monospace'; ctx.textAlign='end';
    ctx.fillText(targetMode==='house'?'יעד House':'יעד שטוח', W-8, 12);
  }
  if(eqCurveData){
    const {freqs,corr}=eqCurveData;
    const z=plotH*0.34, sc=(plotH*0.22)/12;
    ctx.textAlign='end'; ctx.font='9px monospace';
    [12,6,0,-6,-12].forEach(d=>{ const yy=z-d*sc;
      ctx.strokeStyle=d===0?'rgba(80,230,140,.55)':'rgba(80,230,140,.16)';
      ctx.setLineDash(d===0?[]:[2,3]); ctx.beginPath();ctx.moveTo(0,yy);ctx.lineTo(W,yy);ctx.stroke();
      ctx.fillStyle='rgba(120,220,160,.9)'; ctx.fillText((d>0?'+':'')+d, W-4, yy-2); });
    ctx.setLineDash([]);
    const lo=ISO[0], hi=ISO[BANDS-1];
    ctx.strokeStyle='#50e68c'; ctx.lineWidth=2.5; ctx.beginPath(); let started=false;
    for(let k=0;k<freqs.length;k++){ if(corr[k]==null) continue; const f=freqs[k]; if(f<lo||f>hi) continue;
      const x=xForFreq(f), yy=z-Math.max(-12,Math.min(12,corr[k]))*sc;
      started?ctx.lineTo(x,yy):ctx.moveTo(x,yy); started=true; }
    ctx.stroke();
    ctx.font='10px monospace'; ctx.textAlign='center';
    for(let k=1;k<freqs.length-1;k++){ const v=corr[k]; if(v==null) continue;
      const pv=corr[k-1], nv=corr[k+1]; if(pv==null||nv==null) continue;
      const isExt=(v>=pv&&v>nv)||(v<=pv&&v<nv);
      if(!isExt||Math.abs(v)<2) continue; const f=freqs[k]; if(f<lo||f>hi) continue;
      const x=xForFreq(f), yy=z-Math.max(-12,Math.min(12,v))*sc;
      const lbl=(f>=1000?(f/1000).toFixed(1)+'k':Math.round(f))+' '+(v>0?'+':'')+v.toFixed(0);
      ctx.fillStyle='#0d1117'; const tw=ctx.measureText(lbl).width+6;
      ctx.fillRect(x-tw/2, v>0?yy-16:yy+4, tw, 13);
      ctx.fillStyle='#8ff0b8'; ctx.fillText(lbl, x, v>0?yy-6:yy+14); }
    ctx.fillStyle='rgba(120,220,160,.9)'; ctx.textAlign='start'; ctx.font='10px monospace';
    ctx.fillText('תיקון EQ', 8, z-12*sc-4);
  }
  if(cursorX!=null && cursorX>=0 && cursorX<=W){
    const cf=freqForX(cursorX);
    const bi=Math.max(0,Math.min(BANDS-1,Math.floor(cursorX/bw)));
    ctx.strokeStyle='rgba(255,255,255,.55)'; ctx.setLineDash([3,3]); ctx.lineWidth=1;
    ctx.beginPath();ctx.moveTo(cursorX,0);ctx.lineTo(cursorX,plotH);ctx.stroke(); ctx.setLineDash([]);
    const fl=cf>=1000?(cf/1000).toFixed(2)+'kHz':Math.round(cf)+'Hz';
    const lvl=(lastBandDb[bi]!=null&&lastBandDb[bi]>-119)?('  '+Math.round(lastBandDb[bi])+'dB'):'';
    const label=fl+lvl;
    ctx.font='12px monospace'; ctx.textAlign='left';
    const tw=ctx.measureText(label).width+12;
    let tx=Math.max(2,Math.min(W-tw-2, cursorX-tw/2));
    ctx.fillStyle='rgba(13,17,23,.92)'; ctx.fillRect(tx,plotH-22,tw,18);
    ctx.strokeStyle='rgba(47,155,255,.7)'; ctx.strokeRect(tx,plotH-22,tw,18);
    ctx.fillStyle='#e6ecf3'; ctx.fillText(label,tx+6,plotH-9);
  }
  const visAreas=areas.filter(a=>a.show);
  if(visAreas.length){
    visAreas.forEach(a=>{
      ctx.strokeStyle=a.color; ctx.lineWidth=2; ctx.beginPath(); let started=false;
      for(let k=0;k<GEQ.length;k++){
        const f=GEQ[k]; if(f<ISO[0]||f>ISO[BANDS-1]) continue;
        const comp = pinkComp?3*Math.log2(f/1000):0;
        const x=xForFreq(f), yy=plotH-norm(a.db[k]+comp)*plotH;
        started?ctx.lineTo(x,yy):ctx.moveTo(x,yy); started=true;
      }
      ctx.stroke();
    });
    ctx.textAlign='start'; ctx.font='11px monospace';
    visAreas.forEach((a,i)=>{
      const y=30+i*16;
      ctx.fillStyle=a.color; ctx.fillRect(8,y-8,16,3);
      ctx.fillStyle='#e6ecf3'; ctx.fillText(a.name,28,y-2);
    });
  }
  let exactHz=0;
  if(peakBand>=0 && peakVal>0.05){
    const fc=ISO[peakBand];
    let lo=Math.floor((fc/R)/nyquist*bins), hi=Math.ceil((fc*R)/nyquist*bins);
    lo=Math.max(1,lo); hi=Math.min(bins-1,hi);
    let bMax=-999, bi=lo;
    for(let i=lo;i<=hi;i++){ if(floatData[i]>bMax){ bMax=floatData[i]; bi=i; } }
    let idx=bi;
    if(bi>0&&bi<bins-1){ const a=floatData[bi-1],b=floatData[bi],c=floatData[bi+1], d=a-2*b+c;
      if(d!==0) idx=bi+0.5*(a-c)/d; }
    exactHz=idx*nyquist/bins;
  }
  peakHzEl.textContent = exactHz>0
    ? (exactHz>=1000?(exactHz/1000).toFixed(3)+' kHz':Math.round(exactHz)+' Hz') : '—';
}

function drawSpec(W,H,nyquist,bins,xForFreq){
  specCtx.drawImage(specCanvas,0,-1);
  const y=specCanvas.height-1;
  for(let px=0;px<specCanvas.width;px++){
    const f=Math.exp(((px/specCanvas.width))*(Math.log(ISO[BANDS-1])-Math.log(ISO[0]))+Math.log(ISO[0]));
    const bin=Math.min(bins-1,Math.round(f/nyquist*bins));
    specCtx.fillStyle=heat(norm(floatData[bin]));
    specCtx.fillRect(px,y,1,1);
  }
  const meterH = (meterEl && meterEl.style.display!=='none') ? 40 : 6;
  const specH = H - meterH;
  ctx.clearRect(0,0,W,H);
  ctx.drawImage(specCanvas,0,0,W,specH);
  ctx.fillStyle='#c2cbd6'; ctx.font='11px monospace'; ctx.textAlign='center';
  const lo=ISO[0], hi=ISO[BANDS-1];
  [20,31.5,50,100,200,500,1000,2000,5000,10000,20000].filter(f=>f>=lo&&f<=hi).forEach(f=>{
    const x=xForFreq(f);
    ctx.strokeStyle='rgba(255,255,255,.14)';ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,specH);ctx.stroke();
    ctx.fillText(fLabel(f)+'Hz',x,12);
  });
  let pk=-Infinity,pkf=0;
  for(let i=1;i<bins;i++){ if(floatData[i]>pk){pk=floatData[i]; pkf=i*nyquist/bins;} }
  peakHzEl.textContent= pk>floorDb ? (pkf>=1000?(pkf/1000).toFixed(1)+' kHz':Math.round(pkf)+' Hz') : '—';
}

function detectFeedback(nyquist,bins){
  const PROM=fbProm;
  const MINDB=-58;
  const HOLD=14;
  const win=24;
  const seen=new Set();

  const iLo=Math.max(2,Math.floor(60/nyquist*bins));
  const iHi=Math.min(bins-2,Math.floor(12000/nyquist*bins));
  for(let i=iLo;i<=iHi;i++){
    const d=floatData[i];
    if(d<MINDB) continue;
    if(!(d>floatData[i-1]&&d>=floatData[i+1])) continue;
    let sum=0,n=0;
    for(let j=i-win;j<=i+win;j++){ if(Math.abs(j-i)>2&&j>=0&&j<bins){sum+=floatData[j];n++;} }
    const avg=sum/Math.max(1,n);
    if(d-avg<PROM) continue;
    const prom=d-avg;
    let li=i, ri=i;
    while(li>1 && floatData[li]>d-3) li--;
    while(ri<bins-1 && floatData[ri]>d-3) ri++;
    const bw3=Math.max(1,(ri-li))*nyquist/bins;
    const hz=Math.round(i*nyquist/bins);
    const q=Math.max(2,Math.min(12, hz/bw3));
    const cut=Math.max(3,Math.min(12, Math.round(prom*0.7)));
    const key=Math.round(hz/ (hz<300?5:hz<2000?15:60));
    seen.add(key);
    const rec=fbTrack.get(key)||{frames:0,db:d,hz:hz,cut:cut,q:q};
    rec.frames=Math.min(HOLD+30,rec.frames+2);
    rec.db=d; rec.hz=hz; rec.cut=cut; rec.q=q; fbTrack.set(key,rec);
  }
  for(const [k,rec] of fbTrack){ if(!seen.has(k)){ rec.frames-=1; if(rec.frames<=0) fbTrack.delete(k);} }
}

loadCalStore();
document.getElementById('ver').textContent='v110';
// ---- accent color picker (swaps one CSS var — instant, no per-frame cost) ----
function applyAccent(hex){
  document.documentElement.style.setProperty('--accent',hex);
  document.documentElement.style.setProperty('--amber',hex);
  try{ localStorage.setItem('rta_accent',hex); }catch(_){}
}
(function initAccent(){
  const saved=localStorage.getItem('rta_accent');
  if(saved){ applyAccent(saved);
    document.querySelectorAll('#swatches .sw').forEach(b=>b.classList.toggle('on', b.dataset.c===saved)); }
})();
document.querySelectorAll('#swatches .sw').forEach(b=>b.addEventListener('click',function(){
  document.querySelectorAll('#swatches .sw').forEach(x=>x.classList.remove('on'));
  this.classList.add('on'); applyAccent(this.dataset.c);
}));
// ---- signal tint: subtle edge glow that follows the generator signal ----
const sigTint=document.getElementById('sigTint');
let _lastTint='';
function updateSignalTint(){
  if(!genOn){ if(_lastTint!==''){ sigTint.classList.remove('on'); _lastTint=''; } return; }
  let rgb=null;
  if(genType==='white') rgb='rgba(235,242,250,.16)';
  else if(genType==='pink') rgb='rgba(255,120,180,.16)';
  else if(genType==='sweep'){
    const now=audioCtx?audioCtx.currentTime:0, t=((now-(sweepStartT||now))%genSweepDur)/genSweepDur;
    const hue=250-250*Math.max(0,Math.min(1,t));   // low freq→blue, high→red
    rgb='hsla('+Math.round(hue)+',90%,60%,.16)';
  }
  if(rgb){ if(rgb!==_lastTint){ sigTint.style.boxShadow='inset 0 0 140px 30px '+rgb; _lastTint=rgb; } sigTint.classList.add('on'); }
  else if(_lastTint!==''){ sigTint.classList.remove('on'); _lastTint=''; }
}
const HELP={
  mRta:'תצוגת ספקטרום — עוצמה לפי תדר, בזמן אמת.',
  mSpec:'ווטרפול — הספקטרום לאורך זמן.',
  genBtn:'גנרטור אותות: רעש ורוד/לבן, סינוס או סוויפ.\nלמדידה ולכיוונון המערכת.',
  eqBtn:'מדידת תגובה: חד־ערוצי או דו־ערוצי (TF).',
  calBtn:'כיולי מיקרופון: טען קובץ כיול (REW)\nלתיקון צביעת המיקרופון.',
  tfBtn:'Transfer Function דו־ערוצי:\nמיק\' מול רפרנס מהמיקסר → תיקון EQ.',
  dlyBtn:'מדידת דיליי דו־ערוצי: זמן ההשהיה\nבין רמקולים (סאב מול טופ).',
  rtBtn:'RT60: מדידת זמן הדהוד החדר.\nדורש עוצמה וחדר אמיתי.',
  wgtBtn:'שקלול המד: dBZ (טכני), dBA (חוק/אוזן),\ndBC (עם בס). לחיצה מחליפה.',
  leqBtn:'אפס Leq: מתחיל מדידת ממוצע עוצמה\nמחדש מהרגע הזה.',
  peakBtn:'Peak Hold: משאיר את השיאים על המסך.',
  avgBtn:'מיצוע: מייצב את התצוגה לאורך זמן.',
  freezeBtn:'הקפא: שומר עקומה להשוואה,\nעם סימון תדרי הפיקים.',
  fbBtn:'גלאי פידבק: מזהה תדרים שמתחילים\nלשרוק, עם המלצת חיתוך.',
  stopBtn:'אפס סשן: מנקה מדידות והגדרות\nבלי לכבות את המיקרופון.',
  pngBtn:'ייצוא תמונת מסך (PNG).',
  csvBtn:'ייצוא הנתונים כקובץ CSV.',
  inSel:'מקור קלט: בחר מיקרופון / כרטיס קול.',
  outSel:'יציאת פלט: לאן יוצא אות הגנרטור.',
  genOnBtn:'מפעיל/עוצר את אות הגנרטור.',
  floor:'רצפת רעש: הסף התחתון של התצוגה.',
  cal:'כיול SPL: התאם למד ייחוס\nכדי לקבל dB SPL אמיתי.',
  genLvl:'עוצמת אות הגנרטור. התחל נמוך!',
  genFreq:'תדר הסינוס.',
  genSweep:'משך מחזור הסוויפ.',
  smooth:'החלקה: מרכך קפיצות בתצוגה.',
  res:'רזולוציה: פסים לאוקטבה.'
};
let helpMode=false;
const helpTip=document.createElement('div'); helpTip.id='helpTip'; document.body.appendChild(helpTip);
document.getElementById('helpBtn').addEventListener('click',function(){
  helpMode=!helpMode; this.classList.toggle('on',helpMode); document.body.classList.toggle('help-on',helpMode);
  if(!helpMode) helpTip.style.display='none';
});
document.addEventListener('mousemove',e=>{
  if(!helpMode) return;
  const el=e.target.closest('[id]'); const txt=el?HELP[el.id]:null;
  if(txt){ helpTip.textContent=txt; helpTip.style.whiteSpace='pre-line'; helpTip.style.display='block';
    let x=Math.min(e.clientX+14, innerWidth-helpTip.offsetWidth-10), y=Math.min(e.clientY+16, innerHeight-helpTip.offsetHeight-10);
    helpTip.style.left=x+'px'; helpTip.style.top=y+'px';
  } else helpTip.style.display='none';
});

(function plexus(){
  const g=document.getElementById('pcbTraces'); if(!g) return;
  const NS='http://www.w3.org/2000/svg', W=600,H=200, N=42, LINK=54;
  let s=90210; const rnd=()=>{ s=(s*1103515245+12345)&0x7fffffff; return s/0x7fffffff; };
  const nodes=[], dots=[];
  // one shared path for ALL connecting lines (1 DOM update/frame instead of hundreds)
  const linePath=document.createElementNS(NS,'path');
  linePath.setAttribute('stroke','#5ab0ff'); linePath.setAttribute('stroke-width','0.4');
  linePath.setAttribute('fill','none'); linePath.setAttribute('opacity','0.5'); g.appendChild(linePath);
  for(let i=0;i<N;i++){
    const n={x:rnd()*W,y:rnd()*H,vx:(rnd()-0.5)*0.12,vy:(rnd()-0.5)*0.12,r:0.5+rnd()*1.6};
    nodes.push(n);
    const c=document.createElementNS(NS,'circle'); c.setAttribute('r',n.r.toFixed(1));
    c.setAttribute('fill','#9fd4ff'); c.setAttribute('opacity',(0.4+rnd()*0.5).toFixed(2));
    g.appendChild(c); dots.push(c);
  }
  let last=0;
  function frame(t){
    requestAnimationFrame(frame);
    if(t-last<70) return;                 // ~14fps — decorative, keeps the main thread free for meters
    if(document.hidden) return;           // pause when tab/app not visible
    last=t;
    let d='';
    for(const n of nodes){ n.x+=n.vx; n.y+=n.vy; if(n.x<0||n.x>W)n.vx*=-1; if(n.y<0||n.y>H)n.vy*=-1; }
    for(let i=0;i<N;i++){ dots[i].setAttribute('cx',nodes[i].x.toFixed(1)); dots[i].setAttribute('cy',nodes[i].y.toFixed(1)); }
    for(let i=0;i<N;i++) for(let j=i+1;j<N;j++){
      const dx=nodes[i].x-nodes[j].x, dy=nodes[i].y-nodes[j].y, d2=dx*dx+dy*dy;
      if(d2<LINK*LINK) d+='M'+nodes[i].x.toFixed(1)+' '+nodes[i].y.toFixed(1)+'L'+nodes[j].x.toFixed(1)+' '+nodes[j].y.toFixed(1);
    }
    linePath.setAttribute('d', d);        // single write for every connection
  }
  requestAnimationFrame(frame);
})();

function reviveAudio(){ if(running && audioCtx && audioCtx.state==='suspended') audioCtx.resume(); }
document.addEventListener('visibilitychange',()=>{ if(!document.hidden) reviveAudio(); });
window.addEventListener('focus',reviveAudio);
resize();
if('ResizeObserver' in window){
  const _ro=new ResizeObserver(()=>{ resize(); });
  _ro.observe(document.getElementById('stage'));
}
if('serviceWorker' in navigator){
  window.addEventListener('load',()=>navigator.serviceWorker.register('sw.js').catch(()=>{}));
}
