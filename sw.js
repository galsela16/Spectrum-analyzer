const bw=W/BANDS, gap=Math.max(0.5,bw*0.12);
  const tfOpen = ((tfOverlay || (typeof tfPanel!=='undefined' && tfPanel.classList.contains('open'))) && floatDataRef && analyserRef);
  let peakBand=-1,peakVal=0;

  // עדכון ערכים נומריים לכל פס (נחוץ למדים ולזיהוי שיאים)
  for(let b=0;b<BANDS;b++){
    const fc=ISO[b];
    const rawDb=bandPowDb(fc/R,fc*R);
    lastBandDb[b]=rawDb;
    let v=norm(rawDb);
    if(avgOn){ avgBuf[b]=avgBuf[b]*0.9+v*0.1; v=avgBuf[b]; } else { avgBuf[b]=v; }
    lastV[b]=v;
    if(v>peakVal){peakVal=v;peakBand=b;}

    // במצב RTA רגיל (עמודות) - מציירים כאן
    if(!tfOpen){
      const x=b*bw+gap/2, barW=bw-gap;
      const barH=v*plotH, y=plotH-barH;
      let col= v<0.85?'rgba('+accentRgb[0]+','+accentRgb[1]+','+accentRgb[2]+','+(0.4+v).toFixed(2)+')' : '#ff3b6b';
      ctx.fillStyle=col; ctx.fillRect(x,y,barW,barH);
      if(peakHold){
        if(v>=peaks[b]) peaks[b]=v; else peaks[b]=Math.max(0,peaks[b]-0.005);
        const py=plotH-peaks[b]*plotH;
        ctx.fillStyle='rgba(255,255,255,.85)'; ctx.fillRect(x,py-2,barW,2);
      }
    }
  }

  // ציור עקומות TF ברזולוציה גבוהה לפי פיקסלים
  if(tfOpen){
    if(!frozen) analyserRef.getFloatFrequencyData(floatDataRef);
    if(!_pfxRef || _pfxRef.length!==bins+1) _pfxRef=new Float64Array(bins+1);
    { let acc=0; _pfxRef[0]=0; for(let i=0;i<bins;i++){ acc+=db2lin(floatDataRef[i]); _pfxRef[i+1]=acc; } }
    
    const refBandDb=(fLo,fHi)=>{ 
      let lo=Math.floor(fLo/nyquist*bins),hi=Math.ceil(fHi/nyquist*bins); 
      lo=Math.max(0,lo);hi=Math.min(bins-1,hi);if(hi<lo)hi=lo; 
      return 10*Math.log10((_pfxRef[hi+1]-_pfxRef[lo])+1e-12); 
    };

    const micPts=[];
    const refPts=[];
    const stepPx = 2; // דגימה כל 2 פיקסלים לקבלת קו רציף וחלקה

    for(let px = 0; px <= W; px += stepPx){
      const f = freqForX(px);
      // מרווח דגימה צר (1/48 אוקטבה סביב התדר) לרזולוציה מקסימלית
      const fLo = f / 1.0145;
      const fHi = f * 1.0145;

      const mDb = bandPowDb(fLo, fHi);
      const rDb = refBandDb(fLo, fHi);

      micPts.push([px, plotH - norm(mDb) * plotH]);
      refPts.push([px, plotH - norm(rDb) * plotH]);
    }

    // ציור שטחי ועקומת המיקרופון
    ctx.beginPath(); 
    micPts.forEach(([x,y],i)=> i?ctx.lineTo(x,y):ctx.moveTo(x,y)); 
    ctx.lineTo(micPts[micPts.length-1][0],plotH); 
    ctx.lineTo(micPts[0][0],plotH); 
    ctx.closePath();
    ctx.fillStyle='rgba('+accentRgb.join(',')+',0.13)'; ctx.fill();

    ctx.beginPath(); 
    micPts.forEach(([x,y],i)=> i?ctx.lineTo(x,y):ctx.moveTo(x,y));
    ctx.strokeStyle='rgb('+accentRgb.join(',')+')'; ctx.lineWidth=2; ctx.lineJoin='round'; ctx.stroke();

    // ציור עקומת הרפרנס
    ctx.beginPath(); 
    refPts.forEach(([x,y],i)=> i?ctx.lineTo(x,y):ctx.moveTo(x,y));
    ctx.strokeStyle='#ffb020'; ctx.lineWidth=2; ctx.lineJoin='round'; ctx.stroke();

    // מקרא
    ctx.font='11px monospace'; ctx.textAlign='start';
    ctx.fillStyle='rgb('+accentRgb.join(',')+')'; ctx.fillText('— '+(tfSwap?'רפרנס':"מיקרופון"), 10, 14);
    ctx.fillStyle='#ffb020'; ctx.fillText('— '+(tfSwap?"מיקרופון":'רפרנס'), 10, 28);
  }
