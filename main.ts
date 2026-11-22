import {readFileSync,readdirSync,mkdirSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
const letters='udlr';
function parse(text){
  const rows=text.replace(/\r/g,'').split('\n');
  while(rows.length && rows.at(-1)==='') rows.pop();
  const w=Math.max(0,...rows.map(r=>r.length))+2, n=w*(rows.length+2);
  const floor=new Uint8Array(n), boxes=[], goals=[]; let player=-1;
  rows.forEach((r,y)=>{for(let x=0;x<r.length;x++){
    const c=r[x], p=(y+1)*w+x+1;
    if(c==='#')continue; floor[p]=1;
    if('.+*'.includes(c))goals.push(p);
    if('$*'.includes(c))boxes.push(p);
    if('@+'.includes(c))player=p;
  }});
  return {w,n,floor,boxes,goals,player,dirs:[-w,w,-1,1]};
}
function walk(b,boxes,start){
  const occupied=new Uint8Array(b.n); for(const p of boxes)occupied[p]=1;
  const prev=new Int32Array(b.n).fill(-1), via=new Int8Array(b.n), q=[start];
  prev[start]=start; let canon=start;
  for(let i=0;i<q.length;i++)for(let d=0;d<4;d++){
    const p=q[i]+b.dirs[d];
    if(b.floor[p]&&!occupied[p]&&prev[p]===-1){prev[p]=q[i];via[p]=d;q.push(p);canon=Math.min(canon,p);}
  }
  return {prev,via,canon,occupied};
}
function path(r,start,end){
  if(r.prev[end]===-1)return null;
  let s='';for(let p=end;p!==start;p=r.prev[p])s=letters[r.via[p]]+s;return s;
}
// Push A*: reverse distances ignore other boxes, and assignment is a lower bound.
function search(b,boxes,goals,start,cap){
  if(boxes.length!==goals.length||start<0||!b.floor[start])return null;
  const dist=goals.map(g=>{
    const a=new Int32Array(b.n).fill(1000000),q=[g];a[g]=0;
    for(let i=0;i<q.length;i++)for(const d of b.dirs){const p=q[i]-d;
      if(b.floor[p]&&b.floor[p-d]&&a[p]>a[q[i]]+1){a[p]=a[q[i]]+1;q.push(p);}}
    return a;
  });
  const hc=new Map();
  function heuristic(bs){
    const key=bs.join(',');if(hc.has(key))return hc.get(key);
    let h=0;
    if(bs.length<=8){
      const dp=new Float64Array(1<<bs.length).fill(Infinity);dp[0]=0;
      for(let mask=0;mask<dp.length;mask++){
        let k=0;for(let v=mask;v;v&=v-1)k++;
        if(k===bs.length)continue;
        for(let j=0;j<bs.length;j++)if(!(mask&(1<<j))){const m=mask|(1<<j);dp[m]=Math.min(dp[m],dp[mask]+dist[j][bs[k]]);}
      }h=dp.at(-1);
    }else for(const p of bs)h+=Math.min(...dist.map(a=>a[p]));
    hc.set(key,h);return h;
  }
  const heap=[];let serial=0;
  const less=(a,c)=>a.g+a.h<c.g+c.h||(a.g+a.h===c.g+c.h&&(a.h<c.h||(a.h===c.h&&a.order<c.order)));
  function put(v){let i=heap.length;heap.push(v);while(i){const p=(i-1)>>1;if(!less(v,heap[p]))break;heap[i]=heap[p];i=p;}heap[i]=v;}
  function take(){const top=heap[0],v=heap.pop();if(heap.length){let i=0;while(i*2+1<heap.length){let k=i*2+1;if(k+1<heap.length&&less(heap[k+1],heap[k]))k++;if(!less(heap[k],v))break;heap[i]=heap[k];i=k;}heap[i]=v;}return top;}
  boxes=boxes.slice().sort((a,c)=>a-c);
  const r=walk(b,boxes,start), key=boxes.join(',')+':'+r.canon;
  const root={bs:boxes,p:start,g:0,h:heuristic(boxes),key,parent:null,move:null,order:serial++};
  if(root.h>=1000000)return null;
  const best=new Map([[key,0]]);put(root);let expanded=0;
  while(heap.length&&expanded<cap){
    const cur=take();if(best.get(cur.key)!==cur.g)continue;
    if(cur.h===0){const out=[];for(let v=cur;v.parent;v=v.parent)out.push(v.move);return out.reverse();}
    expanded++;const reach=walk(b,cur.bs,cur.p);
    for(let k=0;k<cur.bs.length;k++)for(let di=0;di<4;di++){
      const p=cur.bs[k],d=b.dirs[di],to=p+d;
      if(reach.prev[p-d]===-1||!b.floor[to]||reach.occupied[to])continue;
      const bs=cur.bs.slice();bs[k]=to;bs.sort((a,c)=>a-c);
      const h=heuristic(bs);if(h>=1000000)continue;
      const region=walk(b,bs,p),key=bs.join(',')+':'+region.canon,g=cur.g+1;
      if((best.get(key)??Infinity)<=g)continue;
      best.set(key,g);put({bs,p,g,h,key,parent:cur,move:[p,di],order:serial++});
    }
  }return null;
}
function assemble(b,state,moves){
  let out='';for(const [box,di] of moves){
    const d=b.dirs[di],r=walk(b,state.boxes,state.player),s=path(r,state.player,box-d);
    if(s===null||!state.boxes.includes(box)||!b.floor[box+d]||state.boxes.includes(box+d))return null;
    out+=s+letters[di];state.boxes[state.boxes.indexOf(box)]=box+d;state.player=box;
  }return out;
}
function decomposed(b){
  const row=Math.floor(b.player/b.w),hall=[];
  for(let p=0;p<b.n;p++)if(b.floor[p]&&Math.floor(p/b.w)===row)hall.push(p);
  if(!hall.length||hall.some((p,i)=>i&&p!==hall[i-1]+1)||b.boxes.some(p=>hall.includes(p))||b.goals.some(p=>hall.includes(p)))return null;
  const seen=new Uint8Array(b.n),rooms=[];
  for(let p=0;p<b.n;p++)if(b.floor[p]&&!seen[p]&&!hall.includes(p)){
    const cells=[p];seen[p]=1;const doors=new Set();
    for(let i=0;i<cells.length;i++)for(const d of b.dirs){const q=cells[i]+d;
      if(!b.floor[q])continue;if(hall.includes(q)){doors.add(q);continue;}
      if(!seen[q]){seen[q]=1;cells.push(q);}
    }
    const set=new Set(cells),boxes=b.boxes.filter(x=>set.has(x)),goals=b.goals.filter(x=>set.has(x));
    if(!boxes.length&&!goals.length)continue;
    if(doors.size!==1||boxes.length>4||boxes.length!==goals.length)return null;
    rooms.push({cells,boxes,goals,door:[...doors][0]});
  }
  if(!rooms.length||rooms.length>4||new Set(rooms.map(r=>r.door)).size!==rooms.length)return null;
  const state={boxes:b.boxes.slice(),player:b.player};let out='';
  for(const room of rooms){
    const floor=new Uint8Array(b.n);for(const p of room.cells)floor[p]=1;floor[room.door]=1;
    const sub={...b,floor},moves=search(sub,room.boxes,room.goals,room.door,250000);
    if(moves===null)return null;
    const s=assemble(b,state,moves);if(s===null)return null;out+=s;
  }
  return state.boxes.every(p=>b.goals.includes(p))?out:null;
}
function solve(text){
  const b=parse(text);if(b.player<0)return '';
  const result=decomposed(b);if(result!==null)return result;
  const moves=search(b,b.boxes,b.goals,b.player,100000);
  return moves===null?'':assemble(b,{boxes:b.boxes.slice(),player:b.player},moves)??'';
}
const input=process.env.MAKEFUN_INPUT_DIR??'/input',output=process.env.MAKEFUN_OUTPUT_DIR??'/output';
for(const id of readdirSync(input).sort()){
  let moves='';try{moves=solve(readFileSync(join(input,id,'level.txt'),'utf8'));}catch{}
  mkdirSync(join(output,id),{recursive:true});writeFileSync(join(output,id,'solution.txt'),moves+'\n');
}
