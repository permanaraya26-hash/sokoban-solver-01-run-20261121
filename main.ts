import{mkdirSync as M,readdirSync as R,readFileSync as F,writeFileSync as W}from'node:fs';
import{join as J}from'node:path';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output',X=[0,0,-1,1],Y=[-1,1,0,0],C='udlr',A=3e5,B=3e6,E=1e7;
let u=0;
function pa(t){let r=t.split('\n').filter(e=>e.length),h=r.length,w=Math.max(...r.map(e=>e.length)),a=new Uint8Array(w*h).fill(1),g=[],b=[],p=-1;
r.forEach((s,y)=>{for(let x=0;x<s.length;x++){let c=s[x],i=y*w+x;if(c=='#')continue;a[i]=0;if('.*+'.includes(c))g.push(i);if('$*'.includes(c))b.push(i);if('@+'.includes(c))p=i;}});
for(let y=0;y<h;y++)for(let x=0;x<w;x++)if(!x||!y||x==w-1||y==h-1)a[y*w+x]=1;
return{w,h,wall:a,goals:g,boxes:b.sort((x,y)=>x-y),player:p};}
function li(l){let{w,wall:a,goals:g}=l,n=a.length,v=new Uint8Array(n),q=g.slice();
for(let e of g)v[e]=1;
for(let i=0;i<q.length;i++){let x=q[i];for(let k=0;k<4;k++){let d=Y[k]*w+X[k],y=x-d;
if(y>=0&&y<n&&y-d>=0&&y-d<n&&!a[y]&&!a[y-d]&&!v[y]){v[y]=1;q.push(y);}}}return v;}
function rg(w,a,o,f,v,s,t){let l=f,n=0;t[n++]=f;v[f]=s;
while(n){let p=t[--n];if(p<l)l=p;for(let k=0;k<4;k++){let q=p+Y[k]*w+X[k];
if(q>=0&&q<a.length&&!a[q]&&!o[q]&&v[q]!=s){v[q]=s;t[n++]=q;}}}return l;}
function fz(w,a,o,g,t){for(let e of[t,t-1,t-w,t-w-1]){let b=e+1,c=e+w,d=c+1;
if(e<0||d>=a.length)continue;
if((a[e]||o[e])&&(a[b]||o[b])&&(a[c]||o[c])&&(a[d]||o[d])&&((o[e]&&!g[e])||(o[b]&&!g[b])||(o[c]&&!g[c])||(o[d]&&!g[d])))return 1;}return 0;}
function wk(w,a,o,f,t){if(f==t)return'';let n=a.length,p=new Int32Array(n).fill(-1),h=new Int8Array(n),q=[f];p[f]=f;
for(let i=0;i<q.length;i++){let e=q[i];if(e==t)break;for(let k=0;k<4;k++){let s=e+Y[k]*w+X[k];
if(s<0||s>=n||a[s]||o[s]||p[s]!=-1)continue;p[s]=e;h[s]=k;q.push(s);}}
if(p[t]==-1)throw Error('w');let s='';for(let e=t;e!=f;e=p[e])s=C[h[e]]+s;return s;}
function sp(l,m){let{w,wall:a,goals:g}=l,n=a.length,o=new Uint8Array(n),V=new Int32Array(n),Z=new Int32Array(n),S=new Int32Array(n),G=new Uint8Array(n);
for(let e of g)G[e]=1;let v=li(l);if(l.boxes.some(e=>!v[e]))return null;let T=0;
let B=[l.boxes.slice()],P=[l.player],Q=[-1],F=[-1],D=[-1],H=new Map(),f=l.boxes.every(e=>G[e])?0:-1;
let ky=(b,y)=>{let k=y;for(let e of b)k=k*n+e;return k;};
for(let e of l.boxes)o[e]=1;H.set(ky(l.boxes,rg(w,a,o,l.player,Z,++T,S)),0);for(let e of l.boxes)o[e]=0;
for(let h=0;f<0&&h<B.length;h++){let b=B[h];for(let e of b)o[e]=1;let r=++T;rg(w,a,o,P[h],V,r,S);
for(let i=0;i<b.length&&f<0;i++){let c=b[i];for(let k=0;k<4;k++){let d=Y[k]*w+X[k],y=c+d;
if(V[c-d]!=r||a[y]||o[y]||!v[y])continue;o[c]=0;o[y]=1;let e=fz(w,a,o,G,y),j=-1,N=null;
if(!e){N=b.slice();N[i]=y;N.sort((x,z)=>x-z);j=ky(N,rg(w,a,o,c,Z,++T,S));}o[y]=0;o[c]=1;
if(e||H.has(j))continue;if(B.length>=m||++u>E)return null;
H.set(j,B.length);B.push(N);P.push(c);Q.push(h);F.push(c);D.push(k);
if(N.every(z=>G[z])){f=B.length-1;break;}}}
for(let e of b)o[e]=0;}
if(f<0)return null;let p=[];for(let e=f;e>0;e=Q[e])p.push(e);p.reverse();
let x='',y=l.player,b=l.boxes;
for(let e of p){let N=B[e],c=F[e],k=D[e],d=Y[k]*w+X[k];
for(let z of b)o[z]=1;x+=wk(w,a,o,y,c-d);for(let z of b)o[z]=0;x+=C[k].toUpperCase();y=c;b=N;}
return x;}
function eo(w,f,m){let p=f;for(let c of m.toLowerCase())p+=c=='u'?-w:c=='d'?w:c=='l'?-1:1;return p;}
function rm(l){let{w,wall:a,goals:g,boxes:b,player:p}=l,V=li(l),n=a.length,r=Math.floor(p/w),c=new Uint8Array(n);
for(let i=r*w;i<(r+1)*w;i++)if(!a[i]&&!V[i])c[i]=1;
if(b.some(e=>c[e]))return null;
let q=new Int32Array(n).fill(-1),R=[];
for(let s=0;s<n;s++){if(a[s]||c[s]||q[s]>=0)continue;let d=[s];q[s]=R.length;
for(let i=0;i<d.length;i++)for(let k=0;k<4;k++){let y=d[i]+Y[k]*w+X[k];
if(y>=0&&y<n&&!a[y]&&!c[y]&&q[y]<0){q[y]=R.length;d.push(y);}}R.push({boxes:[],goals:[]});}
for(let e of b)R[q[e]].boxes.push(e);
for(let e of g){if(q[e]<0)return null;R[q[e]].goals.push(e);}
if(R.some(e=>e.boxes.length!=e.goals.length))return null;
return R.filter(e=>e.boxes.length);}
function sl(l){let R=rm(l);if(!R){let s=sp(l,A);if(s===null)s=sp(l,B);return s;}
let p=l.player,x='';
for(let r of R){let a=l.wall.slice();
for(let o of R)if(o!==r)for(let b of o.done?o.goals:o.boxes)a[b]=1;
let v={w:l.w,h:l.h,wall:a,goals:r.goals.slice().sort((e,t)=>e-t),boxes:r.boxes.slice().sort((e,t)=>e-t),player:p};
let s=sp(v,A);if(s===null)s=sp(v,B);if(s===null)return null;
x+=s;p=eo(l.w,p,s);r.done=1;}
return x;}
for(let id of R(I).sort()){let m='';try{m=sl(pa(F(J(I,id,'level.txt'),'utf8')))??'';}catch{m='';}M(J(O,id),{recursive:true});W(J(O,id,'solution.txt'),m+'\n');}
