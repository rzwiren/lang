// cl opi.c /GL /O1 /Gy /MD /DNDEBUG /link /LTCG /OPT:REF /OPT:ICF
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef unsigned long long Q;typedef unsigned int D;typedef unsigned short W;typedef unsigned char B;typedef char C;
typedef struct {D n;} AH; // header for shape 0 and 2. data is after the header.
typedef struct {B t;D m;D n;} Z; // header for shape 3 which is only used for type 0 for read heavy operations when shape is 111; z is size of data,m is metada count;n is count of data
typedef Q(*DV)(Q,Q); 
typedef Q(*MV)(Q);
// pointer is 08t6s2d48 0 in high 8 bits type in next 6 shape in next 2 and data/pointer in low 48
// type 0 is an absolute pointer. 
//   you may want to play with using the shape header for relative pointers when t is 0
//   since we can address 48 bits then we can get away with relptr being 48
Q d(Q q){return q&0x0000ffffffffffffULL;} 
Q*p(Q q){return (Q*)d(q);} 
B r(Q r){return d(r)+'a';}
B v(Q v){return d(v);}
AH* ah(Q q){return (AH*)d(q);}
Z*  zh(Q q){return (Z*)d(q);}

Q wh(B t,D n,Q q){Q s=((~0)==n)?((!t)?3:1):(!t)?0:2;Q h=(t<<2)|s;return (h<<48)|q;}

Q ar(Q r){return wh(1,~0,r);} // n param is unsigned so use 0xfffffffff as sentinel for atom
Q av(Q v){return wh(2,~0,v);} 
Q an(Q n){return wh(3,~0,n);} // needs to change when literals are bigger?

B h(Q q){return q>>48;} 
B th(Q q){return h(q)>>2;} 
B sh(Q q){return 3&h(q);} // it is potentially overkill to have room for 64 builtin types. 

// include a param for tyoe size
// I want to be able to specify the size of the integer or float.
// types are ptr0 ref1 verb2 int3 float4
// a ref is a single column or single key value
// a vector of ref is a dictionary
// a vector of ref all same size vals is a table
// this also means that a single ref that points to a vec is a single col table.
Q tn(B t,D n){AH h={n};AH*o=malloc(sizeof(AH)+8*n);*o=h;return wh(t,n,(Q)(o+1));} // pointers are non 0 in high bits based on the type shape, no the type itself. an atom and a vector of type int will have bits set in the pointer. This means we never need to include the datatype in the preample before the data. Any pointer should be carrying the info already. 

// i think i am allocating an extra int in metadata, dont need pos 0 to be descrpition of self
// this is suitable for math heavy stuff w/o depending on allocator for contig space
// db table should be classic type 0
//  can prolly use relptr tho
Q zn(B t,D m,D n){                           // t is underlying type. all data must be same type for this to make sense. 
  Z*o=malloc(sizeof(Z)+(2*4*m)+(8*n)); // allocate the size of the header plus the size of each metadata list plus the size of the data list
  Z h={t,m,n};  // metadata is length 2m and starts at ((Z)o)+1;first m is counts next m is offsets. data starts at ((Z)o)+4*2*m). if an offset is < data pointer then we know we are dealing with a type 0.
  *o=h;
  return wh(0,~0,(Q)o); // set the type in pointer to 0
}
D  mz(Q a){return zh(a)->m;}
D  nz(Q a){return zh(a)->n;}
D* Nz(Q a){return (D*)(1+zh(a));}
D* Oz(Q a){return mz(a)+Nz(a);}
Q* Dz(Q a){return (Q*)((mz(a)*2)+Nz(a));}
D  fz(Q a,D o){D m=mz(a);D z=o;while(z<m){z=Oz(a)[z];};return z;} // dist from Oz(a) to first data item 
D  no(Q a,D o,D n){
  D nzo=Nz(a)[o]; // number of children under this offset
  D oo=Oz(a)[o];
  if(oo>=mz(a)){return Nz(a)[o];}
  for(D i=0;i<nzo;i++){n+=no(a,o+i,n);}
  return n;
} // total data items under some offset o

Q I(Q a,D w){B s=sh(a);return 1==sh(a)?d(a):(0==s || 2==s)?p(a)[w]:Dz(a)[w];} // not a good setup for 3==s
D n(Q a){B s=sh(a);return 1==s?1:(0==s||2==s)?ah(a)[-1].n:3==sh(a)?(*Nz(a)):0;} 
B t(Q a){B t;return th(a);}

Q O[26];
C* VT;

void pr(Q q){
  if(0==q){return;}
  if(0==t(q)){
    if(3==sh(q)){for(D i=0;i<nz(q);i++){printf("%lld ",Dz(q)[i]);}}
    if(!sh(q)){for(D i=0;i<n(q);i++){pr(p(q)[i]);}}}
  if(1==t(q)){printf("%c ",r(q));pr(O[d(q)]);}
  if(2==t(q)){printf("%c",VT[v(q)]);}
  if(3==t(q)){
    if(0==sh(q)){printf("?num\n");}
    if(1==sh(q)){printf("%lld\n",d(q));}
    if(2==sh(q)){
      for(D i=0;i<n(q);i++){printf("%lld ",p(q)[i]);}}
    }
  printf("\n");
}
DV VD[8][4][4];
MV VM[8][4];

Q noP(Q w){Q z=tn(0,n(w));for(D i=0;i<n(w);i++){p(z)[i]=VM[1][sh(p(w)[i])](p(w)[i]);};return z;}
Q noA(Q w){return an(!d(w));}
Q noV(Q w){Q z=tn(3,n(w));for(D i=0;i<n(w);i++){p(z)[i]=!p(w)[i];};return z;}
Q noZ(Q w){Q z=zn(3,mz(w),nz(w));for(D i=0;i<2*mz(w);i++){Nz(z)[i]=Nz(w)[i];}for(D i=0;i<nz(w);i++){Dz(z)[i]=!Dz(w)[i];};return z;}

Q tlA(Q w){Q z=tn(3,d(w));for(D i=0;i<d(w);i++){p(z)[i]=i;}return z;}
//Q tlV(Q v){Q z=tn(0,n(v));for(D i=0;i<n(v);i++){p(z)[i]=tlA(p(v)[i]);};return z;}
Q tlV(Q w){
  D nw=n(w);D mz=1+nw;D nz=0;for(D i=0;i<nw;i++){nz+=p(w)[i];};Q z=zn(3,mz,nz);
  Nz(z)[0]=nw;Oz(z)[0]=1;D l=0;
  for(D i=0;i<nw;i++){Oz(z)[i+1]=((D*)(Dz(z)+l))-Oz(z);l+=Nz(z)[i+1]=p(w)[i];}
  D k=0;for(D i=0;i<nw;i++){for(D j=0;j<p(w)[i];j++){Dz(z)[k++]=j;}};
  return z;
}
Q tlZ(Q z){return z;}


Q at(Q a,Q w){D sz=n(w);C ta=t(a);Q z=tn(t(a),sz);for(D i=0;i<sz;i++){p(z)[i]=p(a)[p(w)[i]];};return z;}

Q tp(Q a){return an(t(a));}
Q ct(Q a){return an(n(a));}

Q plVV(Q a,Q w){Q z=tn(3,n(w));for(D i=0;i<n(w);i++){p(z)[i]=p(a)[i]+p(w)[i];};return z;}
Q plAV(Q a,Q w){Q z=tn(3,n(w));for(D i=0;i<n(w);i++){p(z)[i]=d(a)+p(w)[i];};return z;} 
Q plVA(Q a,Q w){return plAV(w,a);}
Q plAA(Q a,Q w){return an(d(a)+d(w));}
Q plAP(Q a,Q w){Q z=tn(0,n(w));for(D i=0;i<n(w);i++){p(z)[i]=VD[5][1][sh(p(w)[i])](a,p(w)[i]);};return z;} 
Q plPA(Q a,Q w){return plAP(w,a);}
Q plPP(Q a,Q w){Q z=tn(0,n(w));for(D i=0;i<n(w);i++){p(z)[i]=VD[5][sh(p(a)[i])][sh(p(w)[i])](p(a)[i],p(w)[i]);}return z;}
Q plPV(Q a,Q w){Q z=tn(0,n(w));for(D i=0;i<n(w);i++){p(z)[i]=VD[5][sh(p(a)[i])][1](p(a)[i],an(p(w)[i]));}return z;}
Q plVP(Q a,Q w){return plPV(w,a);}
Q plAZ(Q a,Q w){  // this case is simple because we don't need to examine metadata, just need to copy.
  Q z=zn(3,mz(w),nz(w));
  for(D i=0;i<2*mz(w);i++){Nz(z)[i]=Nz(w)[i];} // counts and offsets are same size
  for(D i=0;i<nz(w);i++){Dz(z)[i]=d(a)+Dz(w)[i];}
  return z;
} 
Q plZA(Q a,Q w){return plAZ(w,a);}
Q plVZ(Q a,Q w){  // this case is medium hard, metadata still the ssame but need to examine metadata to know which vector index conforms to while data index in the z list
  Q z=zn(3,mz(w),nz(w));
  for(D i=0;i<2*mz(w);i++){Nz(z)[i]=Nz(w)[i];} // counts and offsets are same size
  Q o=*Oz(w); // o is the distance from Oz(w) to the next offset. 
  for(D i=0;i<*Nz(w);i++){
    D d=fz(w,o+i);
    for(D j=0;j<no(w,o+i,0);j++){
      ((Q*)(Oz(z)+d))[j]=((Q*)(Oz(w)+d))[j]+p(a)[i];
    }
  }
  return z;
}
Q plZV(Q a,Q w){return plVZ(w,a);}
Q plZZ(Q a,Q w){ // not atomic in the usual sense of a k implementation. 
  Q z=zn(3,mz(w),nz(w));
  for(D i=0;i<2*mz(w);i++){Nz(z)[i]=Nz(w)[i];}
  for(D i=0;i<nz(w);i++){Dz(z)[i]=Dz(a)[i]+Dz(w)[i];}
  return z;
}

Q as(Q a,Q w){O[d(a)]=w;return w;}

Q caAA(Q a,Q w){Q z=tn(t(w),2);p(z)[0]=d(a);p(z)[1]=d(w);return z;}
Q caAV(Q a,Q w){Q z=tn(t(w),1+n(w));p(z)[0]=d(a);for(D i=0;i<n(w);i++){p(z)[i+1]=p(w)[i];}return z;}
Q caAZ(Q a,Q w){Q z=zn(t(w),1+mz(w),1+nz(w));
  Oz(z)[0]=1;Oz(z)[1]=((D*)Dz(z))-Oz(z);
  *Nz(z)=1+*Nz(w);
  for(D i=1;i<mz(w);i++){Oz(z)[i+1]=Oz(w)[i]+((Oz(w)[i]>=mz(w))?2:1);Nz(z)[i+1]=Nz(w)[i];}
  *Dz(z)=d(a);
  for(D i=0;i<nz(w);i++){Dz(z)[i+1]=Dz(w)[i];}
  return z;
}
Q caVA(Q a,Q w){Q z=tn(t(w),1+n(a));for(D i=0;i<n(a);i++){p(z)[i]=p(a)[i];}p(z)[n(a)]=d(a);return z;}
Q caVV(Q a,Q w){Q z=tn(t(w),n(a)+n(w));D j=0;for(D i=0;i<n(a);i++,j++){p(z)[j]=p(a)[i];};for(D i=0;i<n(w);i++,j++){p(z)[j]=p(w)[i];}return z;}
Q caVZ(Q a,Q w){Q z=zn(t(w),1+mz(w),n(a)+nz(w));
  Oz(z)[0]=1;Oz(z)[1]=((D*)Dz(z))-Oz(z);
  *Nz(z)=1+*Nz(w);Nz(z)[1]=n(a);
  for(D i=1;i<mz(w);i++){Oz(z)[i+1]=Oz(w)[i]+((Oz(w)[i]>=mz(w))?1+n(a)*2:1);Nz(z)[i+1]=Nz(w)[i];}
  for(D i=0;i<n(a);i++){Dz(z)[i]=p(a)[i];}
  for(D i=0;i<nz(w);i++){Dz(z)[i+n(a)]=Dz(w)[i];}
  return z;
}
Q caZA(Q a,Q w){Q z=zn(t(w),1+mz(a),1+nz(a));
  Oz(z)[0]=1;*Nz(z)=1+*Nz(a);
  for(D i=1;i<2*mz(a);i++){Nz(z)[i]=Nz(a)[i];}
  for(D i=0;i<nz(a);i++){Dz(z)[i]=Dz(a)[i];}
  Nz(z)[mz(a)]=1;Oz(z)[mz(a)]=((D*)(Dz(z)+nz(a)))-Oz(z);Dz(z)[nz(a)]=d(w);
  return z;
}
Q caZV(Q a,Q w){Q z=zn(t(w),1+mz(a),n(w)+nz(a));
  Oz(z)[0]=1;*Nz(z)=1+*Nz(a);
  for(D i=1;i<2*mz(a);i++){Nz(z)[i]=Nz(a)[i];}
  for(D i=0;i<nz(a);i++){Dz(z)[i]=Dz(a)[i];}
  Nz(z)[mz(a)]=1;Oz(z)[mz(a)]=((D*)(Dz(z)+nz(a)))-Oz(z);
  for(D i=0;i<n(w);i++){Dz(z)[nz(a)+i]=p(w)[i];}

  return z;
}
Q caZZ(Q a,Q w){Q z=zn(t(w),mz(a)+mz(w),nz(a)+nz(w));
  D i=1,j=0;
  Oz(z)[0]=1;*Nz(z)=(*Nz(a))+(*Nz(w));
  printf("nz(z) %d *Nz(z) %d\n",nz(z),*Nz(z));
  for(j=1;j<*Nz(a);j++,i++){Oz(z)[i]=Oz(a)[j];Nz(z)[i]=Oz(a)[j];}
  for(j=1;j<*Nz(w);j++,i++){Oz(z)[i]=Oz(z)[*Nz(a)]+Oz(w)[j]; Nz(z)[i]=Oz(w)[j];}
  for(j=*Nz(a);j<mz(a);j++,i++){Oz(z)[i]=Oz(z)[*Nz(a)+*Nz(w)-1]+Oz(a)[j];Nz(z)[i]=Oz(a)[j];}
  for(j=*Nz(w);j<mz(w);j++,i++){Oz(z)[i]=Oz(z)[ mz(a)+*Nz(w)-1]+Oz(w)[j];Nz(z)[i]=Oz(w)[j];}
  for(i=0,j=0;i<nz(a);i++,j++){Dz(z)[i]=Dz(a)[j];}
  for(j=0;j<nz(w);i++,j++){Dz(z)[i]=Dz(w)[j];}
  return z;
}


Q id(Q a){return a;}
DV VD[8][4][4]={
  {{0,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}},
  {{0,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}},
  {{0,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}},
  {{0,0,0,0},{0,0,0,0},{0,at,0,0},{0,0,0,0}}, //at
  {{0,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}},
  {{plPP,plPA,plPV,0},{plAP,plAA,plAV,plAZ},{plVP,plVA,plVV,plVZ},{0,plZA,plZV,plZZ}}, //pl,
  {{0,0,0,0},{as,as,as,as},{0,0,0,0},{0,0,0,0}}, // as
  {{0,0,0,0},{0,caAA,caAV,caAZ},{0,caVA,caVV,caVZ},{0,caZA,caZV,caZZ}}}; // ca
MV VM[8][4]={
  {0,0,0,0},
  {noP,noA,noV,noZ},
  {0,tlA,tlV,0},
  {tp,tp,tp,tp},
  {ct,ct,ct,ct},
  {0,0,0,0}, // consider making this x<<1
  {id,id,id,id},
  {0,0,0,0}};
C* VT=" ~!@#+:,";

Q e(Q* q);
Q emv(Q*q){Q w=e(q+1);return VM[v(*q)][sh(w)](w);}
Q edv(Q a,Q*q){a=((1==t(a))&&(6!=v(*q)))?O[d(a)]:a;Q w=e(q+1);DV dv=VD[v(*q)][sh(a)][sh(w)];return dv(a,w);}
Q e(Q* q){
  Q a=*q;Q w=q[1];
  return (2==t(a)&&w) ?
         emv(q)       :
         (w&&2==t(w)) ?
         edv(a,q+1)   :
         (1==t(a))    ?
         O[d(a)]      :
         a            ;
}

Q R(C a){return ('a'<=a&&a<='z')?ar(a-'a'):0;} 
Q N(C a){return ('0'<=a&&a<='9')?an(a-'0'):0;}
Q V(C a){for(D i=0;i<8;i++){if(VT[i]==a){return av(i);}}return 0;} 
Q* pe(C*b){D l=strlen(b);Q* q=malloc(8*l);D i=0;
  for(;i<l;i++){
    Q a;q[i]=(a=R(b[i]))?a:(a=V(b[i]))?a:(a=N(b[i]))?a:0;
  }
  q[i]=0;
  return q;
}

C buffer[100];
D main(void){
  while (1) {
    printf(" "); if (!fgets(buffer, 100, stdin)){break;}
    buffer[strcspn(buffer, "\r")] = '\0'; buffer[strcspn(buffer, "\n")] = '\0';
    if (strcmp(buffer, "\\\\") == 0){break;}
    pr(e(pe(buffer)));
  }
  return 0;
}

/**
 * Can I come up with a better type 0? 
 *  issue is that we have to store absolute pointers which can point anywhere in memory.
 *  I want to make sure that certain allocations happen in contiguous spaces at once. 
 *  
 *  suppose l:(0;1 2;(3 4;(5 6;7 8;9 10 11 12 13 14 15));16;17 18)
 * 
 *  I want
 *  (5 1 2 2 2 3 2 2 7 1  2 ; n
 *   0 0 1 3 3 5 5 7 9 16 17; offset from base
 *   0 0 0 0 3 3 5 5 5 0  0 ; parent
 *   0 1 2 3 4 5 6 7 8  9 10 11 12 13 14 15 16 17 18) data
 *  
 * even better would be
 *  (5 1 2 2 1  2  2 3 2 2 7 ; n
 *   0 0 1 3 16 17 3 5 5 7 9 ; offset from base
 *   0 0 0 0 0  0  3 3 5 5 5 ; parent
 *   0 1 2 3 4 5 6 7 8  9 10 11 12 13 14 15 16 17 18) data
 * so that all elements would be stored in depth order. 
 * the size of the metadata vectors is related to the size of each of the lists.
 * note that rows where parent=offset from base are the start of sublists
 * 
 * even even better would be to eliminate the parent and instead use first child
 * 
 * ( 5 1 2 2 1  2  2 3 2 2 7 ; n
 *   0 0 1 3 16 17 3 5 5 7 9 ; offset from base
 *   1 0 0 6 0  0  0 9 0 0 0 ; first child (0 if no children)
 *   0 1 2 3 4 5 6 7 8  9 10 11 12 13 14 15 16 17 18) data
 *  
 *  versus
 *  p0->[a1,p2,p3,a2,p9]
 *  p3->[p4,p5]
 *  p5->[p6,p7,p8]
 *  
 *  which is 10 pointers x 8 bytes/pointer = 80 bytes
 * 
 *  Memory allocation factors for consideration: 
 *   A range of low bits in a pointer can be guaranteed to be 0 by changing the smallest allocation size. 
 *   byte aligned is multiple of 8   000
 *   w    aligned                16  0000
 *   d                           32  00000
 *   q                           64  000000
 *   o                           128 0000000
 *   h                           256 00000000
 *   i                           512 000000000
 * 
 * and so on.
 * 
 * atoms are annoying. they reduce regularity in the codebase in order to avoid fetches from memory
 *  you need to believe that atoms are common in order to build this into the system. 
 *  
 * how can I take advantage of not having atoms in my language? 
 *  the point of atoms is that they are easy to pass around. They look the same as any other data
 *  but you don't need to fetch the actual data from memory
 *  you need to find a super nice encoding that allows for    
 * 
 * is there really a need to do type checking in the evaluator? 
 *  the types are float and int
 *  the sizes of each of the types can vary
 *  the presentation of each of the types can vary
 * 
 * 
 */