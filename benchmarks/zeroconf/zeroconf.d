process count = 3;
global synchronizer SEND_USED,SEND_FRESH,RECV;
#define probes_max 4

local discrete s:0 .. 2;
local discrete probes:0 .. 4;
local discrete ip:0 .. 2;
local clock x;
local discrete e:0 .. 2;
local clock y;

mode sender (((s==0)=>(x<=0))&&((s==1)=>(x<=20))&&((s==2)=>(true))) {
/*1*/
when (s==0) may s=1;ip=1;
/*2*/
when (s==0) may s=1;ip=2;
/*3*/
when ?SEND_USED ((((s==1)&&(x==20))&&(ip==2))&&(probes<4)) may probes=(probes+1);x=0;
/*4*/
when ?SEND_FRESH ((((s==1)&&(x==20))&&(ip==1))&&(probes<4)) may probes=(probes+1);x=0;
/*5*/
when (((s==1)&&(x==20))&&(probes==4)) may s=2;x=0;
/*6*/
when ?RECV (s==1) may s=0;x=0;ip=0;probes=0;
/*7*/
when (s==2) may ;
}
 
mode environment (((e==0)=>(true))&&((e>=1)=>(y<=5))) {
/*8*/
when ?SEND_FRESH (e==0) may ;
/*9*/
when ?SEND_USED (e==0) may e=0;y=0;
/*10*/
when ?SEND_USED (e==0) may e=1;y=0;
/*11*/
when ((e==1)&&(y>=1)) may e=0;y=0;
/*12*/
when ((e==1)&&(y>=1)) may e=2;y=0;
/*13*/
when ?RECV ((e==2)&&(y>=1)) may e=0;y=0;
}
 

mode signal(true){
/*14*/
when !(2)SEND_USED(true) may;
/*15*/
when !(2)SEND_FRESH(true) may;
/*16*/
when !(2)RECV(true) may;
}

initially 
signal@(3)
 && sender@(1) && s@(1)==0 && probes@(1)==0 && ip@(1)==0 && x@(1)==0
 && environment@(2) && e@(2)==0 && y@(2)==0
;
