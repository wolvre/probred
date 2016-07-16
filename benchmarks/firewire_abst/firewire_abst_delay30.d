process count = 2;
#define rc_fast_max 850
#define rc_fast_min 760
#define rc_slow_max 1670
#define rc_slow_min 1590
#define delay 30
#define fast 0.5
#define slow 0.5

local clock x;
local discrete s:0 .. 9;

mode abstract_firewire (((s==0)=>(x<=30))&&((s==1)=>(x<=30))&&((s==2)=>(x<=30))&&((s==3)=>(x<=30))&&((s==4)=>(x<=30))&&((s==5)=>(x<=850))&&((s==6)=>(x<=1670))&&((s==7)=>(x<=1670))&&((s==8)=>(x<=1670))) {
/*1*/
when (s==0) may s=1;
/*2*/
when (s==0) may s=4;
/*3*/
when (s==0) may s=2;
/*4*/
when (s==0) may s=3;
/*5*/
when (s==1) may s=5;x=0;
/*6*/
when (s==1) may s=6;x=0;
/*7*/
when (s==2) may s=5;x=0;
/*8*/
when (s==2) may s=7;x=0;
/*9*/
when (s==3) may s=6;x=0;
/*10*/
when (s==3) may s=8;x=0;
/*11*/
when (s==4) may s=7;x=0;
/*12*/
when (s==4) may s=8;x=0;
/*13*/
when ((s==5)&&(x>=760)) may s=0;x=0;
/*14*/
when ((s==5)&&(x>=730)) may s=9;x=0;
/*15*/
when ((s==6)&&(x>=1560)) may s=9;x=0;
/*16*/
when ((s==7)&&(x>=1560)) may s=9;x=0;
/*17*/
when ((s==8)&&(x>=1590)) may s=0;x=0;
/*18*/
when ((s==8)&&(x>=1560)) may s=9;x=0;
/*19*/
when (s==9) may ;
}
 

mode signal(true){
}

initially 
signal@(2)
 && abstract_firewire@(1) && x@(1)==0 && s@(1)==0
;
