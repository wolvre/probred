process count = 5;
global synchronizer SND_REQ12,SND_ACK12,SND_IDLE12,REC_REQ12,REC_ACK12,REC_IDLE12,REC_IDLE21,REC_REQ21,REC_ACK21,LOOP,SND_REQ21,SND_IDLE21,SND_ACK21;
#define rc_fast_max 850
#define rc_fast_min 760
#define rc_slow_max 1670
#define rc_slow_min 1590
#define delay 360
#define fast 0.5
#define slow 0.5

local discrete w12:0 .. 9;
local discrete w21:0 .. 9;
local clock y1;
local clock z1;
local clock y2;
local clock z2;
local clock x1;
local clock x2;
local discrete s1:0 .. 8;
local discrete s2:0 .. 8;

mode wire12 (((w12==1)=>(y2<=360))&&((w12==2)=>(y1<=360))&&((w12==3)=>(y2<=360))&&((w12==4)=>(y1<=360))&&((w12==5)=>(y2<=360))&&((w12==6)=>(y1<=360))&&((w12==7)=>(y1<=360))&&((w12==8)=>(y1<=360))&&((w12==9)=>(y1<=360))) {
/*1*/
when ?SND_REQ12 (w12==0) may w12=1;y1=0;y2=0;
/*2*/
when ?SND_ACK12 (w12==0) may w12=3;y1=0;y2=0;
/*3*/
when ?SND_IDLE12 (w12==0) may w12=5;y1=0;y2=0;
/*4*/
when ?SND_REQ12 (w12==1) may w12=1;
/*5*/
when ?REC_REQ12 (w12==1) may w12=0;y1=0;y2=0;
/*6*/
when ?SND_ACK12 (w12==1) may w12=2;y2=0;
/*7*/
when ?SND_IDLE12 (w12==1) may w12=8;y2=0;
/*8*/
when ?SND_ACK12 (w12==2) may w12=2;
/*9*/
when ?REC_REQ12 (w12==2) may w12=3;
/*10*/
when ?SND_ACK12 (w12==3) may w12=3;
/*11*/
when ?REC_ACK12 (w12==3) may w12=0;y1=0;y2=0;
/*12*/
when ?SND_IDLE12 (w12==3) may w12=4;y2=0;
/*13*/
when ?SND_REQ12 (w12==3) may w12=7;y2=0;
/*14*/
when ?SND_IDLE12 (w12==4) may w12=4;
/*15*/
when ?REC_ACK12 (w12==4) may w12=5;
/*16*/
when ?SND_IDLE12 (w12==5) may w12=5;
/*17*/
when ?REC_IDLE12 (w12==5) may w12=0;y1=0;y2=0;
/*18*/
when ?SND_REQ12 (w12==5) may w12=6;y2=0;
/*19*/
when ?SND_ACK12 (w12==5) may w12=9;y2=0;
/*20*/
when ?SND_REQ12 (w12==6) may w12=6;
/*21*/
when ?REC_IDLE12 (w12==6) may w12=1;
/*22*/
when ?SND_REQ12 (w12==7) may w12=7;
/*23*/
when ?REC_ACK12 (w12==7) may w12=1;
/*24*/
when ?SND_IDLE12 (w12==8) may w12=8;
/*25*/
when ?REC_REQ12 (w12==8) may w12=5;
/*26*/
when ?SND_ACK12 (w12==9) may w12=9;
/*27*/
when ?REC_IDLE12 (w12==9) may w12=3;
}
 
mode node1 (((s1==2)=>(x1<=850))&&((s1==3)=>(x1<=1670))&&((s1==4)=>(x1<=850))&&((s1==5)=>(x1<=1670))&&((s1==0)=>(x1<=0))&&((s1==1)=>(x1<=0))) {
/*28*/
when ?SND_IDLE12 ((s1==0)&&(x1==0)) may s1=2;
/*29*/
when ?SND_IDLE12 ((s1==0)&&(x1==0)) may s1=3;
/*30*/
when ?REC_IDLE21 ((s1==0)&&(x1==0)) may s1=1;
/*31*/
when ?SND_IDLE12 ((s1==1)&&(x1==0)) may s1=4;
/*32*/
when ?SND_IDLE12 ((s1==1)&&(x1==0)) may s1=5;
/*33*/
when ?REC_REQ21 ((s1==1)&&(x1==0)) may s1=0;
/*34*/
when ?REC_IDLE21 (s1==2) may s1=4;
/*35*/
when ?SND_ACK12 ((s1==2)&&(x1>=760)) may s1=7;x1=0;
/*36*/
when ?REC_IDLE21 (s1==3) may s1=5;
/*37*/
when ?SND_ACK12 ((s1==3)&&(x1>=1590)) may s1=7;x1=0;
/*38*/
when ?REC_REQ21 (s1==4) may s1=2;
/*39*/
when ?SND_REQ12 ((s1==4)&&(x1>=760)) may s1=6;x1=0;
/*40*/
when ?REC_REQ21 (s1==5) may s1=3;
/*41*/
when ?SND_REQ12 ((s1==5)&&(x1>=1590)) may s1=6;x1=0;
/*42*/
when ?REC_REQ21 (s1==6) may s1=0;x1=0;
/*43*/
when ?REC_ACK21 (s1==6) may s1=8;x1=0;
/*44*/
when ?LOOP (s1==7) may ;
/*45*/
when ?LOOP (s1==8) may ;
}
 
mode wire21 (((w21==1)=>(z2<=360))&&((w21==2)=>(z1<=360))&&((w21==3)=>(z2<=360))&&((w21==4)=>(z1<=360))&&((w21==5)=>(z2<=360))&&((w21==6)=>(z1<=360))&&((w21==7)=>(z1<=360))&&((w21==8)=>(z1<=360))&&((w21==9)=>(z1<=360))) {
/*46*/
when ?SND_REQ21 (w21==0) may w21=1;z1=0;z2=0;
/*47*/
when ?SND_ACK21 (w21==0) may w21=3;z1=0;z2=0;
/*48*/
when ?SND_IDLE21 (w21==0) may w21=5;z1=0;z2=0;
/*49*/
when ?SND_REQ21 (w21==1) may w21=1;
/*50*/
when ?REC_REQ21 (w21==1) may w21=0;z1=0;z2=0;
/*51*/
when ?SND_ACK21 (w21==1) may w21=2;z2=0;
/*52*/
when ?SND_IDLE21 (w21==1) may w21=8;z2=0;
/*53*/
when ?SND_ACK21 (w21==2) may w21=2;
/*54*/
when ?REC_REQ21 (w21==2) may w21=3;
/*55*/
when ?SND_ACK21 (w21==3) may w21=3;
/*56*/
when ?REC_ACK21 (w21==3) may w21=0;z1=0;z2=0;
/*57*/
when ?SND_IDLE21 (w21==3) may w21=4;z2=0;
/*58*/
when ?SND_REQ21 (w21==3) may w21=7;z2=0;
/*59*/
when ?SND_IDLE21 (w21==4) may w21=4;
/*60*/
when ?REC_ACK21 (w21==4) may w21=5;
/*61*/
when ?SND_IDLE21 (w21==5) may w21=5;
/*62*/
when ?REC_IDLE21 (w21==5) may w21=0;z1=0;z2=0;
/*63*/
when ?SND_REQ21 (w21==5) may w21=6;z2=0;
/*64*/
when ?SND_ACK21 (w21==5) may w21=9;z2=0;
/*65*/
when ?SND_REQ21 (w21==6) may w21=6;
/*66*/
when ?REC_IDLE21 (w21==6) may w21=1;
/*67*/
when ?SND_REQ21 (w21==7) may w21=7;
/*68*/
when ?REC_ACK21 (w21==7) may w21=1;
/*69*/
when ?SND_IDLE21 (w21==8) may w21=8;
/*70*/
when ?REC_REQ21 (w21==8) may w21=5;
/*71*/
when ?SND_ACK21 (w21==9) may w21=9;
/*72*/
when ?REC_IDLE21 (w21==9) may w21=3;
}
 
mode node2 (((s2==2)=>(x2<=850))&&((s2==3)=>(x2<=1670))&&((s2==4)=>(x2<=850))&&((s2==5)=>(x2<=1670))&&((s2==0)=>(x2<=0))&&((s2==1)=>(x2<=0))) {
/*73*/
when ?SND_IDLE21 ((s2==0)&&(x2==0)) may s2=2;
/*74*/
when ?SND_IDLE21 ((s2==0)&&(x2==0)) may s2=3;
/*75*/
when ?REC_IDLE12 ((s2==0)&&(x2==0)) may s2=1;
/*76*/
when ?SND_IDLE21 ((s2==1)&&(x2==0)) may s2=4;
/*77*/
when ?SND_IDLE21 ((s2==1)&&(x2==0)) may s2=5;
/*78*/
when ?REC_REQ12 ((s2==1)&&(x2==0)) may s2=0;
/*79*/
when ?REC_IDLE12 (s2==2) may s2=4;
/*80*/
when ?SND_ACK21 ((s2==2)&&(x2>=760)) may s2=7;x2=0;
/*81*/
when ?REC_IDLE12 (s2==3) may s2=5;
/*82*/
when ?SND_ACK21 ((s2==3)&&(x2>=1590)) may s2=7;x2=0;
/*83*/
when ?REC_REQ12 (s2==4) may s2=2;
/*84*/
when ?SND_REQ21 ((s2==4)&&(x2>=760)) may s2=6;x2=0;
/*85*/
when ?REC_REQ12 (s2==5) may s2=3;
/*86*/
when ?SND_REQ21 ((s2==5)&&(x2>=1590)) may s2=6;x2=0;
/*87*/
when ?REC_REQ12 (s2==6) may s2=0;x2=0;
/*88*/
when ?REC_ACK12 (s2==6) may s2=8;x2=0;
/*89*/
when ?LOOP (s2==7) may ;
/*90*/
when ?LOOP (s2==8) may ;
}
 

mode signal(true){
/*91*/
when !(2)SND_REQ12(true) may;
/*92*/
when !(2)SND_ACK12(true) may;
/*93*/
when !(2)SND_IDLE12(true) may;
/*94*/
when !(2)REC_REQ12(true) may;
/*95*/
when !(2)REC_ACK12(true) may;
/*96*/
when !(2)REC_IDLE12(true) may;
/*97*/
when !(2)REC_IDLE21(true) may;
/*98*/
when !(2)REC_REQ21(true) may;
/*99*/
when !(2)REC_ACK21(true) may;
/*100*/
when !(2)LOOP(true) may;
/*101*/
when !(2)SND_REQ21(true) may;
/*102*/
when !(2)SND_IDLE21(true) may;
/*103*/
when !(2)SND_ACK21(true) may;
}

initially 
signal@(5)
 && wire12@(1) && w12@(1)==0 && y1@(1)==0 && y2@(1)==0
 && node1@(2) && x1@(2)==0 && s1@(2)==0
 && wire21@(3) && w21@(3)==0 && z1@(3)==0 && z2@(3)==0
 && node2@(4) && x2@(4)==0 && s2@(4)==0
;
