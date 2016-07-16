process count = 3;
global synchronizer REQ,MESSAGE,ACK,DECODE,FINISHED,STOP,ERROR,DECODED_RANDOM,DECODED_LAST;

local discrete o:0 .. 12;
local clock x;
local discrete r:0 .. 3;
local clock y;

mode originator (((o==0)=>(true))&&((o==1)=>(x<=0))&&((o==2)=>(x<=5))&&((o==3)=>(x<=0))&&((o==4)=>(x<=0))&&((o==5)=>(x<=0))&&((o==6)=>(true))&&((o==7)=>(true))&&((o==8)=>(true))&&((o==9)=>(true))&&((o==10)=>(true))&&((o==11)=>(x<=5))&&((o==12)=>(x<=5))) {
/*1*/
when ?REQ (o==0) may o=1;x=0;
/*2*/
when ?MESSAGE ((o==1)&&(x<=0)) may o=2;
/*3*/
when ?ACK ((o==2)&&((x>=1)&&(x<=4))) may o=1;x=0;
/*4*/
when ?ACK ((o==2)&&((x>=1)&&(x<=4))) may o=3;x=0;
/*5*/
when ((o==2)&&(x>4)) may o=1;x=0;
/*6*/
when ((o==2)&&(x>4)) may o=3;x=0;
/*7*/
when ?DECODE (o==2) may o=6;
/*8*/
when ?DECODE (o==2) may o=7;
/*9*/
when ?FINISHED (o==3) may o=8;x=0;
/*10*/
when (o==8) may o=8;
/*11*/
when (o==9) may o=9;
/*12*/
when (o==10) may o=10;
/*13*/
when ?STOP (o==4) may o=9;
/*14*/
when ?ERROR (o==5) may o=10;
/*15*/
when ?DECODED_RANDOM (o==6) may o=11;
/*16*/
when ?DECODED_LAST (o==7) may o=12;
/*17*/
when ?ACK ((o==11)&&((x>=1)&&(x<=4))) may o=1;x=0;
/*18*/
when ?STOP ((o==11)&&(x>4)) may o=9;x=0;
/*19*/
when ?ACK ((o==12)&&((x>=1)&&(x<=4))) may o=3;x=0;
/*20*/
when ?STOP ((o==12)&&(x>4)) may o=10;x=0;
}
 
mode recipient (((r==0)=>(y<=0))&&((r==1)=>(true))&&((r==2)=>(y<=4))&&((r==3)=>(true))) {
/*21*/
when ?REQ ((r==0)&&(y==0)) may r=1;
/*22*/
when ?MESSAGE (r==1) may r=2;y=0;
/*23*/
when ?FINISHED (r==1) may r=3;
/*24*/
when ?ACK ((r==2)&&((y>=1)&&(y<=4))) may r=1;y=0;
/*25*/
when ?DECODE (r==3) may r=3;
/*26*/
when ?DECODED_RANDOM (r==3) may r=3;
/*27*/
when ?DECODED_LAST (r==3) may r=3;
}
 

mode signal(true){
/*28*/
when !(2)REQ(true) may;
/*29*/
when !(2)MESSAGE(true) may;
/*30*/
when !(2)ACK(true) may;
/*31*/
when !(2)DECODE(true) may;
/*32*/
when !(2)FINISHED(true) may;
/*33*/
when !(1)STOP(true) may;
/*34*/
when !(1)ERROR(true) may;
/*35*/
when !(2)DECODED_RANDOM(true) may;
/*36*/
when !(2)DECODED_LAST(true) may;
}

initially 
signal@(3)
 && originator@(1) && o@(1)==0 && x@(1)==0
 && recipient@(2) && r@(2)==0 && y@(2)==0
;
