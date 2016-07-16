FLAG = -g -pg


pta : pta.o redlib/redlib.a redcplugins.o;
	gcc ${FLAG} -o pta pta.o redlib/redlib.a redcplugins.o 

pta.o : pta.c redlib.h redlib.e;
	gcc ${FLAG} -c  pta.c
	
redcplugins.o : redcplugins.c redlib.h redlib.e;
	gcc ${FLAG} -c  redcplugins.c
