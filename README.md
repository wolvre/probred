# probred
Probabilistic RED

A prototype tool for the reachability analysis of probabilistic timed automata based on an integrated quantitative state-space representation, which is an extension of RED diagrams.

# To compile it
```
cd redlib
make
cd ..
make
```

# To run it
>pta -Tg -Max -G0.000001 <.d> <.goal> <.prob>

>pta -Tg -Min -G0.000001 <.d> <.goal> <.prob>

args    |description
--------|----------------------
-Tg     |reachability analysis
-Max    |maximum probability
-Min    |minimum probability
-G      |precision threshold
<.d>    |model file            
<.goal> |symbolic target state 
<.prob> |probability file      
