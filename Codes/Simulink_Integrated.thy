theory Simulink_Integrated
imports Main Complex_Main  
begin

(*fun Gain :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "Gain x y = mult x y"*)

primrec feedback :: "nat \<Rightarrow> nat" where
  "feedback 0 = Suc(0)"|
  "feedback (Suc t) = (feedback t)*3"

fun simulink :: "real \<Rightarrow> real" where
  "simulink 0 = 1"|
  "simulink(t+h) = simulink(t) + h*(1/simulink(t))"

fun y :: "nat \<Rightarrow> nat" where
  "y 0 = Suc(0)"|
  "y(Suc(t)) = y(t) + (y(t))"
  
lemma int_th2: "\<not>(t>5) \<or> ((y t) > 30)"  
proof (induct t) 
  case 0
  show ?case by simp
next
  case (Suc t)
  thus ?case
  proof
    assume "\<not>t > 5"
    moreover have "y 6 = 64" by code_simp 
      -- \<open>"simp add: eval_nat_numeral" would also work\<close>
    ultimately show ?thesis
      by (cases "t = 5") auto
  next
    assume "y t > 30"
    thus ?thesis by simp
  qed
qed
  
lemma th1: "threegains 3 4 5 6 = 360"
  apply(simp)
  done    

(*
lemma th3: "feedback t = pow 3 t"
  apply(induct t)
  apply(simp)
  apply(auto)
  apply(sym)  
done *)   
(*\<lbrakk> if foo then a \<noteq> a else b \<noteq> b \<rbrakk>*)

(*  
lemma th2: "\<not>(t>5) \<or> ((feedback t) > 200)" (is "?H(t)" is "?P(t)\<or>?Q(t)" is "(?P(t))\<or>(?F(t) > 200)") 
proof(induct t) 
    case 0 show "?P 0 \<or> ?Q 0" by simp
  next 
    have b: "?F (Suc(t)) \<ge> ?F(t)" by simp
    assume a:" ?F(t) > 200"
    from b and a have c: "?F(Suc(t)) > 200" by simp
    from c have e: "?Q(Suc(t))" by simp    
    assume d: "?P(t) = False"
    from d have f:"?P(Suc(t)) = False" by simp
    from f and e have g: "?P(Suc(t))\<or>?Q(Suc(t))" by simp
    from a and d and g have h: "?P(t)\<or>?Q(t) \<Longrightarrow> ?P(Suc(t))\<or>?Q(Suc(t))" by simp 
    from a and d have "?H(Suc(t))" by simp   
  qed
*)    
lemma th2: "\<not>(t>5) \<or> ((feedback t) > 200)"  
proof (induct t) 
  case 0
  show ?case by simp
next
  case (Suc t)
  thus ?case
  proof
    assume "\<not>t > 5"
    moreover have "feedback 6 = 729" by code_simp 
      -- \<open>"simp add: eval_nat_numeral" would also work\<close>
    ultimately show ?thesis
      by (cases "t = 5") auto
  next
    assume "feedback t > 200"
    thus ?thesis by simp
  qed
qed    
  
lemma th3: "\<not>(t>5) \<or> ((feedback t) > 200)"  
proof (induct t) 
  case (Suc t)
  moreover have "feedback 6 = 729" by code_simp
  ultimately show ?case by (cases "t = 5") auto
qed simp_all  
  