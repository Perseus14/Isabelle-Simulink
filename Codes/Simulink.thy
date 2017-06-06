theory Simulink
imports Main  
begin

(*fun Gain :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "Gain x y = mult x y"*)
primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

primrec mult :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mult 0 n = 0" |
  "mult (Suc m) n = add (mult m n) m"

primrec pow :: "nat => nat => nat" where
  "pow 0 x       = Suc 0" | 
  "pow (Suc n) x = mult x (pow n x)"
  
  
definition
  threegains :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "threegains t x y z = t*x*y*z"
declare threegains_def[simp] 

primrec feedback :: "nat \<Rightarrow> nat" where
  "feedback 0 = Suc(0)"|
  "feedback (Suc t) = (feedback t)*3"

  
theorem sum_of_naturals:
  "2 * (\<Sum>i::nat=0..n. i) = n * (n + 1)"
  (is "?P n" is "?S n = _")
proof (induct n)
  show "?P 0" by simp
next
  fix n have "?S (n + 1) = ?S n + 2 * (n + 1)"
    by simp
  assume "?P n"
  also have "\<dots> + 2 * (n + 1) = (n + 1) * (n + 2)"
    by simp
  finally show "?P (Suc n)"
    by simp
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
  