theory Sum
imports Main Complex_Main  
begin

primrec sum :: "nat list => nat" where
"sum [] = 0"| 
"sum (x#l) = x + sum l"

primrec sum_till :: "nat \<Rightarrow> nat" where
 "sum_till 0 = 0"|
 "sum_till (Suc k) = sum_till (k) + Suc(k)" 

lemma sum_2_list [simp]: "sum (l1 @ l2) = sum l1 + sum l2"
  apply(induct l1)
  apply(auto)
  done

theorem sum_rev_list: "sum (rev l) = sum l"
  apply (induct l)
  apply (auto simp: sum_2_list)
  done    
    
theorem sum_formula: "sum_till n = n*(n+1) div 2"
  apply (induct n)
  apply (auto) 
  done  


theorem sum_n: "(\<Sum>i::nat=0..n. i) = n*(n+1::nat) div 2" (is "?P n")
proof(induct n)
  case 0
  show ?case by simp 
  case Suc
  fix n assume "?P n"    
  thus "?P(Suc n)" by simp
qed      


theorem sum_of_squares:
  "(\<Sum>i::nat=0..n. i^Suc (Suc 0)) = n * (n + 1) * (2 * n + 1) div 6"
(is "?P n")  
proof (induct n)
  case 0
  show ?case by simp 
  case Suc
  fix n assume "?P n"    
  thus "?P(Suc n)" by (simp add: add_mult_distrib add_mult_distrib2)
qed

  
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
  
end  