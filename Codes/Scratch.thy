theory Sum
imports Main  
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
text \<open>
  The sum of natural numbers \<open>0 + \<cdots> + n\<close> equals \<open>n \<times> (n + 1)/2\<close>. Avoiding
  formal reasoning about division we prove this equation multiplied by \<open>2\<close>.
\<close>
    
theorem sum_formula: "2*sum_till n = n*(n+1)"
  apply (induct n)
  apply (auto) 
  done  
    
end  