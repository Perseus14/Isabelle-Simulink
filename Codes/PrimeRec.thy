theory PrimeRec
imports Main
begin

datatype nati = Zero | Suc nati
  
primrec add :: "nati \<Rightarrow> nati \<Rightarrow> nati" where
"add Zero n = n" |
"add (Suc m) n = Suc(add m n)"

primrec mult :: "nati \<Rightarrow> nati \<Rightarrow> nati" where
  "mult Zero n = Zero" |
  "mult (Suc m) n = add (mult m n) m"

primrec pow :: "nati => nati => nati" where
  "pow Zero x       = Suc Zero" | 
  "pow (Suc n) x = mult x (pow n x)"

primrec pow :: "nat => nat => nat" where
  "pow x 0       = Suc 0"
| "pow x (Suc n) = x * pow x n"  
  
lemma add_02[simp]: "add a Zero = a"
apply(induction a)
apply(auto)
done

lemma add_Associativ[simp]: "add(add a b) c = add a (add b c)"
apply(induction a)
apply(auto)
done   

lemma add_suc[simp]: "add a (Suc b) = Suc( add a b)"
apply(induction a)
apply(simp)
apply(simp)    
done  
  
lemma add_com[simp]: "add a b= add b a"
apply(induction a)
apply(simp)
apply(simp)    
done

lemma a1: "(a + a) = 2*a"  
apply(arith) 
done    
    
lemma mult_a0: "add a a = mult(a Suc(Suc(Zero)))"
done    
end