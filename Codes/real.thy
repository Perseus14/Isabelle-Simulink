(*  Title:      HOL/ex/Sqrt.thy
    Author:     Markus Wenzel, Tobias Nipkow, TU Muenchen
*)


theory real
imports Power Complex_Main "~~/src/HOL/Number_Theory/Primes"
begin

text {* The square root of any prime number (including 2) is irrational. *}


theorem sqrt-prime-irrational1: prime p \<Longrightarrow> sqrt (real p) \<notin> Q
apply clarsimp
apply (elim rationals-rep)
apply simp
apply (simp add : nonzero-eq-divide-eq)
apply (drule arg-cong [where f = \<lambda>x . x * x ])
apply (simp only: mult-ac)
apply (simp only: power2-eq-square[symmetric])
apply (simp only: real-sqrt-pow2 )
apply (simp only: mult-assoc[symmetric])
apply (simp add : power2-eq-square)
apply (simp only: real-of-nat-mult[symmetric])
apply (simp only: real-of-nat-inject)
apply (simp add : power2-eq-square[symmetric] eq-commute)
apply (frule-tac m=m in prime-dvd-power-two, simp)
apply (frule-tac m=n in prime-dvd-power-two)
apply (frule iffD1 [OF dvd-def ], clarsimp)
apply (simp add : power2-eq-square mult-ac prime-def )
apply (simp only: mult-assoc[symmetric])
apply (simp add : eq-commute)
apply (drule (1 ) gcd-greatest)
apply (thin-tac p dvd n)
apply (drule dvd-imp-le, simp)
apply (clarsimp simp: prime-def )
done  
  
end