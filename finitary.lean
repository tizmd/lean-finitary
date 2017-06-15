import .equipotent .data.fin.misc

universe u 

def finitary (α : Type u) (n) := equipotent α (fin n) 
def permutation (n) := finitary (fin n) n 

namespace finitary  

def eq_of_finitary_fin {m n} : finitary (fin m) n → m = n 
:= assume H, 
   decidable.by_contradiction $ assume ne, 
     or.elim (lt_or_gt_of_ne ne) 
       (assume Hlt, fin.not_injective_of_gt _ Hlt 
         (bijection.injective_of_bijection H.bijection.inverse)) 
         (assume Hgt, fin.not_injective_of_gt _ Hgt (bijection.injective_of_bijection H.bijection))

variable {α : Type u}

lemma univalence {m n} : finitary α n → finitary α m → n = m := 
  assume Hn Hm, 
     eq_of_finitary_fin (equipotent.trans (equipotent.symm Hn) Hm)      

lemma {v} equipotent_of_eq {n} {β : Type v} : finitary α n → finitary β n → equipotent α β 
:= assume Ha Hb, equipotent.trans Ha (equipotent.symm Hb)

def empty_0 : finitary empty 0 := 
{
    map := empty.rec _, 
    bijection := {
        inv := fin.elim0,
        left_inverse_of_inv := empty.rec _,
        right_inverse_of_inv := take i, absurd i.is_lt (nat.not_lt_zero _)
    }
} 
private lemma fin1_eq_zero : ∀ i : fin 1, i = 0 
| ⟨0, is_lt⟩ := rfl 
| ⟨n+1, is_lt⟩ := absurd (nat.lt_of_succ_lt_succ is_lt) (nat.not_lt_zero _) 

instance : subsingleton (fin 1) := subsingleton.intro 
  (λ i j, begin rw fin1_eq_zero i, rw fin1_eq_zero j end) 
end finitary 


