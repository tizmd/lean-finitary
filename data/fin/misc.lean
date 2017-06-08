import function.isomorphism data.list.distinct
open fin function



namespace fin
protected
lemma le_refl {n} (a : fin n) : a ≤ a := fin.cases_on a (λ a _, nat.le_refl a)
protected
lemma le_trans {n} {a b c : fin n} : a ≤ b → b ≤ c → a ≤ c := 
fin.cases_on a (λ _ _, 
fin.cases_on b (λ _ _,
fin.cases_on c (λ _ _,
  assume Hab Hbc,
  nat.le_trans Hab Hbc
)
)
)

protected 
lemma le_antisymm {n}{a b : fin n} : a ≤ b → b ≤ a → a = b :=
fin.cases_on a (λ _ _,
fin.cases_on b (λ _ _,
  assume Hab Hba,
  fin.eq_of_veq (nat.le_antisymm Hab Hba)
)
)

instance {n} : decidable_linear_order (fin n) :=
{
  lt := fin.lt,
  le := fin.le,
  le_refl := fin.le_refl,
  le_trans := @fin.le_trans _,
  le_antisymm := @fin.le_antisymm _,
  le_iff_lt_or_eq := λ a b, 
    fin.cases_on a (λ i _,
    fin.cases_on b (λ j _,
     iff.intro (assume H, or.elim (nat.lt_or_eq_of_le H) or.inl (assume Heq, or.inr (fin.eq_of_veq Heq))) 
       (assume H, nat.le_of_lt_or_eq (or.imp id (begin intro heq, apply (fin.veq_of_eq heq) end) H))
    )
    ),
  lt_irrefl := λ a, fin.cases_on a (λ _ _, 
    nat.lt_irrefl _
  ),
  le_total := λ a b, fin.cases_on a (λ _ _, fin.cases_on b (λ _ _, nat.le_total)),
  decidable_lt := fin.decidable_lt,
  decidable_le := fin.decidable_le,
  decidable_eq := fin.decidable_eq _
}
def swap {n} (k : fin (n+1)) : fin (n+1) → fin (n+1) := take i, if i = k then 0 else if i = 0 then k else i

namespace swap
variables {n : ℕ } {k : fin (n+1)}
lemma idem : ∀ i, swap k (swap k i) = i
:= take i, if Hik : i = k then 
             if Hkz : k = 0 then by simp [Hik, Hkz, swap] else 
                begin 
                 simp_using_hs [swap],
                 apply if_neg,
                 intro H,
                 apply Hkz,
                 symmetry,
                 assumption
                end
           else if Hiz : i = 0 then 
                begin 
                 rw Hiz,
                 simp [swap],
                 apply if_pos,
                 apply if_neg,
                 intro H,
                 apply Hik,
                 rw Hiz,
                 assumption
                end else 
                by
                simp [swap];
                cc

lemma has_left_inverse  : has_left_inverse (swap k) := ⟨ swap k, idem ⟩         
lemma has_right_inverse  :  has_right_inverse (swap k) := ⟨ swap k, idem ⟩  
lemma has_isomorphism : has_isomorphism (swap k) := ⟨ swap k,  idem , idem ⟩ 

lemma injective : injective (swap k) := injective_of_has_left_inverse has_left_inverse
lemma surjective : surjective (swap k) := surjective_of_has_right_inverse has_right_inverse

instance : isomorphism (swap k) := ⟨ swap k, idem , idem ⟩ 

lemma k_eq_zero : swap k k = 0 := by simp [swap]
lemma zero_eq_k : swap k 0 = k := if H : 0 = k then by simp_using_hs [swap] else by simp_using_hs [swap]
lemma id_of_zero : swap 0 = @id (fin (n+1)) := 
  begin
  apply funext,
  intro i,
  simp_using_hs [swap],
  cases (fin.decidable_eq _ i 0) with H H,
  repeat {simp_using_hs}
  end
end swap

lemma ne_zero_of_succ {n} : ∀ i : fin n, fin.succ i ≠ 0 :=
 begin
  intros i, 
  cases i, 
  unfold fin.succ,
  intro H,
  apply (nat.succ_ne_zero val),
  apply (fin.veq_of_eq H),
 end 
lemma succ.injective {n} : injective (@fin.succ n) := 
begin
 intros fi fj H,
 cases fi with i ilt,
 cases fj with j jlt,
 simp [fin.succ] at H,
 apply fin.eq_of_veq,
 apply nat.succ.inj,
 simp,
 exact (fin.veq_of_eq H)
end

lemma pred.injective {n} {i j : fin (n + 1)} { ine0 : i ≠ 0} { jne0 : j ≠ 0} : fin.pred i ine0 = fin.pred j jne0 → i = j
:= 
begin 
cases i with ival ilt,
cases j with jval jlt,
simp [fin.pred],
intro H,
apply fin.eq_of_veq,
simp,
apply nat.pred_inj,
{
  -- ival > 0
  apply nat.pos_of_ne_zero,
  exact (fin.vne_of_ne ine0)
},
{
  -- jval > 0
  apply nat.pos_of_ne_zero,
  exact (fin.vne_of_ne jne0)
},
{
  exact (fin.veq_of_eq H)
}
end

theorem not_injective_of_gt {m n} (f : fin m → fin n) : m > n → ¬ injective f := 
begin
  revert m,
  induction n with n iH,
  {
      intros m f H Hinj,
      cases (f ⟨0, H⟩ ) with val is_lt,
      exact (absurd is_lt (nat.not_lt_zero _))
  },
  {
      intros m f Hmn Hinj,
      pose pred_m := nat.pred m,
      assert Hm : m = nat.succ pred_m, {
          symmetry,
          apply nat.succ_pred_eq_of_pos,
          transitivity,
          exact Hmn,
          apply nat.zero_lt_succ
      },
      revert f Hmn,
      rw Hm,
      intros f Hpmn Hinj,
      pose g := swap (f 0) ∘ f ∘ fin.succ,
      assert Hgnz : ∀ i, g i ≠ 0,
      {
        intros i Hgz,
        apply (ne_zero_of_succ i),
        apply Hinj,
        apply (@swap.injective _ (f 0)),
        rw swap.k_eq_zero,
        assumption
      },
      pose h := λ i, fin.pred (g i) (Hgnz i),
      apply (iH h),
        {
          apply nat.le_of_succ_le_succ,
          apply Hpmn,
        },
        {
            intros i₁ i₂ Heq,
            apply succ.injective,
            apply Hinj,
            apply swap.injective,
            apply pred.injective,
            assumption
        }
  }
end

def elems : ∀ n : ℕ, list (fin n)
| 0 := []
| (n+1) := 0 :: list.map fin.succ (elems n)

def mem_elems : ∀ {n} (i : fin n), i ∈ elems n 
| 0     ⟨_ , is_lt⟩ := absurd is_lt (nat.not_lt_zero _)
| (n+1) ⟨0 , _⟩ := list.mem_cons_self _ _
| (n+1) ⟨i + 1, is_lt⟩ := list.mem_cons_of_mem _ (list.mem_map fin.succ (mem_elems ⟨i, nat.le_of_succ_le_succ is_lt⟩))

def {u} nth { α : Type u} : Π (l : list α), fin (list.length l) → α 
| [] ⟨_, is_lt⟩  := absurd is_lt (nat.not_lt_zero _)
| (x :: xs) ⟨0, _⟩  := x 
| (_ :: xs) ⟨n+1, is_lt⟩ := nth xs ⟨n, nat.le_of_succ_le_succ is_lt⟩ 

lemma {u} mem_nth {α : Type u} : ∀ (l : list α) i, nth l i ∈ l
| [] ⟨_, is_lt⟩  := absurd is_lt (nat.not_lt_zero _)
| (x :: xs) ⟨0, _⟩ := list.mem_cons_self _ _
| (_ :: xs) ⟨i+1, is_lt⟩ := list.mem_cons_of_mem _ $ mem_nth xs ⟨i, nat.le_of_succ_le_succ is_lt⟩ 

def {u} left_index {α : Type u}[decidable_eq α]{a} : Π {l : list α}, a ∈ l → fin (list.length l)
| []      h := absurd h (list.not_mem_nil _)
| (x::xs) h := if H : a = x then (0 : fin ((list.length xs) + 1)) 
               else fin.succ $ left_index $ or.resolve_left h H

def {u} nth_left_index_left_inverse {α : Type u} [deq : decidable_eq α] {l : list α} {a} (h : a ∈ l) : nth l (left_index h) = a := 
begin
induction l with x xs iH,
{
  exact (absurd h (list.not_mem_nil _))
},
{
  unfold left_index,
  cases (deq a x) with Hne Heq,
  {
    rw dif_neg,
    assert Hmem : a ∈ xs, apply or.resolve_left, assumption, assumption,
    change nth (x :: xs) (fin.succ (left_index Hmem)) = a,
    assert Lem : ∀ a x (xs : list α)(H : a ∈ xs), nth (x :: xs) (fin.succ (left_index H)) = nth xs (left_index H),
    {
      intros a x xs H,
      generalize (left_index H) i,
      intro i,
      cases i,
      simp [fin.succ, nth],
      refl
    },
    rw Lem,
    apply iH,
    assumption 
  },
  {
    rw dif_pos,
    rw Heq,
    refl,
    assumption
  }
}
end


lemma {u} nth_ne_nth_of_distinct_of_lt {α : Type u} {l : list α}  : Π {i j : fin (list.length l)}, distinct l → i < j → nth l i ≠ nth l j :=
begin
induction l with x xs iH,
{
  intro i,
  exact (absurd i.is_lt (nat.not_lt_zero _))
},
{
  intros i j Hdis Hlt Heq,
  cases i with i ilt,
  cases j with j jlt,
  assert Hj : j = nat.succ (nat.pred j),
  {
    symmetry,
    apply nat.succ_pred_eq_of_pos,
    apply nat.lt_of_le_of_lt,
    apply nat.zero_le,
    assumption
  },
  revert jlt,
  rw Hj,
  intros jlt Hlt Heq,
  cases i with i,
  {
    simp [nth] at Heq,
    apply (not_mem_of_distinct_cons Hdis),
    rw Heq,
    apply mem_nth
  },
  {
    simp [nth] at Heq,
    apply (@iH ⟨i, nat.lt_of_succ_lt_succ ilt⟩ ⟨nat.pred j, nat.lt_of_succ_lt_succ jlt⟩ ),
    apply distinct_of_distinct_cons,
    assumption,
    exact (nat.lt_of_succ_lt_succ Hlt),
    assumption
  }
}
end
lemma {u} left_index_mem_nth_left_inverse_of_distinct {α : Type u}[decidable_eq α]{l : list α} : distinct l → ∀ i, left_index (mem_nth l i) = i :=
begin
intros Hdis i,
induction Hdis with x xs dxs Hx iH,
{
  exact (absurd i.is_lt (nat.not_lt_zero _))
},
{
  cases i with i ilt,
  cases i with i,
  {
    change left_index (list.mem_cons_self x xs) = ⟨0, _⟩,
    simp [left_index],
    rw dif_pos,
    refl,
    refl
  },
  {
    simp [left_index, mem_nth],
    rw dif_neg,
    assert Lem : ∀ {n}(i : fin n), (fin.succ i).val = nat.succ i.val, 
    {
      intros n i,
      cases i,
      simp [fin.succ]
    },
    apply fin.eq_of_veq,
    rw Lem,
    simp,
    apply (congr_arg nat.succ),
    pose j : fin (list.length xs) := ⟨i, nat.lt_of_succ_lt_succ ilt⟩, 
    change (left_index (mem_nth xs j)).val = j.val,
    apply fin.veq_of_eq,
    apply iH,
    simp [nth],
    intro H,
    apply Hx,
    rw -H,
    apply mem_nth
  }
}
end
lemma {u} injective_nth_of_distinct {α : Type u}{l : list α} : distinct l → injective (nth l) :=
  assume Hdis, take i j, assume H, 
      if Heq : i = j then Heq
      else if Hlt : i < j then absurd H (nth_ne_nth_of_distinct_of_lt Hdis Hlt) 
      else have j < i, from or.resolve_left (lt_or_gt_of_ne Heq) Hlt,
           absurd (eq.symm H) (nth_ne_nth_of_distinct_of_lt Hdis this)
lemma length_le_of_distinct_fin {n} {l : list (fin n)} : distinct l → list.length l ≤ n :=
begin
 intro Hdis,
 induction l with x xs iH, 
 {
   exact (nat.zero_le _)
 },
 {
    apply le_of_not_gt,
    unfold list.length,
    intro Hgt,
    pose f : fin (list.length xs + 1) → fin n := nth (x::xs),
    apply not_injective_of_gt f Hgt,
    intros i j Hf,
    cases (fin.decidable_eq _ i j) with Hne Heq,
      {
        assert Ho : i < j ∨ i > j,
        {
          cases i with i ilt,
          cases j with j jlt,
          change (i < j ∨ i > j),
          apply lt_or_gt_of_ne,
          apply (fin.vne_of_ne Hne)
        },
       cases Ho with Hlt Hgt,
       {
          exact (absurd Hf (nth_ne_nth_of_distinct_of_lt Hdis Hlt))
       },
       {
         exact (absurd (eq.symm Hf) (nth_ne_nth_of_distinct_of_lt Hdis Hgt))
       }
       
      },
      {
        exact Heq
      }
 }
end
end fin