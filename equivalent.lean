import function.isomorphism
import data.fin.misc
universes u v
open function


class equivalent (α : Sort u) (β : Sort v) := 
  (map : α → β)
  (iso : isomorphism map)

namespace equivalent
variables {α : Sort u} {β : Sort v}

@[refl]
instance rfl : equivalent α α := 
  {
      map := id,
      iso := isomorphism.of_id
  }

@[symm]
instance symm (eqv : equivalent α β) : equivalent β α := 
 {
     map := eqv.iso.inv,
     iso := isomorphism.inverse eqv.iso
 }

 universe w
 variable {γ : Sort w}
 @[trans]
 instance trans (eqv₁ : equivalent α β) (eqv₂ : equivalent β γ) : equivalent α γ := 
 {
     map := eqv₂.map ∘ eqv₁.map,
     iso := isomorphism.comp eqv₁.iso eqv₂.iso
 }
end equivalent

def equivalent_map (α : Sort u) (β : Sort v) := { f : α → β // has_isomorphism f }
def is_equivalent (α : Sort u) (β : Sort v) := ∃ f : α → β, has_isomorphism f

namespace is_equivalent
variables {α : Sort u}{β : Sort v}

@[refl]
def rfl : is_equivalent α α := exists.intro id (exists.intro id (and.intro (take x, rfl) (take x, rfl)))

@[symm]
def symm : is_equivalent α β → is_equivalent β α := 
  assume Heqv,
  exists.elim Heqv (λ f ex, exists.elim ex (λ g h, exists.intro g (exists.intro f (and.intro h.right h.left))))

universe w
variable {γ : Sort w}

@[trans]
def trans : is_equivalent α β → is_equivalent β γ → is_equivalent α γ :=
  begin
  intros Hab Hbc,
  cases Hab with f f_iso,
  cases Hbc with g g_iso,
  apply exists.intro,
  apply has_isomorphism.trans,
  exact f_iso,
  exact g_iso
  end

def is_equivalent_iff_iff {α : Prop} {β : Prop} : (α ↔ β) ↔ is_equivalent α β :=
  begin
    apply iff.intro,
      {
          intro H,
          apply (exists.intro (iff.elim_left H)),
          apply (exists.intro (iff.elim_right H)), 
          apply and.intro,
          intro p, apply proof_irrel,
          intro p, apply proof_irrel
      },
      {
          intro H,
          cases H with p ex,
          cases ex with q h,
          apply iff.intro,
          assumption, assumption
      }
  end
end is_equivalent

def is_finitary (α : Sort u) n := is_equivalent α (fin n)

namespace is_finitary

lemma eq_size_of_fin {m n} : is_finitary (fin m) n → m = n :=
   assume ⟨f, Hiso⟩,
   
   if Heq  : m = n then 
     Heq
   else if Hlt : m < n then
     exists.elim Hiso (take g, assume Hg, 
       have Hinj : injective g, from injective_of_left_inverse Hg.right,
       absurd Hinj (fin.not_injective_of_gt g Hlt)
       )
   else
     have Hinj : injective f, from has_isomorphism.injective_of_has_isomorphism Hiso,
     have m > n, from lt_of_le_of_ne (le_of_not_gt Hlt) (ne.symm Heq),
     absurd Hinj (fin.not_injective_of_gt f this)

theorem eq_of_size {m n}{α : Sort u} : is_finitary α m → is_finitary α n → m = n :=
  assume Hm Hn,
  have is_finitary (fin m) n, from is_equivalent.trans (is_equivalent.symm Hm) Hn,
  eq_size_of_fin this

end is_finitary