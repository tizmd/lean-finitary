import function.bijection
import data.fin.misc
universes u v
open function


class equipotent (α : Sort u) (β : Sort v) := 
  (map : α → β)
  (has_bijection : bijection map)

namespace equipotent
variables {α : Sort u} {β : Sort v}

@[refl]
instance rfl : equipotent α α := 
  {
      map := id,
      has_bijection := bijection.of_id
  }

@[symm]
instance symm (eqv : equipotent α β) : equipotent β α := 
 {
     map := eqv.has_bijection.inv,
     has_bijection := bijection.inverse eqv.has_bijection
 }

 universe w
 variable {γ : Sort w}
 @[trans]
 instance trans (eqv₁ : equipotent α β) (eqv₂ : equipotent β γ) : equipotent α γ := 
 {
     map := eqv₂.map ∘ eqv₁.map,
     has_bijection := bijection.comp eqv₁.has_bijection eqv₂.has_bijection
 }


end equipotent


def is_equipotent (α : Sort u) (β : Sort v) := ∃ f : α → β, has_bijection f

namespace is_equipotent
variables {α : Sort u}{β : Sort v}

@[refl]
def rfl : is_equipotent α α := exists.intro id (exists.intro id (and.intro (take x, rfl) (take x, rfl)))

@[symm]
def symm : is_equipotent α β → is_equipotent β α := 
  assume Heqv,
  exists.elim Heqv (λ f ex, exists.elim ex (λ g h, exists.intro g (exists.intro f (and.intro h.right h.left))))

universe w
variable {γ : Sort w}

@[trans]
def trans : is_equipotent α β → is_equipotent β γ → is_equipotent α γ :=
  begin
  intros Hab Hbc,
  cases Hab with f f_has_bijection,
  cases Hbc with g g_has_bijection,
  apply exists.intro,
  apply has_bijection.trans,
  exact f_has_bijection,
  exact g_has_bijection
  end

def is_equipotent_iff_iff {α : Prop} {β : Prop} : (α ↔ β) ↔ is_equipotent α β :=
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
end is_equipotent

def is_finitary (α : Sort u) n := is_equipotent α (fin n)

namespace is_finitary

lemma eq_size_of_fin {m n} : is_finitary (fin m) n → m = n :=
   assume ⟨f, Hhas_bijection⟩,
   
   if Heq  : m = n then 
     Heq
   else if Hlt : m < n then
     exists.elim Hhas_bijection (take g, assume Hg, 
       have Hinj : injective g, from injective_of_left_inverse Hg.right,
       absurd Hinj (fin.not_injective_of_gt g Hlt)
       )
   else
     have Hinj : injective f, from has_bijection.injective_of_has_bijection Hhas_bijection,
     have m > n, from lt_of_le_of_ne (le_of_not_gt Hlt) (ne.symm Heq),
     absurd Hinj (fin.not_injective_of_gt f this)

theorem eq_of_size {m n}{α : Sort u} : is_finitary α m → is_finitary α n → m = n :=
  assume Hm Hn,
  have is_finitary (fin m) n, from is_equipotent.trans (is_equipotent.symm Hm) Hn,
  eq_size_of_fin this

end is_finitary