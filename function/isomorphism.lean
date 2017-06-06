universes u v
open function

class isomorphism {α : Sort u} {β : Sort v} (f : α → β) :=
  (inv : β → α)
  (left_inverse_of_inv : left_inverse inv f)
  (right_inverse_of_inv : right_inverse inv f)

namespace isomorphism
variables {α : Sort u} {β : Sort v} {f : α → β}


instance of_id : isomorphism (@id α) :=
  ⟨ id, take a, rfl, take a, rfl⟩ 

instance inverse (iso_f : isomorphism f) : isomorphism (inv f) :=
  ⟨f, right_inverse_of_inv f, left_inverse_of_inv f⟩ 

def injective_of_isomorphism (iso_f : isomorphism f) : injective f :=
  injective_of_left_inverse (left_inverse_of_inv f)

lemma eq_of_inv_of_isomorphism (iso₁ iso₂: isomorphism f) : iso₁.inv = iso₂.inv :=
begin
  apply funext,
  intro,
  apply injective_of_isomorphism,
  assumption,
  rw iso₁.right_inverse_of_inv,
  rw iso₂.right_inverse_of_inv
end

private def has_right_inverse_of_isomorphism (iso_f : isomorphism f) : has_right_inverse f := ⟨ inv f ,  right_inverse_of_inv f⟩ 

def surjective_of_isomorphism (iso_f : isomorphism f) : surjective f := 
  surjective_of_has_right_inverse (has_right_inverse_of_isomorphism iso_f)

def bijective_of_isomorphism (iso_f : isomorphism f) : bijective f := ⟨ injective_of_isomorphism iso_f , surjective_of_isomorphism iso_f⟩

universe w
variables {γ : Sort w} {g : β → γ}
instance comp (iso_f : isomorphism f) (iso_g : isomorphism g) : isomorphism (g ∘ f) := 
 ⟨ inv f ∘ inv g, 
   begin
     intro a,
     simp [comp],
     repeat {rw [left_inverse_of_inv]}
   end, 
   begin
     intro c,
     simp [comp],
     rw [right_inverse_of_inv f, right_inverse_of_inv g]
   end⟩ 
end isomorphism

def has_isomorphism {α : Sort u}{β : Sort v} (f : α → β) := ∃ g : β → α, left_inverse g f ∧ right_inverse g f

namespace has_isomorphism
variables {α : Sort u}{β : Sort v} {f : α → β}

def injective_of_has_isomorphism : has_isomorphism f → injective f :=
  λ ex, exists.elim ex (λ g h, injective_of_left_inverse (and.left h))
def surjective_of_has_isomorphism : has_isomorphism f → surjective f :=
  λ ex, exists.elim ex (λ g h, surjective_of_has_right_inverse (exists.intro g (and.right h)))

def bijective_of_has_isomorphism : has_isomorphism f → bijective f := λ h, and.intro (injective_of_has_isomorphism h) (surjective_of_has_isomorphism h)

def of_isomorphism [ins : isomorphism f] : has_isomorphism f := exists.intro ins.inv (and.intro ins.left_inverse_of_inv ins.right_inverse_of_inv)

universe w
variables {γ : Sort w} {g : β → γ}


def trans : has_isomorphism f → has_isomorphism g → has_isomorphism (g ∘ f) :=
begin
intros fH gH,
cases fH with f_inv f_inv_h,
cases gH with g_inv g_inv_h,
apply (exists.intro (f_inv ∘ g_inv)),
apply and.intro,
{
    intro x,
    simp [comp],
    rw [g_inv_h.left, f_inv_h.left]
},
{
    intro x,
    simp [comp],
    rw [f_inv_h.right, g_inv_h.right]
}
end
end has_isomorphism

