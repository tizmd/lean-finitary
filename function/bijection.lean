universes u v
open function

class bijection {α : Sort u} {β : Sort v} (f : α → β) :=
  (inv : β → α)
  (left_inverse_of_inv : left_inverse inv f)
  (right_inverse_of_inv : right_inverse inv f)

namespace bijection
variables {α : Sort u} {β : Sort v} {f : α → β}


instance of_id : bijection (@id α) :=
  ⟨ id, take a, rfl, take a, rfl⟩ 

instance inverse (iso_f : bijection f) : bijection (inv f) :=
  ⟨f, right_inverse_of_inv f, left_inverse_of_inv f⟩ 

def injective_of_bijection (iso_f : bijection f) : injective f :=
  injective_of_left_inverse (left_inverse_of_inv f)

lemma eq_of_inv_of_bijection (iso₁ iso₂: bijection f) : iso₁.inv = iso₂.inv :=
begin
  apply funext,
  intro,
  apply injective_of_bijection,
  assumption,
  rw iso₁.right_inverse_of_inv,
  rw iso₂.right_inverse_of_inv
end

lemma bijection_of_iff {a b : Prop} (h : a ↔ b) : bijection (h.mp) :=
{
  inv := h.mpr,
  left_inverse_of_inv := take p, proof_irrel _ _,
  right_inverse_of_inv := take p, proof_irrel _ _
}

private def has_right_inverse_of_bijection (iso_f : bijection f) : has_right_inverse f := ⟨ inv f ,  right_inverse_of_inv f⟩ 

def surjective_of_bijection (iso_f : bijection f) : surjective f := 
  surjective_of_has_right_inverse (has_right_inverse_of_bijection iso_f)

def bijective_of_bijection (iso_f : bijection f) : bijective f := ⟨ injective_of_bijection iso_f , surjective_of_bijection iso_f⟩

universe w
variables {γ : Sort w} {g : β → γ}
instance comp (iso_f : bijection f) (iso_g : bijection g) : bijection (g ∘ f) := 
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
end bijection

def has_bijection {α : Sort u}{β : Sort v} (f : α → β) := ∃ g : β → α, left_inverse g f ∧ right_inverse g f

namespace has_bijection
variables {α : Sort u}{β : Sort v} {f : α → β}

def injective_of_has_bijection : has_bijection f → injective f :=
  λ ex, exists.elim ex (λ g h, injective_of_left_inverse (and.left h))
def surjective_of_has_bijection : has_bijection f → surjective f :=
  λ ex, exists.elim ex (λ g h, surjective_of_has_right_inverse (exists.intro g (and.right h)))

def bijective_of_has_bijection : has_bijection f → bijective f := λ h, and.intro (injective_of_has_bijection h) (surjective_of_has_bijection h)

def of_bijection [ins : bijection f] : has_bijection f := exists.intro ins.inv (and.intro ins.left_inverse_of_inv ins.right_inverse_of_inv)

universe w
variables {γ : Sort w} {g : β → γ}


def trans : has_bijection f → has_bijection g → has_bijection (g ∘ f) :=
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
end has_bijection

