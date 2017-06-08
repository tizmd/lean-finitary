import equivalent data.fin.misc
import data.list.distinct
universe u

class fintype (α : Type u) := 
  (size : ℕ)
  (finitary : equivalent α (fin size))

namespace fintype
variables {α : Type u}[fintype α]
@[reducible]
def enum : α → fin (size α) := (finitary α).map
@[reducible]
def index : fin (size α) → α := (finitary α).iso.inv


def elems : list α := list.map (@index α _) (fin.elems (size α))
theorem mem_elems : ∀ a : α, a ∈ (elems : list α) :=
  begin
    intro a,
    assert H : index (enum a) ∈ (elems : list α),  
      {
          simp [elems],
          apply list.mem_map,
          apply fin.mem_elems
      },
    simp [enum,index] at H,
    rw (finitary α).iso.left_inverse_of_inv at H,
    assumption 
  end

end fintype
