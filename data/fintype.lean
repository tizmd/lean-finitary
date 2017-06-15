import finitary data.fin.misc
universe u

class fintype (α : Type u) := 
  (size : ℕ)
  (finitary : finitary α size)

namespace fintype
variables {α : Type u}[fintype α]

@[reducible]
def enum : α → fin (size α) := (finitary α).map
@[reducible]
def index : fin (size α) → α := (finitary α).bijection.inv

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
    rw (finitary α).bijection.left_inverse_of_inv at H,
    assumption 
  end

end fintype

def fsubtype {α : Type u}{l : list α} (prop : list.nodup l) := { a : α // a ∈ l } 

namespace fsubtype
variables {α : Type u}[decidable_eq α]{l : list α} {prop : list.nodup l} 
def index : fsubtype prop → fin l.length := 
  take ⟨a, hmem⟩, fin.left_index hmem  
def enum : fin l.length → fsubtype prop := 
  take i, ⟨fin.nth l i, fin.mem_nth _ _⟩ 

def enum_index_inverse : function.left_inverse enum (@index _ _ _ prop) := 
  take ⟨a, hmem⟩, subtype.eq $ fin.nth_left_index_left_inverse hmem 

def index_enum_inverse : function.right_inverse enum (@index _ _ _ prop) := 
  take i, fin.left_index_mem_nth_left_inverse_of_nodup prop i 

end fsubtype

instance {α : Type u}[decidable_eq α]{l : list α} {prop : list.nodup l} : fintype (fsubtype prop) := 
{
  size := l.length,
  finitary := {
    map := fsubtype.index,
    bijection := {
      inv := fsubtype.enum,
      left_inverse_of_inv := fsubtype.enum_index_inverse,
      right_inverse_of_inv := fsubtype.index_enum_inverse
    }
  }
}



