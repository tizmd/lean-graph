import .path 
universes u₁ u₂ 

structure graph := (vertex : Type u₁) (edge : vertex → vertex → Sort u₂)

namespace graph 
variables {g : graph}

def incoming (v) := Σ' w, g.edge w v  
def outgoing (v) := Σ' w, g.edge v w

def path : g.vertex → g.vertex → Type _ := path g.edge
def rpath : g.vertex → g.vertex → Type _ := path.rewind_path g.edge

end graph 

def fin_graph {n} : (fin n → fin n → ℕ) → graph := λ spec, ⟨fin n, λ i j, fin (spec i j)⟩ 


 
