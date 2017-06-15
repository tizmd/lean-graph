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

structure rooted_graph extends graph := 
  (root : vertex)
  (root_reachable : Π (v : vertex), graph.path root v)
  (root_init  : graph.incoming root → false)

 
namespace rooted_graph 
variable {g : rooted_graph}
#check (λ w : g.vertex, root_reachable g w) 
def dom v (w : g.vertex) : Prop := ∀ (p : g.root_reachable w), v ∈ p.occurrences


end rooted_graph