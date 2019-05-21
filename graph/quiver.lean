import .basic .path 
universes u₁ u₂ 

structure quiver (V : Type u₁) (E : Type u₂) := (src : E → V) (tgt : E → V)

namespace quiver 
variables { V : Type u₁} {E : Type u₂}
def to_graph (q : quiver V E) : graph := { vertex := V, edge := λ s t, { e : E // src q e = s ∧ tgt q e = t }}
instance : has_coe (quiver V E) graph := ⟨ to_graph ⟩ 

def path (q : quiver V E) := @graph.path (to_graph q)
def edge (q : quiver V E) := @graph.edge (to_graph q)

def discrete (V) : quiver V V := ⟨id, id⟩ 
def simple {V} (p : set (V × V)) : quiver V { e : V × V // p e } := ⟨ λ e, e.val.fst , λ e, e.val.snd ⟩ 

instance simple_edge_subsingleton {p : set (V × V )} {v w : V} : subsingleton (edge (simple p) v w) 
:= subsingleton.intro (λ ⟨⟨e₁, p₁⟩, h₁⟩ ⟨⟨e₂, p₂⟩, h₂⟩, 
   begin
    apply subtype.eq,
    apply subtype.eq,
    have H₁ : e₁.fst = v ∧ e₁.snd = w, apply h₁,
    have H₂  : e₂.fst = v ∧ e₂.snd = w, apply h₂,
    have H : e₁.fst = e₂.fst ∧ e₁.snd = e₂.snd, 
       { apply and.intro,
         simp [*],
         simp [*]
       },   
    have Lem : ∀ x : V × V, x = ⟨x.fst, x.snd⟩, 
      {
          intro x,
          cases x,
          refl
      },
    simp,
    rw Lem e₁, 
    rw Lem e₂,
    rw H₁.left,
    rw H₁.right,
    rw H₂.left,
    rw H₂.right,
   end)

end quiver 

def fin_quiver {n m} := quiver (fin n) (fin m) 

