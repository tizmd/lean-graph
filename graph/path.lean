import data.list
universes u₀ u₁ 
variables {α : Type u₀}

inductive path (R : α → α → Sort u₁) : α → α → Type (max u₀ u₁)
| nil {} : Π {x}, path x x
| cons   : Π {x y z}, R x y → path y z → path x z 

namespace path 
variables {R : α → α → Sort u₁}

def singleton {x y} : R x y → path R x y := λ e, cons e nil 

def length : Π {x y}, path R x y → ℕ
| _ .(_) nil := 0
| _ _ (@cons .(_) .(_) .(_) _ .(_) e p)  := 1 + length p 

def append : Π {x y z}, path R x y → path R y z → path R x z
| _ .(_) _ nil p := p 
| _ _ _ (@cons .(_) .(_) .(_) w .(_) e p₁) p₂ := cons e (append p₁ p₂) 

lemma nil_append {x y}{p : path R x y} : append nil p = p := rfl 

@[simp]
lemma append_nil : Π {x y}{p : path R x y}, append p nil = p 
| _ ._ nil := rfl 
| _ _ (@cons ._ ._ ._ _ ._ _ p) := congr_arg (cons _) append_nil

@[simp]
lemma append_assoc : Π {w x y z}{p₁ : path R w x}{p₂ : path R x y}{p₃ : path R y z}, 
  append (append p₁ p₂) p₃ = append p₁ (append p₂ p₃) 
| _ ._ _ _ nil p₂ p₃ := rfl 
| _ _ _ _ (@cons ._ ._ ._ _ ._ e p₁) p₂ p₃ := sorry

@[simp]
lemma length_append : Π {x y z}{p₁ : path R x y}{p₂ : path R y z}, length (append p₁ p₂) = p₁.length + p₂.length 
| _ ._ _ nil _ := by simp [append, length]
| _ _ _ (@cons ._ ._ ._ _ ._ e p₁) p₂ := 
begin
simp [append, length], rw length_append,
cc
end 

def concat : Π {x y z}, path R x y → R y z → path R x z 
| _ .(_) _ nil e := singleton e
| _ _ _ (@cons .(_) .(_) .(_) w .(_) e₁ p) e₂ := cons e₁ (concat p e₂)

lemma concat_append : Π {w x y z}{p₁ : path R w x}{p₂ : path R x y}{e : R y z}, concat (append p₁ p₂) e = append p₁ (concat p₂ e) 
| _ ._ _ _ nil p₂ _ := rfl 
| _ _ _ _ (@cons ._ ._ ._ _ ._ e₁ p₁) p₂ e₂ := 
begin
simp [append, concat],
rw concat_append
end
def targets : Π {x y}, path R x y → list α
| .(_) _ nil := []
| _ _ (@cons .(_) .(_) .(_) x .(_) _ p) := x :: targets p 

def sources : Π {x y}, path R x y → list α 
| .(_) _ nil := []
| x _ (@cons .(_) .(_) .(_) _ .(_) _ p) := x :: sources p 

@[reducible,inline]
def occurrences {x y} : path R x y → list α := λ p, x :: targets p

lemma source_mem_occurrences {x y}(p : path R x y) : x ∈ occurrences p := list.mem_cons_self _ _ 
lemma target_mem_occurrences : Π{x y}(p : path R x y), y ∈ occurrences p 
| _ ._ nil := list.mem_cons_self _ _
| _ _ (@cons ._ ._ ._ _ ._ e p) := list.mem_cons_of_mem _ (target_mem_occurrences _)

lemma occurrences_eq_concat_sources : Π {x y}(p : path R x y), occurrences p = list.concat (sources p) y
| _ ._ nil := rfl 
| x y (@cons ._ ._ ._ z ._ e p) := 
begin
simp [occurrences, sources, targets],
change x :: occurrences p = x :: sources p ++ [y],
rw occurrences_eq_concat_sources,
simp 
end

@[simp]
lemma occurrences_cons {x y z}{ e : R x y}{ p : path R y z} : occurrences (cons e p) = x :: occurrences p 
:= rfl

lemma occurrences_concat : Π {x y z}{p : path R x y}{e : R y z}, occurrences (concat p e) = list.concat (occurrences p) z
| x ._ z nil e := rfl
| _ _ z (@cons ._ ._ ._ _ ._ e₁ p) e₂ := 
begin
simp[concat],
rw occurrences_concat,
simp
end

lemma length_occurrences {x y} : Π {p : path R x y}, p.occurrences.length = p.length + 1
:= 
begin intro p, induction p, simph [occurrences, targets, length],
simp[ih_1, length]
end

lemma occurrences_append_targets : Π {x y z}{p₁ : path R x y}{p₂ : path R y z}, occurrences (append p₁ p₂) = occurrences p₁ ++ targets p₂ 
| _ ._ _ nil p := rfl 
| x y z (@cons ._ ._ ._ w ._ e p₁) p₂ := 
begin
simp [occurrences, append, targets],
apply (congr_arg (list.cons _)),
apply occurrences_append_targets
end

lemma occurrences_append_sources {x y z}{p₁ : path R x y}{p₂ : path R y z} : occurrences (append p₁ p₂) = sources p₁ ++ occurrences p₂
:= 
begin
simp [occurrences],
change occurrences (append p₁ p₂) = sources p₁ ++ ([y] ++ targets p₂),
rw -list.append_assoc,
rw -list.concat_eq_append,
rw -occurrences_eq_concat_sources,
apply occurrences_append_targets
end

def rewind_path (R) : α → α → Type _ := function.swap (path (function.swap R))

def rewind : Π {x y}, path R x y → rewind_path R x y 
| _ .(_) nil := nil 
| _ _ (@cons .(_) .(_) .(_) _ .(_) e p) := concat (rewind p) e 


def occurrences_rewind : Π {x y} {p : path R x y}, p.rewind.occurrences = p.occurrences.reverse 
| _ ._ nil := rfl 
| x y (@cons ._ ._ ._ z ._ e p) := 
begin
unfold rewind,
rw occurrences_concat,
rw occurrences_rewind,
simp
end

lemma rewind_concat : Π {x y z}{p : path R x y}{e : R y z}, rewind (concat p e) = cons e (rewind p) 
| _ ._ _ nil _        := rfl 
| _ _ _ (@cons ._ ._ ._ _ ._ e₁ p) e₂ := 
begin
unfold concat,
unfold rewind,
rw rewind_concat,
refl 
end

lemma rewind_rewind : Π {x y}{p : path R x y}, p.rewind.rewind = p 
| _ ._ nil := rfl 
| _ _ (@cons ._ ._ ._ _ ._ e p) := 
begin
unfold rewind,
rw rewind_concat,
rw rewind_rewind
end 

lemma rewind_append : Π {x y z}{p₁ : path R x y}{p₂ : path R y z}, rewind (append p₁ p₂) = append p₂.rewind p₁.rewind 
| _ ._ _ nil _ := by simp [rewind,append]
| _ _ _ (@cons ._ ._ ._ _ ._ e p₁) p₂ := 
begin
unfold append,
unfold rewind,
rw rewind_append,
apply concat_append 
end

def split [deq : decidable_eq α] : Π {x y z} {p : path R x y}, 
   z ∈ occurrences p → 
     Σ' (p₁ : path R x z) (p₂ : path R z y), p = append p₁ p₂ ∧ z ∉ sources p₁ := 

  begin
  intros x y z p h,
  induction p with x x w y e p iH,
  {
    simp [occurrences, targets] at h,
    rw h,
    exact ⟨nil, nil, rfl, list.not_mem_nil _⟩ 
  },
  {
      cases (deq z x) with Hne Heq,
      {
          simp [occurrences, targets] at h,
          assert H : z ∈ occurrences p, apply or.resolve_left h Hne,
          cases (iH H) with p₁ rest,
          cases rest with p₂ Hp,
          exact ⟨cons e p₁, p₂, 
            begin rw Hp.left, refl end, list.not_mem_cons_of_ne_of_not_mem Hne Hp.right⟩  

      },
      {
        rw Heq,
        exact ⟨nil, cons e p, rfl, list.not_mem_nil _⟩ 
      }
  }
  end

def is_simple {x y}(p : path R x y) : Prop := list.nodup (occurrences p)
def simple_path (R) := λ x y : α, { p : path R x y // is_simple p}
instance {x y} : has_coe (simple_path R x y) (path R x y) := ⟨subtype.val⟩ 
lemma nil_is_simple {x : α} : is_simple (@nil _ R x) := list.nodup_singleton _ 
lemma is_simple_of_is_simple_append_left {x y z}{p₁ : path R x y}{p₂ : path R y z} : is_simple (append p₁ p₂) → is_simple p₁ 
:= 
begin
unfold is_simple,
rw occurrences_append_targets,
apply list.nodup_of_nodup_append_left
end
lemma is_simple_of_is_simple_append_right {x y z}{p₁ : path R x y}{p₂ : path R y z} : is_simple (append p₁ p₂) → is_simple p₂ 
:= 
begin
unfold is_simple,
rw occurrences_append_sources,
apply list.nodup_of_nodup_append_right
end
namespace list
lemma mem_reverse_of_mem : Π {x} {l : list α}, x ∈ l → x ∈ l.reverse 
| _ [] h := absurd h $ list.not_mem_nil _ 
| y (x :: xs) h := by simp; assumption

lemma nodup_reverse_of_nodup : Π {l : list α}, list.nodup l → list.nodup l.reverse 
| [] list.nodup.ndnil := list.nodup.ndnil 
| (x :: xs) (list.nodup.ndcons h nd) := 
begin
simp,
apply list.nodup_append_of_nodup_of_nodup_of_disjoint,
{
    apply nodup_reverse_of_nodup nd
},
{
    apply list.nodup_singleton
},
{
  intro y,
  simp,
  intros h₁ h₂,
  apply h,
  rw -h₂,
  assumption
}
end
end list

def is_simple_rewind_of_is_simple {x y} {p : path R x y} : is_simple p → is_simple p.rewind 
:= 
begin
intro H,
unfold is_simple,
rw occurrences_rewind,
apply list.nodup_reverse_of_nodup,
assumption
end

def remove_cycle [decidable_eq α] : Π {x y} (p : path R x y), Σ' (sp : simple_path R x y), occurrences sp.val <+ occurrences p
| _ ._ nil := ⟨⟨nil, nil_is_simple⟩ , list.sublist.refl _⟩ 
| x y (@cons ._ ._ ._ _ ._ e p) := 
   let ⟨⟨p', hsp'⟩, hsubp'⟩ := remove_cycle p in 
   if H : x ∈ occurrences p' then 
     match split H with 
     | ⟨p₁, p₂, h₁, h₂⟩ := ⟨⟨p₂, begin apply is_simple_of_is_simple_append_right, rw -h₁, assumption end⟩ , 
         begin simp, apply list.sublist.trans,
               { apply list.sublist_append_right (sources p₁)},
               { rw [-occurrences_append_sources, -h₁],
                 apply list.sublist.trans,
                 apply hsubp',
                 simp[occurrences, targets]
               }
         end⟩ 
     end  else ⟨⟨cons e p', list.nodup_cons H hsp'⟩, list.cons_sublist_cons _ hsubp'⟩ 
def to_simple_path [decidable_eq α] {x y} : path R x y →  simple_path R x y := λ p, (remove_cycle p).1

def is_nonempty : Π {x y}( p : path R x y ), Prop 
| _ ._ nil := false 
| _ _ _ := true 

end path
