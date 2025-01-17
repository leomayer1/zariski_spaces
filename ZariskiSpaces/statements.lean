import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import Mathlib.Topology.Separation
import Mathlib.Tactic.Contrapose

open TopologicalSpace

section genpt
variable {X : Type} [TopologicalSpace X]

/- x is a generic point for C if the closure of {x} is C -/
def is_generic_point (x : X) (C : Closeds X) := closure {x} = C

lemma is_generic_point_singleton (x : X) : is_generic_point x (Closeds.closure {x}) := rfl

end genpt

section zarspace
variable (X : Type) [TopologicalSpace X] [NoetherianSpace X]

#check (⊤ : Closeds X)
#check (⊥ : Closeds X)

structure LocCloseds where
carrier : Set X
isLocClosed : IsLocallyClosed carrier

#check LocCloseds
variable (A : LocCloseds (X := X))
#check Opens

def is_zariski_space := ∀ C : Closeds X, IsIrreducible C.carrier → (∃! x : X, is_generic_point x C)
end zarspace

variable {X : Type} [TopologicalSpace X] [NoetherianSpace X]

lemma noetherian_induction (P : Closeds X → Prop) (hP : ∀ Y : Closeds X, (∀ Z < Y, P Z) → P Y) : P ⊤ := by
    exact WellFounded.induction NoetherianSpace.wellFounded_closeds ⊤ hP

variable (hX : is_zariski_space X)

/- 3.17b
    show that any minimal nonempty closed subset of a Zariski space consists of one point
-/

def is_irreducible (s: Set X) : Prop :=
    s ≠ ⊥ ∧ (∀ u v : Closeds s, (u.carrier ∩ v.carrier ≠ ⊥) → (s ∩ (u.carrier ∩ v.carrier) ≠ ⊥))

lemma irreducible_of_min (C : Closeds X) (hC_nonempty : ⊥ ≠ C.carrier) (hC_min : ∀ D : Closeds X, D < C → D = ⊥) : IsIrreducible C.carrier := by
    apply And.intro
    . rw [Set.bot_eq_empty] at hC_nonempty
      symm at hC_nonempty
      rw [← Set.nonempty_iff_ne_empty] at hC_nonempty
      exact hC_nonempty
    . rw [isPreirreducible_iff_closed_union_closed]
      intro z₁ z₂ hz₁ hz₂ hC
      by_cases h : C.carrier ⊆ z₁
      . left; assumption
      . right
        let Z₁ : Closeds X := ⟨z₁, hz₁⟩
        let Z₂ : Closeds X := ⟨z₂, hz₂⟩
        have hZ₁ : Z₁ ⊓ C = ⊥ := by
            apply hC_min
            rw [lt_iff_le_and_ne]
            constructor
            simp
            intro H; apply h
            symm at H
            have HH := le_trans (le_of_eq H) (inf_le_left)
            apply HH
        have H : C ≤ Z₁ ⊔ Z₂ := hC
        have HH := inf_le_inf_right C H
        rw [inf_idem, inf_sup_right, hZ₁, bot_sup_eq] at HH
        simp at HH
        apply HH

lemma eq_of_generic_point (hX : is_zariski_space X) (x y : X)
    (hClosure_eq : closure {x} = closure {y}) : x = y := by
    apply ExistsUnique.unique (hX (Closeds.closure {x}) _)
    . apply is_generic_point_singleton
    . have h : Closeds.closure {x} = Closeds.closure {y} := by
        simp [Closeds.closure, hClosure_eq]
      rw [h]; apply is_generic_point_singleton
    simp [Closeds.closure, isIrreducible_iff_closure]
    apply isIrreducible_singleton

lemma min_closed_eq_point (hX : is_zariski_space X) (C : Closeds X) (hC_nonempty : ⊥ ≠ C.carrier) (hC_min : ∀ D : Closeds X, D < C → D = ⊥) : ∃ x : X, {x} = C.carrier := by
    have hIrreducible : IsIrreducible C := irreducible_of_min C hC_nonempty hC_min
    rw [Set.bot_eq_empty] at hC_nonempty
    symm at hC_nonempty
    rw [← Set.nonempty_iff_ne_empty] at hC_nonempty
    cases' hC_nonempty with x hx
    use x
    -- have hPoint : ⊥ ≠ C → ∃ x : X, x ∈ C := sorry
    have hGeneric : is_generic_point x C := sorry
        --use minimality, since closure {x} nonempty
    symm
    rw [Set.eq_singleton_iff_unique_mem]
    apply And.intro
    . exact hx
    . intro y hy
      have hGenericY : is_generic_point y C := sorry
      have genPtUnique: y=x := sorry -- apply is_zariski_space definition somehow?
      exact genPtUnique

lemma min_closed_eq_point2 (C : Closeds X) (hC_nonempty : ⊥ ≠ C) (hC_points : ∃ x y : X, x ≠ y ∧  x ∈ C ∧ y ∈ C) : ¬(∀ D : Closeds X, D < C → D = ⊥) := by sorry

/- 3.17c
    show that a Zariski space X satisfies the axiom T₀: given any two distinct points of X,
    there is an open set containing one but not the other
-/
lemma t0_of_zariski_space (x y : X) : ∃ U : Opens X, (x ∈ U ∧ ¬ y∈ U) ∨ (¬x ∈ U ∧ y ∈ U) := sorry

/- 3.17d
    Show that If X is an irreducible Zariski space, then its generic point is contained in every nonempty open subset of X.
-/

/- define a variable for the generic point? -/

lemma generic_point_opens [IrreducibleSpace X] (U : Opens X) (hU_nonempty : ⊥ ≠ U)
    : ∃ g : U, closure {g} = X := sorry

/- 3.17e
    Let X be a Zariski space. Define a partial ordering where x_1 > x_0 if x_0 is in the closure of x_1.

    Show that the minimal points in the ordering are the closed points, and the maximal points are the generic points of the irreducible components of X.

    Show that a closed subset of X contains every specialization of any of its points.

    Show that an open subset of X contains every generalization of any of its points.
-/

/- x specializes to y, i.e., x > y in the partial ordering for 3.17e -/
def spec (x y : X) := y ∈ closure {x}

/- hXmin: If x > y, x = y (x is minimal)-/
lemma min_spec_closed (x : X) (hXmin : ∀ y : X, spec x y → x = y)
    : {x} = closure {x} := by

    sorry


lemma max_spec_gen (x : X) (hXmax: ∀ y : X, spec y x → x = y)
    : ∃ C : Closeds X, (IsIrreducible C.carrier) ∧ (is_generic_point x C) := by sorry

lemma closed_spec_stable (C : Closeds X)
    : ∀ c x : X, (c ∈ C → spec c x) → x ∈ C := by sorry
    -- : ∀ c : C, (∀ x : X, spec c.1 x → x ∈ C) := by sorry

lemma open_gen_stable (O : Opens X)
    : ∀ o x : X, (o ∈ C → spec x o) → x ∈ C := by sorry

/- Defining constructible sets -/

inductive is_constructible : Set X → Prop :=
    | op : (IsOpen A) → is_constructible A
    -- | int (B C : Set X) : (A = B ∩ C) → (is_constructible B ∧ is_constructible C) → is_constructible A
    | int : is_constructible B → is_constructible C → is_constructible (B ∩ C)
    | comp : (is_constructible Aᶜ) → is_constructible A

#check is_constructible.int

lemma is_constructible_loc_closed (C U : Set X) (hC : IsClosed C) (hU : IsOpen U) : is_constructible (C ∩ U) := by
    apply is_constructible.int
    .   apply is_constructible.comp
        apply is_constructible.op
        simp
        -- rw [← isClosed_compl_iff]
        -- rw [compl_compl]
        exact hC
    .   apply is_constructible.op
        exact hU

/- 3.18a
    Show that a subset of X is constructible iff it can be written as a finite disjoint union of locally closed subsets -/


variable (P : Set X → Prop)

lemma constructible_disjoint_union (A : Set X)
    : is_constructible A → P A := by
    intro h
    induction h
    . sorry
    . sorry
    . sorry
