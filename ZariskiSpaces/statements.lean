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

instance : SetLike (LocCloseds X) X where
  coe := LocCloseds.carrier
  coe_injective' s t h := by cases s; cases t; congr

instance : Lattice (LocCloseds X) where
  sup A B := ⟨A.carrier ∪ B.carrier, by
    sorry⟩
  le_sup_left := fun a b => Set.subset_union_left
  le_sup_right := fun a b => Set.subset_union_right
  sup_le := fun a b c => Set.union_subset
  inf A B := ⟨A.carrier ∩ B.carrier, by
    sorry⟩
  inf_le_left := fun a b => Set.inter_subset_left
  inf_le_right := fun a b => Set.inter_subset_right
  le_inf := fun a b c => Set.subset_inter


-- #check LocCloseds
-- variable (A : LocCloseds (X := X))
-- #check Opens

class ZariskiSpace : Prop where
    /-- Irreducible closed sets have generic point -/
    irr_closed_gen : ∀ C : Closeds X, IsIrreducible C.carrier → (∃! x : X, is_generic_point x C)

end zarspace

section noetherian_induction

variable (X : Type) [TopologicalSpace X] [NoetherianSpace X]

lemma noetherian_induction (P : Closeds X → Prop) (hP : ∀ Y : Closeds X, (∀ Z < Y, P Z) → P Y) : P ⊤ := by
    exact WellFounded.induction NoetherianSpace.wellFounded_closeds ⊤ hP

end noetherian_induction

-- variable (hX : is_zariski_space X)

section threepoint17

open ZariskiSpace

variable (X : Type) [TopologicalSpace X] [ZariskiSpace X]

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

lemma eq_of_generic_point (x y : X)
    (hClosure_eq : closure {x} = closure {y}) : x = y := by
    apply ExistsUnique.unique (irr_closed_gen (Closeds.closure {x}) _)
    . apply is_generic_point_singleton
    . have h : Closeds.closure {x} = Closeds.closure {y} := by
        simp [Closeds.closure, hClosure_eq]
      rw [h]; apply is_generic_point_singleton
    simp [Closeds.closure, isIrreducible_iff_closure]
    apply isIrreducible_singleton

-- minimal -> consists of one point
lemma min_closed_eq_point (C : Closeds X) (hC_nonempty : ⊥ ≠ C.carrier) (hC_min : ∀ D : Closeds X, D < C → D = ⊥) : ∃ x : X, {x} = C.carrier := by
    rw [Set.bot_eq_empty] at hC_nonempty
    symm at hC_nonempty
    rw [← Set.nonempty_iff_ne_empty] at hC_nonempty
    have hGeneric {x : X} (hx : x ∈ C) : is_generic_point x C := by
        let D : Closeds X := ⟨closure {x}, isClosed_closure⟩
        have H : D ≤ C := (IsClosed.mem_iff_closure_subset C.2).mp hx
        rw [le_iff_lt_or_eq] at H
        cases' H with H H
        . have H : D = ⊥ := hC_min _ (by assumption)
          exfalso
          have HH : x ∈ D := subset_closure (Set.mem_singleton _)
          rw [H] at HH
          apply HH
        . rw [←H]
          rfl
    cases' hC_nonempty with x hx
    use x
    symm
    rw [Set.eq_singleton_iff_unique_mem]
    apply And.intro
    . exact hx
    . intro y hy
      apply eq_of_generic_point
      rw [hGeneric hy, hGeneric hx]

-- consists of two points -> not minimal
lemma min_closed_eq_point2 (C : Closeds X) (hC_nonempty : ⊥ ≠ C) (hC_points : ∃ x y : X, x ≠ y ∧  x ∈ C ∧ y ∈ C) : ¬(∀ D : Closeds X, D < C → D = ⊥) := by sorry

/- 3.17c
    show that a Zariski space X satisfies the axiom T₀: given any two distinct points of X,
    there is an open set containing one but not the other
-/
lemma t0_of_zariski_space (x y : X) (h_ne : x ≠ y) :
    ∃ U : Opens X, (x ∈ U ∧ ¬ y∈ U) ∨ (¬x ∈ U ∧ y ∈ U) := by
    let C : Closeds X := ⟨closure {x}, isClosed_closure⟩ --let C be closure {x}
    let D : Closeds X := ⟨closure {y}, isClosed_closure⟩ --let D be closure {y}
    have H : C ≠ D := by --first note that C ≠ D
        intro h; apply h_ne --if it was
        apply eq_of_generic_point --then x = y, which is a contradiction
        show C.carrier = D.carrier
        rw [h]
    have H₂ : x ∉ D ∨ y ∉ C := by --claim that...
        apply by_contradiction
        intro h; push_neg at h; apply H --otherwise, x ∈ D and y ∈ C
        apply le_antisymm --but then D = C, which is a contradiction
        . apply (IsClosed.mem_iff_closure_subset D.closed).mp h.1
        . apply (IsClosed.mem_iff_closure_subset C.closed).mp h.2
    cases H₂ with
    | inl H₂ =>
        use D.compl; left; constructor
        . apply H₂
        . show y ∉ (D.carrier)ᶜ
          rw [Set.mem_compl_iff, not_not]
          apply subset_closure (Set.mem_singleton _)
    | inr H₂ =>
        use C.compl; right; constructor
        . show x ∉ (C.carrier)ᶜ
          rw [Set.mem_compl_iff, not_not]
          apply subset_closure (Set.mem_singleton _)
        . apply H₂

/- 3.17d
    Show that If X is an irreducible Zariski space, then its generic point is contained in every nonempty open subset of X.
-/

/- define a variable for the generic point? -/

lemma generic_point_opens [IrreducibleSpace X]
    (U : Opens X) (hU_nonempty : ⊥ ≠ U): ∃ g : X, g ∈ U ∧ closure {g} = ⊤ := by
    cases' (irr_closed_gen ⊤ (IrreducibleSpace.isIrreducible_univ X)).exists with g hg
    use g
    constructor
    . apply by_contradiction
      intro H
      have hg₂ : g ∈ (U.compl : Closeds X) := H
      let G : Closeds X := ⟨closure {g}, isClosed_closure⟩
      have hg₃ : G ≤ U.compl := (IsClosed.mem_iff_closure_subset U.compl.2).mp hg₂
      have hU : U.compl < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro hU
        apply hU_nonempty
        apply Eq.symm
        have hUU : U.carrierᶜ = ⊤ := by
            ext
            show _ ∈ U.compl ↔ _ ∈ (⊤ : Closeds X)
            rw [hU]
        rw [compl_eq_top] at hUU
        ext
        show _ ∈ U.carrier ↔ _
        rw [hUU]
        rfl
      have hG : G ≠ ⊤ := by
        rw [←lt_top_iff_ne_top]
        apply lt_of_le_of_lt hg₃ hU
      apply hG
      have HH : G.carrier = (⊤ : Closeds X).carrier := hg
      ext
      show _ ∈ G.carrier ↔ _ ∈ (⊤ : Closeds X).carrier
      rw [HH]
    . apply hg

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

end threepoint17

section threepoint18

variable (X : Type) [TopologicalSpace X]

/- Defining constructible sets -/

inductive is_constructible : Set X → Prop :=
    | op : (IsOpen A) → is_constructible A
    | int : is_constructible B → is_constructible C → is_constructible (B ∩ C)
    | comp : (is_constructible Aᶜ) → is_constructible A

#check is_constructible.int

lemma is_constructible_loc_closed (C: Closeds X) (U: Opens X) : is_constructible (C.carrier ∩ U.carrier) := by
    apply is_constructible.int
    .   apply is_constructible.comp
        apply is_constructible.op
        simp
        exact C.closed'
    .   apply is_constructible.op
        exact U.is_open'

/- 3.18a
    Show that a subset of X is constructible iff it can be written as a finite disjoint union of locally closed subsets -/

def finite_disjoint_union (t: ι → Set β) : Prop :=
    Finite ι ∧ ∀ i j : ι, i ≠ j → (t i ∩ t j = ∅)

def P (A: Set X) : Prop :=
    ∃ ι : Type, ∃ t: ι → Set X, finite_disjoint_union t → ⋃ (i : ι), t i = A

lemma constructible_disjoint_union (A : Set X)
    : is_constructible A ↔ P A := by
    apply Iff.intro
    .   intro h
        induction h
        . sorry -- assume A is open
        . sorry -- assume B, C are constructible
        . sorry -- assume complement of A is constructible
    .   intro hA -- prove the other implication
        rcases hA with ⟨ι, t, hA⟩
        sorry

lemma iInt_int (t: ι → Set β)(s: ι' → Set β) :
    (⋃ (i : ι), t i) ∩ (⋃ (j : ι'), s j) = ⋃ (i : ι), ⋃ (j : ι'), t i ∩ s j
    := by sorry

end threepoint18

-- organize proofs into sections
-- rewrite/shorten proofs
-- spec problems
-- constructible dju
