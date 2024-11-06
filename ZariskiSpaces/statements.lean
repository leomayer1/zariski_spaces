import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import Mathlib.Topology.Separation

open TopologicalSpace

section genpt
variable {X : Type} [TopologicalSpace X] [NoetherianSpace X]

/- x is a generic point for C if the closure of {x} is C -/
def is_generic_point (x : X) (C : Closeds X) := closure {x} = C
end genpt

section zarspace
variable (X : Type) [TopologicalSpace X] [NoetherianSpace X]

#check (⊤ : Closeds X)
#check (⊥ : Closeds X)

def is_zariski_space := ∀ C : Closeds X, IsIrreducible C.carrier → (∃! x : X, is_generic_point x C)
end zarspace

variable {X : Type} [TopologicalSpace X] [NoetherianSpace X]

lemma noetherian_induction (P : Closeds X → Prop) : ∀ Y : Closeds X, (∀ Z : Closeds X, Z < Y → P Z) → P Y := by
    sorry


variable (hX : is_zariski_space X)

/- 3.17b
    show that any minimal nonempty closed subset of a Zariski space consists of one point
-/
lemma min_closed_eq_point (C : Closeds X) (hC_nonempty : ⊥ ≠ C) (hC_min : ∀ D : Closeds X, D < C → D = ⊥)
    : ∃ x : X, {x} = C.carrier := sorry


/- 3.17c
    show that a Zariski space X satisfies the axiom T₀: given any two distinct points of X,
    there is an open set containing one but not the other
-/
lemma t0_of_zariski_space (x y : X) : ∃ U : Opens X, (x ∈ U ∧ ¬ y∈ U) ∨ (¬x ∈ U ∧ y ∈ U) := sorry

/- 3.17d
    Show that If X is an irreducible Zariski space, then its generic point is contained in every nonempty open subset of X.
-/

/- define a variable for the generic point? -/

lemma generic_point_opens (U : Opens X) (hU_nonempty : ⊥ ≠ U)
    : ∃ g : U, closure {g} = X := sorry

/- 3.17e
    Let X be a Zariski space. Define a partial ordering where x_1 > x_0 if x_0 is in the closure of x_1.

    Show that the minimal points in the ordering are the closed points, and the maximal points are the generic points of the irreducible components of X.

    Show that a closed subset of X contains every specialization of any of its points.
-/

/- x specializes to y, i.e., x > y in the partial ordering for 3.17e -/
def spec (x y : X) := y ∈ closure {x}

/- hXmin: If x > y, x = y (x is minimal)-/
lemma min_spec_closed (x : X) (hXmin : ∀ y : X, spec x y → x = y)
    : {x} = closure {x} := sorry


lemma max_spec_gen (x : X) (hXmax: ∀ y : X, spec y x → x = y)
    : ∃ C : Closeds X, (IsIrreducible C.carrier) ∧ (is_generic_point x C) := by sorry

lemma closed_spec_stable (C : Closeds X)
    : ∀ c : C, (∀ x : X, spec c x → x ∈ C) by sorry

/- Defining constructible sets -/

inductive is.constructible (A : Set X) :=


/- 3.18a
    Show that a subset of X is constructible iff it can be written as a finite disjoint union of locally closed subsets -/

lemma
