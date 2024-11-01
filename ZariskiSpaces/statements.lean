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
