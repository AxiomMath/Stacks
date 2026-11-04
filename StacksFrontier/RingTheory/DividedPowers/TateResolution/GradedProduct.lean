module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.FiniteStage
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableLift

/-! # The graph argument for the product of two graded divided power algebras

The product of two nonnegatively graded algebras is graded by the products of their homogeneous
pieces, and the product of two divided power structures on the positive even parts is a divided
power structure on the positive even part of the product; that construction lives in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction`. This
file carries the conclusion drawn from it, the graph argument: to check that a ring homomorphism
out of a set-variable divided power extension respects divided powers, it suffices to check it on
the coefficients and on the adjoined variables, because the graph of the homomorphism is a
subring of the product and the finite variable stages are stable under the product's divided
powers.

## Main results

* `DividedPowers.TateResolution.ringHom_dpow_of_finiteVariableStage` — compatibility with divided
  powers propagates from the coefficients and the variables to a whole finite variable stage, for
  a ring homomorphism commuting with the structure maps and variables of one common degree.
* `DividedPowers.TateResolution.map_dpow_of_finiteVariableStage` — the same propagation for an
  algebra homomorphism, with the adjoined variables allowed to have distinct degrees.

## Implementation notes

The graph argument is stated twice, because neither form subsumes the other.
`ringHom_dpow_of_finiteVariableStage` takes a *ring* homomorphism together with the hypothesis
that it commutes with the structure maps, rather than an algebra homomorphism, because the maps
it is applied to are built by the one-variable mapping properties of
`StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableLift`, which produce ring
homomorphisms; it asks that the adjoined variables share one degree.
`map_dpow_of_finiteVariableStage` takes an algebra homomorphism but lets each variable have its
own degree.

The graph argument was first developed in
`StacksFrontier/RingTheory/DividedPowers/TateResolution/SetVariableExtension/Construction.lean` for
the algebra homomorphisms of that file's own universal property and left `private` there. The
declarations here are the same mathematics stated publicly, with the graph argument generalized
from algebra to ring homomorphisms.

## References

* [Stacks Project, Tag 09PG](https://stacks.math.columbia.edu/tag/09PG)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

universe u v w z t

section ProdDpow

attribute [local instance] prodGradedAlgebra prodStrictlyGradedComm

/-- The graph argument for an algebra homomorphism, with a degree for each adjoined variable. -/
private theorem map_dpow_of_finiteVariableStage_aux
    {R : Type u} {A : Type v} {C : Type z} {D : Type t} {J : Type w}
    [CommRing R] [Ring A] [Ring C] [Ring D]
    [Algebra R A] [Algebra R C] [Algebra R D]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (δ : DividedPowerStructure Cᵢ) (ε : DividedPowerStructure Dᵢ)
    (ι : A →ₐ[R] C) (T : J → C) (S : Finset J) (deg : J → ℕ)
    (hgrade : ∀ m a, a ∈ Aᵢ m → ι a ∈ Cᵢ m)
    (hT : ∀ j, T j ∈ Cᵢ (deg j))
    (hclosed : ∀ n a, ι a ∈ positiveEvenPart Cᵢ → δ.dpow n (ι a) ∈ Set.range ι)
    (f : C →ₐ[R] D) (hf : ∀ m x, x ∈ Cᵢ m → f x ∈ Dᵢ m)
    (hcoeff : ∀ n a, ι a ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f (ι a)) = f (δ.dpow n (ι a)))
    (hgen : ∀ n j, T j ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f (T j)) = f (δ.dpow n (T j)))
    {x : C} (hx : x ∈ finiteVariableStage δ ι T S)
    (hp : x ∈ positiveEvenPart Cᵢ) (n : ℕ) :
    ε.dpow n (f x) = f (δ.dpow n x) := by
  classical
  let P := fun m => (Cᵢ m).prod (Dᵢ m)
  let η := prodDividedPowerStructure Cᵢ Dᵢ δ ε
  let k : C →ₐ[R] C × D := (AlgHom.id R C).prod f
  have hk (m : ℕ) (x : C) (hx : x ∈ Cᵢ m) : k x ∈ P m := ⟨hx, hf m x hx⟩
  have hkpos {x : C} (hx : x ∈ positiveEvenPart Cᵢ) : k x ∈ positiveEvenPart P :=
    algHom_mem_positiveEvenPart Cᵢ P k hk hx
  have hfst {p : C × D} (hp : p ∈ positiveEvenPart P) :
      p.1 ∈ positiveEvenPart Cᵢ := by
    rw [show positiveEvenPart P = (positiveEvenPart Cᵢ).prod (positiveEvenPart Dᵢ) from
      prodGrade_iSup Cᵢ Dᵢ (fun n => 2 * (n + 1))] at hp
    exact hp.1
  have hdp {x : C} (he : ∀ n, x ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f x) = f (δ.dpow n x)) (n : ℕ) : η.dpow n (k x) = k (δ.dpow n x) := by
    by_cases hp : x ∈ positiveEvenPart Cᵢ
    · rw [prodDividedPowerStructure_dpow Cᵢ Dᵢ δ ε n (hkpos hp)]
      exact Prod.ext rfl (he n hp)
    · rw [η.dpow_null (fun h => hp (hfst h)), δ.dpow_null hp, map_zero]
  have hdpgen (n : ℕ) (j : J) : η.dpow n (k (T j)) = k (δ.dpow n (T j)) :=
    hdp (hgen · j) n
  let Q := finiteVariableStage η (k.comp ι) (fun j => k (T j)) S
  have hxQ : k x ∈ Q := by
    clear hp
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨j, hj, rfl | ⟨m, rfl⟩⟩
      · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨j, hj, Or.inl rfl⟩)
      · rw [← hdpgen]
        exact Subring.subset_closure (Or.inr ⟨j, hj, Or.inr ⟨m, rfl⟩⟩)
    | zero => simp
    | one => simp
    | add a b ha hb ha' hb' => simpa only [map_add] using Q.add_mem ha' hb'
    | neg a ha ha' => simpa only [map_neg] using Q.neg_mem ha'
    | mul a b ha hb ha' hb' => simpa only [map_mul] using Q.mul_mem ha' hb'
  have hdQ : η.dpow n (k x) ∈ Q := finiteVariableStage_dpow_mem Aᵢ P η
    (k.comp ι) (fun j => k (T j)) S deg
    (fun m a ha => hk m _ (hgrade m a ha)) (fun j => hk (deg j) _ (hT j))
    (by
      intro m a ha
      obtain ⟨b, hb⟩ := hclosed m a (hfst ha)
      refine ⟨b, ?_⟩
      show k (ι b) = η.dpow m (k (ι a))
      rw [hdp (hcoeff · a), hb]) n (k x) hxQ (hkpos hp)
  let G : Subring (C × D) :=
    { carrier := {p | f p.1 = p.2}
      zero_mem' := map_zero f
      one_mem' := map_one f
      add_mem' := fun ha hb => (map_add f _ _).trans (congrArg₂ (· + ·) ha hb)
      neg_mem' := fun ha => (map_neg f _).trans (congrArg Neg.neg ha)
      mul_mem' := fun ha hb => (map_mul f _ _).trans (congrArg₂ (· * ·) ha hb) }
  have hQG : Q ≤ G := by
    apply Subring.closure_le.mpr
    rintro p (⟨a, rfl⟩ | ⟨j, hj, rfl | ⟨m, rfl⟩⟩)
    · rfl
    · rfl
    · rw [hdpgen]; rfl
  have heq := hQG hdQ
  rw [prodDividedPowerStructure_dpow Cᵢ Dᵢ δ ε n (hkpos hp)] at heq
  exact heq.symm

/-- Compatibility with divided powers propagates from the coefficients and the adjoined variables
to a whole finite variable stage. The argument is that the graph of the homomorphism is a subring
of the product containing the images of the generators, and that finite variable stages of the
product are stable under its divided powers.

This supersedes the `private` `map_dpow_of_finiteVariableStage` of
`StacksFrontier/RingTheory/DividedPowers/TateResolution/SetVariableExtension/Construction.lean`,
generalized from an algebra homomorphism to a ring homomorphism commuting with the structure
maps. -/
@[stacks 0F4I "divided powers on a finite stage"]
public theorem ringHom_dpow_of_finiteVariableStage
    {R : Type u} {P : Type v} {C : Type z} {D : Type*} {J : Type w}
    [CommRing R] [Ring P] [Ring C] [Ring D]
    [Algebra R P] [Algebra R C] [Algebra R D]
    (Pᵢ : ℕ → Submodule R P) [GradedAlgebra Pᵢ]
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (δ : DividedPowerStructure Cᵢ) (ε : DividedPowerStructure Dᵢ)
    (ι : P →ₐ[R] C) (T : J → C) (S : Finset J) (d : ℕ)
    (hgrade : ∀ (m : ℕ) (a : P), a ∈ Pᵢ m → ι a ∈ Cᵢ m)
    (hT : ∀ j : J, T j ∈ Cᵢ d)
    (hclosed : ∀ (n : ℕ) (a : P), ι a ∈ positiveEvenPart Cᵢ →
      δ.dpow n (ι a) ∈ Set.range ι)
    (f : C →+* D) (hf : ∀ (m : ℕ) (x : C), x ∈ Cᵢ m → f x ∈ Dᵢ m)
    (hfalg : ∀ r : R, f (algebraMap R C r) = algebraMap R D r)
    (hcoeff : ∀ (n : ℕ) (a : P), ι a ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f (ι a)) = f (δ.dpow n (ι a)))
    (hgen : ∀ (n : ℕ) (j : J), T j ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f (T j)) = f (δ.dpow n (T j)))
    {x : C} (hx : x ∈ finiteVariableStage δ ι T S)
    (hp : x ∈ positiveEvenPart Cᵢ) (n : ℕ) :
    ε.dpow n (f x) = f (δ.dpow n x) := by
  exact map_dpow_of_finiteVariableStage_aux Pᵢ Cᵢ Dᵢ δ ε ι T S (fun _ => d) hgrade hT
    hclosed { f with commutes' := hfalg } hf hcoeff hgen hx hp n

/-- A graded algebra homomorphism out of a divided-power algebra is compatible with divided
powers on a whole finite-variable stage as soon as it is compatible on the coefficient algebra
and on each adjoined variable. The argument passes to the graph of the homomorphism inside the
product divided-power algebra, where closure of the finite stages under divided powers does the
work.

This is the variant of `ringHom_dpow_of_finiteVariableStage` in which the adjoined variables are
allowed to have distinct degrees `deg j`, at the cost of asking for an algebra homomorphism
rather than a ring homomorphism commuting with the structure maps. -/
public theorem map_dpow_of_finiteVariableStage
    {R : Type u} {A : Type v} {C : Type z} {D : Type t} {J : Type w}
    [CommRing R] [Ring A] [Ring C] [Ring D]
    [Algebra R A] [Algebra R C] [Algebra R D]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (δ : DividedPowerStructure Cᵢ) (ε : DividedPowerStructure Dᵢ)
    (ι : A →ₐ[R] C) (T : J → C) (S : Finset J) (deg : J → ℕ)
    (hgrade : ∀ m a, a ∈ Aᵢ m → ι a ∈ Cᵢ m)
    (hT : ∀ j, T j ∈ Cᵢ (deg j))
    (hclosed : ∀ n a, ι a ∈ positiveEvenPart Cᵢ → δ.dpow n (ι a) ∈ Set.range ι)
    (f : C →ₐ[R] D) (hf : ∀ m x, x ∈ Cᵢ m → f x ∈ Dᵢ m)
    (hcoeff : ∀ n a, ι a ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f (ι a)) = f (δ.dpow n (ι a)))
    (hgen : ∀ n j, T j ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f (T j)) = f (δ.dpow n (T j)))
    {x : C} (hx : x ∈ finiteVariableStage δ ι T S)
    (hp : x ∈ positiveEvenPart Cᵢ) (n : ℕ) :
    ε.dpow n (f x) = f (δ.dpow n x) := by
  exact map_dpow_of_finiteVariableStage_aux Aᵢ Cᵢ Dᵢ δ ε ι T S deg hgrade hT hclosed f hf
    hcoeff hgen hx hp n

end ProdDpow

end DividedPowers.TateResolution

end
