module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatBaseChangeRefined
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow
public import StacksFrontier.RingTheory.Rig.FlatBaseChange
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Commutativity
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientLimit
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalPropertyRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined
import all StacksFrontier.RingTheory.Rig.FlatBaseChange

/-!
# Flatness is stable under completed base change (Stacks 0GCA): the refined forms

The strengthened and newly added declarations of the 2026-10 chapter-87 round that belong with
`StacksFrontier.RingTheory.Rig.FlatBaseChange`. A declaration of that module whose statement the
round strengthened keeps its original statement there; its strengthened form lives here under a
primed name.
-/

@[expose] public section

namespace TopologicalRing

open Filter
open scoped Topology TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Noetherianity of a completed tensor product, symmetrically -/

/-! ### Transporting locality from the weakly admissible to the Noetherian adic setting -/

/-- A local property of morphisms of countably indexed weakly admissible rings is in particular
a local property in the Noetherian adic sense of Remark 0ANI. -/
private theorem propertyIsLocalNoetherian_of_propertyIsLocal'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop)
    (hP : PropertyIsLocal' P) : PropertyIsLocalNoetherian' P := by
  change PropertyIsLocal' P (fun R ↦ IsAdic R ∧ IsNoetherianRing R)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eB eA heB heBs heA heAs f hf hB hA hB' hA'
    exact hP.isomorphismInvariant eB eA heB heBs heA heAs f hf
      (isCountablyWeaklyAdmissible_of_isAdic hB.1)
      (isCountablyWeaklyAdmissible_of_isAdic hA.1)
      (isCountablyWeaklyAdmissible_of_isAdic hB'.1)
      (isCountablyWeaklyAdmissible_of_isAdic hA'.1)
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D _ _ hA' hB' hProp
    exact hP.localizationPreserves D
      ⟨D.weaklyAdmissibleA, D.countableA⟩ ⟨D.weaklyAdmissibleB, D.countableB⟩
      (isCountablyWeaklyAdmissible_of_isAdic hA'.1)
      (isCountablyWeaklyAdmissible_of_isAdic hB'.1) hProp
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D _ _ hA' hB' hFF hProp
    exact hP.faithfullyFlatDescent D
      ⟨D.weaklyAdmissibleA, D.countableA⟩ ⟨D.weaklyAdmissibleB, D.countableB⟩
      (isCountablyWeaklyAdmissible_of_isAdic hA'.1)
      (isCountablyWeaklyAdmissible_of_isAdic hB'.1) hFF hProp
  · intro B _ _ _ _ hB hBcount ι _ A _ _ _ _ hAweak hAcount f hf _ _ hfProp
    exact hP.finiteProduct hB hBcount A hAweak hAcount f hf
      ⟨hB, hBcount⟩ (fun i ↦ ⟨hAweak i, hAcount i⟩) hfProp

/-! ### Adic completions of a base change, as a tower -/

section

open CategoryTheory CategoryTheory.Limits

/-! ### The tower of stagewise completions -/

section TensorLimits

variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C] [Algebra B A] [Algebra B C]

end TensorLimits

section TensorTower

variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C] [Algebra B A] [Algebra B C]

attribute [local instance] tensorQuotientAlgebra

attribute [local instance] tensorQuotient_scalarTower

end TensorTower

end

/-! ### Flatness of a completed base change from Noetherian stages -/

/-! ### Part (1): base change by a morphism of finite type on reductions -/

/-- A Noetherian pre-adic topological ring has a finitely generated ideal of definition. -/
private theorem exists_isIdealOfDefinition_fg {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsNoetherianRing R] (hR : IsPreAdic R) :
    ∃ I : Ideal R, IsIdealOfDefinition I ∧ I.FG :=
  have ⟨I, hI, _⟩ := hR
  ⟨I, hI, Ideal.fg_of_isNoetherianRing I⟩

/-- **Stacks 0GCA, part (1).** Flatness of morphisms of Noetherian adic topological rings
(Stacks 0GC9) is stable under completed tensor-product base change along morphisms of finite
type on reductions (Stacks 0GC2), in the sense of Remark 0GBG. -/
@[stacks 0GCA "part (1)"]
public theorem flat_isStableUnderBaseChangeByFiniteTypeOnReductions' :
    IsStableUnderBaseChangeBy'
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦ φ.Flat)
      FiniteTypeOnReductionsProperty := by
  refine ⟨flat_isLocalNoetherian',
    propertyIsLocalNoetherian_of_propertyIsLocal' _ isFiniteTypeOnReductions_propertyIsLocal', ?_⟩
  intro B A C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hC hBA hBC hP hQ
  rcases hQ with ⟨_, hredQ⟩
  have hredC : Rig.IsFiniteTypeOnReductions (algebraMap B C) hBC := hredQ
  have hCweak := isCountablyWeaklyAdmissible_of_isAdic hC
  have hBCtft : IsTopologicallyOfFiniteType (algebraMap B C) :=
    Rig.isTopologicallyOfFiniteType_of_isFiniteTypeOnReductions
      (algebraMap B C) hBC hCweak.1 hredC
  have hstage (J : Ideal C) (_ : IsIdealOfDefinition J) (hJ : _root_.IsAdic J) (n : ℕ) :
      IsNoetherianRing (A ⊗[B] (C ⧸ J ^ n)) := by
    have : Algebra.FiniteType B (C ⧸ J ^ n) :=
      finiteType_quotient_of_isTopologicallyOfFiniteType hBCtft (J ^ n)
        ((isAdic_iff.mp hJ).1 n)
    let : Algebra.FiniteType A (A ⊗[B] (C ⧸ J ^ n)) := inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  exact ⟨completedTensorProduct_isAdic hBA hBC hA.1 (exists_isIdealOfDefinition_fg hA.1) hC.1
      (exists_isIdealOfDefinition_fg hC.1),
    completedTensorProduct_isNoetherianRing_of_isFiniteTypeOnReductions hA.1 hC.1 hBA hBC
      (Or.inr hredC),
    flat_completedTensorProduct_of_isNoetherianRing_stages hA hC hP hstage⟩

/-! ### Part (2): arbitrary base change of a flat adic morphism of topologically finite type -/

/-- Two local properties of morphisms have a local conjunction: presentation independence and
each of the three axioms of Situation 0CBA holds for `P ∧ Q` because it holds for `P` and for
`Q` separately. -/
public theorem PropertyIsLocal'.and
    {P Q : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
    {K : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop}
    (hP : PropertyIsLocal' P K) (hQ : PropertyIsLocal' Q K) :
    PropertyIsLocal' (fun φ ↦ P φ ∧ Q φ) K := by
  refine ⟨IsomorphismInvariant.and hP.isomorphismInvariant hQ.isomorphismInvariant, ?_, ?_, ?_⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' h
    exact ⟨hP.localizationPreserves D hA hB hA' hB' h.1,
      hQ.localizationPreserves D hA hB hA' hB' h.2⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hff h
    exact ⟨hP.faithfullyFlatDescent D hA hB hA' hB' hff h.1,
      hQ.faithfullyFlatDescent D hA hB hA' hB' hff h.2⟩
  · intro B _ _ _ _ hB hBcount ι _ A _ _ _ _ hAw hAcount f hf hKB hKA h
    exact ⟨hP.finiteProduct hB hBcount A hAw hAcount f hf hKB hKA (fun i ↦ (h i).1),
      hQ.finiteProduct hB hBcount A hAw hAcount f hf hKB hKA (fun i ↦ (h i).2)⟩

/-- **Stacks 0GCA, part (2).** Flatness (Stacks 0GC9) together with the property of Stacks
0GBW, being adic and topologically of finite type, is stable under base change in the sense of
Remark 0GBF: for continuous homomorphisms `B → A` and `B → C` of Noetherian adic topological
rings with `B → A` flat, adic and topologically of finite type, the completed tensor product
`A ⊗̂_B C` is Noetherian adic and `C → A ⊗̂_B C` is again flat, adic and topologically of finite
type. No condition is imposed on `B → C`. -/
@[stacks 0GCA "part (2)"]
public theorem flatAdicFiniteType_isStableUnderBaseChange' :
    IsStableUnderBaseChangeNoetherian'
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        φ.Flat ∧ RingHom.IsAdic φ ∧ IsTopologicallyOfFiniteType φ) := by
  refine ⟨PropertyIsLocal'.and flat_isLocalNoetherian' adicAndFiniteType_propertyIsLocalNoetherian',
    ?_⟩
  intro B A C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB hA hC hBA hBC ⟨hP, hR⟩
  have hBweak := isCountablyWeaklyAdmissible_of_isAdic hB
  have hred : Rig.IsFiniteTypeOnReductions (algebraMap B A) hBA :=
    Rig.isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType (algebraMap B A) hBA
      hBweak.1.1 (RingHom.isTaut_of_isAdic (algebraMap B A) hR.1) hR.2
  have hstage (J : Ideal C) (_ : IsIdealOfDefinition J) (hJ : _root_.IsAdic J) (n : ℕ) :
      IsNoetherianRing (A ⊗[B] (C ⧸ J ^ n)) :=
    isNoetherianRing_tensor_quotient_of_isAdic_of_isTopologicallyOfFiniteType hBC hR.1 hR.2
      (J ^ n) ((isAdic_iff.mp hJ).1 n)
  exact ⟨completedTensorProduct_isAdic hBA hBC hA.1 (exists_isIdealOfDefinition_fg hA.1) hC.1
      (exists_isIdealOfDefinition_fg hC.1),
    completedTensorProduct_isNoetherianRing_of_isFiniteTypeOnReductions hA.1 hC.1 hBA hBC
      (Or.inl hred),
    flat_completedTensorProduct_of_isNoetherianRing_stages hA hC hP hstage,
    isAdic_and_isTopologicallyOfFiniteType_completedTensorProduct_baseChange
      (isCountablyWeaklyAdmissible_of_isAdic hA).1 (isCountablyWeaklyAdmissible_of_isAdic hC).1
      (Rig.exists_fg_isAdic_of_isAdicRing hC) hBA hBC hR⟩

end TopologicalRing

end
