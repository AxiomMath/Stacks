module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.QcohUniversalDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.PuncturedSpectrumAffineCriterion

/-!
# The complement of a dense affine open is an effective Cartier divisor

Let `X` be a Noetherian scheme with affine diagonal and `U ⊆ X` a dense affine open.  If
`𝒪_{X,x}` is a unique factorization domain for every `x ∈ X \ U`, then there is an effective
Cartier divisor `D ⊆ X` with `U = X \ D`.

## Main results

* `AlgebraicGeometry.exists_effectiveCartierDivisor_compl_affineOpen`: **Stacks Tag 0EGJ.**

## The argument

Because the diagonal of `X` is affine and `U` is affine, the inclusion `U ⟶ X` is an affine
morphism, so each generic point of an irreducible component of `X \ U` has local ring of
dimension one, by
`Stacks.Divisors.ringKrullDim_stalk_at_genericPoint_compl_affineOpenImmersion_eq_one`.
Each such component, with its reduced structure, is therefore an integral closed subscheme of
codimension one, hence an effective Cartier divisor by Tag 0AGA
(`AlgebraicGeometry.isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid`).
Noetherianness bounds the number of components, and the sum of the finitely many of them is an
effective Cartier divisor by Tag 01WU (`AlgebraicGeometry.isEffectiveCartierDivisor_mul`) whose
support is exactly `X \ U`.

## References

* [Stacks Project, Tag 0EGJ](https://stacks.math.columbia.edu/tag/0EGJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors TopologicalSpace

universe u

namespace AlgebraicGeometry

private alias affine_inclusion_of_affine_diagonal :=
  Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen

private noncomputable def componentSupport {X : Scheme.{u}} {B : Set X}
    (hB : IsClosed B) (C : irreducibleComponents B) : IrreducibleCloseds X :=
  ⟨Subtype.val '' (C : Set B), C.property.1.image _ continuous_subtype_val.continuousOn,
    hB.isClosedEmbedding_subtypeVal.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ C.property)⟩

private noncomputable def componentIdeal {X : Scheme.{u}} {B : Set X}
    (hB : IsClosed B) (C : irreducibleComponents B) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨componentSupport hB C, (componentSupport hB C).isClosed⟩

private lemma componentIdeal_support {X : Scheme.{u}} {B : Set X}
    (hB : IsClosed B) (C : irreducibleComponents B) :
    ((componentIdeal hB C).support : Set X) = (componentSupport hB C : Set X) := by
  simp [componentIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]

open Stacks.AlgebraicGeometry.IrreducibleDevissage in
private lemma componentIdeal_isIntegral {X : Scheme.{u}} {B : Set X}
    (hB : IsClosed B) (C : irreducibleComponents B) :
    IsIntegral (componentIdeal hB C).subscheme := by
  unfold componentIdeal
  exact isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
    (componentSupport hB C).isIrreducible'

private lemma componentIdeal_genericPoint_closure {X : Scheme.{u}} {B : Set X}
    (hB : IsClosed B) (C : irreducibleComponents B)
    [IsIntegral (componentIdeal hB C).subscheme] :
    closure ({(componentIdeal hB C).subschemeι
      (_root_.genericPoint (componentIdeal hB C).subscheme)} : Set X) =
        (componentSupport hB C : Set X) := by
  let I := componentIdeal hB C
  rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ, I.range_subschemeι, componentIdeal_support]

private lemma componentSupport_genericPoint_closure {X : Scheme.{u}} {B : Set X}
    (hB : IsClosed B) [QuasiSober B] (C : irreducibleComponents B) :
    closure ({((genericPoints.ofComponent C).1 : X)} : Set X) =
      (componentSupport hB C : Set X) := by
  rw [← Set.image_singleton, hB.isClosedEmbedding_subtypeVal.closure_image_eq,
    (genericPoints.isGenericPoint_ofComponent C).def]
  rfl

attribute [local instance] specializationOrder in
private lemma codimension_closureSingleton_eq_coheight {X : Type u}
    [TopologicalSpace X] [QuasiSober X] [T0Space X] (x : X) :
    codimension (IrreducibleCloseds.closureSingleton x) = Order.coheight x := by
  rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton x =
    (irreducibleSetEquivPoints (α := X)).symm x from IrreducibleCloseds.ext rfl]
  exact Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x

/-- **Stacks Project, Tag 0EGJ.** The complement of a dense affine open in a Noetherian
scheme with affine diagonal is the support of an effective Cartier divisor if its local
rings along the complement are UFDs. -/
@[stacks 0EGJ, stacks 0BCW "the separated case, where the diagonal is affine"]
theorem exists_effectiveCartierDivisor_compl_affineOpen
    (X : Scheme.{u}) [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (hDense : Dense (U : Set X))
    (hUFD : ∀ x : X, x ∉ U → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ I : X.IdealSheafData,
      IsEffectiveCartierDivisor I ∧
        (I.support : Set X) = (U : Set X)ᶜ := by
  classical
  let B : Set X := (U : Set X)ᶜ
  have hB : IsClosed B := U.2.isClosed_compl
  have : QuasiSober B := hB.isClosedEmbedding_subtypeVal.quasiSober
  let K := irreducibleComponents B
  have : Finite K := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let _ : Fintype K := Fintype.ofFinite K
  have := affine_inclusion_of_affine_diagonal X U hU
  have hdiv (C : K) : IsEffectiveCartierDivisor (componentIdeal hB C) := by
    have := componentIdeal_isIntegral hB C
    apply isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid
    · rw [show IrreducibleCloseds.closureSingleton ((componentIdeal hB C).subschemeι
          (_root_.genericPoint (componentIdeal hB C).subscheme)) =
          IrreducibleCloseds.closureSingleton ((genericPoints.ofComponent C).1 : X) from
        IrreducibleCloseds.ext ((componentIdeal_genericPoint_closure hB C).trans
          (componentSupport_genericPoint_closure hB C).symm),
        codimension_closureSingleton_eq_coheight]
      have h : (Order.coheight ((genericPoints.ofComponent C).1 : X) : WithBot ℕ∞) = 1 := by
        rw [← ringKrullDim_stalk_eq_coheight]
        exact ringKrullDim_stalk_at_genericPoint_compl_affineOpenImmersion_eq_one X U C.property
          (genericPoints.isGenericPoint_ofComponent C) (Or.inl hDense)
      exact_mod_cast h
    · intro x hx
      change x ∈ (componentSupport hB C : Set X) at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact hUFD _ y.property
  have hprod_support (s : Finset K) :
      ((∏ C ∈ s, componentIdeal hB C).support : Set X) =
        ⋃ C ∈ s, ((componentIdeal hB C).support : Set X) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert C s hCs ih =>
      rw [Finset.prod_insert hCs, Scheme.IdealSheafData.support_mul, Closeds.coe_sup, ih]
      ext x
      simp
  have hI_support_set : ((∏ C : K, componentIdeal hB C).support : Set X) =
      ⋃ C : K, ((componentIdeal hB C).support : Set X) := by
    simpa using hprod_support Finset.univ
  refine ⟨∏ C : K, componentIdeal hB C,
    Finset.prod_induction _ IsEffectiveCartierDivisor
      (fun a b => isEffectiveCartierDivisor_mul a b)
      (by simpa using isEffectiveCartierDivisor_top)
      fun C _ => hdiv C, ?_⟩
  ext x
  rw [hI_support_set, Set.mem_iUnion]
  constructor
  · rintro ⟨C, hxC⟩
    rw [componentIdeal_support] at hxC
    obtain ⟨y, -, rfl⟩ := hxC
    exact y.property
  · intro hx
    refine ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (⟨x, hx⟩ : B)⟩, ?_⟩
    rw [componentIdeal_support]
    exact ⟨⟨x, hx⟩, mem_irreducibleComponent, rfl⟩

end AlgebraicGeometry

end
