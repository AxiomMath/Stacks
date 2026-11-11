module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Examples.Geometric.Completion
public import StacksFrontier.Deformation.Examples.Geometric.CompletionRankOneCoefficients
public import StacksFrontier.Deformation.LiftsOfObjects.Smoothness.Criterion

/-!
# The completion functor on tangent spaces

Let `k` be a field, `P` a finite type `k`-algebra which is smooth over `k` outside the zero set
of an ideal `J ⊆ P`, and `P^` the `J`-adic completion. Completion of deformations is a functor
`𝓓_P ⟶ 𝓓_{P^}` over `𝒞_Λ` (**Stacks 0DYV**). This file shows that its differential on tangent
spaces is bijective, which is the second conclusion of **Stacks 0DZ5**.

The argument is the source's. A deformation `x` of `P` over a base presented as `k ⊕ V` is a
square-zero extension of `P` by `P ⊗[k] V` (**Stacks 0GPT**), its completion is one of `P^` by
`P^ ⊗[k] V`, and the canonical map `Q → Q^` of middle rings is a `k`-algebra map compatible with
`P → P^` and with the coefficient map. By the criterion of **Stacks 0GPV** the two classes
therefore have the same image in `Ext¹_P(NL_{P/k}, P^ ⊗[k] V)`; that is
`Deformation.Examples.squareZeroFiberExtClass_completion`. Both comparison maps into that group
are bijective by **Stacks 0DZ4**, in the rank-one form of
`StacksFrontier.Deformation.Examples.Geometric.CompletionRankOneCoefficients`, and the family of
classes is bijective on each tangent space by **Stacks 0DY3**, so the differential is bijective.

## Main results

* `Deformation.Examples.extClass_eq_towerMap_of_middleRingHom`: a map of the middle rings of two
  first-order extensions, over the reductions and over the base `k ⊕ V`, identifies the two
  classes through the two comparison maps of Stacks 0GPV.
* `Deformation.Examples.squareZeroFiberExtClass_completion`: that identification for a
  deformation and its completion.
* `Deformation.Examples.bijective_differential_adicCompletionFunctorData`: **the tangent-space
  conclusion of Stacks 0DZ5.**

## Implementation notes

The completion functor of Stacks 0DYV is recorded as a
`Deformation.Examples.AdicCompletionFunctorData`, and the results here are stated for any such
datum which in addition satisfies
`Deformation.Examples.AdicCompletionFunctorData.IsBaseCompatible`; such data exist, by
`Deformation.Examples.nonempty_isBaseCompatible_adicCompletionFunctorData`. The extra clause is
what makes the canonical map `Q → Q^` a map over the Artinian base, hence a `k`-algebra map
semilinear for the augmentation ideal, and it cannot be recovered from the recorded clauses of a
datum after the fact — `Deformation.Examples.adicCompletionFunctor` is an arbitrary choice of a
datum without it.

`Deformation.Examples.extClass_eq_towerMap_of_middleRingHom` is stated for
`Deformation.Examples.firstOrderExtension` with all algebra structures as instance arguments,
rather than for `Deformation.Examples.fiberFirstOrderExtension`, so that the structures carried
by a point of a fibre are supplied at the point of use; this is what lets the specialisation be
a single application.

## References

* [Stacks Project, Tag 0DZ5](https://stacks.math.columbia.edu/tag/0DZ5)
* [Stacks Project, Tag 0DZ4](https://stacks.math.columbia.edu/tag/0DZ4)
* [Stacks Project, Tag 0DYV](https://stacks.math.columbia.edu/tag/0DYV)
* [Stacks Project, Tag 0DY3](https://stacks.math.columbia.edu/tag/0DY3)
* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
-/

@[expose] public section

open CategoryTheory Stacks.Deformation TrivSqZeroExt
open scoped TensorProduct

universe u w

namespace Deformation.Examples

/-! ### Comparison of two first-order extensions through a map of middle rings -/

section Abstract

variable {k : Type w} [Field k] {V : Type w} [AddCommGroup V] [Module k V]

local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

variable {P C : Type w} [CommRing P] [Algebra k P] [CommRing C] [Algebra k C]
  [Algebra P C] [IsScalarTower k P C]
  {Q : Type w} [CommRing Q] [Algebra (TrivSqZeroExt k V) Q] [Algebra k Q]
  [IsScalarTower k (TrivSqZeroExt k V) Q] [Module.Flat (TrivSqZeroExt k V) Q]
  {Q' : Type w} [CommRing Q'] [Algebra (TrivSqZeroExt k V) Q'] [Algebra k Q']
  [IsScalarTower k (TrivSqZeroExt k V) Q'] [Module.Flat (TrivSqZeroExt k V) Q']

/-- **A map of middle rings identifies the two classes of Stacks 0GPV.** Let `Q` be a
first-order flat deformation of `P` over `k ⊕ V` and `Q'` one of `C` over `k ⊕ V`, and let
`g : Q → Q'` be a ring map which is a map of `k ⊕ V`-algebras and carries the reduction `Q → P`
to the reduction `Q' → C` over `P → C`. Then the class of the square-zero extension of `P` by
`P ⊗[k] V` determined by `Q` and the class of the one of `C` by `C ⊗[k] V` determined by `Q'`
have the same image in `Ext¹_P(NL_{P/k}, C ⊗[k] V)`.

This is the criterion of **Stacks 0GPV** applied to `g`: a `k`-algebra map of middle rings over
`P → C` and over the coefficient map `c` exists, so the two images agree. -/
public theorem extClass_eq_towerMap_of_middleRingHom
    (π : Q →ₐ[k] P) (hπ : Function.Surjective π) (hπa : IsFirstOrderReduction V π)
    (hker : ∀ z : Q, π z = 0 → z ∈ kerIdeal k V • (⊤ : Submodule (TrivSqZeroExt k V) Q))
    (π' : Q' →ₐ[k] C) (hπ' : Function.Surjective π') (hπa' : IsFirstOrderReduction V π')
    (hker' : ∀ z : Q', π' z = 0 → z ∈ kerIdeal k V • (⊤ : Submodule (TrivSqZeroExt k V) Q'))
    (c : P ⊗[k] V →ₗ[P] C ⊗[k] V)
    (hc : ∀ (p : P) (v : V), c (p ⊗ₜ[k] v) = algebraMap P C p ⊗ₜ[k] v)
    (g : Q →+* Q')
    (hgbase : ∀ a : TrivSqZeroExt k V,
      g (algebraMap (TrivSqZeroExt k V) Q a) = algebraMap (TrivSqZeroExt k V) Q' a)
    (hgred : ∀ z : Q, π' (g z) = algebraMap P C (π z)) :
    naiveCotangentExtOneMap k P c (extClass (firstOrderExtension (V := V) π hπ hπa hker))
      = naiveCotangentExtOneTowerMap k P C
          (extClass (firstOrderExtension (V := V) π' hπ' hπa' hker')) := by
  have hcm : ∀ r : k, g (algebraMap k Q r) = algebraMap k Q' r := by
    intro r
    rw [IsScalarTower.algebraMap_apply k (TrivSqZeroExt k V) Q, hgbase,
      ← IsScalarTower.algebraMap_apply k (TrivSqZeroExt k V) Q']
  have hkern : ∀ m : P ⊗[k] V,
      g (firstOrderConormalHom π hπ m) = firstOrderConormalHom π' hπ' (c m) := by
    intro m
    induction m with
    | add m₁ m₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul p v =>
      obtain ⟨q, hq⟩ := hπ p
      have hq' : π' (g q) = algebraMap P C p := by rw [hgred, hq]
      rw [hc, firstOrderConormalHom_tmul π hπ hker p v q hq,
        firstOrderConormalHom_tmul π' hπ' hker' (algebraMap P C p) v (g q) hq',
        Algebra.smul_def, Algebra.smul_def, map_mul, hgbase]
  refine (exists_compatible_algebraMap_iff k P C c
    (firstOrderExtension (V := V) π hπ hπa hker)
    (firstOrderExtension (V := V) π' hπ' hπa' hker')).mp ?_
  exact ⟨{ toRingHom := g, commutes' := hcm }, fun z => hgred z, fun m => hkern m⟩

end Abstract

/-! ### The canonical map from a deformation to its completion -/

section Fibre

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P] {J : Ideal P}
  {V : Type w} [AddCommGroup V] [Module k V]

local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

/-- **The canonical map from the fibre of a deformation to the fibre of its completion.** The
recorded fibre identification of a completion functor carries this to the canonical map of a
ring into its adic completion. -/
public noncomputable def completionFiberHom
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    X.left.fiber →+* (F.functor.obj X).left.fiber :=
  ((F.fiberEquiv X).symm : AdicCompletion (J.comap X.hom.map.hom) X.left.fiber ≃+*
      (F.functor.obj X).left.fiber).toRingHom.comp
    (algebraMap X.left.fiber (AdicCompletion (J.comap X.hom.map.hom) X.left.fiber))

/-- The canonical map to the completion is compatible with the two reductions: this is the
`special_comm` clause of the recorded data. -/
public theorem completionFiberHom_reduction
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) (q : X.left.fiber) :
    (F.functor.obj X).hom.map.hom (completionFiberHom F X q)
      = algebraMap P (AdicCompletion J P) (X.hom.map.hom q) :=
  F.special_comm X q

/-- **The canonical map to the completion is a map of algebras over the Artinian base.** This is
where `Deformation.Examples.AdicCompletionFunctorData.IsBaseCompatible` is used: the structural
map of the completed fibre out of its own base is carried to the structural map of the fibre,
read through the identification of the two bases. -/
public theorem completionFiberHom_algebraMap
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) (hF : F.IsBaseCompatible)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (a : ((F.functor.obj X).left.base : Type w)) :
    completionFiberHom F X
        (algebraMap ((X.left.base : Type w)) X.left.fiber
          ((eqToHom (F.functor.w_obj X)).hom a))
      = algebraMap (((F.functor.obj X).left.base : Type w)) (F.functor.obj X).left.fiber a := by
  refine (F.fiberEquiv X).injective ?_
  rw [hF X a]
  change (F.fiberEquiv X) ((F.fiberEquiv X).symm (algebraMap X.left.fiber
    (AdicCompletion (J.comap X.hom.map.hom) X.left.fiber)
      (algebraMap ((X.left.base : Type w)) X.left.fiber
        ((eqToHom (F.functor.w_obj X)).hom a)))) = _
  rw [(F.fiberEquiv X).apply_symm_apply]
  exact (IsScalarTower.algebraMap_apply ((X.left.base : Type w)) X.left.fiber
    (AdicCompletion (J.comap X.hom.map.hom) X.left.fiber) _).symm

variable {A : ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- The image of a point of a fibre of the deformation category of `P` under a completion
functor: a point of the fibre of the deformation category of `P^` over the same base. -/
public def completionFiberPoint
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J)
    (x : (ringDeformationProjection Λ k P).Fiber A) :
    (ringDeformationProjection Λ k (AdicCompletion J P)).Fiber A :=
  ⟨F.functor.obj x.1, (F.functor.w_obj x.1).trans x.2⟩

/-- The two canonical presentations of the base of a point of a fibre over `k ⊕ V` and of its
completion agree through the identification of the two bases. -/
public theorem fiberSquareZeroEquiv_completionFiberPoint (W : FGModuleCat.{w} k)
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (a : (((F.functor.obj x.1).left.base) : Type w)) :
    fiberSquareZeroEquiv W x ((eqToHom (F.functor.w_obj x.1)).hom a)
      = fiberSquareZeroEquiv W (completionFiberPoint F x) a := by
  have h₁ : (eqToHom (F.functor.w_obj x.1)).hom a
      = ringEquivOfEq (F.functor.w_obj x.1) a := hom_eqToHom_apply _ a
  exact (congrArg (fun z => fiberSquareZeroEquiv W x z) h₁).trans
    (ringEquivOfEq_trans_apply (F.functor.w_obj x.1) x.2 a)

/-- The canonical presentations of the two bases carry the same element of `k ⊕ V` to elements
matched by the identification of the bases. -/
public theorem eqToHom_fiberSquareZeroEquiv_symm (W : FGModuleCat.{w} k)
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (a : TrivSqZeroExt k W.obj) :
    (eqToHom (F.functor.w_obj x.1)).hom
        ((fiberSquareZeroEquiv W (completionFiberPoint F x)).symm a)
      = (fiberSquareZeroEquiv W x).symm a := by
  refine (fiberSquareZeroEquiv W x).injective ?_
  exact ((fiberSquareZeroEquiv_completionFiberPoint W F x
      ((fiberSquareZeroEquiv W (completionFiberPoint F x)).symm a)).trans
    ((fiberSquareZeroEquiv W (completionFiberPoint F x)).apply_symm_apply a)).trans
    ((fiberSquareZeroEquiv W x).apply_symm_apply a).symm

/-- A structure map out of `k ⊕ V` is the structure map of a base presented by `e`, read through
`e.symm`. -/
private theorem algebraMap_eq_algebraMap_symm {R Q : Type w} [CommRing R] [CommRing Q]
    [Algebra R Q] [Algebra (TrivSqZeroExt k V) Q] (e : R ≃+* TrivSqZeroExt k V)
    (hQ : ∀ r : R, algebraMap (TrivSqZeroExt k V) Q (e r) = algebraMap R Q r)
    (a : TrivSqZeroExt k V) :
    algebraMap (TrivSqZeroExt k V) Q a = algebraMap R Q (e.symm a) := by
  rw [← hQ, e.apply_symm_apply]

/-- **The class of a deformation and the class of its completion agree through the two
comparison maps of Stacks 0GPV.** For a point `x` of the fibre of the deformation category of
`P` over the square-zero base `k ⊕ V`, the class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)` of `x` and the
class in `Ext¹_{P^}(NL_{P^/k}, P^ ⊗[k] V)` of its completion have the same image in
`Ext¹_P(NL_{P/k}, P^ ⊗[k] V)`.

The map of middle rings is the canonical map `Q → Q^`, which is a map over the Artinian base by
`Deformation.Examples.completionFiberHom_algebraMap` — this is where base-compatibility of the
completion functor is used — and compatible with the two reductions by
`Deformation.Examples.completionFiberHom_reduction`. -/
public theorem squareZeroFiberExtClass_completion [IsNoetherianRing P] (W : FGModuleCat.{w} k)
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) (hF : F.IsBaseCompatible)
    (c : P ⊗[k] W.obj →ₗ[P] AdicCompletion J P ⊗[k] W.obj)
    (hc : ∀ (p : P) (v : W.obj),
      c (p ⊗ₜ[k] v) = algebraMap P (AdicCompletion J P) p ⊗ₜ[k] v)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W)) :
    naiveCotangentExtOneMap k P c (squareZeroFiberExtClass W x)
      = naiveCotangentExtOneTowerMap k P (AdicCompletion J P)
          (squareZeroFiberExtClass W (completionFiberPoint F x)) := by
  set y := completionFiberPoint F x with hy
  set eX := fiberSquareZeroEquiv W x with heX
  set eY := fiberSquareZeroEquiv W y with heY
  let _ := fiberAugAlgebra x
  let _ := fiberRedAlgebra x
  let _ := fiberBaseAlgebra x
  let _ := fiber_isScalarTower_aug x
  let _ := fiber_isScalarTower_red x
  let _ := fiber_isPushout x
  let _ := algebraOfBaseEquiv x.1.left.fiber eX
  let _ := baseAlgebraOfBaseEquiv x.1.left.fiber eX
  let _ := isScalarTower_baseAlgebraOfBaseEquiv x.1.left.fiber eX
  let _ := flat_algebraOfBaseEquiv x.1.left.fiber eX
    (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX)
  let _ := fiberAugAlgebra y
  let _ := fiberRedAlgebra y
  let _ := fiberBaseAlgebra y
  let _ := fiber_isScalarTower_aug y
  let _ := fiber_isScalarTower_red y
  let _ := fiber_isPushout y
  let _ := algebraOfBaseEquiv y.1.left.fiber eY
  let _ := baseAlgebraOfBaseEquiv y.1.left.fiber eY
  let _ := isScalarTower_baseAlgebraOfBaseEquiv y.1.left.fiber eY
  let _ := flat_algebraOfBaseEquiv y.1.left.fiber eY
    (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY)
  have hρX := fiberAug_fiberSquareZeroEquiv W x
  have hρY := fiberAug_fiberSquareZeroEquiv W y
  have hgbase : ∀ a : TrivSqZeroExt k W.obj,
      completionFiberHom F x.1 (algebraMap (TrivSqZeroExt k W.obj) x.1.left.fiber a)
        = algebraMap (TrivSqZeroExt k W.obj) y.1.left.fiber a := by
    intro a
    rw [algebraMap_eq_algebraMap_symm eX (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX),
      algebraMap_eq_algebraMap_symm eY (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY),
      ← eqToHom_fiberSquareZeroEquiv_symm W F x a]
    exact completionFiberHom_algebraMap F hF x.1 (eY.symm a)
  exact extClass_eq_towerMap_of_middleRingHom (V := W.obj)
    (reductionOfBaseEquiv (P := P) x.1.left.fiber eX
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX) hρX)
    (surjective_algebraMap_of_isPushout x.1.left.fiber (fiberAug_surjective x))
    (isFirstOrderReduction_reductionOfBaseEquiv x.1.left.fiber eX
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX) hρX)
    (mem_kerIdeal_smul_of_algebraMap_eq_zero x.1.left.fiber eX
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX) hρX (fiberAug_surjective x))
    (reductionOfBaseEquiv (P := AdicCompletion J P) y.1.left.fiber eY
      (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY) hρY)
    (surjective_algebraMap_of_isPushout y.1.left.fiber (fiberAug_surjective y))
    (isFirstOrderReduction_reductionOfBaseEquiv y.1.left.fiber eY
      (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY) hρY)
    (mem_kerIdeal_smul_of_algebraMap_eq_zero y.1.left.fiber eY
      (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY) hρY (fiberAug_surjective y))
    c hc (completionFiberHom F x.1) hgbase (completionFiberHom_reduction F x.1)

end Fibre

/-! ### The differential of the completion functor -/

section Tangent

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)

/-- The image of a point of a fibre under the based functor of a completion datum is the
completed point. -/
public theorem fiberFunctor_obj_completionFiberPoint
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J)
    (x : (ringDeformationProjection Λ k P).Fiber A) :
    (fiberFunctor F.functor A).obj x = completionFiberPoint F x := rfl

/-- The differential of a based functor is the map on fibrewise isomorphism classes over the
square-zero extension of the rank-one module. -/
public theorem differential_eq_mapIsomorphismClasses
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) :
    differential (𝓕 := ringDeformationBasedCategory Λ k P)
        (𝓖 := ringDeformationBasedCategory Λ k (AdicCompletion J P))
        isCofiberedInGroupoids_ringDeformationProjection
        isCofiberedInGroupoids_ringDeformationProjection F.functor
      = mapIsomorphismClasses (𝓕 := ringDeformationBasedCategory Λ k P)
          (𝓖 := ringDeformationBasedCategory Λ k (AdicCompletion J P))
          isCofiberedInGroupoids_ringDeformationProjection
          isCofiberedInGroupoids_ringDeformationProjection F.functor
          ((squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k k)) := rfl

/-- **Stacks 0DZ5, the tangent-space conclusion.** Let `k` be a field, `P` a finite type
`k`-algebra, `J ⊆ P` an ideal such that `Spec(P) → Spec(k)` is smooth outside `V(J)`, and `P^`
the `J`-adic completion. The completion functor `𝓓_P ⟶ 𝓓_{P^}` of **Stacks 0DYV** induces a
bijection on tangent spaces.

The proof is the source's: the family of extension classes of **Stacks 0DY3** is a bijection of
each tangent space with a first Ext group of the naive cotangent complex, by
`Deformation.Examples.bijective_tangentExtClass`; the functor is compatible with those classes
through the two comparison maps of **Stacks 0GPV**, by
`Deformation.Examples.squareZeroFiberExtClass_completion`; and both comparison maps are
bijective by **Stacks 0DZ4**. -/
public theorem bijective_differential_adicCompletionFunctorData
    [Algebra.FiniteType k P]
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) (hF : F.IsBaseCompatible)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    Function.Bijective (differential (𝓕 := ringDeformationBasedCategory Λ k P)
      (𝓖 := ringDeformationBasedCategory Λ k (AdicCompletion J P))
      isCofiberedInGroupoids_ringDeformationProjection
      isCofiberedInGroupoids_ringDeformationProjection F.functor) := by
  have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  set W := FGModuleCat.of k k with hW
  let ι : ((W.obj : Type w)) ≃ₗ[k] k := LinearEquiv.refl k k
  have hc := completionCoefficientMap_tmul k P J ι
  have hΦ : Function.Bijective (fun z => naiveCotangentExtOneTowerMap k P (AdicCompletion J P)
      (tangentExtClass (Λ := Λ) (P := AdicCompletion J P) W z)) :=
    (bijective_naiveCotangentExtOneTowerMap_rankOne k P J hsm ι).comp
      (bijective_tangentExtClass (Λ := Λ) (P := AdicCompletion J P) W)
  have hΨ : Function.Bijective (fun z => naiveCotangentExtOneMap k P
      (completionCoefficientMap k P J ι) (tangentExtClass (Λ := Λ) (P := P) W z)) :=
    (bijective_naiveCotangentExtOneMap_completionCoefficientMap k P J hsm ι).comp
      (bijective_tangentExtClass (Λ := Λ) (P := P) W)
  have key : ∀ x : (ringDeformationBasedCategory Λ k P).p.Fiber
        ((squareZeroExtensionArtinian Λ k).obj W),
      naiveCotangentExtOneTowerMap k P (AdicCompletion J P)
          (tangentExtClass W (differential (𝓕 := ringDeformationBasedCategory Λ k P)
            (𝓖 := ringDeformationBasedCategory Λ k (AdicCompletion J P))
            isCofiberedInGroupoids_ringDeformationProjection
            isCofiberedInGroupoids_ringDeformationProjection F.functor
            (classOf (ringDeformationBasedCategory Λ k P)
              isCofiberedInGroupoids_ringDeformationProjection x)))
        = naiveCotangentExtOneMap k P (completionCoefficientMap k P J ι)
          (tangentExtClass W (classOf (ringDeformationBasedCategory Λ k P)
            isCofiberedInGroupoids_ringDeformationProjection x)) := fun x => by
    have hstep : differential (𝓕 := ringDeformationBasedCategory Λ k P)
      (𝓖 := ringDeformationBasedCategory Λ k (AdicCompletion J P))
      isCofiberedInGroupoids_ringDeformationProjection
      isCofiberedInGroupoids_ringDeformationProjection F.functor
        (classOf (ringDeformationBasedCategory Λ k P)
          isCofiberedInGroupoids_ringDeformationProjection x)
        = classOf (ringDeformationBasedCategory Λ k (AdicCompletion J P))
          isCofiberedInGroupoids_ringDeformationProjection (completionFiberPoint F x) :=
      mapIsomorphismClasses_classOf isCofiberedInGroupoids_ringDeformationProjection
        isCofiberedInGroupoids_ringDeformationProjection F.functor x
    rw [hstep]
    have e₁ := tangentExtClass_classOf (Λ := Λ) (P := AdicCompletion J P) W
      (completionFiberPoint F x)
    have e₂ := tangentExtClass_classOf (Λ := Λ) (P := P) W x
    exact (congrArg (fun t => naiveCotangentExtOneTowerMap k P (AdicCompletion J P) t) e₁).trans
      (((squareZeroFiberExtClass_completion W F hF
            (completionCoefficientMap k P J ι) hc x).symm).trans
        (congrArg (fun t => naiveCotangentExtOneMap k P
          (completionCoefficientMap k P J ι) t) e₂.symm))
  refine (Function.Bijective.of_comp_iff' hΦ _).mp ?_
  refine bijective_of_forall_eq hΨ (fun z => ?_)
  obtain ⟨x, hx⟩ := classOf_surjective (ringDeformationBasedCategory Λ k P)
    isCofiberedInGroupoids_ringDeformationProjection
    ((squareZeroExtensionArtinian Λ k).obj W) z
  subst hx
  exact key x

/-- **Stacks 0DZ5, the smoothness conclusion, granted the correspondence of liftability.**
Under the hypotheses of Stacks 0DZ5, the completion functor `𝓓_P ⟶ 𝓓_{P^}` is smooth as soon as
liftability of a deformation along a small extension of the Artinian base is implied by
liftability of its completion.

That implication is the deformation-category reading of **Stacks 0DZ3** and is the only input
missing: the other half of the criterion of **Stacks 0DYP**, surjectivity of the differential,
is `Deformation.Examples.bijective_differential_adicCompletionFunctorData`. -/
public theorem isSmooth_adicCompletionFunctorData_of_lifts
    [Algebra.FiniteType k P]
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) (hF : F.IsBaseCompatible)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (hlifts : ∀ ⦃B A : ArtinianLocalAlgCat.{u, w, w} Λ k⦄ (f : B ⟶ A),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
        ∀ x : (ringDeformationBasedCategory Λ k P).p.Fiber A,
          (∃ (y' : (ringDeformationBasedCategory Λ k (AdicCompletion J P)).obj)
              (g : y' ⟶ F.functor.obj x.1),
            (ringDeformationBasedCategory Λ k (AdicCompletion J P)).p.IsHomLift f g) →
            ∃ (x' : (ringDeformationBasedCategory Λ k P).obj) (h : x' ⟶ x.1),
              (ringDeformationBasedCategory Λ k P).p.IsHomLift f h) :
    IsSmooth F.functor :=
  (isSmooth_iff_differential_surjective_and_lifts
      (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P)
      (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k)
        (AdicCompletion J P)) F.functor).mpr
    ⟨(bijective_differential_adicCompletionFunctorData P J F hF hsm).2, hlifts⟩

end Tangent

end Deformation.Examples

end
