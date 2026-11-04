module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Examples.Geometric.CompletionTangentSpace
public import StacksFrontier.Deformation.Examples.Geometric.Localization
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationRankOneCoefficients

/-!
# The localization functor on tangent spaces

Let `k` be a field, `P` a finite type `k`-algebra, `S ⊆ P` a multiplicative subset such that
`Spec(P) → Spec(k)` is smooth at every point of `V(g)` for every `g ∈ S`, and `S⁻¹P` the
localization. Localization of deformations is a functor `𝓓_P ⟶ 𝓓_{S⁻¹P}` over `𝒞_Λ`
(**Stacks 0DYS**). This file shows that its differential on tangent spaces is bijective, which
is the second conclusion of **Stacks 0DZ9**.

The argument is the source's. A deformation `x` of `P` over a base presented as `k ⊕ V` is a
square-zero extension of `P` by `P ⊗[k] V` (**Stacks 0GPT**), its localization is one of `S⁻¹P`
by `S⁻¹P ⊗[k] V`, and the localization map `Q → S_Q⁻¹Q` of middle rings is a `k`-algebra map
compatible with `P → S⁻¹P` and with the coefficient map. By the criterion of **Stacks 0GPV** the
two classes therefore have the same image in `Ext¹_P(NL_{P/k}, S⁻¹P ⊗[k] V)`; that is
`Deformation.Examples.squareZeroFiberExtClass_localization`. **Stacks 0DZ8**, read in Ext form
at rank-one coefficients as
`Deformation.Examples.naiveCotangentExtOneMap_localizationCoefficientMap`, says that the same
image is reached from the bijection of **Stacks 0DZ8**; and restriction along a localization is
injective on first-order extension classes, by
`Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_isLocalization`. So the differential
agrees with the bijection of Stacks 0DZ8 through the family of extension classes of
**Stacks 0DY3**, which is bijective on each tangent space.

## Main results

* `Deformation.Examples.localizationMap_algebraMap`: the localization map of a deformation is a
  map of algebras over the Artinian base, read through the identification of the two bases.
* `Deformation.Examples.squareZeroFiberExtClass_localization`: the class of a deformation over
  `k ⊕ V` and the class of its localization have the same image in
  `Ext¹_P(NL_{P/k}, S⁻¹P ⊗[k] V)`.
* `Deformation.Examples.bijective_differential_localizationFunctorData`: **the tangent-space
  conclusion of Stacks 0DZ9**, for an arbitrary functor datum of Stacks 0DYS.
* `Deformation.Examples.bijective_differential_localizationFunctor`: the same at the canonical
  localization functor `Deformation.Examples.localizationFunctor`.

## Implementation notes

Unlike the completion functor of Stacks 0DYV, the localization functor of Stacks 0DYS is
recorded by `Deformation.Examples.LocalizationFunctorData`, whose `base_comm` clause already
says that the localization map of each deformation is a map over the Artinian base. So no extra
base-compatibility clause is needed and no hypothesis on the datum is carried: the results below
hold for every datum, and in particular for the canonical `localizationFunctor`, which is an
honest definition rather than a choice.

The other assertion of Stacks 0DZ9, smoothness of the functor, is reduced by the criterion of
**Stacks 0DYP** to surjectivity of the differential — supplied in full by the results here — and
to the correspondence of liftability of **Stacks 0DZ7**. That correspondence, and smoothness,
are in `StacksFrontier.Deformation.Examples.Geometric.LocalizationSmooth`: the criterion of
Stacks 0DYP quantifies only over *small* extensions of Artinian bases, whose kernels are
square-zero, and at a square-zero kernel Stacks 0DZ7 carries no hypothesis, by
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_of_sqZero`. Nothing about
smoothness is asserted in this file.

## References

* [Stacks Project, Tag 0DZ9](https://stacks.math.columbia.edu/tag/0DZ9)
* [Stacks Project, Tag 0DZ8](https://stacks.math.columbia.edu/tag/0DZ8)
* [Stacks Project, Tag 0DYS](https://stacks.math.columbia.edu/tag/0DYS)
* [Stacks Project, Tag 0DY3](https://stacks.math.columbia.edu/tag/0DY3)
* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
-/

@[expose] public section

open CategoryTheory Stacks.Deformation TrivSqZeroExt
open scoped TensorProduct

universe u w

namespace Deformation.Examples

/-! ### The canonical map from a deformation to its localization -/

section Fibre

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P] {S : Submonoid P}
  {V : Type w} [AddCommGroup V] [Module k V]

/-- The `kᵐᵒᵖ`-module structure on `V` in which `op c` acts as `c`. -/
local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The left and right actions of `k` on `V` agree. -/
local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

/-- Transporting an element of the carrier of an object of `𝒞_Λ` along an equality of objects
and back is the identity. -/
private theorem cast_hom_eqToHom {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B)
    (a : (A : Type w)) :
    cast (congrArg ArtinianLocalAlgCat.carrier h.symm) ((eqToHom h).hom a) = a := by
  subst h
  rfl

/-- Transporting an element of the carrier of an object of `𝒞_Λ` along an equality of objects
and back is the identity. -/
public alias cast_hom_eqToHom_of_eq := cast_hom_eqToHom

/-- **The localization map of a deformation is a map of algebras over the Artinian base.** This
is the `base_comm` clause of the recorded data of **Stacks 0DYS**, read through the
identification of the base of the localized deformation with the base of the deformation. -/
public theorem localizationMap_algebraMap
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (a : ((F.functor.obj X).left.base : Type w)) :
    F.localizationMap X
        (algebraMap ((X.left.base : Type w)) X.left.fiber
          ((eqToHom (F.functor.w_obj X)).hom a))
      = algebraMap (((F.functor.obj X).left.base : Type w)) (F.functor.obj X).left.fiber a := by
  rw [F.base_comm X ((eqToHom (F.functor.w_obj X)).hom a)]
  exact congrArg _ (cast_hom_eqToHom (F.functor.w_obj X) a)

/-- The localization map is compatible with the two reductions: this is the `specialFiber_comm`
clause of the recorded data. -/
public theorem localizationMap_reduction
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) (q : X.left.fiber) :
    (F.functor.obj X).hom.map.hom (F.localizationMap X q)
      = algebraMap P (Localization S) (X.hom.map.hom q) :=
  (F.specialFiber_comm X q).symm

variable {A : ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- The image of a point of a fibre of the deformation category of `P` under a localization
functor: a point of the fibre of the deformation category of `S⁻¹P` over the same base. -/
public def localizationFiberPoint
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (x : (ringDeformationProjection Λ k P).Fiber A) :
    (ringDeformationProjection Λ k (Localization S)).Fiber A :=
  ⟨F.functor.obj x.1, (F.functor.w_obj x.1).trans x.2⟩

/-- The two canonical presentations of the base of a point of a fibre over `k ⊕ V` and of its
localization agree through the identification of the two bases. -/
public theorem fiberSquareZeroEquiv_localizationFiberPoint (W : FGModuleCat.{w} k)
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (a : (((F.functor.obj x.1).left.base) : Type w)) :
    fiberSquareZeroEquiv W x ((eqToHom (F.functor.w_obj x.1)).hom a)
      = fiberSquareZeroEquiv W (localizationFiberPoint F x) a :=
  (congrArg (fiberSquareZeroEquiv W x) (hom_eqToHom_apply (F.functor.w_obj x.1) a)).trans
    (ringEquivOfEq_trans_apply (F.functor.w_obj x.1) x.2 a)

/-- The canonical presentations of the two bases carry the same element of `k ⊕ V` to elements
matched by the identification of the bases. -/
public theorem eqToHom_fiberSquareZeroEquiv_symm_localization (W : FGModuleCat.{w} k)
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (a : TrivSqZeroExt k W.obj) :
    (eqToHom (F.functor.w_obj x.1)).hom
        ((fiberSquareZeroEquiv W (localizationFiberPoint F x)).symm a)
      = (fiberSquareZeroEquiv W x).symm a :=
  (fiberSquareZeroEquiv W x).injective <|
    ((fiberSquareZeroEquiv_localizationFiberPoint W F x
      ((fiberSquareZeroEquiv W (localizationFiberPoint F x)).symm a)).trans
    ((fiberSquareZeroEquiv W (localizationFiberPoint F x)).apply_symm_apply a)).trans
    ((fiberSquareZeroEquiv W x).apply_symm_apply a).symm

/-- **The class of a deformation and the class of its localization agree through the two
comparison maps of Stacks 0GPV.** For a point `x` of the fibre of the deformation category of
`P` over the square-zero base `k ⊕ V`, the class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)` of `x` and the
class in `Ext¹_{S⁻¹P}(NL_{S⁻¹P/k}, S⁻¹P ⊗[k] V)` of its localization have the same image in
`Ext¹_P(NL_{P/k}, S⁻¹P ⊗[k] V)`. -/
public theorem squareZeroFiberExtClass_localization (W : FGModuleCat.{w} k)
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (c : P ⊗[k] W.obj →ₗ[P] Localization S ⊗[k] W.obj)
    (hc : ∀ (p : P) (v : W.obj),
      c (p ⊗ₜ[k] v) = algebraMap P (Localization S) p ⊗ₜ[k] v)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W)) :
    naiveCotangentExtOneMap k P c (squareZeroFiberExtClass W x)
      = naiveCotangentExtOneTowerMap k P (Localization S)
          (squareZeroFiberExtClass W (localizationFiberPoint F x)) := by
  set y := localizationFiberPoint F x
  set eX := fiberSquareZeroEquiv W x
  set eY := fiberSquareZeroEquiv W y
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
      F.localizationMap x.1 (algebraMap (TrivSqZeroExt k W.obj) x.1.left.fiber a)
        = algebraMap (TrivSqZeroExt k W.obj) y.1.left.fiber a := by
    intro a
    have h₁ : algebraMap (TrivSqZeroExt k W.obj) x.1.left.fiber a
        = algebraMap ((x.1.left.base : Type w)) x.1.left.fiber (eX.symm a) := by
      conv_lhs => rw [← eX.apply_symm_apply a]
      exact algebraMap_algebraOfBaseEquiv x.1.left.fiber eX (eX.symm a)
    have h₂ : algebraMap (TrivSqZeroExt k W.obj) y.1.left.fiber a
        = algebraMap ((y.1.left.base : Type w)) y.1.left.fiber (eY.symm a) := by
      conv_lhs => rw [← eY.apply_symm_apply a]
      exact algebraMap_algebraOfBaseEquiv y.1.left.fiber eY (eY.symm a)
    rw [h₁, h₂, ← eqToHom_fiberSquareZeroEquiv_symm_localization W F x a]
    exact localizationMap_algebraMap F x.1 (eY.symm a)
  exact extClass_eq_towerMap_of_middleRingHom (V := W.obj)
    (reductionOfBaseEquiv (P := P) x.1.left.fiber eX
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX) hρX)
    (surjective_algebraMap_of_isPushout x.1.left.fiber (fiberAug_surjective x))
    (isFirstOrderReduction_reductionOfBaseEquiv x.1.left.fiber eX
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX) hρX)
    (mem_kerIdeal_smul_of_algebraMap_eq_zero x.1.left.fiber eX
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX) hρX (fiberAug_surjective x))
    (reductionOfBaseEquiv (P := Localization S) y.1.left.fiber eY
      (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY) hρY)
    (surjective_algebraMap_of_isPushout y.1.left.fiber (fiberAug_surjective y))
    (isFirstOrderReduction_reductionOfBaseEquiv y.1.left.fiber eY
      (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY) hρY)
    (mem_kerIdeal_smul_of_algebraMap_eq_zero y.1.left.fiber eY
      (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY) hρY (fiberAug_surjective y))
    c hc (F.localizationMap x.1) hgbase (localizationMap_reduction F x.1)

end Fibre

/-! ### The differential of the localization functor -/

section Tangent

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (P : Type w) [CommRing P] [Algebra k P] (S : Submonoid P)

/-- The image of a point of a fibre under the based functor of a localization datum is the
localized point. -/
public theorem fiberFunctor_obj_localizationFiberPoint
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (x : (ringDeformationProjection Λ k P).Fiber A) :
    (fiberFunctor F.functor A).obj x = localizationFiberPoint F x := rfl

/-- Let `k` be a field, `P` a finite type `k`-algebra and `S ⊆ P` a multiplicative subset such
that `Spec(P) → Spec(k)` is smooth at every point of `V(g)` for every `g ∈ S`. Then the
localization functor `𝓓_P ⟶ 𝓓_{S⁻¹P}` of **Stacks 0DYS**, given by any
`LocalizationFunctorData`, induces a bijection on tangent spaces.

The proof is the source's: the family of extension classes of **Stacks 0DY3** is a bijection of
each tangent space with a first Ext group of the naive cotangent complex, by
`Deformation.Examples.bijective_tangentExtClass`; the functor is compatible with those classes
through the two comparison maps of **Stacks 0GPV**, by
`Deformation.Examples.squareZeroFiberExtClass_localization`; the bijection of **Stacks 0DZ8**
is compatible with the same two maps, by
`Deformation.Examples.naiveCotangentExtOneMap_localizationCoefficientMap`; and restriction along
`P → S⁻¹P` is injective, by
`Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_isLocalization`. -/
@[stacks 0DZ9 "the tangent-space assertion: the functor of Stacks 0DYS induces an isomorphism \
on tangent spaces. Under the tag's own hypotheses: (1) is `Algebra.FiniteType k P` and (2) is \
`hsm`, smoothness of `Spec(P) → Spec(k)` at every point of `V(g)` for every `g` of `S`. \
Stated for an arbitrary functor datum of Stacks 0DYS, with no extra hypothesis on the datum"]
public theorem bijective_differential_localizationFunctorData
    [Algebra.FiniteType k P]
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (hsm : ∀ g ∈ S, ∀ q : PrimeSpectrum P, g ∈ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    Function.Bijective (differential (𝓕 := ringDeformationBasedCategory Λ k P)
      (𝓖 := ringDeformationBasedCategory Λ k (Localization S))
      isCofiberedInGroupoids_ringDeformationProjection
      isCofiberedInGroupoids_ringDeformationProjection F.functor) := by
  classical
  set W := FGModuleCat.of k k
  let ι : ((W.obj : Type w)) ≃ₗ[k] k := LinearEquiv.refl k k
  -- both sides have the same image under restriction along `P → S⁻¹P`
  have hEq : ∀ z, tangentExtClass (Λ := Λ) (P := Localization S) W
          (differential (𝓕 := ringDeformationBasedCategory Λ k P)
            (𝓖 := ringDeformationBasedCategory Λ k (Localization S))
            isCofiberedInGroupoids_ringDeformationProjection
            isCofiberedInGroupoids_ringDeformationProjection F.functor z)
        = localizationExtOne k P S hsm ι
          (tangentExtClass (Λ := Λ) (P := P) W z) := by
    intro z
    obtain ⟨x, hx⟩ := classOf_surjective (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection
      ((squareZeroExtensionArtinian Λ k).obj W) z
    subst hx
    refine injective_naiveCotangentExtOneTowerMap_isLocalization k P S (Localization S)
      (Localization S ⊗[k] W.obj) ?_
    have hstep : differential (𝓕 := ringDeformationBasedCategory Λ k P)
          (𝓖 := ringDeformationBasedCategory Λ k (Localization S))
          isCofiberedInGroupoids_ringDeformationProjection
          isCofiberedInGroupoids_ringDeformationProjection F.functor
          (classOf (ringDeformationBasedCategory Λ k P)
            isCofiberedInGroupoids_ringDeformationProjection x)
        = classOf (ringDeformationBasedCategory Λ k (Localization S))
          isCofiberedInGroupoids_ringDeformationProjection (localizationFiberPoint F x) :=
      mapIsomorphismClasses_classOf isCofiberedInGroupoids_ringDeformationProjection
        isCofiberedInGroupoids_ringDeformationProjection F.functor x
    refine (congrArg (fun t => naiveCotangentExtOneTowerMap k P (Localization S)
      (tangentExtClass (Λ := Λ) (P := Localization S) W t)) hstep).trans ?_
    refine (congrArg (fun t => naiveCotangentExtOneTowerMap k P (Localization S) t)
      (tangentExtClass_classOf (Λ := Λ) (P := Localization S) W
        (localizationFiberPoint F x))).trans ?_
    refine ((squareZeroFiberExtClass_localization W F
      (localizationCoefficientMap k P S ι) (localizationCoefficientMap_tmul k P S ι)
      x).symm).trans ?_
    refine (congrArg (fun t => naiveCotangentExtOneMap k P
      (localizationCoefficientMap k P S ι) t)
      (tangentExtClass_classOf (Λ := Λ) (P := P) W x).symm).trans ?_
    exact naiveCotangentExtOneMap_localizationCoefficientMap k P S hsm ι _
  exact (Function.Bijective.of_comp_iff'
    (bijective_tangentExtClass (Λ := Λ) (P := Localization S) W) _).mp
    (bijective_of_forall_eq ((bijective_localizationExtOne k P S hsm ι).comp
      (bijective_tangentExtClass (Λ := Λ) (P := P) W)) hEq)

/-- Under the hypotheses of `Deformation.Examples.bijective_differential_localizationFunctorData`,
the canonical localization functor `Deformation.Examples.localizationFunctor`, the functor datum
built in the proof of **Stacks 0DYS**, induces a bijection on tangent spaces. -/
@[stacks 0DZ9 "the tangent-space assertion: the functor induces an isomorphism on tangent \
spaces, at the canonical localization functor \
`Deformation.Examples.localizationFunctor` of Stacks 0DYS. Under the tag's own hypotheses"]
public theorem bijective_differential_localizationFunctor [Algebra.FiniteType k P]
    (hsm : ∀ g ∈ S, ∀ q : PrimeSpectrum P, g ∈ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    Function.Bijective (differential (𝓕 := ringDeformationBasedCategory Λ k P)
      (𝓖 := ringDeformationBasedCategory Λ k (Localization S))
      isCofiberedInGroupoids_ringDeformationProjection
      isCofiberedInGroupoids_ringDeformationProjection
      (localizationFunctor (Λ := Λ) (k := k) S).functor) :=
  bijective_differential_localizationFunctorData P S
    (localizationFunctor (Λ := Λ) (k := k) S) hsm

end Tangent

end Deformation.Examples

end
