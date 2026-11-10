module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Examples.Geometric.Henselization
public import StacksFrontier.Deformation.Examples.Geometric.HenselizationTowerInjective
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationTangentSpace
public import StacksFrontier.RingTheory.Henselian.HenselizationExtOneCoefficients
public import StacksFrontier.RingTheory.Rig.HenselizationDescent

/-!
# The henselization functor on tangent spaces

Let `k` be a field, `P` a finite type `k`-algebra which is smooth over `k` outside the zero set
of an ideal `J ⊆ P`, and `(Pʰ, Jʰ)` the henselization of the pair `(P, J)`. Henselization of
deformations is a functor `𝓓_P ⟶ 𝓓_{Pʰ}` over `𝒞_Λ` (**Stacks 0DYT**). This file shows that its
differential on tangent spaces is bijective, which is the tangent-space conclusion of
**Stacks 0DZD** in the form the criterion of **Stacks 0DYP** consumes.

The argument is the one `Deformation.Examples.bijective_differential_localizationFunctorData`
runs for a localization. A deformation `x` of `P` over a base presented as `k ⊕ V` is a
square-zero extension of `P` by `P ⊗[k] V` (**Stacks 0GPT**), its henselization is one of `Pʰ`
by `Pʰ ⊗[k] V`, and the henselization map `Q → Qʰ` of middle rings is a `k`-algebra map
compatible with `P → Pʰ` and with the coefficient map. By the criterion of **Stacks 0GPV** the
two classes therefore have the same image in `Ext¹_P(NL_{P/k}, Pʰ ⊗[k] V)`; that is
`Deformation.Examples.squareZeroFiberExtClass_henselization`. The coefficient comparison into
that group is bijective, by the henselization half of **Stacks 0DZC** in the canonical form of
`Deformation.Examples.bijective_naiveCotangentExtOneMap_henselization`, and the restriction
along `P → Pʰ` is injective, by
`Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_henselization`. Those two facts and
the bijection of **Stacks 0DY3** on each tangent space force the differential to be bijective.

The file then reads the differential as the bijection of isomorphism classes of square-zero
extensions that **Stacks 0DZC** asserts at `N = P`, and identifies the two: the tangent space
of `𝓓_P` is the set of isomorphism classes of square-zero extensions of `P` by `P`, that of
`𝓓_{Pʰ}` the set of isomorphism classes of square-zero extensions of `Pʰ` by `Pʰ ⊗_P P`, and
the differential satisfies between them exactly the compatibility with the two comparison maps
of Stacks 0GPV that characterizes the bijection of Stacks 0DZC.

## Main definitions

* `Deformation.Examples.tensorCoefficientMap`: the `P`-linear coefficient map
  `P ⊗[k] V → Bh ⊗[k] V` of a `k`-algebra `P → Bh`, which on `p ⊗ v` is
  `(algebraMap p) ⊗ v`.
* `Deformation.Examples.squareZeroClassesEquivOfBijective`: the isomorphism classes of
  square-zero extensions of `A` by `N` as a receptacle, through **Stacks 0GPT**.
* `Deformation.Examples.tensorRankOneBaseChangeEquiv`: for a rank-one `V`, the `Pʰ`-linear
  equivalence `Pʰ ⊗[k] V ≃ Pʰ ⊗_P P` between the coefficients of the tangent space and the
  coefficients Stacks 0DZC uses.
* `Deformation.Examples.henselizationTangentClassesEquiv`: the differential of the henselization
  functor, read as a bijection of isomorphism classes of square-zero extensions of `P` by `P`
  with those of `Pʰ` by `Pʰ ⊗_P P`.

## Main results

* `Deformation.Examples.bijective_naiveCotangentExtOneMap_tensorCoefficientMap`: for the
  henselization of the pair `(P, J)` the induced map
  `Ext¹_P(NL_{P/k}, P ⊗[k] V) → Ext¹_P(NL_{P/k}, Pʰ ⊗[k] V)` is bijective.
* `Deformation.Examples.squareZeroFiberExtClass_henselization`: the class of a deformation over
  `k ⊕ V` and the class of its henselization have the same image in
  `Ext¹_P(NL_{P/k}, Pʰ ⊗[k] V)`.
* `Deformation.Examples.bijective_differential_henselizationFunctorData`: **the tangent-space
  conclusion of Stacks 0DZD**, for the map *induced* by an arbitrary functor datum of
  Stacks 0DYT.
* `Deformation.Examples.bijective_differential_henselizationFunctor`: the same at the canonical
  henselization functor.
* `Deformation.Examples.naiveCotangentExtOneTowerMap_henselizationTangentClassesEquiv`: **the
  bijection of square-zero-extension classes of Stacks 0DZC at `N = P` is the differential of
  the functor of Stacks 0DYT** — the differential, read on isomorphism classes, satisfies the
  compatibility with the two comparison maps of Stacks 0GPV that characterizes that bijection.
* `Deformation.Examples.bijective_naiveCotangentExtOneTowerMap_henselization`: restriction along
  `P → Pʰ` is *bijective*, not merely injective, on `Ext¹(NL, Pʰ ⊗_P P)`.

## Implementation notes

Only *injectivity* of the restriction map of Stacks 0GPV along `P → Pʰ` is used for
bijectivity of the differential, where the completion analogue of Stacks 0DZ5 uses bijectivity
of both comparison maps. That is enough: the square says that the restriction of the image of a
tangent vector under the differential is the coefficient push of that vector, so a restriction
that is merely injective still determines the differential, and a coefficient push that is
bijective makes it bijective. Bijectivity of the restriction then *follows*, by
`Deformation.Examples.bijective_naiveCotangentExtOneTowerMap_henselization`: the differential
sits between the two comparison maps, so once it is bijective and the coefficient push is, the
restriction is too. No analogue of the tower half of Stacks 0DZ4 — that is, of Stacks 0D08
composed with Stacks 0GPY — is needed anywhere.

**Why the receptacle is phrased the way it is.** Definitional unfolding of
`Stacks.Deformation.squareZeroAlgebraExtensionClassesEquivExtOne` to the point of projecting
out one of its fields exhausts the recursion budget, at every concrete coefficient module; this
is the same obstacle that forced
`Stacks.Deformation.extOneCokernelHenselizationBaseChangeEquiv` to be marked `irreducible`. So
`Deformation.Examples.squareZeroClassesEquivOfBijective` takes the bijection onto the extension
group as a parameter, is stated with the algebra and the coefficient module abstract, is marked
`irreducible` after the one lemma that computes it, and every statement below is phrased in
terms of it rather than of a composite of its own. The same is done for
`Deformation.Examples.henselizationTangentClassesEquiv`. For the same reason the differential
is given a name, `Deformation.Examples.henselizationTangentMap`, whose type presents both
tangent spaces as values of `Deformation.associatedTangentSpaceSetFunctor` — the presentation
`Deformation.Examples.tangentExtClass` uses — so that the definitional equality with
`Deformation.differential` is checked once, in
`Deformation.Examples.differential_eq_henselizationTangentMap`, and never again.

The coefficient map is built from
`TensorProduct.AlgebraTensorModule.cancelBaseChange`: the coefficient comparison of
Stacks 0DZC is stated at the coefficients `Bh ⊗_P N`, whereas a first-order deformation over
`k ⊕ V` produces `P ⊗[k] V` downstairs and `Bh ⊗[k] V` upstairs, and at `N = P ⊗[k] V` the two
differ by exactly that cancellation. No rank-one hypothesis on `V` is needed for this, unlike
the localization and completion analogues, whose comparison maps are stated at a localized or
completed module rather than a base change.

## References

* [Stacks Project, Tag 0DZD](https://stacks.math.columbia.edu/tag/0DZD)
* [Stacks Project, Tag 0DZC](https://stacks.math.columbia.edu/tag/0DZC)
* [Stacks Project, Tag 0DYT](https://stacks.math.columbia.edu/tag/0DYT)
* [Stacks Project, Tag 0DY3](https://stacks.math.columbia.edu/tag/0DY3)
* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
-/

@[expose] public section

open CategoryTheory Stacks.Deformation TrivSqZeroExt
open scoped TensorProduct

universe u v w

namespace Deformation.Examples

attribute [local instance 100] henselizationAlgebra

/-- The henselization of a pair of `R`-algebras is an `R`-algebra over the ring, for the
`k`-algebra structure of `Deformation.Examples.henselizationAlgebra`. -/
local instance isScalarTower_henselizationAlgebra {R A : Type w} [CommRing R] [CommRing A]
    [Algebra R A] (I : Ideal A) : IsScalarTower R A (henselization A I : Type w) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-! ### The coefficient map of a base change -/

section Coefficients

variable (k P : Type w) [Field k] [CommRing P] [Algebra k P]
  (Bh : Type w) [CommRing Bh] [Algebra k Bh] [Algebra P Bh] [IsScalarTower k P Bh]
  {V : Type w} [AddCommGroup V] [Module k V]

/-- **The coefficient map of a base change at tensor coefficients**: the `P`-linear map
`P ⊗[k] V → Bh ⊗[k] V` pushing the left tensor factor along `P → Bh`. It is the canonical map
`N → Bh ⊗_P N` at `N = P ⊗[k] V`, read through the cancellation
`Bh ⊗_P (P ⊗[k] V) ≃ Bh ⊗[k] V`. -/
public noncomputable def tensorCoefficientMap : P ⊗[k] V →ₗ[P] Bh ⊗[k] V :=
  (((TensorProduct.AlgebraTensorModule.cancelBaseChange k P Bh Bh V :
        Bh ⊗[P] (P ⊗[k] V) ≃ₗ[Bh] Bh ⊗[k] V) :
      Bh ⊗[P] (P ⊗[k] V) →ₗ[Bh] Bh ⊗[k] V).restrictScalars P).comp
    (TensorProduct.mk P Bh (P ⊗[k] V) 1)

/-- The coefficient map pushes the left tensor factor along `P → Bh`. -/
public theorem tensorCoefficientMap_tmul (p : P) (v : V) :
    tensorCoefficientMap k P Bh (p ⊗ₜ[k] v) = algebraMap P Bh p ⊗ₜ[k] v := by
  change (p • (1 : Bh)) ⊗ₜ[k] v = _
  rw [← Algebra.algebraMap_eq_smul_one]

/-- **The coefficient comparison of Stacks 0DZC at tensor coefficients is bijective.** For a
finite type `k`-algebra `P` smooth over `k` outside the zero set of `J` and the henselization
`(Pʰ, Jʰ)` of the pair `(P, J)`, the map
`Ext¹_P(NL_{P/k}, P ⊗[k] V) → Ext¹_P(NL_{P/k}, Pʰ ⊗[k] V)` induced by the coefficient map is
bijective.

It is `Deformation.Examples.bijective_naiveCotangentExtOneMap_henselization` at the
coefficients `N = P ⊗[k] V`, composed with the bijection induced by the cancellation
`Pʰ ⊗_P (P ⊗[k] V) ≃ Pʰ ⊗[k] V`. -/
public theorem bijective_naiveCotangentExtOneMap_tensorCoefficientMap
    [Algebra.FiniteType k P] (J : Ideal P)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (hhens : HenselianPair Bh (J.map (algebraMap P Bh)))
    (huniv : ∀ (C : Type w) (_ : CommRing C) (JC : Ideal C), HenselianPair C JC →
      ∀ f : P →+* C, J ≤ JC.comap f →
        ∃! g : Bh →+* C, g.comp (algebraMap P Bh) = f ∧
          J.map (algebraMap P Bh) ≤ JC.comap g) :
    Function.Bijective (naiveCotangentExtOneMap k P
      (tensorCoefficientMap k P Bh (V := V))) := by
  have hmk := bijective_naiveCotangentExtOneMap_henselization k P (P ⊗[k] V) Bh J hsm hhens huniv
  have hcancel : Function.Bijective (naiveCotangentExtOneMap k P
      (((TensorProduct.AlgebraTensorModule.cancelBaseChange k P Bh Bh V :
            Bh ⊗[P] (P ⊗[k] V) ≃ₗ[Bh] Bh ⊗[k] V) :
          Bh ⊗[P] (P ⊗[k] V) →ₗ[Bh] Bh ⊗[k] V).restrictScalars P)) :=
    bijective_naiveCotangentExtOneMap_of_inverse k P _
      ((((TensorProduct.AlgebraTensorModule.cancelBaseChange k P Bh Bh V).symm :
          Bh ⊗[k] V ≃ₗ[Bh] Bh ⊗[P] (P ⊗[k] V)) :
        Bh ⊗[k] V →ₗ[Bh] Bh ⊗[P] (P ⊗[k] V)).restrictScalars P)
      (fun m => (TensorProduct.AlgebraTensorModule.cancelBaseChange k P Bh Bh
        V).symm_apply_apply m)
      (fun n => (TensorProduct.AlgebraTensorModule.cancelBaseChange k P Bh Bh
        V).apply_symm_apply n)
  exact bijective_of_forall_eq (hcancel.comp hmk) fun x =>
    naiveCotangentExtOneMap_comp k P (TensorProduct.mk P Bh (P ⊗[k] V) 1) _ x

end Coefficients

/-! ### The canonical map from a deformation to its henselization -/

section Fibre

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P] {J : Ideal P}
  {V : Type w} [AddCommGroup V] [Module k V]

/-- The right `k`-module structure on `V`, given by letting `kᵐᵒᵖ` act through
`MulOpposite.unop`. -/
local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The left and right actions of `k` on `V` agree. -/
local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

/-- The structure map of the transported algebra on `Q` is the original one, read through the
inverse of the presentation of the base. -/
private theorem algebraMap_eq_algebraMap_symm {R : Type w} [CommRing R] (Q : Type w)
    [CommRing Q] [Algebra R Q] (e : R ≃+* TrivSqZeroExt k V) (a : TrivSqZeroExt k V) :
    letI := algebraOfBaseEquiv Q e
    algebraMap (TrivSqZeroExt k V) Q a = algebraMap R Q (e.symm a) := by
  let := algebraOfBaseEquiv Q e
  conv_lhs => rw [← e.apply_symm_apply a]
  exact algebraMap_algebraOfBaseEquiv Q e (e.symm a)

/-- **The henselization map of a deformation is a map of algebras over the Artinian base.** This
is the `base_comm` clause of the recorded data of **Stacks 0DYT**, read through the
identification of the base of the henselized deformation with the base of the deformation. -/
public theorem henselizationMap_algebraMap
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (a : ((F.functor.obj X).left.base : Type w)) :
    F.henselizationMap X
        (algebraMap ((X.left.base : Type w)) X.left.fiber
          ((eqToHom (F.functor.w_obj X)).hom a))
      = algebraMap (((F.functor.obj X).left.base : Type w)) (F.functor.obj X).left.fiber a := by
  rw [F.base_comm X ((eqToHom (F.functor.w_obj X)).hom a)]
  exact congrArg _ (cast_hom_eqToHom_of_eq (F.functor.w_obj X) a)

variable {A : ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- The image of a point of a fibre of the deformation category of `P` under a henselization
functor: a point of the fibre of the deformation category of `Pʰ` over the same base. -/
public def henselizationFiberPoint
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (x : (ringDeformationProjection Λ k P).Fiber A) :
    (ringDeformationProjection Λ k (henselization P J : Type w)).Fiber A :=
  ⟨F.functor.obj x.1, (F.functor.w_obj x.1).trans x.2⟩

/-- The two canonical presentations of the base of a point of a fibre over `k ⊕ V` and of its
henselization agree through the identification of the two bases. -/
public theorem fiberSquareZeroEquiv_henselizationFiberPoint (W : FGModuleCat.{w} k)
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (a : (((F.functor.obj x.1).left.base) : Type w)) :
    fiberSquareZeroEquiv W x ((eqToHom (F.functor.w_obj x.1)).hom a)
      = fiberSquareZeroEquiv W (henselizationFiberPoint F x) a := by
  have h₁ : (eqToHom (F.functor.w_obj x.1)).hom a
      = ringEquivOfEq (F.functor.w_obj x.1) a := hom_eqToHom_apply _ a
  exact (congrArg (fun z => fiberSquareZeroEquiv W x z) h₁).trans
    (ringEquivOfEq_trans_apply (F.functor.w_obj x.1) x.2 a)

/-- The canonical presentations of the two bases carry the same element of `k ⊕ V` to elements
matched by the identification of the bases. -/
public theorem eqToHom_fiberSquareZeroEquiv_symm_henselization (W : FGModuleCat.{w} k)
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (a : TrivSqZeroExt k W.obj) :
    (eqToHom (F.functor.w_obj x.1)).hom
        ((fiberSquareZeroEquiv W (henselizationFiberPoint F x)).symm a)
      = (fiberSquareZeroEquiv W x).symm a :=
  (fiberSquareZeroEquiv W x).injective <|
    ((fiberSquareZeroEquiv_henselizationFiberPoint W F x
      ((fiberSquareZeroEquiv W (henselizationFiberPoint F x)).symm a)).trans
    ((fiberSquareZeroEquiv W (henselizationFiberPoint F x)).apply_symm_apply a)).trans
    ((fiberSquareZeroEquiv W x).apply_symm_apply a).symm

/-- **The class of a deformation and the class of its henselization agree through the two
comparison maps of Stacks 0GPV.** For a point `x` of the fibre of the deformation category of
`P` over the square-zero base `k ⊕ V`, the class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)` of `x` and the
class in `Ext¹_{Pʰ}(NL_{Pʰ/k}, Pʰ ⊗[k] V)` of its henselization have the same image in
`Ext¹_P(NL_{P/k}, Pʰ ⊗[k] V)`.

The map of middle rings is the henselization map `Q → Qʰ` recorded by the datum, which is a map
over the Artinian base by `Deformation.Examples.henselizationMap_algebraMap` and compatible with
the two reductions by the `specialFiber_comm` clause. -/
public theorem squareZeroFiberExtClass_henselization (W : FGModuleCat.{w} k)
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (c : P ⊗[k] W.obj →ₗ[P] (henselization P J : Type w) ⊗[k] W.obj)
    (hc : ∀ (p : P) (v : W.obj),
      c (p ⊗ₜ[k] v) = algebraMap P (henselization P J : Type w) p ⊗ₜ[k] v)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W)) :
    naiveCotangentExtOneMap k P c (squareZeroFiberExtClass W x)
      = naiveCotangentExtOneTowerMap k P (henselization P J : Type w)
          (squareZeroFiberExtClass W (henselizationFiberPoint F x)) := by
  set y := henselizationFiberPoint F x
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
      F.henselizationMap x.1 (algebraMap (TrivSqZeroExt k W.obj) x.1.left.fiber a)
        = algebraMap (TrivSqZeroExt k W.obj) y.1.left.fiber a := by
    intro a
    rw [algebraMap_eq_algebraMap_symm x.1.left.fiber eX a,
      algebraMap_eq_algebraMap_symm y.1.left.fiber eY a,
      ← eqToHom_fiberSquareZeroEquiv_symm_henselization W F x a]
    exact henselizationMap_algebraMap F x.1 (eY.symm a)
  exact extClass_eq_towerMap_of_middleRingHom (V := W.obj)
    (reductionOfBaseEquiv (P := P) x.1.left.fiber eX
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX) hρX)
    (surjective_algebraMap_of_isPushout x.1.left.fiber (fiberAug_surjective x))
    (isFirstOrderReduction_reductionOfBaseEquiv x.1.left.fiber eX
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX) hρX)
    (mem_kerIdeal_smul_of_algebraMap_eq_zero x.1.left.fiber eX
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber eX) hρX (fiberAug_surjective x))
    (reductionOfBaseEquiv (P := (henselization P J : Type w)) y.1.left.fiber eY
      (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY) hρY)
    (surjective_algebraMap_of_isPushout y.1.left.fiber (fiberAug_surjective y))
    (isFirstOrderReduction_reductionOfBaseEquiv y.1.left.fiber eY
      (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY) hρY)
    (mem_kerIdeal_smul_of_algebraMap_eq_zero y.1.left.fiber eY
      (algebraMap_algebraOfBaseEquiv y.1.left.fiber eY) hρY (fiberAug_surjective y))
    c hc (F.henselizationMap x.1) hgbase (F.specialFiber_comm x.1)

end Fibre

/-! ### The differential of the henselization functor -/

section Tangent

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)

/-- A map whose composite with an injection agrees with a bijection is itself a bijection. -/
private theorem bijective_of_injective_comp_eq {α β γ : Type*} {f : α → β} {Φ : β → γ}
    {Ψ : α → γ} (hΦ : Function.Injective Φ) (hΨ : Function.Bijective Ψ)
    (h : ∀ a, Φ (f a) = Ψ a) : Function.Bijective f := by
  refine ⟨fun a₁ a₂ ha => hΨ.1 ?_, fun b => ?_⟩
  · rw [← h, ← h, ha]
  · obtain ⟨a, ha⟩ := hΨ.2 (Φ b)
    exact ⟨a, hΦ ((h a).trans ha)⟩

/-- The image of a point of a fibre under the based functor of a henselization datum is the
henselized point. -/
public theorem fiberFunctor_obj_henselizationFiberPoint
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (x : (ringDeformationProjection Λ k P).Fiber A) :
    (fiberFunctor F.functor A).obj x = henselizationFiberPoint F x := rfl

/-- **The map induced by a henselization functor on isomorphism classes of deformations over
`k ⊕ V`, read through the two comparison maps of Stacks 0GPV.** For an isomorphism class `z` of
deformations of `P` over `k ⊕ V`, the class in `Ext¹_{Pʰ}(NL_{Pʰ/k}, Pʰ ⊗[k] V)` of its image
restricts along `P → Pʰ` to the class of `z` pushed along the coefficient map
`P ⊗[k] V → Pʰ ⊗[k] V`.

This is `Deformation.Examples.squareZeroFiberExtClass_henselization` read on isomorphism
classes: the induced map carries the class of a point of the fibre to the class of its
henselization, by `Deformation.mapIsomorphismClasses_classOf`. It carries no hypothesis beyond
the functor datum — the smoothness hypothesis of Stacks 0DZD is used only to make the two
comparison maps bijective, not to make this square commute. At `V = k` the induced map is
`Deformation.differential`. -/
public theorem naiveCotangentExtOneTowerMap_tangentExtClass_mapIsomorphismClasses
    (W : FGModuleCat.{w} k)
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (z : (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection).obj W) :
    naiveCotangentExtOneTowerMap k P (henselization P J : Type w)
        (tangentExtClass (Λ := Λ) (P := (henselization P J : Type w)) W
          (mapIsomorphismClasses isCofiberedInGroupoids_ringDeformationProjection
            isCofiberedInGroupoids_ringDeformationProjection F.functor
            ((squareZeroExtensionArtinian Λ k).obj W) z))
      = naiveCotangentExtOneMap k P
          (tensorCoefficientMap k P (henselization P J : Type w) (V := W.obj))
          (tangentExtClass (Λ := Λ) (P := P) W z) := by
  classical
  obtain ⟨x, hx⟩ := classOf_surjective (ringDeformationBasedCategory Λ k P)
    isCofiberedInGroupoids_ringDeformationProjection
    ((squareZeroExtensionArtinian Λ k).obj W) z
  subst hx
  have hstep : mapIsomorphismClasses isCofiberedInGroupoids_ringDeformationProjection
        isCofiberedInGroupoids_ringDeformationProjection F.functor
        ((squareZeroExtensionArtinian Λ k).obj W)
        (classOf (ringDeformationBasedCategory Λ k P)
          isCofiberedInGroupoids_ringDeformationProjection x)
      = classOf (ringDeformationBasedCategory Λ k (henselization P J : Type w))
        isCofiberedInGroupoids_ringDeformationProjection (henselizationFiberPoint F x) :=
    mapIsomorphismClasses_classOf isCofiberedInGroupoids_ringDeformationProjection
      isCofiberedInGroupoids_ringDeformationProjection F.functor x
  have e₁ := tangentExtClass_classOf (Λ := Λ) (P := (henselization P J : Type w)) W
    (henselizationFiberPoint F x)
  have e₂ := tangentExtClass_classOf (Λ := Λ) (P := P) W x
  refine (congrArg (fun t => naiveCotangentExtOneTowerMap k P (henselization P J : Type w)
    (tangentExtClass (Λ := Λ) (P := (henselization P J : Type w)) W t)) hstep).trans ?_
  refine (congrArg (fun t => naiveCotangentExtOneTowerMap k P
    (henselization P J : Type w) t) e₁).trans ?_
  refine ((squareZeroFiberExtClass_henselization W F
    (tensorCoefficientMap k P (henselization P J : Type w) (V := W.obj))
    (tensorCoefficientMap_tmul k P (henselization P J : Type w)) x).symm).trans ?_
  exact congrArg (fun t => naiveCotangentExtOneMap k P
    (tensorCoefficientMap k P (henselization P J : Type w) (V := W.obj)) t) e₂.symm

/-- **Stacks 0DZD, the tangent-space conclusion, for the map induced by the functor.** Let `k`
be a field, `P` a finite type `k`-algebra and `J ⊆ P` an ideal such that `Spec(P) → Spec(k)` is
smooth on the complement of `V(J)`. The henselization functor `𝓓_P ⟶ 𝓓_{Pʰ}` of **Stacks 0DYT**
induces a bijection on tangent spaces.

The proof is the source's: the family of extension classes of **Stacks 0DY3** is a bijection of
each tangent space with a first Ext group of the naive cotangent complex, by
`Deformation.Examples.bijective_tangentExtClass`; the functor is compatible with those classes
through the two comparison maps of **Stacks 0GPV**, by
`Deformation.Examples.squareZeroFiberExtClass_henselization`; the coefficient comparison is
bijective by the henselization half of **Stacks 0DZC**, in the form
`Deformation.Examples.bijective_naiveCotangentExtOneMap_tensorCoefficientMap`; and restriction
along `P → Pʰ` is injective, by
`Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_henselization`. -/
@[stacks 0DZD "the second conclusion, the tangent-space assertion, for the map INDUCED by the \
functor of Stacks 0DYT: `Deformation.differential` of that functor is bijective, the tangent \
spaces being those of Stacks 06IH carried by the two deformation categories. Under the tag's \
own hypotheses and no others: (1) is `Algebra.FiniteType k P` and (2) is `hsm`, smoothness of \
`Spec(P) -> Spec(k)` at every prime outside `V(J)`. Stated for an arbitrary functor datum of \
Stacks 0DYT, with no extra hypothesis on the datum. The inputs are the classification of \
Stacks 0GPT through Stacks 0DY3, the comparison criterion of Stacks 0GPV, the coefficient half \
of Stacks 0DZC and injectivity of restriction along `P -> P^h`"]
public theorem bijective_differential_henselizationFunctorData [Algebra.FiniteType k P]
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    Function.Bijective (differential (𝓕 := ringDeformationBasedCategory Λ k P)
      (𝓖 := ringDeformationBasedCategory Λ k (henselization P J : Type w))
      isCofiberedInGroupoids_ringDeformationProjection
      isCofiberedInGroupoids_ringDeformationProjection F.functor) := by
  classical
  set W := FGModuleCat.of k k
  have hinj : Function.Injective
      (naiveCotangentExtOneTowerMap k P (henselization P J : Type w)
        (N := (henselization P J : Type w) ⊗[k] W.obj)) :=
    injective_naiveCotangentExtOneTowerMap_henselization k P J (henselization P J : Type w)
      (henselianPair_henselization P J) (henselization_universalProperty P J)
      ((henselization P J : Type w) ⊗[k] W.obj)
  have hco : Function.Bijective (naiveCotangentExtOneMap k P
      (tensorCoefficientMap k P (henselization P J : Type w) (V := W.obj))) :=
    bijective_naiveCotangentExtOneMap_tensorCoefficientMap k P
      (henselization P J : Type w) J hsm
      (henselianPair_henselization P J) (henselization_universalProperty P J)
  refine bijective_of_injective_comp_eq
    (Φ := fun z => naiveCotangentExtOneTowerMap k P (henselization P J : Type w)
      (tangentExtClass (Λ := Λ) (P := (henselization P J : Type w)) W z))
    (Ψ := fun z => naiveCotangentExtOneMap k P
      (tensorCoefficientMap k P (henselization P J : Type w) (V := W.obj))
      (tangentExtClass (Λ := Λ) (P := P) W z))
    (hinj.comp (bijective_tangentExtClass (Λ := Λ)
      (P := (henselization P J : Type w)) W).injective)
    (hco.comp (bijective_tangentExtClass (Λ := Λ) (P := P) W)) fun z =>
    naiveCotangentExtOneTowerMap_tangentExtClass_mapIsomorphismClasses P J W F z

/-- **Stacks 0DZD, the tangent-space conclusion, at the canonical henselization functor.** This
is `Deformation.Examples.bijective_differential_henselizationFunctorData` specialized to
`Deformation.Examples.henselizationFunctor`, the functor datum built in the proof of
**Stacks 0DYT**. -/
@[stacks 0DZD "the second conclusion, the tangent-space assertion for the map induced by the \
functor, at the canonical henselization functor \
`Deformation.Examples.henselizationFunctor` of Stacks 0DYT. Under the tag's own hypotheses and \
no others"]
public theorem bijective_differential_henselizationFunctor [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    Function.Bijective (differential (𝓕 := ringDeformationBasedCategory Λ k P)
      (𝓖 := ringDeformationBasedCategory Λ k (henselization P J : Type w))
      isCofiberedInGroupoids_ringDeformationProjection
      isCofiberedInGroupoids_ringDeformationProjection
      (henselizationFunctor (Λ := Λ) (k := k) J).functor) :=
  bijective_differential_henselizationFunctorData P J
    (henselizationFunctor (Λ := Λ) (k := k) J) hsm

end Tangent

/-! ### Isomorphism classes of square-zero extensions as a receptacle -/

section Receptacle

/-- **A bijection onto `Ext¹_A(NL_{A/k}, N)` is a bijection onto the isomorphism classes of
square-zero extensions of `A` by `N`.** This is the classification of **Stacks 0GPT** read as a
receptacle: a set already known to be in bijection with the extension group is in bijection with
the isomorphism classes themselves.

Stated with the algebra and the coefficient module abstract. Every consumer below is phrased in
terms of this definition rather than of a composite of its own, because a definitional-equality
check that has to project a field out of
`Stacks.Deformation.squareZeroAlgebraExtensionClassesEquivExtOne` exhausts the recursion budget
— the same obstacle the implementation notes of
`Stacks.Deformation.extOneCokernelHenselizationBaseChangeEquiv` record. -/
public noncomputable def squareZeroClassesEquivOfBijective (k A : Type w) [CommRing k]
    [CommRing A] [Algebra k A] {N : Type w} [AddCommGroup N] [Module A N] {α : Type v}
    (f : α → naiveCotangentExtOne k A N) (hf : Function.Bijective f) :
    α ≃ SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{w, w, w, w, w}
      (algebraExtensionProblem k A N) :=
  Equiv.ofBijective (fun a ↦ (squareZeroAlgebraExtensionClassesEquivExtOne k A N).symm (f a))
    ((squareZeroAlgebraExtensionClassesEquivExtOne k A N).symm.bijective.comp hf)

/-- The class of the square-zero extension attached to an element is that element's image. -/
public theorem squareZeroAlgebraExtensionClassesEquivExtOne_squareZeroClassesEquivOfBijective
    (k A : Type w) [CommRing k] [CommRing A] [Algebra k A] {N : Type w} [AddCommGroup N]
    [Module A N] {α : Type v} (f : α → naiveCotangentExtOne k A N)
    (hf : Function.Bijective f) (a : α) :
    squareZeroAlgebraExtensionClassesEquivExtOne k A N
        (squareZeroClassesEquivOfBijective k A f hf a) = f a :=
  (squareZeroAlgebraExtensionClassesEquivExtOne k A N).apply_symm_apply (f a)

-- Marked `irreducible` from here on: unfolding it reaches the field projections of
-- `Stacks.Deformation.squareZeroAlgebraExtensionClassesEquivExtOne`, and a
-- definitional-equality check which does that at a concrete coefficient module exhausts the
-- recursion budget.  Every consumer below uses it as a bijection, never as a formula.
attribute [irreducible] squareZeroClassesEquivOfBijective

/-- **A linear equivalence of coefficient modules induces a bijection on first extension
groups.** -/
public theorem bijective_naiveCotangentExtOneMap_linearEquiv (k A : Type w) [CommRing k]
    [CommRing A] [Algebra k A] {M N : Type w} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (c : M ≃ₗ[A] N) :
    Function.Bijective (naiveCotangentExtOneMap k A (c : M →ₗ[A] N)) :=
  bijective_naiveCotangentExtOneMap_of_inverse k A (c : M →ₗ[A] N) (c.symm : N →ₗ[A] M)
    (fun m ↦ c.symm_apply_apply m) fun n ↦ c.apply_symm_apply n

end Receptacle

/-! ### The rank-one coefficients of the tangent space, as a base change -/

section RankOneBaseChange

variable (k P Bh : Type w) [Field k] [CommRing P] [Algebra k P] [CommRing Bh] [Algebra k Bh]
  [Algebra P Bh] {V : Type w} [AddCommGroup V] [Module k V]

/-- **At rank-one coefficients, a tensor coefficient over `k` and a base change along `P → Pʰ`
agree.** For a one-dimensional `k`-vector space `V` presented as `k` by `ι`, both `Pʰ ⊗[k] V`
and `Pʰ ⊗_P P` are canonically `Pʰ`, so they are canonically `Pʰ`-linearly isomorphic. -/
public noncomputable def tensorRankOneBaseChangeEquiv (ι : V ≃ₗ[k] k) :
    Bh ⊗[k] V ≃ₗ[Bh] Bh ⊗[P] P :=
  (tensorRankOneTrivialization k Bh ι).trans
    (TensorProduct.AlgebraTensorModule.rid P Bh Bh).symm

variable [IsScalarTower k P Bh]

/-- **The two coefficient maps agree.** The coefficient map of the base change,
`Deformation.Examples.tensorCoefficientMap`, followed by the comparison of the two
presentations of the coefficients, is the canonical map `N → Pʰ ⊗_P N` at `N = P`, preceded by
the trivialisation of the rank-one tensor coefficient. -/
public theorem tensorRankOneBaseChangeEquiv_tensorCoefficientMap (ι : V ≃ₗ[k] k)
    (x : P ⊗[k] V) :
    tensorRankOneBaseChangeEquiv k P Bh ι (tensorCoefficientMap k P Bh x)
      = TensorProduct.mk P Bh P 1 (tensorRankOneTrivialization k P ι x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p v =>
      rw [tensorCoefficientMap_tmul]
      change (TensorProduct.AlgebraTensorModule.rid P Bh Bh).symm
          (tensorRankOneTrivialization k Bh ι (algebraMap P Bh p ⊗ₜ[k] v))
        = (1 : Bh) ⊗ₜ[P] tensorRankOneTrivialization k P ι (p ⊗ₜ[k] v)
      rw [tensorRankOneTrivialization_tmul, tensorRankOneTrivialization_tmul,
        TensorProduct.AlgebraTensorModule.rid_symm_apply]
      have h₁ : algebraMap P Bh (ι v • p) = ι v • algebraMap P Bh p := by
        rw [Algebra.smul_def (ι v) p, map_mul, ← IsScalarTower.algebraMap_apply k P Bh,
          Algebra.smul_def (ι v) (algebraMap P Bh p)]
      calc (ι v • algebraMap P Bh p) ⊗ₜ[P] (1 : P)
          = ((ι v • p) • (1 : Bh)) ⊗ₜ[P] (1 : P) := by
            rw [← Algebra.algebraMap_eq_smul_one, h₁]
        _ = (1 : Bh) ⊗ₜ[P] ((ι v • p) • (1 : P)) := TensorProduct.smul_tmul _ _ _
        _ = (1 : Bh) ⊗ₜ[P] (ι v • p) := by rw [smul_eq_mul, mul_one]

/-- The agreement of the two coefficient maps, read on first extension groups. -/
public theorem naiveCotangentExtOneMap_tensorRankOneBaseChangeEquiv (ι : V ≃ₗ[k] k)
    (ξ : naiveCotangentExtOne k P (P ⊗[k] V)) :
    naiveCotangentExtOneMap k P
        ((tensorRankOneBaseChangeEquiv k P Bh ι :
            Bh ⊗[k] V →ₗ[Bh] Bh ⊗[P] P).restrictScalars P)
        (naiveCotangentExtOneMap k P (tensorCoefficientMap k P Bh (V := V)) ξ)
      = naiveCotangentExtOneMap k P (TensorProduct.mk P Bh P 1)
          (naiveCotangentExtOneMap k P
            (tensorRankOneTrivialization k P ι : P ⊗[k] V →ₗ[P] P) ξ) := by
  rw [← naiveCotangentExtOneMap_comp, ← naiveCotangentExtOneMap_comp]
  exact congrArg (fun c ↦ naiveCotangentExtOneMap k P c ξ)
    (LinearMap.ext fun x ↦ tensorRankOneBaseChangeEquiv_tensorCoefficientMap k P Bh ι x)

/-- **The comparison square of Stacks 0GPV, carried from the coefficients `Pʰ ⊗[k] V` to the
coefficients `Pʰ ⊗_P P` of Stacks 0DZC.** If a class over `Pʰ` with coefficients `Pʰ ⊗[k] V`
restricts along `P → Pʰ` to the push of a class over `P` with coefficients `P ⊗[k] V`, then the
same holds after both are carried to the coefficients of **Stacks 0DZC**: `Pʰ ⊗_P P` above and,
below, the push along the canonical map `P → Pʰ ⊗_P P`.

The restriction map is natural in the coefficients by
`Stacks.Deformation.naiveCotangentExtOneTowerMap_map`, and the two coefficient maps agree by
`Deformation.Examples.naiveCotangentExtOneMap_tensorRankOneBaseChangeEquiv`. -/
public theorem naiveCotangentExtOneTowerMap_tensorRankOneBaseChangeEquiv (ι : V ≃ₗ[k] k)
    (ξ : naiveCotangentExtOne k Bh (Bh ⊗[k] V)) (η : naiveCotangentExtOne k P (P ⊗[k] V))
    (h : naiveCotangentExtOneTowerMap k P Bh ξ
      = naiveCotangentExtOneMap k P (tensorCoefficientMap k P Bh (V := V)) η) :
    naiveCotangentExtOneTowerMap k P Bh
        (naiveCotangentExtOneMap k Bh
          (tensorRankOneBaseChangeEquiv k P Bh ι : Bh ⊗[k] V →ₗ[Bh] Bh ⊗[P] P) ξ)
      = naiveCotangentExtOneMap k P (TensorProduct.mk P Bh P 1)
          (naiveCotangentExtOneMap k P
            (tensorRankOneTrivialization k P ι : P ⊗[k] V →ₗ[P] P) η) := by
  rw [naiveCotangentExtOneTowerMap_map, h,
    naiveCotangentExtOneMap_tensorRankOneBaseChangeEquiv]

end RankOneBaseChange

/-! ### The differential as the bijection of square-zero-extension classes of Stacks 0DZC -/

section Identification

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)

/-- **The differential of a henselization functor, on the value of the tangent-space set
functor at the rank-one module.** It is `Deformation.differential` of the functor of
**Stacks 0DYT**, by `Deformation.Examples.differential_eq_henselizationTangentMap`; the body is
written with `Deformation.mapIsomorphismClasses` so that the two tangent spaces are presented
as values of `Deformation.associatedTangentSpaceSetFunctor`, which is the presentation
`Deformation.Examples.tangentExtClass` uses. -/
public noncomputable def henselizationTangentMap
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J) :
    (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
        isCofiberedInGroupoids_ringDeformationProjection).obj (FGModuleCat.of k k) →
      (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k
          (henselization P J : Type w))
        isCofiberedInGroupoids_ringDeformationProjection).obj (FGModuleCat.of k k) :=
  mapIsomorphismClasses isCofiberedInGroupoids_ringDeformationProjection
    isCofiberedInGroupoids_ringDeformationProjection F.functor
    ((squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k k))

/-- The map above is the differential of **Stacks 06II** of the functor of **Stacks 0DYT**: the
square-zero extension of the rank-one module is the augmented dual numbers at which the
differential is taken. -/
public theorem differential_eq_henselizationTangentMap
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J) :
    differential (𝓕 := ringDeformationBasedCategory Λ k P)
        (𝓖 := ringDeformationBasedCategory Λ k (henselization P J : Type w))
        isCofiberedInGroupoids_ringDeformationProjection
        isCofiberedInGroupoids_ringDeformationProjection F.functor
      = henselizationTangentMap P J F := rfl

/-- **Stacks 0DZD, the tangent-space conclusion, for the map of
`Deformation.Examples.henselizationTangentMap`.** This is
`Deformation.Examples.bijective_differential_henselizationFunctorData` at that presentation of
the differential. -/
public theorem bijective_henselizationTangentMap [Algebra.FiniteType k P]
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    Function.Bijective (henselizationTangentMap (Λ := Λ) P J F) :=
  bijective_differential_henselizationFunctorData (Λ := Λ) P J F hsm

/-- **The comparison square of Stacks 0GPV for the differential of a henselization functor.**
This is
`Deformation.Examples.naiveCotangentExtOneTowerMap_tangentExtClass_mapIsomorphismClasses` at
the rank-one module. -/
public theorem naiveCotangentExtOneTowerMap_tangentExtClass_henselizationTangentMap
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (z : (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection).obj (FGModuleCat.of k k)) :
    naiveCotangentExtOneTowerMap k P (henselization P J : Type w)
        (tangentExtClass (Λ := Λ) (P := (henselization P J : Type w)) (FGModuleCat.of k k)
          (henselizationTangentMap (Λ := Λ) P J F z))
      = naiveCotangentExtOneMap k P
          (tensorCoefficientMap k P (henselization P J : Type w)
            (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj))
          (tangentExtClass (Λ := Λ) (P := P) (FGModuleCat.of k k) z) :=
  naiveCotangentExtOneTowerMap_tangentExtClass_mapIsomorphismClasses P J
    (FGModuleCat.of k k) F z

/-- **The differential of a henselization functor as a bijection of isomorphism classes of
square-zero extensions.** The tangent space of `𝓓_P` is the set of isomorphism classes of
square-zero extensions of `P` by `P`, and that of `𝓓_{Pʰ}` the set of isomorphism classes of
square-zero extensions of `Pʰ` by `Pʰ ⊗_P P` — by **Stacks 0DY3** and **Stacks 0GPT**, read at
the rank-one coefficient module of the tangent space through
`Deformation.Examples.squareZeroClassesEquivOfBijective`,
`Deformation.Examples.tensorRankOneTrivialization` and
`Deformation.Examples.tensorRankOneBaseChangeEquiv`. This is the differential of
**Stacks 0DYT** read through those two identifications.

It is the bijection asserted by the case `N = P` of **Stacks 0DZC**:
`Deformation.Examples.naiveCotangentExtOneTowerMap_henselizationTangentClassesEquiv` is the
compatibility with the two comparison maps of **Stacks 0GPV** that characterizes it. -/
public noncomputable def henselizationTangentClassesEquiv [Algebra.FiniteType k P]
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{w, w, w, w, w}
        (algebraExtensionProblem k P P) ≃
      SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{w, w, w, w, w}
        (algebraExtensionProblem k (henselization P J : Type w)
          ((henselization P J : Type w) ⊗[P] P)) :=
  (squareZeroClassesEquivOfBijective k P
      (fun z ↦ naiveCotangentExtOneMap k P
        (tensorRankOneTrivialization k P
            (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj) (LinearEquiv.refl k k) :
          P ⊗[k] ((FGModuleCat.of k k : FGModuleCat.{w} k).obj) →ₗ[P] P)
        (tangentExtClass (Λ := Λ) (P := P) (FGModuleCat.of k k) z))
      ((bijective_naiveCotangentExtOneMap_linearEquiv k P
          (tensorRankOneTrivialization k P
            (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj) (LinearEquiv.refl k k))).comp
        (bijective_tangentExtClass (Λ := Λ) (P := P) (FGModuleCat.of k k)))).symm.trans
    ((Equiv.ofBijective (henselizationTangentMap (Λ := Λ) P J F)
        (bijective_henselizationTangentMap (Λ := Λ) P J F hsm)).trans
      (squareZeroClassesEquivOfBijective k (henselization P J : Type w)
        (fun t ↦ naiveCotangentExtOneMap k (henselization P J : Type w)
          (tensorRankOneBaseChangeEquiv k P (henselization P J : Type w)
              (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj) (LinearEquiv.refl k k) :
            (henselization P J : Type w) ⊗[k] ((FGModuleCat.of k k : FGModuleCat.{w} k).obj)
              →ₗ[(henselization P J : Type w)] (henselization P J : Type w) ⊗[P] P)
          (tangentExtClass (Λ := Λ) (P := (henselization P J : Type w)) (FGModuleCat.of k k) t))
        ((bijective_naiveCotangentExtOneMap_linearEquiv k (henselization P J : Type w)
            (tensorRankOneBaseChangeEquiv k P (henselization P J : Type w)
              (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj)
              (LinearEquiv.refl k k))).comp
          (bijective_tangentExtClass (Λ := Λ) (P := (henselization P J : Type w))
            (FGModuleCat.of k k)))))

/-- The bijection of classes is the differential: on the class of a tangent vector it is the
class of the image of that vector under the differential. -/
public theorem henselizationTangentClassesEquiv_squareZeroClassesEquivOfBijective
    [Algebra.FiniteType k P]
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (z : (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection).obj (FGModuleCat.of k k)) :
    henselizationTangentClassesEquiv P J F hsm
        (squareZeroClassesEquivOfBijective k P
      (fun z ↦ naiveCotangentExtOneMap k P
        (tensorRankOneTrivialization k P
            (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj) (LinearEquiv.refl k k) :
          P ⊗[k] ((FGModuleCat.of k k : FGModuleCat.{w} k).obj) →ₗ[P] P)
        (tangentExtClass (Λ := Λ) (P := P) (FGModuleCat.of k k) z))
      ((bijective_naiveCotangentExtOneMap_linearEquiv k P
          (tensorRankOneTrivialization k P
            (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj) (LinearEquiv.refl k k))).comp
        (bijective_tangentExtClass (Λ := Λ) (P := P) (FGModuleCat.of k k))) z)
      = squareZeroClassesEquivOfBijective k (henselization P J : Type w)
        (fun t ↦ naiveCotangentExtOneMap k (henselization P J : Type w)
        (tensorRankOneBaseChangeEquiv k P (henselization P J : Type w)
          (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj) (LinearEquiv.refl k k) :
        (henselization P J : Type w) ⊗[k] ((FGModuleCat.of k k : FGModuleCat.{w} k).obj)
          →ₗ[(henselization P J : Type w)] (henselization P J : Type w) ⊗[P] P)
        (tangentExtClass (Λ := Λ) (P := (henselization P J : Type w)) (FGModuleCat.of k k) t))
      ((bijective_naiveCotangentExtOneMap_linearEquiv k (henselization P J : Type w)
        (tensorRankOneBaseChangeEquiv k P (henselization P J : Type w)
          (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj)
          (LinearEquiv.refl k k))).comp
        (bijective_tangentExtClass (Λ := Λ) (P := (henselization P J : Type w))
        (FGModuleCat.of k k)))
          (henselizationTangentMap (Λ := Λ) P J F z) := by
  simp only [henselizationTangentClassesEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.ofBijective_apply]

-- Marked `irreducible` from here on, for the reason
-- `Deformation.Examples.squareZeroClassesEquivOfBijective` is: the identification above is the
-- only thing a consumer needs, and a definitional-equality check which unfolds the composite
-- reaches the field projections of
-- `Stacks.Deformation.squareZeroAlgebraExtensionClassesEquivExtOne` and exhausts the recursion
-- budget.
attribute [irreducible] henselizationTangentClassesEquiv

/-- **Stacks 0DZD, the tangent-space conclusion: the bijection of square-zero-extension classes
of Stacks 0DZC at `N = P` IS the differential of the functor of Stacks 0DYT.** The differential,
read through Stacks 0DY3 and Stacks 0GPT as the bijection
`Deformation.Examples.henselizationTangentClassesEquiv` of the isomorphism classes of
square-zero extensions of `P` by `P` with those of `Pʰ` by `Pʰ ⊗_P P`, satisfies the
compatibility with the two comparison maps of **Stacks 0GPV** that Stacks 0DZC asserts of its
bijection: the class of `x` pushed along the canonical coefficient map `P → Pʰ ⊗_P P` is the
class of the image of `x` restricted along `P → Pʰ`.

Both maps of Stacks 0GPV are injective here — the coefficient push is bijective by the
coefficient half of Stacks 0DZC and the restriction is injective by
`Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_henselization` — so this
compatibility determines the bijection, and therefore identifies the differential with the
bijection of Stacks 0DZC in the canonical form of Stacks 0GPV.

The inputs are
`Deformation.Examples.naiveCotangentExtOneTowerMap_tangentExtClass_henselizationTangentMap`,
the criterion of Stacks 0GPV applied to the henselization map of a deformation;
`Deformation.Examples.naiveCotangentExtOneTowerMap_tensorRankOneBaseChangeEquiv`, which carries
that square from the coefficients `Pʰ ⊗[k] k` of the tangent space to the coefficients
`Pʰ ⊗_P P` of Stacks 0DZC; and the computation lemma of
`Deformation.Examples.squareZeroClassesEquivOfBijective`, which carries it through the
classification of Stacks 0GPT. -/
public theorem naiveCotangentExtOneTowerMap_henselizationTangentClassesEquiv
    [Algebra.FiniteType k P]
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (x : SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{w, w, w, w, w}
      (algebraExtensionProblem k P P)) :
    naiveCotangentExtOneTowerMap k P (henselization P J : Type w)
        (squareZeroAlgebraExtensionClassesEquivExtOne k (henselization P J : Type w)
          ((henselization P J : Type w) ⊗[P] P)
          (henselizationTangentClassesEquiv P J F hsm x))
      = naiveCotangentExtOneMap k P
          (TensorProduct.mk P (henselization P J : Type w) P 1)
          (squareZeroAlgebraExtensionClassesEquivExtOne k P P x) := by
  classical
  obtain ⟨z, rfl⟩ := (squareZeroClassesEquivOfBijective k P
      (fun z ↦ naiveCotangentExtOneMap k P
        (tensorRankOneTrivialization k P
            (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj) (LinearEquiv.refl k k) :
          P ⊗[k] ((FGModuleCat.of k k : FGModuleCat.{w} k).obj) →ₗ[P] P)
        (tangentExtClass (Λ := Λ) (P := P) (FGModuleCat.of k k) z))
      ((bijective_naiveCotangentExtOneMap_linearEquiv k P
          (tensorRankOneTrivialization k P
            (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj) (LinearEquiv.refl k k))).comp
        (bijective_tangentExtClass (Λ := Λ) (P := P) (FGModuleCat.of k k)))).surjective x
  refine (congrArg (fun u ↦ naiveCotangentExtOneTowerMap k P (henselization P J : Type w)
      (squareZeroAlgebraExtensionClassesEquivExtOne k (henselization P J : Type w)
        ((henselization P J : Type w) ⊗[P] P) u))
    (henselizationTangentClassesEquiv_squareZeroClassesEquivOfBijective P J F hsm z)).trans ?_
  rw [squareZeroAlgebraExtensionClassesEquivExtOne_squareZeroClassesEquivOfBijective,
    squareZeroAlgebraExtensionClassesEquivExtOne_squareZeroClassesEquivOfBijective]
  exact naiveCotangentExtOneTowerMap_tensorRankOneBaseChangeEquiv k P
    (henselization P J : Type w) (V := (FGModuleCat.of k k : FGModuleCat.{w} k).obj)
    (LinearEquiv.refl k k)
    (tangentExtClass (Λ := Λ) (P := (henselization P J : Type w)) (FGModuleCat.of k k)
      (henselizationTangentMap (Λ := Λ) P J F z))
    (tangentExtClass (Λ := Λ) (P := P) (FGModuleCat.of k k) z)
    (naiveCotangentExtOneTowerMap_tangentExtClass_henselizationTangentMap P J F z)

/-- **Restriction along a henselization is bijective on first-order extension classes at the
coefficients of Stacks 0DZC.** For a finite type `k`-algebra `P` smooth over `k` outside the
zero set of `J`, the restriction map
`Ext¹_{Pʰ}(NL_{Pʰ/k}, Pʰ ⊗_P P) → Ext¹_P(NL_{P/k}, Pʰ ⊗_P P)` of **Stacks 0GPV** is bijective,
and not merely injective as
`Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_henselization` has it.

It is bijective because the differential of a henselization functor is, by
`Deformation.Examples.bijective_differential_henselizationFunctorData`, and because the square
of `Deformation.Examples.naiveCotangentExtOneTowerMap_henselizationTangentClassesEquiv` puts
that differential between the restriction map and the coefficient comparison
`Ext¹_P(NL_{P/k}, P) → Ext¹_P(NL_{P/k}, Pʰ ⊗_P P)`, which is bijective by the coefficient half
of **Stacks 0DZC**. This is the henselization analogue of
`Deformation.Examples.bijective_naiveCotangentExtOneTowerMap_rankOne`; it does not go through
Stacks 0D08 and Stacks 0GPY. -/
public theorem bijective_naiveCotangentExtOneTowerMap_henselization
    [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    Function.Bijective (naiveCotangentExtOneTowerMap k P (henselization P J : Type w)
      (N := (henselization P J : Type w) ⊗[P] P)) := by
  classical
  obtain ⟨F⟩ := nonempty_henselizationFunctorData (Λ := k) (k := k) (P := P) J
  have hco : Function.Bijective (naiveCotangentExtOneMap k P
      (TensorProduct.mk P (henselization P J : Type w) P 1)) :=
    bijective_naiveCotangentExtOneMap_henselization k P P
      (henselization P J : Type w) J hsm
      (henselianPair_henselization P J) (henselization_universalProperty P J)
  have hleft : Function.Bijective
      (fun x ↦ squareZeroAlgebraExtensionClassesEquivExtOne k
        (henselization P J : Type w) ((henselization P J : Type w) ⊗[P] P)
        (henselizationTangentClassesEquiv (Λ := k) P J F hsm x)) :=
    (squareZeroAlgebraExtensionClassesEquivExtOne k (henselization P J : Type w)
      ((henselization P J : Type w) ⊗[P] P)).bijective.comp
      (henselizationTangentClassesEquiv (Λ := k) P J F hsm).bijective
  exact (Function.Bijective.of_comp_iff _ hleft).mp <| bijective_of_forall_eq
    (hco.comp (squareZeroAlgebraExtensionClassesEquivExtOne k P P).bijective)
    fun x ↦ naiveCotangentExtOneTowerMap_henselizationTangentClassesEquiv P J F hsm x

end Identification

end Deformation.Examples

end
