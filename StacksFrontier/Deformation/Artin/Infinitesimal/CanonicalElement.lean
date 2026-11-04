module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
public import StacksFrontier.RingTheory.Kaehler.Defs

/-!
# The canonical element of the tangent functor

Let `A` be a `Λ`-algebra and let `x` be an object of a category fibred in groupoids over the
big fppf site of `S`, lying over `Spec A`. The universal derivation `d : A → Ω_{A/Λ}` gives a
ring map

`A → A[Ω_{A/Λ}],  a ↦ (a, d a)`,

which is a section of the projection `A[Ω_{A/Λ}] → A`. Pulling `x` back along the
corresponding morphism of spectra produces a lift of `x` over `A[Ω_{A/Λ}]`, hence an element

`x_can ∈ T_x(Ω_{A/Λ}) = Lift(x, A[Ω_{A/Λ}])`,

the *canonical element*. Composing with the functoriality of `T_x` turns a `Λ`-derivation of
`A` with values in a module `k`, written as an `A`-linear map `Ω_{A/Λ} → k`, into an element
of `T_x(k)`: this is the map on tangent spaces induced by the family `x` over `Spec A`.

## Main definitions

* `Deformation.Artin.differentialsModule`,
  `Deformation.Artin.differentialsSiteModule` — the module of differentials `Ω_{A/Λ}` as an
  object of `Mod_A` and, given that its square-zero spectrum lies in the site, as a site
  module.
* `Deformation.Artin.CanonicalDeformationData` — the canonical section, the lift of `x` it
  produces, and the resulting element of the tangent module.
* `Deformation.Artin.canonicalDeformationElement` — that datum.
* `Deformation.Artin.canonicalTangentMap` — the induced map on tangent spaces.

## Implementation notes

The chosen big fppf site must contain the spectrum of the square-zero extension by the module
of differentials; this is a hypothesis rather than a consequence, since it is a size
condition. The factorization of `Spec A → S` through an affine open `Spec Λ` is recorded by
the two arguments `baseMap` and `baseFactorization`, which is all that the source's choice of
affine open is used for.

The element of the tangent module is pinned down by a *representative*: a lift of `x` whose
class is the image of the element under the identification of `Deformation.Artin.liftEquiv`,
together with a cartesian arrow from that lift to `x` over the canonical section and the
identity triangle over `A`. Those fields specify the element independently of which cartesian
lift is chosen.

For the tangent-space map, the source identifies the tangent space of `Spec A` with
`Der_Λ(A, k) = Hom_A(Ω_{A/Λ}, k)` and the tangent space of the deformation functor with
`T_x(k)`; those descriptions are used directly, so the hypotheses that `k` is a residue field
at a finite-type point and that `Λ → A` is of finite type over a Noetherian `Λ` are not
needed for the formula and are not imposed. That the value is the pullback of the canonical
element follows from the naturality field of the tangent functor data.

## References

* [Stacks Project, Tag 07YC](https://stacks.math.columbia.edu/tag/07YC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace Deformation.Artin

/-- The induced right action of `A` on the module of differentials `Ω_{A/Λ}`, which the
trivial square-zero extension `A[Ω_{A/Λ}]` needs in addition to the left action. -/
local instance differentialsOpposite {Λ A : Type*} [CommRing Λ] [CommRing A] [Algebra Λ A] :
    Module Aᵐᵒᵖ Ω[A⁄Λ] :=
  Module.oppositeOfCommSemiring A Ω[A⁄Λ]

/-- Over a commutative ring the left and right actions on the module of differentials agree. -/
local instance differentialsCentralScalar {Λ A : Type*} [CommRing Λ] [CommRing A]
    [Algebra Λ A] : IsCentralScalar A Ω[A⁄Λ] :=
  Module.isCentralScalar_oppositeOfCommSemiring A Ω[A⁄Λ]

/-! ### The module of differentials as a site module -/

section Differentials

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- The module of differentials `Ω_{A/Λ}` as an object of `Mod_A`. -/
public abbrev differentialsModule : ModuleCat.{u} A := ModuleCat.of A Ω[A⁄Λ]

variable (B : BigFppfSite.{u})

/-- The module of differentials as a site module, given that its trivial square-zero
extension occurs in the chosen big fppf site. -/
public abbrev differentialsSiteModule
    (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A)))) :
    SiteModule A B :=
  ⟨differentialsModule Λ A, hΩ⟩

end Differentials

/-! ### The canonical element -/

section Canonical

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))

/-- The canonical section `a ↦ (a, d a)` of the square-zero projection, the lift of `x` it
produces, and the resulting element of the tangent module. -/
public structure CanonicalDeformationData where
  /-- The section `a ↦ (a, d a)` of the square-zero projection. -/
  sectionRing : A →+* TrivSqZeroExt A Ω[A⁄Λ]
  /-- It is given by the universal derivation. -/
  sectionRing_apply : ∀ a : A, sectionRing a = (a, KaehlerDifferential.D Λ A a)
  /-- The induced morphism over the base scheme. -/
  sectionScheme : squareZeroOver A B S hS toS (differentialsSiteModule Λ A B hΩ) ⟶
    algebraOver A B S hS toS hA
  /-- It is the morphism of spectra determined by the section. -/
  sectionScheme_spec : (BigFppfOver.toScheme B S hS).map sectionScheme =
    Spec.map (CommRingCat.ofHom sectionRing)
  /-- The section is a right inverse of the square-zero closed immersion. -/
  section_isRightInverse :
    squareZeroArrow A B S hS toS hA (differentialsSiteModule Λ A B hΩ) ≫ sectionScheme =
      𝟙 (algebraOver A B S hS toS hA)
  /-- The canonical element of the tangent module at `Ω_{A/Λ}`. -/
  element : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
    (differentialsSiteModule Λ A B hΩ)
  /-- A representative of the lift class corresponding to the canonical element. -/
  representative : (Under.post p).Fiber (Under.mk (eqToHom hx ≫
    squareZeroArrow A B S hS toS hA (differentialsSiteModule Λ A B hΩ)))
  /-- The representative represents the canonical element. -/
  representative_class :
    (tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
        (differentialsSiteModule Λ A B hΩ) element = Quotient.mk _ representative
  /-- The arrow exhibiting the representative as a pullback of `x`. -/
  cartesianMap : representative.1.right ⟶ x
  /-- It is cartesian over the canonical section. -/
  cartesian : p.IsStronglyCartesian sectionScheme cartesianMap
  /-- Restricting it back along the square-zero immersion recovers the identity of `x`. -/
  restrictsToOriginal : representative.1.hom ≫ cartesianMap = 𝟙 x

/-- **Stacks 07YC.** The canonical element of `T_x(Ω_{A/Λ})` attached to the universal
derivation `d : A → Ω_{A/Λ}`. -/
@[stacks 07YC "canonical_deformation_element"]
public def canonicalDeformationElement (baseMap : Spec (.of Λ) ⟶ S)
    (baseFactorization :
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS) :
    CanonicalDeformationData Λ A B S hS toS hA p x hx hp hRS hΩ := by
  let s : A →+* TrivSqZeroExt A Ω[A⁄Λ] :=
    { toFun a := (a, KaehlerDifferential.D Λ A a)
      map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
      map_mul' a b := by
        refine TrivSqZeroExt.ext rfl ?_
        change (KaehlerDifferential.D Λ A) (a * b) =
          a • (KaehlerDifferential.D Λ A) b + b • (KaehlerDifferential.D Λ A) a
        simp only [Derivation.leibniz]
      map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
      map_add' a b := TrivSqZeroExt.ext rfl ((KaehlerDifferential.D Λ A).map_add a b) }
  let M := differentialsSiteModule Λ A B hΩ
  have hbase : CommRingCat.ofHom (algebraMap Λ A) ≫ CommRingCat.ofHom s =
      CommRingCat.ofHom (algebraMap Λ A) ≫
        CommRingCat.ofHom (TrivSqZeroExt.inlHom A Ω[A⁄Λ]) := by
    apply CommRingCat.hom_ext
    ext r
    · rfl
    · exact (KaehlerDifferential.D Λ A).map_algebraMap r
  let f : squareZeroOver A B S hS toS M ⟶ algebraOver A B S hS toS hA := by
    refine Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom s)) : B.obj hΩ ⟶ B.obj hA) ?_
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom s) ≫ toS =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A Ω[A⁄Λ])) ≫ toS
    rw [← baseFactorization, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, hbase]
  have hf : (BigFppfOver.toScheme B S hS).map f = Spec.map (CommRingCat.ofHom s) := rfl
  have hright : squareZeroArrow A B S hS toS hA M ≫ f = 𝟙 (algebraOver A B S hS toS hA) := by
    ext
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A Ω[A⁄Λ]).toRingHom) ≫
      Spec.map (CommRingCat.ofHom s) = 𝟙 (Spec (.of A))
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom s ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom A A Ω[A⁄Λ]).toRingHom =
        𝟙 (CommRingCat.of A) := by
      apply CommRingCat.hom_ext
      ext a
      rfl
    rw [h, Spec.map_id]
  let y := Classical.choose (hp.exists_lift f x hx)
  let φ := Classical.choose (Classical.choose_spec (hp.exists_lift f x hx))
  letI : p.IsHomLift f φ :=
    Classical.choose_spec (Classical.choose_spec (hp.exists_lift f x hx))
  have hcart : p.IsStronglyCartesian f φ := hp.isStronglyCartesian_homLift f φ
  letI : p.IsStronglyCartesian f φ := hcart
  letI : p.IsHomLift (eqToHom hx) (𝟙 x) := by
    apply IsHomLift.of_fac p (eqToHom hx) (𝟙 x) rfl hx
    simp
  have hcomp : eqToHom hx =
      (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) ≫ f := by
    rw [Category.assoc, hright, Category.comp_id]
  let ψ : x ⟶ y := Functor.IsStronglyCartesian.map p f φ hcomp (𝟙 x)
  have hψφ : ψ ≫ φ = 𝟙 x := Functor.IsStronglyCartesian.fac p f φ hcomp (𝟙 x)
  have hy : p.obj y = squareZeroOver A B S hS toS M := IsHomLift.domain_eq p f φ
  have hpψ : p.map ψ ≫ eqToHom hy =
      eqToHom hx ≫ squareZeroArrow A B S hS toS hA M := by
    rw [IsHomLift.fac' p (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) ψ]
    simp
  have underMkEq {Y Z : BigFppfOver B S hS} (h : Y = Z) (u : p.obj x ⟶ Y)
      (v : p.obj x ⟶ Z) (huv : u ≫ eqToHom h = v) :
      (Under.mk u : Under (p.obj x)) = Under.mk v := by
    cases h
    simpa using congrArg (fun t => (Under.mk t : Under (p.obj x))) huv
  let rep : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)) := by
    refine ⟨Under.mk ψ, ?_⟩
    change Under.mk (p.map ψ) =
      Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)
    exact underMkEq hy (p.map ψ) _ hpψ
  let e := (tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv M
  exact
    { sectionRing := s
      sectionRing_apply := fun a => rfl
      sectionScheme := f
      sectionScheme_spec := hf
      section_isRightInverse := hright
      element := e.symm (Quotient.mk _ rep)
      representative := rep
      representative_class := e.apply_symm_apply _
      cartesianMap := φ
      cartesian := hcart
      restrictsToOriginal := hψφ }

end Canonical

/-! ### The induced map on tangent spaces -/

section TangentMap

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

/-- **Stacks 07YC.** The map on tangent spaces induced by the family `x` over `Spec A`: a
`Λ`-derivation of `A` with values in `k`, written as an `A`-linear map `Ω_{A/Λ} → k`, carries
the canonical element to an element of `T_x(k)`. -/
@[stacks 07YC "the tangent-space map"]
public def canonicalTangentMap (θ : Ω[A⁄Λ] →ₗ[A] k) :
    (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) :=
  (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map
    (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
      baseMap baseFactorization).element

end TangentMap

end Deformation.Artin
