module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspace
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspaceExistence
public import StacksFrontier.AlgebraicGeometry.Crystalline.BasisCriteria
public import StacksFrontier.AlgebraicGeometry.Crystalline.ClosedFiberPullback
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerGluing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecDividedPowerScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.ClosedFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.IdealSheafQuasicoherent
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Fibre products of divided power schemes

Let `(S, I, γ)` be a divided power scheme and let `f : (T, J, δ) → (S, I, γ)` and
`f' : (T', J', δ') → (S, I, γ)` be morphisms of divided power schemes.  Then the fibre product
of `f` and `f'` exists in the category of divided power schemes.  Its underlying scheme is a
closed subscheme of the ordinary scheme-theoretic fibre product `T ×_S T'`, and its closed
fibre is the ordinary fibre product `T₀ ×_{S₀} T'₀` of the closed fibres.

The construction is local on `T ×_S T'`.  Over affine opens `U ⊆ S`, `V ⊆ T`, `V' ⊆ T'` with
`f(V), f'(V') ⊆ U` the chart is the spectrum of the pushout of divided power rings
`Γ(V, 𝒪) ⊗_{Γ(U, 𝒪)} Γ(V', 𝒪) → B''`; the canonical map from the tensor product to the pushout
is surjective, so the chart is a closed subscheme of `V ×_U V'`, and its quotient by the
distinguished ideal is the ordinary fibre product of the quotients.  The charts glue because
divided powers extend uniquely along the flat localization maps that compare two charts, which
also produces the divided power structure on the glued ideal sheaf.  The universal property is
checked chart by chart against an arbitrary cone.

This file holds the affine step: the comparison of the spectrum of a pushout of divided power
rings with the ordinary fibre product of spectra and with the fibre product of the closed
fibres, and the localizations of divided power rings, with their pushouts, that compare two
affine charts.

## References

* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
* [Stacks Project, Tag 0H86](https://stacks.math.columbia.edu/tag/0H86)
* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Opposite
open scoped AlgebraicGeometry

universe u v w

namespace Crystalline.DividedPowerScheme

attribute [local implicit_reducible] specDividedPowerScheme toSpecDividedPowerScheme
  specDividedPowerSchemeUnit specDividedPowerHomEquiv

private theorem dividedPowerRing_pushout_tensorComparison_isClosedImmersion
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (DividedPowerRing.tensorProductToPushout f f' g g' h.w))) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra A B' := f'.toRingHom.toAlgebra
  apply IsClosedImmersion.spec_of_surjective
  exact DividedPowerRing.tensorProductToPushout_surjective f f' g g' h

noncomputable def affineDividedPowerPushoutComparison
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    Spec (CommRingCat.of B'') ⟶
      pullback (Spec.map (CommRingCat.ofHom f.toRingHom))
        (Spec.map (CommRingCat.ofHom f'.toRingHom)) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra A B' := f'.toRingHom.toAlgebra
  exact Spec.map (CommRingCat.ofHom
      (DividedPowerRing.tensorProductToPushout f f' g g' h.w)) ≫
    (pullbackSpecIso A B B').inv

attribute [local implicit_reducible] affineDividedPowerPushoutComparison

theorem affineDividedPowerPushoutComparison_fst
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    affineDividedPowerPushoutComparison f f' g g' h ≫
      pullback.fst (Spec.map (CommRingCat.ofHom f.toRingHom))
        (Spec.map (CommRingCat.ofHom f'.toRingHom)) = Spec.map (CommRingCat.ofHom g.toRingHom) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra A B' := f'.toRingHom.toAlgebra
  show Spec.map (CommRingCat.ofHom
      (DividedPowerRing.tensorProductToPushout f f' g g' h.w)) ≫
    (pullbackSpecIso A B B').inv ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A B'))) = _
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  show DividedPowerRing.tensorProductToPushout f f' g g' h.w
    (b ⊗ₜ[A] (1 : B')) = g b
  rw [DividedPowerRing.tensorProductToPushout_tmul]
  show g b * (g'.toRingHom 1) = g b
  rw [map_one, mul_one]

theorem affineDividedPowerPushoutComparison_snd
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    affineDividedPowerPushoutComparison f f' g g' h ≫
      pullback.snd (Spec.map (CommRingCat.ofHom f.toRingHom))
        (Spec.map (CommRingCat.ofHom f'.toRingHom)) =
      Spec.map (CommRingCat.ofHom g'.toRingHom) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra A B' := f'.toRingHom.toAlgebra
  show Spec.map (CommRingCat.ofHom
      (DividedPowerRing.tensorProductToPushout f f' g g' h.w)) ≫
    (pullbackSpecIso A B B').inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A B'))) = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  show DividedPowerRing.tensorProductToPushout f f' g g' h.w
    ((1 : B) ⊗ₜ[A] b) = g' b
  rw [DividedPowerRing.tensorProductToPushout_tmul]
  show (g.toRingHom 1) * g' b = g' b
  rw [map_one, one_mul]

theorem affineDividedPowerPushoutComparison_isClosedImmersion
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    IsClosedImmersion (affineDividedPowerPushoutComparison f f' g g' h) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra A B' := f'.toRingHom.toAlgebra
  show IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (DividedPowerRing.tensorProductToPushout f f' g g' h.w)) ≫
    (pullbackSpecIso A B B').inv)
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (DividedPowerRing.tensorProductToPushout f f' g g' h.w))) :=
    dividedPowerRing_pushout_tensorComparison_isClosedImmersion f f' g g' h
  infer_instance

/-- On affine charts, the closed fibre of a divided-power pushout is the ordinary
scheme-theoretic pullback of the two closed fibres.  This is the local algebra bridge for
the global closed-fibre comparison. -/
private noncomputable def affineDividedPowerPushoutClosedFiberComparison
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    Spec (CommRingCat.of (B'' ⧸ B''.ideal)) ⟶
      CategoryTheory.Limits.pullback
        (Spec.map (CommRingCat.ofHom
          (DividedPowerRing.quotientRingHom f)))
        (Spec.map (CommRingCat.ofHom
          (DividedPowerRing.quotientRingHom f'))) := by
  let : Algebra (A ⧸ A.ideal) (B ⧸ B.ideal) :=
    (DividedPowerRing.quotientRingHom f).toAlgebra
  let : Algebra (A ⧸ A.ideal) (B' ⧸ B'.ideal) :=
    (DividedPowerRing.quotientRingHom f').toAlgebra
  let e := DividedPowerRing.tensorProductQuotientEquivPushoutQuotient
    f f' g g' h
  exact Spec.map (CommRingCat.ofHom e.1.toRingHom) ≫
    (pullbackSpecIso (A ⧸ A.ideal) (B ⧸ B.ideal) (B' ⧸ B'.ideal)).inv

attribute [local implicit_reducible] affineDividedPowerPushoutClosedFiberComparison

private theorem affineDividedPowerPushoutClosedFiberComparison_fst
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    affineDividedPowerPushoutClosedFiberComparison f f' g g' h ≫
      pullback.fst
        (Spec.map (CommRingCat.ofHom
          (DividedPowerRing.quotientRingHom f)))
        (Spec.map (CommRingCat.ofHom
          (DividedPowerRing.quotientRingHom f'))) =
      Spec.map (CommRingCat.ofHom
        (DividedPowerRing.quotientRingHom g)) := by
  let : Algebra (A ⧸ A.ideal) (B ⧸ B.ideal) :=
    (DividedPowerRing.quotientRingHom f).toAlgebra
  let : Algebra (A ⧸ A.ideal) (B' ⧸ B'.ideal) :=
    (DividedPowerRing.quotientRingHom f').toAlgebra
  let e := DividedPowerRing.tensorProductQuotientEquivPushoutQuotient
    f f' g g' h
  show Spec.map (CommRingCat.ofHom e.1.toRingHom) ≫
    (pullbackSpecIso (A ⧸ A.ideal) (B ⧸ B.ideal) (B' ⧸ B'.ideal)).inv ≫ _ = _
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  show e.1 (Ideal.Quotient.mk B.ideal b ⊗ₜ[A ⧸ A.ideal]
      Ideal.Quotient.mk B'.ideal 1) =
    Ideal.Quotient.mk B''.ideal (g b)
  rw [e.2 b 1]
  show Ideal.Quotient.mk B''.ideal ((g.toRingHom b) * (g'.toRingHom 1)) = _
  rw [map_one, mul_one]
  rfl

private theorem affineDividedPowerPushoutClosedFiberComparison_snd
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    affineDividedPowerPushoutClosedFiberComparison f f' g g' h ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom
          (DividedPowerRing.quotientRingHom f)))
        (Spec.map (CommRingCat.ofHom
          (DividedPowerRing.quotientRingHom f'))) =
      Spec.map (CommRingCat.ofHom
        (DividedPowerRing.quotientRingHom g')) := by
  let : Algebra (A ⧸ A.ideal) (B ⧸ B.ideal) :=
    (DividedPowerRing.quotientRingHom f).toAlgebra
  let : Algebra (A ⧸ A.ideal) (B' ⧸ B'.ideal) :=
    (DividedPowerRing.quotientRingHom f').toAlgebra
  let e := DividedPowerRing.tensorProductQuotientEquivPushoutQuotient
    f f' g g' h
  show Spec.map (CommRingCat.ofHom e.1.toRingHom) ≫
    (pullbackSpecIso (A ⧸ A.ideal) (B ⧸ B.ideal) (B' ⧸ B'.ideal)).inv ≫ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  show e.1 (Ideal.Quotient.mk B.ideal 1 ⊗ₜ[A ⧸ A.ideal]
      Ideal.Quotient.mk B'.ideal b) =
    Ideal.Quotient.mk B''.ideal (g' b)
  rw [e.2 1 b]
  show Ideal.Quotient.mk B''.ideal ((g.toRingHom 1) * (g'.toRingHom b)) = _
  rw [map_one, one_mul]
  rfl

private theorem affineDividedPowerPushoutClosedFiberComparison_isIso
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    IsIso (affineDividedPowerPushoutClosedFiberComparison f f' g g' h) := by
  let : Algebra (A ⧸ A.ideal) (B ⧸ B.ideal) :=
    (DividedPowerRing.quotientRingHom f).toAlgebra
  let : Algebra (A ⧸ A.ideal) (B' ⧸ B'.ideal) :=
    (DividedPowerRing.quotientRingHom f').toAlgebra
  let e := DividedPowerRing.tensorProductQuotientEquivPushoutQuotient
    f f' g g' h
  show IsIso (Spec.map (CommRingCat.ofHom e.1.toRingHom) ≫
    (pullbackSpecIso (A ⧸ A.ideal) (B ⧸ B.ideal) (B' ⧸ B'.ideal)).inv)
  have : IsIso (CommRingCat.ofHom e.1.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 e.1.bijective
  infer_instance

/-- A flat restriction of a divided-power ring carries the unique extension of its divided
powers to the image ideal.  This is the ring-level compatibility used on overlaps of affine
charts in a global construction. -/
private noncomputable def flatRestrictedDividedPowerRing
    {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    (f : A →+* B) (hf : f.Flat) : DividedPowerRing.{v} :=
  ⟨B, A.ideal.map f,
    DividedPowers.DividedPowerRing.extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat
      A f (Or.inr (Or.inr hf))⟩

attribute [local implicit_reducible] flatRestrictedDividedPowerRing

private theorem flatRestrictedDividedPowerRing_map_isDPMorphism
    {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    (f : A →+* B) (hf : f.Flat) :
    DividedPowers.IsDPMorphism A.dividedPowers
      (flatRestrictedDividedPowerRing f hf).dividedPowers f :=
  DividedPowers.DividedPowerRing.isDPMorphism_extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat
    A f (Or.inr (Or.inr hf))

/-- Localization of a divided-power ring at one element, with the divided powers extended
along the flat localization map. -/
private noncomputable def dividedPowerRingAway
    (A : DividedPowerRing.{u}) (r : A) : DividedPowerRing.{u} :=
  flatRestrictedDividedPowerRing (algebraMap A (Localization.Away r))
    (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.Away r) (Submonoid.powers r)))

attribute [local implicit_reducible] dividedPowerRingAway

/-- The canonical map into a localization is a divided-power morphism for the extended
divided powers. -/
private theorem dividedPowerRingAway_isDPMorphism
    (A : DividedPowerRing.{u}) (r : A) :
    DividedPowers.IsDPMorphism A.dividedPowers
      (dividedPowerRingAway A r).dividedPowers (algebraMap A (Localization.Away r)) :=
  flatRestrictedDividedPowerRing_map_isDPMorphism _ _

/-- The underlying ring of the bundled divided-power localization is the usual away
localization. -/
private noncomputable def dividedPowerRingAway_ringEquiv
    (A : DividedPowerRing.{u}) (r : A) :
    Localization.Away r ≃+* dividedPowerRingAway A r := by
  unfold dividedPowerRingAway flatRestrictedDividedPowerRing
  exact RingEquiv.refl _

attribute [local implicit_reducible] dividedPowerRingAway_ringEquiv

/-- A divided-power map which inverts an element extends uniquely across the corresponding
localization. -/
private noncomputable def dividedPowerRingAwayLift
    (A E : DividedPowerRing.{u}) (r : A) (φ : A ⟶ E)
    (hφ : IsUnit (φ.toRingHom r)) : dividedPowerRingAway A r ⟶ E := by
  let k : Localization.Away r →+* E :=
    IsLocalization.Away.lift r (g := φ.toRingHom) hφ
  have hcomp : DividedPowers.IsDPMorphism A.dividedPowers E.dividedPowers φ.toRingHom :=
    φ.isDPMorphism
  have hkcomp : k.comp (algebraMap A (Localization.Away r)) = φ.toRingHom := by
    simp [k, IsLocalization.Away.lift_comp r (g := φ.toRingHom) hφ]
  have hk : DividedPowers.IsDPMorphism (dividedPowerRingAway A r).dividedPowers
      E.dividedPowers k :=
    DividedPowers.IsDPMorphism.of_comp A.dividedPowers
      (dividedPowerRingAway A r).dividedPowers E.dividedPowers
      (algebraMap A (Localization.Away r)) k
      (show (dividedPowerRingAway A r).ideal =
        A.ideal.map (algebraMap A (Localization.Away r)) from rfl)
      (dividedPowerRingAway_isDPMorphism A r) (hkcomp ▸ hcomp)
  exact DividedPowers.DPMorphism.mk' (f := k) hk

attribute [local implicit_reducible] dividedPowerRingAwayLift

/-- The localization extension restricts to the original divided-power map. -/
private theorem dividedPowerRingAwayLift_comp
    (A E : DividedPowerRing.{u}) (r : A) (φ : A ⟶ E)
    (hφ : IsUnit (φ.toRingHom r)) :
    (dividedPowerRingAwayLift A E r φ hφ).comp
        (DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism A r)) = φ := by
  apply DividedPowers.DPMorphism.ext
  funext x
  exact congrFun (congrArg DFunLike.coe
    (IsLocalization.Away.lift_comp r (g := φ.toRingHom) hφ)) x

/-- The bundled away ring retains the usual localization universal property. -/
private theorem dividedPowerRingAway_isLocalization
    (A : DividedPowerRing.{u}) (r : A) :
    (let _i : Algebra A (dividedPowerRingAway A r) :=
      ((dividedPowerRingAway_ringEquiv A r).toRingHom.comp
        (algebraMap A (Localization.Away r))).toAlgebra
     IsLocalization (Submonoid.powers r) (dividedPowerRingAway A r)) := by
  let e := dividedPowerRingAway_ringEquiv A r
  let : Algebra A (dividedPowerRingAway A r) :=
    (e.toRingHom.comp (algebraMap A (Localization.Away r))).toAlgebra
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (R := A) (M := Submonoid.powers r) e).mp inferInstance

/-- Maps out of an away localization are determined by their restriction to the original
ring. -/
private theorem dividedPowerRingAway_hom_ext
    (A E : DividedPowerRing.{u}) (r : A)
    (φ ψ : dividedPowerRingAway A r ⟶ E)
    (h : φ.comp (DividedPowers.DPMorphism.mk'
        (dividedPowerRingAway_isDPMorphism A r)) =
      ψ.comp (DividedPowers.DPMorphism.mk'
        (dividedPowerRingAway_isDPMorphism A r))) :
    φ = ψ := by
  apply DividedPowers.DPMorphism.ext
  funext x
  let e := dividedPowerRingAway_ringEquiv A r
  let : Algebra A (dividedPowerRingAway A r) :=
    (e.toRingHom.comp (algebraMap A (Localization.Away r))).toAlgebra
  let : IsLocalization (Submonoid.powers r) (dividedPowerRingAway A r) :=
    dividedPowerRingAway_isLocalization A r
  have hring : φ.toRingHom = ψ.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    exact congrArg DividedPowers.DPMorphism.toRingHom h
  exact DFunLike.congr_fun hring x

/-- The canonical image of `r` in the away localization of a divided-power ring is a unit. -/
private theorem dividedPowerRingAway_isUnit_self (A : DividedPowerRing.{u}) (r : A) :
    IsUnit ((DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism A r)).toRingHom r) :=
  (IsLocalization.Away.algebraMap_isUnit r).map (dividedPowerRingAway_ringEquiv A r).toRingHom

/-- Both factors of `x * y` become units in the away localization at `x * y`. -/
private theorem dividedPowerRingAway_isUnit_mul {D : DividedPowerRing.{u}} (x y : D) :
    IsUnit ((DividedPowers.DPMorphism.mk'
      (dividedPowerRingAway_isDPMorphism D (x * y))).toRingHom x) ∧
    IsUnit ((DividedPowers.DPMorphism.mk'
      (dividedPowerRingAway_isDPMorphism D (x * y))).toRingHom y) := by
  have := dividedPowerRingAway_isUnit_self D (x * y)
  rw [map_mul] at this
  exact IsUnit.mul_iff.mp this

/-- The left arm of a divided-power ring pushout restricts to the corresponding affine
localization charts. -/
private noncomputable def dividedPowerRingAwayPushoutInl
    {B C D : DividedPowerRing.{u}}
    (g : B ⟶ D) (g' : C ⟶ D) (b : B) (c : C) :
  dividedPowerRingAway B b ⟶
  dividedPowerRingAway D (g.toRingHom b * g'.toRingHom c) :=
  dividedPowerRingAwayLift B _ b
    (g ≫ DividedPowers.DPMorphism.mk'
      (dividedPowerRingAway_isDPMorphism D (g.toRingHom b * g'.toRingHom c)))
    (dividedPowerRingAway_isUnit_mul _ _).1

attribute [local implicit_reducible] dividedPowerRingAwayPushoutInl

/-- The right arm of a divided-power ring pushout restricts to the corresponding affine
localization charts. -/
private noncomputable def dividedPowerRingAwayPushoutInr
    {B C D : DividedPowerRing.{u}}
    (g : B ⟶ D) (g' : C ⟶ D) (b : B) (c : C) :
    dividedPowerRingAway C c ⟶
      dividedPowerRingAway D (g.toRingHom b * g'.toRingHom c) :=
  dividedPowerRingAwayLift C _ c
    (g' ≫ DividedPowers.DPMorphism.mk'
      (dividedPowerRingAway_isDPMorphism D (g.toRingHom b * g'.toRingHom c)))
    (dividedPowerRingAway_isUnit_mul _ _).2

attribute [local implicit_reducible] dividedPowerRingAwayPushoutInr

/-- The localized left pushout map is the composite of the original leg and the
localization of the pushout. -/
private theorem dividedPowerRingAwayPushoutInl_square
    {B C D : DividedPowerRing.{u}}
    (g : B ⟶ D) (g' : C ⟶ D) (b : B) (c : C) :
    (dividedPowerRingAwayPushoutInl g g' b c).comp
        (DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism B b)) =
      (DividedPowers.DPMorphism.mk'
        (dividedPowerRingAway_isDPMorphism D
          (g.toRingHom b * g'.toRingHom c))).comp g :=
  dividedPowerRingAwayLift_comp _ _ _ _ _

/-- The localized right pushout map is the composite of the original leg and the
localization of the pushout. -/
private theorem dividedPowerRingAwayPushoutInr_square
    {B C D : DividedPowerRing.{u}}
    (g : B ⟶ D) (g' : C ⟶ D) (b : B) (c : C) :
    (dividedPowerRingAwayPushoutInr g g' b c).comp
        (DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism C c)) =
      (DividedPowers.DPMorphism.mk'
        (dividedPowerRingAway_isDPMorphism D
          (g.toRingHom b * g'.toRingHom c))).comp g' :=
  dividedPowerRingAwayLift_comp _ _ _ _ _

/-- The two localized maps from the common divided-power ring agree. -/
private theorem dividedPowerRingAwayPushout_compatible
    {A B C D : DividedPowerRing.{u}}
    (f : A ⟶ B) (f' : A ⟶ C) (g : B ⟶ D) (g' : C ⟶ D)
    (h : IsPushout f f' g g') (b : B) (c : C) :
    (f ≫ DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism B b)) ≫
        dividedPowerRingAwayPushoutInl g g' b c =
      (f' ≫ DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism C c)) ≫
        dividedPowerRingAwayPushoutInr g g' b c := by
  let jB : B ⟶ dividedPowerRingAway B b :=
    DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism B b)
  let jC : C ⟶ dividedPowerRingAway C c :=
    DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism C c)
  let q : D := g.toRingHom b * g'.toRingHom c
  let jD : D ⟶ dividedPowerRingAway D q :=
    DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism D q)
  have hL : jB ≫ dividedPowerRingAwayPushoutInl g g' b c = g ≫ jD :=
    dividedPowerRingAwayPushoutInl_square g g' b c
  have hR : jC ≫ dividedPowerRingAwayPushoutInr g g' b c = g' ≫ jD :=
    dividedPowerRingAwayPushoutInr_square g g' b c
  simp only [Category.assoc]
  rw [hL, reassoc_of% h.w, ← hR]

/-- A divided-power map out of the localized pushout is determined by its restrictions to
the two localization charts. -/
private theorem dividedPowerRingAwayPushout_hom_ext
    {A B C D : DividedPowerRing.{u}}
    (f : A ⟶ B) (f' : A ⟶ C) (g : B ⟶ D) (g' : C ⟶ D)
    (h : IsPushout f f' g g') (b : B) (c : C)
    {E : DividedPowerRing.{u}}
    (φ ψ : dividedPowerRingAway D (g.toRingHom b * g'.toRingHom c) ⟶ E)
    (hφ : dividedPowerRingAwayPushoutInl g g' b c ≫ φ =
      dividedPowerRingAwayPushoutInl g g' b c ≫ ψ)
    (hψ : dividedPowerRingAwayPushoutInr g g' b c ≫ φ =
      dividedPowerRingAwayPushoutInr g g' b c ≫ ψ) :
    φ = ψ := by
  let jB : B ⟶ dividedPowerRingAway B b :=
    DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism B b)
  let jC : C ⟶ dividedPowerRingAway C c :=
    DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism C c)
  let q : D := g.toRingHom b * g'.toRingHom c
  let jD : D ⟶ dividedPowerRingAway D q :=
    DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism D q)
  let inl := dividedPowerRingAwayPushoutInl g g' b c
  let inr := dividedPowerRingAwayPushoutInr g g' b c
  have hB : jB ≫ inl = g ≫ jD :=
    dividedPowerRingAwayPushoutInl_square g g' b c
  have hC : jC ≫ inr = g' ≫ jD :=
    dividedPowerRingAwayPushoutInr_square g g' b c
  have hleft : g ≫ jD ≫ φ = g ≫ jD ≫ ψ := by
    rw [← reassoc_of% hB, ← reassoc_of% hB, hφ]
  have hright : g' ≫ jD ≫ φ = g' ≫ jD ≫ ψ := by
    rw [← reassoc_of% hC, ← reassoc_of% hC, hψ]
  have hD : jD ≫ φ = jD ≫ ψ := by
    apply h.hom_ext
    · simpa [Category.assoc, q] using hleft
    · simpa [Category.assoc, q] using hright
  change φ.comp (DividedPowers.DPMorphism.mk'
    (dividedPowerRingAway_isDPMorphism D q)) =
    ψ.comp (DividedPowers.DPMorphism.mk'
      (dividedPowerRingAway_isDPMorphism D q)) at hD
  exact dividedPowerRingAway_hom_ext D E q φ ψ hD

/-- Rewriting a three-fold composite along a commuting square and a retraction identity.
Stated over variables in an abstract category so that applying it does not force the
localization data of a divided-power ring to be unfolded. -/
private theorem comp_comp_eq_of_square {C : Type*} [Category C] {W X Y Z V : C}
    (a : W ⟶ X) (bb : X ⟶ Y) (e : Y ⟶ Z) (gg : W ⟶ V) (j : V ⟶ Y) (k : V ⟶ Z) (p : W ⟶ Z)
    (hsq : a ≫ bb = gg ≫ j) (hk : j ≫ e = k) (hp : gg ≫ k = p) :
    a ≫ bb ≫ e = p := by
  rw [← Category.assoc, hsq, Category.assoc, hk, hp]

/-- Two divided-power maps out of the localization charts that agree over the base factor
through the localized pushout. -/
private theorem dividedPowerRingAwayPushout_exists_desc
    {A B C D : DividedPowerRing.{u}}
    (f : A ⟶ B) (f' : A ⟶ C) (g : B ⟶ D) (g' : C ⟶ D)
    (h : IsPushout f f' g g') (b : B) (c : C)
    {E : DividedPowerRing.{u}}
    (φ : dividedPowerRingAway B b ⟶ E) (ψ : dividedPowerRingAway C c ⟶ E)
    (hφ : (f ≫ DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism B b)) ≫ φ =
      (f' ≫ DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism C c)) ≫ ψ) :
    ∃ l : dividedPowerRingAway D (g.toRingHom b * g'.toRingHom c) ⟶ E,
      dividedPowerRingAwayPushoutInl g g' b c ≫ l = φ ∧
        dividedPowerRingAwayPushoutInr g g' b c ≫ l = ψ := by
  let jB : B ⟶ dividedPowerRingAway B b :=
    DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism B b)
  let jC : C ⟶ dividedPowerRingAway C c :=
    DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism C c)
  let q : D := g.toRingHom b * g'.toRingHom c
  let jD : D ⟶ dividedPowerRingAway D q :=
    DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism D q)
  let inl := dividedPowerRingAwayPushoutInl g g' b c
  let inr := dividedPowerRingAwayPushoutInr g g' b c
  have hB : jB ≫ inl = g ≫ jD :=
    dividedPowerRingAwayPushoutInl_square g g' b c
  have hC : jC ≫ inr = g' ≫ jD :=
    dividedPowerRingAwayPushoutInr_square g g' b c
  let φB := jB ≫ φ
  let ψC := jC ≫ ψ
  have hbase : f ≫ φB = f' ≫ ψC := by
    simpa [φB, ψC, Category.assoc] using hφ
  let k : D ⟶ E := h.desc φB ψC hbase
  have hgb : k.toRingHom (g.toRingHom b) = φB.toRingHom b :=
    congrArg (fun t : B ⟶ E => t.toRingHom b) (h.inl_desc φB ψC hbase)
  have hgc : k.toRingHom (g'.toRingHom c) = ψC.toRingHom c :=
    congrArg (fun t : C ⟶ E => t.toRingHom c) (h.inr_desc φB ψC hbase)
  have huB : IsUnit (φB.toRingHom b) := (dividedPowerRingAway_isUnit_self B b).map φ.toRingHom
  have huC : IsUnit (ψC.toRingHom c) := (dividedPowerRingAway_isUnit_self C c).map ψ.toRingHom
  have huq : IsUnit (k.toRingHom q) := by
    show IsUnit (k.toRingHom (g.toRingHom b * g'.toRingHom c))
    rw [map_mul, hgb, hgc]
    exact huB.mul huC
  let ell : dividedPowerRingAway D q ⟶ E :=
    dividedPowerRingAwayLift D E q k huq
  have hjk : jD ≫ ell = k := dividedPowerRingAwayLift_comp D E q k huq
  have hleft : jB ≫ inl ≫ ell = jB ≫ φ :=
    comp_comp_eq_of_square jB inl ell g jD k (jB ≫ φ) hB hjk (h.inl_desc φB ψC hbase)
  have hright : jC ≫ inr ≫ ell = jC ≫ ψ :=
    comp_comp_eq_of_square jC inr ell g' jD k (jC ≫ ψ) hC hjk (h.inr_desc φB ψC hbase)
  exact ⟨ell, dividedPowerRingAway_hom_ext B E b (inl ≫ ell) φ hleft,
    dividedPowerRingAway_hom_ext C E c (inr ≫ ell) ψ hright⟩

/-- Localizing the two sides of a divided-power pushout gives the localization of the
pushout at the product of the chart elements. -/
private theorem dividedPowerRingAwayPushout_isPushout
    {A B C D : DividedPowerRing.{u}}
    (f : A ⟶ B) (f' : A ⟶ C) (g : B ⟶ D) (g' : C ⟶ D)
    (h : IsPushout f f' g g') (b : B) (c : C) :
    IsPushout
      (f ≫ DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism B b))
      (f' ≫ DividedPowers.DPMorphism.mk' (dividedPowerRingAway_isDPMorphism C c))
      (dividedPowerRingAwayPushoutInl g g' b c)
      (dividedPowerRingAwayPushoutInr g g' b c) :=
  IsPushout.mk' (dividedPowerRingAwayPushout_compatible f f' g g' h b c)
    (fun _ _ _ hφ hψ => dividedPowerRingAwayPushout_hom_ext f f' g g' h b c _ _ hφ hψ)
    (fun _ _ _ hab => dividedPowerRingAwayPushout_exists_desc f f' g g' h b c _ _ hab)

/-- The ideal obtained by two successive flat restrictions is the ideal obtained by
restricting once along the composite. -/
private theorem flatRestrictedDividedPowerRing_ideal_comp
    {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    {C : Type w} [CommRing C] (f : A →+* B) (hf : f.Flat) (g : B →+* C) :
    (flatRestrictedDividedPowerRing f hf).ideal.map g =
      A.ideal.map (g.comp f) := by
  show Ideal.map g (Ideal.map f A.ideal) = Ideal.map (g.comp f) A.ideal
  rw [Ideal.map_map]

/-- Successive flat extensions preserve the original divided powers along the composite.
This is the overlap compatibility needed when affine charts are restricted further. -/
private theorem flatRestrictedDividedPowerRing_comp_isDPMorphism
    {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    {C : Type w} [CommRing C] (f : A →+* B) (hf : f.Flat)
    (g : B →+* C) (hg : g.Flat) :
    DividedPowers.IsDPMorphism A.dividedPowers
      (flatRestrictedDividedPowerRing g hg
        (A := flatRestrictedDividedPowerRing f hf)).dividedPowers
      (g.comp f) :=
  DividedPowers.IsDPMorphism.comp _
    (flatRestrictedDividedPowerRing_map_isDPMorphism g hg
      (A := flatRestrictedDividedPowerRing f hf))
    (flatRestrictedDividedPowerRing_map_isDPMorphism f hf)

private theorem dpMorphism_transport_targetIdeal
    {R T : Type*} [CommRing R] [CommRing T] {I : Ideal R}
    {J K : Ideal T} (e : J = K) {γ : DividedPowers I} {δ : DividedPowers J}
    (f : R →+* T) (h : DividedPowers.IsDPMorphism γ δ f) :
    DividedPowers.IsDPMorphism γ (e ▸ δ) f := by
  cases e
  exact h

/-- Uniqueness of extension identifies a one-step flat restriction with the
corresponding pair of successive flat restrictions. -/
private theorem flatRestrictedDividedPowerRing_comp_dpow
    {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    {C : Type w} [CommRing C] (f : A →+* B) (hf : f.Flat)
    (g : B →+* C) (hg : g.Flat) :
    ∀ hI : (flatRestrictedDividedPowerRing g hg
        (A := flatRestrictedDividedPowerRing f hf)).ideal =
      (flatRestrictedDividedPowerRing (g.comp f) (RingHom.Flat.comp hf hg)).ideal,
      hI ▸ (flatRestrictedDividedPowerRing g hg
        (A := flatRestrictedDividedPowerRing f hf)).dividedPowers =
        (flatRestrictedDividedPowerRing (g.comp f)
          (RingHom.Flat.comp hf hg)).dividedPowers := by
  intro hI
  let N := flatRestrictedDividedPowerRing g hg
    (A := flatRestrictedDividedPowerRing f hf)
  let D := flatRestrictedDividedPowerRing (g.comp f) (RingHom.Flat.comp hf hg)
  have hext : DividedPowers.Extends A.dividedPowers (g.comp f) :=
    DividedPowers.DividedPowerRing.dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat
      A (g.comp f) (Or.inr (Or.inr (RingHom.Flat.comp hf hg)))
  have huniq := DividedPowers.existsUnique_extension
    A.dividedPowers (g.comp f) hext
  have hN : DividedPowers.IsDPMorphism A.dividedPowers
      (hI ▸ N.dividedPowers) (g.comp f) :=
    dpMorphism_transport_targetIdeal hI (g.comp f)
      (flatRestrictedDividedPowerRing_comp_isDPMorphism f hf g hg)
  have hD : DividedPowers.IsDPMorphism A.dividedPowers D.dividedPowers
      (g.comp f) :=
    flatRestrictedDividedPowerRing_map_isDPMorphism (g.comp f)
      (RingHom.Flat.comp hf hg)
  exact huniq.unique hN hD

private theorem flatRestrictedDividedPowerRing_dpow_eq
    {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    (f : A →+* B) (hf : f.Flat) (δ : DividedPowers (A.ideal.map f))
    (hδ : DividedPowers.IsDPMorphism A.dividedPowers δ f) :
    δ = (flatRestrictedDividedPowerRing f hf).dividedPowers := by
  have hext : DividedPowers.Extends A.dividedPowers f :=
    DividedPowers.DividedPowerRing.dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat
      A f (Or.inr (Or.inr hf))
  exact (DividedPowers.existsUnique_extension
      A.dividedPowers f hext).unique hδ
    (flatRestrictedDividedPowerRing_map_isDPMorphism f hf)

end Crystalline.DividedPowerScheme

end
