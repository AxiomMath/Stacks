module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.RingTheory.AnalyticallyUnramified.IntegralClosure
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the normalization morphism

Let `A` be a Noetherian local ring and let `X` be a scheme locally of finite type over `A`. If `A`
is analytically unramified and `X` is étale over `A` at the generic points of its irreducible
components, then the normalization morphism of `X` is finite.

## Main results

* `AlgebraicGeometry.Scheme.generic_residueField_essentiallyEtale`: at a generic point in the étale
  locus over a reduced Noetherian ring `A`, the residue field is flat, formally unramified and
  essentially of finite type over `A`.
* `AlgebraicGeometry.Scheme.finite_integralClosure_generic_sections`: over an affine open `U`, the
  integral closure of `Γ(X, U)` in the sections of the generic-point residue spectrum is finite.
* `AlgebraicGeometry.Scheme.normalization_isFinite_of_etaleAt_genericPoints`: the normalization
  morphism of `X` is finite.

## References

* [Stacks Project, Tag 0BG8](https://stacks.math.columbia.edu/tag/0BG8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

/-- A morphism to an affine scheme which is étale at `x` is étale on the sections over some affine
open neighbourhood of `x`, computed against the whole target. -/
theorem exists_etale_appLE_top {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) {x : X} (hx : EtaleAt f x) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U),
      (f.appLE ⊤ U (by simp)).hom.Etale := by
  obtain ⟨U, hU, hxU, V, hV, e, he⟩ := hx
  refine ⟨U, hU, hxU, ?_⟩
  have hr : ((Spec (.of A)).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom.Etale := by
    simpa [Scheme.Hom.appLE] using HasRingHomProperty.appLE (P := @Etale) (𝟙 (Spec (.of A)))
      (inferInstance : Etale (𝟙 (Spec (.of A)))) ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by simp)
  simpa only [← CommRingCat.hom_comp, Scheme.Hom.map_appLE] using
    RingHom.Etale.stableUnderComposition _ _ hr he

/-- Taking sections over an open `U` and then the germ at a point of `U` agrees with taking global
sections and then the germ. -/
theorem Hom.appLE_top_germ {Y X : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (x : X) (hx : x ∈ U) :
    f.appLE ⊤ U (by simp) ≫ X.presheaf.germ U x hx =
      f.appTop ≫ X.presheaf.germ ⊤ x trivial := by
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

/-- At a generic point in the étale locus over a reduced Noetherian base, the residue field is
flat, formally unramified and essentially of finite type over the base. -/
theorem generic_residueField_essentiallyEtale {A : Type u} [CommRing A] [IsNoetherianRing A]
    [_root_.IsReduced A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (x : X) (hx : x ∈ genericPoints X)
    (he : EtaleAt f x) :
    let φ := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.Γevaluation x).hom
    φ.Flat ∧ φ.FormallyUnramified ∧ φ.EssFiniteType := by
  obtain ⟨U, hU, hxU, hUe⟩ := exists_etale_appLE_top f he
  let B := Γ(X, U)
  let T := X.presheaf.stalk x
  let α : A →+* B := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U (by simp)).hom
  let : Algebra A B := α.toAlgebra
  have hα : α.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv)) hUe
  have : Algebra.Etale A B := hα
  let : Algebra B T := (X.presheaf.germ U x hxU).hom.toAlgebra
  let : Algebra A T := Algebra.compHom T α
  have : IsScalarTower A B T := IsScalarTower.of_compHom A B T
  have hloc : IsLocalization.AtPrime T (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.EssFiniteType B T := Algebra.EssFiniteType.of_isLocalization T
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have : Algebra.EssFiniteType A T := Algebra.EssFiniteType.comp A B T
  have : Module.Flat B T := IsLocalization.flat T
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have : Module.Flat A T := Module.Flat.trans A B T
  have : Algebra.FormallyEtale B T := Algebra.FormallyEtale.of_isLocalization
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have : Algebra.FormallyEtale A T := Algebra.FormallyEtale.comp A B T
  have : _root_.IsReduced T := isReduced_of_formallyUnramified_of_flat A T
  have hp : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∈ minimalPrimes B := by
    rw [← genericPointsInOpenEquivMinimalPrimes_asIdeal hU ⟨⟨x, hx⟩, hxU⟩]
    exact (genericPointsInOpenEquivMinimalPrimes hU ⟨⟨x, hx⟩, hxU⟩).2
  have : Ring.KrullDimLE 0 T := Ring.KrullDimLE.of_isLocalization
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal hp T
  let : Field T := Ring.KrullDimLE.isField_of_isReduced.toField
  have hres : Function.Bijective (X.residue x).hom :=
    ⟨RingHom.injective _, X.residue_surjective x⟩
  have hφ : ((X.residue x).hom.comp (algebraMap A T)) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.Γevaluation x).hom := by
    change (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U (by simp) ≫
      X.presheaf.germ U x hxU) ≫ X.residue x).hom = _
    rw [Category.assoc, Hom.appLE_top_germ]
    rfl
  rw [← hφ]
  exact ⟨(show (algebraMap A T).Flat from ‹_›).comp (RingHom.Flat.of_bijective hres),
    (RingHom.formallyUnramified_algebraMap.mpr inferInstance).comp
      (RingHom.FormallyUnramified.of_surjective hres.2),
    (show (algebraMap A T).EssFiniteType from ‹_›).comp
      (RingHom.FiniteType.of_surjective _ hres.2).essFiniteType⟩

/-- Over an analytically unramified Noetherian local base, the sections of the generic-point
residue spectrum over the preimage of an affine open `U` have finite integral closure over
`Γ(X, U)`. -/
theorem finite_integralClosure_generic_sections {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hA : IsAnalyticallyUnramified A)
    (hf : ∀ x : X, x ∈ genericPoints X → EtaleAt f x)
    (U : X.Opens) (hU : IsAffineOpen U) [Finite {η : genericPoints X // η.1 ∈ U}] :
    let g := fromGenericPointResidueFields X
    let _ := (g.app U).hom.toAlgebra
    Module.Finite Γ(X, U) (integralClosure Γ(X, U) Γ(genericPointResidueSpectrum X, g ⁻¹ᵁ U)) := by
  let g := fromGenericPointResidueFields X
  let B := Γ(X, U)
  let L := Γ(genericPointResidueSpectrum X, g ⁻¹ᵁ U)
  let : Algebra B L := (g.app U).hom.toAlgebra
  let α : A →+* B := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U (by simp)).hom
  let : Algebra A B := α.toAlgebra
  have hα : α.FiniteType := (f.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2)
  have : Algebra.FiniteType A B := hα
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let S := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : _root_.IsReduced S := hA
  have : Module.FaithfullyFlat A S :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson (IsLocalRing.maximalIdeal A)
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have : _root_.IsReduced A := isReduced_of_injective (algebraMap A S)
    (FaithfulSMul.algebraMap_injective A S)
  let ι := {η : genericPoints X // η.1 ∈ U}
  let K (i : ι) : Type u := X.residueField i.1.1
  let (i : ι) : Algebra B (K i) := (X.evaluation U i.1.1 i.2).hom.toAlgebra
  let (i : ι) : Algebra A (K i) := Algebra.compHom (K i) α
  have (i : ι) : IsScalarTower A B (K i) := IsScalarTower.of_compHom A B (K i)
  have (i : ι) : Module.Finite B (integralClosure B (K i)) := by
    have hi := generic_residueField_essentiallyEtale f i.1.1 i.1.2 (hf i.1.1 i.1.2)
    have hc : algebraMap A (K i) =
        ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.Γevaluation i.1.1).hom := by
      change ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U (by simp) ≫
        X.evaluation U i.1.1 i.2).hom = _
      simp only [Scheme.evaluation, ← Category.assoc, Hom.appLE_top_germ]
      rfl
    rw [← hc] at hi
    have : Module.Flat A (K i) := hi.1
    have : Algebra.FormallyUnramified A (K i) := hi.2.1
    have : Algebra.EssFiniteType A (K i) := hi.2.2
    exact finite_integralClosure_of_essentiallyEtale hA
  let e := genericPreimageSectionsRingEquiv X U
  let φ (i : ι) : L →ₐ[B] K i :=
    { toRingHom := (Pi.evalRingHom K i).comp e.toRingHom
      commutes' b := by
        change e ((g.app U).hom b) i = (X.evaluation U i.1.1 i.2).hom b
        exact congrArg (fun h : B →+* K i ↦ h b)
          (congrArg CommRingCat.Hom.hom (genericPreimageSectionsRingEquiv_comp_app X U i)) }
  exact finite_integralClosure_of_finite_family K φ fun _ _ h ↦ e.injective h

/-- If a scheme is locally of finite type over an analytically
unramified Noetherian local ring and is étale over it at the generic points of its irreducible
components, then its normalization morphism is finite. -/
@[stacks 0BG8]
theorem normalization_isFinite_of_etaleAt_genericPoints (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] (hA : IsAnalyticallyUnramified A)
    (hf : ∀ x : X, x ∈ genericPoints X → EtaleAt f x) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let hX : ∀ U : X.Opens, IsCompact (U : Set X) →
        (irreducibleComponents U).Finite := fun U hU ↦ by
      let : CompactSpace U := isCompact_iff_compactSpace.mp hU
      let : NoetherianSpace U :=
        noetherianSpace_of_isLocallyNoetherianSpace U
          ((isLocallyNoetherianSpace_of_isLocallyNoetherian X).subtype U)
      exact NoetherianSpace.finite_irreducibleComponents
    IsFinite (normalization X hX) := by
  intro hX
  let g := fromGenericPointResidueFields X
  have : QuasiCompact g := quasiCompactFromGenericPointResidueFields X hX
  have : QuasiSeparated g := quasiSeparatedFromGenericPointResidueFields X
  change IsFinite g.fromNormalization
  constructor
  intro U hU
  have : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hX U hU.isCompact)).to_subtype
  have : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_injective (genericPointsInOpenEquiv X U) (genericPointsInOpenEquiv X U).injective
  let := (g.app U).hom.toAlgebra
  have := finite_integralClosure_generic_sections f hA hf U hU
  rw [g.fromNormalization_app hU, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (g.normalizationObjIso hU).inv).2).comp
      (show (algebraMap _ _).Finite from ‹_›)

end AlgebraicGeometry.Scheme

end
