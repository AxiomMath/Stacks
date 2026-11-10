module

public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativePerfection
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModelAnyModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkPointwise
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.Homology.TorAmplitude.Local
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingFiniteTorDimension
import all StacksFrontier.Homology.TorAmplitude.Local

/-!
# Finite Tor dimension of the relative dualizing complex

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a flat morphism of `AlgebraicGeometry.FTS S`,
the category of [Stacks, Tag 0F42]. An object `ω` of `D(𝒪_X)` with the affine-chart description
`Stacks.Duality.IsShriekOfStructureSheafOnCharts` of `f^!𝒪_Y` locally has finite Tor dimension over
`f^{-1}𝒪_Y`, at the genuine derived tensor product; together with its pseudo-coherence this is the
statement that `ω` is perfect relative to `Y` in the sense of [Stacks, Tag 0DI0], the first
assertion of [Stacks, Tag 0E9T] read on the chart description.

## Main results

* `Stacks.Duality.affineGermRingHom_eq_germ` — the ring map `Γ(X, U) → 𝒪_{X,x}` through which the
  stalk of an associated sheaf is computed is the germ map.
* `Stacks.Duality.hasTorAmplitudeCanonical_restrictScalars_extendScalars_of_isLocalization` — a
  Tor-amplitude bound over `R` of a complex `M` over `A` passes to `B ⊗_A M` over `C`, for
  localizations `A → B` and `R → C` compatible with a map `C → B`.
* `Stacks.Duality.exists_hasTorAmplitudeCanonical_stalk_of_chart` — on a chart the derived stalks
  of `ω`, read over the local rings of `Y`, have uniformly bounded Tor amplitude.
* `Stacks.Duality.locallyHasFiniteTorDimension_of_isShriekOfStructureSheafOnCharts` — the Tor
  conjunct of `Y`-perfectness.
* `Stacks.Duality.isPerfectRelativeTo_of_isShriekOfStructureSheafOnCharts` — `ω` is perfect
  relative to `Y`.

## Implementation notes

The ring-level input is [Stacks, Tag 0BZW] (1)(b), in the namespace `Dualizing`,
`PolynomialPresentation.relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap`,
applied to each chart ring map `f.appLE V U`. At a point `y` of a chart the derived stalk of `ω` is
the localization of the chart model
(`Stacks.Duality.nonempty_derivedStalkOfComplex_iso_extendScalars_anyModel`), the Tor bound
survives localization over the base, and the stalkwise criterion
`Scheme.Hom.locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_base_bound`
turns a bound uniform over the finitely many charts covering the quasi-compact `X` into the Tor
conjunct.

## References

* [Stacks Project, Tag 0E9T](https://stacks.math.columbia.edu/tag/0E9T)
* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
* [Stacks Project, Tag 0DI0](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 0DHY](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open StacksDraft.TorAmplitude

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- The germ map `R → 𝒪_{Spec R, y}` is the inverse of `Γ(Spec R, ⊤) ≅ R` followed by the germ of
the structure sheaf at `y`. -/
theorem specGermRingHom_eq_germ (R : CommRingCat.{u}) (y : Spec R) :
    CommRingCat.ofHom (specGermRingHom R y) =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ y trivial := by
  let : Algebra R ((Spec R).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  ext a
  rw [specGermRingHom_eq]
  rfl

/-- **The ring map presenting `𝒪_{X,x}` as a localization of `Γ(X, U)` is the germ map**, for an
affine open `U` containing `x`. -/
theorem affineGermRingHom_eq_germ {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) : affineGermRingHom hU x hx = (X.presheaf.germ U x hx).hom := by
  let xU : U.toScheme := ⟨x, hx⟩
  have key : ∀ a : Γ(X, U), (hU.isoSpec.hom.stalkMap xU).hom
      (specGermRingHom Γ(X, U) (hU.isoSpec.hom xU) a) =
        (U.ι.stalkMap xU).hom ((X.presheaf.germ U x hx).hom a) := by
    intro a
    have e1 := congrArg (fun g => g.hom a) (specGermRingHom_eq_germ Γ(X, U) (hU.isoSpec.hom xU))
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply] at e1
    rw [e1, Scheme.Hom.germ_stalkMap_apply hU.isoSpec.hom ⊤ xU trivial]
    have e3 := Scheme.Hom.germ_stalkMap_apply U.ι U xU hx a
    refine Eq.trans ?_ e3.symm
    have e4 : (hU.isoSpec.hom.app ⊤).hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom a) =
        U.topIso.inv.hom a := by
      rw [hU.isoSpec_hom, show U.toSpecΓ.app ⊤ = U.toSpecΓ.appTop from rfl,
        Scheme.Opens.toSpecΓ_appTop]
      exact congrArg U.topIso.inv.hom (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X, U)) a)
    rw [e4]
    have hle : U.ι ⁻¹ᵁ U ≤ hU.isoSpec.hom ⁻¹ᵁ ⊤ := fun _ _ => trivial
    refine (TopCat.Presheaf.germ_res_apply U.toScheme.presheaf (homOfLE hle) xU hx
      (U.topIso.inv.hom a)).symm.trans (congrArg _ ?_)
    simp only [Scheme.Opens.topIso, Scheme.Opens.ι_app_self]
    change (X.presheaf.map _ ≫ X.presheaf.map _).hom a = (X.presheaf.map _).hom a
    have hm : ∀ {V W W' : (X.Opens)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ W') (h : V ⟶ W'),
        X.presheaf.map f ≫ X.presheaf.map g = X.presheaf.map h := fun f g h =>
      (X.presheaf.map_comp f g).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))
    exact ConcreteCategory.congr_hom (hm _ _ _) a
  ext a
  change (affineStalkRingEquiv hU x hx).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  have := isIso_stalkMap_of_isOpenImmersion hU.isoSpec.hom xU
  apply (ConcreteCategory.bijective_of_isIso (hU.isoSpec.hom.stalkMap xU)).1
  refine (key a).trans ?_
  change _ = (hU.isoSpec.hom.stalkMap xU).hom ((inv (hU.isoSpec.hom.stalkMap xU)).hom
    ((U.ι.stalkMap xU).hom _))
  exact (ConcreteCategory.congr_hom (IsIso.inv_hom_id (hU.isoSpec.hom.stalkMap xU)) _).symm

open StacksDraft.TorAmplitude AlgebraicGeometry.AffineRelativeTorAmplitude in
/-- **Tor amplitude localizes over a localized base.** Let `φ : R → A`, let `σ : A → B` and
`τ : R → C` be localizations and `ψ : C → B` a ring map with `σ ∘ φ = ψ ∘ τ`. If a complex `M` of
`A`-modules has Tor amplitude in `[a, b]` over `R`, then `B ⊗_A M` has Tor amplitude in `[a, b]`
over `C`. -/
theorem hasTorAmplitudeCanonical_restrictScalars_extendScalars_of_isLocalization
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (φ : R →+* A) (σ : A →+* B) (τ : R →+* C) (ψ : C →+* B) (hcomm : σ.comp φ = ψ.comp τ)
    (P : Submonoid A) (hσ : letI := σ.toAlgebra; IsLocalization P B)
    (Q : Submonoid R) (hτ : letI := τ.toAlgebra; IsLocalization Q C)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (h : HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
      ((CochainComplex.restrictScalars φ).obj M)) a b) :
    HasTorAmplitudeCanonical C (DerivedCategory.Q.obj
      ((CochainComplex.restrictScalars ψ).obj ((CochainComplex.extendScalars σ).obj M))) a b := by
  let : Algebra R A := φ.toAlgebra
  let : Algebra A B := σ.toAlgebra
  let : Algebra R B := (σ.comp φ).toAlgebra
  let : Algebra R C := τ.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat A B := IsLocalization.flat B P
  have h1 := hasTorAmplitude_restrictScalars_extendScalars_of_flat R A B M a b
    ((hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b).1 h)
  have h2 : HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
      ((CochainComplex.restrictScalars τ).obj ((CochainComplex.restrictScalars ψ).obj
        ((CochainComplex.extendScalars σ).obj M)))) a b :=
    BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp'.{u} τ ψ (σ.comp φ) hcomm) (ComplexShape.up ℤ)).app _))
      a b ((hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b).2 h1)
  exact (hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b).2
    (hasTorAmplitude_of_restrictScalars_isLocalization R C Q _ a b
      ((hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b).1 h2))

/-- The germ at `y ∈ U` after `f.appLE V U` is the germ at `f y ∈ V` followed by the stalk map. -/
theorem germ_comp_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hUV : U ≤ f ⁻¹ᵁ V) (y : X) (hy : y ∈ U) :
    (X.presheaf.germ U y hy).hom.comp (f.appLE V U hUV).hom =
      (f.stalkMap y).hom.comp
        (Y.presheaf.germ V (f.base y) (show f.base y ∈ V from hUV hy)).hom := by
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  symm
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

section Chart

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)

/-- Restriction of scalars along any ring homomorphism is additive. -/
local instance (priority := 10000) additive_restrictScalars_chart
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along any ring homomorphism preserves finite limits. -/
local instance (priority := 10000) preservesFiniteLimits_restrictScalars_chart
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars along any ring homomorphism preserves finite colimits. -/
local instance (priority := 10000) preservesFiniteColimits_restrictScalars_chart
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits φ

/-- Tor amplitude of the restriction of scalars of an object of the derived category can be read on
any complex representing it. -/
private theorem hasTorAmplitudeCanonical_restrictScalars_objPreimage_iff
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ) :
    HasTorAmplitudeCanonical R ((ModuleCat.restrictScalars φ).mapDerivedCategory.obj ω) a b ↔
      HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
        ((CochainComplex.restrictScalars φ).obj (DerivedCategory.Q.objPreimage ω))) a b :=
  let eR := (ModuleCat.restrictScalars φ).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso ω).symm ≪≫
    (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage ω)
  ⟨BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso eR a b,
    BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso eR.symm a b⟩

/-- **On a chart, a Tor bound of `f^!𝒪_Y` over the base ring passes to the derived stalks.** Let
`U ⊆ X` and `V ⊆ Y` be affine opens with `U ⊆ f⁻¹(V)` and let `E ∈ D(𝒪_X)` restrict on `U` to the
sheaf associated to `ω = φ^!(Γ(Y, V))` along a presentation of `φ = f.appLE V U`. If `ω` has Tor
amplitude in `[a, b]` over `Γ(Y, V)`, then the derived stalk of `E` at each `y ∈ U`, read over
`𝒪_{Y, f y}`, has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitudeCanonical_stalk_of_chart
    {U : X.left.Opens} (hU : IsAffineOpen U) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f.left ⁻¹ᵁ V) (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom)
    (E : DerivedCategory X.left.Modules)
    (he : letI := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E ≅
        (tilde.functor Γ(X.left, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
            (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))))
    (a b : ℤ)
    (hab : HasTorAmplitudeCanonical Γ(Y.left, V)
      ((ModuleCat.restrictScalars (f.left.appLE V U hUV).hom).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))) a b)
    (y : X.left) (hy : y ∈ U) :
    HasTorAmplitudeCanonical (Y.left.presheaf.stalk (f.left.base y))
      ((ModuleCat.restrictScalars (f.left.stalkMap y).hom).mapDerivedCategory.obj
        ((Stacks.Duality.modulesStalkFunctor y).mapDerivedCategory.obj E)) a b := by
  have hYn : IsLocallyNoetherian Y.left := by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Y.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hVn : IsNoetherianRing Γ(Y.left, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let φ := (f.left.appLE V U hUV).hom
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := φ.toAlgebra
  let ω := p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)
  let M := DerivedCategory.Q.objPreimage ω
  let eM : DerivedCategory.Q.obj M ≅ ω := DerivedCategory.Q.objObjPreimageIso ω
  have hab' := (hasTorAmplitudeCanonical_restrictScalars_objPreimage_iff φ ω a b).1 hab
  have hyV : f.left.base y ∈ V := hUV hy
  let := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme
  let E₀ := DerivedCategory.Q.objPreimage E
  let e₀ : DerivedCategory.Q.obj E₀ ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let g := affineGermRingHom hU y hy
  let : Algebra Γ(X.left, U) (X.left.presheaf.stalk y) := g.toAlgebra
  have hloc := isLocalization_affineGermRingHom hU y hy
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (X.left.presheaf.stalk y)
          (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl))
  obtain ⟨dS⟩ := nonempty_derivedStalkOfComplex_iso_extendScalars_anyModel E₀ ⟨e₀⟩ hU y hy ω he
  have hcomm : g.comp φ = (f.left.stalkMap y).hom.comp (Y.left.presheaf.germ V _ hyV).hom := by
    simpa only [g, affineGermRingHom_eq_germ] using germ_comp_appLE f.left hUV y hy
  have halg := hasTorAmplitudeCanonical_restrictScalars_extendScalars_of_isLocalization φ g
    (Y.left.presheaf.germ V _ hyV).hom (f.left.stalkMap y).hom hcomm _ hloc _
    (hV.isLocalization_stalk ⟨f.left.base y, hyV⟩) M a b hab'
  refine BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ?_ a b halg
  let res := ModuleCat.restrictScalars.{u} (f.left.stalkMap y).hom
  let ext := ModuleCat.extendScalars.{u, u, u} g
  exact (res.mapDerivedCategoryFactors.app _).symm ≪≫
    res.mapDerivedCategory.mapIso ((ext.mapDerivedCategoryFactors.app M).symm ≪≫
      ext.mapDerivedCategory.mapIso eM ≪≫ dS.symm ≪≫
      ((Stacks.Duality.modulesStalkFunctor y).mapDerivedCategoryFactors.app E₀).symm ≪≫
      (Stacks.Duality.modulesStalkFunctor y).mapDerivedCategory.mapIso e₀)

/-- **On a chart, the derived stalks of `f^!𝒪_Y` have bounded Tor amplitude over the base.** Let
`U ⊆ X` and `V ⊆ Y` be affine opens with `U ⊆ f⁻¹(V)` and let `E ∈ D(𝒪_X)` restrict on `U` to
the sheaf associated to `φ^!(Γ(Y, V))` along a presentation of `φ = f.appLE V U`. Then for some
interval `[a, b]`, and every larger one, the derived stalk of `E` at each `y ∈ U`, read over
`𝒪_{Y, f y}`, has Tor amplitude in that interval. -/
theorem exists_hasTorAmplitudeCanonical_stalk_of_chart [Perfect f.left]
    {U : X.left.Opens} (hU : IsAffineOpen U) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f.left ⁻¹ᵁ V) (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom)
    (E : DerivedCategory X.left.Modules)
    (he : letI := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E ≅
        (tilde.functor Γ(X.left, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
            (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)))) :
    ∃ a b : ℤ, ∀ a' b' : ℤ, a' ≤ a → b ≤ b' → ∀ y : X.left, y ∈ U →
      HasTorAmplitudeCanonical (Y.left.presheaf.stalk (f.left.base y))
        ((ModuleCat.restrictScalars (f.left.stalkMap y).hom).mapDerivedCategory.obj
          ((Stacks.Duality.modulesStalkFunctor y).mapDerivedCategory.obj E)) a' b' := by
  have hVn : IsNoetherianRing Γ(Y.left, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let φ := (f.left.appLE V U hUV).hom
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := φ.toAlgebra
  let ω := p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)
  let D : CertifiedDerivedTensoring.{u, u} Γ(Y.left, V) :=
    canonicalCertifiedDerivedTensoring Γ(Y.left, V)
  have htor :=
    p.relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap
      (R := Γ(Y.left, V)) (A := Γ(X.left, U)) D.tensor D.comparison D.isLeftDerived
      (AlgebraicGeometry.Perfect.perfect_appLE f.left U hU V hV hUV D)
  let M := DerivedCategory.Q.objPreimage ω
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars φ).obj M) a b := by
    obtain ⟨a, b, h⟩ :=
      (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).1
        ((AffineRelativeTorAmplitude.hasFiniteTorDimension_iff_hasFiniteTorDimensionCanonical
          _ _ _).1 htor)
    exact ⟨a, b,
      (AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b).1
        ((hasTorAmplitudeCanonical_restrictScalars_objPreimage_iff φ ω a b).1 h)⟩
  refine ⟨a, b, fun a' b' ha hb y hy => ?_⟩
  have hab' : FaithfullyFlat.HasTorAmplitude ((CochainComplex.restrictScalars φ).obj M) a' b' :=
    fun N i hi => hab N i (by omega)
  exact hasTorAmplitudeCanonical_stalk_of_chart f hU hV hUV p E he a' b'
    ((hasTorAmplitudeCanonical_restrictScalars_objPreimage_iff φ ω a' b').2
      ((AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a' b').2
        hab')) y hy

/-- The two spellings of the derived stalk of an object of `D(𝒪_X)` read over the local ring of
the base agree: Tor amplitude may be read through either. -/
theorem hasTorAmplitudeCanonical_stalk_base_of_modulesStalk {Z T : Scheme.{u}} (g : Z ⟶ T)
    (E : DerivedCategory Z.Modules) (y : Z) (a b : ℤ)
    (h : HasTorAmplitudeCanonical (T.presheaf.stalk (g.base y))
      ((ModuleCat.restrictScalars (g.stalkMap y).hom).mapDerivedCategory.obj
        ((Stacks.Duality.modulesStalkFunctor y).mapDerivedCategory.obj E)) a b) :
    HasTorAmplitudeCanonical (ToType (T.presheaf.stalk (g.base y)))
      ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv Z.presheaf y).symm.toRingHom.comp
            (g.stalkMap y).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (StrictlyPerfect.structureSheafOfRings.{u} Z.toRingedSpace) y).mapDerivedCategory.obj E))
      a b := by
  let E₀ := DerivedCategory.Q.objPreimage E
  let e₀ : DerivedCategory.Q.obj E₀ ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let st := AlgebraicGeometry.SheafOfModules.stalkFunctor
    (StrictlyPerfect.structureSheafOfRings.{u} Z.toRingedSpace) y
  let ψ := (g.stalkMap y).hom
  let ρ := (SemilinearStalk.commStalkRingEquiv Z.presheaf y).symm.toRingHom
  let rs₁ := ModuleCat.restrictScalars.{u} (ρ.comp ψ)
  let rs₂ := ModuleCat.restrictScalars.{u} ψ
  have : st.Additive := inferInstance
  have : rs₁.Additive := additive_restrictScalars_chart _
  have : rs₂.Additive := additive_restrictScalars_chart _
  let θ : st ⋙ rs₁ ≅ Stacks.Duality.modulesStalkFunctor y ⋙ rs₂ :=
    Functor.isoWhiskerLeft st (ModuleCat.restrictScalarsComp'.{u} ψ ρ (ρ.comp ψ) rfl)
  refine BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ?_ a b h
  exact rs₂.mapDerivedCategory.mapIso
      ((Stacks.Duality.modulesStalkFunctor y).mapDerivedCategory.mapIso e₀.symm ≪≫
        (Stacks.Duality.modulesStalkFunctor y).mapDerivedCategoryFactors.app E₀) ≪≫
    rs₂.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
      (fun i => θ.app (E₀.X i)) (fun i j _ => (θ.hom.naturality (E₀.d i j)).symm)).symm ≪≫
    (rs₁.mapDerivedCategoryFactors.app _).symm ≪≫
    rs₁.mapDerivedCategory.mapIso ((st.mapDerivedCategoryFactors.app E₀).symm ≪≫
      st.mapDerivedCategory.mapIso e₀)

/-- A morphism of `FTS S` over a Noetherian base is locally of finite presentation: it is locally
of finite type, since its composite with the separated structure morphism of the target is, and its
target is locally Noetherian. -/
theorem locallyOfFinitePresentation_left : LocallyOfFinitePresentation f.left :=
  inferInstance

/-- **The Tor conjunct of `Y`-perfectness of `f^!𝒪_Y`.** For `f` perfect, an object `ω` of `D(𝒪_X)`
with the affine-chart description of `f^!𝒪_Y` locally has finite Tor dimension over
`f^{-1}𝒪_Y`, at the genuine derived tensor product of each open subspace. -/
theorem locallyHasFiniteTorDimension_of_isShriekOfStructureSheafOnCharts [Perfect f.left]
    (ω : quasiCoherentDerivedCategory.{u + 1, u} X.left)
    (hw : IsShriekOfStructureSheafOnCharts f ω.obj) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage Y.left.toRingedSpace f.left.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction f.left).obj ω.obj) := by
  refine
    Scheme.Hom.locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_base_bound
      f.left _ (Scheme.Hom.isGenuineRelativeTensorFamily_canonical f.left) ω.obj ?_
  choose U hU V hV hUV hxU p he using hw
  choose a b hab using fun x => exists_hasTorAmplitudeCanonical_stalk_of_chart f (hU x) (hV x)
    (hUV x) (p x) ω.obj (he x)
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X.left)).elim_finite_subcover
      (fun x : X.left => (U x : Set X.left)) (fun x => (U x).isOpen)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨-∑ x ∈ t, |a x|, ∑ x ∈ t, |b x|, fun y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  have ha : -∑ x ∈ t, |a x| ≤ a x := by
    have := Finset.single_le_sum (f := fun x => |a x|) (fun _ _ => abs_nonneg _) hxt
    have := neg_abs_le (a x)
    omega
  have hb : b x ≤ ∑ x ∈ t, |b x| := by
    have := Finset.single_le_sum (f := fun x => |b x|) (fun _ _ => abs_nonneg _) hxt
    have := le_abs_self (b x)
    omega
  exact hasTorAmplitudeCanonical_stalk_base_of_modulesStalk f.left ω.obj y _ _
    (hab x _ _ ha hb y hyx)

/-- **`f^!𝒪_Y` is perfect relative to `Y`**, read on its affine-chart description: for `f` flat,
an object `ω` of `D(𝒪_X)` with the chart description of `f^!𝒪_Y` is pseudo-coherent and locally
has finite Tor dimension over `f^{-1}𝒪_Y`, at the genuine derived tensor product. -/
theorem isPerfectRelativeTo_of_isShriekOfStructureSheafOnCharts [Flat f.left]
    (ω : quasiCoherentDerivedCategory.{u + 1, u} X.left)
    (hw : IsShriekOfStructureSheafOnCharts f ω.obj) :
    letI := locallyOfFinitePresentation_left f
    f.left.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ω.obj :=
  let := locallyOfFinitePresentation_left f
  ⟨isPseudoCoherent_of_isShriekOfStructureSheafOnCharts f ω hw,
    locallyHasFiniteTorDimension_of_isShriekOfStructureSheafOnCharts f ω hw⟩

end Chart

end Stacks.Duality
