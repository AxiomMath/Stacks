module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPullback
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedTildeOverRing
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion

/-!
# The derived décalage of a triple on an affine chart

Let `(X, D, M)` be a triple as in Situation 0F8S and let `(U, A, f, M^•)` be an affine chart for
it.  This file computes the derived décalage `Lη_I M` of [Stacks, Tag 0F8Q] on the chart: its
derived pullback to `Spec A` is the sheaf associated with the décalage `η_f M^•` of the chart
complex (More on Algebra, Tag 0F7N).  When the determinantal ideals of the chart are principal,
`η_f M^•` is a bounded complex of finite projective modules (Tag 0F7W), hence K-flat, and the
computation propagates along an arbitrary morphism `h : Y ⟶ X`: over an affine open
`V = Spec B ⊆ Y` lying over `U`, the restriction of `Lh^*(Lη_I M)` is the sheaf associated with
`η_f M^• ⊗_A B`, and so are its cohomology sheaves.  This is what parts (2) and (3) of More on
Flatness, Tag 0GTZ need: there `h` is the closed immersion `T ⟶ D ⟶ X`.

## Main results

All in the namespace `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart`.

* `nonempty_derivedPullbackObject_fromSpec_iso`: the derived pullback of `M` to `Spec A` is the
  sheafified chart complex.
* `nonempty_derivedPullback_fromSpec_derivedEta_iso`: the derived pullback of `Lη_I M` to
  `Spec A` is the sheafified décalage `(η_f M^•)^~`.  This is Stacks 0F9X for the flat morphism
  `Spec A ⟶ X` followed by the second assertion of Stacks 0GTV, read over `A`
  (`Stacks.Divisors.Eta.nonempty_derivedEta_tilde_iso`).
* `kFlat_etaObject`: the décalage of a chart with principal determinantal ideals is K-flat.
* `nonempty_restrict_derivedPullback_derivedEta_iso` and
  `nonempty_restrict_homology_derivedPullback_derivedEta_iso`: the restriction of `Lh^*(Lη_I M)`,
  and of its cohomology sheaves, to an affine open over a chart with principal determinantal
  ideals.

## Implementation notes

The derived pullback and the derived décalage of this library are constructed at the standard
models of the derived categories (`CategoryTheory.HasDerivedCategory.standard`), so the
statements here install those models by `letI`; the local macro `std_models` does so inside the
proofs, at the three spellings `Scheme.Modules`, `StrictlyPerfect.OXMod` and
`SheafOfModules (structureSheafRing _)` of the category of modules on a scheme.  The object `M` of
the triple lives at an arbitrary model and is transported to the standard one as
`ComplexAndDivisorSituation.standardObject`.

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u d

/-- Installs the standard models of the derived categories of modules on a scheme, at the three
spellings `Scheme.Modules`, `StrictlyPerfect.OXMod` and `SheafOfModules (structureSheafRing _)` of
its category of modules, as local instances.  The derived pullback and the derived décalage of
this library are compared at these models. -/
local macro "std_models " X:term : tactic => `(tactic| (
  let := HasDerivedCategory.standard (AlgebraicGeometry.Scheme.Modules $X)
  let := HasDerivedCategory.standard (StrictlyPerfect.OXMod.{_, _}
    (($X : AlgebraicGeometry.Scheme).toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{_}
    (structureSheafRing (($X : AlgebraicGeometry.Scheme).toRingedSpace)))))

namespace AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- **The pullback of the object of a triple to the spectrum of a chart is the sheafified chart
complex.**  Along `Spec Γ(X, U) ⟶ X`, the derived pullback of `M` is derived sheafification of
the chart complex `M^•`. -/
theorem nonempty_derivedPullbackObject_fromSpec_iso (C : AffineChart S) :
    letI := HasDerivedCategory.standard (Spec Γ(S.X, C.U)).Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, C.U))
    Nonempty (S.derivedPullbackObject C.U.2.fromSpec ≅
      (tilde.functor Γ(S.X, C.U)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj C.complex.toCochainComplex)) := by
  std_models (Spec Γ(S.X, C.U))
  std_models C.U.1.toScheme
  std_models S.X
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, C.U))
  obtain ⟨E₀, ⟨hE₀⟩, ⟨e⟩⟩ := C.represents
  have uniqIso : S.standardObject ≅ DerivedCategory.Q.obj E₀ :=
    (Localization.uniq
        (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
          (OXMod.{u, u} S.X.toRingedSpace)))
        (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
          (ComplexShape.up ℤ))).functor.mapIso hE₀.symm ≪≫
      (Localization.compUniqFunctor
        (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
          (OXMod.{u, u} S.X.toRingedSpace)))
        (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
          (ComplexShape.up ℤ))).app E₀
  have e' : (Scheme.Modules.restrictFunctor C.U.1.ι).mapDerivedCategory.obj
      (DerivedCategory.Q.obj E₀) ≅
      (tilde.functor Γ(S.X, C.U) ⋙
        Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapDerivedCategory.obj
          (DerivedCategory.Q.obj C.complex.toCochainComplex) :=
    (Scheme.Modules.restrictFunctor C.U.1.ι).mapDerivedCategoryFactors.app E₀ ≪≫ e ≪≫
      ((tilde.functor Γ(S.X, C.U) ⋙
        Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapDerivedCategoryFactors.app
          C.complex.toCochainComplex).symm
  exact ⟨(derivedPullback C.U.2.fromSpec.toLRSHom.toShHom).mapIso uniqIso ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      C.U.2.isoSpec.inv.toLRSHom.toShHom C.U.1.ι.toLRSHom.toShHom).app _).symm ≪≫
    (derivedPullback C.U.2.isoSpec.inv.toLRSHom.toShHom).mapIso
      (((Scheme.Modules.derivedRestrictIsoDerivedPullback C.U.1.ι).app _).symm ≪≫ e') ≪≫
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback C.U.2.isoSpec.inv).app _).symm ≪≫
    (Stacks.AffineTilde.tildeIsoSpecCancelIso C.U.2).app _⟩

/-- The ring map of `Spec Γ(X, U) ⟶ X` from the sections over `U` to the global functions on
`Spec Γ(X, U)` is the inverse of `Γ(Spec A, ⊤) ≅ A`. -/
theorem fromSpec_appLE_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

/-- The pulled-back divisor on the spectrum of a chart is cut out by the chart's equation, read
in the global functions of the spectrum. -/
theorem ideal_comap_fromSpec_top (C : AffineChart S) :
    (S.D.comap C.U.2.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso Γ(S.X, C.U)).inv C.f} := by
  have h : ((⟨⊤, isAffineOpen_top _⟩ : (Spec Γ(S.X, C.U)).affineOpens) :
      (Spec Γ(S.X, C.U)).Opens) ≤ C.U.2.fromSpec ⁻¹ᵁ (C.U : S.X.Opens) := by
    rw [C.U.2.fromSpec_preimage_self]
  rw [Stacks.IdealSheaf.ideal_comap_appLE S.D C.U.2.fromSpec C.U _ h, C.divisor_ideal,
    Ideal.map_span, Set.image_singleton]
  exact congrArg (fun φ => Ideal.span {φ.hom C.f}) (fromSpec_appLE_top C.U.2 h)

/-- **The derived décalage of a triple, pulled back to the spectrum of an affine chart.**  For an
affine chart `(U, A, f, M^•)` of a triple as in Situation 0F8S, the derived pullback of
`Lη_I M` along `Spec A ⟶ X` is the sheafified décalage `(η_f M^•)^~`.

Pulling back along the open immersion `Spec A ⟶ X` commutes with the derived décalage (Stacks
0F9X for a flat morphism, `ComplexAndDivisorSituation.derivedEtaPullbackIso`); the pullback of `M`
is the sheafified chart complex (`nonempty_derivedPullbackObject_fromSpec_iso`); and on `Spec A`
the derived décalage of a sheafified complex of `f`-torsion-free modules is the sheafified décalage
(the second assertion of Stacks 0GTV, `Stacks.Divisors.Eta.nonempty_derivedEta_tilde_iso`). No
principality of the determinantal ideals is needed. -/
theorem nonempty_derivedPullback_fromSpec_derivedEta_iso (C : AffineChart S) :
    haveI := S.isEffectiveCartierDivisor
    letI := HasDerivedCategory.standard (Spec Γ(S.X, C.U)).Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, C.U))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing (Spec Γ(S.X, C.U)).toRingedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace))
    letI := HasDerivedCategory.standard S.X.Modules
    Nonempty ((derivedPullback C.U.2.fromSpec.toLRSHom.toShHom).obj
        ((Stacks.Divisors.Eta.derivedEtaData S.D).functor.obj S.standardObject) ≅
      (tilde.functor Γ(S.X, C.U)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (EtaComplex.etaObject C.f C.complex.toCochainComplex))) := by
  have := S.isEffectiveCartierDivisor
  std_models (Spec Γ(S.X, C.U))
  std_models S.X
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, C.U))
  have : IsOpenImmersion C.U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec C.U.2
  have : AlgebraicGeometry.Flat C.U.2.fromSpec := inferInstance
  have hD : Stacks.Divisors.IsPullbackDefined C.U.2.fromSpec S.D :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ S.isEffectiveCartierDivisor
  obtain ⟨K, ⟨hK⟩⟩ := Stacks.Divisors.Eta.exists_torsionFreeComplex_iso S.D S.standardObject
  obtain ⟨eA⟩ := C.nonempty_derivedPullbackObject_fromSpec_iso
  obtain ⟨eB⟩ := Stacks.Divisors.Eta.nonempty_derivedEta_tilde_iso Γ(S.X, C.U)
    (S.D.comap C.U.2.fromSpec) C.f C.ideal_comap_fromSpec_top C.complex.toCochainComplex
    (fun n => by
      change IsSMulRegular (Fin (C.complex.rank n) → Γ(S.X, C.U)) C.f
      exact Module.Flat.isSMulRegular_of_isRegular C.regular)
  exact ⟨S.derivedEtaPullbackIso C.U.2.fromSpec K hK ≪≫
    (Stacks.Divisors.Eta.derivedEtaData (S.D.comap C.U.2.fromSpec)).functor.mapIso eA ≪≫ eB⟩

/-- The décalage of the complex of a chart with principal determinantal ideals is K-flat: it is
bounded above, the chart's complex being bounded, and its terms are finite projective
(Tag 0F7W). -/
theorem kFlat_etaObject (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) :
    CochainComplex.KFlat.{u, u} (EtaComplex.etaObject C.f C.complex.toCochainComplex) := by
  obtain ⟨b, hb⟩ := C.complex.bounded.bddAbove
  have : (EtaComplex.etaObject C.f C.complex.toCochainComplex).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    refine C.isZero_etaComplex_X ?_
    by_contra h
    exact (not_le_of_gt hi) (hb h)
  have hflat : ∀ n : ℤ, Module.Flat Γ(S.X, C.U)
      ((EtaComplex.etaObject C.f C.complex.toCochainComplex).X n) := fun n => by
    obtain ⟨_, hproj⟩ := C.finite_projective_etaComplex_X hI n
    exact @Module.Flat.of_projective _ _ _ _ _ hproj
  exact CochainComplex.KFlat.kFlat_of_flat _ b

/-- A morphism restricted to an affine open lying over the affine open of a chart factors through
the spectrum of the chart: `V ⟶ Y ⟶ X` is `V ≅ Spec Γ(Y, V) ⟶ Spec Γ(X, U) ⟶ X`. -/
theorem ι_comp_eq_isoSpec_hom_comp {X Y : Scheme.{u}} (h : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (U : X.Opens)) :
    V.1.ι ≫ h = V.2.isoSpec.hom ≫ Spec.map (h.appLE U V hV) ≫ U.2.fromSpec := by
  have hvm : h.resLE U V hV ≫ U.2.isoSpec.hom = V.2.isoSpec.hom ≫ Spec.map (h.appLE U V hV) :=
    (Scheme.Opens.toSpecΓ_SpecMap_appLE h (U : X.Opens) (V : Y.Opens) hV).symm
  rw [← Scheme.Hom.resLE_comp_ι h hV, ← IsAffineOpen.isoSpec_hom_fromSpec U.2, reassoc_of% hvm]

/-- **The derived décalage of a triple, pulled back along a morphism and restricted to an affine
open over a good chart.**  Let `(U, A, f, M^•)` be an affine chart with principal determinantal
ideals, let `h : Y ⟶ X` be any morphism of schemes and `V = Spec B ⊆ Y` an affine open with
`h(V) ⊆ U`.  Then the restriction to `V` of `Lh^*(Lη_I M)` is the sheaf of modules associated
with the base change `η_f M^• ⊗_A B` of the décalage of the chart complex.

The morphism `V ⟶ X` factors through `Spec A`, where the derived décalage is the sheafified
décalage (`nonempty_derivedPullback_fromSpec_derivedEta_iso`); the décalage is a K-flat complex
(`kFlat_etaObject`), so its derived pullback along `Spec B ⟶ Spec A` is the termwise one, which
is the sheafified base change (`tildePullbackComplexIso`). -/
theorem nonempty_restrict_derivedPullback_derivedEta_iso (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)) :
    haveI := S.isEffectiveCartierDivisor
    letI := HasDerivedCategory.standard S.X.Modules
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    letI := HasDerivedCategory.standard Y.Modules
    letI := HasDerivedCategory.standard V.1.toScheme.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y, V))
    Nonempty ((Scheme.Modules.restrictFunctor V.1.ι).mapDerivedCategory.obj
        ((derivedPullback h.toLRSHom.toShHom).obj
          ((Stacks.Divisors.Eta.derivedEtaData S.D).functor.obj S.standardObject)) ≅
      (tilde.functor Γ(Y, V) ⋙
          Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars (h.appLE C.U V hV).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (EtaComplex.etaObject C.f C.complex.toCochainComplex)))) := by
  have := S.isEffectiveCartierDivisor
  std_models S.X
  std_models Y
  std_models V.1.toScheme
  std_models (Spec Γ(S.X, C.U))
  std_models (Spec Γ(Y, V))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, C.U))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y, V))
  let φ := h.appLE C.U V hV
  let p : Spec Γ(Y, V) ⟶ Spec Γ(S.X, C.U) := Spec.map φ
  let P := EtaComplex.etaObject C.f C.complex.toCochainComplex
  let K := ((tilde.functor Γ(S.X, C.U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex
      (Spec Γ(S.X, C.U)).toRingedSpace K :=
    Stacks.TildeStalk.kFlatComplex_tilde _ P (C.kFlat_etaObject hI)
  obtain ⟨eCE⟩ := C.nonempty_derivedPullback_fromSpec_derivedEta_iso
  have hfac' : V.1.ι.toLRSHom.toShHom ≫ h.toLRSHom.toShHom =
      V.2.isoSpec.hom.toLRSHom.toShHom ≫ (p.toLRSHom.toShHom ≫
        C.U.2.fromSpec.toLRSHom.toShHom) := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      congrArg (fun k : V.1.toScheme ⟶ S.X => k.toLRSHom.toShHom)
        (ι_comp_eq_isoSpec_hom_comp h C.U V hV)
  have a₃ : ((Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((tilde.functor Γ(Y, V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≅
      (((tilde.functor Γ(Y, V) ⋙
          Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor V.2.isoSpec.hom))
      (ComplexShape.up ℤ)).app _
  exact ⟨(Scheme.Modules.derivedRestrictIsoDerivedPullback V.1.ι).app _ ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      V.1.ι.toLRSHom.toShHom h.toLRSHom.toShHom).app _ ≪≫
    eqToIso (congrArg (fun k : V.1.toScheme.toRingedSpace ⟶ S.X.toRingedSpace =>
      (derivedPullback k).obj
        ((Stacks.Divisors.Eta.derivedEtaData S.D).functor.obj S.standardObject)) hfac') ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      V.2.isoSpec.hom.toLRSHom.toShHom
        (p.toLRSHom.toShHom ≫ C.U.2.fromSpec.toLRSHom.toShHom)).app _).symm ≪≫
    (derivedPullback V.2.isoSpec.hom.toLRSHom.toShHom).mapIso
      (((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        p.toLRSHom.toShHom C.U.2.fromSpec.toLRSHom.toShHom).app _).symm ≪≫
      (derivedPullback p.toLRSHom.toShHom).mapIso
        (eCE ≪≫ (tilde.functor Γ(S.X, C.U)).mapDerivedCategoryFactors.app P) ≪≫
      Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat p.toLRSHom.toShHom K hK ≪≫
      DerivedCategory.Q.mapIso ((tildePullbackComplexIso Γ(S.X, C.U) Γ(Y, V) φ).app P)) ≪≫
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback V.2.isoSpec.hom).app _).symm ≪≫
    (Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso a₃ ≪≫
    ((tilde.functor Γ(Y, V) ⋙
      Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapDerivedCategoryFactors.app _).symm⟩

/-- **The cohomology sheaves of `Lh^*(Lη_I M)` over an affine open lying over a good chart.**
With the notation of `nonempty_restrict_derivedPullback_derivedEta_iso`, the restriction to `V`
of the `n`-th cohomology sheaf of `Lh^*(Lη_I M)` is the sheaf of modules associated with the
`n`-th cohomology module of `η_f M^• ⊗_A B`: restriction to an open and sheafification are exact,
so they commute with cohomology. -/
theorem nonempty_restrict_homology_derivedPullback_derivedEta_iso (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)) (n : ℤ) :
    haveI := S.isEffectiveCartierDivisor
    letI := HasDerivedCategory.standard S.X.Modules
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    letI := HasDerivedCategory.standard Y.Modules
    Nonempty ((Scheme.Modules.restrictFunctor V.1.ι).obj
        ((DerivedCategory.homologyFunctor Y.Modules n).obj
          ((derivedPullback h.toLRSHom.toShHom).obj
            ((Stacks.Divisors.Eta.derivedEtaData S.D).functor.obj S.standardObject))) ≅
      (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor V.2.isoSpec.hom).obj
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} Γ(Y, V)) (ComplexShape.up ℤ) n).obj
          (((ModuleCat.extendScalars (h.appLE C.U V hV).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (EtaComplex.etaObject C.f C.complex.toCochainComplex)))) := by
  have := S.isEffectiveCartierDivisor
  std_models S.X
  std_models Y
  std_models V.1.toScheme
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y, V))
  obtain ⟨e⟩ := C.nonempty_restrict_derivedPullback_derivedEta_iso hI h V hV
  exact ⟨(((Scheme.Modules.restrictFunctor V.1.ι).mapDerivedCategoryHomologyIso n).app _).symm ≪≫
    (DerivedCategory.homologyFunctor V.1.toScheme.Modules n).mapIso e ≪≫
    ((tilde.functor Γ(Y, V) ⋙
      Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapDerivedCategoryHomologyIso n).app _ ≪≫
    (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapIso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} Γ(Y, V)) n).app _)⟩

end AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart

end
