module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.RingTheory.GeometricallyIntegral.FibreLocusSchemeBridge
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# The hypotheses of the affine-chart form of Tag 0810, supplied from geometry

`Stacks.StrictTransform.exists_fg_ideal_forall_chartFreeOfRank` is the scheme-level reading of
[Stacks, Tag 0810], but its hypotheses are stated on the two rings of global sections: `Γ(X, ⊤)`
is asked to be flat and of finite presentation over `Γ(S, ⊤)`, its fibre algebras to be
geometrically integral, the module `M` to be finite and finitely presented after inverting an
element, and the presentation `F ≅ M^~` to be given. This file supplies each of those from the
corresponding property of the morphism `f : X ⟶ S` or of the module `F` on `X`, for `X` and `S`
affine. Nothing here is a statement about blowups: each result is one translation step, and they
are independent of each other.

## Main results

* `Stacks.StrictTransform.module_flat_of_flat`: flatness of `f` gives flatness of `Γ(X, ⊤)` over
  `Γ(S, ⊤)`.
* `Stacks.StrictTransform.algebra_finitePresentation_of_finitePresentation`: finite presentation
  of `f` gives finite presentation of the algebra `Γ(X, ⊤)`.
* `Stacks.StrictTransform.isGeometricallyIntegral_fiber_of_geometricallyIntegral`: geometric
  integrality of `f` gives geometric integrality of every fibre algebra `q.Fiber Γ(X, ⊤)` over
  the residue field `κ(q)`.
* `Stacks.StrictTransform.exists_moduleCat_finite_iso_tilde`: a quasi-coherent module of finite
  type on an affine scheme is `M^~` for a finite module `M` of global sections.
* `Stacks.StrictTransform.finitePresentation_localizedModule_away_of_preimage_basicOpen`: finite
  presentation of `F` on `f⁻¹(D(t))` gives finite presentation of `M` after inverting the image
  of `t`.

## Implementation notes

(a) and (b) are the `HasRingHomProperty` lemmas `AlgebraicGeometry.Scheme.Hom.flat_appTop` and
`AlgebraicGeometry.Scheme.Hom.finitePresentation_appTop` read through
`RingHom.flat_algebraMap_iff` and `RingHom.finitePresentation_algebraMap`; the hypothesis `halg`
says the ambient algebra structure is the one `f` induces, exactly as
`exists_fg_ideal_forall_chartFreeOfRank` asks.

(c) is `AlgebraicGeometry.geometricallyIntegral_fiberToSpecResidueField_iff` preceded by two
transports: `f` is isomorphic as an arrow to `Spec Γ(f)` by
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality`, and `GeometricallyIntegral` respects
isomorphisms because it is stable under base change; the passage to the fibre is the base change
of `f` along `Spec κ(q) ⟶ S`.

(d) is the finite-type analogue of
`Stacks.AlgebraicGeometry.AffineTilde.exists_iso_tildeOf`: the module is `Γ` of the pullback of
`F` to `Spec Γ(X, ⊤)`, which is `M^~` because that pullback is quasi-coherent, and finiteness is
`AlgebraicGeometry.tilde_isFiniteType_iff`.

(e) is stated with the geometric hypothesis in the form
`((Scheme.Modules.pullback (f ⁻¹ᵁ S.basicOpen t).ι).obj F).IsFinitePresentation`, i.e. finite
presentation of the pullback of `F` along the open immersion of the preimage of `D(t)`. The
preimage is the basic open of `f^♯ t` (`AlgebraicGeometry.Scheme.preimage_basicOpen_top`); the
statement is carried to `Spec Γ(X, ⊤)` along `AlgebraicGeometry.Scheme.isoSpec`, where the open
becomes `PrimeSpectrum.basicOpen (f^♯ t)` and the module becomes `M^~`, and there the sections are
the away-localization: `Mathlib`'s instance `IsLocalizedModule.Away` for
`AlgebraicGeometry.tilde.toOpen` together with `IsLocalization.Away` for the structure sheaf turn
finite presentation of the sections into finite presentation of `LocalizedModule`. The last step
is `Stacks.StrictTransform.finitePresentation_localizedModule_of_isLocalizedModule`, a statement
about rings alone.

The rank hypothesis `hrank` of `exists_fg_ideal_forall_chartFreeOfRank` is *not* supplied here.
Deducing it from the geometric statement that `Scheme.Modules.fiberRank F b = r` at the generic
points of the fibres over `D(t)` needs a bridge this file does not build: for the point `b` of
`X` corresponding to the prime `q·Γ(X, ⊤)`, the simultaneous identification of the local ring
`X.presheaf.stalk b` with `Localization (q·Γ(X, ⊤)).primeCompl` and of the stalk of `F` at `b`
with `LocalizedModule (q·Γ(X, ⊤)).primeCompl M`, transported along
`AlgebraicGeometry.Scheme.isoSpec` and the presentation `F ≅ M^~`. `Scheme.Modules.fiberRank` is
a `Module.finrank` of a residue-field base change of that stalk, so without the transport there
is nothing to compare the rank `r` to. The remaining steps are available: that `q·Γ(X, ⊤)` lies
over `q` and is the generic point of the fibre comes from faithful flatness together with the
integrality of the fibre, and freeness of the stalk from flatness plus finite presentation over
a local ring (`Module.free_of_flat_of_isLocalRing`, as in
`AlgebraicGeometry.Scheme.Modules.exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk`).

## References

* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.StrictTransform

variable {X S : Scheme.{u}}

/-- On affine schemes a flat morphism induces a flat ring map on global sections. -/
public theorem module_flat_of_flat [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [AlgebraicGeometry.Flat f] [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : (algebraMap Γ(S, ⊤) Γ(X, ⊤) : Γ(S, ⊤) →+* Γ(X, ⊤)) = f.appTop.hom) :
    Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
  RingHom.flat_algebraMap_iff.mp (halg ▸ f.flat_appTop)

/-- On affine schemes a morphism of finite presentation induces a finitely presented algebra on
global sections. -/
public theorem algebra_finitePresentation_of_finitePresentation [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (hf : AlgebraicGeometry.FinitePresentation f) [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : (algebraMap Γ(S, ⊤) Γ(X, ⊤) : Γ(S, ⊤) →+* Γ(X, ⊤)) = f.appTop.hom) :
    Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) := by
  have := hf.locallyOfFinitePresentation
  exact RingHom.finitePresentation_algebraMap.mp
    (halg ▸ AlgebraicGeometry.Scheme.Hom.finitePresentation_appTop f)

/-- Geometric integrality passes from a morphism of affine schemes to the spectrum of the ring
map it induces on global sections: the two are isomorphic as arrows, and the property respects
isomorphisms because it is stable under base change. -/
public theorem geometricallyIntegral_specMap_appTop [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [AlgebraicGeometry.GeometricallyIntegral f] :
    AlgebraicGeometry.GeometricallyIntegral (Spec.map f.appTop) :=
  have : MorphismProperty.RespectsIso (@AlgebraicGeometry.GeometricallyIntegral) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk X.isoSpec S.isoSpec (Scheme.isoSpec_hom_naturality f))).mp ‹_›

/-- Geometric integrality of a morphism of affine schemes gives geometric integrality of every
fibre algebra. -/
public theorem isGeometricallyIntegral_fiber_of_geometricallyIntegral [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [AlgebraicGeometry.GeometricallyIntegral f] [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : (algebraMap Γ(S, ⊤) Γ(X, ⊤) : Γ(S, ⊤) →+* Γ(X, ⊤)) = f.appTop.hom)
    (q : Ideal Γ(S, ⊤)) (hq : q.IsPrime) :
    letI := hq
    Algebra.IsGeometricallyIntegral q.ResidueField (q.Fiber Γ(X, ⊤)) := by
  have hspec : AlgebraicGeometry.GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)))) := by
    rw [halg, CommRingCat.ofHom_hom]
    exact geometricallyIntegral_specMap_appTop f
  exact (AlgebraicGeometry.geometricallyIntegral_fiberToSpecResidueField_iff
    Γ(S, ⊤) Γ(X, ⊤) ⟨q, hq⟩).mp <| MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ _) hspec

/-- An isomorphism `G ≅ e⁻¹ᵃ F` of sheaves of modules gives `e_* G ≅ F`, for `e` an isomorphism of
schemes, where `e⁻¹ᵃ` and `e_*` are the pullbacks along `e.inv` and `e.hom`. -/
private def pullbackIsoOfIsoInv {Y Z : Scheme.{u}} (e : Y ≅ Z) {F : Y.Modules} {G : Z.Modules}
    (ε : G ≅ (Scheme.Modules.pullback e.inv).obj F) : (Scheme.Modules.pullback e.hom).obj G ≅ F :=
  (Scheme.Modules.pullback e.hom).mapIso ε ≪≫ (Scheme.Modules.pullbackComp e.hom e.inv).app F ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app F ≪≫ (Scheme.Modules.pullbackId Y).app F

/-- **Every quasi-coherent module of finite type on an affine scheme is `M^~`** for a finite
module `M` of global sections. -/
public theorem exists_moduleCat_finite_iso_tilde {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ M : ModuleCat.{u} Γ(X, ⊤), Module.Finite Γ(X, ⊤) M ∧
      Nonempty (F ≅ (Scheme.Modules.pullback X.isoSpec.hom).obj (tilde M)) := by
  let F' : (Spec Γ(X, ⊤)).Modules := (Scheme.Modules.pullback X.isoSpec.inv).obj F
  have hqc : F'.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback X.isoSpec.inv F
  have hft : F'.IsFiniteType :=
    @AlgebraicGeometry.SheafOfModules.pullback_isFiniteType _ _
      (Scheme.Hom.toLRSHom X.isoSpec.inv).toShHom F ‹_›
  let M : ModuleCat.{u} Γ(X, ⊤) := moduleSpecΓFunctor.obj F'
  let eF' : tilde M ≅ F' := @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ F')
    (@Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ F' hqc)
  have : (tilde M).IsFiniteType := Stacks.SheafOfModules.isFiniteType_of_iso.{u} eF'.symm
  exact ⟨M, (tilde_isFiniteType_iff M).mp ‹_›,
    ⟨(pullbackIsoOfIsoInv X.isoSpec eF').symm⟩⟩

/-- Finite presentation of a sheaf of modules on a scheme is invariant under isomorphism, with
the hypothesis supplied explicitly rather than by instance search. -/
public theorem isFinitePresentation_of_iso {Y : Scheme.{u}} {A B : Y.Modules} (ε : A ≅ B)
    (h : A.IsFinitePresentation) : B.IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso ε h

/-- The inverse image under `X ≅ Spec Γ(X, ⊤)` of the basic open of `g` on `X` is the basic open
of `g` on the spectrum. -/
public theorem isoSpec_inv_preimage_basicOpen {X : Scheme.{u}} [IsAffine X] (g : Γ(X, ⊤)) :
    X.isoSpec.inv ⁻¹ᵁ X.basicOpen g = PrimeSpectrum.basicOpen g := by
  have key : ∀ P : (Spec Γ(X, ⊤)).Opens, X.isoSpec.inv ⁻¹ᵁ (X.isoSpec.hom ⁻¹ᵁ P) = P :=
    fun P ↦ by simp [← Scheme.Hom.comp_preimage]
  exact (congrArg (X.isoSpec.inv ⁻¹ᵁ ·)
    (Scheme.map_PrimeSpectrum_basicOpen_of_affine X g)).symm.trans (key _)

/-- **Finite presentation of a quasi-coherent module on a basic open, read on the spectrum.**
If `F ≅ M^~` and `F` is finitely presented on the basic open of `g` in `X`, then `M^~` is
finitely presented on the basic open of `g` in `Spec Γ(X, ⊤)`. -/
public theorem isFinitePresentation_pullback_tilde_basicOpen {X : Scheme.{u}} [IsAffine X]
    (F : X.Modules) (M : ModuleCat.{u} Γ(X, ⊤))
    (ε : F ≅ (Scheme.Modules.pullback X.isoSpec.hom).obj (tilde M)) (g : Γ(X, ⊤))
    (hfp : ((Scheme.Modules.pullback (X.basicOpen g).ι).obj F).IsFinitePresentation) :
    ((Scheme.Modules.pullback (X.isoSpec.inv ⁻¹ᵁ X.basicOpen g).ι).obj
      (tilde M)).IsFinitePresentation := by
  set V : (Spec Γ(X, ⊤)).Opens := X.isoSpec.inv ⁻¹ᵁ X.basicOpen g
  have hk : (X.isoSpec.inv.resLE (X.basicOpen g) V le_rfl) ≫ (X.basicOpen g).ι
      = V.ι ≫ X.isoSpec.inv := Scheme.Hom.resLE_comp_ι _ _
  have h1 : ((Scheme.Modules.pullback (V.ι ≫ X.isoSpec.inv)).obj F).IsFinitePresentation := by
    rw [← hk]
    exact isFinitePresentation_of_iso
      ((Scheme.Modules.pullbackComp (X.isoSpec.inv.resLE (X.basicOpen g) V le_rfl)
        (X.basicOpen g).ι).app F)
      (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ _)
  let eInv : (Scheme.Modules.pullback X.isoSpec.inv).obj F ≅ tilde M :=
    pullbackIsoOfIsoInv X.isoSpec.symm ε
  exact isFinitePresentation_of_iso
    (((Scheme.Modules.pullbackComp V.ι X.isoSpec.inv).app F).symm ≪≫
      (Scheme.Modules.pullback V.ι).mapIso eInv) h1

/-- **A module is finitely presented over a localization as soon as some realization of its
localization is.** If `A` is a localization of `P` at `T` and `N` is a localization of `N₀` at
`T`, then finite presentation of `N` over `A` is finite presentation of `LocalizedModule T N₀`
over `Localization T`. -/
public theorem finitePresentation_localizedModule_of_isLocalizedModule
    {P A N₀ N : Type*} [CommRing P] [CommRing A] [Algebra P A]
    [AddCommGroup N₀] [Module P N₀] [AddCommGroup N] [Module P N]
    [Module A N] (hsc : IsScalarTower P A N)
    (T : Submonoid P) [IsLocalization T A]
    (φ : N₀ →ₗ[P] N) (hφ : IsLocalizedModule T φ)
    [Module.FinitePresentation A N] :
    Module.FinitePresentation (Localization T) (LocalizedModule T N₀) := by
  let eA := IsLocalization.algEquiv T (Localization T) A
  let : Algebra (Localization T) A := eA.toRingHom.toAlgebra
  let : Module (Localization T) N := Module.compHom N eA.toRingHom
  have : IsScalarTower (Localization T) A N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower P (Localization T) N :=
    IsScalarTower.of_algebraMap_smul fun r m ↦ by
      change eA (algebraMap P (Localization T) r) • m = r • m
      rw [eA.commutes, algebraMap_smul]
  have : Module.FinitePresentation (Localization T) A :=
    Module.FinitePresentation.of_equiv
      (LinearEquiv.ofBijective (Algebra.linearMap (Localization T) A) eA.bijective)
  have : Module.FinitePresentation (Localization T) N :=
    Module.FinitePresentation.trans (Localization T) N A
  exact Module.FinitePresentation.of_equiv
    ((IsLocalizedModule.iso T φ).extendScalarsOfIsLocalization T (Localization T)).symm

/-- **The away-localization of `M` is finitely presented as soon as `M^~` is finitely presented
on the basic open of `g`.** -/
public theorem finitePresentation_localizedModule_away_of_tilde {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (g : R) (W : (Spec R).Opens) (hW : W = PrimeSpectrum.basicOpen g)
    (hfp : ((Scheme.Modules.pullback W.ι).obj (tilde M)).IsFinitePresentation) :
    Module.FinitePresentation (Localization.Away g)
      (LocalizedModule (Submonoid.powers g) M) := by
  subst hW
  let D : (Spec R).affineOpens := ⟨PrimeSpectrum.basicOpen g, IsAffineOpen.Spec_basicOpen g⟩
  have hsec : Module.FinitePresentation Γ(Spec R, D.1) Γ(tilde M, D.1) :=
    Stacks.AlgebraicGeometry.FinitePresentationLocal.finitePresentation_sections_of_restrict
      (tilde M) D.2 (isFinitePresentation_of_iso
        ((Scheme.Modules.restrictFunctorIsoPullback D.1.ι).app (tilde M)).symm hfp)
  let : Algebra R Γ(Spec R, D.1) := by
    change Algebra R ((Spec.structureSheaf R).obj.obj (.op D.1))
    exact StructureSheaf.openAlgebra R _
  let : IsLocalization.Away g Γ(Spec R, D.1) := by
    change IsLocalization.Away g
      ((Spec.structureSheaf R).obj.obj (.op (PrimeSpectrum.basicOpen g)))
    exact StructureSheaf.IsLocalization.to_basicOpen R g
  have hloc : IsLocalizedModule (Submonoid.powers g)
      (tilde.toOpen M (PrimeSpectrum.basicOpen g)).hom := inferInstance
  exact finitePresentation_localizedModule_of_isLocalizedModule
    (A := Γ(Spec R, D.1)) (N₀ := M) (N := Γ(tilde M, D.1))
    (IsScalarTower.of_compHom R Γ(Spec R, D.1) Γ(tilde M, D.1)) (Submonoid.powers g)
    (tilde.toOpen M (PrimeSpectrum.basicOpen g)).hom hloc

/-- **Finite presentation after inverting `t`.** If `F ≅ M^~` on the affine scheme `X` and `F` is
finitely presented on the inverse image of the basic open of `t ∈ Γ(S, ⊤)`, then `M` is finitely
presented after inverting the image of `t` in `Γ(X, ⊤)`. This is the hypothesis `hfp` of
`Stacks.StrictTransform.exists_fg_ideal_forall_chartFreeOfRank`. -/
public theorem finitePresentation_localizedModule_away_of_preimage_basicOpen [IsAffine X]
    [IsAffine S] (f : X ⟶ S) (F : X.Modules) (M : ModuleCat.{u} Γ(X, ⊤))
    (ε : F ≅ (Scheme.Modules.pullback X.isoSpec.hom).obj (tilde M))
    [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : (algebraMap Γ(S, ⊤) Γ(X, ⊤) : Γ(S, ⊤) →+* Γ(X, ⊤)) = f.appTop.hom) (t : Γ(S, ⊤))
    (hfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ S.basicOpen t).ι).obj F).IsFinitePresentation) :
    Module.FinitePresentation (Localization.Away (algebraMap Γ(S, ⊤) Γ(X, ⊤) t))
      (LocalizedModule (Submonoid.powers (algebraMap Γ(S, ⊤) Γ(X, ⊤) t)) M) := by
  rw [show algebraMap Γ(S, ⊤) Γ(X, ⊤) t = f.appTop.hom t by rw [halg]]
  rw [Scheme.preimage_basicOpen_top f t] at hfp
  exact finitePresentation_localizedModule_away_of_tilde M (f.appTop.hom t) _
    (isoSpec_inv_preimage_basicOpen (f.appTop.hom t))
    (isFinitePresentation_pullback_tilde_basicOpen F M ε (f.appTop.hom t) hfp)

end Stacks.StrictTransform

end
