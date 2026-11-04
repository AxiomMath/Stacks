module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexAffineCover
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# A dualizing complex is recognised on one affine open cover

[Stacks, Tag 0A86] says that an object `K` of `D(𝒪_X)` on a locally Noetherian scheme is a
dualizing complex — it carries a dualizing model at *every* affine open — as soon as it carries
one at the members of a single affine open cover.

`Stacks.Duality.isDualizingComplex_of_affineOpenCover` reduces this to two steps: carrying a
dualizing model passes to the basic opens of sections, and it descends from a family of basic
opens whose sections generate the unit ideal. Both are proved here, and the equivalence follows.

The first step is [Stacks, Tag 0A7G] read through the affine dictionary: over a basic open
`V = D(f)` of an affine open `U` the sections are the localization `Γ(X, U)_f`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`), extension of scalars along the
restriction map is exact, and `Stacks.AffineTilde.tildeIsoSpecRestrictIso` identifies the
restriction to `V` of the sheaf associated to `ω` with the sheaf associated to the extension of
`ω`. The second step is [Stacks, Tag 0A7H]: the candidate dualizing complex over `Γ(X, U)` is
produced by `AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory` from the
quasi-coherence of the cohomology sheaves of `K`, and full faithfulness of derived
sheafification identifies its extension to `Γ(X, D(f))` with the dualizing complex supplied by
the model there.

## Main definitions

* `Stacks.AffineTilde.tildeIsoSpecRestrictIso` — the affine dictionary between two nested affine
  opens, and `tildeIsoSpecRestrictDerivedIso` its derived form.

## Main results

* `Stacks.Duality.hasDualizingModelOn_basicOpen` — the basic-open step.
* `Stacks.Duality.hasDualizingModelOn_of_span_basicOpen` — the unit-ideal step.
* `Stacks.Duality.isDualizingComplex_iff_exists_affineOpenCover` — **[Stacks, Tag 0A86]**: being
  a dualizing complex is equivalent to carrying a dualizing model on one affine open cover.

## Implementation notes

The derived categories of `Stacks.Duality.HasDualizingModelOn` that depend on the affine open
are sealed inside its body at `CategoryTheory.HasDerivedCategory.standard`, so this file installs
that model with priority `10000`, as
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` requires of its
importers.

`CategoryTheory.Limits.PreservesFiniteLimits` for extension of scalars along a restriction map is
an instance hypothesis rather than a derived side condition, matching
`Stacks.AffineTilde.tildeRestrictDerivedIso`; at a basic open it is supplied by
`Stacks.Duality.preservesFiniteLimits_extendScalars_basicOpen`.

## References

* [Stacks Project, Tag 01IW](https://stacks.math.columbia.edu/tag/01IW)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A7H](https://stacks.math.columbia.edu/tag/0A7H)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.CoherentTFAE
open StacksDraft.PseudoCoherence (localizationAwayFunctorAux)

universe u w

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}}

/-- The inclusion of an affine open `V` into an affine open `U` containing it is, read on
spectra, the spectrum of the restriction map on sections. -/
theorem homOfLE_isoSpec_hom {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hle : V ≤ U) :
    X.homOfLE hle ≫ hU.isoSpec.hom =
      hV.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE hle).op) := by
  have h := hU.map_fromSpec hV (homOfLE hle).op
  rw [IsAffineOpen.fromSpec, IsAffineOpen.fromSpec, ← X.homOfLE_ι hle] at h
  have h2 : Spec.map (X.presheaf.map (homOfLE hle).op) ≫ hU.isoSpec.inv =
      hV.isoSpec.inv ≫ X.homOfLE hle := by
    rw [← cancel_mono U.ι]
    simpa only [Category.assoc] using h
  rw [← Iso.eq_comp_inv, Category.assoc, h2, Iso.hom_inv_id_assoc]

/-- Restricting along `U ≅ Spec Γ(X, U)` and then along its inverse is the identity. -/
def restrictIsoSpecCompIso {U : X.Opens} (hU : IsAffineOpen U) :
    Scheme.Modules.restrictFunctor hU.isoSpec.hom ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.inv ≅
      𝟭 (Spec Γ(X, U)).Modules :=
  (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom).symm ≪≫
    Scheme.Modules.restrictFunctorCongr hU.isoSpec.inv_hom_id ≪≫
    Scheme.Modules.restrictFunctorId

/-- Restricting along the inverse of `U ≅ Spec Γ(X, U)` and then along it is the identity. -/
def restrictIsoSpecInvCompIso {U : X.Opens} (hU : IsAffineOpen U) :
    Scheme.Modules.restrictFunctor hU.isoSpec.inv ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom ≅
      𝟭 U.toScheme.Modules :=
  (Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
    Scheme.Modules.restrictFunctorCongr hU.isoSpec.hom_inv_id ≪≫
    Scheme.Modules.restrictFunctorId

end AlgebraicGeometry.IsAffineOpen

namespace Stacks.AffineTilde

variable {X : Scheme.{u}}

/-- **The affine dictionary between two nested affine opens.** Restricting to an affine open
`V ⊆ U` the complex of sheaves associated to an object of `D(Γ(X, U))`, read on `U`, gives the
complex of sheaves associated to its extension of scalars to `Γ(X, V)`, read on `V`. -/
def tildeIsoSpecRestrictIso {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hle : V ≤ U) [IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE hle).op))] :
    (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ⋙
        Scheme.Modules.restrictFunctor (X.homOfLE hle) ≅
      ModuleCat.extendScalars (X.presheaf.map (homOfLE hle).op).hom ⋙
        (tilde.functor Γ(X, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Scheme.Modules.restrictFunctorComp (X.homOfLE hle) hU.isoSpec.hom).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (hU.homOfLE_isoSpec_hom hV hle) ≪≫
        Scheme.Modules.restrictFunctorComp hV.isoSpec.hom
          (Spec.map (X.presheaf.map (homOfLE hle).op))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tildeRestrictIso (X.presheaf.map (homOfLE hle).op)) _ ≪≫
    Functor.associator _ _ _

/-- `Stacks.AffineTilde.tildeIsoSpecRestrictIso` on unbounded derived categories, for a
restriction map along which extension of scalars is exact. -/
def tildeIsoSpecRestrictDerivedIso {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hle : V ≤ U) [IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE hle).op))]
    [PreservesFiniteLimits (ModuleCat.extendScalars (X.presheaf.map (homOfLE hle).op).hom)] :
    (tilde.functor Γ(X, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor (X.homOfLE hle)).mapDerivedCategory ≅
      (ModuleCat.extendScalars
          (X.presheaf.map (homOfLE hle).op).hom).mapDerivedCategory ⋙
        (tilde.functor Γ(X, V) ⋙
          Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCongr (tildeIsoSpecRestrictIso hU hV hle) ≪≫
    (Functor.mapDerivedCategoryCompIso (Iso.refl _)).symm

/-- One further restriction along the inverse of `U ≅ Spec Γ(X, U)` cancels the transport in the
functor presenting a dualizing model, leaving derived sheafification. -/
def tildeIsoSpecCancelIso {U : X.Opens} (hU : IsAffineOpen U) :
    (tilde.functor Γ(X, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory ≅
      (tilde.functor Γ(X, U)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCongr (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ hU.restrictIsoSpecCompIso ≪≫ Functor.rightUnitor _)

end Stacks.AffineTilde

namespace Stacks.Duality

variable {X : Scheme.{u}}

/-- Extension of scalars along a localization map is exact. -/
private theorem preservesFiniteLimits_extendScalars_algebraMap_of_isLocalization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) :=
  extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S M))

/-- Extension of scalars to the sections over a basic open of an affine open is exact: those
sections are a localization of the sections over the ambient open. -/
theorem preservesFiniteLimits_extendScalars_algebraMap_basicOpen (V : X.affineOpens)
    (f : Γ(X, V.1)) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (algebraMap Γ(X, V.1) Γ(X, X.basicOpen f))) :=
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := V.2.isLocalization_basicOpen f
  preservesFiniteLimits_extendScalars_algebraMap_of_isLocalization (Submonoid.powers f)

/-- `Stacks.Duality.preservesFiniteLimits_extendScalars_algebraMap_basicOpen` spelled with the
restriction map of the structure sheaf, which is the algebra structure map. -/
theorem preservesFiniteLimits_extendScalars_basicOpen (V : X.affineOpens) (f : Γ(X, V.1)) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) :=
  preservesFiniteLimits_extendScalars_algebraMap_basicOpen V f

/-- Extension of scalars to the localization of the sections of an affine open away from one of
them is exact. -/
theorem preservesFiniteLimits_extendScalars_localizationAway (V : X.affineOpens)
    (f : Γ(X, V.1)) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (algebraMap Γ(X, V.1) (Localization.Away f))) :=
  preservesFiniteLimits_extendScalars_algebraMap_of_isLocalization (Submonoid.powers f)

/-- Spectra turn the restriction map to a basic open into an open immersion. -/
theorem isOpenImmersion_specMap_basicOpen (V : X.affineOpens) (f : Γ(X, V.1)) :
    IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) :=
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := V.2.isLocalization_basicOpen f
  AlgebraicGeometry.IsOpenImmersion.of_isLocalization
    (R := Γ(X, V.1)) (S := Γ(X, X.basicOpen f)) f

variable [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

omit [HasDerivedCategory.{w} X.Modules] in
/-- **[Stacks, Tag 0A7G] at a basic open of an affine open.** The extension to the sections over
`D(f)` of a dualizing complex over `Γ(X, U)` is a dualizing complex over `Γ(X, D(f))`. -/
theorem isDualizingComplex_extendScalars_basicOpen (V : X.affineOpens) (f : Γ(X, V.1))
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, V.1)))
    (hω : letI : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
      Dualizing.IsDualizingComplex ω) :
    letI := preservesFiniteLimits_extendScalars_basicOpen V f
    letI : IsNoetherianRing Γ(X, X.basicOpen f) :=
      IsLocallyNoetherian.component_noetherian ⟨X.basicOpen f, V.2.basicOpen f⟩
    Dualizing.IsDualizingComplex
      ((ModuleCat.extendScalars
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).mapDerivedCategory.obj ω) := by
  let := preservesFiniteLimits_extendScalars_basicOpen V f
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := V.2.isLocalization_basicOpen f
  exact Dualizing.isDualizingComplex_extendScalars_of_isLocalization (Submonoid.powers f) ω hω

omit [IsLocallyNoetherian X] in
/-- **The presentation of `K|_U` by an object of `D(Γ(X, U))` restricts to the basic opens of
sections.** Over `D(f)` the presenting object is the extension of scalars of the one over `U`;
this is `Stacks.AffineTilde.tildeIsoSpecRestrictDerivedIso` together with the factorisation of
the inclusion of `D(f)` through `U`. -/
theorem nonempty_iso_extendScalars_basicOpen {K : DerivedCategory X.Modules} (V : X.affineOpens)
    (f : Γ(X, V.1)) (ω : DerivedCategory (ModuleCat.{u} Γ(X, V.1)))
    (e : (Scheme.Modules.restrictFunctor V.1.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, V.1) ⋙
        Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapDerivedCategory.obj ω) :
    letI := preservesFiniteLimits_extendScalars_basicOpen V f
    Nonempty ((Scheme.Modules.restrictFunctor (X.basicOpen f).ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, X.basicOpen f) ⋙
          Scheme.Modules.restrictFunctor (V.2.basicOpen f).isoSpec.hom).mapDerivedCategory.obj
        ((ModuleCat.extendScalars
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).mapDerivedCategory.obj ω)) := by
  let := preservesFiniteLimits_extendScalars_basicOpen V f
  let := isOpenImmersion_specMap_basicOpen V f
  let eres : (Scheme.Modules.restrictFunctor V.1.ι).mapDerivedCategory ⋙
      (Scheme.Modules.restrictFunctor (X.homOfLE (X.basicOpen_le f))).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor (X.basicOpen f).ι).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso
      ((Scheme.Modules.restrictFunctorComp (X.homOfLE (X.basicOpen_le f)) V.1.ι).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι (X.basicOpen_le f)))
  exact ⟨(eres.app K).symm ≪≫
    (Scheme.Modules.restrictFunctor
      (X.homOfLE (X.basicOpen_le f))).mapDerivedCategory.mapIso e ≪≫
    (Stacks.AffineTilde.tildeIsoSpecRestrictDerivedIso V.2 (V.2.basicOpen f)
      (X.basicOpen_le f)).app ω⟩

/-- **Carrying a dualizing model passes to the basic opens of sections.** This is the first step
of the proof of [Stacks, Tag 0A86]: [Stacks, Tag 0A7G] carried through the affine dictionary. -/
theorem hasDualizingModelOn_basicOpen {K : DerivedCategory X.Modules} (V : X.affineOpens)
    (f : Γ(X, V.1)) (h : HasDualizingModelOn K V.1 V.2) :
    HasDualizingModelOn K (X.affineBasicOpen f).1 (X.affineBasicOpen f).2 := by
  let := preservesFiniteLimits_extendScalars_basicOpen V f
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  exact ⟨(ModuleCat.extendScalars
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).mapDerivedCategory.obj ω,
    isDualizingComplex_extendScalars_basicOpen V f ω hω,
    nonempty_iso_extendScalars_basicOpen V f ω e⟩

omit [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] in
/-- Being the associated sheaf of a finite module over an affine open depends on the open only
through its value. -/
theorem isFiniteTildeOn_congr {F : X.Modules} {W W' : X.Opens} (hW : IsAffineOpen W)
    (hW' : IsAffineOpen W') (e : W = W') (h : IsFiniteTildeOn F W hW) :
    IsFiniteTildeOn F W' hW' := by
  subst e
  exact h

/-- The cohomology sheaves of `K` are quasi-coherent as soon as `K` carries a dualizing model at
the members of one affine open cover: on each of them a cohomology sheaf is the sheaf associated
to a finite module. -/
theorem isQuasicoherent_homology_of_hasDualizingModelOn_cover {K : DerivedCategory X.Modules}
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (h : ∀ i, HasDualizingModelOn K (U i) (hU i)) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent := by
  have hc : TopologicalSpace.IsOpenCover
      (fun V : {V : X.affineOpens // ∃ j, U j = V.1} => V.1.1) := by
    refine top_le_iff.mp ?_
    rw [← hcov]
    exact iSup_le fun j => le_iSup_of_le ⟨⟨U j, hU j⟩, j, rfl⟩ le_rfl
  refine isQuasicoherent_of_cover_isFiniteTildeOn _ _ hc (fun V => V.1.2) fun V => ?_
  obtain ⟨j, hj⟩ := V.2
  exact isFiniteTildeOn_congr (hU j) V.1.2 hj
    (isFiniteTildeOn_homology_of_hasDualizingModelOn (h j) i)



omit [IsLocallyNoetherian X] in
/-- **Quasi-coherent cohomology is inherited by the restriction to an open subscheme**, at any
model of `D(𝒪_X)`: restriction along an open immersion is exact and preserves quasi-coherence,
so it commutes with taking cohomology. -/
theorem isQuasicoherent_homology_restrictFunctor {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] {E : DerivedCategory X.Modules}
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj E)).IsQuasicoherent := by
  refine (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((Dualizing.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor g) i).app E).symm ?_
  have := hE i
  show ((Scheme.Modules.restrictFunctor g).obj
    ((DerivedCategory.homologyFunctor X.Modules i).obj E)).IsQuasicoherent
  infer_instance

omit [IsLocallyNoetherian X] in
/-- **An object with quasi-coherent cohomology is presented over an affine open by an object of
`D(Γ(X, U))`.** This is the essential surjectivity half of the affine derived equivalence,
`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`, read on `U` rather than on
`Spec Γ(X, U)`. -/
theorem exists_nonempty_iso_tilde_of_isQuasicoherent {K : DerivedCategory X.Modules}
    {U : X.Opens} (hU : IsAffineOpen U)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) :
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
        (tilde.functor Γ(X, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω) := by
  obtain ⟨ω, ⟨e⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory Γ(X, U)
    ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.obj
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K))
    (fun n => isQuasicoherent_homology_restrictFunctor hU.isoSpec.inv
      (isQuasicoherent_homology_restrictFunctor U.ι hqc) n)
  let ecancel : (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory ⋙
      (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory ≅
      𝟭 (DerivedCategory U.toScheme.Modules) :=
    Functor.mapDerivedCategoryCompIso hU.restrictIsoSpecInvCompIso ≪≫
      Functor.mapDerivedCategoryId _
  exact ⟨ω, ⟨(ecancel.app _).symm ≪≫
    (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.mapIso e.symm ≪≫
    (Functor.mapDerivedCategoryCompIso (Iso.refl _)).app ω⟩⟩

omit [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] in
/-- **Two presenting objects over the same affine open are isomorphic.** Derived sheafification
is fully faithful, and the transport along `U ≅ Spec Γ(X, U)` is cancelled by its inverse. -/
theorem nonempty_iso_of_nonempty_iso_tilde {U : X.Opens} (hU : IsAffineOpen U)
    {E : DerivedCategory U.toScheme.Modules}
    {ω ω' : DerivedCategory (ModuleCat.{u} Γ(X, U))}
    (e : E ≅ (tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)
    (e' : E ≅ (tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω') :
    Nonempty (ω ≅ ω') :=
  ⟨(AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful Γ(X, U)).preimageIso
    (((Stacks.AffineTilde.tildeIsoSpecCancelIso hU).app ω).symm ≪≫
      (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.mapIso
        (e.symm ≪≫ e') ≪≫
      (Stacks.AffineTilde.tildeIsoSpecCancelIso hU).app ω')⟩

/-- **Carrying a dualizing model descends from a family of basic opens generating the unit
ideal.** This is the second step of the proof of [Stacks, Tag 0A86]: the candidate complex over
`Γ(X, U)` is supplied by the affine derived equivalence, and [Stacks, Tag 0A7H] makes it
dualizing. -/
theorem hasDualizingModelOn_of_span_basicOpen {K : DerivedCategory X.Modules}
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (V : X.affineOpens) (s : Finset Γ(X, V.1))
    (hs : Ideal.span (s : Set Γ(X, V.1)) = ⊤)
    (h : ∀ f : s, HasDualizingModelOn K (X.affineBasicOpen f.1).1
      (X.affineBasicOpen f.1).2) :
    HasDualizingModelOn K V.1 V.2 := by
  have hA : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨ω, ⟨eω⟩⟩ := exists_nonempty_iso_tilde_of_isQuasicoherent V.2 hqc
  refine ⟨ω, ?_, ⟨eω⟩⟩
  refine Dualizing.isDualizingComplex_of_localizations (fun f : s => (f : Γ(X, V.1))) ω
    (by simpa using hs) fun f => ?_
  have hW : IsNoetherianRing Γ(X, X.basicOpen (f : Γ(X, V.1))) :=
    IsLocallyNoetherian.component_noetherian
      ⟨X.basicOpen (f : Γ(X, V.1)), V.2.basicOpen _⟩
  have hLoc : IsLocalization.Away (f : Γ(X, V.1)) Γ(X, X.basicOpen (f : Γ(X, V.1))) :=
    V.2.isLocalization_basicOpen _
  let := preservesFiniteLimits_extendScalars_algebraMap_basicOpen V (f : Γ(X, V.1))
  let := preservesFiniteLimits_extendScalars_localizationAway V (f : Γ(X, V.1))
  obtain ⟨ωf, hωf, ⟨ef⟩⟩ := h f
  obtain ⟨e'⟩ := nonempty_iso_extendScalars_basicOpen V (f : Γ(X, V.1)) ω eω
  obtain ⟨eiso⟩ := nonempty_iso_of_nonempty_iso_tilde (V.2.basicOpen (f : Γ(X, V.1))) e' ef
  exact Dualizing.isDualizingComplex_localizationAway_of_extendScalars
    (B := Γ(X, X.basicOpen (f : Γ(X, V.1)))) (f : Γ(X, V.1)) ω
    (Dualizing.isDualizingComplex_of_iso eiso.symm hωf)

/-- **The implication (2) ⟹ (1) of [Stacks, Tag 0A86].** A dualizing model at the members of one
affine open cover gives one at every affine open. -/
theorem isDualizingComplex_of_hasDualizingModelOn_cover {K : DerivedCategory X.Modules}
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (h : ∀ i, HasDualizingModelOn K (U i) (hU i)) :
    IsDualizingComplex K :=
  isDualizingComplex_of_affineOpenCover
    (fun W f hW => hasDualizingModelOn_basicOpen W f hW)
    (fun W t ht hW => hasDualizingModelOn_of_span_basicOpen
      (isQuasicoherent_homology_of_hasDualizingModelOn_cover U hU hcov h) W t ht hW)
    U hU hcov h

/-- **The pointwise form of the implication (2) ⟹ (1) of [Stacks, Tag 0A86].** A dualizing model
at *some* affine open through each point of `X` gives one at every affine open: the opens the
hypothesis produces cover `X`, so
`Stacks.Duality.isDualizingComplex_of_hasDualizingModelOn_cover` applies to them. -/
theorem isDualizingComplex_of_forall_exists_hasDualizingModelOn {K : DerivedCategory X.Modules}
    (h : ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧ HasDualizingModelOn K U hU) :
    IsDualizingComplex K := by
  choose U hU hmem hmodel using h
  refine isDualizingComplex_of_hasDualizingModelOn_cover U hU (top_unique fun x _ => ?_) hmodel
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩

/-- **Stacks Project, Tag 0A86.** On a locally Noetherian scheme an object of `D(𝒪_X)` is a
dualizing complex — it carries a dualizing model at every affine open — exactly when it carries
one at the members of a single affine open cover. -/
@[stacks 0A86]
theorem isDualizingComplex_iff_exists_affineOpenCover {K : DerivedCategory X.Modules} :
    IsDualizingComplex K ↔
      ∃ (ι : Type u) (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)),
        (⨆ i, U i = ⊤) ∧ ∀ i, HasDualizingModelOn K (U i) (hU i) :=
  ⟨fun hK => ⟨X.affineOpens, fun W => W.1, fun W => W.2, iSup_affineOpens_eq_top X,
      fun W => hK W.1 W.2⟩,
    fun ⟨_, U, hU, hcov, h⟩ => isDualizingComplex_of_hasDualizingModelOn_cover U hU hcov h⟩

end Stacks.Duality

end
