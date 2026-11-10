module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Sections
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.SliceRestriction
import all StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.SliceRestriction
public import StacksFrontier.Topology.OpensMapFinal

/-!
# Pushforward of quasi-coherent modules: basic-open presentation descent

Part 2 of the proof of `AlgebraicGeometry.pushforward_isQuasicoherent`.

On a basic open `D(r)` contained in a cover member of the quasi-coherence data, the restriction
of a sheaf of modules is a geometric tilde. The section-localization descent reduces the
basic-open localization of sections on `Spec R` to a finite cover, and the section isos of the
pullback along an open immersion transport `IsLocalizedModule` across ring isomorphisms.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u


namespace AlgebraicGeometry

open CategoryTheory Limits

/-! ## Supplementary results — basic-open presentation descent (the affine keystone)

This section assembles the the affine case per-element keystone
that statement
(`isIso_fromTildeΓ_restrict_basicOpen`): on a basic open `D(r)` contained in a cover member
`q.X i` of the quasi-coherence data, the restricted sheaf `M|_{D(r)}` is a geometric tilde, i.e.
its `fromTildeΓ` counit is an isomorphism.

The route follows the affine descent of the recipe, building on the slice-to-geometric presentation
transport of the previous section:

1. `presentationPullbackιOfQuasicoherentData M q i` is a *global* `Presentation` of the geometric
   restriction `N := (q.X i).ι^* M` on the open subscheme `Z := (q.X i).toScheme`.
2. For any open `W ⊆ Z`, the global presentation `PN` slices to a slice presentation `N.over W` via
   the single `Presentation.map` of the over-functor `pushforward (𝟙 …)` (the
   `QuasicoherentData.ofPresentation` template — no iterated-slice equivalence is needed because
   `PN` is already a global presentation on the genuine scheme `Z`).
3. `overRestrictPresentation W N PNW` transports it to a global presentation of the geometric
   restriction `(pullback W.ι).obj N` on the open subscheme `W.toScheme`.
4. For `W` *affine*, `IsAffineOpen.isoSpec` identifies `W.toScheme ≅ Spec Γ(Z, W)`; transporting
   the presentation across this iso (whose `Opens.map` is `Final`, so `pullbackObjUnitToUnit` is an
   iso) lands a global presentation on the genuine affine `Spec Γ(Z, W)`.
5. A global presentation forces `fromTildeΓ` to be an isomorphism
   (`isIso_fromTildeΓ_of_presentation`).

Mathlib (at the pinned commit) carries no `QCoh(Spec R) ≃ Mod R` essential-image bridge;
this descent
is -/

section BasicOpenPresentationDescent

open CategoryTheory Limits TopologicalSpace Topology

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-! The three sheafification facts below are found by instance search in a clean context in
well under the default budget, but the goals that need them sit inside large elaborations where
the search no longer fits. Naming each one puts it in the discrimination tree, so the use sites
resolve immediately and need no `synthInstance` budget. -/

/-- Sheafification of abelian-group-valued presheaves exists on every slice of the opens site
of a scheme. -/
private instance hasSheafify_opensOver {Y : Scheme.{u}} (W : Y.Opens) :
    HasSheafify ((Opens.grothendieckTopology ↥Y).over W) AddCommGrpCat.{u} :=
  inferInstance

/-- The forgetful functor from abelian sheaves on the opens site of a scheme has a left
adjoint, i.e. that site admits weak sheafification. -/
private instance isRightAdjoint_sheafToPresheaf_opens {Y : Scheme.{u}} :
    (sheafToPresheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}).IsRightAdjoint :=
  inferInstance

/-- The same, on a doubly-sliced opens site of a scheme. -/
private instance isRightAdjoint_sheafToPresheaf_opensOverOver {Y : Scheme.{u}} (W : Y.Opens)
    (T : CategoryTheory.Over W) :
    (sheafToPresheaf (((Opens.grothendieckTopology ↥Y).over W).over T)
      AddCommGrpCat.{u}).IsRightAdjoint :=
  inferInstance

/-- On a slice of the opens site of a scheme, the weak-equivalence class of the abelian
sheafification is exactly the locally bijective maps. -/
private instance wEqualsLocallyBijective_opensOver {Y : Scheme.{u}} (W : Y.Opens) :
    ((Opens.grothendieckTopology ↥Y).over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance

/-- The same, on a doubly-sliced opens site of a scheme. -/
private instance wEqualsLocallyBijective_opensOverOver {Y : Scheme.{u}} (W : Y.Opens)
    (T : CategoryTheory.Over W) :
    (((Opens.grothendieckTopology ↥Y).over W).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  inferInstance

-- Slicing the global presentation down to an open subscheme.
/-- **Presentation of the geometric restriction of `M` to an open `W` of a cover member**.

For a sheaf of modules `M` on `X` with quasi-coherence data `q`, an index `i`, and *any* open
`W ⊆ (q.X i).toScheme` of the cover-member subscheme, the geometric restriction
`(pullback W.ι).obj ((pullback (q.X i).ι).obj M)` of `M` (pulled back to `Z := (q.X i).toScheme`,
then to `W`) admits a `SheafOfModules.Presentation` on the open subscheme `W.toScheme`.

It slices the *global* presentation `presentationPullbackιOfQuasicoherentData M q i` of
`N := (q.X i).ι^* M` on `Z` down to the slice `N.over W` (a single `Presentation.map` of the
over-functor — the `QuasicoherentData.ofPresentation` template, no iterated-slice equivalence
needed since `PN` is global on the genuine scheme `Z`), then geometrizes via
`overRestrictPresentation`. feeds the affine descent of the keystone
`isIso_fromTildeΓ_restrict_basicOpen`. -/
private noncomputable def presentationPullbackιRestrict (M : X.Modules)
    (q : M.QuasicoherentData) (i : q.I) (W : (Scheme.Opens.toScheme (X := X) (q.X i)).Opens) :
    ((Scheme.Modules.pullback (Scheme.Opens.ι W)).obj
      ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M)).Presentation :=
  overRestrictPresentation W ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M)
    (SheafOfModules.Presentation.map.{u}
      (presentationPullbackιOfQuasicoherentData M q i)
      (SheafOfModules.pushforward
        (𝟙 ((Scheme.Opens.toScheme (X := X) (q.X i)).ringCatSheaf.over W))) (by rfl))

/-- **The opens functor of an iso of schemes is an equivalence of opens sites.** For `φ : Y ≅ Z`,
the inverse-image functor `Opens.map φ.inv.base : Opens ↥Y ⥤ Opens ↥Z` is an equivalence (with
inverse `Opens.map φ.hom.base`), assembled from the pseudofunctoriality isos `Opens.mapComp` /
`Opens.mapId`. Its purpose is to supply the `Final` instance that makes `pullbackObjUnitToUnit` an
isomorphism in `pullbackSchemeIsoUnitIso`. -/
private noncomputable def opensMapEquivOfIso {Y Z : Scheme.{u}} (φ : Y ≅ Z) :
    TopologicalSpace.Opens ↥Y ≌ TopologicalSpace.Opens ↥Z where
  functor := Opens.map φ.inv.base
  inverse := Opens.map φ.hom.base
  unitIso := (Opens.mapId _).symm ≪≫
      Opens.mapIso (𝟙 _) (φ.hom.base ≫ φ.inv.base)
        (show (𝟙 _) = φ.hom.base ≫ φ.inv.base by
          rw [← AlgebraicGeometry.Scheme.Hom.comp_base, φ.hom_inv_id]; rfl) ≪≫
      Opens.mapComp φ.hom.base φ.inv.base
  counitIso := (Opens.mapComp φ.inv.base φ.hom.base).symm ≪≫
      Opens.mapIso (φ.inv.base ≫ φ.hom.base) (𝟙 _)
        (show φ.inv.base ≫ φ.hom.base = 𝟙 _ by
          rw [← AlgebraicGeometry.Scheme.Hom.comp_base, φ.inv_hom_id]; rfl) ≪≫
      Opens.mapId _

/-- **The opens functor of an iso of schemes is final.** Immediate from
`opensMapEquivOfIso` (an equivalence is final); the `Final` fact needed by
`pullbackObjUnitToUnit`. Supplied via `haveI` at use sites (instance resolution cannot invert
`φ.inv.base`). -/
private theorem opensMap_final_of_schemeIso {Y Z : Scheme.{u}} (φ : Y ≅ Z) :
    (Opens.map φ.inv.base).Final :=
  Stacks.Topology.final_opensMap φ.inv.base

private instance final_opensMap_of_schemeIso {Y Z : Scheme.{u}} (φ : Y ≅ Z) :
    (Opens.map φ.inv.base).Final :=
  opensMap_final_of_schemeIso φ

/-- `Scheme.Modules.pullback`, with both ends spelled `SheafOfModules …` rather than `·.Modules`.

`SheafOfModules.Presentation.map` is stated over `SheafOfModules.{u} R ⥤ SheafOfModules.{u} S`, and
`Scheme.Modules` is a structure copy of `SheafOfModules` with its own `Category` instance, so an
instance proved about `Scheme.Modules.pullback k` at its own type is not the instance
`Presentation.map` asks for. Naming the functor here fixes the spelling for both. -/
noncomputable def pullbackFunctor {A B : Scheme.{u}} (k : A ⟶ B) :
    SheafOfModules.{u} B.ringCatSheaf ⥤ SheafOfModules.{u} A.ringCatSheaf :=
  Scheme.Modules.pullback k

/-- Pullback preserves colimits, being a left adjoint. -/
private instance pullbackFunctor_preservesColimitsOfSize {A B : Scheme.{u}} (k : A ⟶ B) :
    PreservesColimitsOfSize.{u, u} (pullbackFunctor k) :=
  (Scheme.Modules.pullbackPushforwardAdjunction k).leftAdjoint_preservesColimits

/-- The canonical comparison out of the pullback of the unit module along an iso of schemes is an
isomorphism.

Mathlib's `SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal` says exactly this, but search
cannot apply it here: it has to unify `pullbackObjUnitToUnit ?φ` against the goal, and the
`[(pushforward ?φ).IsRightAdjoint]` argument of `pullbackObjUnitToUnit` is a synthetic instance
metavariable, so unification must synthesize it before `?φ` is known and then compare the result at
reducible transparency. Restating the conclusion here, with the arguments the goal has, moves that
comparison into a term elaboration, where it is done at default transparency. -/
instance isIso_pullbackObjUnitToUnit_schemeIso {Y Z : Scheme.{u}} (φ : Y ≅ Z) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit (φ.inv.toRingCatSheafHom)) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

/-- **Pullback along an iso of schemes sends the unit module to the unit module**.

For an isomorphism of schemes `φ : Y ≅ Z`, the pullback functor along `φ.inv : Z ⟶ Y` carries the
structure-sheaf (unit) module of `Y` to that of `Z`. The underlying canonical comparison
`pullbackObjUnitToUnit` is an isomorphism because the site functor `Opens.map φ.inv.base` of an iso
of schemes is `Final` (`opensMap_final_of_schemeIso`). This is the `F.obj (unit R) ≅ unit S` datum
consumed by `Presentation.map` along `pullback φ.inv` in `presentationPullbackOfSchemeIso`. -/
private noncomputable def pullbackSchemeIsoUnitIso {Y Z : Scheme.{u}} (φ : Y ≅ Z) :
    (pullbackFunctor φ.inv).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (φ.inv.toRingCatSheafHom))
    (isIso_pullbackObjUnitToUnit_schemeIso φ)

-- Mapping the presentation through pullback requires the colimit-preservation instance chain.
/-- **A presentation transports across the pullback by an iso of schemes** (step 4).

Given an isomorphism of schemes `φ : Y ≅ Z` and a `SheafOfModules.Presentation` of a module `N` on
`Y`, the geometric pullback `(pullback φ.inv).obj N` of `N` to `Z` admits a presentation. It is
`Presentation.map` along the colimit-preserving pullback functor `pullback φ.inv`, using
the unit-iso
`pullbackSchemeIsoUnitIso φ`. This is the affine-identification transport step of the keystone:
applied with `φ` the `IsAffineOpen.isoSpec` of the affine restriction, it moves the
presentation onto
a genuine `Spec`. -/
private noncomputable def presentationPullbackOfSchemeIso {Y Z : Scheme.{u}} (φ : Y ≅ Z)
    (N : Y.Modules) (P : N.Presentation) :
    ((Scheme.Modules.pullback φ.inv).obj N).Presentation :=
  SheafOfModules.Presentation.map.{u} P (pullbackFunctor φ.inv)
    (pullbackSchemeIsoUnitIso φ).symm

-- The affine counit comparison unfolds the transported presentation and tilde equivalence.
/-- **Quasi-coherent restricts to a tilde on every affine open of a cover member**.

For a sheaf of modules `M` on `X` with quasi-coherence data `q`, an index `i`, and an *affine* open
`W ⊆ (q.X i).toScheme` of the cover-member subscheme, the geometric restriction of `M` to the
affine `Spec Γ((q.X i).toScheme, W) ≅ W` (pulled back to `Z := (q.X i).toScheme`, then to `W`,
then across the affine identification `IsAffineOpen.isoSpec`) has an isomorphism `fromTildeΓ`
counit; that is, it is a geometric tilde.

This is the geometric heart of the affine case per-element transport: the slice presentation
supplied by the quasi-coherence datum geometrizes (`presentationPullbackιRestrict`) to a global
presentation on `W.toScheme`, which transports across the affine iso
(`presentationPullbackOfSchemeIso`) to a global presentation on the genuine affine `Spec Γ(Z, W)`;
a global presentation forces `fromTildeΓ` to be an isomorphism
(`isIso_fromTildeΓ_of_presentation`). Mathlib has no `QCoh(Spec R) ≃ Mod R` essential-image
bridge. -/
private theorem isIso_fromTildeΓ_presentationPullback (M : X.Modules)
    (q : M.QuasicoherentData) (i : q.I)
    (W : (Scheme.Opens.toScheme (X := X) (q.X i)).Opens) (hW : IsAffineOpen W) :
    IsIso ((Scheme.Modules.pullback hW.isoSpec.inv).obj
      ((Scheme.Modules.pullback (Scheme.Opens.ι W)).obj
        ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M))).fromTildeΓ :=
  isIso_fromTildeΓ_of_presentation _
    (presentationPullbackOfSchemeIso hW.isoSpec
      ((Scheme.Modules.pullback (Scheme.Opens.ι W)).obj
        ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M))
      (presentationPullbackιRestrict M q i W))

-- Specializing the counit comparison to a basic open triggers the slice-site instance search.
/-- **Quasi-coherent restricts to a tilde on each basic open of the cover** (the affine keystone,
that statement).

Let `M` be a sheaf of modules on `Spec R` with quasi-coherence data `q`, and let `r : R` with
`D(r) ≤ q.X i` for some cover member. Then the geometric restriction of `M` to the affine basic
open `D(r)` — realised as the preimage `W := (q.X i).ι ⁻¹ᵁ D(r)` inside the cover-member subscheme
`Z := (q.X i).toScheme`, transported across the affine identification `W ≅ Spec Γ(Z, W)` (which is
`Spec R_r` since `D(r)` is affine) — has an isomorphism `fromTildeΓ` counit, i.e. `M|_{D(r)}` is a
geometric tilde.

This is the per-element step of the affine case: it is the affine instance `W = (q.X i).ι ⁻¹ᵁ D(r)`
of
`isIso_fromTildeΓ_presentationPullback`, with affineness of `W` from
`IsAffineOpen.Spec_basicOpen` (`D(r)` is affine in `Spec R`) and
`IsAffineOpen.preimage_of_isOpenImmersion` (its preimage under the open immersion `(q.X i).ι` is
affine, using `D(r) ≤ q.X i = (q.X i).ι.opensRange`). -/
theorem isIso_fromTildeΓ_restrict_basicOpen {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (r : R) (i : q.I)
    (hr : (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ q.X i) :
    IsIso (@Scheme.Modules.fromTildeΓ
      (Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen r)))
      ((Scheme.Modules.pullback
          (((IsAffineOpen.Spec_basicOpen r).preimage_of_isOpenImmersion (Scheme.Opens.ι (q.X i))
            (by rwa [Scheme.Opens.opensRange_ι])).isoSpec.inv)).obj
        ((Scheme.Modules.pullback (Scheme.Opens.ι
            ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen r)))).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M)))) :=
  isIso_fromTildeΓ_presentationPullback M q i
    ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen r))
    ((IsAffineOpen.Spec_basicOpen r).preimage_of_isOpenImmersion (Scheme.Opens.ι (q.X i))
      (by rwa [Scheme.Opens.opensRange_ι]))

/-! ## Supplementary results — : the section-localization descent

The keystone `isLocalizedModule_basicOpen_descent` reduces (Hartshorne II.5.3 / Stacks
`lemma-invert-f-sections`) to a finite-cover sheaf-gluing argument.  The single geometric input
is the **per-cover-element** fact that on each `D(r)` of a finite cover `{D(r_j)}` of `Spec R`
(with `D(r_j) ≤ q.X i`), the basic-open restriction `Γ(M, D(r)) → Γ(M, D(f) ⊓ D(r))` is a
localization at `powers f` — this is exactly the local-tilde data transported to sections, and
is the gated hypothesis `Hfr` below.  Given `Hfr` (for every `r` whose `D(r)` sits inside a cover
member, hence also for the overlaps `D(r r')`), the descent is pure sheaf theory: separatedness
gives the `exists_of_eq` field, gluing the patched compatible family gives `surj'`, and the global
`map_units` field holds for arbitrary `M` (`map_units_restrict_basicOpen`). -/

/-- A finite family `t` spanning `R` gives a basic-open cover of `Spec R`: the supremum of the
`D(r)` over `r ∈ t` is `⊤`.  Glue feeding the sheaf-gluing reduction of the
section-localization descent. -/
private lemma iSup_basicOpen_subtype_eq_top {R : CommRingCat.{u}} {t : Finset R}
    (hspan : Ideal.span (t : Set R) = ⊤) :
    (⨆ r : {x // x ∈ t}, (PrimeSpectrum.basicOpen (r : R) : (Spec R).Opens)) = ⊤ := by
  rw [iSup_subtype]
  have h := (PrimeSpectrum.iSup_basicOpen_eq_top_iff' (s := (t : Set R))).mpr hspan
  simpa using h

/-- Restriction maps of `modulesSpecToSheaf.obj M` compose: restricting `A → B → C` equals the
direct restriction `A → C`.  Poset-hom uniqueness makes the two intermediate morphisms compose to
the direct one.   bookkeeping for the section-localization descent. -/
private lemma res_comp {R : CommRingCat.{u}}
    (F : TopCat.Sheaf (ModuleCat.{u} ↑R) ↑(Spec R).toPresheafedSpace)
    {A B C : (Spec R).Opens} (hBA : B ≤ A) (hCB : C ≤ B) (hCA : C ≤ A)
    (y : ToType (F.presheaf.obj (.op A))) :
    (F.presheaf.map (homOfLE hCB).op).hom ((F.presheaf.map (homOfLE hBA).op).hom y)
      = (F.presheaf.map (homOfLE hCA).op).hom y := by
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp]; rfl

/-- Splitting a power of `f` acting on `v`: `f ^ N • v = f ^ (N - k) • f ^ k • v` for `k ≤ N`. -/
private lemma pow_smul_eq_pow_sub_smul_pow_smul {R V : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] (f : R) {k N : ℕ} (hle : k ≤ N) (v : V) :
    f ^ N • v = f ^ (N - k) • f ^ k • v := by
  rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hle]

/-- **Separatedness/torsion field of the section-localization descent.**  Given the
per-cover-element localization data `Hfr` (on each `D(r)` of a finite basic-open cover `{D(r)}` of
`Spec R`, the restriction `Γ(M, D(r)) → Γ(M, D(f) ⊓ D(r))` is a localization at `powers f`), any
global section `x` that restricts to `0` on `D(f)` is killed by a power of `f`.  This is the
`exists_of_eq` engine of `isLocalizedModule_basicOpen_descent`: per cover element a power of `f`
kills `x|_{D(r)}` (`IsLocalizedModule.exists_of_eq` of `Hfr`), the finite sup of these powers kills
every `x|_{D(r)}`, and sheaf separatedness over the cover (`TopCat.Sheaf.eq_of_locally_eq'`) lifts
this to `f^n • x = 0`.  the geometric content (`Hfr`) is the gated tilde data. -/
private lemma descent_smul_eq_zero {R : CommRingCat.{u}} (M : (Spec R).Modules) (f : R)
    (t : Finset R) (hspan : Ideal.span (t : Set R) = ⊤)
    (Hfr : ∀ r ∈ t, IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right :
          PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen r)).op).hom)
    (x : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)))
    (hx : ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x = 0) :
    ∃ n : ℕ, f ^ n • x = 0 := by
  classical
  have key : ∀ r : {x // x ∈ t}, ∃ k : ℕ, f ^ k •
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen (r:R) ≤ ⊤)).op).hom x = 0 := by
    rintro ⟨r, hr⟩
    have e1 := res_comp (modulesSpecToSheaf.obj M)
        (A := ⊤) (B := PrimeSpectrum.basicOpen r)
        (C := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r) le_top inf_le_right le_top x
    have e2 := res_comp (modulesSpecToSheaf.obj M)
        (A := ⊤) (B := PrimeSpectrum.basicOpen f)
        (C := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r) le_top inf_le_left le_top x
    have hzero := e1.trans (e2.symm.trans
      ((congrArg (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left :
            PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
              ≤ PrimeSpectrum.basicOpen f)).op).hom) hx).trans
        (map_zero _)))
    obtain ⟨c, hc⟩ := (Hfr r hr).exists_of_eq (hzero.trans (map_zero _).symm)
    obtain ⟨k, hk⟩ := c.2
    have hk' : f ^ k = (c : R) := hk
    refine ⟨k, ?_⟩
    have h2 : c • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen (r:R) ≤ ⊤)).op).hom x) = 0 :=
      hc.trans (smul_zero c)
    rwa [hk']
  choose k hk using key
  refine ⟨Finset.univ.sup k, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (modulesSpecToSheaf.obj M)
    (fun r : {x // x ∈ t} => (PrimeSpectrum.basicOpen (r:R) : (Spec R).Opens)) ⊤
    (fun r => homOfLE le_top) (le_of_eq (iSup_basicOpen_subtype_eq_top hspan).symm)
    (f ^ Finset.univ.sup k • x) 0 ?_
  intro r
  have hle : k r ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ r)
  set g := ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen (r:R) ≤ ⊤)).op).hom with hg
  have hms : g (f ^ Finset.univ.sup k • x) = f ^ Finset.univ.sup k • g x := LinearMap.map_smul g _ x
  have hzero : g (f ^ Finset.univ.sup k • x) = 0 :=
    hms.trans ((pow_smul_eq_pow_sub_smul_pow_smul f hle _).trans
      ((congrArg (fun y => f ^ (Finset.univ.sup k - k r) • y) (hk r)).trans (smul_zero _)))
  change g (f ^ Finset.univ.sup k • x) = g 0
  rw [hzero, map_zero]

/-- **Overlap agreement for the surjectivity field.**  If a section `br` on `D(r)` satisfies the
normalized identity `ρ[D(r), D(f) ⊓ D(r)] br = f^N • (y|_{D(f) ⊓ D(r)})`, then for any open
`U ≤ D(r)` its restriction to `U`, pushed down to `D(f) ⊓ U`, equals `f^N • (y|_{D(f) ⊓ U})`.
Specializing `U` to an overlap `D(r) ⊓ D(r')` shows the normalized sections of two cover members
agree there after restriction to `D(f) ⊓ (D(r) ⊓ D(r'))`, which (via the per-overlap localization)
makes a common `f`-power glue them.   bookkeeping for `descent_surj`. -/
private lemma descent_overlap_agree {R : CommRingCat.{u}} (M : (Spec R).Modules) (f : R) (r : R)
    (N : ℕ) (U : (Spec R).Opens) (hUr : U ≤ PrimeSpectrum.basicOpen r)
    (y : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op (PrimeSpectrum.basicOpen f))))
    (br : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op (PrimeSpectrum.basicOpen r))))
    (hbr : ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen r)).op).hom br
        = f ^ N • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen f)).op).hom y)) :
    ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ U ≤ U)).op).hom
      (((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hUr).op).hom br)
    = f ^ N • (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ U
          ≤ PrimeSpectrum.basicOpen f)).op).hom y) := by
  have hCB : PrimeSpectrum.basicOpen f ⊓ U
      ≤ PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r := inf_le_inf_left _ hUr
  have e1 := res_comp (modulesSpecToSheaf.obj M)
      (A := PrimeSpectrum.basicOpen r) (B := U) (C := PrimeSpectrum.basicOpen f ⊓ U)
      hUr inf_le_right (inf_le_right.trans hUr) br
  have e2 := res_comp (modulesSpecToSheaf.obj M) (A := PrimeSpectrum.basicOpen r)
      (B := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r)
      (C := PrimeSpectrum.basicOpen f ⊓ U) inf_le_right hCB (inf_le_right.trans hUr) br
  have e3 := res_comp (modulesSpecToSheaf.obj M) (A := PrimeSpectrum.basicOpen f)
      (B := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r)
      (C := PrimeSpectrum.basicOpen f ⊓ U) inf_le_left hCB inf_le_left y
  have hms := LinearMap.map_smul ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hCB).op).hom
      (f ^ N) (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
          ≤ PrimeSpectrum.basicOpen f)).op).hom y)
  exact e1.trans (e2.symm.trans ((congrArg _ hbr).trans (hms.trans (congrArg (f ^ N • ·) e3))))

/-- **Surjectivity field of the section-localization descent.**  With the per-cover-element (and
per-overlap) localization data `Hfr`, every section `y` over `D(f)` becomes, after multiplying by a
power of `f`, the restriction of a global section.  The classical Hartshorne II.5.3 argument: each
`D(r)` of a finite basic-open cover `{D(r)}` of `Spec R`, `y|_{D(f) ⊓ D(r)}` is `f^{-N}` times the
restriction of a section `b_r` on `D(r)` (`IsLocalizedModule.surj` of `Hfr` at `D(r)`, with a
common power `N`); on overlaps the `b_r` agree after a further power `f^P`
(`descent_overlap_agree` + `IsLocalizedModule.exists_of_eq` of `Hfr` at `D(r) ⊓ D(r')`), so
`f^P • b_r` glue
(`TopCat.Sheaf.existsUnique_gluing'`) to a global `x` with `x|_{D(f)} = f^{N+P} • y` (by sheaf
separatedness over the cover `{D(f) ⊓ D(r)}` of `D(f)`).  `Hfr` is the gated
local-tilde data. -/
private lemma descent_surj {R : CommRingCat.{u}} (M : (Spec R).Modules) (f : R)
    (t : Finset R) (hspan : Ideal.span (t : Set R) = ⊤)
    (Hfr : ∀ U : (Spec R).Opens, (∃ s : R, U = PrimeSpectrum.basicOpen s) →
      (∃ r ∈ t, U ≤ PrimeSpectrum.basicOpen r) →
      IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ U ≤ U)).op).hom)
    (y : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op (PrimeSpectrum.basicOpen f)))) :
    ∃ (x : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤))) (n : ℕ),
      f ^ n • y = ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x := by
  classical
  -- Stage 1: per cover element a section `a r` and a power `m r`.
  have perr : ∀ r : {x // x ∈ t}, ∃ (a : ToType ((modulesSpecToSheaf.obj M).presheaf.obj
        (.op (PrimeSpectrum.basicOpen (r:R))))) (m : ℕ),
        f ^ m • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen f)).op).hom y)
        = ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen (r:R))).op).hom a := by
    rintro ⟨r, hr⟩
    have hloc := Hfr (PrimeSpectrum.basicOpen r) ⟨r, rfl⟩ ⟨r, hr, le_refl _⟩
    obtain ⟨⟨a, s⟩, hs⟩ := hloc.surj (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen f)).op).hom y)
    obtain ⟨m, hm⟩ := s.2
    refine ⟨a, m, ?_⟩
    have hsR : (s : R) • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen f)).op).hom y)
        = ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen r)).op).hom a := hs
    rwa [← hm] at hsR
  choose a m hm using perr
  -- Stage 2: common power N and normalized sections b r := f^(N - m r) • a r.
  set N := Finset.univ.sup m with hN
  have hb : ∀ r : {x // x ∈ t},
      ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen (r:R))).op).hom (f ^ (N - m r) • a r)
        = f ^ N • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen f)).op).hom y) := by
    intro r
    have hle : m r ≤ N := Finset.le_sup (Finset.mem_univ r)
    set g := ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen (r:R))).op).hom with hg
    have hms : g (f ^ (N - m r) • a r) = f ^ (N - m r) • g (a r) := LinearMap.map_smul g _ (a r)
    rw [hms, ← hm r, ← pow_smul_eq_pow_sub_smul_pow_smul f hle]
  -- Stage 3: overlaps — common further power exists pairwise.
  have hover : ∀ i j : {x // x ∈ t}, ∃ p : ℕ,
      f ^ p • ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (i:R))).op).hom (f ^ (N - m i) • a i)
      = f ^ p • ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (j:R))).op).hom (f ^ (N - m j) • a j) := by
    intro i j
    have ai := descent_overlap_agree M f i N
      (PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)) inf_le_left y _ (hb i)
    have aj := descent_overlap_agree M f j N
      (PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)) inf_le_right y _ (hb j)
    have hloc := Hfr (PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R))
      ⟨(i:R) * (j:R), (PrimeSpectrum.basicOpen_mul (i:R) (j:R)).symm⟩ ⟨i, i.2, inf_le_left⟩
    obtain ⟨c, hc⟩ := hloc.exists_of_eq (ai.trans aj.symm)
    obtain ⟨p, hp⟩ := c.2
    have hp' : f ^ p = (c : R) := hp
    exact ⟨p, by rwa [hp']⟩
  choose p hp using hover
  -- Stage 4: global further power P, glue the compatible family.
  set P := Finset.univ.sup (fun i => Finset.univ.sup (fun j => p i j)) with hP
  have hPle : ∀ i j : {x // x ∈ t}, p i j ≤ P := fun i j =>
    le_trans (Finset.le_sup (f := fun j => p i j) (Finset.mem_univ j))
      (Finset.le_sup (f := fun i => Finset.univ.sup (fun j => p i j)) (Finset.mem_univ i))
  have hcompat : TopCat.Presheaf.IsCompatible (modulesSpecToSheaf.obj M).presheaf
      (fun r : {x // x ∈ t} => (PrimeSpectrum.basicOpen (r:R) : (Spec R).Opens))
      (fun r => f ^ P • (f ^ (N - m r) • a r)) := by
    intro i j
    change ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (i:R))).op).hom (f ^ P • (f ^ (N - m i) • a i))
      = ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (j:R))).op).hom (f ^ P • (f ^ (N - m j) • a j))
    have ms_i := LinearMap.map_smul ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (i:R))).op).hom (f ^ P) (f ^ (N - m i) • a i)
    have ms_j := LinearMap.map_smul ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (j:R))).op).hom (f ^ P) (f ^ (N - m j) • a j)
    have X : f ^ P • ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (i:R))).op).hom (f ^ (N - m i) • a i)
      = f ^ P • ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (j:R))).op).hom (f ^ (N - m j) • a j) := by
      rw [pow_smul_eq_pow_sub_smul_pow_smul f (hPle i j),
        pow_smul_eq_pow_sub_smul_pow_smul f (hPle i j), hp i j]
    exact ms_i.trans (X.trans ms_j.symm)
  obtain ⟨x, hx, -⟩ := TopCat.Sheaf.existsUnique_gluing' (modulesSpecToSheaf.obj M)
    (fun r : {x // x ∈ t} => (PrimeSpectrum.basicOpen (r:R) : (Spec R).Opens)) ⊤
    (fun r => homOfLE le_top) (le_of_eq (iSup_basicOpen_subtype_eq_top hspan).symm)
    (fun r => f ^ P • (f ^ (N - m r) • a r)) hcompat
  -- Stage 5: x|_{D(f)} = f^(N+P) • y, by separatedness over the cover {D(f) ⊓ D(r)} of D(f).
  refine ⟨x, P + N, ?_⟩
  have hcoverDf : (PrimeSpectrum.basicOpen f : (Spec R).Opens)
      ≤ ⨆ r : {x // x ∈ t}, (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)) := by
    rw [← inf_iSup_eq, iSup_basicOpen_subtype_eq_top hspan, inf_top_eq]
  refine TopCat.Sheaf.eq_of_locally_eq' (modulesSpecToSheaf.obj M)
    (fun r : {x // x ∈ t} => (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)))
    (PrimeSpectrum.basicOpen f) (fun r => homOfLE inf_le_left) hcoverDf
    (f ^ (P + N) • y)
    (((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x) ?_
  intro r
  -- LHS = f^(N+P) • (y|_{D(f) ⊓ D(r)})
  change ((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
        ≤ PrimeSpectrum.basicOpen f)).op).hom (f ^ (P + N) • y)
    = ((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
        ≤ PrimeSpectrum.basicOpen f)).op).hom
      (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x)
  -- compute the right-hand side via x|_{D(r)} = f^P • b r
  have ex := res_comp (modulesSpecToSheaf.obj M) (A := ⊤) (B := PrimeSpectrum.basicOpen f)
      (C := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R))
      le_top inf_le_left le_top x
  have ex2 := res_comp (modulesSpecToSheaf.obj M) (A := ⊤) (B := PrimeSpectrum.basicOpen (r:R))
      (C := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R))
      le_top inf_le_right le_top x
  have hxr : ((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen (r:R) ≤ ⊤)).op).hom x
      = f ^ P • (f ^ (N - m r) • a r) := hx r
  -- ρ[D(f),Dfr] (x|_{D(f)}) = ρ[⊤,Dfr] x = ρ[D(r),Dfr] (x|_{D(r)}) = ρ[D(r),Dfr] (f^P • b r)
  have hRHS : ((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
        ≤ PrimeSpectrum.basicOpen f)).op).hom
      (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x)
    = f ^ (P + N) • (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
          ≤ PrimeSpectrum.basicOpen f)).op).hom y) :=
    ex.trans (ex2.symm.trans ((congrArg _ hxr).trans
      ((LinearMap.map_smul _ (f ^ P) (f ^ (N - m r) • a r)).trans
        ((congrArg (f ^ P • ·) (hb r)).trans
          ((mul_smul (f ^ P) (f ^ N) _).symm.trans (congrArg (· • _) (pow_add f P N).symm))))))
  exact (LinearMap.map_smul _ (f ^ (P + N)) y).trans hRHS.symm

/-- The three `IsLocalizedModule` fields of the section-localization descent, from the localization
data `Hfr` at the basic opens `U` inside a cover member. -/
private theorem isLocalizedModule_basicOpen_descent_core {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (f : R) (t : Finset R) (hspan : Ideal.span (t : Set R) = ⊤)
    (Hfr : ∀ U : (Spec R).Opens, (∃ s : R, U = PrimeSpectrum.basicOpen s) →
      (∃ r ∈ t, U ≤ PrimeSpectrum.basicOpen r) →
      IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ U ≤ U)).op).hom) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom where
  map_units := map_units_restrict_basicOpen M f
  surj y := by
    obtain ⟨x, n, hxn⟩ := descent_surj M f t hspan Hfr y
    exact ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, hxn⟩
  exists_of_eq {x₁ x₂} h := by
    have hθ : ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom (x₁ - x₂) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨n, hn⟩ := descent_smul_eq_zero M f t hspan
      (fun r hr => Hfr (PrimeSpectrum.basicOpen r) ⟨r, rfl⟩ ⟨r, hr, le_refl _⟩) (x₁ - x₂) hθ
    exact ⟨⟨f ^ n, n, rfl⟩, sub_eq_zero.mp ((smul_sub (f ^ n) x₁ x₂).symm.trans hn)⟩

/-- **Section-localization descent from a local-tilde cover (keystone, D), cover form.**  Let
`M` be a sheaf of modules on `Spec R` and `f : R`.  Suppose `{D(r)}_{r ∈ t}` is a finite basic-open
cover of `Spec R` (`Ideal.span t = ⊤`) and for every open `U` contained in some cover member `D(r)`
(in particular each `D(r)` and each overlap `D(r) ⊓ D(r')`) the basic-open restriction
`Γ(M, U) → Γ(M, D(f) ⊓ U)` is a localization at `powers f` (`Hfr` — the gated local-tilde data).
Then the section restriction `Γ(M, ⊤) → Γ(M, D(f))` is `IsLocalizedModule (powers f)` over `R`.

This is the project-internal finite-equalizer/flatness descent of Stacks `lemma-invert-f-sections`
(Hartshorne II.5.3), built without the global affine `QCoh(Spec R) ≃ Mod R` equivalence (which is
the affine case itself): `map_units` holds for arbitrary `M` (`map_units_restrict_basicOpen`),
`surj'` is
`descent_surj`, and `exists_of_eq` is `descent_smul_eq_zero`.  The named keystone
`isLocalizedModule_basicOpen_descent` for quasi-coherent `M` is this lemma instantiated at the
cover `exists_finite_basicOpen_cover_le_quasicoherentData` once `Hfr` is produced from
`isIso_fromTildeΓ_restrict_basicOpen` (the slice→Spec-`R_r` section transport, the remaining gated
step). -/
private theorem isLocalizedModule_basicOpen_descent_of_cover {R : CommRingCat.{u}}
    (M : (Spec R).Modules)
    (f : R) (t : Finset R) (hspan : Ideal.span (t : Set R) = ⊤)
    (Hfr : ∀ U : (Spec R).Opens, (∃ r ∈ t, U ≤ PrimeSpectrum.basicOpen r) →
      IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ U ≤ U)).op).hom) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom :=
  isLocalizedModule_basicOpen_descent_core M f t hspan fun U _ hcov => Hfr U hcov

/-- **Section-localization descent from a local-tilde cover, basic-open hypothesis form.**

Same conclusion as `isLocalizedModule_basicOpen_descent_of_cover`, but the per-cover-element
localization data `Hfr` need only be supplied for *basic* opens `D(s) ≤ D(r)` (rather than every
open `U ≤ D(r)`).  This is the **instantiable** form of the cover-descent: the per-element
transport produces a localization only on the basic opens of the affine slice `Spec R_r` — a
general open of `Spec R_r` need not be quasi-compact, so the global Stacks
`lemma-invert-f-sections` is unavailable for it — while the sheaf-gluing engines
`descent_surj`/`descent_smul_eq_zero` only ever consult `Hfr` at the basic opens `D(r)` and the
overlaps `D(r) ⊓ D(r') = D(r·r')`.

It rebuilds the three `IsLocalizedModule` fields directly: `map_units` is
`map_units_restrict_basicOpen` (holds for arbitrary `M`), `surj` is `descent_surj` fed
the basic-open
`Hfr` (the open `U` it consults is always `D(s)`, so `Hfr s` supplies the datum after `U = D(s)` is
substituted), and `exists_of_eq` is `descent_smul_eq_zero` fed `Hfr` at each `D(r)`.  :
the named keystone `isLocalizedModule_basicOpen_descent` for quasi-coherent `M` is this lemma
instantiated at the cover `exists_finite_basicOpen_cover_le_quasicoherentData`, with the basic-open
`Hfr` produced from the affine transport `isIso_fromTildeΓ_restrict_basicOpen`. -/
theorem isLocalizedModule_basicOpen_descent_of_basicOpen_cover {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (f : R) (t : Finset R) (hspan : Ideal.span (t : Set R) = ⊤)
    (Hfr : ∀ s : R, (∃ r ∈ t, (PrimeSpectrum.basicOpen s : (Spec R).Opens)
        ≤ PrimeSpectrum.basicOpen r) →
      IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen s
            ≤ PrimeSpectrum.basicOpen s)).op).hom) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom :=
  isLocalizedModule_basicOpen_descent_core M f t hspan
    fun U hbo hcov => by obtain ⟨s, rfl⟩ := hbo; exact Hfr s hcov

/-! ## Supplementary results — `IsLocalizedModule` transport for  Hfr

The section-transport iso `gammaPullbackImageIso` is only an additive-group (`Ab`) isomorphism,
semilinear over the *source-scheme* section ring, whereas the `Hfr` hypothesis of
`isLocalizedModule_basicOpen_descent_of_cover` is an `IsLocalizedModule` statement `R`-linear over
the base ring `R`. Two Mathlib-absent transport ingredients bridge the gap:

* **(I)** `isLocalizedModule_of_ringEquiv_semilinear` — transport `IsLocalizedModule S g` across a
  ring-iso-`σ`-semilinear `AddEquiv` pair. Mathlib only has the same-ring `of_linearEquiv` /
  `of_linearEquiv_right`; the section iso crosses a ring iso, so this is the genuine gap.
* **(II)** `isLocalizedModule_restrictScalars_powers_algebraMap` — a localization at
  `powers (algebraMap R Rr f)` over a base-changed ring `Rr` (here `R` localized at `r`) is, after
  restriction of scalars, a localization at `powers f` over `R`.

Both are pure module algebra and Mathlib-absent at the pinned commit; project-bespoke. -/

/-- **(I) Ring-iso-semilinear `IsLocalizedModule` transport.** Given a ring isomorphism
`σ : R ≃+* R'`, two `σ`-semilinear additive isomorphisms `e₁ : M₁ ≃+ N₁`, `e₂ : M₂ ≃+ N₂` (i.e.
`eᵢ (a • x) = σ a • eᵢ x`), and an `R'`-linear map `h : N₁ →ₗ[R'] N₂` intertwining a localization
map `g` with the `eᵢ` (`h (e₁ x) = e₂ (g x)`), the map `h` is a localization at the image submonoid
`S.map σ`. Mathlib only provides the same-ring `IsLocalizedModule.of_linearEquiv`; this crosses a
ring iso, the form needed to turn the `Ab`/semilinear section iso `gammaPullbackImageIso` into the
`R`-linear `Hfr` data. -/
private theorem isLocalizedModule_of_ringEquiv_semilinear
    {R R' : Type*} [CommRing R] [CommRing R'] (σ : R ≃+* R')
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R' N₁] [AddCommGroup N₂] [Module R' N₂]
    (S : Submonoid R)
    (g : M₁ →ₗ[R] M₂) [IsLocalizedModule S g]
    (e₁ : M₁ ≃+ N₁) (e₂ : M₂ ≃+ N₂)
    (he₁ : ∀ (a : R) (x : M₁), e₁ (a • x) = σ a • e₁ x)
    (he₂ : ∀ (a : R) (x : M₂), e₂ (a • x) = σ a • e₂ x)
    (h : N₁ →ₗ[R'] N₂)
    (hh : ∀ x, h (e₁ x) = e₂ (g x)) :
    IsLocalizedModule (S.map (σ : R →+* R')) h where
  map_units x := by
    obtain ⟨s, hs, hsx⟩ := x.2
    rw [Module.End.isUnit_iff]
    have hsrc := IsLocalizedModule.map_units g ⟨s, hs⟩
    rw [Module.End.isUnit_iff] at hsrc
    have hfun : (⇑(algebraMap R' (Module.End R' N₂) (↑x : R')))
        = ⇑e₂ ∘ ⇑(algebraMap R (Module.End R M₂) (⟨s, hs⟩ : S)) ∘ ⇑e₂.symm := by
      funext y
      rw [Module.algebraMap_end_apply, Function.comp_apply, Function.comp_apply,
        Module.algebraMap_end_apply, he₂, e₂.apply_symm_apply]
      congr 1
      exact hsx.symm
    rw [hfun]
    exact e₂.bijective.comp (hsrc.comp e₂.symm.bijective)
  surj y := by
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj S g (e₂.symm y)
    refine ⟨⟨e₁ x, ⟨σ ↑s, ↑s, s.2, rfl⟩⟩, ?_⟩
    have he : e₂ ((↑s : R) • e₂.symm y) = e₂ (g x) := congrArg e₂ hx
    rw [he₂, e₂.apply_symm_apply, ← hh] at he
    exact he
  exists_of_eq {y₁ y₂} heq := by
    have h1 : e₂ (g (e₁.symm y₁)) = e₂ (g (e₁.symm y₂)) := by
      rwa [← hh, ← hh, e₁.apply_symm_apply, e₁.apply_symm_apply]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := g) (e₂.injective h1)
    refine ⟨⟨σ ↑c, ↑c, c.2, rfl⟩, ?_⟩
    have hc' : (↑c : R) • e₁.symm y₁ = (↑c : R) • e₁.symm y₂ := hc
    have hcc := congrArg e₁ hc'
    rw [he₁, he₁, e₁.apply_symm_apply, e₁.apply_symm_apply] at hcc
    exact hcc

/-- A power of `f` acts as its image `algebraMap R Rr f ^ n` in a scalar tower. -/
private lemma pow_smul_eq_of_algebraMap_pow_eq {R Rr V : Type*} [CommRing R] [CommRing Rr]
    [Algebra R Rr] [AddCommGroup V] [Module R V] [Module Rr V] [IsScalarTower R Rr V]
    {f : R} {n : ℕ} {s : Rr} (hn : algebraMap R Rr f ^ n = s) (y : V) :
    (f ^ n : R) • y = s • y := by
  rw [← hn, ← map_pow, algebraMap_smul]

/-- **(II) Localization at a base-changed submonoid descends to the base ring.** If `g` is
`Rr`-linear and exhibits a localization at `powers (algebraMap R Rr f)` over a base-changed ring
`Rr` (an algebra over `R` — here `R` localized at some `r`), then its restriction of scalars to `R`
is a localization
at `powers f` over `R`. This lets the `R_r`-level localization that the affine case (`IsIso
fromTildeΓ`) produces
on the slice `Spec R_r` be read back as the `R`-level `Hfr` data the cover-form descent consumes.
Mathlib-absent; -/
private theorem isLocalizedModule_restrictScalars_powers_algebraMap
    {R Rr : Type*} [CommRing R] [CommRing Rr] [Algebra R Rr]
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [Module Rr M₁] [IsScalarTower R Rr M₁]
    [AddCommGroup M₂] [Module R M₂] [Module Rr M₂] [IsScalarTower R Rr M₂]
    (f : R) (g : M₁ →ₗ[Rr] M₂)
    [IsLocalizedModule (Submonoid.powers (algebraMap R Rr f)) g] :
    IsLocalizedModule (Submonoid.powers f) (g.restrictScalars R) where
  map_units x := by
    obtain ⟨n, hn⟩ := x.2
    have hn' : f ^ n = ↑x := hn
    rw [Module.End.isUnit_iff]
    have hmem : (algebraMap R Rr f) ^ n ∈ Submonoid.powers (algebraMap R Rr f) := ⟨n, rfl⟩
    have hsrc := IsLocalizedModule.map_units g ⟨_, hmem⟩
    rw [Module.End.isUnit_iff] at hsrc
    have hfun : ⇑(algebraMap R (Module.End R M₂) (↑x : R))
        = ⇑(algebraMap Rr (Module.End Rr M₂) ((algebraMap R Rr f) ^ n)) := by
      funext z
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← hn']
      exact pow_smul_eq_of_algebraMap_pow_eq rfl z
    rwa [hfun]
  surj y := by
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers (algebraMap R Rr f)) g y
    obtain ⟨n, hn⟩ := s.2
    have hn' : (algebraMap R Rr f) ^ n = ↑s := hn
    refine ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, ?_⟩
    change (f ^ n : R) • y = (g.restrictScalars R) x
    rwa [pow_smul_eq_of_algebraMap_pow_eq hn' y, LinearMap.coe_restrictScalars]
  exists_of_eq {x₁ x₂} heq := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (algebraMap R Rr f))
      (f := g) heq
    obtain ⟨n, hn⟩ := c.2
    have hn' : (algebraMap R Rr f) ^ n = ↑c := hn
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    change (f ^ n : R) • x₁ = (f ^ n : R) • x₂
    rwa [pow_smul_eq_of_algebraMap_pow_eq hn', pow_smul_eq_of_algebraMap_pow_eq hn']

/-! ## Supplementary results — Hfr: pullback-section transport

The remaining gated ingredient of the named keystone
`isLocalizedModule_basicOpen_descent` is the **section-level** analogue of the affine case's
object-level
transport: for an open immersion `f : X ⟶ Y` and a sheaf of modules `M` on `Y`, the sections of the
geometric pullback `(pullback f).obj M` over an open `U ⊆ X` are canonically identified with the
sections of `M` over the image `f ''ᵁ U`.

The construction is `Γ(-, U)` applied to the inverse of Mathlib's `restrictFunctorIsoPullback f`
(`restrictFunctor f ≅ pullback f`) at `M`, using the *definitional* identity
`Γ((restrictFunctor f).obj M, U) = Γ(M, f ''ᵁ U)` (`Scheme.Modules.restrict_obj`, `rfl`). Because
both sides are `Γ(-, U)` of a single fixed module isomorphism, naturality in `U` (intertwining the
presheaf restriction maps) is free: it is the naturality of the underlying abelian-presheaf
morphism. Mathlib-absent at the pinned commit; project-bespoke. -/

/-- **Global sections of a pullback along an open immersion are sections over the image**
(the affine case, Hfr section transport, general open). For an open immersion `f : X ⟶ Y`, a sheaf
of modules
`M` on `Y`, and an open `U ⊆ X`, the additive groups of sections satisfy
`Γ((pullback f).obj M, U) ≅ Γ(M, f ''ᵁ U)`. This is `Γ(-, U)` of `(restrictFunctorIsoPullback f)⁻¹`
at `M`; the codomain is `Γ((restrictFunctor f).obj M, U) = Γ(M, f ''ᵁ U)` definitionally.
Naturality in `U` is `gammaPullbackImageIso_hom_naturality`. -/
noncomputable def gammaPullbackImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : X.Opens) :
    Γ((Scheme.Modules.pullback f).obj M, U) ≅ Γ(M, f ''ᵁ U) :=
  (Scheme.Modules.toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (Opposite.op U)).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback f).symm.app M)

/-- **The pullback-section comparison intertwines the restriction maps** (the affine case, Hfr,
naturality).
For opens `V ≤ U` of `X`, `gammaPullbackImageIso` commutes with the presheaf restriction maps of
`(pullback f).obj M` and of `M` (along the image inclusion `f ''ᵁ V ≤ f ''ᵁ U`). This is the
naturality of the underlying morphism of abelian presheaves. -/
theorem gammaPullbackImageIso_hom_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f]
    (M : Y.Modules) {U V : X.Opens} (i : V ⟶ U) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map i.op ≫ (gammaPullbackImageIso f M V).hom
      = (gammaPullbackImageIso f M U).hom ≫ M.presheaf.map (f.opensFunctor.map i).op :=
    (((Scheme.Modules.restrictFunctorIsoPullback f).symm.app M).hom.mapPresheaf).naturality i.op

/- **Global sections of a pullback along an open immersion are sections over the range**
(the affine case, Hfr section transport). The `U = ⊤` instance of `gammaPullbackImageIso`:
`Γ((pullback f).obj M, ⊤) ≅ Γ(M, f.opensRange)`, using `f ''ᵁ ⊤ = f.opensRange`. Once this lands
the named-form descent `isLocalizedModule_basicOpen_descent` and the affine case follow. -/
/-- **Open-immersion structure-sheaf ring iso on an image open** (the affine case, Hfr
semilinearity).
For an open immersion `j : X ⟶ Y` and an open `V ⊆ X`, the immersion is an isomorphism onto its
image `j ''ᵁ V`, so pulling structure-sheaf sections back gives a ring isomorphism
`σ_V : Γ(X, V) ≃+* Γ(Y, j ''ᵁ V)`. This is `(j.appIso V)⁻¹` packaged as a `RingEquiv`; it is the
`σ` along which `gammaPullbackImageIso_hom_semilinear` is semilinear, the form bridge (I)
`isLocalizedModule_of_ringEquiv_semilinear` consumes.

The direction is source `→` image (so `σ_V a` lands in `Γ(Y, j ''ᵁ V)` for `a : Γ(X, V)`, the
section ring acting on the pullback module's sections). -/
noncomputable def gammaImageRingEquiv {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (V : X.Opens) : Γ(X, V) ≃+* Γ(Y, j ''ᵁ V) :=
  (j.appIso V).commRingCatIsoToRingEquiv.symm

/-- **Semilinearity of the pullback section transport** (semilinearity step). The forward map
of `gammaPullbackImageIso` is `σ_V`-semilinear (`σ_V = gammaImageRingEquiv`): for `a : Γ(X, V)` a
section of the structure sheaf and `x` a section of the pullback module,
`hom (a • x) = σ_V a • hom x`. The pullback-side action is the structure-sheaf action through
the pullback's `mapPresheaf`; the action on the `M` side is `M`'s action through `σ_V`. -/
theorem gammaPullbackImageIso_hom_semilinear {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (M : Y.Modules) (V : X.Opens) (a : Γ(X, V))
    (x : Γ((Scheme.Modules.pullback j).obj M, V)) :
    (gammaPullbackImageIso j M V).hom (a • x)
      = gammaImageRingEquiv j V a • (gammaPullbackImageIso j M V).hom x := by
  -- `gammaPullbackImageIso j M V`'s forward map is `Γ(-, V)` of the `Ab`-morphism
  -- `ψ := ((restrictFunctorIsoPullback j).symm.app M).hom`, i.e. the section map `ψ.app V`.
  simp only [gammaPullbackImageIso, Functor.mapIso_hom, Functor.comp_map,
    Scheme.Modules.toPresheaf_map]
  -- `ψ.app V` is `Γ(X, V)`-linear (`Hom.app_smul`): `ψ.app V (a • x) = a • ψ.app V x`, the
  -- `Γ(X, V)`-action being `restrictFunctor`'s `restrictScalars`-action along `(j.appIso V).inv`.
  -- `refine … .trans ?_` rather than `erw`: the final defeq check of `refine` absorbs the
  -- instance-path mismatch in the `Γ(X, V)`-action that `rw` cannot abstract across.
  refine (Scheme.Modules.Hom.app_smul _ a x).trans ?_
  -- The `restrictScalars` action `a •_{restrict} m` is defeq to `(j.appIso V).inv a •_M m`,
  -- and `σ_V a = gammaImageRingEquiv j V a = (j.appIso V).inv a`, so the two sides agree by `rfl`.
  rfl

end Scheme.Modules

end BasicOpenPresentationDescent

end AlgebraicGeometry
