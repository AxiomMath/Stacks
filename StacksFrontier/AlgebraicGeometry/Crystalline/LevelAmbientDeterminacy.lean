module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelCrystalDeterminacy
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AffineRestrictionPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom

/-!
# `hlevel`: a morphism out of a quasi-coherent crystal is determined by its sections over a level

`StacksFrontier/AlgebraicGeometry/Crystalline/LevelCrystalDeterminacy.lean` reduces the hypothesis
`hdet` of the faithfulness half of [Stacks, Proposition 60.17.4, Tag 07JH] to two hypotheses
about the levels alone, and discharges the half of it that is about the site.  One of the two,
`hlevel`, is the passage from the sections of a crystal over a single level `T_e` to the
restricted sheaf on the ambient scheme of `T_e`: that two morphisms agreeing on `Γ(T_e, ℱ)` agree
as morphisms `ℱ_{T_e} ⟶ 𝒢_{T_e}` of sheaves of `𝒪_{T_e}`-modules.

This module proves it.  The ambient scheme of a level is affine, and a morphism out of a
quasi-coherent module on an affine scheme is determined by its action on global sections; what
stood in the way was only that the two sides speak about different sheaves of rings, and the
bridge between them is already in the tree.

## The bridge

`...CohomologyRestriction.moduleRestrictionSheaf` produces a sheaf of modules over
`...Thickening.ringRestrictionSheaf`, whose sections over an open `W` of the ambient scheme are
the global sections of the open subscheme `W`, while
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top` is a statement about a module over
`AlgebraicGeometry.Scheme.ringCatSheaf`, whose sections over `W` are the sections of the
structure sheaf over `W`.  The two sheaves of rings are identified by
`...Thickening.ringRestrictionSheafStructureIso`, and restriction of scalars along that
isomorphism carries quasi-coherence, by
`Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso`.  Quasi-coherence then
crosses from `SheafOfModules.IsQuasicoherentOnSite` to Mathlib's
`SheafOfModules.IsQuasicoherent` by
`SheafOfModules.IsQuasicoherentOnSite.isQuasicoherent`, whose size hypothesis
`UnivLE.{max u v r, r}` reads `UnivLE.{u, u}` on the Zariski site of a `Type u`-scheme and is
therefore automatic.  Both steps are the small-site counterparts of the big-site constructions of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsModules/AffineRestrictionPresentation.lean`.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isQuasicoherent_ambientModuleRestriction` — **the restriction `ℱ_T` of a locally
  quasi-coherent sheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object of `Cris(X/S)`,
  read over the structure sheaf of that scheme, is quasi-coherent in the sense of Mathlib.**
* `moduleRestrictionSheafMap_eq_of_forall_app_eq` — **the statement `hlevel` makes, for a single
  object with affine ambient scheme**: two morphisms of locally quasi-coherent sheaves of
  `𝒪_{X/S}`-modules which agree on the sections over an object `A` whose ambient scheme is affine
  have equal restrictions `ℱ_A ⟶ 𝒢_A`.
* `levelRestriction_of_isAffine` — the same for the levels of a system, in the exact shape the
  hypothesis `hlevel` of `...SmallSite.det_of_levelRestriction` asks for.
* `det_of_levelSections` — **`hdet` with `hlevel` discharged**: two morphisms of crystals in
  quasi-coherent `𝒪_{X/S}`-modules agreeing on `Γ(T_e, ℱ)` for every level are equal, given only
  the weak finality of the levels.
* `LevelComparison07JG.faithful_functor_of_levelSections` and
  `LevelReduction07JG.faithful_functor07JG_of_levelSections` — **the faithfulness half of
  [Stacks, Tag 07JH] with `hlevel` gone.**

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no tag attribute is placed
in this module.**  The tag
asserts that the functor is an equivalence; only faithfulness is at issue here, and the full and
essentially-surjective halves are untouched.  What the faithfulness half still costs, after this
module, is

* `hlev`, the **weak finality of the levels** — a level `level B` and a morphism
  `B ⟶ T_{level B}` for every object `B` of `Cris(X/S)`, carried as data.  This is
  [Stacks, Lemma 60.5.6, Tag 07HP]; see the module documentation of
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelCrystalDeterminacy.lean` for what stands
  between the tag and it;
* `hL`, that the system is the degree-zero member of `...SmallSite.wholeSpaceSystem`, which is a
  **delimiter and not a weakening** — it is the field
  `...SmallSite.Reduction07JG.levelSystem_isLevel` on the nose and is refuted by the degenerate
  system (`...SmallSite.not_levelSystem_isLevel_preReduction07JGBot`);
* `hlqc` and `hsurj`, the source's own standing hypotheses at [Stacks, Tag 07JN].

`hlevel` is **no longer** among them: it was the one hypothesis below standing in for a result
the library does not have, and it is proved here.  `hlev` is still carried, and it is still a
hypothesis named for a result the tree does not assemble — so the faithfulness statements below
remain conditional and carry no tag attribute, quite apart from the tag being an equivalence
statement.  What has changed is that the condition is now weak finality alone.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u uI

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace SmallSite

open CohomologyRestriction

/-! ### The restriction to the ambient scheme, over the structure sheaf of that scheme -/

/-- **Stacks Project, Tag 07IQ.**  The restriction `ℱ_T` of a sheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)` to the ambient scheme of an object, with its scalars read in the structure sheaf of
that scheme rather than in the restriction of `𝒪_{X/S}`.

This is the small-site counterpart of
`Crystalline.GlobalCrystallineSituation.Thickening.ambientModuleRestriction`, and it is the same
restriction of scalars along the same isomorphism of sheaves of rings: the restriction of
`𝒪_{X/S}` to the opens of the ambient scheme of an object of `Cris(X/S)` is the restriction at
the underlying object of `CRIS(X/S)`, by
`...SmallSite.CohomologyRestriction.ringRestriction_eq`, so the identification
`...Thickening.ringRestrictionSheafStructureIso` applies unchanged.  The module is unchanged on
sections. -/
noncomputable def ambientModuleRestriction (M : SheafOfModules.{u} (structureSheaf S))
    (A : CrystallineThickening S) :
    SheafOfModules.{u} A.obj.thickening.target.scheme.ringCatSheaf :=
  (SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A.obj).inv).obj
    (moduleRestrictionSheaf M A)

/-- The restriction of a morphism of sheaves of `𝒪_{X/S}`-modules to the ambient scheme of an
object, read over the structure sheaf of that scheme. -/
noncomputable def ambientModuleRestrictionMap {M N : SheafOfModules.{u} (structureSheaf S)}
    (psi : M ⟶ N) (A : CrystallineThickening S) :
    ambientModuleRestriction M A ⟶ ambientModuleRestriction N A :=
  (SheafOfModules.restrictScalars
    (Thickening.ringRestrictionSheafStructureIso A.obj).inv).map (moduleRestrictionSheafMap psi A)

/-- **Local quasi-coherence, read with the sheaf-of-modules restriction.**  The definition of
`...SmallSite.IsLocallyQuasiCoherent` quantifies over the sheaf condition of the presheaf-level
restriction; that condition always holds, and the sheaf of modules it produces is
`...SmallSite.CohomologyRestriction.moduleRestrictionSheaf`. -/
theorem isQuasicoherentOnSite_moduleRestrictionSheaf
    {M : SheafOfModules.{u} (structureSheaf S)} (hM : IsLocallyQuasiCoherent M)
    (A : CrystallineThickening S) : (moduleRestrictionSheaf M A).IsQuasicoherentOnSite :=
  (hM A).choose_spec

/-- **The restriction of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` to
the ambient scheme of an object is quasi-coherent in the sense of Mathlib.**

Two steps: restriction of scalars along the isomorphism
`...Thickening.ringRestrictionSheafStructureIso` carries quasi-coherence on the site, and on the
Zariski site of a scheme quasi-coherence on the site is Mathlib's — the size hypothesis of
`SheafOfModules.IsQuasicoherentOnSite.isQuasicoherent` reads `UnivLE.{u, u}` there. -/
theorem isQuasicoherent_ambientModuleRestriction
    {M : SheafOfModules.{u} (structureSheaf S)} (hM : IsLocallyQuasiCoherent M)
    (A : CrystallineThickening S) : (ambientModuleRestriction M A).IsQuasicoherent :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso _ _
    (isQuasicoherentOnSite_moduleRestrictionSheaf hM A)).isQuasicoherent

/-! ### Determinacy over a single object with affine ambient scheme -/

/-- **A morphism of sheaves of `𝒪_{X/S}`-modules is determined on the restrictions to the opens
of the ambient scheme of an object by its component at that object**, when the ambient scheme is
affine and both sheaves are locally quasi-coherent.  This is the statement the hypothesis
`hlevel` of `...SmallSite.det_of_levelRestriction` makes, at one object.

The component at the object determines the component at its restriction to `⊤`, the restriction
map along `...SmallSite.CrystallineThickening.restrictOpenHom` being invertible there
(`...SmallSite.CrystallineThickening.isIso_restrictOpenHom_top`); and the component at `⊤` is the
action on global sections of the restricted morphism, read over the structure sheaf of the
ambient scheme.  Quasi-coherence and affineness then give the whole morphism, by
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top`. -/
theorem moduleRestrictionSheafMap_eq_of_forall_app_eq
    {F G : SheafOfModules.{u} (structureSheaf S)} (hF : IsLocallyQuasiCoherent F)
    (hG : IsLocallyQuasiCoherent G) {psi chi : F ⟶ G} (A : CrystallineThickening S)
    [IsAffine A.obj.thickening.target.scheme]
    (h : ∀ s : (F.val : PresheafOfModules.{u} (crisRing S)).obj (op A),
      (PresheafOfModules.Hom.app psi.val (op A)).hom s =
        (PresheafOfModules.Hom.app chi.val (op A)).hom s) :
    moduleRestrictionSheafMap psi A = moduleRestrictionSheafMap chi A := by
  have := CrystallineThickening.isIso_restrictOpenHom_top A
  have := isQuasicoherent_ambientModuleRestriction hF A
  have := isQuasicoherent_ambientModuleRestriction hG A
  -- The component at `A.restrictOpen ⊤`, from the component at `A`.
  have hcomp : (inv (A.restrictOpenHom ⊤)).op ≫ (A.restrictOpenHom ⊤).op =
      𝟙 (op (A.restrictOpen (⊤ : A.obj.thickening.target.scheme.Opens))) :=
    congrArg Quiver.Hom.op (IsIso.hom_inv_id (A.restrictOpenHom ⊤))
  have hid : ∀ s : (F.val : PresheafOfModules.{u} (crisRing S)).obj
      (op (A.restrictOpen (⊤ : A.obj.thickening.target.scheme.Opens))),
      (F.val : PresheafOfModules.{u} (crisRing S)).map (A.restrictOpenHom ⊤).op
          ((F.val : PresheafOfModules.{u} (crisRing S)).map
            (inv (A.restrictOpenHom ⊤)).op s) = s := by
    intro s
    rw [← PresheafOfModules.map_comp_apply,
      (F.val : PresheafOfModules.{u} (crisRing S)).congr_map_apply hcomp,
      ← PresheafOfModules.presheaf_map_apply_coe,
      (F.val : PresheafOfModules.{u} (crisRing S)).presheaf.map_id]
    rfl
  have htop : ∀ s : (F.val : PresheafOfModules.{u} (crisRing S)).obj
      (op (A.restrictOpen (⊤ : A.obj.thickening.target.scheme.Opens))),
      (PresheafOfModules.Hom.app psi.val
            (op (A.restrictOpen (⊤ : A.obj.thickening.target.scheme.Opens)))).hom s =
        (PresheafOfModules.Hom.app chi.val
            (op (A.restrictOpen (⊤ : A.obj.thickening.target.scheme.Opens)))).hom s := by
    intro s
    rw [← hid s]
    exact (PresheafOfModules.naturality_apply psi.val (A.restrictOpenHom ⊤).op _).trans
      ((congrArg (fun y ↦ ((G.val : PresheafOfModules.{u} (crisRing S)).map
            (A.restrictOpenHom ⊤).op).hom y) (h _)).trans
        (PresheafOfModules.naturality_apply chi.val (A.restrictOpenHom ⊤).op _).symm)
  -- Affineness and quasi-coherence on the ambient scheme.
  have key : ambientModuleRestrictionMap psi A = ambientModuleRestrictionMap chi A :=
    Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top fun a ↦ htop a
  -- Restriction of scalars is faithful, so the equality descends.
  refine SheafOfModules.Hom.ext (Functor.map_injective
    (PresheafOfModules.restrictScalars
      (Thickening.ringRestrictionSheafStructureIso A.obj).inv.hom) ?_)
  exact congrArg SheafOfModules.Hom.val key

/-! ### `hlevel` for the levels, and faithfulness with it gone -/

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  {L : LevelScalars07JG S D}

/-- **`hlevel` for a system of levels whose ambient schemes are affine.**  This is the hypothesis
`hlevel` of `...SmallSite.det_of_levelRestriction` in its exact shape, proved: agreement of two
morphisms of crystals in quasi-coherent `𝒪_{X/S}`-modules on `Γ(T_e, ℱ)` for every level upgrades
to agreement of the restricted morphisms `ℱ_{T_e} ⟶ 𝒢_{T_e}`.

The ambient scheme of a level is affine by
`...SmallSite.isAffine_target_levelSystem`, and the upgrade at one object is
`...SmallSite.moduleRestrictionSheafMap_eq_of_forall_app_eq`.  The hypothesis `hlqc` supplies the
local quasi-coherence of the two sheaves; it is the source's own standing hypothesis (1) at
[Stacks, Tag 07JN]. -/
theorem levelRestriction_of_isAffine [IsAffine S.X] [IsAffine S.S.scheme]
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G)
    (hs : ∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
          (op (L.levelSystem.obj e))).hom s =
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
          (op (L.levelSystem.obj e))).hom s) (e : ℕ) :
    moduleRestrictionSheafMap ((quasiCoherentCrystalι S).map psi) (L.levelSystem.obj e) =
      moduleRestrictionSheafMap ((quasiCoherentCrystalι S).map chi) (L.levelSystem.obj e) :=
  have := isAffine_target_levelSystem hp hL e
  moduleRestrictionSheafMap_eq_of_forall_app_eq (hlqc F) (hlqc G) (L.levelSystem.obj e) (hs e)

/-- **`hdet` from the weak finality of the levels alone.**  Two morphisms of crystals in
quasi-coherent `𝒪_{X/S}`-modules which agree on `Γ(T_e, ℱ)` for every level `T_e` are equal.

This is `...SmallSite.det_of_levelRestriction` with its hypothesis `hlevel` discharged by
`...SmallSite.levelRestriction_of_isAffine`.  What remains is the weak finality of the levels,
carried as the data `level` and `hlev`, the delimiter `hL`, and the standing hypothesis `hlqc` of
[Stacks, Tag 07JN]. -/
theorem det_of_levelSections [IsAffine S.X] [IsAffine S.S.scheme]
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (level : CrystallineThickening S → ℕ)
    (hlev : ∀ B : CrystallineThickening S, B ⟶ L.levelSystem.obj (level B))
    {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G)
    (hs : ∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
          (op (L.levelSystem.obj e))).hom s =
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
          (op (L.levelSystem.obj e))).hom s) :
    psi = chi :=
  det_of_levelRestriction level hlev
    (levelRestriction_of_isAffine hp hL hlqc) psi chi hs

/-- **The faithfulness half of [Stacks, Tag 07JH] for the constructed functor, with `hlevel`
gone.**  `...SmallSite.LevelComparison07JG.faithful_functor_of_levelRestriction` runs on the weak
finality of the levels together with `hlevel`; here `hlevel` is
`...SmallSite.levelRestriction_of_isAffine`, so the only hypothesis about the levels that remains
is their weak finality, carried as the data `level` and `hlev`.

`hL` is a **delimiter and not a weakening**: it is the field
`...SmallSite.Reduction07JG.levelSystem_isLevel` on the nose, and it is refuted by the degenerate
system over the empty open of `X`
(`...SmallSite.not_levelSystem_isLevel_preReduction07JGBot`).  `hlqc` and `hsurj` are the
source's own standing hypotheses at [Stacks, Tag 07JN].

No tag attribute is placed: [Stacks, Tag 07JH] asserts that the functor is an equivalence, and
only faithfulness is proved here. -/
theorem LevelComparison07JG.faithful_functor_of_levelSections [IsAffine S.X]
    [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (C : LevelComparison07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (hsurj : ∀ F : QuasiCoherentCrystal S,
      CohomologyRestriction.IsSurjectiveComparison F.obj.val)
    (level : CrystallineThickening S → ℕ)
    (hlev : ∀ B : CrystallineThickening S, B ⟶ L.levelSystem.obj (level B)) :
    Functor.Faithful C.functor :=
  C.faithful_functor_of_levelRestriction hp hL hlqc hsurj level hlev
    fun psi chi ↦ levelRestriction_of_isAffine hp hL hlqc psi chi

/-- **The faithfulness half of [Stacks, Tag 07JH] itself, with `hlevel` gone.**  The passage from
the constructed functor to the tag's own functor costs nothing, by
`...SmallSite.faithful_functor07JG_iff`.

No tag attribute is placed: the tag asserts that the functor is an equivalence, and the full and
essentially-surjective halves are untouched. -/
theorem LevelReduction07JG.faithful_functor07JG_of_levelSections [IsAffine S.X]
    [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (R : LevelReduction07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (hsurj : ∀ F : QuasiCoherentCrystal S,
      CohomologyRestriction.IsSurjectiveComparison F.obj.val)
    (level : CrystallineThickening S → ℕ)
    (hlev : ∀ B : CrystallineThickening S, B ⟶ L.levelSystem.obj (level B)) :
    Functor.Faithful (functor07JG (R.toReduction07JG (hp := hp) hL)) :=
  R.faithful_functor07JG_of_levelRestriction hp hL hlqc hsurj level hlev
    fun psi chi ↦ levelRestriction_of_isAffine hp hL hlqc psi chi

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
