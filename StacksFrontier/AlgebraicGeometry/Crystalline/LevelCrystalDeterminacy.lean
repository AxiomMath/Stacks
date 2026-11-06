module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelFaithfulSurjectivity

/-!
# `hdet` reduced to the levels: a crystal morphism is determined by its restrictions

`StacksFrontier/AlgebraicGeometry/Crystalline/LevelFaithfulSurjectivity.lean` leaves the faithfulness
half of [Stacks, Proposition 60.17.4, Tag 07JH] standing on one hypothesis, `hdet`: that a
morphism of crystals in quasi-coherent `𝒪_{X/S}`-modules is determined by its restrictions to the
levels.  As stated there, `hdet` quantifies over **every object of `Cris(X/S)`** — it is the
assertion that two morphisms agreeing on `Γ(T_e, ℱ)` for every `e` are equal, and equality of
morphisms of sheaves on the site is equality over every object.

This module removes that quantifier.  The crystal condition
`Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal` is **used**, not carried: for a
crystal `ℱ` and a morphism `g : B ⟶ T` of `Cris(X/S)`, the comparison map
`c_g : g^* ℱ_T ⟶ ℱ_B` is an isomorphism, and the comparison map is natural in the module
(`...CohomologyRestriction.moduleComparisonSheaf_naturality`), so cancelling the isomorphism
carries an agreement of two crystal morphisms *on the ambient scheme of `T`* to an agreement on
the ambient scheme of `B`.  Since the levels are weakly final in the sense that every object
receives a morphism from one of them, this reduces `hdet` to a statement about a single level.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation`, the determinacy results
in its subnamespace `SmallSite`.

* `SmallSite.app_eq_of_moduleRestrictionSheafMap_eq` — **two morphisms of sheaves of
  `𝒪_{X/S}`-modules which agree on the ambient scheme of one object have the same component at
  that object.**  No hypothesis on either sheaf.
* `SmallSite.eq_of_forall_moduleRestrictionSheafMap_eq` — **two morphisms of sheaves of
  `𝒪_{X/S}`-modules which agree on the ambient scheme of every object are equal.**  No hypothesis
  on either sheaf.
* `SmallSite.moduleRestrictionSheafMap_eq_of_hom` — **the crystal step.**  If `ℱ` is a crystal,
  `g : B ⟶ T` is a morphism of `Cris(X/S)` and two morphisms out of `ℱ` agree on the ambient
  scheme of `T`, then they agree on the ambient scheme of `B`.
* `SmallSite.eq_of_moduleRestrictionSheafMap_eq_of_hom` — the two together: a morphism out of a
  crystal is determined by its restrictions to any family of objects which every object maps to.
* `SmallSite.LevelComparison07JG.faithful_functor_of_levelRestriction` and
  `SmallSite.LevelReduction07JG.faithful_functor07JG_of_levelRestriction` — **the faithfulness
  half of [Stacks, Tag 07JH] with `hdet` replaced by a hypothesis about the levels alone**,
  together with the weak finality of the levels and the two hypotheses of [Stacks, Tag 07JN].

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no tag attribute is placed
in this module.**  The full and
essentially-surjective halves are untouched and `Functor.IsEquivalence` is not mentioned below.
What changes against `LevelFaithfulSurjectivity.lean` is the *shape* of what the faithfulness half
still costs.  There `hdet` was one hypothesis about the whole site; here it is split into two
hypotheses, neither of which mentions an arbitrary object of `Cris(X/S)`:

* `hlev`, the **weak finality of the levels**: a level `level B` and a morphism
  `B ⟶ T_{level B}` for every object `B`.  This is [Stacks, Lemma 60.5.6, Tag 07HP], formalized as
  `Crystalline.exists_levelEnvelope_hom` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/AffineSite/Completed.lean`, read across
  `...wholeSiteEquivLittleAffine` — except that the levels 07HP produces are the envelopes of the
  truncations `P/(p)^e` of the polynomial presentation (`Crystalline.levelEnvelope`) while the
  levels here are the truncations `D/(p)^{N + e}` of the completed envelope
  (`Crystalline.levelThickening`, through `Crystalline.uniformLevelSystem`).  Identifying the two
  families is [Stacks, Tag 07KG] and [Stacks, Tag 07KH]; the tree has
  `Crystalline.completedEnvelope_isLimit` and `...SmallSite.envelopeLevelRingLimitEquiv` toward it
  and not the identification.  It is carried here as data rather than as an existence statement
  because the conclusion consumes the morphism and not merely its existence.
* `hlevel`, the **upgrade from the sections over a level to the restricted sheaf on it**: that two
  morphisms agreeing on `Γ(T_e, ℱ)` for every `e` agree as morphisms
  `ℱ_{T_e} ⟶ 𝒢_{T_e}` of sheaves of `𝒪_{T_e}`-modules.  This is a statement about **one object**
  of the site and nothing else, and it is where quasi-coherence has to enter: `ℱ_{T_e}` is a
  quasi-coherent sheaf on the ambient scheme of `T_e`, which is affine, and a morphism out of a
  quasi-coherent module on an affine scheme is determined by its sections over the whole scheme.
  **It is proved**, in
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelAmbientDeterminacy.lean`, as
  `...SmallSite.levelRestriction_of_isAffine`, from
  `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top` together with the two change-of-base
  steps that file assembles: restriction of scalars along
  `...Thickening.ringRestrictionSheafStructureIso`, which identifies the restriction of
  `𝒪_{X/S}` to the ambient scheme with that scheme's structure sheaf, and
  `SheafOfModules.IsQuasicoherentOnSite.isQuasicoherent`, whose size hypothesis is automatic on
  the Zariski site of a scheme.  It is carried as a hypothesis here only because this module does
  not import the affine theory; see `...SmallSite.det_of_levelSections` for the statement with it
  discharged.

What is **no longer** owed is the part of `hdet` that was about the site.  The crystal condition
discharges it: `moduleRestrictionSheafMap_eq_of_hom` is the whole of the passage from a morphism
`B ⟶ T_e` to agreement over `B`, and it needs neither a sections description of
`SheafOfModules.pullback` nor the datum
`...GlobalCrystallineSituation.FirstOrderIdealBaseChange` which the note of
`LevelFaithfulSurjectivity.lean` named as the obstruction.  That note asked for the generation
statement "the sections over `B` are locally generated by the restrictions from `T_e`"; the
argument here does not go through sections over `B` at all, but cancels the comparison
isomorphism on the two sides of the naturality square, so the generation half of the base change
is not needed either.

`hstep` remains discharged, by `...SmallSite.surjective_levelSystem_module_map_of_eq`, and the
hypotheses `hlqc` and `hsurj` below are the source's own standing hypotheses at
[Stacks, Tag 07JN], carried exactly as
`...SmallSite.LevelComparison07JG.faithful_functor_of_isLevel` carries them.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u uI

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace SmallSite

/-! ### Determinacy from the restrictions to the ambient schemes -/

open CohomologyRestriction

/-- **Two morphisms of sheaves of `𝒪_{X/S}`-modules which agree on the ambient scheme of one
object of `Cris(X/S)` have the same component at that object.**

The restriction `ℱ ↦ ℱ_T` of [Stacks, Tag 07IQ] records the sections of `ℱ` over the restrictions
`(U ∩ W, W, δ|_W)` of the object to the opens of its ambient scheme, so the components of
`...CohomologyRestriction.moduleRestrictionSheafMap ψ A` are the components of `ψ` at those
restrictions, and not at `A` itself.  The two are related by
`...SmallSite.CrystallineThickening.isIso_restrictOpenHom_top`: the restriction over `⊤` is
isomorphic to the object, so the component at `A` is determined by the component at
`A.restrictOpen ⊤` through the naturality square of `ψ`.

This carries no hypothesis: neither sheaf need be quasi-coherent or a crystal. -/
theorem app_eq_of_moduleRestrictionSheafMap_eq
    {F G : SheafOfModules.{u} (structureSheaf S)} {psi chi : F ⟶ G}
    (A : CrystallineThickening S)
    (h : moduleRestrictionSheafMap psi A = moduleRestrictionSheafMap chi A) :
    PresheafOfModules.Hom.app psi.val (op A) =
      PresheafOfModules.Hom.app chi.val (op A) := by
  have := CrystallineThickening.isIso_restrictOpenHom_top A
  have key : PresheafOfModules.Hom.app psi.val (op (A.restrictOpen ⊤)) =
      PresheafOfModules.Hom.app chi.val (op (A.restrictOpen ⊤)) :=
    congrArg (fun k : moduleRestrictionSheaf F A ⟶ moduleRestrictionSheaf G A ↦
      PresheafOfModules.Hom.app k.val
        (op (⊤ : A.obj.thickening.target.scheme.Opens))) h
  have hcomp : (A.restrictOpenHom ⊤).op ≫ (inv (A.restrictOpenHom ⊤)).op = 𝟙 (op A) :=
    congrArg Quiver.Hom.op (IsIso.inv_hom_id (A.restrictOpenHom ⊤))
  have hid : ∀ w : (G.val : PresheafOfModules.{u} (crisRing S)).obj (op A),
      (G.val : PresheafOfModules.{u} (crisRing S)).map (inv (A.restrictOpenHom ⊤)).op
          ((G.val : PresheafOfModules.{u} (crisRing S)).map
            (A.restrictOpenHom ⊤).op w) = w := by
    intro w
    rw [← PresheafOfModules.map_comp_apply,
      (G.val : PresheafOfModules.{u} (crisRing S)).congr_map_apply hcomp,
      ← PresheafOfModules.presheaf_map_apply_coe,
      (G.val : PresheafOfModules.{u} (crisRing S)).presheaf.map_id]
    rfl
  have hinj : Function.Injective
      ((G.val : PresheafOfModules.{u} (crisRing S)).map (A.restrictOpenHom ⊤).op) :=
    fun y z hyz ↦ by rw [← hid y, ← hid z, hyz]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ hinj ?_)
  rw [← PresheafOfModules.naturality_apply psi.val (A.restrictOpenHom ⊤).op x,
    ← PresheafOfModules.naturality_apply chi.val (A.restrictOpenHom ⊤).op x, key]

/-- **Two morphisms of sheaves of `𝒪_{X/S}`-modules which agree on the ambient scheme of every
object of `Cris(X/S)` are equal.**

The restriction `ℱ ↦ ℱ_T` of [Stacks, Tag 07IQ] records the sections of `ℱ` over the restrictions
`(U ∩ W, W, δ|_W)` of the object to the opens of its ambient scheme, so the components of
`...CohomologyRestriction.moduleRestrictionSheafMap ψ A` are the components of `ψ` at those
restrictions, and not at `A` itself.  The two are related by
`...SmallSite.CohomologyRestriction.app_eq_of_moduleRestrictionSheafMap_eq`, applied at every
object.

This carries no hypothesis: neither sheaf need be quasi-coherent or a crystal. -/
theorem eq_of_forall_moduleRestrictionSheafMap_eq
    {F G : SheafOfModules.{u} (structureSheaf S)} {psi chi : F ⟶ G}
    (h : ∀ A : CrystallineThickening S,
      moduleRestrictionSheafMap psi A = moduleRestrictionSheafMap chi A) :
    psi = chi :=
  SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun X ↦ by
    obtain ⟨A⟩ := X
    exact app_eq_of_moduleRestrictionSheafMap_eq A (h A))

/-- **The crystal step: a morphism out of a crystal which agrees with another on the ambient
scheme of the target of a morphism of `Cris(X/S)` agrees with it on the ambient scheme of the
source.**

For `g : B ⟶ T` the comparison map `c_g : g^* ℱ_T ⟶ ℱ_B` of [Stacks, Tag 07IQ] is an isomorphism,
`ℱ` being a crystal, and it is natural in the module by
`...CohomologyRestriction.moduleComparisonSheaf_naturality`.  The two naturality squares of `ψ`
and `χ` have the same left edge once `ψ_T = χ_T`, so their right edges agree after precomposition
with the isomorphism, and cancelling it gives `ψ_B = χ_B`.

This is the whole of the passage from a morphism `B ⟶ T` to agreement over `B`.  In particular it
consumes no description of the sections of `SheafOfModules.pullback`: the argument never evaluates
`g^* ℱ_T` on an open. -/
theorem moduleRestrictionSheafMap_eq_of_hom
    {F G : SheafOfModules.{u} (structureSheaf S)} (hF : IsSheafCrystal F) {psi chi : F ⟶ G}
    {B T : CrystallineThickening S} (g : B ⟶ T)
    (h : moduleRestrictionSheafMap psi T = moduleRestrictionSheafMap chi T) :
    moduleRestrictionSheafMap psi B = moduleRestrictionSheafMap chi B := by
  have hiso := hF B T g
  have : Epi (moduleComparisonSheaf F g) := @IsIso.epi_of_iso _ _ _ _ _ hiso
  have h1 := moduleComparisonSheaf_naturality psi g
  have h2 := moduleComparisonSheaf_naturality chi g
  rw [h] at h1
  exact (cancel_epi (moduleComparisonSheaf F g)).1 (h1.symm.trans h2)

/-- **A morphism out of a crystal is determined by its restrictions to a weakly final family.**
If every object `B` of `Cris(X/S)` admits a morphism to a member `T B` of a family on whose
ambient schemes two morphisms out of a crystal agree, then the two morphisms are equal.

The family is given as data — an assignment `B ↦ T B` together with the morphisms — because the
conclusion consumes the morphisms themselves. -/
theorem eq_of_moduleRestrictionSheafMap_eq_of_hom
    {F G : SheafOfModules.{u} (structureSheaf S)} (hF : IsSheafCrystal F) {psi chi : F ⟶ G}
    (T : CrystallineThickening S → CrystallineThickening S)
    (lev : ∀ B : CrystallineThickening S, B ⟶ T B)
    (h : ∀ B : CrystallineThickening S,
      moduleRestrictionSheafMap psi (T B) = moduleRestrictionSheafMap chi (T B)) :
    psi = chi :=
  eq_of_forall_moduleRestrictionSheafMap_eq fun B ↦
    moduleRestrictionSheafMap_eq_of_hom hF (lev B) (h B)

/-! ### `hdet` for the crystals in quasi-coherent modules -/

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  {L : LevelScalars07JG S D}

/-- **The ambient scheme of a level is affine.**  A system of levels that is the degree-zero
member of `...SmallSite.wholeSpaceSystem` consists of thickenings of the whole of `X`, by
`...SmallSite.isWholeSpaceSystem_wholeSpaceSystem`, and the ambient scheme of such an object is
affine when `X` is, by `...SmallSite.isAffine_target_of_isIso_toX`.

This is the affine half of the hypothesis `hlevel` below: `hlevel` asks that a morphism out of
`ℱ_{T_e}` be determined by its sections over the whole of `T_e`, and what that needs beyond this
affineness is the quasi-coherence of `ℱ_{T_e}` in the sense of Mathlib's
`SheafOfModules.IsQuasicoherent`.  The hypothesis `hlqc` gives it in the sense of
`SheafOfModules.IsQuasicoherentOnSite`, and the two agree on the Zariski site of a scheme by
`SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite`; the two halves are put together in
`...SmallSite.levelRestriction_of_isAffine` of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelAmbientDeterminacy.lean`. -/
theorem isAffine_target_levelSystem [IsAffine S.X] [IsAffine S.S.scheme]
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0))) (e : ℕ) :
    IsAffine (L.levelSystem.obj e).obj.thickening.target.scheme := by
  rw [hL]
  exact isAffine_target_of_isIso_toX _
    (isWholeSpaceSystem_wholeSpaceSystem S hp 0 e)

/-- **`hdet` from the levels alone.**  Two morphisms of crystals in quasi-coherent
`𝒪_{X/S}`-modules which agree on `Γ(T_e, ℱ)` for every level `T_e` are equal, given

* `level` and `hlev`, that every object of `Cris(X/S)` admits a morphism to a level, and
* `hlevel`, that agreement on `Γ(T_e, ℱ)` for every `e` upgrades to agreement of the restricted
  morphisms `ℱ_{T_e} ⟶ 𝒢_{T_e}` of sheaves on the ambient scheme of `T_e`.

This is the conclusion `hdet` asserts, and the crystal condition is what bridges the levels to the
rest of the site: it enters through `moduleRestrictionSheafMap_eq_of_hom` and through nothing
else, `Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_obj` supplying it.

`hlevel` is discharged in
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelAmbientDeterminacy.lean`, where this statement
reappears as `...SmallSite.det_of_levelSections` without it; it is carried here because this
module does not import the affine theory.  This is **not** [Stacks, Tag 07JH] — the tag is an
equivalence statement — and no tag attribute is placed. -/
theorem det_of_levelRestriction
    (level : CrystallineThickening S → ℕ)
    (hlev : ∀ B : CrystallineThickening S, B ⟶ L.levelSystem.obj (level B))
    (hlevel : ∀ {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G),
      (∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
            (op (L.levelSystem.obj e))).hom s =
          (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
            (op (L.levelSystem.obj e))).hom s) →
      ∀ e : ℕ, moduleRestrictionSheafMap ((quasiCoherentCrystalι S).map psi)
            (L.levelSystem.obj e) =
          moduleRestrictionSheafMap ((quasiCoherentCrystalι S).map chi)
            (L.levelSystem.obj e))
    {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G)
    (hs : ∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
          (op (L.levelSystem.obj e))).hom s =
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
          (op (L.levelSystem.obj e))).hom s) :
    psi = chi :=
  (quasiCoherentCrystalι S).map_injective
    (eq_of_moduleRestrictionSheafMap_eq_of_hom (isSheafCrystal_obj F)
      (fun B ↦ L.levelSystem.obj (level B)) hlev fun B ↦ hlevel psi chi hs (level B))

/-- **The faithfulness half of [Stacks, Tag 07JH] for the constructed functor, with `hdet`
replaced by the two hypotheses about the levels.**

`...SmallSite.LevelComparison07JG.faithful_functor_of_isLevel` runs on `hdet` together with
hypotheses (1) and (2) of [Stacks, Tag 07JN]; here `hdet` is produced by `det_of_levelRestriction`
from the weak finality of the levels and the upgrade from their sections to the restricted
sheaves on them.  Neither new hypothesis mentions an arbitrary object of `Cris(X/S)`.

`hL` is a **delimiter and not a weakening**, exactly as in
`...SmallSite.LevelComparison07JG.faithful_functor_of_isLevel`: it is the field
`...SmallSite.Reduction07JG.levelSystem_isLevel` on the nose, it is what makes the levels the
objects `T_e = Spec(D/(p)^{N + e})` the surjectivity of the one-step restrictions is about, and it
is refuted by the degenerate system over the empty open of `X`
(`...SmallSite.not_levelSystem_isLevel_preReduction07JGBot`).

`hlevel` is discharged in
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelAmbientDeterminacy.lean`, where this statement
reappears as `...SmallSite.LevelComparison07JG.faithful_functor_of_levelSections` without it.
**This is not [Stacks, Tag 07JH]** — only faithfulness is at issue — and no tag attribute is
placed. -/
theorem LevelComparison07JG.faithful_functor_of_levelRestriction [IsAffine S.X]
    [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (C : LevelComparison07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (hsurj : ∀ F : QuasiCoherentCrystal S,
      CohomologyRestriction.IsSurjectiveComparison F.obj.val)
    (level : CrystallineThickening S → ℕ)
    (hlev : ∀ B : CrystallineThickening S, B ⟶ L.levelSystem.obj (level B))
    (hlevel : ∀ {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G),
      (∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
            (op (L.levelSystem.obj e))).hom s =
          (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
            (op (L.levelSystem.obj e))).hom s) →
      ∀ e : ℕ, moduleRestrictionSheafMap ((quasiCoherentCrystalι S).map psi)
            (L.levelSystem.obj e) =
          moduleRestrictionSheafMap ((quasiCoherentCrystalι S).map chi)
            (L.levelSystem.obj e)) :
    Functor.Faithful C.functor :=
  C.faithful_functor_of_isLevel hp hL hlqc hsurj fun psi chi hs ↦
    det_of_levelRestriction level hlev hlevel psi chi hs

/-- **The faithfulness half of [Stacks, Tag 07JH] itself, with `hdet` replaced by the two
hypotheses about the levels.**  The passage from the constructed functor to the tag's own functor
costs nothing, by `...SmallSite.faithful_functor07JG_iff`.

`hlevel` is discharged in
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelAmbientDeterminacy.lean`, where this statement
reappears as `...SmallSite.LevelReduction07JG.faithful_functor07JG_of_levelSections` without it.
The full and essentially-surjective halves of the tag are untouched, and no tag attribute is
placed. -/
theorem LevelReduction07JG.faithful_functor07JG_of_levelRestriction [IsAffine S.X]
    [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (R : LevelReduction07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (hsurj : ∀ F : QuasiCoherentCrystal S,
      CohomologyRestriction.IsSurjectiveComparison F.obj.val)
    (level : CrystallineThickening S → ℕ)
    (hlev : ∀ B : CrystallineThickening S, B ⟶ L.levelSystem.obj (level B))
    (hlevel : ∀ {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G),
      (∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
            (op (L.levelSystem.obj e))).hom s =
          (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
            (op (L.levelSystem.obj e))).hom s) →
      ∀ e : ℕ, moduleRestrictionSheafMap ((quasiCoherentCrystalι S).map psi)
            (L.levelSystem.obj e) =
          moduleRestrictionSheafMap ((quasiCoherentCrystalι S).map chi)
            (L.levelSystem.obj e)) :
    Functor.Faithful (functor07JG (R.toReduction07JG (hp := hp) hL)) :=
  (faithful_functor07JG_iff (R.toReduction07JG hL)).2
    (R.toLevelComparison07JG.faithful_functor_of_levelRestriction hp hL hlqc hsurj level hlev
      hlevel)

end SmallSite

end Crystalline.GlobalCrystallineSituation
