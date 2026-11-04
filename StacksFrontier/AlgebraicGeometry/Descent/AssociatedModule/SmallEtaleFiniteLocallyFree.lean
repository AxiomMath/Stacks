module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCoveringFpqc
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedObjectRestriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness crosses from the small étale site to the Zariski site

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites
of Stacks 08H7, whose pullback of modules is the associated-module functor `𝓕 ↦ 𝓕^a` of
Stacks 03DU (4).  This file proves the reflection half of Stacks 05VG for the clause
03DL (2): a quasi-coherent `𝒪_S`-module whose associated module on the small étale site is
finite locally free is itself finite locally free.

The argument is the source's.  Finite local freeness on a site may be tested on a single
family covering the final object, Stacks 03DN, so `𝓕^a` finite locally free produces a family
`{U i}` of étale objects covering the final object of `S_étale` with every `(𝓕^a)|_{U i}`
finite free.  Read on the small étale site of the scheme `Y i` of `U i`, that restriction is
the associated module of the Zariski pullback `f_i^*𝓕` — Stacks 03DV, available here as
`AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictObjIso` — so each `(f_i^*𝓕)^a` is
finite free.  Finite freeness *descends* along `𝓕 ↦ 𝓕^a`, because that functor carries a free
module to a free module and is fully faithful on the quasi-coherent modules by Stacks 03DX (2)
at `τ = étale`; hence every `f_i^*𝓕` is finite free, so finite locally free.  Finally the
family `{Y i ⟶ S}` of structure morphisms is an fpqc covering of schemes, étale coverings
being fpqc coverings, and Stacks 05B2 descends finite local freeness along it.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteFree_of_isFiniteFree_associatedModule` and
  `AlgebraicGeometry.SmallEtale.isFiniteFree_associatedModule_iff`: finite freeness of a
  quasi-coherent module is detected by its associated module on the small étale site.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_associatedModule`:
  **Stacks 05VG for the clause 03DL (2) at `τ = étale`, the reflection half.**
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOfRank_associatedModule`: **Stacks 05VG for
  the rank clause of Stacks 0409 at `τ = étale`, the forward half** — the rank is carried across,
  not forgotten.
* `Stacks.SheafOfModules.exists_isColimitCofan_pullback`: the pullback of modules along a morphism
  of sites carries a presentation as a coproduct of copies of the structure sheaf to such a
  presentation **with the same index type**.  `Stacks.SheafOfModules.isFiniteFree_pullback` is
  that statement with the index forgotten.

## Implementation notes

Full faithfulness of `𝓕 ↦ 𝓕^a` on the quasi-coherent modules is taken from
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`, the unconditional
form of Stacks 03DX (2) at `τ = étale`.  Older implementation notes in this directory describe
that clause as unavailable; they predate
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit`.

`AlgebraicGeometry.SmallEtale.associatedModule` is `SheafOfModules.pullback` along
`AlgebraicGeometry.SmallEtale.structureMap`, so `SheafOfModules.pullbackObjFreeIso` applies to
it directly; its finality hypothesis is `AlgebraicGeometry.SmallEtale.final_opensToSmallEtale`.

The restriction of a module to the slice at an object of the small étale site is compared with
its reading on the small étale site of that object's scheme by
`Stacks.SheafOfModules.isFiniteFree_reindex_iff` at
`AlgebraicGeometry.SmallEtale.localizationEquivalence`; the two structure sheaves agree on the
nose by `AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence`, which is what makes
the transport available at all.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u₁ v₂ u₂

namespace Stacks.SheafOfModules

/-- Finite freeness depends only on the isomorphism class of a sheaf of modules. -/
theorem isFiniteFree_of_iso {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {F G : _root_.SheafOfModules.{u} R} (e : F ≅ G)
    (hF : _root_.SheafOfModules.IsFiniteFree R F) :
    _root_.SheafOfModules.IsFiniteFree R G := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R F).1 hF
  exact (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R G).2
    ⟨n, fun i => ι i ≫ e.hom, ⟨hc.ofIsoColimit (Cocone.ext e (fun _ => rfl))⟩⟩

/-- A finite free sheaf of modules restricts to a finite free sheaf on every slice:
restriction is additive, so it preserves the finite coproduct witnessing finite freeness. -/
theorem isFiniteFree_over {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : _root_.SheafOfModules.{u} R) (U : C)
    (h : _root_.SheafOfModules.IsFiniteFree R M) :
    _root_.SheafOfModules.IsFiniteFree (R.over U) (M.over U) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R M).1 h
  refine (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2
    ⟨n, fun i => (_root_.SheafOfModules.overFunctor R U).map (ι i), ⟨?_⟩⟩
  let T := _root_.SheafOfModules.overFunctor R U
  let : T.Additive := ⟨rfl⟩
  exact (Cofan.isColimitMapCoconeEquiv T _ _).toFun (isColimitOfPreserves T hc)

/-- A free sheaf of modules on a finite index type is finite free. -/
theorem isFiniteFree_freeULift {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J RingCat.{u}) (n : ℕ) :
    _root_.SheafOfModules.IsFiniteFree R
      (_root_.SheafOfModules.free.{u} (R := R) (ULift.{u} (Fin n))) :=
  (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2
    ⟨n, _, ⟨Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _
      (_root_.SheafOfModules.isColimitFreeCofan _)⟩⟩

/-- A presentation of a sheaf of modules as a coproduct of copies of the structure sheaf
transports along an isomorphism, with the *same* index type. -/
theorem exists_isColimitCofan_of_iso {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N) {I : Type*}
    (h : ∃ ι : I → (_root_.SheafOfModules.unit R ⟶ M),
      Nonempty (IsColimit (Cofan.mk M ι))) :
    ∃ ι : I → (_root_.SheafOfModules.unit R ⟶ N), Nonempty (IsColimit (Cofan.mk N ι)) := by
  obtain ⟨ι, ⟨hc⟩⟩ := h
  exact ⟨fun i => ι i ≫ e.hom,
    ⟨IsColimit.ofIsoColimit hc (Cocone.ext e (fun _ => rfl))⟩⟩

/-- A sheaf of modules isomorphic to the free module on `I` is presented as a coproduct of copies
of the structure sheaf indexed by `I`. -/
theorem exists_isColimitCofan_of_iso_free {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {R : Sheaf J RingCat.{u}}
    {N : _root_.SheafOfModules.{u} R} {I : Type u}
    (e : _root_.SheafOfModules.free.{u} (R := R) I ≅ N) :
    ∃ ι : I → (_root_.SheafOfModules.unit R ⟶ N), Nonempty (IsColimit (Cofan.mk N ι)) :=
  exists_isColimitCofan_of_iso e
    ⟨_root_.SheafOfModules.ιFree, ⟨_root_.SheafOfModules.isColimitFreeCofan I⟩⟩

/-- A sheaf of modules presented as a coproduct of copies of the structure sheaf indexed by `I` is
isomorphic to the free module on `I`: both are colimits of the same diagram. -/
theorem nonempty_iso_free_of_exists_isColimitCofan {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {R : Sheaf J RingCat.{u}}
    {M : _root_.SheafOfModules.{u} R} {I : Type u}
    (h : ∃ ι : I → (_root_.SheafOfModules.unit R ⟶ M),
      Nonempty (IsColimit (Cofan.mk M ι))) :
    Nonempty (_root_.SheafOfModules.free.{u} (R := R) I ≅ M) := by
  obtain ⟨ι, ⟨hc⟩⟩ := h
  exact ⟨(_root_.SheafOfModules.isColimitFreeCofan I).coconePointUniqueUpToIso hc⟩

/-- A presentation of a sheaf of modules as a coproduct of copies of the structure sheaf indexed
by `Fin n` is the same as one indexed by `ULift (Fin n)`. -/
private theorem exists_isColimitCofan_fin_iff_ulift {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : _root_.SheafOfModules.{u} R}
    {n : ℕ} :
    (∃ ι : Fin n → (_root_.SheafOfModules.unit R ⟶ M), Nonempty (IsColimit (Cofan.mk M ι))) ↔
      ∃ ι : ULift.{u} (Fin n) → (_root_.SheafOfModules.unit R ⟶ M),
        Nonempty (IsColimit (Cofan.mk M ι)) := by
  constructor
  · rintro ⟨ι, ⟨hc⟩⟩
    exact ⟨fun i => ι i.down, ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk M ι)) hc⟩⟩
  · rintro ⟨ι, ⟨hc⟩⟩
    exact ⟨fun i => ι ⟨i⟩, ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _) hc⟩⟩

/-- **The pullback of modules along a morphism of sites carries a presentation as a coproduct of
copies of the structure sheaf to such a presentation, with the same index type.**  The pullback
preserves colimits, being a left adjoint, and carries the unit object to the unit object when the
underlying functor is final, so it carries the free module on `I` to the free module on `I`
(`SheafOfModules.pullbackObjFreeIso`). -/
@[ega "0 5.4.5" "more general"]
theorem exists_isColimitCofan_pullback {C : Type u₁} [Category.{v} C] {D : Type u₂}
    [Category.{v₂} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [F.IsContinuous J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    [(_root_.SheafOfModules.pushforward φ).IsRightAdjoint]
    [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.Final]
    (M : _root_.SheafOfModules.{u} S) {I : Type u}
    (h : ∃ ι : I → (_root_.SheafOfModules.unit S ⟶ M),
      Nonempty (IsColimit (Cofan.mk M ι))) :
    ∃ ι : I → (_root_.SheafOfModules.unit R ⟶
        (_root_.SheafOfModules.pullback φ).obj M),
      Nonempty (IsColimit (Cofan.mk ((_root_.SheafOfModules.pullback φ).obj M) ι)) := by
  obtain ⟨e⟩ := nonempty_iso_free_of_exists_isColimitCofan h
  exact exists_isColimitCofan_of_iso_free
    ((_root_.SheafOfModules.pullbackObjFreeIso φ I).symm ≪≫
      (_root_.SheafOfModules.pullback φ).mapIso e)

/-- **The pullback of modules along a morphism of sites carries a finite free module to a finite
free module.**  This is `Stacks.SheafOfModules.exists_isColimitCofan_pullback` with the index type
of the presentation forgotten, the finite index being raised to the universe of the sections. -/
theorem isFiniteFree_pullback {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [F.IsContinuous J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    [(_root_.SheafOfModules.pushforward φ).IsRightAdjoint]
    [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.Final]
    (M : _root_.SheafOfModules.{u} S) (h : _root_.SheafOfModules.IsFiniteFree S M) :
    _root_.SheafOfModules.IsFiniteFree R ((_root_.SheafOfModules.pullback φ).obj M) := by
  obtain ⟨n, hn⟩ := (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1 h
  exact (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2
    ⟨n, exists_isColimitCofan_fin_iff_ulift.2
      (exists_isColimitCofan_pullback φ M (exists_isColimitCofan_fin_iff_ulift.1 hn))⟩

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

open _root_.AlgebraicGeometry

/-- The top open of a scheme covers the final object of its small Zariski site. -/
theorem coversTop_top (S : Scheme.{u}) : (Opens.grothendieckTopology ↥S).CoversTop
    (fun _ : PUnit.{u + 1} => (⊤ : S.Opens)) := by
  intro X
  convert (Opens.grothendieckTopology ↥S).top_mem X using 1
  ext W f
  simpa using ⟨PUnit.unit, ⟨homOfLE le_top⟩⟩

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent, at
the `AlgebraicGeometry.Scheme.Modules.pullback` spelling. -/
theorem schemePullback_isQuasicoherent {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules)
    [hqc : M.IsQuasicoherent] : ((Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _ f.toLRSHom.toShHom M hqc

/-- A finite free module on a scheme is finite locally free: the top open alone trivializes it.
-/
theorem isFiniteLocallyFree_of_isFiniteFree {S : Scheme.{u}} (M : S.Modules)
    (h : _root_.SheafOfModules.IsFiniteFree S.ringCatSheaf M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  refine AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite M ?_
  refine (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      S.zariskiRingedSite M).2
    ⟨PUnit.{u + 1}, fun _ => (⊤ : S.Opens), coversTop_top S, fun _ => ?_⟩
  exact (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1
    (isFiniteFree_over M (⊤ : S.Opens) h)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The associated module of a free module is free.**  `𝓕 ↦ 𝓕^a` is a pullback of sheaves of
modules, and the small Zariski site of `S` is a final subcategory of its small étale site. -/
noncomputable def associatedModuleFreeIso (I : Type u) :
    (associatedModule B S hS).obj (_root_.SheafOfModules.free.{u} (R := S.ringCatSheaf) I) ≅
      _root_.SheafOfModules.free.{u} I :=
  _root_.SheafOfModules.pullbackObjFreeIso.{u} (structureMap B S hS) I

/-- **Finite freeness descends along `𝓕 ↦ 𝓕^a` on the small étale site.**  If the associated
module of a quasi-coherent `𝒪_S`-module is finite free, the module is finite free.

The associated module carries a free module to a free module, so a finite free `𝓕^a` is
isomorphic to the associated module of a free `𝒪_S`-module; both are quasi-coherent, and
`𝓕 ↦ 𝓕^a` is fully faithful on the quasi-coherent modules by Stacks 03DX (2) at `τ = étale`,
so the isomorphism descends. -/
theorem isFiniteFree_of_isFiniteFree_associatedModule (M : S.Modules) [M.IsQuasicoherent]
    (h : _root_.SheafOfModules.IsFiniteFree (structureSheaf B S hS)
      ((associatedModule B S hS).obj M)) :
    _root_.SheafOfModules.IsFiniteFree S.ringCatSheaf M := by
  obtain ⟨n, hn⟩ := (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1 h
  let I := ULift.{u} (Fin n)
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_free_of_exists_isColimitCofan
    (Stacks.SheafOfModules.exists_isColimitCofan_fin_iff_ulift.1 hn)
  have := isEquivalence_associatedModuleQcohOnSite' B S hS
  let Mq : (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let Fq : (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    ⟨_root_.SheafOfModules.free.{u} I,
      Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I⟩
  have eobj : (associatedModuleQcohOnSite B S hS).obj Fq ≅
      (associatedModuleQcohOnSite B S hS).obj Mq :=
    (ObjectProperty.ι _).preimageIso (associatedModuleFreeIso B S hS I ≪≫ e)
  exact Stacks.SheafOfModules.isFiniteFree_of_iso
    ((ObjectProperty.ι _).mapIso ((associatedModuleQcohOnSite B S hS).preimageIso eobj))
    (Stacks.SheafOfModules.isFiniteFree_freeULift S.ringCatSheaf n)

/-- **Finite freeness of a quasi-coherent module is detected by its associated module on the
small étale site.** -/
theorem isFiniteFree_associatedModule_iff (M : S.Modules) [M.IsQuasicoherent] :
    _root_.SheafOfModules.IsFiniteFree (structureSheaf B S hS)
        ((associatedModule B S hS).obj M) ↔
      _root_.SheafOfModules.IsFiniteFree S.ringCatSheaf M :=
  ⟨isFiniteFree_of_isFiniteFree_associatedModule B S hS M,
    Stacks.SheafOfModules.isFiniteFree_pullback (structureMap B S hS) M⟩

/-- The Zariski pullback of `𝓕` to the scheme of an object `U` of the small étale site is
finite locally free as soon as `𝓕^a` is finite free on the slice at `U`. -/
theorem isFiniteLocallyFree_pullback_objHom (𝓕 : S.Modules) [𝓕.IsQuasicoherent]
    (U : SmallEtale B S hS)
    (h : _root_.SheafOfModules.IsFiniteFree ((structureSheaf B S hS).over U)
      (((associatedModule B S hS).obj 𝓕).over U)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕) := by
  have hYc : B.Contains (objScheme B S hS U) := contains_objScheme B S hS U
  have hcross : _root_.SheafOfModules.IsFiniteFree (structureSheaf B (objScheme B S hS U) hYc)
      ((objRestrict B S hS U).obj ((associatedModule B S hS).obj 𝓕)) :=
    (Stacks.SheafOfModules.isFiniteFree_reindex_iff
      (localizationEquivalence B S hS U) ((structureSheaf B S hS).over U) _).2 h
  have := Stacks.SheafOfModules.schemePullback_isQuasicoherent (objHom B S hS U) 𝓕
  exact Stacks.SheafOfModules.isFiniteLocallyFree_of_isFiniteFree _
    (isFiniteFree_of_isFiniteFree_associatedModule B (objScheme B S hS U) hYc _
      (Stacks.SheafOfModules.isFiniteFree_of_iso
        (associatedModuleObjRestrictObjIso B S hS U 𝓕).symm hcross))

/-- **Stacks 05VG for the clause 03DL (2) at `τ = étale`, the reflection half.**  A
quasi-coherent `𝒪_S`-module whose associated module on the small étale site of `S` is finite
locally free is finite locally free. -/
@[stacks 05VG "finite locally free, τ = étale, small sites: the reflection half"]
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_associatedModule
    (𝓕 : S.Modules) [𝓕.IsQuasicoherent]
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite ((associatedModule B S hS).obj 𝓕)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝓕 := by
  obtain ⟨I, U, hU, hfree⟩ :=
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      (smallEtaleRingedSite B S hS) ((associatedModule B S hS).obj 𝓕)).1 h
  refine isFiniteLocallyFree_of_pullback_fpqcCover 𝓕
    { toPreZeroHypercover := coveringHypercover B S hS U
      mem₀ := presieve₀_mem_fpqcPrecoverage_coveringHypercover B S hS U hU } fun i => ?_
  exact isFiniteLocallyFree_pullback_objHom B S hS 𝓕 (U i)
    ((_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2 (hfree i))

/-- **Stacks 05VG for the clause 03DL (2) at `τ = étale`, the forward half.**  The associated
module on the small étale site of a finite locally free `𝒪_S`-module is finite locally free.

Stacks 03DN tests the conclusion on a single family covering the final object.  A finite locally
free `𝓕` is finite free over the members of some Zariski covering of `S`; the images of those
opens in `S_étale` cover its final object by
`AlgebraicGeometry.SmallEtale.coversTop_opensToSmallEtale_ulift`, and over each of them `𝓕^a` is
the pullback of `𝓕|_V` along the localized comparison of structure sheaves by Stacks 03DV
(`AlgebraicGeometry.SmallEtale.associatedModuleOverObjIso`), which is finite free because a
pullback of modules carries a finite free module to a finite free one. -/
@[stacks 05VG "finite locally free, τ = étale, small sites: the forward half"]
theorem isFiniteLocallyFreeOnSite_associatedModule (𝓕 : S.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝓕) :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((associatedModule B S hS).obj 𝓕) := by
  obtain ⟨K, V, hV, hfree⟩ :=
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
        S.zariskiRingedSite 𝓕).1
      (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree 𝓕 h)
  refine (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
    (smallEtaleRingedSite B S hS) _).2
    ⟨ULift.{u + 1} K, fun i => (opensToSmallEtale B S hS).obj (V i.down),
      coversTop_opensToSmallEtale_ulift B S hS V hV, fun i => ?_⟩
  refine (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1 ?_
  refine Stacks.SheafOfModules.isFiniteFree_of_iso
    (associatedModuleOverObjIso B S hS (V i.down) 𝓕) ?_
  exact Stacks.SheafOfModules.isFiniteFree_pullback (sliceStructureMap B S hS (V i.down)) _
    ((_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2 (hfree i.down))

/-- **Stacks 05VG for the rank clause of Stacks 0409 at `τ = étale`, the forward half.**  If an
`𝒪_S`-module has rank `r` on the small Zariski site of `S`, its associated module has rank `r` on
the small étale site.

This is the rank-indexed form of
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule`, and the argument is the
same one: the rank clause is local on a family covering the final object
(`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit`), the images
in `S_étale` of a Zariski covering of `S` cover its final object
(`AlgebraicGeometry.SmallEtale.coversTop_opensToSmallEtale_ulift`), and over each of them `𝓕^a` is
the pullback of `𝓕|_V` along the localized comparison of structure sheaves by Stacks 03DV
(`AlgebraicGeometry.SmallEtale.associatedModuleOverObjIso`).  What differs is only that the
presentation is transported with its index type *kept* — the pullback carries a coproduct of `r`
copies of the structure sheaf to a coproduct of `r` copies of it, by
`Stacks.SheafOfModules.exists_isColimitCofan_pullback` — rather than with the index replaced by a
natural number quantified away.  The index of the free model lives in the universe of the
sections, so `Fin r` is raised and lowered across the transport. -/
theorem isFiniteLocallyFreeOfRank_associatedModule (𝓕 : S.Modules) (r : ℕ)
    (h : RingedSite.IsFiniteLocallyFreeOfRank S.zariskiRingedSite 𝓕 r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS)
      ((associatedModule B S hS).obj 𝓕) r := by
  obtain ⟨K, V, hV, hfree⟩ :=
    (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit
      S.zariskiRingedSite 𝓕 r).1 h
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit
    (smallEtaleRingedSite B S hS) _ r).2
    ⟨ULift.{u + 1} K, fun i => (opensToSmallEtale B S hS).obj (V i.down),
      coversTop_opensToSmallEtale_ulift B S hS V hV, fun i => ?_⟩
  exact Stacks.SheafOfModules.exists_isColimitCofan_fin_iff_ulift.2
    (Stacks.SheafOfModules.exists_isColimitCofan_of_iso
      (associatedModuleOverObjIso B S hS (V i.down) 𝓕)
      (Stacks.SheafOfModules.exists_isColimitCofan_pullback
        (sliceStructureMap B S hS (V i.down)) _
        (Stacks.SheafOfModules.exists_isColimitCofan_fin_iff_ulift.1 (hfree i.down))))

/-- **Stacks 05VG for the clause 03DL (2) at `τ = étale`.**  A quasi-coherent `𝒪_S`-module is
finite locally free if and only if its associated module on the small étale site of `S` is. -/
@[stacks 05VG "finite locally free, τ = étale, small sites"]
theorem isFiniteLocallyFreeOnSite_associatedModule_iff (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((associatedModule B S hS).obj 𝓕) ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝓕 :=
  ⟨isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_associatedModule B S hS 𝓕,
    isFiniteLocallyFreeOnSite_associatedModule B S hS 𝓕⟩

end AlgebraicGeometry.SmallEtale

end
