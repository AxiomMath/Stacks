module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiPushforwardAssociatedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation

/-!
# `𝓕 ↦ 𝓕^a` on the small Zariski site: Stacks 0GN7, 06VE (1) and 03DX (2) at `τ = Zariski`

Stacks 0GN7 says that for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` the functor
`𝓕 ↦ 𝓕^a` of Definition 03DU is fully faithful on quasi-coherent modules, both into the modules
on the big site `(Sch/S)_τ` and — for the two topologies that have a small site,
`τ ∈ {Zariski, étale}` — into the modules on the small site `S_τ`.  Clause (2) of Stacks 03DX
sharpens the small-site half to an equivalence `QCoh(𝒪_S) ≌ QCoh(S_τ, 𝒪)`.  The big-site half of
0GN7 is proved at every `τ` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful`, the small étale half
in `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity`, and
03DX (2) at `τ = étale` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit`.  **This file proves
the `τ = Zariski` half of all three**, for the functor of Remark 03FH,
`AlgebraicGeometry.SmallZariski.associatedModule`: the pullback of sheaves of modules along the
genuine morphism of ringed sites `(S_Zar, 𝒪) → (S_Zar, 𝒪_S)`, whose coefficient sheaf is the
sheaf `T/S ↦ Γ(T, 𝒪_T)` of Definition 03DU (2) rather than `𝒪_S` itself.

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiFullyFaithful` and
`StacksDraft.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiEquivalence` carry a
different reading, in which the small Zariski site is spelled `S.Opens` with coefficient sheaf
`AlgebraicGeometry.Scheme.ringCatSheaf` and `𝓕 ↦ 𝓕^a` is the pullback along the *identity*
morphism of ringed sites; there the statements are statements about the identity functor and
nothing is registered.  As the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSite` record, the
coefficient sheaf of Definition 03DU (2) is *isomorphic* to `𝒪_S` and not equal to it, so that
reading states something else; this file states the clauses over the functor the source names and
proves them with the structure-sheaf comparison carried along.

## The proof

**Full faithfulness.**  The source's chain is
`Hom(𝓕^a, 𝓖^a) = Hom(f^*𝓕, f^*𝓖) = Hom(𝓕, f_*f^*𝓖) = Hom(𝓕, 𝓖)`, whose last step is the unit of
the pullback--pushforward adjunction being an isomorphism.  At `τ = Zariski` the morphism of
ringed sites is an *equivalence* of ringed sites: its site half is the inverse of the open-image
comparison of Stacks 020X, `AlgebraicGeometry.smallZariskiSiteEquiv`, and its ring half
`AlgebraicGeometry.SmallZariski.structureMap` is an isomorphism
(`AlgebraicGeometry.SmallZariski.isIso_structureMap`).  Pushing forward along the two directions
of an equivalence of sites with such a comparison is an equivalence of module categories, and
that equivalence is already in the library as Stacks 03FG,
`AlgebraicGeometry.smallZariskiModuleEquiv`: its functor is `pushforward` along the very morphism
`AlgebraicGeometry.SmallZariski.structureMap` that `restrictModule` is `pushforward` along, so
`AlgebraicGeometry.SmallZariski.restrictModule` *is* that equivalence's functor, and
`𝓕 ↦ 𝓕^a`, being its left adjoint, is an equivalence too.  The unit of the adjunction is then an
isomorphism at every `𝒪_S`-module, quasi-coherent or not, and full faithfulness on `QCoh(𝒪_S)`
follows by composing with the inclusion of a full subcategory.

Nothing here is true by fiat: `𝓕 ↦ 𝓕^a` is the pullback along the comparison, and the
identification with the equivalence of Stacks 03FG is proved, not assumed.  This is the theorem
the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSite` anticipate when
they say that `AlgebraicGeometry.smallZariskiModuleEquiv` makes `𝓕 ↦ 𝓕^a` an equivalence, "that
is a *theorem about* it and not its definition".

**The equivalence onto `QCoh(S_Zar, 𝒪)`.**  That `𝓕 ↦ 𝓕^a` is an equivalence of the *whole*
module categories is not yet clause (2) of 03DX, which asserts an equivalence between the two
*quasi-coherent* subcategories, cut out by the two different predicates the library carries:
`SheafOfModules.IsQuasicoherent`, Mathlib's, under which `QCoh(𝒪_S)` is formed, and
`SheafOfModules.IsQuasicoherentOnSite`, the site-theoretic one of Stacks 03DL (6), under which
`QCoh(S_τ, 𝒪)` is formed.  The functor corestricts by Stacks 03DV (2),
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`, and
what essential surjectivity needs is the converse direction:
**`AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule`**, that the restriction of a
module quasi-coherent on `S_Zar` is quasi-coherent on `S`.  That is the étale file's
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` at `τ = Zariski`, and it is proved
here by a different route, the étale one going through the cartesian criterion over affine
objects and the small Zariski site having no analogue of its `commStructureMap`.  The route taken
instead:

* quasi-coherence on the site gives Mathlib's quasi-coherent data, because the slices of the
  small Zariski site are essentially small in the universe of the sections — this is
  `Stacks.SheafOfModules.nonempty_quasicoherentData_of_isQuasicoherentOnSite`, and it is
  available on `S_Zar` where on a big site it is not;
* Mathlib's `SheafOfModules.isQuasicoherent_pushforward` then carries Mathlib's quasi-coherence
  along `restrictModule`, its structure-sheaf hypothesis `η` being
  `AlgebraicGeometry.SmallZariski.pushforwardUnitIso` and its colimit hypothesis holding because
  `structureMap` is an isomorphism, so each slice pushforward is a left adjoint.

With that, the counit of the adjunction — an isomorphism, `restrictModule` being fully faithful —
exhibits every quasi-coherent `𝒪`-module on `S_Zar` as an `𝓕^a`.

## Main definitions

* `AlgebraicGeometry.SmallZariski.associatedModuleOfSheaf` and
  `AlgebraicGeometry.SmallZariski.restrictModuleOfSheaf`: the associated-module functor and its
  right adjoint, retyped so that they are composable with
  `CategoryTheory.ObjectProperty.ι`; see the implementation notes.
* `AlgebraicGeometry.SmallZariski.associatedModuleQcoh`: **the functor of Stacks 0GN7 at
  `τ = Zariski`**, `𝓕 ↦ 𝓕^a` as a functor `QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪)`.
* `AlgebraicGeometry.SmallZariski.associatedModuleQcohOnSite`: **the functor of Stacks 03DX (2)
  at `τ = Zariski`**, the same corestricted along Stacks 03DV (2) to
  `QCoh(𝒪_S) ⥤ QCoh(S_Zar, 𝒪)`, which is also how 0GN7 spells its target.
* `AlgebraicGeometry.SmallZariski.pushforwardUnitIso`: `f_*𝒪 ≅ 𝒪_S`, the structure-sheaf
  comparison `SheafOfModules.isQuasicoherent_pushforward` asks for.

## Main results

* `AlgebraicGeometry.SmallZariski.isIso_structureMap`: the comparison of structure sheaves of
  Remark 03FH is an isomorphism at `τ = Zariski`.
* `AlgebraicGeometry.SmallZariski.isEquivalence_restrictModuleOfSheaf` and
  `AlgebraicGeometry.SmallZariski.isEquivalence_associatedModuleOfSheaf`: restriction along the
  morphism of ringed sites of Remark 03FH is the equivalence of Stacks 03FG, hence so is
  `𝓕 ↦ 𝓕^a`, at the `SheafOfModules.{u} S.ringCatSheaf` retypings.  At the
  `AlgebraicGeometry.Scheme.Modules` typing these are the imported instances
  `AlgebraicGeometry.SmallZariski.isEquivalence_restrictModule` and
  `AlgebraicGeometry.SmallZariski.isEquivalence_associatedModule`.
* `AlgebraicGeometry.SmallZariski.restrictAssociatedModuleIso`: **`f_*f^*𝓕 = 𝓕`**, the step the
  source's proof turns on, at every `𝒪_S`-module and with no quasi-coherence hypothesis.
* `AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModule`: `𝓕 ↦ 𝓕^a` is fully faithful
  on all of `Mod(S_Zar, 𝒪_S)`.
* `AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh`, with its halves
  `AlgebraicGeometry.SmallZariski.full_associatedModuleQcoh` and
  `AlgebraicGeometry.SmallZariski.faithful_associatedModuleQcoh`: **Stacks 0GN7 for the small
  site at `τ = Zariski`**, which is also **clause (1) of Stacks 06VE** for that lemma's second
  functor at `τ = Zariski`.
* `AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule`: the restriction of a module
  quasi-coherent on `S_Zar` is quasi-coherent on `S`.
* `AlgebraicGeometry.SmallZariski.essSurj_associatedModuleQcohOnSite`,
  `AlgebraicGeometry.SmallZariski.isEquivalence_associatedModuleQcohOnSite` and
  `AlgebraicGeometry.SmallZariski.associatedModuleEquivalence`: **Stacks 03DX clause (2) at
  `τ = Zariski`**.

## Implementation notes

`AlgebraicGeometry.SmallZariski.associatedModule` is stated on
`AlgebraicGeometry.Scheme.Modules`, whose `CategoryTheory.Category` instance is definitionally
equal to, but not syntactically the same as, the one on `SheafOfModules.{u} S.ringCatSheaf`,
which is where `CategoryTheory.ObjectProperty.ι` and
`AlgebraicGeometry.smallZariskiModuleEquiv` land.  Instance search matches up to reducible
unfolding and does not identify the two, so every statement below that must see through one of
those is written at the retyping `AlgebraicGeometry.SmallZariski.associatedModuleOfSheaf` or
`AlgebraicGeometry.SmallZariski.restrictModuleOfSheaf`, exactly as
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf` is in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.SmallEtaleAssociatedModuleColimits`.

**Why the colimit hypothesis of `SheafOfModules.isQuasicoherent_pushforward` is discharged by
hand** rather than by Mathlib's `SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint`,
which exists and discharges exactly it: that lemma asks for `IsIso` of the structure-sheaf
comparison as an *instance*, and the comparison's codomain mentions a
`CategoryTheory.Functor.IsContinuous` instance argument that the lemma synthesizes afresh.  The
two spellings are definitionally equal by proof irrelevance but not up to the reducible
unfolding instance search uses, so `AlgebraicGeometry.SmallZariski.isIso_structureMap` is not
found there even though it is found everywhere else.  The hypothesis is therefore supplied as a
term, which is Mathlib's own proof of that lemma with `IsIso` applied rather than searched for.

## References

* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Retypings at `SheafOfModules.{u} S.ringCatSheaf` -/

/-- The associated-module functor of the small Zariski site of `S`, retyped so that its source
carries the category instance of `SheafOfModules.{u} S.ringCatSheaf`; see the implementation
notes of this module. -/
public noncomputable abbrev associatedModuleOfSheaf :
    SheafOfModules.{u} S.ringCatSheaf ⥤
      SheafOfModules.{u} (AlgebraicGeometry.SmallZariski.structureSheaf B S hS) :=
  associatedModule B S hS

/-- Restriction along the morphism of ringed sites of the small Zariski site of `S`, retyped so
that its target carries the category instance of `SheafOfModules.{u} S.ringCatSheaf`. -/
public noncomputable abbrev restrictModuleOfSheaf :
    SheafOfModules.{u} (AlgebraicGeometry.SmallZariski.structureSheaf B S hS) ⥤
      SheafOfModules.{u} S.ringCatSheaf :=
  restrictModule B S hS

/-! ### `𝓕 ↦ 𝓕^a` is an equivalence -/

/-- **Restriction along the morphism of ringed sites of Remark 03FH at `τ = Zariski` is the
equivalence of Stacks 03FG.**  Both are `SheafOfModules.pushforward` along the same morphism:
`AlgebraicGeometry.smallZariskiModuleEquiv` is built from
`SheafOfModules.pushforwardPushforwardEquivalence` over the site equivalence of Stacks 020X with
the structure-sheaf comparison `AlgebraicGeometry.smallZariskiStructureSheaf_iso` in the inverse
direction, which is `AlgebraicGeometry.SmallZariski.structureMap`. -/
public instance isEquivalence_restrictModuleOfSheaf :
    (restrictModuleOfSheaf B S hS).IsEquivalence :=
  (smallZariskiModuleEquiv.{u, u} B S hS).isEquivalence_functor

/-- `𝓕 ↦ 𝓕^a` is an equivalence, at the retyping of
`AlgebraicGeometry.SmallZariski.associatedModuleOfSheaf`. -/
public instance isEquivalence_associatedModuleOfSheaf :
    (associatedModuleOfSheaf B S hS).IsEquivalence := by
  have h : (associatedModule B S hS).IsEquivalence := inferInstance
  exact h

/-! ### Full faithfulness -/

/-- **`f_*f^*𝓕 = 𝓕` on the small Zariski site**, which is the step the source's proof of
Stacks 0GN7 turns on: restricting `𝓕^a` back along the morphism of ringed sites of Remark 03FH
returns `𝓕`, at every `𝒪_S`-module and with no quasi-coherence hypothesis.

This is the unit of `AlgebraicGeometry.SmallZariski.associatedModuleAdjunction`, which is an
isomorphism because `𝓕 ↦ 𝓕^a` is fully faithful. -/
public noncomputable def restrictAssociatedModuleIso :
    𝟭 S.Modules ≅ associatedModule B S hS ⋙ restrictModule B S hS :=
  asIso (associatedModuleAdjunction B S hS).unit

/-- **`𝓕 ↦ 𝓕^a` is fully faithful on all of `Mod(S_Zar, 𝒪_S)`**, not only on the quasi-coherent
modules: on the small Zariski site the morphism of ringed sites of Remark 03FH is an equivalence
of ringed sites, so no quasi-coherence is needed. -/
public noncomputable def fullyFaithfulAssociatedModule :
    (associatedModule B S hS).FullyFaithful :=
  .ofFullyFaithful _

/-- `𝓕 ↦ 𝓕^a` is fully faithful, at the retyping of
`AlgebraicGeometry.SmallZariski.associatedModuleOfSheaf`. -/
public noncomputable def fullyFaithfulAssociatedModuleOfSheaf :
    (associatedModuleOfSheaf B S hS).FullyFaithful :=
  .ofFullyFaithful _

/-- **The functor of Stacks 0GN7 at `τ = Zariski`**: the associated-module functor `𝓕 ↦ 𝓕^a` of
Definition 03DU (4), the pullback along the morphism of ringed sites of Remark 03FH, restricted
to the quasi-coherent modules of `S`, as a functor `QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪)`.

This is the second functor of Stacks 06VE at `τ = Zariski`, whose target `Mod(S_τ, 𝒪)` is the
target here on the nose. -/
public noncomputable abbrev associatedModuleQcoh :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ associatedModuleOfSheaf B S hS

/-- **Stacks 0GN7 for the small site at `τ = Zariski`, the fullness half.** -/
public instance full_associatedModuleQcoh : (associatedModuleQcoh B S hS).Full :=
  inferInstance

/-- **Stacks 0GN7 for the small site at `τ = Zariski`, the faithfulness half.** -/
public instance faithful_associatedModuleQcoh : (associatedModuleQcoh B S hS).Faithful :=
  inferInstance

/-- **Stacks 0GN7 for the small site at `τ = Zariski`, and clause (1) of Stacks 06VE for it.**
The functor `𝓕 ↦ 𝓕^a` of Definition 03DU (4) at `τ = Zariski` — the pullback of sheaves of
modules along the morphism of ringed sites `(S_Zar, 𝒪) → (S_Zar, 𝒪_S)` of Remark 03FH, with the
coefficient sheaf `T/S ↦ Γ(T, 𝒪_T)` of Definition 03DU (2) — from the quasi-coherent
`𝒪_S`-modules to the `𝒪`-modules on the small Zariski site, is fully faithful.

Together with `AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh` (the big
site, every `τ`) and `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'` (the
small site at `τ = étale`) this completes the covering set of 0GN7: Definition 03DU gives a small
site only for `τ ∈ {Zariski, étale}`, so those three statements are every functor the lemma
quantifies over.

0GN7 spells the target `QCoh(S_Zar, 𝒪)` where this is `Mod(S_Zar, 𝒪)`, and that is the same
statement for the same reason as at `τ = étale` and on the big site: full faithfulness of a
functor into a category is full faithfulness into any full subcategory containing its image, and
the image lands in `QCoh(S_Zar, 𝒪)` by Stacks 03DV (2),
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`;
the corestriction itself is
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcohOnSite` below.  06VE's second
functor has target `Mod(S_τ, 𝒪)`, which is the target here with nothing to read through. -/
@[stacks 0GN7 "small site at τ = Zariski", stacks 06VE "part (1), small site at τ = Zariski"]
public noncomputable def fullyFaithfulAssociatedModuleQcoh :
    (associatedModuleQcoh B S hS).FullyFaithful :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).fullyFaithfulι.comp
    (fullyFaithfulAssociatedModuleOfSheaf B S hS)

/-! ### The comparison of structure sheaves is an isomorphism -/

/-- **The comparison of structure sheaves of Remark 03FH is an isomorphism at `τ = Zariski`.**
`AlgebraicGeometry.SmallZariski.structureMap` is
`AlgebraicGeometry.smallZariskiStructureSheaf_iso` read as a morphism into the pushforward, and a
sheaf morphism is an isomorphism as soon as the underlying morphism of presheaves is, the
inclusion of the sheaves being fully faithful. -/
public instance isIso_structureMap : IsIso (structureMap B S hS) := by
  have : IsIso ((ObjectProperty.ι (Presheaf.IsSheaf (Opens.grothendieckTopology ↥S))).map
      (structureMap B S hS)) := by
    change IsIso (smallZariskiStructureSheaf_iso B S hS).inv.hom
    exact inferInstanceAs (IsIso ((ObjectProperty.ι _).map
      (smallZariskiStructureSheaf_iso B S hS).inv))
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map (structureMap B S hS)

/-- **`f_*𝒪 ≅ 𝒪_S`**: restriction along the morphism of ringed sites of Remark 03FH takes the
unit module of `(S_Zar, 𝒪)` to the unit module of `(S_Zar, 𝒪_S)`.

This is the structure-sheaf comparison `SheafOfModules.isQuasicoherent_pushforward` asks for.  It
is assembled from two facts the library already has: `𝒪_S^a ≅ 𝒪`, which is
`AlgebraicGeometry.SmallZariski.isIso_pullbackObjUnitToUnit` — the inclusion of the small
Zariski site being final — and `f_*f^* ≅ 𝟭`, which is
`AlgebraicGeometry.SmallZariski.restrictAssociatedModuleIso`. -/
public noncomputable def pushforwardUnitIso :
    (SheafOfModules.pushforward.{u} (structureMap B S hS)).obj
      (SheafOfModules.unit (structureSheaf B S hS)) ≅ SheafOfModules.unit S.ringCatSheaf :=
  (restrictModuleOfSheaf B S hS).mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B S hS))).symm ≪≫
    ((restrictAssociatedModuleIso B S hS).app (SheafOfModules.unit S.ringCatSheaf)).symm

/-! ### Stacks 03DX (2) at `τ = Zariski` -/

/-- **The restriction of a quasi-coherent `𝒪`-module on `S_Zar` is a quasi-coherent
`𝒪_S`-module.**  This is the converse of Stacks 03DV (2), and the one input of 03DX (2) at
`τ = Zariski` that does not come from the equivalence; it is
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` read at `τ = Zariski`.

The quasi-coherence of Stacks 03DL (6) gives Mathlib's quasi-coherent data here, the slices of
the small Zariski site being essentially small in the universe of the sections, and Mathlib's
`SheafOfModules.isQuasicoherent_pushforward` then carries Mathlib's quasi-coherence along
`restrictModule`.  Its colimit hypothesis holds because
`AlgebraicGeometry.SmallZariski.isIso_structureMap` makes each slice comparison an isomorphism,
hence each slice pushforward a left adjoint; see the implementation notes for why it is supplied
as a term rather than by `SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint`. -/
public theorem isQuasicoherent_restrictModule
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModuleOfSheaf B S hS).obj G) := by
  have : G.IsQuasicoherent :=
    (Stacks.SheafOfModules.nonempty_quasicoherentData_of_isQuasicoherentOnSite
      G hG).some.isQuasicoherent
  refine SheafOfModules.isQuasicoherent_pushforward
    (opensToSmallZariski B S hS) (structureMap B S hS) (pushforwardUnitIso B S hS) ?_
  intro X Y f
  let G' := Over.post (X := X) (opensToSmallZariski B S hS) ⋙ Over.map f
  have : G'.IsContinuous ((Opens.grothendieckTopology ↥S).over X) ((topology B S hS).over Y) :=
    Functor.isContinuous_comp _ _ _ ((topology B S hS).over _) _
  have : G'.IsCocontinuous ((Opens.grothendieckTopology ↥S).over X)
      ((topology B S hS).over Y) :=
    isCocontinuous_comp _ _ _ ((topology B S hS).over _)
  let a : (S.ringCatSheaf).over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} ((Opens.grothendieckTopology ↥S).over X)
        ((topology B S hS).over Y)).obj ((structureSheaf B S hS).over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u}
      ((Opens.grothendieckTopology ↥S).over X) (Opens.grothendieckTopology ↥S)).map
      (structureMap B S hS)
  have : IsIso a := Functor.map_isIso _ (structureMap B S hS)
  have : (SheafOfModules.pushforward.{u} a).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso a
  infer_instance

/-- **The functor of Stacks 03DX (2) at `τ = Zariski`**: `𝓕 ↦ 𝓕^a` as a functor
`QCoh(𝒪_S) ⥤ QCoh(S_Zar, 𝒪)`.

This is `AlgebraicGeometry.SmallZariski.associatedModuleQcoh`, whose target is *all* modules on
`S_Zar`, corestricted along Stacks 03DV (2),
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`.  It
is also the functor of Stacks 0GN7 read in the target that lemma spells. -/
public noncomputable abbrev associatedModuleQcohOnSite :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (AlgebraicGeometry.SmallZariski.structureSheaf B S hS)).FullSubcategory :=
  ObjectProperty.lift _ (associatedModuleQcoh B S hS) fun M =>
    isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS M.obj M.property

/-- **Stacks 0GN7 for the small site at `τ = Zariski`, read in the target the source spells**:
the functor `QCoh(𝒪_S) ⥤ QCoh(S_Zar, 𝒪)` is fully faithful.  Corestricting a functor to a full
subcategory containing its image changes neither fullness nor faithfulness, so the content is
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh`, where the attribute sits —
as it does at `τ = étale`, on
`AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'`. -/
public noncomputable def fullyFaithfulAssociatedModuleQcohOnSite :
    (AlgebraicGeometry.SmallZariski.associatedModuleQcohOnSite B S hS).FullyFaithful :=
  .ofFullyFaithful _

/-- **Essential surjectivity of the functor of Stacks 03DX (2) at `τ = Zariski`**: every
quasi-coherent `𝒪`-module on the small Zariski site of `S` is `𝓕^a` for a quasi-coherent
`𝒪_S`-module `𝓕`, namely for its own restriction along the morphism of ringed sites of
Remark 03FH.

That the restriction is quasi-coherent is
`AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule`; the isomorphism is the counit of
`AlgebraicGeometry.SmallZariski.associatedModuleAdjunction`, which is an isomorphism because
`AlgebraicGeometry.SmallZariski.restrictModule` is fully faithful. -/
public theorem essSurj_associatedModuleQcohOnSite :
    (associatedModuleQcohOnSite B S hS).EssSurj where
  mem_essImage G :=
    ⟨⟨(restrictModuleOfSheaf B S hS).obj G.obj,
        isQuasicoherent_restrictModule B S hS G.obj G.property⟩,
      ⟨ObjectProperty.isoMk _
        (asIso ((associatedModuleAdjunction B S hS).counit.app G.obj))⟩⟩

/-- **Stacks 03DX clause (2) at `τ = Zariski`**: `𝓕 ↦ 𝓕^a` is an equivalence
`QCoh(𝒪_S) ⥤ QCoh(S_Zar, 𝒪)`.

`CategoryTheory.Functor.IsEquivalence` is fullness, faithfulness and essential surjectivity
together, which is the decomposition the source's proof uses: Stacks 03DV (2) for the functor,
Stacks 0GN7 for full faithfulness, and
`AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule` for essential surjectivity.
Clause (2) also ranges over `τ = étale`, which is
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`; clause (1), over the
big sites, is untouched here. -/
@[stacks 03DX "clause (2) at τ = Zariski: 𝓕 ↦ 𝓕^a is an equivalence \
QCoh(𝒪_S) ⥤ QCoh(S_Zar, 𝒪)"]
public theorem isEquivalence_associatedModuleQcohOnSite :
    (AlgebraicGeometry.SmallZariski.associatedModuleQcohOnSite B S hS).IsEquivalence :=
  have hff := fullyFaithfulAssociatedModuleQcohOnSite B S hS
  have := hff.full
  have := hff.faithful
  have := essSurj_associatedModuleQcohOnSite B S hS
  {}

/-- **The equivalence of categories of Stacks 03DX (2) at `τ = Zariski`**,
`QCoh(𝒪_S) ≌ QCoh(S_Zar, 𝒪)`, with `𝓕 ↦ 𝓕^a` as its functor.

The source states the clause as an equivalence rather than as the three properties of the
functor, and this is that statement; its `CategoryTheory.Equivalence.functor` is
`AlgebraicGeometry.SmallZariski.associatedModuleQcohOnSite` by definition. -/
@[stacks 03DX "clause (2) at τ = Zariski: the equivalence of categories \
QCoh(𝒪_S) ≌ QCoh(S_Zar, 𝒪)"]
public noncomputable def associatedModuleEquivalence :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  have := isEquivalence_associatedModuleQcohOnSite B S hS
  (associatedModuleQcohOnSite B S hS).asEquivalence

end AlgebraicGeometry.SmallZariski

end
