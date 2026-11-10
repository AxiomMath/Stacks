module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSiteHomGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# Four local types of modules under `𝓕 ↦ 𝓕^a` on the small Zariski site

Descent, Lemma 05VG compares properties of modules across the comparison functors
`𝓕 ↦ 𝓕^a` of Descent, Proposition 03DX.  The seven *global* clauses of Modules on Sites,
Definition 03DE at the small site for `τ = Zariski` are settled in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiTypesComparison`, where a
global clause costs nothing because it is a condition on the module alone and the comparison is
an equivalence of the whole module categories.

**This file settles three of the five *local* clauses of Definition 03DL at the small site for
`τ = Zariski`** — local generation by `r` sections (03DL (4)), being of finite type (03DL (5))
and finite presentation (03DL (7)) — **and the flatness clause of Definition 03ER (3) there.**
A local clause quantifies over the objects of the site and over coverings of them, so
transporting it means carrying covering data across the underlying change of sites, and
invariance under isomorphism of modules says nothing about that.

## The route

Stacks 03DM says that each of the three conditions of 03DL depends only on the associated ringed
topos: an equivalence of ringed topoi both preserves and reflects it.  For an arbitrary morphism
of ringed topoi whose direct image on sheaves of sets is an equivalence and whose structure map
is invertible, this is
`AlgebraicGeometry.RingedToposHom.isLocallyGeneratedByOnSite_iff_pullbackModules`,
`AlgebraicGeometry.RingedToposHom.isFiniteType_iff_pullbackModules` and
`AlgebraicGeometry.RingedToposHom.isFinitePresentation_iff_pullbackModules` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence`.  **The small Zariski
site is the one case of 05VG whose comparison is such a morphism**, and this file instantiates
them there.

What that needs is three steps.

* The morphism of ringed topoi.  `AlgebraicGeometry.SmallZariski.toOpensRingedSiteHom` is
  Remark 03FH's `id_{small, Zar, Zar} : (S_Zar, 𝒪) ⟶ (S_Zar, 𝒪_S)` as a
  `AlgebraicGeometry.RingedSite.HomGeneral`, and
  `AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom` turns it into the two-field
  morphism of ringed topoi of Stacks 01D3 (2).  That is
  `AlgebraicGeometry.SmallZariski.toOpensRingedToposHom`.
* Its two instance hypotheses.  Its direct image on sheaves of sets is the direct image of the
  site functor on the nose, by
  `AlgebraicGeometry.RingedSite.HomGeneral.toposHom_pushforward`, and that is an equivalence
  because the inclusion of the opens of the space of `S` into the small Zariski site is a dense
  subsite inclusion; and its structure map is
  `AlgebraicGeometry.SmallZariski.commStructureMap` followed by
  `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, each of them invertible.
* The identification of its pullback of modules with `𝓕 ↦ 𝓕^a`.  Here two constructions of
  Stacks 03D6 (2) meet.  The engine lemmas are stated for
  `f.toModulesHom.pullbackModules`, the pullback along the two-field morphism `f`;
  `AlgebraicGeometry.SmallZariski.pullbackToposGeneral_toOpensRingedSiteHom` identifies, by
  `rfl`, the *site-presented* pullback with `AlgebraicGeometry.SmallZariski.associatedModule`.
  `AlgebraicGeometry.SmallZariski.associatedModuleIsoPullbackModules` joins them, through
  `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` and one further
  comparison, and the conclusion is transported along it by the three
  `Stacks.SheafOfModules.Intrinsic.*_of_iso`.

No quasi-coherence hypothesis appears, for the same reason as in the global file: at
`τ = Zariski` the comparison is an equivalence of the whole module categories and not only of
the quasi-coherent ones.

## The flat clause

`AlgebraicGeometry.RingedToposHom.isFlat_iff_pullbackModules` is the same statement for Modules on
Sites, Definition 03ER (3): a module on the target of an equivalence of ringed topoi is flat if and
only if its pullback is, its forward half being Modules on Sites, Lemma 05VD. The three steps above
instantiate it at the same morphism, with two further inputs.

* `Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`, which is 05VD, asks of each ringed
  topos a left exact sheafification of type-valued presheaves.  On the small Zariski site that is
  `AlgebraicGeometry.SmallZariski.hasSheafify_smallType`, the site being essentially small in the
  universe of its sections; on the opens of the space of `S` it is already an instance.
* The reverse half transports flatness along
  `AlgebraicGeometry.SmallZariski.associatedModuleIsoPullbackModules` by
  `Stacks.ModuleUp.isFlat_of_iso`.

## The two local clauses that this file's route does not reach at `τ = Zariski`

* **03DL (2)**, finite locally free, and **03DL (3)**, locally generated by sections, have no
  Stacks 03DM in this development: there is no statement that an equivalence of ringed topoi
  preserves either, and the transports along a pullback of modules —
  `Stacks.Sheaves.LocalGeneration.pullbackModules_isLocallyGeneratedByOnSite` and the finite
  freeness statements of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules` — are for the bounded
  clause (4) and for the *global* clause 03DE (2) respectively.  The missing statements are
  `((f.toModulesHom.pullbackModules).obj F).IsLocallyGeneratedBySectionsOnSite` from
  `F.IsLocallyGeneratedBySectionsOnSite`, and the same for
  `Stacks.SheafOfModules.IsFiniteLocallyFreeOnSite`; each needs the restriction of the pullback
  to the slice sites, which the bounded clause gets from `generatingTupleSheaf`, a construction
  indexed by `Fin r` throughout.

  **Both clauses are proved at `τ = Zariski` all the same**, by arguments that work on the site
  rather than on the associated ringed topos, so what this bullet records is the reach of *this
  file's* route and not an open clause.  03DL (3) is
  `AlgebraicGeometry.SmallZariski.isLocallyGeneratedBySectionsOnSite_associatedModule_iff` in
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.LocalGenerationBySectionsAgreement`,
  and 03DL (2) is
  `AlgebraicGeometry.SmallZariski.isFiniteLocallyFreeOnSite_associatedModule_iff` in
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiFiniteLocallyFreeAgreement`
  (its proof goes through the localization of Remark 03FH's comparison at an open of `S` and
  needs no quasi-coherence either).

## Main results

* `AlgebraicGeometry.SmallZariski.isLocallyGeneratedByOnSite_iff_associatedModule`:
  **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (4), on the small Zariski site.**
* `AlgebraicGeometry.SmallZariski.isFiniteType_iff_associatedModule`:
  **the same for Definition 03DL (5).**
* `AlgebraicGeometry.SmallZariski.isFinitePresentation_iff_associatedModule`:
  **the same for Definition 03DL (7).**
* `AlgebraicGeometry.SmallZariski.isFlat_iff_associatedModule`:
  **the same for Modules on Sites, Definition 03ER (3).**

## Main definitions

* `AlgebraicGeometry.SmallZariski.toOpensRingedToposHom`: Remark 03FH's morphism of ringed sites
  at `τ = Zariski`, read as a morphism of ringed topoi in the sense of Stacks 01D3 (2).
* `AlgebraicGeometry.SmallZariski.commStructureIsoSheaf`: its structure map on sheaves of
  commutative rings, as an isomorphism.
* `AlgebraicGeometry.SmallZariski.associatedModuleIsoPullbackModules`: the identification of the
  pullback of modules along it with `𝓕 ↦ 𝓕^a`.

## Implementation notes

`AlgebraicGeometry.SmallZariski.pullbackModulesCompare` is stated without a type ascription.
Writing its type out defeats elaboration: `Stacks.Sheaves.RingedToposModules.pullbackModules` is
typed with `Stacks.Sheaves.RingedToposModules.structureRingSheaf` of a ringed topos while the
pullback `f.toModulesHom.pullbackModules` along a two-field morphism `f` is typed with
`Stacks.ringSheaf` of its two projections, and although the two agree definitionally the
elaborator fixes the universe metavariables of the ascription — to `0` — before it unifies them.
Leaving the type to be inferred from the two adjunctions avoids the ascription entirely.

For the same reason the morphism of ringed topoi is named, as the abbreviation
`toOpensRingedToposHom`, rather than written as `(toOpensRingedSiteHom B S hS).toRingedToposHom`
at each use: generalized field notation on the latter leaves the universes of
`AlgebraicGeometry.RingedToposHom` to be defaulted.  Two instances are recorded twice for the
corresponding reason — `AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom` is a `def` and
does not unfold at instance transparency, so an instance about `toposHom` is not found about
`toRingedToposHom.toToposHom`.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison as a morphism of ringed topoi -/

/-- **The structure map of Remark 03FH at `τ = Zariski` is an isomorphism**, as a map of sheaves
of commutative rings: it is `AlgebraicGeometry.smallZariskiCommStructureIso` read as a morphism
into the pushforward, and that is an isomorphism of presheaves because each of its components is
`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop`.

Its underlying morphism is `AlgebraicGeometry.SmallZariski.commStructureMap` on the nose. -/
def commStructureIsoSheaf :
    S.zariskiRingedSite.O ≅
      ((opensToSmallZariski B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS)).obj
          (smallZariskiRingedSite B S hS).O :=
  ObjectProperty.isoMk _ (smallZariskiCommStructureIso B S hS)

/-- The underlying morphism of `AlgebraicGeometry.SmallZariski.commStructureIsoSheaf` is
`AlgebraicGeometry.SmallZariski.commStructureMap`. -/
@[simp]
theorem commStructureIsoSheaf_hom :
    (commStructureIsoSheaf B S hS).hom = commStructureMap B S hS := rfl

/-- **Remark 03FH's `id_{small, Zar, Zar} : (S_Zar, 𝒪) ⟶ (S_Zar, 𝒪_S)` as a morphism of ringed
topoi** in the sense of Stacks 01D3 (2): the associated morphism of ringed topoi of
`AlgebraicGeometry.SmallZariski.toOpensRingedSiteHom`. -/
abbrev toOpensRingedToposHom :
    RingedToposHom (smallZariskiRingedSite B S hS).toRingedTopos
      S.zariskiRingedSite.toRingedTopos :=
  (toOpensRingedSiteHom B S hS).toRingedToposHom

/-- **The direct image of Remark 03FH at `τ = Zariski` on sheaves of sets is an equivalence.**
It is the direct image along the site functor on the nose, by
`AlgebraicGeometry.RingedSite.HomGeneral.toposHom_pushforward`, and the inclusion of the opens
of the space of `S` into the small Zariski site is a dense subsite inclusion, so restriction
along it is an equivalence of sheaf topoi. -/
instance isEquivalence_pushforward_toOpensToposHom :
    ((toOpensRingedSiteHom B S hS).toposHom).pushforward.IsEquivalence :=
  inferInstanceAs ((opensToSmallZariski B S hS).sheafPushforwardContinuous (Type u)
    (Opens.grothendieckTopology ↥S) (topology B S hS)).IsEquivalence

/-- The direct image is an equivalence, at the spelling the morphism of ringed topoi is stated
with. -/
instance isEquivalence_pushforward_toOpensRingedToposHom :
    ((toOpensRingedToposHom B S hS).toToposHom).pushforward.IsEquivalence :=
  isEquivalence_pushforward_toOpensToposHom B S hS

/-- **The structure map of Remark 03FH at `τ = Zariski`, read on the associated morphism of
ringed topoi, is an isomorphism.**  It is
`AlgebraicGeometry.SmallZariski.commStructureMap` followed by the inverse of
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, which compares the restriction of the
structure sheaf along the site functor with its direct image along the induced morphism of
topoi; both are isomorphisms. -/
instance isIso_fSharp_toOpensRingedToposHom :
    IsIso ((toOpensRingedToposHom B S hS).fSharp) :=
  ((commStructureIsoSheaf B S hS) ≪≫
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso S.zariskiRingedSite.J
      (smallZariskiRingedSite B S hS).J (opensToSmallZariski B S hS)
      (smallZariskiRingedSite B S hS).O).symm).isIso_hom

/-! ### The pullback of modules along it is `𝓕 ↦ 𝓕^a` -/

/-- **The two constructions of Stacks 03D6 (2) at Remark 03FH's morphism agree.**  The pullback
of sheaves of modules along the four-field morphism of ringed topoi of the modules development
is the pullback along the two-field morphism of Stacks 01D3 (2).

Both are left adjoints of the two pushforwards, which agree by
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`, so this is uniqueness of left
adjoints.  The type is left to be inferred; see the implementation notes of this module. -/
def pullbackModulesCompare :=
  Adjunction.leftAdjointUniq
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (toOpensRingedToposHom B S hS).toRingedToposModulesHom).ofNatIsoRight
        (toOpensRingedToposHom B S hS).pushforwardModulesIso)
    (toOpensRingedToposHom B S hS).pullbackAdjPushforwardModules

/-- **The pullback of a sheaf of `𝒪_S`-modules along Remark 03FH's morphism of ringed topoi is
`𝓕^a`.**  Two comparisons are composed: `pullbackModulesCompare`, which replaces the pullback
along the two-field morphism by the pullback of the modules development, and
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral`, which replaces that by
the site-presented pullback — which *is* `AlgebraicGeometry.SmallZariski.associatedModule`, by
`AlgebraicGeometry.SmallZariski.pullbackToposGeneral_toOpensRingedSiteHom`. -/
def associatedModuleIsoPullbackModules (F : SheafOfModules.{u} S.ringCatSheaf) :
    ((toOpensRingedToposHom B S hS).toModulesHom.pullbackModules).obj F ≅
      (associatedModuleOfSheaf B S hS).obj F :=
  ((pullbackModulesCompare B S hS).app F).symm ≪≫
    ((toOpensRingedSiteHom B S hS).pullbackModulesToposIsoGeneral).app F

/-! ### The three local clauses of 03DL -/

/-- A property transported along isomorphisms holds of an object if and only if it holds of any
isomorphic object. -/
private theorem iff_of_iso_of_forall_iso {C : Type*} [Category C] {P : C → Prop}
    (hP : ∀ {X Y : C}, (X ≅ Y) → P X → P Y) {X Y : C} (e : X ≅ Y) : P X ↔ P Y :=
  ⟨hP e, hP e.symm⟩

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (4), on the small Zariski
site.**  A sheaf of `𝒪_S`-modules is locally generated by `r` sections if and only if `𝓕^a` is
locally generated by `r` sections as an `𝒪`-module on `S_Zar`.

This is Stacks 03DM for that clause,
`AlgebraicGeometry.RingedToposHom.isLocallyGeneratedByOnSite_iff_pullbackModules`, instantiated
at `AlgebraicGeometry.SmallZariski.toOpensRingedToposHom` and transported along
`AlgebraicGeometry.SmallZariski.associatedModuleIsoPullbackModules`.  No quasi-coherence is
needed, the comparison being an equivalence of the whole module categories. -/
@[stacks 05VG "locally generated by r sections (03DL (4)), small site at τ = Zariski, at the \
comparison functor of 03DX itself"]
theorem isLocallyGeneratedByOnSite_iff_associatedModule
    (F : SheafOfModules.{u} S.ringCatSheaf) (r : ℕ) :
    F.IsLocallyGeneratedByOnSite r ↔
      ((associatedModuleOfSheaf B S hS).obj F).IsLocallyGeneratedByOnSite r := by
  have h := (toOpensRingedToposHom B S hS).isLocallyGeneratedByOnSite_iff_pullbackModules
  exact (h F r).trans (iff_of_iso_of_forall_iso
    (fun e => Stacks.SheafOfModules.Intrinsic.isLocallyGeneratedByOnSite_of_iso e r)
    (associatedModuleIsoPullbackModules B S hS F))

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (5), on the small Zariski
site.**  A sheaf of `𝒪_S`-modules is of finite type if and only if `𝓕^a` is of finite type as
an `𝒪`-module on `S_Zar`.

This is Stacks 03DM for that clause,
`AlgebraicGeometry.RingedToposHom.isFiniteType_iff_pullbackModules`, instantiated at
`AlgebraicGeometry.SmallZariski.toOpensRingedToposHom` and transported along
`AlgebraicGeometry.SmallZariski.associatedModuleIsoPullbackModules`. -/
@[stacks 05VG "finite type (03DL (5)), small site at τ = Zariski, at the comparison functor of \
03DX itself"]
theorem isFiniteType_iff_associatedModule (F : SheafOfModules.{u} S.ringCatSheaf) :
    F.IsFiniteType ↔ ((associatedModuleOfSheaf B S hS).obj F).IsFiniteType := by
  have h := (toOpensRingedToposHom B S hS).isFiniteType_iff_pullbackModules
  exact (h F).trans (iff_of_iso_of_forall_iso
    (fun e => Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso e)
    (associatedModuleIsoPullbackModules B S hS F))

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (7), on the small Zariski
site.**  A sheaf of `𝒪_S`-modules is of finite presentation if and only if `𝓕^a` is of finite
presentation as an `𝒪`-module on `S_Zar`.

This is Stacks 03DM for that clause,
`AlgebraicGeometry.RingedToposHom.isFinitePresentation_iff_pullbackModules`, instantiated at
`AlgebraicGeometry.SmallZariski.toOpensRingedToposHom` and transported along
`AlgebraicGeometry.SmallZariski.associatedModuleIsoPullbackModules`. -/
@[stacks 05VG "finite presentation (03DL (7)), small site at τ = Zariski, at the comparison \
functor of 03DX itself"]
theorem isFinitePresentation_iff_associatedModule (F : SheafOfModules.{u} S.ringCatSheaf) :
    F.IsFinitePresentation ↔ ((associatedModuleOfSheaf B S hS).obj F).IsFinitePresentation := by
  have h := (toOpensRingedToposHom B S hS).isFinitePresentation_iff_pullbackModules
  exact (h F).trans (iff_of_iso_of_forall_iso
    (fun e => Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso e)
    (associatedModuleIsoPullbackModules B S hS F))

/-! ### The flat clause -/

/-- Type-valued presheaves on the small Zariski site of `S` have a left exact sheafification,
the site being essentially small in the universe of its sections.  This is what Modules on
Sites, Lemma 05VD asks of a ringed topos; the `AddCommGrpCat`-valued instance is
`AlgebraicGeometry.SmallZariski.hasWeakSheafify_smallZariski`. -/
public instance hasSheafify_smallType :
    HasSheafify (AlgebraicGeometry.SmallZariski.topology B S hS) (Type u) :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), on the small Zariski
site.**  A sheaf of `𝒪_S`-modules is flat if and only if `𝓕^a` is flat as an `𝒪`-module on
`S_Zar`.

This is `AlgebraicGeometry.RingedToposHom.isFlat_iff_pullbackModules` — the flatness clause for
an equivalence of ringed topoi, whose forward half is Modules on Sites, Lemma 05VD — instantiated
at
`AlgebraicGeometry.SmallZariski.toOpensRingedToposHom` and transported along
`AlgebraicGeometry.SmallZariski.associatedModuleIsoPullbackModules` by
`Stacks.ModuleUp.isFlat_of_iso_anySite`.  No quasi-coherence is needed, the comparison being an
equivalence of the whole module categories; the source's clause carries quasi-coherence, so this
is the clause over a weaker hypothesis than the source's. -/
@[stacks 05VG "flat (03ER (3)), small site at τ = Zariski, at the comparison functor of \
03DX itself"]
public theorem isFlat_iff_associatedModule (F : SheafOfModules.{u} S.ringCatSheaf) :
    Stacks.SheafOfModules.IsFlat (O := S.zariskiRingedSite.O) F ↔
      Stacks.SheafOfModules.IsFlat (O := (smallZariskiRingedSite B S hS).O)
        ((associatedModuleOfSheaf B S hS).obj F) := by
  have h := (toOpensRingedToposHom B S hS).isFlat_iff_pullbackModules
  exact (h F).trans (iff_of_iso_of_forall_iso
    (fun e => Stacks.ModuleUp.isFlat_of_iso_anySite (O := (smallZariskiRingedSite B S hS).O) e)
    (associatedModuleIsoPullbackModules B S hS F))

end AlgebraicGeometry.SmallZariski

end
