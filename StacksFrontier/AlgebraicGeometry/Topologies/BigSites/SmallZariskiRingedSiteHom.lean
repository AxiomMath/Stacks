module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.RingedBigSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.ComapSheafCondition
public import StacksCore.Tactic.StacksAttribute

/-!
# `f_small` as a morphism of ringed small Zariski sites

Stacks 070R, part (2) states that a morphism of schemes `f : X ⟶ Y` makes the morphism of
small sites `f_small : X_\etale ⟶ Y_\etale` a morphism of ringed sites

```
  (f_small, f_small^♯) : (X_\etale, 𝒪_X) ⟶ (Y_\etale, 𝒪_Y),
```

and adds "similarly for the small Zariski site".  The étale case is
`AlgebraicGeometry.smallEtaleRingedSiteHom`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/RingedSiteHom.lean`); this
file is the small Zariski case, item (27) of the change-of-topologies list of Topologies,
Section 03FE.

## Main definitions

* `AlgebraicGeometry.smallZariskiStructureSharp`: the structure map
  `f_small^♯ : 𝒪_S ⟶ f_{small, *}𝒪_T` on the small Zariski sites.
* `AlgebraicGeometry.smallZariskiRingedSiteHom`: the pair `(f_small, f_small^♯)` as a morphism
  of ringed sites.

## Main results

* `AlgebraicGeometry.preservesFiniteLimits_smallZariskiBaseChange` and
  `AlgebraicGeometry.representablyFlat_smallZariskiBaseChange`: small Zariski base change is
  left exact.
* `AlgebraicGeometry.smallZariskiBaseChange_isMorphismOfSites_ringUniverse`: it defines a
  morphism of sites at the universe of the sections of the structure sheaves.

## Implementation notes

The lemma `AlgebraicGeometry.smallZariskiBaseChange_isMorphismOfSites` is the site condition
for sheaves of sets in `Type (u + 1)`, the universe of the *objects* of the small Zariski site,
whereas a morphism of ringed sites reads its site condition at the universe of the sections of
the structure sheaves.  The condition needed here is therefore a different statement, obtained
from `isMorphismOfSites_of_essentiallySmall`: the small Zariski site is essentially small at `u`
because a localized big site is
(`AlgebraicGeometry.essentiallySmall_overBase`) and the small Zariski site is a full
subcategory of one.

Left exactness of base change has to be rebuilt rather than quoted, because
`AlgebraicGeometry.smallZariskiBaseChange` is defined by `Classical.choose` from
`AlgebraicGeometry.exists_smallZariskiBaseChange`, which records only continuity, the
`Type (u + 1)` site condition and the identification with the fibre product — not flatness,
which the private functor underlying the choice does have.  It is recovered from that
identification: the composite with the fully faithful functor to the schemes over the base
preserves finite limits, and a fully faithful functor reflects limits.

The ringed site is `AlgebraicGeometry.smallZariskiRingedSite`, whose structure sheaf
is that of `AlgebraicGeometry.SmallZariski.ringedTopos`; it is the same sheaf as the one
`AlgebraicGeometry.ChangeOfSites.ringedSite` builds from the sheaf condition of Stacks 03DU, so
no second ringed site is introduced and the two spellings agree by `rfl`.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 0211](https://stacks.math.columbia.edu/tag/0211)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

/-! ### Finite limits on the small Zariski site -/

/-- The inclusion of the small Zariski site of `S` into the big Zariski site over `S` preserves
finite limits: it preserves the terminal object and fibre products. -/
public instance preservesFiniteLimits_smallZariskiInclusion :
    PreservesFiniteLimits (SmallZariski.inclusion B S.1 S.property) :=
  have : PreservesLimitsOfShape (Discrete.{0} PEmpty)
      (SmallZariski.inclusion B S.1 S.property) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- Postcomposition with the inclusion of the chosen category of schemes preserves the terminal
object of the big Zariski site over `S`: that object is the identity of `S`, which
postcomposition carries to the identity of `S` read in all schemes. -/
public instance preservesTerminal_bigZariskiOverPost :
    PreservesLimitsOfShape (Discrete.{0} PEmpty) (Over.post (X := S) B.inclusion) := by
  refine CategoryTheory.Functor.preservesLimitsOfShape_pempty_of_isTerminal _
    (Over.mkIdTerminal (X := S)) ?_
  have h : (Over.post (X := S) B.inclusion).obj (Over.mk (𝟙 S)) =
      Over.mk (𝟙 (B.inclusion.obj S)) := by simp
  rw [h]
  exact Over.mkIdTerminal

/-- Postcomposition with the inclusion of the chosen category of schemes preserves finite
limits. -/
public instance preservesFiniteLimits_bigZariskiOverPost :
    PreservesFiniteLimits (Over.post (X := S) B.inclusion) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- The canonical functor from the small Zariski site of `S` to the schemes over `S` preserves
finite limits. -/
public instance preservesFiniteLimits_smallSiteInSchemesOver :
    PreservesFiniteLimits (smallSiteInSchemesOver B S) := by
  have h₁ := preservesFiniteLimits_smallZariskiInclusion (S := S) B
  have h₂ := preservesFiniteLimits_bigZariskiOverPost (S := S) B
  exact comp_preservesFiniteLimits _ _

/-- The canonical functor from the small Zariski site of `S` to the schemes over `S` is full. -/
public instance full_smallSiteInSchemesOver : (smallSiteInSchemesOver B S).Full :=
  inferInstanceAs ((SmallZariski.inclusion B S.1 S.property ⋙
    Over.post (X := S) B.inclusion).Full)

/-- The canonical functor from the small Zariski site of `S` to the schemes over `S` is
faithful. -/
public instance faithful_smallSiteInSchemesOver : (smallSiteInSchemesOver B S).Faithful :=
  inferInstanceAs ((SmallZariski.inclusion B S.1 S.property ⋙
    Over.post (X := S) B.inclusion).Faithful)

/-- **The small Zariski site of `S` is essentially small at the universe of its morphisms.**  It
is a full subcategory of the big Zariski site over `S`, which is a localized big site. -/
public instance essentiallySmall_smallZariski :
    EssentiallySmall.{u} (SmallZariski B S.1 S.property) :=
  have : EssentiallySmall.{u} (BigZariskiOver B S.1 S.property) :=
    essentiallySmall_overBase (τ := .zariski) B S.1 S.property
  essentiallySmall_of_fully_faithful (SmallZariski.inclusion B S.1 S.property)

/-- The small Zariski site of `S` has finite limits. -/
public instance hasFiniteLimits_smallZariski :
    HasFiniteLimits (SmallZariski B S.1 S.property) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-! ### Left exactness of small Zariski base change -/

/-- **Small Zariski base change is left exact.**  Composed with the canonical functor to the
schemes over the base it is the fibre product of a left exact functor, by
`AlgebraicGeometry.smallZariskiBaseChangeIso`, and that functor is fully faithful, hence
reflects limits. -/
public instance preservesFiniteLimits_smallZariskiBaseChange :
    PreservesFiniteLimits (smallZariskiBaseChange B f) := by
  have h : PreservesFiniteLimits (smallZariskiBaseChange B f ⋙ smallSiteInSchemesOver B T) :=
    preservesFiniteLimits_of_natIso (smallZariskiBaseChangeIso B f).symm
  exact ⟨fun _ _ _ =>
    preservesLimitsOfShape_of_reflects_of_preserves _ (smallSiteInSchemesOver B T)⟩

/-- Small Zariski base change is representably flat. -/
public instance representablyFlat_smallZariskiBaseChange :
    RepresentablyFlat (smallZariskiBaseChange B f) :=
  flat_of_preservesFiniteLimits _

/-- **Stacks 0211 at the universe of the structure rings.**  Small Zariski base change along
`f` defines a morphism of sites for sheaves of sets valued in the universe `u` of the sections
of the structure sheaves.

This is the input a morphism of ringed sites needs, and
`AlgebraicGeometry.smallZariskiBaseChange_isMorphismOfSites` does not provide it: that one is
stated for sheaves of sets in `Type (u + 1)`, the universe of the objects of the site. -/
@[stacks 0211 "f_small on small Zariski sites, at the universe of the structure rings"]
public instance smallZariskiBaseChange_isMorphismOfSites_ringUniverse :
    IsMorphismOfSites.{u} (smallZariskiBaseChange B f)
      (SmallZariski.topology B S.1 S.property) (SmallZariski.topology B T.1 T.property) :=
  isMorphismOfSites_of_essentiallySmall _ _ _

/-! ### `(f_small, f_small^♯)` on the small Zariski sites -/

/-- The ringed site of the small Zariski site of `S` as built from the sheaf condition of
Stacks 03DU is `AlgebraicGeometry.smallZariskiRingedSite`: both have the presheaf of
global functions as structure sheaf. -/
public theorem changeOfSites_ringedSite_eq_smallZariskiRingedSite :
    ChangeOfSites.ringedSite S.1 (SmallZariski.topology B S.1 S.property)
        (smallSiteInSchemesOver B S) (SmallZariski.structure_isSheaf B S.1 S.property) =
      smallZariskiRingedSite B S.1 S.property := rfl

/-- **Stacks 070R, part (2): the structure map `f_small^♯ : 𝒪_S ⟶ f_{small, *}𝒪_T`** on the
small Zariski sites.  On an open `V/S` it is the map on global functions induced by the
projection `T ×_S V ⟶ V`, through the identification of small Zariski base change with the
fibre product. -/
@[stacks 070R "part (2): `f_small^♯` for the small Zariski sites"]
public noncomputable def smallZariskiStructureSharp :
    (smallZariskiRingedSite B S.1 S.property).O ⟶
      ((smallZariskiBaseChange B f).sheafPushforwardContinuous CommRingCat.{u}
          (SmallZariski.topology B S.1 S.property)
          (SmallZariski.topology B T.1 T.property)).obj
        (smallZariskiRingedSite B T.1 T.property).O :=
  ChangeOfSites.structureSharpOfBaseChange (SmallZariski.topology B S.1 S.property)
    (SmallZariski.topology B T.1 T.property) (smallSiteInSchemesOver B S)
    (smallSiteInSchemesOver B T) (smallZariskiBaseChange B f) (B.inclusion.map f)
    (smallZariskiBaseChangeIso B f) (SmallZariski.structure_isSheaf B S.1 S.property)
    (SmallZariski.structure_isSheaf B T.1 T.property)

/-- The component of `f_small^♯` at an open `V` of the small Zariski site of `S` is the map on
global sections of the first projection `V ×_S T ⟶ V`, precomposed with the identification of
the base change of `V` with that fibre product. -/
@[simp]
public theorem smallZariskiStructureSharp_hom_app (V : SmallZariski B S.1 S.property) :
    (smallZariskiStructureSharp B f).hom.app (op V) =
      Scheme.Γ.map (op (((smallZariskiBaseChangeIso B f).hom.app V).left ≫
        pullback.fst ((smallSiteInSchemesOver B S).obj V).hom (B.inclusion.map f))) := rfl

/-- **Stacks 070R, part (2), for the small Zariski site.**  A morphism of schemes `f : T ⟶ S` of
a big Zariski site makes the morphism of small sites `f_small : T_{Zar} ⟶ S_{Zar}` a morphism of
ringed sites

```
  (f_small, f_small^♯) : (T_{Zar}, 𝒪_T) ⟶ (S_{Zar}, 𝒪_S)
```

in the sense of Stacks 03AD.  This is the "similarly for the small Zariski site" of part (2),
and item (27) of the change-of-topologies list of Topologies, Section 03FE. -/
@[stacks 070R "part (2): `(f_small, f_small^♯)` for the small Zariski sites"]
public noncomputable def smallZariskiRingedSiteHom :
    RingedSite.HomGeneral (smallZariskiRingedSite B T.1 T.property)
      (smallZariskiRingedSite B S.1 S.property) where
  u := smallZariskiBaseChange B f
  isMorphismOfSites := smallZariskiBaseChange_isMorphismOfSites_ringUniverse B f
  fsharp := smallZariskiStructureSharp B f

/-- The underlying functor of `(f_small, f_small^♯)` is small Zariski base change along `f`. -/
@[simp]
public theorem smallZariskiRingedSiteHom_u :
    (smallZariskiRingedSiteHom B f).u = smallZariskiBaseChange B f := rfl

/-- The structure map of `(f_small, f_small^♯)` is
`AlgebraicGeometry.smallZariskiStructureSharp`. -/
@[simp]
public theorem smallZariskiRingedSiteHom_fsharp :
    (smallZariskiRingedSiteHom B f).fsharp = smallZariskiStructureSharp B f := rfl

end AlgebraicGeometry

end
