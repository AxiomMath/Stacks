module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposTriangle
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Pullback

/-!
# Pullback of modules along the inclusion of a full subsite is restriction (Stacks 0788 (1)(f))

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids carrying the site of **Stacks 06TP**, and
let `P` cut out a full subcategory whose inclusion is continuous and cocontinuous for the inherited
topology. `StacksFrontier/AlgebraicGeometry/Stacks/SubcategoryRingedTopos.lean` assembles from this
the morphism of ringed topoi `g : (Sh(𝒳'), 𝒪_{𝒳'}) ⟶ (Sh(𝒳), 𝒪_𝒳)` whose inverse image is
restriction along the inclusion and whose structure map is an isomorphism.

This file proves that **pullback of sheaves of modules along `g` is restriction of sheaves of
modules**, which is the precise content of the source's `g^{-1} = g^*`: the third assertion of
**Stacks 0788** (1)(f) for the lisse-étale site, and of (2)(f) for the flat-fppf site. The
lisse-étale case is the instantiation `AlgebraicGeometry.Stack.LisseEtale.modulePullbackIso`,
which carries the tag; the first two assertions of (1)(f) — the identification
`g⁻¹𝒪_𝒳 = 𝒪_{𝒳_{lisse,étale}}` and flatness of `g` — are
`StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure`.

The proof has two halves, and neither is about the lisse-étale site in particular, which is why
everything below the instantiation is stated for an arbitrary full subsite.

* **The inverse image.** Because the inclusion is cocontinuous as well as continuous, the inverse
  image of `g` on sheaves of sets *is* restriction along the inclusion, on the nose. So the inverse
  image of sheaves of modules of **Stacks 03D2** is restriction of sheaves of modules, the two
  differing only by the transport of the module structure along a sections functor — which is
  `Stacks.Sheaves.ToposPullback.restrictionModuleIso`, for an arbitrary continuous functor of
  sites. The scalars are compared along the ring-level comparison
  `AlgebraicGeometry.Stack.subsiteRingRestrictionIso`.
* **The extension of scalars.** Pullback of modules is that inverse image followed by extension of
  scalars along the inverse-image form of the structure map, and here that structure map is the
  ring-level comparison itself, hence an isomorphism
  (`AlgebraicGeometry.Stack.subsiteRingedToposModulesHom_fSharpInverseImage`). Restriction of
  scalars along an isomorphism of sheaves of rings is fully faithful, so the counit of the
  adjunction of **Stacks 03CZ** is an isomorphism and the extension of scalars undoes the
  restriction of scalars left over from the first half.

## Main definitions

* `AlgebraicGeometry.Stack.subsiteRingedToposModuleRestriction`: restriction of sheaves of modules
  along the inclusion of the full subsite, the functor the assertion identifies the pullback with.
* `AlgebraicGeometry.Stack.subsiteRingedToposModulesHom`: the morphism of ringed topoi of a full
  subsite presented as a `Stacks.Sheaves.RingedToposModules.RingedToposHom`, which is the datum the
  pullback of modules of **Stacks 03D6** part (2) is stated for.
* `AlgebraicGeometry.Stack.subsiteRingRestrictionIso`: the inverse image of the structure sheaf is
  its restriction, at the level of sheaves of rings.

## Main results

* `AlgebraicGeometry.Stack.subsiteModulePullbackIso`: pullback of sheaves of modules along the
  morphism of ringed topoi of a full subsite is restriction of sheaves of modules along the
  inclusion.
* `AlgebraicGeometry.Stack.LisseEtale.modulePullbackIso`: **Stacks 0788** (1)(f), third
  assertion — that statement for the inclusion of the lisse-étale site of an algebraic stack into
  its étale site, with no hypothesis.

## Implementation notes

An `AlgebraicGeometry.RingedToposHom` carries only the direct-image form of the structure map, and
`Stacks.Sheaves.RingedToposModules.RingedToposHom` is the four-field datum carrying both forms at
the `RingCat` level together with the equation making them adjunct. Nothing is chosen in passing
from the one to the other:
`Stacks.Sheaves.RingedToposModules.RingedToposHom.ofFSharpInverseImage` takes the same morphism of
topoi and the same inverse-image structure map as
`AlgebraicGeometry.Stack.subsiteRingedToposHom`, read through
`CategoryTheory.forget₂ CommRingCat RingCat`, and the remaining two fields are forced.

The sheafification hypotheses the pullback of modules needs on the subsite — existence of
sheafification for `AddCommGrpCat.{u}`-valued presheaves, and sheafification equivalences being the
local bijections — are not available by the size-matched route when the site has its objects above
the universe of the sections. They are the instances
`AlgebraicGeometry.Stack.hasSheafifyAddCommGrpCat_subsiteTopology` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_subsiteTopology` of
`StacksFrontier/AlgebraicGeometry/Stacks/SubcategoryModuleLowerShriek.lean`, which hold because a full
subsite of an essentially small site is essentially small.

For the lisse-étale instantiation the two locality hypotheses are
`AlgebraicGeometry.Stack.LisseEtale.isContinuous_inclusion'` and
`AlgebraicGeometry.Stack.LisseEtale.isCocontinuous_inclusion'`, which hold for every algebraic
stack, and essential smallness is the instance
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`, so the instantiation carries no
hypothesis. Its subsite ringed topos and morphism of ringed topoi are
`AlgebraicGeometry.Stack.LisseEtale.ringedTopos'` and
`AlgebraicGeometry.Stack.LisseEtale.ringedToposMorphism'` unfolded one step, those two being the
`subsite` constructions at `P = AlgebraicGeometry.Stack.smoothObject`.

The flat-fppf case is *not* re-derived here: it is already
`AlgebraicGeometry.Stack.FlatFppf.modulePullbackIso` of
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfRingedModules.lean`, stated at that file's own
spelling of the morphism of ringed topoi, which is read at
`AlgebraicGeometry.Stack.FlatFppf.topology` rather than at the inherited topology.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (P : ObjectProperty X)
  [EssentiallySmall.{u} X]
  [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- **Restriction of sheaves of modules along the inclusion of a full subsite**, over the structure
sheaf of **Stacks 06TV** and its restriction. The scalar comparison is the identity, because the
structure sheaf of the subsite is the restriction of the ambient one with its original rings of
sections.

This is the functor that the third assertion of **Stacks 0788** (1)(f) and (2)(f) identifies
pullback of modules along `AlgebraicGeometry.Stack.subsiteRingedToposHom` with; the identification
is `AlgebraicGeometry.Stack.subsiteModulePullbackIso`. -/
noncomputable def subsiteRingedToposModuleRestriction :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS p hp τ hτ P).O) :=
  SheafOfModules.pushforward (F := P.ι) (𝟙 _)

/-- The morphism of ringed topoi of a full subsite, presented as a
`Stacks.Sheaves.RingedToposModules.RingedToposHom` — the datum the pullback of sheaves of modules
of **Stacks 03D6** part (2) is stated for. It carries the same morphism of topoi and the same
inverse-image structure map as `AlgebraicGeometry.Stack.subsiteRingedToposHom`, read at the
`RingCat` level; the direct-image form and the equation making the two adjunct are then forced. -/
noncomputable def subsiteRingedToposModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (subsiteRingedTopos B S hS p hp τ hτ P) (associatedRingedTopos B S hS p hp τ hτ) :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.ofFSharpInverseImage
    (X := subsiteRingedTopos B S hS p hp τ hτ P)
    (Y := associatedRingedTopos B S hS p hp τ hτ) (subsiteToposMorphism B S hS p τ P)
    ((sheafCompose (subsiteTopology B S hS p τ P)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (subsiteRingedToposHom B S hS p hp τ hτ P).fSharpInverseImage)

/-- **The inverse image of the structure sheaf is its restriction, as a sheaf of rings.** This is
`AlgebraicGeometry.Stack.subsiteStructureSheafIso` after forgetting commutativity: the inverse
image of the morphism of topoi of a full subsite is restriction along the inclusion, so the
comparison is the identity on sections.

It is stated at the morphism of topoi carried by
`AlgebraicGeometry.Stack.subsiteRingedToposModulesHom`, which is
`AlgebraicGeometry.Stack.subsiteToposMorphism` on the nose
(`Stacks.Sheaves.RingedToposModules.RingedToposHom.ofFSharpInverseImage_toToposHom`); writing it
that way is what lets the extension-of-scalars half of
`AlgebraicGeometry.Stack.subsiteModulePullbackIso` be assembled without reducing a structure
projection inside an implicit argument. -/
noncomputable def subsiteRingRestrictionIso :
    inverseImageRingSheaf.{u, u, w, v, w, v}
        (subsiteRingedToposModulesHom B S hS p hp τ hτ P).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O) ≅
      Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS p hp τ hτ P).O :=
  restrictionRingIso (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι
    (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O)

/-- The inverse-image form of the structure map of the morphism of ringed topoi of a full subsite
is the ring-level restriction comparison. In particular it is an isomorphism, which is what makes
the extension of scalars in the pullback of modules undo a restriction of scalars. -/
theorem subsiteRingedToposModulesHom_fSharpInverseImage :
    (subsiteRingedToposModulesHom B S hS p hp τ hτ P).fSharpInverseImage =
      (subsiteRingRestrictionIso B S hS p hp τ hτ P).hom :=
  (sheafCompose (subsiteTopology B S hS p τ P) (forget₂ CommRingCat.{u} RingCat.{u})).congr_map
    (fSharpInverseImage_subsiteRingedToposHom B S hS p hp τ hτ P)

/-- **`g^* = g^{-1}` on sheaves of modules for a full subsite.** Pullback of sheaves of modules
along the morphism of ringed topoi of a full subsite *is* restriction of sheaves of modules along
the inclusion, over the structure sheaf of **Stacks 06TV** and its restriction.

The inverse image of sheaves of modules is restriction of sheaves of modules with its scalars read
through `AlgebraicGeometry.Stack.subsiteRingRestrictionIso`
(`Stacks.Sheaves.ToposPullback.restrictionModuleIso`), and the extension of scalars that completes
the pullback is extension along that same comparison, so it undoes that restriction of scalars:
restriction of scalars along an isomorphism of sheaves of rings is fully faithful, so the counit of
**Stacks 03CZ** is an isomorphism. -/
noncomputable def subsiteModulePullbackIso :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, w, v, w, v}
        (subsiteRingedToposModulesHom B S hS p hp τ hτ P) ≅
      subsiteRingedToposModuleRestriction B S hS p hp τ hτ P := by
  let f := subsiteRingedToposModulesHom B S hS p hp τ hτ P
  let k := (subsiteRingRestrictionIso B S hS p hp τ hτ P).hom
  let E := extendScalarsFSharp f
  let R := SheafOfModules.restrictScalars k
  let ff := AlgebraicGeometry.RingedSite.restrictScalarsFullyFaithful k
  have hk : SheafOfModules.restrictScalars
      (commRingSheafMap (subsiteTopology B S hS p τ P) (fSharpCommRing f)
        (inverseImageRingSheaf.{u, u, w, v, w, v} f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (associatedRingedTopos B S hS p hp τ hτ).O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (subsiteRingedTopos B S hS p hp τ hτ P).O).property) = R :=
    congrArg SheafOfModules.restrictScalars
      ((commRingSheafMap_fSharpCommRing f).trans
        (subsiteRingedToposModulesHom_fSharpInverseImage B S hS p hp τ hτ P))
  let adj : E ⊣ R :=
    Adjunction.ofNatIsoRight
      (extendRestrictScalarsAdjunction (subsiteTopology B S hS p τ P) (fSharpCommRing f)
        (inverseImageRingSheaf.{u, u, w, v, w, v} f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (associatedRingedTopos B S hS p hp τ hτ).O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (subsiteRingedTopos B S hS p hp τ hτ P).O).property)
      (eqToIso hk)
  have := ff.full
  have := ff.faithful
  let counitIso : R ⋙ E ≅ 𝟭 _ := asIso adj.counit
  -- the inverse image of modules along `g` is restriction of modules, with the scalars read
  -- through the ring-level comparison; ascribing the type here is what pins the inverse image of
  -- `g` to be restriction along the inclusion
  let e : inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O) ≅
      subsiteRingedToposModuleRestriction B S hS p hp τ hτ P ⋙ R :=
    restrictionModuleIso (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O)
  exact Functor.isoWhiskerRight e E ≪≫
    Functor.associator (subsiteRingedToposModuleRestriction B S hS p hp τ hτ P) R E ≪≫
    Functor.isoWhiskerLeft (subsiteRingedToposModuleRestriction B S hS p hp τ hτ P) counitIso ≪≫
      Functor.rightUnitor (subsiteRingedToposModuleRestriction B S hS p hp τ hτ P)

/-! ### The lisse-étale site -/

namespace LisseEtale

universe t

variable (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **Stacks 0788, part (1)(f), third assertion**: `g^{-1} = g^*`. Pullback of sheaves of modules
along the lisse-étale morphism of ringed topoi
`AlgebraicGeometry.Stack.LisseEtale.ringedToposMorphism'` *is* restriction of sheaves of modules
along the inclusion of the smooth objects, over the étale structure sheaf of **Stacks 06TV** and
its restriction. No hypothesis is carried: this is
`AlgebraicGeometry.Stack.subsiteModulePullbackIso` at `P = AlgebraicGeometry.Stack.smoothObject`
and the étale topology, where the two locality hypotheses hold for every algebraic stack. -/
@[stacks 0788 "part (1)(f): pullback of modules along it is restriction of modules"]
noncomputable def modulePullbackIso :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u + 1}
        (subsiteRingedToposModulesHom B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳)) ≅
      subsiteRingedToposModuleRestriction B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳) :=
  subsiteModulePullbackIso B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
    (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳)

end LisseEtale

end AlgebraicGeometry.Stack

end
