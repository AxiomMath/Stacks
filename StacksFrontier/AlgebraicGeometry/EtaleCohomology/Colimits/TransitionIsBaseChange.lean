module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-! # The transition functors of Stacks 0EYL are étale base change

`Stacks.EtaleCohomology.AffineEtaleSiteColimit` records that each transition functor of the site
system of Stacks 0EYL *is* geometric base change, by the fibre-product squares
`transition_isPullback`: the image of an object `Y` of the level `j` under `system.u a` has, as
its structure morphism over `X_i`, the second projection of a fibre product of the structure
morphism of `Y` along `X_i ⟶ X_j`. That is a square-by-square statement about objects.

This file turns it into an isomorphism of *functors* into the small étale site of `X_i`:

`system.u a ⋙ levelEtale i ≅ levelEtale j ⋙ smallEtaleBaseChange (X_i ⟶ X_j)`

where `levelEtale i` reads a level as the small affine étale site of `X_i` and then as a full
subcategory of the small étale site of `X_i`, and `AlgebraicGeometry.smallEtaleBaseChange` is
base change of small étale sites.

The point of landing in the small *étale* site rather than the small affine étale site is that
base change of small étale sites exists for *every* morphism of the big étale site
(`AlgebraicGeometry.smallEtaleBaseChange`), together with its continuity and its universal
property, whereas base change between small *affine* étale sites is assembled only when both
ends are affine (`AlgebraicGeometry.smallAffineEtaleBaseChange`); and the small affine étale
site is a dense subsite of the small étale site, so nothing is lost by passing to the larger
one.

## Main definitions

* `levelEtale` — a level of the system of Stacks 0EYL, read as a full subcategory of the small
  étale site of the scheme it sits over.
* `stageMap` — the transition morphism `X_i ⟶ X_j` of the system, read in the bounded category
  of the big étale site.
* `transitionIso` — **the comparison isomorphism**: the transition functor of the system is base
  change along `stageMap`.

## Main results

* `componentIso_hom_fst` and `componentIso_hom_snd`: the components of the comparison are pinned
  by the two projections of the fibre product — the first is the projection `transitionFst` of
  the system, the second is the structure morphism.
* `stageMap_id` and `stageMap_comp`: the transition morphisms of the stages compose and carry
  identities to identities.
* `AlgebraicGeometry.SmallEtale.hom_ext_fst`: two morphisms into a small étale base change agree
  as soon as their composites with the projection onto the object based from agree, for an
  arbitrary morphism of the big étale site; `hom_ext_fst` is its instance at a transition
  morphism of the system.

## Implementation notes

No affineness of the transition morphisms is used, and neither is the limit cone: the fibre
products involved exist in the bounded category of any big étale site, and the squares are data
of `AffineEtaleSiteColimit`.

Every component is constructed by `CategoryTheory.IsPullback.isoIsPullback` from the two squares
over the one cospan `(structure morphism of Y, X_i ⟶ X_j)`, and is therefore uniquely determined
by its compatibility with the two projections. Identities between components are proved by
checking those two compatibilities, through the faithfulness of the inclusions of the small étale
site into the slice category and of the bounded category into schemes.

## References

* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v u

namespace AlgebraicGeometry.SmallEtale

/-- **Two morphisms into a small étale base change agree as soon as they agree on the projection
onto the object based from.** The remaining projection of the fibre product is the structure
morphism, and every morphism of the small étale site of `T` is a morphism over `T`. -/
theorem hom_ext_fst {B : AlgebraicGeometry.BigEtaleSite.{w}} {S T : B.Scheme} (f : T ⟶ S)
    {Z : AlgebraicGeometry.SmallEtale B S.obj S.property}
    {W : AlgebraicGeometry.SmallEtale B T.obj T.property}
    (α β : W ⟶ (AlgebraicGeometry.smallEtaleBaseChange B f).obj Z)
    (h : (toScheme B T.obj T.property).map α ≫ B.inclusion.map (pullback.fst Z.obj.hom f) =
      (toScheme B T.obj T.property).map β ≫ B.inclusion.map (pullback.fst Z.obj.hom f)) :
    α = β := by
  refine (inclusion B T.obj T.property).map_injective
    (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))
  · have e : ∀ γ : W ⟶ (AlgebraicGeometry.smallEtaleBaseChange B f).obj Z,
        B.inclusion.map (((inclusion B T.obj T.property).map γ).left ≫
            pullback.fst Z.obj.hom f) =
          (toScheme B T.obj T.property).map γ ≫ B.inclusion.map (pullback.fst Z.obj.hom f) :=
      fun _ => B.inclusion.map_comp _ _
    exact B.inclusion.map_injective ((e α).trans (h.trans (e β).symm))
  · exact (Over.w _).trans (Over.w _).symm

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology.TransitionBaseChange

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX)

/-- The stage of `Iᵒᵖ` that a level of the system sits over. -/
abbrev stage (i : E.system.I) : Iᵒᵖ := E.indexEquiv.functor.obj i

/-- A level of the system of Stacks 0EYL, read as a full subcategory of the small étale site of
the scheme it sits over. -/
abbrev levelEtale (i : E.system.I) :
    E.system.C i ⥤ AlgebraicGeometry.SmallEtale B (D.obj (stage E i)) (hD (stage E i)) :=
  (E.levelEquiv i).functor ⋙
    AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i)) (hD (stage E i))

/-- The transition morphism `X_i ⟶ X_j` of the system, read in the bounded category of the big
étale site. -/
def stageMap {i j : E.system.I} (a : i ⟶ j) :
    B.obj (D.obj (stage E i)) (hD (stage E i)) ⟶ B.obj (D.obj (stage E j)) (hD (stage E j)) :=
  B.inclusion.preimage
    (X := B.obj (D.obj (stage E i)) (hD (stage E i)))
    (Y := B.obj (D.obj (stage E j)) (hD (stage E j)))
    (D.map (E.indexEquiv.functor.map a))

/-- The image of the transition morphism in schemes is the transition morphism `D.map` of the
diagram. -/
@[simp]
theorem inclusion_map_stageMap {i j : E.system.I} (a : i ⟶ j) :
    B.inclusion.map (stageMap E a) = D.map (E.indexEquiv.functor.map a) :=
  B.inclusion.map_preimage _

/-- The transition morphism of an identity arrow is the identity. -/
@[simp]
theorem stageMap_id (i : E.system.I) : stageMap E (𝟙 i) = 𝟙 _ := by
  refine B.inclusion.map_injective ?_
  rw [inclusion_map_stageMap, E.indexEquiv.functor.map_id, D.map_id,
    B.inclusion.map_id]
  rfl

/-- The transition morphisms compose. -/
@[simp]
theorem stageMap_comp {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    stageMap E (a ≫ b) = stageMap E a ≫ stageMap E b := by
  refine B.inclusion.map_injective ?_
  rw [inclusion_map_stageMap, B.inclusion.map_comp, inclusion_map_stageMap,
    inclusion_map_stageMap, E.indexEquiv.functor.map_comp, D.map_comp]

section Transition

variable {i j : E.system.I}

/-- The base-change square of the transition morphism, read in schemes. -/
theorem baseChange_isPullback (a : i ⟶ j) (Y : E.system.C j) :
    IsPullback
      (B.inclusion.map (pullback.fst ((levelEtale E j).obj Y).obj.hom (stageMap E a)))
      (B.inclusion.map (pullback.snd ((levelEtale E j).obj Y).obj.hom (stageMap E a)))
      (B.inclusion.map ((levelEtale E j).obj Y).obj.hom)
      (D.map (E.indexEquiv.functor.map a)) := by
  rw [← inclusion_map_stageMap E a]
  exact Functor.map_isPullback B.inclusion (IsPullback.of_hasPullback _ _)

/-- The comparison of the transition square with the base-change square, in schemes. -/
def schemeIso (a : i ⟶ j) (Y : E.system.C j) :
    B.inclusion.obj ((levelEtale E i).obj ((E.system.u a).obj Y)).obj.left ≅
      B.inclusion.obj (pullback ((levelEtale E j).obj Y).obj.hom (stageMap E a)) :=
  IsPullback.isoIsPullback _ _ (E.transition_isPullback a Y) (baseChange_isPullback E a Y)

/-- The comparison of the two fibre products, in the bounded category. -/
def boundedIso (a : i ⟶ j) (Y : E.system.C j) :
    ((levelEtale E i).obj ((E.system.u a).obj Y)).obj.left ≅
      pullback ((levelEtale E j).obj Y).obj.hom (stageMap E a) :=
  B.inclusion.preimageIso (schemeIso E a Y)

/-- The image of the comparison of the two fibre products in schemes is `schemeIso`. -/
theorem inclusion_map_boundedIso_hom (a : i ⟶ j) (Y : E.system.C j) :
    B.inclusion.map (boundedIso E a Y).hom = (schemeIso E a Y).hom :=
  B.inclusion.map_preimage _

/-- The comparison is compatible with the projection onto the object it is based from. -/
theorem boundedIso_hom_fst (a : i ⟶ j) (Y : E.system.C j) :
    B.inclusion.map ((boundedIso E a Y).hom ≫
        pullback.fst ((levelEtale E j).obj Y).obj.hom (stageMap E a)) =
      (E.transitionFst a).app Y := by
  rw [B.inclusion.map_comp, inclusion_map_boundedIso_hom]
  exact IsPullback.isoIsPullback_hom_fst _ _ (E.transition_isPullback a Y)
    (baseChange_isPullback E a Y)

/-- The comparison is compatible with the structure morphisms. -/
theorem boundedIso_hom_snd (a : i ⟶ j) (Y : E.system.C j) :
    (boundedIso E a Y).hom ≫ pullback.snd ((levelEtale E j).obj Y).obj.hom (stageMap E a) =
      ((levelEtale E i).obj ((E.system.u a).obj Y)).obj.hom := by
  refine B.inclusion.map_injective ?_
  rw [B.inclusion.map_comp, inclusion_map_boundedIso_hom]
  exact IsPullback.isoIsPullback_hom_snd _ _ (E.transition_isPullback a Y)
    (baseChange_isPullback E a Y)

/-- The comparison, as an isomorphism of the slice category over `X_i`. -/
def overIso (a : i ⟶ j) (Y : E.system.C j) :
    ((levelEtale E i).obj ((E.system.u a).obj Y)).obj ≅
      (Over.pullback (stageMap E a)).obj ((levelEtale E j).obj Y).obj :=
  Over.isoMk (boundedIso E a Y) (boundedIso_hom_snd E a Y)

/-- The comparison, as an isomorphism of the small étale site of `X_i`. -/
def componentIso (a : i ⟶ j) (Y : E.system.C j) :
    (levelEtale E i).obj ((E.system.u a).obj Y) ≅
      (AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).obj ((levelEtale E j).obj Y) :=
  Functor.preimageIso
    (AlgebraicGeometry.SmallEtale.inclusion B (D.obj (stage E i)) (hD (stage E i)))
    (overIso E a Y)

/-- The functor from the small étale site of `X_i` to schemes. -/
abbrev toS (i : E.system.I) :
    AlgebraicGeometry.SmallEtale B (D.obj (stage E i)) (hD (stage E i)) ⥤ Scheme.{max u v} :=
  AlgebraicGeometry.SmallEtale.toScheme B (D.obj (stage E i)) (hD (stage E i))

/-- The projection of the base change of an object of the level `j` onto that object, in
schemes. -/
abbrev fstProj {i j : E.system.I} (a : i ⟶ j) (Y : E.system.C j) :
    B.inclusion.obj (pullback ((levelEtale E j).obj Y).obj.hom (stageMap E a)) ⟶
      (toS E j).obj ((levelEtale E j).obj Y) :=
  B.inclusion.map (pullback.fst ((levelEtale E j).obj Y).obj.hom (stageMap E a))

/-- The image of a component of the comparison in schemes is the comparison of the two
fibre-product squares. -/
theorem toS_map_componentIso_hom (a : i ⟶ j) (Y : E.system.C j) :
    (toS E i).map (componentIso E a Y).hom = (schemeIso E a Y).hom := by
  have h : (AlgebraicGeometry.SmallEtale.inclusion B (D.obj (stage E i))
      (hD (stage E i))).map (componentIso E a Y).hom = (overIso E a Y).hom :=
    Functor.map_preimage _ _
  have h2 : B.inclusion.map
      ((AlgebraicGeometry.SmallEtale.inclusion B (D.obj (stage E i))
        (hD (stage E i))).map (componentIso E a Y).hom).left =
      B.inclusion.map (overIso E a Y).hom.left :=
    congrArg (fun ψ => B.inclusion.map (Over.Hom.left ψ)) h
  exact h2.trans (inclusion_map_boundedIso_hom E a Y)

/-- **The comparison is the comparison of the two fibre-product squares, first projection.** The
component of the comparison at `Y`, followed by the projection of the fibre product onto `Y`, is
the projection `AffineEtaleSiteColimit.transitionFst` of the system. -/
theorem componentIso_hom_fst (a : i ⟶ j) (Y : E.system.C j) :
    (toS E i).map (componentIso E a Y).hom ≫ fstProj E a Y = (E.transitionFst a).app Y :=
  by
  rw [toS_map_componentIso_hom, ← inclusion_map_boundedIso_hom]
  exact (B.inclusion.map_comp _ _).symm.trans (boundedIso_hom_fst E a Y)

/-- **The comparison is the comparison of the two fibre-product squares, second projection.** The
component of the comparison at `Y`, followed by the projection of the fibre product onto `X_i`,
is the structure morphism of `(system.u a).obj Y`. -/
theorem componentIso_hom_snd (a : i ⟶ j) (Y : E.system.C j) :
    (toS E i).map (componentIso E a Y).hom ≫
        B.inclusion.map (pullback.snd ((levelEtale E j).obj Y).obj.hom (stageMap E a)) =
      B.inclusion.map ((levelEtale E i).obj ((E.system.u a).obj Y)).obj.hom :=
  by
  rw [toS_map_componentIso_hom, ← inclusion_map_boundedIso_hom]
  exact (B.inclusion.map_comp _ _).symm.trans (congrArg _ (boundedIso_hom_snd E a Y))

/-- Base change in a slice category is compatible with the projection onto the object based
from. -/
private theorem pullback_map_left_fst {C : Type*} [Category* C] [HasPullbacks C]
    {S T : C} (f : T ⟶ S) {Z Z' : Over S} (ψ : Z ⟶ Z') :
    ((Over.pullback f).map ψ).left ≫ pullback.fst Z'.hom f =
      pullback.fst Z.hom f ≫ ψ.left := by
  simp only [Over.pullback]
  exact pullback.lift_fst _ _ _

include E in
omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The projection onto the object based from is natural: base change of a morphism of the level
`j`, followed by that projection, is the projection followed by the morphism. -/
theorem fstProj_naturality (a : i ⟶ j) {Y Y' : E.system.C j} (φ : Y ⟶ Y') :
    (toS E i).map ((levelEtale E j ⋙
          AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map φ) ≫ fstProj E a Y' =
      fstProj E a Y ≫ (toS E j).map ((levelEtale E j).map φ) := by
  have h := congrArg B.inclusion.map (pullback_map_left_fst (stageMap E a)
    ((AlgebraicGeometry.SmallEtale.inclusion B (D.obj (stage E j))
      (hD (stage E j))).map ((levelEtale E j).map φ)))
  rw [B.inclusion.map_comp, B.inclusion.map_comp] at h
  exact h

include E in
omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **Two morphisms into a base change agree as soon as they agree on the projection onto the
object based from.** The transition instance of
`AlgebraicGeometry.SmallEtale.hom_ext_fst`. -/
theorem hom_ext_fst (a : i ⟶ j)
    {Z' : AlgebraicGeometry.SmallEtale B (D.obj (stage E j)) (hD (stage E j))}
    {W : AlgebraicGeometry.SmallEtale B (D.obj (stage E i)) (hD (stage E i))}
    (α β : W ⟶ (AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).obj Z')
    (h : (toS E i).map α ≫ B.inclusion.map (pullback.fst Z'.obj.hom (stageMap E a)) =
        (toS E i).map β ≫ B.inclusion.map (pullback.fst Z'.obj.hom (stageMap E a))) :
    α = β :=
  AlgebraicGeometry.SmallEtale.hom_ext_fst (stageMap E a) α β h

/-- **The transition functor of the site system of Stacks 0EYL is étale base change.** For an
arrow `a : i ⟶ j` of the index category of the system, the transition functor
`system.u a : C j ⥤ C i`, read into the small étale site of `X_i`, is base change along the
transition morphism `X_i ⟶ X_j` applied to the reading of `C j` into the small étale site of
`X_j`.

The component at `Y` is the comparison of the fibre-product square
`AffineEtaleSiteColimit.transition_isPullback` with the base-change square, characterised by
`componentIso_hom_fst` and `componentIso_hom_snd`. -/
def transitionIso (a : i ⟶ j) :
    E.system.u a ⋙ levelEtale E i ≅
      levelEtale E j ⋙ AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a) :=
  NatIso.ofComponents (fun Y => componentIso E a Y) <| by
    intro Y Y' φ
    refine hom_ext_fst E a _ _ ?_
    calc (toS E i).map ((E.system.u a ⋙ levelEtale E i).map φ ≫ (componentIso E a Y').hom) ≫
          fstProj E a Y'
        = ((toS E i).map ((E.system.u a ⋙ levelEtale E i).map φ) ≫
            (toS E i).map (componentIso E a Y').hom) ≫ fstProj E a Y' := by
          rw [Functor.map_comp]
      _ = (toS E i).map ((E.system.u a ⋙ levelEtale E i).map φ) ≫
            ((toS E i).map (componentIso E a Y').hom ≫ fstProj E a Y') := Category.assoc _ _ _
      _ = (toS E i).map ((E.system.u a ⋙ levelEtale E i).map φ) ≫
            (E.transitionFst a).app Y' :=
          congrArg (fun ψ => (toS E i).map ((E.system.u a ⋙ levelEtale E i).map φ) ≫ ψ)
            (componentIso_hom_fst E a Y')
      _ = (E.transitionFst a).app Y ≫ (toS E j).map ((levelEtale E j).map φ) :=
          (E.transitionFst a).naturality φ
      _ = ((toS E i).map (componentIso E a Y).hom ≫ fstProj E a Y) ≫
            (toS E j).map ((levelEtale E j).map φ) :=
          congrArg (fun ψ => ψ ≫ (toS E j).map ((levelEtale E j).map φ))
            (componentIso_hom_fst E a Y).symm
      _ = (toS E i).map (componentIso E a Y).hom ≫
            (fstProj E a Y ≫ (toS E j).map ((levelEtale E j).map φ)) := Category.assoc _ _ _
      _ = (toS E i).map (componentIso E a Y).hom ≫
            ((toS E i).map ((levelEtale E j ⋙
              AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map φ) ≫
              fstProj E a Y') :=
          congrArg (fun ψ => (toS E i).map (componentIso E a Y).hom ≫ ψ)
            (fstProj_naturality E a φ).symm
      _ = ((toS E i).map (componentIso E a Y).hom ≫ (toS E i).map ((levelEtale E j ⋙
            AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map φ)) ≫
            fstProj E a Y' := (Category.assoc _ _ _).symm
      _ = (toS E i).map ((componentIso E a Y).hom ≫ (levelEtale E j ⋙
            AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map φ) ≫
            fstProj E a Y' := by rw [Functor.map_comp]

/-- The component of `transitionIso` at `Y` is `componentIso`. -/
theorem transitionIso_hom_app (a : i ⟶ j) (Y : E.system.C j) :
    (transitionIso E a).hom.app Y = (componentIso E a Y).hom := rfl

end Transition

end Stacks.EtaleCohomology.TransitionBaseChange

end
