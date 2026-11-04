module

public import StacksFrontier.AlgebraicGeometry.Equivalence.PuncturedStage

/-!
# The punctured system of affine open neighbourhoods, read in the ambient scheme

Let `S` be a scheme, `V` an open of it, `x` a point and `W₀` an affine open neighbourhood of `x`.
`AlgebraicGeometry.opensDiagram` presents the inverse system whose stage at `j : Over W₀` is the
preimage of `V` in the smaller neighbourhood `W_j`, and
`AlgebraicGeometry.isLimitOpensSpecStalkCone` says that its limit is the preimage of `V` in
`Spec 𝒪_{S, x}`.  Every one of those stages is an *open of `W_j`*, not an open of `S`, and the
limit is the apex `π_{W₀}⁻¹(W₀ ∩ V)`, not the open `S.fromSpecStalk x ⁻¹ᵁ V` that the consumer
names.  This file identifies both with the opens of `S` that the statement of
[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) speaks about: the stage at `j` with
`V ⊓ W_j`, and the apex with the punctured local scheme.

## Why the identification is needed at all

Tag 0E8Q's gluing engine
(`AlgebraicGeometry.exists_finitePresentation_isPullback_glueAvoiding`) takes its overlap
isomorphism over `V ⊓ W` with `V ⊓ W` an open of `S`, and its charts over an open `W` of `S`.  The
descent that produces that isomorphism runs over the system above, whose stages are opens of
`W_j`.  The two are isomorphic but not equal, so the comparison has to be written down once, with
its compatibility with the inclusions into `S`, its naturality in the stage, and its
compatibility with the legs of the limit cone.  Those four facts are this file.

## Main definitions

* `AlgebraicGeometry.puncturedNhdsDiagram`: the punctured system, named.
* `AlgebraicGeometry.puncturedNhdsStageIso`: the stage at `j` is `V ⊓ W_j`.
* `AlgebraicGeometry.puncturedNhdsApexIso`: the apex of Mathlib's limit cone is the punctured
  local scheme `S.fromSpecStalk x ⁻¹ᵁ V`.
* `AlgebraicGeometry.puncturedNhdsLeg`: the leg of that cone, read as a morphism from the
  punctured local scheme to `V ⊓ W_j`.

## Main results

* `AlgebraicGeometry.puncturedNhdsStageIso_hom_ι`: the identification commutes with the
  inclusions into `S`.
* `AlgebraicGeometry.puncturedNhdsDiagram_map_comp_stageIso`: it is natural in the stage.
* `AlgebraicGeometry.opensCone_π_comp_stageIso`: it carries the legs of Mathlib's limit cone to
  the legs above.
* `AlgebraicGeometry.puncturedNhdsLeg_comp_homOfLE` and
  `AlgebraicGeometry.puncturedNhdsLeg_comp_homOfLE_right`: the leg, followed by the two
  inclusions of `V ⊓ W_j`, is the restriction of `AlgebraicGeometry.Scheme.fromSpecStalk` to `V`
  and the canonical map to `W_j` restricted to the punctured part.

## Implementation notes

The identification is Mathlib's `AlgebraicGeometry.Scheme.Hom.isoImage` for the inclusion of
`W_j`, followed by `AlgebraicGeometry.Scheme.isoOfEq`; it is *not* built as an
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` of the composite inclusion, because instance
search does not find `IsOpenImmersion` for that composite: the middle object is
`(AlgebraicGeometry.affineOpenNhdsDiagram S x).obj j.left`, and identifying it with the open
subscheme `W_j` needs `affineOpenNhdsDiagram` to be unfolded, which does not happen at instance
transparency.  Routing through `isoImage`, whose open immersion is the explicit
`AlgebraicGeometry.Scheme.Opens.ι`, removes the question.

Every equation below is proved by cancelling the monomorphism `(V ⊓ W_j).ι`, so that each side
becomes a composite of inclusions into `S` and the `AlgebraicGeometry.opensDiagram` and
`AlgebraicGeometry.opensCone` equations of
`StacksFrontier.AlgebraicGeometry.Equivalence.PuncturedStage` apply directly.  The
cancelled equations are then chained with `Eq.trans` rather than with `rw` or `simp`: the stage
is the open subscheme of `(AlgebraicGeometry.affineOpenNhdsDiagram S x).obj j.left`, which is
identified with the open subscheme `W_j` only after that functor is unfolded, so a keyed rewrite
whose pattern spans the two spellings reports a missing pattern that is present, while a term
built by `Eq.trans` is checked at default transparency and goes through.  The same boundary is
why no inverse system is assembled here out of the opens `V ⊓ W_j`: `IsAffineHom` of its
transitions is not synthesized across it, and the descent is therefore run against Mathlib's own
`AlgebraicGeometry.opensDiagram`, whose instances are all in place.

No `@[stacks]` attribute is attached: Tag 0E8Q's `equivalence` label has the single
`CategoryTheory.Functor.IsEquivalence` assertion as its covering set.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (V : S.Opens) (x : S)

/-- **A transition of the system of affine open neighbourhoods is the inclusion of the smaller
one**, for an arbitrary morphism of neighbourhoods rather than for the structure morphism of an
object of an over category. -/
theorem affineOpenNhdsDiagram_map_ι {W W' : AffineOpenNhds S x} (f : W ⟶ W') :
    (affineOpenNhdsDiagram S x).map f ≫ Scheme.Opens.ι (X := S) W'.obj.1 =
      Scheme.Opens.ι (X := S) W.obj.1 := by
  rw [affineOpenNhdsDiagram_map]
  exact S.homOfLE_ι _

variable (W₀ : AffineOpenNhds S x)

/-- The punctured system of affine open neighbourhoods of `x` inside `W₀`: the stage at `j` is
the preimage of `V` in the neighbourhood `j.left`. -/
noncomputable abbrev puncturedNhdsDiagram : Over W₀ ⥤ Scheme.{u} :=
  opensDiagram (affineOpenNhdsDiagram S x) W₀ (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ V)

/-- **A stage of the punctured system is the open `V ⊓ W_j` of the ambient scheme.**  The stage
is first identified with the preimage of `V` in `W_j` — which it is only propositionally, the
transition at the identity being `AlgebraicGeometry.Scheme.homOfLE` of a reflexive inequality
rather than the identity — and that preimage is then carried to its image in `S`. -/
noncomputable def puncturedNhdsStageIso (j : Over W₀) :
    (puncturedNhdsDiagram V x W₀).obj j ≅ ((V ⊓ j.left.obj.1 : S.Opens) : Scheme.{u}) :=
  (Scheme.Opens.toScheme (X := S) j.left.obj.1).isoOfEq
        (map_preimage_affineOpenNhds V x W₀ j) ≪≫
      (Scheme.Opens.ι (X := S) j.left.obj.1).isoImage
        (Scheme.Opens.ι (X := S) j.left.obj.1 ⁻¹ᵁ V) ≪≫
    S.isoOfEq (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm])

/-- **The identification of a stage with `V ⊓ W_j` commutes with the inclusions into `S`.** -/
theorem puncturedNhdsStageIso_hom_ι (j : Over W₀) :
    (puncturedNhdsStageIso V x W₀ j).hom ≫ (V ⊓ j.left.obj.1 : S.Opens).ι =
      Scheme.Opens.ι ((affineOpenNhdsDiagram S x).map j.hom ⁻¹ᵁ
          (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ V)) ≫
        Scheme.Opens.ι (X := S) j.left.obj.1 := by
  refine Eq.trans (Iso.trans_hom _ _ =≫ _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (_ ≫= (Iso.trans_hom _ _ =≫ _)) ?_
  refine Eq.trans (_ ≫= Category.assoc _ _ _) ?_
  refine Eq.trans (_ ≫= (_ ≫= Scheme.isoOfEq_hom_ι _ _)) ?_
  refine Eq.trans (_ ≫= Scheme.Hom.isoImage_hom_ι _ _) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact Scheme.isoOfEq_hom_ι _ _ =≫ _

/-- A morphism into a stage followed by the stage identification equals `g` once both are
compared in `S`. -/
private theorem comp_stageIso_hom_eq_of_comp_ι {W₀ : AffineOpenNhds S x} {j : Over W₀}
    {Y : Scheme.{u}} (f : Y ⟶ (puncturedNhdsDiagram V x W₀).obj j)
    (g : Y ⟶ ((V ⊓ j.left.obj.1 : S.Opens) : Scheme.{u}))
    (h : (f ≫ Scheme.Opens.ι ((affineOpenNhdsDiagram S x).map j.hom ⁻¹ᵁ
          (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ V))) ≫ Scheme.Opens.ι (X := S) j.left.obj.1 =
        g ≫ (V ⊓ j.left.obj.1 : S.Opens).ι) :
    f ≫ (puncturedNhdsStageIso V x W₀ j).hom = g := by
  refine (cancel_mono (V ⊓ j.left.obj.1 : S.Opens).ι).mp ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (_ ≫= puncturedNhdsStageIso_hom_ι V x W₀ j) ?_
  exact Eq.trans (Category.assoc _ _ _).symm h

/-- **The identification of the stages is natural**: it carries a transition of the punctured
system to the inclusion `V ⊓ W_j ≤ V ⊓ W_k`. -/
theorem puncturedNhdsDiagram_map_comp_stageIso {j k : Over W₀} (e : j ⟶ k) :
    (puncturedNhdsDiagram V x W₀).map e ≫ (puncturedNhdsStageIso V x W₀ k).hom =
      (puncturedNhdsStageIso V x W₀ j).hom ≫
        S.homOfLE (inf_le_inf_left V
          (show j.left.obj.1 ≤ k.left.obj.1 from
            leOfHom ((affineOpenNhds S x).ι.map e.left))) := by
  refine comp_stageIso_hom_eq_of_comp_ι V x _ _ ?_
  refine Eq.trans (opensDiagram_map_comp_ι _ _ _ e =≫ _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (_ ≫= affineOpenNhdsDiagram_map_ι x e.left) ?_
  refine Eq.symm (Eq.trans (Category.assoc _ _ _) ?_)
  refine Eq.trans (_ ≫= Scheme.homOfLE_ι S _) ?_
  exact puncturedNhdsStageIso_hom_ι V x W₀ j

/-- The whole local scheme lies over any neighbourhood of the point: `Spec 𝒪_{S, x} ⟶ S`
factors through every open containing `x`, so the preimage of such an open is everything.
No hypothesis on `x` is needed; `AlgebraicGeometry.fromSpecStalk_preimage_eq_top` is the same
conclusion asked only at a generic point. -/
theorem fromSpecStalk_preimage_eq_top' {W : S.Opens} (hxW : x ∈ W) :
    S.fromSpecStalk x ⁻¹ᵁ W = ⊤ := by
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι W x hxW, Scheme.Hom.comp_preimage,
    Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

/-- For an open `W` containing `x`, the preimage of `V` under `Spec 𝒪_{S, x} ⟶ S` is contained
in the preimage of `V ⊓ W`. -/
theorem fromSpecStalk_preimage_le {W : S.Opens} (hxW : x ∈ W) :
    S.fromSpecStalk x ⁻¹ᵁ V ≤ S.fromSpecStalk x ⁻¹ᵁ (V ⊓ W) := by
  rw [Scheme.Hom.preimage_inf, fromSpecStalk_preimage_eq_top' x hxW]
  exact le_inf le_rfl le_top

/-- The leg of the limit cone at the stage `j`, read as a morphism from the punctured local
scheme to `V ⊓ W_j`. -/
noncomputable def puncturedNhdsLeg (j : Over W₀) :
    ((S.fromSpecStalk x ⁻¹ᵁ V : (Spec (S.presheaf.stalk x)).Opens) : Scheme.{u}) ⟶
      ((V ⊓ j.left.obj.1 : S.Opens) : Scheme.{u}) :=
  (S.fromSpecStalk x).resLE (V ⊓ j.left.obj.1) (S.fromSpecStalk x ⁻¹ᵁ V)
    (fromSpecStalk_preimage_le V x j.left.obj.2)

/-- **The leg, followed by the inclusion of `V ⊓ W_j` into `V`, is the restriction of
`AlgebraicGeometry.Scheme.fromSpecStalk` to `V`.** -/
theorem puncturedNhdsLeg_comp_homOfLE (j : Over W₀) :
    puncturedNhdsLeg V x W₀ j ≫ S.homOfLE (inf_le_left : V ⊓ j.left.obj.1 ≤ V) =
      S.fromSpecStalk x ∣_ V := by
  rw [puncturedNhdsLeg, Scheme.Hom.resLE_map, Scheme.Hom.resLE_eq_morphismRestrict]

/-- **The leg, followed by the inclusion of `V ⊓ W_j` into `W_j`, is the canonical map from the
local scheme to the neighbourhood, restricted to the punctured part.** -/
theorem puncturedNhdsLeg_comp_homOfLE_right (j : Over W₀) :
    puncturedNhdsLeg V x W₀ j ≫
        S.homOfLE (inf_le_right : V ⊓ j.left.obj.1 ≤ j.left.obj.1) =
      (S.fromSpecStalk x ⁻¹ᵁ V : (Spec (S.presheaf.stalk x)).Opens).ι ≫
        Scheme.Opens.fromSpecStalkOfMem (X := S) j.left.obj.1 x j.left.obj.2 := by
  refine (cancel_mono (Scheme.Opens.ι (X := S) j.left.obj.1)).mp ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (_ ≫= Scheme.homOfLE_ι S _) ?_
  refine Eq.trans (Scheme.Hom.resLE_comp_ι _ _) ?_
  refine Eq.symm (Eq.trans (Category.assoc _ _ _) ?_)
  exact _ ≫= Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

/-- **The apex of the limit cone of the punctured system is the punctured local scheme.** -/
noncomputable def puncturedNhdsApexIso :
    (opensCone (affineOpenNhdsDiagram S x) (specStalkCone S x) W₀
        (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ V)).pt ≅
      ((S.fromSpecStalk x ⁻¹ᵁ V : (Spec (S.presheaf.stalk x)).Opens) : Scheme.{u}) :=
  (specStalkCone S x).pt.isoOfEq (specStalkCone_π_preimage S x W₀ V)

/-- **The identification of the stages carries the legs of Mathlib's limit cone to the legs
above.** -/
theorem opensCone_π_comp_stageIso (j : Over W₀) :
    (opensCone (affineOpenNhdsDiagram S x) (specStalkCone S x) W₀
          (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ V)).π.app j ≫
        (puncturedNhdsStageIso V x W₀ j).hom =
      (puncturedNhdsApexIso V x W₀).hom ≫ puncturedNhdsLeg V x W₀ j := by
  refine comp_stageIso_hom_eq_of_comp_ι V x _ _ ?_
  refine Eq.trans (opensCone_π_comp_ι _ _ _ _ j =≫ _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (_ ≫= Scheme.Opens.fromSpecStalkOfMem_ι _ _ _) ?_
  refine Eq.symm (Eq.trans (Category.assoc _ _ _) ?_)
  refine Eq.trans (_ ≫= Scheme.Hom.resLE_comp_ι _ _) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact Scheme.isoOfEq_hom_ι _ _ =≫ _

end AlgebraicGeometry

end
