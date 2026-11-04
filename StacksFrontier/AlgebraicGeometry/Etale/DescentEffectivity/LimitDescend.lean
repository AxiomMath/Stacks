module

public import StacksFrontier.AlgebraicGeometry.EssSurj.IsoDescentCompat
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.LimitPasting
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.PullbackSquare
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# Reindexing base changes along the fibre products of a limit of schemes

Let `f : X ⟶ S` be the limit of a cofiltered system of morphisms `f_i : X_i ⟶ S_i` of schemes.
For an object `W` over a stage `X_i`, base changing `W` along a projection of `X_i ×_{S_i} X_i` (or
of the triple fibre product) and then along a cone leg or a transition morphism is isomorphic to
base changing it in the other order. This file constructs these isomorphisms and computes their
first projections.

## Main definitions

* `AlgebraicGeometry.LimitDatum.sqLegFstIso`, `sqLegSndIso`, `sqMapFstIso`, `sqMapSndIso`,
  `triLegFstIso`, `triLegThdIso`, `triMapFstIso`, `triMapThdIso`: the reindexing isomorphisms
  that say base changing a stage object along a projection and then along a cone leg or a
  transition morphism is base changing it in the other order.

## Main results

* `AlgebraicGeometry.overPullback_hom_ext`: a morphism into a base change in an over category is
  determined by its first projection.
* `AlgebraicGeometry.overPullbackCompIso_trans_symm_hom_left_fst`: the first projection of a
  reindexing isomorphism between two iterated base changes along the same composite.
* `AlgebraicGeometry.LimitDatum.sqLegFstIso_hom_left_fst` and the seven analogous lemmas: the
  first projections of the eight reindexing isomorphisms.

## References

* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-! ### Two generalities about base change in an over category -/

/-- **A morphism into a base change is determined by its first projection.** The second
projection of such a morphism is its structure morphism, so the first is all that is free. -/
lemma overPullback_hom_ext {T S' : Scheme.{u}} {r : S' ⟶ T} {W : Over T} {A : Over S'}
    {m n : A ⟶ (Over.pullback r).obj W}
    (h : m.left ≫ pullback.fst W.hom r = n.left ≫ pullback.fst W.hom r) : m = n := by
  apply Over.OverMorphism.ext
  refine pullback.hom_ext h ?_
  simpa only [Over.pullback_obj_hom] using (Over.w m).trans (Over.w n).symm

/-- **The first projection of a reindexing isomorphism between two iterated base changes along
the same composite.** -/
lemma overPullbackCompIso_trans_symm_hom_left_fst {S₁ S₂ S₃ T : Scheme.{u}} (p₁ : S₁ ⟶ T)
    (q₁ : S₃ ⟶ S₁) (p₂ : S₂ ⟶ T) (q₂ : S₃ ⟶ S₂) (r : S₃ ⟶ T) (h₁ : q₁ ≫ p₁ = r)
    (h₂ : q₂ ≫ p₂ = r) (W : Over T) :
    (overPullbackCompIso p₁ q₁ r h₁ W ≪≫
          (overPullbackCompIso p₂ q₂ r h₂ W).symm).hom.left ≫
        pullback.fst ((Over.pullback p₂).obj W).hom q₂ ≫ pullback.fst W.hom p₂ =
      pullback.fst ((Over.pullback p₁).obj W).hom q₁ ≫ pullback.fst W.hom p₁ := by
  rw [Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc,
    overPullbackCompIso_inv_fst, overPullbackCompIso_fst]

namespace LimitDatum

variable {I : Type u} [Category.{u} I] {𝒳 𝒮 : I ⥤ Scheme.{u}} (φ : 𝒳 ⟶ 𝒮)
  {cX : Cone 𝒳} {cS : Cone 𝒮} (f : cX.pt ⟶ cS.pt)
  (hf : ∀ i, cX.π.app i ≫ φ.app i = f ≫ cS.π.app i)

/-! ### Reindexing along the double fibre product -/

include hf in
/-- Base changing a stage object along the first projection and then to `X ×_S X` is base
changing it to `X` and then along the first projection. -/
def sqLegFstIso (i : I) (W : Over (𝒳.obj i)) :
    (Over.pullback ((sqCone φ f hf).π.app i)).obj
        ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj W) ≅
      (Over.pullback (pullback.fst f f)).obj ((Over.pullback (cX.π.app i)).obj W) :=
  overPullbackCompIso _ _ _ (FibreProductLimit.cone_π_app_fst φ φ f f hf hf i) W ≪≫
    (overPullbackCompIso (cX.π.app i) (pullback.fst f f) _ rfl W).symm

include hf in
/-- Base changing a stage object along the second projection and then to `X ×_S X` is base
changing it to `X` and then along the second projection. -/
def sqLegSndIso (i : I) (W : Over (𝒳.obj i)) :
    (Over.pullback ((sqCone φ f hf).π.app i)).obj
        ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj W) ≅
      (Over.pullback (pullback.snd f f)).obj ((Over.pullback (cX.π.app i)).obj W) :=
  overPullbackCompIso _ _ _ (FibreProductLimit.cone_π_app_snd φ φ f f hf hf i) W ≪≫
    (overPullbackCompIso (cX.π.app i) (pullback.snd f f) _ rfl W).symm

/-- Base changing a stage object along the first projection and then along a transition
morphism of the double fibre products is base changing it along the transition morphism and
then along the first projection. -/
def sqMapFstIso {i j : I} (e : j ⟶ i) (W : Over (𝒳.obj i)) :
    (Over.pullback ((sqDiagram φ).map e)).obj
        ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj W) ≅
      (Over.pullback (pullback.fst (φ.app j) (φ.app j))).obj
        ((Over.pullback (𝒳.map e)).obj W) :=
  overPullbackCompIso _ _ _ (FibreProductLimit.diagram_map_fst φ φ e) W ≪≫
    (overPullbackCompIso (𝒳.map e) (pullback.fst (φ.app j) (φ.app j)) _ rfl W).symm

/-- Base changing a stage object along the second projection and then along a transition
morphism of the double fibre products is base changing it along the transition morphism and
then along the second projection. -/
def sqMapSndIso {i j : I} (e : j ⟶ i) (W : Over (𝒳.obj i)) :
    (Over.pullback ((sqDiagram φ).map e)).obj
        ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj W) ≅
      (Over.pullback (pullback.snd (φ.app j) (φ.app j))).obj
        ((Over.pullback (𝒳.map e)).obj W) :=
  overPullbackCompIso _ _ _ (FibreProductLimit.diagram_map_snd φ φ e) W ≪≫
    (overPullbackCompIso (𝒳.map e) (pullback.snd (φ.app j) (φ.app j)) _ rfl W).symm

/-- **The reindexing of an isomorphism of the two base changes of a stage object to a later
stage.** -/
abbrev sqReindexIso {i j : I} (m : j ⟶ i) (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V) :
    (Over.pullback (pullback.fst (φ.app j) (φ.app j))).obj ((Over.pullback (𝒳.map m)).obj V) ≅
      (Over.pullback (pullback.snd (φ.app j) (φ.app j))).obj
        ((Over.pullback (𝒳.map m)).obj V) :=
  (sqMapFstIso φ m V).symm ≪≫ (Over.pullback ((sqDiagram φ).map m)).mapIso ψ ≪≫
    sqMapSndIso φ m V

/-! ### Reindexing along the triple fibre product -/

/-- Precomposing the cone leg of the triple fibre product with its first projection. -/
private theorem triCone_π_comp_fst_comp {Z : Scheme.{u}} (i : I)
    (k : pullback (φ.app i) (φ.app i) ⟶ Z) :
    (triCone φ f hf).π.app i ≫ pullback.fst ((sqToBase φ).app i) (φ.app i) ≫ k =
      pullback.fst (sqToBaseLimit φ f hf) f ≫ (sqCone φ f hf).π.app i ≫ k := by
  rw [← Category.assoc,
    FibreProductLimit.cone_π_app_fst (sqToBase φ) φ (sqToBaseLimit φ f hf) f
      (sqCone_π_comp_sqToBase φ f hf) hf i, Category.assoc]

include hf in
/-- The first projection of the triple fibre product commutes with the legs of the two limit
cones. -/
theorem triCone_π_comp_tripleBaseFst (i : I) :
    (triCone φ f hf).π.app i ≫ DescentDatum.tripleBaseFst (φ.app i) =
      DescentDatum.tripleBaseFst f ≫ cX.π.app i := by
  refine (triCone_π_comp_fst_comp φ f hf i _).trans ?_
  rw [FibreProductLimit.cone_π_app_fst φ φ f f hf hf i]
  rfl

include hf in
/-- The second projection of the triple fibre product commutes with the legs of the two limit
cones. -/
theorem triCone_π_comp_tripleBaseSnd (i : I) :
    (triCone φ f hf).π.app i ≫ DescentDatum.tripleBaseSnd (φ.app i) =
      DescentDatum.tripleBaseSnd f ≫ cX.π.app i := by
  refine (triCone_π_comp_fst_comp φ f hf i _).trans ?_
  rw [FibreProductLimit.cone_π_app_snd φ φ f f hf hf i]
  rfl

include hf in
/-- The third projection of the triple fibre product commutes with the legs of the two limit
cones. -/
theorem triCone_π_comp_tripleBaseThd (i : I) :
    (triCone φ f hf).π.app i ≫ DescentDatum.tripleBaseThd (φ.app i) =
      DescentDatum.tripleBaseThd f ≫ cX.π.app i :=
  FibreProductLimit.cone_π_app_snd (sqToBase φ) φ (sqToBaseLimit φ f hf) f
    (sqCone_π_comp_sqToBase φ f hf) hf i

/-- Precomposing a transition morphism of the triple fibre products with the first projection. -/
private theorem triDiagram_map_comp_fst_comp {Z : Scheme.{u}} {i j : I} (e : j ⟶ i)
    (k : pullback (φ.app i) (φ.app i) ⟶ Z) :
    (triDiagram φ).map e ≫ pullback.fst ((sqToBase φ).app i) (φ.app i) ≫ k =
      pullback.fst ((sqToBase φ).app j) (φ.app j) ≫ (sqDiagram φ).map e ≫ k := by
  rw [← Category.assoc, FibreProductLimit.diagram_map_fst (sqToBase φ) φ e, Category.assoc]

/-- The first projection of the triple fibre product commutes with the transition
morphisms. -/
theorem triDiagram_map_comp_tripleBaseFst {i j : I} (e : j ⟶ i) :
    (triDiagram φ).map e ≫ DescentDatum.tripleBaseFst (φ.app i) =
      DescentDatum.tripleBaseFst (φ.app j) ≫ 𝒳.map e := by
  refine (triDiagram_map_comp_fst_comp φ e _).trans ?_
  rw [FibreProductLimit.diagram_map_fst φ φ e]
  rfl

/-- The second projection of the triple fibre product commutes with the transition
morphisms. -/
theorem triDiagram_map_comp_tripleBaseSnd {i j : I} (e : j ⟶ i) :
    (triDiagram φ).map e ≫ DescentDatum.tripleBaseSnd (φ.app i) =
      DescentDatum.tripleBaseSnd (φ.app j) ≫ 𝒳.map e := by
  refine (triDiagram_map_comp_fst_comp φ e _).trans ?_
  rw [FibreProductLimit.diagram_map_snd φ φ e]
  rfl

/-- The third projection of the triple fibre product commutes with the transition
morphisms. -/
theorem triDiagram_map_comp_tripleBaseThd {i j : I} (e : j ⟶ i) :
    (triDiagram φ).map e ≫ DescentDatum.tripleBaseThd (φ.app i) =
      DescentDatum.tripleBaseThd (φ.app j) ≫ 𝒳.map e :=
  FibreProductLimit.diagram_map_snd (sqToBase φ) φ e

include hf in
/-- Base changing a stage object along the first projection of the triple fibre product and
then to the limit is base changing it to `X` and then along the first projection. -/
def triLegFstIso (i : I) (W : Over (𝒳.obj i)) :
    (Over.pullback ((triCone φ f hf).π.app i)).obj
        ((Over.pullback (DescentDatum.tripleBaseFst (φ.app i))).obj W) ≅
      (Over.pullback (DescentDatum.tripleBaseFst f)).obj
        ((Over.pullback (cX.π.app i)).obj W) :=
  overPullbackCompIso _ _ _ (triCone_π_comp_tripleBaseFst φ f hf i) W ≪≫
    (overPullbackCompIso (cX.π.app i) (DescentDatum.tripleBaseFst f) _ rfl W).symm

include hf in
/-- Base changing a stage object along the third projection of the triple fibre product and
then to the limit is base changing it to `X` and then along the third projection. -/
def triLegThdIso (i : I) (W : Over (𝒳.obj i)) :
    (Over.pullback ((triCone φ f hf).π.app i)).obj
        ((Over.pullback (DescentDatum.tripleBaseThd (φ.app i))).obj W) ≅
      (Over.pullback (DescentDatum.tripleBaseThd f)).obj
        ((Over.pullback (cX.π.app i)).obj W) :=
  overPullbackCompIso _ _ _ (triCone_π_comp_tripleBaseThd φ f hf i) W ≪≫
    (overPullbackCompIso (cX.π.app i) (DescentDatum.tripleBaseThd f) _ rfl W).symm

/-- Base changing a stage object along the first projection of the triple fibre product and
then along a transition morphism, in the other order. -/
def triMapFstIso {i j : I} (e : j ⟶ i) (W : Over (𝒳.obj i)) :
    (Over.pullback ((triDiagram φ).map e)).obj
        ((Over.pullback (DescentDatum.tripleBaseFst (φ.app i))).obj W) ≅
      (Over.pullback (DescentDatum.tripleBaseFst (φ.app j))).obj
        ((Over.pullback (𝒳.map e)).obj W) :=
  overPullbackCompIso _ _ _ (triDiagram_map_comp_tripleBaseFst φ e) W ≪≫
    (overPullbackCompIso (𝒳.map e) (DescentDatum.tripleBaseFst (φ.app j)) _ rfl W).symm

/-- Base changing a stage object along the third projection of the triple fibre product and
then along a transition morphism, in the other order. -/
def triMapThdIso {i j : I} (e : j ⟶ i) (W : Over (𝒳.obj i)) :
    (Over.pullback ((triDiagram φ).map e)).obj
        ((Over.pullback (DescentDatum.tripleBaseThd (φ.app i))).obj W) ≅
      (Over.pullback (DescentDatum.tripleBaseThd (φ.app j))).obj
        ((Over.pullback (𝒳.map e)).obj W) :=
  overPullbackCompIso _ _ _ (triDiagram_map_comp_tripleBaseThd φ e) W ≪≫
    (overPullbackCompIso (𝒳.map e) (DescentDatum.tripleBaseThd (φ.app j)) _ rfl W).symm

/-! ### The first projections of the eight reindexing isomorphisms

Each of the eight isomorphisms above is a composite of two comparisons between an iterated base
change and a direct one, so its first projection is the composite of pullback projections given
by `AlgebraicGeometry.overPullbackCompIso_trans_symm_hom_left_fst`. -/

include hf in
/-- The first projection of `sqLegFstIso`, followed by the first projection to `W`, is the first
projection of the base change of `W` along the first projection of the double fibre product and
along the cone leg, followed by the first projection to `W`. -/
lemma sqLegFstIso_hom_left_fst (i : I) (W : Over (𝒳.obj i)) :
    (sqLegFstIso φ f hf i W).hom.left ≫
        pullback.fst ((Over.pullback (cX.π.app i)).obj W).hom (pullback.fst f f) ≫
          pullback.fst W.hom (cX.π.app i) =
      pullback.fst ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj W).hom
          ((sqCone φ f hf).π.app i) ≫ pullback.fst W.hom (pullback.fst (φ.app i) (φ.app i)) :=
  overPullbackCompIso_trans_symm_hom_left_fst _ _ _ _ _ _ _ W

include hf in
/-- The first projection of `sqLegSndIso`, followed by the first projection to `W`, is the first
projection of the base change of `W` along the second projection of the double fibre product and
along the cone leg, followed by the first projection to `W`. -/
lemma sqLegSndIso_hom_left_fst (i : I) (W : Over (𝒳.obj i)) :
    (sqLegSndIso φ f hf i W).hom.left ≫
        pullback.fst ((Over.pullback (cX.π.app i)).obj W).hom (pullback.snd f f) ≫
          pullback.fst W.hom (cX.π.app i) =
      pullback.fst ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj W).hom
          ((sqCone φ f hf).π.app i) ≫ pullback.fst W.hom (pullback.snd (φ.app i) (φ.app i)) :=
  overPullbackCompIso_trans_symm_hom_left_fst _ _ _ _ _ _ _ W

/-- The first projection of `sqMapFstIso`, followed by the first projection to `W`, is the first
projection of the base change of `W` along the first projection of the double fibre product and
along the transition morphism, followed by the first projection to `W`. -/
lemma sqMapFstIso_hom_left_fst {i j : I} (e : j ⟶ i) (W : Over (𝒳.obj i)) :
    (sqMapFstIso φ e W).hom.left ≫
        pullback.fst ((Over.pullback (𝒳.map e)).obj W).hom
            (pullback.fst (φ.app j) (φ.app j)) ≫
          pullback.fst W.hom (𝒳.map e) =
      pullback.fst ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj W).hom
          ((sqDiagram φ).map e) ≫ pullback.fst W.hom (pullback.fst (φ.app i) (φ.app i)) :=
  overPullbackCompIso_trans_symm_hom_left_fst _ _ _ _ _ _ _ W

/-- The first projection of `sqMapSndIso`, followed by the first projection to `W`, is the first
projection of the base change of `W` along the second projection of the double fibre product and
along the transition morphism, followed by the first projection to `W`. -/
lemma sqMapSndIso_hom_left_fst {i j : I} (e : j ⟶ i) (W : Over (𝒳.obj i)) :
    (sqMapSndIso φ e W).hom.left ≫
        pullback.fst ((Over.pullback (𝒳.map e)).obj W).hom
            (pullback.snd (φ.app j) (φ.app j)) ≫
          pullback.fst W.hom (𝒳.map e) =
      pullback.fst ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj W).hom
          ((sqDiagram φ).map e) ≫ pullback.fst W.hom (pullback.snd (φ.app i) (φ.app i)) :=
  overPullbackCompIso_trans_symm_hom_left_fst _ _ _ _ _ _ _ W

include hf in
/-- The first projection of `triLegFstIso`, followed by the first projection to `W`, is the first
projection of the base change of `W` along the first projection of the triple fibre product and
along the cone leg, followed by the first projection to `W`. -/
lemma triLegFstIso_hom_left_fst (i : I) (W : Over (𝒳.obj i)) :
    (triLegFstIso φ f hf i W).hom.left ≫
        pullback.fst ((Over.pullback (cX.π.app i)).obj W).hom
            (DescentDatum.tripleBaseFst f) ≫
          pullback.fst W.hom (cX.π.app i) =
      pullback.fst ((Over.pullback (DescentDatum.tripleBaseFst (φ.app i))).obj W).hom
          ((triCone φ f hf).π.app i) ≫
        pullback.fst W.hom (DescentDatum.tripleBaseFst (φ.app i)) :=
  overPullbackCompIso_trans_symm_hom_left_fst _ _ _ _ _ _ _ W

include hf in
/-- The first projection of `triLegThdIso`, followed by the first projection to `W`, is the first
projection of the base change of `W` along the third projection of the triple fibre product and
along the cone leg, followed by the first projection to `W`. -/
lemma triLegThdIso_hom_left_fst (i : I) (W : Over (𝒳.obj i)) :
    (triLegThdIso φ f hf i W).hom.left ≫
        pullback.fst ((Over.pullback (cX.π.app i)).obj W).hom
            (DescentDatum.tripleBaseThd f) ≫
          pullback.fst W.hom (cX.π.app i) =
      pullback.fst ((Over.pullback (DescentDatum.tripleBaseThd (φ.app i))).obj W).hom
          ((triCone φ f hf).π.app i) ≫
        pullback.fst W.hom (DescentDatum.tripleBaseThd (φ.app i)) :=
  overPullbackCompIso_trans_symm_hom_left_fst _ _ _ _ _ _ _ W

/-- The first projection of `triMapFstIso`, followed by the first projection to `W`, is the first
projection of the base change of `W` along the first projection of the triple fibre product and
along the transition morphism, followed by the first projection to `W`. -/
lemma triMapFstIso_hom_left_fst {i j : I} (e : j ⟶ i) (W : Over (𝒳.obj i)) :
    (triMapFstIso φ e W).hom.left ≫
        pullback.fst ((Over.pullback (𝒳.map e)).obj W).hom
            (DescentDatum.tripleBaseFst (φ.app j)) ≫
          pullback.fst W.hom (𝒳.map e) =
      pullback.fst ((Over.pullback (DescentDatum.tripleBaseFst (φ.app i))).obj W).hom
          ((triDiagram φ).map e) ≫
        pullback.fst W.hom (DescentDatum.tripleBaseFst (φ.app i)) :=
  overPullbackCompIso_trans_symm_hom_left_fst _ _ _ _ _ _ _ W

/-- The first projection of `triMapThdIso`, followed by the first projection to `W`, is the first
projection of the base change of `W` along the third projection of the triple fibre product and
along the transition morphism, followed by the first projection to `W`. -/
lemma triMapThdIso_hom_left_fst {i j : I} (e : j ⟶ i) (W : Over (𝒳.obj i)) :
    (triMapThdIso φ e W).hom.left ≫
        pullback.fst ((Over.pullback (𝒳.map e)).obj W).hom
            (DescentDatum.tripleBaseThd (φ.app j)) ≫
          pullback.fst W.hom (𝒳.map e) =
      pullback.fst ((Over.pullback (DescentDatum.tripleBaseThd (φ.app i))).obj W).hom
          ((triDiagram φ).map e) ≫
        pullback.fst W.hom (DescentDatum.tripleBaseThd (φ.app i)) :=
  overPullbackCompIso_trans_symm_hom_left_fst _ _ _ _ _ _ _ W

end LimitDatum

end AlgebraicGeometry

end
