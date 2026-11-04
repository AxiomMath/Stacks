module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringForkVertex

/-!
# The simplicial transition on the localization direct images

Let `(C, J)` be a small site and `K` a simplicial object of `SR(C)`, so that the simplicial site
`n ↦ C/K_n` of Stacks 0D8B exists. Stacks 0D8B identifies the morphism of topoi `a_n` which
Stacks 0D70 attaches to the augmentation with the morphism of topoi of the localization functor
`j_n : C/K_n ⥤ C`. This file proves that the identification is compatible with the simplicial
structure: the comparison of Stacks 0D70, compatibility (1), which compares `f_φ` composed with
`a_m` to `a_n`, becomes the comparison of direct images of the composable pair
`r_φ : C/K_n ⥤ C/K_m` and `j_m`, whose composite is `j_n`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.localizationPushforwardCompIso`: the comparison
  `r_{φ,*} ∘ j_{m,*} ≅ j_{n,*}` of direct images along the composable pair of Stacks 0D85.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.componentPushforwardIso_transitionPushforwardIso`:
  the Stacks 0D8B identifications of the direct images carry the comparison of Stacks 0D70,
  compatibility (1), to `localizationPushforwardCompIso`.

## Implementation notes

Both comparisons are built from the same two primitives: the compositor
`CategoryTheory.sheafPushforwardCocontinuousCompIso` of direct images along cocontinuous site
functors, and the transport
`CategoryTheory.SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq` along an equality of such
functors. The identity is therefore an instance of the cocycle law
`CategoryTheory.sheafPushforwardCocontinuousCompIso_assoc` for the triple
`r_φ`, `r_{v_m}`, `j_0`, where `v_m : ⦋0⦌ ⟶ m` is the vertex the augmentation of Stacks 0D70
uses: the two ways of bracketing `r_φ ⋙ r_{v_m} ⋙ j_0 = j_n` are exactly the two sides.

The comparison of two vertices, `vertexPushforwardIso`, enters through its degree-`n` instance at
`v_m ≫ φ` and `v_n`; it is a `sheafPushforwardCocontinuousCompIsoOfEq`, so after cancelling the
compositor against the one inside the Stacks 0D8B identification only a transport along an
equality of functors is left, and transports compose. That cancellation is why the cocycle law
applies with `T = T' = j_n` and so with an identity transport between them.

The declarations of this file are stated for an arbitrary simplicial object of `SR(C)`: no
hypercovering condition is used, only the simplicial site of Stacks 0D8B and the cocontinuity of
its functors, which is Stacks 0D85.

## References

* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 03L5](https://stacks.math.columbia.edu/tag/03L5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-- Transports of a direct image along equalities of cocontinuous site functors compose. -/
theorem SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_trans {X Y : Type u}
    [SmallCategory X] [SmallCategory Y] (Jx : GrothendieckTopology X)
    (Jy : GrothendieckTopology Y) {F G H : X ⥤ Y} [F.IsCocontinuous Jx Jy]
    [G.IsCocontinuous Jx Jy] [H.IsCocontinuous Jx Jy] (h : F = G) (h' : G = H) :
    cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} Jx Jy h ≪≫
        cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} Jx Jy h' =
      cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} Jx Jy (h.trans h') := by
  subst h
  subst h'
  simp [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl]

/-- The comparison of the two composites of direct images attached to `g ⋙ f = h ⋙ f`,
followed by the identification of the second composite with the direct image along a functor
equal to it, is the identification of the first composite with that direct image: the
compositors cancel and the two transports compose. -/
theorem sheafPushforwardCocontinuousCompIsoOfEq_trans_compIso {X Y Z : Type u}
    [SmallCategory X] [SmallCategory Y] [SmallCategory Z] (Jx : GrothendieckTopology X)
    (Jy : GrothendieckTopology Y) (Jz : GrothendieckTopology Z) (g h : X ⥤ Y) (f : Y ⥤ Z)
    {T : X ⥤ Z} [g.IsCocontinuous Jx Jy] [h.IsCocontinuous Jx Jy] [f.IsCocontinuous Jy Jz]
    [(g ⋙ f).IsCocontinuous Jx Jz] [(h ⋙ f).IsCocontinuous Jx Jz] [T.IsCocontinuous Jx Jz]
    (e : g ⋙ f = h ⋙ f) (hT : h ⋙ f = T) :
    sheafPushforwardCocontinuousCompIsoOfEq Jx Jy Jz g h f e ≪≫
        ((sheafPushforwardCocontinuousCompIso Jx Jy Jz h f).symm ≪≫
          SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} Jx Jz hT) =
      (sheafPushforwardCocontinuousCompIso Jx Jy Jz g f).symm ≪≫
        SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} Jx Jz
          (e.trans hT) := by
  rw [sheafPushforwardCocontinuousCompIsoOfEq]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_trans]

/-- **The cocycle law in the form the comparison of two vertices needs.** For a composable triple
`a`, `b`, `c` of cocontinuous site functors, with `b ⋙ c` identified with `BC`, `a ⋙ b` with
`AB`, and `AB ⋙ c` compared with `AB' ⋙ c` and then identified with `T`, the two ways of
comparing the three direct images with the direct image along `T` agree.

This is `CategoryTheory.sheafPushforwardCocontinuousCompIso_assoc` at `T' = T`, with the
comparison of `AB` and `AB'` absorbed by
`CategoryTheory.sheafPushforwardCocontinuousCompIsoOfEq_trans_compIso`. -/
theorem sheafPushforwardCocontinuousCompIso_assoc_vertex
    {C₀ : Type u} [SmallCategory C₀] {C₁ : Type u} [SmallCategory C₁]
    {C₂ : Type u} [SmallCategory C₂] {C₃ : Type u} [SmallCategory C₃]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
    (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
    {a : C₃ ⥤ C₂} {b : C₂ ⥤ C₁} {c : C₁ ⥤ C₀}
    {BC : C₂ ⥤ C₀} {AB AB' : C₃ ⥤ C₁} {T : C₃ ⥤ C₀}
    [ia : a.IsCocontinuous J₃ J₂] [ib : b.IsCocontinuous J₂ J₁] [ic : c.IsCocontinuous J₁ J₀]
    [iBC : BC.IsCocontinuous J₂ J₀] [iAB : AB.IsCocontinuous J₃ J₁]
    [iAB' : AB'.IsCocontinuous J₃ J₁] [iT : T.IsCocontinuous J₃ J₀]
    [ibc : (b ⋙ c).IsCocontinuous J₂ J₀] [iab : (a ⋙ b).IsCocontinuous J₃ J₁]
    [iaBC : (a ⋙ BC).IsCocontinuous J₃ J₀] [iABc : (AB ⋙ c).IsCocontinuous J₃ J₀]
    [iABc' : (AB' ⋙ c).IsCocontinuous J₃ J₀]
    (hbc : b ⋙ c = BC) (hab : a ⋙ b = AB) (hT : a ⋙ BC = T)
    (compat : AB ⋙ c = AB' ⋙ c) (hT' : AB' ⋙ c = T) :
    Functor.isoWhiskerLeft (a.sheafPushforwardCocontinuous (Type u) J₃ J₂)
          ((sheafPushforwardCocontinuousCompIso J₂ J₁ J₀ b c).symm ≪≫
            SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u}
              J₂ J₀ hbc) ≪≫
        ((sheafPushforwardCocontinuousCompIso J₃ J₂ J₀ a BC).symm ≪≫
          SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J₃ J₀ hT) =
      ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
              ((sheafPushforwardCocontinuousCompIso J₃ J₂ J₁ a b).symm ≪≫
                SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u}
                  J₃ J₁ hab)
              (c.sheafPushforwardCocontinuous (Type u) J₁ J₀) ≪≫
            sheafPushforwardCocontinuousCompIsoOfEq J₃ J₁ J₀ AB AB' c compat) ≪≫
        ((sheafPushforwardCocontinuousCompIso J₃ J₁ J₀ AB' c).symm ≪≫
          SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J₃ J₀ hT') := by
  have h := sheafPushforwardCocontinuousCompIso_assoc J₀ J₁ J₂ J₃ hbc hab hT
    (compat.trans hT') (rfl : T.sheafPushforwardCocontinuous (Type u) J₃ J₀ = _)
  rw [Iso.trans_assoc, Iso.trans_assoc,
    sheafPushforwardCocontinuousCompIsoOfEq_trans_compIso J₃ J₁ J₀ AB AB' c compat hT']
  rw [eqToIso_refl, Iso.trans_refl] at h
  rw [h]

/-- The composite of two cocontinuous functors is cocontinuous, with the hypotheses explicit. -/
private theorem isCocontinuous_comp' {X Y Z : Type u} [SmallCategory X] [SmallCategory Y]
    [SmallCategory Z] {Jx : GrothendieckTopology X} {Jy : GrothendieckTopology Y}
    {Jz : GrothendieckTopology Z} {g : X ⥤ Y} {f : Y ⥤ Z} (hg : g.IsCocontinuous Jx Jy)
    (hf : f.IsCocontinuous Jy Jz) : (g ⋙ f).IsCocontinuous Jx Jz :=
  isCocontinuous_comp g f Jx Jy

namespace SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **The comparison of the localization direct images along a simplex map.** The transition
functor `r_φ : C/K_n ⥤ C/K_m` of a simplex map followed by the localization functor `j_m` is the
localization functor `j_n`, so the direct image along `r_φ` followed by the direct image along
`j_m` agrees canonically with the direct image along `j_n`. -/
def localizationPushforwardCompIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ((situation J K).transitionMorphism φ).pushforward ⋙
        (localizationMorphism J K m).pushforward ≅
      (localizationMorphism J K n).pushforward :=
  haveI h1 : (componentOverMap (K.map φ.op)).IsCocontinuous
      ((situation J K).componentTopology n) ((situation J K).componentTopology m) :=
    componentOverMap_isCocontinuous J K φ
  haveI h2 : (sliceForget K (op m)).IsCocontinuous
      ((situation J K).componentTopology m) J := sliceForget_isCocontinuous J K m
  haveI h3 : (componentOverMap (K.map φ.op) ⋙ sliceForget K (op m)).IsCocontinuous
      ((situation J K).componentTopology n) J :=
    @CategoryTheory.isCocontinuous_comp _ _ _ _ _ _ _ _
      ((situation J K).componentTopology n) ((situation J K).componentTopology m) J h1 h2
  (@sheafPushforwardCocontinuousCompIso _ _ _ _ _ _
      ((situation J K).componentTopology n) ((situation J K).componentTopology m) J
      (componentOverMap (K.map φ.op)) (sliceForget K (op m)) h1 h2).symm ≪≫
    @SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} _ _ _ _
      ((situation J K).componentTopology n) J _ _ h3 (sliceForget_isCocontinuous J K n)
      (slicesMap_comp_sliceForget K φ.op)

/-- **The Stacks 0D8B identification of the direct images is compatible with the simplicial
structure.** The comparison of Stacks 0D70, compatibility (1), which compares the direct image of
a simplex transition composed with the component augmentation of the source degree to the
component augmentation of the target degree, is carried by the Stacks 0D8B identifications to the
comparison `localizationPushforwardCompIso` of the direct images of the composable pair
`r_φ`, `j_m`.

Both sides are built from the compositor of direct images along cocontinuous site functors and
transports along equalities of such functors, so the identity is the cocycle law
`CategoryTheory.sheafPushforwardCocontinuousCompIso_assoc_vertex` for the triple `r_φ`, `r_{v_m}`,
`j_0`: the equality `r_φ ⋙ r_{v_m} = r_{v_m ≫ φ}` is the functoriality of `K`, the comparison of
the vertices `v_m ≫ φ` and `v_n` is the compatibility field of the augmentation, and both
bracketings identify the triple composite with `j_n`. -/
theorem componentPushforwardIso_transitionPushforwardIso {m n : SimplexCategory} (φ : m ⟶ n) :
    Functor.isoWhiskerLeft ((situation J K).transitionMorphism φ).pushforward
          (componentPushforwardIso J K m) ≪≫
        localizationPushforwardCompIso J K φ =
      SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation J K) (Cat.of C) J
          (situationAugmentation J K) φ ≪≫
        componentPushforwardIso J K n := by
  have hφ : (((slices K).map φ.op).toFunctor).IsCocontinuous
      ((situation J K).componentTopology n) ((situation J K).componentTopology m) :=
    componentOverMap_isCocontinuous J K φ
  have hvm : (((slices K).map (SimplexCategory.const
        (SimplexCategory.mk 0) m 0).op).toFunctor).IsCocontinuous
      ((situation J K).componentTopology m)
      ((situation J K).componentTopology (SimplexCategory.mk 0)) :=
    componentOverMap_isCocontinuous J K (SimplexCategory.const (SimplexCategory.mk 0) m 0)
  have hvn : (((slices K).map (SimplexCategory.const
        (SimplexCategory.mk 0) n 0).op).toFunctor).IsCocontinuous
      ((situation J K).componentTopology n)
      ((situation J K).componentTopology (SimplexCategory.mk 0)) :=
    componentOverMap_isCocontinuous J K (SimplexCategory.const (SimplexCategory.mk 0) n 0)
  have hvmφ : (((slices K).map ((SimplexCategory.const
        (SimplexCategory.mk 0) m 0 ≫ φ)).op).toFunctor).IsCocontinuous
      ((situation J K).componentTopology n)
      ((situation J K).componentTopology (SimplexCategory.mk 0)) :=
    componentOverMap_isCocontinuous J K (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)
  have h0 : (sliceForget K (op (SimplexCategory.mk 0))).IsCocontinuous
      ((situation J K).componentTopology (SimplexCategory.mk 0)) J :=
    sliceForget_isCocontinuous J K (SimplexCategory.mk 0)
  have hm : (sliceForget K (op m)).IsCocontinuous
      ((situation J K).componentTopology m) J := sliceForget_isCocontinuous J K m
  have hn : (sliceForget K (op n)).IsCocontinuous
      ((situation J K).componentTopology n) J := sliceForget_isCocontinuous J K n
  exact sheafPushforwardCocontinuousCompIso_assoc_vertex J
    ((situation J K).componentTopology (SimplexCategory.mk 0))
    ((situation J K).componentTopology m) ((situation J K).componentTopology n)
    (ia := hφ) (ib := hvm) (ic := h0) (iBC := hm) (iAB := hvmφ) (iAB' := hvn) (iT := hn)
    (ibc := isCocontinuous_comp' hvm h0) (iab := isCocontinuous_comp' hφ hvm)
    (iaBC := isCocontinuous_comp' hφ hm) (iABc := isCocontinuous_comp' hvmφ h0)
    (iABc' := isCocontinuous_comp' hvn h0)
    (slicesMap_comp_sliceForget K (SimplexCategory.const (SimplexCategory.mk 0) m 0).op)
    (congrArg Cat.Hom.toFunctor ((slices K).map_comp φ.op
      (SimplexCategory.const (SimplexCategory.mk 0) m 0).op)).symm
    (slicesMap_comp_sliceForget K φ.op)
    ((augmentation J K).compatibility n
      (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)
      (SimplexCategory.const (SimplexCategory.mk 0) n 0))
    (slicesMap_comp_sliceForget K (SimplexCategory.const (SimplexCategory.mk 0) n 0).op)

end SimplicialSemiRepresentable

end CategoryTheory

end
