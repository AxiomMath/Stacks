module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProjectiveSpaceContracted
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# The projective-space diagram of a scheme which is H-projective over an affine base

The proof of Stacks 08AR applies Stacks 08AQ to the morphism `π : Z' ⟶ Z` of its Chow diagram,
with `Z' ⟶ P^n_A` a closed immersion over `Spec A` and `Z ⟶ Spec A` proper; for that it needs
`Z'` as a closed subspace of `P^n_Z`, which the source obtains as the closed immersion
`(i, π) : Z' ⟶ P^n_A ×_A Z = P^n_Z` (Stacks 03KO). This file builds that diagram in the form
`AlgebraicGeometry.Space.ProjectiveSpaceImmersion` of Stacks 08AQ, in which `P^n_Y` is the
fibre product `Y ×_S P^n_S` with the projective space over the base scheme of the site.

## Main results

* `AlgebraicGeometry.Space.exists_projectiveSpaceImmersion_of_isClosedImmersion`: let `T` be an
  object of the site, `f : X ⟶ h_T` a separated morphism of algebraic spaces, `ψ : Z ⟶ T` a
  morphism of the site and `q : h_Z ⟶ X` with `q ≫ f = h_ψ`. If `ψ` factors through a closed
  immersion `i : Z ⟶ P^n_T` on underlying schemes, then `q` is the composite of a closed
  immersion `h_Z ⟶ X ×_S P^n_S` with the projection, the second component of the immersion
  being the Yoneda image of `Z ⟶ P^n_T ⟶ P^n_S`.

## Implementation notes

The immersion is `(q, c) : h_Z ⟶ X ×_S P^n_S`, with `c` the Yoneda image of
`Z ⟶ P^n_T ⟶ P^n_S`. Following it by `f ×_S P^n_S : X ×_S P^n_S ⟶ h_T ×_S P^n_S` gives
`(h_ψ, c)`, which is the Yoneda image of the morphism of the site `Z ⟶ T ×_S P^n_S` whose
underlying morphism of schemes is `i` read through the identification of `T ×_S P^n_S` with
`P^n_T` (`AlgebraicGeometry.isPullback_projectiveSpaceOverMap`); so it is a closed immersion.
The morphism `f ×_S P^n_S` is a base change of `f`, hence separated (Stacks 03KL), and Stacks 0AGC
part (3), `AlgebraicGeometry.Space.isClosedImmersion_of_comp_of_isSeparated`, concludes. This is
the source's appeal to Stacks 03KO in the form that needs no separate graph.

## References

* [Stacks Project, Tag 08AQ](https://stacks.math.columbia.edu/tag/08AQ)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 0AGC](https://stacks.math.columbia.edu/tag/0AGC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` for `HasPullbacks` of presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_ProjectiveSpaceImmersionOfHProjective :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ProjectiveSpaceImmersionOfHProjective
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The diagram `Z ⟶ P^n_X` of Stacks 08AQ for a scheme H-projective over the base.**

Let `T` be an object of the big fppf site of `S`, `f : X ⟶ h_T` a separated morphism of
algebraic spaces, `ψ : Z ⟶ T` a morphism of the site, and `q : h_Z ⟶ X` with `q ≫ f = h_ψ`.
Suppose that on underlying schemes `ψ` is a closed immersion `i : Z ⟶ P^n_T` followed by the
projection. Then there is a `ProjectiveSpaceImmersion` of `h_Z` into `X ×_S P^n_S` whose
composite with the projection is `q`, and whose composite with the coordinates
`X ×_S P^n_S ⟶ P^n_S` is the Yoneda image of a morphism of the site `k : Z ⟶ P^n_S` with
underlying morphism `Z ⟶ P^n_T ⟶ P^n_S`. -/
theorem exists_projectiveSpaceImmersion_of_isClosedImmersion
    {X : AlgebraicSpaces B S hS} (T : BigFppfOver B S hS)
    (f : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (hf : IsSeparated B S hS f.hom)
    {Z : BigFppfOver B S hS} (ψ : Z ⟶ T)
    (q : (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (hq : q.hom ≫ f.hom = yoneda.map ψ) (n : ℕ)
    (i : (BigFppfOver.toScheme B S hS).obj Z ⟶
      projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj T))
    (hi : _root_.AlgebraicGeometry.IsClosedImmersion i)
    (hiψ : i ≫ (projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj T) ↘
      (BigFppfOver.toScheme B S hS).obj T) = (BigFppfOver.toScheme B S hS).map ψ) :
    ∃ (D : ProjectiveSpaceImmersion B S hS n (contains_projectiveSpaceOver B S hS n)
        ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ X)
      (k : Z ⟶ projectiveSpaceSiteObj B S hS n (contains_projectiveSpaceOver B S hS n)),
      D.hom = q ∧ (D.imm ≫ D.coord).hom = yoneda.map k ∧
        (BigFppfOver.toScheme B S hS).map k = i ≫ projectiveSpaceOverMap n T.hom.hom := by
  have hP := contains_projectiveSpaceOver B S hS n
  let T₀ := (BigFppfOver.toScheme B S hS).obj T
  let toB := projectiveSpaceSiteObjToBase B S hS n hP
  let tB : T ⟶ baseSiteObj B S hS := Over.homMk T.hom
  have hT := isTerminal_yoneda_obj_base B S hS
  -- The coordinates `Z ⟶ P^n_T ⟶ P^n_S`, as a morphism of the site.
  have hk : (i ≫ projectiveSpaceOverMap n T.hom.hom) ≫ (projectiveSpaceOver n S ↘ S) =
      Z.hom.hom := by
    change (i ≫ projectiveSpaceOverMap n T.hom.hom) ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = Z.hom.hom
    rw [Category.assoc, projectiveSpaceOverMap_fst, ← Category.assoc]
    change (i ≫ (projectiveSpaceOver n T₀ ↘ T₀)) ≫ T.hom.hom = Z.hom.hom
    rw [hiψ]
    exact congrArg (fun φ => φ.hom) (Over.w ψ)
  let k : Z ⟶ projectiveSpaceSiteObj B S hS n hP :=
    Over.homMk (ObjectProperty.homMk (i ≫ projectiveSpaceOverMap n T.hom.hom)) (by ext1; exact hk)
  let base0 : X.1 ⟶ yoneda.obj (baseSiteObj B S hS) := hT.from X.1
  let PX : AlgebraicSpaces B S hS :=
    ⟨pullback base0 (yoneda.map toB), isAlgebraicSpace_pullback B S hS _ _ X.2
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)⟩
  let immh : yoneda.obj Z ⟶ pullback base0 (yoneda.map toB) :=
    pullback.lift q.hom (yoneda.map k) (hT.hom_ext _ _)
  -- The closed immersion.
  let Q := pullback (yoneda.map tB) (yoneda.map toB)
  let m : pullback base0 (yoneda.map toB) ⟶ Q :=
    pullback.lift (pullback.fst base0 (yoneda.map toB) ≫ f.hom)
      (pullback.snd base0 (yoneda.map toB)) (hT.hom_ext _ _)
  have hm1 : m ≫ pullback.fst (yoneda.map tB) (yoneda.map toB) =
      pullback.fst base0 (yoneda.map toB) ≫ f.hom := pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd (yoneda.map tB) (yoneda.map toB) =
      pullback.snd base0 (yoneda.map toB) := pullback.lift_snd _ _ _
  have hi1 : immh ≫ pullback.fst base0 (yoneda.map toB) = q.hom := pullback.lift_fst _ _ _
  have hi2 : immh ≫ pullback.snd base0 (yoneda.map toB) = yoneda.map k := pullback.lift_snd _ _ _
  have hm : IsSeparated B S hS m := by
    have H : IsPullback (pullback.fst base0 (yoneda.map toB))
        (m ≫ pullback.snd (yoneda.map tB) (yoneda.map toB)) (f.hom ≫ yoneda.map tB)
        (yoneda.map toB) := by
      rw [hm2, show f.hom ≫ yoneda.map tB = base0 from hT.hom_ext _ _]
      exact IsPullback.of_hasPullback _ _
    have sq : IsPullback (pullback.fst base0 (yoneda.map toB)) m f.hom
        (pullback.fst (yoneda.map tB) (yoneda.map toB)) :=
      IsPullback.of_bot H hm1.symm (IsPullback.of_hasPullback _ _)
    rw [← sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f.hom
      (pullback.fst (yoneda.map tB) (yoneda.map toB)))]
    exact isSeparated_comp B S hS _ _
      (isSeparated_of_isIso B S hS
        (sq.isoIsPullback _ _ (IsPullback.of_hasPullback f.hom _)).hom)
      (isSeparated_pullback B S hS f.hom _ hf)
  have hcomp : IsClosedImmersion B S hS (immh ≫ m) := by
    have w : ψ ≫ tB = k ≫ toB := (Over.mkIdTerminal (X := B.obj hS)).hom_ext _ _
    let L : Z ⟶ pullback tB toB := pullback.lift ψ k w
    have hPt : IsPullback (yoneda.map (pullback.fst tB toB)) (yoneda.map (pullback.snd tB toB))
        (yoneda.map tB) (yoneda.map toB) :=
      (IsPullback.of_hasPullback tB toB).map yoneda
    have hL : immh ≫ m = yoneda.map L ≫ hPt.isoPullback.hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, hm1, ← Category.assoc, hi1, hq, Category.assoc,
          IsPullback.isoPullback_hom_fst, ← Functor.map_comp, pullback.lift_fst]
      · rw [Category.assoc, hm2, hi2, Category.assoc, IsPullback.isoPullback_hom_snd,
          ← Functor.map_comp, pullback.lift_snd]
    rw [hL]
    refine MorphismProperty.RespectsIso.postcomp _ _ _ ?_
    refine (presheaf_yoneda_map_iff B S hS
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) inferInstance L).2 ?_
    have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.forget B S hS) := inferInstance
    have _ : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
    have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      comp_preservesLimitsOfShape _ _
    have hs := (BigFppfOver.toScheme B S hS).map_isPullback (IsPullback.of_hasPullback tB toB)
    have hp : IsPullback
        (pullback.fst (terminal.from T₀) (terminal.from (projectiveSpaceAtUniverse.{u} n)))
        (projectiveSpaceOverMap n T.hom.hom) ((BigFppfOver.toScheme B S hS).map tB)
        ((BigFppfOver.toScheme B S hS).map toB) :=
      (isPullback_projectiveSpaceOverMap n T.hom.hom).flip
    obtain ⟨e, he1, he2⟩ : ∃ e : (BigFppfOver.toScheme B S hS).obj (pullback tB toB) ≅
        projectiveSpaceOver n T₀,
        e.hom ≫ pullback.fst (terminal.from T₀) (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
          (BigFppfOver.toScheme B S hS).map (pullback.fst tB toB) ∧
        e.hom ≫ projectiveSpaceOverMap n T.hom.hom =
          (BigFppfOver.toScheme B S hS).map (pullback.snd tB toB) :=
      ⟨hs.isoIsPullback _ _ hp, IsPullback.isoIsPullback_hom_fst _ _ hs hp,
        IsPullback.isoIsPullback_hom_snd _ _ hs hp⟩
    have hLe : (BigFppfOver.toScheme B S hS).map L = i ≫ e.inv := by
      rw [Iso.eq_comp_inv]
      apply hp.hom_ext
      · rw [Category.assoc, he1, ← Functor.map_comp, pullback.lift_fst]
        exact hiψ.symm
      · have h2 : (BigFppfOver.toScheme B S hS).map L ≫
            (BigFppfOver.toScheme B S hS).map (pullback.snd tB toB) =
            i ≫ projectiveSpaceOverMap n T.hom.hom := by
          rw [← Functor.map_comp, pullback.lift_snd]
          rfl
        rw [Category.assoc, he2]
        exact h2
    rw [hLe]
    infer_instance
  exact ⟨{ projSpace := PX
           proj := ObjectProperty.homMk (pullback.fst _ _)
           coord := ObjectProperty.homMk (pullback.snd _ _)
           base := ObjectProperty.homMk base0
           isPullback := IsPullback.of_hasPullback _ _
           imm := ObjectProperty.homMk immh
           imm_isClosedImmersion :=
             isClosedImmersion_of_comp_of_isSeparated B S hS immh m hcomp hm },
    k, ObjectProperty.hom_ext _ hi1, hi2, rfl⟩

end AlgebraicGeometry.Space

end
