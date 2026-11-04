module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceImmersionOfHProjective

/-!
# The diagram of Stacks 08AQ after base change to an étale chart

Let `D` be a closed immersion `h_Z ⟶ P^n_X = X ×_S P^n_S` of algebraic spaces over `S`, as in
`AlgebraicGeometry.Space.ProjectiveSpaceImmersion`, whose source is the represented space of an
object `Z` of the big fppf site and whose composite with the coordinates `P^n_X ⟶ P^n_S` is the
Yoneda image of a morphism of the site `k : Z ⟶ P^n_S`.  The composite `q : h_Z ⟶ X` is
representable, so for every étale chart `V ⟶ X` the fibre product `V ×_X h_Z` is represented by
an object `W` of the site, with a morphism `ψ_V : W ⟶ V` (the base change of `q`) and a morphism
`π : W ⟶ Z`.

This file proves that **`ψ_V` is H-projective**, with an explicit presentation: there is a closed
immersion `ι : W ⟶ P^n_V` over `V` whose composite with the base change `P^n_V ⟶ P^n_S` is
`π ≫ k`.  The closed immersion is the base change of `h_Z ⟶ X ×_S P^n_S` along
`V ×_S P^n_S ⟶ X ×_S P^n_S`.

This is the input from which the proof of Stacks 08AR applies Stacks 02O1 and Stacks 02O4 to the
morphism `π : Z' ⟶ Z` of its Chow diagram, étale locally on the target.

## Main results

* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.exists_chart_isClosedImmersion`: the closed
  immersion `ι : W ⟶ P^n_V` above.

## References

* [Stacks Project, Tag 08AQ](https://stacks.math.columbia.edu/tag/08AQ)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.ProjectiveSpaceImmersion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {n : ℕ}
  {hP : B.Contains (projectiveSpaceOver n S)} {X : AlgebraicSpaces B S hS} {Z : BigFppfOver B S hS}

/-- **The 08AQ diagram over an étale chart.**  Let `D : h_Z ⟶ X ×_S P^n_S` be a closed immersion
whose composite with the coordinates is `h_k` for a morphism of the site `k : Z ⟶ P^n_S`, and let
`V` be an étale chart of `X`.  Write `W` for the object of the site representing `V ×_X h_Z`,
`ψ_V : W ⟶ V` for the base change of `q = D.hom` and `π : W ⟶ Z` for the other projection.  Then
there is a closed immersion `ι : W ⟶ P^n_V` of schemes over `V` whose composite with the base
change `P^n_V ⟶ P^n_S` is `π ≫ k`. -/
theorem exists_chart_isClosedImmersion
    (D : ProjectiveSpaceImmersion B S hS n hP ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ X)
    (k : Z ⟶ projectiveSpaceSiteObj B S hS n hP) (hk : (D.imm ≫ D.coord).hom = yoneda.map k)
    (V : SmallEtale B S hS X.1) :
    ∃ (π : D.relativelyRepresentable_hom.pullback V.1.hom ⟶ Z)
      (ι : (BigFppfOver.toScheme B S hS).obj (D.relativelyRepresentable_hom.pullback V.1.hom) ⟶
        projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj V.1.left)),
      yoneda.map π = D.relativelyRepresentable_hom.fst V.1.hom ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ι ∧
      ι ≫ (projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj V.1.left) ↘
          (BigFppfOver.toScheme B S hS).obj V.1.left) =
        (BigFppfOver.toScheme B S hS).map (D.relativelyRepresentable_hom.snd V.1.hom) ∧
      ι ≫ projectiveSpaceOverMap n V.1.left.hom.hom =
        (BigFppfOver.toScheme B S hS).map π ≫ (BigFppfOver.toScheme B S hS).map k := by
  have hq := D.relativelyRepresentable_hom
  let V₁ := V.1.left
  let v : yoneda.obj V₁ ⟶ X.1 := V.1.hom
  let s : hq.pullback v ⟶ V₁ := hq.snd v
  let toB := projectiveSpaceSiteObjToBase B S hS n hP
  let tV : V₁ ⟶ baseSiteObj B S hS := Over.homMk V₁.hom
  have hT := isTerminal_yoneda_obj_base B S hS
  obtain ⟨π, hπ⟩ : ∃ π : hq.pullback v ⟶ Z, yoneda.map π = hq.fst v :=
    ⟨Yoneda.fullyFaithful.preimage (hq.fst v), Yoneda.fullyFaithful.map_preimage _⟩
  have wVP : s ≫ tV = (π ≫ k) ≫ toB := (Over.mkIdTerminal (X := B.obj hS)).hom_ext _ _
  let L : hq.pullback v ⟶ pullback tV toB := pullback.lift s (π ≫ k) wVP
  have hLf : L ≫ pullback.fst tV toB = s := pullback.lift_fst _ _ _
  have hLs : L ≫ pullback.snd tV toB = π ≫ k := pullback.lift_snd _ _ _
  -- `V ×_S P^n_S ⟶ X ×_S P^n_S`
  let m' : yoneda.obj (pullback tV toB) ⟶ D.projSpace.1 :=
    D.isPullback.lift (yoneda.map (pullback.fst tV toB) ≫ v) (yoneda.map (pullback.snd tV toB))
      (hT.hom_ext _ _)
  have hm1 : m' ≫ D.proj.hom = yoneda.map (pullback.fst tV toB) ≫ v := D.isPullback.lift_fst _ _ _
  have hm2 : m' ≫ D.coord.hom = yoneda.map (pullback.snd tV toB) := D.isPullback.lift_snd _ _ _
  have hbot : IsPullback m' (yoneda.map (pullback.fst tV toB)) D.proj.hom v := by
    refine IsPullback.of_right (h₁₂ := D.coord.hom) (h₂₂ := D.base.hom) ?_ hm1 D.isPullback.flip
    rw [hm2, show v ≫ D.base.hom = yoneda.map tV from hT.hom_ext _ _]
    exact ((IsPullback.of_hasPullback tV toB).map yoneda).flip
  have hsq : IsPullback (hq.fst v) (yoneda.map L ≫ yoneda.map (pullback.fst tV toB))
      (D.imm.hom ≫ D.proj.hom) v := by
    rw [← Functor.map_comp, hLf]
    exact hq.isPullback v
  have hp : hq.fst v ≫ D.imm.hom = yoneda.map L ≫ m' := by
    apply D.isPullback.hom_ext
    · rw [Category.assoc, Category.assoc, hm1, ← Category.assoc (yoneda.map L),
        ← Functor.map_comp, hLf]
      exact hq.w v
    · rw [Category.assoc, Category.assoc, hm2]
      refine (congrArg (hq.fst v ≫ ·) hk).trans ?_
      rw [← hπ]
      exact (yoneda.map_comp π k).symm.trans
        ((congrArg yoneda.map hLs.symm).trans (yoneda.map_comp L _))
  have hclL : IsClosedImmersion B S hS (yoneda.map L) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback (IsPullback.of_bot hsq hp hbot)
        D.imm_isClosedImmersion
  have hcl : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map L) :=
    (presheaf_yoneda_map_iff B S hS
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) inferInstance L).1 hclL
  -- `V ×_S P^n_S` is `P^n_V`
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hs := (BigFppfOver.toScheme B S hS).map_isPullback (IsPullback.of_hasPullback tV toB)
  have hpr : IsPullback
      (pullback.fst (terminal.from ((BigFppfOver.toScheme B S hS).obj V₁))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      (projectiveSpaceOverMap n V₁.hom.hom) ((BigFppfOver.toScheme B S hS).map tV)
      ((BigFppfOver.toScheme B S hS).map toB) :=
    (isPullback_projectiveSpaceOverMap n V₁.hom.hom).flip
  refine ⟨π, (BigFppfOver.toScheme B S hS).map L ≫ (hs.isoIsPullback _ _ hpr).hom, hπ,
    inferInstance, ?_, ?_⟩
  · show _ ≫ pullback.fst (terminal.from ((BigFppfOver.toScheme B S hS).obj V₁))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) = _
    rw [Category.assoc, IsPullback.isoIsPullback_hom_fst _ _ hs hpr, ← Functor.map_comp, hLf]
  · exact (Category.assoc _ _ _).trans ((congrArg ((BigFppfOver.toScheme B S hS).map L ≫ ·)
      (IsPullback.isoIsPullback_hom_snd _ _ hs hpr)).trans
        (by rw [← Functor.map_comp, hLs, Functor.map_comp]))

end AlgebraicGeometry.Space.ProjectiveSpaceImmersion

end
