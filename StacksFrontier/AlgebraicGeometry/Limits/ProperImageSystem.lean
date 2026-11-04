module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeSystem
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Properness of the stage morphisms of a system of scheme-theoretic images

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, let `X ⟶ S` and `Y ⟶ S` be quasi-separated and of finite type, and let
`f : X ⟶ Y` be a morphism over `S`. Tags 0CNQ and 0CNR describe `X` and `Y` as the limits of the
inverse systems of scheme-theoretic images attached to good diagrams for them, and realise `f` by
a morphism `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt` of those systems on a common
tail.

Tag 0CNV asserts that if `f` is proper then its stage morphisms are eventually proper. The
Stacks proof derives this from the freedom, recorded in Remark 0CNS, to choose the good diagram:
one chooses a model `W` for `X` which is *proper* over the model of `Y`, and then every stage
morphism — not merely the eventual ones — is proper.

This file proves that second half, which is the geometric content of the tag and the half that
needs no further input: given good diagrams over a common stage whose models are related by a
proper morphism compatible with `f`, there is a `MorphismAt` all of whose stage morphisms are
proper.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.exists_morphismAt_isProper_of_isProper_model`: a
  proper morphism of models at a common stage induces a morphism of the image systems whose every
  stage morphism is proper.

## Implementation notes

The stage morphism at `j` is `AlgebraicGeometry.Scheme.Hom.imageMap` of the square built from the
two stage maps, `f`, and the base change `b j` of `m` to the stage; so it is proper by
`AlgebraicGeometry.Scheme.Hom.isProper_imageMap`, properness being stable under base change. The
natural transformation is defined on all of `Over (op i)` and then whiskered along
`CategoryTheory.Over.map`, which is what makes the two `MorphismAt` axioms hold by the two
characterising identities of `imageMap` with no bookkeeping about the restriction functor.

## What is still missing for Tag 0CNV

**Tag 09ZR, and nothing else.** The inputs of the Stacks proof that *produce* the proper model are
Tag 09ZR (a proper morphism factors as a closed immersion into a proper morphism of finite
presentation), part (1) of Tag 01ZM and Tag 081F. The last two are available, and
`StacksDraft.AlgebraicGeometry.F3b.Limits.ProperImageSystemModels` performs both descents, so
Tag 09ZR is the whole residue:
`AlgebraicGeometry.LimitNoetherianSituation.eventually_isProper_morphismAt_of_exists_factorisation`
is the conclusion of this tag on that single hypothesis.

Tag 081F rests on Chow's lemma (`AlgebraicGeometry.HasChowModification`), and both are
available here. Chow's lemma over a Noetherian base is Tag 0200,
`AlgebraicGeometry.hasDenseChowModification`
(`StacksFrontier/AlgebraicGeometry/Segre/ChartSurjective.lean:461`, `@[stacks 0200]` at `:460`);
the Noetherian form of Tag 081F it yields is
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`
(`StacksFrontier/AlgebraicGeometry/ProperLimitStage/NoetherianChow.lean:76`); and the Noetherian
case is the one this situation needs, because Tag 081F is applied over a stage of the image
system of the good diagram for the target and those stages are Noetherian. Part (1) of Tag 01ZM
is `AlgebraicGeometry.LimitDescent.hasFinitePresentationModels`
(`StacksFrontier/AlgebraicGeometry/LimitDescentGlueing/Glueing.lean`).

The assembly of the two good diagrams out of a 09ZR-shaped factorisation is
`StacksDraft.AlgebraicGeometry.F3b.Limits.ProperModelFromClosedImmersion`. Tag 0CNS, the
independence of the construction from the choice of good diagram, is then what converts "there is
*some* good diagram with proper stage morphisms" into the tag's "the given morphism of systems
has eventually proper stage morphisms".

## References

* [Stacks Project, Tag 0CNV](https://stacks.math.columbia.edu/tag/0CNV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe v u

namespace LimitNoetherianSituation

/-- **Tag 0CNV, the geometric step.** Suppose the finite-type models of two good diagrams, taken
over a common stage of the system, are related by a *proper* morphism `m` lying over that stage
and compatible with `f : X ⟶ Y`. Then `f` is induced by a morphism of the two systems of
scheme-theoretic images every one of whose stage morphisms is proper. -/
theorem exists_morphismAt_isProper_of_isProper_model {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (hi : GX.index = GY.index) (m : GX.W ⟶ GY.W) [IsProper m]
    (hm : m ≫ GY.modelMap = GX.modelMap ≫ D.system.map (eqToHom (congrArg op hi)))
    (ht : GX.toModel ≫ m = f ≫ GY.toModel) :
    ∃ (i : I) (hx : GX.index ≤ i) (hy : GY.index ≤ i)
      (F : MorphismAt D f GX GY i hx hy), ∀ j, IsProper (F.maps.app j) := by
  rcases GX with ⟨ix, WX, mx, tx, cx, lx, qx, ex⟩
  rcases GY with ⟨iy, WY, my, ty, cy, ly, qy, ey⟩
  dsimp at hi hm ht m
  subst iy
  simp only [eqToHom_refl, D.system.map_id, Category.comp_id] at hm
  set GX : GoodDiagram D pX := ⟨ix, WX, mx, tx, cx, lx, qx, ex⟩ with hGX
  set GY : GoodDiagram D pY := ⟨ix, WY, my, ty, cy, ly, qy, ey⟩ with hGY
  -- the base change of `m` to each stage of the system
  let b (j : Over (op ix)) :
      pullback (D.system.map j.hom) mx ⟶ pullback (D.system.map j.hom) my :=
    pullback.map _ _ _ _ (𝟙 _) m (𝟙 _) (by simp) (by simpa using hm.symm)
  have bf (j : Over (op ix)) : b j ≫ pullback.fst _ _ = pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have bs (j : Over (op ix)) : b j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ m :=
    pullback.lift_snd _ _ _
  have hb (j : Over (op ix)) : IsProper (b j) :=
    MorphismProperty.pullbackMap (P := @IsProper)
      (inferInstance : IsProper (𝟙 _)) (inferInstance : IsProper m) (by simp) hm.symm
  -- the two stage maps and `f` fit into a square over `b j`
  have hc (j : Over (op ix)) :
      GoodDiagram.stageMap GX j ≫ b j = f ≫ GoodDiagram.stageMap GY j := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, bf, GoodDiagram.stageMap_fst, Category.assoc,
        GoodDiagram.stageMap_fst, ← Category.assoc, hf]
    · rw [Category.assoc, bs, ← Category.assoc, GoodDiagram.stageMap_snd, Category.assoc,
        GoodDiagram.stageMap_snd]
      exact ht
  -- and `b` is compatible with the transition morphisms of the base-changed models
  have hbT : ∀ {j k : Over (op ix)} (a : j ⟶ k),
      GoodDiagram.stageTargetMap GX a ≫ b k = b j ≫ GoodDiagram.stageTargetMap GY a := by
    intro j k a
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, bf, GoodDiagram.stageTargetMap_fst, Category.assoc,
        GoodDiagram.stageTargetMap_fst, ← Category.assoc, bf]
    · rw [Category.assoc, bs, ← Category.assoc, GoodDiagram.stageTargetMap_snd,
        Category.assoc, GoodDiagram.stageTargetMap_snd, bs]
  have hbase : ∀ j : Over (op ix),
      Scheme.Hom.imageMap (GoodDiagram.stageMap GX j) (GoodDiagram.stageMap GY j) f (b j) (hc j)
          ≫ (GoodDiagram.stageMap GY j).imageι ≫ pullback.fst _ _ =
        (GoodDiagram.stageMap GX j).imageι ≫ pullback.fst _ _ := by
    intro j
    rw [Scheme.Hom.imageMap_imageι_assoc, bf]
  have hind : ∀ j : Over (op ix),
      (GoodDiagram.stageMap GX j).toImage ≫
          Scheme.Hom.imageMap (GoodDiagram.stageMap GX j) (GoodDiagram.stageMap GY j)
            f (b j) (hc j) =
        f ≫ (GoodDiagram.stageMap GY j).toImage := fun j =>
    Scheme.Hom.toImage_imageMap _ _ _ _ _
  -- the induced morphism of image systems, defined on all of `Over (op ix)`
  let τ : GoodDiagram.imageSystem GX ⟶ GoodDiagram.imageSystem GY :=
    { app := fun j => Scheme.Hom.imageMap (GoodDiagram.stageMap GX j)
        (GoodDiagram.stageMap GY j) f (b j) (hc j)
      naturality := by
        intro j k a
        apply (cancel_mono (GoodDiagram.stageMap GY k).imageι).mp
        have e₁ : (GoodDiagram.imageTransition GX a ≫
              Scheme.Hom.imageMap (GoodDiagram.stageMap GX k) (GoodDiagram.stageMap GY k)
                f (b k) (hc k)) ≫ (GoodDiagram.stageMap GY k).imageι =
            (GoodDiagram.stageMap GX j).imageι ≫
              GoodDiagram.stageTargetMap GX a ≫ b k := by
          rw [Category.assoc, Scheme.Hom.imageMap_imageι, ← Category.assoc,
            GoodDiagram.imageTransition_imageι, Category.assoc]
        have e₂ : (Scheme.Hom.imageMap (GoodDiagram.stageMap GX j)
              (GoodDiagram.stageMap GY j) f (b j) (hc j) ≫
              GoodDiagram.imageTransition GY a) ≫ (GoodDiagram.stageMap GY k).imageι =
            (GoodDiagram.stageMap GX j).imageι ≫
              b j ≫ GoodDiagram.stageTargetMap GY a := by
          rw [Category.assoc, GoodDiagram.imageTransition_imageι, ← Category.assoc,
            Scheme.Hom.imageMap_imageι, Category.assoc]
        exact e₁.trans ((congrArg _ (hbT a)).trans e₂.symm) }
  refine ⟨ix, le_rfl, le_rfl,
    { maps := Functor.whiskerLeft (Over.map ((homOfLE (le_refl ix)).op)) τ
      over_base := fun j => hbase _
      induces := fun j => hind _ }, ?_⟩
  intro j
  set k := (Over.map ((homOfLE (le_refl ix)).op)).obj j with hk
  have := hb k
  exact Scheme.Hom.isProper_imageMap (GoodDiagram.stageMap GX k)
    (GoodDiagram.stageMap GY k) f (b k) (hc k)

end LimitNoetherianSituation

end AlgebraicGeometry

end
