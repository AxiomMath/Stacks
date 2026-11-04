module

public import StacksFrontier.AlgebraicGeometry.LimitSmallDominantIndex.Uniqueness
public import StacksFrontier.AlgebraicGeometry.Existence.Descent

/-!
# Stacks 0CNR, existence, with no smallness hypothesis on the index

A morphism `f : X ⟶ Y` of schemes over the limit `S` of a `LimitNoetherianSituation`, together
with good diagrams for `X` and for `Y`, is induced on a sufficiently late common tail by a
morphism of the two inverse systems of scheme-theoretic images. This file proves that, at
exactly the source's hypotheses — in particular with the index type at a universe independent of
the scheme universe and *no* smallness hypothesis on it.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.ambientHom`: the morphism from a stage
  of the source's image system into the ambient base change `S_i ×_{S_{i_2}} V` of the target's
  model, assembled from the projection to the base system and a factorisation of `X ⟶ Y ⟶ V`
  through one stage.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.stageHom`: that morphism, factored
  through the scheme-theoretic image `Y_i`.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.ofModelHom`: the resulting
  `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.exists_morphismAt_of_dominant`:
  **Stacks 0CNR, existence**, at the source's own hypotheses.

## Route

This is the Stacks proof, with the two inputs it names replaced by the forms available here.

The model `V ⟶ S_{i_2}` of the target's good diagram is locally of finite *presentation*, not
merely of finite type, because `S_{i_2}` is Noetherian. By Stacks 0CNQ the source is the limit
of its own image system, and that system is affine over the base change of the source's model to
a common stage `i_1 ≥ max(i_1', i_2)` with quasi-compact scheme-theoretically dominant
projections — the hypotheses of
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant'`. So
`X ⟶ Y ⟶ V` factors as `X ⟶ X_{i_0} ⟶ V` for some `i_0 ≥ i_1`, over `S_{i_2}`.

For every stage `j` above `i_0` that factorisation and the projection `X_j ⟶ S_j` assemble into
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.ambientHom`, a morphism
`X_j ⟶ S_j ×_{S_{i_2}} V`. Its restriction along the cone leg `X ⟶ X_j` is `X ⟶ Y ⟶
S_j ×_{S_{i_2}} V`, which factors through the scheme-theoretic image `Y_j` by definition of
that image; since `X ⟶ X_j` is scheme-theoretically dominant, so does the morphism itself, by
`AlgebraicGeometry.IsClosedImmersion.liftOfDominant` — the content of Stacks 01R9 used here.
Naturality, the two axioms of
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt` and the identification of the induced
morphism on limits with `f` all follow by cancelling the closed embedding of the image, which is
a monomorphism.

## Universe situation

The index type is at a universe `v` independent of the scheme universe `u`, and nothing relates
the two. The smallness that
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall`
would have imposed is removed exactly as it is for the eventual-uniqueness half
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.eventually_eq_morphismAt_of_dominant`, by
the universe-freeing device `AlgebraicGeometry.exists_small_limit_of_affine_of_dominant`.

## Transparency gotchas

`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageSystem` is a semireducible `def`,
so a statement whose subject is a system object rather than the scheme-theoretic image it is
defined to be is not reducibly of the expected shape. Every equation below is therefore either
proved by cancelling a monomorphism and `pullback.hom_ext`, or assembled in term mode out of
`CategoryTheory.Category.assoc` and `congrArg`, where the comparison happens at default
transparency. In particular `quasiSeparatedSpace_imageSystem_obj` passes both of its instance
arguments explicitly: with them left to synthesis the `QuasiSeparated` search is keyed on the
system object and misses the available instance on the image.

## References

* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR), the existence half.
* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ), the limit description.
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC), Proposition.
* [Stacks Project, Tag 01R9](https://stacks.math.columbia.edu/tag/01R9).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace GoodDiagram

variable {X : Scheme.{u}} {f : X ⟶ D.limitScheme}

/-- Each stage of the image system is a quasi-separated space: it is a closed subscheme of a
base change of the model, which is locally Noetherian because the model is of finite type over a
Noetherian stage. -/
public instance quasiSeparatedSpace_imageSystem_obj (G : GoodDiagram D f)
    (j : Over (op G.index)) : QuasiSeparatedSpace (G.imageSystem.obj j) :=
  have h₁ : QuasiSeparatedSpace (G.stageTarget j) := inferInstance
  have h₂ : QuasiSeparated (G.stageMap j).imageι := inferInstance
  @quasiSeparatedSpace_of_quasiSeparated _ _ (G.stageMap j).imageι h₁ h₂

/-- The cone leg from `X` followed by the structure morphism of a stage of the restricted image
system down to the base system is the projection of `X` to that stage of the base system. -/
public lemma imageCone_π_comp_restrictedStageProj (G : GoodDiagram D f) {i₀ : I}
    (hX : G.index ≤ i₀) (j : Over (op i₀)) :
    G.imageCone.π.app ((Over.map (homOfLE hX).op).obj j) ≫ G.restrictedStageProj hX j =
      f ≫ D.limitCone.π.app j.left :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg
        (· ≫ pullback.fst (D.system.map ((Over.map (homOfLE hX).op).obj j).hom) G.modelMap)
        (G.imageCone_π_app_imageι ((Over.map (homOfLE hX).op).obj j))).trans
      (G.stageMap_fst ((Over.map (homOfLE hX).op).obj j)))

end GoodDiagram

namespace MorphismAt

variable {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme} {f : X ⟶ Y}

/-- The cone leg from `X` followed by the morphism of a stage of the source's restricted image
system to the stage of the target's good diagram is `X ⟶ Y ⟶ V ⟶ S_{i_2}`. This is the
compatibility that lets the factorisation of `X ⟶ V` through a stage be extracted. -/
public lemma imageCone_π_comp_restrictedStructureMap (GX : GoodDiagram D pX) {i₀ : I}
    (hX : GX.index ≤ i₀) (GY : GoodDiagram D pY) (hY : GY.index ≤ i₀)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (j : Over (op i₀)) :
    GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj j) ≫
        (GX.restrictedStructureMap hX GY hY).app j =
      (f ≫ GY.toModel) ≫ GY.modelMap := by
  have e₁ : GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj j) ≫
      (GX.restrictedStructureMap hX GY hY).app j =
      (pX ≫ D.limitCone.π.app j.left) ≫
        D.system.map ((Over.map (homOfLE hY).op).obj j).hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ D.system.map ((Over.map (homOfLE hY).op).obj j).hom)
        (GX.imageCone_π_comp_restrictedStageProj hX j))
  have e₂ : (pX ≫ D.limitCone.π.app j.left) ≫
        D.system.map ((Over.map (homOfLE hY).op).obj j).hom = pX ≫ D.proj GY.index :=
    (Category.assoc _ _ _).trans
      (congrArg (pX ≫ ·) (D.limitCone.w ((Over.map (homOfLE hY).op).obj j).hom))
  have e₃ : pX ≫ D.proj GY.index = (f ≫ GY.toModel) ≫ GY.modelMap := by
    rw [← hf, Category.assoc, Category.assoc, GY.commutes]
  exact e₁.trans (e₂.trans e₃)

section OfModelHom

variable (GX : GoodDiagram D pX) (GY : GoodDiagram D pY) {i₀ : I}
  (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)

/-- The transition of the source's restricted image system from a stage down to the base
stage `i_0`. -/
public noncomputable abbrev sourceToBase (j : Over (op i₀)) :
    (Over.map (homOfLE hX).op ⋙ GX.imageSystem).obj j ⟶
      (Over.map (homOfLE hX).op ⋙ GX.imageSystem).obj (tailBase i₀) :=
  (Over.map (homOfLE hX).op ⋙ GX.imageSystem).map (toTailBase j)

variable (h₀ : (Over.map (homOfLE hX).op ⋙ GX.imageSystem).obj (tailBase i₀) ⟶ GY.W)
  (hover : h₀ ≫ GY.modelMap = (GX.restrictedStructureMap hX GY hY).app (tailBase i₀))

/-- The morphism from a stage of the source's image system into the ambient base change
`S_j ×_{S_{i_2}} V` of the target's model: its projection to the base system is the structure
morphism of the stage, and its projection to the model is the transition down to the base stage
followed by the given factorisation `X_{i_0} ⟶ V`. -/
public noncomputable def ambientHom (j : Over (op i₀)) :
    (Over.map (homOfLE hX).op ⋙ GX.imageSystem).obj j ⟶
      GY.stageTarget ((Over.map (homOfLE hY).op).obj j) :=
  pullback.lift (GX.restrictedStageProj hX j) (sourceToBase GX hX j ≫ h₀) (by
    have hn := (GX.restrictedStructureMap hX GY hY).naturality (toTailBase j)
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hn
    calc GX.restrictedStageProj hX j ≫
            D.system.map ((Over.map (homOfLE hY).op).obj j).hom
        = (GX.restrictedStructureMap hX GY hY).app j := rfl
      _ = sourceToBase GX hX j ≫ (GX.restrictedStructureMap hX GY hY).app (tailBase i₀) :=
          hn.symm
      _ = (sourceToBase GX hX j ≫ h₀) ≫ GY.modelMap := by rw [Category.assoc, hover])

/-- The projection of `ambientHom` to the base system is the structure morphism of the stage. -/
@[simp]
public lemma ambientHom_fst (j : Over (op i₀)) :
    ambientHom GX GY hX hY h₀ hover j ≫
        pullback.fst (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap =
      GX.restrictedStageProj hX j :=
  pullback.lift_fst _ _ _

/-- The projection of `ambientHom` to the model is the transition down to the base stage followed
by the factorisation `h₀`. -/
@[simp]
public lemma ambientHom_snd (j : Over (op i₀)) :
    ambientHom GX GY hX hY h₀ hover j ≫
        pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap =
      sourceToBase GX hX j ≫ h₀ :=
  pullback.lift_snd _ _ _

/-- The morphisms into the ambient base changes are natural for the transitions of the two
restricted systems. -/
public lemma ambientHom_naturality {j k : Over (op i₀)} (a : j ⟶ k) :
    (Over.map (homOfLE hX).op ⋙ GX.imageSystem).map a ≫ ambientHom GX GY hX hY h₀ hover k =
      ambientHom GX GY hX hY h₀ hover j ≫
        GY.stageTargetMap ((Over.map (homOfLE hY).op).map a) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ambientHom_fst, GX.restrictedStageProj_naturality hX a,
      Category.assoc, GY.stageTargetMap_fst, ← Category.assoc, ambientHom_fst,
      Over.map_map_left]
  · rw [Category.assoc, ambientHom_snd, Category.assoc, GY.stageTargetMap_snd,
      ambientHom_snd, ← Category.assoc, ← Functor.map_comp,
      show a ≫ toTailBase k = toTailBase j from Subsingleton.elim _ _]

/-- The cone leg from `X` followed by the morphism into the ambient base change is `f` followed
by the stage map of the target's good diagram. This is what forces the morphism into the
scheme-theoretic image. -/
public lemma π_comp_ambientHom (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (hfac : GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj (tailBase i₀)) ≫ h₀ =
      f ≫ GY.toModel) (j : Over (op i₀)) :
    GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj j) ≫
        ambientHom GX GY hX hY h₀ hover j =
      f ≫ GY.stageMap ((Over.map (homOfLE hY).op).obj j) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ambientHom_fst, GX.imageCone_π_comp_restrictedStageProj hX j,
      Category.assoc, GY.stageMap_fst, ← Category.assoc, hf]
    rfl
  · have hw : GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj j) ≫ sourceToBase GX hX j =
        GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj (tailBase i₀)) :=
      (GX.imageCone.whisker (Over.map (homOfLE hX).op)).w (toTailBase j)
    rw [Category.assoc, ambientHom_snd, ← Category.assoc, hw, hfac, Category.assoc,
      GY.stageMap_snd]

/-- The morphism of a stage of the source's image system to the corresponding stage of the
target's, obtained by factoring
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.ambientHom` through the scheme-theoretic
image `Y_j`. -/
public noncomputable def stageHom (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (hfac : GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj (tailBase i₀)) ≫ h₀ =
      f ≫ GY.toModel) (j : Over (op i₀)) :
    (Over.map (homOfLE hX).op ⋙ GX.imageSystem).obj j ⟶
      (Over.map (homOfLE hY).op ⋙ GY.imageSystem).obj j :=
  have _hdom : IsSchemeTheoreticallyDominant
      (GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj j)) :=
    GX.isSchemeTheoreticallyDominant_π _
  IsClosedImmersion.liftOfDominant (GY.restrictedImageι hY j)
    (ambientHom GX GY hX hY h₀ hover j)
    (GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj j))
    (f ≫ GY.imageCone.π.app ((Over.map (homOfLE hY).op).obj j))
    ((π_comp_ambientHom GX GY hX hY h₀ hover f hf hfac j).trans
      ((congrArg (f ≫ ·)
          (GY.imageCone_π_app_imageι ((Over.map (homOfLE hY).op).obj j)).symm).trans
        (Category.assoc _ _ _).symm))

/-- The morphism `stageHom` followed by the closed immersion of the target's stage into the
ambient base change is `ambientHom`. -/
@[simp]
public lemma stageHom_restrictedImageι (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (hfac : GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj (tailBase i₀)) ≫ h₀ =
      f ≫ GY.toModel) (j : Over (op i₀)) :
    stageHom GX GY hX hY h₀ hover f hf hfac j ≫ GY.restrictedImageι hY j =
      ambientHom GX GY hX hY h₀ hover j :=
  IsClosedImmersion.lift_fac _ _ _

/-- **Stacks Project, Tag 0CNR, existence, assembled.** A factorisation of `X ⟶ Y ⟶ V` through
one stage of the source's image system, over `S_{i_2}`, induces a morphism of the two image
systems on the whole tail above that stage. -/
public noncomputable def ofModelHom (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (hfac : GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj (tailBase i₀)) ≫ h₀ =
      f ≫ GY.toModel) :
    MorphismAt D f GX GY i₀ hX hY where
  maps :=
    { app j := stageHom GX GY hX hY h₀ hover f hf hfac j
      naturality := fun j k a => by
        rw [← cancel_mono (GY.restrictedImageι hY k), Category.assoc,
          stageHom_restrictedImageι, Category.assoc, GY.restrictedImageι_naturality hY a,
          ← Category.assoc, stageHom_restrictedImageι,
          ambientHom_naturality GX GY hX hY h₀ hover a] }
  over_base j :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg
          (· ≫ pullback.fst (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap)
          (stageHom_restrictedImageι GX GY hX hY h₀ hover f hf hfac j)).trans
        (ambientHom_fst GX GY hX hY h₀ hover j))
  induces j :=
    (cancel_mono (GY.restrictedImageι hY j)).mp
      (((Category.assoc _ _ _).trans
            ((congrArg (GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj j) ≫ ·)
                (stageHom_restrictedImageι GX GY hX hY h₀ hover f hf hfac j)).trans
              (π_comp_ambientHom GX GY hX hY h₀ hover f hf hfac j))).trans
        ((congrArg (f ≫ ·)
              (GY.imageCone_π_app_imageι ((Over.map (homOfLE hY).op).obj j)).symm).trans
          (Category.assoc _ _ _).symm))

end OfModelHom

end MorphismAt

/-- **Stacks Project, Tag 0CNR, existence.** A morphism of schemes over the limit is realized by
a morphism of the systems of scheme-theoretic images on a sufficiently late common tail.

No hypothesis beyond the source's: in particular no smallness of the index type, and none of the
quasi-separatedness, finite-type or quasi-compactness hypotheses the source carries, all three
of which are consequences of the good diagrams. -/
@[stacks 0CNR "existence"]
public theorem exists_morphismAt_of_dominant (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY) :
    ∃ (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀),
      Nonempty (MorphismAt D f GX GY i₀ hX hY) := by
  obtain ⟨i₁, hX₁, hY₁⟩ := exists_ge_ge GX.index GY.index
  have hne : Nonempty (Set.Ici i₁) := ⟨⟨i₁, le_rfl⟩⟩
  have hdir := directed_tail (I := I) i₁
  obtain ⟨i, h, hh₁, hh₂⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant'
      (GX.tailImageSystem hX₁) (GX.tailImageCone hX₁) (GX.isLimitTailImageCone hX₁)
      (GX.tailImageHom hX₁)
      (GX.stageMap ((Over.map (homOfLE hX₁).op).obj (tailBase i₁)))
      (fun x => GX.imageCone_π_comp_imageOverHom hX₁ ((tailToOver i₁).obj x))
      (fun x => GX.isAffineHom_imageOverHom hX₁ ((tailToOver i₁).obj x))
      (GX.isAffineHom_stageMap _)
      (fun _ => GX.quasiCompact_imageCone_π_app _)
      (fun _ => GX.isSchemeTheoreticallyDominant_π _)
      (fun _ => GX.compactSpace_imageSystem_obj _)
      (fun _ => GX.quasiSeparatedSpace_imageSystem_obj _)
      (MorphismAt.tailStructureMap GX hX₁ GY hY₁) GY.modelMap inferInstance
      (f ≫ GY.toModel)
      (fun x => MorphismAt.imageCone_π_comp_restrictedStructureMap GX hX₁ GY hY₁ f hf
        ((tailToOver i₁).obj x))
  exact ⟨i.val, hX₁.trans i.property, hY₁.trans i.property,
    ⟨MorphismAt.ofModelHom GX GY _ _ h hh₂ f hf hh₁⟩⟩

end AlgebraicGeometry.LimitNoetherianSituation

/-! ### Faithfulness check

The conclusion proved above, restated with the binders of the source's own statement of the
existence half — every one explicit, in the source's order, *including* the six instance
hypotheses on the two structure morphisms that the source carries and that the proof above does
not need — and closed by it. There is no added hypothesis: in particular no smallness of the
index type. The structure `MorphismAt` and the good diagrams it is stated over are the library's,
which carry the source's names and types.
-/

namespace Tag0CNRExistence

open AlgebraicGeometry AlgebraicGeometry.LimitNoetherianSituation

example {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY) :
    ∃ (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀),
      Nonempty (MorphismAt D f GX GY i₀ hX hY) :=
  exists_morphismAt_of_dominant D f hf GX GY

end Tag0CNRExistence

end
