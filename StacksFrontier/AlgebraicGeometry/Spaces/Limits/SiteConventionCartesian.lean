module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.BaseChangeLimitsConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionRelocalize

/-!
# The chapter's convention on the site passes to cartesian subsystems

Section 70.2 of the source (tag 07SD) assumes that every ring it considers has its spectrum in
the big fppf site. For an inverse system `D` of presheaves on the big fppf site of `S` with
affine transition morphisms this is `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: for
every stage `D i` and every affine scheme-valued point `Z ⟶ D i`, the limit of the affine
schemes `Z ×_{D i} D k`, `k` over `i`, lies in the site.

Let `α : D' ⟶ G ⋙ D` be a natural transformation, along a reindexing `G : J ⥤ I`, all of whose
naturality squares are cartesian. Then for a scheme-valued point `g : Z ⟶ D' j` the base changes
`Z ×_{D' j} D' k` are the base changes `Z ×_{D (G j)} D (G k)` along `g ≫ α j`, by pasting
cartesian squares. So if, for every `j`, the stages over `j` are initial among the stages over
`G j`, the schemes the convention speaks about for `D'` are among those it speaks about for `D`,
and the convention for `D` gives it for `D'`.

The case in view is the system of inverse images of an open subspace `V` of a stage `D i₀` in the
later stages: this is a cartesian subsystem of the restriction of `D` to the tail of the index
above `i₀`, and the slices of the tail are the slices of the index.

## Main results

* `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.of_isPullback`: the convention passes
  along a cartesian natural transformation whose reindexing has initial slices.
* `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.preimageDiagram`: the convention passes
  to a system of inverse images of a subfunctor.
* `AlgebraicGeometry.initial_post_limitTailForget`: the slices of the tail of a preorder above an
  element are initial in the slices of the preorder.

## Implementation notes

`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.comp_subtypeGe` and
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.baseChangeOverSystem` treat the tail and
the base change separately, along an equivalence of slices; the system of inverse images is the
two at once, and is not syntactically a base change system, so it is handled here directly by the
cartesian-square criterion, through
`AlgebraicGeometry.BigFppfOver.LimitInSite.comp_initial`.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The inclusion of the tail of a preorder above `i₀`, as a functor between the opposite
categories. -/
abbrev limitTailForget {I : Type u} [Preorder I] (i₀ : I) : (LimitTail I i₀)ᵒᵖ ⥤ Iᵒᵖ :=
  (limitTailOverEquiv i₀).functor ⋙ Over.forget (op i₀)

/-- **The slices of the tail are initial in the slices of the preorder.** The tail of a preorder
above `i₀` is upward closed, so every element above a member of the tail lies in the tail. -/
instance initial_post_limitTailForget {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (i₀ : I) (j : (LimitTail I i₀)ᵒᵖ) :
    (Over.post (X := j) (limitTailForget i₀)).Initial := by
  have _ : IsDirected (LimitTail I i₀) (· ≤ ·) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
    exact ⟨⟨k, x.2.trans hxk⟩, hxk, hyk⟩
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d => ?_) (fun {d c} s s' => ?_)
  · have hd : j.unop.1 ≤ d.left.unop := leOfHom d.hom.unop
    let c : Over j := Over.mk (X := j) (Y := op ⟨d.left.unop, j.unop.2.trans hd⟩)
      (homOfLE (show j.unop ≤ ⟨d.left.unop, j.unop.2.trans hd⟩ from hd)).op
    exact ⟨c, ⟨Over.homMk (𝟙 d.left) (Subsingleton.elim _ _)⟩⟩
  · exact ⟨c, 𝟙 c, by ext; exact Subsingleton.elim _ _⟩

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Cartesian

variable {I J : Type u} [Category.{u} I] [Category.{u} J]
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {D' : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (G : J ⥤ I) (α : D' ⟶ G ⋙ D)
  (hα : ∀ {j k : J} (f : j ⟶ k), IsPullback (D'.map f) (α.app j) (α.app k) (D.map (G.map f)))
  (j : J) (Z : BigAffineFppf B S hS)
  (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D'.obj j)

include hα in
/-- A base change of a stage of `D'` along `g` is the base change of the corresponding stage of
`D` along `g ≫ α j`, by pasting cartesian squares. -/
theorem isPullback_stageBaseChangeFst_comp_app (k : Over j) :
    IsPullback (stageBaseChangeFst B S hS j D' Z g k ≫ α.app k.left)
      (stageBaseChangeSnd B S hS j D' Z g k) (D.map (G.map k.hom)) (g ≫ α.app j) :=
  ((isPullback_stageBaseChange B S hS j D' Z g k).flip.paste_vert (hα k.hom)).flip

/-- The comparison of the base changes of `D'` along `g` with those of `D` along `g ≫ α j`, at
one stage over `j`. -/
def stageBaseChangeCartesianIsoApp (k : Over j) :
    (stageBaseChangeDiagram B S hS j D' Z g).obj k ≅
      (stageBaseChangeDiagram B S hS (G.obj j) D Z (g ≫ α.app j)).obj ((Over.post G).obj k) :=
  (isPullback_stageBaseChangeFst_comp_app G α hα j Z g k).isoIsPullback _ _
    (isPullback_stageBaseChange B S hS (G.obj j) D Z (g ≫ α.app j) ((Over.post G).obj k))

/-- The comparison `stageBaseChangeCartesianIsoApp` followed by the first projection to `D` is the
first projection to `D'` followed by `α`. -/
theorem stageBaseChangeCartesianIsoApp_hom_fst (k : Over j) :
    (stageBaseChangeCartesianIsoApp G α hα j Z g k).hom ≫
        stageBaseChangeFst B S hS (G.obj j) D Z (g ≫ α.app j) ((Over.post G).obj k) =
      stageBaseChangeFst B S hS j D' Z g k ≫ α.app k.left :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The comparison `stageBaseChangeCartesianIsoApp` commutes with the second projections. -/
theorem stageBaseChangeCartesianIsoApp_hom_snd (k : Over j) :
    (stageBaseChangeCartesianIsoApp G α hα j Z g k).hom ≫
        stageBaseChangeSnd B S hS (G.obj j) D Z (g ≫ α.app j) ((Over.post G).obj k) =
      stageBaseChangeSnd B S hS j D' Z g k :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **The base changes of a cartesian subsystem.** The diagram of base changes of `D'` along `g`
is the restriction along `Over.post G` of the diagram of base changes of `D` along `g ≫ α j`. -/
def stageBaseChangeCartesianIso :
    stageBaseChangeDiagram B S hS j D' Z g ≅
      Over.post G ⋙ stageBaseChangeDiagram B S hS (G.obj j) D Z (g ≫ α.app j) :=
  NatIso.ofComponents (stageBaseChangeCartesianIsoApp G α hα j Z g) (fun {k k'} m => by
    refine (isPullback_stageBaseChange B S hS (G.obj j) D Z (g ≫ α.app j)
      ((Over.post G).obj k')).hom_ext ?_ ?_
    · have h1 := stageBaseChangeDiagram_map_comp_fst B S hS (G.obj j) D Z (g ≫ α.app j)
        ((Over.post G).map m)
      have h2 := stageBaseChangeDiagram_map_comp_fst B S hS j D' Z g m
      have e1 : (stageBaseChangeDiagram B S hS j D' Z g).map m ≫
          (stageBaseChangeCartesianIsoApp G α hα j Z g k').hom ≫
            stageBaseChangeFst B S hS (G.obj j) D Z (g ≫ α.app j) ((Over.post G).obj k') =
          stageBaseChangeFst B S hS j D' Z g k ≫ α.app k.left ≫ D.map (G.map m.left) := by
        rw [stageBaseChangeCartesianIsoApp_hom_fst]
        exact (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ α.app k'.left) h2).trans <| (Category.assoc _ _ _).trans <|
            congrArg (stageBaseChangeFst B S hS j D' Z g k ≫ ·) (α.naturality m.left)
      have e2 : (stageBaseChangeCartesianIsoApp G α hα j Z g k).hom ≫
          (Over.post G ⋙ stageBaseChangeDiagram B S hS (G.obj j) D Z (g ≫ α.app j)).map m ≫
            stageBaseChangeFst B S hS (G.obj j) D Z (g ≫ α.app j) ((Over.post G).obj k') =
          stageBaseChangeFst B S hS j D' Z g k ≫ α.app k.left ≫ D.map (G.map m.left) := by
        rw [Functor.comp_map]
        exact (congrArg ((stageBaseChangeCartesianIsoApp G α hα j Z g k).hom ≫ ·) h1).trans <|
          (Category.assoc _ _ _).symm.trans <|
            (congrArg (· ≫ D.map (G.map m.left))
              (stageBaseChangeCartesianIsoApp_hom_fst G α hα j Z g k)).trans
              (Category.assoc _ _ _)
      simpa only [Category.assoc] using e1.trans e2.symm
    · have h1 := stageBaseChangeDiagram_map_comp_snd B S hS (G.obj j) D Z (g ≫ α.app j)
        ((Over.post G).map m)
      have h2 := stageBaseChangeDiagram_map_comp_snd B S hS j D' Z g m
      have e1 : (stageBaseChangeDiagram B S hS j D' Z g).map m ≫
          (stageBaseChangeCartesianIsoApp G α hα j Z g k').hom ≫
            stageBaseChangeSnd B S hS (G.obj j) D Z (g ≫ α.app j) ((Over.post G).obj k') =
          stageBaseChangeSnd B S hS j D' Z g k := by
        rw [stageBaseChangeCartesianIsoApp_hom_snd, h2]
      have e2 : (stageBaseChangeCartesianIsoApp G α hα j Z g k).hom ≫
          (Over.post G ⋙ stageBaseChangeDiagram B S hS (G.obj j) D Z (g ≫ α.app j)).map m ≫
            stageBaseChangeSnd B S hS (G.obj j) D Z (g ≫ α.app j) ((Over.post G).obj k') =
          stageBaseChangeSnd B S hS j D' Z g k := by
        rw [Functor.comp_map, h1, stageBaseChangeCartesianIsoApp_hom_snd]
      simpa only [Category.assoc] using e1.trans e2.symm)

end Cartesian

/-- **The convention passes along a cartesian natural transformation.** Let `α : D' ⟶ G ⋙ D` be a
natural transformation all of whose naturality squares are cartesian, along a reindexing `G` for
which the stages over `j` are initial among the stages over `G j`. If `D` has affine transition
morphisms and satisfies the chapter's convention, so does `D'`: the base changes of `D'` along a
scheme-valued point `g` of `D' j` are those of `D` along `g ≫ α j`, restricted along an initial
functor. -/
theorem SiteContainsBaseChangeLimits.of_isPullback {I J : Type u} [Category.{u} I]
    [Category.{u} J] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {D' : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : J ⥤ I)
    [∀ j : J, (Over.post (X := j) G).Initial] (α : D' ⟶ G ⋙ D)
    (hα : ∀ {j k : J} (f : j ⟶ k), IsPullback (D'.map f) (α.app j) (α.app k) (D.map (G.map f)))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hconv : SiteContainsBaseChangeLimits B S hS D) :
    SiteContainsBaseChangeLimits B S hS D' := by
  intro j Z g W iso
  set C := affineChartSystem B S hS (G.obj j) D Z (g ≫ α.app j) hAffine with hC
  have hL : BigFppfOver.LimitInSite C.siteDiagram := hconv _ Z _ C.diagram C.iso
  have ey : (W ⋙ BigAffineFppf.inclusion B S hS) ⋙ yoneda ≅
      (Over.post G ⋙ C.siteDiagram) ⋙ yoneda :=
    iso ≪≫ stageBaseChangeCartesianIso G α hα j Z g ≪≫
      Functor.isoWhiskerLeft (Over.post G) C.iso.symm
  have e : W ⋙ BigAffineFppf.inclusion B S hS ≅ Over.post G ⋙ C.siteDiagram :=
    (Functor.FullyFaithful.whiskeringRight (Functor.FullyFaithful.ofFullyFaithful yoneda)
      _).preimageIso ey
  exact BigFppfOver.LimitInSite.of_iso (V' := Over.post G ⋙ C.siteDiagram)
    (Functor.isoWhiskerRight e (BigFppfOver.toScheme B S hS))
    (BigFppfOver.LimitInSite.comp_initial (Over.post G) hL)

/-- **The convention passes to a system of inverse images.** Let `τ : G ⋙ D ⟶ const T` be a
natural transformation to a constant system and `V` a subfunctor of `T`. The inverse images of
`V` in the stages of `G ⋙ D` form a cartesian subsystem
(`CategoryTheory.Subfunctor.isPullback_preimageDiagram_map`), so if the stages over `j` are
initial among the stages over `G j`, the convention for `D` gives it for the system of inverse
images. -/
theorem SiteContainsBaseChangeLimits.preimageDiagram {I J : Type u} [Category.{u} I]
    [Category.{u} J] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : J ⥤ I)
    [∀ j : J, (Over.post (X := j) G).Initial] {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (τ : G ⋙ D ⟶ (Functor.const J).obj T) (V : Subfunctor T)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hconv : SiteContainsBaseChangeLimits B S hS D) :
    SiteContainsBaseChangeLimits B S hS (Subfunctor.preimageDiagram τ V) :=
  SiteContainsBaseChangeLimits.of_isPullback G
    { app := fun j => (V.preimage (τ.app j)).ι
      naturality := fun {j k} f => by simp [Subfunctor.preimageDiagram] }
    (fun f => Subfunctor.isPullback_preimageDiagram_map τ V f) hAffine hconv

end Space

end AlgebraicGeometry

end
