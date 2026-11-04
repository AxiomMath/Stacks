module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizationBaseChange

/-! # The square of Stacks 04H1 is compatible with base change

Let `f : E ⟶ D` be a morphism of topoi and let `b : G' ⟶ G` be a morphism of `D`.  Stacks 04H1
produces, for each object of `D`, a morphism of topoi `f' : E/f⁻¹G ⟶ D/G` together with the
commutativity `j_{f⁻¹G}⁻¹ ∘ f⁻¹ ≅ j_G⁻¹ ∘ (f')⁻¹` of its square on inverse images
(`MorphismOfTopoi.inverseImageCompToOverIso`, which is the comparison of `f⁻¹`
with binary products packaged as a morphism of slices).  This file proves that the two
commutativities obtained at `G` and at `G'` agree once both are read in `E/f⁻¹G'`: restricting
the one at `G` along the relocalization at `f⁻¹b` is the one at `G'`, the two being compared by
Beck–Chevalley for `Over.post f⁻¹` (`CategoryTheory.Over.postPullbackIso`) and by the identity
`j_{U/U'}⁻¹ ∘ j_{U'}⁻¹ = j_U⁻¹` of Stacks 03EH (`CategoryTheory.toOverCompPullbackIso`).

This is the naturality in the target sheaf of 04H1's square, and it is the one input the
localized morphisms of Stacks 04IF need in order to be compared over a change of the sheaf on
the target.

Everything is proved on underlying objects, where the statement becomes a comparison of first
projections: both sides are morphisms of `E/f⁻¹G'` into `(f')⁻¹(H ⊗ G')`, so their second
components agree because both are the structure morphism, and `f⁻¹` carries `H ⊗ G'` to a
product, so the first components determine them.

## Main results

* `MorphismOfTopoi.inverseImageCompToOverIso_hom_app_left_counit`: the first
  projection of the comparison of Stacks 04H1 is the first projection.
* `MorphismOfTopoi.overPostToOver_hom_ext`: two morphisms into
  `Over.post f⁻¹ (H ⊗ G)` agree as soon as their first projections do.
* `MorphismOfTopoi.inverseImageCompToOverIso_baseChange`: the compatibility of
  Stacks 04H1's square with base change along `b : G' ⟶ G`.
-/

@[expose] public section

namespace MorphismOfTopoi

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe v v' u u'

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

variable {E : Type u} [Category.{v} E] {D : Type u'} [Category.{v'} D]
  [HasPullbacks E] [HasPullbacks D] [CartesianMonoidalCategory E]
  [CartesianMonoidalCategory D] (f : MorphismOfTopoi E D)

omit [HasPullbacks E] in
/-- The first projection of **Stacks 04H1**'s comparison of inverse images: the comparison
`f⁻¹H ⊗ f⁻¹G ⟶ f⁻¹(H ⊗ G)` followed by `f⁻¹` of the first projection is the first projection.

The comparison is the monoidal structure map `μ` of the left exact functor `f⁻¹`, so this is
`CategoryTheory.Functor.Monoidal.μ_fst`.  The projections are written as counits of
`CategoryTheory.forgetAdjToOver`, the form in which they occur as components of morphisms of
slice categories. -/
theorem inverseImageCompToOverIso_hom_app_left_counit (G H : D) :
    ((f.inverseImageCompToOverIso G).hom.app H).left ≫
        f.inverseImage.map ((forgetAdjToOver G).counit.app H) =
      (forgetAdjToOver (f.inverseImage.obj G)).counit.app (f.inverseImage.obj H) := by
  let : f.inverseImage.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  exact Functor.Monoidal.μ_fst f.inverseImage H G

omit [HasPullbacks E] [HasPullbacks D] in
/-- Two morphisms of `E/f⁻¹B` into `(f')⁻¹(A ⊗ B) = Over.post f⁻¹ (A ⊗ B)` agree as soon as
their first projections agree.

Since `f⁻¹` is left exact, `f⁻¹(A ⊗ B)` is a product of `f⁻¹A` and `f⁻¹B`, compared with the
chosen one by the monoidal structure map of `f⁻¹`; the second projections of the two morphisms
agree because both are the structure morphism of the source. -/
theorem overPostToOver_hom_ext {A B : D} {P : Over (f.inverseImage.obj B)}
    {α β : P ⟶ (Over.post f.inverseImage).obj ((toOver B).obj A)}
    (h : α.left ≫ f.inverseImage.map ((forgetAdjToOver B).counit.app A) =
      β.left ≫ f.inverseImage.map ((forgetAdjToOver B).counit.app A)) : α = β := by
  let : f.inverseImage.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  have efst : (Functor.Monoidal.μIso f.inverseImage A B).inv ≫ fst _ _ =
      f.inverseImage.map (fst A B) := by
    rw [← Functor.Monoidal.μ_fst f.inverseImage A B]; simp
  have esnd : (Functor.Monoidal.μIso f.inverseImage A B).inv ≫ snd _ _ =
      f.inverseImage.map (snd A B) := by
    rw [← Functor.Monoidal.μ_snd f.inverseImage A B]; simp
  refine Over.OverMorphism.ext
    ((cancel_mono (Functor.Monoidal.μIso f.inverseImage A B).inv).1
      (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_))
  · erw [Category.assoc, Category.assoc, efst]
    exact h
  · erw [Category.assoc, Category.assoc, esnd]
    exact (Over.w α).trans (Over.w β).symm

/-- The compatibility of Stacks 04H1's square with base change, on underlying objects and
followed by the first projection.

Both composites are computed to be the first projection of
`f⁻¹H ⊗ f⁻¹G ×_{f⁻¹G} f⁻¹G'` followed by the first projection of `f⁻¹H ⊗ f⁻¹G`: on the left by
Stacks 03EH's identity for `b`, by Beck–Chevalley for `Over.post f⁻¹` and by the hypothesis on
`m`, on the right by the hypothesis on `m'` and Stacks 03EH's identity for `f⁻¹b`. -/
private theorem inverseImageCompToOverIso_baseChange_left {G G' : D} (b : G' ⟶ G) (H : D)
    (m : (toOver (f.inverseImage.obj G)).obj (f.inverseImage.obj H) ⟶
      (Over.post f.inverseImage).obj ((toOver G).obj H))
    (m' : (toOver (f.inverseImage.obj G')).obj (f.inverseImage.obj H) ⟶
      (Over.post f.inverseImage).obj ((toOver G').obj H))
    (hm : m.left ≫ f.inverseImage.map ((forgetAdjToOver G).counit.app H) =
      (forgetAdjToOver (f.inverseImage.obj G)).counit.app (f.inverseImage.obj H))
    (hm' : m'.left ≫ f.inverseImage.map ((forgetAdjToOver G').counit.app H) =
      (forgetAdjToOver (f.inverseImage.obj G')).counit.app (f.inverseImage.obj H)) :
    ((Over.pullback (f.inverseImage.map b)).map m).left ≫
        ((Over.postPullbackIso f.inverseImage b).inv.app ((toOver G).obj H)).left ≫
        ((Over.post f.inverseImage).map ((toOverCompPullbackIso b).hom.app H)).left ≫
        f.inverseImage.map ((forgetAdjToOver G').counit.app H) =
      ((toOverCompPullbackIso (f.inverseImage.map b)).hom.app (f.inverseImage.obj H)).left ≫
        m'.left ≫ f.inverseImage.map ((forgetAdjToOver G').counit.app H) := by
  have hb := forget_map_toOverCompPullbackIso_hom_app b H
  have hfb := forget_map_toOverCompPullbackIso_hom_app (f.inverseImage.map b)
    (f.inverseImage.obj H)
  have hpost : ((Over.post f.inverseImage).map ((toOverCompPullbackIso b).hom.app H)).left ≫
      f.inverseImage.map ((forgetAdjToOver G').counit.app H) =
      f.inverseImage.map (pullback.fst ((toOver G).obj H).hom b) ≫
        f.inverseImage.map ((forgetAdjToOver G).counit.app H) :=
    ((f.inverseImage.map_comp _ _).symm.trans
      (congrArg f.inverseImage.map hb)).trans (f.inverseImage.map_comp _ _)
  calc ((Over.pullback (f.inverseImage.map b)).map m).left ≫
          ((Over.postPullbackIso f.inverseImage b).inv.app ((toOver G).obj H)).left ≫
          ((Over.post f.inverseImage).map ((toOverCompPullbackIso b).hom.app H)).left ≫
          f.inverseImage.map ((forgetAdjToOver G').counit.app H)
      = ((Over.pullback (f.inverseImage.map b)).map m).left ≫
          ((Over.postPullbackIso f.inverseImage b).inv.app ((toOver G).obj H)).left ≫
          f.inverseImage.map (pullback.fst ((toOver G).obj H).hom b) ≫
          f.inverseImage.map ((forgetAdjToOver G).counit.app H) :=
        congrArg (fun z => ((Over.pullback (f.inverseImage.map b)).map m).left ≫
          ((Over.postPullbackIso f.inverseImage b).inv.app ((toOver G).obj H)).left ≫ z) hpost
    _ = ((Over.pullback (f.inverseImage.map b)).map m).left ≫
          pullback.fst (f.inverseImage.map ((toOver G).obj H).hom) (f.inverseImage.map b) ≫
          f.inverseImage.map ((forgetAdjToOver G).counit.app H) :=
        congrArg (fun z => ((Over.pullback (f.inverseImage.map b)).map m).left ≫ z)
          (PreservesPullback.iso_inv_fst_assoc ..)
    _ = (pullback.fst ((toOver (f.inverseImage.obj G)).obj (f.inverseImage.obj H)).hom
            (f.inverseImage.map b) ≫ m.left) ≫
          f.inverseImage.map ((forgetAdjToOver G).counit.app H) :=
        pullback.lift_fst_assoc ..
    _ = pullback.fst ((toOver (f.inverseImage.obj G)).obj (f.inverseImage.obj H)).hom
            (f.inverseImage.map b) ≫
          (forgetAdjToOver (f.inverseImage.obj G)).counit.app (f.inverseImage.obj H) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun z => pullback.fst
            ((toOver (f.inverseImage.obj G)).obj (f.inverseImage.obj H)).hom
            (f.inverseImage.map b) ≫ z) hm)
    _ = ((toOverCompPullbackIso (f.inverseImage.map b)).hom.app (f.inverseImage.obj H)).left ≫
          m'.left ≫ f.inverseImage.map ((forgetAdjToOver G').counit.app H) :=
        ((congrArg (fun z => ((toOverCompPullbackIso
          (f.inverseImage.map b)).hom.app (f.inverseImage.obj H)).left ≫ z) hm').trans hfb).symm

/-- **Stacks 04H1, compatibility of the square on inverse images with base change.**  Let
`b : G' ⟶ G` be a morphism of the target topos.  Restricting the comparison
`j_{f⁻¹G}⁻¹ ∘ f⁻¹ ≅ j_G⁻¹ ∘ (f')⁻¹` at `G` along the relocalization `j_{f⁻¹G'/f⁻¹G}⁻¹`, and then
comparing with the square at `G'` by Beck–Chevalley for `Over.post f⁻¹` and by Stacks 03EH's
identity `j_{U/U'}⁻¹ ∘ j_{U'}⁻¹ = j_U⁻¹`, gives the comparison at `G'`:
```
  j_{f⁻¹G'/f⁻¹G}⁻¹(04H1 at G) ≫ Beck–Chevalley ≫ (f')⁻¹(03EH at b)
    = (03EH at f⁻¹b) ≫ (04H1 at G') .
```
This is the naturality of Stacks 04H1's square in the sheaf on the target. -/
theorem inverseImageCompToOverIso_baseChange {G G' : D} (b : G' ⟶ G) (H : D) :
    (Over.pullback (f.inverseImage.map b)).map ((f.inverseImageCompToOverIso G).hom.app H) ≫
        (Over.postPullbackIso f.inverseImage b).inv.app ((toOver G).obj H) ≫
        (Over.post f.inverseImage).map ((toOverCompPullbackIso b).hom.app H) =
      (toOverCompPullbackIso (f.inverseImage.map b)).hom.app (f.inverseImage.obj H) ≫
        (f.inverseImageCompToOverIso G').hom.app H :=
  f.overPostToOver_hom_ext (((Category.assoc _ _ _).trans
    (congrArg (fun z =>
      ((Over.pullback (f.inverseImage.map b)).map
        ((f.inverseImageCompToOverIso G).hom.app H)).left ≫ z) (Category.assoc _ _ _))).trans
    ((f.inverseImageCompToOverIso_baseChange_left b H _ _
      (f.inverseImageCompToOverIso_hom_app_left_counit G H)
      (f.inverseImageCompToOverIso_hom_app_left_counit G' H)).trans (Category.assoc _ _ _).symm))

end MorphismOfTopoi
