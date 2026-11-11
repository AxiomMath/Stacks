module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageSheafification

/-!
# Colimits and higher direct images on algebraic stacks (Stacks 0GQW)

Stacks 0GQW says that for a quasi-compact and quasi-separated 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks and a filtered system `(ℱ_i)` of abelian sheaves on `𝒳`, the comparison
`colim_i R^p f_* ℱ_i ⟶ R^p f_* (colim_i ℱ_i)` is an isomorphism in every degree `p`, in the
fppf topology and in the étale topology alike.

This file proves the *sheafification step* of that assertion: the step that turns the local
statement — cohomology of the 2-fibres of `f` commutes with the colimit — into the global one.
The local statement is an explicit named hypothesis here; see "What is proved here and where the
rest is" below. Stacks 0GQW itself, at the source's hypotheses, is proved and registered in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfHigherDirectImagesQcqs.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.fibreSections`: the functor whose `p`-th right derived functor is the
  value at an object `y` of `𝒴` of the presheaf of fibre cohomology, namely the inclusion of
  sheaves into presheaves followed by right Kan extension along `f` and evaluation at `y`.

## Main results

* `AlgebraicGeometry.Stack.preservesColimitsOfShape_abelianFibreCohomologyPresheaf`: the presheaf
  of fibre cohomology commutes with a colimit as soon as each of its values does.
* `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage`: the
  conclusion of Stacks 0GQW for an arbitrary one of the five topologies of Stacks 06TP, from the
  assumption that each value of the presheaf of fibre cohomology commutes with the colimit.
* `AlgebraicGeometry.Stack`
  `.preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf` and
  `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_etale`: the
  same in the fppf and in the étale topology, the two assertions the source makes.

## What is proved here and where the rest is

The proof of the source has two steps. First, `R^p f_*` is the sheafification of the presheaf
`y ↦ H^p` of the 2-fibre of `f` over `y`; since sheafification is a left adjoint, it commutes
with all colimits, and the assertion reduces to the same one for that presheaf of cohomology,
hence — colimits of presheaves being computed objectwise — to the same one for each of its
values. Second, each of those values is the cohomology of a quasi-compact and quasi-separated
algebraic stack, so commutes with filtered colimits by Stacks 0GQV.

**The first step is what is proved here, in full.** The identification of `R^p f_*` with the
sheafification of the derived presheaf direct image is the proved half of Stacks 075G,
`AlgebraicGeometry.Stack.abelianHigherDirectImage_iso_sheafify_fibreCohomology`; that derived
presheaf direct image is
`AlgebraicGeometry.Stack.abelianFibreCohomologyPresheaf`, and the reduction of a statement about
it to statements about its values at the objects of `𝒴` is
`CategoryTheory.Limits.preservesColimitsOfShape_of_evaluation` together with the comparison
`CategoryTheory.Functor.rightDerivedCompIso` of the derived functor of a composite — evaluation
of presheaves being exact, the value at `y` of the derived presheaf direct image is the derived
functor of `AlgebraicGeometry.Stack.fibreSections` at `y`.

**The second step is the hypothesis `h` of the results below.** It is discharged, for `f`
quasi-compact and quasi-separated, in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfHigherDirectImagesQcqs.lean`: the value half of
Stacks 075G (`AlgebraicGeometry.Stack.rightDerivedFibreSectionsIso`, using Stacks 06X1 for the
pullback along the first projection of the 2-fibre product) and Stacks 0GQV for the
quasi-compact and quasi-separated 2-fibre products over affine objects. That file proves
**Stacks 0GQW** at the source's hypotheses, as
`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf_of_qcqs`
and `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_etale_of_qcqs`,
and carries the tag.

The results below take `h` for every object of `𝒴` and are stated for an arbitrary diagram
shape; they are the reduction lemmas, not the tag.

## Implementation notes

The instances the statements need — left exact sheafification on the two sites, enough
injectives on abelian sheaves on `𝒳`, and additivity of the direct image — are installed with
`letI` in the statements themselves, exactly as
`AlgebraicGeometry.Stack.abelianHigherDirectImage_iso_sheafify_fibreCohomology` installs them, so
that no instance is carried as a hypothesis. They are all `Prop`-valued classes, so no choice
among them can clash with another.

## References

* [Stacks Project, Tag 0GQW](https://stacks.math.columbia.edu/tag/0GQW)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
* [Stacks Project, Tag 075G](https://stacks.math.columbia.edu/tag/075G)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules

universe u w a v v'

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Presheaf

variable {X Y : Type (u + 1)} [Category.{u} X] [Category.{u} Y]
  (pX : X ⥤ BigFppfOver B S hS) (f : X ⥤ Y) (τ : SiteKind)

/-- The functor of sections over the fibre of `f` at an object `y` of the target: the inclusion
of abelian sheaves on the site associated with `pX` into presheaves, followed by right Kan
extension along `f.op`, followed by evaluation at `y`.

Its `n`-th right derived functor is the value at `y` of the derived presheaf direct image
`AlgebraicGeometry.Stack.abelianFibreCohomologyPresheaf`, by
`AlgebraicGeometry.Stack.preservesColimitsOfShape_abelianFibreCohomologyPresheaf` and the
comparison used in its proof. In the source this functor is global sections of the 2-fibre
product of `f` and `y` composed with pullback along its projection to `𝒳`; that identification
is the value half of Stacks 075G, proved for algebraic stacks as
`AlgebraicGeometry.Stack.rightDerivedFibreSectionsIso` in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfHigherDirectImagesQcqs.lean`. -/
abbrev fibreSections (y : Y) :
    Sheaf (BigFppfOver.associatedTopology B S hS pX τ) AddCommGrpCat.{max (u + 1) a} ⥤
      AddCommGrpCat.{max (u + 1) a} :=
  (sheafToPresheaf (BigFppfOver.associatedTopology B S hS pX τ)
      AddCommGrpCat.{max (u + 1) a} ⋙ f.op.ran) ⋙
    (evaluation Yᵒᵖ AddCommGrpCat.{max (u + 1) a}).obj (op y)

/-- The sections over a fibre of `f` form an additive functor: the inclusion of sheaves into
presheaves and evaluation are additive, and right Kan extension along `f.op` is a right
adjoint. -/
instance additive_fibreSections (y : Y) :
    (fibreSections.{u, a} B S hS pX f τ y).Additive := by
  let := (f.op.ranAdjunction AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
  infer_instance

/-- The derived presheaf direct image commutes with a colimit as soon as each of its values
does.

Colimits of presheaves are computed objectwise, so it is enough to check the assertion after
evaluation at every object `y` of the target; and evaluation of presheaves is exact, so the
value at `y` of the `n`-th derived presheaf direct image is the `n`-th right derived functor of
`AlgebraicGeometry.Stack.fibreSections` at `y`. Nothing about the sites or about the shape of the
diagram is used. -/
theorem preservesColimitsOfShape_abelianFibreCohomologyPresheaf
    [HasSheafify (BigFppfOver.associatedTopology B S hS pX τ) AddCommGrpCat.{max (u + 1) a}]
    [HasInjectiveResolutions (Sheaf (BigFppfOver.associatedTopology B S hS pX τ)
      AddCommGrpCat.{max (u + 1) a})]
    (n : ℕ) {I : Type v} [Category.{v'} I]
    (h : ∀ y : Y, PreservesColimitsOfShape I
      ((fibreSections.{u, a} B S hS pX f τ y).rightDerived n)) :
    PreservesColimitsOfShape I (abelianFibreCohomologyPresheaf.{u, a} B S hS pX f τ n) := by
  refine preservesColimitsOfShape_of_evaluation _ I fun y => ?_
  let := (f.op.ranAdjunction AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
  let := (sheafificationAdjunction (BigFppfOver.associatedTopology B S hS pX τ)
    AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
  have := h y.unop
  exact preservesColimitsOfShape_of_natIso
    (Functor.rightDerivedCompIso
      (sheafToPresheaf (BigFppfOver.associatedTopology B S hS pX τ)
        AddCommGrpCat.{max (u + 1) a} ⋙ f.op.ran)
      ((evaluation Yᵒᵖ AddCommGrpCat.{max (u + 1) a}).obj y) n)

end Presheaf

section AlgebraicStacks

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (τ : SiteKind)

/-- **The sheafification step of Stacks 0GQW, for an arbitrary one of the five topologies of
Stacks 06TP.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` contained
in a big fppf site, let `n` be a degree and let `I` be a diagram shape. If for every object `y`
of the site of `𝒴` the `n`-th derived functor of `AlgebraicGeometry.Stack.fibreSections` at `y`
commutes with colimits of shape `I`, then so does the `n`-th higher direct image `R^n f_*` of
abelian sheaves.

This is the first of the two steps of the source: `R^n f_*` is the sheafification of the derived
presheaf direct image by the proved half of Stacks 075G,
`AlgebraicGeometry.Stack.abelianHigherDirectImage_iso_sheafify_fibreCohomology`, sheafification
is a left adjoint and so commutes with every colimit, and the derived presheaf direct image is
handled objectwise by
`AlgebraicGeometry.Stack.preservesColimitsOfShape_abelianFibreCohomologyPresheaf`.

The hypothesis is the second step of the source; neither quasi-compactness nor
quasi-separatedness of `f` appears, those being what the source uses to obtain it. Stacks 0GQW at
the source's hypotheses is
`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf_of_qcqs`
and its étale form. -/
theorem preservesColimitsOfShape_rightDerived_abelianDirectImage (n : ℕ)
    {I : Type v} [Category.{v'} I]
    (h :
      letI := site_hasSheafify_addCommGrp.{u + 1, u, a}
        (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
        AddCommGrpCat.{max (u + 1) a}
      letI := IsGrothendieckAbelian.enoughInjectives
        (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
          AddCommGrpCat.{max (u + 1) a})
      ∀ y : 𝒴.val.val.obj, PreservesColimitsOfShape I
        ((fibreSections.{u, a} B S hS 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom) τ y).rightDerived n)) :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, a}
      (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    letI := site_hasSheafify_addCommGrp.{u + 1, u, a}
      (J := BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{max (u + 1) a}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
        AddCommGrpCat.{max (u + 1) a})
    letI := abelianDirectImageAdditive.{u, w, a} B S hS f τ
    PreservesColimitsOfShape I
      (((CatFiberedInGroupoids.homFunctor f.hom).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
        (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ)).rightDerived n) := by
  let := site_hasSheafify_addCommGrp.{u + 1, u, a}
    (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
  let := site_hasSheafify_addCommGrp.{u + 1, u, a}
    (J := BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ)
  let := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{max (u + 1) a}
  let := IsGrothendieckAbelian.enoughInjectives
    (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      AddCommGrpCat.{max (u + 1) a})
  let := abelianDirectImageAdditive.{u, w, a} B S hS f τ
  have : PreservesColimitsOfShape I
      (abelianFibreCohomologyPresheaf.{u, a} B S hS 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) τ n) :=
    preservesColimitsOfShape_abelianFibreCohomologyPresheaf.{u, a, v, v'} B S hS
      𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) τ n h
  have : PreservesColimitsOfShape I
      (presheafToSheaf (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ)
        AddCommGrpCat.{max (u + 1) a}) :=
    ((sheafificationAdjunction (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ)
      AddCommGrpCat.{max (u + 1) a}).leftAdjoint_preservesColimits.{v', v}).preservesColimitsOfShape
  exact preservesColimitsOfShape_of_natIso
    (abelianHigherDirectImage_iso_sheafify_fibreCohomology.{u, w, a} B S hS f τ n).symm

/-- **The sheafification step of Stacks 0GQW in the fppf topology.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over a scheme `S` contained in a big fppf site. If for every
object `y` of the fppf site of `𝒴` the `n`-th derived functor of
`AlgebraicGeometry.Stack.fibreSections` at `y` commutes with colimits of shape `I`, then so does
the `n`-th higher direct image `R^n f_*` of abelian fppf sheaves.

This is `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage` at the
fppf topology of Stacks 06TP. It is the first of the two steps of the source's proof; the
hypothesis is the second, and is what quasi-compactness and quasi-separatedness of `f` are used
for. Stacks 0GQW in the fppf topology, at the source's hypotheses, is
`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf_of_qcqs`. -/
theorem preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf (n : ℕ)
    {I : Type v} [Category.{v'} I] [IsFiltered I]
    (h :
      letI := site_hasSheafify_addCommGrp.{u + 1, u, a}
        (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
        AddCommGrpCat.{max (u + 1) a}
      letI := IsGrothendieckAbelian.enoughInjectives
        (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
          AddCommGrpCat.{max (u + 1) a})
      ∀ y : 𝒴.val.val.obj, PreservesColimitsOfShape I
        ((fibreSections.{u, a} B S hS 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom) .fppf y).rightDerived n)) :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, a}
      (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
    letI := site_hasSheafify_addCommGrp.{u + 1, u, a}
      (J := BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .fppf)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{max (u + 1) a}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
        AddCommGrpCat.{max (u + 1) a})
    letI := abelianDirectImageAdditive.{u, w, a} B S hS f .fppf
    PreservesColimitsOfShape I
      (((CatFiberedInGroupoids.homFunctor f.hom).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
        (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .fppf)).rightDerived n) :=
  preservesColimitsOfShape_rightDerived_abelianDirectImage.{u, w, a, v, v'} B S hS f .fppf n h

/-- **The sheafification step of Stacks 0GQW in the étale topology.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over a scheme `S` contained in a big fppf site. If for every
object `y` of the étale site of `𝒴` the `n`-th derived functor of
`AlgebraicGeometry.Stack.fibreSections` at `y` commutes with colimits of shape `I`, then so does
the `n`-th higher direct image `R^n f_*` of abelian étale sheaves.

This is `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage` at the
étale topology of Stacks 06TP. It is the first of the two steps of the source's proof; the
hypothesis is the second, and is what quasi-compactness and quasi-separatedness of `f` are used
for. Stacks 0GQW in the étale topology, at the source's hypotheses, is
`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_etale_of_qcqs`. -/
theorem preservesColimitsOfShape_rightDerived_abelianDirectImage_etale (n : ℕ)
    {I : Type v} [Category.{v'} I] [IsFiltered I]
    (h :
      letI := site_hasSheafify_addCommGrp.{u + 1, u, a}
        (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
      letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
        AddCommGrpCat.{max (u + 1) a}
      letI := IsGrothendieckAbelian.enoughInjectives
        (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
          AddCommGrpCat.{max (u + 1) a})
      ∀ y : 𝒴.val.val.obj, PreservesColimitsOfShape I
        ((fibreSections.{u, a} B S hS 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom) .etale y).rightDerived n)) :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, a}
      (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
    letI := site_hasSheafify_addCommGrp.{u + 1, u, a}
      (J := BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .etale)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{max (u + 1) a}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
        AddCommGrpCat.{max (u + 1) a})
    letI := abelianDirectImageAdditive.{u, w, a} B S hS f .etale
    PreservesColimitsOfShape I
      (((CatFiberedInGroupoids.homFunctor f.hom).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
        (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .etale)).rightDerived n) :=
  preservesColimitsOfShape_rightDerived_abelianDirectImage.{u, w, a, v, v'} B S hS f .etale n h

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
