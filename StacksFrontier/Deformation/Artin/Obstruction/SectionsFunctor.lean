module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsLift
public import StacksFrontier.CategoryTheory.Sites.Stack.PresheafElementsStack
public import StacksFrontier.Deformation.Artin.Obstruction.Theory

/-!
# The functor of sections of a pulled-back quasi-coherent module, and its fibred category

Let `S` be a scheme, let `q : W → S` be a morphism of schemes and let `𝓕` be a quasi-coherent
`𝒪_W`-module. Consider
```
F : (Sch/S)_{fppf}^{opp} ⟶ Sets,   T/S ↦ H⁰(W_T, 𝓕_T)
```
where `W_T = T ×_S W` and `𝓕_T` is the pullback of `𝓕` to `W_T`. This file defines `F` and its
category of elements `𝒳`, a category fibred in groupoids over the big fppf site of `S`, and
characterizes when an object of `𝒳` lifts across a deformation situation.

## Main definitions

* `Deformation.Artin.SectionsSheaf.baseChangeOver` — the base-change functor
  `Sch/S ⥤ Sch/W`, `T ↦ (W_T → W)`.
* `Deformation.Artin.SectionsSheaf.sectionsPresheafOver` — the functor `F` on all schemes over
  `S`: `T ↦ H⁰(W_T, 𝓕_T)`.
* `Deformation.Artin.SectionsSheaf.sectionsPresheaf` — the same on the big fppf site over `S`,
  valued in types.
* `Deformation.Artin.SectionsSheaf.sectionsFibredCategory` — the category of elements `𝒳` of
  `F`, projected to the site; it is fibred in sets, hence in groupoids.

## Main results

* `Deformation.Artin.SectionsSheaf.sectionsPresheafOver_obj` and
  `Deformation.Artin.SectionsSheaf.sectionsPresheaf_obj`: the value at `T` is
  `H⁰(W_T, 𝓕_T)`, on the nose.
* `Deformation.Artin.SectionsSheaf.sectionsPresheafOver_map`: the restriction map along
  `T' → T` is the canonical pullback map on global sections, on the nose.
* `Deformation.Artin.SectionsSheaf.hasLift_iff_exists_section_sectionsPresheaf`: an object of
  `𝒳` lifts across a deformation situation, in the sense of
  `Deformation.Artin.AffineObject.HasLift`, exactly when the section of `𝓕_A` it names is the
  restriction of a section of `𝓕_{A'}`.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 04TM](https://stacks.math.columbia.edu/tag/04TM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Deformation.Artin.SectionsSheaf

variable {S W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules) [𝓕.IsQuasicoherent]

/-- The base change `T ↦ W_T = T ×_S W`, as a functor from schemes over `S` to schemes over `W`:
its value at `T` is `W_T` with its projection to `W`. -/
abbrev baseChangeOver : Over S ⥤ Over W := Over.pullback q

/-- The functor `T/S ↦ H⁰(W_T, 𝓕_T)` on all schemes over `S`, with its canonical pullback
restriction maps: the base change `T ↦ W_T` followed by the presheaf of sections of the pullbacks
of `𝓕`. -/
def sectionsPresheafOver : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (baseChangeOver q).op ⋙ AlgebraicGeometry.quasiCoherentPresheafFunctor W 𝓕

/-- The value of `Deformation.Artin.SectionsSheaf.sectionsPresheafOver` at `T/S` is the group of
global sections of `𝓕_T` on `W_T`. -/
theorem sectionsPresheafOver_obj (T : Over S) :
    (sectionsPresheafOver q 𝓕).obj (op T) =
      AddCommGrpCat.of Γ((Scheme.Modules.pullback (pullback.snd T.hom q)).obj 𝓕, ⊤) :=
  rfl

/-- The restriction map of `Deformation.Artin.SectionsSheaf.sectionsPresheafOver` along `T' ⟶ T`
is the canonical pullback map on global sections along `W_{T'} ⟶ W_T`. -/
theorem sectionsPresheafOver_map {T T' : Over S} (α : T' ⟶ T) :
    (sectionsPresheafOver q 𝓕).map α.op =
      AlgebraicGeometry.pullbackSectionsMap 𝓕 ((baseChangeOver q).map α) :=
  rfl

section Site

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains S)

/-- The big fppf category over `S`, viewed as a category of schemes over `S`. -/
abbrev siteToOver : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S :=
  Over.post B.inclusion

/-- The functor `T/S ↦ H⁰(W_T, 𝓕_T)` on the big fppf site over `S`, valued in types. -/
def sectionsPresheaf : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (siteToOver B hS).op ⋙ sectionsPresheafOver q 𝓕 ⋙ forget AddCommGrpCat.{u}

/-- The value of `Deformation.Artin.SectionsSheaf.sectionsPresheaf` at an object `T` of the big
fppf site is `H⁰(W_T, 𝓕_T)`. -/
theorem sectionsPresheaf_obj (T : AlgebraicGeometry.BigFppfOver B S hS) :
    (sectionsPresheaf q 𝓕 B hS).obj (op T) =
      Γ((Scheme.Modules.pullback (pullback.snd (B.inclusion.map T.hom) q)).obj 𝓕, ⊤) :=
  rfl

/-- The category fibred in groupoids `𝒳` attached to
`Deformation.Artin.SectionsSheaf.sectionsPresheaf`: its category of elements, projected to the
big fppf site over `S`. Its fibre over `T` is `H⁰(W_T, 𝓕_T)`, so it is fibred in sets and hence
in groupoids. -/
abbrev sectionsFibredCategory :=
  PresheafOfCategories.discreteProjection (sectionsPresheaf q 𝓕 B hS)

/-- An object of `𝒳` over `Spec A`, that is, a section of `𝓕_A` on `W_A`, lifts across a
deformation situation `A' → A`, in the sense of `Deformation.Artin.AffineObject.HasLift`, exactly
when the section it names is the restriction of a section of `𝓕_{A'}` on `W_{A'}`. -/
theorem hasLift_iff_exists_section_sectionsPresheaf
    (Q : Deformation.Artin.AffineObject B S hS
      (PresheafOfCategories.discreteProjection (sectionsPresheaf q 𝓕 B hS)))
    (t : Deformation.Artin.DeformationSituation B S hS Q.alg) :
    Deformation.Artin.AffineObject.HasLift
        (Functor.IsFiberedInSets.isFiberedInGroupoids
          (PresheafOfCategories.discreteProjection (sectionsPresheaf q 𝓕 B hS))) Q t ↔
      ∃ s' : (sectionsPresheaf q 𝓕 B hS).obj (op t.top.over),
        (sectionsPresheaf q 𝓕 B hS).map t.hom.specMap.op s' =
          PresheafOfCategories.discreteFiberEquiv
            (sectionsPresheaf q 𝓕 B hS) Q.alg.over Q.obj :=
  PresheafOfCategories.nonempty_iso_pullbackFunctor_obj_iff
    (sectionsPresheaf q 𝓕 B hS) t.hom.specMap Q.obj

end Site

end Deformation.Artin.SectionsSheaf

end
