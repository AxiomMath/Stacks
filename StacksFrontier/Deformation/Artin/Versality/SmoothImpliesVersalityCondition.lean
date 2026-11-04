module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.Deformation.Artin.Versality.SmoothPredeformation

/-!
# Smoothness and the versality condition of Stacks 07XS

Let `S` be a locally Noetherian scheme and let `p : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred
in groupoids over the big fppf category of `S`. **Stacks 07XW** has two clauses, each concluding
the condition of **Stacks 07XS** — smoothness of the induced functor of predeformation
categories at every finite type field-valued point of the source. The first clause assumes that
`p` is formally smooth on objects, the second that `p` is representable by algebraic spaces and
smooth. The source proves the lemma as a reformulation of Stacks 07WK, of which the two clauses
are cases (1) and (3).

The formally-smooth-on-objects clause is
`Deformation.Artin.isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjects`, which states
it with no hypothesis beyond the source's and carries the `07XW` tag beside its `07WK` one. This
file is the representable-and-smooth clause.

## Main results

* `AlgebraicGeometry.BigFppfOver.isRelativelyFormallySmooth_of_isRelativelySmooth`: a smooth
  1-morphism representable by algebraic spaces whose base changes are representable by schemes
  is formally smooth.
* `Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth_of_representable`:
  **Stacks 07XW**, the representable-and-smooth clause, for a 1-morphism whose base changes are
  representable by schemes.
* `AlgebraicGeometry.BigFppfOver.isRepresentable_of_relativelyRepresentable_relocalizeToYoneda`:
  if the structure morphism `Λ_U F ⟶ h_U` is relatively representable, then `Λ_U F` is
  representable.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 06D3](https://stacks.math.columbia.edu/tag/06D3)
* [Stacks Project, Tag 07WK](https://stacks.math.columbia.edu/tag/07WK)
* [Stacks Project, Tag 07XS](https://stacks.math.columbia.edu/tag/07XS)
* [Stacks Project, Tag 07XW](https://stacks.math.columbia.edu/tag/07XW)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.BigFppfOver

/-- **A smooth 1-morphism representable by algebraic spaces whose base changes are representable
by schemes is formally smooth.** -/
public theorem isRelativelyFormallySmooth_of_isRelativelySmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hsmooth : Stack.IsRelativelySmooth B S hS p)
    (hrep : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (_hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor p))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      yoneda.relativelyRepresentable (OverShriek.relocalizeToYoneda U.hom F)) :
    IsRelativelyFormallySmooth B S hS p := by
  have : (Space.smoothMorphismProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (Space.formallySmoothProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨_, hP⟩ := hsmooth
  intro U y hy F hF hE
  refine (Stack.prop_algebraicSpaceMap_iff B S hS (Space.formallySmoothProperty B S hS)
    U F hF).mpr ?_
  exact (Space.isLocallyOfFinitePresentation_and_formallySmooth_of_isSmooth
    (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom F hF)
    (isAlgebraicSpace_yoneda B S hS U) (hrep U y hy F hF hE)
    ((Stack.prop_algebraicSpaceMap_iff B S hS (Space.smoothMorphismProperty B S hS)
      U F hF).mp (hP U y hy F hF hE))).2

/-- If the structural morphism `Λ_U F ⟶ h_U` of the lower-shriek extension of a presheaf `F` on
the big fppf site of `U` is relatively representable, then `Λ_U F` is itself representable. -/
public theorem isRepresentable_of_relativelyRepresentable_relocalizeToYoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : yoneda.relativelyRepresentable (OverShriek.relocalizeToYoneda U.hom F)) :
    ((OverShriek.relocalizePresheafFunctor U.hom).obj F).IsRepresentable :=
  Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _ hF

end AlgebraicGeometry.BigFppfOver

namespace Deformation.Artin

/-- A 1-morphism `p` of categories fibred in groupoids over the big fppf category of a locally
Noetherian scheme `S` which is representable by algebraic spaces and smooth, and such that each
algebraic space representing a base change of `p` along a scheme-valued point of the target is
representable by schemes (`hrep`), induces a smooth functor of predeformation categories at every
finite type field-valued point of the source. -/
@[stacks 07XW "the representable-and-smooth clause, for a 1-morphism whose base changes along
scheme-valued points of the target are representable by schemes"]
public theorem isSmoothOnPredeformationCategories_of_isRelativelySmooth_of_representable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hsmooth : Stack.IsRelativelySmooth B S hS p)
    (hrep : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (_hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor p))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      yoneda.relativelyRepresentable (OverShriek.relocalizeToYoneda U.hom F)) :
    IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) :=
  isSmoothOnPredeformationCategories_of_isRelativelyFormallySmooth B S hS p
    (hsmooth.elim fun hr _ => hr)
    (BigFppfOver.isRelativelyFormallySmooth_of_isRelativelySmooth B S hS p hsmooth hrep)

namespace OpennessOfVersality

end OpennessOfVersality

end Deformation.Artin

end
