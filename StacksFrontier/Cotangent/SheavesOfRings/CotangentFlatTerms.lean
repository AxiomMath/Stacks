module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafDifferentials
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The terms of the cotangent complex of a morphism of sheaves of rings are flat

Let `f : A ⟶ B` be a morphism of sheaves of commutative rings on a site. The terms of the
simplicial sheaf of `B`-modules `Ω_{P_•/A} ⊗_{P_•} B` of [Stacks, Tag 08SS] are flat.

Every term `P_n` of the standard resolution is a free `A`-algebra sheaf on a sheaf of sets, so
its sheaf of relative differentials is the free sheaf of `P_n`-modules on that sheaf of sets
(`CategoryTheory.Sheaf.freeAlgebraSheafDifferentialsIso`), hence flat; and extension of scalars
along the augmentation `P_n ⟶ B` takes a flat sheaf of modules to a flat sheaf of modules by
[Stacks, Tag 05V4].

## Main results

* `CategoryTheory.Sheaf.standardResolution_obj_free`: every term of the standard resolution is
  a free `A`-algebra sheaf.
* `CategoryTheory.Sheaf.isFlat_resolutionDifferentials`: the sheaf of relative differentials of
  a term of the standard resolution is flat.
* `CategoryTheory.Sheaf.cotangentSimplicialModuleObjIso`: the degree-`n` term of the
  base-changed simplicial module is the extension of scalars of those differentials along the
  augmentation.
* `CategoryTheory.Sheaf.isFlat_cotangentSimplicialModule_obj`: **the terms of
  `Ω_{P_•/A} ⊗_{P_•} B` are flat.**

## Implementation notes

`CategoryTheory.Sheaf.cotangentSimplicialModule` is a choice of corepresentation of the
`A`-derivations of the standard resolution, so its terms are not given by a formula. The
identification with the extension of scalars is therefore made the only way available: both
corepresent the same functor of sheaves of `B`-modules — the first by its defining
`derivationEquiv`, the second by composing the extension–restriction adjunction of [Stacks, Tag
03CZ] with the corepresentation of [Stacks, Tag 04BL] — and
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso` compares them.

Extension of scalars has two spellings in this development: the one of
`Stacks.Sheaves.RingedToposModules.extendScalars`, used in the construction of
`CategoryTheory.Sheaf.cotangentSimplicialModule`, and `Stacks.FlatChangeOfRings.extendScalars`,
which is the one Tag 05V4 is proved for. No comparison between them is needed here: what is
used of either is only that it is left adjoint to restriction of scalars along the augmentation,
and the corepresentation above is built from the second adjunction directly.

## References

* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex
  of a morphism of sheaves of rings.
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR), the standard
  resolution.
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4), flatness under
  extension of scalars.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), corepresentability of
  the functor of relative derivations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry.SheafOfModules (derivationsFunctor)

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- **Every term of the standard resolution is a free `A`-algebra sheaf**, namely the free
`A`-algebra on the underlying sheaf of sets of the `n`-fold iterate of the free–forgetful
comonad at `B`. -/
theorem standardResolution_obj_free (n : ℕ) :
    (standardResolution J f).left.obj (op ⦋n⦌) =
      (freeAlgebraSheaf J A).obj ((forgetAlgebraSheaf J A).obj
        ((((standardResolutionComonad J A : Comonad (Under A)) :
          Under A ⥤ Under A).iterate n).obj (Under.mk f))) := by
  rw [standardResolution_obj]; rfl

/-- **The sheaf of relative differentials of a term of the standard resolution is flat.** The
term is a free `A`-algebra sheaf, so its differentials are free on its sheaf of generators. -/
theorem isFlat_resolutionDifferentials (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v w, max u v w}
      (O := resolutionTerm J f (op ⦋n⦌)) (resolutionDifferentials J f (op ⦋n⦌)) := by
  have key : ∀ (X : Under A) (E : Sheaf J (Type (max u v w))),
      X = (freeAlgebraSheaf J A).obj E →
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v w, max u v w} (O := X.right)
        (derivationsFunctor.{max u v w} A X.right X.hom).coreprX := by
    rintro X E rfl
    have h := isFlat_freeAlgebraSheafDifferentials J A E
    exact h
  exact key _ _ (standardResolution_obj_free J f n)

/-- The functor of `A`-derivations of the degree-`n` term of the standard resolution, read on
sheaves of `B`-modules through the augmentation. This is the functor the degree-`n` term of
`Ω_{P_•/A} ⊗_{P_•} B` corepresents. -/
noncomputable abbrev resolutionDerivationsFunctor (n : SimplexCategoryᵒᵖ) :
    targetModules J B ⥤ Type (max u v w) :=
  SheafOfModules.restrictScalars (resolutionAugmentationRing J f n) ⋙
    derivationsFunctor.{max u v w} A (resolutionTerm J f n) (resolutionBase J f n)

/-- The degree-`n` term of the base-changed simplicial module corepresents the `A`-derivations
of the degree-`n` term of the standard resolution. This is its defining property. -/
noncomputable def cotangentSimplicialModuleCorepresentableBy (n : SimplexCategoryᵒᵖ) :
    (resolutionDerivationsFunctor J f n).CorepresentableBy
      ((cotangentSimplicialModule.{u, v, w} J f).object.obj n) where
  homEquiv {M} := (cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n M
  homEquiv_comp g k := (cotangentSimplicialModule.{u, v, w} J f).naturality n k g

/-- **The extension of scalars of the differentials along the augmentation corepresents the
same derivations**: that is the universal property of `Ω_{P_n/A} ⊗_{P_n} B`, obtained by
composing the extension–restriction adjunction with the corepresentation of the derivations. -/
noncomputable def extendScalarsDifferentialsCorepresentableBy (n : SimplexCategoryᵒᵖ) :
    (resolutionDerivationsFunctor J f n).CorepresentableBy
      ((Stacks.FlatChangeOfRings.extendScalars (resolutionAugmentation J f n)).obj
        (resolutionDifferentials J f n)) where
  homEquiv {M} :=
    ((Stacks.FlatChangeOfRings.extendScalarsAdjunction
        (resolutionAugmentation J f n)).homEquiv (resolutionDifferentials J f n) M).trans
      (derivationsFunctor.{max u v w} A (resolutionTerm J f n)
        (resolutionBase J f n)).corepresentableBy.homEquiv
  homEquiv_comp {M N} g k := by
    refine Eq.trans (congrArg (fun z => (derivationsFunctor.{max u v w} A
        (resolutionTerm J f n) (resolutionBase J f n)).corepresentableBy.homEquiv z)
      (Adjunction.homEquiv_naturality_right
        (Stacks.FlatChangeOfRings.extendScalarsAdjunction (resolutionAugmentation J f n))
        k g)) ?_
    exact (derivationsFunctor.{max u v w} A (resolutionTerm J f n)
      (resolutionBase J f n)).corepresentableBy.homEquiv_comp _ _

/-- **The degree-`n` term of the base-changed simplicial module is the extension of scalars of
the differentials of `P_n` along the augmentation**, both corepresenting the `A`-derivations
of `P_n`. -/
noncomputable def cotangentSimplicialModuleObjIso (n : SimplexCategoryᵒᵖ) :
    (cotangentSimplicialModule.{u, v, w} J f).object.obj n ≅
      (Stacks.FlatChangeOfRings.extendScalars (resolutionAugmentation J f n)).obj
        (resolutionDifferentials J f n) :=
  (cotangentSimplicialModuleCorepresentableBy J f n).uniqueUpToIso
    (extendScalarsDifferentialsCorepresentableBy J f n)

/-- **The terms of the simplicial sheaf of `B`-modules `Ω_{P_•/A} ⊗_{P_•} B` are flat.** The
differentials of a term of the standard resolution are free on its sheaf of generators, and
extension of scalars preserves flatness. -/
theorem isFlat_cotangentSimplicialModule_obj (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v w, max u v w} (O := B)
      ((cotangentSimplicialModule.{u, v, w} J f).object.obj (op ⦋n⦌)) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso B
    (cotangentSimplicialModuleObjIso J f (op ⦋n⦌)).symm
    (Stacks.FlatChangeOfRings.isFlat_extendScalars (resolutionAugmentation J f (op ⦋n⦌)) _
      (isFlat_resolutionDifferentials J f n))

end CategoryTheory.Sheaf

end
