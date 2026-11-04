module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Sections over an object compute derived sections, naturally

Let `(C, O)` be a ringed site and `U` an object of `C`. On a K-injective complex `I` of
`O`-modules the complex of sections `Γ(U, I)` already computes `RΓ(U, I)`; that comparison is
`Stacks.Cohomology.ModuleSections.sectionsKInjectiveIso`. This file proves that it is **natural
in the complex**, which is the local counterpart of
`Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso_naturality`.

## Main results

* `Stacks.Cohomology.ModuleSections.sectionsKInjectiveIso_naturality`: for a morphism
  `φ : I ⟶ J` of K-injective complexes, the comparison of the complex of sections over `U` with
  derived sections over `U` commutes with `φ`.

## Implementation notes

The comparison is a composite of four components of natural transformations — the localization
comparison `CategoryTheory.DerivedCategory.quotientCompQhIso` at both ends, the factorization of
`CategoryTheory.Functor.mapHomotopyCategory` through
`CategoryTheory.Functor.mapHomologicalComplex`, and the unit of the derived functor — so the
square is those four naturality squares composed, exactly as in the global twin.

Mirroring the global proof verbatim does **not** go through, and the reason is worth recording.
`Stacks.Cohomology.Localization.sectionsOverObject` evaluates the sheaf of modules and then
forgets the module structure, whereas `AlgebraicGeometry.RingedSite.sectionComplex` forgets it
first and then evaluates the underlying sheaf of abelian groups. The two composites agree — that
is `Stacks.Cohomology.ModuleSections.sectionsOverObject_mapHomologicalComplex`, which holds by
`rfl` — but they are different terms, and `rfl`-equality is not enough for `rw`: the object
sitting between two factors of a composition is stored at one spelling and the domain of
`sectionsKInjectiveIso` at the other, so a rewrite either fails to match or produces a motive
that is not type-correct at the transparency `rw` checks it with. The global twin escapes this
only because `Stacks.Cohomology.ModuleSections.moduleGlobalSections` and
`AlgebraicGeometry.RingedSite.globalSectionsComplex` are built from the same functor.

The fix here is to stage the proof: `sectionsKInjectiveIso'` is the same isomorphism with its
domain written in the `Functor.mapHomologicalComplex` spelling throughout, so that all four
naturality squares match syntactically, and the statement about `sectionsKInjectiveIso` is then
the statement about `sectionsKInjectiveIso'` — a single defeq check, performed once, in term
mode. The rewriting-up-to-reducible-unfolding tactic that would paper over the mismatch is
not permitted in this development.

The public statement is spelled with `AlgebraicGeometry.RingedSite.sectionComplexMap`, the
morphism of section complexes induced by a morphism of complexes of modules, because that is the
spelling the consumers of Stacks 0A94 over an object use.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.Cohomology.ModuleSections

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- `sectionsKInjectiveIso` with its domain written as the degreewise image of the complex under
`Stacks.Cohomology.Localization.sectionsOverObject`, rather than as
`AlgebraicGeometry.RingedSite.sectionComplex`.

The two are the same isomorphism; see the implementation notes for why one spelling is needed to
run the proof and the other to state the result. -/
private def sectionsKInjectiveIso' (U : X.C)
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.obj
        (((Localization.sectionsOverObject X U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      (Localization.derivedSectionsOverObject X U).obj (DerivedCategory.Q.obj I) :=
  ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app
        (((Localization.sectionsOverObject X U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)).symm ≪≫
    DerivedCategory.Qh.mapIso
        (((Localization.sectionsOverObject X U).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app I).symm ≪≫
      @asIso _ _ _ _ ((derivedSectionsOverObjectUnit X U).app
            ((HomotopyCategory.quotient
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj I))
          (Localization.derivedUnit_isIsoOnKInjective
            (Localization.homotopySectionsOverObject X U)
            (Localization.derivedSectionsOverObject X U)
            (derivedSectionsOverObjectUnit X U) I) ≪≫
        (Localization.derivedSectionsOverObject X U).mapIso
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app I)

/-- Naturality of `sectionsKInjectiveIso'`: the four constituent naturality squares, composed. -/
private theorem sectionsKInjectiveIso'_naturality (U : X.C)
    (I J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (φ : I ⟶ J) :
    DerivedCategory.Q.map
          (((Localization.sectionsOverObject X U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) ≫
        (sectionsKInjectiveIso' X U J).hom =
      (sectionsKInjectiveIso' X U I).hom ≫
        (Localization.derivedSectionsOverObject X U).map (DerivedCategory.Q.map φ) := by
  have h1 := (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.naturality
    (((Localization.sectionsOverObject X U).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
  have h2 := congrArg (fun t => DerivedCategory.Qh.map t)
    (((Localization.sectionsOverObject X U).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv.naturality φ)
  have h3 := (derivedSectionsOverObjectUnit X U).naturality
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)).map φ)
  have h4 := congrArg (fun t => (Localization.derivedSectionsOverObject X U).map t)
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.naturality φ)
  dsimp only [sectionsKInjectiveIso', Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Functor.comp_map] at h2 h3 h4 ⊢
  simp only [Functor.map_comp, Category.assoc] at h2 h3 h4 ⊢
  rw [← Category.assoc, h1, Category.assoc]
  dsimp only [Functor.comp_map]
  rw [reassoc_of% h2, reassoc_of% h3, h4]

/-- **`sectionsKInjectiveIso` is natural in the complex.** For a morphism `φ : I ⟶ J` of
K-injective complexes, the comparison of the complex of sections over `U` with derived sections
over `U` commutes with `φ`.

This is the local counterpart of `globalSectionsKInjectiveIso_naturality`, proved the same way
from the naturality of the four transformations the comparison is composed of. -/
theorem sectionsKInjectiveIso_naturality (U : X.C)
    (I J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (φ : I ⟶ J) :
    DerivedCategory.Q.map (RingedSite.sectionComplexMap X U φ) ≫
        (sectionsKInjectiveIso X U J).hom =
      (sectionsKInjectiveIso X U I).hom ≫
        (Localization.derivedSectionsOverObject X U).map (DerivedCategory.Q.map φ) :=
  sectionsKInjectiveIso'_naturality X U I J φ

end Stacks.Cohomology.ModuleSections

end
