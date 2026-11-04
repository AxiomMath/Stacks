module

public import StacksFrontier.CategoryTheory.Sites.Modules.SectionsOverObjectHomotopyCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex

/-!
# Derived Hom out of `j_{U!} O_U` is hypercohomology over `U`

Let `(C, O)` be a ringed site whose objects, morphisms and ring sections share one universe,
and let `U` be an object of `C`.  For an object `E` of the unbounded derived category `D(O)` of
sheaves of `O`-modules and an integer `n`, this file identifies

`Hom_{D(O)}(j_{U!} O_U, E⟦n⟧) ≅ Hⁿ(RΓ(U, E))`,

the degree-`n` hypercohomology of `E` over `U`, and draws the consequence that the left-hand
side vanishes whenever the right-hand side does.

## Why this is here

`Stacks.Sites.ExtensionByZero.sectionsOverObjectHomologyAddEquiv` identifies `Hⁿ(Γ(U, M^•))`
with `Hom_{K(O)}((j_{U!} O_U)[0], M^•⟦n⟧)` in the *homotopy* category, for an arbitrary complex
`M^•`.  Taking `M^• = I^•` K-injective turns both sides into derived-category data with no
further hypothesis: the left side becomes `Hⁿ(RΓ(U, -))` at `I^•`, because the comparison of a
right derived functor is invertible on a K-injective complex
(`Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`); the right side becomes
`Hom_{D(O)}` by `CochainComplex.IsKInjective.Qh_map_bijective`.  Since every object of `D(O)` is
isomorphic to the image of a K-injective complex, the comparison then transports to an arbitrary
`E`.

This is the computation that the local-lifting step of Stacks 08HE (2) ⇒ (1) runs on.  There the
object whose Hom group has to vanish is `(τ^{<n}E)⟦1⟧`, and what makes it vanish is precisely
that its hypercohomology over `U` is zero in the relevant degree; the shape in which that is
consumed is `subsingleton_hom_singleExtensionByZeroUnit_of_isZero`.

## Main definitions

* `Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnit`: the object `j_{U!} O_U` of `D(O)`,
  placed in degree zero.
* `Stacks.Sites.ExtensionByZero.derivedSectionsOverObjectIsoOfIsKInjective`: derived sections
  over `U` of a K-injective complex are its complex of sections over `U`.
* `Stacks.Sites.ExtensionByZero.homologyDerivedSectionsAddEquivOfIsKInjective`: **the
  comparison**, at a K-injective complex.
* `Stacks.Sites.ExtensionByZero.quotientShiftIso`: the localization of a shifted complex is the
  shift of its localization.

## Main results

* `Stacks.Sites.ExtensionByZero.exists_isKInjective_quotient_iso`: every object of `D(O)` is
  isomorphic to the image of a K-injective complex.
* `Stacks.Sites.ExtensionByZero.nonempty_homologyDerivedSectionsAddEquiv`: **the comparison at an
  arbitrary object** of `D(O)`, as an isomorphism of abelian groups
  `Hⁿ(RΓ(U, E)) ≅ Hom_{D(O)}(j_{U!} O_U, E⟦n⟧)`.
* `Stacks.Sites.ExtensionByZero.subsingleton_hom_singleExtensionByZeroUnit_of_isZero`: if
  `Hⁿ(RΓ(U, E))` is a zero object then every morphism `j_{U!} O_U ⟶ E⟦n⟧` in `D(O)` is zero, and
  `Stacks.Sites.ExtensionByZero.subsingleton_hom_cofan_singleExtensionByZeroUnit_of_isZero`: the
  same out of a direct sum of copies of `j_{U!} O_U`.

## Implementation notes

`nonempty_homologyDerivedSectionsAddEquiv` is an existence statement and not a canonical
isomorphism, because the K-injective representative of an object of `D(O)` is produced by
`CategoryTheory.Functor.objPreimage` and is therefore not canonical.  What is canonical is
`homologyDerivedSectionsAddEquivOfIsKInjective`, which is stated at a complex and is the brick
to quote where naturality matters.  The vanishing consequence does not need naturality, which is
why it is derived from the existence form.

Derived sections here are `Stacks.Cohomology.Localization.derivedSectionsOverObject`, with values
in `D(Ab)`: the module structure over `Γ(U, O)` is forgotten before deriving, which is what makes
the target of the comparison a group of morphisms of `D(O)` rather than a module.  The other
derived sections of this development,
`Stacks.Cohomology.HypercohomologyEdge.derivedSections`, is the right derived functor of
`SheafOfModules.evaluation` itself and takes values in `D(Mod Γ(U, O))`.  The two agree after
forgetting the module structure, because `forget₂ (ModuleCat R) AddCommGrpCat` is exact; this is
`Stacks.Cohomology.HypercohomologyEdge.derivedSectionsForgetModuleIso`, with the degreewise form
`Stacks.Cohomology.HypercohomologyEdge.homologyDerivedSectionsForgetModuleIso`.

`subsingleton_hom_cofan_singleExtensionByZeroUnit_of_isZero` takes the coproduct as a colimiting
cofan rather than as `∐`, so that it applies to whatever presentation of `O^{⊕t}` its consumer
has in hand and needs no `HasCoproducts` instance; the index type is arbitrary because the
universal property is all the proof uses.

## References

* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Localization
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Sites.ExtensionByZero

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- `j_{U!} O_U` as an object of the unbounded derived category of `O`-modules, placed in
degree zero. -/
abbrev singleExtensionByZeroUnit :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  DerivedCategory.Q.obj
    ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (extensionByZeroUnitObj X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))

/-- **Derived sections over `U` of a K-injective complex are its sections over `U`.**  The
comparison of a right derived functor is invertible on a K-injective complex, which is
`Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`; the remaining step is that the
localization of the homotopy category of the image complex is the localization of the complex
itself. -/
def derivedSectionsOverObjectIsoOfIsKInjective
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    (derivedSectionsOverObject X U).obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj
            I)) ≅
      DerivedCategory.Q.obj
        (((sectionsOverObjectFunctor X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
  have hγ := derivedUnit_isIsoOnKInjective (homotopySectionsOverObject X U)
    (derivedSectionsOverObject X U)
    ((homotopySectionsOverObject X U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))) I
  (@asIso _ _ _ _ _ hγ).symm ≪≫ (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app _

/-- **The comparison `Hⁿ(RΓ(U, I)) ≅ Hom_{D(O)}(j_{U!} O_U, I⟦n⟧)` at a K-injective complex.**

Three identifications are composed: derived sections of a K-injective complex are its sections
complex (`derivedSectionsOverObjectIsoOfIsKInjective`), whose homology in the derived category is
its homology as a complex; the homology of the complex of sections over `U` is a group of
morphisms out of `j_{U!} O_U` in the *homotopy* category
(`Stacks.Sites.ExtensionByZero.sectionsOverObjectHomologyAddEquiv`, out of Stacks 0G1V); and for
a K-injective target the localization map to the derived category is bijective on morphisms,
which is Stacks 0A64. -/
def homologyDerivedSectionsAddEquivOfIsKInjective
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (n : ℤ) :
    ToType ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedSectionsOverObject X U).obj
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj I)))) ≃+
      (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
              (extensionByZeroUnitObj X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj
            (I⟦n⟧))) :=
  ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
        (derivedSectionsOverObjectIsoOfIsKInjective X U I) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
        _).addCommGroupIsoToAddEquiv).trans
    ((sectionsOverObjectHomologyAddEquiv X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I n).trans
      (qhMapAddEquivOfBijective (CochainComplex.IsKInjective.Qh_map_bijective _ (I⟦n⟧)))))

/-- **Every object of `D(O)` is isomorphic to the image of a K-injective complex.**  Sheaves of
modules on a ringed site form a Grothendieck abelian category, so a complex representing the
object admits a quasi-isomorphism into a K-injective complex (Stacks 079P), and the localization
functor inverts it. -/
theorem exists_isKInjective_quotient_iso
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      I.IsKInjective ∧
      Nonempty (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj I)
          ≅ E) := by
  obtain ⟨I, f, hI, hf⟩ :=
    enoughKInjectives (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (DerivedCategory.Qh.objPreimage E).as
  refine ⟨I, hI, ⟨?_⟩⟩
  have := hI
  have := hf
  exact (@asIso _ _ _ _ _
      (isIso_Qh_map_quotient_map_of_quasiIso
        (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) f)).symm ≪≫
    DerivedCategory.Qh.objObjPreimageIso E

/-- The localization of a shifted complex is the shift of its localization:
`Qh(I⟦n⟧) ≅ Qh(I)⟦n⟧`.  This is the shift compatibility of `DerivedCategory.Q`, read through the
identification of `Q` with the localization of the homotopy category. -/
def quotientShiftIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj
          (I⟦n⟧)) ≅
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj
          I))⟦n⟧ :=
  (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
      (I⟦n⟧) ≪≫
    (DerivedCategory.Q.commShiftIso n).app I ≪≫
    (shiftFunctor
        (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app I).symm

/-- **The comparison `Hⁿ(RΓ(U, E)) ≅ Hom_{D(O)}(j_{U!} O_U, E⟦n⟧)` at an arbitrary object of
`D(O)`**: the degree-`n` hypercohomology of `E` over `U` is the group of morphisms from
`j_{U!} O_U`, placed in degree zero, into `E⟦n⟧`.

This is `homologyDerivedSectionsAddEquivOfIsKInjective` transported along a K-injective
representative of `E`, which exists by `exists_isKInjective_quotient_iso` and is not canonical;
hence the `Nonempty`. -/
theorem nonempty_homologyDerivedSectionsAddEquiv
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) :
    Nonempty (ToType ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedSectionsOverObject X U).obj E)) ≃+
      (singleExtensionByZeroUnit X U ⟶ E⟦n⟧)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_quotient_iso X E
  have := hI
  exact ⟨(((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
      ((derivedSectionsOverObject X U).mapIso e.symm)).addCommGroupIsoToAddEquiv).trans
    ((homologyDerivedSectionsAddEquivOfIsKInjective X U I n).trans
      (Stacks.Injectives.homCongrAddEquiv
        ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
          ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
            (extensionByZeroUnitObj X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)))
        (quotientShiftIso X I n ≪≫
          (shiftFunctor
            (DerivedCategory
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso e)))⟩

/-- **If the degree-`n` hypercohomology of `E` over `U` vanishes then every morphism
`j_{U!} O_U ⟶ E⟦n⟧` of `D(O)` is zero.**  This is the shape in which the comparison is consumed
by the local-lifting step of Stacks 08HE (2) ⇒ (1): the obstruction to lifting a map into the
truncation `τ^{≥n}E` back to `E` lives in such a group, and what kills it is the vanishing of a
hypercohomology group of `τ^{<n}E`. -/
theorem subsingleton_hom_singleExtensionByZeroUnit_of_isZero
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedSectionsOverObject X U).obj E))) :
    Subsingleton (singleExtensionByZeroUnit X U ⟶ E⟦n⟧) := by
  obtain ⟨f⟩ := nonempty_homologyDerivedSectionsAddEquiv X U E n
  have := AddCommGrpCat.subsingleton_of_isZero h
  exact f.symm.toEquiv.subsingleton

/-- **The same for a direct sum of copies of `j_{U!} O_U`.**  If the degree-`n` hypercohomology of
`E` over `U` vanishes then every morphism `⊕ᵢ j_{U!} O_U ⟶ E⟦n⟧` of `D(O)` is zero, for a
coproduct over any index type: two morphisms out of a coproduct agreeing on every summand are
equal, and each summand contributes nothing by
`subsingleton_hom_singleExtensionByZeroUnit_of_isZero`.

This is the `𝒪^{⊕t}` form the local-lifting step of Stacks 08HE (2) ⇒ (1) consumes; the index
type is left arbitrary because the argument does not use finiteness. -/
theorem subsingleton_hom_cofan_singleExtensionByZeroUnit_of_isZero {ι : Type*}
    (c : Cofan (fun _ : ι => singleExtensionByZeroUnit X U)) (hc : IsColimit c)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedSectionsOverObject X U).obj E))) :
    Subsingleton (c.pt ⟶ E⟦n⟧) := by
  have := subsingleton_hom_singleExtensionByZeroUnit_of_isZero X U E n h
  exact ⟨fun a b => Cofan.IsColimit.hom_ext hc a b fun _ => Subsingleton.elim _ _⟩

end Stacks.Sites.ExtensionByZero

end
