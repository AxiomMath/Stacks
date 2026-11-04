module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering

/-!
# The cohomology of derived sections on the complement of a zero locus

Let `A` be a commutative ring, `I ⊆ A` an ideal and `U = Spec A \ V(I)`. Derived sections
`RΓ(U, -)` on `U` are built in
`StacksFrontier/RingTheory/LocalCohomology/AffineLocalizationTriangle.lean` as the total right
derived functor of sections over `U` on the *unbounded* derived category of sheaves of modules on
`Spec A`, which is the form the localization triangle of Stacks 0DWR needs. Sheaf cohomology, on
the other hand, is everywhere else in the repository the `ℕ`-indexed right derived functor of
sections: Mathlib's `CategoryTheory.Functor.rightDerived`, in the abelian-group-valued spelling
`Hgroup` for which the vanishing theorems — Serre vanishing on an affine open among them — are
stated.

This file identifies the two, in every degree and for every sheaf of modules on `Spec A`:

`Hⁿ(RΓ(U, F)) ≅ Hⁿ(U, F)`,

the right-hand side read as an `A`-module through `A ⟶ Γ(U, 𝒪)`. Nothing here is specific to the
complement of a zero locus; what is specific is that `RΓ(U, -)` exists on the unbounded derived
category, which is why `U` is taken to be that open.

The identification is a composite of three existing comparisons, each of which reconciles one
discrepancy between the two sides.

* The unbounded derived functor against the classical one. A right derived functor on the
  unbounded derived category, applied to an object placed in degree zero, has the classical
  right derived functors as its cohomology:
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`. Its hypothesis is the
  existence of K-injective resolutions, which sheaves of modules on a scheme have because they
  form a Grothendieck abelian category.
* The coefficients. Sections over `U` are taken here as `A`-modules, by restriction of scalars
  along `A ⟶ Γ(U, 𝒪)`; the Čech and sheaf-cohomology machinery takes them as `Γ(U, 𝒪)`-modules.
  Restriction of scalars is exact, so it may be pulled out of a right derived functor:
  `CategoryTheory.Functor.rightDerivedCompIso`.
* The indexing. The Čech comparison of Stacks 01EQ lands in the bounded-below derived category,
  whose `ℤ`-indexed cohomology is the `ℕ`-indexed classical one in non-negative degrees:
  `Stacks.DerivedIndexing.rightDerivedIso`.

## Main definitions

* `Stacks.LocalCohomology.homologyDerivedSectionsNatIsoRightDerived` — `Hⁿ(RΓ(U, -))` is the
  classical right derived functor of sections over `U`.
* `Stacks.LocalCohomology.rightDerivedSectionsOnAffineComplementIso'` — the same with the
  coefficients changed back to `Γ(U, 𝒪)`.
* `Stacks.LocalCohomology.rightDerivedEvaluationComplementIsoPlus` — the same against the
  bounded-below derived global sections that the Čech comparison uses.
* `Stacks.LocalCohomology.homologyDerivedSectionsIsoDerivedGlobalSections` — the composite.

## Main results

* `Stacks.LocalCohomology.isZero_homology_derivedSectionsOnAffineComplement_iff` — the degree-`n`
  cohomology of `RΓ(U, F)` vanishes exactly when the sheaf cohomology group `Hⁿ(U, F)` does.
  This is what makes every vanishing theorem stated for `Hgroup` — Serre vanishing on an affine
  open, and the vanishing above the dimension of the support — a statement about derived sections
  on `U`.

## Implementation notes

No `@[stacks]` attribute is placed here. The higher-degree half of Stacks 0DWR asks for
`Hⁿ(U, M̃|U) ≅ H^{n+1}_{V(I)}(M)`; what this file supplies is the left-hand side, identified with
the cohomology of the *derived sections functor*. The identification of the third term of the
localization triangle — which `Stacks.LocalCohomology.cechComplementFunctor` builds from the
*algebraic* Čech complex of a generating family of `I` — with derived sections on `U` is proved,
as an isomorphism of abelian groups, in
`StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.HgroupAndCechComplement`. What Stacks
0DWR asserts is an isomorphism of `A`-modules, which for a general finitely generated `I` is
still open; see the implementation notes of
`StacksFrontier/RingTheory/LocalCohomology/ComplementCohomology.lean`, which supplies the degree
bookkeeping on the other side.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I : Ideal A)

/-! ### The structure map of the complement -/

/-- The ring map `A ⟶ Γ(U, 𝒪)` along which sections on `U = Spec A \ V(I)` are regarded as
`A`-modules: the inverse of `A ≅ Γ(Spec A, 𝒪)` followed by restriction to `U`. This is the map
`Stacks.LocalCohomology.sectionsOnAffineComplement` restricts scalars along. -/
abbrev complementSectionsRingHom : A →+* (Spec (CommRingCat.of A)).ringCatSheaf.obj.obj
    (op (complementZeroLocus A I)) :=
  ((Spec (CommRingCat.of A)).ringCatSheaf.obj.map
      (homOfLE (le_top : complementZeroLocus A I ≤ ⊤)).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- Sections over `U = Spec A \ V(I)` as `A`-modules are sections over `U` as modules over the
ring of sections of the structure sheaf there, with the scalars restricted. -/
theorem sectionsOnAffineComplement_eq :
    sectionsOnAffineComplement A I =
      SheafOfModules.evaluation.{u} (Spec (CommRingCat.of A)).ringCatSheaf
          (op (complementZeroLocus A I)) ⋙
        ModuleCat.restrictScalars (complementSectionsRingHom A I) :=
  rfl

/-- Taking sections over `U = Spec A \ V(I)` with values in modules over the ring of sections
there is additive: a morphism of sheaves of modules acts on sections sectionwise.

`Stacks.LocalCohomology.additive_evaluation_complementZeroLocus` is the same instance with the
ring taken implicitly. -/
instance additive_evaluation_complementZeroLocus' :
    (SheafOfModules.evaluation.{u} (Spec (CommRingCat.of A)).ringCatSheaf
      (op (complementZeroLocus A I))).Additive where
  map_add := rfl

/-! ### The three comparisons -/

/-- **The cohomology of derived sections on `U` is the classical right derived functor of
sections on `U`.** `RΓ(U, -)` is a right derived functor of sections over
`U = Spec A \ V(I)` on the unbounded derived category, so its degree-`n` cohomology at a sheaf of
modules placed in degree zero is Mathlib's `ℕ`-indexed `Rⁿ Γ(U, -)`, naturally in the sheaf.

The hypothesis of the general comparison is the existence of K-injective resolutions of
complexes of sheaves of modules on `Spec A`, which is
`Stacks.LocalCohomology.exists_quasiIso_isKInjective_specModules`.

This is the natural isomorphism of functors;
`Stacks.LocalCohomology.homologyDerivedSectionsIsoRightDerived` is the isomorphism of its
values at a fixed sheaf of modules. -/
def homologyDerivedSectionsNatIsoRightDerived (n : ℕ) :
    DerivedCategory.singleFunctor (Spec (CommRingCat.of A)).Modules 0 ⋙
        derivedSectionsOnAffineComplement A I ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ) ≅
      (sectionsOnAffineComplement A I).rightDerived n :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (sectionsOnAffineComplement A I) (derivedSectionsOnAffineComplement A I)
    (derivedSectionsOnAffineComplementUnit A I)
    (exists_quasiIso_isKInjective_specModules A) n

/-- **Restriction of scalars commutes with deriving sections on `U`.** Sections over
`U = Spec A \ V(I)` as `A`-modules are sections as `Γ(U, 𝒪)`-modules with the scalars restricted,
and restriction of scalars is exact — it is the identity on underlying abelian groups — so it may
be pulled out of the right derived functor.

`Stacks.LocalCohomology.rightDerivedSectionsOnAffineComplementIso` is the same statement with
the ring and the ideal taken implicitly and explicitly respectively, and with the structure map
named `Stacks.LocalCohomology.complementOpenScalars` instead of
`Stacks.LocalCohomology.complementSectionsRingHom`. -/
def rightDerivedSectionsOnAffineComplementIso' (n : ℕ) :
    (sectionsOnAffineComplement A I).rightDerived n ≅
      (SheafOfModules.evaluation.{u} (Spec (CommRingCat.of A)).ringCatSheaf
          (op (complementZeroLocus A I))).rightDerived n ⋙
        ModuleCat.restrictScalars (complementSectionsRingHom A I) :=
  let _ : (ModuleCat.restrictScalars (complementSectionsRingHom A I)).PreservesHomology :=
    Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars _
  Functor.rightDerivedCompIso
    (SheafOfModules.evaluation.{u} (Spec (CommRingCat.of A)).ringCatSheaf
      (op (complementZeroLocus A I)))
    (ModuleCat.restrictScalars (complementSectionsRingHom A I)) n

/-- **The classical right derived functor of sections on `U` is the cohomology of bounded-below
derived global sections.** The latter is the functor the Čech-to-cohomology comparison of
Stacks 01EQ lands in; the two differ only in how the degree is indexed. -/
def rightDerivedEvaluationComplementIsoPlus (n : ℕ) :
    (SheafOfModules.evaluation.{u} (Spec (CommRingCat.of A)).ringCatSheaf
        (op (complementZeroLocus A I))).rightDerived n ≅
      Stacks.Cohomology.CechDerived.derivedGlobalSectionsFunctor
          (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) ⋙
        DerivedCategory.Plus.homologyFunctor _ (n : ℤ) :=
  Stacks.DerivedIndexing.rightDerivedIso _ n

/-- **The cohomology of derived sections on `U` is bounded-below derived global sections on
`U`.** The composite of the three comparisons: `Hⁿ(RΓ(U, -))`, with `RΓ(U, -)` the unbounded
derived functor used by the localization triangle, is the degree-`n` cohomology of the
bounded-below derived global sections functor that the Čech comparison of Stacks 01EQ computes,
with the scalars restricted to `A`. -/
def homologyDerivedSectionsIsoDerivedGlobalSections (n : ℕ) :
    DerivedCategory.singleFunctor (Spec (CommRingCat.of A)).Modules 0 ⋙
        derivedSectionsOnAffineComplement A I ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ) ≅
      (Stacks.Cohomology.CechDerived.derivedGlobalSectionsFunctor
            (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) ⋙
          DerivedCategory.Plus.homologyFunctor _ (n : ℤ)) ⋙
        ModuleCat.restrictScalars (complementSectionsRingHom A I) :=
  homologyDerivedSectionsNatIsoRightDerived A I n ≪≫
    rightDerivedSectionsOnAffineComplementIso' A I n ≪≫
      Functor.isoWhiskerRight (rightDerivedEvaluationComplementIsoPlus A I n)
        (ModuleCat.restrictScalars (complementSectionsRingHom A I))

/-! ### Vanishing -/

/-- **Derived sections on `U` have vanishing degree-`n` cohomology exactly when the sheaf
cohomology group `Hⁿ(U, F)` vanishes.** The left-hand side is the cohomology of the unbounded
derived functor that the localization triangle of Stacks 0DWR is built from; the right-hand side
is the abelian-group-valued cohomology in which the repository's vanishing theorems — Serre
vanishing on an affine open, the vanishing above the dimension of the support — are stated.

Two reflections carry the vanishing across: restriction of scalars along `A ⟶ Γ(U, 𝒪)` and the
forgetful functor from `Γ(U, 𝒪)`-modules to abelian groups are both faithful and exact. -/
theorem isZero_homology_derivedSectionsOnAffineComplement_iff (n : ℕ)
    (F : (Spec (CommRingCat.of A)).Modules) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj
        ((derivedSectionsOnAffineComplement A I).obj
          ((DerivedCategory.singleFunctor (Spec (CommRingCat.of A)).Modules 0).obj F))) ↔
      IsZero (Hgroup (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) n F) := by
  refine Iff.trans ?_
    (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) n F)
  have e := (homologyDerivedSectionsNatIsoRightDerived A I n ≪≫
    rightDerivedSectionsOnAffineComplementIso' A I n).app F
  refine ⟨fun h => ?_, fun h => IsZero.of_iso
    (Functor.map_isZero (ModuleCat.restrictScalars (complementSectionsRingHom A I)) h) e⟩
  exact (IsZero.iff_id_eq_zero _).2 (Functor.map_injective
    (ModuleCat.restrictScalars (complementSectionsRingHom A I)) ((h.of_iso e.symm).eq_of_tgt _ _))

end Stacks.LocalCohomology

end
