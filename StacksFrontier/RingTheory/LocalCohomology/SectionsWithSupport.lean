module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Local cohomology with a specialization-closed support

For a subset `T` of the prime spectrum of a ring `A`, degree-zero sections with support in
`T` form a functor on `A`-modules. Its total right derived functor defines local cohomology
with support in `T`, both on the bounded-below and the unbounded derived category.

## Main definitions

* `Stacks.LocalCohomology.sectionsWithSupportIn`: the degree-zero sections of a module with
  support in `T`, as a submodule.
* `Stacks.LocalCohomology.sectionsWithSupportInFunctor`: the functor `H⁰_T` on modules.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInPlus`: its total right derived functor
  on the bounded-below derived category.
* `Stacks.LocalCohomology.derivedSectionsWithSupportIn`: its total right derived functor on
  the unbounded derived category.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInUnit`: the canonical comparison from the
  functor on complexes to its unbounded right derived functor.
* `Stacks.LocalCohomology.localCohomologyWithSupportInPlus` and
  `Stacks.LocalCohomology.localCohomologyWithSupportIn`: the resulting cohomology modules.

## Main results

* `Stacks.LocalCohomology.sectionsWithSupportInFunctor_map_val`: the functor `H⁰_T` acts on a
  morphism by restriction.
* `Stacks.LocalCohomology.hasPointwiseRightDerivedSectionsWithSupportIn`: `H⁰_T` has a
  pointwise right derived functor on the unbounded homotopy category.
* `Stacks.LocalCohomology.derivedSectionsWithSupportIn_isRightDerivedFunctor`: the comparison
  `derivedSectionsWithSupportInUnit` exhibits `derivedSectionsWithSupportIn` as the right
  derived functor of `H⁰_T`.

## References

* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- An element of a submodule has the same annihilator in the submodule as its image has in the
ambient module. -/
theorem torsionOf_submodule_eq {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (N : Submodule A M) (x : N) :
    Ideal.torsionOf A N x = Ideal.torsionOf A M x.val := by
  ext a
  simp only [Ideal.mem_torsionOf_iff]
  exact Subtype.ext_iff

/-- The degree-zero sections of `M` with support in `T`. It is the supremum of the
`I`-power-torsion submodules as `V(I)` ranges over the closed subsets contained in `T`. -/
def sectionsWithSupportIn (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : Type v) [AddCommGroup M] [Module A M] :
    Submodule A M :=
  ⨆ (I : Ideal A) (_ : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T),
    I.primaryComponent M

/-- Degree-zero sections with support in `T`, functorial in the module: on objects, the
filtered colimit of the `I`-power-torsion submodules over ideals whose zero locus is contained
in `T`. -/
@[implicit_reducible, stacks 0EF4 "local_cohomology_with_support_in_t"]
def sectionsWithSupportInFunctor (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A where
  obj M := ModuleCat.of A (sectionsWithSupportIn A T M)
  map {M N} f := ModuleCat.ofHom <|
    (f.hom.domRestrict (sectionsWithSupportIn A T M)).codRestrict
      (sectionsWithSupportIn A T N) (fun x ↦ by
        have hmap : Submodule.map f.hom (sectionsWithSupportIn A T M) ≤
            sectionsWithSupportIn A T N := by
          rw [sectionsWithSupportIn, Submodule.map_iSup]
          refine iSup_le fun I ↦ ?_
          rw [Submodule.map_iSup]
          refine iSup_le fun hI ↦ ?_
          refine le_iSup_of_le I (le_iSup_of_le hI ?_)
          rintro _ ⟨y, hy, rfl⟩
          exact Ideal.primaryComponent_map_mem I f.hom ⟨y, hy⟩
        exact hmap (Submodule.mem_map_of_mem (f := f.hom) x.property))
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The underlying map of `sectionsWithSupportInFunctor` is the restriction of the given map. -/
@[simp]
theorem sectionsWithSupportInFunctor_map_val (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) {M N : ModuleCat.{max u v} A} (f : M ⟶ N)
    (x : sectionsWithSupportIn A T M) :
    (((sectionsWithSupportInFunctor.{u, v} A T).map f).hom x).val = f.hom x.val := rfl

/-- Sections with support in `T` is an additive functor. -/
instance sectionsWithSupportInFunctor_additive
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    (sectionsWithSupportInFunctor.{u, v} A T).Additive where
  map_add := by intros; ext; rfl

/-- The total right derived functor of degree-zero sections with support in `T`, on bounded-below
derived objects. -/
@[implicit_reducible, stacks 0EF4 "local_cohomology_with_support_in_t"]
noncomputable def derivedSectionsWithSupportInPlus (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    DerivedCategory.Plus (ModuleCat.{max u v} A) ⥤
      DerivedCategory.Plus (ModuleCat.{max u v} A) := by
  letI : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  exact (sectionsWithSupportInFunctor A T).rightDerivedFunctorPlus

/-- Degree-zero sections with support in `T` have a pointwise right derived functor on the
unbounded homotopy category of modules. -/
noncomputable instance hasPointwiseRightDerivedSectionsWithSupportIn
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    HasPointwiseRightDerivedFunctor
      ((sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) := by
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  let F := sectionsWithSupportInFunctor.{u, v} A T
  exact (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
        max u v, max (u + 1) (v + 1), max (u + 1) (v + 1),
        max (u + 1) (v + 1), max (u + 1) (v + 1), max (u + 1) (v + 1)}
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K ↦ by
        obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
        exact ⟨I, q, hI, hq⟩)).1

/-- The total right derived functor of degree-zero sections with support in `T`, on the unbounded
derived category. -/
@[implicit_reducible, stacks 0EF4 "local_cohomology_with_support_in_t"]
noncomputable def derivedSectionsWithSupportIn (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} A) :=
  totalRightDerived
    ((sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))

/-- The canonical comparison from applying sections with support to a complex to applying
its unbounded right derived functor. -/
noncomputable abbrev derivedSectionsWithSupportInUnit (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    (sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsWithSupportIn.{u, v} A T :=
  ((sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))

/-- The comparison `derivedSectionsWithSupportInUnit` exhibits `derivedSectionsWithSupportIn`
as the right derived functor of degree-zero sections with support in `T`. -/
noncomputable instance derivedSectionsWithSupportIn_isRightDerivedFunctor
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    (derivedSectionsWithSupportIn.{u, v} A T).IsRightDerivedFunctor
      (derivedSectionsWithSupportInUnit.{u, v} A T)
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) := by
  change (((sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))).IsRightDerivedFunctor
    (((sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))
  infer_instance

/-- The `i`-th local cohomology module with support in `T` of a bounded-below derived object. -/
@[stacks 0EF4 "local_cohomology_with_support_in_t"]
noncomputable abbrev localCohomologyWithSupportInPlus
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) (i : ℤ) :
    ModuleCat.{max u v} A :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj
    ((derivedSectionsWithSupportInPlus A T).obj K)

/-- The `i`-th local cohomology module with support in `T` of an unbounded derived object. -/
@[stacks 0EF4 "local_cohomology_with_support_in_t"]
noncomputable abbrev localCohomologyWithSupportIn
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) : ModuleCat.{max u v} A :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
    ((derivedSectionsWithSupportIn A T).obj K)

end Stacks.LocalCohomology
