module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomotopyCategoryHoms
import StacksCore.Tactic.StacksAttribute

/-!
# Derived morphisms out of the internal Hom complex into a K-injective complex

Let `(X, O_X)` be a ringed space, let `L` be a complex of `O_X`-modules and let `I` be a
*K-injective* complex of `O_X`-modules. For an open `U ⊆ X`, the degree-zero cohomology of the
complex of sections over `U` of the internal Hom complex `SheafHom^•(L, I)` is the group of
morphisms `L|_U ⟶ I|_U` in the derived category of `O_U`-modules:
`H^0(Γ(U, SheafHom^•(L, I))) = Hom_{D(O_U)}(L|_U, I|_U)`.

This is [Stacks, Tag 0A8R]. By [Stacks, Tag 0A8L] the left-hand side is the group of morphisms
`L|_U ⟶ I|_U` in the *homotopy* category, and localization at the quasi-isomorphisms is
bijective on morphisms into a K-injective complex, which is the second half of the proof. The
restriction `j^* I` of a K-injective complex to an open subspace is again K-injective by
[Stacks, Tag 08BS], and a shift of a K-injective complex is K-injective, which is what makes
that second half applicable.

## Main definitions

* `Stacks.SheafOfModules.restrictComplexToSubspace`: restriction of a complex of `O_X`-modules
  to the open subspace associated with an open set, degreewise.
* `Stacks.SheafOfModules.sheafHomComplexHomologyEquivDerivedCategory`: the identification
  above, as an additive equivalence.

## Main results

* `Stacks.SheafOfModules.sheafHomComplexHomologyEquivDerivedCategory_apply` describes the
  equivalence on a section class: it is the homotopy-class morphism of [Stacks, Tag 0A8L],
  transported from the slice-site model of `L|_U` and `I|_U` to the open-subspace model and
  then localized.

## Implementation notes

The internal Hom complex enters as an arbitrary realization
`H : Stacks.SheafOfModules.SheafHomComplex Rc L I`, so the left-hand side is literally the
degree-zero cohomology of its sections.

On the right-hand side `L|_U` and `I|_U` are modelled on the *open subspace* `U`, by
`ExtensionByZeroModules.jStar` over the restricted sheaf of rings
`ExtensionByZeroModules.resRing`, and not on the slice site `Opens X / U` which the section
data of the internal Hom complex uses. The two models are identified by Mathlib's equivalence
`Opens.sheafOfModulesEquivOver`, and transporting along it is one of the two steps of the
composite. The objects of the derived category representing the restrictions are then taken as
*parameters* `LU`, `MU` together with isomorphisms `eL`, `eM` from the localized restricted
complexes, so that the statement applies to any chosen representatives instead of fixing one.

## References

* [Stacks Project, Tag 0A8R](https://stacks.math.columbia.edu/tag/0A8R)
* [Stacks Project, Tag 0A8L](https://stacks.math.columbia.edu/tag/0A8L)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace ExtensionByZeroModules

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of a complex of modules to the open subspace associated with `U`. -/
abbrev restrictComplexToSubspace {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ :=
  ((jStar U O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Mathlib's equivalence between modules on the slice site over `U` and modules on the open
subspace `U` is additive: it is the identity on the underlying maps of sheaves. -/
instance sheafOfModulesEquivOver_functor_additive {X : TopCat.{u}} (U : Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    (U.sheafOfModulesEquivOver O).functor.Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

/-- Restriction of a complex to the open subspace `U` is restriction to the slice site over
`U` followed by the equivalence between the two models of `O_U`-modules.

This is `rfl`, and it is stated as its own lemma because both sides occur in the statement of
Stacks 0A8R: the section data of an internal Hom complex is on the slice site, while the
objects of the derived category it is compared with are on the open subspace. Elaborating a
term of the comparison type directly makes the unifier discover this equality inside a much
larger goal, which it does not do within the default heartbeat budget. -/
theorem mapHomologicalComplex_restrictComplex {X : TopCat.{u}}
    (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)
    (K : CochainComplex (StructureSheafModules Rc) ℤ) :
    ((U.sheafOfModulesEquivOver (structureSheaf Rc)).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (restrictComplex Rc K U) =
      restrictComplexToSubspace (structureSheaf Rc) U K := rfl

/-- The shifted form of `Stacks.SheafOfModules.mapHomologicalComplex_restrictComplex`: the
equivalence between the two models of `O_U`-modules carries the zero-shifted slice-site
restriction to the zero-shifted subspace restriction. Also `rfl`; see there for why it is
stated separately. The shift is by `0` because that is the shift occurring in Stacks 0A8R,
where it records that the target is taken in degree `0`; for a general shift the two sides are
no longer definitionally equal, since the shift functor of a cochain complex reindexes the
differentials. -/
theorem mapHomologicalComplex_restrictComplex_shiftZero {X : TopCat.{u}}
    (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)
    (K : CochainComplex (StructureSheafModules Rc) ℤ) :
    ((U.sheafOfModulesEquivOver (structureSheaf Rc)).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((restrictComplex Rc K U)⟦(0 : ℤ)⟧) =
      (restrictComplexToSubspace (structureSheaf Rc) U K)⟦(0 : ℤ)⟧ := rfl

/-- **Stacks 0A8R.** If `I` is K-injective, degree-zero cohomology over `U` of the internal
Hom complex from `L` to `I` is canonically the group of derived morphisms between the objects
represented by their restrictions to the open subspace `U`. -/
@[stacks 0A8R]
noncomputable def sheafHomComplexHomologyEquivDerivedCategory
    {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)
    (L I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective]
    (H : SheafHomComplex Rc L I)
    (LU MU : DerivedCategory
      (SheafOfModules.{u} (resRing U (structureSheaf Rc))))
    (eL : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ _).obj
        (restrictComplexToSubspace (structureSheaf Rc) U L)) ≅ LU)
    (eM : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ _).obj
        ((restrictComplexToSubspace (structureSheaf Rc) U I)⟦(0 : ℤ)⟧)) ≅ MU) :
    (sectionComplex Rc H.obj U).homology 0 ≃+
      (LU ⟶ MU) :=
  let E := U.sheafOfModulesEquivOver (structureSheaf Rc)
  let Fh := E.functor.mapHomotopyCategory (ComplexShape.up ℤ)
  let K := restrictComplex Rc L U
  let J := (restrictComplex Rc I U)⟦(0 : ℤ)⟧
  let RI := restrictComplexToSubspace (structureSheaf Rc) U I
  let RJ := RI⟦(0 : ℤ)⟧
  let eK := (E.functor.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K ≪≫
    (HomotopyCategory.quotient _ _).mapIso
      (eqToIso (mapHomologicalComplex_restrictComplex Rc U L))
  let eJ := (E.functor.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app J ≪≫
    (HomotopyCategory.quotient _ _).mapIso
      (eqToIso (mapHomologicalComplex_restrictComplex_shiftZero Rc U I))
  letI : RI.IsKInjective :=
    ExtensionByZeroModules.isKInjective_jStar U (structureSheaf Rc) I
  letI : RJ.IsKInjective :=
    (CochainComplex.isKInjective_shift_iff _ _).2 inferInstance
  (sheafHomComplexHomologyEquivHomotopyCategory Rc U L I H 0).trans <|
    (AddEquiv.ofBijective Fh.mapAddHom
      ⟨Fh.map_injective, Fh.map_surjective⟩).trans <|
      (CategoryTheory.Linear.homCongr ℤ eK eJ).toAddEquiv.trans <|
        (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
          (CochainComplex.IsKInjective.Qh_map_bijective _ RJ)).trans
            (CategoryTheory.Linear.homCongr ℤ eL eM).toAddEquiv

/-- **Stacks 0A8R.** The canonical identification sends a section cohomology class first to its
homotopy-class morphism, transports that morphism from the slice-site model to the
open-subspace model, and then localizes it. In particular this fixes its value on the identity
class and its behaviour under changing the two representatives. -/
@[stacks 0A8R "canonical comparison on section classes"]
theorem sheafHomComplexHomologyEquivDerivedCategory_apply
    {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)
    (L I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective]
    (H : SheafHomComplex Rc L I)
    (LU MU : DerivedCategory
      (SheafOfModules.{u} (resRing U (structureSheaf Rc))))
    (eL : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ _).obj
        (restrictComplexToSubspace (structureSheaf Rc) U L)) ≅ LU)
    (eM : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ _).obj
        ((restrictComplexToSubspace (structureSheaf Rc) U I)⟦(0 : ℤ)⟧)) ≅ MU)
    (z : (sectionComplex Rc H.obj U).homology 0) :
    sheafHomComplexHomologyEquivDerivedCategory Rc U L I H LU MU eL eM z =
      (let E := U.sheafOfModulesEquivOver (structureSheaf Rc)
            let Fh := E.functor.mapHomotopyCategory (ComplexShape.up ℤ)
       let K := restrictComplex Rc L U
       let J := (restrictComplex Rc I U)⟦(0 : ℤ)⟧
       let eK := (E.functor.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K ≪≫
         (HomotopyCategory.quotient _ _).mapIso
           (eqToIso (mapHomologicalComplex_restrictComplex Rc U L))
       let eJ := (E.functor.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app J ≪≫
         (HomotopyCategory.quotient _ _).mapIso
           (eqToIso (mapHomologicalComplex_restrictComplex_shiftZero Rc U I))
       eL.inv ≫ DerivedCategory.Qh.map
         (eK.inv ≫ Fh.map
           (sheafHomComplexHomologyEquivHomotopyCategory
             Rc U L I H 0 z) ≫ eJ.hom) ≫ eM.hom) := by
  let E := U.sheafOfModulesEquivOver (structureSheaf Rc)
  let Fh := E.functor.mapHomotopyCategory (ComplexShape.up ℤ)
  let K := restrictComplex Rc L U
  let J := (restrictComplex Rc I U)⟦(0 : ℤ)⟧
  let RI := restrictComplexToSubspace (structureSheaf Rc) U I
  let RJ := RI⟦(0 : ℤ)⟧
  let eK := (E.functor.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K ≪≫
    (HomotopyCategory.quotient _ _).mapIso
      (eqToIso (mapHomologicalComplex_restrictComplex Rc U L))
  let eJ := (E.functor.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app J ≪≫
    (HomotopyCategory.quotient _ _).mapIso
      (eqToIso (mapHomologicalComplex_restrictComplex_shiftZero Rc U I))
  let _ : RI.IsKInjective :=
    ExtensionByZeroModules.isKInjective_jStar U (structureSheaf Rc) I
  let _ : RJ.IsKInjective :=
    (CochainComplex.isKInjective_shift_iff _ _).2 inferInstance
  change
    ((sheafHomComplexHomologyEquivHomotopyCategory Rc U L I H 0).trans
      ((AddEquiv.ofBijective Fh.mapAddHom
        ⟨Fh.map_injective, Fh.map_surjective⟩).trans
        ((CategoryTheory.Linear.homCongr ℤ eK eJ).toAddEquiv.trans
          ((AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
            (CochainComplex.IsKInjective.Qh_map_bijective _ RJ)).trans
            (CategoryTheory.Linear.homCongr ℤ eL eM).toAddEquiv)))) z = _
  simp only [AddEquiv.trans_apply]
  change
    CategoryTheory.Linear.homCongr ℤ eL eM
      (DerivedCategory.Qh.map
        (CategoryTheory.Linear.homCongr ℤ eK eJ
          (Fh.map
            (sheafHomComplexHomologyEquivHomotopyCategory
              Rc U L I H 0 z)))) = _
  simp only [CategoryTheory.Linear.homCongr_apply, Category.assoc]
  rfl

end Stacks.SheafOfModules
