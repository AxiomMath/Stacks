module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum

/-!
# The objectwise direct sum of a family of sheaves of modules is a separated presheaf

Let `R` be a sheaf of rings on a site `(C, J)` and let `N : ι → SheafOfModules R` be a family of
sheaves of modules. The objectwise direct sum `Stacks.directSum (fun i => (N i).val)` is in
general *not* a sheaf: a section with locally finite support need not have globally finite
support. It is however always *separated*, because equality in a direct sum is equality of
components and each component is a sheaf. This file proves that, and draws the consequence that
the sheafification unit of the ungraded realization of a sheaf of graded algebras is injective on
the sections over **every** object of the site, not merely locally injective.

The bijectivity of the same unit is a strictly stronger statement and fails over a general
object — see `Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff`, which holds over a
quasi-compact object only; injectivity needs no such hypothesis.

## Main results

* `Stacks.directSumRestrict_apply`: restriction in the objectwise direct sum is restriction of
  each component.
* `Stacks.isSeparated_directSum` and `Stacks.isSeparated_directSum_sheaves`: **the objectwise
  direct sum of a family of separated presheaves of modules is separated**, in particular the
  objectwise direct sum of a family of sheaves of modules is.
* `Stacks.GradedAlgebra.isSeparated_totalPresheaf`: the ungraded realization of a graded algebra
  is a separated presheaf of rings as soon as its homogeneous components are separated.
* `Stacks.GradedAlgebra.injective_totalUnit` and
  `SheafOfModules.GradedAlgebra.injective_ungradedUnit`: **the sheafification unit of the
  ungraded realization is injective on the sections over every object of the site.**

## Implementation notes

Separatedness is asked of the underlying presheaf of abelian groups, in the form
`CategoryTheory.Presheaf.IsSeparated`, because that is the form in which a sheaf of modules
supplies it: `SheafOfModules.isSheaf` is a statement about `val.presheaf`, which is
`PresheafOfModules.toPresheaf` on the nose, and `CategoryTheory.Presheaf.IsSheaf.isSeparated`
turns it into separatedness. The passage to the `Type`-valued form
`CategoryTheory.Presieve.IsSeparated` that
`CategoryTheory.Presheaf.isLocallyInjective_iff_injective_of_separated` consumes is carried out
in `Stacks.GradedAlgebra.isSeparated_totalPresheaf`: two amalgamations of one family of elements
agree on the covering sieve, which is exactly the hypothesis of
`Stacks.directSum_section_ext`.

Local injectivity of the unit is taken as an explicit hypothesis rather than as an instance. It
is an instance under `[J.WEqualsLocallyBijective RingCat]`, which does not synthesize for the
site of opens of a scheme; there it is `Stacks.RelativeSpec.isLocallyInjective_toTotalSheaf`,
read off `CategoryTheory.toSheafify` directly.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks

/-! ### Separatedness of the objectwise direct sum -/

section DirectSum

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  (P : ι → PresheafOfModules.{w} R)

/-- Restriction in the objectwise direct sum is restriction of each component. -/
lemma directSumRestrict_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : DirectSumType P X) (i : ι) :
    directSumRestrict P f z i = sectionRestrict (P i) f (z i) := by
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
  | of j y =>
    rw [directSumRestrict_of]
    rcases eq_or_ne i j with rfl | hij
    · rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hij, DirectSum.of_eq_of_ne _ _ _ hij, map_zero]
  | add z z' hz hz' =>
    rw [map_add, DirectSum.add_apply, hz, hz', DirectSum.add_apply, map_add]

variable (J : GrothendieckTopology C)
  (hsep : ∀ i, Presheaf.IsSeparated J ((PresheafOfModules.toPresheaf R).obj (P i)))

include hsep in
/-- Two sections of the objectwise direct sum agreeing on a covering sieve are equal, the
homogeneous components being separated. -/
theorem directSum_section_ext {X : C} (S : Sieve X) (hS : S ∈ J X)
    (x y : DirectSumType P (op X))
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → directSumRestrict P f.op x = directSumRestrict P f.op y) :
    x = y := by
  refine DirectSum.ext fun i => ?_
  refine hsep i X S hS (x i) (y i) fun Y f hf => ?_
  have key := congrArg (fun z : DirectSumType P (op Y) => z i) (h f hf)
  rwa [directSumRestrict_apply, directSumRestrict_apply] at key

include hsep in
/-- **The objectwise direct sum of a family of separated presheaves of modules is separated.** -/
theorem isSeparated_directSum :
    Presheaf.IsSeparated J ((PresheafOfModules.toPresheaf R).obj (directSum P)) :=
  fun _ S hS x y h => directSum_section_ext P J hsep S hS x y fun _ f hf => h _ f hf

end DirectSum

/-- **The objectwise direct sum of a family of sheaves of modules is a separated presheaf.** -/
theorem isSeparated_directSum_sheaves {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} {ι : Type} [DecidableEq ι]
    (N : ι → SheafOfModules.{w} R) :
    Presheaf.IsSeparated J
      ((PresheafOfModules.toPresheaf R.obj).obj (directSum fun i => (N i).val)) :=
  isSeparated_directSum _ J fun i => (N i).isSheaf.isSeparated

/-! ### Injectivity of the sheafification unit of an ungraded realization -/

namespace GradedAlgebra

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{w} R} (A : GradedAlgebra P)
  (J : GrothendieckTopology C) [HasSheafify J RingCat.{w}]
  (hsep : ∀ i, Presheaf.IsSeparated J ((PresheafOfModules.toPresheaf R).obj (P i)))

omit [HasSheafify J RingCat.{w}] in
include hsep in
/-- **The ungraded realization of a graded algebra is a separated presheaf of rings** as soon as
its homogeneous components are separated. -/
theorem isSeparated_totalPresheaf :
    Presieve.IsSeparated J (A.totalPresheaf ⋙ CategoryTheory.forget RingCat.{w}) :=
  fun _ S hS _ t₁ t₂ h₁ h₂ =>
    directSum_section_ext P J hsep S hS t₁ t₂ fun _ f hf => (h₁ f hf).trans (h₂ f hf).symm

include hsep in
/-- **The sheafification unit of the ungraded realization of a graded algebra is injective on
the sections over every object of the site**, as soon as the homogeneous components are
separated. -/
theorem injective_totalUnit (hli : Presheaf.IsLocallyInjective J (A.toTotalSheaf J))
    (X : Cᵒᵖ) : Function.Injective (A.totalUnit J X) :=
  (Presheaf.isLocallyInjective_iff_injective_of_separated J (A.toTotalSheaf J)
    (A.isSeparated_totalPresheaf J hsep)).1 hli X

end GradedAlgebra

end Stacks

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J RingCat.{w}] (A : GradedAlgebra.{w, w} R)

omit [HasSheafify J RingCat.{w}] in
/-- A homogeneous piece of a sheaf of graded algebras is a separated presheaf. -/
theorem isSeparated_piece (i : ℤ) :
    Presheaf.IsSeparated J ((PresheafOfModules.toPresheaf R.obj).obj (A.piece i).val) :=
  (A.piece i).isSheaf.isSeparated

/-- **The sheafification unit of the ungraded realization of a sheaf of graded algebras is
injective on the sections over every object of the site.** -/
theorem injective_ungradedUnit
    (hli : Presheaf.IsLocallyInjective J (A.toPresheafGradedAlgebra.toTotalSheaf J))
    (X : Cᵒᵖ) : Function.Injective (A.toPresheafGradedAlgebra.totalUnit J X) :=
  A.toPresheafGradedAlgebra.injective_totalUnit J A.isSeparated_piece hli X

/-! ### Homogeneous local sections inside the ungraded realization -/

/-- The inclusion of a homogeneous piece into the ungraded realization is additive. -/
theorem ungradedIncl_add (n : ℤ) (U : Cᵒᵖ) (x y : (A.piece n).val.obj U) :
    A.ungradedIncl n (x + y) = A.ungradedIncl n x + A.ungradedIncl n y :=
  A.toPresheafGradedAlgebra.inclSheaf_add J n x y

/-- A scalar multiple of a homogeneous local section is, inside the ungraded realization, the
product with the image of the scalar under the structure map. -/
theorem ungradedIncl_smul (n : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (A.piece n).val.obj U) :
    A.ungradedIncl n (r • x) =
      (A.ungradedStructureMap.hom.app U).hom r * A.ungradedIncl n x := by
  have h1 : A.toPresheafGradedAlgebra.incl n (r • x) =
      A.toPresheafGradedAlgebra.structureMap U r * A.toPresheafGradedAlgebra.incl n x := by
    rw [A.toPresheafGradedAlgebra.incl_smul,
      A.toPresheafGradedAlgebra.smul_eq_structureMap_mul]
  change A.toPresheafGradedAlgebra.totalUnit J U (A.toPresheafGradedAlgebra.incl n (r • x)) = _
  rw [h1, map_mul]
  rfl

/-- A scalar multiple of the algebra unit is, inside the ungraded realization, the image of that
scalar under the structure map. -/
theorem ungradedIncl_smul_one (U : Cᵒᵖ) (r : R.obj.obj U) :
    A.ungradedIncl 0 (r • A.one.eval U) = (A.ungradedStructureMap.hom.app U).hom r := by
  rw [A.ungradedIncl_smul, A.ungradedIncl_one, _root_.mul_one]

/-- The inclusion of a homogeneous piece into the ungraded realization commutes with
restriction. -/
theorem ungradedIncl_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℤ) (x : (A.piece n).val.obj U) :
    (A.ungradedSheaf.obj.map f).hom (A.ungradedIncl n x) =
      A.ungradedIncl n (Stacks.sectionRestrict (A.piece n).val f x) :=
  A.toPresheafGradedAlgebra.totalSheafRestrict_inclSheaf J f n x

end SheafOfModules.GradedAlgebra

end
