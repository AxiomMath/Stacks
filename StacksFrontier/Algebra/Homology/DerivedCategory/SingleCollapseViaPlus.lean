module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction

/-! # The collapse at an acyclic object, in the unbounded model

Let `F : A ⥤ B` be additive with `A` having enough injectives and K-injective resolutions, let
`(RF, α)` be an unbounded right derived functor of `F`, and let `X : A` be **right acyclic** for
`F`. Then `RF` applied to `X` placed in degree `0` is `F X` placed in degree `0`.

On the bounded below derived category this is
`Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso`, which is one of the two
factors of [Stacks, Tag 089W]. This file builds the unbounded counterpart and proves that the two
correspond under `CategoryTheory.Functor.boundedDerivedIso`.

## Main definitions

* `CategoryTheory.Functor.singleCollapse`: **the collapse** `RF(X[0]) ⟶ (F X)[0]`, and
  `singleCollapseIso` as an isomorphism.

## Main results

* `CategoryTheory.Functor.isIso_app_single_of_rightAcyclic`: **the unbounded comparison `α` is
  invertible at the single complex `X[0]`** when `X` is right acyclic for `F`.
* `CategoryTheory.Functor.isIso_app_single_of_rightAcyclic`, again: it is what makes the
  collapse definable, and it is the only thing the acyclicity is used for.

## Implementation notes

*Why a data version at all, when a `Nonempty` one exists.*
`Stacks.Perfect.CechDerivedSupport.nonempty_rightDerived_obj_single_iso`
(`AlgebraicGeometry/Perfect/SupportClosedSubset/DerivedSupportInvertsAugmentation.lean:120`)
is this collapse already, and it is consumed in its own file. It cannot serve here for two
reasons. It is wrapped in `Nonempty`, so the isomorphism cannot be named and no equation about it
can be stated — and an equation is the whole point, the collapse being one of the two factors of
[Stacks, Tag 089W] that a comparison of the two models has to match. And its hypotheses are
**incomparable** to these: it takes the comparison's invertibility at K-injective complexes as the
explicit `hcomp` rather than `[RF.IsRightDerivedFunctor α _]` together with `hres`, so it cannot
be rewritten through `CategoryTheory.Functor.boundedDerivedIso` without acquiring `hres`, which
would weaken it. It is also built on the `Nonempty` bridge
`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`, of which
`boundedDerivedIso` is the data version, and it re-inlines
`Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso` rather than citing it.
So the two are left standing side by side, and this file says which is which.

*Why the invertibility is not
`Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic`.* That lemma gives the same conclusion
for an arbitrary bounded below complex with right-acyclic terms, and it would apply here — the
terms of `X[0]` are `X` and zero objects — but it asks for `IsGrothendieckAbelian A`, for
`PreservesFiniteLimits F`, and for right acyclicity of the zero object, which is not an instance
in `AcyclicObjects.lean`. Off `boundedDerivedIso_hom_app` the single-complex case needs none of
those: right acyclicity of `X` **is**, by the definition of
`CategoryTheory.Functor.rightAcyclic`, invertibility of the unit of `R⁺F` at `X[0]`, and the
pinning of the crossing carries that to `α`. The two statements are therefore not duplicates of
one another; the one with fewer hypotheses is the one used.

## What is not proved

**The matching of this collapse with the one on `D⁺`**, i.e. that
`CategoryTheory.Functor.boundedDerivedIso` carries
`Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso` to `singleCollapse`.
The design for it is settled and the two coherences it needs **already exist**, so it must not be
written from scratch:

* `Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_hom_app`
  (`StacksFrontier/Homology/DerivedIndexing/SingleDegreeUnit.lean:125`) and its `inv` companion
  `Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_inv_app`
  (`StacksFrontier/Homology/DerivedIndexing/Composite.lean:750`);
* `Stacks.DerivedIndexing.ι_map_mapSingleFunctorCompQhIso_inv_app`
  (`StacksFrontier/Homology/DerivedIndexing/Composite.lean:820`), with the raw preimage form at `:808`.

Note which directions those are: the second is available for `inv` and not for `hom`. So the
matching should be stated in the **inverse** direction — the `D⁺` collapse's inverse is
`mapSingleFunctorCompQhIso.inv`, then the unit of `R⁺F`, then `R⁺F` of
`singleFunctorPlusIsoCompQh.inv` — where both existing lemmas apply as they stand. Stating it in
the `hom` direction forces a `hom` sibling of `ι_map_mapSingleFunctorCompQhIso_inv_app`, which is
a one-line `Functor.map_preimage` but belongs beside that lemma rather than here. It also writes
its right-hand side through `HomologicalComplex.singleMapHomologicalComplex` rather than through
`CategoryTheory.Functor.mapHomotopyCategorySingleFunctor`, so `singleCollapse` as defined above
will meet it through `Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app`, which
that proof already uses.

The two coherences are not restated here: they already exist in
`StacksFrontier/Homology/DerivedIndexing/` under the `ι_`-prefixed spelling used throughout that
directory, as does `Stacks.DerivedIndexing.ι_map_singleIsoResPlusQh_hom_app_eq`. The directions in
which those `ι_` lemmas are stated determine the **shape** of step 2.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 05T5](https://stacks.math.columbia.edu/tag/05T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v u vB uB wA wB

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- `IsIso` read off a composite of two invertible morphisms whose value is known. At variables of
an abstract category; at the concrete spelling the two sides of the pinning are definitionally but
not syntactically equal, so `rw` is unavailable on it. -/
private lemma isIso_of_comp_eq {C : Type*} [Category* C] {X Y Z : C} {a : X ⟶ Y}
    (ha : IsIso a) (e : Y ≅ Z) {c : X ⟶ Z} (h : a ≫ e.hom = c) : IsIso c := by
  have := ha
  rw [← h]
  infer_instance

/-- **The unbounded comparison is invertible at the single complex of a right acyclic object.**
Right acyclicity of `X` is, by definition, invertibility of the unit of `R⁺F` at `X[0]`, and
`boundedDerivedIso_hom_app` carries that to `α`. -/
theorem isIso_app_single_of_rightAcyclic
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : A) (hX : F.rightAcyclic X) :
    IsIso (α.app ((HomotopyCategory.singleFunctor A 0).obj X)) := by
  have h₁ : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := hX
  exact isIso_of_comp_eq
    (@Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Plus.ι _ h₁)
    ((boundedDerivedIso F RF α hres).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj X)))
    (boundedDerivedIso_hom_app F RF α hres ((HomotopyCategory.Plus.singleFunctor A 0).obj X))

/-- **The collapse of the unbounded right derived functor at a right acyclic object**,
`RF(X[0]) ⟶ (F X)[0]`: the identification of `X[0]` with the single complex in the homotopy
category, the comparison `α` inverted — invertible by `isIso_app_single_of_rightAcyclic` — and the
two single-functor coherences. -/
def singleCollapse
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : A) (hX : F.rightAcyclic X) :
    RF.obj ((DerivedCategory.singleFunctor A 0).obj X) ⟶
      (DerivedCategory.singleFunctor B 0).obj (F.obj X) :=
  haveI := isIso_app_single_of_rightAcyclic F RF α hres X hX
  RF.map ((DerivedCategory.singleFunctorIsoCompQh A 0).hom.app X) ≫
    CategoryTheory.inv (α.app ((HomotopyCategory.singleFunctor A 0).obj X)) ≫
      DerivedCategory.Qh.map ((mapHomotopyCategorySingleFunctor F 0).hom.app X) ≫
        (DerivedCategory.singleFunctorIsoCompQh B 0).inv.app (F.obj X)

/-- **The collapse, as an isomorphism.** Its three factors are invertible. -/
def singleCollapseIso
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : A) (hX : F.rightAcyclic X) :
    RF.obj ((DerivedCategory.singleFunctor A 0).obj X) ≅
      (DerivedCategory.singleFunctor B 0).obj (F.obj X) :=
  haveI := isIso_app_single_of_rightAcyclic F RF α hres X hX
  RF.mapIso ((DerivedCategory.singleFunctorIsoCompQh A 0).app X) ≪≫
    (asIso (α.app ((HomotopyCategory.singleFunctor A 0).obj X))).symm ≪≫
      DerivedCategory.Qh.mapIso ((mapHomotopyCategorySingleFunctor F 0).app X) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQh B 0).app (F.obj X)).symm

/-- The forward direction of `singleCollapseIso` is `singleCollapse`. -/
theorem singleCollapseIso_hom
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : A) (hX : F.rightAcyclic X) :
    (singleCollapseIso F RF α hres X hX).hom = singleCollapse F RF α hres X hX :=
  rfl

end CategoryTheory.Functor


end
