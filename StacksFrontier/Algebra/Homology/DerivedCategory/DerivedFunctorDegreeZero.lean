module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective

/-! # `R⁰w ≅ w` for a left exact functor, on the unbounded derived category

Let `A` and `B` be abelian categories, `A` with enough injectives, let `w : A ⥤ B` be additive and
let `Rw : D(A) ⥤ D(B)`, with unit `α`, be a right derived functor of `w` on the *unbounded*
derived category. For every degree `i` there is a canonical natural transformation

`w ⟶ singleFunctor A i ⋙ Rw ⋙ homologyFunctor B i`

-- the unit of `Rw` read at the complexes `X[i]` by degree-`i` cohomology -- and it is an
isomorphism as soon as `w` is left exact. This file constructs the resulting natural isomorphism,
`Stacks.DerivedFunctor.derivedDegreeNatIso`, whose shape is exactly the `hsingle` hypothesis of
`Stacks.DerivedFunctor.homologyEdge`.

Left exactness of `w` is the only hypothesis on `w`: it is what makes the comparison invertible,
and the statement is false without it.

## The argument

Everything happens in degree `0`; the general degree is obtained from it by the shift, in
`derivedDegreeNatIso`, using nothing but `Rw.CommShift`.

The comparison `singleUnitHomology` is `H⁰(α)` at the complexes `X[0]`, with its source
identified with `w` (`singleUnitSourceIso`) and its target with `R⁰w`
(`singleUnitTargetIso`). Both of those functors are left exact: `w` by hypothesis, and `R⁰w`
because the distinguished triangle of a short exact sequence of `A` has an exact degree-`0`
cohomology sequence which starts at `R⁰w`, there being no cohomology in degree `-1`
(`preservesFiniteLimits_singleCompDerivedCompHomology`). The comparison is invertible at an
injective object, because the complex `J[0]` of an injective `J` is a bounded below complex of
injectives, hence K-injective, and the unit of a right derived functor is invertible at a
K-injective complex (`isIso_unit_app_single_of_injective`). Finally every object of `A` is the
kernel of a map between two injective objects -- the first two terms of an injective resolution --
and a transformation of left exact functors invertible at both of those is invertible at the
kernel.

## Main definitions

* `Stacks.DerivedFunctor.singleUnitHomology`: the canonical comparison `w ⟶ R⁰w`, that is
  `H⁰(α)` at the complexes `X[0]`.
* `Stacks.DerivedFunctor.derivedZeroNatIso`: `R⁰w ≅ w` in degree `0`.
* `Stacks.DerivedFunctor.derivedDegreeNatIso`: `R⁰w ≅ w` in an arbitrary degree `i`, in the form
  `singleFunctor A i ⋙ Rw ⋙ homologyFunctor B i ≅ w`.
* `Stacks.DerivedFunctor.derivedDegreeNatIsoOfKInjective`: the same, with the hypothesis on
  injective objects discharged from the existence of K-injective resolutions.

## Main results

* `Stacks.DerivedFunctor.preservesFiniteLimits_singleCompDerivedCompHomology`: `R⁰w` is left
  exact.
* `Stacks.DerivedFunctor.isIso_unit_app_single_of_injective`: the unit of `Rw` is invertible at
  the complex `J[0]` of an injective object `J`.
* `Stacks.DerivedFunctor.isIso_singleUnitHomology_app`: the comparison `w ⟶ R⁰w` is invertible.

## Implementation notes

`Rw` is taken as data together with its unit `α`, as a right derived functor of
`w(-) : K(A) ⥤ D(B)` along the localization `Qh : K(A) ⥤ D(A)` at quasi-isomorphisms. Without a
unit there is no canonical map to be an isomorphism, so this is the weakest form in which the
statement has content; any two such pairs are uniquely isomorphic compatibly with their units
(`CategoryTheory.Functor.rightDerivedUnique`), so nothing depends on a construction.

`Rw.CommShift ℤ` and `Rw.IsTriangulated` are instance hypotheses, exactly as in
`StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorHomologyEdge`, which is the consumer.
For the canonical unbounded right derived functor the first is automatic -- Mathlib's instance
`CategoryTheory.Functor.IsRightDerivedFunctor.instCommShiftTotalRightDerived` applies, provided
`Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift` is imported, which is not in the
closure of the two modules above. The second is not: triangulatedness of an *unbounded* right
derived functor is a theorem with hypotheses of its own (`Functor.isTriangulated_of_leftExtension`
needs every morphism of `D(A)` to be represented by a map between complexes computing `Rw` whose
mapping cone computes it too), not an instance.

Left t-exactness enters only as `hGE`, the vanishing `R⁻¹w = 0` in the form
`(Rw (X[0])).IsGE 0`, which is strictly weaker than the `hGE` of `homologyEdge` and is implied by
it. For the unbounded right derived functor of an additive functor out of a Grothendieck abelian
category it is `Stacks.DerivedFunctor.isGE_totalRightDerived_obj`.

The invertibility of the unit on injective objects is taken as the hypothesis `hinj` in the main
results, and separately derived from the existence of K-injective resolutions in
`isIso_unit_app_single_of_injective` and `derivedDegreeNatIsoOfKInjective`. Stated this way the
construction also applies to a caller who knows which objects compute `Rw` for another reason.

`isIso_natTrans_app_of_isLimitKernelFork` repeats the content of the public
`CategoryTheory.Functor.isIso_app_of_isLimit_kernelFork` of
`StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective`; it is private and
local here only because that module publicly imports
`StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects`, whose one pre-existing long-line
warning would stop this module from ever building under `--wfail`.

The bounded-below counterpart of this file is
`StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective`, whose
`CategoryTheory.Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits`
([Stacks, Tag 05TD]) is this statement on `D⁺`; the degree-`i` object-level identification on
`D(A)` is `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso`, which carries no
naturality and is therefore not usable as `hsingle`. Instantiated at `Rw = w.mapDerivedCategory`
for an *exact* `w`, `derivedDegreeNatIso` supplies
`Stacks.DerivedFunctor.HigherDerivedOfExact.higherDerived_zero_iso` without its `Nonempty` wrapper.

## References

* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated ZeroObject DerivedCategory

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-! ## The two sides of the unit at a complex concentrated in one degree -/

variable (w : A ⥤ B) [w.Additive]

/-- The source of the unit of a right derived functor of `w`, read at the complexes `X[n]`, is
`X ↦ w(X)[n]`: applying `w` degreewise commutes with placing an object in degree `n`. -/
def mapSingleQhIso (n : ℤ) :
    HomotopyCategory.singleFunctor A n ⋙ w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ≅
      w ⋙ DerivedCategory.singleFunctor B n :=
  Functor.isoWhiskerRight (HomotopyCategory.singleFunctorPostcompQuotientIso A n)
      (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor A n)
      (Functor.isoWhiskerRight (w.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) Qh) ≪≫
    Functor.isoWhiskerRight
      (HomologicalComplex.singleMapHomologicalComplex w (ComplexShape.up ℤ) n)
      (HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ Qh) ≪≫
    Functor.isoWhiskerLeft w
      (Functor.isoWhiskerRight (HomotopyCategory.singleFunctorPostcompQuotientIso B n).symm Qh ≪≫
        (DerivedCategory.singleFunctorIsoCompQh B n).symm)

/-- **The source of `Hⁿ(α)` at the complexes `X[n]` is `w`.** The complex `w(X)[n]` has
degree-`n` cohomology `w(X)`. -/
def singleUnitSourceIso (n : ℤ) :
    HomotopyCategory.singleFunctor A n ⋙ w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⋙
        DerivedCategory.homologyFunctor B n ≅
      w :=
  Functor.isoWhiskerRight (mapSingleQhIso w n) (DerivedCategory.homologyFunctor B n) ≪≫
    Functor.isoWhiskerLeft w (DerivedCategory.singleFunctorCompHomologyFunctorIso B n) ≪≫
    Functor.rightUnitor w

variable (Rw : DerivedCategory A ⥤ DerivedCategory B)

/-- **The target of `Hⁿ(α)` at the complexes `X[n]` is `Rⁿw`.** The single functor into the
unbounded derived category factors through the homotopy category. -/
def singleUnitTargetIso (n : ℤ) :
    HomotopyCategory.singleFunctor A n ⋙ Qh ⋙ Rw ⋙ DerivedCategory.homologyFunctor B n ≅
      DerivedCategory.singleFunctor A n ⋙ Rw ⋙ DerivedCategory.homologyFunctor B n :=
  Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQh A n).symm
    (Rw ⋙ DerivedCategory.homologyFunctor B n)

variable (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ Rw)

/-- **The canonical comparison `w ⟶ Rⁿw` in the degree the object sits in**: the unit of `Rw`,
read at the complexes `X[n]` by degree-`n` cohomology. Its source and target are identified with
`w` and `Rⁿw` by `singleUnitSourceIso` and `singleUnitTargetIso`. -/
def singleUnitHomology (n : ℤ) :
    HomotopyCategory.singleFunctor A n ⋙ w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⋙
        DerivedCategory.homologyFunctor B n ⟶
      HomotopyCategory.singleFunctor A n ⋙ Qh ⋙ Rw ⋙
        DerivedCategory.homologyFunctor B n :=
  Functor.whiskerRight (Functor.whiskerLeft (HomotopyCategory.singleFunctor A n) α)
    (DerivedCategory.homologyFunctor B n)

/-- The comparison `w ⟶ Rⁿw` at an object is the unit of `Rw` at the complex `X[n]`, read by
degree-`n` cohomology. -/
lemma singleUnitHomology_app (n : ℤ) (X : A) :
    (singleUnitHomology w Rw α n).app X =
      (DerivedCategory.homologyFunctor B n).map
        (α.app ((HomotopyCategory.singleFunctor A n).obj X)) :=
  rfl

/-! ## Left exactness of `R⁰w` -/

variable [Rw.CommShift ℤ] [Rw.IsTriangulated]

/-- **`R⁰w` is left exact.** A short exact sequence of `A` gives a distinguished triangle of
`D(A)`, whose image under the triangulated functor `Rw` is distinguished; the long exact
cohomology sequence of the homological functor `H⁰` is then exact at its first two spots because
`R⁻¹w` vanishes, which is the hypothesis `hGE`. -/
lemma preservesFiniteLimits_singleCompDerivedCompHomology
    (hGE : ∀ X : A, (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0) :
    PreservesFiniteLimits (DerivedCategory.singleFunctor A 0 ⋙ Rw ⋙
      DerivedCategory.homologyFunctor B 0) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have hT : Rw.mapTriangle.obj hS.singleTriangle ∈ distTriang (DerivedCategory B) :=
    Rw.map_distinguished _ hS.singleTriangle_distinguished
  have hz : IsZero (((DerivedCategory.homologyFunctor B 0).shift (-1 : ℤ)).obj
      (Rw.obj ((DerivedCategory.singleFunctor A 0).obj S.X₃))) := by
    have := hGE S.X₃
    exact DerivedCategory.isZero_of_isGE _ 0 (-1) (by norm_num)
  exact ⟨(DerivedCategory.homologyFunctor B 0).homologySequence_exact₂ _ hT 0,
    ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₁_iff
      _ hT (-1) 0 (by ring)).2 (hz.eq_of_src _ _)⟩

/-! ## The comparison is invertible -/

section Injective

omit [Rw.CommShift ℤ] [Rw.IsTriangulated]
variable [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

omit [HasDerivedCategory.{wA} A] in
/-- The terms of the complex `J[n]` of an injective object `J` are injective: in degree `n` the
term is `J`, and in every other degree it is a zero object. -/
lemma injective_singleFunctor_obj_X (n : ℤ) (J : A) [Injective J] (m : ℤ) :
    Injective (((CochainComplex.singleFunctor A n).obj J).X m) := by
  by_cases h : m = n
  · subst h
    exact Injective.of_iso
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m J).symm) ‹_›
  · exact Injective.of_iso
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n J m h).isoZero.symm
      (inferInstanceAs (Injective (0 : A)))

/-- **The unit of `Rw` is invertible at the complex `J[0]` of an injective object.** That complex
is strictly bounded below with injective terms, hence K-injective, and a K-injective complex
computes a right derived functor as soon as K-injective resolutions exist. -/
lemma isIso_unit_app_single_of_injective
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (J : A) (hJ : Injective J) :
    IsIso (α.app ((HomotopyCategory.singleFunctor A 0).obj J)) := by
  have := injective_singleFunctor_obj_X 0 J
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh) hres).2 Qh Rw α _
    (CochainComplex.isKInjective_of_injective _ 0)

end Injective

omit [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] in
/-- A natural transformation between two functors that preserve the kernel of `g : Y₀ ⟶ Y₁` is
invertible at any kernel of `g` as soon as it is invertible at `Y₀` and at `Y₁`. -/
private lemma isIso_natTrans_app_of_isLimitKernelFork {G₁ G₂ : A ⥤ B}
    [G₁.PreservesZeroMorphisms] [G₂.PreservesZeroMorphisms]
    {X Y₀ Y₁ : A} {f : X ⟶ Y₀} {g : Y₀ ⟶ Y₁} (hfg : f ≫ g = 0)
    [PreservesLimit (parallelPair g 0) G₁] [PreservesLimit (parallelPair g 0) G₂]
    (η : G₁ ⟶ G₂) (hf : IsLimit (KernelFork.ofι f hfg))
    [IsIso (η.app Y₀)] [IsIso (η.app Y₁)] : IsIso (η.app X) := by
  have k₁ := KernelFork.mapIsLimit _ hf G₁
  have hnat : CategoryTheory.inv (η.app Y₀) ≫ G₁.map g =
      G₂.map g ≫ CategoryTheory.inv (η.app Y₁) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← η.naturality g, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have hzero : (G₂.map f ≫ CategoryTheory.inv (η.app Y₀)) ≫ G₁.map g = 0 := by
    rw [Category.assoc, hnat, ← Category.assoc, ← G₂.map_comp, hfg, G₂.map_zero, zero_comp]
  have hl : k₁.lift (KernelFork.ofι _ hzero) ≫ G₁.map f =
      G₂.map f ≫ CategoryTheory.inv (η.app Y₀) :=
    k₁.fac (KernelFork.ofι _ hzero) WalkingParallelPair.zero
  refine ⟨k₁.lift (KernelFork.ofι _ hzero), ?_, ?_⟩
  · refine Fork.IsLimit.hom_ext k₁ ?_
    dsimp
    rw [Category.assoc, hl, ← Category.assoc, ← η.naturality f, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · refine Fork.IsLimit.hom_ext (KernelFork.mapIsLimit _ hf G₂) ?_
    dsimp
    rw [Category.assoc, ← η.naturality f, ← Category.assoc, hl, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

variable [EnoughInjectives A]

/-- **The comparison `w ⟶ R⁰w` is invertible for a left exact `w`.** Both functors are left
exact, the comparison is invertible at the injective objects by `hinj`, and every object of `A`
is the kernel of a map between two injective objects -- the first two terms of an injective
resolution. -/
lemma isIso_singleUnitHomology_app [PreservesFiniteLimits w]
    (hGE : ∀ X : A, (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0)
    (hinj : ∀ J : A, Injective J →
      IsIso (α.app ((HomotopyCategory.singleFunctor A 0).obj J)))
    (X : A) : IsIso ((singleUnitHomology w Rw α 0).app X) := by
  have := preservesFiniteLimits_singleCompDerivedCompHomology Rw hGE
  have i₁ : PreservesFiniteLimits (HomotopyCategory.singleFunctor A 0 ⋙
      w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⋙
      DerivedCategory.homologyFunctor B 0) :=
    preservesFiniteLimits_of_natIso (singleUnitSourceIso w 0).symm
  have i₂ : PreservesFiniteLimits (HomotopyCategory.singleFunctor A 0 ⋙ Qh ⋙ Rw ⋙
      DerivedCategory.homologyFunctor B 0) :=
    preservesFiniteLimits_of_natIso (singleUnitTargetIso Rw 0).symm
  have hβ : ∀ J : A, Injective J → IsIso ((singleUnitHomology w Rw α 0).app J) := by
    intro J hJ
    rw [singleUnitHomology_app]
    have := hinj J hJ
    infer_instance
  let P := injectiveResolution X
  have h₀ := hβ (P.cocomplex.X 0) (P.injective 0)
  have h₁ := hβ (P.cocomplex.X 1) (P.injective 1)
  exact isIso_natTrans_app_of_isLimitKernelFork P.ι_f_zero_comp_complex_d
    (singleUnitHomology w Rw α 0) P.isLimitKernelFork

/-! ## The isomorphism -/

/-- **`R⁰w ≅ w` in degree `0`, for a left exact `w`.** -/
def derivedZeroNatIso [PreservesFiniteLimits w]
    (hGE : ∀ X : A, (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0)
    (hinj : ∀ J : A, Injective J →
      IsIso (α.app ((HomotopyCategory.singleFunctor A 0).obj J))) :
    DerivedCategory.singleFunctor A 0 ⋙ Rw ⋙ DerivedCategory.homologyFunctor B 0 ≅ w :=
  have : ∀ X, IsIso ((singleUnitHomology w Rw α 0).app X) :=
    isIso_singleUnitHomology_app w Rw α hGE hinj
  have : IsIso (singleUnitHomology w Rw α 0) := NatIso.isIso_of_isIso_app _
  (singleUnitTargetIso Rw 0).symm ≪≫ (asIso (singleUnitHomology w Rw α 0)).symm ≪≫
    singleUnitSourceIso w 0

/-- The degree-`i` form of `R⁰w` is the degree-`0` form: the single functor, the derived functor
and cohomology all commute with the shift. -/
def derivedShiftIso (i : ℤ) :
    DerivedCategory.singleFunctor A i ⋙ Rw ⋙ DerivedCategory.homologyFunctor B i ≅
      DerivedCategory.singleFunctor A 0 ⋙ Rw ⋙ DerivedCategory.homologyFunctor B 0 :=
  Functor.isoWhiskerRight ((DerivedCategory.singleFunctors A).shiftIso (-i) i 0 (by omega)).symm
      (Rw ⋙ DerivedCategory.homologyFunctor B i) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0)
      (Functor.isoWhiskerRight (Rw.commShiftIso (-i)) (DerivedCategory.homologyFunctor B i) ≪≫
        Functor.isoWhiskerLeft Rw
          ((DerivedCategory.homologyFunctor B 0).shiftIso (-i) i 0 (by omega)))

/-- **`R⁰w ≅ w` in an arbitrary degree, for a left exact `w`.** For an object `X` of `A` placed
in degree `i` of the unbounded derived category, the degree-`i` cohomology of `Rw(X[i])` is
`w(X)`, naturally in `X`.

This is the `hsingle` hypothesis of `Stacks.DerivedFunctor.homologyEdge`, which is the one place
left exactness of `w` enters the construction of the edge transformation
`Hⁱ ∘ Rw ⟶ w ∘ Hⁱ`. -/
def derivedDegreeNatIso [PreservesFiniteLimits w]
    (hGE : ∀ X : A, (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0)
    (hinj : ∀ J : A, Injective J →
      IsIso (α.app ((HomotopyCategory.singleFunctor A 0).obj J)))
    (i : ℤ) :
    DerivedCategory.singleFunctor A i ⋙ Rw ⋙ DerivedCategory.homologyFunctor B i ≅ w :=
  derivedShiftIso Rw i ≪≫ derivedZeroNatIso w Rw α hGE hinj

/-- **`R⁰w ≅ w` in an arbitrary degree**, with the hypothesis on injective objects discharged
from the existence of K-injective resolutions. -/
def derivedDegreeNatIsoOfKInjective [PreservesFiniteLimits w]
    [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hGE : ∀ X : A, (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0)
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (i : ℤ) :
    DerivedCategory.singleFunctor A i ⋙ Rw ⋙ DerivedCategory.homologyFunctor B i ≅ w :=
  derivedDegreeNatIso w Rw α hGE
    (fun J hJ => isIso_unit_app_single_of_injective w Rw α hres J hJ) i

end Stacks.DerivedFunctor

end
