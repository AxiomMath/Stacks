module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedZerothCohomologyHomological
public import StacksFrontier.CategoryTheory.Triangulated.Quotient

/-!
# The acyclic differential graded modules form a triangulated subcategory

Let `(C, O)` be a ringed site and let `A` be a sheaf of differential graded `O`-algebras. An
object of the homotopy category `K(Mod(A, d))` of right differential graded `A`-modules is
*acyclic* when the complex of sheaves of `O`-modules underlying it has vanishing cohomology in
every degree. This file proves that the acyclic objects form a strictly full saturated
triangulated subcategory of `K(Mod(A, d))`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.acyclic`: the acyclic objects of the homotopy
  category.

## Main results

* `SheafOfModules.DifferentialGradedModule.homologicalKernel_eq_acyclic`: the acyclic objects
  are exactly the objects killed by zeroth cohomology in every translate.
* `SheafOfModules.DifferentialGradedModule.acyclic_isClosedUnderIsomorphisms`,
  `SheafOfModules.DifferentialGradedModule.acyclic_isTriangulated`,
  `SheafOfModules.DifferentialGradedModule.acyclic_isSaturated`: **the acyclic objects are a
  strictly full saturated triangulated subcategory.**

## Implementation notes

The source's proof is exactly the argument carried out here: an object `M` is acyclic if and
only if `H^i(M) = H^0(M[i])` vanishes for all `i`, so the acyclic objects are the homological
kernel of `H^0`, and the homological kernel of a homological functor on a triangulated category
is a strictly full saturated triangulated subcategory — Stacks Project Tag 05RD, which this
development has as
`CategoryTheory.Functor.isTriangulated_and_isSaturated_homologicalKernel`. That zeroth
cohomology on the homotopy category is homological is the second clause of tag 0FT2,
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.zerothCohomologyFunctor_isHomological`.

The identification `H^0(M[i]) = H^i(M)` is used here **only on objects**, which is why no
comparison of the translations of `K(Mod(A, d))` with the shift of complexes on *morphisms* is
needed. On objects the identification is an equality of complexes: the complex underlying the
`i`-th translate of the class of `M` is literally the `i`-th shift of the complex underlying `M`
(`SheafOfModules.DifferentialGradedModule.HomotopyCategory.shiftFunctor_obj_complex`, read off
the field `shifted_complex` of
`SheafOfModules.DifferentialGradedModule.CanonicalShiftAxiomB`), and the cohomology of a shifted
cochain complex is Mathlib's `CochainComplex` shift sequence for the homology functor.

The hypotheses `HasSheafify X.J AddCommGrpCat.{w}` and
`X.J.WEqualsLocallyBijective AddCommGrpCat.{w}` are what make `SheafOfModules.{w} X.ringSheaf`
abelian, and hence make cohomology of its cochain complexes available; they replace the source's
standing convention that a site admits sheafification. The base is a ringed site, as in the
source, because that is the only setting in which this development has the pre-triangulated
structure on `K(Mod(A, d))`.

## References

* [Stacks Project, Tag 0FT3](https://stacks.math.columbia.edu/tag/0FT3)
* [Stacks Project, Tag 0FT2](https://stacks.math.columbia.edu/tag/0FT2)
* [Stacks Project, Tag 05RD](https://stacks.math.columbia.edu/tag/05RD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- For a short exact sequence `0 → K → L → N → 0` of cochain complexes in an abelian category,
the first map is a quasi-isomorphism exactly when `N` is acyclic. One direction is
`CategoryTheory.ShortComplex.ShortExact.acyclic_X₃`; the other reads off the long exact
cohomology sequence, in which the two neighbours of `H^i(K) → H^i(L)` are `H^{i-1}(N)` and
`H^i(N)`. -/
theorem quasiIso_f_iff_acyclic_X₃ {B : Type*} [Category* B] [Abelian B]
    {S : ShortComplex (CochainComplex B ℤ)} (hS : S.ShortExact) :
    QuasiIso S.f ↔ S.X₃.Acyclic := by
  refine ⟨fun h => hS.acyclic_X₃ h, fun h => ⟨fun i => ?_⟩⟩
  have hz : ∀ j : ℤ, IsZero (S.X₃.homology j) := fun j =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ j).1 (h j)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hepi : Epi (HomologicalComplex.homologyMap S.f i) := by
    rw [(hS.homology_exact₂ i).epi_f_iff]
    exact (hz i).eq_of_tgt _ _
  have hmono : Mono (HomologicalComplex.homologyMap S.f i) := by
    rw [(hS.homology_exact₁ (i - 1) i (by simp)).mono_g_iff]
    exact (hz (i - 1)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- **Stacks Project, Tag 0FT3.** The acyclic objects of the homotopy category of right
differential graded `A`-modules: those whose underlying complex of sheaves of `O`-modules has
vanishing cohomology in every degree. -/
@[stacks 0FT3 "the full subcategory of acyclic modules"]
def acyclic : ObjectProperty (HomotopyCategory.{u, v, w} A) :=
  fun M => M.as.complex.Acyclic

/-- Being acyclic is vanishing of cohomology in every degree. -/
theorem acyclic_iff (M : DifferentialGradedModule.{u, v, w} A) :
    acyclic.{u, v, w} A ((HomotopyCategory.quotient A).obj M) ↔
      ∀ n : ℤ, IsZero ((HomologicalComplex.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
          n).obj M.complex) :=
  forall_congr' fun n => HomologicalComplex.exactAt_iff_isZero_homology _ n

/-- Zeroth cohomology of the `n`-th translate of the class of a right differential graded module
is its cohomology in degree `n`: on objects the translate has the shifted complex, and the
cohomology of a shifted cochain complex is given by the shift sequence of the homology functor.
-/
theorem zerothCohomology_shift_isZero_iff (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    IsZero ((HomotopyCategory.zerothCohomologyFunctor.{u, v, w} A).obj
        ((CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) n).obj
          ((HomotopyCategory.quotient A).obj M))) ↔
      IsZero ((HomologicalComplex.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
          n).obj M.complex) := by
  rw [HomotopyCategory.shiftFunctor_obj_eq.{u, v, w} A n M]
  refine Iso.isZero_iff ?_
  refine Iso.trans (eqToIso ?_)
    (((HomologicalComplex.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) 0).shiftIso n 0 n (by omega)).app M.complex)
  exact congrArg (HomologicalComplex.homologyFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
    (dgShiftFunctor_complex.{u, v, w} A n M)

/-- **Stacks Project, Tag 0FT3.** The objects of the homotopy category killed by zeroth
cohomology in every translate are exactly the acyclic ones, which is the first sentence of the
source's proof. -/
theorem homologicalKernel_eq_acyclic :
    (HomotopyCategory.zerothCohomologyFunctor.{u, v, w} A).homologicalKernel =
      acyclic.{u, v, w} A := by
  ext Y
  cases Y with
  | mk M =>
    exact (forall_congr' fun n => zerothCohomology_shift_isZero_iff.{u, v, w} A M n).trans
      (acyclic_iff.{u, v, w} A M).symm

/-- **Stacks Project, Tag 0FT3.** The subcategory of acyclic objects is strictly full: it is the
homological kernel of a functor, which is closed under isomorphisms. -/
@[stacks 0FT3 "strict fullness"]
instance acyclic_isClosedUnderIsomorphisms :
    (acyclic.{u, v, w} A).IsClosedUnderIsomorphisms := by
  rw [← homologicalKernel_eq_acyclic.{u, v, w} A]
  infer_instance

/-- **Stacks Project, Tag 0FT3.** The acyclic objects form a triangulated subcategory of the
homotopy category: they are the homological kernel of zeroth cohomology, which is a homological
functor on a triangulated category. -/
@[stacks 0FT3 "triangulated subcategory"]
instance acyclic_isTriangulated : (acyclic.{u, v, w} A).IsTriangulated := by
  rw [← homologicalKernel_eq_acyclic.{u, v, w} A]
  exact (Functor.isTriangulated_and_isSaturated_homologicalKernel
    (HomotopyCategory.zerothCohomologyFunctor.{u, v, w} A)).1

/-- **Stacks Project, Tag 0FT3.** The triangulated subcategory of acyclic objects is saturated:
the homological kernel of a homological functor is stable under retracts, and a direct summand is
a retract. -/
@[stacks 0FT3 "saturation"]
instance acyclic_isSaturated : (acyclic.{u, v, w} A).IsSaturated := by
  rw [← homologicalKernel_eq_acyclic.{u, v, w} A]
  exact (Functor.isTriangulated_and_isSaturated_homologicalKernel
    (HomotopyCategory.zerothCohomologyFunctor.{u, v, w} A)).2

end SheafOfModules.DifferentialGradedModule

end
