module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.Abelian
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.Subquotient
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksCore.Algebra.Homology.HomologicalComplexAbelian

/-!
# The long exact cohomology sequence of a short exact sequence of differential graded modules

The forgetful functor from right differential graded modules over a differential graded algebra
to cochain complexes of modules over its base ring preserves short exact sequences: in the
abelian category `Mod_{(A,d)}` monomorphisms are injective and epimorphisms are surjective on
underlying modules, and exactness can be checked one homogeneous degree at a time. Consequently
every short exact sequence of differential graded modules has a long exact cohomology sequence,
with connecting homomorphism from degree `n` to degree `n + 1`.

## Main results

* `DifferentialGradedModule.Hom.injective_of_mono` and
  `DifferentialGradedModule.Hom.surjective_of_epi`: monomorphisms and epimorphisms of
  differential graded modules are injective, resp. surjective, on underlying modules.
* `DifferentialGradedModule.shortExact_forgetToCochainComplex`: the underlying sequence of
  cochain complexes of a short exact sequence is short exact.
* `DifferentialGradedModule.longExactCohomology`: the long exact cohomology sequence.

## References

* [Stacks Project, Tag 09JK](https://stacks.math.columbia.edu/tag/09JK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- A monomorphism of differential graded modules is injective on underlying modules. -/
theorem Hom.injective_of_mono {M N : DifferentialGradedModule A} (f : M ⟶ N) [Mono f] :
    Function.Injective f.toFun := by
  have hker : f.kernelι = 0 := by
    apply (cancel_mono f).1
    rw [Hom.kernelι_comp, zero_comp]
  intro x y hxy
  have hx : x - y ∈ f.ker := by rw [Hom.mem_ker, map_sub, hxy, sub_self]
  have hz := congrArg (fun k : f.kernelObj ⟶ M => k.toFun ⟨x - y, hx⟩) hker
  change x - y = 0 at hz
  exact sub_eq_zero.mp hz

/-- An epimorphism of differential graded modules is surjective on underlying modules. -/
theorem Hom.surjective_of_epi {M N : DifferentialGradedModule A} (f : M ⟶ N) [Epi f] :
    Function.Surjective f.toFun := by
  have hcok : f.cokernelπ = 0 := by
    apply (cancel_epi f).1
    rw [Hom.comp_cokernelπ, comp_zero]
  intro y
  have hz := congrArg (fun k : N ⟶ f.cokernelObj => k.toFun y) hcok
  rw [Hom.cokernelπ_toFun_apply, Hom.hom_zero_toFun] at hz
  change (Submodule.Quotient.mk y : N.M ⧸ f.range) = 0 at hz
  exact (Submodule.Quotient.mk_eq_zero _).mp hz

/-- A short exact sequence of differential graded modules is exact in each homogeneous degree. -/
private theorem exact_gradedMap (S : ShortComplex (DifferentialGradedModule A))
    (hS : S.ShortExact) (n : ℤ) :
    Function.Exact (S.f.gradedMap n) (S.g.gradedMap n) := by
  intro y
  constructor
  · intro hy
    have hmem : (y : S.X₂.M) ∈ S.g.ker := congrArg Subtype.val hy
    let cone : KernelFork S.g := KernelFork.ofι S.g.kernelι (Hom.kernelι_comp S.g)
    refine ⟨(hS.fIsKernel.lift cone).gradedMap n ⟨⟨y, hmem⟩, y.2⟩, Subtype.ext ?_⟩
    exact congrArg (fun k : S.g.kernelObj ⟶ S.X₂ => k.toFun ⟨y, hmem⟩)
      (hS.fIsKernel.fac cone WalkingParallelPair.zero)
  · rintro ⟨x, rfl⟩
    exact Subtype.ext <|
      LinearMap.congr_fun (congrArg (fun k : S.X₁ ⟶ S.X₃ => k.toFun) S.zero) (x : S.X₁.M)

/-- A short exact sequence of differential graded modules remains short exact after forgetting
to cochain complexes of modules over the base ring. -/
@[stacks 09JK "the underlying exact sequence of cochain complexes"]
theorem shortExact_forgetToCochainComplex (S : ShortComplex (DifferentialGradedModule A))
    (hS : S.ShortExact) :
    (S.map (forgetToCochainComplex A)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  let _ : Mono S.f := hS.mono_f
  let _ : Epi S.g := hS.epi_g
  intro n
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact exact_gradedMap A S hS n
  · rw [ModuleCat.mono_iff_injective]
    show Function.Injective (S.f.gradedMap n)
    exact fun x y hxy => Subtype.ext (Hom.injective_of_mono A S.f (congrArg Subtype.val hxy))
  · rw [ModuleCat.epi_iff_surjective]
    show Function.Surjective (S.g.gradedMap n)
    intro y
    obtain ⟨x, hx⟩ := Hom.surjective_of_epi A S.g (y : S.X₃.M)
    have hgraded := DirectSum.coe_decompose_apply_map S.X₂.grading S.X₃.grading S.g.toFun
      (fun i z hz => S.g.map_grading i z hz) x n
    rw [hx, DirectSum.decompose_of_mem_same S.X₃.grading y.2] at hgraded
    exact ⟨⟨DirectSum.decompose S.X₂.grading x n,
      (DirectSum.decompose S.X₂.grading x n).2⟩, Subtype.ext hgraded.symm⟩

/-- The cohomology of a short exact sequence of differential graded modules forms a long exact
sequence, including its canonical connecting maps. -/
@[stacks 09JK "the long exact cohomology sequence"]
theorem longExactCohomology (S : ShortComplex (DifferentialGradedModule A))
    (hS : S.ShortExact) (n m : ℤ) (hnm : (ComplexShape.up ℤ).Rel n m) :
    (HomologicalComplex.HomologySequence.composableArrows₅
      (C := ModuleCat.{u} R) (c := ComplexShape.up ℤ)
      (S₁ := S.map (forgetToCochainComplex A))
      (shortExact_forgetToCochainComplex A S hS) n m hnm).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (shortExact_forgetToCochainComplex A S hS) n m hnm

end DifferentialGradedModule
