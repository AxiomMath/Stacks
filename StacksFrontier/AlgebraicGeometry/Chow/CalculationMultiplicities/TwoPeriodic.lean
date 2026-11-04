module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.FinCases

/-!
# The two-periodic complex of a pair of mutually annihilating endomorphisms

Two endomorphisms of a module that annihilate each other in both orders assemble into a
`ZMod 2`-indexed complex with those two maps as its differentials. Its cohomology in each
degree is computed by the quotient of the kernel of one map by the image of the other.

## Main definitions

* `AlgebraicGeometry.twoPeriodicComplex` is the two-periodic complex associated to two mutually
  annihilating endomorphisms.
* `AlgebraicGeometry.twoPeriodicComplexMap` is the morphism of two-periodic complexes induced by
  a linear map intertwining both differentials.

## Main results

* `AlgebraicGeometry.homology_length_eq_ker_quotient` identifies the length of the cohomology of
  the two-periodic complex in either degree.
* `AlgebraicGeometry.quotient_length_of_bijective_map` compares the lengths of the quotients by
  a submodule and by its preimage under a surjection.

## Implementation notes

The differential out of degree zero is the first endomorphism and the differential out of
degree one is the second, matching the ordering of the multiplicities in the source. The
cohomology computation is phrased through the short complex `HomologicalComplex.sc`, whose
`ModuleCat` left homology data presents the cohomology as a quotient of an explicit kernel.

## References

* [Stacks Project, Tag 0EAB](https://stacks.math.columbia.edu/tag/0EAB)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The length of a quotient is unchanged when the submodule and the ambient module are both
pulled back along a surjection. -/
public lemma quotient_length_of_bijective_map {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (S : Submodule R N) :
    Module.length R (M ⧸ S.comap f) = Module.length R (N ⧸ S) := by
  refine (LinearEquiv.ofBijective ((S.comap f).mapQ S f le_rfl)
    ⟨fun x y hxy => ?_, fun y => ?_⟩).length_eq
  · induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        exact (Submodule.Quotient.eq (S.comap f)).2
          (by simpa only [Submodule.mem_comap, map_sub] using
            ((Submodule.Quotient.eq S).1 hxy))
  · induction y using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- The two-periodic complex with differential `f` out of degree zero and differential `g` out
of degree one. -/
public noncomputable def twoPeriodicComplex {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (f g : Module.End R M) (hfg : f * g = 0) (hgf : g * f = 0) :
    HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2)) where
  X _ := ModuleCat.of R M
  d i j := if (ComplexShape.up (ZMod 2)).Rel i j then
    if i = 0 then ModuleCat.ofHom f else ModuleCat.ofHom g
    else 0
  shape _ _ hij := ite_eq_right hij
  d_comp_d' i j k hij hjk := by
    obtain rfl : i + 1 = j := hij
    obtain rfl : i + 1 + 1 = k := hjk
    fin_cases i <;> simp only <;> ext x
    exacts [LinearMap.congr_fun hgf x, LinearMap.congr_fun hfg x]

/-- The cohomology of the two-periodic complex in degree zero is the kernel of the first
differential modulo the image of the second, and symmetrically in degree one. -/
public lemma homology_length_eq_ker_quotient {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (f g : Module.End R M) (hfg : f * g = 0) (hgf : g * f = 0)
    (i : ZMod 2) (hi : i = 0 ∨ i = 1) :
    Module.length R ((twoPeriodicComplex f g hfg hgf).homology i) =
      if i = 0 then
        Module.length R ((LinearMap.ker f) ⧸
          (LinearMap.range g).comap (LinearMap.ker f).subtype)
      else
        Module.length R ((LinearMap.ker g) ⧸
          (LinearMap.range f).comap (LinearMap.ker g).subtype) := by
  let C := twoPeriodicComplex f g hfg hgf
  let S := C.sc i
  have h : S.g.hom = (if i = 0 then f else g) ∧ S.f.hom = (if i = 0 then g else f) := by
    rcases hi with rfl | rfl <;> refine ⟨?_, ?_⟩ <;>
      simp [S, C, twoPeriodicComplex, CochainComplex.next, CochainComplex.prev,
        show (1 : ZMod 2) + 1 = 0 by decide] <;> rfl
  have hquot : LinearMap.range S.moduleCatToCycles =
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩
  show Module.length R S.homology = _
  rw [S.moduleCatHomologyIso.toLinearEquiv.length_eq]
  show Module.length R ((LinearMap.ker S.g.hom) ⧸
    LinearMap.range S.moduleCatToCycles) = _
  rw [hquot, h.1, h.2]
  rcases hi with rfl | rfl <;> rfl

/-- A linear map intertwining both differentials induces a morphism of the two-periodic
complexes they define. -/
public noncomputable def twoPeriodicComplexMap {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f g : Module.End R M) (hfg : f * g = 0) (hgf : g * f = 0)
    (f' g' : Module.End R N) (hfg' : f' * g' = 0) (hgf' : g' * f' = 0)
    (u : M →ₗ[R] N) (hf : u ∘ₗ f = f' ∘ₗ u) (hg : u ∘ₗ g = g' ∘ₗ u) :
    twoPeriodicComplex f g hfg hgf ⟶ twoPeriodicComplex f' g' hfg' hgf' where
  f _ := ModuleCat.ofHom u
  comm' i j hij := by
    fin_cases i <;> fin_cases j <;>
      ext y <;> simp only [twoPeriodicComplex] <;> split_ifs <;>
        first
          | exact (LinearMap.congr_fun hf y).symm
          | exact (LinearMap.congr_fun hg y).symm

/-- Every component of the morphism induced by an intertwining linear map is that map. -/
@[simp]
public theorem twoPeriodicComplexMap_f {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f g : Module.End R M) (hfg : f * g = 0) (hgf : g * f = 0)
    (f' g' : Module.End R N) (hfg' : f' * g' = 0) (hgf' : g' * f' = 0)
    (u : M →ₗ[R] N) (hf : u ∘ₗ f = f' ∘ₗ u) (hg : u ∘ₗ g = g' ∘ₗ u) (i : ZMod 2) :
    (twoPeriodicComplexMap f g hfg hgf f' g' hfg' hgf' u hf hg).f i = ModuleCat.ofHom u :=
  rfl

end AlgebraicGeometry
