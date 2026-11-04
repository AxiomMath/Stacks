module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.LinearAlgebra.Dimension.Localization
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence, reflexivity and rank of an associated sheaf

Let `R` be a commutative ring and `M` an `R`-module, and let `M̃` be the quasi-coherent sheaf
on `Spec R` associated to `M`.  This file collects general facts about `M̃` of three kinds.

Finiteness: over a Noetherian ring, finiteness of `M` makes `M̃` coherent.  This is the
combination of `tilde_isFinitePresentation_iff` with the equivalence of the five
characterizations of coherence on a locally Noetherian scheme.

Rank: over a domain, the stalk of `M̃` at a point `x` of `Spec R` is the localization of `M` at
the corresponding prime, and localization at a submonoid of nonzerodivisors changes neither the
rank of the ring over which the module is taken nor the rank of the module.  So the rank of the
stalk over the local ring is the rank of `M` over `R`, uniformly in `x`.  At the generic point
the residue-field fibre is computed instead, and for a torsion-free `M` embedding into `R` it is
one-dimensional.

Reflexivity: over a Noetherian domain the stalks of `M̃` are flat base changes of `M`, hence
reflexive as soon as `M` is; reflexivity of `M̃` as a sheaf then follows because reflexivity is
a condition on the stalks.

## Main results

* `AlgebraicGeometry.tilde_isCoherent_of_finite` (in `CoherenceCriteria.Basic`, used here):
  over a Noetherian ring, the sheaf associated to a finite module is coherent.
* `AlgebraicGeometry.rank_stalk_tilde`: over a domain, the rank of a stalk of `M̃` over the
  local ring there is the rank of `M` over `R`; `rank_stalk_tilde_eq_one` is the rank-one case.
* `AlgebraicGeometry.isReflexive_stalk_tilde`: over a Noetherian domain, the stalks of the sheaf
  associated to a finite reflexive module are reflexive.
* `AlgebraicGeometry.isReflexive_tilde`: over a Noetherian domain, the sheaf associated to a
  finite reflexive module is reflexive.
* `AlgebraicGeometry.finrank_eq_one_of_injective`: a finite module with injective linear maps
  both from and into the base ring has rank one.
* `AlgebraicGeometry.fiberRank_tilde_genericPoint_eq_one`: over a domain, the fibre rank of `M̃`
  at the generic point is one for a nontrivial torsion-free `M` embedding into `R`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If `R` is a nontrivial commutative ring and `M` a finite `R`-module admitting injective
linear maps `R →ₗ[R] M` and `M →ₗ[R] R`, then `M` has rank one. -/
theorem finrank_eq_one_of_injective {R M : Type*}
    [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : R →ₗ[R] M) (hf : Function.Injective f)
    (g : M →ₗ[R] R) (hg : Function.Injective g) :
    Module.finrank R M = 1 := by
  simpa using le_antisymm (LinearMap.finrank_le_finrank_of_injective hg)
    (LinearMap.finrank_le_finrank_of_injective hf)

/-- Over a domain, the stalk of `M̃` at a point `x` of `Spec R` has the same rank over the local
ring `𝒪_{Spec R, x}` as `M` has over `R`. -/
theorem rank_stalk_tilde {R : CommRingCat.{u}} [IsDomain R] (M : ModuleCat.{u} R)
    (x : Spec R) :
    Module.rank ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) = Module.rank R M := by
  let p : PrimeSpectrum R := x
  let B : Type u := (Spec R).presheaf.stalk x
  let N : Type u := (tilde M).presheaf.stalk x
  let S := p.asIdeal.primeCompl
  let : Algebra R B := StructureSheaf.stalkAlgebra R p
  let : Module R N := inferInstanceAs (Module R ((tilde M).presheaf.stalk p))
  let : Module B N := AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde M) x
  have : IsScalarTower R B N := .of_algebraMap_smul fun _ _ => rfl
  let : IsLocalization.AtPrime B p.asIdeal := StructureSheaf.IsLocalization.to_stalk R p
  have hS : S ≤ nonZeroDivisors R := fun y hy =>
    mem_nonZeroDivisors_of_ne_zero fun h => hy (h ▸ p.asIdeal.zero_mem)
  show Module.rank B N = _
  rw [IsLocalization.rank_eq B S hS]
  exact IsLocalizedModule.rank_eq S hS (tilde.toStalk M p).hom

/-- Over a Noetherian domain, every stalk of the sheaf associated to a finite reflexive module
is a reflexive module over the corresponding stalk of the structure sheaf. -/
theorem isReflexive_stalk_tilde {R : CommRingCat.{u}} [IsDomain R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M] (x : Spec R) :
    Module.IsReflexive ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) := by
  let p : PrimeSpectrum R := x
  let B : Type u := (Spec R).presheaf.stalk x
  let N : Type u := (tilde M).presheaf.stalk x
  let S := p.asIdeal.primeCompl
  let : Algebra R B := StructureSheaf.stalkAlgebra R p
  let : Module R N := inferInstanceAs (Module R ((tilde M).presheaf.stalk p))
  let : Module B N := AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde M) x
  have : IsScalarTower R B N := .of_algebraMap_smul fun _ _ => rfl
  let : IsLocalization.AtPrime B p.asIdeal := StructureSheaf.IsLocalization.to_stalk R p
  have : IsDomain B := IsLocalization.isDomain_of_atPrime B p.asIdeal
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing S B inferInstance
  have : Module.Flat R B := IsLocalization.flat B S
  have : Module.IsReflexive B (TensorProduct R B M) := isReflexive_baseChange_of_flat
  show Module.IsReflexive B N
  exact Module.equiv (IsLocalizedModule.isBaseChange S B (tilde.toStalk M p).hom).equiv

/-- Over a domain, if `M` is a finite module of rank one then every stalk of `M̃` has rank one
over the corresponding stalk of the structure sheaf. -/
theorem rank_stalk_tilde_eq_one {R : CommRingCat.{u}} [IsDomain R] (M : ModuleCat.{u} R)
    (hM : Module.finrank R M = 1) (x : Spec R) :
    Module.rank ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) = 1 := by
  rw [rank_stalk_tilde M x, Module.rank_eq_one_iff_finrank_eq_one]
  exact hM

/-- Over a Noetherian domain, the sheaf associated to a finite reflexive module is a reflexive
module on `Spec R`. -/
theorem isReflexive_tilde {R : CommRingCat.{u}} [IsDomain R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M] :
    Stacks.AlgebraicGeometry.ReflexiveModules.IsReflexive (tilde M) := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let : (tilde M).IsFinitePresentation := (tilde_isFinitePresentation_iff M).2 inferInstance
  let : (tilde M).IsCoherent := tilde_isCoherent_of_finite M
  let : (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
      (tilde M)).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFinitePresentation_dualSheaf (tilde M)
  exact Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_of_forall_isReflexive_stalk
    (tilde M) (isReflexive_stalk_tilde M)

/-- Over a domain, a nontrivial torsion-free module admitting an injective linear map into `R`
has associated sheaf of fibre rank one at the generic point of `Spec R`. -/
@[ega "I 7.4.3" "converse"]
theorem fiberRank_tilde_genericPoint_eq_one {R : CommRingCat.{u}} [IsDomain R]
    (M : ModuleCat.{u} R) [Nontrivial M] [Module.IsTorsionFree R M]
    (f : M →ₗ[R] R) (hf : Function.Injective f) :
    Scheme.Modules.fiberRank (tilde M) (genericPoint (Spec R)) = 1 := by
  let X := Spec R
  let x := genericPoint X
  let K := X.functionField
  let N := (tilde M).presheaf.stalk x
  let p : PrimeSpectrum R := x
  let : p.asIdeal.IsPrime := p.isPrime
  let : Algebra R K := StructureSheaf.stalkAlgebra R p
  let : Module K N := AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde M) x
  let : Module R N := inferInstanceAs (Module R ((tilde M).presheaf.stalk p))
  let : IsScalarTower R K N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g := tilde.toStalk M p
  let : IsLocalization.AtPrime K p.asIdeal := StructureSheaf.IsLocalization.to_stalk R p
  let : Module.Flat R K := IsLocalization.flat K p.asIdeal.primeCompl
  let e := (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl K g.hom).equiv
  let j : N →ₗ[K] K :=
    (TensorProduct.AlgebraTensorModule.rid R K K).toLinearMap ∘ₗ
      (f.baseChange K) ∘ₗ e.symm.toLinearMap
  have hj : Function.Injective j :=
    (TensorProduct.AlgebraTensorModule.rid R K K).injective.comp
      ((Module.Flat.lTensor_preserves_injective_linearMap f hf).comp e.symm.injective)
  have hg : Function.Injective g.hom :=
    (IsLocalizedModule.injective_iff_isRegular p.asIdeal.primeCompl g.hom).2 fun c =>
      smul_right_injective M
        (mem_nonZeroDivisors_iff_ne_zero.mp
          (p.asIdeal.primeCompl_le_nonZeroDivisors c.property))
  let : Nontrivial N := hg.nontrivial
  let : Module.Finite K N := Module.Finite.of_injective j hj
  have hn : Module.finrank K N = 1 := by
    have hle := LinearMap.finrank_le_finrank_of_injective hj
    have hpos : 0 < Module.finrank K N := Module.finrank_pos
    simpa using Nat.le_antisymm (by simpa using hle) hpos
  let : Algebra K (X.residueField x) := (X.residue x).hom.toAlgebra
  show Module.finrank (X.residueField x) (TensorProduct K (X.residueField x) N) = 1
  rw [Module.finrank_baseChange, hn]

end AlgebraicGeometry

end
