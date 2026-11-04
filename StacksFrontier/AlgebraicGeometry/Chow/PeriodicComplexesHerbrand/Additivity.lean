module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.Algebra.Homology.HomologicalComplexAbelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Defs

/-!
# Additivity of the length of a two-periodic complex

In a short exact sequence of two-periodic complexes, finite length of the cohomology of any
two complexes implies finite length of the cohomology of the third. The periodic length is
additive on such a sequence.

## Main definitions

* `AlgebraicGeometry.HasFiniteLengthHomology` says that both cohomology modules of a
  two-periodic complex have finite length.

## Main results

* `AlgebraicGeometry.finiteLengthHomology_X3_of_shortExact`,
  `AlgebraicGeometry.finiteLengthHomology_X2_of_shortExact`, and
  `AlgebraicGeometry.finiteLengthHomology_X1_of_shortExact` give the two-out-of-three property.
* `AlgebraicGeometry.periodicLength_additive_of_shortExact` gives additivity of periodic length.

## Implementation notes

A two-periodic complex is represented by a homological complex indexed by `ZMod 2`. A short
exact sequence is represented by a `ShortComplex` in the abelian category of these complexes.
The three two-out-of-three implications are separate declarations, while additivity accepts
any of the three possible pairs of finiteness hypotheses.

## References

* [Stacks Project, Tag 0EA7](https://stacks.math.columbia.edu/tag/0EA7)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A module sitting in the middle of an exact sequence of finite-length modules has finite
length. -/
private lemma finiteLength_of_exact {R : Type u} [Ring R]
    {L M N : Type v} [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : L →ₗ[R] M) (g : M →ₗ[R] N) (hfg : Function.Exact f g)
    (hL : IsFiniteLength R L) (hN : IsFiniteLength R N) : IsFiniteLength R M := by
  let : IsNoetherian R L := (isFiniteLength_iff_isNoetherian_isArtinian.mp hL).1
  let : IsArtinian R L := (isFiniteLength_iff_isNoetherian_isArtinian.mp hL).2
  let : IsNoetherian R N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1
  let : IsArtinian R N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_range_eq_ker f g (LinearMap.exact_iff.mp hfg).symm,
      isArtinian_of_range_eq_ker f g (LinearMap.exact_iff.mp hfg).symm⟩

/-- An exact short complex of modules gives exact underlying linear maps. -/
private lemma function_exact_of_exact {R : Type u} [Ring R]
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.Exact) : Function.Exact S.f.hom S.g.hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS

/-- The middle term of an exact short complex of modules has finite length as soon as the two
outer terms do. -/
private lemma finiteLength_of_exact_cat {R : Type u} [Ring R]
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.Exact)
    (h₁ : IsFiniteLength R S.X₁) (h₃ : IsFiniteLength R S.X₃) :
    IsFiniteLength R S.X₂ :=
  finiteLength_of_exact S.f.hom S.g.hom (function_exact_of_exact hS) h₁ h₃

/-- The length of a finite-length module is the sum of the lengths of the kernel and of the
range of any linear map out of it, as a natural number. -/
private lemma lengthToNat_eq_ker_add_range {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hM : IsFiniteLength R M) :
    (Module.length R M).toNat = (Module.length R (LinearMap.ker f)).toNat +
      (Module.length R (LinearMap.range f)).toNat := by
  have h := Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by simp))
  rw [h, ENat.toNat_add]
  · exact Module.length_ne_top_iff.mpr
      (IsFiniteLength.of_injective (f := (LinearMap.ker f).subtype) hM
        (Submodule.subtype_injective _))
  · exact Module.length_ne_top_iff.mpr
      (IsFiniteLength.of_surjective (f := f.rangeRestrict) hM f.surjective_rangeRestrict)

/-- For an exact hexagon of finite-length modules, the alternating sum of the lengths of the
middle column is the sum of those of the two outer columns. -/
private lemma alternatingLength_six_of_exact {R : Type u} [Ring R]
    {A₀ B₀ C₀ A₁ B₁ C₁ : Type v}
    [AddCommGroup A₀] [Module R A₀] [AddCommGroup B₀] [Module R B₀]
    [AddCommGroup C₀] [Module R C₀] [AddCommGroup A₁] [Module R A₁]
    [AddCommGroup B₁] [Module R B₁] [AddCommGroup C₁] [Module R C₁]
    (f₀ : A₀ →ₗ[R] B₀) (g₀ : B₀ →ₗ[R] C₀) (d₀ : C₀ →ₗ[R] A₁)
    (f₁ : A₁ →ₗ[R] B₁) (g₁ : B₁ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] A₀)
    (efg₀ : Function.Exact f₀ g₀) (egd₀ : Function.Exact g₀ d₀)
    (edf₁ : Function.Exact d₀ f₁) (efg₁ : Function.Exact f₁ g₁)
    (egd₁ : Function.Exact g₁ d₁) (edf₀ : Function.Exact d₁ f₀)
    (hA₀ : IsFiniteLength R A₀) (hB₀ : IsFiniteLength R B₀)
    (hC₀ : IsFiniteLength R C₀) (hA₁ : IsFiniteLength R A₁)
    (hB₁ : IsFiniteLength R B₁) (hC₁ : IsFiniteLength R C₁) :
    ((Module.length R B₀).toNat : ℤ) - (Module.length R B₁).toNat =
      (((Module.length R A₀).toNat : ℤ) - (Module.length R A₁).toNat) +
      (((Module.length R C₀).toNat : ℤ) - (Module.length R C₁).toNat) := by
  have hA₀' := lengthToNat_eq_ker_add_range f₀ hA₀
  have hB₀' := lengthToNat_eq_ker_add_range g₀ hB₀
  have hC₀' := lengthToNat_eq_ker_add_range d₀ hC₀
  have hA₁' := lengthToNat_eq_ker_add_range f₁ hA₁
  have hB₁' := lengthToNat_eq_ker_add_range g₁ hB₁
  have hC₁' := lengthToNat_eq_ker_add_range d₁ hC₁
  rw [LinearMap.exact_iff.mp efg₀] at hB₀'
  rw [LinearMap.exact_iff.mp egd₀] at hC₀'
  rw [LinearMap.exact_iff.mp edf₁] at hA₁'
  rw [LinearMap.exact_iff.mp efg₁] at hB₁'
  rw [LinearMap.exact_iff.mp egd₁] at hC₁'
  rw [LinearMap.exact_iff.mp edf₀] at hA₀'
  omega

/-- In the two-periodic shape, `i` is related to `i + 1`. -/
private lemma up_rel_self_add_one (i : ZMod 2) :
    (ComplexShape.up (ZMod 2)).Rel i (i + 1) := by
  simp

/-- In the two-periodic shape, `i + 1` is related back to `i`. -/
private lemma up_rel_add_one_self (i : ZMod 2) :
    (ComplexShape.up (ZMod 2)).Rel (i + 1) i := by
  simp only [ComplexShape.up_Rel]
  revert i
  decide

/-- A two-periodic complex has finite-length cohomology if its cohomology module in every
degree has finite length. -/
public abbrev HasFiniteLengthHomology {R : Type u} [Ring R]
    (C : HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))) : Prop :=
  ∀ i : ZMod 2, IsFiniteLength R (C.homology i)

/-- In a short exact sequence of two-periodic complexes, finite-length cohomology of the first
two terms implies finite-length cohomology of the third. -/
@[stacks 0EA7 "two-out-of-three, third term"]
public lemma finiteLengthHomology_X3_of_shortExact {R : Type u} [Ring R]
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))))
    (hS : S.ShortExact) (h₁ : HasFiniteLengthHomology S.X₁)
    (h₂ : HasFiniteLengthHomology S.X₂) : HasFiniteLengthHomology S.X₃ := by
  intro i
  exact finiteLength_of_exact_cat (hS.homology_exact₃ i (i + 1)
    (up_rel_self_add_one i)) (h₂ i) (h₁ (i + 1))

/-- In a short exact sequence of two-periodic complexes, finite-length cohomology of the outer
terms implies finite-length cohomology of the middle term. -/
@[stacks 0EA7 "two-out-of-three, middle term"]
public lemma finiteLengthHomology_X2_of_shortExact {R : Type u} [Ring R]
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))))
    (hS : S.ShortExact) (h₁ : HasFiniteLengthHomology S.X₁)
    (h₃ : HasFiniteLengthHomology S.X₃) : HasFiniteLengthHomology S.X₂ := by
  intro i
  exact finiteLength_of_exact_cat (hS.homology_exact₂ i) (h₁ i) (h₃ i)

/-- In a short exact sequence of two-periodic complexes, finite-length cohomology of the last
two terms implies finite-length cohomology of the first. -/
@[stacks 0EA7 "two-out-of-three, first term"]
public lemma finiteLengthHomology_X1_of_shortExact {R : Type u} [Ring R]
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))))
    (hS : S.ShortExact) (h₂ : HasFiniteLengthHomology S.X₂)
    (h₃ : HasFiniteLengthHomology S.X₃) : HasFiniteLengthHomology S.X₁ := by
  intro i
  exact finiteLength_of_exact_cat (hS.homology_exact₁ (i + 1) i
    (up_rel_add_one_self i)) (h₃ (i + 1)) (h₂ i)

/-- Periodic length is additive on a short exact sequence of two-periodic complexes as soon as
the cohomology of any two of its terms has finite length. -/
@[stacks 0EA7 "additivity"]
public lemma periodicLength_additive_of_shortExact {R : Type u} [Ring R]
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))))
    (hS : S.ShortExact)
    (hfin : (HasFiniteLengthHomology S.X₁ ∧ HasFiniteLengthHomology S.X₂) ∨
      (HasFiniteLengthHomology S.X₁ ∧ HasFiniteLengthHomology S.X₃) ∨
      (HasFiniteLengthHomology S.X₂ ∧ HasFiniteLengthHomology S.X₃)) :
    periodicLength S.X₂ = periodicLength S.X₁ + periodicLength S.X₃ := by
  obtain ⟨hA, hB, hC⟩ : HasFiniteLengthHomology S.X₁ ∧
      HasFiniteLengthHomology S.X₂ ∧ HasFiniteLengthHomology S.X₃ := by
    rcases hfin with ⟨hA, hB⟩ | ⟨hA, hC⟩ | ⟨hB, hC⟩
    · exact ⟨hA, hB, finiteLengthHomology_X3_of_shortExact S hS hA hB⟩
    · exact ⟨hA, finiteLengthHomology_X2_of_shortExact S hS hA hC, hC⟩
    · exact ⟨finiteLengthHomology_X1_of_shortExact S hS hB hC, hB, hC⟩
  refine alternatingLength_six_of_exact
    (HomologicalComplex.homologyMap S.f (0 : ZMod 2)).hom
    (HomologicalComplex.homologyMap S.g (0 : ZMod 2)).hom
    (hS.δ (0 : ZMod 2) (1 : ZMod 2) (by decide)).hom
    (HomologicalComplex.homologyMap S.f (1 : ZMod 2)).hom
    (HomologicalComplex.homologyMap S.g (1 : ZMod 2)).hom
    (hS.δ (1 : ZMod 2) (0 : ZMod 2) (by decide)).hom
    (function_exact_of_exact (hS.homology_exact₂ 0))
    (function_exact_of_exact (hS.homology_exact₃ 0 1 (by decide)))
    (function_exact_of_exact (hS.homology_exact₁ 0 1 (by decide)))
    (function_exact_of_exact (hS.homology_exact₂ 1))
    (function_exact_of_exact (hS.homology_exact₃ 1 0 (by decide)))
    (function_exact_of_exact (hS.homology_exact₁ 1 0 (by decide)))
    (hA 0) (hB 0) (hC 0) (hA 1) (hB 1) (hC 1)

end AlgebraicGeometry
