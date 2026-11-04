module

public import StacksFrontier.RingTheory.Koszul.Defs
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.LinearAlgebra.ExteriorAlgebra.Prod
public import StacksCore.Tactic.StacksAttribute

/-!
# The inverse system of truncated Koszul complexes

For a finite sequence `f` in a commutative ring, the complexes obtained from the Koszul
complexes on the coordinatewise powers of `f` form an inverse system.

## Main definitions

* `Koszul.coordinatewiseMul` is coordinatewise multiplication on a finite free module.
* `Koszul.koszulIdealComplex` is the shifted, sign-changed truncation `I^•(f)`.
* `Koszul.KoszulIdealComplexSystem` records the canonical transition maps.
* `Koszul.koszulIdealComplexSystem` constructs the inverse system
  `I^•(f) ← I^•(f²) ← I^•(f³) ← ⋯`.

## References

* [Stacks Project, Tag 08CY](https://stacks.math.columbia.edu/tag/08CY)
* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
-/

@[expose] public section

open CategoryTheory

namespace Koszul

universe u

variable {A : Type u} [CommRing A]

/-- Coordinatewise multiplication on a finite free module. -/
def coordinatewiseMul {r : ℕ} (f : Fin r → A) :
    (Fin r → A) →ₗ[A] (Fin r → A) where
  toFun x i := f i * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ac_rfl

/-- The complex `I^•(f)`: after reversing its nonpositive cohomological grading,
degree `n` is degree `n + 1` of the Koszul complex, with negated differential. -/
noncomputable def koszulIdealComplex {r : ℕ} (f : Fin r → A) :
    ChainComplex (ModuleCat.{u} A) ℕ where
  X n := (Koszul.seqComplex f).X (n + 1)
  d i j := - (Koszul.seqComplex f).d (i + 1) (j + 1)
  shape i j h := by
    rw [(Koszul.seqComplex f).shape (i + 1) (j + 1)]
    · exact neg_zero
    · simpa [ComplexShape.down_Rel] using h
  d_comp_d' i j k hij hjk := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
      (Koszul.seqComplex f).d_comp_d (i + 1) (j + 1) (k + 1)]

/-- The stage with exponent `e + 1` in the inverse system attached to `f`. -/
noncomputable abbrev koszulIdealComplexPower {r : ℕ} (f : Fin r → A) (e : ℕ) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  koszulIdealComplex (fun i ↦ f i ^ (e + 1))

/-- Data of the inverse system of the complexes `I^•(f₁^e, …, f_r^e)`, consisting of its
successor transition maps; the component in degree `n` is the map on `(n+1)`st exterior powers
induced by coordinatewise multiplication by `f`. -/
structure KoszulIdealComplexSystem {r : ℕ} (f : Fin r → A) where
  /-- The transition from exponent `e + 2` to exponent `e + 1`. -/
  transition (e : ℕ) :
    koszulIdealComplexPower f (e + 1) ⟶ koszulIdealComplexPower f e
  /-- In degree `n` the transition is the exterior power of coordinatewise multiplication. -/
  transition_f (e n : ℕ) :
    (transition e).f n =
      ModuleCat.ofHom (exteriorPower.map (n + 1) (coordinatewiseMul f))

namespace KoszulIdealComplexSystem

/-- The inverse-system functor associated to the successor transition maps. -/
noncomputable def diagram {r : ℕ} {f : Fin r → A}
    (S : KoszulIdealComplexSystem f) :
    ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} A) ℕ :=
  Functor.ofOpSequence S.transition

end KoszulIdealComplexSystem

/-- The canonical inverse system `I^•(f) ← I^•(f²) ← I^•(f³) ← ⋯`. -/
@[stacks 08CY]
noncomputable def koszulIdealComplexSystem {r : ℕ} (f : Fin r → A) :
    KoszulIdealComplexSystem f := by
  have hdual : ∀ e : ℕ,
      (Koszul.seqDual (fun i ↦ f i ^ (e + 1))).comp (coordinatewiseMul f) =
        Koszul.seqDual (fun i ↦ f i ^ (e + 2)) := fun e => by
    ext x
    simp [Koszul.seqDual_apply, coordinatewiseMul, pow_succ', mul_assoc,
      mul_comm, mul_left_comm]
  let tr : ∀ e : ℕ,
      koszulIdealComplexPower f (e + 1) ⟶ koszulIdealComplexPower f e := fun e =>
    { f := fun n => ModuleCat.ofHom (exteriorPower.map (n + 1) (coordinatewiseMul f))
      comm' := by
        rintro i j (rfl : j + 1 = i)
        dsimp [koszulIdealComplexPower, koszulIdealComplex, Koszul.seqComplex,
          Koszul.complex]
        rw [ChainComplex.of_d, ChainComplex.of_d]
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        change (⋀[A]^(j + 2) (Fin r → A)) at x
        dsimp [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
        change
          (-Koszul.d (Koszul.seqDual (fun i ↦ f i ^ (e + 1))) (j + 1))
              (exteriorPower.map (j + 1 + 1) (coordinatewiseMul f) x) =
            (exteriorPower.map (j + 1) (coordinatewiseMul f))
              ((-Koszul.d (Koszul.seqDual (fun i ↦ f i ^ (e + 2))) (j + 1)) x)
        simp only [LinearMap.neg_apply, map_neg, neg_inj]
        apply Subtype.ext
        rw [Koszul.d_apply_coe, exteriorPower.coe_map, exteriorPower.coe_map, Koszul.d_apply_coe,
          ← map_contractLeft_pow (coordinatewiseMul f)
            (Koszul.seqDual (fun i ↦ f i ^ (e + 1))) (j + 2) x]
        · rw [hdual e]
        · exact x.2 }
  exact
    { transition := tr
      transition_f _ _ := rfl }

end Koszul
