module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksFrontier.RingTheory.Flat.Finiteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The torsion-free quotient of a finite module over a valuation ring

Let `A` be a valuation ring, let `B` be an `A`-algebra of finite type and let `N` be a finite
`B`-module.  Killing the `A`-torsion of `N` produces a `B`-module which is still finite over `B`,
is flat over `A`, and — by Nagata's theorem — is finitely presented over `B`.  This is the
valuation-ring model step in the proof of [Stacks, Tag 053I]: there `B` is a polynomial algebra
`A[x_1, …, x_n]` and `N` is the base change to `A` of a finite module over `R[x_1, …, x_n]`.

The three ingredients are all already available:

* the `A`-torsion submodule of `N` is a `B`-submodule, because the `A`-action and the `B`-action
  on `N` commute (`Submodule.smul_mem_torsion` below);
* the quotient of a module by its torsion submodule is torsion free
  ([Stacks, Tag 0537], `Submodule.QuotientTorsion.instIsTorsionFree`), and over a valuation ring
  a torsion-free module is flat ([Stacks, Tag 0539],
  `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`, since a valuation ring is Bézout); the
  converse direction of Tag 0539, that a flat module over a domain is torsion free
  ([Stacks, Tag 0538]), is `Module.Flat.isTorsionFree`;
* a finite module over a finite-type algebra over a valuation ring which is flat over that
  valuation ring is finitely presented ([Stacks, Tag 053E], Nagata), which is
  `finitePresentation_of_flat_of_finiteType_of_valuationRing`.

## Main definitions

* `Module.baseTorsion A B N`: the `A`-torsion submodule of `N`, viewed as a `B`-submodule.
* `Module.torsionFreeQuot A B N`: the quotient of `N` by its `A`-torsion, a `B`-module.
* `MvPolynomial.moduleBaseChange R A n M`: for `M` a module over `R[x_1, …, x_n]` and `A` an
  `R`-algebra, the base change of `M` along `R[x_1, …, x_n] → A[x_1, …, x_n]`, a module over
  `A[x_1, …, x_n]` and over `A`.

## Main results

* `Module.instFiniteTorsionFreeQuot`: `Module.torsionFreeQuot A B N` is finite over `B`.
* `Module.instFlatTorsionFreeQuot`: `Module.torsionFreeQuot A B N` is flat over the valuation
  ring `A`.
* `Module.instFinitePresentationTorsionFreeQuot`: `Module.torsionFreeQuot A B N` is finitely
  presented over `B`.
* `MvPolynomial.flat_and_finitePresentation_torsionFreeQuot_moduleBaseChange`: the two previous
  statements packaged for the base change of a finite `R[x_1, …, x_n]`-module along a valuation
  ring `A` which is an `R`-algebra.

## References

* [Stacks Project, Tag 0537](https://stacks.math.columbia.edu/tag/0537)
* [Stacks Project, Tag 0538](https://stacks.math.columbia.edu/tag/0538)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
* [Stacks Project, Tag 053E](https://stacks.math.columbia.edu/tag/053E)
* [Stacks Project, Tag 053I](https://stacks.math.columbia.edu/tag/053I)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

section TorsionFreeQuotient

variable (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
  (N : Type w) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- The `A`-torsion submodule of an `A`-algebra module `N` over `B` is stable under the
`B`-action: if a nonzerodivisor `a` of `A` kills `x`, then it kills `b • x` as well, because the
`A`-action and the `B`-action commute. -/
theorem Submodule.smul_mem_torsion (b : B) {x : N} (hx : x ∈ Submodule.torsion A N) :
    b • x ∈ Submodule.torsion A N := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, by rw [smul_comm, ha, smul_zero]⟩

/-- The `A`-torsion submodule of `N`, viewed as a `B`-submodule.  Its carrier is by definition
the carrier of `Submodule.torsion A N`; it is a `B`-submodule by
`Submodule.smul_mem_torsion`. -/
def Module.baseTorsion : Submodule B N :=
  { Submodule.torsion A N with
    smul_mem' := fun b _ hx => Submodule.smul_mem_torsion A B N b hx }

/-- Membership in `Module.baseTorsion A B N` is membership in the `A`-torsion submodule. -/
theorem Module.mem_baseTorsion_iff {x : N} :
    x ∈ Module.baseTorsion A B N ↔ x ∈ Submodule.torsion A N :=
  Iff.rfl

/-- Membership in `Module.baseTorsion A B N` means being killed by a nonzerodivisor of `A`. -/
theorem Module.mem_baseTorsion_iff_exists {x : N} :
    x ∈ Module.baseTorsion A B N ↔ ∃ a : nonZeroDivisors A, (a : A) • x = 0 :=
  Iff.rfl

/-- The quotient of `N` by its `A`-torsion: a `B`-module which is torsion free over `A`.
This is the module appearing in [Stacks, Tag 0537]. -/
@[sga "7 I 1.3"]
def Module.torsionFreeQuot : Type w := N ⧸ Module.baseTorsion A B N

namespace Module

/-- The torsion-free quotient is an additive group, being a quotient of `N`. -/
instance instAddCommGroupTorsionFreeQuot : AddCommGroup (torsionFreeQuot A B N) :=
  inferInstanceAs (AddCommGroup (N ⧸ baseTorsion A B N))

/-- The torsion-free quotient is a `B`-module, since the `A`-torsion is a `B`-submodule. -/
instance instModuleTorsionFreeQuot : Module B (torsionFreeQuot A B N) :=
  inferInstanceAs (Module B (N ⧸ baseTorsion A B N))

/-- The torsion-free quotient is an `A`-module by restriction of scalars along `A → B`. -/
instance instModuleBaseTorsionFreeQuot : Module A (torsionFreeQuot A B N) :=
  inferInstanceAs (Module A (N ⧸ baseTorsion A B N))

/-- The `A`-action on the torsion-free quotient is the restriction of the `B`-action. -/
instance instIsScalarTowerTorsionFreeQuot : IsScalarTower A B (torsionFreeQuot A B N) :=
  inferInstanceAs (IsScalarTower A B (N ⧸ baseTorsion A B N))

/-- The quotient map from `N` onto its torsion-free quotient. -/
@[sga "7 I 1.3"]
def torsionFreeQuot.mkQ : N →ₗ[B] torsionFreeQuot A B N :=
  Submodule.mkQ (baseTorsion A B N)

/-- The quotient map onto the torsion-free quotient is surjective. -/
theorem torsionFreeQuot.mkQ_surjective : Function.Surjective (torsionFreeQuot.mkQ A B N) :=
  Submodule.mkQ_surjective _

/-- The class of `x` in the torsion-free quotient vanishes exactly when `x` is `A`-torsion. -/
theorem torsionFreeQuot.mkQ_eq_zero_iff {x : N} :
    torsionFreeQuot.mkQ A B N x = 0 ↔ x ∈ baseTorsion A B N :=
  Submodule.Quotient.mk_eq_zero _

/-- **Part of Stacks Tag 053E, first conclusion.** The torsion-free quotient of a finite
`B`-module is a finite `B`-module, being a quotient of it. -/
instance instFiniteTorsionFreeQuot [Module.Finite B N] :
    Module.Finite B (torsionFreeQuot A B N) :=
  inferInstanceAs (Module.Finite B (N ⧸ baseTorsion A B N))

/-- **Stacks Tag 0537.** The quotient of `N` by its `A`-torsion is torsion free over the
domain `A`. -/
@[sga "7 I 1.3" "torsion-freeness of H₀"]
instance instIsTorsionFreeTorsionFreeQuot [IsDomain A] :
    Module.IsTorsionFree A (torsionFreeQuot A B N) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a q ha
  rcases eq_or_ne a 0 with rfl | h0
  · exact Or.inl rfl
  refine Or.inr ?_
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    change (Submodule.Quotient.mk x : torsionFreeQuot A B N) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hax : (Submodule.Quotient.mk (a • x) : N ⧸ baseTorsion A B N) = 0 := by
      rw [Submodule.Quotient.mk_smul]; exact ha
    rw [Submodule.Quotient.mk_eq_zero] at hax
    obtain ⟨c, hc⟩ := hax
    refine ⟨c * ⟨a, mem_nonZeroDivisors_of_ne_zero h0⟩, ?_⟩
    change ((c : A) * a) • x = 0
    rw [mul_smul]
    exact hc

end Module


namespace Module

/-- **Stacks Tag 0539.** The torsion-free quotient of `N` is flat over the valuation ring `A`. -/
instance instFlatTorsionFreeQuot [IsDomain A] [ValuationRing A] :
    Module.Flat A (torsionFreeQuot A B N) :=
  Module.Flat.of_isTorsionFree_of_valuationRing

/-- **Stacks Tag 053E, second conclusion (Nagata).** For `A` a valuation ring, `B` an `A`-algebra
of finite type and `N` a finite `B`-module, the quotient of `N` by its `A`-torsion is finitely
presented over `B`: it is flat over `A` by `Module.instFlatTorsionFreeQuot` and finite over `B`
by `Module.instFiniteTorsionFreeQuot`. -/
instance instFinitePresentationTorsionFreeQuot [IsDomain A] [ValuationRing A]
    [Algebra.FiniteType A B] [Module.Finite B N] :
    Module.FinitePresentation B (torsionFreeQuot A B N) :=
  (finitePresentation_of_flat_of_finiteType_of_valuationRing
    (A := A) (B := B) (M := torsionFreeQuot A B N)).2 inferInstance inferInstance

end Module

end TorsionFreeQuotient

section MvPolynomialBaseChange

namespace MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] (n : ℕ)
  (M : Type w) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]

/-- The base change of an `R[x_1, …, x_n]`-module `M` along `R[x_1, …, x_n] → A[x_1, …, x_n]`,
for `A` an `R`-algebra.  It carries both an `A[x_1, …, x_n]`-action, on the left tensor factor,
and an `A`-action, by restriction of scalars.

Since `A ⊗[R] R[x_1, …, x_n] ≃ A[x_1, …, x_n]` (`MvPolynomial.algebraTensorAlgEquiv`), this is
canonically the base change `A ⊗[R] M` of `M` to `A`; that identification is not formalized
here, and nothing below uses it. -/
noncomputable def moduleBaseChange : Type (max v w) :=
  MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) R] M

/-- The base change is an additive group. -/
noncomputable instance instAddCommGroupModuleBaseChange : AddCommGroup (moduleBaseChange R A n M) :=
  inferInstanceAs
    (AddCommGroup (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) R] M))

/-- The base change is a module over `A[x_1, …, x_n]`, acting on the left tensor factor. -/
noncomputable instance instModuleModuleBaseChange :
    Module (MvPolynomial (Fin n) A) (moduleBaseChange R A n M) :=
  inferInstanceAs
    (Module (MvPolynomial (Fin n) A)
      (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) R] M))

/-- The base change is a module over `A`, by restriction of scalars along
`A → A[x_1, …, x_n]`. -/
noncomputable instance instModuleBaseModuleBaseChange : Module A (moduleBaseChange R A n M) :=
  Module.compHom _ (algebraMap A (MvPolynomial (Fin n) A))

/-- The `A`-action on the base change is the restriction of the `A[x_1, …, x_n]`-action. -/
instance instIsScalarTowerModuleBaseChange :
    IsScalarTower A (MvPolynomial (Fin n) A) (moduleBaseChange R A n M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The base change of a finite `R[x_1, …, x_n]`-module is a finite
`A[x_1, …, x_n]`-module. -/
noncomputable instance instFiniteModuleBaseChange [Module.Finite (MvPolynomial (Fin n) R) M] :
    Module.Finite (MvPolynomial (Fin n) A) (moduleBaseChange R A n M) :=
  inferInstanceAs
    (Module.Finite (MvPolynomial (Fin n) A)
      (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) R] M))

/-- **The valuation-ring model step of Stacks Tag 053I.** Let `R` be a commutative ring, let `A`
be an `R`-algebra which is a valuation ring and let `M` be a finite module over
`R[x_1, …, x_n]`.  Then the `A`-torsion-free quotient of the base change of `M` to
`A[x_1, …, x_n]` is flat over `A` (Tag 0539) and finitely presented over `A[x_1, …, x_n]`
(Tag 053E). -/
theorem flat_and_finitePresentation_torsionFreeQuot_moduleBaseChange [IsDomain A]
    [ValuationRing A] [Module.Finite (MvPolynomial (Fin n) R) M] :
    Module.Flat A
        (Module.torsionFreeQuot A (MvPolynomial (Fin n) A) (moduleBaseChange R A n M)) ∧
      Module.FinitePresentation (MvPolynomial (Fin n) A)
        (Module.torsionFreeQuot A (MvPolynomial (Fin n) A) (moduleBaseChange R A n M)) :=
  ⟨inferInstance, inferInstance⟩

end MvPolynomial

end MvPolynomialBaseChange
