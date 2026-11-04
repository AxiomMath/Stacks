module

public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# Global sections over the ground field, as a functor

The global sections `Γ(X, ℱ)` of an `𝒪_X`-module on a scheme over a field `k` form a
`k`-vector space, `AlgebraicGeometry.globalSectionsOverField`. This file makes that assignment
functorial and shows that it is finite dimensional for a coherent module on a proper scheme. It
also proves that a nonincreasing sequence of natural numbers is eventually constant, that an
injective map between spaces of equal finite dimension is surjective, and that a property
holding on each residue class of a modulus below some bound holds for every sufficiently
negative integer.

## Main definitions

* `Stacks.EnriquesSeveriZariski.globalSectionsFunctor`: `ℱ ↦ Γ(X, ℱ)` as a functor to
  `k`-vector spaces. Its value on objects is `AlgebraicGeometry.globalSectionsOverField`, and its
  value on a morphism is that morphism's action on sections over `⊤`.

## Main results

* `Stacks.EnriquesSeveriZariski.finiteDimensional_globalSectionsOverField`: the global sections
  of a coherent module on a proper scheme over a field form a finite dimensional vector space.
* `Stacks.EnriquesSeveriZariski.exists_eventually_eq_of_antitone`: a nonincreasing sequence of
  natural numbers is constant from some index on.
* `Stacks.EnriquesSeveriZariski.surjective_of_injective_of_finrank_eq`: an injective linear map
  between vector spaces of the same finite dimension is surjective.
* `Stacks.EnriquesSeveriZariski.exists_forall_le_of_forall_residue`: a property of integers
  holding on each residue class of a modulus `e` from some point downwards holds for every
  sufficiently negative integer.

## References

* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.EnriquesSeveriZariski

/-- **The global sections over the ground field, as a functor.** Sections over the whole space,
with scalars restricted along the structure morphism. -/
def globalSectionsFunctor (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    X.Modules ⥤ ModuleCat.{u} k :=
  _root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The functor computes `AlgebraicGeometry.globalSectionsOverField` on objects. -/
theorem globalSectionsFunctor_obj (F : X.Modules) :
    (globalSectionsFunctor k f).obj F = globalSectionsOverField k f F :=
  rfl

/-- A morphism acting injectively on sections over the whole space acts injectively on global
sections over the ground field. -/
theorem injective_globalSectionsFunctor_map {A B : X.Modules} (h : A ⟶ B)
    (hinj : Function.Injective (h.app (⊤ : X.Opens))) :
    Function.Injective ((globalSectionsFunctor k f).map h) :=
  hinj

/-- Conversely, injectivity on global sections over the ground field is injectivity on sections
over the whole space. -/
theorem injective_app_top_of_injective_globalSectionsFunctor_map {A B : X.Modules} (h : A ⟶ B)
    (hinj : Function.Injective ((globalSectionsFunctor k f).map h)) :
    Function.Injective (h.app (⊤ : X.Opens)) :=
  hinj

/-- **The global sections of a coherent module on a proper scheme over a field are finite
dimensional.** -/
theorem finiteDimensional_globalSectionsOverField [IsProper f] (F : X.Modules) [F.IsCoherent] :
    FiniteDimensional k (globalSectionsOverField k f F) :=
  have : FiniteDimensional k (cohomologyOverField k f F 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f F 0
  LinearEquiv.finiteDimensional (cohomologyOverFieldZeroIso k f F).toLinearEquiv

/-! ### Two pieces of linear algebra -/

/-- **A nonincreasing sequence of natural numbers is constant from some index on.** -/
theorem exists_eventually_eq_of_antitone {d : ℕ → ℕ} (hd : ∀ j : ℕ, d (j + 1) ≤ d j) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → d j = d J := by
  obtain ⟨J, hJ⟩ := Nat.sInf_mem (⟨d 0, 0, rfl⟩ : (Set.range d).Nonempty)
  exact ⟨J, fun j hj ↦
    le_antisymm (antitone_nat_of_succ_le hd hj) (hJ.trans_le (Nat.sInf_le ⟨j, rfl⟩))⟩

/-- **An injective linear map between vector spaces of the same finite dimension is
surjective.** -/
theorem surjective_of_injective_of_finrank_eq {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (hdim : Module.finrank k V = Module.finrank k W) (φ : V →ₗ[k] W)
    (hφ : Function.Injective φ) : Function.Surjective φ :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hφ

/-! ### From the residue classes of a modulus to all sufficiently negative integers -/

/-- **A property holding on every residue class far enough down holds for all sufficiently
negative integers.** If `P` holds at `-i - j * e` for every residue `i < e` and every `j` beyond
a bound depending on `i`, then `P n` holds for all `n` below some `n₀`. -/
theorem exists_forall_le_of_forall_residue {e : ℕ} (he : 1 ≤ e) (P : ℤ → Prop) (J : ℕ → ℕ)
    (hP : ∀ i : ℕ, i < e → ∀ j : ℕ, J i ≤ j → P (-(i : ℤ) - j * e)) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≤ n₀ → P n := by
  have hepos : (0 : ℤ) < e := by omega
  refine ⟨(Finset.range e).inf' (Finset.nonempty_range_iff.2 (by omega))
    fun i ↦ -(i : ℤ) - J i * e, fun n hn ↦ ?_⟩
  set i : ℕ := ((-n) % (e : ℤ)).toNat
  have hi : (i : ℤ) = (-n) % e := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hie : i < e := by have := Int.emod_lt_of_pos (-n) hepos; omega
  have hn' : n = -(i : ℤ) - (-n) / e * e := by rw [hi, Int.emod_def]; ring
  have hJ : (J i : ℤ) ≤ (-n) / e := le_of_mul_le_mul_right (by
    linarith [hn.trans (Finset.inf'_le _ (Finset.mem_range.2 hie))]) hepos
  have := hP i hie ((-n) / e).toNat (by omega)
  rwa [Int.toNat_of_nonneg (show 0 ≤ (-n) / (e : ℤ) by omega), ← hn'] at this

end Stacks.EnriquesSeveriZariski

end
