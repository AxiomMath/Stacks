module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Cohomology of the reduction of a complex modulo an integer

Let `P` be a cochain complex of `R`-modules on which multiplication by `n` is injective in every
degree, and `q : P ⟶ P/nP` the quotient map (the cokernel of `n • 𝟙 P`). The long exact
cohomology sequence of `0 → P →ⁿ P → P/nP → 0` gives:

* the kernel of `Hⁱ(q) : Hⁱ(P) → Hⁱ(P/nP)` is `n Hⁱ(P)`
  (`CochainComplex.exists_nsmul_eq_of_homologyMap_cokernelπ_eq_zero`);
* the cokernel of `Hⁱ(q)` embeds into the `n`-torsion of `Hⁱ⁺¹(P)` through the connecting
  map, so it is killed by every `c` killing that torsion
  (`CochainComplex.exists_homologyMap_cokernelπ_eq_nsmul`).

This is the universal coefficient sequence `0 → Hⁱ(K)/n → Hⁱ(K ⊗ᴸ ℤ/n) → Hⁱ⁺¹(K)[n] → 0` for a
complex of torsion-free modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex

variable {R : Type u} [Ring R] (P : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℕ)

/-- The short complex `P →ⁿ P → P/nP` of cochain complexes. -/
abbrev nsmulShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ) :=
  ShortComplex.mk (n • 𝟙 P) (cokernel.π (n • 𝟙 P)) (cokernel.condition _)

variable {P n}

/-- `0 → P →ⁿ P → P/nP → 0` is short exact when multiplication by `n` is injective on `P`. -/
theorem nsmulShortComplex_shortExact (hP : ∀ (j : ℤ) (x : P.X j), n • x = 0 → x = 0) :
    (nsmulShortComplex P n).ShortExact := by
  have : Mono (n • 𝟙 P) := by
    refine HomologicalComplex.mono_of_mono_f _ fun j => ?_
    rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
    exact fun x hx => hP j x (by simpa using hx)
  exact { exact := ShortComplex.exact_cokernel (n • 𝟙 P) }

/-- The map induced on `Hⁱ(P)` by multiplication by `n` on `P` is multiplication by `n`. -/
theorem homologyMap_nsmul_id_apply (i : ℤ) (x : P.homology i) :
    HomologicalComplex.homologyMap (n • 𝟙 P) i x = n • x := by
  have h : HomologicalComplex.homologyMap (n • 𝟙 P) i = n • 𝟙 (P.homology i) := by
    show (HomologicalComplex.homologyFunctor _ _ i).map (n • 𝟙 P) = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  rw [h]
  rfl

section General

variable {P' : CochainComplex (ModuleCat.{v} R) ℤ} {g : P ⟶ P'} (w : (n • 𝟙 P) ≫ g = 0)
  (hS : (ShortComplex.mk _ _ w).ShortExact)

include hS in
/-- **The kernel of `Hⁱ(P) → Hⁱ(P')` is `n Hⁱ(P)`** for a short exact `0 → P →ⁿ P → P' → 0`. -/
theorem exists_nsmul_eq_of_homologyMap_eq_zero (i : ℤ) (x : P.homology i)
    (hx : HomologicalComplex.homologyMap g i x = 0) : ∃ x' : P.homology i, x = n • x' := by
  obtain ⟨x', hx'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (hS.homology_exact₂ i) x hx
  exact ⟨x', hx'.symm.trans (homologyMap_nsmul_id_apply i x')⟩

include hS in
/-- **The cokernel of `Hⁱ(P) → Hⁱ(P')` is killed by every `c` killing the `n`-torsion of
`Hⁱ⁺¹(P)`**, for a short exact `0 → P →ⁿ P → P' → 0`. -/
theorem exists_homologyMap_eq_nsmul (i : ℤ) (c : ℕ)
    (hc : ∀ z : P.homology (i + 1), n • z = 0 → c • z = 0) (y : P'.homology i) :
    ∃ x : P.homology i, HomologicalComplex.homologyMap g i x = c • y := by
  have hrel : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
  set δ := hS.δ i (i + 1) hrel
  have h1 : n • δ y = 0 := by
    rw [← homologyMap_nsmul_id_apply (i + 1) (δ y)]
    exact congrArg (fun φ => φ.hom y) (hS.δ_comp i (i + 1) hrel)
  have h2 : δ (c • y) = 0 := by
    rw [map_nsmul, hc _ h1]
  exact (ShortComplex.moduleCat_exact_iff _).1 (hS.homology_exact₃ i (i + 1) hrel) _ h2

end General

/-- **The kernel of `Hⁱ(P) → Hⁱ(P/nP)` is `n Hⁱ(P)`.** -/
theorem exists_nsmul_eq_of_homologyMap_cokernelπ_eq_zero
    (hP : ∀ (j : ℤ) (x : P.X j), n • x = 0 → x = 0) (i : ℤ) (x : P.homology i)
    (hx : HomologicalComplex.homologyMap (cokernel.π (n • 𝟙 P)) i x = 0) :
    ∃ x' : P.homology i, x = n • x' :=
  exists_nsmul_eq_of_homologyMap_eq_zero _ (nsmulShortComplex_shortExact hP) i x hx

/-- **The cokernel of `Hⁱ(P) → Hⁱ(P/nP)` is killed by every `c` killing the `n`-torsion of
`Hⁱ⁺¹(P)`.** -/
theorem exists_homologyMap_cokernelπ_eq_nsmul
    (hP : ∀ (j : ℤ) (x : P.X j), n • x = 0 → x = 0) (i : ℤ) (c : ℕ)
    (hc : ∀ z : P.homology (i + 1), n • z = 0 → c • z = 0)
    (y : (cokernel (n • 𝟙 P)).homology i) :
    ∃ x : P.homology i, HomologicalComplex.homologyMap (cokernel.π (n • 𝟙 P)) i x = c • y :=
  exists_homologyMap_eq_nsmul _ (nsmulShortComplex_shortExact hP) i c hc y

end CochainComplex

end
