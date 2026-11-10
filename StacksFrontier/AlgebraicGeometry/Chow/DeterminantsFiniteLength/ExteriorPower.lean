module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension

/-!
# Comparing the determinant with the top exterior power

Let `R` be a local ring and let `M` be a finite-dimensional vector space over its residue
field, with the induced `R`-module structure. Every sequence in `M` is then admissible, the
length of `M` as an `R`-module is its dimension over the residue field, and the determinant
of `M` is canonically isomorphic to the top exterior power of `M`, by the map sending a
symbol to the exterior product of its entries.

## Main definitions

* `Module.FiniteLength.comparisonMap` is the map from the determinant to the top exterior
  power.
* `Module.FiniteLength.DeterminantExteriorPowerComparison` packages the equality between
  module length and residue-field dimension together with the comparison isomorphism and
  its value on symbols.

## Main results

* `Module.FiniteLength.determinantExteriorPowerComparison` is the comparison between the
  determinant and the top exterior power.
* `Module.FiniteLength.comparisonMap_surjective`: `Module.FiniteLength.comparisonMap` is
  surjective.

## Implementation notes

An `IsScalarTower` assumption expresses that the `R`-action on `M` is induced by the residue
map; in particular the maximal ideal annihilates `M`, so every sequence is admissible and
the three determinant relations become the familiar vanishing, scaling and alternating
properties of the exterior product. The comparison includes the equality between
`Module.FiniteLength.moduleLength R M` and `Module.finrank (IsLocalRing.ResidueField R) M`.

## References

* [Stacks Project, Tag 02P8](https://stacks.math.columbia.edu/tag/02P8)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength
universe u v

/-- For a module whose `R`-action is induced by the residue map, the length over `R` is the
dimension over the residue field. -/
public lemma moduleLength_eq_finrank
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M]
    [Module.Finite (IsLocalRing.ResidueField R) M] :
    moduleLength R M = Module.finrank (IsLocalRing.ResidueField R) M := by
  unfold moduleLength
  rw [Module.length_eq_of_surjective
    (S := R) (R := IsLocalRing.ResidueField R) (M := M)
    (IsLocalRing.residue_surjective (R := R))]
  simp [Module.length_eq_finrank]

/-- An alternating map vanishes on a sequence one of whose entries has been replaced by an
element of the span of the preceding entries. -/
public lemma alternatingMap_update_eq_zero_of_mem_spanBefore
    {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] {n : ℕ}
    (f : M [⋀^Fin n]→ₗ[K] N) (e : Fin n → M) (i : Fin n) (x : M)
    (h : x ∈ spanBefore (R := K) e i) : f (Function.update e i x) = 0 := by
  classical
  let S : Submodule K M := Submodule.span K (e '' Set.Iio i)
  have aux (x : M) (hx : x ∈ S) : f (Function.update e i x) = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact f.map_update_self e (ne_of_lt hj).symm
    | zero => exact f.map_update_zero e i
    | add x y hx hy ihx ihy => simp [f.map_update_add, ihx, ihy]
    | smul a x hx ih => simp [f.map_update_smul, ih]
  exact aux x h

/-- The span over `R` of the entries preceding an index is contained in their span over the
residue field, when the `R`-action is induced by the residue map. -/
public lemma spanBefore_le_residue
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M]
    {n : ℕ} (e : Fin n → M) (i : Fin n) (x : M) (hx : x ∈ spanBefore (R := R) e i) :
    x ∈ spanBefore (R := IsLocalRing.ResidueField R) e i := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.mem_span_of_mem hx
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    rw [← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField R)]
    exact Submodule.smul_mem _ _ ih

/-- The maximal ideal annihilates a module whose `R`-action is induced by the residue map. -/
public lemma maximalIdeal_smul_eq_zero
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M]
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) (x : M) : r • x = 0 := by
  rw [← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField R),
    show (algebraMap R (IsLocalRing.ResidueField R)) r = 0 from
      (IsLocalRing.residue_eq_zero_iff r).mpr hr, zero_smul]

/-- Every sequence in a module whose `R`-action is induced by the residue map is admissible. -/
public lemma all_admissible
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M]
    {n : ℕ} (e : Fin n → M) : IsAdmissibleSequence (R := R) e := by
  intro i r hr
  rw [maximalIdeal_smul_eq_zero R M r hr]
  exact Submodule.zero_mem _

/-- The map on the free vector space on symbols sending a symbol to the exterior product of
its entries. -/
public noncomputable def rawComparison
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M] :
    DeterminantFree R M →ₗ[IsLocalRing.ResidueField R]
      ⋀[IsLocalRing.ResidueField R]^(moduleLength R M) M :=
  Finsupp.linearCombination (IsLocalRing.ResidueField R)
    (fun e : AdmissibleSequence R M ↦
      exteriorPower.ιMulti (IsLocalRing.ResidueField R) (moduleLength R M) e.1)

/-- `rawComparison` on a single symbol. -/
public lemma rawComparison_single
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M]
    (e : AdmissibleSequence R M) :
    rawComparison R M (Finsupp.single e 1) =
      exteriorPower.ιMulti (IsLocalRing.ResidueField R) (moduleLength R M) e.1 := by
  simp [rawComparison]

/-- `rawComparison` kills every admissible relation. -/
public lemma rawComparison_relation
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M]
    (z : DeterminantFree R M) (hz : DeterminantRelation z) :
    rawComparison R M z = 0 := by
  classical
  let K := IsLocalRing.ResidueField R
  let f := exteriorPower.ιMulti K (moduleLength R M) (M := M)
  cases hz with
  | dependent e a ha =>
    rw [rawComparison_single]
    simpa only [Function.update_eq_self] using
      alternatingMap_update_eq_zero_of_mem_spanBefore f e.1 a (e.1 a)
        (spanBefore_le_residue R M e.1 a _ ha)
  | unitChange e a unit replacement x ha hx hreplacement =>
    simp only [map_sub, map_smul, rawComparison_single, sub_eq_zero]
    change f e.1 = (IsLocalRing.residue R unit) •
      f (Function.update e.1 a replacement)
    have hxa : f (Function.update e.1 a x) = 0 :=
      alternatingMap_update_eq_zero_of_mem_spanBefore f e.1 a x
        (spanBefore_le_residue R M e.1 a x hx)
    calc
      f e.1 = f (Function.update e.1 a ((unit : R) • replacement + x)) := by
        rw [← ha, Function.update_eq_self]
      _ = f (Function.update e.1 a ((unit : R) • replacement)) +
            f (Function.update e.1 a x) := f.map_update_add e.1 a _ _
      _ = (IsLocalRing.residue R unit) • f (Function.update e.1 a replacement) := by
        rw [hxa, add_zero, ← IsScalarTower.algebraMap_smul K (unit : R) replacement,
          f.map_update_smul, IsLocalRing.ResidueField.algebraMap_eq]
  | swap e a b hba ha hswap =>
    simp only [map_add, rawComparison_single, add_eq_zero_iff_eq_neg]
    change f e.1 = -f (Function.update (Function.update e.1 b (e.1 a)) a (e.1 b))
    have hab : a ≠ b := by omega
    have hswapFun :
        Function.update (Function.update e.1 b (e.1 a)) a (e.1 b) =
          e.1 ∘ Equiv.swap a b := by
      funext j
      by_cases hja : j = a
      · subst j
        simp [Equiv.swap_apply_left]
      by_cases hjb : j = b
      · subst j
        simp [Equiv.swap_apply_right, hab.symm]
      simp [hja, hjb, Equiv.swap_apply_of_ne_of_ne hja hjb]
    rw [hswapFun, f.map_swap e.1 hab]
    simp

/-- The map from the determinant to the top exterior power induced by `rawComparison`. -/
public noncomputable def comparisonMap
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M] :
    determinant R M →ₗ[IsLocalRing.ResidueField R]
      ⋀[IsLocalRing.ResidueField R]^(moduleLength R M) M :=
  (determinantRelations R M).liftQ (rawComparison R M) (by
    apply Submodule.span_le.mpr
    intro z hz
    exact LinearMap.mem_ker.mpr (rawComparison_relation R M z hz))

/-- `comparisonMap` sends a symbol to the exterior product of its entries. -/
public lemma comparisonMap_symbol
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M]
    (e : AdmissibleSequence R M) :
    comparisonMap R M (symbol e) =
      exteriorPower.ιMulti (IsLocalRing.ResidueField R) (moduleLength R M) e.1 :=
  rawComparison_single R M e

/-- `comparisonMap` is surjective. -/
public lemma comparisonMap_surjective
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M] :
    Function.Surjective (comparisonMap R M) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply le_antisymm le_top
  rw [← exteriorPower.ιMulti_span (IsLocalRing.ResidueField R) (moduleLength R M) M]
  apply Submodule.span_le.mpr
  rintro y ⟨e, rfl⟩
  let ae : AdmissibleSequence R M := ⟨e, all_admissible R M e⟩
  exact ⟨symbol ae, comparisonMap_symbol R M ae⟩

/-- The identification of exterior powers along an equality of degrees. -/
public noncomputable def castExterior
    (K : Type*) [Field K] (M : Type*) [AddCommGroup M] [Module K M] {n m : ℕ}
    (h : n = m) : (⋀[K]^n M) ≃ₗ[K] (⋀[K]^m M) := by
  cases h; exact LinearEquiv.refl K _

/-- `castExterior` relabels an exterior product. -/
public lemma castExterior_ιMulti
    (K : Type*) [Field K] (M : Type*) [AddCommGroup M] [Module K M] {n m : ℕ}
    (h : n = m) (e : Fin n → M) :
    castExterior K M h (exteriorPower.ιMulti K n e) =
      exteriorPower.ιMulti K m (fun i ↦ e (Fin.cast h.symm i)) := by
  cases h; rfl

/-- The comparison data between the determinant of a module annihilated by the maximal ideal
and its top exterior power: the equality of length and dimension, an isomorphism, and the fact
that it sends an admissible symbol to the exterior product of its entries. -/
public structure DeterminantExteriorPowerComparison
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M]
    [IsScalarTower R (IsLocalRing.ResidueField R) M] where
  length_eq_finrank :
    moduleLength R M = Module.finrank (IsLocalRing.ResidueField R) M
  equiv :
    determinant R M ≃ₗ[IsLocalRing.ResidueField R]
      ⋀[IsLocalRing.ResidueField R]^(Module.finrank (IsLocalRing.ResidueField R) M) M
  equiv_symbol : ∀ e : AdmissibleSequence R M,
    equiv (symbol e) =
      exteriorPower.ιMulti (IsLocalRing.ResidueField R)
        (Module.finrank (IsLocalRing.ResidueField R) M)
        (fun i ↦ e.1 (Fin.cast length_eq_finrank.symm i))

/-- For a finite-dimensional module over the residue field of a local ring, the determinant
defined from admissible symbols is isomorphic to its top exterior power. Under this
isomorphism a symbol is sent to the exterior product of its entries. -/
@[stacks 02P8]
public noncomputable def determinantExteriorPowerComparison
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M]
    [IsScalarTower R (IsLocalRing.ResidueField R) M]
    [Module.Finite (IsLocalRing.ResidueField R) M] :
    DeterminantExteriorPowerComparison R M := by
  let K := IsLocalRing.ResidueField R
  let hLen : moduleLength R M = Module.finrank K M := moduleLength_eq_finrank R M
  have hM : IsFiniteLength R M := by
    apply Module.length_ne_top_iff.mp
    rw [Module.length_eq_of_surjective
      (S := R) (R := K) (M := M) (IsLocalRing.residue_surjective (R := R))]
    simp [Module.length_eq_finrank]
  have hDet : Module.finrank K (determinant R M) = 1 :=
    finrank_determinant_eq_one hM
  haveI : Module.Finite K (determinant R M) :=
    Module.finite_of_finrank_eq_succ hDet
  have hTop : Module.finrank K (⋀[K]^(Module.finrank K M) M) = 1 := by
    simp [exteriorPower.finrank_eq]
  let g : determinant R M →ₗ[K] ⋀[K]^(Module.finrank K M) M :=
    (castExterior K M hLen).toLinearMap.comp (comparisonMap R M)
  have hgsurj : Function.Surjective g :=
    (castExterior K M hLen).surjective.comp (comparisonMap_surjective R M)
  have hginj : Function.Injective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hDet.trans hTop.symm)).mpr hgsurj
  refine ⟨hLen, LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩, ?_⟩
  intro e
  change castExterior K M hLen (comparisonMap R M (symbol e)) = _
  rw [comparisonMap_symbol, castExterior_ιMulti]

end Module.FiniteLength

end
