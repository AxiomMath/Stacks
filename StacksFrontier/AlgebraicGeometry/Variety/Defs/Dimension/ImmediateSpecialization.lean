module

public import Mathlib.RingTheory.Ideal.Height
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.DimensionFunction
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# Dimension along an immediate specialization

For a scheme locally of finite type over a field, the transcendence degree of the residue field
drops by exactly one along an immediate specialization. If moreover the scheme is irreducible or
equidimensional, the local dimension is the same at both points, so by the dimension formula the
Krull dimension of the local ring goes up by exactly one.

## Main results

* `AlgebraicGeometry.trdeg_residueField_eq_add_one_of_isImmediateSpecialization` computes the
  change in transcendence degree along an immediate specialization.
* `AlgebraicGeometry.krullDimOfRing_stalk_eq_add_one_of_isImmediateSpecialization` computes the
  change in local-ring dimension along an immediate specialization.

## Implementation notes

A locally algebraic `k`-scheme is represented by its structure morphism to `Spec k`, together
with the `LocallyOfFiniteType` instance. The `k`-algebra structures on the residue fields are
the canonical composites through global sections and evaluation at the relevant points, and
dimensions of local rings are expressed using `ringKrullDim`, so they take values in
`WithBot ℕ∞`.

The transcendence-degree statement is proved on the reduced induced subscheme on the closure of
the more general point: there that point is generic, so the dimension is its residue-field
transcendence degree, while the other point has a height-one prime in an affine chart because
the specialization is immediate.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CommRingCat

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0A21.** For an immediate specialization in a scheme locally of finite
type over a field, the transcendence degree of the residue field at the more general point is
one greater than that at the more special point. -/
@[stacks 0A21 "immediate_specialization_trdeg"]
theorem trdeg_residueField_eq_add_one_of_isImmediateSpecialization
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] {x x' : X} (h : IsImmediateSpecialization x x') :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    letI : Algebra k (X.residueField x') :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x').hom.toAlgebra
    Algebra.trdeg k (X.residueField x) = Algebra.trdeg k (X.residueField x') + 1 := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Algebra k (X.residueField x') :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x').hom.toAlgebra
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  let Y := I.subscheme
  let y : Y := ⟨x, subset_closure (Set.mem_singleton x)⟩
  have hy' : x' ∈ I.support := by
    change x' ∈ closure ({x} : Set X)
    exact specializes_iff_mem_closure.mp h.1
  let y' : Y := ⟨x', hy'⟩
  let i : Y ⟶ X := I.subschemeι
  have iy : i y = x := by simpa [i, y] using I.subschemeι_apply y
  have iy' : i y' = x' := by simpa [i, y'] using I.subschemeι_apply y'
  have hyy' : y ⤳ y' := by
    apply i.isClosedEmbedding.isInducing.specializes_iff.mp
    simpa only [iy, iy'] using h.1
  have hYirred : IrreducibleSpace Y :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := x)).closure
  have hy : IsGenericPoint y (Set.univ : Set Y) := by
    apply isGenericPoint_iff_specializes.mpr
    intro z
    exact iff_of_true
      (Topology.IsInducing.subtypeVal.specializes_iff.mp
        (show x ⤳ z.1 from specializes_iff_mem_closure.mpr z.2)) (Set.mem_univ z)
  let g : Y ⟶ Spec (.of k) := i ≫ f
  let : LocallyOfFiniteType g := by
    let : LocallyOfFiniteType i := inferInstance
    exact AlgebraicGeometry.locallyOfFiniteType_comp i f
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  let : Algebra k (Y.residueField y') :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Y.Γevaluation y').hom.toAlgebra
  have htrdegY := topologicalKrullDim_eq_trdeg_residueField k Y g y hy
  have htrdegYx := trdeg_residueField_of_surjectiveOnStalks k f i y
  have htrdegYx' := trdeg_residueField_of_surjectiveOnStalks k f i y'
  have hdimAt := topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y g y'
  have hformula := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y g y'
  obtain ⟨U, hU, hy'U, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show y' ∈ (⊤ : Y.Opens) from trivial)
  have hyU : y ∈ U := hyy'.mem_open U.2 hy'U
  let p : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨y, hyU⟩
  let q : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨y', hy'U⟩
  let yU : U.toScheme := ⟨y, hyU⟩
  let y'U : U.toScheme := ⟨y', hy'U⟩
  have hpmin : IsMin p := by
    rw [isMin_iff_forall_not_lt]
    intro r hr
    let e := hU.isoSpec.hom.homeomorph
    let z : U.toScheme := e.symm r
    have hzr : e z = r := e.apply_symm_apply r
    have hyzY : y ⤳ z.1 := hy.specializes_iff_mem.mpr (Set.mem_univ z.1)
    have hyzU : yU ⤳ z := Topology.IsInducing.subtypeVal.specializes_iff.mp hyzY
    have hspec := e.continuous.specialization_monotone hyzU
    have hs : p ≤ r := by
      have hdual := (specOrderIsoPrimeSpectrum (Γ(Y, U))).map_rel_iff.mpr hspec
      change OrderDual.toDual r ≤ OrderDual.toDual p
      rw [← hzr]
      simpa [p, e, IsAffineOpen.primeIdealOf] using hdual
    exact (not_lt_of_ge hs) hr
  have hp : hU.fromSpec p = y := hU.fromSpec_primeIdealOf yU
  have hq : hU.fromSpec q = y' := hU.fromSpec_primeIdealOf y'U
  have hpq : p < q := by
    have hs : yU ⤳ y'U := Topology.IsInducing.subtypeVal.specializes_iff.mp hyy'
    have hs' : p ⤳ q := by
      apply hU.isoSpec.hom.homeomorph.continuous.specialization_monotone hs
    rw [← PrimeSpectrum.le_iff_specializes] at hs'
    refine lt_of_le_of_ne hs' ?_
    intro he
    have hyEq : y = y' := hp.symm.trans ((congrArg hU.fromSpec he).trans hq)
    apply h.2.1
    calc
      x = i y := iy.symm
      _ = i y' := congrArg i hyEq
      _ = x' := iy'
  have hbelow : ∀ r : PrimeSpectrum Γ(Y, U), r < q → r = p := by
    intro r hr
    let z : Y := hU.fromSpec r
    have hyzY : y ⤳ z := hy.specializes_iff_mem.mpr (Set.mem_univ z)
    have hzy'Y : z ⤳ y' := by
      have hrq : r ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).mp (le_of_lt hr)
      have hmapped := hU.fromSpec.continuous.specialization_monotone hrq
      have horder : hU.fromSpec q ≤ hU.fromSpec r := hmapped
      have hspec : hU.fromSpec r ⤳ hU.fromSpec q := (Scheme.le_iff_specializes).mp horder
      rwa [hq] at hspec
    have hyzX : x ⤳ i z := by
      have hz := i.isClosedEmbedding.isInducing.specializes_iff.mpr hyzY
      simpa [iy] using hz
    have hzy'X : i z ⤳ x' := by
      have hz := i.isClosedEmbedding.isInducing.specializes_iff.mpr hzy'Y
      simpa [iy'] using hz
    rcases h.2.2 (i z) hyzX hzy'X with heq | heq
    · have hzY : z = y := i.isClosedEmbedding.injective (by simpa [iy] using heq)
      exact hU.fromSpec.isOpenEmbedding.injective (hzY.trans hp.symm)
    · have hzY : z = y' := i.isClosedEmbedding.injective (by simpa [iy'] using heq)
      have hrq : r = q := by
        exact hU.fromSpec.isOpenEmbedding.injective (hzY.trans hq.symm)
      exact (hr.ne hrq).elim
  have hheightle : Order.height q ≤ 1 := by
    apply Order.height_le_iff'.2
    intro s hs
    by_contra hlen
    have htwo : 1 < s.length := by
      by_contra hnot
      have hle : s.length ≤ 1 := Nat.le_of_not_gt hnot
      apply hlen
      exact_mod_cast hle
    let j₀ : Fin (s.length + 1) := ⟨0, by omega⟩
    let j₁ : Fin (s.length + 1) := ⟨1, by omega⟩
    have h01 : s j₀ < s j₁ := s.strictMono (Fin.mk_lt_mk.mpr (by omega))
    have hj₁last : s j₁ < s.last := by
      rw [RelSeries.last]
      exact s.strictMono (by exact htwo)
    have hj₀q : s j₀ < q := by simpa [hs] using lt_trans h01 hj₁last
    have hj₁q : s j₁ < q := by simpa [hs] using hj₁last
    rw [hbelow _ hj₀q, hbelow _ hj₁q] at h01
    exact (lt_irrefl p) h01
  have hheight : Order.height q = 1 := by
    apply le_antisymm hheightle
    simpa [Order.height_eq_zero.mpr hpmin] using Order.height_add_one_le hpq
  have hstalk : ringKrullDim (Y.presheaf.stalk y') = 1 := by
    rw [hU.ringKrullDim_stalk_eq_height y' hy'U, PrimeSpectrum.height_eq_orderHeight]
    exact_mod_cast hheight
  have hENatY :
      (Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) : WithBot ℕ∞) =
        (Cardinal.toENat (Algebra.trdeg k (Y.residueField y')) : WithBot ℕ∞) + 1 := by
    calc
      _ = topologicalKrullDim Y := htrdegY.symm
      _ = topologicalKrullDimAt Y y' := hdimAt
      _ = _ := by rw [hformula, hstalk]
  have hENat :
      Cardinal.toENat (Algebra.trdeg k (X.residueField x)) =
        Cardinal.toENat (Algebra.trdeg k (X.residueField x')) + 1 := by
    rw [← htrdegYx, ← htrdegYx'] at hENatY
    have hiy : i y = x := rfl
    have hiy' : i y' = x' := rfl
    rw [hiy, hiy'] at hENatY
    exact_mod_cast hENatY
  have hfin : ∀ z : X, letI : Algebra k (X.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation z).hom.toAlgebra
      Algebra.trdeg k (X.residueField z) < Cardinal.aleph0 := fun z => by
    let : Algebra k (X.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation z).hom.toAlgebra
    let : FinTrdeg k (X.residueField z) := residueField_finTrdeg k f z
    exact trdeg_lt_aleph0 k _
  have hcard : Algebra.trdeg k (X.residueField x) =
      Algebra.trdeg k (X.residueField x') + 1 := by
    have hENat' : Cardinal.toENat (Algebra.trdeg k (X.residueField x)) =
        Cardinal.toENat (Algebra.trdeg k (X.residueField x') + 1) := by
      simpa only [map_add, map_one] using hENat
    exact (Cardinal.toENat_eq_iff_of_le_aleph0 (hfin x).le
      (Cardinal.add_lt_aleph0_iff.mpr ⟨hfin x', Cardinal.one_lt_aleph0⟩).le).mp hENat'
  exact hcard

/-- For an irreducible or equidimensional scheme locally of finite type over a field, local-ring
dimension increases by one under an immediate specialization. -/
@[stacks 0A21 "immediate_specialization_local_ring"]
theorem krullDimOfRing_stalk_eq_add_one_of_isImmediateSpecialization
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x x' : X) (hxx' : IsImmediateSpecialization x x')
    (hX : IrreducibleSpace X ∨ TopologicalSpace.Equidimensional X) :
    ringKrullDim (X.presheaf.stalk x') =
      ringKrullDim (X.presheaf.stalk x) + 1 := by
  have hdim : topologicalKrullDimAt X x = topologicalKrullDimAt X x' := by
    rcases hX with hX | hX
    · let := hX
      exact (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x).symm.trans
        (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x')
    · obtain ⟨Z, hZ, hxZ, hZdim⟩ :=
        exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X f x
      obtain ⟨W, hW, hxW, hWdim⟩ :=
        exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X f x'
      exact hZdim.symm.trans ((hX Z hZ W hW).trans hWdim)
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Algebra k (X.residueField x') :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x').hom.toAlgebra
  have hx := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X f x
  have hx' := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X f x'
  have ht := trdeg_residueField_eq_add_one_of_isImmediateSpecialization k X f hxx'
  have hlt := trdeg_residueField_lt_of_specialization k X f (x := x) (x' := x')
    hxx'.1 hxx'.2.1
  have hfinite : Algebra.trdeg k (X.residueField x') < Cardinal.aleph0 := by
    rw [← not_le]
    intro hinfinite
    rw [ht, Cardinal.add_one_eq hinfinite] at hlt
    exact (lt_irrefl _ hlt)
  have htENat :
      Cardinal.toENat (Algebra.trdeg k (X.residueField x)) =
        Cardinal.toENat (Algebra.trdeg k (X.residueField x')) + 1 := by
    simpa only [map_add, map_one] using congrArg Cardinal.toENat ht
  have ht' :
      (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) =
        (Cardinal.toENat (Algebra.trdeg k (X.residueField x')) : WithBot ℕ∞) + 1 := by
    exact_mod_cast htENat
  have heq := hx.symm.trans (hdim.trans hx')
  apply Eq.symm
  apply (show IsAddLeftRegular
    (Cardinal.toENat (Algebra.trdeg k (X.residueField x'))) from
    ENat.add_right_injective_of_ne_top
      (Cardinal.toENat_eq_top.not.mpr (not_le_of_gt hfinite))).withBot
  simpa only [ht', add_assoc, add_comm, add_left_comm] using heq

end AlgebraicGeometry

end
