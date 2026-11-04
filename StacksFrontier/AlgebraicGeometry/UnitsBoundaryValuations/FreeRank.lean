module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import StacksFrontier.AlgebraicGeometry.NormalExtension.Basic
public import StacksFrontier.AlgebraicGeometry.UnitsBoundaryValuations.Basic

/-!
# The units of an open subscheme of a normal proper variety are free of rank `r - 1`

Let `k` be an algebraically closed field, let `Y` be a normal proper variety over `k` and let
`V ⊆ Y` be a nonempty open subscheme with `r` boundary points of codimension one.  This file
upgrades the finite generation of `Γ(Y, V)ˣ / k^*` proved in
`StacksFrontier.AlgebraicGeometry.UnitsBoundaryValuations.Basic` to the full structure statement:
that group is *free* abelian, of rank at most `r - 1`.

Freeness is immediate once the family of boundary orders is known to have kernel exactly the
constants: the quotient then embeds in the free abelian group `ℤ^r`, so it is torsion free, and a
finitely generated torsion-free module over a principal ideal domain is free.

The strict bound `r - 1` is the mathematical content.  It comes from *properness* and needs no
degree theory on the curve, only algebraic Hartogs in its nonnegative form
`AlgebraicGeometry.exists_germ_top_eq_of_forall_zero_le_ord`:  a unit on `V` all of whose boundary
orders are nonnegative has nonnegative order of vanishing at every codimension-one point of `Y`,
hence is a global section, hence a constant, hence has all its boundary orders *zero*.  So the
lattice of boundary orders meets the nonnegative orthant of `ℤ^r` only in the origin, and a
subgroup of `ℤ^r` with that property has rank at most `r - 1`:  a subgroup of full rank `r` has
finite index, so it contains a positive multiple of each standard basis vector, and those lie in
the nonnegative orthant.

## Main results

* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.exists_pos_smul_mem_of_card_le_finrank`: a
  subgroup of `ℤ^J` of full rank contains a positive multiple of every vector.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.finrank_lt_card_of_forall_nonneg_eq_zero`: a
  subgroup of `ℤ^J` meeting the nonnegative orthant only in the origin has rank `< #J`.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.free_finrank_lt_card_of_intCounting`: the
  group-theoretic conclusion, for a commutative group with an additive integer-valued counting
  function whose kernel is the given subgroup and which never takes a nonzero nonnegative value.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.boundaryOrd_eq_zero_of_forall_nonneg`: a unit
  on `V` with no pole on `Y` is a constant.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.units_quotient_free_finrank_lt_of_isNormal`
  and `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.exists_linearEquiv_units_quotient`:
  **the units of `Γ(Y, V)` modulo the constants are free abelian of rank at most `r - 1`.**

## Relation to Stacks Tag 03RR

Tag 03RR computes `H¹_étale(X, μ_n)` for an affine smooth curve `X = X̄ \ {x_1, …, x_r}` over an
algebraically closed field as `(ℤ/n)^{2g + r - 1}`, and the group proved free here is the one
carrying the summand `r - 1` of that count:  the left-hand end of the Kummer sequence of the
affine curve, `Γ(X, 𝒪_X)ˣ / (Γ(X, 𝒪_X)ˣ)^n`, which is the base change to `ℤ/n` of the group
`Γ(X, 𝒪_X)ˣ / k^*` because `k^*` is divisible.  What is proved here is the *inequality* `rank
≤ r - 1`, which is a theorem with no hypotheses beyond those stated.  Equality is **false in
general** and is not proved here: the rank is `r - 1` exactly when the differences `[x_i] - [x_j]`
of the deleted points generate a torsion subgroup of `Pic⁰(X̄)`, which fails already for an
elliptic curve with two points removed whose difference has infinite order.  The `2g + r - 1` of
the tag is therefore not the sum of an unconditional `r - 1` and an unconditional `2g`; only the
total is unconditional, and it is read off the Picard scheme of Tag 0BA0 together with the
`n`-divisibility of `Pic⁰` of Tag 03RP, neither of which is in this file's input.

## References

* [Stacks Project, Tag 04L4](https://stacks.math.columbia.edu/tag/04L4)
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.UnitsBoundaryValuations

open Stacks.AlgebraicGeometry.UnitsNormalProper

/-! ### Subgroups of `ℤ^J` -/

/-- A subgroup of `ℤ^J` whose rank is the full rank `#J` has finite index:  a positive multiple of
every vector of `ℤ^J` lies in it.  Indeed the quotient is then a finitely generated module of rank
zero, hence a torsion module. -/
theorem exists_pos_smul_mem_of_card_le_finrank {J : Type*} [Finite J]
    (L : Submodule ℤ (J → ℤ)) (hL : Nat.card J ≤ Module.finrank ℤ L) (x : J → ℤ) :
    ∃ m : ℤ, 0 < m ∧ m • x ∈ L := by
  classical
  have _ : Fintype J := Fintype.ofFinite J
  have hcard : Module.finrank ℤ (J → ℤ) = Nat.card J := by
    rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  have hadd := L.finrank_quotient_add_finrank
  have hq : Module.finrank ℤ ((J → ℤ) ⧸ L) = 0 := by omega
  obtain ⟨a, ha⟩ := Module.finrank_eq_zero_iff_isTorsion.mp hq (x := L.mkQ x)
  have hmem : (a : ℤ) • x ∈ L := by
    have h1 : L.mkQ ((a : ℤ) • x) = 0 := by rwa [map_smul]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  rcases (nonZeroDivisors.coe_ne_zero a).lt_or_gt with h | h
  · exact ⟨-(a : ℤ), by omega, by rw [neg_smul]; exact L.neg_mem hmem⟩
  · exact ⟨(a : ℤ), h, hmem⟩

/-- A subgroup of `ℤ^J` that meets the nonnegative orthant only in the origin has rank at most
`#J - 1`.  A subgroup of full rank contains a positive multiple of a standard basis vector, and
that multiple is a nonzero nonnegative vector. -/
theorem finrank_lt_card_of_forall_nonneg_eq_zero {J : Type*} [Finite J] [Nonempty J]
    (L : Submodule ℤ (J → ℤ)) (h : ∀ x ∈ L, (∀ j, 0 ≤ x j) → x = 0) :
    Module.finrank ℤ L < Nat.card J := by
  classical
  by_contra hc
  obtain ⟨m, hm, hmem⟩ := exists_pos_smul_mem_of_card_le_finrank L (not_lt.mp hc)
    (Pi.single (Classical.arbitrary J) 1)
  have hzero := h _ hmem fun j => by
    rcases eq_or_ne j (Classical.arbitrary J) with rfl | hj
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      omega
    · simp [Pi.single_eq_of_ne hj]
  have hval := congrFun hzero (Classical.arbitrary J)
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at hval
  omega

/-! ### The group-theoretic step -/

/-- The quotient of a commutative group by the exact kernel of an additive integer-valued counting
function with finitely many coordinates, none of whose values is nonzero and nonnegative, is a
*free* abelian group of rank less than the number of coordinates. -/
theorem free_finrank_lt_card_of_intCounting {G : Type*} [CommGroup G] {J : Type*} [Finite J]
    [Nonempty J] (N : Subgroup G) (Φ : G → J → ℤ) (hmul : ∀ a b : G, Φ (a * b) = Φ a + Φ b)
    (hker : ∀ a : G, Φ a = 0 ↔ a ∈ N) (hnonneg : ∀ a : G, (∀ j, 0 ≤ Φ a j) → Φ a = 0) :
    Module.Finite ℤ (Additive (G ⧸ N)) ∧ Module.Free ℤ (Additive (G ⧸ N)) ∧
      Module.finrank ℤ (Additive (G ⧸ N)) < Nat.card J := by
  obtain ⟨Φ', hmk, hmul', hker'⟩ := exists_intCounting_quotient N Φ hmul hker
  have hnn' : ∀ y : G ⧸ N, (∀ j, 0 ≤ Φ' y j) → Φ' y = 0 := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H b =>
      intro hy
      rw [hmk b] at hy ⊢
      exact hnonneg b hy
  let ψ : Additive (G ⧸ N) →+ (J → ℤ) :=
    AddMonoidHom.mk' (fun a => Φ' a.toMul) fun a b => hmul' a.toMul b.toMul
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).mpr fun a ha => ?_
    simpa using congrArg Additive.ofMul (hker' a.toMul ha)
  have hfin : Module.Finite ℤ (Additive (G ⧸ N)) :=
    Module.Finite.of_injective ψ.toIntLinearMap hψ
  have htf : Module.IsTorsionFree ℤ (Additive (G ⧸ N)) :=
    hψ.moduleIsTorsionFree (R := ℤ) _ fun r m => map_zsmul ψ r m
  refine ⟨hfin, inferInstance, ?_⟩
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofInjective ψ.toIntLinearMap hψ)]
  refine finrank_lt_card_of_forall_nonneg_eq_zero _ ?_
  rintro x ⟨y, rfl⟩ hx
  exact hnn' y.toMul hx

/-! ### The units of an open subscheme of a normal proper variety -/

/-- On an integral normal scheme the ring of sections of *every* affine open is integrally closed,
the empty affine open included:  its ring of sections is the trivial ring, which is integrally
closed for want of anything to close.  This is the shape of normality that
`AlgebraicGeometry.exists_germ_top_eq_of_forall_zero_le_ord` asks for, whereas
`AlgebraicGeometry.isNormal_iff_forall_affineOpen_normal` supplies it only over the *nonempty*
affine opens, where the ring of sections is a domain. -/
theorem isIntegrallyClosed_sections_affineOpens (Y : Scheme.{u}) [IsIntegral Y]
    [AlgebraicGeometry.IsNormal Y] (U : Y.affineOpens) : IsIntegrallyClosed Γ(Y, U.1) := by
  by_cases hne : Nonempty U.1
  · exact (AlgebraicGeometry.isNormal_iff_forall_affineOpen_normal Y).mp inferInstance U hne
  · have hU : U.1 = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨⟨x, hx⟩⟩
    have : Subsingleton Γ(Y, U.1) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hU)
    infer_instance

/-- The generic point of an integral scheme lies in every nonempty open subscheme. -/
private theorem genericPoint_mem_of_nonempty {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] : genericPoint Y ∈ V :=
  ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)

section Proper

variable (k : Type u) [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
variable [IsAlgClosed k] [AlgebraicGeometry.IsProperVariety k g] [AlgebraicGeometry.IsNormal Y]

/-- **A unit on `V` with no pole on `Y` is a constant.**  If every boundary order of a unit of
`Γ(Y, V)` is nonnegative then, being zero at the points of `V`, its order of vanishing is
nonnegative at every codimension-one point of `Y`;  algebraic Hartogs makes it a global section,
and properness over an algebraically closed field makes that section a constant.  So the boundary
orders are in fact all zero.

This is what forbids the lattice of boundary orders from having full rank, and so is the source of
the `- 1` in the rank count. -/
theorem boundaryOrd_eq_zero_of_forall_nonneg [IsLocallyNoetherian Y] (V : Y.Opens) [Nonempty V]
    (u : Γ(Y, V)ˣ) (hu : ∀ b : boundaryPoints V, 0 ≤ boundaryOrd V u b) :
    boundaryOrd V u = 0 := by
  have hgen := genericPoint_mem_of_nonempty V
  have hnorm : ∀ U : Y.affineOpens, IsIntegrallyClosed Γ(Y, U.1) :=
    isIntegrallyClosed_sections_affineOpens Y
  have hne : Y.germToFunctionField V u.1 ≠ 0 := germToFunctionField_ne_zero V u
  have hord : ∀ z : Y, coheight z = 1 → 0 ≤ Scheme.ord (Y.germToFunctionField V u.1) z := by
    intro z hz
    by_cases hzV : z ∈ (V : Set Y)
    · exact le_of_eq (Scheme.ord_of_isUnit u.isUnit hzV).symm
    · exact hu ⟨z, hz, hzV⟩
  obtain ⟨s, hs⟩ := exists_germ_top_eq_of_forall_zero_le_ord hnorm hne hord
  obtain ⟨c, hc⟩ := (bijective_structMap k g).2 s
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    rw [← hc, map_zero] at hs
    exact hne hs.symm
  refine (boundaryOrd_eq_zero_iff k g V u).mpr ⟨Units.mk0 c hc0, Units.ext ?_⟩
  show structMapOpen k g V c = u.1
  rw [structMapOpen_apply, hc]
  refine Y.germToFunctionField_injective V ?_
  rwa [Y.presheaf.germ_res_apply (homOfLE (le_top : V ≤ ⊤)) (genericPoint Y) hgen]

/-- **The units of an open subscheme of a normal proper variety, modulo the constants, are free
abelian of rank at most `r - 1`.**  Here `k` is algebraically closed, `Y` is a normal proper
variety over `k`, `V ⊆ Y` is a nonempty open subscheme and `r` is the number of boundary points of
`Y` of codimension one outside `V`, assumed nonzero.

This is the structure statement behind the summand `r - 1` of the rank count `2g + r - 1` of
Stacks Tag 03RR;  see the module documentation for what equality would additionally require and
why it is not available — indeed not true — in this generality. -/
theorem units_quotient_free_finrank_lt_of_isNormal (V : Y.Opens) [Nonempty V]
    (hV : (boundaryPoints V).Nonempty) :
    Module.Finite ℤ (Additive (Γ(Y, V)ˣ ⧸ (Units.map (structMapOpen k g V).toMonoidHom).range)) ∧
      Module.Free ℤ
        (Additive (Γ(Y, V)ˣ ⧸ (Units.map (structMapOpen k g V).toMonoidHom).range)) ∧
      Module.finrank ℤ
          (Additive (Γ(Y, V)ˣ ⧸ (Units.map (structMapOpen k g V).toMonoidHom).range)) <
        Nat.card (boundaryPoints V) := by
  have _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have _ : AlgebraicGeometry.IsNoetherian Y := AlgebraicGeometry.IsNoetherian.mk
  have hgen := genericPoint_mem_of_nonempty V
  have _ : Finite (boundaryPoints V) :=
    (finite_coheight_one_notMem
      (fun _ _ => AlgebraicGeometry.Scheme.le_iff_specializes) V.isOpen hgen).to_subtype
  have _ : Nonempty (boundaryPoints V) := hV.to_subtype
  exact free_finrank_lt_card_of_intCounting _ (boundaryOrd V) (boundaryOrd_mul V)
    (boundaryOrd_eq_zero_iff k g V) (boundaryOrd_eq_zero_of_forall_nonneg k g V)

/-- The same conclusion as an explicit isomorphism:  the units of `Γ(Y, V)` modulo the constants
are isomorphic, as an abelian group written additively, to `ℤ^m` for some `m` with
`m + 1 ≤ r`. -/
theorem exists_linearEquiv_units_quotient (V : Y.Opens) [Nonempty V]
    (hV : (boundaryPoints V).Nonempty) :
    ∃ m : ℕ, m + 1 ≤ Nat.card (boundaryPoints V) ∧
      Nonempty (Additive (Γ(Y, V)ˣ ⧸ (Units.map (structMapOpen k g V).toMonoidHom).range)
        ≃ₗ[ℤ] (Fin m → ℤ)) := by
  obtain ⟨_, _, hlt⟩ := units_quotient_free_finrank_lt_of_isNormal k g V hV
  exact ⟨_, hlt, ⟨(Module.finBasis ℤ
    (Additive (Γ(Y, V)ˣ ⧸ (Units.map (structMapOpen k g V).toMonoidHom).range))).equivFun⟩⟩

end Proper

end Stacks.AlgebraicGeometry.UnitsBoundaryValuations
