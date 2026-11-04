module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.NoetherianSpace

/-!
# Two finiteness inputs for the units of an open subscheme

This file isolates the two finiteness statements that the proof of
[Stacks, Tag 04L4](https://stacks.math.columbia.edu/tag/04L4) rests on, neither of which mentions
schemes of global sections or orders of vanishing.

The first is pure group theory: a commutative group carrying an integer-valued "counting"
function which is additive and has trivial kernel is finitely generated, because the integral
span of its image is a submodule of a Noetherian module.  In Tag 04L4 the counting function is
the family of valuations at the boundary points of codimension one, and the group is the units of
the open subscheme modulo the constants.

The second is topological: on an irreducible Noetherian space, an open set containing the generic
point omits only finitely many points of codimension one.  This is what makes the index set of
the family of valuations finite, and it is the content of the sentence in the source that says
"let `ξ_1, …, ξ_r` be the generic points of `X̄ \ X`".

## Main results

* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.exists_intCounting_quotient`: the counting
  function descends to the quotient by its kernel, with trivial kernel there.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.group_fg_of_intCounting`: a commutative group
  with an injective additive map to `J → ℤ` for a finite `J` is finitely generated.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.finite_coheight_one_notMem`: the points of
  coheight one outside an open subset containing the generic point of an irreducible Noetherian
  space form a finite set.

## Implementation notes

`group_fg_of_intCounting` takes the counting function as a bare function together with its
additivity, rather than as a bundled `MonoidHom` into `Multiplicative (J → ℤ)`.  This is
deliberate: the consumer builds the function out of `AlgebraicGeometry.Scheme.ord`, whose
multiplicativity lemma `ord_mul` carries nonvanishing side conditions, so bundling it first
would force the side conditions to be discharged twice.

The topological statement is proved by decomposing the closed complement into finitely many
irreducible closed pieces and showing that a point of coheight one in the complement is the
generic point of its piece.  The step that rules out a strictly more generic point of the
complement uses `Order.coheight_add_one_le`: a point strictly above a point of coheight one is
maximal, hence — the space being irreducible and sober — the generic point of the whole space,
which lies in the open set by hypothesis.

## References

* [Stacks Project, Tag 04L4](https://stacks.math.columbia.edu/tag/04L4)
* [Stacks Project, Tag 0052](https://stacks.math.columbia.edu/tag/0052)
-/

@[expose] public section

open AlgebraicGeometry Order Set TopologicalSpace Topology

universe u

namespace Stacks.AlgebraicGeometry.UnitsBoundaryValuations

/-- A commutative group admitting an additive integer-valued counting function with finitely
many coordinates and trivial kernel is finitely generated. -/
theorem group_fg_of_intCounting {G : Type*} [CommGroup G] {J : Type*} [Finite J]
    (Φ : G → J → ℤ) (hmul : ∀ a b : G, Φ (a * b) = Φ a + Φ b)
    (hker : ∀ a : G, Φ a = 0 → a = 1) :
    Group.FG G := by
  let ψ : Additive G →+ (J → ℤ) :=
    AddMonoidHom.mk' (fun a => Φ a.toMul) (fun a b => hmul a.toMul b.toMul)
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).mpr fun a ha => ?_
    simpa using congrArg Additive.ofMul (hker a.toMul ha)
  exact GroupFG.iff_add_fg.mpr
    (Module.Finite.iff_addGroup_fg.mp (Module.Finite.of_injective ψ.toIntLinearMap hψ))

/-- An additive integer-valued counting function whose kernel is exactly a subgroup `N` descends
to the quotient by `N`, where it is still additive and has trivial kernel. -/
theorem exists_intCounting_quotient {G : Type*} [CommGroup G] {J : Type*}
    (N : Subgroup G) (Φ : G → J → ℤ) (hmul : ∀ a b : G, Φ (a * b) = Φ a + Φ b)
    (hker : ∀ a : G, Φ a = 0 ↔ a ∈ N) :
    ∃ Φ' : G ⧸ N → J → ℤ, (∀ a : G, Φ' (QuotientGroup.mk a) = Φ a) ∧
      (∀ x y : G ⧸ N, Φ' (x * y) = Φ' x + Φ' y) ∧ (∀ x : G ⧸ N, Φ' x = 0 → x = 1) := by
  have hone : Φ (1 : G) = 0 := (hker 1).mpr N.one_mem
  have hinv : ∀ a : G, Φ a⁻¹ = -Φ a := fun a =>
    eq_neg_of_add_eq_zero_right (by rw [← hmul, mul_inv_cancel, hone])
  have hwd : ∀ a b : G, QuotientGroup.leftRel N a b → Φ a = Φ b := by
    intro a b hab
    have h : Φ (a⁻¹ * b) = 0 := (hker _).mpr ((QuotientGroup.leftRel_apply).mp hab)
    rw [hmul, hinv] at h
    exact neg_add_eq_zero.mp h
  refine ⟨fun x => Quotient.liftOn' x Φ hwd, fun _ => rfl, fun x y => ?_, fun x hx => ?_⟩
  · induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b => exact hmul a b
  · induction x using QuotientGroup.induction_on with
    | H a => exact (QuotientGroup.eq_one_iff a).mpr ((hker a).mp hx)

/-- The quotient of a commutative group by the exact kernel of an additive integer-valued
counting function with finitely many coordinates is finitely generated. -/
theorem group_fg_quotient_of_intCounting {G : Type*} [CommGroup G] {J : Type*} [Finite J]
    (N : Subgroup G) (Φ : G → J → ℤ) (hmul : ∀ a b : G, Φ (a * b) = Φ a + Φ b)
    (hker : ∀ a : G, Φ a = 0 ↔ a ∈ N) :
    Group.FG (G ⧸ N) := by
  obtain ⟨Φ', -, hmul', hker'⟩ := exists_intCounting_quotient N Φ hmul hker
  exact group_fg_of_intCounting Φ' hmul' hker'

/-- On an irreducible Noetherian sober space, an open set containing the generic point omits only
finitely many points of coheight one.  Every such point is the generic point of one of the
finitely many irreducible components of the closed complement. -/
theorem finite_coheight_one_notMem {Y : Type u} [TopologicalSpace Y] [IrreducibleSpace Y]
    [NoetherianSpace Y] [QuasiSober Y] [T0Space Y] [Preorder Y]
    (hle : ∀ a b : Y, a ≤ b ↔ b ⤳ a) {V : Set Y} (hVo : IsOpen V) (hV : genericPoint Y ∈ V) :
    {y : Y | coheight y = 1 ∧ y ∉ V}.Finite := by
  have hanti : ∀ a b : Y, a ≤ b → b ≤ a → a = b := fun a b hab hba =>
    ((hle b a).mp hba).antisymm ((hle a b).mp hab) |>.eq
  obtain ⟨S, hSfin, hScl, hSirr, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (α := Y) hVo.isClosed_compl
  refine Set.Finite.subset (hSfin.biUnion (t := fun t => {y : Y | closure {y} = t})
    fun t _ => Set.Subsingleton.finite fun y hy y' hy' => ?_) ?_
  · exact (inseparable_iff_closure_eq.mpr (hy.trans hy'.symm)).eq
  · rintro y ⟨hy1, hyV⟩
    obtain ⟨t, htS, hyt⟩ := Set.mem_sUnion.mp (hSU ▸ hyV : y ∈ ⋃₀ S)
    set z := (hSirr t htS).genericPoint
    have hgen : closure {z} = t := (hSirr t htS).closure_genericPoint (hScl t htS)
    have hzt : z ∈ t := hgen ▸ subset_closure (Set.mem_singleton z)
    have hzV : z ∈ Vᶜ := hSU ▸ Set.mem_sUnion.mpr ⟨t, htS, hzt⟩
    have hyz : y ≤ z := (hle y z).mpr (specializes_iff_mem_closure.mpr (hgen ▸ hyt))
    have hyeq : y = z := by
      by_contra hne
      have hlt : y < z := lt_of_le_not_ge hyz fun hzy => hne (hanti y z hyz hzy)
      have h0 : coheight z = 0 :=
        Order.lt_one_iff.mp (coheight_le_coe_iff.mp (by simpa using hy1.le) z hlt)
      have hmax : IsMax z := coheight_eq_zero.mp h0
      have hzg : z ≤ genericPoint Y := (hle z _).mpr (genericPoint_specializes z)
      exact hzV (hanti z _ hzg (hmax hzg) ▸ hV)
    exact Set.mem_biUnion htS (by simpa [hyeq] using hgen)

end Stacks.AlgebraicGeometry.UnitsBoundaryValuations
