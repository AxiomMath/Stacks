module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.DivisorFibreCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.SubvarietyIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectionDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesSeparablePointsBertini
import StacksCore.Tactic.StacksAttribute

/-!
# The intersection product of two properly intersecting closed subvarieties

Let `X` be a nonsingular variety and let `W`, `V ⊆ X` be closed subvarieties with `dim W = s` and
`dim V = r` which intersect properly. Section 43.14 of the source defines

`W · V = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_{r + s - dim X}`

and observes that this is a formal linear combination `∑ e_Z [Z]` of the irreducible components
`Z` of `V ∩ W`, whose coefficients are the intersection multiplicities

`e(X, V · W, Z) = ∑ᵢ (-1)ⁱ length_{𝒪_{X, Z}} Torᵢ^{𝒪_{X, Z}}(𝒪_{W, Z}, 𝒪_{V, Z})`.

This file forms `W · V` from exactly these data and proves what the section says about it.

## Main definitions

* `AlgebraicGeometry.TorFormula.subvarietyIntersectionProduct` — **Tag 0AZR**, the cycle `W · V`
  of two properly intersecting closed subvarieties, in dimension `r + s - dim X`.

## Main results

* `AlgebraicGeometry.TorFormula.schemeDeltaDimension_torSheaf_subvariety_le_sub` — every `Tor`
  sheaf of `𝒪_W` and `𝒪_V` is supported in dimension at most `r + s - dim X`, which is what makes
  `[Torᵢ]_{r + s - dim X}` a cycle. When `r + s < dim X` the intersection is empty.
* `AlgebraicGeometry.TorFormula.subvarietyIntersectionProduct_eq_sum` — the alternating sum is
  the finite sum over `0 ≤ i ≤ dim X`.
* `AlgebraicGeometry.TorFormula.subvarietyIntersectionProduct_apply_of_relativeDimension_eq` —
  at a point of `W ∩ V` of dimension `r + s - dim X` the coefficient is the alternating sum of
  lengths of local `Tor` modules, `Stacks.Intersection.intersectionMultiplicity`.
* `AlgebraicGeometry.TorFormula.mem_inter_of_subvarietyIntersectionProduct_apply_ne_zero` — a
  point with nonzero coefficient is the generic point of an irreducible component of `W ∩ V`.
* `AlgebraicGeometry.TorFormula.subvarietyIntersectionProduct_apply` — **Tag 0AZR**,
  `W · V = ∑ e(X, V · W, Z) [Z]` over the irreducible components `Z` of `V ∩ W`: over an
  algebraically closed field the coefficient at a point is `e(X, V · W, Z)` when the point is the
  generic point of a component `Z`, and zero otherwise.

## Implementation notes

The ambient scheme is regular, locally Noetherian and locally of finite type over a field `K`,
and has dimension `n`; a nonsingular variety over `K` is such a scheme. Closed subvarieties are
irreducible closed subsets, with the reduced induced structure, as in
`AlgebraicGeometry.IntersectProperly`. The generic points of the irreducible components of
`W ∩ V` are spelled as the points `z ∈ W ∩ V` that are not a proper specialization of another
point of `W ∩ V`. The index `r + s - dim X` is the integer `r + s - n`, which may be negative,
in which case `W ∩ V` is empty and `W · V = 0`.

For the description of the coefficients by components, Tag 0AZP is used: every component of
`V ∩ W` has dimension at least `r + s - dim X`; the source works over an algebraically closed
field throughout (Section 43.2), and so does that theorem.

## References

* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZP](https://stacks.math.columbia.edu/tag/0AZP)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

/-- **Below the expected dimension, properly intersecting subvarieties are disjoint.** If
`dim V + dim W < dim X` and `W`, `V` intersect properly, then `W ∩ V` is empty. -/
theorem topologicalKrullDim_inter_eq_bot_of_intersectProperly {X : Scheme.{u}}
    (W V : IrreducibleCloseds X) (r s n : ℕ)
    (hW : topologicalKrullDim (W : Set X) = (s : WithBot ℕ∞))
    (hV : topologicalKrullDim (V : Set X) = (r : WithBot ℕ∞))
    (hX : topologicalKrullDim X = (n : WithBot ℕ∞)) (hrs : r + s < n)
    (hWV : AlgebraicGeometry.IntersectProperly W V) :
    topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) = ⊥ := by
  rw [AlgebraicGeometry.intersectProperly_iff, hW, hV, hX] at hWV
  generalize topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) = A at hWV ⊢
  cases A with
  | bot => rfl
  | coe a =>
    exfalso
    rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add,
      ← WithBot.coe_add, WithBot.coe_le_coe] at hWV
    have h1 : (n : ℕ∞) ≤ ((s + r : ℕ) : ℕ∞) := by
      push_cast
      exact le_add_self.trans hWV
    have h2 : n ≤ s + r := by exact_mod_cast h1
    omega

/-- **The `Tor` sheaves of two properly intersecting subvarieties are supported in dimension at
most `r + s - dim X`.** For `dim W = s`, `dim V = r` and `dim X = n`, the support of each
`Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)` has delta-dimension at most the integer `r + s - n`: it lies in `W ∩ V`,
which proper intersection bounds by `r + s - n`, and which is empty when `r + s < n`. -/
theorem schemeDeltaDimension_torSheaf_subvariety_le_sub (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ (Stacks.Chow.fieldChowSituation K).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) (W V : IrreducibleCloseds X) (r s n : ℕ)
    (hW : topologicalKrullDim (W : Set X) = (s : WithBot ℕ∞))
    (hV : topologicalKrullDim (V : Set X) = (r : WithBot ℕ∞))
    (hXd : topologicalKrullDim X = (n : WithBot ℕ∞))
    (hWV : AlgebraicGeometry.IntersectProperly W V) (i : ℕ) :
    have := isCoherent_torSheaf_of_isRegular X hX (subvarietyStructureSheaf W)
      (subvarietyStructureSheaf V) inferInstance inferInstance i
    Stacks.Chow.schemeDeltaDimension (Stacks.Chow.fieldChowSituation K)
      ((Stacks.Chow.reducedSupport
        (torSheaf X (subvarietyStructureSheaf W) (subvarietyStructureSheaf V) i)).subschemeι
          ≫ sX) ≤ WithBotTop.coe ((r : ℤ) + s - n) := by
  have := isCoherent_torSheaf_of_isRegular X hX (subvarietyStructureSheaf W)
    (subvarietyStructureSheaf V) inferInstance inferInstance i
  rcases le_or_gt n (r + s) with h | h
  · have hk : (r : ℤ) + s - n = ((r + s - n : ℕ) : ℤ) := by omega
    rw [hk]
    exact schemeDeltaDimension_torSheaf_subvariety_le K sX hX W V s r n (r + s - n) hW hV hXd
      (by omega) hWV i
  · have hbot := topologicalKrullDim_inter_eq_bot_of_intersectProperly W V r s n hW hV hXd h hWV
    rw [topologicalKrullDim_eq_bot_iff_isEmpty] at hbot
    exact Stacks.Chow.schemeDeltaDimension_reducedSupport_le _ sX _ fun x hx =>
      (hbot.false ⟨x, supp_torSheaf_subvariety W V i hx⟩).elim

/-- **Stacks 0AZR: the intersection product of two closed subvarieties.** Let `X` be a regular
scheme of dimension `n`, locally of finite type over a field, and let `W`, `V` be closed
subvarieties of dimensions `s` and `r` which intersect properly. Their intersection product is
the cycle

`W · V = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_{r + s - n}`.

Each summand is a cycle because the `Tor` sheaves are coherent and supported in dimension at most
`r + s - n` (`schemeDeltaDimension_torSheaf_subvariety_le_sub`), and only the summands with
`i ≤ n` are nonzero (`subvarietyIntersectionProduct_eq_sum`). -/
@[stacks 0AZR "the definition of the intersection product `W · V = ∑ᵢ (-1)ⁱ \
[Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_{r + s - dim X}` of two closed subvarieties `W`, `V` of dimensions `s` \
and `r` of a nonsingular variety `X` which intersect properly, from the source's data alone: the \
support bound that makes each `[Torᵢ]_{r + s - dim X}` a cycle is proved from proper \
intersection by `schemeDeltaDimension_torSheaf_subvariety_le_sub`. The ambient scheme is any \
regular scheme of finite dimension locally of finite type over a field."]
def subvarietyIntersectionProduct (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ (Stacks.Chow.fieldChowSituation K).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) (W V : IrreducibleCloseds X) {r s n : ℕ}
    (hW : topologicalKrullDim (W : Set X) = (s : WithBot ℕ∞))
    (hV : topologicalKrullDim (V : Set X) = (r : WithBot ℕ∞))
    (hXd : topologicalKrullDim X = (n : WithBot ℕ∞))
    (hWV : AlgebraicGeometry.IntersectProperly W V) : AlgebraicCycle X ℤ :=
  intersectionProductCycle (Stacks.Chow.fieldChowSituation K) sX hX (subvarietyStructureSheaf W)
    (subvarietyStructureSheaf V) inferInstance inferInstance ((r : ℤ) + s - n)
    (schemeDeltaDimension_torSheaf_subvariety_le_sub K sX hX W V r s n hW hV hXd hWV)

section

variable (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ (Stacks.Chow.fieldChowSituation K).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) (W V : IrreducibleCloseds X) {r s n : ℕ}
    (hW : topologicalKrullDim (W : Set X) = (s : WithBot ℕ∞))
    (hV : topologicalKrullDim (V : Set X) = (r : WithBot ℕ∞))
    (hXd : topologicalKrullDim X = (n : WithBot ℕ∞))
    (hWV : AlgebraicGeometry.IntersectProperly W V)

/-- **The alternating sum is finite**: `W · V` is the sum of the terms with `0 ≤ i ≤ dim X`, the
`Tor` sheaves vanishing above the dimension of `X` (Tag 0AZT). -/
theorem subvarietyIntersectionProduct_eq_sum :
    subvarietyIntersectionProduct K sX hX W V hW hV hXd hWV =
      ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) •
        (haveI := isCoherent_torSheaf_of_isRegular X hX (subvarietyStructureSheaf W)
          (subvarietyStructureSheaf V) inferInstance inferInstance i
         Stacks.Chow.coherentSheafCycle (Stacks.Chow.fieldChowSituation K) sX
          (torSheaf X (subvarietyStructureSheaf W) (subvarietyStructureSheaf V) i)
          ((r : ℤ) + s - n)
          (schemeDeltaDimension_torSheaf_subvariety_le_sub K sX hX W V r s n hW hV hXd hWV i)) := by
  have hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y) :=
    fun y => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX y
  rw [subvarietyIntersectionProduct, intersectionProductCycle,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) ?_]
  intro i hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hle
  exact hi (torSheafCycle_eq_zero_of_lt _ sX hX _ _ inferInstance inferInstance _ _ hreg n hXd.le i
    (by omega))

/-- **The coefficient of `W · V` at a point of `W ∩ V` of the expected dimension** is the
intersection multiplicity there: the alternating sum
`∑ᵢ (-1)ⁱ length_{𝒪_{X, z}} Torᵢ^{𝒪_{X, z}}(𝒪_{V, z}, 𝒪_{W, z})` of the lengths of the `Tor`
modules of the two local rings, `𝒪_{W, z} = 𝒪_{X, z} ⧸ (I_W)_z` and `𝒪_{V, z} = 𝒪_{X, z} ⧸ (I_V)_z`.
-/
theorem subvarietyIntersectionProduct_apply_of_relativeDimension_eq {z : X}
    (hzW : z ∈ (W : Set X)) (hzV : z ∈ (V : Set X))
    (hz : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation K).dimensionFunction sX z =
      (r : ℤ) + s - n) :
    (subvarietyIntersectionProduct K sX hX W V hW hV hXd hWV z : ℚ) =
      Stacks.Intersection.intersectionMultiplicity
        (Scheme.IdealSheafData.vanishingIdeal ⟨(V : Set X), V.isClosed⟩)
        (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩) z := by
  classical
  have hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y) :=
    fun y => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX y
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨(W : Set X), W.isClosed⟩ with hI
  set J := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨(V : Set X), V.isClosed⟩ with hJ
  have hzI : z ∈ I.support := by
    change z ∈ (I.support : Set X)
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hzW
  have hzJ : z ∈ J.support := by
    change z ∈ (J.support : Set X)
    rw [hJ, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hzV
  rw [subvarietyIntersectionProduct, intersectionProductCycle_apply _ sX hX _ _ _ _ _ _ hreg n
    hXd.le z]
  have hterm : ∀ i : ℕ,
      (haveI := isCoherent_torSheaf_of_isRegular X hX (subvarietyStructureSheaf W)
        (subvarietyStructureSheaf V) inferInstance inferInstance i
       Stacks.Chow.sheafCycleCoeff (Stacks.Chow.fieldChowSituation K) sX
        (torSheaf X (subvarietyStructureSheaf W) (subvarietyStructureSheaf V) i)
        ((r : ℤ) + s - n) z) =
      (Module.length (X.presheaf.stalk z)
        (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) i).obj
            (ModuleCat.of (X.presheaf.stalk z)
              (X.presheaf.stalk z ⧸ IdealSheafData.stalk J z))).obj
          (ModuleCat.of (X.presheaf.stalk z)
            (X.presheaf.stalk z ⧸ IdealSheafData.stalk I z)))).toNat := by
    intro i
    have := isCoherent_torSheaf_of_isRegular X hX (subvarietyStructureSheaf W)
      (subvarietyStructureSheaf V) inferInstance inferInstance i
    refine Eq.trans (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq
      _ sX _ _ (schemeDeltaDimension_torSheaf_subvariety_le_sub K sX hX W V r s n hW hV hXd hWV i)
      hz) ?_
    refine Eq.trans (sheafMultiplicity_torSheaf_subschemeStructureSheaf I J i z hzI hzJ) ?_
    rw [Module.length_tor_comm]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hterm i]),
    Stacks.Intersection.intersectionMultiplicity_eq, Ideal.localIntersectionMultiplicity,
    tsum_eq_sum (s := Finset.range (n + 2)) (fun i hi => ?_)]
  · push_cast
    rfl
  · rw [Finset.mem_range, not_lt] at hi
    have := hreg z
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.subsingleton_of_isZero
      (isZero_Tor_of_isRegularLocalRing _ _ n i
        ((ringKrullDim_stalk_le X z).trans hXd.le) (by omega)))]
    simp

omit [IsLocallyNoetherian X] in
include hW hV hXd hWV in
/-- A point of `W ∩ V` has relative dimension at most `r + s - dim X`. -/
theorem relativeDimension_le_of_mem_inter {y : X} (hy : y ∈ (W : Set X) ∩ (V : Set X)) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation K).dimensionFunction sX y ≤
      (r : ℤ) + s - n := by
  rcases le_or_gt n (r + s) with h | h
  · have hdim := topologicalKrullDim_inter_le_of_intersectProperly W V s r n (r + s - n) hW hV hXd
      (by omega) hWV
    have hcl : topologicalKrullDim ↥(closure ({y} : Set X)) ≤ ((r + s - n : ℕ) : WithBot ℕ∞) :=
      (topologicalKrullDim_le_of_subset (closure_minimal (Set.singleton_subset_iff.mpr hy)
        (W.isClosed.inter V.isClosed))).trans hdim
    rw [topologicalKrullDim_closure_eq_toNat_relativeDimension K sX y] at hcl
    have h' : (Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation K).dimensionFunction
        sX y).toNat ≤ r + s - n := by exact_mod_cast hcl
    have := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field K sX y
    omega
  · have hbot := topologicalKrullDim_inter_eq_bot_of_intersectProperly W V r s n hW hV hXd h hWV
    rw [topologicalKrullDim_eq_bot_iff_isEmpty] at hbot
    exact (hbot.false ⟨y, hy⟩).elim

/-- **`W · V` is a combination of the irreducible components of `W ∩ V`.** A point at which
`W · V` has a nonzero coefficient lies in `W ∩ V`, has dimension `r + s - dim X`, and is the
generic point of an irreducible component of `W ∩ V`: no other point of `W ∩ V` specializes
to it. -/
theorem mem_inter_of_subvarietyIntersectionProduct_apply_ne_zero {z : X}
    (h : subvarietyIntersectionProduct K sX hX W V hW hV hXd hWV z ≠ 0) :
    z ∈ (W : Set X) ∩ (V : Set X) ∧
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation K).dimensionFunction sX z =
        (r : ℤ) + s - n ∧
      ∀ y ∈ (W : Set X) ∩ (V : Set X), z ∈ closure ({y} : Set X) → y = z := by
  classical
  have hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y) :=
    fun y => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX y
  rw [subvarietyIntersectionProduct, intersectionProductCycle_apply _ sX hX _ _ _ _ _ _ hreg n
    hXd.le z] at h
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hi' := right_ne_zero_of_mul hi
  have := isCoherent_torSheaf_of_isRegular X hX (subvarietyStructureSheaf W)
    (subvarietyStructureSheaf V) inferInstance inferInstance i
  have hcond : z ∈ SheafOfModules.supp
        (torSheaf X (subvarietyStructureSheaf W) (subvarietyStructureSheaf V) i) ∧
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation K).dimensionFunction sX z =
        (r : ℤ) + s - n := by
    by_contra hc
    exact hi' (by simp only [Stacks.Chow.sheafCycleCoeff, hc, ite_false])
  have hzWV := supp_torSheaf_subvariety W V i hcond.1
  refine ⟨hzWV, hcond.2, fun y hy hzy => ?_⟩
  by_contra hne
  have hlt := Stacks.Chow.relativeDimension_lt_of_mem_closure_of_ne
    (Stacks.Chow.fieldChowSituation K) sX hzy (Ne.symm hne)
  have hle := relativeDimension_le_of_mem_inter K sX W V hW hV hXd hWV hy
  omega

end

/-- **Tag 0AZP at a generic point of a component of `W ∩ V`.** Over an algebraically closed
field, on a nonsingular variety of dimension `n`, the generic point of an irreducible component of
the intersection of closed subvarieties of dimensions `s` and `r` has dimension at least
`r + s - n`; for properly intersecting subvarieties it is exactly `r + s - n`. -/
theorem relativeDimension_eq_of_isGenericPoint_component (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [IsVariety K sX] (hX : IsRegular X)
    (W V : IrreducibleCloseds X) {r s n : ℕ}
    (hW : topologicalKrullDim (W : Set X) = (s : WithBot ℕ∞))
    (hV : topologicalKrullDim (V : Set X) = (r : WithBot ℕ∞))
    (hXd : topologicalKrullDim X = (n : WithBot ℕ∞))
    (hWV : AlgebraicGeometry.IntersectProperly W V) {z : X}
    (hz : z ∈ (W : Set X) ∩ (V : Set X))
    (hmax : ∀ y ∈ (W : Set X) ∩ (V : Set X), z ∈ closure ({y} : Set X) → y = z) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation K).dimensionFunction sX z =
      (r : ℤ) + s - n := by
  refine le_antisymm (relativeDimension_le_of_mem_inter K sX W V hW hV hXd hWV hz) ?_
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨(W : Set X), W.isClosed⟩ with hI
  set J := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨(V : Set X), V.isClosed⟩ with hJ
  have := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    ⟨(W : Set X), W.isClosed⟩ W.isIrreducible
  have := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    ⟨(V : Set X), V.isClosed⟩ V.isIrreducible
  have hF : ((I.support : Set X) ∩ (J.support : Set X)) = (W : Set X) ∩ (V : Set X) := by
    rw [hI, hJ, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hz' : z ∈ ((I.support : Set X) ∩ (J.support : Set X)) := hF ▸ hz
  obtain ⟨c, hc, hzc⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({(⟨z, hz'⟩ : ↥((I.support : Set X) ∩ (J.support : Set X)))} : Set _))
    isIrreducible_singleton.closure
  have hcl : IsClosed (Subtype.val '' c : Set X) :=
    (IsClosed.isClosedMap_subtype_val ((I.support.isClosed).inter J.support.isClosed)) c
      (isClosed_of_mem_irreducibleComponents c hc)
  have hirr : IsIrreducible (Subtype.val '' c : Set X) :=
    hc.1.image _ continuous_subtype_val.continuousOn
  set y := hirr.genericPoint with hydef
  have hyD : closure ({y} : Set X) = Subtype.val '' c := hirr.closure_genericPoint hcl
  have hy : y ∈ (W : Set X) ∩ (V : Set X) := by
    have : y ∈ (Subtype.val '' c : Set X) := hyD ▸ subset_closure rfl
    obtain ⟨⟨y', hy'⟩, -, rfl⟩ := this
    exact hF ▸ hy'
  have hzy : z ∈ closure ({y} : Set X) := by
    rw [hyD]
    exact ⟨⟨z, hz'⟩, hzc (subset_closure rfl), rfl⟩
  have hyz : y = z := hmax y hy hzy
  have h0AZP :=
    Stacks.Intersection.add_topologicalKrullDim_le_add_topologicalKrullDim_of_irreducibleComponent
      sX hX I J c hc
  have hdc : topologicalKrullDim ↥c = topologicalKrullDim ↥(closure ({z} : Set X)) := by
    rw [← hyz, hyD]
    exact (topologicalKrullDim_image_eq_of_isEmbedding Topology.IsEmbedding.subtypeVal c).symm
  rw [hdc, topologicalKrullDim_closure_eq_toNat_relativeDimension K sX z, hI, hJ,
    topologicalKrullDim_subscheme_vanishingIdeal W, topologicalKrullDim_subscheme_vanishingIdeal V,
    hW, hV, hXd] at h0AZP
  have h' : s + r ≤ n + (Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation K).dimensionFunction sX z).toNat := by
    exact_mod_cast h0AZP
  have := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field K sX z
  omega

/-- **Stacks 0AZR: `W · V = ∑ e(X, V · W, Z) [Z]`.** Let `X` be a nonsingular variety of dimension
`n` over an algebraically closed field and let `W`, `V` be closed subvarieties of dimensions `s`
and `r` which intersect properly. Then the cycle `W · V` is the formal linear combination of the
irreducible components `Z` of `V ∩ W` with coefficients the intersection multiplicities
`e(X, V · W, Z) = ∑ᵢ (-1)ⁱ length_{𝒪_{X, Z}} Torᵢ^{𝒪_{X, Z}}(𝒪_{V, Z}, 𝒪_{W, Z})`: its
coefficient at the generic point of such a component is `e(X, V · W, Z)`, and at every other
point it is zero. -/
@[stacks 0AZR "the description of the intersection product `V · W` as the formal linear \
combination `∑ e_Z Z` of the irreducible components `Z` of `V ∩ W` with coefficients the \
intersection multiplicities `e_Z = e(X, V · W, Z) = ∑ᵢ (-1)ⁱ length Torᵢ^{𝒪_{X, Z}}(𝒪_{W, Z}, \
𝒪_{V, Z})`, the multiplicity being `Stacks.Intersection.intersectionMultiplicity` at the generic \
point of `Z` (the lengths of `Torᵢ(𝒪_{W, Z}, 𝒪_{V, Z})` and `Torᵢ(𝒪_{V, Z}, 𝒪_{W, Z})` agree). The \
generic points of the components of `V ∩ W` are the points of `V ∩ W` that are a specialization \
of no other point of `V ∩ W`, and the components all have dimension `r + s - dim X` by Tag 0AZP."]
theorem subvarietyIntersectionProduct_apply (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [IsVariety K sX] [IsLocallyNoetherian X]
    (hX : IsRegular X) (W V : IrreducibleCloseds X) {r s n : ℕ}
    (hW : topologicalKrullDim (W : Set X) = (s : WithBot ℕ∞))
    (hV : topologicalKrullDim (V : Set X) = (r : WithBot ℕ∞))
    (hXd : topologicalKrullDim X = (n : WithBot ℕ∞))
    (hWV : AlgebraicGeometry.IntersectProperly W V) (z : X) :
    open Classical in
    (subvarietyIntersectionProduct K sX hX W V hW hV hXd hWV z : ℚ) =
      if z ∈ (W : Set X) ∩ (V : Set X) ∧
          ∀ y ∈ (W : Set X) ∩ (V : Set X), z ∈ closure ({y} : Set X) → y = z then
        Stacks.Intersection.intersectionMultiplicity
          (Scheme.IdealSheafData.vanishingIdeal ⟨(V : Set X), V.isClosed⟩)
          (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩) z
      else 0 := by
  classical
  split_ifs with hc
  · exact subvarietyIntersectionProduct_apply_of_relativeDimension_eq K sX hX W V hW hV hXd hWV
      hc.1.1 hc.1.2
      (relativeDimension_eq_of_isGenericPoint_component K sX hX W V hW hV hXd hWV hc.1 hc.2)
  · have h0 : subvarietyIntersectionProduct K sX hX W V hW hV hXd hWV z = 0 := by
      by_contra hne
      obtain ⟨h1, -, h3⟩ :=
        mem_inter_of_subvarietyIntersectionProduct_apply_ne_zero K sX hX W V hW hV hXd hWV hne
      exact hc ⟨h1, h3⟩
    simp [h0]

end AlgebraicGeometry.TorFormula

end
