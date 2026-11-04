module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.FlatPullbackVariety
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.Defs
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionProductCycle

/-!
# The intersection product of two closed subvarieties

The intersection product of Section 43.14 is formed from two coherent modules by
`AlgebraicGeometry.TorFormula.intersectionProductCycle`, which asks for a bound on the
delta-dimension of the support of each `Tor` sheaf. For the case the source is really after —
two closed subvarieties `W`, `V` of a nonsingular variety which intersect properly, and the
index `k` with `dim W + dim V = dim X + k` — that bound is not an extra assumption but a
consequence of proper intersection. This file supplies the subvarieties as coherent modules and
derives the bound, so that `W · V` can be formed from the proper-intersection hypothesis of
Definition 43.13.5 alone.

The derivation is three steps. The `Tor` sheaves are supported in `W ∩ V`, by the support clause
of Tag 0AZT. Proper intersection bounds the dimension of `W ∩ V` by `k`. And over a field the
delta-dimension of the support of a coherent sheaf is bounded by its topological dimension.

## Main definitions

* `AlgebraicGeometry.TorFormula.subvarietyStructureSheaf` — the structure sheaf `𝒪_W` of a closed
  subvariety, as a coherent `𝒪_X`-module.

## Main results

* `AlgebraicGeometry.TorFormula.supp_subvarietyStructureSheaf` — its support is `W`.
* `AlgebraicGeometry.TorFormula.topologicalKrullDim_subscheme_vanishingIdeal` — the reduced
  induced subscheme on a closed subset has the dimension of that subset.
* `AlgebraicGeometry.TorFormula.supp_torSheaf_subvariety` — the `Tor` sheaves of two
  subvarieties are supported in the intersection.
* `AlgebraicGeometry.TorFormula.topologicalKrullDim_inter_le_of_intersectProperly` — proper
  intersection bounds the dimension of the intersection by `k`.
* `AlgebraicGeometry.TorFormula.schemeDeltaDimension_torSheaf_subvariety_le` — the bound that
  `intersectionProductCycle` consumes, derived from proper intersection.

## Implementation notes

The structure sheaf of the subvariety is the direct image of the monoidal unit along the
inclusion of the reduced induced closed subscheme,
`(Scheme.Modules.pushforward (vanishingIdeal _).subschemeι).obj (Stacks.Ample.unitModule _)`,
which is the spelling the Chow tree already uses in
`StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme`; its coherence is registered
as an instance there, and again here for the named form, because instance search does not unfold
a `def` to find it.

Dimensions of subvarieties and of the ambient scheme are spelled with
`TopologicalSpace.topologicalKrullDim`, as `AlgebraicGeometry.IntersectProperly` is, and the
index is a natural number `k` given by `dim W + dim V = dim X + k` rather than by subtraction, so
that no truncated or extended subtraction occurs.

## References

* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

/-- **The structure sheaf of a closed subvariety**, as an `𝒪_X`-module: the direct image of the
structure sheaf of the reduced induced closed subscheme on `W`. -/
def subvarietyStructureSheaf {X : Scheme.{u}} (W : IrreducibleCloseds X) : X.Modules :=
  (Scheme.Modules.pushforward
    (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subschemeι).obj
      (Stacks.Ample.unitModule _)

/-- The structure sheaf of a closed subvariety is coherent on a locally Noetherian scheme. -/
instance isCoherent_subvarietyStructureSheaf {X : Scheme.{u}} [IsLocallyNoetherian X]
    (W : IrreducibleCloseds X) : SheafOfModules.IsCoherent (subvarietyStructureSheaf W) :=
  Stacks.Chow.isCoherent_pushforwardStructureSheaf _

/-- The support of `𝒪_W` is `W`. -/
theorem supp_subvarietyStructureSheaf {X : Scheme.{u}} [IsLocallyNoetherian X]
    (W : IrreducibleCloseds X) :
    SheafOfModules.supp (subvarietyStructureSheaf W) = (W : Set X) := by
  rw [subvarietyStructureSheaf, Stacks.Chow.supp_pushforwardStructureSheaf]
  exact (Scheme.IdealSheafData.range_subschemeι _).trans (by simp)

/-- **The reduced induced subscheme on a closed subset has the dimension of that subset.** Its
inclusion is a closed embedding with range the subset, hence a homeomorphism onto it. -/
theorem topologicalKrullDim_subscheme_vanishingIdeal {X : Scheme.{u}} (W : IrreducibleCloseds X) :
    topologicalKrullDim ((Scheme.IdealSheafData.vanishingIdeal
        ⟨(W : Set X), W.isClosed⟩).subscheme) = topologicalKrullDim (W : Set X) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨(W : Set X), W.isClosed⟩ with hI
  have hrange : Set.range (ConcreteCategory.hom I.subschemeι.base) = (W : Set X) := by
    rw [hI, Scheme.IdealSheafData.range_subschemeι]; simp
  exact ((I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)).isHomeomorph).topologicalKrullDim_eq _

/-- **The `Tor` sheaves of two closed subvarieties are supported in their intersection.** -/
theorem supp_torSheaf_subvariety {X : Scheme.{u}} [IsLocallyNoetherian X]
    (W V : IrreducibleCloseds X) (i : ℕ) :
    SheafOfModules.supp (torSheaf X (subvarietyStructureSheaf W) (subvarietyStructureSheaf V) i)
      ⊆ (W : Set X) ∩ (V : Set X) := by
  refine (supp_torSheaf_subset_inter X _ _ i).trans ?_
  rw [supp_subvarietyStructureSheaf, supp_subvarietyStructureSheaf]

/-- Cancelling a finite summand on both sides of an inequality of extended dimensions. -/
private theorem le_of_add_le_add_natCast {A : WithBot ℕ∞} {n k : ℕ}
    (h : A + (n : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) + (k : WithBot ℕ∞)) :
    A ≤ (k : WithBot ℕ∞) := by
  cases A with
  | bot => simp
  | coe a =>
    rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, ← WithBot.coe_add,
      WithBot.coe_le_coe] at h
    rw [← WithBot.coe_natCast, WithBot.coe_le_coe]
    cases a with
    | top => exact absurd h (by simp)
    | coe m =>
      have hmn : (m : ℕ) + n ≤ n + k := by exact_mod_cast h
      have : (m : ℕ) ≤ k := by omega
      exact_mod_cast this

/-- **Proper intersection bounds the dimension of the intersection.** If `W` and `V` have
dimensions `r` and `s`, the ambient scheme has dimension `n`, and `r + s = n + k`, then two
properly intersecting subvarieties meet in dimension at most `k`. -/
theorem topologicalKrullDim_inter_le_of_intersectProperly {X : Scheme.{u}}
    (W V : IrreducibleCloseds X) (r s n k : ℕ)
    (hW : topologicalKrullDim (W : Set X) = (r : WithBot ℕ∞))
    (hV : topologicalKrullDim (V : Set X) = (s : WithBot ℕ∞))
    (hX : topologicalKrullDim X = (n : WithBot ℕ∞)) (hrs : r + s = n + k)
    (hWV : AlgebraicGeometry.IntersectProperly W V) :
    topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) ≤ (k : WithBot ℕ∞) := by
  rw [AlgebraicGeometry.intersectProperly_iff, hW, hV, hX] at hWV
  refine le_of_add_le_add_natCast (n := n) ?_
  refine hWV.trans (le_of_eq ?_)
  rw [← Nat.cast_add, ← Nat.cast_add, hrs]

/-- **The bound that the intersection product consumes, derived from proper intersection.** For
two properly intersecting closed subvarieties of a scheme over a field, the delta-dimension of
the support of each `Tor` sheaf is at most `k`. -/
theorem schemeDeltaDimension_torSheaf_subvariety_le (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ (Stacks.Chow.fieldChowSituation K).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) (W V : IrreducibleCloseds X) (r s n k : ℕ)
    (hW : topologicalKrullDim (W : Set X) = (r : WithBot ℕ∞))
    (hV : topologicalKrullDim (V : Set X) = (s : WithBot ℕ∞))
    (hXd : topologicalKrullDim X = (n : WithBot ℕ∞)) (hrs : r + s = n + k)
    (hWV : AlgebraicGeometry.IntersectProperly W V) (i : ℕ) :
    have := isCoherent_torSheaf_of_isRegular X hX (subvarietyStructureSheaf W)
      (subvarietyStructureSheaf V) inferInstance inferInstance i
    Stacks.Chow.schemeDeltaDimension (Stacks.Chow.fieldChowSituation K)
      ((Stacks.Chow.reducedSupport
        (torSheaf X (subvarietyStructureSheaf W) (subvarietyStructureSheaf V) i)).subschemeι
          ≫ sX) ≤ WithBotTop.coe (k : ℤ) := by
  have := isCoherent_torSheaf_of_isRegular X hX (subvarietyStructureSheaf W)
    (subvarietyStructureSheaf V) inferInstance inferInstance i
  exact Stacks.Chow.schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX _ k
    ((topologicalKrullDim_le_of_subset (supp_torSheaf_subvariety W V i)).trans
      (topologicalKrullDim_inter_le_of_intersectProperly W V r s n k hW hV hXd hrs hWV))

end AlgebraicGeometry.TorFormula

end
