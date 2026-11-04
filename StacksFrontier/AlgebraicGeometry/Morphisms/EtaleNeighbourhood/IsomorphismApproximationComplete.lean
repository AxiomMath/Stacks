module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation
public import StacksFrontier.RingTheory.GRing.Criteria
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Approximating an isomorphism of completed local rings over a complete local base

Tag 0CAV approximates an isomorphism of completed local rings by a diagram of elementary étale
neighbourhoods over a base `S`, under two side conditions on `S`: that `S` be locally Noetherian,
and that the local ring of `S` at the common image point be a G-ring. Both conditions hold
automatically when `S = Spec Λ` for `Λ` a complete Noetherian local ring, and this file records
the resulting unconditional specialization.

## Main results

* `StacksDraft.ArtinApproximation.isGRing_stalk_spec`: the local ring of `Spec R` at any point is
  a G-ring as soon as `R` is one.
* `StacksDraft.ArtinApproximation.exists_common_elementaryEtaleNeighborhood_over_spec_complete`:
  Tag 0CAV over the base `Spec Λ` with `Λ` a complete Noetherian local ring, with no remaining
  hypotheses on the base.

## Implementation notes

The G-ring side condition is discharged for an *arbitrary* point of `Spec Λ`, not just the closed
point. The local ring of `Spec R` at a prime `p` is a localization of `R` at `p`
(`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`), hence essentially of finite type
over `R` (`Algebra.EssFiniteType.of_isLocalization`), so Tag 07PV
(`isGRing_of_essFiniteType`) applies directly; no transport along a ring isomorphism is needed.
That `Λ` itself is a G-ring is Tag 07PS, `isGRing_of_isPrecomplete_maximalIdeal`.

Local Noetherianity of the base is Mathlib's instance for `Spec` of a Noetherian ring, and is
found by instance search.

Completeness of `Λ` is spelled as `IsPrecomplete (maximalIdeal Λ) Λ`, which is the hypothesis
shape of Tag 07PS; separatedness is not needed.

## References

* [Stacks Project, Tag 0CAV](https://stacks.math.columbia.edu/tag/0CAV)
* [Stacks Project, Tag 07PS](https://stacks.math.columbia.edu/tag/07PS)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- **Tag 07PV for the local rings of an affine scheme.** If `R` is a G-ring then so is the local
ring of `Spec R` at any point `p`: that local ring is the localization of `R` at the prime `p`,
hence essentially of finite type over `R`. -/
public theorem isGRing_stalk_spec (R : Type u) [CommRing R] (hR : IsGRing R)
    (p : Spec (CommRingCat.of R)) :
    IsGRing ((Spec (CommRingCat.of R)).presheaf.stalk p) := by
  have : p.asIdeal.IsPrime := p.isPrime
  let : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
    StructureSheaf.stalkAlgebra R p
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R p
  have : Algebra.EssFiniteType R ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
    Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl
  exact isGRing_of_essFiniteType hR

/-- **Stacks Project, Tag 0CAV over a complete Noetherian local base.** Let `Λ` be a Noetherian
local ring complete for its maximal-ideal-adic topology, let `f : X ⟶ Spec Λ` and
`g : Y ⟶ Spec Λ` be locally of finite type, and let `x ∈ X` and `y ∈ Y` lie over a common point
of `Spec Λ`. Suppose given an isomorphism `Φ : 𝒪^∧_{Y, y} ≅ 𝒪^∧_{X, x}` compatible with the two
maps from the local ring of the base at that point. Then for every `N ≥ 1` there is a single
pointed scheme `(U, u)` sitting in a diagram `(X, x) ← (U, u) → (Y, y)` over `Spec Λ` in which
*both* legs are elementary étale neighbourhoods, and over which the triangle of completed local
rings commutes modulo `𝔪_u ^ N`.

This is `exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv` with its two side
conditions on the base discharged. Local Noetherianity of `Spec Λ` is instance-level; the G-ring
hypothesis is `isGRing_stalk_spec` applied to Tag 07PS. The image point `f x` is arbitrary — it is
not assumed to be the closed point of `Spec Λ`. -/
public theorem exists_common_elementaryEtaleNeighborhood_over_spec_complete
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [IsLocalRing Λ]
    [IsPrecomplete (maximalIdeal Λ) Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of Λ)) (g : Y ⟶ Spec (CommRingCat.of Λ))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) (y : Y) (hxy : f x = g y) (N : ℕ) (hN : 1 ≤ N)
    (Φ : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hΦ : Φ.toRingHom.comp ((algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))).comp
          (((Spec (CommRingCat.of Λ)).presheaf.stalkCongr (.of_eq hxy)).hom ≫
            g.stalkMap y).hom) =
      (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (f.stalkMap x).hom) :
    ∃ (U : EtaleNeighborhood X x) (q : U.scheme ⟶ Y) (hqEt : Etale q) (hq : q U.point = y),
      U.IsElementary ∧ (U.along q hqEt hq).IsElementary ∧ q ≫ g = U.toBase ≫ f ∧
        ∀ z : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y),
          @HSub.hSub _ _ _ instHSub (U.completionMap (Φ z))
              ((U.along q hqEt hq).completionMap z) ∈
            Ideal.map (algebraMap (U.scheme.presheaf.stalk U.point)
              (AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
                (U.scheme.presheaf.stalk U.point)))
              (maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N) :=
  exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv f g x y hxy
    (isGRing_stalk_spec Λ (isGRing_of_isPrecomplete_maximalIdeal Λ) (f x)) N hN Φ hΦ

end StacksDraft.ArtinApproximation

end
