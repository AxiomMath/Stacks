module

public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraization
public import Mathlib.RingTheory.Jacobson.Ring

/-!
# The closed point of the formal neighbourhood is of finite type over the base

Let `D` be an ideal sheaf on a quasi-compact scheme `X` with nonempty support, let
`A = lim Γ(Cₙ, 𝒪)` be the ring of formal functions along `C = V(D)`, and suppose `A` is local with
maximal ideal `𝔪` contained in the kernel `F₁` of the projection `A ⟶ Γ(C₀, 𝒪)`. If `X` is locally
of finite type over `Spec R` for a Jacobson Noetherian ring `R`, then
`Spec κ(𝔪) ⟶ Spec A ⟶ Spec R` is locally of finite type.

Proof: a closed point `w` of `C₀` maps to the closed point of `Spec A` (its prime contains
`F₁ ⊇ 𝔪`), so `Spec κ(w) ⟶ Spec R` factors through `Spec κ(𝔪)`. As `Spec κ(w) ⟶ C₀ ⟶ X ⟶ Spec R`
is locally of finite type, `R ⟶ κ(𝔪) ⟶ κ(w)` is of finite type, and the subfield `κ(𝔪)` of
`κ(w)` is finite over `R` (Zariski's lemma over the Jacobson Noetherian ring `R`).

This is the hypothesis on the residue field of the closed point needed to build the contraction
situation of Stacks 0D5E.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningToSpec_zero_eq_closedPoint`: `C₀ ⟶ Spec A`
  sends every point to the closed point.
* `AlgebraicGeometry.Scheme.IdealSheafData.`
  `locallyOfFiniteType_fromSpecResidueField_comp_formalNeighborhoodToSpec`:
  `Spec κ(𝔪) ⟶ Spec R` is locally of finite type.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0CY7](https://stacks.math.columbia.edu/tag/0CY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- If the ring of formal functions `A` is local with maximal ideal inside the kernel `F₁` of the
projection `A ⟶ Γ(C₀, 𝒪)`, then `C₀ ⟶ Spec A` sends every point to the closed point. -/
theorem thickeningToSpec_zero_eq_closedPoint [IsLocalRing (formalNeighborhoodRing D)]
    (hI : IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ≤ formalNeighborhoodFiltration D 1)
    (w : thickening D 0) :
    thickeningToSpec D 0 w = IsLocalRing.closedPoint (formalNeighborhoodRing D) := by
  set p := thickeningToSpec D 0 w
  have hle : IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ≤ p.asIdeal := by
    refine hI.trans fun a ha => ?_
    have ha' : formalNeighborhoodProjection D 0 a = 0 := ha
    change formalNeighborhoodProjection D 0 a ∈ ((thickening D 0).toSpecΓ w).asIdeal
    rw [ha']
    exact Ideal.zero_mem _
  exact PrimeSpectrum.ext
    ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le p.isPrime.ne_top hle).symm

/-- **The closed point of the formal neighbourhood is of finite type over the base.** Let `D` be
an ideal sheaf with nonempty support on a quasi-compact scheme `X` locally of finite type over
`Spec R`, `R` Jacobson and Noetherian, and suppose the ring of formal functions `A` is local with
maximal ideal `𝔪 ⊆ F₁`. Then `Spec κ(𝔪) ⟶ Spec A ⟶ Spec R` is locally of finite type. -/
theorem locallyOfFiniteType_fromSpecResidueField_comp_formalNeighborhoodToSpec
    [IsLocalRing (formalNeighborhoodRing D)]
    (hI : IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ≤ formalNeighborhoodFiltration D 1)
    [CompactSpace X] (hne : (D.support : Set X).Nonempty)
    {R : CommRingCat.{u}} [IsJacobsonRing R] [IsNoetherianRing R] (f : X ⟶ Spec R)
    [LocallyOfFiniteType f] :
    LocallyOfFiniteType
      ((Spec (.of (formalNeighborhoodRing D))).fromSpecResidueField
          (IsLocalRing.closedPoint (formalNeighborhoodRing D)) ≫
        formalNeighborhoodToSpec D f) := by
  -- a closed point `w` of `C₀`
  have : CompactSpace (thickening D 0) :=
    QuasiCompact.compactSpace_of_compactSpace (D ^ (0 + 1)).subschemeι
  have hne0 : (Set.univ : Set (thickening D 0)).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    rw [← support_pow_succ D 0, ← range_subschemeι] at hx
    obtain ⟨w, -⟩ := hx
    exact ⟨w, trivial⟩
  obtain ⟨w, -, hw⟩ := isClosed_univ.exists_closed_singleton hne0
  have : IsClosedImmersion ((thickening D 0).fromSpecResidueField w) :=
    isClosed_singleton_iff_isClosedImmersion.mp hw
  rw [← thickeningToSpec_zero_eq_closedPoint D hI w]
  -- the composite `Spec κ(w) ⟶ Spec R` is locally of finite type
  have hw' : LocallyOfFiniteType (Spec.map ((thickeningToSpec D 0).residueFieldMap w) ≫
      (Spec (.of (formalNeighborhoodRing D))).fromSpecResidueField (thickeningToSpec D 0 w) ≫
        formalNeighborhoodToSpec D f) := by
    rw [Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
      thickeningToSpec_formalNeighborhoodToSpec]
    infer_instance
  set g := (Spec (.of (formalNeighborhoodRing D))).fromSpecResidueField (thickeningToSpec D 0 w) ≫
    formalNeighborhoodToSpec D f
  rw [← Spec.map_preimage g] at hw' ⊢
  rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hw'
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.FiniteType.of_finite
    (RingHom.finite_of_algHom_finiteType_of_isJacobsonRing (Spec.preimage g).hom
      ((thickeningToSpec D 0).residueFieldMap w).hom hw')

end AlgebraicGeometry.Scheme.IdealSheafData
