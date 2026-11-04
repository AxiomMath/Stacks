module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.FiniteSupport
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupOpenCover
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFiltration
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreRadicalComponents
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve

/-!
# The exceptional divisor of a regular local surface is a reduced irreducible curve

Let `(A, 𝔪)` be a regular local ring of Krull dimension two and let `X ⟶ Spec A` be the blowup
of `Spec A` in the closed point. The exceptional divisor `E` of that blowup is a reduced,
irreducible closed subscheme of dimension one: by [Stacks, Tag 0AGQ] part (1) it is isomorphic to
`𝐏¹` over the residue field, and the projective line over a field is an integral scheme of
dimension one.

Consequently, a sheaf of ideals supported on `E` is the maximal power of `E` dividing it times a
sheaf of ideals whose support is a finite set of closed points: the finite-support assertion of
[Stacks, Tag 0AGT].

## Main results

* `AlgebraicGeometry.radical_exceptionalIdeal_eq_self` — the exceptional ideal sheaf is radical.
* `AlgebraicGeometry.isIrreducible_support_exceptionalIdeal` — its support is irreducible.
* That support has topological Krull dimension one: this is
  `AlgebraicGeometry.topologicalKrullDim_exceptionalDivisor_residuePoint` ([Stacks, Tag 0B63]),
  read on the support by `Stacks.Chow.topologicalKrullDim_subscheme`.
* `AlgebraicGeometry.exists_finite_isClosed_support_of_maximal_order_blowUp` — the
  finite-support assertion of [Stacks, Tag 0AGT] for the blowup of a regular local surface.

## References

* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The exceptional divisor of the affine blowup -/

/-- The exceptional divisor of the affine blowup of a two-dimensional regular local ring is an
integral scheme of dimension one. -/
private theorem isIntegral_and_topologicalKrullDim_exceptional_blowUpSpec
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    AlgebraicGeometry.IsIntegral
        ((((Stacks.Blowup.residuePoint A).ker).comap
          (Stacks.Blowup.toSpec (IsLocalRing.maximalIdeal A))).subscheme) ∧
      topologicalKrullDim
          ((((Stacks.Blowup.residuePoint A).ker).comap
            (Stacks.Blowup.toSpec (IsLocalRing.maximalIdeal A))).subscheme : Type u) = 1 := by
  have : (IsLocalRing.maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  let _ : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  obtain ⟨x, hspan⟩ := Stacks.Blowup.exists_range_eq_maximalIdeal A hdim
  have hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal A := fun i ↦ by
    rw [hspan]; exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨ρ, -⟩ := Stacks.Blowup.exists_iso_exceptional_projectiveLine A hdim x hx hspan
  rw [Stacks.Blowup.ker_residuePoint]
  refine ⟨?_, ?_⟩
  · have : AlgebraicGeometry.IsIntegral
        (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (A ⧸ IsLocalRing.maximalIdeal A))) :=
      Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj _ 1
    exact IsIntegral.of_isIso ρ.inv
  · rw [IsHomeomorph.topologicalKrullDim_eq ρ.hom (Scheme.homeoOfIso ρ).isHomeomorph]
    simpa using Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin
      (A ⧸ IsLocalRing.maximalIdeal A) (r := 2) two_pos

/-- The affine blowup of a two-dimensional regular local ring in its maximal ideal is identified,
over `Spec A`, with the blowup of the ideal sheaf of the closed point, and the two exceptional
ideal sheaves correspond under that identification. -/
private theorem exists_iso_blowUpSpec_comap_exceptionalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A]
    (ℐ : (Spec (CommRingCat.of A)).IdealSheafData)
    (hℐ : ℐ = (Stacks.Blowup.residuePoint A).ker) :
    ∃ ψ : Stacks.Blowup.blowUpSpec (IsLocalRing.maximalIdeal A) ≅ blowUp ℐ,
      (exceptionalIdeal ℐ).comap ψ.hom =
        ℐ.comap (Stacks.Blowup.toSpec (IsLocalRing.maximalIdeal A)) := by
  have hℐ' : ℐ = Scheme.IdealSheafData.ofIdealTop (Ideal.map
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (IsLocalRing.maximalIdeal A)) :=
    hℐ.trans (ker_residuePoint_eq_ofIdealTop_map A)
  subst hℐ'
  obtain ⟨φ⟩ := Stacks.Blowup.nonempty_over_iso_blowUpToBase A (IsLocalRing.maximalIdeal A)
  have hw : φ.hom.left ≫ blowUpToBase (Scheme.IdealSheafData.ofIdealTop (Ideal.map
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (IsLocalRing.maximalIdeal A))) =
      Stacks.Blowup.toSpec (IsLocalRing.maximalIdeal A) := Over.w φ.hom
  refine ⟨(Over.forget _).mapIso φ, ?_⟩
  show (exceptionalIdeal _).comap φ.hom.left = _
  rw [show exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop (Ideal.map
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (IsLocalRing.maximalIdeal A))) =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.map
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (IsLocalRing.maximalIdeal A))).comap
          (blowUpToBase _) from rfl,
    ← Scheme.IdealSheafData.comap_comp, hw]

/-! ### The three properties of the exceptional divisor -/

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]
  (ℐ : (Spec (CommRingCat.of A)).IdealSheafData)

/-- The affine blowup of a regular local surface is identified with `blowUp ℐ` in such a way that
the pullback of the exceptional ideal sheaf is an integral subscheme. -/
private theorem exists_iso_blowUpSpec_isIntegral_comap_exceptionalIdeal (hdim : ringKrullDim A = 2)
    (hℐ : ℐ = (Stacks.Blowup.residuePoint A).ker) :
    ∃ ψ : Stacks.Blowup.blowUpSpec (IsLocalRing.maximalIdeal A) ≅ blowUp ℐ,
      AlgebraicGeometry.IsIntegral ((exceptionalIdeal ℐ).comap ψ.hom).subscheme := by
  obtain ⟨ψ, hψ⟩ := exists_iso_blowUpSpec_comap_exceptionalIdeal A ℐ hℐ
  have hint := (isIntegral_and_topologicalKrullDim_exceptional_blowUpSpec A hdim).1
  rw [← hℐ] at hint
  exact ⟨ψ, hψ ▸ hint⟩

/-- **The exceptional ideal sheaf of the blowup of a regular local surface at its closed point is
radical.** -/
public theorem radical_exceptionalIdeal_eq_self (hdim : ringKrullDim A = 2)
    (hℐ : ℐ = (Stacks.Blowup.residuePoint A).ker) :
    (exceptionalIdeal ℐ).radical = exceptionalIdeal ℐ := by
  obtain ⟨ψ, this⟩ := exists_iso_blowUpSpec_isIntegral_comap_exceptionalIdeal A ℐ hdim hℐ
  have hrad : ((exceptionalIdeal ℐ).comap ψ.hom).radical = (exceptionalIdeal ℐ).comap ψ.hom :=
    Stacks.Models.radical_eq_self_of_isReduced_subscheme _
  have hback : ∀ K : (blowUp ℐ).IdealSheafData, (K.comap ψ.hom).comap ψ.inv = K := fun K => by
    rw [← Scheme.IdealSheafData.comap_comp, ψ.inv_hom_id, Scheme.IdealSheafData.comap_id]
  conv_lhs => rw [← hback (exceptionalIdeal ℐ).radical]
  rw [← radical_comap_open (exceptionalIdeal ℐ) ψ.hom, hrad, hback]

/-- **The support of the exceptional divisor of the blowup of a regular local surface at its
closed point is irreducible.** -/
public theorem isIrreducible_support_exceptionalIdeal (hdim : ringKrullDim A = 2)
    (hℐ : ℐ = (Stacks.Blowup.residuePoint A).ker) :
    IsIrreducible ((exceptionalIdeal ℐ).support : Set (blowUp ℐ)) := by
  obtain ⟨ψ, this⟩ := exists_iso_blowUpSpec_isIntegral_comap_exceptionalIdeal A ℐ hdim hℐ
  have hIbot : ℐ ≠ ⊥ := hℐ ▸ ker_residuePoint_ne_bot A hdim
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : AlgebraicGeometry.IsIntegral (blowUp ℐ) := isIntegral_blowUp ℐ hIbot
  have : AlgebraicGeometry.IsIntegral
      (Stacks.Blowup.blowUpSpec (IsLocalRing.maximalIdeal A)) := IsIntegral.of_isIso ψ.inv
  have hirr : IsIrreducible (((exceptionalIdeal ℐ).comap ψ.hom).support :
      Set (Stacks.Blowup.blowUpSpec (IsLocalRing.maximalIdeal A))) :=
    Stacks.Divisors.isIrreducible_support_of_isIntegral_subscheme _
  have hpre : (((exceptionalIdeal ℐ).comap ψ.hom).support :
      Set (Stacks.Blowup.blowUpSpec (IsLocalRing.maximalIdeal A))) =
      Scheme.homeoOfIso ψ ⁻¹' ((exceptionalIdeal ℐ).support : Set (blowUp ℐ)) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have := hirr.image _ (Scheme.homeoOfIso ψ).continuous.continuousOn
  rwa [hpre, Homeomorph.image_preimage] at this

/-! ### The finite-support assertion of Tag 0AGT for a regular local surface -/

/-- **The residual ideal after dividing out the exceptional divisor to its maximal order has
finite closed support.** Let `X` be the blowup of a regular local ring of dimension two at its
closed point, with exceptional divisor `E`, let `J` be a sheaf of ideals supported inside `E` and
let `d` be the largest exponent with `J ≤ E ^ d`. Then `J = E ^ d · J'` for a sheaf of ideals `J'`
whose support is a finite set of closed points. -/
public theorem exists_finite_isClosed_support_of_maximal_order_blowUp
    (hdim : ringKrullDim A = 2)
    (hℐ : ℐ = (Stacks.Blowup.residuePoint A).ker)
    (J : (blowUp ℐ).IdealSheafData)
    (hJE : (J.support : Set (blowUp ℐ)) ⊆ ((exceptionalIdeal ℐ).support : Set (blowUp ℐ)))
    (d : ℕ) (hJd : J ≤ exceptionalIdeal ℐ ^ d)
    (hmax : ∀ e : ℕ, J ≤ exceptionalIdeal ℐ ^ e → e ≤ d) :
    ∃ (J' : (blowUp ℐ).IdealSheafData) (T : Finset (blowUp ℐ)),
      exceptionalIdeal ℐ ^ d * J' = J ∧
      (J'.support : Set (blowUp ℐ)) = (T : Set (blowUp ℐ)) ∧
      ∀ x ∈ T, IsClosed ({x} : Set (blowUp ℐ)) :=
  have : AlgebraicGeometry.IsNoetherian (blowUp ℐ) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp ℐ
  Stacks.Blowup.Colength.exists_finite_isClosed_support_of_maximal_order (exceptionalIdeal ℐ) J
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal ℐ)
    (radical_exceptionalIdeal_eq_self A ℐ hdim hℐ)
    (isIrreducible_support_exceptionalIdeal A ℐ hdim hℐ)
    (le_of_eq (by
      have : IsDomain A := IsRegularLocalRing.isDomain A
      subst hℐ
      rw [← Stacks.Chow.topologicalKrullDim_subscheme]
      exact topologicalKrullDim_exceptionalDivisor_residuePoint A hdim)) hJE d hJd hmax

end AlgebraicGeometry

end
