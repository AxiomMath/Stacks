module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.AffineAlgEquiv
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeNormal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.SemilocalDedekind
public import StacksFrontier.RingTheory.DedekindDomain.FiniteProductDimensionOne

/-!
# The normalization of a one-dimensional locally Noetherian scheme

Let `X` be a locally Noetherian scheme of dimension at most one. Over an affine open
`U = Spec A` of `X` the normalization of `X` is the spectrum of the integral closure of `A` in
the product of the residue fields of the minimal primes of `A`, and that integral closure is a
finite product of Dedekind domains, by Krull–Akizuki. Consequently the normalization is locally
Noetherian, again of dimension at most one, and *every* affine open of it, not only one of the
form `ν⁻¹(U)`, has a finite product of Dedekind domains for its ring of sections.

## Main results

* `AlgebraicGeometry.isFiniteProductOfDedekindDomains_sections_preimage_normalization`: the
  sections of the normalization over the preimage of an affine open.
* `AlgebraicGeometry.isLocallyNoetherian_normalizationScheme`: the normalization of a
  one-dimensional locally Noetherian scheme is locally Noetherian.
* `AlgebraicGeometry.topologicalKrullDim_normalizationScheme_le_one`: it again has dimension at
  most one.
* `AlgebraicGeometry.isFiniteProductOfDedekindDomains_sections_normalizationScheme`: every
  affine open of it is the spectrum of a finite product of Dedekind domains.

## Implementation notes

The last result does not follow from the first by restriction, because an affine open of the
normalization need not be contained in the preimage of an affine open of `X`. It is instead
deduced from the normality of the normalization through tag 030C, in the form
`Stacks.isFiniteProductOfDedekindDomains_of_isNormalRing`: the ring of sections is Noetherian
because the normalization is locally Noetherian, it is normal because the normalization is, and
it has dimension at most one because the normalization does.

The dimension hypothesis is `topologicalKrullDim X ≤ 1` rather than an equality, because that is
all the arguments use; the degenerate case of the empty affine open, where the sections are the
zero ring, is covered by the empty product of Dedekind domains.

## References

* [Stacks Project, Tag 0C45](https://stacks.math.columbia.edu/tag/0C45)
* [Stacks Project, Tag 09IG](https://stacks.math.columbia.edu/tag/09IG)
* [Stacks Project, Tag 030C](https://stacks.math.columbia.edu/tag/030C)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.NormalizationStalkAmbient

universe u

namespace AlgebraicGeometry

/-! ### Dimension of an affine open -/

/-- The dimension of an affine open is the Krull dimension of its ring of sections. -/
private theorem topologicalKrullDim_coe_eq_ringKrullDim {Y : Scheme.{u}} (W : Y.Opens)
    (hW : IsAffineOpen W) :
    topologicalKrullDim (W : Set Y) = ringKrullDim Γ(Y, W) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ hW.isoSpec.hom.homeomorph.isHomeomorph

/-- On a scheme of dimension at most one the ring of sections of an affine open has Krull
dimension at most one. -/
theorem krullDimLE_one_sections_of_isAffineOpen {Y : Scheme.{u}}
    (hdim : topologicalKrullDim Y ≤ 1) (W : Y.Opens) (hW : IsAffineOpen W) :
    Ring.KrullDimLE 1 Γ(Y, W) := by
  refine Ring.krullDimLE_iff.mpr ?_
  rw [← topologicalKrullDim_coe_eq_ringKrullDim W hW]
  exact (topologicalKrullDim_subspace_le Y (W : Set Y)).trans hdim

/-! ### The sections of the normalization over the preimage of an affine open -/

/-- **The sections of the normalization over the preimage of an affine open form a finite
product of Dedekind domains.** They are the integral closure of `Γ(X, U)` in the product of the
residue fields of its minimal primes, and Krull–Akizuki computes that integral closure. -/
theorem isFiniteProductOfDedekindDomains_sections_preimage_normalization {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Stacks.IsFiniteProductOfDedekindDomains
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Ring.KrullDimLE 1 Γ(X, U) := krullDimLE_one_sections_of_isAffineOpen hdim U hU
  let : Algebra Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
    (minimalPrimeResidueFieldProductHom Γ(X, U)).toAlgebra
  let : Algebra Γ(X, U)
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) :=
    ((Scheme.normalization X hfin).app U).hom.toAlgebra
  have e₁ := normalizationSectionsAlgEquivIntegralClosureMinimalPrimeResidueFields hfin U hU
  rcases subsingleton_or_nontrivial Γ(X, U) with hsub | hnt
  · -- The empty affine open: both rings are zero.
    have hempty : IsEmpty (minimalPrimes Γ(X, U)) := by
      refine ⟨fun p => ?_⟩
      have hp : (p : Ideal Γ(X, U)).IsPrime := p.2.1.1
      have h1 : (1 : Γ(X, U)) ∈ (p : Ideal Γ(X, U)) := by
        rw [Subsingleton.elim (1 : Γ(X, U)) 0]
        exact Ideal.zero_mem _
      exact hp.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have : Subsingleton (minimalPrimeResidueFieldProduct Γ(X, U)) := inferInstance
    have : Subsingleton (integralClosure Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U))) :=
      Subtype.val_injective.subsingleton
    have : Subsingleton
        Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) :=
      e₁.toEquiv.subsingleton
    exact Stacks.isFiniteProductOfDedekindDomains_of_subsingleton _
  · obtain ⟨n, D, hcr, hded, -, ⟨e₂⟩⟩ :=
      isFiniteProductOfDedekindDomains_integralClosure_minimalPrimeResidueFieldProduct Γ(X, U)
    exact ⟨n, D, hcr, hded, ⟨e₁.toRingEquiv.trans e₂⟩⟩

/-! ### The normalization is locally Noetherian of dimension at most one -/

/-- The preimages of the affine opens of `X` cover the normalization. -/
private def normalizationAffineCover (X : Scheme.{u})
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    (Scheme.normalizationScheme X hfin).OpenCover where
  I₀ := X.affineOpens
  X U := (Scheme.normalization X hfin ⁻¹ᵁ (U : X.Opens)).toScheme
  f U := (Scheme.normalization X hfin ⁻¹ᵁ (U : X.Opens)).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun y => ?_, fun _ => inferInstance⟩
    obtain ⟨-, ⟨U, hU, rfl⟩, hyU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (Scheme.normalization X hfin y)) isOpen_univ
    exact ⟨⟨U, hU⟩, ⟨⟨y, hyU⟩, rfl⟩⟩

/-- **The normalization of a one-dimensional locally Noetherian scheme is locally
Noetherian.** Over the preimage of an affine open its sections are a finite product of Dedekind
domains, hence Noetherian, and those preimages cover it. -/
theorem isLocallyNoetherian_normalizationScheme {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    IsLocallyNoetherian (Scheme.normalizationScheme X hfin) := by
  have haff : ∀ U : X.affineOpens, IsAffine ((normalizationAffineCover X hfin).X U) := fun U =>
    U.2.preimage (Scheme.normalization X hfin)
  refine (@isLocallyNoetherian_iff_of_affine_openCover _
    (normalizationAffineCover X hfin) haff).mpr ?_
  change ∀ U : X.affineOpens, IsNoetherianRing
    Γ((Scheme.normalization X hfin ⁻¹ᵁ (U : X.Opens)).toScheme, ⊤)
  intro U
  have hprod := isFiniteProductOfDedekindDomains_sections_preimage_normalization hdim hfin
    (U : X.Opens) U.2
  have : IsNoetherianRing
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ (U : X.Opens)) :=
    hprod.isNoetherianRing
  exact isNoetherianRing_of_ringEquiv _
    ((Scheme.Opens.topIso
      (Scheme.normalization X hfin ⁻¹ᵁ (U : X.Opens))).symm).commRingCatIsoToRingEquiv

/-- **The normalization of a scheme of dimension at most one again has dimension at most one**:
the normalization morphism is integral. -/
theorem topologicalKrullDim_normalizationScheme_le_one {X : Scheme.{u}}
    (hdim : topologicalKrullDim X ≤ 1)
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    topologicalKrullDim (Scheme.normalizationScheme X hfin) ≤ 1 := by
  have : IsIntegralHom (Scheme.normalization X hfin) :=
    Scheme.isIntegralHom_normalization X hfin
  exact (topologicalKrullDim_le_of_isIntegralHom (Scheme.normalization X hfin)).trans hdim

/-! ### Every affine open of the normalization -/

/-- **Every affine open of the normalization of a one-dimensional locally Noetherian scheme is
the spectrum of a finite product of Dedekind domains.** Its ring of sections is Noetherian,
normal and of dimension at most one, so tag 030C splits it into the product of the quotients by
its minimal primes, each of which is a Dedekind domain. -/
theorem isFiniteProductOfDedekindDomains_sections_normalizationScheme {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (W : (Scheme.normalizationScheme X hfin).Opens) (hW : IsAffineOpen W) :
    Stacks.IsFiniteProductOfDedekindDomains Γ(Scheme.normalizationScheme X hfin, W) := by
  have : IsLocallyNoetherian (Scheme.normalizationScheme X hfin) :=
    isLocallyNoetherian_normalizationScheme hdim hfin
  have : IsNoetherianRing Γ(Scheme.normalizationScheme X hfin, W) :=
    IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hN : IsNormal (Scheme.normalizationScheme X hfin) :=
    Scheme.isNormal_normalizationScheme X hfin
  have htfae : IsNormal (Scheme.normalizationScheme X hfin) ↔
      ∀ V : (Scheme.normalizationScheme X hfin).affineOpens,
        IsNormalRing Γ(Scheme.normalizationScheme X hfin, (V : _)) :=
    (isNormal_tfae (Scheme.normalizationScheme X hfin)).out 1 2
  have hnormal : IsNormalRing Γ(Scheme.normalizationScheme X hfin, W) :=
    htfae.mp hN ⟨W, hW⟩
  exact Stacks.isFiniteProductOfDedekindDomains_of_isNormalRing
    (krullDimLE_one_sections_of_isAffineOpen
      (topologicalKrullDim_normalizationScheme_le_one hdim hfin) W hW) hnormal

end AlgebraicGeometry

end
