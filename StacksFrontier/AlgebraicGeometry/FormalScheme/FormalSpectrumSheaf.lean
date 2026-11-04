module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalScheme.PseudoDiscreteSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf of a formal spectrum

The structure presheaf `𝒪_{Spf A} = lim 𝒪_λ` of the formal spectrum of a pre-admissible
topological ring is a sheaf of topological rings, so the formal spectrum is a sheafed space of
topological rings. The space `Spf A` of open primes is the zero locus of any ideal of definition,
hence a quasi-compact space with a basis of quasi-compact opens; on such a space
pseudo-discretisation preserves the sheaf condition, and a limit of sheaves is a sheaf.

## Main definitions

* `AlgebraicGeometry.spfSheafedSpace`: the formal spectrum `(Spf A, 𝒪_{Spf A})` as a sheafed
  space of topological rings.

## Main results

* `AlgebraicGeometry.openPrimes_eq_zeroLocus_of_isWeakIdealOfDefinition`,
  `AlgebraicGeometry.isClosed_openPrimes` and
  `AlgebraicGeometry.prespectralSpace_spfSpace_of_isWeaklyPreAdmissible`: the open primes of `A`
  are the zero locus of any ideal of definition, a closed subset of `Spec A`, so `Spf A` is
  quasi-compact and its quasi-compact opens form a basis.
* `AlgebraicGeometry.isSheaf_spfComponentOn`: each `𝒪_λ`, the structure sheaf of
  `Spec (A/I_λ)` viewed on `Spf A`, is a sheaf of rings.
* `AlgebraicGeometry.isSheaf_spfPresheaf`: `𝒪_{Spf A}` is a sheaf of topological rings.

## Implementation notes

Only pre-admissibility — the existence of a single ideal of definition — is used: completeness
of `A` enters the source's remaining deferred verifications, namely that the stalks of
`𝒪_{Spf A}` are local rings and that `Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}}`, not this one.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace AlgebraicGeometry

open TopologicalRing

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-! ### The space of open primes -/

/-- The open primes of `A` are the zero locus of any weak ideal of definition: a prime is open
exactly when it contains that ideal. -/
@[ega "0 7.1.5" "more general"]
theorem openPrimes_eq_zeroLocus_of_isWeakIdealOfDefinition {I : Ideal A}
    (hI : IsWeakIdealOfDefinition I) :
    openPrimes A = PrimeSpectrum.zeroLocus (I : Set A) := by
  ext p
  rw [PrimeSpectrum.mem_zeroLocus]
  exact (mem_openPrimes_iff_le_of_isWeakIdealOfDefinition A hI p).trans SetLike.coe_subset_coe.symm

/-- The open primes of `A` are the zero locus of any ideal of definition: a prime is open
exactly when it contains that ideal.

The ideals-of-definition case of `openPrimes_eq_zeroLocus_of_isWeakIdealOfDefinition`. -/
@[ega "0 7.1.5" "more general"]
theorem openPrimes_eq_zeroLocus {I : Ideal A} (hI : IsIdealOfDefinition I) :
    openPrimes A = PrimeSpectrum.zeroLocus (I : Set A) :=
  openPrimes_eq_zeroLocus_of_isWeakIdealOfDefinition A
    (isWeakIdealOfDefinition_of_isIdealOfDefinition hI)

/-- The open primes of a weakly pre-admissible topological ring form a closed subset of
`Spec A`. -/
theorem isClosed_openPrimes_of_isWeaklyPreAdmissible (hA : IsWeaklyPreAdmissible A) :
    IsClosed (openPrimes A) := by
  obtain ⟨I, hI⟩ := hA
  rw [openPrimes_eq_zeroLocus_of_isWeakIdealOfDefinition A hI]
  exact PrimeSpectrum.isClosed_zeroLocus _

/-- The open primes of a pre-admissible topological ring form a closed subset of `Spec A`. -/
theorem isClosed_openPrimes (hA : IsPreAdmissible A) : IsClosed (openPrimes A) :=
  isClosed_openPrimes_of_isWeaklyPreAdmissible A (isWeaklyPreAdmissible_of_isPreAdmissible hA)

/-- The formal spectrum of a weakly pre-admissible topological ring is quasi-compact, being a
closed subspace of `Spec A`. -/
theorem compactSpace_spfSpace_of_isWeaklyPreAdmissible (hA : IsWeaklyPreAdmissible A) :
    CompactSpace (spfSpace A) :=
  isCompact_iff_compactSpace.1
    ((isClosed_openPrimes_of_isWeaklyPreAdmissible A hA).isCompact)

/-- The formal spectrum of a pre-admissible topological ring is quasi-compact, being a closed
subspace of `Spec A`.

The ideals-of-definition case of `compactSpace_spfSpace_of_isWeaklyPreAdmissible`. -/
theorem compactSpace_spfSpace (hA : IsPreAdmissible A) : CompactSpace (spfSpace A) :=
  compactSpace_spfSpace_of_isWeaklyPreAdmissible (A := A)
    (hA := isWeaklyPreAdmissible_of_isPreAdmissible hA)

/-- The quasi-compact opens of the formal spectrum of a weakly pre-admissible topological ring
form a basis of its topology, because it is a subspace of `Spec A`, which has that property. -/
theorem prespectralSpace_spfSpace_of_isWeaklyPreAdmissible (hA : IsWeaklyPreAdmissible A) :
    PrespectralSpace (spfSpace A) :=
  PrespectralSpace.of_isClosedEmbedding Subtype.val
    (isClosed_openPrimes_of_isWeaklyPreAdmissible A hA).isClosedEmbedding_subtypeVal

/-- The quasi-compact opens of the formal spectrum of a pre-admissible topological ring form a
basis of its topology, because it is a subspace of `Spec A`, which has that property.

The ideals-of-definition case of `prespectralSpace_spfSpace_of_isWeaklyPreAdmissible`. -/
theorem prespectralSpace_spfSpace (hA : IsPreAdmissible A) : PrespectralSpace (spfSpace A) :=
  prespectralSpace_spfSpace_of_isWeaklyPreAdmissible (A := A)
    (hA := isWeaklyPreAdmissible_of_isPreAdmissible hA)

/-! ### The sheaf condition -/

/-- The structure sheaf of `Spec (A/I)`, viewed on `Spf A`, is a sheaf of rings: the pushforward
of a sheaf along a continuous map is a sheaf. -/
theorem isSheaf_spfComponentOn (I : SpfIndex A P) : (spfComponentOn A I).IsSheaf :=
  (Opens.map (spfOfQuotientOn A I)).op_comp_isSheaf _ _
    ⟨_, (Spec (spfQuotientOn A I)).IsSheaf⟩

/-- The structure sheaf of `Spec (A/I)`, viewed on `Spf A`, is a sheaf of rings: the pushforward
of a sheaf along a continuous map is a sheaf.

The ideals-of-definition case of `isSheaf_spfComponentOn`. -/
@[ega "I 10.1.1" "partial"]
theorem isSheaf_spfComponent (I : IdealsOfDefinition A) : (spfComponent A I).IsSheaf :=
  isSheaf_spfComponentOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- Each term `𝒪_λ` of the inverse system defining `𝒪_{Spf A}` is a sheaf of topological
rings. -/
@[ega "0 3.8.1" "special case", ega "I 10.1.1" "partial"]
theorem isSheaf_pseudoDiscrete_spfComponentOn (hA : IsWeaklyPreAdmissible A)
    (I : SpfIndex A P) : (pseudoDiscrete (spfComponentOn A I)).IsSheaf :=
  let := prespectralSpace_spfSpace_of_isWeaklyPreAdmissible A hA
  isSheaf_pseudoDiscrete_of_isSheaf _ (isSheaf_spfComponentOn A I)

/-- Each term `𝒪_λ` of the inverse system defining `𝒪_{Spf A}` is a sheaf of topological
rings.

The ideals-of-definition case of `isSheaf_pseudoDiscrete_spfComponentOn`. -/
@[ega "0 3.8.1" "special case", ega "I 10.1.1" "partial"]
theorem isSheaf_pseudoDiscrete_spfComponent (hA : IsPreAdmissible A)
    (I : IdealsOfDefinition A) : (pseudoDiscrete (spfComponent A I)).IsSheaf :=
  isSheaf_pseudoDiscrete_spfComponentOn (A := A) (P := IsIdealOfDefinition)
    (hA := isWeaklyPreAdmissible_of_isPreAdmissible hA) (I := I)

variable (P) in
/-- **Deferred by the source** ("At this point one should check several things"): the structure
presheaf `lim 𝒪_λ` of the formal spectrum taken along a weak ideal system is a sheaf of
topological rings, being a limit of sheaves. -/
@[ega "I 10.1.1" "partial"]
theorem isSheaf_spfPresheafOn (hA : IsWeaklyPreAdmissible A) : (spfPresheafOn A P).IsSheaf :=
  TopCat.limit_isSheaf _ fun I => isSheaf_pseudoDiscrete_spfComponentOn A hA I

/-- The structure presheaf `𝒪_{Spf A} = lim 𝒪_λ` of the formal spectrum of a pre-admissible
topological ring is a sheaf of topological rings. -/
@[ega "I 10.1.1" "partial"]
theorem isSheaf_spfPresheaf (hA : IsPreAdmissible A) : (spfPresheaf A).IsSheaf :=
  isSheaf_spfPresheafOn A IsIdealOfDefinition (isWeaklyPreAdmissible_of_isPreAdmissible hA)

variable (P) in
/-- The formal spectrum taken along a weak ideal system, as a sheafed space of topological
rings. -/
noncomputable def spfSheafedSpaceOn (hA : IsWeaklyPreAdmissible A) :
    SheafedSpace TopCommRingCat.{u} where
  carrier := spfSpace A
  presheaf := spfPresheafOn A P
  IsSheaf := isSheaf_spfPresheafOn A P hA

/-- The formal spectrum `(Spf A, 𝒪_{Spf A})` of a pre-admissible topological ring as a sheafed
space of topological rings. -/
@[reducible, ega "I 10.1.2"] noncomputable def spfSheafedSpace (hA : IsPreAdmissible A) :
    SheafedSpace TopCommRingCat.{u} :=
  spfSheafedSpaceOn A IsIdealOfDefinition (isWeaklyPreAdmissible_of_isPreAdmissible hA)

/-- The presheafed space underlying the sheafed space of the formal spectrum taken along a weak
ideal system is the formal spectrum taken along it. -/
@[simp]
theorem spfSheafedSpaceOn_toPresheafedSpace (hA : IsWeaklyPreAdmissible A) :
    (spfSheafedSpaceOn A P hA).toPresheafedSpace = SpfOn A P := rfl

/-- The presheafed space underlying the sheafed space of the formal spectrum is `Spf A`. -/
@[simp]
theorem spfSheafedSpace_toPresheafedSpace (hA : IsPreAdmissible A) :
    (spfSheafedSpace A hA).toPresheafedSpace = Spf A := rfl

end AlgebraicGeometry
