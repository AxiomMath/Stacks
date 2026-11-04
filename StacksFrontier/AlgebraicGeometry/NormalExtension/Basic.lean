module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.Serre.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension of rational functions over codimension at least two

Let `X` be a normal integral locally Noetherian scheme and let `g` be an element of its function
field.  If `g` lies in the local ring of `X` at every point of codimension one — equivalently, if
its order of vanishing there is nonnegative — then `g` is a global section of `X`.  A rational
function on a normal scheme with no pole along a prime divisor has no pole at all.

The argument is the one of the source.  On an affine open `U = Spec B` the ring `B` is a Noetherian
normal domain whose fraction field is the function field of `X`, and the points of `U` of
codimension one are exactly the primes of `B` of height one, so `g` lies in `B` because a
Noetherian normal domain is the intersection of its localizations at the height-one primes.  The
sections so obtained over an affine cover agree on overlaps: the generic point lies in every
nonempty open of an irreducible space, and a section of an integral scheme is determined by its
germ there.  So they glue.

Normality is taken in the form the source uses — the ring of sections on every affine open is a
normal domain.  The order-of-vanishing form of the hypothesis needs in addition that the local ring
at a codimension-one point is a discrete valuation ring, which is `isDiscreteValuationRing_stalk`
below.

## Main results

* `IsIntegrallyClosed.exists_algebraMap_eq_of_forall_mem_localization`: the ring-theoretic core.
  An element of the fraction field of a Noetherian normal domain lying in every localization at a
  height-one prime lies in the ring.
* `AlgebraicGeometry.IsAffineOpen.exists_germ_eq_of_forall_coheight_eq_one`: the statement over one
  affine open.
* `AlgebraicGeometry.exists_germ_top_eq_of_forall_coheight_eq_one`: the global statement, with the
  hypothesis as membership in the local rings.
* `AlgebraicGeometry.isDiscreteValuationRing_stalk`: the local ring of a normal locally Noetherian
  integral scheme at a point of codimension one is a discrete valuation ring.
* `AlgebraicGeometry.exists_germ_top_eq_of_forall_zero_le_ord`: the global statement, with the
  hypothesis as nonnegativity of the order of vanishing.

## References

* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T), the ring-theoretic input
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD), the local rings
* [Stacks Project, Tag 04L4](https://stacks.math.columbia.edu/tag/04L4), where this step is used
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Order WithZero

universe u

/-- An element of the fraction field of a Noetherian normal domain which lies in the localization
at every prime of height one lies in the ring itself.

This is item (2) of Stacks Tag 031T, read as a membership statement. -/
theorem IsIntegrallyClosed.exists_algebraMap_eq_of_forall_mem_localization {R : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (x : K)
    (h : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      x ∈ Localization.subalgebra.ofField K p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors) :
    ∃ r : R, algebraMap R K r = x :=
  Algebra.mem_bot.mp <| by
    rw [← (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot (R := R) K).2.1]
    exact Algebra.mem_iInf.mpr fun p => Algebra.mem_iInf.mpr fun hp => h p hp

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
/-- Every point of a scheme lies in an affine open. -/
private theorem exists_isAffineOpen_mem (z : X) : ∃ U : X.Opens, IsAffineOpen U ∧ z ∈ U := by
  have hz : z ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hz
  exact ⟨W, W.2, hW⟩

/-- The generic point of an irreducible space lies in every nonempty open. -/
private theorem genericPoint_mem_of_nonempty (W : X.Opens) (hW : (W : Set X).Nonempty) :
    genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using hW)

/-- On an affine open with normal ring of sections, an element of the function field which lies in
the local ring at every point of codimension one is the germ at the generic point of a section. -/
theorem IsAffineOpen.exists_germ_eq_of_forall_coheight_eq_one [IsLocallyNoetherian X]
    {U : X.Opens} (hU : IsAffineOpen U) (hgen : genericPoint X ∈ U)
    (hnorm : IsIntegrallyClosed Γ(X, U)) (g : X.functionField)
    (h : ∀ z : X, z ∈ U → coheight z = 1 →
      ∃ t : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField t = g) :
    ∃ s : Γ(X, U), X.presheaf.germ U (genericPoint X) hgen s = g := by
  have hne : Nonempty U := ⟨⟨genericPoint X, hgen⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  have key : ∀ p : PrimeSpectrum Γ(X, U), p.asIdeal.height = 1 →
      g ∈ Localization.subalgebra.ofField X.functionField p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors := by
    intro p hp
    set q : ↥(Spec Γ(X, U)) := p with hq
    have hz : hU.fromSpec.base q ∈ U := hU.range_fromSpec.le (Set.mem_range_self q)
    have hch : coheight (hU.fromSpec.base q) = 1 := by
      rw [coheight_eq_of_isOpenImmersion hU.fromSpec (x := q),
        ← idealHeight_eq_coheight Γ(X, U) q, hq, hp]
    obtain ⟨t, ht⟩ := h _ hz hch
    let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base q)) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec.base q, hz⟩
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec.base q)) q.asIdeal :=
      hU.isLocalization_stalk' q hz
    have htower : IsScalarTower Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base q))
        X.functionField := functionField_isScalarTower X U ⟨hU.fromSpec.base q, hz⟩
    obtain ⟨a, ⟨s, hs⟩, hast⟩ := IsLocalization.exists_mk'_eq q.asIdeal.primeCompl t
    have hs0 : algebraMap Γ(X, U) X.functionField s ≠ 0 := by
      have hsne : (s : Γ(X, U)) ≠ 0 := fun hz0 => hs (hz0 ▸ q.asIdeal.zero_mem)
      simpa using hsne
    refine ⟨a, s, hs, ?_⟩
    rw [eq_mul_inv_iff_mul_eq₀ hs0, ← ht, ← hast,
      IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base q))
        X.functionField, ← map_mul, IsLocalization.mk'_spec]
    exact (IsScalarTower.algebraMap_apply Γ(X, U)
      (X.presheaf.stalk (hU.fromSpec.base q)) X.functionField a).symm
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_mem_localization
    (R := Γ(X, U)) (K := X.functionField) g key
  exact ⟨r, by simpa [RingHom.algebraMap_toAlgebra] using hr⟩

/-- **Algebraic Hartogs.** On a normal integral locally Noetherian scheme, an element of the
function field which lies in the local ring at every point of codimension one is the germ at the
generic point of a global section.

Normality is the hypothesis that the ring of sections on every affine open is integrally closed. -/
theorem exists_germ_top_eq_of_forall_coheight_eq_one [IsLocallyNoetherian X]
    (hnorm : ∀ U : X.affineOpens, IsIntegrallyClosed Γ(X, U.1)) (g : X.functionField)
    (h : ∀ z : X, coheight z = 1 →
      ∃ t : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField t = g) :
    ∃ s : Γ(X, ⊤), X.presheaf.germ ⊤ (genericPoint X) trivial s = g := by
  classical
  set ι := {U : X.affineOpens // genericPoint X ∈ (U.1 : X.Opens)}
  set V : ι → X.Opens := fun i => (i.1.1 : X.Opens)
  have hsec : ∀ i : ι, ∃ s : Γ(X, V i), X.presheaf.germ (V i) (genericPoint X) i.2 s = g :=
    fun i => i.1.2.exists_germ_eq_of_forall_coheight_eq_one i.2 (hnorm i.1) g
      fun z _ hzc => h z hzc
  choose sf hsf using hsec
  have hi : ∀ x : X, ∃ i : ι, x ∈ V i := fun x => by
    obtain ⟨W, hWa, hxW⟩ := exists_isAffineOpen_mem x
    exact ⟨⟨⟨W, hWa⟩, genericPoint_mem_of_nonempty W ⟨x, hxW⟩⟩, hxW⟩
  have hcover : (⊤ : X.Opens) ≤ iSup V := fun x _ => Opens.mem_iSup.mpr (hi x)
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro i j
    have hij : genericPoint X ∈ V i ⊓ V j := ⟨i.2, j.2⟩
    refine germ_injective_of_isIntegral X (U := V i ⊓ V j) (genericPoint X) hij ?_
    rw [X.presheaf.germ_res_apply (Opens.infLELeft (V i) (V j)) _ hij,
      X.presheaf.germ_res_apply (Opens.infLERight (V i) (V j)) _ hij, hsf i, hsf j]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V ⊤ (fun _ => homOfLE le_top) hcover sf hcompat
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨i, -⟩ := hi x
  exact ⟨s, by rw [← hsf i, ← hs i]; exact (X.presheaf.germ_res_apply _ _ _ s).symm⟩

/-- **Stacks Project, Tag 00PD** applied to a scheme. The local ring of a normal locally Noetherian
integral scheme at a point of codimension one is a discrete valuation ring. -/
@[sga "3 X 8.4" "partial"]
theorem isDiscreteValuationRing_stalk [IsLocallyNoetherian X]
    (hnorm : ∀ U : X.affineOpens, IsIntegrallyClosed Γ(X, U.1)) {z : X} (hz : coheight z = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk z) := by
  obtain ⟨U, hU, hzU⟩ := exists_isAffineOpen_mem z
  have hne : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  have : IsIntegrallyClosed Γ(X, U) := hnorm ⟨U, hU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  have hic : IsIntegrallyClosed (X.presheaf.stalk z) :=
    isIntegrallyClosed_of_isLocalization (X.presheaf.stalk z)
      (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
      (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl_le_nonZeroDivisors
  have hnoeth : IsNoetherianRing (X.presheaf.stalk z) :=
    IsLocalization.isNoetherianRing (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
      (X.presheaf.stalk z) ‹_›
  have hdim : ringKrullDim (X.presheaf.stalk z) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight z, hz]
    rfl
  have hpack : IsNoetherianRing (X.presheaf.stalk z) ∧ IsLocalRing (X.presheaf.stalk z) ∧
      IsDomain (X.presheaf.stalk z) ∧ IsIntegrallyClosed (X.presheaf.stalk z) ∧
      ringKrullDim (X.presheaf.stalk z) = 1 :=
    ⟨hnoeth, inferInstance, inferInstance, hic, hdim⟩
  obtain ⟨_, hdvr⟩ := ((isDiscreteValuationRing_tfae (X.presheaf.stalk z)).out 5 1).mp hpack
  exact hdvr

/-- At a point of codimension one whose local ring is a discrete valuation ring, a nonzero element
of the function field with nonnegative order of vanishing lies in that local ring. -/
theorem exists_algebraMap_eq_of_zero_le_ord [IsLocallyNoetherian X] {z : X}
    (hz : coheight z = 1) [IsDiscreteValuationRing (X.presheaf.stalk z)]
    {g : X.functionField} (hg : g ≠ 0) (hord : 0 ≤ X.ord g z) :
    ∃ t : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField t = g := by
  have h1 : (((Multiplicative.ofAdd (0 : ℤ)) : Multiplicative ℤ) : ℤᵐ⁰) ≤ X.ordHom z hz g :=
    (Scheme.le_ord_iff hz hg).mp hord
  have hkd : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have h2 : X.ordHom z hz g = Ring.ordFrac (X.presheaf.stalk z) g := rfl
  rw [h2, Ring.ordFrac_eq_valuation_inv] at h1
  have hv0 : (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk z)).valuation
      X.functionField g ≠ 0 := by simpa using hg
  have h3 : (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk z)).valuation
      X.functionField g ≤ 1 :=
    (one_le_inv₀ (lt_of_le_of_ne zero_le hv0.symm)).mp (by simpa using h1)
  exact IsDiscreteValuationRing.exists_lift_of_le_one h3

/-- **Algebraic Hartogs, order-of-vanishing form.** On a normal integral locally Noetherian scheme,
a nonzero element of the function field whose order of vanishing at every point of codimension one
is nonnegative is the germ at the generic point of a global section. -/
theorem exists_germ_top_eq_of_forall_zero_le_ord [IsLocallyNoetherian X]
    (hnorm : ∀ U : X.affineOpens, IsIntegrallyClosed Γ(X, U.1)) {g : X.functionField}
    (hg : g ≠ 0) (h : ∀ z : X, coheight z = 1 → 0 ≤ X.ord g z) :
    ∃ s : Γ(X, ⊤), X.presheaf.germ ⊤ (genericPoint X) trivial s = g :=
  exists_germ_top_eq_of_forall_coheight_eq_one hnorm g fun z hzc => by
    have := isDiscreteValuationRing_stalk hnorm hzc
    exact exists_algebraMap_eq_of_zero_le_ord hzc hg (h z hzc)

end AlgebraicGeometry
