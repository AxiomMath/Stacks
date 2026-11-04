module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthTwoLocus
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceOneImmediateSpecialization
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumSpecialization

/-!
# The boundary flag at a point whose closed fibre avoids `Z`

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`, and let `A` be `I`-adically complete. Let `𝔭 ⊆ 𝔮` be
primes of `A` such that every prime above `𝔮` meeting `Y` already lies in `Z`, and suppose that
*no* irreducible component of the closed fibre `\overline{\{𝔭\}} ∩ Y` is contained in `Z`.

This file produces the flag of points that [Stacks, Tag 0EJ8] uses in exactly that case: a
point `z` of `Y` minimal over `𝔮 + I` and lying in `Z`, and an immediate generalization `y` of
`z` inside `Y`, lying over `𝔭` but outside `Z`.

## Main results

* `Stacks.Algebraization.exists_boundary_flag_of_no_component` — the flag.

## Implementation notes

`I`-adic completeness enters only through
`Stacks.Algebraization.exists_specializes_mem_range_Yι`: it puts `I` inside the Jacobson radical
of `A`, so every prime specializes into `Y`, which is what makes `𝔮 + I` a proper ideal and
gives the minimal prime `z` over it. The hypothesis on primes above `𝔮` then places `z` in `Z`.

The component `C` of the closed fibre through `z` is not contained in `Z` by hypothesis, so its
generic point `η` lies outside `Z`; since `Z` is closed and `η ⤳ z` with `z ∈ Z`, the points are
distinct, and [Stacks, Tag 02IM] — in the form
`AlgebraicGeometry.exists_isImmediateSpecialization_mem_of_isLocallyClosed` applied to the
locally closed set `(\overline{\{𝔭\}} ∩ Y) ∖ Z` — produces `y`. Membership of `y` in the closed
fibre is what gives `𝔭 ≤ 𝔭_y`, so no separate specialization argument is needed.

## References

* [Stacks Project, Tag 0EJ8](https://stacks.math.columbia.edu/tag/0EJ8)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 02IM](https://stacks.math.columbia.edu/tag/02IM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Algebraization

/-- The range of `Y ⟶ X` is the zero locus of `I`. -/
public theorem range_Yι_base (S : AlgebraizationSituation.{u}) :
    Set.range S.Yι.base = PrimeSpectrum.zeroLocus (S.I : Set S.A) := by
  have h := _root_.range_comap_of_surjective (S.A ⧸ S.I) (Ideal.Quotient.mk S.I)
    Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at h
  exact h

/-- The range of `Z ⟶ X` is the zero locus of `𝔞`. -/
public theorem range_Zι_base (S : AlgebraizationSituation.{u}) :
    Set.range S.Zι.base = PrimeSpectrum.zeroLocus (S.a : Set S.A) := by
  have h := _root_.range_comap_of_surjective (S.A ⧸ S.a) (Ideal.Quotient.mk S.a)
    Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at h
  exact h

/-- In an `I`-adically complete situation every point of `X` specializes to a point of `Y`: the
ideal `I` lies in the Jacobson radical, hence inside every maximal ideal. -/
public theorem exists_specializes_mem_range_Yι (S : AlgebraizationSituation.{u})
    [IsAdicComplete S.I S.A] (x : PrimeSpectrum S.A) :
    ∃ y : S.Y, x ⤳ S.Yι.base y := by
  obtain ⟨m, hm, hxm⟩ := Ideal.exists_le_maximal x.asIdeal x.isPrime.ne_top
  have _ := hm
  have hmI : S.I ≤ m :=
    (IsAdicComplete.le_jacobson_bot S.I).trans
      ((Ideal.jacobson_mono bot_le).trans_eq Ideal.jacobson_eq_self_of_isMaximal)
  have hz : (⟨m, hm.isPrime⟩ : PrimeSpectrum S.A) ∈ Set.range S.Yι.base := by
    rw [range_Yι_base]
    exact hmI
  obtain ⟨y, hy⟩ := hz
  exact ⟨y, hy ▸ (PrimeSpectrum.le_iff_specializes x ⟨m, hm.isPrime⟩).mp hxm⟩

/-- In an `I`-adically complete situation the ideal `𝔮 + I` is proper for every prime `𝔮`, so it
has a minimal prime. -/
public theorem exists_minimalPrimes_sup_I (S : AlgebraizationSituation.{u})
    [IsAdicComplete S.I S.A] (q : PrimeSpectrum S.A) :
    ∃ z : S.Y, (S.Yι.base z).asIdeal ∈ (q.asIdeal ⊔ S.I).minimalPrimes := by
  obtain ⟨y, hy⟩ := exists_specializes_mem_range_Yι S q
  have hI : S.I ≤ (S.Yι.base y).asIdeal := by
    have hmem : S.Yι.base y ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) := by
      rw [← range_Yι_base]
      exact ⟨y, rfl⟩
    exact hmem
  have _ : (S.Yι.base y).asIdeal.IsPrime := (S.Yι.base y).isPrime
  obtain ⟨P, hP, _⟩ := Ideal.exists_minimalPrimes_le
    (show q.asIdeal ⊔ S.I ≤ (S.Yι.base y).asIdeal from
      sup_le ((PrimeSpectrum.le_iff_specializes _ _).mpr hy) hI)
  have hPrange : (⟨P, hP.1.1⟩ : PrimeSpectrum S.A) ∈ Set.range S.Yι.base := by
    rw [range_Yι_base]
    exact le_sup_right.trans hP.1.2
  obtain ⟨z, hz⟩ := hPrange
  exact ⟨z, by rw [hz]; exact hP⟩

/-- **The boundary flag of [Stacks, Tag 0EJ8].** Let `A` be `I`-adically complete, let
`𝔭 ≤ 𝔮` be primes of `A` such that every prime above `𝔮` containing `I` also contains `𝔞`, and
suppose no irreducible component of the closed fibre `\overline{\{𝔭\}} ∩ Y` is contained in `Z`.
Then there are points `z` and `y` of `Y` with

* `𝔭_z` minimal over `𝔮 + I`, and `z ∈ Z`;
* `𝔭 ≤ 𝔭_y`, and `y ∉ Z`;
* `z` an immediate specialization of `y`.

The point `z` comes from `Stacks.Algebraization.exists_minimalPrimes_sup_I` and lies in `Z` by
the hypothesis on primes above `𝔮`. The irreducible component of the closed fibre through `z`
has generic point outside `Z`, and [Stacks, Tag 02IM] inside the locally closed set
"closed fibre minus `Z`" produces `y`. -/
public theorem exists_boundary_flag_of_no_component (S : AlgebraizationSituation.{u})
    [IsAdicComplete S.I S.A] (p q : PrimeSpectrum S.A) (hpq : p ≤ q)
    (hboundary : ∀ r : PrimeSpectrum S.A, q ≤ r → S.I ≤ r.asIdeal → S.a ≤ r.asIdeal)
    (hcomponent : ¬ ∃ C : Set (S.Yι.base ⁻¹' closure ({p} : Set S.X)),
      C ∈ irreducibleComponents (S.Yι.base ⁻¹' closure ({p} : Set S.X)) ∧
        C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}) :
    ∃ z y : S.Y,
      (S.Yι.base z).asIdeal ∈ (q.asIdeal ⊔ S.I).minimalPrimes ∧
        z ∈ (S.closedSubsetZ : Set S.Y) ∧
        p ≤ S.Yι.base y ∧ y ∉ (S.closedSubsetZ : Set S.Y) ∧
        IsImmediateSpecialization y z := by
  classical
  obtain ⟨z, hzmin⟩ := exists_minimalPrimes_sup_I S q
  have hzI : S.I ≤ (S.Yι.base z).asIdeal := le_sup_right.trans hzmin.1.2
  have hqz : q ≤ S.Yι.base z := le_sup_left.trans hzmin.1.2
  have hzZ : z ∈ (S.closedSubsetZ : Set S.Y) := by
    rw [mem_closedSubsetZ_iff_mem_range_Zι, range_Zι_base]
    exact hboundary (S.Yι.base z) hqz hzI
  -- The closed fibre of `\overline{\{𝔭\}}`, and the component of it through `z`.
  have hW : IsClosed (S.Yι.base ⁻¹' closure ({p} : Set S.X)) :=
    isClosed_closure.preimage S.Yι.continuous
  let _ : QuasiSober (S.Yι.base ⁻¹' closure ({p} : Set S.X)) :=
    hW.isClosedEmbedding_subtypeVal.quasiSober
  have hzW : z ∈ S.Yι.base ⁻¹' closure ({p} : Set S.X) :=
    (PrimeSpectrum.le_iff_mem_closure _ _).mp (hpq.trans hqz)
  have hC := irreducibleComponent_mem_irreducibleComponents
    (⟨z, hzW⟩ : S.Yι.base ⁻¹' closure ({p} : Set S.X))
  have hη : IsGenericPoint hC.1.genericPoint
      (irreducibleComponent (⟨z, hzW⟩ : S.Yι.base ⁻¹' closure ({p} : Set S.X))) :=
    hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  -- The generic point of that component lies outside `Z`, or the component would lie in `Z`.
  have hηZ : hC.1.genericPoint.val ∉ (S.closedSubsetZ : Set S.Y) := by
    intro hmem
    refine hcomponent ⟨_, hC, fun w hw => ?_⟩
    have hspec : hC.1.genericPoint.val ⤳ w.val :=
      (subtype_specializes_iff _ _).mp (hη.specializes hw)
    exact (mem_closedSubsetZ_iff_mem_range_Zι S w.val).mp
      (S.closedSubsetZ.isClosed.stableUnderSpecialization hspec hmem)
  -- `z` lies in `Z` and the generic point does not, so they differ.
  have hspecηz : hC.1.genericPoint ⤳ (⟨z, hzW⟩ : S.Yι.base ⁻¹' closure ({p} : Set S.X)) :=
    hη.specializes mem_irreducibleComponent
  have hne : hC.1.genericPoint.val ≠ z := by
    intro h
    refine hηZ ?_
    rw [h]
    exact hzZ
  -- The closed fibre minus `Z` is locally closed, so [Stacks, Tag 02IM] applies inside it.
  have hE : IsLocallyClosed ((S.Yι.base ⁻¹' closure ({p} : Set S.X)) \
      (S.closedSubsetZ : Set S.Y)) := by
    rw [Set.diff_eq]
    exact hW.isLocallyClosed.inter S.closedSubsetZ.isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨y, hyE, hyimm⟩ :=
    AlgebraicGeometry.exists_isImmediateSpecialization_mem_of_isLocallyClosed S.Y hE
      ⟨hC.1.genericPoint.property, hηZ⟩ ((subtype_specializes_iff _ _).mp hspecηz) hne
  exact ⟨z, y, hzmin, hzZ, (PrimeSpectrum.le_iff_mem_closure _ _).mpr hyE.1, hyE.2, hyimm⟩

end Stacks.Algebraization

end
