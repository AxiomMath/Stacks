module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Algebraization.AlgebraizationLocalCohomologyIIIBootstrapCriterion
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapCompletionSituation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparisonLocal

/-!
# The completion of a bootstrap situation at the closed point

Let `S` be a bootstrap situation whose ring `A` is local with maximal ideal `𝔪` and whose locus
is `T = {𝔪}`, and let `A'`, `I'`, `M'` be the `I`-adic completions of `A`, `I`, `M`. Then `A'` is
local with maximal ideal `𝔪' = 𝔪 A'`, and `A', 𝔪', I', M'` satisfy the hypotheses of the local
algebraization theorem, whether or not `A` itself is complete.

## Main results

* `Stacks.Algebraization.BootstrapSituation.isLocalRing_adicCompletion_self` and
  `Stacks.Algebraization.BootstrapSituation.map_maximalIdeal_adicCompletion`: the completion of
  the ring of such a situation is local, with maximal ideal `𝔪 A'`.
* `Stacks.Algebraization.depthOrDimensionBound_adicCompletion`: the depth-or-dimension bound
  holds for `M'` over `A'`.
* `Stacks.Algebraization.exists_localAlgebraizationHypotheses_adicCompletion`: the hypotheses of
  the local algebraization theorem hold for the `I`-adic completion.
* `Stacks.Algebraization.adicCompletionLocus_eq_closedPoint`: the locus of the completed
  situation is the closed point of `A'`.
* `Stacks.Algebraization.exists_isLocalAlgebraizationIdeal_adicCompletion`: the conclusion of the
  local algebraization theorem over the completion.

## References

* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

namespace BootstrapSituation

variable (S : BootstrapSituation.{u, u, u})

/-- The closed point lies in `V(I)` when the locus of the situation is the closed point. -/
private theorem closedPoint_mem_zeroLocus_of_locus [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) :
    closedPoint S.A ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) :=
  S.subset_adicLocus (hT ▸ Set.mem_singleton _)

/-- The `I`-adic completion of the ring of a bootstrap situation whose ring is local and whose
locus is the closed point is a local ring. -/
public theorem isLocalRing_adicCompletion_self [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) : IsLocalRing (AdicCompletion S.I S.A) :=
  Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal S.I
    (closedPoint_mem_zeroLocus_of_locus S hT)

/-- The ideal `𝔪 A'` is the maximal ideal of the `I`-adic completion `A'`. -/
public theorem map_maximalIdeal_adicCompletion [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) :
    letI := isLocalRing_adicCompletion_self S hT
    (maximalIdeal S.A).map (algebraMap S.A (AdicCompletion S.I S.A)) =
      maximalIdeal (AdicCompletion S.I S.A) := by
  let := isLocalRing_adicCompletion_self S hT
  exact IsLocalRing.eq_maximalIdeal
    (AdicCompletion.isMaximal_map_of_le S.I (maximalIdeal S.A)
      (closedPoint_mem_zeroLocus_of_locus S hT) S.I.fg_of_isNoetherianRing)

/-- The ideal `I A'` of the `I`-adic completion `A'` is proper. -/
public theorem map_ne_top_adicCompletion [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) :
    S.I.map (algebraMap S.A (AdicCompletion S.I S.A)) ≠ ⊤ := by
  let := isLocalRing_adicCompletion_self S hT
  refine ne_top_of_le_ne_top (maximalIdeal.isMaximal (AdicCompletion S.I S.A)).ne_top ?_
  rw [← map_maximalIdeal_adicCompletion S hT]
  exact Ideal.map_mono (closedPoint_mem_zeroLocus_of_locus S hT)

/-- A prime of `A'` lying over the closed point of `A` is the closed point of `A'`. -/
private theorem eq_closedPoint_of_comap_eq_closedPoint [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) (q : PrimeSpectrum (AdicCompletion S.I S.A))
    (h : PrimeSpectrum.comap (algebraMap S.A (AdicCompletion S.I S.A)) q = closedPoint S.A) :
    letI := isLocalRing_adicCompletion_self S hT
    q = closedPoint (AdicCompletion S.I S.A) := by
  let := isLocalRing_adicCompletion_self S hT
  refine PrimeSpectrum.ext ((maximalIdeal.isMaximal (AdicCompletion S.I S.A)).eq_of_le
    q.2.ne_top ?_).symm
  rw [← map_maximalIdeal_adicCompletion S hT]
  exact Ideal.map_le_iff_le_comap.mpr (congrArg PrimeSpectrum.asIdeal h).ge

end BootstrapSituation

section Completion

variable (S : BootstrapSituation.{u, u, u})

/-- For a prime `𝔭'` of the `I`-adic completion `A'` lying outside `V(I')` and with
`V(𝔭') ∩ V(I') ≠ {𝔪'}`, the completed module `M'` satisfies `depth(M'_{𝔭'}) ≥ s` or
`depth(M'_{𝔭'}) + dim(A'/𝔭') > d + s`. -/
public theorem depthOrDimensionBound_adicCompletion [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) :
    letI := BootstrapSituation.isLocalRing_adicCompletion_self S hT
    ∀ p' : PrimeSpectrum (AdicCompletion S.I S.A),
      p' ∉ PrimeSpectrum.zeroLocus
        ((S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) :
          Set (AdicCompletion S.I S.A)) →
      PrimeSpectrum.zeroLocus (p'.asIdeal : Set (AdicCompletion S.I S.A)) ∩
          PrimeSpectrum.zeroLocus
            ((S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) :
              Set (AdicCompletion S.I S.A)) ≠
        {closedPoint (AdicCompletion S.I S.A)} →
      ((enatToEInt
          (Module.depth (Localization.AtPrime p'.asIdeal)
            (maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion S.I S.M))) ≥
            (S.s : EInt)) ∨
        (enatToEInt
            (Module.depth (Localization.AtPrime p'.asIdeal)
              (maximalIdeal (Localization.AtPrime p'.asIdeal))
              (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion S.I S.M))) +
            krullDimToEInt (ringKrullDim (AdicCompletion S.I S.A ⧸ p'.asIdeal)) >
          ((S.d + S.s : ℤ) : EInt))) := by
  let := BootstrapSituation.isLocalRing_adicCompletion_self S hT
  set A' := AdicCompletion S.I S.A
  set f := algebraMap S.A A'
  set I' := S.I.map f
  have hclosed : closedPoint S.A ∈ S.T := hT ▸ Set.mem_singleton _
  have hmeq : (maximalIdeal S.A).map f = maximalIdeal A' :=
    BootstrapSituation.map_maximalIdeal_adicCompletion S hT
  have hI'ne : I' ≠ ⊤ := BootstrapSituation.map_ne_top_adicCompletion S hT
  intro p' hp'I hne
  set p : PrimeSpectrum S.A := ⟨p'.asIdeal.comap f, Ideal.comap_isPrime _ _⟩
  have hpI : p ∉ PrimeSpectrum.zeroLocus (S.I : Set S.A) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    intro hsub
    refine hp'I ?_
    rw [PrimeSpectrum.mem_zeroLocus]
    exact SetLike.coe_subset_coe.mpr
      (Ideal.map_le_iff_le_comap.mpr (SetLike.coe_subset_coe.mp hsub))
  have : p'.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  obtain ⟨r', hr', hr'ne⟩ : ∃ r' : PrimeSpectrum A',
      r' ∈ PrimeSpectrum.zeroLocus (p'.asIdeal : Set A') ∩
        PrimeSpectrum.zeroLocus (I' : Set A') ∧ r' ≠ closedPoint A' := by
    by_contra hcon
    push Not at hcon
    have hmem : closedPoint A' ∈ PrimeSpectrum.zeroLocus (p'.asIdeal : Set A') ∩
        PrimeSpectrum.zeroLocus (I' : Set A') :=
      ⟨closedPoint_mem_zeroLocus p'.2.ne_top, closedPoint_mem_zeroLocus hI'ne⟩
    exact hne (Set.Subset.antisymm (fun x hx ↦ hcon x hx) (Set.singleton_subset_iff.2 hmem))
  set r : PrimeSpectrum S.A := ⟨r'.asIdeal.comap f, Ideal.comap_isPrime _ _⟩
  have hpr : p.asIdeal ≤ r.asIdeal := Ideal.comap_mono (SetLike.coe_subset_coe.mp hr'.1)
  have hrI : r ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    exact SetLike.coe_subset_coe.mpr
      (Ideal.map_le_iff_le_comap.mp (SetLike.coe_subset_coe.mp hr'.2))
  have hrm : r.asIdeal ≤ (closedPoint S.A).asIdeal := IsLocalRing.le_maximalIdeal r.2.ne_top
  have hrT : r ∉ S.T := by
    rw [hT, Set.mem_singleton_iff]
    intro hreq
    exact hr'ne (BootstrapSituation.eq_closedPoint_of_comap_eq_closedPoint S hT r' hreq)
  have hbound := S.depth_or_depth_add_dimension p r (closedPoint S.A) hpr hrm hpI hrI hrT
    hclosed
  rw [ringKrullDim_localization_quotient_map_of_eq_closedPoint
    (q := closedPoint S.A) rfl] at hbound
  rcases hbound with hdep | hbig
  · exact Or.inl (le_trans hdep
      (enatToEInt_mono (Module.depth_localized_adicCompletion_le S.I p.asIdeal p'.asIdeal)))
  · refine Or.inr ?_
    have hE := congrArg krullDimToEInt
      (Module.depth_add_ringKrullDim_quotient_adicCompletion S.A S.dualizing S.I
        (BootstrapSituation.closedPoint_mem_zeroLocus_of_locus S hT) S.M p.asIdeal p'.asIdeal)
    have hadd : ∀ (x : ℕ∞) (y : WithBot ℕ∞),
        krullDimToEInt ((x : WithBot ℕ∞) + y) = enatToEInt x + krullDimToEInt y := by
      intro x y
      induction y using WithBot.recBotCoe with
      | bot => induction x using ENat.recTopCoe <;> rfl
      | coe z => induction x using ENat.recTopCoe <;> induction z using ENat.recTopCoe <;> rfl
    rw [hadd, hadd] at hE
    rwa [hE]

/-- In a bootstrap situation with `A` local and `T = {𝔪}`, there is an object `omega` of the
derived category of `A'`-modules for which the `I`-adic completions `A'`, `I'`, `M'` satisfy the
hypotheses `Stacks.Algebraization.LocalAlgebraizationHypotheses` of the local algebraization
theorem. -/
@[stacks 0EFV "parts (G) and (D) for T = {𝔪}: the hypotheses of Stacks 0DXP hold for the I-adic
completion A', I', M' of A, I, M, whose locus is the closed point of A'"]
public theorem exists_localAlgebraizationHypotheses_adicCompletion [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) :
    letI := BootstrapSituation.isLocalRing_adicCompletion_self S hT
    letI : Module.Finite (AdicCompletion S.I S.A) (AdicCompletion S.I S.M) :=
      finite_adicCompletion S
    ∃ omega : DerivedCategory (ModuleCat.{u} (AdicCompletion S.I S.A)),
      LocalAlgebraizationHypotheses (M := AdicCompletion S.I S.M)
        (S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) S.s S.d omega := by
  let := BootstrapSituation.isLocalRing_adicCompletion_self S hT
  let : Module.Finite (AdicCompletion S.I S.A) (AdicCompletion S.I S.M) :=
    finite_adicCompletion S
  obtain ⟨omega, homega⟩ := dualizing_adicCompletion S
  exact ⟨omega, BootstrapSituation.map_ne_top_adicCompletion S hT,
    (IsAdicComplete.map_algebraMap_iff (S := AdicCompletion S.I S.A) S.I
      (AdicCompletion S.I S.A)).mpr (AdicCompletion.isAdicComplete S.I.fg_of_isNoetherianRing),
    homega, cohomologicalDimension_le_adicCompletion S, depthOrDimensionBound_adicCompletion S hT⟩

/-- The preimage of `{𝔪}` under `Spec(A') → Spec(A)` is `{𝔪'}`. -/
public theorem adicCompletionLocus_eq_closedPoint [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) :
    letI := BootstrapSituation.isLocalRing_adicCompletion_self S hT
    adicCompletionLocus S = {closedPoint (AdicCompletion S.I S.A)} := by
  let := BootstrapSituation.isLocalRing_adicCompletion_self S hT
  have hmeq : (maximalIdeal S.A).map (algebraMap S.A (AdicCompletion S.I S.A)) =
      maximalIdeal (AdicCompletion S.I S.A) :=
    BootstrapSituation.map_maximalIdeal_adicCompletion S hT
  ext q
  simp only [adicCompletionLocus, Set.mem_preimage, hT, Set.mem_singleton_iff]
  exact ⟨BootstrapSituation.eq_closedPoint_of_comap_eq_closedPoint S hT q,
    fun h ↦ h ▸ PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime _)
      (Ideal.map_le_iff_le_comap.mp hmeq.le))⟩

namespace BootstrapSituation

end BootstrapSituation

/-- In a bootstrap situation with `A` local and `T = {𝔪}` there is an ideal `J₀` of the `I`-adic
completion `A'` with `V(J₀) ∩ V(I') = {𝔪'}` such that for every `J ⊆ J₀` with that same property
the canonical map `RΓ_J(M') ⟶ RΓ_{𝔪'}(M')^∧` is an isomorphism on cohomology in degrees `≤ s`. -/
public theorem exists_isLocalAlgebraizationIdeal_adicCompletion [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) :
    letI := BootstrapSituation.isLocalRing_adicCompletion_self S hT
    letI : Module.Finite (AdicCompletion S.I S.A) (AdicCompletion S.I S.M) :=
      finite_adicCompletion S
    ∃ J₀ : Ideal (AdicCompletion S.I S.A),
      IsLocalAlgebraizationIdeal (M := AdicCompletion S.I S.M)
        (S.I.map (algebraMap S.A (AdicCompletion S.I S.A)))
        (BootstrapSituation.map_ne_top_adicCompletion S hT) S.s J₀ := by
  let := BootstrapSituation.isLocalRing_adicCompletion_self S hT
  let : Module.Finite (AdicCompletion S.I S.A) (AdicCompletion S.I S.M) :=
    finite_adicCompletion S
  obtain ⟨omega, H⟩ := exists_localAlgebraizationHypotheses_adicCompletion S hT
  exact exists_isLocalAlgebraizationIdeal
    (S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) S.s S.d omega H

end Completion

end Stacks.Algebraization

end
