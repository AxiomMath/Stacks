module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.DepthThreeImprovementInputs
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.IsolatedPrime
public import StacksFrontier.RingTheory.LocalCohomology.TopLocalCohomology

/-!
# The conditions of the depth-two improvement on `U` from the `(2, 2 + d)`-inequalities

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`, and let `δ^Y_Z` be the distance of a point of `Y` from
`Z`. Let `d ≥ cd(A, I)` and let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)` satisfying the
`(2, 2 + d)`-inequalities of [Stacks, Tag 0EJ3]. The proof of [Stacks, Tag 0EJG] applies
[Stacks, Tag 0EJF] on `U` with `T = {δ^Y_Z ≤ 2}` and `T' = {δ^Y_Z ≤ 1}`; this file derives the
conditions (a)-(d) of that lemma.

## Main results

* `Stacks.Algebraization.AlgebraizationSituation.cohomologicalDimension_idealOnOpen_le`:
  condition (a): on an affine open `V` of `U` the cohomological dimension of `I𝒪_U(V)` is at most
  `cd(A, I)`, by [Stacks, Tag 0DXA], the ideal being extended from `I`.
* `Stacks.Algebraization.AlgebraizationSituation.zero_le_cohomologicalDimension_of_mem_support`:
  if `U ∩ Y` is nonempty then `cd(A, I) ≥ 0`, by [Stacks, Tag 0DXF] at the closed point of the
  localization of `A` at a point of `U ∩ Y`.
* `Stacks.Algebraization.pos_completedStalkDepth_of_satisfiesDepthInequalities`,
  `Stacks.Algebraization.one_lt_completedStalkDepth_of_satisfiesDepthInequalities` and
  `Stacks.Algebraization.completedStalkDepth_of_satisfiesDepthInequalities`: conditions (b),
  (d) and (c) of [Stacks, Tag 0EJF].

## Implementation notes

The source writes "`d ≥ cd(A, I)`" for an integer `d`, which may be `-1`; condition (a) of
[Stacks, Tag 0EJF] is stated with a natural number. The natural number used is `d.toNat`. When
`d < 0` there is no point of `U ∩ Y` at all, because `cd(A, I) ≥ 0` as soon as there is one,
so conditions (b)-(d), which quantify over points of `U ∩ Y`, hold vacuously, and condition (a)
holds since `cd ≤ d ≤ d.toNat`.

At a point of `T'` the distance is exactly `1`, being at least one on `U`
(`Stacks.Algebraization.AlgebraizationSituation.one_le_distanceToZ`); this is how the
inequalities with `δ^Y_Z` added turn into those of [Stacks, Tag 0EJF] without it.

## References

* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3)
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA)
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- In a local ring, `V(𝔪) ∩ V(J)` is the closed point for any ideal `J ≤ 𝔪`. -/
private theorem zeroLocus_maximalIdeal_inter_zeroLocus_eq_closedPoint {R : Type*} [CommRing R]
    [IsLocalRing R] {J : Ideal R} (hJ : J ≤ IsLocalRing.maximalIdeal R) :
    PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) ∩
      PrimeSpectrum.zeroLocus (J : Set R) = {IsLocalRing.closedPoint R} := by
  ext w
  simp only [Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, -⟩
    exact PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
      w.isPrime.ne_top hw).symm
  · rintro rfl
    exact ⟨le_rfl, hJ⟩

namespace AlgebraizationSituation

variable (S : AlgebraizationSituation.{u})

/-! ### Condition (a): the cohomological dimension on affine opens of `U` -/

/-- On an affine open `V` of `U`, the ideal `I𝒪_U(V)` is the extension of `I` along
`A ⟶ Γ(U, V)`. -/
public theorem idealOnOpen_ideal_eq_map (V : S.U.toScheme.affineOpens) :
    (idealOnOpen S).ideal V = S.I.map
      ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.X.presheaf.map (homOfLE le_top).op ≫
        (S.U.ι.appIso V).hom).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ofIdealTop_ideal]
  have hsymm : ∀ K : Ideal Γ(S.X, S.U.ι ''ᵁ V.1),
      K.comap (S.U.ι.appIso V).inv.hom = K.map (S.U.ι.appIso V).hom.hom := fun K =>
    Ideal.comap_symm (I := K) (S.U.ι.appIso V.1).commRingCatIsoToRingEquiv
  rw [hsymm, Ideal.map_map, Ideal.map_map]
  rfl

/-- **Condition (a) of [Stacks, Tag 0EJF] on `U`.** On every affine open `V` of `U` the
cohomological dimension of `I𝒪_U(V)` in `Γ(U, V)` is at most `cd(A, I)`. -/
public theorem cohomologicalDimension_idealOnOpen_le (V : S.U.toScheme.affineOpens)
    (hV : ((idealOnOpen S).ideal V).FG) :
    Stacks.LocalCohomology.cohomologicalDimension Γ(S.U.toScheme, V.1) ((idealOnOpen S).ideal V)
        hV ≤
      Stacks.LocalCohomology.cohomologicalDimension S.A S.I (Ideal.fg_of_isNoetherianRing S.I) := by
  rw [Stacks.LocalCohomology.cohomologicalDimension_congr hV
    ((Ideal.fg_of_isNoetherianRing S.I).map _) (S.idealOnOpen_ideal_eq_map V)]
  exact Stacks.LocalCohomology.cohomologicalDimension_map_le _ S.I _

/-- **Condition (a) of [Stacks, Tag 0EJF] on `U`, in the form of an affine neighbourhood.**
If `cd(A, I) ≤ d`, every point of `U` has an affine open neighbourhood `V` with
`cd(Γ(U, V), I𝒪_U(V)) ≤ d.toNat`. -/
public theorem exists_affineOpen_cohomologicalDimension_idealOnOpen_le (d : ℤ)
    (hd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d) (y : S.U.toScheme) :
    ∃ V : S.U.toScheme.affineOpens, y ∈ V.1 ∧
      ∀ hV : ((idealOnOpen S).ideal V).FG,
        Stacks.LocalCohomology.cohomologicalDimension Γ(S.U.toScheme, V.1)
          ((idealOnOpen S).ideal V) hV ≤ ((d.toNat : ℕ) : ℤ) := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    S.U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  exact ⟨⟨V, hV⟩, hyV, fun hfg =>
    ((S.cohomologicalDimension_idealOnOpen_le ⟨V, hV⟩ hfg).trans hd).trans (Int.self_le_toNat d)⟩

/-- If `U ∩ Y` has a point, then `cd(A, I) ≥ 0`: localizing at that point gives a Noetherian
local ring in which `I` is proper, and there the cohomological dimension is at least the
dimension `0` of the quotient by the maximal ideal ([Stacks, Tag 0DXF]); it does not increase
under the localization ([Stacks, Tag 0DXA]). -/
public theorem zero_le_cohomologicalDimension_of_mem_support (y : S.U.toScheme)
    (hy : y ∈ (idealOnOpen S).support) :
    0 ≤ Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) := by
  obtain ⟨z, hyz⟩ := (S.mem_support_idealOnOpen_iff y).mp hy
  have hIq : S.I ≤ (S.U.ι.base y : PrimeSpectrum S.A).asIdeal := by
    rw [hyz]
    intro a ha
    change Ideal.Quotient.mk S.I a ∈ (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact Ideal.zero_mem _
  let q : PrimeSpectrum S.A := S.U.ι.base y
  let B := Localization.AtPrime q.asIdeal
  let J : Ideal B := S.I.map (algebraMap S.A B)
  have hJm : J ≤ IsLocalRing.maximalIdeal B := Ideal.map_le_iff_le_comap.mpr fun a ha =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B q.asIdeal a).mpr (hIq ha)
  have hdim : ringKrullDim (B ⧸ IsLocalRing.maximalIdeal B) = ((0 : ℕ) : WithBot ℕ∞) := by
    let := Ideal.Quotient.field (IsLocalRing.maximalIdeal B)
    exact ringKrullDim_eq_zero_of_field _
  have h0 := Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension' B
    (IsLocalRing.maximalIdeal B) J ((Ideal.fg_of_isNoetherianRing S.I).map _)
    (zeroLocus_maximalIdeal_inter_zeroLocus_eq_closedPoint hJm) 0 hdim
  exact_mod_cast h0.trans
    (Stacks.LocalCohomology.cohomologicalDimension_map_le (algebraMap S.A B) S.I _)

end AlgebraizationSituation

/-! ### Conditions (b), (c), (d) from the `(2, 2 + d)`-inequalities -/

/-- In the extended integers, `m < n + k` for `n : ℕ∞` and natural `k` says `n = ⊤` or
`n` is a natural number with `m < n + k`. -/
private theorem enatToEInt_add_natCast_gt {n : ℕ∞} {k : ℕ} {m : ℤ}
    (h : enatToEInt n + ((k : ℤ) : EInt) > ((m : ℤ) : EInt)) :
    n = ⊤ ∨ ∃ j : ℕ, n = j ∧ m < (j : ℤ) + k := by
  cases n using ENat.recTopCoe with
  | top => exact Or.inl rfl
  | coe j =>
    refine Or.inr ⟨j, rfl, ?_⟩
    change ((m : ℤ) : EInt) < ((j : ℤ) : EInt) + ((k : ℤ) : EInt) at h
    rw [← Stacks.Chow.coe_add_coe_eq_coe_add] at h
    exact WithBotTop.coe_lt_coe.mp h

/-- In the extended integers, `m ≤ n + k` for `n : ℕ∞` and natural `k` says `n = ⊤` or `n` is a
natural number with `m ≤ n + k`. -/
private theorem enatToEInt_add_natCast_ge {n : ℕ∞} {k : ℕ} {m : ℤ}
    (h : enatToEInt n + ((k : ℤ) : EInt) ≥ ((m : ℤ) : EInt)) :
    n = ⊤ ∨ ∃ j : ℕ, n = j ∧ m ≤ (j : ℤ) + k := by
  cases n using ENat.recTopCoe with
  | top => exact Or.inl rfl
  | coe j =>
    refine Or.inr ⟨j, rfl, ?_⟩
    change ((m : ℤ) : EInt) ≤ ((j : ℤ) : EInt) + ((k : ℤ) : EInt) at h
    rw [← Stacks.Chow.coe_add_coe_eq_coe_add] at h
    exact WithBotTop.coe_le_coe.mp h

/-- A distance at most `k`, finite, written as a natural number. -/
private theorem exists_natCast_eq_of_le {δ : ℕ∞} {k : ℕ} (h : δ ≤ k) :
    ∃ j : ℕ, δ = j ∧ j ≤ k := by
  cases δ using ENat.recTopCoe with
  | top => exact absurd h (by simp)
  | coe j => exact ⟨j, rfl, by exact_mod_cast h⟩

/-- If `𝔭` is a prime other than `𝔪_y^∧` with `V(𝔭) ∩ V(I𝒪_{X,y}^∧) = {𝔪_y^∧}`, then
`𝔭 ∉ V(I𝒪_{X,y}^∧)`: otherwise `𝔭` itself lies in that intersection. -/
private theorem not_completedLocalIdeal_le {X : Scheme.{u}} (I : X.IdealSheafData) (y : X)
    (p : PrimeSpectrum (completedLocalRing I y))
    (hp : p.asIdeal ≠ completedMaximalIdeal I y)
    (hfib : adicClosedFibreThrough I y p = {completedMaximalIdeal I y}) :
    ¬ completedLocalIdeal I y ≤ p.asIdeal := fun hle => by
  have hmem : p.asIdeal ∈ adicClosedFibreThrough I y p := ⟨p.isPrime, le_rfl, hle⟩
  rw [hfib] at hmem
  exact hp hmem

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **Condition (b) of [Stacks, Tag 0EJF] for `T = {δ ≤ 2}`.** If `(ℱₙ)` satisfies the
`(2, b)`-inequalities, then at `y ∈ T` and a nonmaximal prime `𝔭` of `𝒪_{X,y}^∧` with
`V(𝔭) ∩ V(I𝒪_{X,y}^∧) = {𝔪_y^∧}`, the depth of `(ℱ_y^∧)_𝔭` is positive. -/
public theorem pos_completedStalkDepth_of_satisfiesDepthInequalities (b : ℤ)
    (h : SatisfiesDepthInequalities S F 2 b) :
    ∀ y ∈ S.distanceToZSublevel 2, ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
      p.asIdeal ≠ completedMaximalIdeal (idealOnOpen S) y →
      adicClosedFibreThrough (idealOnOpen S) y p = {completedMaximalIdeal (idealOnOpen S) y} →
      0 < completedStalkDepth (idealOnOpen S) F y p := by
  rintro y ⟨z, hyz, hz⟩ p hp hfib
  have hgt := (h y z hyz p (not_completedLocalIdeal_le _ y p hp hfib)).2 hfib
  obtain ⟨j, hj, hj2⟩ := exists_natCast_eq_of_le (k := 2) hz
  unfold depthAddDistance at hgt
  rw [hj] at hgt
  rcases enatToEInt_add_natCast_gt hgt with htop | ⟨i, hi, hlt⟩
  · rw [htop]
    exact ENat.top_pos
  · rw [hi]
    exact_mod_cast (by omega : 0 < i)

/-- **Condition (d) of [Stacks, Tag 0EJF] for `T' = {δ ≤ 1}`.** If `(ℱₙ)` satisfies the
`(2, b)`-inequalities, then at `y ∈ T'` and a nonmaximal prime `𝔭` of `𝒪_{X,y}^∧` with
`V(𝔭) ∩ V(I𝒪_{X,y}^∧) = {𝔪_y^∧}`, the depth of `(ℱ_y^∧)_𝔭` is greater than one. -/
public theorem one_lt_completedStalkDepth_of_satisfiesDepthInequalities (b : ℤ)
    (h : SatisfiesDepthInequalities S F 2 b) :
    ∀ y ∈ S.distanceToZSublevel 1, ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
      p.asIdeal ≠ completedMaximalIdeal (idealOnOpen S) y →
      adicClosedFibreThrough (idealOnOpen S) y p = {completedMaximalIdeal (idealOnOpen S) y} →
      1 < completedStalkDepth (idealOnOpen S) F y p := by
  rintro y ⟨z, hyz, hz⟩ p hp hfib
  have hgt := (h y z hyz p (not_completedLocalIdeal_le _ y p hp hfib)).2 hfib
  obtain ⟨j, hj, hj1⟩ := exists_natCast_eq_of_le (k := 1) hz
  unfold depthAddDistance at hgt
  rw [hj] at hgt
  rcases enatToEInt_add_natCast_gt hgt with htop | ⟨i, hi, hlt⟩
  · rw [htop]
    exact ENat.natCast_lt_top 1
  · rw [hi]
    exact_mod_cast (by omega : 1 < i)

/-- **Condition (c) of [Stacks, Tag 0EJF] for `T' = {δ ≤ 1}`.** Let `d ≥ cd(A, I)`. If `(ℱₙ)`
satisfies the `(2, 2 + d)`-inequalities, then at `y ∈ T'` and a prime `𝔭 ∉ V(I𝒪_{X,y}^∧)` of
`𝒪_{X,y}^∧` with `V(𝔭) ∩ V(I𝒪_{X,y}^∧) ≠ {𝔪_y^∧}`, either the depth of `(ℱ_y^∧)_𝔭` is at
least one or `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 1 + d`. The bound is written with the
natural number `d.toNat`, which is `d` because `U ∩ Y` is nonempty. -/
public theorem completedStalkDepth_of_satisfiesDepthInequalities (d : ℤ)
    (hd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (h : SatisfiesDepthInequalities S F 2 (2 + d)) :
    ∀ y ∈ S.distanceToZSublevel 1, ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
      ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
      adicClosedFibreThrough (idealOnOpen S) y p ≠ {completedMaximalIdeal (idealOnOpen S) y} →
      1 ≤ completedStalkDepth (idealOnOpen S) F y p ∨
        enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
            krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) >
          ((1 + (d.toNat : ℤ) : ℤ) : EInt) := by
  rintro y ⟨z, hyz, hz⟩ p hp hfib
  have hd0 : 0 ≤ d := (S.zero_le_cohomologicalDimension_of_mem_support y
    ((S.mem_support_idealOnOpen_iff y).mpr ⟨z, hyz⟩)).trans hd
  have hdnat : ((d.toNat : ℤ)) = d := Int.toNat_of_nonneg hd0
  have hone : S.distanceToZ z = 1 := le_antisymm hz (S.one_le_distanceToZ y z hyz)
  have hδ : enatToEInt (S.distanceToZ z) = (((1 : ℕ) : ℤ) : EInt) := by
    rw [hone]
    rfl
  rcases (h y z hyz p hp).1 hfib with hge | hgt
  · left
    unfold depthAddDistance at hge
    rw [hδ] at hge
    rcases enatToEInt_add_natCast_ge hge with htop | ⟨i, hi, hle⟩
    · rw [htop]
      exact le_top
    · rw [hi]
      exact_mod_cast (by omega : 1 ≤ i)
  · right
    unfold depthAddDimAddDistance at hgt
    rw [hδ] at hgt
    rw [hdnat]
    have h2 : (((2 + d : ℤ)) : EInt) = ((1 + d : ℤ) : EInt) + (((1 : ℕ) : ℤ) : EInt) := by
      rw [← Stacks.Chow.coe_add_coe_eq_coe_add]
      congr 1
      omega
    rw [h2, gt_iff_lt, ← Stacks.Chow.eintAddRight_apply, ← Stacks.Chow.eintAddRight_apply] at hgt
    exact (Stacks.Chow.eintAddRight _).lt_iff_lt.mp hgt

end Stacks.Algebraization

end
