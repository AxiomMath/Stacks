module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.Regularize
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveFamilyResolution

/-!
# Separating the curves of a family on a regular surface into normal crossings

Let `W` be a regular Noetherian scheme of dimension two and let `F` be a finite family of regular
configuration curves on `W`. A finite sequence of blowups at closed points replaces `F` by a family
of regular configuration curves, covering the inverse image of the union of `F`, in which any two
members meet transversally — their local equations generate the maximal ideal — and no three
members have a common point.

This is the intersection-multiplicity iteration in the middle of the proof of
[Stacks, Tag 0BIC]. For two distinct members `Y, Y'` and a point `x` of both, the invariant is the
intersection multiplicity `m_x(Y ∩ Y')` of [Stacks, Tag 0BI6]. Blowing up a point `p` where
`m_p(Y ∩ Y') ≥ 2` lowers it ([Stacks, Tag 0BI7] part (3)), the new exceptional curve meets every
strict transform with multiplicity one (part (2)), and nothing changes away from `p`; so the sum
of the excesses `m_x(Y ∩ Y') - 1` drops. Once every multiplicity is one, blowing up a point on
three or more members separates them above it, again by part (3), so the number of such points
drops.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_transverse` — the iteration.

## References

* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
* [Stacks Project, Tag 0BI7](https://stacks.math.columbia.edu/tag/0BI7)
* [Stacks Project, Tag 0BI6](https://stacks.math.columbia.edu/tag/0BI6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The blowup map off the exceptional fibre -/

section OffFibre

variable {W : Scheme.{u}} (p : W) (hp : IsClosed ({p} : Set W))

/-- The blowup at a closed point is injective off the fibre over that point. -/
public theorem injOn_blowUpToBase_compl_fibre :
    Set.InjOn (blowUpToBase (centerIdeal p hp)).base
      ((blowUpToBase (centerIdeal p hp)).base ⁻¹' {p})ᶜ := by
  have h := injOn_of_isIso_morphismRestrict (blowUpToBase (centerIdeal p hp))
    ⟨(centerIdeal p hp).supportᶜ, (centerIdeal p hp).support.isClosed.isOpen_compl⟩
    (isIso_blowUp_restrict_compl_support (centerIdeal p hp))
  intro z hz w hw hzw
  refine h ?_ ?_ hzw
  · show (blowUpToBase (centerIdeal p hp)).base z ∉ ((centerIdeal p hp).support : Set W)
    rw [show ((centerIdeal p hp).support : Set W) = {p} from
      Scheme.IdealSheafData.coe_support_vanishingIdeal _]
    exact hz
  · show (blowUpToBase (centerIdeal p hp)).base w ∉ ((centerIdeal p hp).support : Set W)
    rw [show ((centerIdeal p hp).support : Set W) = {p} from
      Scheme.IdealSheafData.coe_support_vanishingIdeal _]
    exact hw

end OffFibre

/-! ### The excess of intersection multiplicities -/

/-- The **excess** of two closed subschemes: the sum over all points of the amount by which their
local intersection colength exceeds one. For two distinct curves on a surface it is the sum of
`m_x(Y ∩ Y') - 1` over their finitely many intersection points, in the notation of
[Stacks, Tag 0BI6]. -/
public def pairExcess {W : Scheme.{u}} (Y Y' : W.IdealSheafData) : ℕ :=
  ∑ᶠ x : W, (localIntersectionColength Y Y' x - 1)

public theorem pairExcess_comm {W : Scheme.{u}} (Y Y' : W.IdealSheafData) :
    pairExcess Y Y' = pairExcess Y' Y := by
  simp only [pairExcess, localIntersectionColength_comm Y Y']

/-- The excess function of two closed subschemes is supported on their intersection. -/
public theorem support_colength_sub_one_subset {W : Scheme.{u}} (Y Y' : W.IdealSheafData) :
    Function.support (fun x : W => localIntersectionColength Y Y' x - 1) ⊆
      (Y.support : Set W) ∩ Y'.support := by
  intro x hx
  by_contra h
  rw [Set.mem_inter_iff, not_and_or] at h
  exact hx (by simp [localIntersectionColength_eq_zero_of_notMem Y Y' x h])

section Generic

variable {W : Scheme.{u}}

/-- The generic point of an integral closed subscheme, as a point of the ambient scheme. -/
local notation3 "gen " Y:max => Scheme.IdealSheafData.subschemeι Y
  (_root_.genericPoint (Scheme.IdealSheafData.subscheme Y))

/-- Two distinct configuration curves on a Noetherian surface meet in finitely many points. -/
public theorem IsConfigCurve.finite_inter_support [IsNoetherian W]
    (hdim : topologicalKrullDim W = 2) {Y Y' : W.IdealSheafData} (hY : IsConfigCurve Y)
    (hY' : IsConfigCurve Y') (hne : Y ≠ Y') :
    ((Y.support : Set W) ∩ Y'.support).Finite := by
  have := hY.isIntegral
  have := hY'.isIntegral
  exact (finite_inter_support_of_ne hdim Y Y' hY.isEffectiveCartierDivisor
    hY'.isEffectiveCartierDivisor hne).1

/-- A point lying on a configuration curve over a closed point `p` of the blown-up surface lies
on the exceptional divisor. -/
private theorem mem_support_exceptionalIdeal_of_eq (p : W) (hp : IsClosed ({p} : Set W))
    (q : blowUp (centerIdeal p hp)) (hq : (blowUpToBase (centerIdeal p hp)).base q = p) :
    q ∈ (exceptionalIdeal (centerIdeal p hp)).support :=
  (mem_exceptionalIdeal_support_iff p hp q).mpr hq

/-- A point on two members of a family of closed subschemes lies on their join. -/
private theorem mem_support_sup_of_mem {Y Y' : W.IdealSheafData} {x : W}
    (h : x ∈ (Y.support : Set W)) (h' : x ∈ (Y'.support : Set W)) : x ∈ (Y ⊔ Y').support := by
  rw [Scheme.IdealSheafData.support_sup]; exact ⟨h, h'⟩

/-- A configuration curve through a point with two-dimensional local ring has dimension one. -/
private theorem topologicalKrullDim_eq_one_of_mem_family [IsNoetherian W]
    (hdim : topologicalKrullDim W = 2) {F : Finset W.IdealSheafData}
    (hF : ∀ Y ∈ F, IsConfigCurve Y) {p : W} (hpdim : ringKrullDim (W.presheaf.stalk p) = 2) :
    ∀ Y ∈ F, p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1 :=
  fun Y hY h => (hF Y hY).topologicalKrullDim_eq_one_of_ringKrullDim_eq_two hdim hpdim h

/-- **The excess of a pair of regular configuration curves drops under the blowup at a point where
they meet with multiplicity at least two, and never grows.** Away from the centre nothing
changes; above it the two strict transforms meet in at most one point, the unique point of the
first on the exceptional curve ([Stacks, Tag 0BI7] part (2)), with smaller multiplicity
([Stacks, Tag 0BI7] part (3)). -/
public theorem pairExcess_transformIdeal_add_le [IsNoetherian W]
    (hW : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    {Y Y' : W.IdealSheafData} (hY : IsConfigCurve Y) (hY' : IsConfigCurve Y')
    (hreg : AlgebraicGeometry.IsRegular Y.subscheme)
    (hreg' : AlgebraicGeometry.IsRegular Y'.subscheme) (hne : Y ≠ Y') (p : W)
    (hp : IsClosed ({p} : Set W)) (hpdim : ringKrullDim (W.presheaf.stalk p) = 2) :
    pairExcess (transformIdeal Y p hp) (transformIdeal Y' p hp) +
        (if 2 ≤ localIntersectionColength Y Y' p then 1 else 0) ≤ pairExcess Y Y' := by
  classical
  have := hY.isIntegral
  have := hY'.isIntegral
  set b := blowUpToBase (centerIdeal p hp) with hb
  have : IsNoetherian (blowUp (centerIdeal p hp)) := isNoetherian_blowUp _
  have hdim' : topologicalKrullDim (blowUp (centerIdeal p hp)) = 2 :=
    (isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton W hW hdim p hp).2
  have hdimY : p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1 :=
    fun h => hY.topologicalKrullDim_eq_one_of_ringKrullDim_eq_two hdim hpdim h
  have hdimY' : p ∈ (Y'.support : Set W) → topologicalKrullDim Y'.subscheme = 1 :=
    fun h => hY'.topologicalKrullDim_eq_one_of_ringKrullDim_eq_two hdim hpdim h
  have hT := isConfigCurve_transformIdeal hW hdim hY p hp
    (genericPoint_ne_of_ringKrullDim_eq_two hY hpdim) hdimY
  have hT' := isConfigCurve_transformIdeal hW hdim hY' p hp
    (genericPoint_ne_of_ringKrullDim_eq_two hY' hpdim) hdimY'
  have hTne : transformIdeal Y p hp ≠ transformIdeal Y' p hp := by
    intro h
    refine hne (injOn_transformIdeal {Y, Y'} (by simp [hY, hY']) p hp
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro _ (rfl | rfl) <;> assumption)
      (by simp) (by simp) h)
  set S := (hY.finite_inter_support hdim hY' hne).toFinset with hS
  set S' := (hT.finite_inter_support hdim' hT' hTne).toFinset with hS'
  set g : W → ℕ := fun x => localIntersectionColength Y Y' x - 1 with hg
  set g' : blowUp (centerIdeal p hp) → ℕ := fun q =>
    localIntersectionColength (transformIdeal Y p hp) (transformIdeal Y' p hp) q - 1 with hg'
  have hgS : Function.support g ⊆ (S : Set W) := by
    rw [hS, Set.Finite.coe_toFinset]; exact support_colength_sub_one_subset Y Y'
  have hg'S' : Function.support g' ⊆ (S' : Set _) := by
    rw [hS', Set.Finite.coe_toFinset]; exact support_colength_sub_one_subset _ _
  show ∑ᶠ q, g' q + _ ≤ ∑ᶠ x, g x
  rw [finsum_eq_sum_of_support_subset g hgS, finsum_eq_sum_of_support_subset g' hg'S',
    ← Finset.sum_filter_add_sum_filter_not S' (fun q => b.base q = p)]
  -- away from the fibre
  have hoff : ∑ q ∈ S'.filter (fun q => ¬ b.base q = p), g' q ≤ ∑ x ∈ S.erase p, g x := by
    calc ∑ q ∈ S'.filter (fun q => ¬ b.base q = p), g' q
        = ∑ q ∈ S'.filter (fun q => ¬ b.base q = p), g (b.base q) := by
          refine Finset.sum_congr rfl fun q hq => ?_
          rw [Finset.mem_filter] at hq
          simp only [hg, hg', localIntersectionColength_transformIdeal_of_ne Y Y' p hp q hq.2, hb]
      _ = ∑ x ∈ (S'.filter (fun q => ¬ b.base q = p)).image b.base, g x := by
          refine (Finset.sum_image fun q hq q' hq' h => ?_).symm
          rw [Finset.coe_filter] at hq hq'
          exact injOn_blowUpToBase_compl_fibre p hp hq.2 hq'.2 h
      _ ≤ ∑ x ∈ S.erase p, g x := by
          refine Finset.sum_le_sum_of_subset fun x hx => ?_
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
          rw [Finset.mem_filter, hS', Set.Finite.mem_toFinset] at hq
          rw [Finset.mem_erase, hS, Set.Finite.mem_toFinset]
          exact ⟨hq.2, transformIdeal_support_subset Y p hp hq.1.1,
            transformIdeal_support_subset Y' p hp hq.1.2⟩
  -- above the centre
  have hon : ∑ q ∈ S'.filter (fun q => b.base q = p), g' q +
      (if 2 ≤ localIntersectionColength Y Y' p then 1 else 0) ≤ g p := by
    by_cases hpYY : p ∈ (Y.support : Set W) ∧ p ∈ (Y'.support : Set W)
    · obtain ⟨hpY, hpY'⟩ := hpYY
      have hd := hdimY hpY
      have hd' := hdimY' hpY'
      obtain ⟨y₀, hy₀⟩ : p ∈ Set.range Y.subschemeι := by rwa [Y.range_subschemeι]
      have hy₀reg := AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hreg y₀
      obtain ⟨q₀, -, hq₀⟩ := strictTransform_exceptional_unique Y hd p hp y₀ hy₀ hy₀reg
      have hpsup := mem_support_sup_of_mem hpY hpY'
      have hlt : ∀ q ∈ S'.filter (fun q => b.base q = p),
          localIntersectionColength (transformIdeal Y p hp) (transformIdeal Y' p hp) q <
            localIntersectionColength Y Y' p := by
        intro q hq
        rw [Finset.mem_filter, hS', Set.Finite.mem_toFinset] at hq
        have hqsup := mem_support_sup_of_mem hq.1.1 hq.1.2
        rw [localIntersectionColength_eq_intersectionLength _ _ q hqsup,
          localIntersectionColength_eq_intersectionLength _ _ p hpsup]
        exact intersectionLength_transformIdeal_lt Y Y' hd hd' hreg hne p hpsup hp q
          (mem_support_exceptionalIdeal_of_eq p hp q hq.2) hqsup
      have hsub : S'.filter (fun q => b.base q = p) ⊆ {q₀} := by
        intro q hq
        rw [Finset.mem_filter, hS', Set.Finite.mem_toFinset] at hq
        exact Finset.mem_singleton.mpr
          (hq₀ q ⟨hq.1.1, mem_support_exceptionalIdeal_of_eq p hp q hq.2⟩)
      rcases Finset.subset_singleton_iff.mp hsub with h | h
      · rw [h, Finset.sum_empty]
        simp only [hg]
        split_ifs <;> omega
      · rw [h, Finset.sum_singleton]
        have := hlt q₀ (by rw [h]; exact Finset.mem_singleton_self q₀)
        simp only [hg, hg']
        split_ifs <;> omega
    · have hzero : localIntersectionColength Y Y' p = 0 :=
        localIntersectionColength_eq_zero_of_notMem Y Y' p (by tauto)
      have hempty : S'.filter (fun q => b.base q = p) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun q hq hqp => ?_
        rw [hS', Set.Finite.mem_toFinset] at hq
        rcases not_and_or.mp hpYY with h | h
        · exact notMem_support_transformIdeal_of_notMem Y p hp h q hqp hq.1
        · exact notMem_support_transformIdeal_of_notMem Y' p hp h q hqp hq.2
      rw [hempty, Finset.sum_empty, hzero]
      simp
  have htotal : g p + ∑ x ∈ S.erase p, g x = ∑ x ∈ S, g x := by
    by_cases hpS : p ∈ S
    · exact Finset.add_sum_erase S g hpS
    · rw [Finset.erase_eq_of_notMem hpS]
      have : g p = 0 := by
        by_contra h
        exact hpS (hgS h)
      rw [this, zero_add]
  omega

/-- **The exceptional curve meets the strict transform of a regular configuration curve with
multiplicity at most one everywhere** ([Stacks, Tag 0BI7] part (2)), so their excess vanishes. -/
public theorem pairExcess_transformIdeal_exceptionalIdeal [IsNoetherian W]
    (hdim : topologicalKrullDim W = 2) {Y : W.IdealSheafData} (hY : IsConfigCurve Y)
    (hreg : AlgebraicGeometry.IsRegular Y.subscheme) (p : W) (hp : IsClosed ({p} : Set W))
    (hpdim : ringKrullDim (W.presheaf.stalk p) = 2) :
    pairExcess (transformIdeal Y p hp) (exceptionalIdeal (centerIdeal p hp)) = 0 := by
  have := hY.isIntegral
  refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
  by_cases hq : (blowUpToBase (centerIdeal p hp)).base q = p
  · by_cases hqT : q ∈ (transformIdeal Y p hp).support
    · have hpY : p ∈ (Y.support : Set W) := hq ▸ transformIdeal_support_subset Y p hp hqT
      have hd := hY.topologicalKrullDim_eq_one_of_ringKrullDim_eq_two hdim hpdim hpY
      obtain ⟨y₀, hy₀⟩ : p ∈ Set.range Y.subschemeι := by rwa [Y.range_subschemeι]
      have hqsup := mem_support_sup_of_mem hqT (mem_support_exceptionalIdeal_of_eq p hp q hq)
      rw [localIntersectionColength_eq_intersectionLength _ _ q hqsup,
        strictTransform_exceptional_multiplicity_one Y hd p hp y₀ hy₀
          (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hreg y₀) q hqsup]
      rfl
    · rw [localIntersectionColength_eq_zero_of_notMem _ _ q (Or.inl hqT)]
      rfl
  · rw [localIntersectionColength_exceptionalIdeal_of_ne p hp _ q hq]
    rfl

open scoped Classical in
/-- The **excess** of a finite family of closed subschemes: the sum of the excesses of its ordered
pairs of distinct members. -/
public def familyExcess (F : Finset W.IdealSheafData) : ℕ :=
  ∑ Y ∈ F, ∑ Y' ∈ F.erase Y, pairExcess Y Y'

/-- Erasing commutes with taking images under a map injective on the finite set. -/
private theorem image_erase_of_injOn [DecidableEq W.IdealSheafData] {V : Scheme.{u}}
    [DecidableEq V.IdealSheafData] {F : Finset W.IdealSheafData}
    {T : W.IdealSheafData → V.IdealSheafData} (hT : Set.InjOn T (F : Set W.IdealSheafData))
    {Y : W.IdealSheafData} (hY : Y ∈ F) : (F.image T).erase (T Y) = (F.erase Y).image T := by
  ext A
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hA, Y', hY', rfl⟩
    exact ⟨Y', ⟨fun h => hA (h ▸ rfl), hY'⟩, rfl⟩
  · rintro ⟨Y', ⟨hne, hY'⟩, rfl⟩
    exact ⟨fun h => hne (hT hY' hY h), Y', hY', rfl⟩

open scoped Classical in
/-- **The excess of a family of regular configuration curves drops under a blowup at a point of
multiplicity at least two.** Blowing up a closed point `p` with two-dimensional local ring, the
excess of the blown-up family plus the number of ordered pairs of members meeting at `p` with
multiplicity at least two is at most the excess of the family: the exceptional curve contributes
nothing, and each pair of strict transforms is controlled by
`Stacks.ResolutionOfSurfaces.pairExcess_transformIdeal_add_le`. -/
public theorem familyExcess_blowupFamily_add_le [IsNoetherian W]
    (hW : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (F : Finset W.IdealSheafData) (hF : ∀ Y ∈ F, IsConfigCurve Y)
    (hreg : ∀ Y ∈ F, AlgebraicGeometry.IsRegular Y.subscheme) (p : W)
    (hp : IsClosed ({p} : Set W)) (hpdim : ringKrullDim (W.presheaf.stalk p) = 2) :
    familyExcess (blowupFamily F p hp) +
        ∑ Y ∈ F, ∑ Y' ∈ F.erase Y,
          (if 2 ≤ localIntersectionColength Y Y' p then 1 else 0) ≤ familyExcess F := by
  have hdimF := topologicalKrullDim_eq_one_of_mem_family hdim hF hpdim
  have hinj := injOn_transformIdeal F hF p hp hdimF
  set T : W.IdealSheafData → (blowUp (centerIdeal p hp)).IdealSheafData :=
    fun Y => transformIdeal Y p hp with hT
  set E := exceptionalIdeal (centerIdeal p hp) with hE
  have hEnot : E ∉ F.image T := by
    simp only [Finset.mem_image, not_exists, not_and]
    exact fun Y hY => transformIdeal_ne_exceptionalIdeal (hF Y hY) p hp
      (genericPoint_ne_of_ringKrullDim_eq_two (hF Y hY) hpdim) (hdimF Y hY)
  have hzero : ∀ Y ∈ F, pairExcess (T Y) E = 0 := fun Y hY =>
    pairExcess_transformIdeal_exceptionalIdeal hdim (hF Y hY) (hreg Y hY) p hp hpdim
  have hnew : familyExcess (blowupFamily F p hp) =
      ∑ Y ∈ F, ∑ Y' ∈ F.erase Y, pairExcess (T Y) (T Y') := by
    rw [familyExcess, blowupFamily, Finset.sum_insert hEnot, Finset.erase_insert hEnot]
    rw [Finset.sum_eq_zero (s := F.image T) (f := fun B => pairExcess E B) (by
      intro B hB
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hB
      rw [pairExcess_comm]; exact hzero Y hY), zero_add]
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun Y hY => ?_
    have hne : T Y ≠ E := fun h => hEnot (h ▸ Finset.mem_image_of_mem T hY)
    rw [Finset.erase_insert_of_ne (Ne.symm hne), Finset.sum_insert (fun h => hEnot
      (Finset.mem_of_mem_erase h)), hzero Y hY, zero_add, image_erase_of_injOn hinj hY,
      Finset.sum_image (hinj.mono (Finset.coe_subset.mpr (Finset.erase_subset Y F)))]
  rw [hnew, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun Y hY => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun Y' hY' => ?_
  obtain ⟨hne, hY'F⟩ := Finset.mem_erase.mp hY'
  exact pairExcess_transformIdeal_add_le hW hdim (hF Y hY) (hF Y' hY'F) (hreg Y hY)
    (hreg Y' hY'F) (Ne.symm hne) p hp hpdim

open scoped Classical in
/-- The **triple points** of a family of closed subschemes: the points lying on at least three
members. -/
public def triplePoints (F : Finset W.IdealSheafData) : Set W :=
  {x | 3 ≤ (F.filter fun Y => x ∈ (Y.support : Set W)).card}

/-- A triple point lies on two distinct members of the family. -/
private theorem exists_ne_of_mem_triplePoints {F : Finset W.IdealSheafData} {x : W}
    (hx : x ∈ triplePoints F) :
    ∃ Y ∈ F, ∃ Y' ∈ F, Y ≠ Y' ∧ x ∈ (Y.support : Set W) ∧ x ∈ (Y'.support : Set W) := by
  classical
  obtain ⟨Y, hY, Y', hY', hne⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num) hx)
  rw [Finset.mem_filter] at hY hY'
  exact ⟨Y, hY.1, Y', hY'.1, hne, hY.2, hY'.2⟩

open scoped Classical in
/-- A family of configuration curves on a Noetherian surface has finitely many triple points. -/
public theorem finite_triplePoints [IsNoetherian W] (hdim : topologicalKrullDim W = 2)
    (F : Finset W.IdealSheafData) (hF : ∀ Y ∈ F, IsConfigCurve Y) :
    (triplePoints F).Finite := by
  refine (Set.Finite.biUnion (F.offDiag.finite_toSet) fun P hP =>
    (hF P.1 (Finset.mem_offDiag.mp hP).1).finite_inter_support hdim
      (hF P.2 (Finset.mem_offDiag.mp hP).2.1) (Finset.mem_offDiag.mp hP).2.2).subset ?_
  intro x hx
  obtain ⟨Y, hY, Y', hY', hne, hxY, hxY'⟩ := exists_ne_of_mem_triplePoints hx
  exact Set.mem_biUnion (x := (Y, Y')) (Finset.mem_offDiag.mpr ⟨hY, hY', hne⟩) ⟨hxY, hxY'⟩

open scoped Classical in
/-- **Blowing up a point where all multiplicities are one leaves no triple point above it.** If
two strict transforms met above the centre, their multiplicity there would be smaller than at the
centre ([Stacks, Tag 0BI7] part (3)), which is one; but it is positive. -/
public theorem notMem_triplePoints_blowupFamily [IsNoetherian W]
    (_hW : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (F : Finset W.IdealSheafData) (hF : ∀ Y ∈ F, IsConfigCurve Y)
    (hreg : ∀ Y ∈ F, AlgebraicGeometry.IsRegular Y.subscheme) (p : W)
    (hp : IsClosed ({p} : Set W)) (hpdim : ringKrullDim (W.presheaf.stalk p) = 2)
    (hone : ∀ Y ∈ F, ∀ Y' ∈ F, Y ≠ Y' → localIntersectionColength Y Y' p ≤ 1)
    (q : blowUp (centerIdeal p hp)) (hq : (blowUpToBase (centerIdeal p hp)).base q = p) :
    q ∉ triplePoints (blowupFamily F p hp) := by
  intro hq3
  have hdimF := topologicalKrullDim_eq_one_of_mem_family hdim hF hpdim
  set S := (blowupFamily F p hp).filter fun A => q ∈ (A.support : Set _) with hS
  have hcard : 1 < (S.erase (exceptionalIdeal (centerIdeal p hp))).card := by
    have h3 : 3 ≤ S.card := hq3
    have := Finset.pred_card_le_card_erase (s := S) (a := exceptionalIdeal (centerIdeal p hp))
    omega
  obtain ⟨A, hA, A', hA', hAA'⟩ := Finset.one_lt_card.mp hcard
  have hmem : ∀ B ∈ S.erase (exceptionalIdeal (centerIdeal p hp)),
      ∃ Y ∈ F, transformIdeal Y p hp = B ∧ q ∈ ((transformIdeal Y p hp).support : Set _) := by
    intro B hB
    obtain ⟨hBE, hB⟩ := Finset.mem_erase.mp hB
    rw [hS, Finset.mem_filter, blowupFamily, Finset.mem_insert, Finset.mem_image] at hB
    obtain ⟨(rfl | ⟨Y, hY, rfl⟩), hqB⟩ := hB
    · exact absurd rfl hBE
    · exact ⟨Y, hY, rfl, hqB⟩
  obtain ⟨Y, hY, rfl, hqY⟩ := hmem A hA
  obtain ⟨Y', hY', rfl, hqY'⟩ := hmem A' hA'
  have hne : Y ≠ Y' := fun h => hAA' (h ▸ rfl)
  have hpY : p ∈ (Y.support : Set W) := hq ▸ transformIdeal_support_subset Y p hp hqY
  have hpY' : p ∈ (Y'.support : Set W) := hq ▸ transformIdeal_support_subset Y' p hp hqY'
  have hd := hdimF Y hY hpY
  have hd' := hdimF Y' hY' hpY'
  have := (hF Y hY).isIntegral
  have := (hF Y' hY').isIntegral
  have hpsup := mem_support_sup_of_mem hpY hpY'
  have hqsup := mem_support_sup_of_mem hqY hqY'
  have hlt := intersectionLength_transformIdeal_lt Y Y' hd hd' (hreg Y hY) hne p hpsup hp q
    (mem_support_exceptionalIdeal_of_eq p hp q hq) hqsup
  have : IsNoetherian (blowUp (centerIdeal p hp)) := isNoetherian_blowUp _
  obtain ⟨hTint, hTd⟩ := transformIdeal_integral_curve Y hd p hp
  obtain ⟨hTint', hTd'⟩ := transformIdeal_integral_curve Y' hd' p hp
  have hTne : transformIdeal Y p hp ≠ transformIdeal Y' p hp := hAA'
  have hpos := intersectionLength_pos _ _ hTd hTd' hTne q hqsup
  have hle := hone Y hY Y' hY' hne
  rw [localIntersectionColength_eq_intersectionLength _ _ p hpsup] at hle
  omega

open scoped Classical in
/-- **The number of triple points drops when one is blown up while all multiplicities there are
one**, and never grows under such a blowup: off the centre the blowup changes nothing, and above it
there are no triple points. -/
public theorem ncard_triplePoints_blowupFamily_add_le [IsNoetherian W]
    (hW : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (F : Finset W.IdealSheafData) (hF : ∀ Y ∈ F, IsConfigCurve Y)
    (hreg : ∀ Y ∈ F, AlgebraicGeometry.IsRegular Y.subscheme) (p : W)
    (hp : IsClosed ({p} : Set W)) (hpdim : ringKrullDim (W.presheaf.stalk p) = 2)
    (hone : ∀ Y ∈ F, ∀ Y' ∈ F, Y ≠ Y' → localIntersectionColength Y Y' p ≤ 1) :
    (triplePoints (blowupFamily F p hp)).ncard + (if p ∈ triplePoints F then 1 else 0) ≤
      (triplePoints F).ncard := by
  set b := blowUpToBase (centerIdeal p hp) with hb
  have hfin := finite_triplePoints hdim F hF
  have hmaps : ∀ q ∈ triplePoints (blowupFamily F p hp), b.base q ∈ triplePoints F \ {p} := by
    intro q hq
    have hqp : b.base q ≠ p := fun h =>
      notMem_triplePoints_blowupFamily hW hdim F hF hreg p hp hpdim hone q h hq
    refine ⟨?_, hqp⟩
    have hsub : ((blowupFamily F p hp).filter fun A => q ∈ (A.support : Set _)) ⊆
        (F.filter fun Y => b.base q ∈ (Y.support : Set W)).image
          fun Y => transformIdeal Y p hp := by
      intro A hA
      rw [Finset.mem_filter, blowupFamily, Finset.mem_insert, Finset.mem_image] at hA
      obtain ⟨(rfl | ⟨Y, hY, rfl⟩), hqA⟩ := hA
      · exact absurd ((mem_exceptionalIdeal_support_iff p hp q).mp hqA) hqp
      · exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
          ⟨hY, transformIdeal_support_subset Y p hp hqA⟩)
    have h3 : 3 ≤ ((blowupFamily F p hp).filter fun A => q ∈ (A.support : Set _)).card := hq
    exact h3.trans ((Finset.card_le_card hsub).trans Finset.card_image_le)
  have hle := Set.ncard_le_ncard_of_injOn b.base hmaps
    ((injOn_blowUpToBase_compl_fibre p hp).mono fun q hq h =>
      (hmaps q hq).2 h) (hfin.diff)
  split_ifs with hpT
  · have := Set.ncard_sdiff_singleton_add_one hpT hfin
    omega
  · rw [Set.diff_singleton_eq_self hpT] at hle
    omega

/-- Every member of the blown-up family of a family of regular configuration curves is regular. -/
public theorem isRegular_of_mem_blowupFamily [IsNoetherian W]
    (hW : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (F : Finset W.IdealSheafData) (hF : ∀ Y ∈ F, IsConfigCurve Y)
    (hreg : ∀ Y ∈ F, AlgebraicGeometry.IsRegular Y.subscheme) (p : W)
    (hp : IsClosed ({p} : Set W)) (hpdim : ringKrullDim (W.presheaf.stalk p) = 2)
    (A : (blowUp (centerIdeal p hp)).IdealSheafData) (hA : A ∈ blowupFamily F p hp) :
    AlgebraicGeometry.IsRegular A.subscheme := by
  by_contra hAreg
  obtain ⟨Y, hY, hYreg, -⟩ := mem_image_of_not_isRegular_of_mem_blowupFamily hW hdim F hF p hp
    hpdim (topologicalKrullDim_eq_one_of_mem_family hdim hF hpdim) A hA hAreg
  exact hYreg (hreg Y hY)

/-- A point on two distinct configuration curves of a Noetherian surface is closed with a
two-dimensional local ring. -/
public theorem IsConfigCurve.isClosed_and_ringKrullDim_of_mem_inter [IsNoetherian W]
    (hdim : topologicalKrullDim W = 2) {Y Y' : W.IdealSheafData} (hY : IsConfigCurve Y)
    (hY' : IsConfigCurve Y') (hne : Y ≠ Y') {x : W} (hx : x ∈ (Y.support : Set W))
    (hx' : x ∈ (Y'.support : Set W)) :
    IsClosed ({x} : Set W) ∧ ringKrullDim (W.presheaf.stalk x) = 2 := by
  have := hY.isIntegral
  have := hY'.isIntegral
  exact (finite_inter_support_of_ne hdim Y Y' hY.isEffectiveCartierDivisor
    hY'.isEffectiveCartierDivisor hne).2 x ⟨hx, hx'⟩

open scoped Classical in
/-- **The intersection-multiplicity iteration of [Stacks, Tag 0BIC].** A family of regular
configuration curves on a regular Noetherian surface is carried by finitely many blowups at closed
points to a family of regular configuration curves, covering the inverse image of the union of the
family, any two members of which meet with multiplicity at most one and no three of which have a
common point.

The induction is on the excess `∑ (m_x(Y ∩ Y') - 1)` followed by the number of triple points, in
the lexicographic order: blowing up a point of multiplicity at least two lowers the excess, and
blowing up a triple point once all multiplicities are one keeps the excess and lowers the number
of triple points. -/
public theorem exists_pointBlowupChain_transverse :
    ∀ (m : ℕ ×ₗ ℕ) (W : Scheme.{u}) [IsNoetherian W], AlgebraicGeometry.IsRegular W →
      topologicalKrullDim W = 2 → ∀ (F : Finset W.IdealSheafData), (∀ Y ∈ F, IsConfigCurve Y) →
      (∀ Y ∈ F, AlgebraicGeometry.IsRegular Y.subscheme) →
      toLex (familyExcess F, (triplePoints F).ncard) = m →
      ∃ (V : Scheme.{u}) (f : V ⟶ W) (F' : Finset V.IdealSheafData),
        PointBlowupChain W Set.univ V f ∧ (∀ A ∈ F', IsConfigCurve A) ∧
        (∀ A ∈ F', AlgebraicGeometry.IsRegular A.subscheme) ∧
        (⋃ A ∈ F', (A.support : Set V)) = f.base ⁻¹' ⋃ Y ∈ F, (Y.support : Set W) ∧
        (∀ A ∈ F', ∀ A' ∈ F', A ≠ A' → ∀ x, localIntersectionColength A A' x ≤ 1) ∧
        triplePoints F' = ∅ := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  intro W _ hW hdim F hF hreg hm
  -- one blowup at a point lying on two distinct members, followed by the induction hypothesis
  have step : ∀ (x : W) (hx : IsClosed ({x} : Set W)),
      ringKrullDim (W.presheaf.stalk x) = 2 → (∃ Y ∈ F, x ∈ (Y.support : Set W)) →
      toLex (familyExcess (blowupFamily F x hx),
        (triplePoints (blowupFamily F x hx)).ncard) < m →
      ∃ (V : Scheme.{u}) (f : V ⟶ W) (F' : Finset V.IdealSheafData),
        PointBlowupChain W Set.univ V f ∧ (∀ A ∈ F', IsConfigCurve A) ∧
        (∀ A ∈ F', AlgebraicGeometry.IsRegular A.subscheme) ∧
        (⋃ A ∈ F', (A.support : Set V)) = f.base ⁻¹' ⋃ Y ∈ F, (Y.support : Set W) ∧
        (∀ A ∈ F', ∀ A' ∈ F', A ≠ A' → ∀ x, localIntersectionColength A A' x ≤ 1) ∧
        triplePoints F' = ∅ := by
    intro x hx hxdim hxF hlt
    have : IsNoetherian (blowUp (centerIdeal x hx)) := isNoetherian_blowUp _
    obtain ⟨hW', hdim'⟩ :=
      isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton W hW hdim x hx
    obtain ⟨V, f, F', hc, hF', hreg', hU', hone', htr'⟩ := ih _ hlt (blowUp (centerIdeal x hx))
      hW' hdim' (blowupFamily F x hx)
      (isConfigCurve_of_mem_blowupFamily hW hdim F hF x hx hxdim
        (topologicalKrullDim_eq_one_of_mem_family hdim hF hxdim))
      (isRegular_of_mem_blowupFamily hW hdim F hF hreg x hx hxdim) rfl
    refine ⟨V, f ≫ blowUpToBase (centerIdeal x hx), F', ?_, hF', hreg', ?_, hone', htr'⟩
    · exact ((PointBlowupChain.refl (X := W) (T := Set.univ)).step x hx (Set.mem_univ _)).comp
        hc fun _ _ => Set.mem_univ _
    · rw [hU', iUnion_support_blowupFamily F x hx hxF, Scheme.Hom.comp_base, TopCat.coe_comp,
        Set.preimage_comp]
  by_cases hbad : ∃ Y ∈ F, ∃ Y' ∈ F, Y ≠ Y' ∧ ∃ x, 2 ≤ localIntersectionColength Y Y' x
  · obtain ⟨Y, hY, Y', hY', hne, x, hx2⟩ := hbad
    have hxYY : x ∈ (Y.support : Set W) ∧ x ∈ (Y'.support : Set W) := by
      by_contra h
      rw [localIntersectionColength_eq_zero_of_notMem Y Y' x (by tauto)] at hx2
      omega
    obtain ⟨hxc, hxdim⟩ :=
      (hF Y hY).isClosed_and_ringKrullDim_of_mem_inter hdim (hF Y' hY') hne hxYY.1 hxYY.2
    refine step x hxc hxdim ⟨Y, hY, hxYY.1⟩ ?_
    have hdrop := familyExcess_blowupFamily_add_le hW hdim F hF hreg x hxc hxdim
    have hpos : 1 ≤ ∑ Z ∈ F, ∑ Z' ∈ F.erase Z,
        (if 2 ≤ localIntersectionColength Z Z' x then 1 else 0) := by
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hY)
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨Ne.symm hne, hY'⟩))
      simp [hx2]
    rw [← hm, Prod.Lex.lt_iff]
    simp only [ofLex_toLex]
    exact Or.inl (by omega)
  push Not at hbad
  by_cases htr : (triplePoints F).Nonempty
  · obtain ⟨x, hx⟩ := htr
    obtain ⟨Y, hY, Y', hY', hne, hxY, hxY'⟩ := exists_ne_of_mem_triplePoints hx
    obtain ⟨hxc, hxdim⟩ :=
      (hF Y hY).isClosed_and_ringKrullDim_of_mem_inter hdim (hF Y' hY') hne hxY hxY'
    have hone : ∀ Z ∈ F, ∀ Z' ∈ F, Z ≠ Z' → localIntersectionColength Z Z' x ≤ 1 :=
      fun Z hZ Z' hZ' hZZ' => by
        have := hbad Z hZ Z' hZ' hZZ' x
        omega
    refine step x hxc hxdim ⟨Y, hY, hxY⟩ ?_
    have hdrop := familyExcess_blowupFamily_add_le hW hdim F hF hreg x hxc hxdim
    have htri := ncard_triplePoints_blowupFamily_add_le hW hdim F hF hreg x hxc hxdim hone
    rw [if_pos hx] at htri
    rw [← hm, Prod.Lex.lt_iff]
    simp only [ofLex_toLex]
    by_cases hlt : familyExcess (blowupFamily F x hxc) < familyExcess F
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, by omega⟩
  · refine ⟨W, 𝟙 W, F, .refl, hF, hreg, by simp, fun A hA A' hA' hne x => ?_,
      Set.not_nonempty_iff_eq_empty.mp htr⟩
    have := hbad A hA A' hA' hne x
    omega

end Generic

end Stacks.ResolutionOfSurfaces

end
