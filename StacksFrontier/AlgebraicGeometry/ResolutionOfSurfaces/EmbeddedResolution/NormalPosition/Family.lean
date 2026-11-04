module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveFamilyResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.ExceptionalFibreGlobal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.StrictTransformSupport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.LocalDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.OffFibre
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveFamilyResolution

/-!
# A finite family of curves on a regular surface under one blowup at a closed point

Let `W` be a regular Noetherian scheme of dimension two and let `F` be a finite set of closed
subschemes of `W`, each an integral effective Cartier divisor which is either regular or a curve
satisfying condition (3) of [Stacks, Tag 0BI4]. Blowing `W` up at a closed point `p` with
two-dimensional local ring lying on one of them, the strict transforms of the members of `F`
together with the exceptional divisor form a family of the same kind on the blowup, whose union
is the inverse image of the union of `F`. This is the bookkeeping behind the first paragraph of
the proof of [Stacks, Tag 0BIC]: "the inverse image `Z'` of `Z` is supported on the strict
transform of `Z` and the exceptional divisor", and the strict transform of a component "is either
equal to `Y` or the blowup of `Y` at `p`".

## Main definitions

* `Stacks.ResolutionOfSurfaces.IsResolvable` — condition (3) of [Stacks, Tag 0BI4]: a finite
  sequence of blowups at closed points with regular source.
* `Stacks.ResolutionOfSurfaces.IsConfigCurve` — an integral effective Cartier divisor which is
  regular or a resolvable curve.
* `Stacks.ResolutionOfSurfaces.blowupFamily` — the strict transforms of a family together with
  the exceptional divisor.

## Main results

* `Stacks.ResolutionOfSurfaces.isConfigCurve_transformIdeal` and
  `Stacks.ResolutionOfSurfaces.isConfigCurve_exceptionalIdeal` — the members of the new family
  are again configuration curves.
* `Stacks.ResolutionOfSurfaces.iUnion_support_blowupFamily` — the union of the new family is the
  inverse image of the union of the old one.
* `Stacks.ResolutionOfSurfaces.injOn_transformIdeal` — distinct members have distinct strict
  transforms, none of which is the exceptional divisor.

## References

* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
* [Stacks Project, Tag 0BI7](https://stacks.math.columbia.edu/tag/0BI7)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

/-- A closed subscheme is **resolvable** when a finite sequence of blowups of it at closed points
has regular source: condition (3) of [Stacks, Tag 0BI4]. -/
public def IsResolvable {W : Scheme.{u}} (Y : W.IdealSheafData) : Prop :=
  ∃ (P : Scheme.{u}) (g : P ⟶ Y.subscheme),
    PointBlowupChain Y.subscheme Set.univ P g ∧ AlgebraicGeometry.IsRegular P

/-- A **configuration curve** on a scheme: an integral effective Cartier divisor which is either
regular or a resolvable one-dimensional scheme. -/
public structure IsConfigCurve {W : Scheme.{u}} (Y : W.IdealSheafData) : Prop where
  isIntegral : IsIntegral Y.subscheme
  isEffectiveCartierDivisor : IsEffectiveCartierDivisor Y
  isRegular_or : AlgebraicGeometry.IsRegular Y.subscheme ∨
    (topologicalKrullDim Y.subscheme = 1 ∧ IsResolvable Y)

/-- **A chain of blowups at closed points of a regular Noetherian scheme of dimension two ends in
a regular Noetherian scheme of dimension two**: one step is the global form of [Stacks, Tag 0AGR],
`AlgebraicGeometry.isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton`. -/
public theorem PointBlowupChain.isRegular_and_topologicalKrullDim {X V : Scheme.{u}}
    [IsNoetherian X] {T : Set X} {f : V ⟶ X} (h : PointBlowupChain X T V f)
    (hX : AlgebraicGeometry.IsRegular X) (hdim : topologicalKrullDim X = 2) :
    AlgebraicGeometry.IsRegular V ∧ topologicalKrullDim V = 2 := by
  induction h with
  | refl => exact ⟨hX, hdim⟩
  | step hh w hw hwT ih =>
      exact @isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton
        _ (isNoetherian_of_pointBlowupChain hh) ih.1 ih.2 w hw

open scoped Classical in
/-- The family obtained from a finite family of closed subschemes by one blowup at a closed point
`p`: the strict transforms of its members together with the exceptional divisor. -/
public def blowupFamily {W : Scheme.{u}} (F : Finset W.IdealSheafData) (p : W)
    (hp : IsClosed ({p} : Set W)) : Finset (blowUp (centerIdeal p hp)).IdealSheafData :=
  insert (exceptionalIdeal (centerIdeal p hp)) (F.image fun Y => transformIdeal Y p hp)

section Generic

variable {W : Scheme.{u}}

/-- The generic point of an integral closed subscheme, as a point of the ambient scheme. -/
local notation3 "gen " Y:max => Scheme.IdealSheafData.subschemeι Y
  (_root_.genericPoint (Scheme.IdealSheafData.subscheme Y))

/-- The local ring of the ambient scheme at the generic point of an integral effective Cartier
divisor is one-dimensional. -/
public theorem ringKrullDim_stalk_genericPoint_of_isConfigCurve [IsLocallyNoetherian W]
    {Y : W.IdealSheafData} (hY : IsConfigCurve Y) :
    letI := hY.isIntegral
    ringKrullDim (W.presheaf.stalk (gen Y)) = 1 := by
  have := hY.isIntegral
  refine ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor Y hY.isEffectiveCartierDivisor
    _ ⟨⟨Set.univ, ?_⟩, ?_⟩
  · simpa using (irreducibleComponents_eq_singleton (X := Y.subscheme)).symm ▸
      Set.mem_singleton _
  · simpa using genericPoint_spec Y.subscheme

/-! ### The exceptional divisor -/

/-- The support of the exceptional divisor of the blowup at a closed point is the fibre over that
point. -/
public theorem coe_support_exceptionalIdeal_centerIdeal (p : W) (hp : IsClosed ({p} : Set W)) :
    ((exceptionalIdeal (centerIdeal p hp)).support : Set (blowUp (centerIdeal p hp))) =
      (blowUpToBase (centerIdeal p hp)).base ⁻¹' {p} :=
  Set.ext (mem_exceptionalIdeal_support_iff p hp)

/-- **The exceptional divisor of the blowup of a regular Noetherian surface at a closed point with
two-dimensional local ring is a configuration curve**: it is an effective Cartier divisor, it is
regular, and it is irreducible. -/
public theorem isConfigCurve_exceptionalIdeal [IsNoetherian W] (hW : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (p : W) (hp : IsClosed ({p} : Set W))
    (hpdim : ringKrullDim (W.presheaf.stalk p) = 2) :
    IsConfigCurve (exceptionalIdeal (centerIdeal p hp)) := by
  have hreg : AlgebraicGeometry.IsRegular (exceptionalIdeal (centerIdeal p hp)).subscheme :=
    isRegular_exceptionalDivisor_vanishingIdeal_singleton hW hdim p hp hpdim
  have : IsReduced (exceptionalIdeal (centerIdeal p hp)).subscheme :=
    AlgebraicGeometry.isReduced_of_isRegular hreg
  have hirr : IsIrreducible (Set.range (exceptionalIdeal (centerIdeal p hp)).subschemeι) := by
    rw [(exceptionalIdeal (centerIdeal p hp)).range_subschemeι,
      coe_support_exceptionalIdeal_centerIdeal]
    exact isIrreducible_preimage_singleton_blowUpToBase_vanishingIdeal_singleton p hp
      (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hW p) hpdim
  have : IrreducibleSpace (exceptionalIdeal (centerIdeal p hp)).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme _ _ hirr
  exact ⟨isIntegral_of_irreducibleSpace_of_isReduced _,
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _, Or.inl hreg⟩

/-! ### Supports of strict transforms -/

/-- Off the exceptional fibre, a point lies on the strict transform exactly when its image lies
on the subscheme. -/
public theorem mem_support_transformIdeal_iff_of_ne [IsNoetherian W] (Y : W.IdealSheafData)
    (p : W) (hp : IsClosed ({p} : Set W)) (q : blowUp (centerIdeal p hp))
    (hq : (blowUpToBase (centerIdeal p hp)).base q ≠ p) :
    q ∈ ((transformIdeal Y p hp).support : Set _) ↔
      (blowUpToBase (centerIdeal p hp)).base q ∈ (Y.support : Set W) := by
  refine ⟨fun h => transformIdeal_support_subset Y p hp h, fun h => ?_⟩
  rw [coe_support_transformIdeal]
  exact subset_closure ⟨h, hq⟩

/-- A strict transform of a subscheme not passing through the centre misses the exceptional
fibre. -/
public theorem notMem_support_transformIdeal_of_notMem (Y : W.IdealSheafData)
    (p : W) (hp : IsClosed ({p} : Set W)) (hpY : p ∉ (Y.support : Set W))
    (q : blowUp (centerIdeal p hp)) (hq : (blowUpToBase (centerIdeal p hp)).base q = p) :
    q ∉ ((transformIdeal Y p hp).support : Set _) := fun h =>
  hpY (hq ▸ transformIdeal_support_subset Y p hp h)

/-- **The union of the blown-up family is the inverse image of the union of the family**, as soon
as the centre lies on a member. -/
public theorem iUnion_support_blowupFamily [IsNoetherian W] (F : Finset W.IdealSheafData)
    (p : W) (hp : IsClosed ({p} : Set W)) (hpF : ∃ Y ∈ F, p ∈ (Y.support : Set W)) :
    ⋃ A ∈ blowupFamily F p hp, (A.support : Set (blowUp (centerIdeal p hp))) =
      (blowUpToBase (centerIdeal p hp)).base ⁻¹' ⋃ Y ∈ F, (Y.support : Set W) := by
  classical
  ext q
  simp only [blowupFamily, Finset.mem_insert, Finset.mem_image, Set.mem_iUnion, Set.mem_preimage,
    exists_prop]
  constructor
  · rintro ⟨A, rfl | ⟨Y, hY, rfl⟩, hqA⟩
    · obtain ⟨Y, hY, hpY⟩ := hpF
      rw [coe_support_exceptionalIdeal_centerIdeal, Set.mem_preimage,
        Set.mem_singleton_iff] at hqA
      exact ⟨Y, hY, by rwa [hqA]⟩
    · exact ⟨Y, hY, transformIdeal_support_subset Y p hp hqA⟩
  · rintro ⟨Y, hY, hqY⟩
    by_cases hq : (blowUpToBase (centerIdeal p hp)).base q = p
    · refine ⟨_, Or.inl rfl, ?_⟩
      rwa [coe_support_exceptionalIdeal_centerIdeal]
    · exact ⟨_, Or.inr ⟨Y, hY, rfl⟩, (mem_support_transformIdeal_iff_of_ne Y p hp q hq).mpr hqY⟩

/-! ### The generic point of a strict transform -/

/-- The generic point of an integral closed subscheme lies in its support. -/
private theorem genericPoint_mem_support (Y : W.IdealSheafData) [IsIntegral Y.subscheme] :
    gen Y ∈ (Y.support : Set W) := by
  rw [← Y.range_subschemeι]
  exact ⟨_, rfl⟩

/-- The generic point of an integral closed subscheme specializes to every point of its support. -/
private theorem genericPoint_specializes_of_mem_support (Y : W.IdealSheafData)
    [IsIntegral Y.subscheme] {x : W} (hx : x ∈ (Y.support : Set W)) : gen Y ⤳ x := by
  rw [← Y.range_subschemeι] at hx
  obtain ⟨t, rfl⟩ := hx
  exact ((genericPoint_spec Y.subscheme).specializes (Set.mem_univ t)).map
    Y.subschemeι.continuous

/-- **The generic point of a strict transform lies over the generic point of the curve**, when
the curve's generic point is not the centre. -/
public theorem blowUpToBase_genericPoint_transformIdeal [IsNoetherian W] (Y : W.IdealSheafData)
    [IsIntegral Y.subscheme] (p : W) (hp : IsClosed ({p} : Set W))
    [IsIntegral (transformIdeal Y p hp).subscheme] (hgen : gen Y ≠ p) :
    (blowUpToBase (centerIdeal p hp)).base (gen (transformIdeal Y p hp)) = gen Y := by
  set b := blowUpToBase (centerIdeal p hp)
  have hηsupp : gen Y ∉ ((centerIdeal p hp).support : Set W) := by
    rwa [show ((centerIdeal p hp).support : Set W) = {p} from
      Scheme.IdealSheafData.coe_support_vanishingIdeal _]
  obtain ⟨q₀, hq₀⟩ := exists_blowUpToBase_eq_of_notMem_support (centerIdeal p hp) hηsupp
  have hq₀T : q₀ ∈ ((transformIdeal Y p hp).support : Set _) := by
    refine (mem_support_transformIdeal_iff_of_ne Y p hp q₀ (by rwa [hq₀])).mpr ?_
    rw [hq₀]
    exact genericPoint_mem_support Y
  have hspec₂ : b.base (gen (transformIdeal Y p hp)) ⤳ gen Y := by
    rw [← hq₀]
    exact (genericPoint_specializes_of_mem_support _ hq₀T).map b.continuous
  exact (hspec₂.antisymm (genericPoint_specializes_of_mem_support Y
    (transformIdeal_support_subset Y p hp (genericPoint_mem_support _)))).eq

/-- **The strict transform of an integral effective Cartier divisor on a regular Noetherian
surface is an effective Cartier divisor**, when it is integral and the centre is not the generic
point of the divisor: its generic point lies off the exceptional fibre, over the generic point of
the divisor, so has a one-dimensional local ring, and the local rings of the blowup are regular,
hence factorial. -/
public theorem isEffectiveCartierDivisor_transformIdeal [IsNoetherian W]
    (hW : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    {Y : W.IdealSheafData} (hY : IsConfigCurve Y) (p : W) (hp : IsClosed ({p} : Set W))
    [IsIntegral (transformIdeal Y p hp).subscheme] (hgen : (letI := hY.isIntegral; gen Y) ≠ p) :
    IsEffectiveCartierDivisor (transformIdeal Y p hp) := by
  have := hY.isIntegral
  have : IsNoetherian (blowUp (centerIdeal p hp)) := isNoetherian_blowUp _
  have hreg : AlgebraicGeometry.IsRegular (blowUp (centerIdeal p hp)) :=
    (isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton W hW hdim p hp).1
  have hbase := blowUpToBase_genericPoint_transformIdeal Y p hp hgen
  have : IsIso ((blowUpToBase (centerIdeal p hp)).stalkMap (gen (transformIdeal Y p hp))) :=
    isIso_stalkMap_blowUpToBase_of_ne (centerIdeal p hp) p (coe_support_centerIdeal p hp) _
      (by rwa [hbase])
  have hstalk : ringKrullDim ((blowUp (centerIdeal p hp)).presheaf.stalk
      (gen (transformIdeal Y p hp))) = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv (asIso ((blowUpToBase (centerIdeal p hp)).stalkMap
      (gen (transformIdeal Y p hp)))).commRingCatIsoToRingEquiv, hbase]
    exact ringKrullDim_stalk_genericPoint_of_isConfigCurve hY
  refine isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid _ ?_
    fun x _ => by
      have := AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hreg x
      exact IsRegularLocalRing.uniqueFactorizationMonoid _
  · rw [Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight]
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hstalk
    exact_mod_cast hstalk

/-! ### Strict transforms of configuration curves -/

/-- **The strict transform of a configuration curve is a configuration curve.** Through the
centre, a curve is one-dimensional and its strict transform is the blowup of it at the centre,
which is regular if the curve is ([Stacks, Tag 0BI7] part (1)) and resolvable if the curve is
(condition (3) of [Stacks, Tag 0BI4] passes to a blowup); off the centre the strict transform is
isomorphic to the curve. -/
public theorem isConfigCurve_transformIdeal [IsNoetherian W] (hW : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) {Y : W.IdealSheafData} (hY : IsConfigCurve Y) (p : W)
    (hp : IsClosed ({p} : Set W)) (hgen : (letI := hY.isIntegral; gen Y) ≠ p)
    (hdimY : p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1) :
    IsConfigCurve (transformIdeal Y p hp) := by
  have := hY.isIntegral
  have key : IsIntegral (transformIdeal Y p hp).subscheme ∧
      (AlgebraicGeometry.IsRegular (transformIdeal Y p hp).subscheme ∨
        (topologicalKrullDim (transformIdeal Y p hp).subscheme = 1 ∧
          IsResolvable (transformIdeal Y p hp))) := by
    by_cases hpY : p ∈ (Y.support : Set W)
    · have hd := hdimY hpY
      obtain ⟨hint, hd₁⟩ := transformIdeal_integral_curve Y hd p hp
      refine ⟨hint, ?_⟩
      rcases hY.isRegular_or with hr | ⟨-, hres⟩
      · exact Or.inl (transformIdeal_regular_curve Y hd hr p hp).2.2
      · exact Or.inr ⟨hd₁,
          exists_pointBlowupChain_isRegular_transformIdeal Y inferInstance hd hres p hp⟩
    · have hiso := transformToCurve_isIso_of_notMem_support Y p hp hpY
      obtain ⟨e⟩ := nonempty_transformIdeal_subscheme_iso_self Y p hp hiso
      refine ⟨IsIntegral.of_isIso e.inv, ?_⟩
      rcases hY.isRegular_or with hr | ⟨hd, hres⟩
      · exact Or.inl (isRegular_of_isIso e.hom hr)
      · exact Or.inr ⟨(topologicalKrullDim_eq_of_iso e).trans hd,
          exists_pointBlowupChain_isRegular_transformIdeal Y inferInstance hd hres p hp⟩
  have := key.1
  exact ⟨key.1, isEffectiveCartierDivisor_transformIdeal hW hdim hY p hp hgen, key.2⟩

/-- The image under the blowup of the support of the strict transform of a configuration curve is
the support of the curve. -/
public theorem image_support_transformIdeal [IsNoetherian W] {Y : W.IdealSheafData}
    (hY : IsConfigCurve Y) (p : W) (hp : IsClosed ({p} : Set W))
    (hdimY : p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1) :
    (blowUpToBase (centerIdeal p hp)).base '' ((transformIdeal Y p hp).support : Set _) =
      (Y.support : Set W) := by
  have := hY.isIntegral
  refine image_transformIdeal_support_eq Y p hp ?_
  by_cases hpY : p ∈ (Y.support : Set W)
  · exact surjective_transformToCurve Y (hdimY hpY) p hp
  · have := transformToCurve_isIso_of_notMem_support Y p hp hpY
    exact (transformToCurve Y p hp).homeomorph.surjective

/-- **Distinct configuration curves have distinct strict transforms.** -/
public theorem injOn_transformIdeal [IsNoetherian W] (F : Finset W.IdealSheafData)
    (hF : ∀ Y ∈ F, IsConfigCurve Y) (p : W) (hp : IsClosed ({p} : Set W))
    (hdimF : ∀ Y ∈ F, p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1) :
    Set.InjOn (fun Y => transformIdeal Y p hp) (F : Set W.IdealSheafData) := by
  intro Y hY Y' hY' heq
  have := (hF Y hY).isIntegral
  have := (hF Y' hY').isIntegral
  refine eq_of_support_eq Y Y' (SetLike.coe_injective ?_)
  rw [← image_support_transformIdeal (hF Y hY) p hp (hdimF Y hY),
    ← image_support_transformIdeal (hF Y' hY') p hp (hdimF Y' hY')]
  exact congrArg (fun A : (blowUp (centerIdeal p hp)).IdealSheafData =>
    (blowUpToBase (centerIdeal p hp)).base '' (A.support : Set _)) heq

/-- **No strict transform of a configuration curve is the exceptional divisor**, as long as the
centre is not the generic point of the curve. -/
public theorem transformIdeal_ne_exceptionalIdeal [IsNoetherian W] {Y : W.IdealSheafData}
    (hY : IsConfigCurve Y) (p : W) (hp : IsClosed ({p} : Set W))
    (hgen : (letI := hY.isIntegral; gen Y) ≠ p)
    (hdimY : p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1) :
    transformIdeal Y p hp ≠ exceptionalIdeal (centerIdeal p hp) := by
  have := hY.isIntegral
  intro h
  have himage := image_support_transformIdeal hY p hp hdimY
  rw [h, coe_support_exceptionalIdeal_centerIdeal] at himage
  have hmem := genericPoint_mem_support Y
  rw [← himage] at hmem
  obtain ⟨q, hq, hqη⟩ := hmem
  exact hgen (hqη.symm.trans hq)

open scoped Classical in
/-- The blown-up family has one more member than the family. -/
public theorem card_blowupFamily [IsNoetherian W] (F : Finset W.IdealSheafData)
    (hF : ∀ Y ∈ F, IsConfigCurve Y) (p : W) (hp : IsClosed ({p} : Set W))
    (hgenF : ∀ Y (hY : Y ∈ F), (letI := (hF Y hY).isIntegral; gen Y) ≠ p)
    (hdimF : ∀ Y ∈ F, p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1) :
    (blowupFamily F p hp).card = F.card + 1 := by
  rw [blowupFamily, Finset.card_insert_of_notMem, Finset.card_image_of_injOn
    (injOn_transformIdeal F hF p hp hdimF)]
  simp only [Finset.mem_image, not_exists, not_and]
  exact fun Y hY => transformIdeal_ne_exceptionalIdeal (hF Y hY) p hp (hgenF Y hY) (hdimF Y hY)

/-- The strict transform of a regular configuration curve is regular. -/
public theorem isRegular_transformIdeal [IsNoetherian W] {Y : W.IdealSheafData}
    (hY : IsConfigCurve Y) (hreg : AlgebraicGeometry.IsRegular Y.subscheme) (p : W)
    (hp : IsClosed ({p} : Set W))
    (hdimY : p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1) :
    AlgebraicGeometry.IsRegular (transformIdeal Y p hp).subscheme := by
  have := hY.isIntegral
  by_cases hpY : p ∈ (Y.support : Set W)
  · exact (transformIdeal_regular_curve Y (hdimY hpY) hreg p hp).2.2
  · have hiso := transformToCurve_isIso_of_notMem_support Y p hp hpY
    obtain ⟨e⟩ := nonempty_transformIdeal_subscheme_iso_self Y p hp hiso
    exact isRegular_of_isIso e.hom hreg

/-- The generic point of a configuration curve is not a point with two-dimensional local ring. -/
public theorem genericPoint_ne_of_ringKrullDim_eq_two [IsLocallyNoetherian W]
    {Y : W.IdealSheafData} (hY : IsConfigCurve Y) {p : W}
    (hpdim : ringKrullDim (W.presheaf.stalk p) = 2) :
    (letI := hY.isIntegral; gen Y) ≠ p := by
  intro h
  have h1 := ringKrullDim_stalk_genericPoint_of_isConfigCurve hY
  rw [h, hpdim] at h1
  exact absurd h1 (by decide)

/-- **One blowup at a closed point with two-dimensional local ring carries a family of
configuration curves to a family of configuration curves**: the strict transforms of the members
together with the exceptional divisor. -/
public theorem isConfigCurve_of_mem_blowupFamily [IsNoetherian W]
    (hW : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (F : Finset W.IdealSheafData) (hF : ∀ Y ∈ F, IsConfigCurve Y) (p : W)
    (hp : IsClosed ({p} : Set W)) (hpdim : ringKrullDim (W.presheaf.stalk p) = 2)
    (hdimF : ∀ Y ∈ F, p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1)
    (A : (blowUp (centerIdeal p hp)).IdealSheafData) (hA : A ∈ blowupFamily F p hp) :
    IsConfigCurve A := by
  classical
  rw [blowupFamily, Finset.mem_insert, Finset.mem_image] at hA
  rcases hA with rfl | ⟨Y, hY, rfl⟩
  · exact isConfigCurve_exceptionalIdeal hW hdim p hp hpdim
  · exact isConfigCurve_transformIdeal hW hdim (hF Y hY) p hp
      (genericPoint_ne_of_ringKrullDim_eq_two (hF Y hY) hpdim) (hdimF Y hY)

/-- After one blowup at a closed point with two-dimensional local ring, every member of the
blown-up family which is not regular is the strict transform of a member which is not regular. -/
public theorem mem_image_of_not_isRegular_of_mem_blowupFamily [IsNoetherian W]
    (hW : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (F : Finset W.IdealSheafData) (hF : ∀ Y ∈ F, IsConfigCurve Y) (p : W)
    (hp : IsClosed ({p} : Set W)) (hpdim : ringKrullDim (W.presheaf.stalk p) = 2)
    (hdimF : ∀ Y ∈ F, p ∈ (Y.support : Set W) → topologicalKrullDim Y.subscheme = 1)
    (A : (blowUp (centerIdeal p hp)).IdealSheafData) (hA : A ∈ blowupFamily F p hp)
    (hAreg : ¬ AlgebraicGeometry.IsRegular A.subscheme) :
    ∃ Y ∈ F, ¬ AlgebraicGeometry.IsRegular Y.subscheme ∧ transformIdeal Y p hp = A := by
  classical
  rw [blowupFamily, Finset.mem_insert, Finset.mem_image] at hA
  rcases hA with rfl | ⟨Y, hY, rfl⟩
  · exact absurd (isRegular_exceptionalDivisor_vanishingIdeal_singleton hW hdim p hp hpdim) hAreg
  · refine ⟨Y, hY, fun hreg => hAreg ?_, rfl⟩
    exact isRegular_transformIdeal (hF Y hY) hreg p hp (hdimF Y hY)

/-- At a point of a configuration curve other than its generic point, the local ring of a surface
is two-dimensional. -/
public theorem IsConfigCurve.ringKrullDim_stalk_eq_two [IsLocallyNoetherian W]
    (hdim : topologicalKrullDim W = 2) {Y : W.IdealSheafData} (hY : IsConfigCurve Y) {x : W}
    (hx : x ∈ (Y.support : Set W)) (hne : (letI := hY.isIntegral; gen Y) ≠ x) :
    ringKrullDim (W.presheaf.stalk x) = 2 := by
  have := hY.isIntegral
  exact ringKrullDim_stalk_eq_two_of_mem_support hdim Y hY.isEffectiveCartierDivisor hx
    (Ne.symm hne)

/-- A configuration curve on a surface with a point other than its generic point is
one-dimensional. -/
public theorem IsConfigCurve.topologicalKrullDim_eq_one [IsLocallyNoetherian W]
    (hdim : topologicalKrullDim W = 2) {Y : W.IdealSheafData} (hY : IsConfigCurve Y) {x : W}
    (hx : x ∈ (Y.support : Set W)) (hne : (letI := hY.isIntegral; gen Y) ≠ x) :
    topologicalKrullDim Y.subscheme = 1 := by
  have := hY.isIntegral
  exact topologicalKrullDim_subscheme_eq_one hdim Y hY.isEffectiveCartierDivisor hx (Ne.symm hne)

/-- At a closed point with two-dimensional local ring, every configuration curve through it is
one-dimensional. -/
public theorem IsConfigCurve.topologicalKrullDim_eq_one_of_ringKrullDim_eq_two
    [IsLocallyNoetherian W] (hdim : topologicalKrullDim W = 2) {Y : W.IdealSheafData}
    (hY : IsConfigCurve Y) {x : W} (hxdim : ringKrullDim (W.presheaf.stalk x) = 2)
    (hx : x ∈ (Y.support : Set W)) : topologicalKrullDim Y.subscheme = 1 :=
  hY.topologicalKrullDim_eq_one hdim hx (genericPoint_ne_of_ringKrullDim_eq_two hY hxdim)

end Generic

end Stacks.ResolutionOfSurfaces

end
