module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.Family
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.AmbientCurveResolution
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveFamilyResolution

/-!
# Making every curve of a family on a regular surface regular

Let `W` be a regular Noetherian scheme of dimension two and let `F` be a finite family of
configuration curves on `W` (integral effective Cartier divisors, each regular or a resolvable
curve). Then a finite sequence of blowups at closed points turns `F` into a family of regular
configuration curves whose union is the inverse image of the union of `F`.

This is the first reduction in the proof of [Stacks, Tag 0BIC]: "the strict transform `Y'` of each
irreducible component `Y` is either equal to `Y` or the blowup of `Y` at `p`. Thus in this process
we do not produce additional singular components of dimension `1`. Thus it follows from
Lemmas 0BIB and 0BI8 that we may assume … that all irreducible components `Y` of `Z` are regular."
A resolvable curve is resolved by the sequence of blowups at closed points that condition (3) of
[Stacks, Tag 0BI4] provides, mirrored in the ambient surface ([Stacks, Tag 0BI5]); the other
members are carried along, the regular ones staying regular, and every exceptional divisor created
is regular by [Stacks, Tag 0AGQ].

## Main results

* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_forall_isRegular` — the reduction.

## References

* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
* [Stacks Project, Tag 0BI5](https://stacks.math.columbia.edu/tag/0BI5)
* [Stacks Project, Tag 0BI4](https://stacks.math.columbia.edu/tag/0BI4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

/-- The generic point of an integral closed subscheme, as a point of the ambient scheme. -/
local notation3 "gen " Y:max => Scheme.IdealSheafData.subschemeι Y
  (_root_.genericPoint (Scheme.IdealSheafData.subscheme Y))

/-- **The generic point of a one-dimensional integral closed subscheme is not a closed point.** -/
public theorem not_isClosed_genericPoint_of_topologicalKrullDim_eq_one {W : Scheme.{u}}
    (Y : W.IdealSheafData) [IsIntegral Y.subscheme] (hd : topologicalKrullDim Y.subscheme = 1) :
    ¬ IsClosed ({gen Y} : Set W) := by
  intro hcl
  have hpre : Y.subschemeι.base ⁻¹' {gen Y} = {_root_.genericPoint Y.subscheme} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Y.subschemeι.isClosedEmbedding.injective.eq_iff
  have hcl' : IsClosed ({_root_.genericPoint Y.subscheme} : Set Y.subscheme) := by
    rw [← hpre]
    exact hcl.preimage Y.subschemeι.continuous
  have huniv : (Set.univ : Set Y.subscheme) = {_root_.genericPoint Y.subscheme} := by
    rw [← (genericPoint_spec Y.subscheme).def, hcl'.closure_eq]
  have : Subsingleton Y.subscheme := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (Set.univ : Set Y.subscheme) := Set.mem_univ a
    have hb : b ∈ (Set.univ : Set Y.subscheme) := Set.mem_univ b
    rw [huniv] at ha hb
    exact ha.trans hb.symm
  have : DiscreteTopology Y.subscheme := inferInstance
  have hle := topologicalKrullDim_zero_of_discreteTopology Y.subscheme
  rw [hd] at hle
  exact absurd hle (by decide)

/-- **Mirroring a resolution of one curve of a family in the ambient surface.** Let `J` be a
one-dimensional member of a family `F` of configuration curves on a regular Noetherian surface
`W`, and let `C ≅ J` admit a finite sequence of blowups at closed points `P ⟶ C`. Then there is
a finite sequence of blowups of `W` at closed points, `V ⟶ W`, and a family `F'` of configuration
curves on `V` covering the inverse image of the union of `F`, together with an assignment `Φ` of
a member of `F'` to each member of `F` (its iterated strict transform), such that `P ≅ Φ J` and
every member of `F'` which is not regular is `Φ Y` for a member `Y` of `F` which is not regular.

The centres are the images of the centres of `P ⟶ C`; the strict transform of `J` is the blowup of
`J` at the corresponding point ([Stacks, Tag 080E]). -/
public theorem exists_pointBlowupChain_lift {C P : Scheme.{u}} {g : P ⟶ C}
    (t : PointBlowupChain C Set.univ P g) :
    ∀ (W : Scheme.{u}) [IsNoetherian W], AlgebraicGeometry.IsRegular W →
      topologicalKrullDim W = 2 → ∀ (F : Finset W.IdealSheafData), (∀ Y ∈ F, IsConfigCurve Y) →
      ∀ J ∈ F, topologicalKrullDim J.subscheme = 1 → Nonempty (C ≅ J.subscheme) →
      ∃ (V : Scheme.{u}) (f : V ⟶ W) (F' : Finset V.IdealSheafData)
        (Φ : W.IdealSheafData → V.IdealSheafData),
        PointBlowupChain W Set.univ V f ∧ (∀ A ∈ F', IsConfigCurve A) ∧
        (⋃ A ∈ F', (A.support : Set V)) = f.base ⁻¹' ⋃ Y ∈ F, (Y.support : Set W) ∧
        (∀ A ∈ F', ¬ AlgebraicGeometry.IsRegular A.subscheme →
          ∃ Y ∈ F, ¬ AlgebraicGeometry.IsRegular Y.subscheme ∧ Φ Y = A) ∧
        Φ J ∈ F' ∧ topologicalKrullDim (Φ J).subscheme = 1 ∧ Nonempty (P ≅ (Φ J).subscheme) := by
  induction t with
  | refl =>
      intro W _ _ _ F hF J hJ hJd hCJ
      refine ⟨W, 𝟙 W, F, id, .refl, hF, by simp, fun A hA hA' => ⟨A, hA, hA', rfl⟩, hJ, hJd,
        hCJ⟩
  | @step P₀ g₀ t₀ v hv _ ih =>
      intro W _ hW hdim F hF J hJ hJd hCJ
      obtain ⟨V₀, f₀, F₀, Φ₀, hc₀, hF₀, hU₀, hreg₀, hJ₀, hJ₀d, ⟨e⟩⟩ :=
        ih W hW hdim F hF J hJ hJd hCJ
      have : IsNoetherian V₀ := isNoetherian_of_pointBlowupChain hc₀
      obtain ⟨hV₀reg, hV₀dim⟩ := hc₀.isRegular_and_topologicalKrullDim hW hdim
      set K := Φ₀ J with hK
      have hK : IsConfigCurve K := hF₀ K hJ₀
      have := hK.isIntegral
      have hq : IsClosed ({e.hom v} : Set K.subscheme) := by
        simpa using (Scheme.homeoOfIso e).isClosedMap _ hv
      have hw : IsClosed ({K.subschemeι (e.hom v)} : Set V₀) := by
        simpa using K.subschemeι.isClosedEmbedding.isClosedMap _ hq
      set w := K.subschemeι (e.hom v) with hwdef
      have hwK : w ∈ (K.support : Set V₀) := by
        rw [← K.range_subschemeι]
        exact ⟨_, rfl⟩
      have hwgen : (gen K) ≠ w := fun h =>
        not_isClosed_genericPoint_of_topologicalKrullDim_eq_one K hJ₀d (h ▸ hw)
      have hwdim : ringKrullDim (V₀.presheaf.stalk w) = 2 :=
        hK.ringKrullDim_stalk_eq_two hV₀dim hwK hwgen
      have hdimF₀ : ∀ Y ∈ F₀, w ∈ (Y.support : Set V₀) → topologicalKrullDim Y.subscheme = 1 :=
        fun Y hY hwY => (hF₀ Y hY).topologicalKrullDim_eq_one_of_ringKrullDim_eq_two hV₀dim hwdim
          hwY
      obtain ⟨d⟩ := nonempty_transformIdeal_subscheme_iso_blowUp K (e.hom v) hq hw
      have hcomap : (centerIdeal (e.hom v) hq).comap e.hom = centerIdeal v hv :=
        comap_centerIdeal_of_isClosedImmersion e.hom v hv hq
      obtain ⟨b⟩ := nonempty_blowUp_comap_iso_of_isIso e.hom (centerIdeal (e.hom v) hq)
      rw [hcomap] at b
      refine ⟨blowUp (centerIdeal w hw), blowUpToBase (centerIdeal w hw) ≫ f₀,
        blowupFamily F₀ w hw, fun Y => transformIdeal (Φ₀ Y) w hw,
        hc₀.step w hw (Set.mem_univ _),
        isConfigCurve_of_mem_blowupFamily hV₀reg hV₀dim F₀ hF₀ w hw hwdim hdimF₀, ?_, ?_, ?_,
        (transformIdeal_integral_curve K hJ₀d w hw).2, ⟨b ≪≫ d.symm⟩⟩
      · rw [iUnion_support_blowupFamily F₀ w hw ⟨K, hJ₀, hwK⟩, hU₀, Scheme.Hom.comp_base,
          TopCat.coe_comp, Set.preimage_comp]
      · intro A hA hAreg
        obtain ⟨Y₀, hY₀, hY₀reg, rfl⟩ := mem_image_of_not_isRegular_of_mem_blowupFamily hV₀reg
          hV₀dim F₀ hF₀ w hw hwdim hdimF₀ A hA hAreg
        obtain ⟨Y, hY, hYreg, rfl⟩ := hreg₀ Y₀ hY₀ hY₀reg
        exact ⟨Y, hY, hYreg, rfl⟩
      · classical
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hJ₀)

open scoped Classical in
/-- **Every member of a family of configuration curves on a regular Noetherian surface can be
made regular by finitely many blowups at closed points**, the family being replaced by the strict
transforms of its members together with the exceptional divisors created, whose union is the
inverse image of the union of the family. -/
public theorem exists_pointBlowupChain_forall_isRegular :
    ∀ (n : ℕ) (W : Scheme.{u}) [IsNoetherian W], AlgebraicGeometry.IsRegular W →
      topologicalKrullDim W = 2 → ∀ (F : Finset W.IdealSheafData), (∀ Y ∈ F, IsConfigCurve Y) →
      (F.filter fun Y => ¬ AlgebraicGeometry.IsRegular Y.subscheme).card = n →
      ∃ (V : Scheme.{u}) (f : V ⟶ W) (F' : Finset V.IdealSheafData),
        PointBlowupChain W Set.univ V f ∧ (∀ A ∈ F', IsConfigCurve A) ∧
        (∀ A ∈ F', AlgebraicGeometry.IsRegular A.subscheme) ∧
        (⋃ A ∈ F', (A.support : Set V)) = f.base ⁻¹' ⋃ Y ∈ F, (Y.support : Set W) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ hW hdim F hF hn
  by_cases hall : ∀ Y ∈ F, AlgebraicGeometry.IsRegular Y.subscheme
  · exact ⟨W, 𝟙 W, F, .refl, hF, hall, by simp⟩
  push Not at hall
  obtain ⟨J, hJ, hJreg⟩ := hall
  obtain ⟨hJd, P, g, t, hPreg⟩ := (hF J hJ).isRegular_or.resolve_left hJreg
  obtain ⟨V₀, f₀, F₀, Φ₀, hc₀, hF₀, hU₀, hreg₀, hJ₀, -, ⟨e⟩⟩ :=
    exists_pointBlowupChain_lift t W hW hdim F hF J hJ hJd ⟨Iso.refl _⟩
  have : IsNoetherian V₀ := isNoetherian_of_pointBlowupChain hc₀
  obtain ⟨hV₀reg, hV₀dim⟩ := hc₀.isRegular_and_topologicalKrullDim hW hdim
  have hΦJ : AlgebraicGeometry.IsRegular (Φ₀ J).subscheme := isRegular_of_isIso e.inv hPreg
  have hsub : (F₀.filter fun A => ¬ AlgebraicGeometry.IsRegular A.subscheme) ⊆
      ((F.filter fun Y => ¬ AlgebraicGeometry.IsRegular Y.subscheme).erase J).image Φ₀ := by
    intro A hA
    rw [Finset.mem_filter] at hA
    obtain ⟨Y, hY, hYreg, rfl⟩ := hreg₀ A hA.1 hA.2
    refine Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hY, hYreg⟩⟩)
    rintro rfl
    exact hA.2 hΦJ
  have hlt : (F₀.filter fun A => ¬ AlgebraicGeometry.IsRegular A.subscheme).card < n := by
    refine lt_of_le_of_lt ((Finset.card_le_card hsub).trans Finset.card_image_le) ?_
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hJ, hJreg⟩), hn]
    have : 0 < n := hn ▸ Finset.card_pos.mpr ⟨J, Finset.mem_filter.mpr ⟨hJ, hJreg⟩⟩
    omega
  obtain ⟨V, f, F', hc, hF', hreg', hU'⟩ := ih _ hlt V₀ hV₀reg hV₀dim F₀ hF₀ rfl
  refine ⟨V, f ≫ f₀, F', hc₀.comp hc (fun _ _ => Set.mem_univ _), hF', hreg', ?_⟩
  rw [hU', hU₀, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]

end Stacks.ResolutionOfSurfaces

end
