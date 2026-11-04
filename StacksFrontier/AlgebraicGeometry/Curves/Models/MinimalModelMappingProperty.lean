module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelUniqueness
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMaps

/-!
# The mapping property of the minimal model

Let `C` be a smooth projective curve over the fraction field `K` of a discrete valuation ring
`R`, with `H⁰(C, 𝒪_C) = K` and genus `> 0`, and let `X` be its minimal model. This file proves
[Stacks, Tag 0C9Z]: every regular proper model `Y` of `C` admits a unique morphism of models
`Y ⟶ X` which is a sequence of contractions of exceptional curves of the first kind.

[Stacks, Tag 0CD9] contracts `Y` by such a sequence `g : Y ⟶ X₀` onto some minimal model `X₀`.
The sequence is proper and birational, hence an isomorphism on generic fibres
(`isIso_genericFiberMap_of_isProper_of_isBirational`), so the identification of the generic fibre
of `Y` with `C` transports to `X₀`, making `g` a morphism of models. By [Stacks, Tag 0C6B] there is
an isomorphism of models `X₀ ≅ X`. Uniqueness holds among all morphisms of models: `C` is
scheme-theoretically dense in `Y` and `X` is separated ([Stacks, Tag 01RH]).

## Main results

* `Stacks.Models.isIso_genericFiberMap_of_isProper_of_isBirational` — a proper birational
  morphism onto a regular proper model is an isomorphism on generic fibres.
* `Stacks.Models.existsUnique_exceptionalContractionSequence_of_isMinimalModel` —
  [Stacks, Tag 0C9Z].

## References

* [Stacks Project, Tag 0C9Z](https://stacks.math.columbia.edu/tag/0C9Z)
* [Stacks Project, Tag 0CD9](https://stacks.math.columbia.edu/tag/0CD9)
* [Stacks Project, Tag 0C6B](https://stacks.math.columbia.edu/tag/0C6B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

local notation "ιRK" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- **A proper birational morphism onto a regular proper model is an isomorphism on generic
fibres.** Every point of the generic fibre of the target is its generic point or has a
one-dimensional regular, hence discrete valuation, local ring, and [Stacks, Tag 0BFP] puts it in
the maximal open over which the morphism is an isomorphism. -/
theorem isIso_genericFiberMap_of_isProper_of_isBirational {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of R)) [IsProper pX] (hX : IsIntegralRegularSurface X) [IsReduced Y]
    (g : Y ⟶ X) [IsProper g] (hg : IsBirational g) :
    IsIso (genericFiberMap (K := K) g pX) := by
  have hXint := hX.isIntegral
  have hXnoe := hX.isNoetherian
  have : IsOpenImmersion ιRK := genericFiberSpec_isOpenImmersion
  obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open g
  let V : X.Opens := pX ⁻¹ᵁ (ιRK).opensRange
  have hVU : V ≤ U := by
    intro x hx
    obtain ⟨t, ht⟩ : pX x ∈ Set.range (ιRK).base := hx
    by_cases hgen : x = genericPoint X
    · exact mem_maximal_isomorphism_open_of_mem_genericPoints g hg U hU x
        (by rw [hgen, genericPoints_eq_singleton]; rfl)
    · obtain ⟨y, hy, hycl⟩ :=
        (isClosed_closure : IsClosed (closure ({x} : Set X))).exists_closed_singleton
          ⟨x, subset_closure rfl⟩
      have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
      have hne : y ≠ x := by
        rintro rfl
        have hpy : pX y = IsLocalRing.closedPoint R := by
          apply eq_closedPoint_of_isClosed_singleton
          have := pX.isClosedMap _ hycl
          rwa [Set.image_singleton] at this
        exact genericFiberSpec_ne_closedPoint t (ht.trans hpy)
      have h1 := Order.coheight_add_one_le (lt_of_specializes_of_ne hxy hne)
      have h2 := Order.coheight_add_one_le
        (lt_of_specializes_of_ne (genericPoint_specializes x) hgen)
      have hy2 := ringKrullDim_stalk_le_two hX y
      rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hy2
      have hy2' : Order.coheight y ≤ 2 := WithBot.coe_le_coe.mp hy2
      have hco : Order.coheight x = 1 := by
        have hle : Order.coheight x + 1 ≤ 2 := le_trans h1 hy2'
        have hge : 1 ≤ Order.coheight x := le_trans (by simp) h2
        induction h : Order.coheight x using ENat.recTopCoe with
        | top => rw [h] at hle; simp at hle
        | coe n =>
          rw [h] at hle hge
          have : n + 1 ≤ 2 := by exact_mod_cast hle
          have : 1 ≤ n := by exact_mod_cast hge
          exact_mod_cast (by omega : n = 1)
      have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
        isDiscreteValuationRing_stalk_of_isRegular hX.isRegular hco
      exact mem_maximal_isomorphism_open_of_isDiscreteValuationRing g hg U hU x
  have : IsIso (g ∣_ V) := Stacks.RestrictIso.isIso_morphismRestrict_of_le g hVU hU.1
  let eg : pullback pX ιRK ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst pX ιRK) V.ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι])
  let ep : pullback (g ≫ pX) ιRK ≅ (g ⁻¹ᵁ V).toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst (g ≫ pX) ιRK) (g ⁻¹ᵁ V).ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι]
      rfl)
  have hm : genericFiberMap (K := K) g pX = ep.hom ≫ (g ∣_ V) ≫ eg.inv := by
    rw [← cancel_mono (pullback.fst pX ιRK), genericFiberMap_fst]
    simp [ep, eg, morphismRestrict_ι]
  rw [hm]
  infer_instance

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- A sequence of contractions runs over `Spec R`. -/
theorem comp_eq_of_exceptionalContractionSequence {C X Y : Scheme.{u}} {c : C ⟶ Spec (.of K)}
    {q : Y ⟶ Spec (.of R)} {p : X ⟶ Spec (.of R)} {g : Y ⟶ X}
    (hs : ExceptionalContractionSequence c q p g) : g ≫ p = q := by
  induction hs with
  | refl p => exact Category.id_comp p
  | step b D k eE hE hb hbp e' hmod hprop hreg rest ih => rw [Category.assoc, ih, hbp]

/-- A sequence of contractions between regular proper models is birational: each contraction is,
up to isomorphism, the blowup of a regular point of codimension two. -/
theorem isBirational_of_exceptionalContractionSequence {C X Y : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] {q : Y ⟶ Spec (.of R)}
    {p : X ⟶ Spec (.of R)} {g : Y ⟶ X} (hs : ExceptionalContractionSequence c q p g)
    (hY : IsIntegral Y) : IsBirational g := by
  induction hs with
  | refl p => exact isBirational_of_isOpenImmersion (𝟙 _)
  | @step X₁ X' Y' p₁ p' q' g' b D k _ eE hE hb hbp e' hmod hprop hreg rest ih =>
    have := hprop
    have hX's := isIntegralRegularSurface_of_isModel c hproj p' e' hmod hreg
    have hX'int := hX's.isIntegral
    have hX'noe := hX's.isNoetherian
    obtain ⟨-, z, hz, -, -, -, e, he⟩ := hb
    have hI : Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X') ≠ ⊥ :=
      vanishingIdeal_singleton_ne_bot hX's.topologicalKrullDim_eq z hz
    have := isIntegral_blowUp _ hI
    have : IsIntegral X₁ := IsIntegral.of_isIso e.inv
    have hbbir : IsBirational b := by
      rw [← he]
      exact (isBirational_of_isOpenImmersion e.hom).comp (isBirational_blowUpToBase _ hI)
    exact hbbir.comp (ih hX'int)

/-- **Stacks Project, Tag 0C9Z.** Let `C` be a smooth projective curve over `K` with
`H⁰(C, 𝒪_C) = K` and genus `> 0`, let `X` be the minimal model of `C` and let `Y` be a regular
proper model of `C`. Then there is a unique morphism of models `Y ⟶ X` which is a sequence of
contractions of exceptional curves of the first kind.

A morphism of models is a morphism over `R` compatible with the identifications of the generic
fibres with `C`; "a sequence of contractions" is a sequence `Y = Xₘ → ⋯ → X₀` of contractions of
exceptional curves of the first kind between regular proper models of `C`
(`Stacks.Models.ExceptionalContractionSequence`), followed by an isomorphism of `X₀` with `X`
over `R`. The morphism is unique among all morphisms of models, and is a sequence of contractions
by [Stacks, Tag 0CD9] and [Stacks, Tag 0C6B]. -/
@[stacks 0C9Z]
theorem existsUnique_exceptionalContractionSequence_of_isMinimalModel {C X Y : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hg : 0 < genus c)
    (p : X ⟶ Spec (.of R)) (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsMinimalModel c p eX) (q : Y ⟶ Spec (.of R))
    (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c q eY) [IsProper q] (hreg : IsRegular Y) :
    ∃! f : Y ⟶ X, (f ≫ p = q ∧
      eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ f =
        eX.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      ∃ (X₀ : Scheme.{u}) (p₀ : X₀ ⟶ Spec (.of R)) (g : Y ⟶ X₀) (ψ : X₀ ≅ X),
        ExceptionalContractionSequence c q p₀ g ∧ ψ.hom ≫ p = p₀ ∧ g ≫ ψ.hom = f := by
  have := hX.isIso_globalSections
  have := hX.isProper
  have hproj := hX.curveProjective
  have hYs := isIntegralRegularSurface_of_isModel c hproj q eY hmod hreg
  have hYint := hYs.isIntegral
  have : Nonempty C := inferInstance
  obtain ⟨X₀, p₀, e₀, g, hseq, hmin₀⟩ :=
    exists_exceptionalContractionSequence_isMinimalModel c hproj hX.isIso_globalSections q eY hmod
      hreg
  have hgq := comp_eq_of_exceptionalContractionSequence hseq
  have := hmin₀.isProper
  have hX₀s := isIntegralRegularSurface_of_isModel c hproj p₀ e₀ hmin₀.isModel hmin₀.regular
  have hgbir : IsBirational g := isBirational_of_exceptionalContractionSequence c hproj hseq hYint
  have hgprop : IsProper g := by
    have : IsProper (g ≫ p₀) := by rw [hgq]; infer_instance
    exact IsProper.of_comp g p₀
  -- the generic fibre is transported along `g`
  subst hgq
  have := isIso_genericFiberMap_of_isProper_of_isBirational (K := K) p₀ hX₀s g hgbir
  let e₀' : C ≅ pullback p₀ ιRK := eY ≪≫ asIso (genericFiberMap (K := K) g p₀)
  have he₀' : e₀'.hom ≫ pullback.fst p₀ ιRK = eY.hom ≫ pullback.fst (g ≫ p₀) ιRK ≫ g := by
    simp [e₀']
  have hmin₀' : IsMinimalModel c p₀ e₀' :=
    { hmin₀ with
      isModel := ⟨hmin₀.isModel.1, hmin₀.isModel.2.1, hmin₀.isModel.2.2.1, by
        simp only [e₀', Iso.trans_hom, asIso_hom, Category.assoc, genericFiberMap_snd]
        exact hmod.2.2.2⟩ }
  obtain ⟨ψ, ⟨hψp, hψc⟩, -⟩ := existsUnique_iso_of_isMinimalModel c hg p₀ p e₀' eX hmin₀' hX
  have hfp : (g ≫ ψ.hom) ≫ p = g ≫ p₀ := by rw [Category.assoc, hψp]
  have hfc : eY.hom ≫ pullback.fst (g ≫ p₀) ιRK ≫ g ≫ ψ.hom = eX.hom ≫ pullback.fst p ιRK := by
    rw [← hψc, reassoc_of% he₀']
  refine ⟨g ≫ ψ.hom, ⟨⟨hfp, hfc⟩, X₀, p₀, g, ψ, hseq, hψp, rfl⟩, fun f hf => ?_⟩
  exact eq_of_comp_eq_of_genericFiber (g ≫ p₀) p eY eX hf.1.1 hfp hf.1.2 hfc

end Stacks.Models

end
