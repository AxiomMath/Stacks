module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Scheme theoretic closure and density for immersions and open subschemes

For an open subscheme `U` of a reduced scheme the three notions of density coincide:
topological density of `U`, the scheme theoretic closure of `U` being all of `X`, and scheme
theoretic density of `U`. Without reducedness of `X` the last two still agree as soon as `U`
itself is reduced, and then `X` is reduced too.

## Main results

* `AlgebraicGeometry.dense_open_tfae`: the three density conditions on an open subscheme of a
  reduced scheme are equivalent.
* `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isSchemeTheoreticallyDense`: for a
  reduced open subscheme, having the whole scheme as scheme theoretic closure is equivalent to
  scheme theoretic density.
* `AlgebraicGeometry.isReduced_of_isSchemeTheoreticallyDense`: a scheme with a reduced scheme
  theoretically dense open subscheme is reduced.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If the image inclusion of a reduced open subscheme is an isomorphism, the open is dense. -/
private lemma dense_of_isIso_imageι {X : Scheme.{u}} (U : X.Opens) [IsReduced U]
    (h : IsIso U.ι.imageι) : Dense (U : Set X) := by
  have : IsDominant U.ι.toImage := isDominant_toImage U.ι (Or.inr inferInstance)
  have : IsDominant U.ι := by rw [← U.ι.toImage_imageι]; infer_instance
  simpa only [Scheme.Opens.range_ι, DenseRange] using this.denseRange

/-- A dense open subscheme is scheme-theoretically dense. -/
private lemma isSchemeTheoreticallyDense_of_dense {X : Scheme.{u}} [IsReduced X] (U : X.Opens)
    (hU : Dense (U : Set X)) : Scheme.Opens.IsSchemeTheoreticallyDense U := fun V ↦ by
  have : IsDominant (V.ι ⁻¹ᵁ U).ι :=
    Opens.isDominant_ι (hU.preimage V.ι.isOpenEmbedding.isOpenMap)
  exact IsSchemeTheoreticallyDominant.of_isDominant _

private lemma isSchemeTheoreticallyDominant_of_isSchemeTheoreticallyDense
    {X : Scheme.{u}} (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) :
    IsSchemeTheoreticallyDominant U.ι := by
  let W : Scheme.Opens (⊤ : X.Opens) := (⊤ : X.Opens).ι ⁻¹ᵁ U
  let e : W.toScheme ≅ U := Scheme.Opens.isoOfLE (le_top : U ≤ (⊤ : X.Opens))
  have : IsSchemeTheoreticallyDominant W.ι := hU ⊤
  have : IsIso (⊤ : X.Opens).ι := (Scheme.topIso X).isIso_hom
  have : IsSchemeTheoreticallyDominant (e.hom ≫ U.ι) := by
    rw [Scheme.Opens.isoOfLE_hom_ι (le_top : U ≤ (⊤ : X.Opens))]
    infer_instance
  simpa using (inferInstance : IsSchemeTheoreticallyDominant (e.inv ≫ (e.hom ≫ U.ι)))

/-- For an open subscheme of a reduced scheme, topological density, having the whole scheme as
scheme-theoretic closure, and scheme-theoretic density are equivalent. -/
@[stacks 056D]
theorem dense_open_tfae {X : Scheme.{u}} [IsReduced X]
    (U : X.Opens) :
    List.TFAE [
      Dense (U : Set X),
      IsIso U.ι.imageι,
      Scheme.Opens.IsSchemeTheoreticallyDense U] := by
  tfae_have h12 : 1 ↔ 2 := by
    constructor
    · intro hU
      have : IsDominant U.ι := Opens.isDominant_ι hU
      exact Scheme.isIso_subschemeι_iff_eq_bot U.ι.ker |>.2
        (IsSchemeTheoreticallyDominant.of_isDominant U.ι).ker_eq_bot
    · exact fun _ ↦ dense_of_isIso_imageι U ‹_›
  tfae_have 1 ↔ 3 := by
    refine ⟨isSchemeTheoreticallyDense_of_dense U, fun hU ↦ h12.mpr ?_⟩
    exact (Scheme.isIso_subschemeι_iff_eq_bot U.ι.ker).2
      (isSchemeTheoreticallyDominant_of_isSchemeTheoreticallyDense U hU).ker_eq_bot
  tfae_finish

private lemma isReduced_image_of_isReduced' {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsReduced Z] : IsReduced f.image := by
  have hker : f.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f)) := by
    calc
      f.ker = (⊥ : Z.IdealSheafData).map f := by
        symm
        simpa [Scheme.IdealSheafData.map] using
          (Scheme.Hom.ker_comp_of_isIso ((⊥ : Z.IdealSheafData).subschemeι) f)
      _ = (Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds Z)).map f := by
        rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
      _ = Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f)) := by
        simpa using Scheme.IdealSheafData.map_vanishingIdeal f (⊤ : TopologicalSpace.Closeds Z)
  show IsReduced f.ker.subscheme
  rw [hker]
  exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
    (TopologicalSpace.Closeds.closure (Set.range f))

/-- The inclusion of a scheme-theoretically dense open subscheme is scheme-theoretically
dominant. -/
alias isSchemeTheoreticallyDominant_of_isSchemeTheoreticallyDense' := isSchemeTheoreticallyDominant_of_isSchemeTheoreticallyDense

private lemma isIso_imageι_and_isReduced_of_dominant {X : Scheme.{u}} (U : X.Opens)
    [IsReduced U] (h : IsSchemeTheoreticallyDominant U.ι) :
    IsIso U.ι.imageι ∧ IsReduced X := by
  have : IsIso U.ι.imageι := (Scheme.isIso_subschemeι_iff_eq_bot U.ι.ker).2 h.ker_eq_bot
  exact ⟨inferInstance, isReduced_of_isOpenImmersion (asIso U.ι.imageι).inv⟩

/-- For a reduced open subscheme, having scheme-theoretic closure equal to the ambient scheme is
equivalent to being scheme-theoretically dense. -/
@[stacks 056E "equivalence"]
lemma isSchemeTheoreticallyDominant_iff_isSchemeTheoreticallyDense
    {X : Scheme.{u}} (U : X.Opens) [IsReduced U] :
    IsSchemeTheoreticallyDominant U.ι ↔ Scheme.Opens.IsSchemeTheoreticallyDense U := by
  refine ⟨fun hdom V ↦ ?_, isSchemeTheoreticallyDominant_of_isSchemeTheoreticallyDense U⟩
  obtain ⟨_, _⟩ := isIso_imageι_and_isReduced_of_dominant U hdom
  exact isSchemeTheoreticallyDense_of_dense U (dense_of_isIso_imageι U ‹_›) V

/-- A scheme with a reduced scheme-theoretically dense open subscheme is reduced. -/
@[stacks 056E "reducedness"]
lemma isReduced_of_isSchemeTheoreticallyDense
    {X : Scheme.{u}} (U : X.Opens) [IsReduced U]
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) : IsReduced X :=
  (isIso_imageι_and_isReduced_of_dominant U
    (isSchemeTheoreticallyDominant_of_isSchemeTheoreticallyDense U hU)).2

end AlgebraicGeometry
