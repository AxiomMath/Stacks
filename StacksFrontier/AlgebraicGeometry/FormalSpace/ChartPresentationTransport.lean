module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleCharacterization
public import StacksFrontier.RingTheory.Rig.RigEtaleRingEquiv
public import StacksFrontier.RingTheory.Rig.RigSmoothRingEquiv
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverNoetherian

/-!
# A chart condition can be checked on one presentation

Let `S` be a scheme contained in a big fppf site `B`, let `C` be a class of weakly admissible
topological rings and let `P` be a property of continuous ring homomorphisms. The chart condition
`AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap C P t` on a map `t : U ⟶ V` of affine
formal algebraic spaces quantifies over *every* presentation of `t` as the formal spectrum of a
homomorphism of rings of the class. When `P` depends on a homomorphism only up to isomorphism of
its source and target, one presentation suffices: by the uniqueness of the presenting rings of a
square of formal spectra (Stacks 0AN0 and Stacks 0AIC,
`AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_comp_eq_of_formalSpectrum_iso_sq`)
any two presentations of `t` differ by isomorphisms of topological rings on either side.

## Main definitions

* `AlgebraicGeometry.FormalSpace.PropertyInvariantUnderRingEquiv`: the invariance of `P`, on
  rings of the class `C`, under isomorphisms of topological rings of source and target.

## Main results

* `hasPropertyOnAffineChartMap_of_presentation_of_propertyInvariantUnderRingEquiv`:
  the chart condition from one presentation, for `P` invariant under isomorphisms of both
  presenting rings at once.
* `AlgebraicGeometry.FormalSpace.propertyInvariantUnderRingEquiv_isRigEtaleHom`: rig-étaleness of
  arrows of `WAdm^{Noeth}` is invariant in this sense.
* `AlgebraicGeometry.FormalSpace.propertyInvariantUnderRingEquiv_isRigSmoothArrow`: so is
  rig-smoothness.

## References

* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- A property `P` of homomorphisms between topological rings of the class `C` is *invariant
under isomorphism* when `g ∘ α = β ∘ g₀`, for isomorphisms `α`, `β` of topological rings
continuous in both directions and `g₀` continuous with `P`, forces `P` on `g`. -/
abbrev PropertyInvariantUnderRingEquiv : Prop :=
  ∀ {A₀ C₀ A R : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [CommRing C₀] [TopologicalSpace C₀] [IsTopologicalRing C₀] [IsLinearTopology C₀ C₀]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R],
    C A₀ → C C₀ → C A → C R →
    ∀ (g₀ : A₀ →+* C₀) (g : A →+* R), Continuous g₀ →
    ∀ (α : A₀ ≃+* A), Continuous α → Continuous α.symm →
    ∀ (β : C₀ ≃+* R), Continuous β → Continuous β.symm →
      g.comp (α : A₀ →+* A) = (β : C₀ →+* R).comp g₀ → P g₀ → P g

attribute [local instance] sheaf_hasColimits

variable {B S hS C P} in
/-- **A chart condition from one presentation.** If `P` is invariant under isomorphism on the
weakly admissible class `C` and the map `t : U ⟶ V` of affine formal algebraic spaces is the
formal spectrum of one continuous homomorphism `g₀` of rings of `C` having `P`, then every
presentation of `t` by rings of `C` has `P`. -/
theorem hasPropertyOnAffineChartMap_of_presentation_of_propertyInvariantUnderRingEquiv
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    (hPiso : PropertyInvariantUnderRingEquiv C P)
    {U V : FppfSheaf B S hS} (t : U ⟶ V) {A₀ C₀ : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [CommRing C₀] [TopologicalSpace C₀] [IsTopologicalRing C₀] [IsLinearTopology C₀ C₀]
    (hA₀ : C A₀) (hC₀ : C C₀) (D₀ : QuotientSystem B S hS A₀) (E₀ : QuotientSystem B S hS C₀)
    (eU₀ : U ≅ formalSpectrum E₀) (eV₀ : V ≅ formalSpectrum D₀) (g₀ : ContinuousHom D₀ E₀)
    (ht : t = eU₀.hom ≫ formalSpectrumMap (hCwa A₀ hA₀) g₀ ≫ eV₀.inv)
    (hP : P g₀.toRingHom) :
    HasPropertyOnAffineChartMap B S hS C P t := by
  intro A R _ _ _ _ _ _ _ _ hA hR hwa D E eU eV g hg
  have hsq : formalSpectrumMap hwa g ≫ (eV.symm ≪≫ eV₀).hom =
      (eU.symm ≪≫ eU₀).hom ≫ formalSpectrumMap (hCwa A₀ hA₀) g₀ := by
    have h := hg.symm.trans ht
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← cancel_epi eU.hom, ← cancel_mono eV₀.inv]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using h
  obtain ⟨k, m, α, β, -, -, hα, hβ, hαc, hαc', hβc, hβc', hcomp⟩ :=
    exists_continuous_ringEquiv_comp_eq_of_formalSpectrum_iso_sq hwa (hCwa A₀ hA₀)
      (hCwa R hR) (hCwa C₀ hC₀) g g₀ (eV.symm ≪≫ eV₀) (eU.symm ≪≫ eU₀) hsq
  refine hPiso hA₀ hC₀ hA hR g₀.toRingHom g.toRingHom g₀.continuous α hαc hαc' β hβc hβc' ?_ hP
  ext x
  have := congrArg (fun φ : A₀ →+* R ↦ φ x) hcomp
  simpa [hα, hβ] using this

variable {B S hS C P} in
/-- A chart condition is unchanged by precomposing the chart map with an isomorphism of its
source: a presentation of the composite is one of the original map, through the isomorphism. -/
theorem HasPropertyOnAffineChartMap.iso_hom_comp {U U' V : FppfSheaf B S hS} (e : U' ≅ U)
    {t : U ⟶ V} (ht : HasPropertyOnAffineChartMap B S hS C P t) :
    HasPropertyOnAffineChartMap B S hS C P (e.hom ≫ t) := by
  intro A R _ _ _ _ _ _ _ _ hA hR hwa D E eU eV g hg
  refine ht A R hA hR hwa D E (e.symm ≪≫ eU) eV g ?_
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hg, Iso.inv_hom_id_assoc]

/-- **Rig-étaleness of arrows of `WAdm^{Noeth}` is invariant under isomorphism** of source and
target, which is what lets the rig-étale chart condition be checked on one presentation. -/
theorem propertyInvariantUnderRingEquiv_isRigEtaleHom :
    PropertyInvariantUnderRingEquiv TopologicalRing.IsNoetherianAdic
      (fun φ ↦ TopologicalRing.IsRigEtaleHom φ) := by
  intro A₀ C₀ A R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA₀ hC₀ hA hR g₀ g _ α hα hα' β hβ hβ'
    hsq hP
  let := hA₀.2
  let := hC₀.2
  let := hA.2
  let := hR.2
  intro _ _ _ _
  exact RingHom.isRigEtaleArrow_of_comp_ringEquiv hA₀.1 hC₀.1 hA.1 hR.1 g₀ g α hα hα' β hβ hβ'
    hsq hP

/-- **Rig-smoothness of arrows of `WAdm^{Noeth}` is invariant under isomorphism** of source and
target, which is what lets the rig-smooth chart condition be checked on one presentation. -/
theorem propertyInvariantUnderRingEquiv_isRigSmoothArrow :
    PropertyInvariantUnderRingEquiv TopologicalRing.IsNoetherianAdic
      (fun φ ↦ RingHom.IsRigSmoothArrow φ) := by
  intro A₀ C₀ A R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA₀ hC₀ hA hR g₀ g _ α hα hα' β hβ hβ'
    hsq hP
  let := hA₀.2
  let := hC₀.2
  let := hA.2
  let := hR.2
  intro _ _ _ _
  exact RingHom.isRigSmoothArrow_of_comp_ringEquiv hA₀.1 hC₀.1 hA.1 hR.1 g₀ g α hα hα' β hβ
    hβ' hsq hP

end AlgebraicGeometry.FormalSpace

end
