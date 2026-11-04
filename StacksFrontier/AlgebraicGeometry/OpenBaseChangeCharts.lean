module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Charts cut out of a base change along an open immersion

Fix a scheme `Z`, an open `Uo : Z.Opens`, a scheme `A` with a morphism `α : A ⟶ Z`, and a
scheme `V` with a morphism `f : V ⟶ Uo.toScheme`.  Suppose that `V`, viewed as an object of the
slice category over `Uo.toScheme`, is isomorphic to the base change of `α` along the open
immersion `Uo.ι`.  This file records the geometric consequences of such an isomorphism.

## Main results

* `Stacks.OpenBaseChangeCharts.isPullback_of_overIso`: the slice isomorphism produces a morphism
  `ρ : V ⟶ A` fitting into a cartesian square over `α` and `Uo.ι`, so that `V` really is the part
  of `A` lying over `Uo`.
* `Stacks.OpenBaseChangeCharts.isOpenImmersion_of_isPullback`: such a `ρ` is automatically an
  open immersion, being a base change of `Uo.ι`.
* `Stacks.OpenBaseChangeCharts.exists_chart`: for every open `Ω ≤ Uo` of `Z`, the part `α ⁻¹ᵁ Ω`
  of `A` over `Ω` sits inside `V` by a morphism `σ` compatible with `ρ`, and the restriction
  `α ∣_ Ω` exhibits it as the base change of `V ⟶ Z` along `Ω.ι`.
* `Stacks.OpenBaseChangeCharts.chart_comp_homOfLE`: these charts are compatible with shrinking
  the open.
-/

@[expose] public section

namespace Stacks.OpenBaseChangeCharts

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

/-- An isomorphism `Over.mk f ≅ (Over.pullback Uo.ι).obj (Over.mk α)` in the slice category over
`Uo.toScheme` exhibits `V` as a fibre product of `α : A ⟶ Z` and the open immersion
`Uo.ι : Uo.toScheme ⟶ Z`: it yields a morphism `ρ : V ⟶ A` making
`IsPullback ρ f α Uo.ι` hold. -/
theorem isPullback_of_overIso {Z : Scheme.{u}} {Uo : Z.Opens} {V A : Scheme.{u}}
    (f : V ⟶ Uo.toScheme) (α : A ⟶ Z)
    (e : Over.mk f ≅ (Over.pullback Uo.ι).obj (Over.mk α)) :
    ∃ ρ : V ⟶ A, IsPullback ρ f α Uo.ι := by
  have hw : e.hom.left ≫ pullback.snd α Uo.ι = f := Over.w e.hom
  have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  refine ⟨e.hom.left ≫ pullback.fst α Uo.ι, ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso e.hom.left) rfl hw
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw]

/-- Given a cartesian square `IsPullback ρ f α Uo.ι` and an open `Ω ≤ Uo` of `Z`, this is the
chart `(α ⁻¹ᵁ Ω).toScheme ⟶ V` obtained from the universal property of the square applied to the
inclusion of `α ⁻¹ᵁ Ω` into `A` and to the restriction of `α` over `Ω`. -/
def chart {Z : Scheme.{u}} {Uo : Z.Opens} {V A : Scheme.{u}} {f : V ⟶ Uo.toScheme} {α : A ⟶ Z}
    {ρ : V ⟶ A} (hρ : IsPullback ρ f α Uo.ι) {Ω : Z.Opens} (hΩ : Ω ≤ Uo) :
    (α ⁻¹ᵁ Ω).toScheme ⟶ V :=
  hρ.flip.lift (α ∣_ Ω ≫ Z.homOfLE hΩ) (α ⁻¹ᵁ Ω).ι
    (by rw [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι])

/-- The chart `chart hρ hΩ` followed by `ρ` is the inclusion of `α ⁻¹ᵁ Ω` into `A`. -/
@[reassoc (attr := simp)]
lemma chart_comp {Z : Scheme.{u}} {Uo : Z.Opens} {V A : Scheme.{u}} {f : V ⟶ Uo.toScheme}
    {α : A ⟶ Z} {ρ : V ⟶ A} (hρ : IsPullback ρ f α Uo.ι) {Ω : Z.Opens} (hΩ : Ω ≤ Uo) :
    chart hρ hΩ ≫ ρ = (α ⁻¹ᵁ Ω).ι :=
  hρ.flip.lift_snd _ _ _

/-- The chart `chart hρ hΩ` exhibits `α ⁻¹ᵁ Ω` as the base change of `f : V ⟶ Uo.toScheme`
along the inclusion `Ω ⟶ Uo`. -/
theorem isPullback_chart {Z : Scheme.{u}} {Uo : Z.Opens} {V A : Scheme.{u}} {f : V ⟶ Uo.toScheme}
    {α : A ⟶ Z} {ρ : V ⟶ A} (hρ : IsPullback ρ f α Uo.ι) {Ω : Z.Opens} (hΩ : Ω ≤ Uo) :
    IsPullback (α ∣_ Ω) (chart hρ hΩ) (Z.homOfLE hΩ) f :=
  IsPullback.of_bot' (v₁₂ := Z.homOfLE hΩ)
    (by rw [Scheme.homOfLE_ι]; exact isPullback_morphismRestrict α Ω) hρ.flip

/-- For every open `Ω` of `Z` contained in `Uo`, the part `α ⁻¹ᵁ Ω` of `A` lying over `Ω` is the
part of `V` lying over `Ω`: there is a morphism `σ : (α ⁻¹ᵁ Ω).toScheme ⟶ V` compatible with `ρ`
such that `α ∣_ Ω` and `σ` form a cartesian square over `Ω.ι` and `f ≫ Uo.ι`. -/
theorem exists_chart {Z : Scheme.{u}} {Uo : Z.Opens} {V A : Scheme.{u}}
    (f : V ⟶ Uo.toScheme) (α : A ⟶ Z) (ρ : V ⟶ A) (hρ : IsPullback ρ f α Uo.ι)
    (Ω : Z.Opens) (hΩ : Ω ≤ Uo) :
    ∃ σ : (α ⁻¹ᵁ Ω).toScheme ⟶ V,
      IsPullback (α ∣_ Ω) σ Ω.ι (f ≫ Uo.ι) ∧ σ ≫ ρ = (α ⁻¹ᵁ Ω).ι := by
  refine ⟨chart hρ hΩ, ?_, chart_comp hρ hΩ⟩
  have t : IsPullback f (𝟙 V) Uo.ι (f ≫ Uo.ι) :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp]⟩
  simpa using (isPullback_chart hρ hΩ).paste_vert t

/-- The charts of `exists_chart` are compatible with shrinking the open: for opens `Ω' ≤ Ω ≤ Uo`,
if `σ` and `σ'` lift the inclusions of `α ⁻¹ᵁ Ω` and `α ⁻¹ᵁ Ω'` along `ρ`, then `σ'` is the
inclusion `α ⁻¹ᵁ Ω' ⟶ α ⁻¹ᵁ Ω` followed by `σ`. -/
theorem chart_comp_homOfLE {Z : Scheme.{u}} {Uo : Z.Opens} {V A : Scheme.{u}}
    {f : V ⟶ Uo.toScheme} {α : A ⟶ Z} {ρ : V ⟶ A} (hρ : IsPullback ρ f α Uo.ι)
    {Ω Ω' : Z.Opens} (h : Ω' ≤ Ω) (hΩ : Ω ≤ Uo)
    {σ : (α ⁻¹ᵁ Ω).toScheme ⟶ V} (hσ : σ ≫ ρ = (α ⁻¹ᵁ Ω).ι)
    {σ' : (α ⁻¹ᵁ Ω').toScheme ⟶ V} (hσ' : σ' ≫ ρ = (α ⁻¹ᵁ Ω').ι) :
    A.homOfLE (show α ⁻¹ᵁ Ω' ≤ α ⁻¹ᵁ Ω from fun _ hx ↦ h hx) ≫ σ = σ' := by
  have : IsOpenImmersion ρ := MorphismProperty.of_isPullback hρ.flip inferInstance
  rw [← cancel_mono ρ, Category.assoc, hσ, hσ', Scheme.homOfLE_ι]

end

end Stacks.OpenBaseChangeCharts
