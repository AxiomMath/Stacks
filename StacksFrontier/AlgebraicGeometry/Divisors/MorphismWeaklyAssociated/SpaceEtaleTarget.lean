module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# The relative weak assassin over an étale morphism of the target

Let `g : X ⟶ Y'` be a morphism of algebraic spaces over `S`, let `ψ : Y' ⟶ Y` be étale and let
`𝓕` be an `𝒪_X`-module. A point of the relative weak assassin `WeakAss_{X/Y'}(𝓕)` of
Stacks 0CV0 then lies in `WeakAss_{X/Y}(𝓕)`: the fibre of `g` over a field-valued point `q` of
`Y'` sits inside the fibre of `g ≫ ψ` over the image of `q` in `Y`, and weak association is
carried across.

## Main definitions

* `AlgebraicGeometry.Space.etaleTargetBaseChange`, with its two projections
  `AlgebraicGeometry.Space.etaleTargetProjection` and
  `AlgebraicGeometry.Space.etaleTargetStructure`, is the base change `X ×_Y Y'` of `g ≫ ψ`
  along `ψ`, and `AlgebraicGeometry.Space.etaleTargetSection` is the section `(𝟙_X, g)` of its
  projection to `X`.

## Main results

* `AlgebraicGeometry.Space.isEtale_etaleTargetSection`: the section is étale.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_comp_of_isEtale`: the relative weak
  assassin over an étale morphism of the target is contained in the relative weak assassin over
  the target.
* `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_subset_comp_of_isEtale`: the same
  statement as a containment of sets.

## Implementation notes

The reverse containment, condition (5) implying condition (1) of Stacks 0CUZ, is
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_comp_of_isEtale`.

No finiteness or quasi-coherence hypothesis enters.

The module universe is that of the structure rings, which is the universe at which Stacks 0CUU,
and so the étale invariance of weak association, is available.

## References

* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Y' : AlgebraicSpaces B S hS} (g : X ⟶ Y') (ψ : Y' ⟶ Y)

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SpaceEtaleTarget :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_SpaceEtaleTarget
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The section of the base change -/

/-- The base change `X ×_Y Y'` of `g ≫ ψ` along `ψ`. -/
noncomputable abbrev etaleTargetBaseChange : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS (g ≫ ψ) ψ

/-- The projection of `X ×_Y Y'` to `X`. -/
noncomputable abbrev etaleTargetProjection : etaleTargetBaseChange B S hS g ψ ⟶ X :=
  ObjectProperty.homMk (pullback.fst (g ≫ ψ).hom ψ.hom)

/-- The projection of `X ×_Y Y'` to `Y'`. -/
noncomputable abbrev etaleTargetStructure : etaleTargetBaseChange B S hS g ψ ⟶ Y' :=
  ObjectProperty.homMk (pullback.snd (g ≫ ψ).hom ψ.hom)

/-- The square presenting `X ×_Y Y'` as the base change of `g ≫ ψ` along `ψ`. -/
theorem isPullback_etaleTargetBaseChange :
    IsPullback (etaleTargetProjection B S hS g ψ) (etaleTargetStructure B S hS g ψ)
      (g ≫ ψ) ψ :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS (g ≫ ψ) ψ

/-- The projection of `X ×_Y Y'` to `X` is étale, being a base change of `ψ`. -/
theorem isEtale_etaleTargetProjection (hψ : IsEtale B S hS ψ.hom) :
    IsEtale B S hS (etaleTargetProjection B S hS g ψ).hom :=
  isEtale_of_isPullback B S hS (etaleTargetStructure B S hS g ψ)
    (etaleTargetProjection B S hS g ψ) ψ (g ≫ ψ)
    (isPullback_etaleTargetBaseChange B S hS g ψ).flip hψ

/-- The section `(𝟙_X, g)` of the projection `X ×_Y Y' ⟶ X`. -/
noncomputable def etaleTargetSection : X ⟶ etaleTargetBaseChange B S hS g ψ :=
  ObjectProperty.homMk (pullback.lift (𝟙 X.1) g.hom
    ((Category.id_comp (g ≫ ψ).hom).trans rfl))

/-- The section is a section of the projection to `X`. -/
theorem etaleTargetSection_comp_projection :
    etaleTargetSection B S hS g ψ ≫ etaleTargetProjection B S hS g ψ = 𝟙 X :=
  (ObjectProperty.fullyFaithfulι _).map_injective (pullback.lift_fst _ _ _)

/-- The section lies over `Y'` through `g`. -/
theorem etaleTargetSection_comp_structure :
    etaleTargetSection B S hS g ψ ≫ etaleTargetStructure B S hS g ψ = g :=
  (ObjectProperty.fullyFaithfulι _).map_injective (pullback.lift_snd _ _ _)

/-- **Stacks 03FV for the section of the base change.** The section `(𝟙_X, g)` is étale. -/
theorem isEtale_etaleTargetSection (hψ : IsEtale B S hS ψ.hom) :
    IsEtale B S hS (etaleTargetSection B S hS g ψ).hom :=
  isEtale_of_isEtale_over B S hS X.2 (etaleTargetBaseChange B S hS g ψ).2 X.2
    (etaleTargetSection B S hS g ψ).hom (𝟙 X.1) (etaleTargetProjection B S hS g ψ).hom
    (isEtale_id B S hS X.1) (isEtale_etaleTargetProjection B S hS g ψ hψ)
    (congrArg (fun k : X ⟶ X ↦ k.hom) (etaleTargetSection_comp_projection B S hS g ψ))

/-- The pullback of `𝓕` along the section identifies with `𝓕` itself: pulling back along the
section and then along the projection is pulling back along their composite, which is the
identity of `X`. -/
noncomputable def etaleTargetSectionModuleIso (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS (etaleTargetSection B S hS g ψ)).obj
        ((modulePullback B S hS (etaleTargetProjection B S hS g ψ)).obj F) ≅ F :=
  (modulePullbackCompIso B S hS (etaleTargetSection B S hS g ψ)
      (etaleTargetProjection B S hS g ψ)).app F ≪≫
    eqToIso (congrArg (fun k : X ⟶ X ↦ (modulePullback B S hS k).obj F)
      (etaleTargetSection_comp_projection B S hS g ψ)) ≪≫
    (modulePullbackIdIso B S hS X).app F

/-! ### The containment of relative weak assassins -/

/-- **Stacks 0CUZ, the relative weak assassin over an étale morphism of the target.** Let
`g : X ⟶ Y'` be a morphism of algebraic spaces over `S`, let `ψ : Y' ⟶ Y` be étale and let `𝓕`
be an `𝒪_X`-module. A point of `WeakAss_{X/Y'}(𝓕)` lies in `WeakAss_{X/Y}(𝓕)`.

Under locally Noetherian fibres these are the sets the source writes `Ass_{X/Y'}(𝓕)` and
`Ass_{X/Y}(𝓕)`. -/
theorem isRelativeWeaklyAssociatedPoint_comp_of_isEtale (hψ : IsEtale B S hS ψ.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) {x : points B S hS X.1}
    (hx : IsRelativeWeaklyAssociatedPoint B S hS g F x) :
    IsRelativeWeaklyAssociatedPoint B S hS (g ≫ ψ) F x := by
  have hsec : IsRelativeWeaklyAssociatedPoint B S hS
      (etaleTargetSection B S hS g ψ ≫ etaleTargetStructure B S hS g ψ)
      ((modulePullback B S hS (etaleTargetSection B S hS g ψ)).obj
        ((modulePullback B S hS (etaleTargetProjection B S hS g ψ)).obj F)) x := by
    rw [etaleTargetSection_comp_structure B S hS g ψ]
    exact (isRelativeWeaklyAssociatedPoint_congr g
      (etaleTargetSectionModuleIso B S hS g ψ F) x).2 hx
  have hbc := isRelativeWeaklyAssociatedPoint_of_baseChange B S hS
    (f := g ≫ ψ) (g := ψ) (f' := etaleTargetStructure B S hS g ψ)
    (g' := etaleTargetProjection B S hS g ψ) (IsPullback.of_hasPullback (g ≫ ψ).hom ψ.hom) F
    ((isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS
      (etaleTargetSection B S hS g ψ) (isEtale_etaleTargetSection B S hS g ψ hψ)
      (etaleTargetStructure B S hS g ψ)
      ((modulePullback B S hS (etaleTargetProjection B S hS g ψ)).obj F) x).1 hsec)
  have hpt : pointsMap B S hS (etaleTargetBaseChange B S hS g ψ).1
      (etaleTargetProjection B S hS g ψ).hom
      (pointsMap B S hS X.1 (etaleTargetSection B S hS g ψ).hom x) = x := by
    have hcomp : (etaleTargetSection B S hS g ψ).hom ≫
        (etaleTargetProjection B S hS g ψ).hom = 𝟙 X.1 :=
      pullback.lift_fst _ _ _
    have h := congrArg (fun k : X.1 ⟶ X.1 ↦ pointsMap B S hS X.1 k x) hcomp
    simp only [pointsMap_comp, Function.comp_apply, pointsMap_id, id_eq] at h
    exact h
  exact hpt ▸ hbc

/-- **Stacks 0CUZ, the relative weak assassin over an étale morphism of the target**, as a
containment of sets: `WeakAss_{X/Y'}(𝓕) ⊆ WeakAss_{X/Y}(𝓕)` for `ψ : Y' ⟶ Y` étale. -/
theorem relativeWeaklyAssociatedPoints_subset_comp_of_isEtale (hψ : IsEtale B S hS ψ.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    relativeWeaklyAssociatedPoints B S hS g F ⊆
      relativeWeaklyAssociatedPoints B S hS (g ≫ ψ) F :=
  fun _ hx => isRelativeWeaklyAssociatedPoint_comp_of_isEtale B S hS g ψ hψ F hx

end AlgebraicGeometry.Space

end
