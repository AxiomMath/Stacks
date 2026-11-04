module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibred categories over a slice category (Stacks 02XR)

If `p : S ⥤ C` is a fibred category which factors as `p = p' ⋙ Over.forget U` through the
slice category `Over U = C/U`, then the factoring functor `p' : S ⥤ Over U` is itself a
fibred category.

## Main results

* `CategoryTheory.Functor.IsFibered.of_comp_over`: if a fibred category `p : S ⥤ C` factors as
  `p' ⋙ Over.forget U`, then `p' : S ⥤ Over U` is a fibred category.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type*} [Category C] {S : Type*} [Category S] (U : C) (p' : S ⥤ Over U)

/-- If the composite `p' ⋙ Over.forget U` lifts `(Over.forget U).map g` along `φ`,
then the domain of `g` in `Over U` is determined to be `p'.obj a`. -/
private lemma domain_eq_of_comp_forget
    {a b : S} {R : Over U} (g : R ⟶ p'.obj b) (φ : a ⟶ b)
    (h : (p' ⋙ Over.forget U).IsHomLift ((Over.forget U).map g) φ) :
    R = p'.obj a := by
  have := h
  have hR : R.left = (p'.obj a).left :=
    (IsHomLift.domain_eq (p' ⋙ Over.forget U) ((Over.forget U).map g) φ).symm
  have hf : (Over.forget U).map g
      = eqToHom hR ≫ (p' ⋙ Over.forget U).map φ ≫ 𝟙 _ :=
    IsHomLift.fac (p' ⋙ Over.forget U) ((Over.forget U).map g) φ
  simp only [Over.forget_obj, Over.forget_map, Functor.comp_obj, Functor.comp_map,
    Category.comp_id] at hf
  have hR' : R.left = (p'.obj a).left := hR
  rcases R with ⟨RL, RR, Rh⟩
  subst hR'
  simp only [eqToHom_refl, Category.id_comp] at hf
  have hRw : g.left ≫ (p'.obj b).hom = Rh := Over.w g
  have hRh : Rh = (p'.obj a).hom := by rw [← hRw, hf, Over.w (p'.map φ)]
  subst hRh
  obtain rfl : RR = (p'.obj a).right := Subsingleton.elim _ _
  rfl

/-- `IsHomLift` for the composite `p' ⋙ Over.forget U` gives `IsHomLift` for `p'`. -/
private lemma isHomLift_of_comp_forget'
    {a b : S} {R : Over U} (g : R ⟶ p'.obj b) (φ : a ⟶ b)
    (h : (p' ⋙ Over.forget U).IsHomLift ((Over.forget U).map g) φ) :
    p'.IsHomLift g φ := by
  obtain rfl : R = p'.obj a := domain_eq_of_comp_forget U p' g φ h
  obtain rfl : p'.map φ = g :=
    (Over.forget U).map_injective (@IsHomLift.eq_of_isHomLift _ _ _ _
      (p' ⋙ Over.forget U) a b ((Over.forget U).map g) φ h).symm
  exact CategoryTheory.IsHomLift.map p' φ

/-- `IsHomLift` for `p'` gives `IsHomLift` for the composite `p' ⋙ Over.forget U`. -/
private lemma isHomLift_comp_forget_of_isHomLift
    {a' b' : S} {R' T' : Over U} (g' : R' ⟶ T') (φ' : a' ⟶ b')
    (h : p'.IsHomLift g' φ') :
    (p' ⋙ Over.forget U).IsHomLift ((Over.forget U).map g') φ' := by
  cases h
  exact ⟨_⟩

/-- Strong cartesianness of `φ` over `(Over.forget U).map g` for the composite
transfers to strong cartesianness of `φ` over `g` for `p'`. -/
private lemma isStronglyCartesian_of_comp_forget'
    {a b : S} {R : Over U} (g : R ⟶ p'.obj b) (φ : a ⟶ b)
    (hp : (p' ⋙ Over.forget U).IsStronglyCartesian ((Over.forget U).map g) φ) :
    p'.IsStronglyCartesian g φ := by
  have : p'.IsHomLift g φ := isHomLift_of_comp_forget' U p' g φ hp.toIsHomLift
  refine @IsStronglyCartesian.mk _ _ _ _ _ _ _ _ _ _ _ ‹_› ?_
  intro a' g' φ' hφ'
  obtain rfl : R = p'.obj a := domain_eq_of_comp_forget U p' g φ hp.toIsHomLift
  have : (p' ⋙ Over.forget U).IsHomLift ((Over.forget U).map (g' ≫ g)) φ' :=
    isHomLift_comp_forget_of_isHomLift U p' (g' ≫ g) φ' hφ'
  obtain ⟨χ, ⟨hχ_lift, hχ_comp⟩, hχ_uniq⟩ :=
    IsStronglyCartesian.universal_property
      (p := p' ⋙ Over.forget U) (f := (Over.forget U).map g) (φ := φ)
      (g := (Over.forget U).map g') (f' := (Over.forget U).map (g' ≫ g)) (by simp) φ'
  refine ⟨χ, ⟨isHomLift_of_comp_forget' U p' g' χ hχ_lift, hχ_comp⟩, ?_⟩
  rintro χ₁ ⟨hχ₁_lift, hχ₁_comp⟩
  exact hχ_uniq χ₁ ⟨isHomLift_comp_forget_of_isHomLift U p' g' χ₁ hχ₁_lift, hχ₁_comp⟩

/-- If a fibred category `p : S ⥤ C` factors as `p' ⋙ Over.forget U` through the slice
category `Over U`, then `p' : S ⥤ Over U` is a fibred category. -/
@[stacks 02XR]
theorem IsFibered.of_comp_over (p : S ⥤ C)
    [p.IsFibered] (h : p' ⋙ Over.forget U = p) :
    p'.IsFibered := by
  subst h
  apply IsFibered.of_exists_isStronglyCartesian
  intro a R g
  obtain ⟨b, φ, hpc⟩ :=
    IsPreFibered.exists_isCartesian' (p := p' ⋙ Over.forget U)
      ((Over.forget U).map g)
  have : (p' ⋙ Over.forget U).IsCartesian ((Over.forget U).map g) φ := hpc
  exact ⟨b, φ, isStronglyCartesian_of_comp_forget' U p' g φ
    (IsFibered.isStronglyCartesian_of_isCartesian _ _ _)⟩

end CategoryTheory.Functor
