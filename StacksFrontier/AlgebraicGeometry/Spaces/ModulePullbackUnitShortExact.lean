module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeDualShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackMonoidal

/-!
# The inverse image of an extension of a finite locally free module by `𝒪`

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and let

  `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0`

be a short exact sequence of `𝒪_X`-modules with `ℰ`, `ℱ` finite locally free. Then the inverse
image `0 ⟶ 𝒪_Y ⟶ g^*ℰ ⟶ g^*ℱ ⟶ 0` is short exact, where `𝒪_Y ≅ g^*𝒪_X` is the unit comparison of
the monoidal functor `g^*` (Stacks 03EL).

The inverse image is right exact, being a left adjoint, so only the monomorphy of
`𝒪_Y ⟶ g^*ℰ` is at stake. It is read off the duals: the dual sequence
`0 ⟶ ℱ^∨ ⟶ ℰ^∨ ⟶ 𝒪_X^∨ ⟶ 0` is short exact
(`AlgebraicGeometry.Space.shortExact_rightDual`), so the pairing `ℰ^∨ ⊗ 𝒪_X ⟶ 𝒪_X`,
`φ ⊗ a ↦ φ(a·1)`, is an epimorphism; `g^*` keeps it an epimorphism and carries it, through its
monoidal structure, to the pairing `g^*ℰ^∨ ⊗ 𝒪_Y ⟶ 𝒪_Y` of the section `s : 𝒪_Y ⟶ g^*ℰ`. A map
`s : 𝟙 ⟶ ℰ'` out of the unit whose pairing with some `χ : X' ⊗ ℰ' ⟶ 𝟙` is an epimorphism is a
monomorphism (`CategoryTheory.mono_of_epi_whiskerLeft_comp`): for `h : W ⟶ 𝟙` with
`h ≫ s = 0` the pairing kills `X' ⊗ W`, and that composite is `h` after the epimorphism
`φ₀ ⊗ W`.

## Main results

* `CategoryTheory.mono_of_epi_whiskerLeft_comp`: the monomorphy criterion above.
* `AlgebraicGeometry.Space.exists_shortExact_modulePullback_of_tensorUnit`: the inverse image of
  `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` is `0 ⟶ 𝒪_Y ⟶ g^*ℰ ⟶ g^*ℱ ⟶ 0`, short exact.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits

universe u

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- For `h : W ⟶ 𝟙` and `φ : X ⟶ 𝟙`, `(X ◁ h) ≫ ρ_X ≫ φ = (φ ▷ W) ≫ λ_W ≫ h`: a map into the
unit is "linear" in the unit variable. -/
theorem whiskerLeft_comp_rightUnitor_hom_comp {X W : C} (h : W ⟶ 𝟙_ C) (φ : X ⟶ 𝟙_ C) :
    X ◁ h ≫ (ρ_ X).hom ≫ φ = φ ▷ W ≫ (λ_ W).hom ≫ h := by
  rw [← rightUnitor_naturality, ← Category.assoc, whisker_exchange, Category.assoc,
    ← unitors_equal, leftUnitor_naturality]

variable [Preadditive C] [MonoidalPreadditive C]

/-- **A map out of the unit with an epimorphic pairing is a monomorphism.** Let `s : 𝟙 ⟶ E` and
`χ : X ⊗ E ⟶ 𝟙` be such that `φ₀ = ρ_X⁻¹ ≫ (X ◁ s) ≫ χ : X ⟶ 𝟙` stays an epimorphism after
tensoring on the right with every object. Then `s` is a monomorphism. -/
theorem mono_of_epi_whiskerLeft_comp {X E : C} (s : 𝟙_ C ⟶ E) (χ : X ⊗ E ⟶ 𝟙_ C)
    (hR : ∀ W : C, Epi (((ρ_ X).inv ≫ X ◁ s ≫ χ) ▷ W)) : Mono s := by
  refine Preadditive.mono_of_cancel_zero _ fun {W} h hh => ?_
  have h1 : X ◁ h ≫ (ρ_ X).hom ≫ ((ρ_ X).inv ≫ X ◁ s ≫ χ) = 0 := by
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hh,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]
  rw [whiskerLeft_comp_rightUnitor_hom_comp] at h1
  have := hR W
  have h3 : (λ_ W).hom ≫ h = 0 := (cancel_epi _).1 (h1.trans comp_zero.symm)
  simpa using congrArg ((λ_ W).inv ≫ ·) h3

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory modulesMonoidalClosed
  modulesMonoidalPreadditive

/-- The abelian structure of the `𝒪`-modules, at the universe of the schemes. -/
local instance abelianModulesUnitShortExact (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

/-- Tensoring an epimorphism of `𝒪`-modules on the right with any module gives an epimorphism:
tensoring on the left is a left adjoint, and the tensor product is braided. -/
theorem epi_whiskerRight_modules {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {A A' : Modules.{u, u} B S hS F hF} (φ : A ⟶ A') [Epi φ]
    (W : Modules.{u, u} B S hS F hF) : Epi (φ ▷ W) := by
  have : (tensorLeft W).IsLeftAdjoint := ⟨_, ⟨ihom.adjunction W⟩⟩
  have hW : Epi (W ◁ φ) := (tensorLeft W).map_epi φ
  have h : φ ▷ W = (β_ A W).hom ≫ W ◁ φ ≫ (β_ A' W).inv := by
    rw [← BraidedCategory.braiding_naturality_left_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  exact @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _
    (@epi_comp _ _ _ _ _ _ hW _ (IsIso.epi_of_iso _))

variable {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)

/-- **The inverse image of an extension of a finite locally free module by `𝒪`.** If
`0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` is a short exact sequence of `𝒪_X`-modules with `ℰ` and `ℱ` finite locally
free, then for every morphism `g : Y ⟶ X` of algebraic spaces there is a short exact sequence
`0 ⟶ 𝒪_Y ⟶ g^*ℰ ⟶ g^*ℱ ⟶ 0` whose second map is `g^*` of the given one (the first map is the
unit comparison `𝒪_Y ≅ g^*𝒪_X` followed by `g^*` of the given one). -/
theorem exists_shortExact_modulePullback_of_tensorUnit {E F : Modules.{u, u} B S hS X.1 X.2}
    (i : 𝟙_ (Modules.{u, u} B S hS X.1 X.2) ⟶ E) (q : E ⟶ F) (hiq : i ≫ q = 0)
    (hT : (ShortComplex.mk i q hiq).ShortExact)
    (h1 : SheafOfModules.IsFiniteLocallyFreeOnSite (𝟙_ (Modules.{u, u} B S hS X.1 X.2)))
    (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    ∃ (i' : 𝟙_ (Modules.{u, u} B S hS Y.1 Y.2) ⟶ (modulePullback B S hS g).obj E)
      (h : i' ≫ (modulePullback B S hS g).map q = 0),
      (ShortComplex.mk i' ((modulePullback B S hS g).map q) h).ShortExact := by
  let := modulePullbackMonoidal g
  let Φ := modulePullback B S hS g
  let adj := modulePullbackAdjunction B S hS g
  have : Φ.IsLeftAdjoint := adj.isLeftAdjoint
  let := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS X.1 X.2 _ h1
  let := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS X.1 X.2 E hE
  let := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS X.1 X.2 F hF
  -- the pairing `ℰ^∨ ⊗ 𝒪 ⟶ 𝒪` of the section `i` is an epimorphism
  have hdual := shortExact_rightDual B S hS X.1 X.2 hT
  have hiepi : Epi (rightAdjointMate i) := hdual.epi_g
  have hev1 : Epi (ε_ (𝟙_ (Modules.{u, u} B S hS X.1 X.2))
      (𝟙_ (Modules.{u, u} B S hS X.1 X.2))ᘁ) := by
    have h0 : Epi (η_ (𝟙_ (Modules.{u, u} B S hS X.1 X.2)) (𝟙_ (Modules.{u, u} B S hS X.1 X.2))ᘁ ▷
        𝟙_ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ (𝟙_ (Modules.{u, u} B S hS X.1 X.2))
          (𝟙_ (Modules.{u, u} B S hS X.1 X.2))ᘁ) := by
      rw [ExactPairing.evaluation_coevaluation]
      exact @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _ (IsIso.epi_of_iso _)
    rw [← Category.assoc] at h0
    have h1 := epi_of_epi (η_ (𝟙_ (Modules.{u, u} B S hS X.1 X.2))
      (𝟙_ (Modules.{u, u} B S hS X.1 X.2))ᘁ ▷ 𝟙_ _ ≫ (α_ _ _ _).hom)
      (_ ◁ ε_ (𝟙_ (Modules.{u, u} B S hS X.1 X.2)) (𝟙_ (Modules.{u, u} B S hS X.1 X.2))ᘁ)
    rw [id_whiskerLeft] at h1
    have h2 : ε_ (𝟙_ (Modules.{u, u} B S hS X.1 X.2)) (𝟙_ (Modules.{u, u} B S hS X.1 X.2))ᘁ =
        (λ_ _).inv ≫ ((λ_ _).hom ≫ ε_ (𝟙_ (Modules.{u, u} B S hS X.1 X.2))
          (𝟙_ (Modules.{u, u} B S hS X.1 X.2))ᘁ ≫ (λ_ _).inv) ≫ (λ_ _).hom := by
      simp
    rw [h2]
    exact @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _
      (@epi_comp _ _ _ _ _ _ h1 _ (IsIso.epi_of_iso _))
  have he : Epi (Eᘁ ◁ i ≫ ε_ E Eᘁ) := by
    rw [← rightAdjointMate_comp_evaluation, MonoidalCategory.whiskerRight_id]
    exact @epi_comp _ _ _ _ _ _ (@epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _
      (@epi_comp _ _ _ _ _ _ hiepi _ (IsIso.epi_of_iso _))) _ hev1
  have hΦe : Epi (Φ.map (Eᘁ ◁ i ≫ ε_ E Eᘁ)) := Φ.map_epi _
  -- its inverse image is the pairing of the section `s = ε ≫ g^*i` of `g^*ℰ`
  let s := Functor.LaxMonoidal.ε Φ ≫ Φ.map i
  let χ := Functor.LaxMonoidal.μ Φ Eᘁ E ≫ Φ.map (ε_ E Eᘁ) ≫ inv (Functor.LaxMonoidal.ε Φ)
  have hψ : Epi ((ρ_ (Φ.obj Eᘁ)).inv ≫ Φ.obj Eᘁ ◁ s ≫ χ) := by
    have hfac : (ρ_ (Φ.obj Eᘁ)).inv ≫ Φ.obj Eᘁ ◁ s ≫ χ =
        ((ρ_ (Φ.obj Eᘁ)).inv ≫ Φ.obj Eᘁ ◁ Functor.LaxMonoidal.ε Φ ≫
          Functor.LaxMonoidal.μ Φ Eᘁ (𝟙_ _)) ≫ Φ.map (Eᘁ ◁ i ≫ ε_ E Eᘁ) ≫
            inv (Functor.LaxMonoidal.ε Φ) := by
      simp only [s, χ, MonoidalCategory.whiskerLeft_comp, Category.assoc, Functor.map_comp,
        Functor.LaxMonoidal.μ_natural_right_assoc]
    have : IsIso (Functor.LaxMonoidal.ε Φ) :=
      inferInstanceAs (IsIso (Functor.Monoidal.εIso Φ).hom)
    have : IsIso (Functor.LaxMonoidal.μ Φ Eᘁ (𝟙_ _)) :=
      inferInstanceAs (IsIso (Functor.Monoidal.μIso Φ Eᘁ (𝟙_ _)).hom)
    have : IsIso (Φ.obj Eᘁ ◁ Functor.LaxMonoidal.ε Φ) :=
      MonoidalCategory.whiskerLeft_isIso _ _
    have hiso : IsIso ((ρ_ (Φ.obj Eᘁ)).inv ≫ Φ.obj Eᘁ ◁ Functor.LaxMonoidal.ε Φ ≫
        Functor.LaxMonoidal.μ Φ Eᘁ (𝟙_ _)) := by
      infer_instance
    rw [hfac]
    exact @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _
      (@epi_comp _ _ _ _ _ _ hΦe _ (IsIso.epi_of_iso _))
  have hs : Mono s := mono_of_epi_whiskerLeft_comp s χ fun W => epi_whiskerRight_modules _ W
  have hmono : Mono (Φ.map i) := by
    have : Φ.map i = inv (Functor.LaxMonoidal.ε Φ) ≫ s := by simp [s]
    rw [this]
    exact @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _ hs
  have hexact : ((ShortComplex.mk i q hiq).map Φ).Exact :=
    hT.exact.map_of_epi_of_preservesCokernel Φ hT.epi_g inferInstance
  have := hT.epi_g
  have hmap : ((ShortComplex.mk i q hiq).map Φ).ShortExact :=
    { exact := hexact
      mono_f := hmono
      epi_g := Φ.map_epi q }
  refine ⟨s, ?_, ?_⟩
  · change Functor.LaxMonoidal.ε Φ ≫ Φ.map i ≫ Φ.map q = 0
    rw [← Φ.map_comp, hiq, Φ.map_zero, comp_zero]
  refine ShortComplex.shortExact_of_iso ?_ hmap
  exact ShortComplex.isoMk (asIso (Functor.LaxMonoidal.ε Φ)).symm (Iso.refl _) (Iso.refl _)
    (by simp [s]) ((Category.id_comp _).trans (Category.comp_id _).symm)

end AlgebraicGeometry.Space

end
