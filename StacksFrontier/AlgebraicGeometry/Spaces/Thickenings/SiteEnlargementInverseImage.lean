module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementPushforward
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare

/-!
# Inverse images commute with enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` for `B` and let `f' : X' ⟶ Y'` be its inverse image on the enlarged
site. Write `R_X` and `R_Y` for restriction along the transport of étale charts. The comparison
`f'_* ⋙ R_Y ≅ R_X ⋙ f_*` of direct images
(`AlgebraicGeometry.SiteEnlargement.pushforwardComparison`) has a mate

`R_Y ⋙ f⁻¹ ⟶ f'⁻¹ ⋙ R_X`

with respect to the adjunctions `f⁻¹ ⊣ f_*` and `f'⁻¹ ⊣ f'_*`, and since the restrictions are
equivalences this mate is an isomorphism. At the structure sheaf of `Y'` it carries the
structure map `f'⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}` to the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`, on underlying sheaves
of sets.

## Main definitions

* `AlgebraicGeometry.SiteEnlargement.inverseImageComparison`: the mate, as a natural
  transformation of functors of sheaves of sets.

## Main results

* `AlgebraicGeometry.SiteEnlargement.isIso_app_mateEquiv_symm`: the mate of an isomorphism along
  fully faithful functors, the second essentially surjective, is an isomorphism.
* `AlgebraicGeometry.SiteEnlargement.isIso_inverseImageComparison`: the comparison of inverse
  images is an isomorphism.
* `AlgebraicGeometry.SiteEnlargement.inverseImageComparison_fSharpInverseImageForget`: the
  comparison carries the structure map `f'⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}` to the structure map
  `f⁻¹𝒪_Y ⟶ 𝒪_X`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace AlgebraicGeometry.SiteEnlargement

section Mates

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Postcomposition with an isomorphism is bijective. -/
theorem bijective_comp_iso {X₀ Y₀ Z₀ : F} (e : Y₀ ≅ Z₀) :
    Function.Bijective (fun y : X₀ ⟶ Y₀ => y ≫ e.hom) :=
  ⟨fun a b hab => by simpa using congrArg (· ≫ e.inv) hab, fun z => ⟨z ≫ e.inv, by simp⟩⟩

/-- Postcomposition with an isomorphism is bijective, in the category `E`. -/
theorem bijective_comp_iso' {X₀ Y₀ Z₀ : E} (e : Y₀ ≅ Z₀) :
    Function.Bijective (fun y : X₀ ⟶ Y₀ => y ≫ e.hom) :=
  ⟨fun a b hab => by simpa using congrArg (· ≫ e.inv) hab, fun z => ⟨z ≫ e.inv, by simp⟩⟩

/-- The adjunct of the mate of a square `τ`, followed by a morphism in the image of `H`, is the
image under `G` of the adjunct of the preimage, followed by `τ`. -/
theorem homEquiv_mateEquiv_symm_comp (τ : R₁ ⋙ G ⟶ H ⋙ R₂) (hH : H.FullyFaithful) (c : C)
    {d : D} (x : H.obj (L₁.obj c) ⟶ H.obj d) :
    adj₂.homEquiv _ _ ((((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ τ)).natTrans.app c) ≫ x) =
      G.map (adj₁.homEquiv _ _ (hH.preimage x)) ≫ τ.app d := by
  have hu := unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ τ) c
  have hn := τ.naturality (hH.preimage x)
  simp only [Functor.comp_map, hH.map_preimage] at hn
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R₂.map_comp, ← Category.assoc]
  show _ ≫ _ = _
  refine (congrArg (· ≫ R₂.map x) hu.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  show G.map (adj₁.unit.app c) ≫ τ.app (L₁.obj c) ≫ R₂.map x = _
  refine (congrArg (G.map (adj₁.unit.app c) ≫ ·) hn.symm).trans ?_
  rw [G.map_comp, Category.assoc]

/-- **The mate of an isomorphism along fully faithful functors is an isomorphism**, as soon as the
functor on the target side is essentially surjective: precomposition with the mate is, up to the
adjunction bijections, a composite of bijections. -/
theorem isIso_app_mateEquiv_symm (τ : R₁ ⋙ G ≅ H ⋙ R₂) (hG : G.FullyFaithful)
    (hH : H.FullyFaithful) [H.EssSurj] (c : C) :
    IsIso (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ τ.hom)).natTrans.app c) := by
  let μc := ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ τ.hom)).natTrans.app c
  have key : ∀ d : D, Function.Bijective (fun x : H.obj (L₁.obj c) ⟶ H.obj d => μc ≫ x) := by
    intro d
    have h1 : (fun x : H.obj (L₁.obj c) ⟶ H.obj d => μc ≫ x) =
        (adj₂.homEquiv _ _).symm ∘ (fun y => y ≫ τ.hom.app d) ∘ G.map ∘ (adj₁.homEquiv _ _) ∘
          hH.preimage := by
      funext x
      apply (adj₂.homEquiv _ _).injective
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
      exact homEquiv_mateEquiv_symm_comp adj₁ adj₂ τ.hom hH c x
    rw [h1]
    refine (adj₂.homEquiv _ _).symm.bijective.comp (Function.Bijective.comp ?_
      ((hG.map_bijective _ _).comp ((adj₁.homEquiv _ _).bijective.comp hH.homEquiv.symm.bijective)))
    exact bijective_comp_iso' (τ.app d)
  rw [isIso_iff_coyoneda_map_bijective]
  intro T
  show Function.Bijective (fun x : H.obj (L₁.obj c) ⟶ T => μc ≫ x)
  let e := H.objObjPreimageIso T
  have h2 : (fun x : H.obj (L₁.obj c) ⟶ T => μc ≫ x) =
      (fun y => y ≫ e.hom) ∘ (fun x : H.obj (L₁.obj c) ⟶ H.obj (H.objPreimage T) => μc ≫ x) ∘
        (fun x => x ≫ e.inv) := by
    funext x
    simp
  rw [h2]
  exact (bijective_comp_iso e).comp ((key _).comp (bijective_comp_iso e.symm))

end Mates

open Space

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') {S : Scheme.{u}}
  {hS : B.Contains S} (hS' : B'.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Restriction of sheaves of sets along the transport of étale charts is fully faithful. -/
def restrictSheafFullyFaithful (X : AlgebraicSpaces B S hS) :
    (restrictSheaf h hS' X).FullyFaithful :=
  .ofFullyFaithful _

/-- Restriction of sheaves of sets along the transport of étale charts is essentially
surjective. -/
instance (X : AlgebraicSpaces B S hS) : (restrictSheaf h hS' X).EssSurj :=
  inferInstanceAs ((chartTransport B B' h S hS X).sheafPushforwardContinuous (Type u)
    (Space.SmallEtale.topology B S hS X.obj)
    (Space.SmallEtale.topology B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj)).EssSurj

/-- **Inverse images commute with enlarging the big fppf site**: the mate
`R_Y ⋙ f⁻¹ ⟶ f'⁻¹ ⋙ R_X` of the comparison of direct images. -/
def inverseImageComparison :
    restrictSheaf h hS' Y ⋙ (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage ⟶
      (smallEtaleRingedToposHom B' S hS'
          ((changeBigSite B B' h S hS).map f)).toToposHom.inverseImage ⋙
        restrictSheaf h hS' X :=
  ((mateEquiv (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f)).toToposHom.adj
    (smallEtaleRingedToposHom B S hS f).toToposHom.adj).symm
      (TwoSquare.mk _ _ _ _ (pushforwardComparison h hS' f).hom)).natTrans

/-- The comparison `R_Y ⋙ f⁻¹ ⟶ f'⁻¹ ⋙ R_X` of inverse images is an isomorphism: it is the mate of
an isomorphism along restrictions which are equivalences. -/
instance isIso_inverseImageComparison : IsIso (inverseImageComparison h hS' f) := by
  have : ∀ c, IsIso ((inverseImageComparison h hS' f).app c) := fun c =>
    isIso_app_mateEquiv_symm _ _ (pushforwardComparison h hS' f)
      (restrictSheafFullyFaithful h hS' Y) (restrictSheafFullyFaithful h hS' X) c
  exact NatIso.isIso_of_isIso_app _

/-- **The comparison of inverse images carries the structure map of `f'` to that of `f`**, on
underlying sheaves of sets: the comparison at the structure sheaf of `Y'`, followed by the
restriction of `f'⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}`, is `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
theorem inverseImageComparison_fSharpInverseImageForget :
    (inverseImageComparison h hS' f).app
        ((smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj Y)).forgetRing.obj
          (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj Y)).O) ≫
      (restrictSheaf h hS' X).map (RingedToposHom.fSharpInverseImageForget
        (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f))) =
      RingedToposHom.fSharpInverseImageForget (smallEtaleRingedToposHom B S hS f) := by
  apply ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _).injective
  refine (homEquiv_mateEquiv_symm_comp _ _ (pushforwardComparison h hS' f).hom
    (restrictSheafFullyFaithful h hS' X) _ _).trans ?_
  let g' := smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f)
  have e1 := (restrictSheafFullyFaithful h hS' X).preimage_map
    (RingedToposHom.fSharpInverseImageForget g')
  have e2 : g'.toToposHom.adj.homEquiv _ _ (RingedToposHom.fSharpInverseImageForget g') =
      RingedToposHom.forgetFSharp g' := Equiv.apply_symm_apply _ _
  refine (congrArg (fun z => (restrictSheaf h hS' Y).map (g'.toToposHom.adj.homEquiv _ _ z) ≫
    (pushforwardComparison h hS' f).hom.app _) e1).trans ?_
  refine (congrArg (fun z => (restrictSheaf h hS' Y).map z ≫
    (pushforwardComparison h hS' f).hom.app _) e2).trans ?_
  exact (pushforwardComparison_structureSharp h hS' f).trans (Equiv.apply_symm_apply _ _).symm

end AlgebraicGeometry.SiteEnlargement

end
