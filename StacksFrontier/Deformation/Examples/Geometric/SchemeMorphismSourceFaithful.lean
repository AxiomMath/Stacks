module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSource

/-!
# Faithfulness of the source-forgetful functor on deformations of a scheme morphism

Let `f : X ⟶ Y` be a morphism of schemes over the residue field `k`. Forgetting the family that
deforms `Y` gives the functor `Deformation.Examples.schemeMorphismSourceForgetful` from
deformations of `f` to deformations of `X`. This functor is faithful as soon as the comparison map
`𝒪_{Q.target} ⟶ (Q.morphism)_* 𝒪_{Q.source}` of every deformation `Q` of `f` is injective on
sections over each open.

## Main results

* `AlgebraicGeometry.Scheme.Hom.eq_of_comp_eq_of_mono_app`: two morphisms of schemes out of
  `V` with the same map of underlying spaces are equal as soon as they agree after
  precomposition with a morphism `g : U ⟶ V` whose comparison map on sections is a
  monomorphism over every open.
* `Deformation.Examples.specialTarget_surjective`: the identification of the fibre over the
  closed point of the target family of a deformation of `f` is surjective on points.
* `Deformation.Examples.target_base_eq`: any two parallel arrows of deformations of `f` induce
  the same map of underlying topological spaces on the target families.
* `Deformation.Examples.schemeMorphismSourceForgetful_faithful_of_mono_app`: the
  source-forgetful functor is faithful once the comparison map on structure sheaves of each
  deformation of `f` is a monomorphism on sections over every open.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An endomorphism of an open of a scheme acts on sections as the identity. -/
theorem Scheme.presheaf_map_endo_eq_id {X : Scheme.{u}} {A : (X.Opens)ᵒᵖ} (m : A ⟶ A) :
    X.presheaf.map m = 𝟙 _ := by
  rw [Subsingleton.elim m (𝟙 A), X.presheaf.map_id]

/-- Two morphisms of schemes `a, a' : V ⟶ Z` inducing the same map of underlying topological
spaces are equal as soon as they agree after precomposition with a morphism `g : U ⟶ V` whose
comparison map `𝒪_V ⟶ g_* 𝒪_U` is a monomorphism on sections over every open. -/
theorem Scheme.Hom.eq_of_comp_eq_of_mono_app {U V Z : Scheme.{u}} (g : U ⟶ V)
    (hg : ∀ W : V.Opens, Mono (g.app W)) {a a' : V ⟶ Z} (hb : a.base = a'.base)
    (hcomp : g ≫ a = g ≫ a') : a = a' := by
  refine Scheme.Hom.ext hb fun W => ?_
  have := hg (a' ⁻¹ᵁ W)
  have h1 := Scheme.Hom.congr_app hcomp W
  simp only [Scheme.Hom.comp_app] at h1
  rw [← cancel_mono (g.app (a' ⁻¹ᵁ W))]
  simp only [Category.assoc, g.naturality]
  simp only [← Category.assoc, h1]
  simp [← Functor.map_comp, Scheme.presheaf_map_endo_eq_id]

end AlgebraicGeometry

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- The morphism of base spectra underlying the identification of the fibre over the closed
point of a deformation of `f` is the closed point of the spectrum of the base. -/
theorem specialTargetBaseSpecMap_eq (P : schemeMorphismDeformationCategory f pX pY hf) :
    baseSpecMap P.hom.base = residueSpecMap P.left.base :=
  baseSpecMap_eq_residueSpecMap P.left.base P.hom.base

/-- The identification of the fibre over the closed point of the target family of a deformation
of `f` is a closed immersion. -/
theorem specialTarget_isClosedImmersion (P : schemeMorphismDeformationCategory f pX pY hf) :
    IsClosedImmersion P.hom.target :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    P.hom.target_pullback.flip
    (by
      rw [specialTargetBaseSpecMap_eq f pX pY hf P]
      exact residueSpecMap_isClosedImmersion P.left.base)

/-- The identification of the fibre over the closed point of the target family of a deformation
of `f` is surjective on points. -/
theorem specialTarget_surjective (P : schemeMorphismDeformationCategory f pX pY hf) :
    Function.Surjective P.hom.target :=
  (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
    P.hom.target_pullback.flip
    (by
      rw [specialTargetBaseSpecMap_eq f pX pY hf P]
      exact ⟨residueSpecMap_surjective P.left.base⟩)).surj

/-- An arrow of deformations of `f` is compatible with the identifications of the fibre over the
closed point of the target families. -/
theorem specialTarget_comp {P Q : schemeMorphismDeformationCategory f pX pY hf} (h : P ⟶ Q) :
    Q.hom.target ≫ h.left.target = P.hom.target :=
  congrArg SchemeMorphismFamily.Hom.target (Over.w h)

/-- Any two parallel arrows of deformations of `f` induce the same map of underlying
topological spaces on the target families. -/
theorem target_base_eq {P Q : schemeMorphismDeformationCategory f pX pY hf} (h h' : P ⟶ Q) :
    h.left.target.base = h'.left.target.base := by
  refine TopCat.hom_ext (ContinuousMap.ext fun y => ?_)
  obtain ⟨z, rfl⟩ := specialTarget_surjective f pX pY hf Q y
  have e : (Q.hom.target ≫ h.left.target) z = (Q.hom.target ≫ h'.left.target) z := by
    rw [specialTarget_comp f pX pY hf h, specialTarget_comp f pX pY hf h']
  simpa using e

/-- The source-forgetful functor on deformations of `f` is faithful as soon as the comparison
map `𝒪_{Q.target} ⟶ (Q.morphism)_* 𝒪_{Q.source}` of every deformation `Q` of `f` is a
monomorphism on sections over every open. -/
theorem schemeMorphismSourceForgetful_faithful_of_mono_app
    (hmono : ∀ (Q : schemeMorphismDeformationCategory f pX pY hf) (W : Q.left.target.Opens),
      Mono (Q.left.morphism.app W)) :
    (schemeMorphismSourceForgetful f pX pY hf).Faithful := by
  refine ⟨fun {P Q} h h' heq ↦ ?_⟩
  have hs : h.left.source = h'.left.source := congrArg SchemeDeformationCategory.Hom.map heq
  refine Over.OverMorphism.ext (SchemeMorphismFamily.Hom.ext
    (congrArg SchemeDeformationCategory.Hom.base heq) hs
    (Scheme.Hom.eq_of_comp_eq_of_mono_app Q.left.morphism (hmono Q)
      (target_base_eq f pX pY hf h h') ?_))
  rw [h.left.source_pullback.w, h'.left.source_pullback.w, hs]

end Deformation.Examples

end
