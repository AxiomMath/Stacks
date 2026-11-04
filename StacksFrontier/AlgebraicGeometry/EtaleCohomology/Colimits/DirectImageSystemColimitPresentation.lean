module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageOfPushforward
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemPresentationCriterion

/-!
# A sheaf on a limit is the colimit of the inverse images of its direct images

Let `X = lim X_i` be a directed limit of schemes with affine transition morphisms `f_{i'i}` and
projections `f_i : X ⟶ X_i`, and let `𝓕` be an abelian sheaf on `X_étale`. The direct images
`f_{i,*}𝓕` form a system of sheaves on `(X_i, f_{i'i})`
(`Stacks.EtaleCohomology.directImageSystem`), the counits `f_i⁻¹f_{i,*}𝓕 ⟶ 𝓕` are compatible
with its transition maps (`Stacks.EtaleCohomology.coneDirectImageCounit_cocone`), and
[Stacks, Tag 0EYN] asserts that they present

`𝓕 = colim f_i⁻¹f_{i,*}𝓕`.

This file proves that colimit assertion. By the recognition criterion
`Stacks.EtaleCohomology.EtaleSheafSystem.isPullbackColimitPresentation_of_forall_exists` it
suffices to see, for every object `V₀` of the small étale site of a stage `X_{i₀}`, that the
sections of `f_{k,*}𝓕` over `V₀ ×_{X_{i₀}} X_k` map bijectively to the sections of `𝓕` over
`V₀ ×_{X_{i₀}} X`. Both are sections of `𝓕` over the base change of `V₀` to `X`, and the map
between them is the restriction along the canonical identification of the two base changes: on
the small étale site of `X_{i₀}` it is the direct image along `f_{k i₀}` of the map adjoint to the
counit — an identity — followed by the comparison `f_{k i₀,*} f_{k,*} ≅ f_{i₀,*}`. It is
therefore an isomorphism.

## Main results

* `Stacks.EtaleCohomology.isIso_pushforwardLeg_directImageSystem`: the pushed-forward legs of the
  counits are isomorphisms.
* `Stacks.EtaleCohomology.isPullbackColimitPresentation_directImageSystem`: the colimit half of
  [Stacks, Tag 0EYN].

## References

* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)
  (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})

/-- **The pushed-forward legs of the counits are isomorphisms.** For `k ⟶ i₀` the leg
`f_{k i₀,*}f_{k,*}𝓕 ⟶ f_{i₀,*}𝓕` attached to the counit `f_k⁻¹f_{k,*}𝓕 ⟶ 𝓕` is the direct image
of the identity of `f_{k,*}𝓕` followed by the comparison `f_{k i₀,*}f_{k,*} ≅ f_{i₀,*}`. -/
theorem isIso_pushforwardLeg_directImageSystem {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) :
    IsIso ((directImageSystem D Ab.{u + 1} c 𝓕).pushforwardLeg c
      (coneDirectImageCounit c 𝓕) a) := by
  have h : (smallEtaleAdjunctionAb (c.π.app k)).homEquiv _ _ (coneDirectImageCounit c 𝓕 k) =
      𝟙 _ :=
    ((smallEtaleAdjunctionAb (c.π.app k)).homEquiv_unit _ _ _).trans
      ((smallEtaleAdjunctionAb (c.π.app k)).right_triangle_components 𝓕)
  have e : (directImageSystem D Ab.{u + 1} c 𝓕).pushforwardLeg c (coneDirectImageCounit c 𝓕) a =
      (systemPushforward D Ab.{u + 1} a).map (𝟙 _) ≫ (coneDirectImageCompAb c a).hom.app 𝓕 :=
    congrArg (fun z => (systemPushforward D Ab.{u + 1} a).map z ≫
      (coneDirectImageCompAb c a).hom.app 𝓕) h
  have hg : IsIso ((systemPushforward D Ab.{u + 1} a).map (𝟙 _) ≫
      (coneDirectImageCompAb c a).hom.app 𝓕) := inferInstance
  exact Eq.subst (motive := fun z => IsIso z) e.symm hg

/-- The components of the pushed-forward legs of the counits are bijective on sections. -/
theorem bijective_pushforwardLeg_directImageSystem_app {k i₀ : Iᵒᵖ} (a : k ⟶ i₀)
    (V₀ : (D.obj i₀).Etale) :
    Function.Bijective (((directImageSystem D Ab.{u + 1} c 𝓕).pushforwardLeg c
      (coneDirectImageCounit c 𝓕) a).hom.app (op V₀)) := by
  have := isIso_pushforwardLeg_directImageSystem c 𝓕 a
  have : IsIso ((sheafToPresheaf _ _).map ((directImageSystem D Ab.{u + 1} c 𝓕).pushforwardLeg c
      (coneDirectImageCounit c 𝓕) a)) := inferInstance
  have : IsIso (((sheafToPresheaf _ _).map ((directImageSystem D Ab.{u + 1} c 𝓕).pushforwardLeg
      c (coneDirectImageCounit c 𝓕) a)).app (op V₀)) := inferInstance
  exact ConcreteCategory.bijective_of_isIso _

variable [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
  {c}

/-- **[Stacks, Tag 0EYN], the colimit.** Let `X = lim X_i` be a directed limit of schemes with
affine transition morphisms and projections `f_i : X ⟶ X_i`, and let `𝓕` be an abelian sheaf on
`X_étale`. Then the counits `f_i⁻¹f_{i,*}𝓕 ⟶ 𝓕` present `𝓕 = colim f_i⁻¹f_{i,*}𝓕` over the
system of sheaves `(f_{i,*}𝓕, φ_{i'i})` of `Stacks.EtaleCohomology.directImageSystem`. -/
@[stacks 0EYN "the colimit `𝓕 = colim f_i⁻¹f_{i,*}𝓕`"]
theorem isPullbackColimitPresentation_directImageSystem (hc : IsLimit c) :
    LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕
      (directImageSystem D Ab.{u + 1} c 𝓕) (coneDirectImageCounit c 𝓕) := by
  refine (directImageSystem D Ab.{u + 1} c 𝓕).isPullbackColimitPresentation_of_forall_exists hc
    (coneDirectImageCounit c 𝓕) (fun a => coneDirectImageCounit_cocone c 𝓕 a) ?_ ?_
  · intro i₀ V₀ _ _ s
    exact ⟨i₀, 𝟙 i₀, (bijective_pushforwardLeg_directImageSystem_app c 𝓕 (𝟙 i₀) V₀).2 s⟩
  · intro i₀ V₀ _ _ k a x hx
    obtain rfl : x = 0 := (bijective_pushforwardLeg_directImageSystem_app c 𝓕 a V₀).1
      (hx.trans (map_zero _).symm)
    exact ⟨k, 𝟙 k, map_zero _⟩

end Stacks.EtaleCohomology

end
