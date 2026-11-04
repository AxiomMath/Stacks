module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackComparisonLocal

/-!
# The local-fullness hypothesis of the transpose, reduced to the chosen cartesian morphisms

Let `u : 𝒞 ⥤ 𝒟` be a functor, let `p : 𝒮 ⥤ 𝒞` and `q : 𝒯 ⥤ 𝒟` be fibred categories and let
`F : 𝒮 ⥤ 𝒯` be a functor over `u` carrying strongly cartesian morphisms to strongly cartesian
morphisms. The adjunction of Stacks 04WI transposes `F` to the 1-morphism `B(F)` of
`CategoryTheory.PullbackAdjunction.leftToRight`, and
`CategoryTheory.PullbackAdjunction.exists_covering_leftToRight_map_comp` reduces local fullness of
`B(F)` to a statement about the *chosen* pullbacks `φ^* F(x)`.

This file removes the chosen pullbacks from that statement. A morphism `φ^* F(x) ⟶ F(y)` is, after
the comparison isomorphism of
`CategoryTheory.PullbackAdjunction.exists_iso_leftToRightMap`, the same thing as a morphism
`z ⟶ F(y)` out of the domain of an arbitrary strongly cartesian morphism `μ : z ⟶ F(x)` over `φ`;
and the identity to be produced likewise only mentions such strongly cartesian morphisms. That is
the form in which a geometric construction can supply it.

## Main results

* `CategoryTheory.PullbackAdjunction.exists_isHomLift_of_obj_eq`: the morphism of `𝒟` that a
  morphism of `𝒯` into a value of `F` lies over.
* `CategoryTheory.PullbackAdjunction.comp_map_eqToHom_of_isHomLift`: the compatibility condition of
  `u_pp 𝒮` for a morphism of `𝒮` read through the morphism of `𝒞` it lies over.
* `CategoryTheory.PullbackAdjunction.hfull_of_core`: **the reduction of the local-fullness
  hypothesis** of `CategoryTheory.PullbackAdjunction.exists_covering_leftToRight_map_comp` to a
  statement about arbitrary strongly cartesian morphisms.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 04WI](https://stacks.math.columbia.edu/tag/04WI)
-/

@[expose] public noncomputable section

namespace CategoryTheory.PullbackAdjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {𝒯 : Type u₄} [Category.{v₄} 𝒯]

variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)

/-- **The compatibility condition of `u_pp 𝒮`, read off from the morphism of `𝒞` that a morphism
of `𝒮` lies over.** The structure morphism of the presentation is the given morphism of `𝒟`
followed by the transport comparing the image of the domain with the morphism of `𝒞`. -/
theorem comp_map_eqToHom_of_isHomLift {x₁ x₀ : 𝒮} {e : x₁ ⟶ x₀} {W : 𝒞} {dd : W ⟶ p.obj x₀}
    (he : p.IsHomLift dd e) {V₁ : 𝒟} (χ : V₁ ⟶ u.obj W) :
    (χ ≫ u.map (eqToHom (IsHomLift.domain_eq p dd e).symm)) ≫ (p ⋙ u).map e =
      χ ≫ u.map dd := by
  have hd : p.obj x₁ = W := IsHomLift.domain_eq p dd e
  have hc : p.obj x₀ = p.obj x₀ := IsHomLift.codomain_eq p dd e
  have hfac : p.map e = eqToHom hd ≫ dd ≫ eqToHom hc.symm := IsHomLift.fac' p dd e
  rw [Functor.comp_map, hfac]
  rw [eqToHom_refl _ hc.symm]
  simp [eqToHom_map]

variable (q : 𝒯 ⥤ 𝒟) [q.IsFibered] (F : 𝒮 ⥤ 𝒯) (hF : F ⋙ q = p ⋙ u)

include hF

omit [q.IsFibered] in
/-- **The morphism of `𝒟` that a morphism of `𝒯` into a value of `F` lies over**, named from the
object of `𝒟` the domain is known to lie over. -/
theorem exists_isHomLift_of_obj_eq {z : 𝒯} {V : 𝒟} (hz : q.obj z = V) {y : 𝒮} (Θ : z ⟶ F.obj y) :
    ∃ ψ : V ⟶ u.obj (p.obj y), q.IsHomLift ψ Θ := by
  refine ⟨eqToHom hz.symm ≫ q.map Θ ≫ eqToHom (Functor.congr_obj hF y),
    IsHomLift.of_fac' q _ Θ hz (Functor.congr_obj hF y) ?_⟩
  simp

variable (hFsc : ∀ {x y : 𝒮} (α : x ⟶ y), p.IsStronglyCartesian (p.map α) α →
    q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))

/-- **The local-fullness hypothesis of
`CategoryTheory.PullbackAdjunction.exists_covering_leftToRight_map_comp`, reduced to arbitrary
strongly cartesian morphisms.** Suppose that for every strongly cartesian `μ : z ⟶ F(x₀)` over
`φ : V ⟶ u(p(x₀))` and every `Θ : z ⟶ F(y)` there is, locally on `V`, a morphism `e : x₁ ⟶ x₀` of
`𝒮` strongly cartesian over its image, a morphism `α : x₁ ⟶ y`, and a restriction of `μ` along
which `Θ` becomes the one induced by `α`. Then the hypothesis holds.

The chosen pullback `φ^* F(x₀)` is one such strongly cartesian morphism, and
`CategoryTheory.PullbackAdjunction.exists_iso_leftToRightMap` identifies the morphism of chosen
pullbacks induced by the resulting presentation with the restriction produced by the
hypothesis. -/
theorem hfull_of_core (K : GrothendieckTopology 𝒟)
    (hcore : ∀ (x₀ y : 𝒮) (V : 𝒟) (φ : V ⟶ u.obj (p.obj x₀)) (z : 𝒯) (μ : z ⟶ F.obj x₀),
      q.IsStronglyCartesian φ μ → ∀ Θ : z ⟶ F.obj y,
      ∃ T ∈ K V, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        ∃ (x₁ : 𝒮) (e : x₁ ⟶ x₀) (φ₁ : V₁ ⟶ u.obj (p.obj x₁)) (α : x₁ ⟶ y) (z₁ : 𝒯)
          (μ₁ : z₁ ⟶ F.obj x₁) (ν : z₁ ⟶ z),
          stronglyCartesianOver p e ∧ φ₁ ≫ (p ⋙ u).map e = β ≫ φ ∧
            q.IsStronglyCartesian φ₁ μ₁ ∧ q.IsHomLift β ν ∧
            ν ≫ μ = μ₁ ≫ F.map e ∧ ν ≫ Θ = μ₁ ≫ F.map α)
    (Z : Comma (𝟭 𝒟) (p ⋙ u)) {y : 𝒮} (Θ : leftToRightObj p u q F hF Z ⟶ F.obj y) :
    ∃ T ∈ K Z.left, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ Z.left⦄, T.arrows β →
      ∃ (x₁ : 𝒮) (e : x₁ ⟶ Z.right) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
        (_ : stronglyCartesianOver p e) (hw : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom) (α : x₁ ⟶ y),
        leftToRightHom p u q F hF (commaHomOf p u Z e β φ₁ hw) ≫ Θ =
          leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁) ≫ F.map α := by
  obtain ⟨T, hT, hspec⟩ := hcore Z.right y Z.left Z.hom (leftToRightObj p u q F hF Z)
    (leftToRightMap p u q F hF Z) (leftToRightMap_isStronglyCartesian p u q F hF Z) Θ
  refine ⟨T, hT, ?_⟩
  intro V₁ β hβ
  obtain ⟨x₁, e, φ₁, α, z₁, μ₁, ν, hsc, hw, hμ₁, hν, hfacν, hΘ⟩ := hspec hβ
  obtain ⟨ι, hιμ, hιν⟩ := exists_iso_leftToRightMap p u q F hF Z e β φ₁ hw hμ₁ hν hfacν
  refine ⟨x₁, e, φ₁, hsc, hw, α, ?_⟩
  refine Eq.trans (congrArg (fun t => t ≫ Θ) hιν.symm) ?_
  refine Eq.trans (Category.assoc ι ν Θ) ?_
  refine Eq.trans (congrArg (fun t => ι ≫ t) hΘ) ?_
  exact (Category.assoc ι μ₁ (F.map α)).symm.trans (congrArg (fun t => t ≫ F.map α) hιμ)

end CategoryTheory.PullbackAdjunction

end
