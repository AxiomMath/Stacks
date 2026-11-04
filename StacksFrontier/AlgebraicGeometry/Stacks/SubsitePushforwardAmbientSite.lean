module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardAmbientComparison

/-!
# The site of the 2-fibre product `V ×_{y, 𝒴} 𝒳`, and sheaves restricted to it

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over a base `𝒞`, with `𝒳` and `𝒴` fibred in
groupoids, let `c` be a choice of pullbacks for `𝒴` and let `y` be an object of a full
subcategory of `𝒴`, lying over `V : 𝒞`. The 2-fibre product `V ×_{y, 𝒴} 𝒳` is then fibred in
groupoids over `𝒞` (**Stacks 0041**), so it carries the topology inherited from any topology on
`𝒞` (**Stacks 06NV**); and the projection `pr : V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` is a 1-morphism of fibred
categories over `𝒞`, hence continuous and cocontinuous for the inherited topologies
(**Stacks 06NW**). In particular `pr^{-1}ℱ` is a sheaf on `V ×_{y, 𝒴} 𝒳` whenever `ℱ` is a
sheaf on `𝒳`.

Over the big fppf category of a scheme `S` the inherited topologies are the five associated
sites of **Stacks 06TP**, and the two statements are repeated there for a 1-morphism of
algebraic stacks, whose structure functors, fibredness and compatibility over the base are
supplied by the algebraic stacks themselves.

## Main definitions

* `CategoryTheory.SubsitePushforward.ambientStructureFunctor`: the structure functor
  `V ×_{y, 𝒴} 𝒳 ⥤ 𝒞` of the 2-fibre product.
* `CategoryTheory.SubsitePushforward.ambientInheritedTopology`: the topology on
  `V ×_{y, 𝒴} 𝒳` inherited from a topology on `𝒞`.
* `AlgebraicGeometry.Stack.ambientTwoFibreProductTopology`: that topology at one of the five
  topologies of Stacks 06TP, for a 1-morphism of algebraic stacks.

## Main results

* `CategoryTheory.SubsitePushforward.isFiberedInGroupoids_ambientStructureFunctor`: the 2-fibre
  product is fibred in groupoids over `𝒞`.
* `CategoryTheory.SubsitePushforward.isContinuous_and_isCocontinuous_ambientProjection`: the
  projection `pr` is continuous and cocontinuous for the inherited topologies.
* `CategoryTheory.SubsitePushforward.isSheaf_comp_ambientProjection` and
  `AlgebraicGeometry.Stack.isSheaf_comp_ambientProjection`: `pr^{-1}ℱ` is a sheaf on the
  2-fibre product when `ℱ` is a sheaf on `𝒳`.

## References

* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber

namespace CategoryTheory.SubsitePushforward

universe u₁ u₂ u₃ v₁ v₂ v₃ w

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (c : p𝒴.ChoiceOfPullbacks)
  {Q : ObjectProperty 𝒴} (y : Q.FullSubcategory)

/-- The structure functor `V ×_{y, 𝒴} 𝒳 ⥤ 𝒞` of the 2-fibre product, sending an object to the
object of `𝒞` that its three components lie over. -/
abbrev ambientStructureFunctor : ambientTwoFibreProduct p𝒳 p𝒴 f c y ⥤ 𝒞 :=
  TwoFibreProductOver.structureFunctor (Over.forget (p𝒴.obj y.obj)) p𝒳 p𝒴
    (c.sliceFunctor ⟨y.obj, rfl⟩) f

/-- The projection `pr : V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` is strictly over `𝒞`: composing it with the
structure functor of `𝒳` gives the structure functor of the 2-fibre product. -/
lemma ambientProjection_comp_eq :
    ambientProjection p𝒳 p𝒴 f c y ⋙ p𝒳 = ambientStructureFunctor p𝒳 p𝒴 f c y :=
  TwoFibreProductOver.snd_comp_eq

/-- **Stacks 0041 for the 2-fibre product `V ×_{y, 𝒴} 𝒳`.** It is fibred in groupoids over `𝒞`,
the slice `𝒞/V` and the two structure functors being so and the two legs of the cospan being
strictly over `𝒞`. -/
theorem isFiberedInGroupoids_ambientStructureFunctor (h𝒳 : p𝒳.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) :
    (ambientStructureFunctor p𝒳 p𝒴 f c y).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids (Over.forget (p𝒴.obj y.obj)) p𝒳 p𝒴
    (c.sliceFunctor ⟨y.obj, rfl⟩) f (Functor.IsFiberedInGroupoids.over_forget _) h𝒳 h𝒴
    (c.sliceFunctor_comp ⟨y.obj, rfl⟩) hf

/-- The projection `pr : V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` is a 1-morphism of fibred categories over `𝒞`: it is
strictly over `𝒞`, and its target is fibred in groupoids, so it preserves strongly cartesian
morphisms. -/
lemma isFibredOneMorphism_ambientProjection (h𝒳 : p𝒳.IsFiberedInGroupoids) :
    (ambientStructureFunctor p𝒳 p𝒴 f c y).IsFibredOneMorphism p𝒳
      (ambientProjection p𝒳 p𝒴 f c y) :=
  Functor.IsFiberedInGroupoids.isFibredOneMorphism h𝒳
    (ambientProjection_comp_eq p𝒳 p𝒴 f c y)

/-- **Stacks 06NV for the 2-fibre product `V ×_{y, 𝒴} 𝒳`.** The topology it inherits along its
structure functor from a topology `J` on the base `𝒞`. -/
abbrev ambientInheritedTopology (J : GrothendieckTopology 𝒞) :
    GrothendieckTopology (ambientTwoFibreProduct p𝒳 p𝒴 f c y) :=
  (ambientStructureFunctor p𝒳 p𝒴 f c y).inheritedTopology J

/-- **Stacks 06NW for the projection `pr : V ×_{y, 𝒴} 𝒳 ⥤ 𝒳`.** It is continuous and
cocontinuous between the topologies that the 2-fibre product and `𝒳` inherit from a topology `J`
on the base. -/
theorem isContinuous_and_isCocontinuous_ambientProjection [HasPullbacks 𝒞]
    (J : GrothendieckTopology 𝒞) (h𝒳 : p𝒳.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) :
    (ambientProjection p𝒳 p𝒴 f c y).IsContinuous
        (ambientInheritedTopology p𝒳 p𝒴 f c y J) (p𝒳.inheritedTopology J) ∧
      (ambientProjection p𝒳 p𝒴 f c y).IsCocontinuous
        (ambientInheritedTopology p𝒳 p𝒴 f c y J) (p𝒳.inheritedTopology J) :=
  let : (ambientStructureFunctor p𝒳 p𝒴 f c y).IsFibered :=
    (isFiberedInGroupoids_ambientStructureFunctor p𝒳 p𝒴 f c y h𝒳 h𝒴 hf).isFibered
  let : p𝒳.IsFibered := h𝒳.isFibered
  (isFibredOneMorphism_ambientProjection p𝒳 p𝒴 f c y
    h𝒳).isContinuous_and_isCocontinuous_inheritedTopology J

/-- The restriction `pr^{-1}ℱ` of a sheaf `ℱ` of sets on `𝒳` along the projection of the
2-fibre product is a sheaf for the inherited topology, the projection being continuous. -/
theorem isSheaf_comp_ambientProjection [HasPullbacks 𝒞] (J : GrothendieckTopology 𝒞)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (ℱ : 𝒳ᵒᵖ ⥤ Type w) (hℱ : Presieve.IsSheaf (p𝒳.inheritedTopology J) ℱ) :
    Presieve.IsSheaf (ambientInheritedTopology p𝒳 p𝒴 f c y J)
      ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ) :=
  let := (isContinuous_and_isCocontinuous_ambientProjection p𝒳 p𝒴 f c y J h𝒳 h𝒴 hf).1
  (ambientProjection p𝒳 p𝒴 f c y).op_comp_isSheaf_of_isSheaf_type
    (ambientInheritedTopology p𝒳 p𝒴 f c y J) hℱ

end CategoryTheory.SubsitePushforward

namespace AlgebraicGeometry.Stack

universe u w a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory)

/-- **The site of the 2-fibre product `V ×_{y, 𝒴} 𝒳` of a 1-morphism of algebraic stacks**, for
one of the five topologies of Stacks 06TP: the topology the 2-fibre product inherits along its
structure functor from the localization at `S` of that topology. -/
abbrev ambientTwoFibreProductTopology (τ : SiteKind) :
    GrothendieckTopology (SubsitePushforward.ambientTwoFibreProduct 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor (ambientChoiceOfPullbacks B S hS 𝒴) y) :=
  BigFppfOver.associatedTopology B S hS
    (SubsitePushforward.ambientStructureFunctor 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
      (ambientChoiceOfPullbacks B S hS 𝒴) y) τ

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks and a sheaf `ℱ` of sets on the associated
site `𝒳_τ` of Stacks 06TP, the restriction `pr^{-1}ℱ` along the projection of the 2-fibre
product `V ×_{y, 𝒴} 𝒳` is a sheaf for the associated topology of that 2-fibre product. -/
theorem isSheaf_comp_ambientProjection (τ : SiteKind) (ℱ : (𝒳.val.val.obj)ᵒᵖ ⥤ Type a)
    (hℱ : Presieve.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) ℱ) :
    Presieve.IsSheaf (ambientTwoFibreProductTopology B S hS f y τ)
      ((SubsitePushforward.ambientProjection 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
        (ambientChoiceOfPullbacks B S hS 𝒴) y).op ⋙ ℱ) :=
  SubsitePushforward.isSheaf_comp_ambientProjection 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor (ambientChoiceOfPullbacks B S hS 𝒴) y
    (BigFppfOver.baseOverTopology B S hS τ) 𝒳.val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids f.hom.hom.w ℱ hℱ

end AlgebraicGeometry.Stack

end
