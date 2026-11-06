module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.RimSchlessingerCategory.ElementsCofibered
public import StacksFrontier.Deformation.SchlessingerConditions.SetValuedFunctor

/-!
# Condition (RS) for a set-valued functor

For a functor `F : 𝒞_Λ ⥤ Sets`, condition (RS) for the associated category cofibered in sets
holds exactly when the canonical map `F(A₁ ×_A A₂) → F(A₁) ×_{F(A)} F(A₂)` is bijective for
every fibre product with `A₂ → A` surjective. This is Schlessinger's condition (H4).

## Main results

* `Deformation.satisfiesRS_elementsProjection_iff_bijective`: condition (RS) for the category of
  elements of a set-valued functor is the bijectivity of `Deformation.fibreProductComparison`.

## Implementation notes

A set-valued functor is read as a category cofibered in sets through the projection from its
category of elements, as in `Deformation.IsDeformationFunctor`. The comparison map and its target,
the subtype of the product cut out by the defining equality, are those of
`Deformation.fibreProductComparison`. The fibre-product square of algebras is supplied as an
`IsPullback`, so the statement covers any model of `A₁ ×_A A₂`.

## References

* [Stacks Project, Tag 06J6](https://stacks.math.columbia.edu/tag/06J6)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits

universe u v w t

/-- The square over `e₁, e₂` in the category of elements with the element `y` at its apex, for a
pullback square of algebras over `e₁.hom, e₂.hom` whose legs carry `y` to the given values. -/
private def elementsPullbackCone
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type t)
    {x₁ x₂ x : G.Elements} (e₁ : x₁ ⟶ x) (e₂ : x₂ ⟶ x)
    {P : ArtinianLocalAlgCat.{u, v, w} Λ k} {p₁ : P ⟶ x₁.obj} {p₂ : P ⟶ x₂.obj}
    (hP : IsPullback p₁ p₂ e₁.hom e₂.hom) (y : G.obj P)
    (hy₁ : G.map p₁ y = x₁.val) (hy₂ : G.map p₂ y = x₂.val) : PullbackCone e₁ e₂ :=
  PullbackCone.mk (Functor.Elements.homMk (x := G.elementsMk P y) p₁ hy₁)
    (Functor.Elements.homMk (x := G.elementsMk P y) p₂ hy₂) (Functor.Elements.hom_ext hP.w)

/-- Under condition (RS) the comparison map of a pullback square whose second map is surjective
is injective. -/
private lemma injective_fibreProductComparison_of_satisfiesRS
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type t)
    (hRS : SatisfiesRS (Functor.Elements.π G))
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hP : IsPullback p₁ p₂ f₁ f₂) (hf₂ : Function.Surjective f₂.hom) :
    Function.Injective (fibreProductComparison G p₁ p₂ f₁ f₂ hP.w.symm) := by
  intro y y' hyy'
  have hv := Prod.ext_iff.mp (congrArg Subtype.val hyy')
  -- The square over the given one with `y` at its apex is a fibre square, by (RS).
  let x₁ : G.Elements := G.elementsMk A₁ (G.map p₁ y)
  let x₂ : G.Elements := G.elementsMk A₂ (G.map p₂ y)
  let x : G.Elements := G.elementsMk A (G.map f₁ (G.map p₁ y))
  let e₁ : x₁ ⟶ x := Functor.Elements.homMk f₁ rfl
  let e₂ : x₂ ⟶ x := Functor.Elements.homMk f₂
    (fibreProductComparison G p₁ p₂ f₁ f₂ hP.w.symm y).2.symm
  let c := elementsPullbackCone G e₁ e₂ hP y rfl rfl
  let c' := elementsPullbackCone G e₁ e₂ hP y' hv.1.symm hv.2.symm
  obtain ⟨hc⟩ := isLimit_of_map_isLimit hRS e₁ e₂ c hf₂ ⟨hP.isLimit⟩
  -- The induced map from the apex of the square built from `y'` lies over the identity.
  have hval₁ : (hc.lift c').hom ≫ p₁ = 𝟙 P ≫ p₁ :=
    (congrArg (·.hom) (hc.fac c' .left)).trans (Category.id_comp p₁).symm
  have hval₂ : (hc.lift c').hom ≫ p₂ = 𝟙 P ≫ p₂ :=
    (congrArg (·.hom) (hc.fac c' .right)).trans (Category.id_comp p₂).symm
  have hprop : G.map (hc.lift c').hom y' = y := Functor.Elements.Hom.map_val _
  rw [hP.hom_ext hval₁ hval₂] at hprop
  exact ((G.map_id_apply P y').symm.trans hprop).symm

/-- Bijectivity of the comparison map of a pullback square produces the fibre product in the
category of elements required by condition (RS). -/
private theorem exists_isLimit_of_bijective_fibreProductComparison
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type t)
    {x₁ x₂ x : G.Elements} (e₁ : x₁ ⟶ x) (e₂ : x₂ ⟶ x)
    {P : ArtinianLocalAlgCat.{u, v, w} Λ k} {p₁ : P ⟶ x₁.obj} {p₂ : P ⟶ x₂.obj}
    (hP : IsPullback p₁ p₂ e₁.hom e₂.hom)
    (hbij : Function.Bijective (fibreProductComparison G p₁ p₂ e₁.hom e₂.hom hP.w.symm)) :
    ∃ c : PullbackCone e₁ e₂,
      Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map (Functor.Elements.π G))) := by
  have hcompat : G.map e₁.hom x₁.val = G.map e₂.hom x₂.val :=
    (Functor.Elements.Hom.map_val e₁).trans (Functor.Elements.Hom.map_val e₂).symm
  obtain ⟨y, hy⟩ := hbij.2 ⟨(x₁.val, x₂.val), hcompat⟩
  have hv := Prod.ext_iff.mp (congrArg Subtype.val hy)
  have hy₁ : G.map p₁ y = x₁.val := hv.1
  have hy₂ : G.map p₂ y = x₂.val := hv.2
  -- Every cone over the cospan lifts uniquely: the base square is a fibre square and the
  -- comparison map is injective.
  have hcond (s : PullbackCone e₁ e₂) : s.fst.hom ≫ e₁.hom = s.snd.hom ≫ e₂.hom :=
    congrArg (fun g => g.hom) s.condition
  let baseLift (s : PullbackCone e₁ e₂) : s.pt.obj ⟶ P :=
    hP.lift s.fst.hom s.snd.hom (hcond s)
  have hbase₁ (s : PullbackCone e₁ e₂) : baseLift s ≫ p₁ = s.fst.hom :=
    hP.lift_fst _ _ (hcond s)
  have hbase₂ (s : PullbackCone e₁ e₂) : baseLift s ≫ p₂ = s.snd.hom :=
    hP.lift_snd _ _ (hcond s)
  have hbaseLift (s : PullbackCone e₁ e₂) : G.map (baseLift s) s.pt.val = y := by
    have hc₁ : G.map p₁ (G.map (baseLift s) s.pt.val) = G.map p₁ y := by
      rw [← G.map_comp_apply, hbase₁ s, Functor.Elements.Hom.map_val s.fst, hy₁]
    have hc₂ : G.map p₂ (G.map (baseLift s) s.pt.val) = G.map p₂ y := by
      rw [← G.map_comp_apply, hbase₂ s, Functor.Elements.Hom.map_val s.snd, hy₂]
    exact hbij.1 (Subtype.ext (Prod.ext hc₁ hc₂))
  refine ⟨elementsPullbackCone G e₁ e₂ hP y hy₁ hy₂, ⟨PullbackCone.isLimitAux _
    (fun s => Functor.Elements.homMk (baseLift s) (hbaseLift s))
    (fun s => Functor.Elements.hom_ext (hbase₁ s))
    (fun s => Functor.Elements.hom_ext (hbase₂ s))
    (fun s m hm => ?_)⟩, ⟨hP.isLimit⟩⟩
  have hm₁ : m.hom ≫ p₁ = s.fst.hom := congrArg (fun g => g.hom) (hm WalkingCospan.left)
  have hm₂ : m.hom ≫ p₂ = s.snd.hom := congrArg (fun g => g.hom) (hm WalkingCospan.right)
  exact Functor.Elements.hom_ext
    (hP.hom_ext (hm₁.trans (hbase₁ s).symm) (hm₂.trans (hbase₂ s).symm))

/-- **Stacks Project, Tag 06J6.** For a set-valued functor `F` on the category of Artinian local
`Λ`-algebras, condition (RS) for the associated category cofibered in sets holds exactly when
the canonical map `F(A₁ ×_A A₂) → F(A₁) ×_{F(A)} F(A₂)` is bijective for every fibre-product
square whose second map is surjective; this is Schlessinger's condition (H4). -/
@[stacks 06J6]
theorem satisfiesRS_elementsProjection_iff_bijective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type t) :
    SatisfiesRS (Functor.Elements.π G) ↔
      ∀ {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
        (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
        (hP : IsPullback p₁ p₂ f₁ f₂), Function.Surjective f₂.hom →
          Function.Bijective (fibreProductComparison G p₁ p₂ f₁ f₂ hP.w.symm) := by
  constructor
  · intro hRS P A₁ A₂ A p₁ p₂ f₁ f₂ hP hf₂
    exact ⟨injective_fibreProductComparison_of_satisfiesRS G hRS hP hf₂,
      (schlessingerConditionS1_elements_iff G).mp
        (schlessingerConditionS1_of_satisfiesRS hRS) f₁ f₂ hf₂ p₁ p₂ hP.flip⟩
  · refine fun h => ⟨isCofiberedInGroupoids_elementsProjection G, fun e₁ e₂ hsurj => ?_⟩
    have hsurj' : Function.Surjective e₂.hom.hom := hsurj
    have hP := ArtinianLocalAlgCat.isPullback_of_surjective e₁.hom e₂.hom (Or.inr hsurj')
    exact exists_isLimit_of_bijective_fibreProductComparison G e₁ e₂ hP (h _ _ _ _ hP hsurj')

end

end Deformation
