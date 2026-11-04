module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite

/-!
# Functoriality of the 2-Yoneda 1-morphism of an object

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids over the big fppf category of a scheme
`S` in `B`. For an object `x` of `𝒳` lying over `U`, the 2-Yoneda lemma (**Stacks 004B**) gives
the 1-morphism `AlgebraicGeometry.Stack.objectMorphism`, written `x : U → 𝒳` in the source.

This construction is functorial in `x`: a morphism `f : x ⟶ y` of `𝒳`, lying over
`g : U ⟶ V`, makes `x : U → 𝒳` canonically 2-isomorphic to the composite of `g : U → V` with
`y : V → 𝒳`.

## Main definitions

* `AlgebraicGeometry.Stack.overMapBased`: the based functor `(Sch/S)/U ⥤ᵇ (Sch/S)/V` induced by
  a morphism `U ⟶ V` of the big fppf category of `S`.
* `AlgebraicGeometry.Stack.schemeFibredCategoryMap`: the same read as a 1-morphism of the
  represented categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.objectMorphismFactorIso`: the 2-isomorphism
  `x ≅ g ≫ y` of 1-morphisms out of the category represented by `U`.

## Implementation notes

The comparison is built in the category of based functors `(Sch/S)/U ⥤ᵇ 𝒳` and transported by
`CategoryTheory.Bicategory.InducedBicategory.isoMk`. The chosen lift of `y` is taken at
`(Over.map g).obj (Over.mk (𝟙 U))`, the object that actually occurs, rather than at `Over.mk g`:
the two are equal only up to `Category.id_comp`, and this choice keeps `eqToHom` out of the
construction.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The based functor `(Sch/S)/U ⥤ᵇ (Sch/S)/V` induced by a morphism `g : U ⟶ V` of the big
fppf category of `S`: postcomposition with `g`, which leaves the underlying scheme of an object
unchanged and so commutes with the two forgetful functors on the nose. -/
def overMapBased {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    (schemeFibredCategory B S hS U).val ⥤ᵇ (schemeFibredCategory B S hS V).val where
  toFunctor := Over.map g
  w := rfl

/-- The 1-morphism of represented categories fibred in groupoids over the big fppf category of
`S` induced by a morphism `g : U ⟶ V`. This is the 1-morphism written `g : U → V` in the
source. -/
def schemeFibredCategoryMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    schemeFibredCategory B S hS U ⟶ schemeFibredCategory B S hS V :=
  Bicategory.InducedBicategory.mkHom (overMapBased B S hS g)

/-- In a category fibred in groupoids, an arrow of the total category lying over the identity
of `U` is an isomorphism between the fibre objects it connects: it is an arrow of the fibre over
`U`, and that fibre is a groupoid. -/
noncomputable def fiberIsoOfHomLift {X : Type (u + 1)} [Category.{u} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (U : BigFppfOver B S hS)
    {a b : p.Fiber U} (φ : a.1 ⟶ b.1) (hφ : p.IsHomLift (𝟙 U) φ) : a ≅ b := by
  haveI := hp.fiber_isGroupoid U
  haveI := hφ
  -- Retyped at `a ⟶ b` so that instance search sees a morphism of the fibre.
  let hm : a ⟶ b := Functor.Fiber.homMk p U φ
  exact asIso hm

/-- The comparison of based functors underlying `AlgebraicGeometry.Stack.objectMorphismFactorIso`:
the chosen-lift functor of `x` is isomorphic to the chosen-lift functor of `y` precomposed with
`Over.map (p.map f)`. -/
noncomputable def basedFactorIso {X : Type (u + 1)} [Category.{u} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : X} (f : x ⟶ y) :
    Functor.TwoYoneda.liftBased p hp (p.obj x) (Functor.Fiber.mk (a := x) rfl) ≅
      BasedFunctor.comp (overMapBased B S hS (p.map f))
        (Functor.TwoYoneda.liftBased p hp (p.obj y) (Functor.Fiber.mk (a := y) rfl)) := by
  let ev := p.twoYonedaEvaluation (p.obj x)
  let G := Functor.TwoYoneda.liftBased p hp (p.obj x) (Functor.Fiber.mk (a := x) rfl)
  let C := BasedFunctor.comp (overMapBased B S hS (p.map f))
    (Functor.TwoYoneda.liftBased p hp (p.obj y) (Functor.Fiber.mk (a := y) rfl))
  let lx := Functor.TwoYoneda.chosenLift p hp (p.obj x) (Functor.Fiber.mk (a := x) rfl)
    (Over.mk (𝟙 (p.obj x)))
  let ly := Functor.TwoYoneda.chosenLift p hp (p.obj y) (Functor.Fiber.mk (a := y) rfl)
    ((Over.map (p.map f)).obj (Over.mk (𝟙 (p.obj x))))
  -- Retyped so that instance search for the universal property finds `hf'`.
  let f' : x ⟶ (Functor.Fiber.mk (p := p) (S := p.obj y) (a := y) rfl).1 := f
  have hf' : p.IsHomLift (p.map f) f' := IsHomLift.map p f
  have hcart : p.IsStronglyCartesian
      ((Over.map (p.map f)).obj (Over.mk (𝟙 (p.obj x)))).hom ly.φ := ly.isStronglyCartesian
  have hfill := (Functor.IsStronglyCartesian.universal_property p
    ((Over.map (p.map f)).obj (Over.mk (𝟙 (p.obj x)))).hom ly.φ
    (𝟙 (p.obj x)) (p.map f) (by simp) f').exists
  let χ := Classical.choose hfill
  have hχ := Classical.choose_spec hfill
  have h1 : p.IsHomLift (𝟙 (p.obj x)) χ := hχ.1
  have h2 : p.IsHomLift (𝟙 (p.obj x)) lx.φ := lx.isStronglyCartesian.toIsHomLift
  have := p.twoYonedaEvaluation_full hp (p.obj x)
  have := p.twoYonedaEvaluation_faithful hp (p.obj x)
  exact (Functor.FullyFaithful.ofFullyFaithful ev).preimageIso (X := G) (Y := C)
    (fiberIsoOfHomLift B S hS p hp (p.obj x) (lx.φ ≫ χ)
      (@IsHomLift.comp_of_lift_id _ _ _ _ p (p.obj x) _ _ _ lx.φ χ h2 h1))

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- A morphism `f : x ⟶ y` of a category fibred in groupoids over the big fppf category of `S`,
lying over `g : U ⟶ V`, makes the 1-morphism `x : U → 𝒳` canonically 2-isomorphic to the
composite `U → V → 𝒳` of `g` with `y : V → 𝒳`. -/
noncomputable def objectMorphismFactorIso {x y : 𝒳.val.obj} (f : x ⟶ y) :
    objectMorphism B S hS 𝒳 (Functor.Fiber.mk (a := x) rfl) ≅
      schemeFibredCategoryMap B S hS (𝒳.val.p.map f) ≫
        objectMorphism B S hS 𝒳 (Functor.Fiber.mk (a := y) rfl) :=
  Bicategory.InducedBicategory.isoMk
    (basedFactorIso B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids f)

end AlgebraicGeometry.Stack

end
