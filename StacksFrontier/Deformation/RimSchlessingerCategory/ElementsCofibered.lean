module

public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# The category of elements of a set-valued functor is cofibered in groupoids

The projection from the category of elements of a set-valued functor to its base is cofibered
in groupoids, and the value of an element of a strict fibre is natural in the base object.

## Main results

* `Deformation.isCofiberedInGroupoids_elementsProjection`: the projection from the category of
  elements is cofibered in groupoids.
* `Deformation.elementsFiberValue_map`: an arrow of the category of elements over a base arrow
  carries the value of its source to the value of its target.

## Implementation notes

Both statements are about an arbitrary set-valued functor on an arbitrary category; neither
mentions Artinian algebras. They are stated here because the Rim-Schlessinger criteria for an
associated functor of isomorphism classes are the first place in the chapter that needs them
on their own, rather than packaged inside a predeformation hypothesis.

The value of an element of the strict fibre over `A` is `Deformation.elementsFiberValue`.

## References

* [Stacks Project, Tag 06J8](https://stacks.math.columbia.edu/tag/06J8)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory

universe u v u₁

/-- The projection from the category of elements of a set-valued functor is cofibered in
groupoids. -/
theorem isCofiberedInGroupoids_elementsProjection {𝒞 : Type u} [Category.{v} 𝒞]
    (G : 𝒞 ⥤ Type u₁) : IsCofiberedInGroupoids (CategoryOfElements.π G) := by
  show Functor.IsFiberedInGroupoids (CategoryOfElements.π G).op
  constructor
  · intro V U f x hx
    rcases V with ⟨V⟩
    rcases U with ⟨U⟩
    rcases x with ⟨x⟩
    change Opposite.op ((CategoryOfElements.π G).obj x) = Opposite.op U at hx
    cases hx
    let y := G.elementsMk V (G.map f.unop x.2)
    let g : x ⟶ y := CategoryOfElements.homMk x y f.unop rfl
    refine ⟨Opposite.op y, g.op, ?_⟩
    rw [← show (CategoryOfElements.π G).op.map g.op = f from
      Quiver.Hom.opEquiv.injective (by simp [g, CategoryOfElements.π])]
    exact inferInstance
  · intro x y z φ ψ f hf
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    rcases z with ⟨z⟩
    have hbase : φ.unop.val ≫ f.unop = ψ.unop.val := by
      simpa using congrArg Quiver.Hom.unop hf
    let g : y ⟶ z := CategoryOfElements.homMk y z f.unop (by
      rw [← CategoryOfElements.map_snd φ.unop, ← Functor.map_comp_apply,
        hbase, CategoryOfElements.map_snd ψ.unop])
    refine ⟨g.op, ⟨?_, ?_⟩, ?_⟩
    · exact Quiver.Hom.opEquiv.injective (by simp [g, CategoryOfElements.π])
    · apply Quiver.Hom.opEquiv.symm.injective
      apply CategoryOfElements.ext
      exact hbase
    · intro χ hχ
      apply Quiver.Hom.opEquiv.symm.injective
      apply CategoryOfElements.ext
      exact congrArg Quiver.Hom.unop hχ.1

/-- An arrow of the category of elements lying over a base arrow carries the value of its
source to the value of its target. -/
theorem elementsFiberValue_map {𝒞 : Type u} [Category.{v} 𝒞]
    (G : 𝒞 ⥤ Type u₁) {A B : 𝒞} (f : A ⟶ B)
    (x : Functor.Fiber (CategoryOfElements.π G) A)
    (y : Functor.Fiber (CategoryOfElements.π G) B) (m : x.1 ⟶ y.1)
    (hm : (CategoryOfElements.π G).IsHomLift f m) :
    G.map f (elementsFiberValue G A x) = elementsFiberValue G B y := by
  dsimp [elementsFiberValue]
  rw [IsHomLift.fac (CategoryOfElements.π G) f m]
  simp

end

end Deformation
