module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.RingTheory.Nilpotent.Ideal

/-!
# Effectivity of systems of objects, and strong formal effectiveness

A system of objects in a category over a base is *effective* over a cocone of base objects
when that base cocone is the image of a cocone of the objects themselves. In a category
fibred in groupoids the lifted comparison morphisms are cartesian, so they exhibit each
object of the system as the restriction of the object over the vertex.

A category fibred in groupoids over the big fppf site of a locally Noetherian scheme is
*strongly formally effective* when every compatible tower of objects over an affine open
chart, whose transition maps are surjective with locally nilpotent kernel, is effective
over the canonical cocone coming from the limit of the tower of algebras. In the source
this property is also referred to as *strong effectiveness*; we use the one predicate for
both rather than introducing a second name for the same property.

## Main definitions

* `Deformation.Artin.IsEffectiveSystem` — effectivity of a system of objects over a
  prescribed base cocone.
* `Deformation.Artin.IsStronglyFormallyEffective` — strong formal effectiveness.

## Implementation notes

An inverse system of algebras is a functor out of `ℕᵒᵖ`; its chosen limit cone specifies
the canonical maps from the spectra of its levels to the spectrum of the limit.
Isomorphisms identify the objects of the chosen big fppf site with these spectra, and
their naturality and compatibility with the cocone ensure that effectivity is tested over
the canonical maps rather than over an arbitrary cocone. The vertex equation records the
affine-open chart and its algebra structure; the equations for the tower then force every
level to lie over that chart.

Effectivity of a system is independent of the locally Noetherian and nilpotence
conditions, which only constrain the systems quantified over in formal effectiveness.

## References

* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
-/

@[expose] public section

namespace Deformation.Artin

/-! ### Effectivity of a system of objects -/

section

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ u₃ v₁ v₂ v₃

/-- A diagram in a category over a base is effective over a specified base cocone when
that cocone comes from a cocone of the objects. In a category fibred in groupoids, the
lifted maps exhibit the diagram objects as the restrictions of the vertex object. -/
@[stacks 0CXT "effectivity_of_a_system_of_objects"]
public abbrev IsEffectiveSystem {J : Type u₁} [Category.{v₁} J] {X : Type u₂}
    [Category.{v₂} X] {C : Type u₃} [Category.{v₃} C] (p : X ⥤ C) (ξ : J ⥤ X)
    (c : Cocone (ξ ⋙ p)) : Prop :=
  ∃ d : Cocone ξ, p.mapCocone d = c

end

/-! ### Strong formal effectiveness -/

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

/-- Strong formal effectiveness for a category fibred in groupoids over the big
fppf site of a locally Noetherian scheme. -/
@[stacks 0CXT "strong_formal_effectiveness"]
public abbrev IsStronglyFormallyEffective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S] {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS)
    (_hp : p.IsFiberedInGroupoids) : Prop :=
  ∀ (Λ : Type u) [CommRing Λ] (chart : Spec (.of Λ) ⟶ S) [IsOpenImmersion chart]
    (R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ) (cR : Cone R) (_hcR : IsLimit cR)
    (_hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
    (_hnil : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j),
      (RingHom.ker (R.map f).hom.toRingHom).LocallyNilpotent)
    (ξ : ℕ ⥤ X) (c : Cocone (ξ ⋙ p))
    (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj ((ξ ⋙ p).obj n) ≅
      Spec (.of (R.obj (.op n))))
    (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt)),
    (∀ {i j : ℕ} (f : i ⟶ j), (BigFppfOver.toScheme B S hS).map ((ξ ⋙ p).map f) ≫
      (e j).hom = (e i).hom ≫
        Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op) →
    (∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
      (e n).hom ≫
        Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op) →
    (eLimit.inv ≫ B.inclusion.map c.pt.hom =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap Λ cR.pt)).op ≫ chart) →
    IsEffectiveSystem p ξ c

end

end Deformation.Artin
