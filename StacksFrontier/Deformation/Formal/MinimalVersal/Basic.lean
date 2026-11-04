module

public import StacksFrontier.Deformation.Formal.MinimalVersal.DescendedMorphism

/-!
# Smallest descents of a formal object

A smallest descent of a formal object is a descent of it over a complete local subalgebra of its
base which stays minimal after every Artinian base change and admits no proper further formal
descent.

## Main definitions

* `Deformation.SmallestDescent`: a descent of a formal object over an embedded complete local
  subalgebra which remains minimal after every Artinian pushforward and admits no proper further
  formal descent.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- A descent of `ξ` over an embedded complete local subalgebra which remains minimal
after every Artinian pushforward and admits no proper further formal descent. -/
public structure SmallestDescent (ξ : FormalObject p) where
  /-- The descended formal object. -/
  object : FormalObject p
  /-- Its morphism to the given formal object. -/
  inclusion : object ⟶ ξ
  /-- The descended complete base is a subalgebra of the original base. -/
  base_injective : Function.Injective inclusion.base.hom
  /-- For every Artinian point and every cocartesian pushforward square over the image
  subalgebra, the resulting descent object is minimal. -/
  pushforward_minimal :
    ∀ (n : ℕ) {x y : F}
      (a : AdicTruncation.obj ξ.base n ⟶ p.obj x)
      (b : AdicTruncation.obj object.base n ⟶ p.obj y)
      (toX : ξ.level n ⟶ x) (toY : object.level n ⟶ y)
      (g : y ⟶ x),
      p.IsHomLift a toX → p.IsHomLift b toY →
      p.IsStronglyCocartesian a toX → p.IsStronglyCocartesian b toY →
      (toY ≫ g = inclusion.app n ≫ toX) →
      (AlgHom.range (p.map g).hom =
        AlgHom.range ((AdicTruncation.map inclusion.base n ≫ a).hom)) →
      (hg : Function.Injective (p.map g).hom) →
      IsMinimalObject (⟨Over.mk g, hg⟩ : DescentObject p x)
  /-- Any morphism of formal objects into the descended one is surjective on bases. -/
  further_descent_surjective :
    ∀ (η : FormalObject p) (f : η ⟶ object), Function.Surjective f.base.hom

end Deformation

end
