module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Properness of the scheme-theoretic image

The scheme-theoretic image in a separated scheme locally of finite type over a base of a
universally closed morphism to that base is proper over the base. The canonical morphism to
the scheme-theoretic image is surjective.

## Main results

* `AlgebraicGeometry.isProper_imageι_comp`: the scheme-theoretic image is proper over the
  base.
* `AlgebraicGeometry.surjective_toImage`: the canonical morphism to the scheme-theoretic
  image is surjective.

## Implementation notes

The map from `X` to the base in the commutative triangle is represented canonically by the
composite `h ≫ g`. The two conclusions are stated separately: the surjectivity conclusion
does not require the local finite-type hypothesis.

## References

* [Stacks Project, Tag 0AH6](https://stacks.math.columbia.edu/tag/0AH6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 0AH6, properness.** The scheme-theoretic image in a separated scheme locally of
finite type over the base of a universally closed morphism to the base is proper over the
base. -/
@[stacks 0AH6 "properness of the scheme-theoretic image", ega "II 5.4.9" "5.4.3(ii), special case"]
lemma isProper_imageι_comp {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    [UniversallyClosed (h ≫ g)] [IsSeparated g] [LocallyOfFiniteType g] :
    IsProper (h.imageι ≫ g) := by
  have : UniversallyClosed h := UniversallyClosed.of_comp_of_isSeparated h g
  have : Surjective h.toImage := Surjective.of_universallyClosed_of_isDominant h.toImage
  have : UniversallyClosed (h.toImage ≫ h.imageι ≫ g) := by simpa
  have := UniversallyClosed.of_comp_surjective h.toImage (h.imageι ≫ g)
  exact ⟨⟩

/-- **Stacks 0AH6, surjectivity.** Under the separatedness hypothesis, the canonical morphism
to the scheme-theoretic image of a universally closed composite is surjective. -/
@[stacks 0AH6 "surjectivity onto the scheme-theoretic image"]
lemma surjective_toImage {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    [UniversallyClosed (h ≫ g)] [IsSeparated g] : Surjective h.toImage := by
  have : UniversallyClosed h := UniversallyClosed.of_comp_of_isSeparated h g
  exact Surjective.of_universallyClosed_of_isDominant h.toImage

end AlgebraicGeometry

end
