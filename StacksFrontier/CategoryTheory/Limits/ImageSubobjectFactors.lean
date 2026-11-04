module

public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Image subobjects of mutually factoring morphisms

Two morphisms `f : A ⟶ Y` and `g : B ⟶ Y` with a common target have the same image as soon as
each of them factors through the other. A factorization `f = u ≫ g` exhibits the image of `f` as
a subobject of the image of `g`, and the opposite factorization gives the reverse inequality;
since `Subobject Y` is a partial order the two inequalities force the image subobjects to be
equal. An equality of subobjects of `Y` is in turn realized by an isomorphism between the chosen
image objects which commutes with their inclusions into `Y`, so mutually factoring morphisms have
canonically isomorphic images over `Y`.

This is the form in which images are compared in an inverse system, where the morphisms being
compared are the restrictions of one map along a tower of transition maps and only the existence
of the intermediate factorizations is available.

## Main results

* `CategoryTheory.Limits.imageSubobject_eq_of_factors` — mutually factoring morphisms into a
  common object have equal image subobjects.
* `CategoryTheory.Limits.imageIsoOfSubobjectEq` — an equality of image subobjects is witnessed by
  an isomorphism of the chosen image objects commuting with the image inclusions.
* `CategoryTheory.Limits.imageIsoOfMutualFactors` — the combination of the two: mutual
  factorization identifies the two image objects over their common target.

## Implementation notes

The factorizations enter as existential hypotheses rather than as data, because the conclusions
depend only on their existence: the image subobject of `f` is determined by `f`, and the
isomorphism produced from an equality of subobjects is determined by that equality. The inclusion
`image f ≤ image g` underlying all of this is Mathlib's `imageSubobject_comp_le`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasImages C] {A B Y : C}

/-- Equal image subobjects give an isomorphism between the chosen image objects whose
inclusions into the ambient object agree. -/
public theorem imageIsoOfSubobjectEq (f : A ⟶ Y) (g : B ⟶ Y)
    (h : imageSubobject f = imageSubobject g) :
    ∃ e : image f ≅ image g, e.hom ≫ image.ι g = image.ι f := by
  refine ⟨Subobject.isoOfMkEqMk (image.ι f) (image.ι g) h, ?_⟩
  simp [Subobject.isoOfMkEqMk]

/-- Morphisms into a common object that factor through each other have the same image
subobject. -/
public theorem imageSubobject_eq_of_factors (f : A ⟶ Y) (g : B ⟶ Y)
    (hfg : ∃ u : A ⟶ B, u ≫ g = f) (hgf : ∃ v : B ⟶ A, v ≫ f = g) :
    imageSubobject f = imageSubobject g := by
  obtain ⟨u, hu⟩ := hfg
  obtain ⟨v, hv⟩ := hgf
  exact le_antisymm (hu ▸ imageSubobject_comp_le u g) (hv ▸ imageSubobject_comp_le v f)

/-- Mutual factorization identifies the two chosen image objects over their common target,
compatibly with the image inclusions. -/
public theorem imageIsoOfMutualFactors (f : A ⟶ Y) (g : B ⟶ Y)
    (hfg : ∃ u : A ⟶ B, u ≫ g = f) (hgf : ∃ v : B ⟶ A, v ≫ f = g) :
    ∃ e : image f ≅ image g, e.hom ≫ image.ι g = image.ι f :=
  imageIsoOfSubobjectEq f g (imageSubobject_eq_of_factors f g hfg hgf)

end CategoryTheory.Limits

end
