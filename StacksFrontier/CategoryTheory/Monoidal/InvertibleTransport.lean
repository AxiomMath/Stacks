module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence

/-!
# Transporting invertibility along a tensor comparison

Let `C` and `D` be monoidal categories with `D` braided, and let `F : C ⥤ D` be a functor
carrying, for each pair of objects, *some* isomorphism `F(A ⊗ B) ≅ F A ⊗ F B`, together with
an isomorphism `F(𝟙_ C) ≅ 𝟙_ D`. Then `F` sends invertible objects to invertible objects.

The point is that **no coherence is used**: neither naturality of the comparison, nor the
associativity or unitality squares that a `CategoryTheory.Functor.Monoidal` structure carries.
`CategoryTheory.MonoidalCategory.IsInvertible.map` does consume a `Functor.Monoidal`
structure, but it does not need to: invertibility in a *braided* category is a one-sided
condition (`CategoryTheory.MonoidalCategory.isInvertible_of_tensorIsoUnit`), so from
`X ⊗ X' ≅ 𝟙_ C` the single isomorphism

`F X ⊗ F X' ≅ F (X ⊗ X') ≅ F (𝟙_ C) ≅ 𝟙_ D`

already exhibits `F X` as invertible, and the braiding of `D` supplies the other side.

This matters wherever the comparison is available but the monoidal structure is not. The
derived stalk functor is the motivating case: the comparison
`(K ⊗^𝐋_𝒪 L)_x ≅ K_x ⊗^𝐋_{𝒪_x} L_x` of Stacks 01CB is available on arbitrary objects of
`D(𝒪)` (`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkNatIso`), whereas the
associativity and unitality coherence of the derived stalk functor is not.

The same observation makes invertibility insensitive to the *choice* of monoidal structure:
two monoidal structures on one category with pairwise isomorphic tensor products and
isomorphic units have the same invertible objects
(`CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided` at the identity
functor), which is what lets an invertibility statement proved for one inhabitant of the
derived tensor product be read at another.

## Main results

* `CategoryTheory.MonoidalCategory.hasInverse_of_iso` and `isInvertible_of_iso`: invertibility
  depends only on the isomorphism class of the object, with no braiding and no comparison.
* `CategoryTheory.MonoidalCategory.hasInverse_of_tensorComparison`: the two-sided inverse
  produced from a pairwise tensor comparison and a unit isomorphism, in a braided target.
* `CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided`: a functor
  with a pairwise tensor comparison and a unit isomorphism preserves invertibility.
* `CategoryTheory.MonoidalCategory.isInvertible_of_isInvertible_obj_of_tensorComparison`: an
  *equivalence* with a pairwise tensor comparison and a unit isomorphism **reflects**
  invertibility.

The reflecting direction is the one a transport along an equivalence usually needs, and it is
not a corollary of the preserving one: the inverse functor comes with no comparison of its own.
What replaces it is essential surjectivity — the inverse object produced in the target is the
image of an object of the source — together with full faithfulness, which turns the resulting
isomorphism in the target back into one in the source. Still no coherence is used.

## References

* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.MonoidalCategory

open scoped MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]
  {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]

omit [MonoidalCategory D] [BraidedCategory D] in
/-- **A two-sided tensor inverse is carried along an isomorphism of the object**: the same
object inverts both, the two isomorphisms being whiskered by `e⁻¹` on the appropriate side.
Nothing else is used — no braiding, and no monoidal structure beyond the whiskerings. -/
def hasInverse_of_iso {X X' : C} (e : X ≅ X') (h : HasInverse X) : HasInverse X' where
  inv := h.inv
  isoLeft := whiskerRightIso e.symm h.inv ≪≫ h.isoLeft
  isoRight := whiskerLeftIso h.inv e.symm ≪≫ h.isoRight

omit [MonoidalCategory D] [BraidedCategory D] in
/-- **Invertibility of an object of a monoidal category depends only on its isomorphism
class.** This is what lets an invertibility statement proved for one presentation of an object
be read at another — for instance at a functor replaced by an isomorphic one. -/
theorem isInvertible_of_iso {X X' : C} (e : X ≅ X') (h : IsInvertible X) : IsInvertible X' :=
  Nonempty.elim h fun hX => ⟨hasInverse_of_iso e hX⟩

/-- **A pairwise tensor comparison and a unit isomorphism carry a two-sided tensor inverse to a
two-sided tensor inverse**, when the target is braided. The isomorphism `F X ⊗ F X' ≅ 𝟙_ D` is
the comparison at `(X, X')` followed by `F` applied to `X ⊗ X' ≅ 𝟙_ C` and the unit
isomorphism; the opposite isomorphism `F X' ⊗ F X ≅ 𝟙_ D` is that one read through the
braiding of `D`, which is why no coherence of the comparison is needed. -/
def hasInverse_of_tensorComparison (F : C ⥤ D)
    (μ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D) {X : C} (h : HasInverse X) :
    HasInverse (F.obj X) :=
  HasInverse.ofBraided
    ((μ X h.inv).symm ≪≫ F.mapIso h.isoLeft ≪≫ ε)

/-- **A functor with a pairwise tensor comparison and a unit isomorphism preserves
invertibility**, when the target is braided. Unlike
`CategoryTheory.MonoidalCategory.IsInvertible.map` this asks for no naturality of the
comparison and for none of the coherence of a `CategoryTheory.Functor.Monoidal` structure. -/
theorem isInvertible_of_tensorComparison_of_braided (F : C ⥤ D)
    (μ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D) {X : C} (h : IsInvertible X) :
    IsInvertible (F.obj X) :=
  Nonempty.elim h fun hX => ⟨hasInverse_of_tensorComparison F μ ε hX⟩

omit [BraidedCategory D] in
/-- **An equivalence with a pairwise tensor comparison and a unit isomorphism reflects
invertibility**, when the source is braided: if `F X` is an invertible object of `D` then `X` is
an invertible object of `C`.

This is the direction a transport along an equivalence needs, and it does not follow from
`CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided` applied to the
inverse functor, which carries no comparison. The inverse object `Y` of `F X` is instead pulled
back along essential surjectivity, and the single isomorphism

`F (X ⊗ F⁻¹Y) ≅ F X ⊗ F (F⁻¹Y) ≅ F X ⊗ Y ≅ 𝟙_ D ≅ F (𝟙_ C)`

is carried to `X ⊗ F⁻¹Y ≅ 𝟙_ C` by full faithfulness; the braiding of `C` supplies the other
side. As in the preserving direction, no naturality of the comparison and no coherence of a
`CategoryTheory.Functor.Monoidal` structure is used.

The braiding is needed on the *source* only. The target keeps its monoidal structure and
nothing else, which is what lets this be read at a monoidal structure on a derived category
whose symmetry is not available. -/
theorem isInvertible_of_isInvertible_obj_of_tensorComparison [BraidedCategory C] (F : C ⥤ D)
    [F.Full] [F.Faithful] [F.EssSurj]
    (μ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D) {X : C} (h : IsInvertible (F.obj X)) :
    IsInvertible X :=
  Nonempty.elim h fun hX =>
    isInvertible_of_tensorIsoUnit (Y := F.objPreimage hX.inv)
      (F.preimageIso (μ X (F.objPreimage hX.inv) ≪≫
        whiskerLeftIso (F.obj X) (F.objObjPreimageIso hX.inv) ≪≫ hX.isoLeft ≪≫ ε.symm))

end CategoryTheory.MonoidalCategory

end
