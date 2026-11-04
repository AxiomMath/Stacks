module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Maps into a K-injective complex are determined up to homotopy by their class in `D(A)`

Let `A` be an abelian category with a derived category and let `I` be a K-injective cochain
complex in `A`. K-injective orthogonality (Stacks 070G, in the form of Mathlib's
`CochainComplex.IsKInjective.Qh_map_bijective`) says that for any complex `K` the map

`Hom_{K(A)}(K, I) ⟶ Hom_{D(A)}(K, I)`

is bijective. Its injectivity is the statement that two morphisms of complexes `K ⟶ I` with the
same class in the derived category are chain homotopic. That consequence is used repeatedly and
is recorded here in the three forms in which it is wanted: equality in the homotopy category,
a chosen homotopy, and the mere existence of one.

Mathlib's bijectivity statement is about `DerivedCategory.Qh`, defined on the homotopy category,
while what one has in practice is an equality of `DerivedCategory.Q`-images, `Q` being defined on
complexes. The bridge is `DerivedCategory.quotientCompQhIso`, the isomorphism
`HomotopyCategory.quotient ⋙ Qh ≅ Q`, whose naturality turns the one into the other.

## Main results

* `CochainComplex.quotient_map_eq_of_Q_map_eq`: two morphisms into a K-injective complex with
  the same class in `D(A)` have the same image in the homotopy category.
* `CochainComplex.homotopyOfQMapEq`: the resulting homotopy between them.
* `CochainComplex.nonempty_homotopy_of_Q_map_eq`: the same, as an existence statement.

## Implementation notes

The three statements are separated because the data and the proposition are wanted in different
places: a construction needs `homotopyOfQMapEq`, while a proof by cases on a homotopy only needs
`nonempty_homotopy_of_Q_map_eq`.

Only the target is required to be K-injective; the source is an arbitrary complex. No hypothesis
beyond `Abelian` and `HasDerivedCategory` is imposed on `A` — in particular the ambient category
need not be Grothendieck abelian, which is why these are stated here rather than inside the
Grothendieck-abelian developments that previously carried private copies of them.

## References

* [Stacks Project, Lemma 13.31.2 (Tag 070G)](https://stacks.math.columbia.edu/tag/070G)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **Two morphisms into a K-injective complex with the same class in `D(A)` agree in the
homotopy category.** This is the injectivity half of K-injective orthogonality, transported from
`DerivedCategory.Qh` to `DerivedCategory.Q` along `DerivedCategory.quotientCompQhIso`. -/
theorem quotient_map_eq_of_Q_map_eq {K I : CochainComplex C ℤ} [I.IsKInjective]
    {f g : K ⟶ I} (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g := by
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) I).injective
  have h1 := DerivedCategory.quotientCompQhIso_hom_naturality (C := C) f
  have h2 := DerivedCategory.quotientCompQhIso_hom_naturality (C := C) g
  rw [h] at h1
  exact (cancel_mono _).mp (h1.trans h2.symm)

/-- **A homotopy between two morphisms into a K-injective complex with the same class in
`D(A)`.** -/
noncomputable def homotopyOfQMapEq {K I : CochainComplex C ℤ} [I.IsKInjective]
    {f g : K ⟶ I} (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Homotopy f g :=
  HomotopyCategory.homotopyOfEq _ _ (quotient_map_eq_of_Q_map_eq h)

/-- **Two morphisms into a K-injective complex with the same class in `D(A)` are homotopic.** -/
theorem nonempty_homotopy_of_Q_map_eq {K I : CochainComplex C ℤ} [I.IsKInjective]
    {f g : K ⟶ I} (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) :=
  ⟨homotopyOfQMapEq h⟩

end CochainComplex

end
