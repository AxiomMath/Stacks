module

public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Transporting invertibility along a functor that is monoidal only pointwise

A functor `F : C ⥤ D` between monoidal categories carries an invertible object
(`CategoryTheory.MonoidalCategory.IsInvertible`, Stacks 0FFN) to an invertible object as soon as
it is monoidal *at the two objects involved*: an isomorphism `𝟙_ D ≅ F.obj (𝟙_ C)` and, for a
chosen two-sided inverse `X'` of `X`, isomorphisms `F X ⊗ F X' ≅ F (X ⊗ X')` and
`F X' ⊗ F X ≅ F (X' ⊗ X)`. No naturality and no coherence law is used.

## Main definitions

* `CategoryTheory.MonoidalCategory.HasInverse.mapOfIsos`: the two-sided tensor inverse
  `F.obj h.inv` of `F.obj X` built from a two-sided tensor inverse `h` of `X` and the three
  comparison isomorphisms.

## Main results

* `CategoryTheory.MonoidalCategory.IsInvertible.mapOfIsos`: an invertible object stays invertible
  under a functor that admits the three comparison isomorphisms at the relevant objects.
* `CategoryTheory.MonoidalCategory.IsInvertible.mapOfTensorIsos`: the same with the comparison
  isomorphisms supplied for every pair, still with no coherence hypothesis.

## Implementation notes

This is strictly weaker in hypotheses than
`Stacks.SheafOfModules.IsInvertible.map` (StacksFrontier/Algebra/Category/ModuleCat/Sheaf/\
StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleEquivalence.lean), which asks for a full `CategoryTheory.Functor.Monoidal` structure on
`F`; that lemma is the special case in which the three isomorphisms are `Functor.Monoidal.εIso F`
and `Functor.Monoidal.μIso F`. Separating them matters for the consumers in this chapter, where
the functor of interest is **not** monoidal and cannot be:

* `DerivedCategory.singleFunctor _ 0 : Mod 𝒪_X ⥤ D(𝒪_X)` is not monoidal for the derived tensor
  product, since `M ⊗^L N` has nonvanishing cohomology in negative degrees as soon as `M` and `N`
  have a nonzero Tor. It is only *lax* monoidal, the comparison
  `single₀ M ⊗^L single₀ N ⟶ single₀ (M ⊗ N)` being the truncation onto `ℋ^0`, and a lax
  monoidal functor does not preserve invertibility. What is true, and what this file reduces the
  problem to, is that the comparison is an isomorphism at a pair one of whose members is flat —
  which is the case for an invertible module, that being locally free of rank one. So the
  obligation recorded in
  `StacksFrontier/Topology/Sheaves/Cohomology/InvertibleDerivedObjects.lean` as "`singleFunctor 0`
  is monoidal" is not provable as stated; what it needs is this lemma together with that one
  pointwise comparison.
* `ProductDecomposition.toOXMod`, which is `SheafOfModules.restrictScalars` along a projection
  `𝒪_X ⟶ 𝒪_n`, likewise carries no `Functor.Monoidal` instance; restriction of scalars along a
  ring map is lax monoidal in general and strong only under flatness-type hypotheses.

The proof is a three-step composite in each direction and uses no coherence, so it cannot be
obtained by weakening the conclusion of the monoidal-functor statement: it is a different
statement, with the comparison isomorphisms as data rather than as structure.

## References

* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

/-- The two-sided tensor inverse `F.obj h.inv` of `F.obj X`, built from a two-sided tensor
inverse `h` of `X`, an identification `εIso` of the unit of `D` with `F` of the unit of `C`, and
the two comparison isomorphisms at the pair `(X, h.inv)`. -/
def HasInverse.mapOfIsos (F : C ⥤ D) {X : C} (h : HasInverse X)
    (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
    (μLeft : F.obj X ⊗ F.obj h.inv ≅ F.obj (X ⊗ h.inv))
    (μRight : F.obj h.inv ⊗ F.obj X ≅ F.obj (h.inv ⊗ X)) :
    HasInverse (F.obj X) where
  inv := F.obj h.inv
  isoLeft := μLeft ≪≫ F.mapIso h.isoLeft ≪≫ εIso.symm
  isoRight := μRight ≪≫ F.mapIso h.isoRight ≪≫ εIso.symm

/-- **Invertibility transports along a functor that is monoidal only at the objects involved.**
If `X` is invertible with inverse `X'`, and `F` admits `𝟙_ D ≅ F (𝟙_ C)` together with
comparison isomorphisms at `(X, X')` and `(X', X)`, then `F.obj X` is invertible. No naturality
or coherence of the comparisons is required. -/
theorem IsInvertible.mapOfIsos (F : C ⥤ D) {X : C} (h : IsInvertible X)
    (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
    (μLeft : ∀ Z : C, F.obj X ⊗ F.obj Z ≅ F.obj (X ⊗ Z))
    (μRight : ∀ Z : C, F.obj Z ⊗ F.obj X ≅ F.obj (Z ⊗ X)) :
    IsInvertible (F.obj X) :=
  let ⟨h⟩ := h
  ⟨h.mapOfIsos F εIso (μLeft h.inv) (μRight h.inv)⟩

/-- The form of `IsInvertible.mapOfIsos` in which the comparison isomorphism is given for every
pair of objects; still no coherence law is used. -/
theorem IsInvertible.mapOfTensorIsos (F : C ⥤ D) {X : C} (h : IsInvertible X)
    (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
    (μ : ∀ Y Z : C, F.obj Y ⊗ F.obj Z ≅ F.obj (Y ⊗ Z)) :
    IsInvertible (F.obj X) :=
  h.mapOfIsos F εIso (fun Z => μ X Z) (fun Z => μ Z X)

end CategoryTheory.MonoidalCategory

end
