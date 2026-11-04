module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The Hilbert functor of points

Let `X` be a scheme over `S` and let `d` be a natural number. For an `S`-scheme `T`, a
*degree-`d` Hilbert family* in `X` over `T` is a closed subscheme of `X ×_S T` which is finite
locally free of rank `d` over `T`. The assignment `T ↦ {degree-d families over T}` is the
*Hilbert functor of points* `Hilb^d_{X/S}`, and a scheme `H` over `S` *represents* it when
morphisms `T ⟶ H` of `S`-schemes correspond bijectively to degree-`d` families over `T`,
naturally in `T`.

This file sets up that vocabulary. Closed subschemes are presented by their ideal sheaves
rather than by schemes together with a closed immersion, which avoids choosing a representative
of an isomorphism class; consequently a Hilbert family is determined by its ideal sheaf, which
is `HilbertFamily.ext`.

## Main definitions

* `Stacks.Hilbert.familyBaseChangeMap` — the map `X ×_S T' ⟶ X ×_S T` induced by `T' ⟶ T`.
* `Stacks.Hilbert.familyAmbientMap` — the map `X ×_S T ⟶ Y ×_S T` induced by `X ⟶ Y`.
* `Stacks.Hilbert.HilbertFamily` — a degree-`d` family of closed subschemes.
* `Stacks.Hilbert.RepresentsHilbertFunctorOfRank` — the data of a representing scheme,
  including the naturality of its universal family.
* `Stacks.Hilbert.ClosedSubschemeRepresentingHilbertFunctor` — a representing closed subscheme
  of a representing scheme of an ambient Hilbert functor.

## Main results

* `Stacks.Hilbert.HilbertFamily.ext` — a family is determined by its ideal sheaf.
* `Stacks.Hilbert.RepresentsHilbertFunctorOfRank.compare` and
  `Stacks.Hilbert.RepresentsHilbertFunctorOfRank.isoOver` — any two schemes representing the
  same Hilbert functor are canonically isomorphic over `S`.

## Implementation notes

Finite local freeness of a morphism of schemes, with a specified rank, is
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank` (Stacks Tag 02KA).

Representability is recorded as a structure carrying a family of bijections together with the
naturality equation, rather than as a natural isomorphism of functors, because the Hilbert
functor itself is not constructed here: the construction of the functor requires knowing that
the formation of degree-`d` families is functorial, which is exactly the naturality equation.

The comparison isomorphism between two representing schemes is the usual Yoneda argument. It is
available because naturality is recorded for the ideal sheaf and a family is determined by its
ideal sheaf, so the recorded naturality is full naturality of `family`.

No declaration here carries the `@[stacks 0B97]` attribute: Tag 0B97 is the statement that a
closed immersion `X ⟶ Y` induces one of Hilbert schemes, and it is proved in
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorClosedImmersion.lean`, which is where the
attribute lives.  `ClosedSubschemeRepresentingHilbertFunctor` is only the shape of its
conclusion.

## References

* [Stacks Project, Tag 0B94](https://stacks.math.columbia.edu/tag/0B94)
* [Stacks Project, Tag 0B97](https://stacks.math.columbia.edu/tag/0B97)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-- The canonical map `X ×_S T' ⟶ X ×_S T` associated to a morphism `T' ⟶ T` over `S`. -/
def familyBaseChangeMap {S : Scheme.{u}} (X : Over S) {T' T : Over S} (g : T' ⟶ T) :
    ((Over.pullback T'.hom).obj X).left ⟶ ((Over.pullback T.hom).obj X).left :=
  pullback.map X.hom T'.hom X.hom T.hom (𝟙 _) g.left (𝟙 _) (by simp) (by simp)

/-- The canonical map `X ×_S T ⟶ Y ×_S T` induced by a morphism `X ⟶ Y` over `S`. -/
def familyAmbientMap {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y) (T : Over S) :
    ((Over.pullback T.hom).obj X).left ⟶ ((Over.pullback T.hom).obj Y).left :=
  pullback.map X.hom T.hom Y.hom T.hom i.left (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- **Stacks Project, Section 0B94.** A degree-`d` Hilbert family in `X` over `T`: an ideal
sheaf on `X ×_S T` whose associated closed subscheme is finite locally free of rank `d` over
`T`.

This is the value `Hilb^d_{X/S}(T)` of the degree-`d` Hilbert functor, which the section
displays as the set of closed subschemes `Z ⊂ X_T` such that `Z → T` is finite locally free of
degree `d`. The functor itself, with its action by base change, is
`Stacks.Hilbert.hilbertFunctorOfRank`. -/
@[stacks 0B94 "the set `Hilb^d_{X/S}(T)`: the closed subschemes of `X_T` that are finite \
locally free of degree `d` over `T`.  The functor these sets are the values of is \
`Stacks.Hilbert.hilbertFunctorOfRank`, which carries the other part of this section"]
structure HilbertFamily {S : Scheme.{u}} (X T : Over S) (d : ℕ) where
  /-- The ideal sheaf on `X ×_S T` cutting out the family. -/
  ideal : ((Over.pullback T.hom).obj X).left.IdealSheafData
  /-- The closed subscheme cut out by `ideal` is finite locally free of rank `d` over `T`. -/
  isFiniteLocallyFreeOfRank :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) d

/-- A Hilbert family is determined by its ideal sheaf: the remaining field is a proposition. -/
@[ext]
theorem HilbertFamily.ext {S : Scheme.{u}} {X T : Over S} {d : ℕ} {Z W : HilbertFamily X T d}
    (h : Z.ideal = W.ideal) : Z = W := by
  obtain ⟨I, hI⟩ := Z
  obtain ⟨J, hJ⟩ := W
  subst h
  rfl

/-- A scheme `H` over `S` represents the degree-`d` Hilbert functor of `X` when maps `T ⟶ H`
correspond bijectively to degree-`d` families over `T`, naturally under base change. -/
structure RepresentsHilbertFunctorOfRank {S : Scheme.{u}} (X H : Over S) (d : ℕ) where
  /-- The universal family: morphisms into `H` are degree-`d` families. -/
  family : ∀ {T : Over S}, (T ⟶ H) ≃ HilbertFamily X T d
  /-- Restricting the family classified by `f` along `g` classifies the family of `g ≫ f`. -/
  naturality : ∀ {T' T : Over S} (g : T' ⟶ T) (f : T ⟶ H),
    (family (g ≫ f)).ideal = (family f).ideal.comap (familyBaseChangeMap X g)

namespace RepresentsHilbertFunctorOfRank

variable {S : Scheme.{u}} {X H H' : Over S} {d : ℕ}

/-- The comparison morphism from one representing scheme of the degree-`d` Hilbert functor to
another: the morphism classifying the universal family of the source. -/
def compare (h : RepresentsHilbertFunctorOfRank X H d)
    (h' : RepresentsHilbertFunctorOfRank X H' d) : H ⟶ H' :=
  h'.family.symm (h.family (𝟙 H))

/-- Composing with a comparison morphism classifies the same family. This is the Yoneda step:
it is naturality of both universal families together with `HilbertFamily.ext`. -/
theorem family_comp_compare (h : RepresentsHilbertFunctorOfRank X H d)
    (h' : RepresentsHilbertFunctorOfRank X H' d) {T : Over S} (f : T ⟶ H) :
    h'.family (f ≫ compare h h') = h.family f := by
  refine HilbertFamily.ext ?_
  rw [compare, h'.naturality f (h'.family.symm (h.family (𝟙 H))), Equiv.apply_symm_apply,
    ← h.naturality f (𝟙 H), Category.comp_id]

/-- The comparison morphisms between two representing schemes of the degree-`d` Hilbert functor
are mutually inverse. -/
theorem compare_comp_compare (h : RepresentsHilbertFunctorOfRank X H d)
    (h' : RepresentsHilbertFunctorOfRank X H' d) :
    compare h h' ≫ compare h' h = 𝟙 H := by
  refine h.family.injective ?_
  have h₁ := family_comp_compare h h' (𝟙 H)
  rw [Category.id_comp] at h₁
  rw [family_comp_compare h' h (compare h h'), h₁]

/-- **Uniqueness of the Hilbert scheme.** Any two schemes over `S` representing the degree-`d`
Hilbert functor of `X` are canonically isomorphic over `S`. -/
def isoOver (h : RepresentsHilbertFunctorOfRank X H d)
    (h' : RepresentsHilbertFunctorOfRank X H' d) : H ≅ H' where
  hom := compare h h'
  inv := compare h' h
  hom_inv_id := compare_comp_compare h h'
  inv_hom_id := compare_comp_compare h' h

end RepresentsHilbertFunctorOfRank

/-- The data produced from a representing Hilbert scheme of `Y`: a representing Hilbert scheme
of `X`, embedded as a closed subscheme of it, with the expected effect on families. -/
structure ClosedSubschemeRepresentingHilbertFunctor {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y)
    (d : ℕ) (H_Y : Over S) (hY : RepresentsHilbertFunctorOfRank Y H_Y d) where
  /-- The representing scheme for the Hilbert functor of `X`. -/
  H_X : Over S
  /-- It represents the degree-`d` Hilbert functor of `X`. -/
  represents : RepresentsHilbertFunctorOfRank X H_X d
  /-- Its embedding into the Hilbert scheme of `Y`. -/
  inclusion : H_X ⟶ H_Y
  /-- The embedding is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion inclusion.left
  /-- The family classified by `f ≫ inclusion` is the image of the family classified by `f`. -/
  family_ideal : ∀ {T : Over S} (f : T ⟶ H_X),
    (hY.family (f ≫ inclusion)).ideal =
      (represents.family f).ideal.map (familyAmbientMap i T)

end Stacks.Hilbert

end
