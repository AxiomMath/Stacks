module

public import StacksFrontier.AlgebraicGeometry.EmptyLimitCounterexample.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The fullness assertion of Tag 0EY1 is false at a free index universe

Tag 0EY1 says that for a scheme which is the inverse limit of a directed system with affine
transition morphisms, the category of quasi-compact quasi-separated schemes locally of finite
presentation over the limit is the filtered colimit of the corresponding categories over the
terms of the system. Its *fullness* half asserts that a morphism over the limit between two
objects coming from a stage descends, after passing to a later stage, to a morphism between
their base changes.

Stated with the index type's universe left free of the scheme universe, and with no smallness
hypothesis on the index, that assertion is **false**. The statement is recorded here as
`Fullness`, and `not_fullness` refutes it at index universe `u + 1` over `Scheme.{u}`.

The witness is the cofiltered system of
`StacksFrontier.AlgebraicGeometry.EmptyLimitCounterexample.Basic`: the spectra of the finitely
generated subrings of a field which is not `u`-small, indexed by the finite subsets of that
field, whose limit is the **empty** scheme although no stage is empty. Over that limit take the
identity of the base stage and the empty scheme over the base stage. Every hypothesis of the
assertion holds: both objects are affine, hence quasi-compact and quasi-separated, the identity
and a morphism out of the empty scheme are locally of finite presentation, and over the empty
limit there is a (unique) morphism between the two base changes. But a morphism at a later
stage would be a morphism from a scheme receiving the nonempty stage into a scheme mapping to
the empty scheme, and there is none.

## Main definitions

* `Fullness`: the fullness assertion of Tag 0EY1, at two independent universe parameters — the
  index universe first, the scheme universe second.

## Main results

* `not_fullness`: the negation of `Fullness` at index universe one above the scheme universe.

## Implementation notes

The index of the witness is `Finset F` for a field `F` which is not `u`-small, which is not a
`u`-small type, so a smallness hypothesis on the index is necessary for the fullness assertion.

Over an empty limit every object has an empty source, so all objects over the limit are
isomorphic and *essential surjectivity* holds for this system.

## References

* [The Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [The Stacks Project, Tag 081D](https://stacks.math.columbia.edu/tag/081D)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Stacks.FullnessCounterexample

/-- A scheme admitting a morphism to an empty scheme is itself empty. -/
theorem isEmpty_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsEmpty Y) : IsEmpty X :=
  ⟨fun x => hY.elim (f.base x)⟩

/-- A scheme receiving a morphism from a nonempty scheme is nonempty. -/
theorem nonempty_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (hX : Nonempty X) : Nonempty Y :=
  ⟨f.base hX.some⟩

/-- The pullback of an identity along `g` receives the domain of `g`, hence is nonempty as
soon as that domain is. -/
theorem nonempty_pullback_id {X Y : Scheme.{u}} (g : Y ⟶ X) (hY : Nonempty Y) :
    Nonempty ↥(Limits.pullback (𝟙 X) g : Scheme.{u}) :=
  nonempty_of_hom (Limits.pullback.lift g (𝟙 Y) (by simp)) hY

/-- An object of the category of schemes over an empty scheme has an empty source. -/
theorem isEmpty_left {X : Scheme.{u}} (hX : IsEmpty X) (A : Over X) : IsEmpty A.left :=
  isEmpty_of_hom A.hom hX

/-- Over an empty scheme there is a morphism between any two objects. -/
def overHom {X : Scheme.{u}} (hX : IsEmpty X) (A B : Over X) : A ⟶ B :=
  haveI := isEmpty_left hX A
  Over.homMk (isInitialOfIsEmpty.to B.left) ((isInitialOfIsEmpty (X := A.left)).hom_ext _ _)

/-- The fullness assertion of Tag 0EY1, with index universe `v` and scheme universe `u`: for a
directed system `D` of schemes with affine transition morphisms and limit cone `c`, every
morphism over the limit between the base changes of two quasi-compact quasi-separated objects
locally of finite presentation over a stage `i` is, compatibly, the base change of a morphism
between their base changes to some later stage `j`. -/
def Fullness : Prop :=
  ∀ {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (_hc : IsLimit c) (i : I)
    (Xᵢ Yᵢ : Over (D.obj (.op i)))
    (_hXqc : CompactSpace Xᵢ.left) (_hXqs : QuasiSeparatedSpace Xᵢ.left)
    (_hYqc : CompactSpace Yᵢ.left) (_hYqs : QuasiSeparatedSpace Yᵢ.left)
    (_hX : LocallyOfFinitePresentation Xᵢ.hom)
    (_hY : LocallyOfFinitePresentation Yᵢ.hom)
    (f : (Over.pullback (c.π.app (.op i))).obj Xᵢ ⟶
      (Over.pullback (c.π.app (.op i))).obj Yᵢ),
    ∃ (j : I) (hij : i ≤ j)
      (g : (Over.pullback (D.map (homOfLE hij).op)).obj Xᵢ ⟶
        (Over.pullback (D.map (homOfLE hij).op)).obj Yᵢ)
      (α : (Over.pullback (c.π.app (.op j))).obj
          ((Over.pullback (D.map (homOfLE hij).op)).obj Xᵢ) ≅
        (Over.pullback (c.π.app (.op i))).obj Xᵢ)
      (β : (Over.pullback (c.π.app (.op j))).obj
          ((Over.pullback (D.map (homOfLE hij).op)).obj Yᵢ) ≅
        (Over.pullback (c.π.app (.op i))).obj Yᵢ),
      (α.hom.left ≫ Limits.pullback.fst Xᵢ.hom (c.π.app (.op i)) =
        Limits.pullback.fst ((Over.pullback (D.map (homOfLE hij).op)).obj Xᵢ).hom
            (c.π.app (.op j)) ≫ Limits.pullback.fst Xᵢ.hom (D.map (homOfLE hij).op)) ∧
      (β.hom.left ≫ Limits.pullback.fst Yᵢ.hom (c.π.app (.op i)) =
        Limits.pullback.fst ((Over.pullback (D.map (homOfLE hij).op)).obj Yᵢ).hom
            (c.π.app (.op j)) ≫ Limits.pullback.fst Yᵢ.hom (D.map (homOfLE hij).op)) ∧
      α.hom ≫ f = (Over.pullback (c.π.app (.op j))).map g ≫ β.hom

open Stacks.EmptyLimitCounterexample

/-- The base stage of the refuting system. -/
abbrev base : Scheme.{u} :=
  Spec (CommRingCat.of (stage bigField.{u} (∅ : Finset bigField.{u})))

/-- The base stage is quasi-compact. -/
instance : CompactSpace base.{u} :=
  inferInstanceAs (CompactSpace (PrimeSpectrum (stage bigField.{u} ∅)))

/-- The nonempty object over the base stage: the base stage over itself. -/
abbrev bigOver : Over base.{u} := Over.mk (𝟙 base.{u})

/-- The empty object over the base stage. -/
abbrev emptyOver : Over base.{u} := Over.mk (Scheme.emptyTo base.{u})

/-- The fullness assertion of Tag 0EY1 fails for an index type in universe `u + 1` and schemes
in universe `u`. -/
theorem not_fullness : ¬ Fullness.{u + 1, u} := by
  intro h
  obtain ⟨j, hij, g, -⟩ :=
    h (schemeDiagram bigField.{u}) (emptyCone bigField.{u}) isLimitEmptyConeBigField
      (∅ : Finset bigField.{u}) bigOver.{u} emptyOver.{u}
      (inferInstanceAs (CompactSpace base.{u}))
      (inferInstanceAs (QuasiSeparatedSpace base.{u}))
      (inferInstanceAs (CompactSpace (∅ : Scheme.{u})))
      (inferInstanceAs (QuasiSeparatedSpace (∅ : Scheme.{u})))
      (inferInstanceAs (LocallyOfFinitePresentation (𝟙 base.{u})))
      (inferInstanceAs (LocallyOfFinitePresentation (Scheme.emptyTo base.{u})))
      (overHom (inferInstanceAs (IsEmpty (∅ : Scheme.{u}))) _ _)
  refine (isEmpty_of_hom g.left ?_).elim (nonempty_pullback_id
    ((schemeDiagram bigField.{u}).map (homOfLE hij).op)
    (inferInstanceAs (Nonempty ((schemeDiagram bigField.{u}).obj (op j))))).some
  exact isEmpty_of_hom (Limits.pullback.fst (emptyOver.{u}).hom _)
    (inferInstanceAs (IsEmpty (∅ : Scheme.{u})))

end Stacks.FullnessCounterexample

end
