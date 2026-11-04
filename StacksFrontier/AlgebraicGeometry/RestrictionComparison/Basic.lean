module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RestrictionComparison.OverSquare
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Restricting to the complement of finitely many closed points and to the local schemes

Let `S` be a scheme and let `s : I → S` be a finite family of closed points. Write
`U = S \ {s i | i}` for the open complement, `S_i = Spec 𝒪_{S, s i}` for the local scheme at
`s i`, and `U_i` for the preimage of `U` in `S_i`, the *punctured* local scheme. A scheme of
finite presentation over `S` restricts to one over `U` and to one over each `S_i`, and these
restrictions agree over each `U_i`.

This file constructs that agreement. The two restrictions to `U_i` are the two iterated base
changes attached to the commutative square
```
U_i --->  S_i
 |         |
 v         v
 U  ---->  S
```
whose bottom row is the open immersion `U ⟶ S` and whose right column is
`Scheme.fromSpecStalk`; the square commutes by `AlgebraicGeometry.morphismRestrict_ι`. The
comparison is therefore the base-change associativity isomorphism of
`CategoryTheory.Over.pullbackSquareIso`, and it is produced here together with the equation
saying that it commutes with the projections down to the scheme being restricted. That
equation is what pins the isomorphism down: it is the one of the two characterizing equations
of the comparison that is not already part of the data of a morphism over `U_i`.

This is the comparison datum of [Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q).

## Main definitions

* `AlgebraicGeometry.FinitePresentationOver`: the category of schemes of finite presentation
  over a fixed scheme.
* `AlgebraicGeometry.finitePresentationBaseChange`: base change of schemes of finite
  presentation along a morphism.
* `AlgebraicGeometry.complementOfClosedPoints`: the open complement of a finite family of
  closed points.
* `AlgebraicGeometry.puncturedLocalScheme`: the preimage of that complement in the local
  scheme at one of the points.
* `AlgebraicGeometry.restrictToComplementOfClosedPoints` and
  `AlgebraicGeometry.restrictToLocalSchemes`: the two restriction functors out of
  `FinitePresentationOver S`.
* `AlgebraicGeometry.restrictOpenToPuncturedLocals` and
  `AlgebraicGeometry.restrictLocalsToPuncturedLocals`: the two restriction functors into the
  product of the categories over the punctured local schemes.
* `AlgebraicGeometry.canonicalRestrictionComparison`: the canonical comparison isomorphism
  between the two composites, bundled with its compatibility equation.

## Main results

* `AlgebraicGeometry.finitePresentationPullbackSquareIso`: base change of schemes of finite
  presentation along a commutative square is associative up to natural isomorphism.
* `AlgebraicGeometry.finitePresentationBaseChange_isEquivalence_of_isIso`: base change of
  schemes of finite presentation along an isomorphism is an equivalence of categories.

## Implementation notes

`FinitePresentationOver T` is the full subcategory of `Over T` on the morphisms of finite
presentation, so a morphism in it is literally a morphism of `Over T` and the comparison
isomorphism is built by `ObjectProperty.isoMk` from an isomorphism of `Over U_i`. Finiteness
of the index type is used only to know that the complement of the family is open; the
construction below never splits the family up.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- Schemes of finite presentation over `T`, as the full subcategory of `Over T` on the
morphisms of finite presentation. -/
abbrev FinitePresentationOver (T : Scheme.{u}) :=
  (show ObjectProperty (Over T) from fun X ↦ FinitePresentation X.hom).FullSubcategory

/-- Base change of schemes of finite presentation along `g : T ⟶ S`. -/
noncomputable def finitePresentationBaseChange {S T : Scheme.{u}} (g : T ⟶ S) :
    FinitePresentationOver S ⥤ FinitePresentationOver T :=
  (show ObjectProperty (Over T) from fun X ↦ FinitePresentation X.hom).lift
    ((show ObjectProperty (Over S) from fun X ↦ FinitePresentation X.hom).ι ⋙
      Over.pullback g) (fun X ↦ by
      let _ : LocallyOfFinitePresentation X.obj.hom := X.property.1
      let _ : QuasiCompact X.obj.hom := X.property.2.1
      let _ : QuasiSeparated X.obj.hom := X.property.2.2
      change FinitePresentation (pullback.snd X.obj.hom g)
      refine ⟨inferInstance, inferInstance, inferInstance⟩)

/-- Base change of schemes of finite presentation along a commutative square
`q ≫ u = v ≫ p` is associative: restricting along `u` and then along `q` agrees with
restricting along `p` and then along `v`. -/
noncomputable def finitePresentationPullbackSquareIso {S U L V : Scheme.{u}} {u : U ⟶ S}
    {p : L ⟶ S} {v : V ⟶ L} {q : V ⟶ U} (w : q ≫ u = v ≫ p) :
    finitePresentationBaseChange u ⋙ finitePresentationBaseChange q ≅
      finitePresentationBaseChange p ⋙ finitePresentationBaseChange v :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ (Over.pullbackSquareObjIso w X.obj))
    (fun {X Y} f ↦ ObjectProperty.hom_ext _
      ((Over.pullbackSquareIso w).hom.naturality (X := X.obj) (Y := Y.obj) f.hom))

/-- The component of `AlgebraicGeometry.finitePresentationPullbackSquareIso` at `X`, as a
morphism of `Over V`, is the base-change associativity isomorphism of `X`. -/
@[simp]
theorem finitePresentationPullbackSquareIso_hom_app_hom {S U L V : Scheme.{u}} {u : U ⟶ S}
    {p : L ⟶ S} {v : V ⟶ L} {q : V ⟶ U} (w : q ≫ u = v ≫ p) (X : FinitePresentationOver S) :
    ((finitePresentationPullbackSquareIso w).hom.app X).hom =
      (Over.pullbackSquareObjIso w X.obj).hom :=
  rfl

/-- Base change along the identity morphism does nothing, up to natural isomorphism. -/
noncomputable def finitePresentationBaseChangeIdIso {S : Scheme.{u}} :
    finitePresentationBaseChange (𝟙 S) ≅ 𝟭 (FinitePresentationOver S) :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (Over.pullbackId.app X.obj))
    (fun {_ _} f ↦ ObjectProperty.hom_ext _ (Over.pullbackId.hom.naturality f.hom))

/-- Base change along the identity, iterated, is still naturally isomorphic to the identity. -/
noncomputable def finitePresentationBaseChangeCompSelfIdIso (X : Scheme.{u}) :
    finitePresentationBaseChange (𝟙 X) ⋙ finitePresentationBaseChange (𝟙 X) ≅
      𝟭 (FinitePresentationOver X) :=
  Functor.isoWhiskerRight finitePresentationBaseChangeIdIso
      (finitePresentationBaseChange (𝟙 X)) ≪≫
    Functor.leftUnitor _ ≪≫ finitePresentationBaseChangeIdIso

/-- Base change of schemes of finite presentation along an isomorphism is an equivalence of
categories, with quasi-inverse given by base change along the inverse isomorphism. -/
theorem finitePresentationBaseChange_isEquivalence_of_isIso
    {S T : Scheme.{u}} (g : T ⟶ S) [IsIso g] :
    (finitePresentationBaseChange g).IsEquivalence :=
  Functor.IsEquivalence.mk' (finitePresentationBaseChange (CategoryTheory.inv g))
    ((finitePresentationPullbackSquareIso
        (u := g) (p := 𝟙 S) (v := 𝟙 S) (q := CategoryTheory.inv g) (by simp)).trans
      (finitePresentationBaseChangeCompSelfIdIso S) |>.symm)
    ((finitePresentationPullbackSquareIso
        (u := CategoryTheory.inv g) (p := 𝟙 T) (v := 𝟙 T) (q := g) (by simp)).trans
      (finitePresentationBaseChangeCompSelfIdIso T))

/-- The open complement of a finite family of closed points. -/
def complementOfClosedPoints {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
    (hs : ∀ i, s i ∈ closedPoints S) : S.Opens where
  carrier := ⋂ i, ({s i}ᶜ : Set S)
  is_open' := isOpen_iInter_of_finite fun i ↦ (mem_closedPoints_iff.mp (hs i)).isOpen_compl

/-- The punctured local scheme at `s i`: the preimage in `Spec 𝒪_{S, s i}` of the open
complement of the whole family of points. -/
noncomputable abbrev puncturedLocalScheme {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
    (hs : ∀ i, s i ∈ closedPoints S) (i : I) : Scheme.{u} :=
  ((S.fromSpecStalk (s i)) ⁻¹ᵁ (complementOfClosedPoints s hs)).toScheme

/-- Restriction from the open complement to every punctured local scheme. -/
noncomputable def restrictOpenToPuncturedLocals {S : Scheme.{u}} {I : Type u} [Finite I]
    (s : I → S) (hs : ∀ i, s i ∈ closedPoints S) :
    FinitePresentationOver (complementOfClosedPoints s hs).toScheme ⥤
      ((i : I) → FinitePresentationOver (puncturedLocalScheme s hs i)) :=
  Functor.pi' (fun i ↦ finitePresentationBaseChange
    ((S.fromSpecStalk (s i)) ∣_ (complementOfClosedPoints s hs)))

/-- Restriction from every local scheme to its punctured local scheme. -/
noncomputable def restrictLocalsToPuncturedLocals {S : Scheme.{u}} {I : Type u} [Finite I]
    (s : I → S) (hs : ∀ i, s i ∈ closedPoints S) :
    ((i : I) → FinitePresentationOver (Spec (S.presheaf.stalk (s i)))) ⥤
      ((i : I) → FinitePresentationOver (puncturedLocalScheme s hs i)) where
  obj X i := (finitePresentationBaseChange
    (((S.fromSpecStalk (s i)) ⁻¹ᵁ (complementOfClosedPoints s hs)).ι)).obj (X i)
  map f := fun i ↦ (finitePresentationBaseChange
    (((S.fromSpecStalk (s i)) ⁻¹ᵁ (complementOfClosedPoints s hs)).ι)).map (f i)

/-- Restriction from the ambient scheme to the complement of the family of closed points. -/
noncomputable def restrictToComplementOfClosedPoints {S : Scheme.{u}} {I : Type u} [Finite I]
    (s : I → S) (hs : ∀ i, s i ∈ closedPoints S) :
    FinitePresentationOver S ⥤
      FinitePresentationOver (complementOfClosedPoints s hs).toScheme :=
  finitePresentationBaseChange (complementOfClosedPoints s hs).ι

/-- Simultaneous restriction from the ambient scheme to the local schemes at the points. -/
noncomputable def restrictToLocalSchemes {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S) :
    FinitePresentationOver S ⥤
      ((i : I) → FinitePresentationOver (Spec (S.presheaf.stalk (s i)))) :=
  Functor.pi' (fun i ↦ finitePresentationBaseChange (S.fromSpecStalk (s i)))

/-- The canonical comparison between the two restrictions of a scheme of finite presentation
over `S` to the punctured local schemes: on each factor it is the base-change associativity
isomorphism of the square `U_i ⟶ S_i ⟶ S = U_i ⟶ U ⟶ S`. -/
noncomputable def restrictionComparisonIso {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
    (hs : ∀ i, s i ∈ closedPoints S) :
    restrictToComplementOfClosedPoints s hs ⋙ restrictOpenToPuncturedLocals s hs ≅
      restrictToLocalSchemes s ⋙ restrictLocalsToPuncturedLocals s hs :=
  NatIso.pi' fun i ↦ finitePresentationPullbackSquareIso
    (morphismRestrict_ι (S.fromSpecStalk (s i)) (complementOfClosedPoints s hs))

/-- The component of `AlgebraicGeometry.restrictionComparisonIso` at `X` and `i`, as a morphism
of `Over U_i`, is the base-change associativity isomorphism of `X` for the square at `s i`. -/
@[simp]
theorem restrictionComparisonIso_hom_app_apply_hom {S : Scheme.{u}} {I : Type u} [Finite I]
    (s : I → S) (hs : ∀ i, s i ∈ closedPoints S) (X : FinitePresentationOver S) (i : I) :
    ((restrictionComparisonIso s hs).hom.app X i).hom =
      (Over.pullbackSquareObjIso
        (morphismRestrict_ι (S.fromSpecStalk (s i)) (complementOfClosedPoints s hs))
        X.obj).hom :=
  rfl

/-- **Stacks Project, Tag 0E8Q**, the canonical comparison. The base-change associativity
isomorphism identifying the two ways of restricting a scheme of finite presentation over `S`
to every punctured local scheme, together with the equation saying that it commutes with the
projections down to the scheme being restricted. -/
@[stacks 0E8Q "canonical comparison"]
noncomputable def canonicalRestrictionComparison {S : Scheme.{u}} {I : Type u} [Finite I]
    (s : I → S) (hs : ∀ i, s i ∈ closedPoints S) :
    { e : restrictToComplementOfClosedPoints s hs ⋙ restrictOpenToPuncturedLocals s hs ≅
        restrictToLocalSchemes s ⋙ restrictLocalsToPuncturedLocals s hs //
      ∀ (X : FinitePresentationOver S) (i : I),
        ((e.hom.app X) i).hom.left ≫
          pullback.fst
            (pullback.snd X.obj.hom (S.fromSpecStalk (s i)))
            (((S.fromSpecStalk (s i)) ⁻¹ᵁ (complementOfClosedPoints s hs)).ι) ≫
          pullback.fst X.obj.hom (S.fromSpecStalk (s i)) =
        pullback.fst
            (pullback.snd X.obj.hom (complementOfClosedPoints s hs).ι)
            ((S.fromSpecStalk (s i)) ∣_ (complementOfClosedPoints s hs)) ≫
          pullback.fst X.obj.hom (complementOfClosedPoints s hs).ι } :=
  ⟨restrictionComparisonIso s hs, fun X i ↦ by
    simp only [restrictionComparisonIso_hom_app_apply_hom]
    exact Over.pullbackSquareObjIso_hom_left_fst _ _⟩

end AlgebraicGeometry

end
