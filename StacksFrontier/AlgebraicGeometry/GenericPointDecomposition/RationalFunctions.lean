module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Rational functions on a scheme

A rational function on a scheme is a rational map to the affine line over the integers.
This file introduces that type and the dictionary which turns a rational function into a
section on a dense open and back.

## Main definitions

* `Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLine`: the affine line over `ℤ`.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.rationalFunctions`: the type of rational
  functions on a scheme, that is, of rational maps to the affine line.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.lineHom` and `lineHomEquiv`: morphisms to
  the affine line are the same thing as global sections.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.ofSectionOn` and `ofSection`: the rational
  function determined by a section on a dense open.

## Main results

* `Stacks.AlgebraicGeometry.GenericPointDecomposition.ofSectionOn_surjective`: every rational
  function comes from a section on a dense open.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.ofSectionOn_eq_iff`: two sections on dense
  opens give the same rational function exactly when they agree after restriction to some
  smaller dense open. This replaces the equality of morphisms in
  `AlgebraicGeometry.Scheme.PartialMap.equiv` by an equality of sections.

## Implementation notes

The affine line is taken over `Spec (ULift ℤ)`, which is terminal in the category of schemes;
consequently every scheme is canonically a scheme over it, the hypothesis `Scheme.Hom.IsOver`
in `AlgebraicGeometry.AffineSpace.homOverEquiv` is automatic, and morphisms to the affine line
are in bijection with global sections with no further hypothesis. That bijection is recorded
directly as `lineHomEquiv` rather than through `homOverEquiv`, with component maps
`AlgebraicGeometry.Scheme.Hom.appTop` of `coordinate` and `lineHom`.

The index type of the affine line is `ULift (Fin 1)`, a subsingleton, so a vector of sections
indexed by it is determined by its single value; the extensionality principle
`AlgebraicGeometry.AffineSpace.hom_ext` is applied with that in mind.

Sections are taken on the restricted scheme `U.toScheme`, as `Γ(U, ⊤)`, rather than on `X`, as
`Γ(X, U)`; the two are exchanged by `AlgebraicGeometry.Scheme.Opens.topIso`, and the former is
what a morphism out of `U.toScheme` acts on. `ofSection` takes a section in `Γ(X, U)`.

## References

* [Stacks Project, Tag 01RU](https://stacks.math.columbia.edu/tag/01RU)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointDecomposition

/-- The affine line over the integers, that is, over the terminal scheme `Spec (ULift ℤ)`. -/
noncomputable abbrev affineLine : Scheme.{u} :=
  AffineSpace (ULift.{u} (Fin 1)) (Spec (.of (ULift.{u} ℤ)))

/-- A rational function on `X` is a rational map from `X` to the affine line. -/
abbrev rationalFunctions (X : Scheme.{u}) : Type u :=
  X.RationalMap (affineLine : Scheme.{u})

/-- The standard coordinate on the affine line. -/
noncomputable abbrev coordinate : Γ(affineLine.{u}, ⊤) :=
  AffineSpace.coord (Spec (.of (ULift.{u} ℤ))) (ULift.up 0)

/-- The morphism to the affine line determined by a global section. -/
noncomputable def lineHom (Y : Scheme.{u}) (s : Γ(Y, ⊤)) : Y ⟶ affineLine :=
  AffineSpace.homOfVector (specULiftZIsTerminal.from Y) (fun _ : ULift.{u} (Fin 1) ↦ s)

/-- The morphism to the affine line attached to a section pulls the coordinate back to that
section. -/
@[simp]
lemma lineHom_appTop_coordinate (Y : Scheme.{u}) (s : Γ(Y, ⊤)) :
    (lineHom Y s).appTop coordinate = s :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- Two morphisms to the affine line are equal if they pull the coordinate back to the same
section. -/
private lemma hom_ext_of_appTop_coordinate {Y : Scheme.{u}} {f g : Y ⟶ affineLine}
    (h : f.appTop coordinate = g.appTop coordinate) : f = g :=
  AffineSpace.hom_ext (specULiftZIsTerminal.hom_ext _ _) fun i ↦ by
    obtain rfl : i = ULift.up 0 := Subsingleton.elim _ _
    exact h

/-- A morphism to the affine line is the one attached to the pullback of the coordinate. -/
lemma lineHom_appTop_coordinate_self (Y : Scheme.{u}) (f : Y ⟶ affineLine) :
    lineHom Y (f.appTop coordinate) = f :=
  hom_ext_of_appTop_coordinate (lineHom_appTop_coordinate Y _)

/-- Morphisms from `Y` to the affine line are the same thing as global sections of `Y`. -/
@[simps]
noncomputable def lineHomEquiv (Y : Scheme.{u}) : (Y ⟶ affineLine) ≃ Γ(Y, ⊤) where
  toFun f := f.appTop coordinate
  invFun s := lineHom Y s
  left_inv f := lineHom_appTop_coordinate_self Y f
  right_inv s := lineHom_appTop_coordinate Y s

/-- The section of `Y` underlying a morphism from `Y` to the affine line. -/
noncomputable abbrev lineSection {Y : Scheme.{u}} (f : Y ⟶ affineLine) : Γ(Y, ⊤) :=
  f.appTop coordinate

variable {X : Scheme.{u}}

/-- Restricting a section along an inclusion of opens is compatible with composition. -/
lemma homOfLE_appTop_appTop {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (s : Γ(W, ⊤)) :
    (X.homOfLE hUV).appTop ((X.homOfLE hVW).appTop s) =
      (X.homOfLE (hUV.trans hVW)).appTop s :=
  congrArg (fun k : U.toScheme ⟶ W.toScheme ↦ k.appTop s) (X.homOfLE_homOfLE hUV hVW)

/-- Composing an inclusion of opens with the morphism to the affine line attached to a section
restricts that section. -/
lemma homOfLE_comp_lineHom {U V : X.Opens} (hUV : V ≤ U) (s : Γ(U, ⊤)) :
    X.homOfLE hUV ≫ lineHom U.toScheme s =
      lineHom V.toScheme ((X.homOfLE hUV).appTop s) :=
  hom_ext_of_appTop_coordinate <| by
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, lineHom_appTop_coordinate]

/-- The partial map to the affine line given by a section on a dense open. -/
noncomputable def partialMapOfSection (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(U, ⊤)) :
    X.PartialMap (affineLine : Scheme.{u}) where
  domain := U
  dense_domain := hU
  hom := lineHom U.toScheme s

/-- The domain of the partial map given by a section on `U` is `U`. -/
@[simp]
lemma partialMapOfSection_domain (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(U, ⊤)) :
    (partialMapOfSection U hU s).domain = U := rfl

/-- The section underlying the partial map given by a section `s` is `s`. -/
@[simp]
lemma lineSection_partialMapOfSection (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(U, ⊤)) :
    lineSection (partialMapOfSection U hU s).hom = s :=
  lineHom_appTop_coordinate _ s

/-- The rational function determined by a section on a dense open, the section being taken on
the restricted scheme. -/
noncomputable def ofSectionOn (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(U, ⊤)) :
    rationalFunctions X :=
  (partialMapOfSection U hU s).toRationalMap

/-- The rational function determined by a section on a dense open. -/
noncomputable def ofSection (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(X, U)) :
    rationalFunctions X :=
  ofSectionOn U hU (U.topIso.inv s)

/-- Every partial map to the affine line is the one given by its own section. -/
lemma partialMapOfSection_lineSection (f : X.PartialMap (affineLine : Scheme.{u})) :
    partialMapOfSection f.domain f.dense_domain (lineSection f.hom) = f := by
  obtain ⟨U, hU, h⟩ := f
  exact congrArg (fun k ↦ (⟨U, hU, k⟩ : X.PartialMap (affineLine : Scheme.{u})))
    (lineHom_appTop_coordinate_self _ h)

/-- Every rational function is given by a section on a dense open. -/
lemma ofSectionOn_surjective (f : rationalFunctions X) :
    ∃ (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(U, ⊤)), ofSectionOn U hU s = f := by
  obtain ⟨g, hg⟩ := f.exists_rep
  exact ⟨g.domain, g.dense_domain, lineSection g.hom, by
    simpa only [ofSectionOn, partialMapOfSection_lineSection] using hg⟩

/-- Restricting a section to a smaller dense open does not change the rational function it
determines. -/
lemma ofSectionOn_homOfLE_appTop {U V : X.Opens} (hV : Dense (V : Set X)) (hUV : V ≤ U)
    (hU : Dense (U : Set X)) (s : Γ(U, ⊤)) :
    ofSectionOn V hV ((X.homOfLE hUV).appTop s) = ofSectionOn U hU s :=
  Scheme.PartialMap.toRationalMap_eq_iff.mpr
    ⟨V, hV, le_rfl, hUV,
      (congrArg (fun k : V.toScheme ⟶ V.toScheme ↦
            k ≫ lineHom V.toScheme ((X.homOfLE hUV).appTop s)) (X.homOfLE_rfl V)).trans
        ((Category.id_comp _).trans (homOfLE_comp_lineHom hUV s).symm)⟩

/-- Two sections on dense opens determine the same rational function exactly when they agree
after restriction to some dense open contained in both. -/
lemma ofSectionOn_eq_iff {U V : X.Opens} (hU : Dense (U : Set X)) (hV : Dense (V : Set X))
    (s : Γ(U, ⊤)) (t : Γ(V, ⊤)) :
    ofSectionOn U hU s = ofSectionOn V hV t ↔
      ∃ (W : X.Opens) (_ : Dense (W : Set X)) (hWU : W ≤ U) (hWV : W ≤ V),
        (X.homOfLE hWU).appTop s = (X.homOfLE hWV).appTop t := by
  refine ⟨fun h ↦ ?_, fun ⟨W, hW, hWU, hWV, hst⟩ ↦ ?_⟩
  · obtain ⟨W, hW, hWU, hWV, hhom⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp h
    refine ⟨W, hW, hWU, hWV, ?_⟩
    have hhom' : X.homOfLE hWU ≫ lineHom U.toScheme s
        = X.homOfLE hWV ≫ lineHom V.toScheme t := hhom
    exact (lineHomEquiv W.toScheme).symm.injective
      ((homOfLE_comp_lineHom hWU s).symm.trans
        (hhom'.trans (homOfLE_comp_lineHom hWV t)))
  · exact (ofSectionOn_homOfLE_appTop hW hWU hU s).symm.trans
      (hst ▸ ofSectionOn_homOfLE_appTop hW hWV hV t)

end Stacks.AlgebraicGeometry.GenericPointDecomposition
