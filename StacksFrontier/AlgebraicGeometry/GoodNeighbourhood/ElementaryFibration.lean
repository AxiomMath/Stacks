module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Elementary fibrations

An *elementary fibration* (SGA 4, Exposé XI, Définition 3.1; also J. S. Milne, *Lectures on étale
cohomology*, the section on Artin's good neighbourhoods) is a morphism `f : U ⟶ S` which is the
complement of a finite étale divisor in a smooth projective family of geometrically irreducible
curves. Precisely, there are an open immersion `j : U ⟶ X̄` and a morphism `f̄ : X̄ ⟶ S` with
`j ≫ f̄ = f` such that

* `f̄` is smooth of relative dimension `1`, projective, and has geometrically irreducible fibres;
* the reduced closed subscheme `Z = X̄ ∖ j(U)` is finite, étale and surjective over `S`.

## Main definitions

* `AlgebraicGeometry.IsElementaryFibration`: the predicate.

## Main results

* `AlgebraicGeometry.IsElementaryFibration.exists_compactification`: the compactification
  `X̄`, its boundary `Z` and all their properties.
* `AlgebraicGeometry.IsElementaryFibration.exists_compactification_smoothOfRelativeDimension`:
  if `S` is smooth of relative dimension `n` over a base `T`, then `X̄` is smooth of relative
  dimension `1 + n` over `T`.

## Implementation notes

*How the conditions are spelled.* "Smooth with fibres of dimension `1`" is Mathlib's
`AlgebraicGeometry.SmoothOfRelativeDimension 1`. "Projective" is H-projectivity,
`AlgebraicGeometry.IsProjectiveMorphism`: a closed immersion into `ℙⁿ_S` over `S`. This implies
projectivity in the sense of [Stacks, Tag 01W8]. "Geometrically irreducible fibres" is Mathlib's
`AlgebraicGeometry.GeometricallyIrreducible`: `X̄ ×_S Spec K` is irreducible, in particular
nonempty, for every field `K` over `S`.

*The boundary.* The boundary is an arbitrary reduced closed subscheme `i : Z ⟶ X̄` whose
support is the complement of the image of `j`. A closed subset carries exactly one reduced
closed subscheme structure, so this is the reduced induced structure on `X̄ ∖ j(U)` of the
source, up to unique isomorphism over `X̄`.

## References

* SGA 4, Tome 3, Exposé XI, Définition 3.1 and Proposition 3.3.
* J. S. Milne, *Lectures on étale cohomology*, the section on good neighbourhoods.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Elementary fibration** (SGA 4, Exposé XI, Définition 3.1). A morphism `f : U ⟶ S` is an
elementary fibration if it is the restriction of a morphism `f̄ : X̄ ⟶ S` to the complement of a
finite étale divisor. That is, there are an open immersion `j : U ⟶ X̄` and `f̄` with
`j ≫ f̄ = f` such that

* `f̄` is smooth of relative dimension `1`, projective (`AlgebraicGeometry.IsProjectiveMorphism`)
  and geometrically irreducible, so its fibres are geometrically irreducible smooth projective
  curves;
* a reduced closed subscheme `i : Z ⟶ X̄` with support `X̄ ∖ j(U)` is finite, étale and
  surjective over `S`. -/
@[sga "4½ Arcata 3.4.2"]
structure IsElementaryFibration {U S : Scheme.{u}} (f : U ⟶ S) : Prop where
  /-- The compactification `X̄` of `U` over `S`, with boundary `Z`. -/
  exists_compactification : ∃ (Xbar Z : Scheme.{u}) (j : U ⟶ Xbar) (fbar : Xbar ⟶ S)
      (i : Z ⟶ Xbar),
    IsOpenImmersion j ∧ j ≫ fbar = f ∧ SmoothOfRelativeDimension 1 fbar ∧
      IsProjectiveMorphism fbar ∧ GeometricallyIrreducible fbar ∧ IsClosedImmersion i ∧
      IsReduced Z ∧ Set.range i.base = (Set.range j.base)ᶜ ∧ IsFinite (i ≫ fbar) ∧
      Etale (i ≫ fbar) ∧ Surjective (i ≫ fbar)

namespace IsElementaryFibration

variable {U S : Scheme.{u}} {f : U ⟶ S}

/-- **The total space of the compactification is smooth over the base of `S`.** If `f : U ⟶ S`
is an elementary fibration and `q : S ⟶ T` is smooth of relative dimension `n`, then the
compactification `f̄ : X̄ ⟶ S` can be chosen, with all the properties of the definition, so that
`f̄ ≫ q` is smooth of relative dimension `1 + n`. In fact every compactification has this
property: relative dimensions add under composition. -/
theorem exists_compactification_smoothOfRelativeDimension (hf : IsElementaryFibration f)
    {T : Scheme.{u}} (q : S ⟶ T) (n : ℕ) [SmoothOfRelativeDimension n q] :
    ∃ (Xbar Z : Scheme.{u}) (j : U ⟶ Xbar) (fbar : Xbar ⟶ S) (i : Z ⟶ Xbar),
      IsOpenImmersion j ∧ j ≫ fbar = f ∧ SmoothOfRelativeDimension 1 fbar ∧
        IsProjectiveMorphism fbar ∧ GeometricallyIrreducible fbar ∧ IsClosedImmersion i ∧
        IsReduced Z ∧ Set.range i.base = (Set.range j.base)ᶜ ∧ IsFinite (i ≫ fbar) ∧
        Etale (i ≫ fbar) ∧ Surjective (i ≫ fbar) ∧
        SmoothOfRelativeDimension (1 + n) (fbar ≫ q) := by
  obtain ⟨Xbar, Z, j, fbar, i, hj, hjf, hsm, hproj, hgi, hi, hZ, hrange, hfin, het, hsurj⟩ :=
    hf.exists_compactification
  exact ⟨Xbar, Z, j, fbar, i, hj, hjf, hsm, hproj, hgi, hi, hZ, hrange, hfin, het, hsurj,
    inferInstance⟩

end IsElementaryFibration

end AlgebraicGeometry

end
