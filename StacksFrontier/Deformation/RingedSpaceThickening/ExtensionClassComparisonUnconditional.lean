module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing the two classes of Stacks 0GQ1 with every input removed

`AlgebraicGeometry.RingedSpaceThickening.exists_compatibleLift_iff_eq_restrictExtClass` of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionClassComparison.lean` states the
equivalence of **Stacks 0GQ1** — the two classes `ξ ∈ Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)` and
`ζ ∈ Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢)` agree in `Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)` exactly when a compatible
`S`-morphism exists — for a type `Lift` of compatible morphisms given together with a bijection
`e` onto the factorizations of a homomorphism `δ` out of the conormal term, and with the
compatibility `hcompat` identifying the difference of the two classes with the class of `δ`.

This file removes all three inputs.  The equivalence holds in the form

`ξ = restrictExtClass ζ ↔ ∃ δ, ξ - restrictExtClass ζ = conormalExtClass δ ∧`
`  (δ factors through the degree 0 term)`,

whose only binders are the two morphisms `g`, `f`, the module `𝒢` and the two classes: no
`Lift`, no `e` and no `hcompat`.  It implies the statement of
`exists_compatibleLift_iff_eq_restrictExtClass` for every `δ`, `Lift`, `e` and `hcompat`.

Two further statements measure each of the removed inputs separately.  The bijection `e` is
dischargeable outright: `nonempty_factorization_iff_eq_restrictExtClass` is the original
equivalence at `Lift` the set of factorizations itself, where `e` is the identity, which is the
shape the ringed-topos twin **Stacks 08UG** uses in
`Deformation.ToposThickening.LiftDiagram.liftingObstruction_eq_zero_iff`.  And `hcompat` is not
an independent assumption either: by `exists_conormalExtClass_sub_iff` a homomorphism `δ`
satisfying it exists if and only if the two classes have the same restriction to the degree `0`
term of `g^*𝖭𝖫_{X/S}`, a condition on `ξ` and `ζ` alone, and
`conormalOfExtClassDifference` produces `δ` and `hcompat` from it.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.conormalOfExtClassDifference`: a homomorphism out of
  the conormal term of `g^*𝖭𝖫_{X/S}` whose class is the difference of the two classes, together
  with that identification, produced from the equality of their restrictions to the degree `0`
  term.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.eq_restrictExtClass_iff_exists_factorization`: the
  equivalence of **Stacks 0GQ1** with every input removed.  This is where **Stacks 0GQ1** is
  registered.
* `AlgebraicGeometry.RingedSpaceThickening.nonempty_factorization_iff_eq_restrictExtClass`: the
  same equivalence with the compatible morphisms taken to be the factorizations themselves, so
  that the bijection `e` is the identity.
* `AlgebraicGeometry.RingedSpaceThickening.exists_conormalExtClass_sub_iff`: a homomorphism `δ`
  satisfying `hcompat` exists exactly when the two classes restrict to the same class on the
  degree `0` term of `g^*𝖭𝖫_{X/S}`.
* `AlgebraicGeometry.RingedSpaceThickening`
  `.nonempty_factorization_conormalOfExtClassDifference_iff`: the equivalence with `δ`, `e` and
  `hcompat` all removed, on that condition alone.

## Implementation notes

**Stacks 0GQ1** is registered on `eq_restrictExtClass_iff_exists_factorization` below, and on
the two components `pulledNaiveCotangentComparison` and `restrictExtClass` of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionClassComparison.lean`.  The equivalence
below reads the source's left hand side through Steps 1 to 3 of **Stacks 08U8**: the existence
of a compatible `S`-morphism `Y' ⟶ X'` is replaced by the existence of a homomorphism out of
the conormal term representing the difference of the two classes and factoring through the
degree `0` term, which is the condition those steps show that existence to be equivalent to.
The two sides of the source's statement are therefore related exactly as in the ringed-topos
twin, where the same substitution is recorded in the implementation notes of
`StacksFrontier/Deformation/ToposThickening/LiftingBetweenThickenings.lean`.  What this file adds
is that no part of the equivalence has to be assumed, which is why the registration sits here
rather than on `exists_compatibleLift_iff_eq_restrictExtClass`: that statement takes the
homomorphism `δ`, a type `Lift` of compatible morphisms, a bijection `e` identifying it with
the factorizations, and the compatibility `hcompat` as binders, none of them a hypothesis of
**Stacks 0GQ1**.

The comparison group is the `Ext¹` of the degreewise pullback `g^*𝖭𝖫_{X/S}`, as in
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionClassComparison.lean`; nothing here
changes that reading.

## References

* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

section Additivity

variable {M : Type*} [Category M] {D : Type*} [Category D] [Limits.HasZeroObject D]
  [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [CategoryTheory.Pretriangulated D] {single : M ⥤ D}

/-- The restriction of a class in `Ext¹(NL(α), 𝒢)` to the degree `0` term of `NL(α)` is
additive: it is precomposition with the inclusion of that term. -/
theorem NaiveCotangentTwoTerm.obstruction_sub (P : NaiveCotangentTwoTerm single) (G : M)
    (a b : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧) :
    P.obstruction G (a - b) = P.obstruction G a - P.obstruction G b :=
  Preadditive.comp_sub _ _ _

/-- Two classes in `Ext¹(NL(α), 𝒢)` have the same restriction to the degree `0` term of `NL(α)`
exactly when the restriction of their difference vanishes. -/
theorem NaiveCotangentTwoTerm.obstruction_sub_eq_zero_iff (P : NaiveCotangentTwoTerm single)
    (G : M) (a b : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧) :
    P.obstruction G (a - b) = 0 ↔ P.obstruction G a = P.obstruction G b := by
  rw [P.obstruction_sub G a b, sub_eq_zero]

end Additivity

variable {X S Y : RingedSpace.{u, u}}

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (g : Y ⟶ X) (f : X ⟶ S)
  (G : SheafOfModules.{u} (ringSheaf
    (J := Opens.grothendieckTopology Y.carrier) Y.sheaf))

/-- **Stacks Project, Tag 0GQ1**, with every input removed.  The two classes agree in
`Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)` if and only if their difference is the class of a homomorphism `δ`
out of the conormal term of `g^*𝖭𝖫_{X/S}` which factors through the degree `0` term.

The right hand side is the condition that Steps 1 to 3 of the proof of **Stacks 08U8** identify
with the existence of a compatible `S`-morphism `Y' ⟶ X'`.  Compared with
`exists_compatibleLift_iff_eq_restrictExtClass` the homomorphism `δ`, the type `Lift`, the
bijection `e` and the compatibility `hcompat` are all gone: the only binders are `g`, `f`, `𝒢`
and the two classes.  That statement follows from this one for every choice of them. -/
@[stacks 0GQ1 "the equivalence with every input removed: the two Ext¹ classes agree exactly \
when their difference is the class of a homomorphism δ out of the conormal term of \
g^*𝖭𝖫_{X/S} which factors through the degree 0 term. The binders are g, f, 𝒢 and the two \
classes alone — there is no type of compatible morphisms, no bijection e and no compatibility \
hcompat — and this implies exists_compatibleLift_iff_eq_restrictExtClass of \
ExtensionClassComparison.lean for every choice of those four. The right hand side is the \
condition that Steps 1 to 3 of the proof of 08U8 identify with the existence of a compatible \
S-morphism Y' ⟶ X'; that identification is a separate result of the source, so the left hand \
side of the source's own equivalence is read here through it. The comparison group is the Ext¹ \
of the DEGREEWISE pullback g^*𝖭𝖫_{X/S} rather than of the derived pullback Lg^*𝖭𝖫_{X/S} of the \
source's statement, and ξ is a FREE ELEMENT of that group rather than the image of the class \
of the extension of 𝒪_X: the first of the source's two maps, which would carry that class in, \
is absent here"]
theorem eq_restrictExtClass_iff_exists_factorization
    (ξ : pulledExtGroup g f G) (ζ : relativeExtGroup g f G) :
    ξ = restrictExtClass g f G ζ ↔
      ∃ δ : (pulledNaiveCotangentTwoTerm g f).conormal ⟶ G,
        ξ - restrictExtClass g f G ζ =
            (pulledNaiveCotangentTwoTerm g f).conormalExtClass G δ ∧
          Nonempty { θ : (pulledNaiveCotangentTwoTerm g f).base ⟶ G //
            (pulledNaiveCotangentTwoTerm g f).d ≫ θ = δ } := by
  have hz := (pulledNaiveCotangentTwoTerm g f).conormalExtClass_eq_zero_iff G
  constructor
  · intro h
    exact ⟨0, (sub_eq_zero.2 h).trans ((hz 0).2 ⟨0, comp_zero⟩).symm, ⟨⟨0, comp_zero⟩⟩⟩
  · rintro ⟨δ, hcompat, θ, hθ⟩
    exact sub_eq_zero.1 (hcompat.trans ((hz δ).2 ⟨θ, hθ⟩))

/-- **Stacks Project, Tag 0GQ1 with the bijection `e` discharged.** The equivalence of
`exists_compatibleLift_iff_eq_restrictExtClass` at `Lift` the set of factorizations of `δ`
through the degree `0` term itself, where `e` is the identity.

This is the shape in which the ringed-topos twin **Stacks 08UG** is stated unconditionally, by
`Deformation.ToposThickening.LiftDiagram.liftingObstruction_eq_zero_iff`. -/
theorem nonempty_factorization_iff_eq_restrictExtClass
    (δ : (pulledNaiveCotangentTwoTerm g f).conormal ⟶ G)
    (ξ : pulledExtGroup g f G) (ζ : relativeExtGroup g f G)
    (hcompat : ξ - restrictExtClass g f G ζ =
      (pulledNaiveCotangentTwoTerm g f).conormalExtClass G δ) :
    Nonempty { θ : (pulledNaiveCotangentTwoTerm g f).base ⟶ G //
        (pulledNaiveCotangentTwoTerm g f).d ≫ θ = δ } ↔
      ξ = restrictExtClass g f G ζ :=
  exists_compatibleLift_iff_eq_restrictExtClass g f G δ (Equiv.refl _) ξ ζ hcompat

/-- **The compatibility `hcompat` is not an independent assumption.** A homomorphism `δ` out of
the conormal term of `g^*𝖭𝖫_{X/S}` whose class is the difference of the two classes exists if
and only if `ξ` and `restrictExtClass ζ` have the same restriction to the degree `0` term of
`g^*𝖭𝖫_{X/S}` — a condition on the two classes alone.

The restriction to the degree `0` term is
`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.obstruction`, precomposition
with the inclusion of that term. -/
theorem exists_conormalExtClass_sub_iff
    (ξ : pulledExtGroup g f G) (ζ : relativeExtGroup g f G) :
    (∃ δ : (pulledNaiveCotangentTwoTerm g f).conormal ⟶ G,
        ξ - restrictExtClass g f G ζ =
          (pulledNaiveCotangentTwoTerm g f).conormalExtClass G δ) ↔
      (pulledNaiveCotangentTwoTerm g f).obstruction G ξ =
        (pulledNaiveCotangentTwoTerm g f).obstruction G (restrictExtClass g f G ζ) :=
  ((pulledNaiveCotangentTwoTerm g f).obstruction_eq_zero_iff G
      (ξ - restrictExtClass g f G ζ)).symm.trans
    ((pulledNaiveCotangentTwoTerm g f).obstruction_sub_eq_zero_iff G ξ
      (restrictExtClass g f G ζ))

/-- **The producer of `δ` and `hcompat`.** From the equality of the restrictions of the two
classes to the degree `0` term of `g^*𝖭𝖫_{X/S}`, a homomorphism out of the conormal term whose
class is the difference of the two classes, together with that identification: the pair of
inputs `δ` and `hcompat` of `exists_compatibleLift_iff_eq_restrictExtClass`.

By `exists_conormalExtClass_sub_iff` the hypothesis is not merely sufficient but necessary. -/
def conormalOfExtClassDifference (ξ : pulledExtGroup g f G) (ζ : relativeExtGroup g f G)
    (hobs : (pulledNaiveCotangentTwoTerm g f).obstruction G ξ =
      (pulledNaiveCotangentTwoTerm g f).obstruction G (restrictExtClass g f G ζ)) :
    { δ : (pulledNaiveCotangentTwoTerm g f).conormal ⟶ G //
      ξ - restrictExtClass g f G ζ =
        (pulledNaiveCotangentTwoTerm g f).conormalExtClass G δ } :=
  ⟨((exists_conormalExtClass_sub_iff g f G ξ ζ).2 hobs).choose,
    ((exists_conormalExtClass_sub_iff g f G ξ ζ).2 hobs).choose_spec⟩

/-- **Stacks Project, Tag 0GQ1 with `δ`, `e` and `hcompat` all removed.** On the equality of the
restrictions of the two classes to the degree `0` term of `g^*𝖭𝖫_{X/S}`, the factorizations of
the difference homomorphism `conormalOfExtClassDifference` chooses are nonempty exactly when the
two classes agree. -/
theorem nonempty_factorization_conormalOfExtClassDifference_iff
    (ξ : pulledExtGroup g f G) (ζ : relativeExtGroup g f G)
    (hobs : (pulledNaiveCotangentTwoTerm g f).obstruction G ξ =
      (pulledNaiveCotangentTwoTerm g f).obstruction G (restrictExtClass g f G ζ)) :
    Nonempty { θ : (pulledNaiveCotangentTwoTerm g f).base ⟶ G //
        (pulledNaiveCotangentTwoTerm g f).d ≫ θ =
          (conormalOfExtClassDifference g f G ξ ζ hobs).1 } ↔
      ξ = restrictExtClass g f G ζ :=
  nonempty_factorization_iff_eq_restrictExtClass g f G _ ξ ζ
    (conormalOfExtClassDifference g f G ξ ζ hobs).2

end Derived

end AlgebraicGeometry.RingedSpaceThickening

end
