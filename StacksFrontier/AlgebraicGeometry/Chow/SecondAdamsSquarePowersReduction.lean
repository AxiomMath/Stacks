module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsSquaresFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.LambdaOperations
public import StacksCore.Tactic.StacksAttribute

/-!
# Reducing the geometric input of the second Adams operator

`AlgebraicGeometry.VectorBundleKZero.SquarePowersData` is the six-field predicate that the
conditional statement of [Stacks, Tag 0FEJ]
(`AlgebraicGeometry.VectorBundleKZero.exists_secondAdamsOperator`) carries as a hypothesis: it
asks that `Sym²` and `⋀²` preserve finite local freeness, that each of the two squares is
additive along a short exact sequence in the three-step way the source describes, and that each
of the two squares of a tensor product decomposes in the way the source's two short exact
sequences give.

**Four of those six fields are not independent.** This file proves it, by exhibiting
`SquarePowersData` as a consequence of the three-field predicate `SquarePowersCore`:

* the two finite-local-freeness fields are *theorems*, not hypotheses — the exterior one is
  `AlgebraicGeometry.VectorBundleKZero.isFiniteLocallyFree_secondExteriorPower` and the symmetric
  one is `AlgebraicGeometry.VectorBundleKZero.isFiniteLocallyFree_secondSymmetricPower`, of
  `StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsSquaresFiniteLocallyFree`;
* the two *symmetric* relations follow from their exterior counterparts, given only the
  elementary relation `[ℰ ⊗ ℰ] = [Sym² ℰ] + [⋀² ℰ]`.

The last reduction is the point, and it is pure Grothendieck-ring algebra. Write `a = [ℰ]`,
`c = [𝒢]`, `A(ℰ) = [⋀² ℰ]`. The relation `[ℰ ⊗ ℰ] = [Sym² ℰ] + [⋀² ℰ]` — the class identity of
the short exact sequence `0 → ⋀² ℰ → ℰ ⊗ ℰ → Sym² ℰ → 0` — says, since multiplication in
`K₀(Vect(X))` is tensor product, that

`[Sym² ℰ] = a² - A(ℰ)`.

So every symmetric class is an exterior class subtracted from a square, and the two symmetric
relations become the two exterior ones. For a short exact sequence `0 → ℰ → ℱ → 𝒢 → 0` the class
`[ℱ]` is `a + c`, so

`[Sym² ℱ] = (a + c)² - A(ℱ) = (a + c)² - A(ℰ) - ac - A(𝒢) = [Sym² ℰ] + [ℰ ⊗ 𝒢] + [Sym² 𝒢]`,

using the exterior filtration relation in the middle; and for a tensor product

`[Sym²(ℰ ⊗ ℱ)] = a²b² - A(ℰ ⊗ ℱ) = a²b² - [Sym² ℰ][⋀² ℱ] - [⋀² ℰ][Sym² ℱ]
               = [⋀² ℰ][⋀² ℱ] + [Sym² ℰ][Sym² ℱ]`,

using the exterior tensor relation. The same computation run backwards derives the exterior
relations from the symmetric ones, so the two pairs are equivalent and the choice of which to
carry is free; the exterior ones are carried because the exterior filtration is the one the
sibling predicate `Stacks.SheafOfModules.ExteriorPowersData` of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.LambdaOperations` already isolates, in all degrees,
for the lambda operations.

## Status of the three fields

The three fields of `SquarePowersCore` were open when this reduction was written; the library
now proves `SquarePowersData` outright, for every scheme
(`AlgebraicGeometry.VectorBundleKZero.squarePowersData`, by way of
`AlgebraicGeometry.VectorBundleKZero.SquarePowersData.of_classOf_sym_tensor`), and Tag 0FEJ
is `AlgebraicGeometry.VectorBundleKZero.exists_secondAdamsOperator_pullbackRingHom`. This file
claims no tag; it records that four of the six fields of `SquarePowersData` are redundant.

## Main definitions

* `AlgebraicGeometry.VectorBundleKZero.SquarePowersCore`: the three independent facts.

## Main results

* `AlgebraicGeometry.VectorBundleKZero.SquarePowersCore.classOf_secondSymmetricPower`: every
  symmetric class is a square minus an exterior class.
* `AlgebraicGeometry.VectorBundleKZero.SquarePowersCore.toSquarePowersData`: **the reduction**.

## References

* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.FiniteLocallyFree

universe u

namespace AlgebraicGeometry.VectorBundleKZero

/-! ### The three independent facts -/

/-- **The irredundant part of the geometric input of Tag 0FEJ.**

Three facts about the second symmetric and exterior powers of a sheaf of modules on a scheme,
read as identities of classes in `K₀(Vect(X))`:

* `classOf_tensorSelf`: the class identity of `0 → ⋀² ℰ → ℰ ⊗ ℰ → Sym² ℰ → 0`;
* `classOf_alt_shortExact`: the three-step filtration of `⋀²` along a short exact sequence;
* `classOf_alt_tensor`: the decomposition of `⋀²` of a tensor product.

`AlgebraicGeometry.VectorBundleKZero.SquarePowersCore.toSquarePowersData` shows these three
imply all six fields of `SquarePowersData`. The two symmetric relations of that predicate are
redundant given the exterior ones, and the two finite-local-freeness fields are theorems. -/
structure SquarePowersCore (X : Scheme.{u}) : Prop where
  /-- The class identity of the short exact sequence `0 → ⋀² ℰ → ℰ ⊗ ℰ → Sym² ℰ → 0`. -/
  classOf_tensorSelf : ∀ E : X.Modules,
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      classOf X (Scheme.Modules.tensorObjRingedSpace X E E) =
        classOf X (secondSymmetricPower X E) + classOf X (secondExteriorPower X E)
  /-- The filtration of `⋀²` along a short exact sequence of finite locally free modules. -/
  classOf_alt_shortExact : ∀ {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G →
          Mono f → Epi g → (ShortComplex.mk f g w).Exact →
            classOf X (secondExteriorPower X F) =
              classOf X (secondExteriorPower X E) +
                classOf X (Scheme.Modules.tensorObjRingedSpace X E G) +
                  classOf X (secondExteriorPower X G)
  /-- The short exact sequence `0 → Sym²ℰ ⊗ ⋀²ℱ → ⋀²(ℰ ⊗ ℱ) → ⋀²ℰ ⊗ Sym²ℱ → 0`. -/
  classOf_alt_tensor : ∀ E F : X.Modules,
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        classOf X (secondExteriorPower X (Scheme.Modules.tensorObjRingedSpace X E F)) =
          classOf X (Scheme.Modules.tensorObjRingedSpace X
              (secondSymmetricPower X E) (secondExteriorPower X F)) +
            classOf X (Scheme.Modules.tensorObjRingedSpace X
              (secondExteriorPower X E) (secondSymmetricPower X F))

namespace SquarePowersCore

variable {X : Scheme.{u}}

/-- **Every symmetric class is a square minus an exterior class.**

Multiplication in `K₀(Vect(X))` is tensor product, so the class identity of
`0 → ⋀² ℰ → ℰ ⊗ ℰ → Sym² ℰ → 0` reads `[ℰ]² = [Sym² ℰ] + [⋀² ℰ]`. This is that identity solved
for the symmetric class, and it is what makes the two symmetric fields of `SquarePowersData`
redundant. -/
theorem classOf_secondSymmetricPower (h : SquarePowersCore X) (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    classOf X (secondSymmetricPower X E) =
      classOf X E * classOf X E - classOf X (secondExteriorPower X E) := by
  have h1 := h.classOf_tensorSelf E hE
  rw [← classOf_mul E E hE hE] at h1
  exact eq_sub_of_add_eq h1.symm

/-- **The reduction**: the three facts of `SquarePowersCore` imply all six fields of
`AlgebraicGeometry.VectorBundleKZero.SquarePowersData`, hence everything the conditional
statement of [Stacks, Tag 0FEJ] consumes.

The two finite-local-freeness fields are discharged by
`isFiniteLocallyFree_secondSymmetricPower` and `isFiniteLocallyFree_secondExteriorPower`; the
two exterior relations are carried unchanged; and the two symmetric relations are derived from
them by `classOf_secondSymmetricPower`, which turns each symmetric class into a square minus an
exterior class, after which both identities are ring identities in `K₀(Vect(X))`. -/
theorem toSquarePowersData (h : SquarePowersCore X) : SquarePowersData X where
  isFiniteLocallyFree_sym E hE := isFiniteLocallyFree_secondSymmetricPower E hE
  isFiniteLocallyFree_alt E hE := isFiniteLocallyFree_secondExteriorPower E hE
  classOf_sym_shortExact {E F G} f g w hE hF hG hmono hepi hex := by
    have := hmono
    have := hepi
    have hb : classOf X F = classOf X E + classOf X G :=
      classOf_shortExact f g w hE hF hG hex
    rw [h.classOf_secondSymmetricPower F hF, h.classOf_secondSymmetricPower E hE,
      h.classOf_secondSymmetricPower G hG,
      h.classOf_alt_shortExact f g w hE hF hG hmono hepi hex,
      ← classOf_mul E G hE hG, hb]
    ring
  classOf_alt_shortExact {E F G} f g w hE hF hG hmono hepi hex :=
    h.classOf_alt_shortExact f g w hE hF hG hmono hepi hex
  classOf_sym_tensor E F hE hF := by
    have hEF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (Scheme.Modules.tensorObjRingedSpace X E F) :=
      @isFiniteLocallyFree_tensorObj X E F hE hF
    rw [h.classOf_secondSymmetricPower _ hEF, h.classOf_alt_tensor E F hE hF,
      ← classOf_mul E F hE hF,
      ← classOf_mul _ _ (isFiniteLocallyFree_secondExteriorPower E hE)
        (isFiniteLocallyFree_secondExteriorPower F hF),
      ← classOf_mul _ _ (isFiniteLocallyFree_secondSymmetricPower E hE)
        (isFiniteLocallyFree_secondSymmetricPower F hF),
      ← classOf_mul _ _ (isFiniteLocallyFree_secondSymmetricPower E hE)
        (isFiniteLocallyFree_secondExteriorPower F hF),
      ← classOf_mul _ _ (isFiniteLocallyFree_secondExteriorPower E hE)
        (isFiniteLocallyFree_secondSymmetricPower F hF),
      h.classOf_secondSymmetricPower E hE, h.classOf_secondSymmetricPower F hF]
    ring
  classOf_alt_tensor E F hE hF := h.classOf_alt_tensor E F hE hF

end SquarePowersCore

end AlgebraicGeometry.VectorBundleKZero

end
