module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackInvertible

/-!
# Stacks 0B71 with the Stacks 02S1 hypothesis discharged

`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback` and
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackInvertible` state Stacks 0B71 with the
vanishing of Stacks 02S1 along the comparison morphism `g : D' ⟶ D` of Remark 0B6Y carried as a
hypothesis `hfac`, because the map `g^* : CH_k(D) ⟶ CH_{k+r}(D')` of Stacks 0FVK cannot be written
down without it. That hypothesis is a theorem:
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` proves Stacks 02S1 for an
arbitrary flat morphism of relative dimension `r`. It lives downstream of those two files, so this
file substitutes it and restates the two identities without `hfac`.

## Main results

* `Stacks.Chow.gysinHomomorphism_flatPullback_of_gysinCompatible` — Stacks 0B71 on Chow groups
  with `hfac` discharged, the component rules and the integral-component compatibility still
  carried.
* `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_of_gysinCompatible` — the same at the
  Gysin map of an invertible module over the canonical square of Remark 0B6Y, so that the
  integral-component compatibility is the only remaining hypothesis.

## Implementation notes

The hypothesis occurs in the conclusion as well as among the premises: `hfac` is an argument of
`Stacks.Chow.flatPullbackChow`, which is the right hand side of both identities. So the statements
below are the originals with the proved term substituted for `hfac` in both places, and the proofs
are the originals applied to that term. Nothing else changes, in particular the integral-component
compatibility `Stacks.Chow.GysinCompatibleWithFlatPullback` — the case of the tag that the source
proves by Stacks 02RE and Stacks 02SS — is still a hypothesis, so no `@[stacks 0B71]` attribute is
placed here either.

## References

* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Stacks 0B71 over an arbitrary square -/

section General

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj X'.ringCatSheaf.property
    ((Scheme.Modules.pullback f).obj L)]
  (chern : FirstChernComponentClassRule C p k)
  (chern' : FirstChernComponentClassRule C (f ≫ p) (k + (r : ℤ)))
  (g : (pullbackZeroScheme f L s).subscheme ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme)
  [LocallyOfFiniteType g] [Flat g] (hg : AlgebraicGeometry.RelativeDimension g r)
  (hbase : g ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) =
    (pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))

/-- **Stacks 0B71.** Gysin pullback through the zero scheme of a section commutes with flat
pullback: `(i')^* f^* α = g^* i^* α` in `A_{k+r}(D')` for every `α ∈ Z_{k+1}(X)`.

This is `Stacks.Chow.gysinHomomorphism_flatPullback` with its Stacks 02S1 hypothesis along `g`
discharged by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, which is also
the proof that the map `g^*` of Stacks 0FVK on the right hand side exists. The component rules of
the two Gysin maps, the invertibility of `f^*L` (Stacks 0B8L) and the identity on integral
components remain parameters. -/
theorem gysinHomomorphism_flatPullback_of_gysinCompatible
    (hcomp : GysinCompatibleWithFlatPullback C p f r k L s chern chern' g hg hbase)
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : CycleGroup C p (k + 1)) :
    gysinHomomorphism C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s) chern'
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) =
      flatPullbackChow C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
        (flatPullbackFactorsThroughRationalEquivalence_general C
          ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k)
        (gysinHomomorphism C p k L s chern α) :=
  gysinHomomorphism_flatPullback C p f r hf k L s chern chern' g hg hbase
    (flatPullbackFactorsThroughRationalEquivalence_general C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k)
    hcomp hcast α

end General

/-! ### Stacks 0B71 over the canonical square of Remark 0B6Y -/

section Invertible

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)

/-- **Stacks 0B71 for an arbitrary cycle**, at the Gysin map of an invertible module and over the
canonical square of Remark 0B6Y:

  `(i')^* f^* α = g^* i^* α`  in  `CH_{k+r}(D')`,  for every `α ∈ Z_{k+1}(X)`.

This is `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback` with its Stacks 02S1 hypothesis
along `g` discharged by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`. The
identity of the tag on integral components is the only remaining hypothesis, and it is the tag's
own statement assumed on components, so **no `@[stacks 0B71]` attribute is placed here**. -/
theorem gysinHomomorphismOfInvertible_flatPullback_of_gysinCompatible
    (hcomp : GysinCompatibleWithFlatPullback C p f r k L s
      (firstChernComponentClass C p k L)
      (firstChernComponentClass C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L))
      (zeroSchemePullbackHom f L s) (relativeDimension_zeroSchemePullbackHom f L s r hf)
      (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl))
    (α : CycleGroup C p (k + 1)) :
    gysinHomomorphismOfInvertible C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L) (AlgebraicGeometry.pullbackGlobalSections f L s)
        ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
          flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) =
      flatPullbackChow C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
        (relativeDimension_zeroSchemePullbackHom f L s r hf) k
        (flatPullbackFactorsThroughRationalEquivalence_general C
          ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
          (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
          (relativeDimension_zeroSchemePullbackHom f L s r hf) k)
        (gysinHomomorphismOfInvertible C p k L s α) :=
  gysinHomomorphismOfInvertible_flatPullback f L s C p r hf k
    (flatPullbackFactorsThroughRationalEquivalence_general C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
      (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
      (relativeDimension_zeroSchemePullbackHom f L s r hf) k)
    hcomp α

end Invertible

end Stacks.Chow

end
