module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward
import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Reduction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.RationalEquivalenceUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization

/-!
# Stacks 02TA at the Gysin map of an invertible module, over the square of Remark 0B6Y

`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward` proves Stacks 02TA — the
compatibility `i^* f_* α' = g_* (i')^* α'` of Gysin pullback with proper pushforward — with five
inputs carried as parameters: the two first-Chern component rules `chern` and `chern'` of the
Gysin maps on `X` and on `X'`, the morphism `g : Z(f^*s) ⟶ Z(s)` of Remark 0B6Y together with its
properness and the commutativity of the square over the base, the vanishing of Stacks 02S2 along
`g`, and the compatibility of the two rules on integral components.

This file removes all five. The morphism `g` is *constructed* here, and with it the properness and
the commutativity; and the component rules are supplied by the first Chern class of an invertible
module, so that both Gysin maps become `Stacks.Chow.gysinHomomorphismOfInvertible`, the declaration
carrying the Stacks 02T8 attribute and a function of `L` and `s` alone. The vanishing of
Stacks 02S2 along `g` is discharged by
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence`, and the compatibility of the two
component rules is discharged by comparing the two sides at the level of classes, which is
`Stacks.Chow.rationallyEquivalent_gysinRule_extendCycleGroup_properPushforward` of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardAssembly`. So Stacks 02TA holds here
under no hypothesis beyond the properness of `f` and the commutativity of `f` over the base.

## Main definitions

* `Stacks.Chow.zeroSchemePullbackHom` — the morphism `g : Z(f^*s) ⟶ Z(s)` of Remark 0B6Y.

## Main results

* `Stacks.Chow.zeroSchemePullbackHom_subschemeι` — `g` sits in the square of Remark 0B6Y:
  `g ≫ i = i' ≫ f`.
* `Stacks.Chow.eq_zeroSchemePullbackHom` — it is the *only* morphism that does, so no choice is
  made: any construction of the Remark 0B6Y morphism agrees with this one.
* `Stacks.Chow.isProper_zeroSchemePullbackHom` — `g` is proper when `f` is.
* `Stacks.Chow.zeroSchemePullbackHom_comp` — the square commutes over the base scheme.
* `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_zeroSchemePullbackHom` — along
  `g`, only the one-subscheme case of Stacks 02S2 is needed.
* `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward` — Stacks 02TA for the Gysin
  map of an invertible module, over the constructed square, with the vanishing of Stacks 02S2 and
  the integral-component compatibility as parameters. This is the form the bivariant presentation
  of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SpecializationProperPushforward` consumes.
* `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible` —
  **Stacks 02TA**, with both of those discharged.

## Implementation notes

### The morphism of Remark 0B6Y is a factorization, and is unique

Remark 0B6Y produces `g` from the identification `Z(f^*s) = f^{-1}(Z(s))` of
`Stacks.Divisors.zeroScheme_pullback` followed by the second projection of the resulting
cartesian square; that is `Stacks.Divisors.zeroSchemePullbackMap`. Here `g` is obtained instead as
the factorization of `i' ≫ f` through the zero scheme `Z(s)`, which exists because the pullback of
`s` to `Z(f^*s)` vanishes — Stacks 02OR (2), in the form
`Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme`. Since
`i : Z(s) ⟶ X` is a closed immersion, hence a monomorphism, the factorization is unique, and
`Stacks.Chow.eq_zeroSchemePullbackHom` records that: the two constructions agree. The advantage of
the factorization is that it lands on `Z(f^*s)` itself rather than on `f^{-1}(Z(s))`, so no
transport along the equality of the two presentations of the pulled-back zero scheme is needed
anywhere below.

Properness of `g` is then `AlgebraicGeometry.IsProper.of_comp` applied to `g ≫ i = i' ≫ f`: the
right side is proper because `i'` is a closed immersion and `f` is proper, and `i` is separated
because it too is a closed immersion.

The support files leading up to Stacks 02TA — `...Gysin42.ProperPushforwardContained`,
`...Gysin42.ProperPushforwardDimensionDrop`, `...Gysin42.ProperPushforwardUncontained` and
`...Gysin42.ProperPushforwardAssembly` — are stated for `Stacks.Divisors.zeroSchemePullbackMap`,
which lives upstream of all of them, so that they can be imported here rather than having to
import this module for `g`. Uniqueness carries their conclusions over to `g`, through
`Stacks.Chow.properPushforward_hom_congr` of
`StacksFrontier.AlgebraicGeometry.Chow.Vocabulary`.

### Stacks 02S2 along `g` is discharged

The vanishing of Stacks 02S2 along `g`, needed to have the map
`g_* : A_k(Z(f^*s)) ⟶ A_k(Z(s))` of Stacks 0GU8 at all, is
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence`, which proves it for an arbitrary
proper morphism over the base with no hypothesis.
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible` substitutes it,
so nothing there needs `hfac` supplied.

### Why the integral-component compatibility is not used

`Stacks.Chow.GysinCompatibleWithPushforward`, the integral-component compatibility and the last
hypothesis of `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward`, asserts the identity
of Stacks 02TA on the fundamental cycle of each integral component of `X'` at the level of cycle
**coefficients**, whereas on a component `W' ⊆ Z(f^*s)` contained in the zero scheme the source
concludes only `f_*(c₁(L'|_{W'}) ∩ [W']) = c₁(L|_W) ∩ [W]` in `A_k(W)` — an identity of
**classes**. The difference is not slack in the bookkeeping: in the contained case
`Stacks.Chow.gysinComponentCycle` is the pushforward of `Quotient.out (chern W hW hDim)`, an
unconstrained representative of the class, so nothing relates the two cycles coefficientwise and
`Stacks.Chow.GysinCompatibleWithPushforward` is independent of the axioms.

So Stacks 02TA is proved at the level of classes, which is the level at which the tag asserts it:
the two cycles are compared over the integral components of `α'` and the per-component rational
equivalences are summed by Stacks 02RZ. That is the content of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardAssembly`, and it uses neither
`Stacks.Chow.GysinCompatibleWithPushforward` nor the coefficientwise
`Stacks.Chow.properPushforward_gysinRule_extendCycleGroup`.

`Stacks.Chow.GysinCompatibleWithPushforward` itself is kept: it is the hypothesis of
`Stacks.Chow.gysinHomomorphism_properPushforward`, which quantifies over arbitrary component
rules, where it cannot be dropped.

## References

* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The morphism of Remark 0B6Y -/

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- The pullback of `s` to the zero scheme of `f^*s`, taken along `i' ≫ f`, vanishes: it is the
pullback along `i'` of `f^*s`, which vanishes on the zero scheme of `f^*s` by Stacks 02OR (2). -/
theorem pullbackGlobalSections_subschemeι_comp_eq_zero :
    AlgebraicGeometry.pullbackGlobalSections
      ((pullbackZeroScheme f L s).subschemeι ≫ f) L s = 0 := by
  rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp
      (pullbackZeroScheme f L s).subschemeι f L s,
    (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X'
      ((Scheme.Modules.pullback f).obj L) (AlgebraicGeometry.pullbackGlobalSections f L s)
      (pullbackZeroScheme f L s).subschemeι).2 ⟨𝟙 _, by simp⟩,
    map_zero]

/-- **The morphism `g : Z(f^*s) ⟶ Z(s)` of Remark 0B6Y.** It is the factorization of `i' ≫ f`
through the zero scheme of `s`, which exists because the pullback of `s` along `i' ≫ f` vanishes.
By `Stacks.Chow.eq_zeroSchemePullbackHom` it is the unique morphism filling the square of Remark
0B6Y, so this agrees with the morphism that remark constructs out of the cartesian square. -/
def zeroSchemePullbackHom :
    (pullbackZeroScheme f L s).subscheme ⟶ (zeroScheme X L s).subscheme :=
  Classical.choose ((pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s
    ((pullbackZeroScheme f L s).subschemeι ≫ f)).1
      (pullbackGlobalSections_subschemeι_comp_eq_zero f L s))

/-- **The square of Remark 0B6Y commutes:** `g ≫ i = i' ≫ f`. -/
@[simp]
theorem zeroSchemePullbackHom_subschemeι :
    zeroSchemePullbackHom f L s ≫ (zeroScheme X L s).subschemeι =
      (pullbackZeroScheme f L s).subschemeι ≫ f :=
  Classical.choose_spec (p := fun g => g ≫ _ = _) _

/-- **The morphism of Remark 0B6Y is unique.** Any morphism `Z(f^*s) ⟶ Z(s)` filling the square
is `Stacks.Chow.zeroSchemePullbackHom`, because the closed immersion `i` is a monomorphism. So
nothing below depends on the choice made in that definition. -/
theorem eq_zeroSchemePullbackHom
    (g : (pullbackZeroScheme f L s).subscheme ⟶ (zeroScheme X L s).subscheme)
    (hg : g ≫ (zeroScheme X L s).subschemeι = (pullbackZeroScheme f L s).subschemeι ≫ f) :
    g = zeroSchemePullbackHom f L s :=
  (cancel_mono (zeroScheme X L s).subschemeι).1
    (hg.trans (zeroSchemePullbackHom_subschemeι f L s).symm)

/-- The morphism of Remark 0B6Y is proper when `f` is: `g ≫ i` is `i' ≫ f`, which is proper
because `i'` is a closed immersion, and `i` is separated. -/
instance isProper_zeroSchemePullbackHom [IsProper f] :
    IsProper (zeroSchemePullbackHom f L s) := by
  have h : IsProper (zeroSchemePullbackHom f L s ≫ (zeroScheme X L s).subschemeι) := by
    rw [zeroSchemePullbackHom_subschemeι]
    infer_instance
  exact IsProper.of_comp _ (zeroScheme X L s).subschemeι

/-! ### Stacks 02TA at the Gysin map of an invertible module -/

section Proper

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p] (p' : X' ⟶ C.S)
  [LocallyOfFiniteType p'] (k : ℤ)

omit [LocallyOfFiniteType p] [LocallyOfFiniteType p'] in
/-- The square of Remark 0B6Y commutes over the base scheme of the Chow situation. -/
theorem zeroSchemePullbackHom_comp (hf : f ≫ p = p') :
    zeroSchemePullbackHom f L s ≫ ((zeroScheme X L s).subschemeι ≫ p) =
      (pullbackZeroScheme f L s).subschemeι ≫ p' := by
  rw [← Category.assoc, zeroSchemePullbackHom_subschemeι, Category.assoc, hf]

/-- **Only the one-subscheme case of Stacks 02S2 is needed along `g`.** The hypothesis `hfac` of
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward` follows from the vanishing or
principality of the pushforward along `g` of the principal divisor of a single rational function
on a single integral closed subscheme, by
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor`.

That one-subscheme case is exactly what
`Stacks.Chow.properPushforwardKillsPrincipalDivisor_of_isProper` proves for an arbitrary proper
morphism with no hypothesis at all; it is unavailable here only because its module and this one
are mutually unimportable, as described in the implementation notes. -/
theorem properPushforwardFactorsThroughRationalEquivalence_zeroSchemePullbackHom [IsProper f]
    (hf : f ≫ p = p')
    (hkill : ProperPushforwardKillsPrincipalDivisor C
      ((pullbackZeroScheme f L s).subschemeι ≫ p') ((zeroScheme X L s).subschemeι ≫ p)
      (zeroSchemePullbackHom f L s) k) :
    ProperPushforwardFactorsThroughRationalEquivalence C
      ((pullbackZeroScheme f L s).subschemeι ≫ p') ((zeroScheme X L s).subschemeι ≫ p)
      (zeroSchemePullbackHom f L s) (zeroSchemePullbackHom_comp f L s C p p' hf) k :=
  properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor C
    ((pullbackZeroScheme f L s).subschemeι ≫ p') ((zeroScheme X L s).subschemeι ≫ p)
    (zeroSchemePullbackHom f L s) (zeroSchemePullbackHom_comp f L s C p p' hf) k hkill

/-- **Stacks 02TA for the Gysin map of an invertible module.** Gysin pullback through the zero
scheme of a global section of an invertible module commutes with proper pushforward across the
square of Remark 0B6Y: `i^* f_* α' = g_* (i')^* α'` in `A_k(Z(s))` for every
`α' ∈ Z_{k+1}(X')`.

Both Gysin maps are `Stacks.Chow.gysinHomomorphismOfInvertible`, functions of the invertible
module and the section alone, and the square is the constructed one. The two remaining
hypotheses are the vanishing of Stacks 02S2 along `g` and the compatibility of the first Chern
component rules on integral components; both are discharged in
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible`, so this form is
kept only for the consumers that already hold those two data, such as the presentation of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SpecializationProperPushforward`. -/
theorem gysinHomomorphismOfInvertible_properPushforward [IsProper f] (hf : f ≫ p = p')
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      ((pullbackZeroScheme f L s).subschemeι ≫ p') ((zeroScheme X L s).subschemeι ≫ p)
      (zeroSchemePullbackHom f L s) (zeroSchemePullbackHom_comp f L s C p p' hf) k)
    (hcomp : GysinCompatibleWithPushforward C p k L s (firstChernComponentClass C p k L) p' f
      (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L))
      (zeroSchemePullbackHom f L s) (zeroSchemePullbackHom_comp f L s C p p' hf))
    (α : CycleGroup C p' (k + 1)) :
    gysinHomomorphismOfInvertible C p k L s (properPushforward C p' p f hf (k + 1) α) =
      properChowPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p p' hf) k hfac
        (gysinHomomorphismOfInvertible C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) α) :=
  gysinHomomorphism_properPushforward C p k L s (firstChernComponentClass C p k L) p' f hf
    (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L))
    (zeroSchemePullbackHom f L s) (zeroSchemePullbackHom_comp f L s C p p' hf) hfac hcomp α

/-- **Stacks 02TA.** Gysin pullback through the zero scheme of a global section of an invertible
module commutes with proper pushforward across the square of Remark 0B6Y:

  `i^* f_* α' = g_* (i')^* α'`  in  `A_k(Z(s))`,  for every `α' ∈ Z_{k+1}(X')`.

Both Gysin maps are `Stacks.Chow.gysinHomomorphismOfInvertible`, functions of the invertible
module and the section alone; the morphism `g` of Remark 0B6Y is
`Stacks.Chow.zeroSchemePullbackHom`; and the instance of Stacks 02S2 that
`Stacks.Chow.properChowPushforward` requires along `g` is supplied by
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence`. Nothing is assumed beyond the
properness of `f` and the commutativity of `f` over the base.

Both sides are classes of cycles on `Z(s)`, and the two cycles are rationally equivalent by
`Stacks.Chow.rationallyEquivalent_gysinRule_extendCycleGroup_properPushforward`. -/
@[stacks 02TA "the identity i^* f_* α' = g_* (i')^* α' in A_k(Z(s)) over the square of Remark \
0B6Y, for the Gysin map of an invertible module and a global section, with no hypothesis beyond \
properness of f and the commutativity of f over the base"]
theorem gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible [IsProper f]
    (hf : f ≫ p = p') (α : CycleGroup C p' (k + 1)) :
    gysinHomomorphismOfInvertible C p k L s (properPushforward C p' p f hf (k + 1) α) =
      properChowPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p p' hf) k
        (properPushforwardFactorsThroughRationalEquivalence C
          ((pullbackZeroScheme f L s).subschemeι ≫ p')
          ((zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
          (zeroSchemePullbackHom_comp f L s C p p' hf) k)
        (gysinHomomorphismOfInvertible C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) α) := by
  change QuotientAddGroup.mk
      ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
        (properPushforward C p' p f hf (k + 1) α)) =
    QuotientAddGroup.mk (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
      ((zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
      (zeroSchemePullbackHom_comp f L s C p p' hf) k
      ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)
        (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L))).extendCycleGroup α))
  rw [properPushforward_hom_congr C ((pullbackZeroScheme f L s).subschemeι ≫ p')
    ((zeroScheme X L s).subschemeι ≫ p)
    (eq_zeroSchemePullbackHom f L s _ (zeroSchemePullbackMap_comp_subschemeι f L s)).symm
    (zeroSchemePullbackHom_comp f L s C p p' hf)
    (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k]
  exact QuotientAddGroup.eq_iff_sub_mem.2
    (rationallyEquivalent_gysinRule_extendCycleGroup_properPushforward C p p' f hf L s k α)

end Proper

end Stacks.Chow

end
