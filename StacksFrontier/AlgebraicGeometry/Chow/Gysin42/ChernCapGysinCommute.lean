module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinKeyFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge

/-!
# Stacks 0B72: the Gysin map commutes with the first Chern class cap product

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module with a global section `s` and zero
scheme `i : D = Z(s) ⟶ X`, and let `𝒩` be a second invertible `𝒪_X`-module. **Stacks 0B72** is
the identity

  `i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α`  in  `A_k(D)`,  for `α ∈ A_{k+2}(X)`.

## Main results

* `Stacks.Chow.gysinChowOfInvertible_firstChernClassCapChow` — **Stacks 0B72, with no
  hypothesis**, for the Gysin map of Stacks 02TO and the cap product of Stacks 02TI.

## Implementation notes

### Why no component-level input is needed

A component-level route would need `Stacks.Chow.GysinChernCapRationallyEquivalentOnComponents`,
Stacks 02TM read on the integral closed subschemes of `X`. That hypothesis has no producer:
Stacks 02TM is proved for an *integral ambient* scheme, as
`Stacks.Chow.gysinHomomorphismOfInvertible_eq_firstChernClassCapOfInvertible`, and restricting it
to the components of a general `X` needs a transport across the two presentations of `D ∩ W`
that this repository does not have, as well as a separate argument in the contained branch
`W ⊆ D`, where `s|_W = 0` and Stacks 02TM does not apply at all.

The proof below avoids the component level entirely. The cap product with `c₁(𝒩)` is itself a
Gysin map — the Gysin map of the **zero** section of `𝒩`, whose zero scheme `Q = Z(0)` is all of
`X` — so the identity is an instance of **Stacks 0B73**, the commutation of two Gysin maps, which
is proved here with no hypothesis as `Stacks.Chow.gysinChowOfInvertible_comm`. What turns each
Gysin map of the zero section back into a cap product is **Stacks 02T9**, and what moves the
Gysin map of `(ℒ, s)` across `Q ⟶ X` is **Stacks 02TA**; both are proved with no hypothesis, as
`Stacks.Chow.properChowPushforward_gysinHomomorphismOfInvertible` and
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible`. The two
presentations of `D ∩ Q` are identified by Stacks 0B6Y in the shape
`Stacks.Chow.exists_iso_zeroSchemeInter`, and that identification composed with the morphism of
Remark 0B6Y is the closed immersion of `D ∩ Q` into `D`, by the monicity of a closed immersion.

### The two Chow-level restatements

Stacks 02T9 and Stacks 02TA are stated for a cycle representative. Both descend to Chow classes
by `QuotientAddGroup.induction_on`, since the Gysin map of Stacks 02TO and the cap product of
Stacks 02TI are *defined* to agree with them on representatives
(`Stacks.Chow.gysinChowOfInvertible_mk`, `Stacks.Chow.firstChernClassCapChow_mk`); those are
`Stacks.Chow.properChowPushforward_gysinChowOfInvertible` and
`Stacks.Chow.gysinChowOfInvertible_properChowPushforward` below.

## References

* [Stacks Project, Tag 0B72](https://stacks.math.columbia.edu/tag/0B72)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Stacks 02T9 and Stacks 02TA on Chow groups -/

/-- **Stacks 02T9 on Chow groups.** Pushing the Gysin class of the zero scheme `i : Z(t) ⟶ Y`
forward to `Y` is capping with the first Chern class of the module: `i_* i^* α = c₁(ℳ) ∩ α` in
`A_k(Y)` for every Chow class `α ∈ A_{k+1}(Y)`.

This is `Stacks.Chow.properChowPushforward_gysinHomomorphismOfInvertible` read on Chow classes;
both operations are defined to agree with their cycle-level counterparts on representatives. -/
theorem properChowPushforward_gysinChowOfInvertible (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ) (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) (α : chowGroup C q (k + 1)) :
    properChowPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme Y M t).subschemeι C
          ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q rfl k)
        (gysinChowOfInvertible C q k M t α) =
      firstChernClassCapChow C k q M α := by
  induction α using QuotientAddGroup.induction_on with
  | H β => exact properChowPushforward_gysinHomomorphismOfInvertible C q k M t β

/-- **Stacks 02TA on Chow groups.** The Gysin map of `(ℒ, s)` commutes with proper pushforward
across the square of Remark 0B6Y, read on Chow classes.

This is `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible` read on
Chow classes. -/
theorem gysinChowOfInvertible_properChowPushforward (C : ChowSituation.{u})
    {X X' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (p' : X' ⟶ C.S)
    [LocallyOfFiniteType p'] (f : X' ⟶ X) [IsProper f] (hf : f ≫ p = p') (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (hfacf : ProperPushforwardFactorsThroughRationalEquivalence C p' p f hf (k + 1))
    (β : chowGroup C p' (k + 1)) :
    gysinChowOfInvertible C p k L s
        (properChowPushforward C p' p f hf (k + 1) hfacf β) =
      properChowPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p p' hf) k
        (properPushforwardFactorsThroughRationalEquivalence C
          ((pullbackZeroScheme f L s).subschemeι ≫ p')
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
          (zeroSchemePullbackHom_comp f L s C p p' hf) k)
        (gysinChowOfInvertible C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) β) := by
  induction β using QuotientAddGroup.induction_on with
  | H γ =>
    exact gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible f L s C p p' k hf γ

/-! ### Stacks 0B72 -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- The identification of the two presentations of `D ∩ Q` of Stacks 0B6Y, composed with the
morphism of Remark 0B6Y, is the closed immersion of `D ∩ Q` into `D`: both become
`(D ∩ Q) ⟶ D ⟶ X` after composing with the closed immersion `D ⟶ X`, which is a
monomorphism. -/
theorem iso_zeroSchemeInter_comp_zeroSchemePullbackHom
    (e : (zeroSchemeInter L N s (0 : Γ(N, ⊤))).subscheme ≅
      (zeroSchemeInter N L (0 : Γ(N, ⊤)) s).subscheme)
    (he : e.hom ≫ (zeroSchemeInter N L (0 : Γ(N, ⊤)) s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X N (0 : Γ(N, ⊤))).subschemeι =
      (zeroSchemeInter L N s (0 : Γ(N, ⊤))).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι) :
    e.hom ≫ zeroSchemePullbackHom
        (Stacks.Divisors.zeroScheme X N (0 : Γ(N, ⊤))).subschemeι L s =
      (zeroSchemeInter L N s (0 : Γ(N, ⊤))).subschemeι := by
  refine (cancel_mono (Stacks.Divisors.zeroScheme X L s).subschemeι).1 ?_
  rw [Category.assoc, zeroSchemePullbackHom_subschemeι]
  exact he

/-- **Stacks 0B72, with no hypothesis.** For an invertible module `ℒ` with a global section `s`
whose zero scheme is `i : D = Z(s) ⟶ X`, and a second invertible module `𝒩` on `X`, Gysin
pullback along `i` commutes with capping with the first Chern class of `𝒩`:

  `i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α`  in  `A_k(D)`,  for  `α ∈ A_{k+2}(X)`.

The Gysin map is the one of Stacks 02TO and the cap product the one of Stacks 02TI, both
constructed in this repository with no hypothesis. Nothing is assumed: the cap product with
`c₁(𝒩)` is itself the Gysin map of the zero section of `𝒩`, so the identity is Stacks 0B73 for
the pairs `(ℒ, s)` and `(𝒩, 0)`, read through Stacks 02T9 on `X` and on `D` and Stacks 02TA
across `Z(0) ⟶ X`. See the implementation notes. -/
@[stacks 0B72 "the identity i^*(c_1(N) cap alpha) = c_1(i^* N) cap i^* alpha in A_k(D), for the \
Gysin map of Stacks 02TO and the cap product of Stacks 02TI, with no hypothesis"]
theorem gysinChowOfInvertible_firstChernClassCapChow (α : chowGroup C p (k + 1 + 1)) :
    gysinChowOfInvertible C p k L s (firstChernClassCapChow C (k + 1) p N α) =
      firstChernClassCapChow C k ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        (zeroSchemeRestrictModule L N s) (gysinChowOfInvertible C p (k + 1) L s α) := by
  classical
  obtain ⟨e, he⟩ := exists_iso_zeroSchemeInter L N s (0 : Γ(N, ⊤))
  have hcomp := iso_zeroSchemeInter_comp_zeroSchemePullbackHom L s N e he
  -- Stacks 02T9 on `X` for the zero section of `𝒩`: the cap product is a pushed-forward Gysin map
  have hN := properChowPushforward_gysinChowOfInvertible C p (k + 1) N (0 : Γ(N, ⊤)) α
  -- Stacks 02TA across `Q = Z(0) ⟶ X`
  have hTA := gysinChowOfInvertible_properChowPushforward C p
    ((Stacks.Divisors.zeroScheme X N (0 : Γ(N, ⊤))).subschemeι ≫ p)
    (Stacks.Divisors.zeroScheme X N (0 : Γ(N, ⊤))).subschemeι rfl k L s
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
      (Stacks.Divisors.zeroScheme X N (0 : Γ(N, ⊤))).subschemeι C
      ((Stacks.Divisors.zeroScheme X N (0 : Γ(N, ⊤))).subschemeι ≫ p) p rfl (k + 1))
    (gysinChowOfInvertible C p (k + 1) N (0 : Γ(N, ⊤)) α)
  -- Stacks 0B73 for the pairs `(ℒ, s)` and `(𝒩, 0)`
  have hcomm := gysinChowOfInvertible_comm C p k L N s (0 : Γ(N, ⊤)) e he α
  -- Stacks 02T9 on `D` for the zero section of `𝒩|_D`
  have hT9D := properChowPushforward_gysinChowOfInvertible C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k (zeroSchemeRestrictModule L N s)
    (restrictSectionToZeroScheme L N s (0 : Γ(N, ⊤)))
    (gysinChowOfInvertible C p (k + 1) L s α)
  rw [← hN, hTA, ← hcomm, ← hT9D]
  -- the identification of the two presentations of `D ∩ Q`, followed by the morphism of Remark
  -- 0B6Y, is the closed immersion of `D ∩ Q` into `D`
  exact (properChowPushforward_comp_apply C _ _ _ e.hom
    (zeroSchemePullbackHom (Stacks.Divisors.zeroScheme X N (0 : Γ(N, ⊤))).subschemeι L s)
    (zeroSchemeInter L N s (0 : Γ(N, ⊤))).subschemeι hcomp _ _ _ k _ _ _ _).symm

end Stacks.Chow

end
