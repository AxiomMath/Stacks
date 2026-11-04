module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHomTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SheafHomBaseChangePseudoCoherentCounterexample

/-!
# Stacks 08JQ, decided: part (1), part (2) for `g` of finite Tor dimension, and the failure of
part (2) as printed

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces, `E ∈ D(𝒪_X)`
and `𝒢^•` a complex of quasi-coherent `𝒪_X`-modules, each `𝒢^n` flat over `Y`. Stacks 08JQ asserts
that for every cartesian square the base change map
`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` is an isomorphism if

1. `E` is perfect and `𝒢^•` is bounded above, or
2. `E` is pseudo-coherent and `𝒢^•` is bounded.

Part (1) holds as printed, and part (2) holds when `g` has finite Tor dimension: both are
`AlgebraicGeometry.Space.isIso_smallEtaleDerivedSheafHomBaseChangeMap_tag`. Part (2) as printed,
for an arbitrary base change `g`, is false:
`not_forall_isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPseudoCoherent`, in the namespace
`AlgebraicGeometry.Space.SheafHomBaseChangeCounterexample`, refutes it for `X = Y = Spec ℤ/4`,
`f = id`, `E = (ℤ/4 ⧸ 2)^~`, `𝒢^• = 𝒪_X` and `g = g' : Spec ℤ/2 ⟶ Spec ℤ/4`. As `ℤ/4` is
self-injective, the source of the map lies in `D^{≤ 0}`, while `L(g')^*E` has `𝒪_{X'}[1]` as a
direct summand, so the target has nonzero cohomology in degree `1`. The source's proof passes
through Stacks 0DKI (3), which needs `g` of finite Tor dimension; `Spec ℤ/2 ⟶ Spec ℤ/4` does not
have it.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedSheafHomBaseChangeMap_and_not_forall_isIso`:
  **Stacks 08JQ**, the three conjuncts above.

## References

* [Stacks Project, Tag 08JQ](https://stacks.math.columbia.edu/tag/08JQ)
* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces,
`E ∈ D(𝒪_X)` and `𝒢^•` a complex of quasi-coherent `𝒪_X`-modules, each `𝒢^n` flat over `Y`. For
every cartesian square, the base change map
`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` is an isomorphism if

1. `E` is perfect and `𝒢^•` is bounded above (the source's part (1), at its hypotheses), or
2. `E` is pseudo-coherent, `𝒢^•` is bounded, and `g` has finite Tor dimension.

Part (2) as printed, for an arbitrary base change `g`, is false, and the third conjunct proves
it: it fails for `X = Y = Spec ℤ/4`, `f = id`, `E = (ℤ/4 ⧸ 2)^~`, `𝒢^• = 𝒪_X` and
`g = g' : Spec ℤ/2 ⟶ Spec ℤ/4`, where the source of the map lies in `D^{≤ 0}` (`ℤ/4` is
self-injective) and the target has nonzero cohomology in degree `1`
(`not_forall_isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPseudoCoherent`, in the namespace
`AlgebraicGeometry.Space.SheafHomBaseChangeCounterexample`). The source proves (2) through
Stacks 0DKH and 0DKI (3); Stacks 0DKI (3) needs `g` of finite Tor dimension, and with that
condition the proof goes through
(`AlgebraicGeometry.Space.isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPseudoCoherent`). The
morphism `Spec ℤ/2 ⟶ Spec ℤ/4` of the counterexample does not have finite Tor dimension. -/
@[stacks 08JQ "erratum: as printed, part (2) (E pseudo-coherent, G bounded and flat over Y, an \
arbitrary base change g) is false, refuted for X = Y = Spec Z/4, f = id, E = (Z/4/2)~, G = O_X and \
g the closed point Spec Z/2 -> Spec Z/4 (third conjunct); it holds when g has finite Tor dimension \
(second conjunct); part (1) holds as printed (first conjunct)"]
theorem isIso_smallEtaleDerivedSheafHomBaseChangeMap_and_not_forall_isIso
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    (RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E →
      (∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) →
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedSheafHomBaseChangeMap f g f' g' sq.w E G)) ∧
    (RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) E →
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (G.X i)) →
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g), HasFiniteTorDimension g →
        IsIso (smallEtaleDerivedSheafHomBaseChangeMap f g f' g' sq.w E G)) ∧
    ¬ ∀ {B : BigFppfSite.{0}} {S : Scheme.{0}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
      (f : X ⟶ Y), IsQuasiCompact B S hS f.hom → IsQuasiSeparated B S hS f.hom →
      ∀ (E : DerivedCategory (SheafOfModules.{0} (ringedToposStructureRingSheaf B S hS X))),
        RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) E →
      ∀ (G : CochainComplex (SheafOfModules.{0} (ringedToposStructureRingSheaf B S hS X)) ℤ),
        (∀ n, (G.X n).IsQuasicoherentOnSite) → (∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) →
        (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (G.X i)) →
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedSheafHomBaseChangeMap f g f' g' sq.w E G) :=
  have h := isIso_smallEtaleDerivedSheafHomBaseChangeMap_tag f hfqc hfqs E G hq hfl
  ⟨h.1, h.2,
    open SheafHomBaseChangeCounterexample in
    not_forall_isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPseudoCoherent⟩

end AlgebraicGeometry.Space

end
