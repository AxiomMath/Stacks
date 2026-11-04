module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericSectionRatioUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallyFiniteSecondSetOfRegularSection

/-!
# `ord_{Z, ℒ}(s) = 0` where `s` generates `ℒ_ξ`, for the canonical ratio

Let `X` be a decent, locally Noetherian, integral algebraic space over `S`, let `Z ⊆ X` be a
prime divisor with generic point `ξ`, let `ℒ` be an invertible `𝒪_X`-module and let `s` be a
meromorphic section of `ℒ` whose germ at `ξ` is a *free generator* of `ℒ_ξ`.  Then
`ord_{Z, ℒ}(s) = 0`.

That is the hypothesis `hord` of
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero_of_isIntegral`, the second
set of Stacks 0EPS, and this file discharges it — not for the arbitrary `ratio` parameter of
`AlgebraicGeometry.Space.orderOfVanishingSection`, which nothing ties to `ℒ` or to `s`, but
for a `ratio` whose value at `s` is the *canonical* ratio of Stacks 0EPR constructed in
`AlgebraicGeometry.Space.PrimeDivisor.exists_ringEquiv_forall_smul_eq_genericMeromorphicGerm`.
Being canonical at `s` is all the second set uses, `ord_{Z, ℒ}(s)` reading `ratio` at `s`
alone.

## Main results

* `AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_generatesGenericModuleStalk`:
  the statement above.
* `AlgebraicGeometry.Space.exists_localRatioFamily_locallyFinite_divisorCoefficients_ne_zero`:
  **the second set of Stacks 0EPS with `hord` supplied rather than assumed.**  For a regular
  meromorphic section `s` of an invertible `ℒ` there is a family of local ratios whose value at
  `s` is, at every prime divisor, the ratio of `s` against a free generator of `ℒ_ξ` — the
  canonical ratio of Stacks 0EPR — whose order of vanishing vanishes wherever `s` generates
  `ℒ_ξ`, and for which the prime divisors with `ord_{Z, ℒ}(s) ≠ 0` are locally finite in `|X|`.
  No hypothesis beyond the source's is carried.

## Implementation notes

*The three statements the first result composes.*  The canonical ratio comes with the equation
`ψ⁻¹(f s) · t_ξ = germ_ξ(s)` characterising it against a free generator `t_ξ` of `ℒ_ξ`.  Where
the germ is itself the image of a free generator,
`AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_genericToMeromorphicFunctions_eq_of_generates`
turns that equation into `ψ⁻¹(f s) = v` for a *unit* `v` of the abstract henselization
`R : Type u` that the germ API carries, read in the meromorphic functions of
`Spec(𝒪^h_{X, ξ})`.  Transporting it to the fraction ring in which
`AlgebraicGeometry.Space.orderOfVanishingSection` reads the ratio is the compatibility square
that `exists_ringEquiv_forall_smul_eq_genericMeromorphicGerm` keeps beside `ψ`; and
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit` then gives `0`.  Nothing
here needs regularity of `s`: generating `ℒ_ξ` is strictly stronger than having a unit ratio.

*Why the second result carries the characterisation of the ratio in its conclusion.*  Without
it the statement would be worthless and not merely weak: `AlgebraicGeometry.Space.LocalRatio`
is a bare function type into a group of units, so `fun _ ↦ 1` is a family, its order of
vanishing is `0` at every prime divisor, and both the vanishing clause and the local finiteness
would hold of it vacuously.  The first clause of the conclusion is what rules that out — it
says that `ratio Z s` is the ratio of `s` against a *free generator* of `ℒ_ξ`, which is the
defining property of `s / s_ξ` in Stacks 0EPR — and it is the reason the result says anything
about `ℒ` and `s` at all.

*Why the second result is an existential, and what it is existential over.*  The source fixes
a generator `s_ξ` of `ℒ_ξ` at each prime divisor and reads `ord_{Z, ℒ}(s)` off it; Stacks 0EPR
makes the answer independent of that choice, which this library has only in the weaker form
`AlgebraicGeometry.Space.orderOfVanishingSection_unit_smul` — invariance under a unit of
`𝒪^h_{X, ξ}` — and not for the further choice of the isomorphism `ψ` across the universe gap
that step (iii) of the construction is existential in.  So the family of ratios is quantified
existentially, exactly over the choices the source also makes, and the conclusion holds for
each of them.

*The ratio away from `s`.*  `AlgebraicGeometry.Space.LocalRatio` is valued in the **units** of
`Q(𝒪^h_{X, ξ})`, and the canonical ratio is a unit precisely at the *regular* sections — the
germ of `0` is `0`, whose ratio against a generator is `0`.  So no family can be canonical at
every section while `LocalRatio` has that target, and the family produced here is canonical at
the given `s` and arbitrary elsewhere.  That is not a defect of the statement, whose content is
`AlgebraicGeometry.Space.divisorCoefficients … s ratio` and so reads `ratio W` at `s` only; it
is the reason the target of `LocalRatio` has to change before the ratio can be constrained in
the type rather than in a hypothesis, which the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection` record together with the
universe wall that blocks the rest of that repair.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))

section OneDivisor

variable (Z : PrimeDivisor B S hS X)

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]
  (hR : B.Contains (Spec (.of R)))

variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

include hX hdec hInt hN in
/-- **Where `s` generates `ℒ_ξ`, the order of vanishing of `s` along `Z` is zero.**  The ratio
is the canonical one of Stacks 0EPR: `ratio s` is the value at `s` of the map `f` that
`AlgebraicGeometry.Space.PrimeDivisor.exists_ringEquiv_forall_smul_eq_genericMeromorphicGerm`
produces against a free generator `t_ξ` of `ℒ_ξ`, with `ψ` and the compatibility square `hev`
the same statement supplies.

This is the hypothesis `hord` of
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero_of_isIntegral`, discharged
at one prime divisor.  Generating `ℒ_ξ` makes the ratio the image of a *unit of `𝒪^h_{X, ξ}`*
and not merely a unit of its fraction ring, and the order of vanishing of such a ratio is
zero. -/
theorem orderOfVanishingSection_eq_zero_of_generatesGenericModuleStalk
    (L : Modules.{u, u} B S hS X hX)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L)
    (t : Z.genericModuleStalk B S hS hX hdec R hR L)
    (ht : Function.Bijective fun r : R => r • t)
    (e : R ≃+* ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (ψ : meromorphicChartRing B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianChart B S hS hX hdec R hR) ≃+*
      Z.genericTotalFractionRing B S hS hX hdec)
    (hev : ∀ v : R, ψ (Z.genericToMeromorphicFunctions B S hS hX hdec R hR v) =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec) (e v))
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (ratio : LocalRatio.{u, u} B S hS hX hdec Z L)
    (hratio : ψ.symm (ratio s : Z.genericTotalFractionRing B S hS hX hdec) •
        toMeromorphicSectionValue B S hS
          (Z.genericHenselianSpace B S hS hX hdec R hR).obj
          (Z.genericHenselianSpace B S hS hX hdec R hR).property
          (Z.genericHenselianPullback B S hS hX hdec R hR L)
          (Z.genericHenselianChart B S hS hX hdec R hR) t =
      Z.genericMeromorphicGerm B S hS hX hdec R hR L s)
    (hgen : Z.GeneratesGenericModuleStalk B S hS hX hdec R hR L s) :
    orderOfVanishingSection.{u, u} B S hS hX hdec Z L s ratio = 0 := by
  obtain ⟨v, hv, hvk⟩ := Z.exists_isUnit_genericToMeromorphicFunctions_eq_of_generates
    B S hS hX hdec hInt hN R hR L hL t ht s hgen _ hratio
  refine orderOfVanishingSection_eq_zero_of_isUnit.{u, u} B S hS hX hdec Z L s ratio
    (v := e v) (hv.map e) ?_
  rw [← hev v, ← hvk, ψ.apply_symm_apply]

end OneDivisor

section Family

variable (RR : PrimeDivisor B S hS X → Type u) [∀ Z, CommRing (RR Z)] [∀ Z, IsLocalRing (RR Z)]
    [∀ Z : PrimeDivisor B S hS X,
      Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point) (RR Z)]
    [∀ Z : PrimeDivisor B S hS X, IsLocalRing.IsHenselization
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)
      (IsLocalRing.ResidueField
        ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
          (Z.genericChart B S hS hX hdec).point)) (RR Z)]
    (hRR : ∀ Z : PrimeDivisor B S hS X, B.Contains (Spec (.of (RR Z))))

variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

include hX hdec hInt hN in
/-- **Stacks 0EPS, the second set, with `hord` supplied rather than assumed.**  Let `S` be a
scheme, let `X` be a locally Noetherian integral algebraic space over `S`, let `ℒ` be an
invertible `𝒪_X`-module and let `s` be a regular meromorphic section of `ℒ`.  Then there is a
family of local ratios whose value at `s` is, at each prime divisor, the ratio of `s` against a
free generator `t_ξ` of `ℒ_ξ` — the canonical ratio `s / s_ξ` of Stacks 0EPR, which is the first
clause of the conclusion — for which `ord_{Z, ℒ}(s) = 0` at every prime divisor where `s`
generates `ℒ_ξ`, and for which the prime divisors with `ord_{Z, ℒ}(s) ≠ 0` are locally finite
in `|X|`.

This carries no hypothesis beyond the source's.  It is
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero_of_isIntegral`, whose single
proviso `hord` is here a conclusion rather than an assumption, and it is existential over the
choices the source also makes.  The first clause is load-bearing: without it `fun _ ↦ 1` would
satisfy the other two vacuously.  See the implementation notes of this module for what the
existential quantifier ranges over and why the family is canonical at `s` and not at every
section. -/
@[stacks 0EPS "the second set: the prime divisors with ord_{Z,ℒ}(s) ≠ 0 are locally finite, at
  the hypotheses of the source alone -- the proviso `hord` of
  locallyFinite_divisorCoefficients_ne_zero_of_isIntegral is supplied here, by the canonical
  ratio of Stacks 0EPR, rather than assumed; the family of ratios is quantified existentially,
  over the choice of a free generator of ℒ_ξ at each prime divisor and of the isomorphism
  across the universe gap that step (iii) of that construction is existential in, and its value
  at s is pinned to the ratio of s against that generator by the first clause of the conclusion"]
theorem exists_localRatioFamily_locallyFinite_divisorCoefficients_ne_zero
    (L : Modules.{u, u} B S hS X hX)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hreg : IsRegularMeromorphicSection.{u, u} B S hS X hX L s) :
    ∃ ratio : LocalRatioFamily.{u, u} B S hS hX hdec L,
      (∀ Z : PrimeDivisor B S hS X,
          ∃ (t : Z.genericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L)
            (ψ : meromorphicChartRing B S hS
                (Z.genericHenselianSpace B S hS hX hdec (RR Z) (hRR Z)).obj
                (Z.genericHenselianSpace B S hS hX hdec (RR Z) (hRR Z)).property
                (Z.genericHenselianChart B S hS hX hdec (RR Z) (hRR Z)) ≃+*
              Z.genericTotalFractionRing B S hS hX hdec),
            (Function.Bijective fun r : RR Z ↦ r • t) ∧
              ψ.symm (ratio Z s : Z.genericTotalFractionRing B S hS hX hdec) •
                  toMeromorphicSectionValue B S hS
                    (Z.genericHenselianSpace B S hS hX hdec (RR Z) (hRR Z)).obj
                    (Z.genericHenselianSpace B S hS hX hdec (RR Z) (hRR Z)).property
                    (Z.genericHenselianPullback B S hS hX hdec (RR Z) (hRR Z) L)
                    (Z.genericHenselianChart B S hS hX hdec (RR Z) (hRR Z)) t =
                Z.genericMeromorphicGerm B S hS hX hdec (RR Z) (hRR Z) L s) ∧
        (∀ Z : PrimeDivisor B S hS X,
            Z.GeneratesGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s →
              divisorCoefficients.{u, u} B S hS hX hdec L s ratio Z = 0) ∧
          LocallyFinite fun Z : PrimeDivisor B S hS X ↦
            if divisorCoefficients.{u, u} B S hS hX hdec L s ratio Z = 0 then ∅
            else Z.support B S hS X := by
  classical
  -- A free generator of `ℒ_ξ` and the canonical ratio against it, at every prime divisor.
  have hdata : ∀ Z : PrimeDivisor B S hS X,
      ∃ (k : Z.genericTotalFractionRing B S hS hX hdec)
        (t : Z.genericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L)
        (ψ : meromorphicChartRing B S hS
            (Z.genericHenselianSpace B S hS hX hdec (RR Z) (hRR Z)).obj
            (Z.genericHenselianSpace B S hS hX hdec (RR Z) (hRR Z)).property
            (Z.genericHenselianChart B S hS hX hdec (RR Z) (hRR Z)) ≃+*
          Z.genericTotalFractionRing B S hS hX hdec),
        IsUnit k ∧ (Function.Bijective fun r : RR Z ↦ r • t) ∧
          (ψ.symm k • toMeromorphicSectionValue B S hS
              (Z.genericHenselianSpace B S hS hX hdec (RR Z) (hRR Z)).obj
              (Z.genericHenselianSpace B S hS hX hdec (RR Z) (hRR Z)).property
              (Z.genericHenselianPullback B S hS hX hdec (RR Z) (hRR Z) L)
              (Z.genericHenselianChart B S hS hX hdec (RR Z) (hRR Z)) t =
            Z.genericMeromorphicGerm B S hS hX hdec (RR Z) (hRR Z) L s) ∧
          ∀ ratio : LocalRatio.{u, u} B S hS hX hdec Z L,
            (ratio s : Z.genericTotalFractionRing B S hS hX hdec) = k →
              Z.GeneratesGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s →
                orderOfVanishingSection.{u, u} B S hS hX hdec Z L s ratio = 0 := by
    intro Z
    obtain ⟨t, -, -, ht⟩ := Z.exists_ne_zero_span_genericModuleStalk_eq_top B S hS hX hdec
      (RR Z) (hRR Z) L hL
    obtain ⟨e, ψ, f, hf, hfunit, hev⟩ :=
      Z.exists_ringEquiv_forall_smul_eq_genericMeromorphicGerm B S hS hX hdec hInt hN
        (RR Z) (hRR Z) L hL t ht
    refine ⟨f s, t, ψ, hfunit s hreg, ht, hf s, fun ratio hratio hgen => ?_⟩
    refine orderOfVanishingSection_eq_zero_of_generatesGenericModuleStalk B S hS hX hdec hInt hN
      Z (RR Z) (hRR Z) L hL t ht e ψ hev s ratio ?_ hgen
    rw [hratio]
    exact hf s
  choose k t ψ hk ht hchar hord using hdata
  -- Read the canonical value as a unit, which is what `LocalRatio` is valued in.
  refine ⟨fun Z _ ↦ (hk Z).unit, fun Z ↦ ⟨t Z, ψ Z, ht Z, ?_⟩,
    fun Z hgen ↦ hord Z _ (hk Z).unit_spec hgen, ?_⟩
  · rw [show ((hk Z).unit : Z.genericTotalFractionRing B S hS hX hdec) = k Z from
      (hk Z).unit_spec]
    exact hchar Z
  · exact locallyFinite_divisorCoefficients_ne_zero_of_isIntegral B S hS hX hdec RR hRR hN hInt
      L hL s hreg _ (fun Z hgen ↦ hord Z _ (hk Z).unit_spec hgen)

end Family

end AlgebraicGeometry.Space

end
