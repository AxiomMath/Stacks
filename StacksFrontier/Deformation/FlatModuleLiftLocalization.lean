module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.Deformation.ExtBaseChangeLocalization
public import StacksFrontier.Deformation.FlatAlgebraLift
public import StacksFrontier.Deformation.FlatModuleLift
public import StacksFrontier.Deformation.FlatModuleLiftBaseChange
public import StacksFrontier.RingTheory.Localization.AwayBaseChange

/-!
# The localization step of Stacks 0DZ2

Let `A' → A` be a surjection with nilpotent kernel whose thickening `P' → P` is square-zero,
let `P'` be a flat `A'`-algebra and let
`P = P' ⊗_{A'} A`. For `g ∈ P'` the localization square `(P')_g → P_g` is again a square-zero
thickening and a base change of `A' → A`, because `(P')_g ⊗_{A'} A` is the localization of `P`
at the image of `g`. If the base change of an `A`-flat finite `P`-module `M` to `P_g` has an
`A'`-flat module lift over `(P')_g`, then: its canonical obstruction morphism vanishes, so the
base change of the obstruction morphism of `M` along `P → P_g` vanishes by Stacks 0DYR(3), so
the obstruction morphism of `M` is killed by a power of the image of `g`.

That last step is the localization half of Stacks 05EC, which identifies the base change of
`Ext` along `P → P_g` with the localization of `Ext` and is proved in
`StacksFrontier.Deformation.ExtBaseChangeLocalization`.

## Main results

* `Deformation.algEquivTensorBaseChangeOfKer`: a surjection `P' → P` with kernel `ker(A' → A)·P'`
  identifies `P` with `P' ⊗_{A'} A` as `P'`-algebras.
* `Deformation.flat_base_of_baseChangeEquiv`: the base change of an `A`-flat module along a flat
  map is `A`-flat.
* `exists_pow_smul_canonicalObstructionMap_eq_zero_of_localizationLift_of_isNilpotent_ker`: a
  module lift over the localized presentation makes the obstruction morphism power torsion
  at `g`.
* `exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift_of_isNilpotent_ker`:
  **Stacks 0DZ2** with the source's local liftability hypothesis.
* `Deformation.exists_pow_smul_canonicalObstructionMap_eq_zero_of_localizationLift` and
  `Deformation.exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift`: those two
  statements with `ker(A' → A)² = ⊥` in place of the square-zero hypothesis on the thickening,
  which that hypothesis implies.  They are instances of the two above, where the proofs are.
* `Deformation.hasFlatModuleLift_comp`: **the chain of square-zero steps composes.** A lift
  across one step of the tower of quotients `A' → A'/Iⁿ⁻¹ → … → A'/I = A` supplied by
  `Deformation.squareZero_devissage` is a lift across the composite. This is the half of the
  source's omitted induction that goes through.
* `Deformation.ObstructionIndependentOfLift`: **the other half**, named — liftability across the
  next square-zero step does not depend on which lift of the previous stage it is asked of.
* `Deformation.hasFlatModuleLift_of_obstructionIndependentOfLift`: **the reduction theorem.**
  The generic step of the chain, with that hypothesis used exactly once; so the source's
  argument, with its omitted step isolated.
* `Deformation.not_obstructionIndependentOfLift`: **that hypothesis is unsatisfiable**, so the
  route the source takes is closed rather than untried. The witness is elementary and is in
  `Deformation.ObstructionWitness`: `A' = ℤ/8`, `t = 2`, `Q' = A'[ε]/(ε²)`, and the two lifts
  `Q''/(ε)` and `Q''/(ε − t)` of one module over `Q'' = Q'/t²Q'`, of which only the first lifts.

## Implementation notes

**What separates the `_of_isNilpotent_ker` forms from Stacks 0DZ2 as the source states it.**
Two things, and only two — besides the finiteness of `M`, which is a correction of the source
rather than a deviation from it and is diagnosed in its own section below.
The first is that the *thickening* `P' → P` is assumed square-zero rather than nilpotent. Only
that one thickening: the kernel `I` of `A' → A` is assumed only nilpotent, as in the source, and
squareness of the second thickening `Q' → Q` is not assumed but derived, by
`Deformation.sq_ker_algebraMap_tensorProduct_eq_bot_of_tower` — both kernels are the extension
of `I`, so `I²·P' = 0` says that every element of `I²` already dies in `P'`, and an element
dying in `P'` dies in the `P'`-algebra `Q'`. The hypothesis `I² = 0` on the kernel of `A' → A`
is removable too, because the
one place it was needed — squareness of the localized thickening
`(P')_g → (P')_g ⊗_{A'} A` — follows from squareness of `P' → P` instead, the kernel of the
localized map being the image of `ker(P' → P)` under `P' → (P')_g` (the identity `hJker` in the
proof of
`exists_pow_smul_canonicalObstructionMap_eq_zero_of_localizationLift_of_isNilpotent_ker`). Note
that squareness of `P' → P` is strictly weaker than `I² = 0` unless `P'` is faithfully flat over
`A'`: it says `I²·P' = 0`.  The two forms that carry `I² = 0`,
`exists_pow_smul_canonicalObstructionMap_eq_zero_of_localizationLift` and
`exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift`, are kept beside them as
immediate instances, so that the two stronger statements are additions rather than replacements.
Those two forms assume `I² = 0` and nothing else about the thickenings: nilpotence of `I`, and
squareness of `P' → P`, are *derived* from it rather than assumed, so `I² = 0` is load-bearing
there and not a spurious extra hypothesis. Surjectivity of the two thickenings is not assumed on
any of the four forms either — both are base changes of `A' → A`, so `surjective_tmul_one`
derives them from `hsurjA` — and neither is `Module.Flat A' Q'`, which is the composite of the
two flat arrows `A' → P' → Q'`.
The second is that `P` and `Q` are the
literal base changes `P' ⊗_{A'} A` and `Q' ⊗_{A'} A`, whereas the source has abstract `P` and
`Q` carrying the kernel identities — the shape recorded as
`Deformation.FlatModuleLiftBaseChangeStatement`.

**Why the remaining square-zero hypothesis is not removable by the source's induction.** The
source reduces to the square-zero case "by induction on the integer `n > 1` such that `Iⁿ = 0`",
with the details omitted. The induction has one gap, it is mathematical rather than
bookkeeping, and it can be named in a single sentence: the second stage has to *select* the
intermediate lift of `M`, and nothing selects it.

One thing that would close the induction is the square-zero case strengthened to say that base
change is *surjective* on isomorphism classes of lifts, since then the lift returned at each
stage can be chosen over the given one. That strengthening is, through the torsor structure on
the set of lifts, surjectivity of `Ext¹_P(M, M ⊗_P IP) → Ext¹_Q(N, N ⊗_Q IQ)`. By Stacks 0A6A
that target is `Ext¹_P(M, M ⊗_P IP) ⊗_P Q`, and `x ↦ 1 ⊗ x` is surjective onto it exactly on the
`J'`-power torsion part (Stacks 05EC, the same lemma step (6) of the source's proof uses for
`Ext²`). So the strengthening needs `Ext¹_P(M, M ⊗_P IP)` to be `J'`-power torsion, and the
hypotheses of Stacks 0DZ2 do not give that: local liftability of `M_g` over `(P')_g` makes the
`Ext²` obstruction class vanish after localization, but says nothing about `Ext¹`, which
measures non-uniqueness of the local lift and does not vanish for a merely liftable `M_g`. It
does hold in the application of Stacks 0DZC, where `B_g` is smooth over `k` and all higher
`Ext` vanish; it does not hold under 0DZ2's own hypotheses, nor under the syntomy hypothesis
that Stacks 0DZB supplies them from. With `A' = k[ε]/(ε²)`, `P' = A'[y, z]`, `J' = (y)`,
`Q' = A'[z][[y]]` and `M = P/(z)` the `P'`-lifts are the `P'/(z - εh)` for `h ∈ k[y]` and the
`Q'`-lifts the `Q'/(z - εH)` for `H ∈ k[[y]]`, so base change on lift sets is `k[y] → k[[y]]`,
which is not surjective: that strengthening is *false*, not merely unavailable.

**The dévissage that carries obstruction classes instead, and why it is blocked too.**
Surjectivity on lift sets is sufficient for the induction but not necessary, so the paragraph
above refutes one route to the nilpotent statement and not the statement itself. The route that
carries only obstruction classes runs as follows. Write `A_j = A'/Iʲ`, `P_j = P' ⊗_{A'} A_j`,
`Q_j = Q' ⊗_{A'} A_j` and `K_j = Iʲ/Iʲ⁺¹`, and carry: there are an `A_j`-flat `P_j`-lift `M_j`
of `M` and an `A_{j+1}`-flat `Q_{j+1}`-lift of `Q_j ⊗_{P_j} M_j`. The square-zero case at
`A_{j+1} → A_j` applies to `M_j` — its `Q`-side module is `Q_j ⊗_{P_j} M_j` by construction,
which is exactly the matching the naive induction lacks — and returns a `P_{j+1}`-lift `M_{j+1}`
of `M_j`. Now `Q_{j+1} ⊗ M_{j+1}` and the hypothesised lift are two lifts of *the same* module
`Q_j ⊗ M_j`, so they differ by a single class `η ∈ Ext¹_Q(N, N ⊗ K_j)` and
`ω(Q_{j+1} ⊗ M_{j+1}) = ∂_Q(η)`, where `∂` records how the obstruction class moves along the
torsor of lifts. Were `∂` additive, flatness of `Q` over `P` would make `im(∂) ⊗_P Q` the image
of `∂_Q`, so the class of `ω(M_{j+1})` in `C = Ext²_P(M, M ⊗ K_{j+1} P)/im(∂)` would die in
`C ⊗_P Q`; it would be `J'`-power torsion, because at each `g ∈ J'` the hypothesised lift of
`M_g` over `(P')_g` reduces to a lift of `(M_j)_g` carrying one step further, which puts the
localized obstruction in the localized image of `∂`; and Stacks 05EC applied to `C` would force
that class to be zero, i.e. `ω(M_{j+1}) ∈ im(∂)`, so that `M_{j+1}` could be corrected within
its torsor to a lift with vanishing obstruction — which supplies the next `Q`-side lift and
continues the induction.

**`∂` IS NOT ADDITIVE, so that route is blocked and not merely unfinished.** This is proved by
`StacksFrontier.Deformation.ObstructionVariationQuadratic`. A lift is a differential on a bounded-above free resolution reduced
modulo `Iʲ⁺¹`, the torsor acts by `d_{j+1} + ε` with `ε` of `K_j`-coefficients, and lifting one
step further gives `(d_{j+2} + ε̃)² = d_{j+2}² + (d_{j+2} ε̃ + ε̃ d_{j+2}) + ε̃²`, whose last term
has coefficients in `I²ʲ`. Read in `K_{j+1} = Iʲ⁺¹/Iʲ⁺²` that term vanishes exactly when
`2j ≥ j + 2`, i.e. for `j ≥ 2`; at `j = 1` — the step this induction starts at — it is the
Yoneda square of `e` pushed along the multiplication `K_1 ⊗ K_1 → K_2`. So the law is
`ω(e · M_{j+1}) = ω(M_{j+1}) + δ(e) + e ∪ e` with `δ` the Bockstein of
`0 → K_{j+1} → Iʲ/Iʲ⁺² → K_j → 0`, and `∂ = δ + (· ∪ ·)` is quadratic. Its image is then not a
submodule, so `Ext²/im(∂)` does not exist and 05EC has nothing to act on; nor can a
multiplicative set be made to act invertibly on a set that is not closed under addition. The
counterexample is elementary: `A' = ZMod 8`, `I = (2)` with `I³ = 0`, `P' = A'[x]/(x²)`,
`M = (ZMod 2)²` with `x` acting as zero, where the obstruction to extending a first-order
deformation to second order is literally the square of its structure matrix
(`Deformation.ObstructionVariation.mul_self_mem_of_hasSecondOrderFlatLift`) and `!![0,1;0,0]`,
`!![0,0;1,0]` are unobstructed while their sum is not. The repair the route would need is a
local-global principle for the solvability of the *quadratic* equation `δ(e) + e ∪ e = -ω` over
`P`, which is not Stacks 05EC and is false for quadratic equations in general.

So the faithful nilpotent statement is still new mathematics rather than a transcription, and no
hypothesis-free form of it is stated here. Two things are missing rather than one: an API
presenting the set of lifts as a torsor under `Ext¹` and identifying how
`Stacks.Deformation.canonicalObstructionMap` — a morphism in a derived category — moves along
it, and, beyond that, an idea that does not route the induction through a submodule
`im(∂)`. (For the module statement the question is in any case moot at a nilpotent kernel:
`Deformation.FlatModuleLiftBaseChangeStatement` is refuted outright, see the implementation
notes of `StacksFrontier.Deformation.FlatAlgebraLiftLocalization`. The dévissage matters for
Stacks 0DZ7, 0DZB and 0DZ3, whose syntomy hypothesis supplies local liftability at every stage
of the filtration.)

**Why that second gap is not bookkeeping.** `algEquivTensorBaseChangeOfKer` supplies the
isomorphism `P ≃ₐ[P'] P' ⊗_{A'} A`, and `flat_base_of_baseChangeEquiv` supplies the one
flatness fact the abstract form does not carry — so neither of those is missing. What is
missing is an API for transporting module structures across a ring isomorphism. `Module P M`
and `Module (P' ⊗_{A'} A) M` are different instances, and `≃ₗ` cannot relate them: every
statement about `M` has to be re-derived through a semilinear identification. Concretely, in
order, the abstract form still needs: the transported module structure on `M` and `N` with
`IsScalarTower A P M` carried across the isomorphism; `Module.Finite` transported across a ring
isomorphism, for which there is no lemma; `Algebra P Q` and `Module.Flat P Q` transported across
*both* isomorphisms at once; the comparison `Q ⊗_P M ≅ (Q' ⊗_{A'} A) ⊗_{P' ⊗_{A'} A} M` that
turns the source's `hN` into the `ModuleCat.extendScalars` form, and the same repackaging for
both sides of the conclusion; and finally the local liftability hypothesis, whose statement
mentions `Localization.Away (algebraMap P' P g)` for the abstract `P`, so it has to be moved
along the isomorphism, then through `IsLocalization.Away.tensorBaseChange`, then out of the
tensor form into the `extendScalars` form.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 087Q](https://stacks.math.columbia.edu/tag/087Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

namespace Deformation

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Transporting an abstract thickening to a literal base change -/

/-- A surjection `P' → P` whose kernel is generated by the kernel of `A' → A` identifies `P`
with the base change `P' ⊗_{A'} A` as `P'`-algebras: both are the quotient of `P'` by that
ideal. -/
def algEquivTensorBaseChangeOfKer (A' A P' P : Type u) [CommRing A'] [CommRing A] [CommRing P']
    [CommRing P] [Algebra A' A] [Algebra A' P'] [Algebra P' P] [Module.Flat A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) :
    P ≃ₐ[P'] TensorProduct A' P' A := by
  have hsurjT : Function.Surjective (algebraMap P' (TensorProduct A' P' A)) :=
    surjective_tmul_one A' A hsurjA P'
  have hker : RingHom.ker (algebraMap P' P) =
      RingHom.ker (algebraMap P' (TensorProduct A' P' A)) :=
    hkerP.trans (Algebra.ker_algebraMap_tensorProduct_left A' P' A).symm
  exact (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId P' P) hsurjP).symm.trans
    ((Ideal.quotientEquivAlgOfEq P' hker).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := Algebra.ofId P' (TensorProduct A' P' A)) hsurjT))

/-- The identification of an abstract thickening with the literal base change respects the
structure map of the base: both sides send `a` to the class of any preimage of `a`. -/
theorem algEquivTensorBaseChangeOfKer_algebraMap_base (A' A P' P : Type u) [CommRing A']
    [CommRing A] [CommRing P'] [CommRing P] [Algebra A' A] [Algebra A' P'] [Algebra P' P]
    [Algebra A' P] [Algebra A P] [IsScalarTower A' A P] [IsScalarTower A' P' P]
    [Module.Flat A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) (a : A) :
    algEquivTensorBaseChangeOfKer A' A P' P hsurjA hsurjP hkerP (algebraMap A P a) =
      algebraMap A (TensorProduct A' P' A) a := by
  obtain ⟨a', rfl⟩ := hsurjA a
  rw [← IsScalarTower.algebraMap_apply A' A P, IsScalarTower.algebraMap_apply A' P' P,
    (algEquivTensorBaseChangeOfKer A' A P' P hsurjA hsurjP hkerP).commutes,
    ← IsScalarTower.algebraMap_apply A' P' (TensorProduct A' P' A),
    IsScalarTower.algebraMap_apply A' A (TensorProduct A' P' A)]

/-- **The flatness of the base change in Stacks 0DZ2.** For `A → P → Q` with `Q` flat over `P`
and an `A`-flat `P`-module `M`, any `Q`-module isomorphic to `Q ⊗_P M` is flat over `A`. -/
theorem flat_base_of_baseChangeEquiv (A P Q : Type u) [CommRing A] [CommRing P] [CommRing Q]
    [Algebra A P] [Algebra P Q] [Algebra A Q] [IsScalarTower A P Q] [Module.Flat P Q]
    (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
    [Module.Flat A M] (N : Type u) [AddCommGroup N] [Module Q N] [Module A N]
    [IsScalarTower A Q N] (e : (Q ⊗[P] M) ≃ₗ[Q] N) :
    Module.Flat A N := by
  have hflat : Module.Flat A (Q ⊗[P] M) :=
    Module.Flat.tensorProduct_of_flat_base (A' := A) (P' := P) (Q' := Q) M
  exact Module.Flat.of_linearEquiv (e.restrictScalars A).symm

/-! ### The localization step -/

/-- **The localization step of Stacks 0DZ2, at the source's nilpotence hypothesis.** Let
`A' → A` be a surjection with nilpotent kernel whose thickening `P' → P` is square-zero, let
`P'` be a flat `A'`-algebra and let `P = P' ⊗_{A'} A`. If the base change of `M` to the
localization of `P` at the image of `g` has an `A'`-flat module lift over the localization of
`P'` at `g`, then the canonical obstruction morphism of `M` is killed by a power of the image
of `g`.

This is `exists_pow_smul_canonicalObstructionMap_eq_zero_of_localizationLift` with the
hypothesis `I² = 0` on `I = ker(A' → A)` dropped: the one place it was used — squareness of the
localized thickening `(P')_g → (P')_g ⊗_{A'} A` — follows from squareness of `P' → P` instead,
the kernel of the localized map being the image of `ker(P' → P)` under `P' → (P')_g` (the
identity `hJker` below).  Squareness of `P' → P` is strictly weaker than `I² = 0` unless `P'`
is faithfully flat over `A'`: it says `I²·P' = 0`. -/
theorem exists_pow_smul_canonicalObstructionMap_eq_zero_of_localizationLift_of_isNilpotent_ker
    (A' A P' : Type u) [CommRing A'] [CommRing A] [CommRing P']
    [Algebra A' A] [Algebra A' P'] [Module.Flat A' P']
    [IsNoetherianRing (TensorProduct A' P' A)]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' (TensorProduct A' P' A)))
    (hzeroP : (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) ^ 2 = ⊥)
    (M : Type u) [AddCommGroup M] [Module (TensorProduct A' P' A) M] [Module A M]
    [IsScalarTower A (TensorProduct A' P' A) M] [Module.Flat A M]
    [Module.Finite (TensorProduct A' P' A) M]
    (K : DerivedCategory (ModuleCat.{u} (TensorProduct A' P' A)))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} (TensorProduct A' P' A))).minus K)
    (eK : K ≅ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))))
    (g : P')
    [Algebra (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A)]
    (hmapg : ∀ (x : P') (a : A),
      algebraMap (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A)
          (x ⊗ₜ[A'] a) = (algebraMap P' (Localization.Away g) x) ⊗ₜ[A'] a)
    (hlift : ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
      (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
      Module.Flat A' L ∧ Nonempty
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap (Localization.Away g)
            (TensorProduct A' (Localization.Away g) A))).obj
              (ModuleCat.of (Localization.Away g) L) ≅
          ModuleCat.of (TensorProduct A' (Localization.Away g) A)
            (ULift.{u} (TensorProduct (TensorProduct A' P' A)
              (TensorProduct A' (Localization.Away g) A) (ULift.{u} M))))) :
    ∃ n : ℕ, (algebraMap P' (TensorProduct A' P' A) g) ^ n •
      (Obstruction.canonicalObstructionMap
        (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP K hK).val = 0 := by
  classical
  -- the localization square and its flatness
  have hflatP'Pg' : Module.Flat P' (Localization.Away g) :=
    IsLocalization.flat (Localization.Away g) (Submonoid.powers g)
  have hflatA'Pg' : Module.Flat A' (Localization.Away g) :=
    Module.Flat.trans A' P' (Localization.Away g)
  have hlocPg : IsLocalization.Away (algebraMap P' (TensorProduct A' P' A) g)
      (TensorProduct A' (Localization.Away g) A) :=
    IsLocalization.Away.tensorBaseChange A' A P' (Localization.Away g) g hmapg
  have hflatPPg : Module.Flat (TensorProduct A' P' A)
      (TensorProduct A' (Localization.Away g) A) :=
    IsLocalization.flat (TensorProduct A' (Localization.Away g) A)
      (Submonoid.powers (algebraMap P' (TensorProduct A' P' A) g))
  have hsurjPg : Function.Surjective (algebraMap (Localization.Away g)
      (TensorProduct A' (Localization.Away g) A)) :=
    surjective_tmul_one A' A hsurjA (Localization.Away g)
  have hkerPg : RingHom.ker (algebraMap (Localization.Away g)
      (TensorProduct A' (Localization.Away g) A)) =
      Ideal.map (algebraMap A' (Localization.Away g)) (RingHom.ker (algebraMap A' A)) :=
    Algebra.ker_algebraMap_tensorProduct_left A' (Localization.Away g) A
  have hJker : RingHom.ker (algebraMap (Localization.Away g)
      (TensorProduct A' (Localization.Away g) A)) =
      Ideal.map (algebraMap P' (Localization.Away g))
        (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) := by
    rw [hkerPg, Algebra.ker_algebraMap_tensorProduct_left A' P' A, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  -- The localized thickening is square-zero because `P' → P` is, not because `A' → A` is: the
  -- kernel of `(P')_g → (P')_g ⊗_{A'} A` is the image of `ker(P' → P)` under `P' → (P')_g`,
  -- so `hzeroP` localizes. This is why no hypothesis on `ker(A' → A)` beyond `hnilA` is needed.
  have hzeroPg : (RingHom.ker (algebraMap (Localization.Away g)
      (TensorProduct A' (Localization.Away g) A))) ^ 2 = ⊥ := by
    rw [hJker, ← Ideal.map_pow, hzeroP, Ideal.map_bot]
  have hcomm : (algebraMap (TensorProduct A' P' A)
        (TensorProduct A' (Localization.Away g) A)).comp
        (algebraMap P' (TensorProduct A' P' A)) =
      (algebraMap (Localization.Away g)
        (TensorProduct A' (Localization.Away g) A)).comp
          (algebraMap P' (Localization.Away g)) := by
    refine RingHom.ext fun x => ?_
    have h1 : algebraMap P' (TensorProduct A' P' A) x = x ⊗ₜ[A'] (1 : A) := rfl
    have h2 : algebraMap (Localization.Away g) (TensorProduct A' (Localization.Away g) A)
        (algebraMap P' (Localization.Away g) x) =
        (algebraMap P' (Localization.Away g) x) ⊗ₜ[A'] (1 : A) := rfl
    rw [RingHom.comp_apply, RingHom.comp_apply, h1, h2, hmapg x 1]
  have hAt : ∀ a : A, algebraMap A (TensorProduct A' (Localization.Away g) A) a =
      algebraMap (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A)
        (algebraMap A (TensorProduct A' P' A) a) := by
    intro a
    have h1 : algebraMap A (TensorProduct A' P' A) a = (1 : P') ⊗ₜ[A'] a := rfl
    have h2 : algebraMap A (TensorProduct A' (Localization.Away g) A) a =
        (1 : Localization.Away g) ⊗ₜ[A'] a := rfl
    rw [h1, h2, hmapg 1 a, map_one]
  have : IsScalarTower A (TensorProduct A' P' A)
      (TensorProduct A' (Localization.Away g) A) := IsScalarTower.of_algebraMap_eq hAt
  -- the base change of `M` and its flatness over `A`
  have hflatMg : Module.Flat A (TensorProduct (TensorProduct A' P' A)
      (TensorProduct A' (Localization.Away g) A) (ULift.{u} M)) :=
    Module.Flat.tensorProduct_of_flat_base (A' := A) (P' := TensorProduct A' P' A)
      (Q' := TensorProduct A' (Localization.Away g) A) (ULift.{u} M)
  -- the derived base change of `K` is the single complex on that base change
  have hld := (derivedExtensionScalarsGeneral.{u, u, u}
    (algebraMap (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A))).isLeftDerived
  have hcompIso : IsIso (derivedExtensionScalarsGeneral.{u, u, u}
      (algebraMap (TensorProduct A' P' A)
        (TensorProduct A' (Localization.Away g) A))).comparison :=
    @StacksDraft.DerivedHom.HomModuleBaseChange.isIso_comparison_of_flat
      (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A) _ _ _ hflatPPg _ _ hld
  have eMod : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A))).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)) ≅
      ModuleCat.of (TensorProduct A' (Localization.Away g) A)
        (ULift.{u} (TensorProduct (TensorProduct A' P' A)
          (TensorProduct A' (Localization.Away g) A) (ULift.{u} M))) :=
    LinearEquiv.toModuleIso
      ((StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))).trans
          (ULift.moduleEquiv).symm)
  have eFK : (derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap (TensorProduct A' P' A)
          (TensorProduct A' (Localization.Away g) A))).functor.obj K ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (ModuleCat.{u} (TensorProduct A' (Localization.Away g) A)) 0).obj
          (ModuleCat.of (TensorProduct A' (Localization.Away g) A)
            (ULift.{u} (TensorProduct (TensorProduct A' P' A)
              (TensorProduct A' (Localization.Away g) A) (ULift.{u} M))))) :=
    (derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap (TensorProduct A' P' A)
          (TensorProduct A' (Localization.Away g) A))).functor.mapIso eK ≪≫
      asIso ((derivedExtensionScalarsGeneral.{u, u, u}
          (algebraMap (TensorProduct A' P' A)
            (TensorProduct A' (Localization.Away g) A))).comparison.app
        ((CochainComplex.singleFunctor (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
          (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)))) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars.{u, u, u}
            (algebraMap (TensorProduct A' P' A)
              (TensorProduct A' (Localization.Away g) A)))
          (ComplexShape.up ℤ) 0).app
            (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))) ≪≫
      DerivedCategory.Q.mapIso ((CochainComplex.singleFunctor
        (ModuleCat.{u} (TensorProduct A' (Localization.Away g) A)) 0).mapIso eMod)
  -- the obstruction morphism of the localization vanishes
  have hFKminus := (derivedExtensionScalarsGeneral.{u, u, u}
    (algebraMap (TensorProduct A' P' A)
      (TensorProduct A' (Localization.Away g) A))).maps_boundedAbove ⟨K, hK⟩
  have hωg : (Obstruction.canonicalObstructionMap
      (algebraMap (Localization.Away g) (TensorProduct A' (Localization.Away g) A))
      hsurjPg hzeroPg ((derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap (TensorProduct A' P' A)
          (TensorProduct A' (Localization.Away g) A))).functor.obj K) hFKminus).val = 0 :=
    (exists_flat_lift_iff_canonicalObstructionMap_eq_zero A' A (Localization.Away g)
      hsurjA hnilA hsurjPg hzeroPg _ _ hFKminus eFK).mp hlift
  -- Stacks 0DYR(3): the base change of the obstruction morphism of `M` vanishes too
  obtain ⟨Θ, hΘ, hΘeq⟩ := Obstruction.exists_isIso_obstructionTargetBaseChange
    (algebraMap P' (TensorProduct A' P' A)) hsurjP
    (algebraMap (Localization.Away g) (TensorProduct A' (Localization.Away g) A)) hsurjPg
    (algebraMap P' (Localization.Away g))
    (algebraMap (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A))
    hcomm hJker (RingHom.flat_algebraMap_iff.mpr hflatP'Pg')
    (RingHom.flat_algebraMap_iff.mpr hflatPPg)
    (Obstruction.canonicalObstructionMap
      (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP K hK).2
    (Obstruction.canonicalObstructionMap
      (algebraMap (Localization.Away g) (TensorProduct A' (Localization.Away g) A))
      hsurjPg hzeroPg ((derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap (TensorProduct A' P' A)
          (TensorProduct A' (Localization.Away g) A))).functor.obj K) hFKminus).2
  have hmono : Mono (((derivedExtensionScalarsGeneral.{u, u, u}
      (algebraMap (TensorProduct A' P' A)
        (TensorProduct A' (Localization.Away g) A))).functor.commShiftIso (2 : ℤ)).hom.app
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
          (TensorProduct A' P' A)).obj K).obj
            (Obstruction.squareZeroKernelObject.{u, u}
              (algebraMap P' (TensorProduct A' P' A)) hsurjP)) ≫
      (shiftFunctor (DerivedCategory
        (ModuleCat.{u} (TensorProduct A' (Localization.Away g) A))) (2 : ℤ)).map Θ) :=
    mono_comp _ _
  rw [hωg] at hΘeq
  have hFzero : (derivedExtensionScalarsGeneral.{u, u, u}
      (algebraMap (TensorProduct A' P' A)
        (TensorProduct A' (Localization.Away g) A))).functor.map
        (Obstruction.canonicalObstructionMap
          (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP K hK).val = 0 :=
    zero_of_comp_mono _ hΘeq
  -- Stacks 05EC: the obstruction morphism is power torsion at `g`
  obtain ⟨N₀, _instN₀, _instN₀mod, ⟨eT⟩⟩ :=
    exists_singleIso_obstructionTarget A' A P' hsurjA hsurjP M K eK
  exact @ExtBaseChange.exists_pow_smul_eq_zero_of_map_eq_zero_of_singleIso
    (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A) _ _ _ _
    (algebraMap P' (TensorProduct A' P' A) g) hlocPg
    (derivedExtensionScalarsGeneral.{u, u, u}
      (algebraMap (TensorProduct A' P' A)
        (TensorProduct A' (Localization.Away g) A))).functor
    (derivedExtensionScalarsGeneral.{u, u, u}
      (algebraMap (TensorProduct A' P' A)
        (TensorProduct A' (Localization.Away g) A))).comparison
    hld _ M N₀ _ _ _ _ _ K _ 2
    (eK ≪≫ ((DerivedCategory.singleFunctorIsoCompQ
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).app _).symm) eT _ hFzero

/-- **The localization step of Stacks 0DZ2.** Let `A' → A` be a surjection with square-zero
kernel, let `P'` be a flat `A'`-algebra and let `P = P' ⊗_{A'} A`. If the base change of `M` to
the localization of `P` at the image of `g` has an `A'`-flat module lift over the localization
of `P'` at `g`, then the canonical obstruction morphism of `M` is killed by a power of the
image of `g`. -/
theorem exists_pow_smul_canonicalObstructionMap_eq_zero_of_localizationLift
    (A' A P' : Type u) [CommRing A'] [CommRing A] [CommRing P']
    [Algebra A' A] [Algebra A' P'] [Module.Flat A' P']
    [IsNoetherianRing (TensorProduct A' P' A)]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : (RingHom.ker (algebraMap A' A)) ^ 2 = ⊥)
    (hsurjP : Function.Surjective (algebraMap P' (TensorProduct A' P' A)))
    (hzeroP : (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) ^ 2 = ⊥)
    (M : Type u) [AddCommGroup M] [Module (TensorProduct A' P' A) M] [Module A M]
    [IsScalarTower A (TensorProduct A' P' A) M] [Module.Flat A M]
    [Module.Finite (TensorProduct A' P' A) M]
    (K : DerivedCategory (ModuleCat.{u} (TensorProduct A' P' A)))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} (TensorProduct A' P' A))).minus K)
    (eK : K ≅ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))))
    (g : P')
    [Algebra (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A)]
    (hmapg : ∀ (x : P') (a : A),
      algebraMap (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A)
          (x ⊗ₜ[A'] a) = (algebraMap P' (Localization.Away g) x) ⊗ₜ[A'] a)
    (hlift : ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
      (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
      Module.Flat A' L ∧ Nonempty
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap (Localization.Away g)
            (TensorProduct A' (Localization.Away g) A))).obj
              (ModuleCat.of (Localization.Away g) L) ≅
          ModuleCat.of (TensorProduct A' (Localization.Away g) A)
            (ULift.{u} (TensorProduct (TensorProduct A' P' A)
              (TensorProduct A' (Localization.Away g) A) (ULift.{u} M))))) :
    ∃ n : ℕ, (algebraMap P' (TensorProduct A' P' A) g) ^ n •
      (Obstruction.canonicalObstructionMap
        (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP K hK).val = 0 := by
  -- Nilpotence of `ker(A' → A)` is not assumed: `hzeroA` is stronger.
  exact exists_pow_smul_canonicalObstructionMap_eq_zero_of_localizationLift_of_isNilpotent_ker
    A' A P' hsurjA ⟨2, hzeroA⟩ hsurjP hzeroP M K hK eK g hmapg hlift

/-- **Stacks 0DZ2 with the source's local liftability hypothesis, at the source's nilpotence
hypothesis.** Let `A' → A` be a surjection of commutative rings with nilpotent kernel whose
thickening `P' → P` is square-zero, let `P'` and `Q'` be flat `A'`-algebras with
`P' → Q'` flat, let `P = P' ⊗_{A'} A` and `Q = Q' ⊗_{A'} A` with `P` Noetherian and
`P/J'P ≅ Q/J'Q` for an ideal `J'` of `P'`, and let `N` be the base change to `Q` of a `P`-module
`M` finite over `P` and flat over `A`. If for every `g ∈ J'` the base change of `M` to the
localization of `P` at the image of `g` has an `A'`-flat module lift over `(P')_g`, then `M` has
an `A'`-flat lift to a `P'`-module if and only if `N` has an `A'`-flat lift to a `Q'`-module.

This is `exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift` with the
hypothesis `ker(A' → A)² = ⊥` dropped, so that the kernel of `A' → A` carries only the
nilpotence the source assumes; what remains square-zero is the single thickening `P' → P`,
squareness of `Q' → Q` being derived from it by
`Deformation.sq_ker_algebraMap_tensorProduct_eq_bot_of_tower`.

Flatness of `N` over `A` is not assumed, in either form: `N` is isomorphic to `Q ⊗_P M` and `M`
is `A`-flat, so `flat_base_of_baseChangeEquiv` supplies it. The source does not assume it either.

The localization of `P` at the image of `g` is realized as `(P')_g ⊗_{A'} A`, which
`IsLocalization.Away.tensorBaseChange` identifies with it. -/
@[stacks 0DZ2 "a RESTRICTED form of 0DZ2, restricted by exactly two hypotheses: `hzeroP`, \
which asks the thickening `P' → P` to be square-zero rather than merely nilpotent, and \
`Module.Finite P M`, which asks `M` to be finite over `P`. NEITHER IS REMOVABLE, because the \
UNRESTRICTED statement is FALSE — a Stacks ERRATUM — so \
what 0DZ2 asserts in this library is the implication (1) => (2), registered on \
`Deformation.HasFlatModuleLift.baseChange`. It is refuted, at every universe, by \
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement`, and in the form \
that writes out every one of the source's hypotheses by \
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful`. That \
witness satisfies both of the hypotheses whose removal is at issue in the other direction: its \
`ker(A' → A) = (t)` has `t³ = 0` and `t² ≠ 0`, so it is nilpotent and not square-zero, and its \
`M` IS finite over `P`. What follows is why each restriction is there. \
Corrected: `M` is assumed finite over `P`. The source's statement omits it, its \
own proof uses it — `here we use that P is Noetherian and M finite`, when invoking Stacks 0A6A \
to commute `Ext²` with the flat base change `P → Q` — and that step is FALSE without it, not \
merely unproved: for `k` countable, `P = k[x, y]`, `Q = k[[x, y]]`, `A' = k[ε]/(ε²)`, \
`J' = (x, y)` and the non-finite `A`-flat module `M = ⨁ₙ P/(xⁿ, yⁿ)`, the comparison \
`Ext²_P(M, M ⊗_P IP) ⊗_P Q → Ext²_Q(M ⊗_P Q, (M ⊗_P Q) ⊗_Q IQ)` is the multiplication map \
`T ⊗_P Q → T` of a copy of `Q` sitting inside the infinite product `T` that `Ext` out of an \
infinite direct sum produces, and `Q ⊗_P Q → Q` has a nonzero kernel. Nothing weaker will do \
either: over the Noetherian `P` that 0DZ2 assumes, the `(-3)`-pseudo-coherence that Stacks 087Q \
needs in degree `2` is equivalent to finiteness. The computation, and the Mayer–Vietoris \
identification of what a finiteness-free proof would still owe, are in the implementation notes \
of this file; the equivalence itself is not refuted for a non-finite `M`, only the source's \
proof of it. Also: the thickening `P' → P` is \
assumed square-zero rather than merely nilpotent, which is what the obstruction calculus of \
Stacks 0DYR needs in order to have an obstruction class at all. Those are the only two \
deviations: the kernel of `A' → A` itself is assumed only nilpotent, as in the source, and \
squareness of the second thickening `Q' → Q` is derived rather than assumed, by \
`Deformation.sq_ker_algebraMap_tensorProduct_eq_bot_of_tower`; so this statement is strictly \
stronger than the one registered on \
`Deformation.exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift`. The \
dévissage from the square-zero thickening to the source's nilpotent one is NOT available from \
0DZ2's own hypotheses. The source's reduction is `details omitted`; with `A'' = A'/I^{n-1}` \
every hypothesis of the lemma transports to the stage `A'' → A`, including local liftability, \
which reduces along the already-proved forward direction, so the induction produces an \
`A''`-flat `P''`-lift `M''` of `M` — and then needs the obstruction class of the square-zero \
step `A' → A''` to be independent of which `A''`-flat `P''`-lift of `M` it is evaluated on. \
Grant that and the induction closes; it is false already for `I³ = 0`. All of this is now a \
Lean object rather than a paragraph: the tower of quotients is \
`Deformation.squareZero_devissage`, a lift across one step of it is a lift across the composite \
by `Deformation.hasFlatModuleLift_comp`, the generic step of the induction with its missing \
input named is `Deformation.hasFlatModuleLift_of_obstructionIndependentOfLift`, that input is \
`Deformation.ObstructionIndependentOfLift`, and it is UNSATISFIABLE — \
`Deformation.not_obstructionIndependentOfLift`, at every universe, by the elementary witness \
`A' = ℤ/8`, `Q' = A'[ε]/(ε²)`, where the two lifts `Q''/(ε)` and `Q''/(ε − 2)` over \
`Q'' = Q'/4Q'` have the same reduction and only the first lifts. So the source's route to the \
nilpotent case is closed, not untried. In the shape the source's own `k` would take it: over \
`A' = k[t]/(t³)`, `P' = k[t, x]/(t³, x²)`, the module `M = k` has the `A'`-flat `P'`-lift \
`P'/(x)`, while its `A''`-flat `P''`-lift `P''/(x - t)` has none, the two obstructions \
differing by the Yoneda square of the separating class in `Ext¹_{k[x]/(x²)}(k, k)`; and that \
is a legitimate instance of 0DZ2, with `Q' = P'` and `J' = P'`. Selecting `M''` instead by \
`Q'' ⊗ M'' ≅ N''` would need base change to be surjective on isomorphism classes of lifts, \
i.e. `Ext¹_P(M, M ⊗_P ĪP)` to be `J'`-power torsion by Stacks 0A6A and 05EC, which fails \
already for a hypersurface `M = P/(f)`. Full diagnosis in the implementation notes of this \
file"]
theorem exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift_of_isNilpotent_ker
    (A' A P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra P' Q'] [IsScalarTower A' P' Q']
    [Module.Flat A' P'] [Module.Flat P' Q']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hzeroP : (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) ^ 2 = ⊥)
    [Algebra (TensorProduct A' P' A) (TensorProduct A' Q' A)]
    [IsNoetherianRing (TensorProduct A' P' A)]
    (hcomm : (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)).comp
        (algebraMap P' (TensorProduct A' P' A)) =
      (algebraMap Q' (TensorProduct A' Q' A)).comp (algebraMap P' Q'))
    (hflatPQ : Module.Flat (TensorProduct A' P' A) (TensorProduct A' Q' A))
    (J' : Ideal P')
    (hquot : Function.Bijective (Ideal.quotientMap
      ((J'.map (algebraMap P' (TensorProduct A' P' A))).map
        (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)))
      (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)) Ideal.le_comap_map))
    (M : Type u) [AddCommGroup M] [Module (TensorProduct A' P' A) M] [Module A M]
    [IsScalarTower A (TensorProduct A' P' A) M] [Module.Flat A M]
    [Module.Finite (TensorProduct A' P' A) M]
    (N : Type u) [AddCommGroup N] [Module (TensorProduct A' Q' A) N] [Module A N]
    [IsScalarTower A (TensorProduct A' Q' A) N]
    (hN : Nonempty ((ModuleCat.extendScalars.{u, u, u}
        (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).obj
          (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)) ≅
      ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N)))
    (K : DerivedCategory (ModuleCat.{u} (TensorProduct A' P' A)))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} (TensorProduct A' P' A))).minus K)
    (eK : K ≅ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))))
    (hlocal : ∀ g ∈ J',
      letI : Algebra (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A' P' (Localization.Away g))
          (AlgHom.id A' A)).toRingHom.toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((ModuleCat.extendScalars.{u, u, u} (algebraMap (Localization.Away g)
              (TensorProduct A' (Localization.Away g) A))).obj
                (ModuleCat.of (Localization.Away g) L) ≅
            ModuleCat.of (TensorProduct A' (Localization.Away g) A)
              (ULift.{u} (TensorProduct (TensorProduct A' P' A)
                (TensorProduct A' (Localization.Away g) A) (ULift.{u} M))))) :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap P' (TensorProduct A' P' A))).obj (ModuleCat.of P' M') ≅
          ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))) ↔
      (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
        (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap Q' (TensorProduct A' Q' A))).obj (ModuleCat.of Q' N') ≅
          ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N))) := by
  obtain ⟨eMod⟩ := hN
  -- Surjectivity of the two thickenings is not assumed: both are base changes of `A' → A`,
  -- so `surjective_tmul_one` derives them from `hsurjA`.  Nor is `Module.Flat A' Q'`: it is
  -- the composite of the two flat arrows `A' → P' → Q'`.
  have hsurjP : Function.Surjective (algebraMap P' (TensorProduct A' P' A)) :=
    surjective_tmul_one A' A hsurjA P'
  have hsurjQ : Function.Surjective (algebraMap Q' (TensorProduct A' Q' A)) :=
    surjective_tmul_one A' A hsurjA Q'
  have : Module.Flat A' Q' := Module.Flat.trans A' P' Q'
  -- `Module.Flat A N` is not assumed: `N ≅ Q ⊗_P M` and `M` is `A`-flat, so it is a theorem.
  have : IsScalarTower A (TensorProduct A' P' A) (TensorProduct A' Q' A) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      obtain ⟨a', rfl⟩ := hsurjA a
      have h1 := RingHom.congr_fun (algebraMap_comp_tensorProduct_comm A' A P') a'
      have h2 := RingHom.congr_fun (algebraMap_comp_tensorProduct_comm A' A Q') a'
      have h3 := RingHom.congr_fun hcomm (algebraMap A' P' a')
      simp only [RingHom.comp_apply] at h1 h2 h3
      rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply A' P' Q']
  have := hflatPQ
  have : Module.Flat A (ULift.{u} N) :=
    flat_base_of_baseChangeEquiv A (TensorProduct A' P' A) (TensorProduct A' Q' A)
      (ULift.{u} M) (ULift.{u} N)
      ((StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))).symm.trans
          eMod.toLinearEquiv)
  have : Module.Flat A N := .of_ulift
  refine exists_flat_lift_iff_exists_flat_lift_baseChange_of_finite A' A P' Q' hsurjA hnilA
    hsurjP hzeroP hsurjQ hcomm hflatPQ
    (J'.map (algebraMap P' (TensorProduct A' P' A))) (IsNoetherian.noetherian _) hquot M N ⟨eMod⟩
    K hK eK ?_
  refine exists_pow_smul_eq_zero_of_mem_map
    (algebraMap P' (TensorProduct A' P' A)) J' fun g hg => ?_
  let : Algebra (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A' P' (Localization.Away g))
      (AlgHom.id A' A)).toRingHom.toAlgebra
  refine exists_pow_smul_canonicalObstructionMap_eq_zero_of_localizationLift_of_isNilpotent_ker
    A' A P' hsurjA hnilA hsurjP hzeroP M K hK eK g (fun x a => ?_) (hlocal g hg)
  show Algebra.TensorProduct.map (IsScalarTower.toAlgHom A' P' (Localization.Away g))
    (AlgHom.id A' A) (x ⊗ₜ[A'] a) = (algebraMap P' (Localization.Away g) x) ⊗ₜ[A'] a
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/-- **Stacks 0DZ2 with the source's local liftability hypothesis.** Let `A' → A` be a surjection
of commutative rings with square-zero kernel, let `P'` and `Q'` be flat `A'`-algebras with
`P' → Q'` flat, let `P = P' ⊗_{A'} A` and `Q = Q' ⊗_{A'} A` with `P` Noetherian and
`P/J'P ≅ Q/J'Q` for an ideal `J'` of `P'`, and let `N` be the base change to `Q` of a `P`-module
`M` finite over `P` and flat over `A`. If for every `g ∈ J'` the base change of `M` to the
localization of `P` at the image of `g` has an `A'`-flat module lift over `(P')_g`, then `M` has
an `A'`-flat lift to a `P'`-module if and only if `N` has an `A'`-flat lift to a `Q'`-module.

Flatness of `N` over `A` is not assumed here either; see
`exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift_of_isNilpotent_ker`.

The localization of `P` at the image of `g` is realized as `(P')_g ⊗_{A'} A`, which
`IsLocalization.Away.tensorBaseChange` identifies with it. -/
@[stacks 0DZ2 "a RESTRICTED form of 0DZ2, restricted by `hzeroA` — the kernel of `A' → A` is \
assumed square-zero rather than merely nilpotent — and by `Module.Finite P M`. NEITHER IS \
REMOVABLE: the UNRESTRICTED statement is FALSE — a Stacks ERRATUM — \
so what 0DZ2 asserts in this library is the implication (1) => (2), registered on \
`Deformation.HasFlatModuleLift.baseChange`. It is refuted at every universe by \
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement` and, with every \
source hypothesis written out, by \
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful`, whose \
witness has a nilpotent non-square-zero `ker(A' → A)` and a finite `M`. Why each restriction is \
there: `M` is assumed finite over `P` — the source's statement omits it, its \
own proof uses it when invoking Stacks 0A6A to commute `Ext²` with the flat base change \
`P → Q`, and that step is false without it, by the counterexample written out in the \
implementation notes of this file; \
and the kernel of `A' → A` is assumed square-zero rather than merely nilpotent, which is what \
makes both the nilpotence of that kernel and squareness of the thickening `P' → P` theorems \
here rather than hypotheses. \
This is the weaker of the two registrations: \
`exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift_of_isNilpotent_ker` \
carries the source's nilpotence on that kernel and asks squareness only of the thickening \
`P' → P`, and the clause there records why the dévissage to the source's nilpotent thickening \
is not available from 0DZ2's own hypotheses"]
theorem exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift
    (A' A P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra P' Q'] [IsScalarTower A' P' Q']
    [Module.Flat A' P'] [Module.Flat P' Q']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : (RingHom.ker (algebraMap A' A)) ^ 2 = ⊥)
    [Algebra (TensorProduct A' P' A) (TensorProduct A' Q' A)]
    [IsNoetherianRing (TensorProduct A' P' A)]
    (hcomm : (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)).comp
        (algebraMap P' (TensorProduct A' P' A)) =
      (algebraMap Q' (TensorProduct A' Q' A)).comp (algebraMap P' Q'))
    (hflatPQ : Module.Flat (TensorProduct A' P' A) (TensorProduct A' Q' A))
    (J' : Ideal P')
    (hquot : Function.Bijective (Ideal.quotientMap
      ((J'.map (algebraMap P' (TensorProduct A' P' A))).map
        (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)))
      (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)) Ideal.le_comap_map))
    (M : Type u) [AddCommGroup M] [Module (TensorProduct A' P' A) M] [Module A M]
    [IsScalarTower A (TensorProduct A' P' A) M] [Module.Flat A M]
    [Module.Finite (TensorProduct A' P' A) M]
    (N : Type u) [AddCommGroup N] [Module (TensorProduct A' Q' A) N] [Module A N]
    [IsScalarTower A (TensorProduct A' Q' A) N]
    (hN : Nonempty ((ModuleCat.extendScalars.{u, u, u}
        (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).obj
          (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)) ≅
      ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N)))
    (K : DerivedCategory (ModuleCat.{u} (TensorProduct A' P' A)))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} (TensorProduct A' P' A))).minus K)
    (eK : K ≅ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))))
    (hlocal : ∀ g ∈ J',
      letI : Algebra (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A' P' (Localization.Away g))
          (AlgHom.id A' A)).toRingHom.toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((ModuleCat.extendScalars.{u, u, u} (algebraMap (Localization.Away g)
              (TensorProduct A' (Localization.Away g) A))).obj
                (ModuleCat.of (Localization.Away g) L) ≅
            ModuleCat.of (TensorProduct A' (Localization.Away g) A)
              (ULift.{u} (TensorProduct (TensorProduct A' P' A)
                (TensorProduct A' (Localization.Away g) A) (ULift.{u} M))))) :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap P' (TensorProduct A' P' A))).obj (ModuleCat.of P' M') ≅
          ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))) ↔
      (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
        (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap Q' (TensorProduct A' Q' A))).obj (ModuleCat.of Q' N') ≅
          ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N))) := by
  -- Everything the stronger form asks of the two thickenings follows from `hzeroA`: the kernel
  -- of `P' → P' ⊗_{A'} A` is the extension of `ker(A' → A)` along the flat `A' → P'`, so its
  -- square is the extension of `ker(A' → A)²`, and nilpotence is the case `n = 2`.
  have hzeroP : (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) ^ 2 = ⊥ := by
    rw [Algebra.ker_algebraMap_tensorProduct_left A' P' A, ← Ideal.map_pow, hzeroA,
      Ideal.map_bot]
  exact exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift_of_isNilpotent_ker
    A' A P' Q' hsurjA ⟨2, hzeroA⟩ hzeroP hcomm hflatPQ J' hquot M N hN K hK eK
    hlocal

/-! ### The chain of square-zero steps, and the step the source leaves out -/

/-- **The hypothesis the source's omitted induction needs, and that the square-zero case does
not supply.**

Stacks 0DZ2 reduces its nilpotent thickening to a chain of square-zero ones — "*induction on the
integer `n > 1` such that `Iⁿ = 0` … details omitted*" — and the chain is the tower of quotients
`A' → A'/I^{n-1} → … → A'/I = A` supplied by `Deformation.squareZero_devissage`. Running it
backwards produces, at the intermediate stage `A'' = A'/I^{n-1}`, *some* `A''`-flat lift of the
module, and then needs the next square-zero step to be applicable to *that* lift. What it is
owed, and never gets, is that liftability across the next square-zero step does not depend on
which lift of the previous stage it is asked of.

This records that statement. For a square-zero thickening `s : Q' → Q''` which is the base
change of a square-zero ideal `K` of the base `A'`, and a further nilpotent reduction
`r : Q'' → Q` which is the base change of a nilpotent ideal `L` of `A'`, it says: two
`Q''`-modules with isomorphic reductions along `r` are liftable or unliftable together. Since
liftability across a square-zero step is the vanishing of the obstruction class of Stacks 0DYR,
this is the independence of that class from the lift it is evaluated on.

It is **false**: `Deformation.not_obstructionIndependentOfLift`. -/
def ObstructionIndependentOfLift : Prop :=
  ∀ (A' Q' Q'' Q : Type u) [CommRing A'] [CommRing Q'] [CommRing Q''] [CommRing Q]
    (b : A' →+* Q') (s : Q' →+* Q'') (r : Q'' →+* Q) (K L : Ideal A'),
    Function.Surjective s → Function.Surjective r →
    K ^ 2 = ⊥ → IsNilpotent L →
    RingHom.ker s = K.map b → RingHom.ker r = L.map (s.comp b) →
    @Module.Flat A' Q' _ _ (Module.compHom Q' b) →
    ∀ (N₀ : Type u) (_ : AddCommGroup N₀) (_ : Module Q'' N₀)
      (N₁ : Type u) (_ : AddCommGroup N₁) (_ : Module Q'' N₁),
      letI : Algebra Q'' Q := r.toAlgebra
      Nonempty ((Q ⊗[Q''] N₀) ≃ₗ[Q''] (Q ⊗[Q''] N₁)) →
      HasFlatModuleLift b s N₀ → HasFlatModuleLift b s N₁

/-- **The chain composes.** If `M''` has an `A'`-flat lift across one step `p₁ : P' → P''` of a
chain of thickenings, and `M` is the base change of `M''` along the next step `p₂ : P'' → P`,
then `M` has an `A'`-flat lift across the composite `p₂ ∘ p₁`.

This is what makes the tower of quotients `A' → A'/Iⁿ⁻¹ → … → A'/I = A` of
`Deformation.squareZero_devissage` usable for the lifting problem: a lift obtained at one stage
of the chain is a lift at every later stage, and in particular a lift across the first,
square-zero, step is a lift across the whole nilpotent thickening. It is the half of the
source's omitted induction that does go through; what does not is
`Deformation.ObstructionIndependentOfLift`. -/
theorem hasFlatModuleLift_comp {A' P' P'' P : Type u} [CommRing A'] [CommRing P'] [CommRing P'']
    [CommRing P] (a : A' →+* P') (p₁ : P' →+* P'') (p₂ : P'' →+* P)
    (M : Type u) [AddCommGroup M] [Module P M]
    (M'' : Type u) [AddCommGroup M''] [Module P'' M'']
    (hM : letI : Algebra P'' P := p₂.toAlgebra
      Nonempty ((P ⊗[P''] M'') ≃ₗ[P] M))
    (h : HasFlatModuleLift a p₁ M'') :
    HasFlatModuleLift a (p₂.comp p₁) M := by
  let : Algebra P' P'' := p₁.toAlgebra
  let : Algebra P'' P := p₂.toAlgebra
  let : Algebra P' P := (p₂.comp p₁).toAlgebra
  have : IsScalarTower P' P'' P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨N, hNflat, ⟨eN⟩⟩ := h
  obtain ⟨eM⟩ := hM
  refine ⟨N, hNflat, ⟨?_⟩⟩
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange P' P'' P P
      (N : Type u)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P P) eN ≪≫ₗ eM


namespace ObstructionWitness

open Polynomial

/-- The base ring of the witness: `ℤ/8` in the ambient universe. -/
abbrev Base : Type u := ULift.{u} (ZMod 8)

/-- The nilpotent `t = 2` of the base: `t³ = 0` and `t² ≠ 0`. -/
abbrev t : Base.{u} := 2

/-- Under `ULift.ringEquiv`, `t` is `2 : ZMod 8`. -/
theorem ringEquiv_t : ULift.ringEquiv (t.{u}) = (2 : ZMod 8) := map_ofNat _ 2

/-- `t³ = 0` in the base. -/
theorem t_pow_three : (t.{u}) ^ 3 = 0 :=
  ULift.ringEquiv.injective (by rw [map_pow, map_zero, ringEquiv_t]; decide)

/-- `t² · t = 0` in the base. -/
theorem t_sq_mul_t : (t.{u}) ^ 2 * t.{u} = 0 := by
  rw [← pow_succ]; exact t_pow_three

/-- `t² · t² = 0` in the base. -/
theorem t_sq_mul_t_sq : (t.{u}) ^ 2 * t.{u} ^ 2 = 0 := by
  have : (t.{u}) ^ 2 * t.{u} ^ 2 = (t.{u} ^ 2 * t.{u}) * t.{u} := by ring
  rw [this, t_sq_mul_t, zero_mul]

/-- The annihilator of `t²` in the base is `(t)`: this is the one arithmetic fact about `ℤ/8`
that the flatness step consumes. -/
theorem t_dvd_of_t_sq_mul_eq_zero {x : Base.{u}} (h : t.{u} ^ 2 * x = 0) : t.{u} ∣ x := by
  have h2 : (2 : ZMod 8) ^ 2 * ULift.ringEquiv x = 0 := by
    have := congrArg ULift.ringEquiv h
    rwa [map_mul, map_pow, ringEquiv_t, map_zero] at this
  have h3 : (2 : ZMod 8) ∣ ULift.ringEquiv x := by
    revert h2
    generalize ULift.ringEquiv x = y
    revert y
    decide
  obtain ⟨c, hc⟩ := h3
  refine ⟨ULift.ringEquiv.symm c, ULift.ringEquiv.injective ?_⟩
  rw [map_mul, ringEquiv_t, RingEquiv.apply_symm_apply, hc]


/-- `Amb = Base[ε]/(ε²)`: free of rank two over `Base`, hence flat, and not smooth. -/
abbrev Amb : Type u := AdjoinRoot (X ^ 2 : Polynomial Base.{u})

/-- The structure map of `Amb`. -/
abbrev bAmb : Base.{u} →+* Amb.{u} := algebraMap Base.{u} Amb.{u}

/-- The square-zero element `ε` of `Amb`. -/
abbrev eps : Amb.{u} := AdjoinRoot.root (X ^ 2 : Polynomial Base.{u})

/-- `ε² = 0` in `Amb`. -/
theorem eps_sq : (eps.{u}) ^ 2 = 0 := by
  have h : AdjoinRoot.mk (X ^ 2 : Polynomial Base.{u}) (X ^ 2) = 0 := AdjoinRoot.mk_self
  rw [map_pow] at h
  exact h

/-- `Amb` is flat over the base. -/
theorem flat_Amb : Module.Flat Base.{u} Amb.{u} := by
  have : Module.Free Base.{u} Amb.{u} :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_X_pow 2)).basis
  exact Module.Flat.of_free

/-- `Amb` is flat over the base for the module structure given by restriction of scalars along
`bAmb`. -/
theorem flat_compHom_Amb :
    @Module.Flat Base.{u} Amb.{u} _ _ (Module.compHom Amb.{u} bAmb.{u}) := by
  have h : Module.compHom Amb.{u} bAmb.{u} = (inferInstance : Module Base.{u} Amb.{u}) :=
    Module.ext' _ _ fun a x => (Algebra.smul_def a x).symm
  rw [h]
  exact flat_Amb

/-- `K = (t²)`, the square-zero ideal of the base. -/
abbrev Ksq : Ideal Base.{u} := Ideal.span {t.{u} ^ 2}

/-- `L = (t)`, the nilpotent ideal of the base. -/
abbrev Lnil : Ideal Base.{u} := Ideal.span {t.{u}}

/-- The ideal `(t²)` of the base squares to zero. -/
theorem Ksq_sq : (Ksq.{u}) ^ 2 = ⊥ := by
  rw [Ideal.span_singleton_pow, ← pow_mul]
  have h : (t.{u}) ^ (2 * 2) = 0 := by
    have : (t.{u}) ^ (2 * 2) = t.{u} ^ 2 * t.{u} ^ 2 := by ring
    rw [this, t_sq_mul_t_sq]
  rw [h]
  exact Ideal.span_singleton_eq_bot.mpr rfl

/-- The ideal `(t)` of the base is nilpotent. -/
theorem isNilpotent_Lnil : IsNilpotent (Lnil.{u}) :=
  ⟨3, by
    rw [Ideal.span_singleton_pow, t_pow_three]
    exact Ideal.span_singleton_eq_bot.mpr rfl⟩

/-- `Mid = Amb/t²Amb`: the square-zero thickening of the witness. -/
abbrev Mid : Type u := Amb.{u} ⧸ Ksq.{u}.map bAmb.{u}

/-- The square-zero step. -/
abbrev sMid : Amb.{u} →+* Mid.{u} := Ideal.Quotient.mk _

/-- `Red = Mid/tMid`: the remaining reduction. -/
abbrev Red : Type u := Mid.{u} ⧸ Lnil.{u}.map (sMid.{u}.comp bAmb.{u})

/-- The remaining reduction. -/
abbrev rRed : Mid.{u} →+* Red.{u} := Ideal.Quotient.mk _

/-- The kernel of `sMid : Amb → Mid` is the extension of `(t²)` to `Amb`. -/
theorem ker_sMid : RingHom.ker sMid.{u} = Ksq.{u}.map bAmb.{u} := Ideal.mk_ker

/-- The kernel of the algebra map `Amb → Mid` is the extension of `(t²)` to `Amb`. -/
theorem ker_algebraMap_Mid :
    RingHom.ker (algebraMap Amb.{u} Mid.{u}) = Ksq.{u}.map bAmb.{u} := Ideal.mk_ker

/-- The kernel of `rRed : Mid → Red` is the extension of `(t)` to `Mid`. -/
theorem ker_rRed : RingHom.ker rRed.{u} = Lnil.{u}.map (sMid.{u}.comp bAmb.{u}) := Ideal.mk_ker


/-- `ε̄`, the image of `ε` in `Mid`. -/
abbrev epsMid : Mid.{u} := sMid.{u} eps.{u}

/-- `t̄`, the image of `t` in `Mid`. -/
abbrev tMid : Mid.{u} := sMid.{u} (bAmb.{u} t.{u})

/-- The image of `t̄` in `Red` is zero. -/
theorem rRed_tMid : rRed.{u} tMid.{u} = 0 := by
  rw [← RingHom.mem_ker, ker_rRed]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)

/-- The lift on which `ε` acts as `0`. It lifts across the square-zero step, to `Amb/(ε)`. -/
abbrev Nzero : Type u := Mid.{u} ⧸ Ideal.span {epsMid.{u}}

/-- The lift on which `ε` acts as `t`. It does not lift. -/
abbrev Nshift : Type u := Mid.{u} ⧸ Ideal.span {epsMid.{u} - tMid.{u}}

/-- `Amb/(ε)`, the lift of `Nzero` across the square-zero step. -/
abbrev W0 : Type u := Amb.{u} ⧸ Ideal.span {eps.{u}}

/-- The retraction of `Amb` onto its base, killing `ε`. -/
abbrev projAmb : Amb.{u} →ₐ[Base.{u}] Base.{u} :=
  AdjoinRoot.liftAlgHom (X ^ 2 : Polynomial Base.{u}) (AlgHom.id Base.{u} Base.{u}) 0 (by simp)

/-- `projAmb` sends `ε` to `0`. -/
theorem projAmb_eps : projAmb.{u} eps.{u} = 0 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- `projAmb : Amb → Base` is surjective. -/
theorem surjective_projAmb : Function.Surjective projAmb.{u} :=
  fun x => ⟨bAmb.{u} x, projAmb.{u}.commutes x⟩

/-- The kernel of `projAmb : Amb → Base` is the ideal `(ε)`. -/
theorem ker_projAmb :
    RingHom.ker (projAmb.{u} : Amb.{u} →+* Base.{u}) = Ideal.span {eps.{u}} := by
  refine le_antisymm (fun z hz => ?_) ?_
  · obtain ⟨p, rfl⟩ : ∃ p, AdjoinRoot.mk (X ^ 2 : Polynomial Base.{u}) p = z :=
      AdjoinRoot.induction_on _ z fun p => ⟨p, rfl⟩
    have hval : projAmb.{u} (AdjoinRoot.mk _ p) = p.coeff 0 := by
      rw [AdjoinRoot.liftAlgHom_mk]
      simp
    have h0 : p.coeff 0 = 0 := by
      rw [← hval]
      exact RingHom.mem_ker.mp hz
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    refine Ideal.mem_span_singleton.mpr ⟨AdjoinRoot.mk _ q, ?_⟩
    rw [hq, map_mul]
    rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact projAmb_eps

/-- `Amb/(ε) ≅ Base`, as `Base`-algebras. -/
def equivW0 : W0.{u} ≃ₐ[Base.{u}] Base.{u} :=
  (Ideal.quotientEquivAlgOfEq Base.{u} ker_projAmb.{u}.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective surjective_projAmb.{u})

/-- `W0 = Amb/(ε)` is flat over the base for the module structure given by restriction of scalars
along `bAmb`. -/
theorem flat_compHom_W0 :
    @Module.Flat Base.{u} W0.{u} _ _ (Module.compHom W0.{u} bAmb.{u}) := by
  have htow : ∀ (a : Base.{u}) (x : W0.{u}), (bAmb.{u} a) • x = a • x := by
    intro a x
    refine Quotient.inductionOn' x fun z => ?_
    simp only [Submodule.Quotient.mk''_eq_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [smul_eq_mul]
    exact (Algebra.smul_def a z).symm
  have h : Module.compHom W0.{u} bAmb.{u} = (inferInstance : Module Base.{u} W0.{u}) :=
    Module.ext' _ _ htow
  rw [h]
  exact Module.Flat.of_linearEquiv equivW0.{u}.toLinearEquiv


/-- **The flatness step.** Over `ℤ/8` a flat module killed by `t²` is zero: by the equational
criterion the relation `t²·m = 0` is trivial, so `m ∈ tW`; iterating, `m ∈ t²W = 0`. -/
theorem eq_zero_of_flat_of_t_sq_smul_eq_zero {W : Type u} [AddCommGroup W]
    [Module Base.{u} W] [Module.Flat Base.{u} W]
    (h : ∀ m : W, (t.{u} ^ 2) • m = 0) (m : W) : m = 0 := by
  have key : ∀ x : W, ∃ z : W, x = t.{u} • z := by
    intro x
    obtain ⟨k, a, y, hx, hf⟩ :=
      Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := Base.{u}) (M := W)
        (ι := Unit) (f := fun _ => (t.{u} ^ 2)) (x := fun _ => x) (by simpa using h x)
    have hdvd : ∀ j, ∃ c : Base.{u}, a () j = t.{u} * c := by
      intro j
      have hj := hf j
      simp only [Finset.univ_unique, Finset.sum_singleton] at hj
      exact t_dvd_of_t_sq_mul_eq_zero hj
    choose c hc using hdvd
    refine ⟨∑ j, c j • y j, ?_⟩
    have hx' : x = ∑ j, a () j • y j := hx ()
    rw [hx', Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hc j, mul_smul]
  obtain ⟨z, hz⟩ := key m
  obtain ⟨w, hw⟩ := key z
  rw [hz, hw, smul_smul, ← pow_two]
  exact h w

/-- `Nshift` is `ℤ/4`, in particular not zero: the ring map `Amb → ℤ/4` sending `ε` and `t`
both to `2` factors through it. -/
theorem nontrivial_Nshift : Nontrivial Nshift.{u} := by
  have h48 : (4 : ℕ) ∣ 8 := by norm_num
  set ψ₀ : Base.{u} →+* ZMod 4 :=
    (ZMod.castHom h48 (ZMod 4)).comp (ULift.ringEquiv : Base.{u} ≃+* ZMod 8).toRingHom with hψ₀
  have hroot : (X ^ 2 : Polynomial Base.{u}).eval₂ ψ₀ 2 = 0 := by
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
    decide
  set ψ : Amb.{u} →+* ZMod 4 := AdjoinRoot.lift ψ₀ 2 hroot with hψ
  have hψeps : ψ eps.{u} = 2 := AdjoinRoot.lift_root hroot
  have hψt : ψ (bAmb.{u} t.{u}) = 2 := by
    have hrt : (ULift.ringEquiv : Base.{u} ≃+* ZMod 8).toRingHom t.{u} = 2 := ringEquiv_t.{u}
    rw [hψ, show bAmb.{u} t.{u} = AdjoinRoot.of _ t.{u} from rfl, AdjoinRoot.lift_of hroot, hψ₀,
      RingHom.comp_apply, hrt]
    exact map_ofNat _ 2
  have hker1 : Ksq.{u}.map bAmb.{u} ≤ RingHom.ker ψ := by
    rw [Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff,
      SetLike.mem_coe, RingHom.mem_ker, map_pow, map_pow, hψt]
    decide
  set χ₁ : Mid.{u} →+* ZMod 4 := Ideal.Quotient.lift _ ψ hker1 with hχ₁
  have hχ₁eps : χ₁ epsMid.{u} = 2 := by
    rw [hχ₁, epsMid]; exact (Ideal.Quotient.lift_mk _ _ _).trans hψeps
  have hχ₁t : χ₁ tMid.{u} = 2 := by rw [hχ₁, tMid]; exact (Ideal.Quotient.lift_mk _ _ _).trans hψt
  have hker2 : Ideal.span {epsMid.{u} - tMid.{u}} ≤ RingHom.ker χ₁ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
      hχ₁eps, hχ₁t, sub_self]
  set χ : Nshift.{u} →+* ZMod 4 := Ideal.Quotient.lift _ χ₁ hker2 with hχ
  refine ⟨⟨1, 0, fun hcon => ?_⟩⟩
  have h1 : χ (1 : Nshift.{u}) = χ (0 : Nshift.{u}) := congrArg χ hcon
  rw [map_one, map_zero] at h1
  exact absurd h1 (by decide)


/-- The ideals `(ε̄)` and `(ε̄ − t̄)` of `Mid` have the same extension to `Red`. -/
theorem map_span_eq :
    (Ideal.span {epsMid.{u}}).map (algebraMap Mid.{u} Red.{u}) =
      (Ideal.span {epsMid.{u} - tMid.{u}}).map (algebraMap Mid.{u} Red.{u}) := by
  have h : (algebraMap Mid.{u} Red.{u}) tMid.{u} = 0 := rRed_tMid.{u}
  rw [Ideal.map_span (algebraMap Mid.{u} Red.{u}) {epsMid.{u}},
    Ideal.map_span (algebraMap Mid.{u} Red.{u}) {epsMid.{u} - tMid.{u}}]
  simp only [Set.image_singleton, map_sub, h, sub_zero]

/-- The two lifts have isomorphic reductions: `ε` and `ε − t` generate the same ideal of `Red`,
because `t` dies there. -/
def matchingEquiv :
    (Red.{u} ⊗[Mid.{u}] Nzero.{u}) ≃ₗ[Mid.{u}] (Red.{u} ⊗[Mid.{u}] Nshift.{u}) :=
  (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot Red.{u}
        (Ideal.span {epsMid.{u}})).symm.trans
      ((Ideal.quotientEquivAlgOfEq Red.{u} map_span_eq.{u}).trans
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Red.{u}
          (Ideal.span {epsMid.{u} - tMid.{u}})))).toLinearEquiv).restrictScalars Mid.{u}

/-- **The lift on which `ε` acts as zero does lift**, to `Amb/(ε)`. -/
theorem hasFlatModuleLift_Nzero : HasFlatModuleLift bAmb.{u} sMid.{u} Nzero.{u} := by
  have hmap : Ideal.span {epsMid.{u}} =
      (Ideal.span {eps.{u}}).map (algebraMap Amb.{u} Mid.{u}) := by
    rw [Ideal.map_span (algebraMap Amb.{u} Mid.{u}) {eps.{u}}, Set.image_singleton]
    rfl
  refine ⟨ModuleCat.of Amb.{u} W0.{u}, flat_compHom_W0.{u}, ⟨?_⟩⟩
  exact ((Ideal.quotientEquivAlgOfEq Mid.{u} hmap).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Mid.{u}
      (Ideal.span {eps.{u}}))).symm.toLinearEquiv

/-- On `Nshift` the element `ε` acts as `t`. -/
theorem epsMid_smul_Nshift (y : Nshift.{u}) : epsMid.{u} • y = tMid.{u} • y := by
  refine Quotient.inductionOn' y fun z => ?_
  simp only [Submodule.Quotient.mk''_eq_mk, ← Submodule.Quotient.mk_smul]
  refine (Submodule.Quotient.eq _).mpr ?_
  have h : epsMid.{u} • z - tMid.{u} • z = (epsMid.{u} - tMid.{u}) * z := by
    rw [smul_eq_mul, smul_eq_mul, sub_mul]
  rw [h]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- **The lift on which `ε` acts as `t` does not lift.** If `L` were an `A'`-flat `Amb`-module
with `Mid ⊗ L ≅ Nshift`, then `ε` would act on `L` as `t` modulo `t²L`, so `ε² = 0` would force
`t²L = 0`, and flatness over `ℤ/8` would make `L`, hence `Nshift`, zero. -/
theorem not_hasFlatModuleLift_Nshift : ¬ HasFlatModuleLift bAmb.{u} sMid.{u} Nshift.{u} := by
  rintro ⟨W, hWflat, ⟨e0⟩⟩
  have e : (Mid.{u} ⊗[Amb.{u}] (W : Type u)) ≃ₗ[Mid.{u}] Nshift.{u} := e0
  set S : Amb.{u} := bAmb.{u} (t.{u} ^ 2) with hS
  set T : Amb.{u} := bAmb.{u} t.{u} with hT
  have hTT : T * T = S := by rw [hT, hS, ← map_mul, ← pow_two]
  have hTS : T * S = 0 := by
    rw [hT, hS, ← map_mul, show t.{u} * t.{u} ^ 2 = t.{u} ^ 3 by ring, t_pow_three, map_zero]
  have hST : S * T = 0 := by rw [mul_comm]; exact hTS
  have hSS : S * S = 0 := by rw [hS, ← map_mul, t_sq_mul_t_sq, map_zero]
  -- `ε` acts as `t` on `Mid ⊗[Amb] W`
  have hact : ∀ w : Mid.{u} ⊗[Amb.{u}] (W : Type u), epsMid.{u} • w = tMid.{u} • w := by
    intro w
    refine e.injective ?_
    rw [map_smul, map_smul, epsMid_smul_Nshift]
  -- hence `ε·m − t·m ∈ t²W` for every `m`
  have hstep : ∀ m : (W : Type u), ∃ y : (W : Type u), eps.{u} • m - T • m = S • y := by
    intro m
    have hsurj : Function.Surjective (algebraMap Amb.{u} Mid.{u}) :=
      Ideal.Quotient.mk_surjective
    have h1 : (TensorProduct.mk Amb.{u} Mid.{u} (W : Type u) 1) (eps.{u} • m - T • m) = 0 := by
      have hl : ∀ a : Amb.{u}, (1 : Mid.{u}) ⊗ₜ[Amb.{u}] (a • m) =
          (algebraMap Amb.{u} Mid.{u} a) ⊗ₜ[Amb.{u}] m := by
        intro a
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      have h2 := hact ((1 : Mid.{u}) ⊗ₜ[Amb.{u}] m)
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
        mul_one, mul_one] at h2
      show (1 : Mid.{u}) ⊗ₜ[Amb.{u}] (eps.{u} • m - T • m) = 0
      rw [TensorProduct.tmul_sub, hl, hl, sub_eq_zero]
      exact h2
    rw [← LinearMap.mem_ker, TensorProduct.ker_mk_one hsurj, ker_algebraMap_Mid, Ideal.map_span,
      Set.image_singleton, Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact ⟨y, hy.symm⟩
  -- the obstruction computation
  have hzero : ∀ m : (W : Type u), S • m = 0 := by
    intro m
    obtain ⟨y, hy⟩ := hstep m
    obtain ⟨y', hy'⟩ := hstep y
    have hem : eps.{u} • m = T • m + S • y := by rw [← hy]; abel
    have hey : eps.{u} • y = T • y + S • y' := by rw [← hy']; abel
    have h0 : (eps.{u} * eps.{u}) • m = 0 := by rw [← pow_two, eps_sq, zero_smul]
    have key : (eps.{u} * eps.{u}) • m = S • m := by
      rw [mul_smul, hem, smul_add, smul_smul, smul_smul, mul_comm eps.{u} T,
        mul_comm eps.{u} S, ← smul_smul, ← smul_smul, hem, hey, smul_add, smul_add,
        smul_smul, smul_smul, smul_smul, smul_smul, hTT, hTS, hST, hSS]
      simp
    rw [key] at h0
    exact h0
  -- flatness kills `W`
  have hW : ∀ m : (W : Type u), m = 0 := by
    intro m
    exact @eq_zero_of_flat_of_t_sq_smul_eq_zero.{u} (W : Type u) _
      (Module.compHom (W : Type u) bAmb.{u}) hWflat hzero m
  -- so `Nshift` is zero, which it is not
  have : Subsingleton (Mid.{u} ⊗[Amb.{u}] (W : Type u)) := by
    refine ⟨fun x y => ?_⟩
    have hz : ∀ w : Mid.{u} ⊗[Amb.{u}] (W : Type u), w = 0 := by
      intro w
      induction w with
      | zero => rfl
      | add a b ha hb => rw [ha, hb, add_zero]
      | tmul c n => rw [hW n, TensorProduct.tmul_zero]
    rw [hz x, hz y]
  have hsub : Subsingleton Nshift.{u} := e.toEquiv.symm.injective.subsingleton
  exact (not_subsingleton_iff_nontrivial.mpr nontrivial_Nshift.{u}) hsub

end ObstructionWitness

/-- **The hypothesis the source's induction needs is unsatisfiable.** -/
theorem not_obstructionIndependentOfLift : ¬ ObstructionIndependentOfLift.{u} := by
  intro h
  refine ObstructionWitness.not_hasFlatModuleLift_Nshift.{u} ?_
  exact h ObstructionWitness.Base.{u} ObstructionWitness.Amb.{u} ObstructionWitness.Mid.{u}
    ObstructionWitness.Red.{u} ObstructionWitness.bAmb.{u} ObstructionWitness.sMid.{u}
    ObstructionWitness.rRed.{u} ObstructionWitness.Ksq.{u} ObstructionWitness.Lnil.{u}
    Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective ObstructionWitness.Ksq_sq.{u}
    ObstructionWitness.isNilpotent_Lnil.{u} ObstructionWitness.ker_sMid.{u}
    ObstructionWitness.ker_rRed.{u} ObstructionWitness.flat_compHom_Amb.{u}
    ObstructionWitness.Nzero.{u} _ _ ObstructionWitness.Nshift.{u} _ _
    ⟨ObstructionWitness.matchingEquiv.{u}⟩ ObstructionWitness.hasFlatModuleLift_Nzero.{u}


/-- **The reduction theorem: one step of the source's omitted induction, with its missing input
named.** Fix a chain `A' → A'' → A` of surjections whose first step is square-zero, realised on
the two thickenings as `P' → P'' → P` and `Q' → Q'' → Q`; this is the generic step of the tower
of quotients `A' → A'/Iⁿ⁻¹ → … → A'/I = A` that `Deformation.squareZero_devissage` produces.
Suppose
* `M''` is a lift of `M` at the intermediate stage — what the inductive hypothesis supplies;
* `N₀` has an `A'`-flat `Q'`-lift — what the forward implication
  `Deformation.HasFlatModuleLift.baseChange` supplies from clause (2);
* `N₀` and `Q'' ⊗_{P''} M''` have isomorphic reductions to `Q` — both are lifts of the same
  `Q`-module;
* the square-zero converse holds at the step `A' → A''` for the module `Q'' ⊗_{P''} M''`.

Then `M` has an `A'`-flat lift across the whole nilpotent thickening. The one thing the chain
needs beyond the square-zero case is `Deformation.ObstructionIndependentOfLift`, used exactly
once, to pass from the lift of `N₀` to a lift of `Q'' ⊗_{P''} M''`: the square-zero case
supplies non-emptiness of the two lift sets and never a *matching* of lifts. Everything else is
`Deformation.hasFlatModuleLift_comp`.

So this theorem is the source's argument with its omitted step isolated — and that step is
unsatisfiable, by `Deformation.not_obstructionIndependentOfLift`. The route the source takes to
the nilpotent case is therefore closed, not merely untried. -/
theorem hasFlatModuleLift_of_obstructionIndependentOfLift
    (hind : ObstructionIndependentOfLift.{u})
    {A' P' P'' P Q' Q'' Q : Type u} [CommRing A'] [CommRing P'] [CommRing P''] [CommRing P]
    [CommRing Q'] [CommRing Q''] [CommRing Q]
    (a : A' →+* P') (p₁ : P' →+* P'') (p₂ : P'' →+* P)
    (b : A' →+* Q') (s₁ : Q' →+* Q'') (s₂ : Q'' →+* Q) (u'' : P'' →+* Q'')
    (K L : Ideal A')
    (hs₁ : Function.Surjective s₁) (hs₂ : Function.Surjective s₂)
    (hK : K ^ 2 = ⊥) (hL : IsNilpotent L)
    (hkers₁ : RingHom.ker s₁ = K.map b) (hkers₂ : RingHom.ker s₂ = L.map (s₁.comp b))
    (hflatQ' : @Module.Flat A' Q' _ _ (Module.compHom Q' b))
    (M : Type u) [AddCommGroup M] [Module P M]
    (M'' : Type u) [AddCommGroup M''] [Module P'' M'']
    (N₀ : Type u) [AddCommGroup N₀] [Module Q'' N₀]
    (hM : letI : Algebra P'' P := p₂.toAlgebra
      Nonempty ((P ⊗[P''] M'') ≃ₗ[P] M))
    (hN₀ : HasFlatModuleLift b s₁ N₀)
    (hmatch : letI : Algebra Q'' Q := s₂.toAlgebra
      letI : Algebra P'' Q'' := u''.toAlgebra
      Nonempty ((Q ⊗[Q''] N₀) ≃ₗ[Q''] (Q ⊗[Q''] (Q'' ⊗[P''] M''))))
    (hsq : letI : Algebra P'' Q'' := u''.toAlgebra
      HasFlatModuleLift b s₁ (Q'' ⊗[P''] M'') → HasFlatModuleLift a p₁ M'') :
    HasFlatModuleLift a (p₂.comp p₁) M := by
  let : Algebra P'' Q'' := u''.toAlgebra
  refine hasFlatModuleLift_comp a p₁ p₂ M M'' hM (hsq ?_)
  exact hind A' Q' Q'' Q b s₁ s₂ K L hs₁ hs₂ hK hL hkers₁ hkers₂ hflatQ'
    N₀ _ _ (Q'' ⊗[P''] M'') _ _ hmatch hN₀


end Deformation

end
