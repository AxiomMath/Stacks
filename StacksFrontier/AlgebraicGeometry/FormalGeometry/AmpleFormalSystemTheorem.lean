module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicClosedSubschemeRigidity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerTransitionKernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemLineBundle
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemTowerComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization

/-!
# Grothendieck's algebraization theorem

This file states and proves [Stacks, Tag 089A] as one statement, with the theorem's own
hypotheses and the whole of its conclusion.

Let `A` be a Noetherian ring complete with respect to an ideal `I`, write `S = Spec A` and
`Sₙ = Spec (A / Iⁿ)`, and let

```
  X₀ --i₀--> X₁ --i₁--> X₂ --> ⋯
  |          |          |
  S₀ ------> S₁ ------> S₂ --> ⋯
```

be a commutative diagram of schemes with cartesian squares, together with invertible modules
`ℒₙ` on `Xₙ` and isomorphisms `φₙ : iₙ^* ℒₙ₊₁ ≅ ℒₙ`. If `X₀ ⟶ S₀` is proper and `ℒ₀` is ample on
`X₀`, then there are a proper morphism `X ⟶ S`, an ample invertible `𝒪_X`-module `ℒ`, morphisms
`kₙ : Xₙ ⟶ X` compatible with the `iₙ` exhibiting each `Xₙ` as `X ×_S Sₙ`, and isomorphisms
`ℒₙ ≅ ℒ|_{Xₙ}` compatible with the `φₙ`.

The index is shifted by one from the source's: `n` here is the source's `n + 1`, so the source's
`X₁` and `ℒ₁` are `X 0` and `L 0`.

## Main results

* `Stacks.AmpleFormalSystemTheorem.exists_isProper_isAmple_of_isAmple` — the theorem.
* `Stacks.AmpleFormalSystemTheorem.surjective_transitionSections_of_isZero_h1` — the long exact
  sequence step of the source's proof: the vanishing of `H¹` of the twisted transition ideal
  makes the transition maps of the tower `(ℒₙ ^⊗ d)` surjective on global sections.

## Main definitions

* `Stacks.AmpleFormalSystemTheorem.powTransitionIso` — the `d`-th tensor power of `φₙ`, which is
  the transition isomorphism of the tower `(ℒₙ ^⊗ d)` the lifting step runs along.
* `Stacks.AmpleFormalSystemTheorem.AdicTowerModuleAlgebraization`,
  `Stacks.AmpleFormalSystemTheorem.AdicTowerInvertibility`,
  `Stacks.AmpleFormalSystemTheorem.AdicTowerAmpleness` — the three inputs to the sheaf half of
  the conclusion that this library does not carry, each stated for an arbitrary algebraization of
  the given tower, so that none of them presupposes the one the theorem produces.
* `Stacks.AmpleFormalSystemTheorem.AdicCanonicalTowerModuleAlgebraization` — the first of those
  three read off the *canonical* tower `Xₙ = X ×_{Spec A} Sₙ` alone;
  `adicTowerModuleAlgebraization_of_canonicalTower` deduces `AdicTowerModuleAlgebraization` from
  it, so `hequiv` no longer mentions the tower the theorem is given.

## The two halves

The geometric half — the proper `X ⟶ S` and the cartesian identifications `Xₙ ≅ X ×_S Sₙ` — is
`Stacks.AmpleFormalSystemAlgebraization.exists_isProjectiveMorphism_of_isAmple`, the source's own
argument: the embedding step at the bottom of the tower, the inductive lifting of its sections,
and the closing appeal to [Stacks, Tag 0899]. It delivers `X ⟶ S` **H-projective**, since
[Stacks, Tag 0899] algebraizes the tower to a closed subscheme of the ambient `ℙᴺ_S`; properness
is `AlgebraicGeometry.isProper_of_isProjectiveMorphism`.

The sheaf half — the ample invertible `ℒ` with `ℒₙ ≅ ℒ|_{Xₙ}` compatibly with the `φₙ` — is
`Stacks.AmpleFormalSystemLineBundle.exists_isAmple_of_restriction_isEquivalence`, which
algebraizes the system `(ℒₙ, φₙ)` itself. The source does not say how `ℒ` is obtained: its proof
only ever sees `ℒₙ ^⊗ d`, and [Stacks, Tag 0899] produces no module at all.

## The hypotheses this library does not carry

[Stacks, Tag 0899] rests on two inputs. The second of them, adic rigidity over a proper base —
the way [Stacks, Tag 0A42] enters — **is no longer a hypothesis**: it is
`Stacks.AdicClosedSubschemeRigidity.adicRigidity`
(`FormalGeometry/AdicClosedSubschemeRigidity.lean`), proved outright from the faithfulness half
of [Stacks, Tag 0883], which `Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper`
(`FormalGeometry/CompletionFunctor/FullyFaithfulComplete.lean:294`) carries unconditionally for a
proper morphism over a Noetherian adically complete base. Only faithfulness is needed, so nothing
there rests on [Stacks, Tag 088C]; `adicMorphismRigidity_of_adicRigidity` reduces it to the shape
[Stacks, Tag 0899] consumes.

`halg` is the first input: Grothendieck existence for finite sheaves of algebras, which is how
[Stacks, Tag 09ZT] enters, reduced to exactly that one Prop by
`adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization`, so that the ambient
projective space of the proof contributes no hypothesis of its own. It is used only at
`Stacks.AmpleFormalSystemAmbient.ambientHom A N`, which is projective, and the *module* half of
Grothendieck existence is available there unconditionally
(`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing`,
[Stacks, Tag 0885], and
`AlgebraicGeometry.isEquivalence_completionFunctorProperOver_of_isProjective` for
[Stacks, Tag 088E]); what is missing is the *algebra-structure* step,
`AlgebraicGeometry.AlgebraStructureOnAlgebraization`, which has no carrier, together with
`AlgebraicGeometry.UnderlyingModuleAdicTransitionPullback` and the essential surjectivity
of `AlgebraicGeometry.adicThickeningCompletionFunctor`. The last of those is the same
functor-comparison gap as `hequiv` below.

`hvan` is the vanishing of the second paragraph of the source's proof, in arbitrarily large
degree `d`: the `H¹` on `Xₙ₊₁` of the ideal sheaf of `iₙ` twisted by `ℒₙ₊₁ ^⊗ d`. It is the only
thing the geometric half still needs — `surjective_transitionSections_of_isZero_h1` turns it into
the surjectivity of the transition maps on global sections that the lifting step consumes, so the
lifting is no longer conditional on an unexplained surjectivity. The downstairs form of the same
vanishing, on `X₀`, is `Stacks.AdicTower.UniformTwistVanishing`
(`FormalGeometry/AdicTowerTransitionKernelVanishing.lean:69`), and
`Stacks.AdicTower.pushforwardTransitionKernelIso`
(`FormalGeometry/AdicTowerTransitionKernel.lean:372`) identifies the ideal sheaf of `iₙ` with the
pushforward of the transition kernel `𝓕ₙ = Ker(𝒪_{Xₙ₊₁} ⟶ 𝒪_{Xₙ})` from `X₀`. Two things are
missing between them.

* The graded `𝒪_{X₀}`-algebra `⨁ₙ 𝓕ₙ` over `⨁ₙ Iⁿ/Iⁿ⁺¹` that
  `Stacks.AdicTower.uniformTwistVanishing_of_isZero_pieceTwistCohomology` asks for, together with
  [Stacks, Tag 0897] part (2) for it. The library's unconditional carrier of that vanishing,
  `Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_isProper`
  (`FormalGeometry/CompletionProjectiveEquivalenceAuxEpiAssembly.lean:129`), is stated for the
  associated graded of `I · 𝒪_X` on a **single** scheme `X` proper over `Spec A`, which is not
  the graded algebra needed here; and the general carrier
  `Stacks.AlgebraicGeometry.GradedProperCohomology.exists_isZero_pieceTwistCohomology`
  still carries the base-change comparison as a hypothesis. For the same reason
  [Stacks, Tag 0884] — proved outright in this library as
  `Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule`
  (`FormalGeometry/CoherentAdicSystem/TransitionKernelTwistVanishing.lean:347`) — does **not**
  apply: it is stated for a `Stacks.Coherent.CoherentAdicSystems` on one scheme already proper
  over `Spec A`, and the tower `Xₙ` has no such scheme until this theorem is proved.
* The projection formula for the twist along the closed immersion `X₀ ⟶ Xₙ₊₁`. The comparison of
  cohomology itself is *not* missing: [Stacks, Tag 089W] is unconditional in this library, both in
  the spelling used here (`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`,
  `AlgebraicGeometry/AffineCohomologyComparison/Basic.lean:194`) and in the `Hgroup` spelling. The
  projection formula is proved only at the level of ringed topoi
  (`Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isClosedImmersion`,
  `Algebra/Category/ModuleCat/Sheaf/PushforwardTensorMap.lean:372`); in the scheme-level
  `TensorStalkRingedSpace.tensorSheaf` spelling only the map is constructed, and
  `AlgebraicGeometry/ProjectionFormulaMap/AmpleCriterion.lean:45` records that
  [Stacks, Tag 0FZE] is not proved there.

`hequiv`, `hinvertible` and `hampleX` are the three inputs to the sheaf half, described at
`Stacks.AmpleFormalSystemLineBundle.exists_isAmple_of_restriction_isEquivalence`.

`hequiv` is Grothendieck existence along the tower, [Stacks, Tag 088F]. Two things about it have
changed, and what is left of it is purely formal.

First, **the tower is no longer the obstacle.** `hequiv` is now reduced to the *canonical* tower:
`AdicCanonicalTowerModuleAlgebraization` asks only that
`Stacks.CoherentTower.restriction` along `Xₙ = X ×_{Spec A} Sₙ`
(`AlgebraicGeometry.adicBaseChange`) be an equivalence, and
`adicTowerModuleAlgebraization_of_canonicalTower` deduces `hequiv` from it. The transport is
`Stacks.AmpleFormalSystemTowerComparison.isEquivalence_restriction`
(`FormalGeometry/AmpleFormalSystemTowerComparison.lean:300`), which carries an equivalence along
the comparison isomorphisms `cₙ : Xₙ ≅ X ×_{Spec A} Sₙ` that the universal property of the fibre
product provides; its mathematical content is the coherence identity
`Stacks.AmpleFormalSystemTowerComparison.pullbackCoherence`
(`StacksFrontier/AlgebraicGeometry/Spaces/AdicFiniteAlgebraization/TowerComparison.lean:178`), Mathlib's
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` applied twice.

Second, **the mathematics behind the canonical statement is all in place.** Because the geometric
half delivers an H-projective `X ⟶ S`, all three Props are stated for an H-projective `fX`, and
for such an `fX` this library proves [Stacks, Tag 088C] outright:
`AlgebraicGeometry.IsProjectiveMorphism.isProjective`
([Stacks, Tag 01W9], `AlgebraicGeometry/QuasiProjective/HProjective.lean:139`) turns
H-projectivity into projectivity, and
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing`
(`FormalGeometry/CompletionProjectiveEquivalence.lean:147`, [Stacks, Tag 0885]) is unconditional
under exactly that hypothesis; [Stacks, Tag 088E] is
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_holds`
(`FormalGeometry/CompletionProper/AdicUnitConditionDescent.lean`), at the source's hypotheses;
and the identification of 088E's category `Stacks.Coherent.CoherentAdicSystems` with the systems
on the honest fibre products — the content 088F adds — is no longer missing either: it is
`AlgebraicGeometry.adicThickeningCoherentAdicSystemsEquivalence`, for a proper `f`.

What is **not** done is the last link, and it is bookkeeping rather than mathematics:
`AlgebraicGeometry.adicThickeningCompletionFunctor` and `Stacks.CoherentTower.restriction` at the
canonical tower have the same objects — the pullbacks along `Xₙ ⟶ X` — and literally the same
transition isomorphisms, `AlgebraicGeometry.adicThickeningCompletionNatIso` and
`Stacks.CoherentTower.restrictionNatIso` being the same composite of
`Scheme.Modules.pullbackComp` with `Scheme.Modules.pullbackCongr`; but the two are not *cheaply*
definitionally equal. `Scheme.Modules` is a semireducible `def`, and a `rfl` between the two
functors, an objectwise `Iso.refl`, and an objectwise comparison closed by `dsimp` all exhaust
first the elaborator's and then the kernel's heartbeat budget. Closing it needs a comparison
assembled by hand from the two definitions, and that is not carried out here. The two full
subcategories in the way — the proper-support condition on the modules and clause (3) on the
systems — are vacuous for a proper `f` and cost nothing
(`Stacks.Algebraization.hasProperSupport_of_isProper` and
`AlgebraicGeometry.AdicCoherentModuleSystem.ofIsProper`).

`hinvertible` and `hampleX` have no carrier at all. Nothing in this library derives invertibility
of a coherent module from invertibility of its restrictions to an adic tower; the ampleness
criteria of the shape "`k^* M` ample implies `M` ample" that the library does prove
([Stacks, Tag 09MS] at `AlgebraicGeometry/AmpleSurjectiveThickening/Basic.lean:336`,
[Stacks, Tag 09MW] at `AlgebraicGeometry/AmpleThickeningLimit/Basic.lean:144`,
[Stacks, Tag 0B5V] at `AlgebraicGeometry/AmpleFiniteSurjective/Basic.lean:727`) all require the
closed immersion to be surjective, which `k 0 : X₀ ⟶ X` is not — `X = Spec ℤ_p` over `A = ℤ_p`
is already a counterexample. The route the source's own argument suggests runs through
`isAmple_of_exists_isAmple_tensorPowModule` and the pullback of `𝒪(1)` along the closed immersion
into `ℙᴺ_S`, and identifying that pullback with `ℒ ^⊗ d` needs the full faithfulness half of
`hequiv`.

Each of the three is stated for an **arbitrary** H-projective `fX : X ⟶ Spec A` with an arbitrary
cartesian family `kₙ`, never for the one the geometric half produces; so none of them is the
conclusion in disguise.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.CoherentTower
open Stacks.AmpleFormalSystemAmbient

universe u

namespace Stacks.AmpleFormalSystemTheorem

variable (A : Type u) [CommRing A] (I : Ideal A)

/-! ### The two inputs of [Stacks, Tag 0899], reduced to the Props the library names -/

/-- **[Stacks, Tag 09ZT] in the shape [Stacks, Tag 0899] consumes it.** The hypothesis
`AlgebraicGeometry.AdicFiniteSystemAlgebraization` of
`AlgebraicGeometry.exists_closedImmersion_algebraization_of_isPullback` is the conclusion of
`AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem` with its existentials
regrouped, so the latter discharges it from the one Prop this library names for Grothendieck
existence for finite sheaves of algebras. -/
public lemma adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization
    [IsNoetherianRing A] [IsAdicComplete I A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (halg : AdicFiniteAlgebraAlgebraization A I f) :
    AdicFiniteSystemAlgebraization A I f := by
  intro Z j t hcart hfin hproper
  obtain ⟨W, g, hgfin, hgproper, k, hkcart, hkg⟩ :=
    exists_finite_algebraization_of_adicFiniteSystem A I f halg Z j t hcart hfin hproper
  exact ⟨W, g, k, hgfin, hgproper, hkcart, hkg⟩

/-- **The rigidity clause of [Stacks, Tag 0A42] in the shape [Stacks, Tag 0899] consumes it.**
`AlgebraicGeometry.AdicMorphismRigidity` is `AlgebraicGeometry.hom_ext_of_adicBaseChangeMap`,
which this library proves from the one Prop it names for adic rigidity over a proper base; the
finite-type and quasi-compactness clauses of `AdicMorphismRigidity` are not even needed. -/
public lemma adicMorphismRigidity_of_adicRigidity (hrig : AdicRigidity A I) :
    AdicMorphismRigidity A I := by
  intro P W fP fW hP hW _ _ a ha b hb h
  have := hP
  have := hW
  exact hom_ext_of_adicBaseChangeMap A I hrig fP fW a b ha hb h

/-! ### The three inputs to the sheaf half that this library does not carry -/

variable {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
  (i : ∀ n, Xn n ⟶ Xn (n + 1))

/-- **The unwinding of Grothendieck existence along the tower, [Stacks, Tag 088F].** For every
H-projective `fX : X ⟶ Spec A` and every family `kₙ : Xₙ ⟶ X`, compatible with the transitions and
exhibiting each `Xₙ` as `X ×_{Spec A} Sₙ`, restriction along the `kₙ` is an equivalence from the
coherent `𝒪_X`-modules onto the systems of coherent modules along the tower.

The hypothesis on `fX` is H-projectivity, not properness, because that is what the geometric half
delivers (`Stacks.AmpleFormalSystemAlgebraization.exists_isProjectiveMorphism_of_isAmple`) and it
is the hypothesis under which this library proves Grothendieck existence outright: for a
projective morphism the completion functor of [Stacks, Tag 0880] is an equivalence by
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing`
(`FormalGeometry/CompletionProjectiveEquivalence.lean:147`, [Stacks, Tag 0885], unconditional),
and H-projectivity gives projectivity by `AlgebraicGeometry.IsProjectiveMorphism.isProjective`
([Stacks, Tag 01W9]). What is still missing is only the *unwinding* — the identification of the
category that equivalence is stated against with the systems along the tower; see the module
documentation. -/
public def AdicTowerModuleAlgebraization [IsNoetherianRing A] : Prop :=
  ∀ {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) (_hfX : IsProjectiveMorphism fX)
    (k : ∀ n, Xn n ⟶ X)
    (hk : ∀ n, i n ≫ k (n + 1) = k n)
    (hkcart : ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n)),
    haveI := isProper_of_isProjectiveMorphism fX _hfX
    letI : ∀ n, IsLocallyNoetherian (Xn n) := fun n =>
      Stacks.AmpleFormalSystemLineBundle.isLocallyNoetherian_of_isPullback A I fX q k hkcart n
    (restriction i k hk).IsEquivalence

/-- **Grothendieck existence along the *canonical* adic tower.** For every H-projective
`fX : X ⟶ Spec A`, restriction along the tower of honest fibre products
`Xₙ = X ×_{Spec A} Sₙ = adicBaseChange A I fX n` is an equivalence onto the systems of coherent
modules along it.

This is the shape in which the library's Grothendieck existence lives: it says nothing about the
tower the theorem is given, only about the canonical one, and
`adicTowerModuleAlgebraization_of_canonicalTower` below deduces
`AdicTowerModuleAlgebraization` from it. -/
public def AdicCanonicalTowerModuleAlgebraization (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) : Prop :=
  ∀ {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) (hfX : IsProjectiveMorphism fX),
    haveI := isProper_of_isProjectiveMorphism fX hfX
    letI : ∀ n : ℕ, IsLocallyNoetherian (adicBaseChange A I fX n) := fun n =>
      Stacks.AmpleFormalSystemLineBundle.isLocallyNoetherian_of_isPullback A I fX
        (fun m => pullback.snd fX (adicThickeningι A I m))
        (fun m => pullback.fst fX (adicThickeningι A I m))
        (fun m => IsPullback.of_hasPullback fX (adicThickeningι A I m)) n
    (restriction (adicBaseChangeSucc A I fX)
      (fun n => pullback.fst fX (adicThickeningι A I n))
      (adicBaseChangeSucc_fst A I fX)).IsEquivalence

/-- **`hequiv` reduces to the canonical tower.** The tower of [Stacks, Tag 089A] is cartesian
over the thickenings, so the universal property of the fibre product gives isomorphisms
`cₙ : Xₙ ≅ X ×_{Spec A} Sₙ` compatible with the transitions and with the morphisms to `X`;
`Stacks.AmpleFormalSystemTowerComparison.isEquivalence_restriction` then transports the
equivalence from the canonical tower to the given one. -/
public lemma adicTowerModuleAlgebraization_of_canonicalTower [IsNoetherianRing A]
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (hcanon : AdicCanonicalTowerModuleAlgebraization A I) :
    AdicTowerModuleAlgebraization A I q i := by
  intro X fX hfX k hk hkcart
  have := isProper_of_isProjectiveMorphism fX hfX
  let : ∀ n : ℕ, IsLocallyNoetherian (Xn n) := fun n =>
    Stacks.AmpleFormalSystemLineBundle.isLocallyNoetherian_of_isPullback A I fX q k hkcart n
  let : ∀ n : ℕ, IsLocallyNoetherian (adicBaseChange A I fX n) := fun n =>
    Stacks.AmpleFormalSystemLineBundle.isLocallyNoetherian_of_isPullback A I fX
      (fun m => pullback.snd fX (adicThickeningι A I m))
      (fun m => pullback.fst fX (adicThickeningι A I m))
      (fun m => IsPullback.of_hasPullback fX (adicThickeningι A I m)) n
  have hc : ∀ n : ℕ, i n ≫ (hkcart (n + 1)).isoPullback.hom =
      (hkcart n).isoPullback.hom ≫ adicBaseChangeSucc A I fX n := fun n => by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, (hkcart (n + 1)).isoPullback_hom_fst, Category.assoc,
        adicBaseChangeSucc_fst, (hkcart n).isoPullback_hom_fst, hk n]
    · rw [Category.assoc, (hkcart (n + 1)).isoPullback_hom_snd, Category.assoc,
        (isPullback_adicBaseChangeSucc A I fX n).w, ← Category.assoc,
        (hkcart n).isoPullback_hom_snd, (hcart n).w]
  exact Stacks.AmpleFormalSystemTowerComparison.isEquivalence_restriction i
    (adicBaseChangeSucc A I fX) (fun n => (hkcart n).isoPullback.hom) k
    (fun n => pullback.fst fX (adicThickeningι A I n)) hc hk
    (adicBaseChangeSucc_fst A I fX) (fun n => (hkcart n).isoPullback_hom_fst)
    (fun n => inferInstance) (hcanon fX hfX)

/-- **A coherent module on an algebraization of the tower whose restrictions are all invertible
is invertible.** This is a statement about an H-projective `fX : X ⟶ Spec A` carrying a cartesian
family `kₙ` and nothing else; the system `(ℒₙ, φₙ)` does not enter it. -/
public def AdicTowerInvertibility : Prop :=
  ∀ {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)), IsProjectiveMorphism fX → ∀ k : ∀ n, Xn n ⟶ X,
    (∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n)) →
    ∀ M : X.Modules, _root_.SheafOfModules.IsCoherent.{u} M →
      (∀ n, IsInvertibleModule (Xn n) ((Scheme.Modules.pullback (k n)).obj M)) →
      IsInvertibleModule X M

/-- **An invertible module on an algebraization of the tower whose restriction to the closed
member is ample is ample.** Again a statement about `fX` and the family `kₙ` alone.
`Stacks.AmpleFormalSystemLineBundle.isAmple_of_exists_isAmple_tensorPowModule` reduces it to the
ampleness of a positive tensor power, which is the form the source's projective embedding
delivers. `fX` is H-projective here, again because that is what the geometric half delivers. -/
public def AdicTowerAmpleness : Prop :=
  ∀ {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)), IsProjectiveMorphism fX → ∀ k : ∀ n, Xn n ⟶ X,
    (∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n)) →
    ∀ (M : X.Modules) (hM : IsInvertibleModule X M),
      @IsAmple (Xn 0) ((Scheme.Modules.pullback (k 0)).obj M)
        (Stacks.AmpleFormalSystemLineBundle.isInvertibleModule_pullback (k 0) M hM) →
      @IsAmple X M hM

/-! ### The transition isomorphisms in degree `d`, and the long exact sequence step -/

variable (L : ∀ n, (Xn n).Modules) (hL : ∀ n, IsInvertibleModule (Xn n) (L n))
  (φ : ∀ n, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n)

/-- **The `d`-th tensor power of the transition isomorphism `φₙ`**, which is the transition
isomorphism of the tower `(ℒₙ ^⊗ d)` that the lifting step of [Stacks, Tag 089A] runs along:
pullback commutes with tensor powers of an invertible module
(`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`), and `φₙ` is then raised to the `d`-th
power (`Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso`). -/
public def powTransitionIso (d n : ℕ) :
    (Scheme.Modules.pullback (i n)).obj
        (letI := hL (n + 1); tensorPowModule (Xn (n + 1)) (L (n + 1)) (d : ℤ)) ≅
      (letI := hL n; tensorPowModule (Xn n) (L n) (d : ℤ)) :=
  letI := hL n
  letI := hL (n + 1)
  letI : IsInvertibleModule (Xn n) ((Scheme.Modules.pullback (i n)).obj (L (n + 1))) :=
    Stacks.AmpleFormalSystemLineBundle.isInvertibleModule_pullback (i n) (L (n + 1)) (hL (n + 1))
  Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (i n) (L (n + 1)) d ≪≫
    Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso (Xn n)
      ((Scheme.Modules.pullback (i n)).obj (L (n + 1))) (L n) (φ n) d

/-- **The long exact sequence step of the proof of [Stacks, Tag 089A].** If `H¹` of the ideal
sheaf of `iₙ` twisted by `ℒₙ₊₁ ^⊗ d` vanishes, then the transition map
`Γ(Xₙ₊₁, ℒₙ₊₁ ^⊗ d) ⟶ Γ(Xₙ, ℒₙ ^⊗ d)` of the tower is surjective.

The transitions `iₙ` are closed immersions because the squares are cartesian over the closed
immersions `Sₙ ⟶ Sₙ₊₁` (`Stacks.AdicTower.isClosedImmersion_transition`), so
`Stacks.AmpleSurjectiveThickening.surjective_pullbackGlobalSection_of_isZero_h1` applies; the
transition map of the tower is that restriction map followed by the bijection induced by
`powTransitionIso`. -/
public lemma surjective_transitionSections_of_isZero_h1
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n)) (d n : ℕ)
    (hvan : IsZero (((AlgebraicGeometry.moduleGlobalSections (Xn (n + 1))).rightDerived 1).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((Xn (n + 1)).toRingedSpace).presheaf, ((Xn (n + 1)).toRingedSpace).IsSheaf⟩).obj
          (Stacks.ClosedImmersion.idealSheaf (i n).toLRSHom.toShHom)).obj
        (letI := hL (n + 1); tensorPowModule (Xn (n + 1)) (L (n + 1)) (d : ℤ)))))) :
    Function.Surjective (Stacks.AmpleFormalSystemLifting.transitionSections i
      (fun m => letI := hL m; tensorPowModule (Xn m) (L m) (d : ℤ))
      (powTransitionIso i L hL φ d) n) := by
  have := Stacks.AdicTower.isClosedImmersion_transition q i hcart n
  let := hL (n + 1)
  have hsurj := Stacks.AmpleSurjectiveThickening.surjective_pullbackGlobalSection_of_isZero_h1
    (i n) (tensorPowModule (Xn (n + 1)) (L (n + 1)) (d : ℤ)) hvan
  intro y
  obtain ⟨x, hx⟩ := hsurj (Scheme.Modules.Hom.app (powTransitionIso i L hL φ d n).inv ⊤ y)
  refine ⟨x, ?_⟩
  rw [Stacks.AmpleFormalSystemLifting.transitionSections,
    Stacks.AmpleFormalSystemLifting.pullbackGlobalSections_eq_pullbackGlobalSection, hx]
  exact Stacks.AmpleFormalSystemEmbeddedTuple.app_hom_app_inv _ y

/-! ### The theorem -/

/-- **Grothendieck's algebraization theorem, [Stacks, Tag 089A].**

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `Xₙ` be a tower of
schemes over the thickenings `Sₙ = Spec (A / Iⁿ⁺¹)` whose squares are cartesian, and let `ℒₙ` be
invertible modules on the `Xₙ` with isomorphisms `φₙ : iₙ^* ℒₙ₊₁ ≅ ℒₙ`. Assume `X₀ ⟶ S₀` is
proper and `ℒ₀` is ample on `X₀`. Then there are a proper morphism `fX : X ⟶ Spec A`, an ample
invertible `𝒪_X`-module `ℒ`, morphisms `kₙ : Xₙ ⟶ X` with `iₙ ≫ kₙ₊₁ = kₙ` exhibiting every `Xₙ`
as `X ×_{Spec A} Sₙ`, and isomorphisms `ℒₙ ≅ ℒ|_{Xₙ}` compatible with the `φₙ`.

The conclusion is the tag's, whole, and the hypotheses on the data are the tag's own: `X₀ ⟶ S₀`
proper and `ℒ₀` ample, no restricted base and no special case. Five further inputs are carried
because this library does not prove them: `halg` for [Stacks, Tag 0899], `hvan` for
the vanishing of the second paragraph of the source's proof, and `hequiv`, `hinvertible` and
`hampleX` for the sheaf half. See the module documentation for what each is and where it is
missing. The sixth, adic rigidity, used to be the hypothesis `hrig`; it is now discharged by
`Stacks.AdicClosedSubschemeRigidity.adicRigidity` and no longer appears.

**No `stacks` attribute is attached, and none may be while those five are hypotheses.** A tag
counts only on a declaration proved under the source's own hypotheses, and this one is not: it
would read as a claim that [Stacks, Tag 089A] is proved here, which it is not. The partial
registration of the tag stays where the base put it, on the embedding step at
`AmpleFormalSystemEmbedding.lean:126`, which is scoped and accurate.

Where each of the five stands:

* `halg` is the input of [Stacks, Tag 09ZT]. For the projective `ambientHom A N` the module half
  of Grothendieck existence is unconditional; the algebra-structure step
  `AlgebraicGeometry.AlgebraStructureOnAlgebraization` has no carrier. See the module
  documentation.
* `hvan` needs the graded `𝒪_{X₀}`-algebra `⨁ₙ 𝓕ₙ` and [Stacks, Tag 0897] for it, and the
  scheme-level projection formula along `X₀ ⟶ Xₙ₊₁`; neither exists in this library. Note that the
  library's outright proof of [Stacks, Tag 0884] does not apply, because it is stated for a
  coherent adic system on a single scheme already proper over `Spec A`.
* `hequiv` is reduced to the canonical tower by
  `adicTowerModuleAlgebraization_of_canonicalTower`, so what it asks is
  `AdicCanonicalTowerModuleAlgebraization`, a statement about `X ×_{Spec A} Sₙ` alone. Neither
  [Stacks, Tag 088C] nor the identification of the two kinds of coherent adic system is a blocker
  any more — 0885 is unconditional for a projective morphism and the identification is
  `AlgebraicGeometry.adicThickeningCoherentAdicSystemsEquivalence`. What is left is the formal
  transport of that equivalence onto the `Stacks.CoherentTower.restriction` spelling, which the
  module documentation explains and which is not done here.
* `hinvertible` and `hampleX` have no carrier; the library's ampleness criteria of this shape all
  need a surjective closed immersion, which `k 0` is not.

The module documentation gives the file:line of every result named here. -/
public theorem exists_isProper_isAmple_of_isAmple [IsNoetherianRing A]
    (hcomplete : IsAdicComplete I A)
    (halg : ∀ {P : Scheme.{u}} (fP : P ⟶ Spec (.of A)), AdicFiniteAlgebraAlgebraization A I fP)
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (hproper : IsProper (q 0))
    (hample : letI := hL 0; IsAmple (Xn 0) (L 0))
    (hvan : ∀ d₁ : ℕ, ∃ d : ℕ, d₁ ≤ d ∧ ∀ n : ℕ,
      IsZero (((AlgebraicGeometry.moduleGlobalSections (Xn (n + 1))).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((Xn (n + 1)).toRingedSpace).presheaf, ((Xn (n + 1)).toRingedSpace).IsSheaf⟩).obj
            (Stacks.ClosedImmersion.idealSheaf (i n).toLRSHom.toShHom)).obj
          (letI := hL (n + 1); tensorPowModule (Xn (n + 1)) (L (n + 1)) (d : ℤ))))))
    (hequiv : AdicTowerModuleAlgebraization A I q i)
    (hinvertible : AdicTowerInvertibility A I q)
    (hampleX : AdicTowerAmpleness A I q) :
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (.of A)), IsProper fX ∧
      ∃ (M : X.Modules) (hM : IsInvertibleModule X M), @IsAmple X M hM ∧
        ∃ (k : ∀ n, Xn n ⟶ X) (hk : ∀ n, i n ≫ k (n + 1) = k n),
          (∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n)) ∧
          ∃ e : ∀ n, L n ≅ (Scheme.Modules.pullback (k n)).obj M,
            ∀ n, (φ n).hom ≫ (e n).hom =
              (Scheme.Modules.pullback (i n)).map (e (n + 1)).hom ≫
                (Scheme.Modules.pullbackComp (i n) (k (n + 1))).hom.app M ≫
                  (Scheme.Modules.pullbackCongr (hk n)).hom.app M := by
  have := hcomplete
  obtain ⟨X, fX, hfX, k, hk, hkcart⟩ :=
    Stacks.AmpleFormalSystemAlgebraization.exists_isProjectiveMorphism_of_isAmple A I hcomplete
      (fun N => adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization A I
        (ambientHom A N) (halg (ambientHom A N)))
      (adicMorphismRigidity_of_adicRigidity A I
        (Stacks.AdicClosedSubschemeRigidity.adicRigidity A I))
      q i hcart L hL hproper hample
      (fun d₁ => by
        obtain ⟨d, hdd, hv⟩ := hvan d₁
        exact ⟨d, hdd, powTransitionIso i L hL φ d, fun n =>
          surjective_transitionSections_of_isZero_h1 A I q i L hL φ hcart d n (hv n)⟩)
  have := isProper_of_isProjectiveMorphism fX hfX
  obtain ⟨M, hM, hMample, e, hcomp⟩ :=
    Stacks.AmpleFormalSystemLineBundle.exists_isAmple_of_restriction_isEquivalence A I fX q i k hk
      hkcart L hL φ (hequiv fX hfX k hk hkcart) (hinvertible fX hfX k hkcart)
      (hampleX fX hfX k hkcart) hample
  exact ⟨X, fX, isProper_of_isProjectiveMorphism fX hfX, M, hM, hMample, k, hk, hkcart, e,
    hcomp⟩

end Stacks.AmpleFormalSystemTheorem

end
