module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIntersectionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealCoproductGenericIso
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupportIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealMeet
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport

/-!
# The higher-rank dévissage principle for coherent modules on a Noetherian algebraic space

Stacks 08AN is the higher-rank variant of the dévissage principle Stacks 07US.  Where 07US asks
a property `P` of coherent modules on a Noetherian algebraic space `X` to hold for *every*
direct image `i_*I` of a quasi-coherent sheaf of ideals on a reduced closed subspace
`i : Z → X` with `|Z|` irreducible, the variant asks only that

1. for a short exact sequence of coherent modules, two of the three terms having `P` forces the
   third (`AlgebraicGeometry.Space.TwoOutOfThreeCoherent`);
2. `P` descends from a finite direct sum of `r ≥ 1` copies of a module to the module
   (`AlgebraicGeometry.Space.ClosedUnderDirectSumDescent`);
3. every reduced closed subspace `Z ⊆ X` with `|Z|` irreducible carries *some* coherent module
   on `X` with `P`, namely one whose scheme-theoretic support is `Z`
   (`AlgebraicGeometry.Space.HasCoherentWitnessOnIntegralSubspaces`),

and concludes that `P` holds for every coherent module on `X`.

## The shape of the argument

Hypothesis (2) of Stacks 07US is deduced from (1), (2) and (3) by a Noetherian induction, which
the source organizes as the choice of a minimal reduced closed subspace `Z` for which some
`i_*I` fails `P`.  At such a `Z` the witness `G` of (3) and Stacks 07UQ give a short exact
sequence

`0 → (i_*I₀)^{⊕r} → G → Q → 0`

with `I₀ ≠ 0` and with `Q` supported on a proper closed subspace of `Z`; minimality gives `P`
for `Q`, hypothesis (1) gives it for `(i_*I₀)^{⊕r}`, hypothesis (2) gives it for `i_*I₀`, and a
comparison of `I₀` with an arbitrary `J` through `I₀ ∩ J` gives it for every `i_*J`.

All of that is carried out here, as

* `AlgebraicGeometry.Space.property_of_moduleSupportSet_subset`, which converts a statement
  about direct images of sheaves of ideals into one about *all* coherent modules supported in a
  given set.  This is the only place where Stacks 07US is invoked, applied to the property
  `fun M => Supp M ⊆ W → P M`; its hypotheses transfer because the support of a submodule and
  of a quotient module are contained in the support of the module.
* `AlgebraicGeometry.Space.idealPushforwardComparison`, the comparison of `I₀` with an
  arbitrary `J` through `I₀ ⊓ J`, which is the last paragraph of the source's proof.
* `AlgebraicGeometry.Space.property_idealPushforward_of_property_of_lt`, the step at a minimal
  subspace, which is the paragraph of the source displayed above.
* `AlgebraicGeometry.Space.forall_property_idealPushforward`, the Noetherian induction itself,
  run over the closed subsets of `|X|` — a Noetherian topological space because `X` is a
  Noetherian algebraic space — and indexed by the support of `i_*I`.
* `AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree`, **Stacks 08AN**.

Stacks 08AN is therefore not a specialization of Stacks 07US: it is a genuine strengthening of
it, in that hypothesis (2) of 07US is *concluded* from the weaker (2) and (3) above by an
induction which 07US itself knows nothing about.  What 07US contributes, and all it
contributes, is the single application inside
`AlgebraicGeometry.Space.property_of_moduleSupportSet_subset`; Stacks 07UR contributes the
hypothesis `hdev` that 07US consumes.

## What is carried, and why

Three hypotheses are carried beyond the source's list.  Not one of them is mathematics of
Stacks 08AN: each is the conclusion, or a named clause, of another tag, and each is a statement
that tag's own formalization in this repository still carries.

* `hdev`, the conclusion of Stacks 07UR for every coherent module on `X`.  This is what the
  library's Stacks 07US consumes; it is the conclusion of Stacks 07UR,
  `AlgebraicGeometry.Space.hasIdealDevissage_of_isCoherent`.
* `AlgebraicGeometry.Space.IdealPushforwardCoherent`, the **coherence clause of Stacks 07UH**
  at the inclusion `i : Z → X` of a closed subspace and a quasi-coherent sheaf of ideals
  `I ⊆ 𝒪_Z`: the direct image `i_*I` is a coherent `𝒪_X`-module.  A closed immersion is finite
  and `I` is a coherent `𝒪_Z`-module by
  `AlgebraicGeometry.Space.isCoherent_quasicoherentIdeal`, so this is an instance of
  `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite`, whose hypothesis `hchart`
  — the étale-site form of Stacks 01Y6, that is Stacks 03DW — this development does not carry.
  It is carried in exactly the shape the proofs below consume and no more generally.
* `AlgebraicGeometry.Space.ExistsSupportModuleAndGenericTrivialization`, the **two inputs of
  Stacks 07UQ**: the module `G` on `Z` with `i_*G ≅ F`, which for `Z` the
  scheme-theoretic support is the existence assertion of Stacks 07U0 and is available
  unconditionally from the essential-image assertion of Stacks 04CJ part (3), by
  `AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion`; and the
  generically bijective map out of a finite direct sum of copies of a reduced ideal sheaf, which
  is the surjectivity half of Stacks 07UM.  Both are taken as data here because the statements
  below are about an arbitrary closed subspace `Z`.

Three things are **not** carried as hypotheses.

**Stacks 07UQ itself** is not a hypothesis: the general-case
`AlgebraicGeometry.Space.exists_mono_modulePushforward_cokernelCofork_support_subset_image`
supplies it, and `AlgebraicGeometry.Space.existsIdealInjectionDevissageStep` puts it in the
shape `AlgebraicGeometry.Space.ExistsIdealInjectionDevissageStep` that the minimal-subspace step
consumes, absorbing the `i_*(I^{⊕r})` versus `(i_*I)^{⊕r}` presentation, the coherence of the
direct sum and the passage from a non-strict to a strict inclusion of supports.  What remains
of it is the pair of inputs that the tag's formalization itself carries, listed above.

**The last paragraph of the source's proof**, the passage from one nonzero sheaf of ideals to
all of them through their intersection, is proved:
`AlgebraicGeometry.Space.idealPushforwardComparison`.  The two inputs it needs are
available — right exactness of the direct image along a closed immersion, through
`AlgebraicGeometry.Space.shortExact_map_modulePushforward_of_isClosedImmersion` and
`AlgebraicGeometry.Space.modulePushforwardCokernelIso`, and the meet of two quasi-coherent
sheaves of ideals, through `AlgebraicGeometry.Space.quasicoherentIdealsInf` — and the one thing
the paragraph needs beyond them is coherence of the three direct images `i_*I`, `i_*J` and
`i_*(I ⊓ J)`, which is what `AlgebraicGeometry.Space.IdealPushforwardCoherent` supplies.

**The equality of the supports** of the direct images of any two nonzero quasi-coherent sheaves
of ideals on `Z` — both supports being `|Z|` — is not carried either:
`AlgebraicGeometry.Space.idealPushforwardSupportConstant` proves it from
`AlgebraicGeometry.Space.supportOfSheaf_quasicoherentIdeal_closedSubspace_eq_univ`, that the
support of a nonzero quasi-coherent sheaf of ideals on `Z` is all of `|Z|`, and
`AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion`, that
the support of a direct image along a closed immersion is the image of the support.

## Main definitions

* `AlgebraicGeometry.Space.ClosedUnderDirectSumDescent` and
  `AlgebraicGeometry.Space.HasCoherentWitnessOnIntegralSubspaces` are hypotheses (2) and (3) of
  Stacks 08AN; hypothesis (1), `AlgebraicGeometry.Space.TwoOutOfThreeCoherent`, is stated in
  `StacksFrontier/AlgebraicGeometry/Spaces/CoherentDevissage.lean` beside hypothesis (1) of
  Stacks 07US, which it strengthens.
* `AlgebraicGeometry.Space.IdealPushforwardCoherent` and
  `AlgebraicGeometry.Space.ExistsSupportModuleAndGenericTrivialization` are the two carried
  statements, and `AlgebraicGeometry.Space.ExistsIdealInjectionDevissageStep`,
  `AlgebraicGeometry.Space.IdealPushforwardSupportConstant` and
  `AlgebraicGeometry.Space.IdealPushforwardComparison` name the three statements which are
  proved here.

## Main results

* `AlgebraicGeometry.Space.idealPushforwardSupportConstant`: on a locally Noetherian algebraic
  space the direct images of any two nonzero quasi-coherent sheaves of ideals on a reduced
  closed subspace with irreducible space of points have the same support.
* `AlgebraicGeometry.Space.idealPushforwardComparison`: the last paragraph of the source's
  proof, the comparison of two quasi-coherent sheaves of ideals on `Z` through their meet.
* `AlgebraicGeometry.Space.existsIdealInjectionDevissageStep`: **Stacks 07UQ** in the shape the
  minimal-subspace step consumes.
* `AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree` is **Stacks 08AN**.

## References

* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two auxiliary facts about the zero sheaf of ideals -/

/-- The direct image of a zero module along a morphism of algebraic spaces is a zero module:
the direct image preserves zero morphisms.

The morphism is taken as a variable because that is what the instance for preservation of zero
morphisms is found for; at a morphism written out, such as
`AlgebraicGeometry.Space.closedSubfunctorι`, it is not. -/
theorem isZero_modulePushforward_of_isZero (W X : AlgebraicSpaces B S hS) (i : W ⟶ X)
    {A : Modules.{u, u} B S hS W.1 W.2} (h : IsZero A) :
    IsZero ((modulePushforward B S hS i).obj A) :=
  Functor.map_isZero _ h

/-- The direct image of the zero sheaf of ideals on a closed subspace is a zero module: the
bottom submodule is a zero object and the direct image preserves zero morphisms. -/
theorem isZero_modulePushforward_of_eq_bot (X : AlgebraicSpaces B S hS) {Z : Subfunctor X.1}
    (hZ : IsClosedSubspace B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ)) (hI : I.1 = ⊥) :
    IsZero ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
      I.1.toSheafOfModules) := by
  rw [hI]
  exact isZero_modulePushforward_of_isZero B S hS _ X (closedSubfunctorι B S hS hZ)
    (SheafOfModules.Submodule.isZero_toSheafOfModules_bot _)

/-! ### The three hypotheses of Stacks 08AN

Hypothesis (1) is `AlgebraicGeometry.Space.TwoOutOfThreeCoherent`, stated in
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentDevissage.lean`; hypotheses (2) and (3) are
stated here. -/

/-- Hypothesis (1) of Stacks 08AN implies hypothesis (1) of Stacks 07US: the first of its three
implications. -/
theorem closedUnderCoherentExtensions_of_twoOutOfThreeCoherent (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop) (h : TwoOutOfThreeCoherent B S hS X P) :
    ClosedUnderCoherentExtensions B S hS X P :=
  fun E hE h1 h2 h3 hP1 hP3 => (h E hE h1 h2 h3).1 hP1 hP3

/-- **Hypothesis (2) of Stacks 08AN.**  If the property `P` holds for the direct sum of `r ≥ 1`
copies of a module, then it holds for that module. -/
def ClosedUnderDirectSumDescent (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop) : Prop :=
  ∀ (F : Modules.{u, u} B S hS X.1 X.2) (r : ℕ), 1 ≤ r → P (⨁ fun _ : Fin r => F) → P F

/-- **Hypothesis (3) of Stacks 08AN.**  For every reduced closed subspace `Z ⊆ X` with `|Z|`
irreducible there is a coherent module on `X` whose scheme-theoretic support, Stacks 07U1, is
`Z` and which has the property `P`. -/
def HasCoherentWitnessOnIntegralSubspaces (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop) : Prop :=
  ∀ Z : Subfunctor X.1, IsClosedSubspace B S hS Z → IsReducedIrreducible B S hS Z →
    ∃ G : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 G ∧
      schemeTheoreticSupport B S hS X G = Z ∧ P G

/-! ### The two carried statements, and one which is proved below -/

/-- **Stacks 07UQ**, as a hypothesis.  Let `F` be a coherent module on `X` whose
scheme-theoretic support is a reduced closed subspace `Z` with `|Z|` irreducible.  Then there
are an integer `r > 0`, a nonzero quasi-coherent sheaf of ideals `I ⊆ 𝒪_Z` and an injection of
coherent modules `(i_*I)^{⊕r} → F` whose cokernel is supported on a proper closed subspace
of `Z`.

Three points of presentation, none of them changing the content:

* the source writes the source of the injection as `i_*(I^{⊕r})`; the direct image is additive,
  so that is the direct sum of `r` copies of `i_*I`, which is the form used here;
* the cokernel is presented as a cokernel cofork, as in
  `AlgebraicGeometry.Space.HasIdealDevissage`, so that the statement needs no `HasCokernel`
  instance;
* "supported on a proper closed subspace of `Z`" is expressed as a strict inclusion into the
  support of `i_*I`, which is `|Z|` because `I` is nonzero and `Z` is reduced with `|Z|`
  irreducible — this is
  `AlgebraicGeometry.Space.supportOfSheaf_quasicoherentIdeal_closedSubspace_eq_univ`, so no
  generality is lost and the ambient `|Z|` need not be named. -/
def ExistsIdealInjectionDevissageStep (X : AlgebraicSpaces B S hS) : Prop :=
  ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
    ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z), IsReducedIrreducible B S hS Z →
      schemeTheoreticSupport B S hS X F = Z →
      ∃ (r : ℕ) (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ)),
        0 < r ∧ I.1 ≠ ⊥ ∧
        IsCoherent B S hS X.1 X.2 (⨁ fun _ : Fin r =>
          (modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) ∧
        ∃ (φ : (⨁ fun _ : Fin r =>
            (modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
              I.1.toSheafOfModules) ⟶ F) (_ : Mono φ) (Q : Modules.{u, u} B S hS X.1 X.2)
          (q : F ⟶ Q) (hq : φ ≫ q = 0),
          Nonempty (IsColimit (CokernelCofork.ofπ q hq)) ∧
            moduleSupportSet B S hS X Q ⊂ moduleSupportSet B S hS X
              ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
                I.1.toSheafOfModules)

/-- **The two inputs of Stacks 07UQ**, as a hypothesis.  For a coherent module `F` on
`X` whose scheme-theoretic support is a reduced closed subspace `Z` with `|Z|` irreducible,
there are

* a module `G` on `Z` with `i_*G ≅ F`.  This is the existence assertion of Stacks 07U0, which
  `AlgebraicGeometry.Space.exists_module_on_schemeTheoreticSupport` deduces
  unconditionally from the essential-image assertion of Stacks 04CJ part (3) — equivalently
  Stacks 04E5 part (2) — for `Z` the scheme-theoretic support of `F`; it is data here because
  `Z` is an arbitrary closed subspace.
* a closed `T ⊊ |Z|`, an integer `r > 0` and a map `ψ` from the product of `r` copies of the
  reduced ideal sheaf of `T` to `G` which is bijective on the sections over every chart carrying
  the unit ideal of that sheaf.  This is the **surjectivity half of Stacks 07UM**, the map of
  its first display being generically an isomorphism.

These are exactly the hypotheses `G`, `eG`, `T`, `hT`, `hTne`, `r`, `hr`, `ψ` and `hψ` of the
library's Stacks 07UQ,
`AlgebraicGeometry.Space.exists_mono_modulePushforward_cokernelCofork_support_subset_image`,
which proves everything else; so this carries the two statements that tag itself carries, and
nothing beyond them.  `AlgebraicGeometry.Space.existsIdealInjectionDevissageStep` turns it into
`AlgebraicGeometry.Space.ExistsIdealInjectionDevissageStep`. -/
def ExistsSupportModuleAndGenericTrivialization (X : AlgebraicSpaces B S hS) : Prop :=
  ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
    ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z), IsReducedIrreducible B S hS Z →
      schemeTheoreticSupport B S hS X F = Z →
      ∃ (G : Modules.{u, u} B S hS (closedSubfunctorSpace B S hS hZ).1
          (closedSubfunctorSpace B S hS hZ).2)
        (_ : (modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj G ≅ F)
        (T : Set (points B S hS (closedSubfunctorSpace B S hS hZ).1)) (hT : IsClosed T)
        (_ : T ≠ Set.univ) (r : ℕ), 0 < r ∧
        ∃ ψ : (∏ᶜ fun _ : Fin r =>
            ((reducedIdealSheaf B S hS (closedSubfunctorSpace B S hS hZ) T
                hT).toSheafOfModules :
              Modules.{u, u} B S hS (closedSubfunctorSpace B S hS hZ).1
                (closedSubfunctorSpace B S hS hZ).2)) ⟶ G,
          ∀ W : SmallEtale B S hS (closedSubfunctorSpace B S hS hZ).1,
            (reducedIdealSheaf B S hS (closedSubfunctorSpace B S hS hZ) T hT).obj (op W) = ⊤ →
              Function.Bijective (ψ.val.app (op W))

/-- **The supports of the direct images of two nonzero quasi-coherent sheaves of ideals on a
reduced closed subspace with irreducible space of points agree**, both being `|Z|`.

This is *not* carried: it is proved below, as
`AlgebraicGeometry.Space.idealPushforwardSupportConstant`, for a locally Noetherian `X`.  The
name is kept because it is the statement the step at a minimal subspace consumes, and naming it
keeps that step's hypothesis list readable. -/
def IdealPushforwardSupportConstant (X : AlgebraicSpaces B S hS) : Prop :=
  ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z), IsReducedIrreducible B S hS Z →
    ∀ I J : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ), I.1 ≠ ⊥ → J.1 ≠ ⊥ →
      moduleSupportSet B S hS X ((modulePushforward B S hS
          (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) =
        moduleSupportSet B S hS X ((modulePushforward B S hS
          (closedSubfunctorι B S hS hZ)).obj J.1.toSheafOfModules)

/-- **The coherence clause of Stacks 07UH for the direct image of a quasi-coherent sheaf of
ideals on a closed subspace**, as a hypothesis.

The inclusion `i : Z → X` of a closed subspace is a finite morphism, and on a locally
Noetherian `X` a quasi-coherent sheaf of ideals `I ⊆ 𝒪_Z` is a coherent `𝒪_Z`-module by
`AlgebraicGeometry.Space.isCoherent_quasicoherentIdeal`; so this is the instance of the
coherence assertion of Stacks 07UH at `i` and `I`.  That assertion is available here only as
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite`, whose hypothesis `hchart`
is the étale-site form of Stacks 01Y6, that is Stacks 03DW, which this development does not
carry; so the instance of it that Stacks 08AN consumes is carried, and it is carried in exactly
the shape consumed — no more generality, so that the single tag 07UH discharges it.

It is what makes the two short exact sequences of
`AlgebraicGeometry.Space.idealPushforwardComparison` sequences of *coherent* modules, which is
what hypothesis (1) of Stacks 08AN asks for; it is needed at the three sheaves of ideals `I`,
`J` and `I ⊓ J`, and `AlgebraicGeometry.Space.quasicoherentIdealsInf` makes the third one of
them a quasi-coherent sheaf of ideals again. -/
def IdealPushforwardCoherent (X : AlgebraicSpaces B S hS) : Prop :=
  ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ)),
    IsCoherent B S hS X.1 X.2
      ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules)

/-- **The last paragraph of the proof of Stacks 08AN**: on a reduced closed subspace `Z` with
`|Z|` irreducible, once the property `P` is known for the direct image of one nonzero
quasi-coherent sheaf of ideals, and for every coherent module of strictly smaller support, it
holds for the direct image of every quasi-coherent sheaf of ideals on `Z`.

This is *not* carried: it is proved below, as
`AlgebraicGeometry.Space.idealPushforwardComparison`, on a locally Noetherian `X` granted
`AlgebraicGeometry.Space.IdealPushforwardCoherent`.  The name is kept because it is the
statement the step at a minimal subspace consumes, and naming it keeps that step's hypothesis
list readable.  It is stated for an arbitrary property, so that it records the mathematics of
the paragraph and not the property to which Stacks 08AN is being applied. -/
def IdealPushforwardComparison (X : AlgebraicSpaces B S hS) : Prop :=
  ∀ P : Modules.{u, u} B S hS X.1 X.2 → Prop,
    (∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M) →
    TwoOutOfThreeCoherent B S hS X P →
    ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z), IsReducedIrreducible B S hS Z →
      ∀ I J : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ), I.1 ≠ ⊥ →
        (∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
          moduleSupportSet B S hS X N ⊂ moduleSupportSet B S hS X
            ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
              I.1.toSheafOfModules) → P N) →
        P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) →
          P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj J.1.toSheafOfModules)

/-! ### The support of the direct image of a nonzero sheaf of ideals -/

/-- A closed subspace of a locally Noetherian algebraic space is locally Noetherian: its
inclusion is a closed immersion, hence locally of finite type by
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isClosedImmersion`, and a morphism locally of
finite type with locally Noetherian target has locally Noetherian source by Stacks 04ZK. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_closedSubfunctor
    (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {Z : Subfunctor X.1} (hZ : IsClosedSubspace B S hS Z) :
    HasEtaleLocalProperty B S hS Z.toFunctor (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hZ.1 X.2 Z.ι
    (isLocallyOfFiniteType_of_isClosedImmersion B S hS Z.ι hZ.2) hN

/-- **The support of the direct image of a nonzero quasi-coherent sheaf of ideals on a reduced
closed subspace with irreducible space of points is the image of that subspace.**

The support of the sheaf of ideals itself is all of `|Z|` by
`AlgebraicGeometry.Space.supportOfSheaf_quasicoherentIdeal_closedSubspace_eq_univ`; the support
of a direct image along a closed immersion is the image of the support by
`AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion`, whose
closedness hypothesis is satisfied because that support is the whole space. -/
theorem moduleSupportSet_idealPushforward_eq_image
    (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {Z : Subfunctor X.1} (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ)) (hI : I.1 ≠ ⊥) :
    moduleSupportSet B S hS X ((modulePushforward B S hS
        (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) =
      pointsMap B S hS Z.toFunctor (closedSubfunctorι B S hS hZ).hom '' Set.univ := by
  have hsupp : supportOfSheaf B S hS Z.toFunctor
      ((SheafOfModules.toSheaf _).obj I.1.toSheafOfModules) = Set.univ :=
    supportOfSheaf_quasicoherentIdeal_closedSubspace_eq_univ B S hS hZ hint
      (hasEtaleLocalProperty_isLocallyNoetherian_closedSubfunctor B S hS X hN hZ) I hI
  refine (supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B S hS
    (closedSubfunctorι B S hS hZ) hZ.2 I.1.toSheafOfModules ?_).trans (congrArg _ hsupp)
  change IsClosed (supportOfSheaf B S hS Z.toFunctor
    ((SheafOfModules.toSheaf
      (structureRingSheaf B S hS (closedSubfunctorSpace B S hS hZ))).obj I.1.toSheafOfModules))
  rw [hsupp]
  exact isClosed_univ

/-- **The supports of the direct images of two nonzero quasi-coherent sheaves of ideals on a
reduced closed subspace with irreducible space of points agree**, both being the image of that
subspace.

This discharges `AlgebraicGeometry.Space.IdealPushforwardSupportConstant` on a locally
Noetherian algebraic space, by applying
`AlgebraicGeometry.Space.moduleSupportSet_idealPushforward_eq_image` to each of the two sheaves
of ideals. -/
theorem idealPushforwardSupportConstant (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    IdealPushforwardSupportConstant B S hS X := fun _Z hZ hint I J hI hJ =>
  (moduleSupportSet_idealPushforward_eq_image B S hS X hN hZ hint I hI).trans
    (moduleSupportSet_idealPushforward_eq_image B S hS X hN hZ hint J hJ).symm

/-! ### The comparison of two sheaves of ideals through their meet -/

/-- Isomorphic modules have the same support: each of the two inclusions of supports is an
instance of `AlgebraicGeometry.Space.moduleSupportSet_subset_of_mono`, respectively of
`AlgebraicGeometry.Space.moduleSupportSet_subset_of_epi`, at the isomorphism. -/
theorem moduleSupportSet_congr (X : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N) :
    moduleSupportSet B S hS X M = moduleSupportSet B S hS X N :=
  Set.Subset.antisymm
    (moduleSupportSet_subset_of_mono B S hS X e.hom (IsIso.mono_of_iso e.hom))
    (moduleSupportSet_subset_of_epi B S hS X e.hom (IsIso.epi_of_iso e.hom))

/-- **A quasi-coherent sheaf of ideals on a locally Noetherian algebraic space is coherent.**
The structure sheaf is coherent by Stacks 07UB and a quasi-coherent submodule of a coherent
module is coherent by Stacks 07UD. -/
theorem isCoherent_quasicoherentIdeal (W : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS W.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (I : QuasicoherentIdeals B S hS W) :
    IsCoherent B S hS W.1 W.2 I.1.toSheafOfModules :=
  @isCoherent_of_mono_of_isQuasicoherentOnSite B S hS W.1 W.2 ⟨hN⟩ _ _ I.1.ι
    (SheafOfModules.Submodule.mono_ι_via_forget I.1) I.2 (@isCoherent_structureSheaf B S hS W.1 W.2
        ⟨hN⟩)

/-- Over a chart carrying the unit ideal of `J`, the meet `I ⊓ J` has all the sections of `I`:
the sections of the meet over a chart are the intersection of the two submodules of sections,
and the second of them is everything.

This is the surjectivity on the charts of the unit locus of `J` which
`AlgebraicGeometry.Space.supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective` consumes,
and it is how "`I/(I ∩ J)` is annihilated by `J`" is used: the quotient has no sections where
`J` is everything. -/
theorem surjective_submoduleInfFst_app (W : AlgebraicSpaces B S hS)
    (I J : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule)
    (V : SmallEtale B S hS W.1) (hV : J.obj (op V) = ⊤)
    (s : I.toSheafOfModules.val.obj (op V)) :
    ∃ y : (I ⊓ J).toSheafOfModules.val.obj (op V),
      (Stacks.SheafOfModules.submoduleInfFst I J).val.app (op V) y = s := by
  refine ⟨⟨s.1, ?_⟩, ?_⟩
  · change (s.1 : _) ∈ I.obj (op V) ⊓ J.obj (op V)
    exact Submodule.mem_inf.2 ⟨s.2, by rw [hV]; exact Submodule.mem_top⟩
  · rfl

/-- Over a chart carrying the unit ideal of `I`, the meet `I ⊓ J` has all the sections of `J`.
This is `AlgebraicGeometry.Space.surjective_submoduleInfFst_app` with the two sheaves of ideals
exchanged. -/
theorem surjective_submoduleInfSnd_app (W : AlgebraicSpaces B S hS)
    (I J : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule)
    (V : SmallEtale B S hS W.1) (hV : I.obj (op V) = ⊤)
    (s : J.toSheafOfModules.val.obj (op V)) :
    ∃ y : (I ⊓ J).toSheafOfModules.val.obj (op V),
      (Stacks.SheafOfModules.submoduleInfSnd I J).val.app (op V) y = s := by
  refine ⟨⟨s.1, ?_⟩, ?_⟩
  · change (s.1 : _) ∈ I.obj (op V) ⊓ J.obj (op V)
    exact Submodule.mem_inf.2 ⟨by rw [hV]; exact Submodule.mem_top, s.2⟩
  · rfl

/-- **The image of a set which is not everything, under an injective map, is strictly smaller
than the image of everything.**  A point outside the set has its image outside the image of the
set, by injectivity, and inside the image of everything. -/
theorem image_ssubset_image_univ {α β : Type*} {f : α → β} (hf : Function.Injective f)
    {T : Set α} (hT : T ≠ Set.univ) : f '' T ⊂ f '' Set.univ := by
  obtain ⟨x, hx⟩ := Set.nonempty_compl.2 hT
  refine ⟨Set.image_mono (Set.subset_univ _), fun hcon => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hcon ⟨x, Set.mem_univ x, rfl⟩
  exact hx (hf hyx ▸ hy)

/-- **The image of the zero locus of a nonzero sheaf of ideals on a reduced closed subspace with
irreducible space of points is strictly smaller than the image of the whole subspace.**

The unit locus of a nonzero sheaf of ideals on a reduced algebraic space is nonempty, by
`AlgebraicGeometry.Space.idealUnitLocus_nonempty_of_ne_bot`, so the zero locus — its complement
— is not everything; and a closed immersion is injective on points by
`AlgebraicGeometry.Space.pointsMap_hom_injective_of_isClosedImmersion`. -/
theorem image_idealZeroLocus_ssubset {X : AlgebraicSpaces B S hS}
    {Z : Subfunctor X.1} (hZ : IsClosedSubspace B S hS Z)
    (hint : IsReducedIrreducible B S hS Z)
    (K : (SheafOfModules.unit (structureRingSheaf B S hS
      (closedSubfunctorSpace B S hS hZ))).Submodule) (hK : K ≠ ⊥) :
    pointsMap B S hS Z.toFunctor (closedSubfunctorι B S hS hZ).hom ''
        idealZeroLocus B S hS (closedSubfunctorSpace B S hS hZ) K ⊂
      pointsMap B S hS Z.toFunctor (closedSubfunctorι B S hS hZ).hom '' Set.univ := by
  obtain ⟨x, hx⟩ := idealUnitLocus_nonempty_of_ne_bot B S hS
    (closedSubfunctorSpace B S hS hZ) hint.1 K hK
  refine image_ssubset_image_univ
    (pointsMap_hom_injective_of_isClosedImmersion B S hS (closedSubfunctorι B S hS hZ) hZ.2)
    (fun hcon => ?_)
  have hmem : x ∈ idealZeroLocus B S hS (closedSubfunctorSpace B S hS hZ) K :=
    hcon ▸ Set.mem_univ x
  exact hmem hx

/-- **The direct image along a closed immersion of a short exact sequence whose third term is a
cokernel**, in the form the two sequences of the last paragraph of Stacks 08AN need: for a
monomorphism `φ` of `𝒪_W`-modules the complex

`0 → i_*A → i_*C → coker(i_*φ) → 0`

is short exact.  The direct image of a monomorphism is a monomorphism by
`AlgebraicGeometry.Space.mono_modulePushforward_map`, and the rest is the cokernel sequence of
an abelian category. -/
theorem shortExact_cokernelSequence_modulePushforward (X W : AlgebraicSpaces B S hS) (i : W ⟶ X)
    {A C : Modules.{u, u} B S hS W.1 W.2} (φ : A ⟶ C) (hφ : Mono φ) :
    (ShortComplex.mk ((modulePushforward B S hS i).map φ)
      (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2)
        ((modulePushforward B S hS i).map φ))
      (cokernel.condition (C := Modules.{u, u} B S hS X.1 X.2)
        ((modulePushforward B S hS i).map φ))).ShortExact := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (mono_modulePushforward_map B S hS i φ hφ)
    (coequalizer.π_epi (C := Modules.{u, u} B S hS X.1 X.2))

/-- **The support of the cokernel of a direct image along a closed immersion is the image of the
support of the cokernel.**  The direct image along a closed immersion is exact, so it commutes
with cokernels by `AlgebraicGeometry.Space.modulePushforwardCokernelIso`, and the support of a
direct image along a closed immersion is the image of the support; the closedness that needs is
supplied by coherence of the cokernel on `W`. -/
theorem moduleSupportSet_cokernel_modulePushforward (X W : AlgebraicSpaces B S hS) (i : W ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    {A C : Modules.{u, u} B S hS W.1 W.2} (φ : A ⟶ C)
    (hcoker : IsCoherent B S hS W.1 W.2 (cokernel φ)) :
    moduleSupportSet B S hS X (cokernel ((modulePushforward B S hS i).map φ)) =
      pointsMap B S hS W.1 i.hom '' moduleSupportSet B S hS W (cokernel φ) :=
  (moduleSupportSet_congr B S hS X (modulePushforwardCokernelIso B S hS i hi φ)).trans
    (supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B S hS i hi (cokernel φ)
      (isClosed_moduleSupportSet B S hS W (cokernel φ) hcoker))

/-- **The last paragraph of the proof of Stacks 08AN.**  This discharges
`AlgebraicGeometry.Space.IdealPushforwardComparison` on a locally Noetherian algebraic space,
granted `AlgebraicGeometry.Space.IdealPushforwardCoherent`.

The zero sheaf of ideals is disposed of by `hzero`.  Otherwise put `K = I ⊓ J`, which is a
quasi-coherent sheaf of ideals again by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_idealInf`, and push the two short exact
sequences

`0 → K → I → I/K → 0` and `0 → K → J → J/K → 0`

forward along `i`, which is exact by
`AlgebraicGeometry.Space.shortExact_map_modulePushforward_of_isClosedImmersion` and commutes
with the two cokernels by `AlgebraicGeometry.Space.modulePushforwardCokernelIso`.  All six
terms are coherent: the three direct images of sheaves of ideals by `hcoh`, and the two
cokernels by Stacks 07UC.  The quotient `I/K` has no sections over a chart carrying the unit
ideal of `J` — which is how the source's "`I/K` is annihilated by `J`" is used — so its support
lies in the zero locus `V(J)`, strictly inside `|Z|` because `J ≠ 0` and `Z` is reduced with
`|Z|` irreducible; hence `i_*(I/K)` has `P` by `hsmall`, and the first sequence gives `P` for
`i_*K` by the second implication of hypothesis (1).  Symmetrically `i_*(J/K)` has `P`, using
`I ≠ 0`, and the second sequence gives `P` for `i_*J` by the first implication. -/
theorem idealPushforwardComparison (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hcoh : IdealPushforwardCoherent B S hS X) :
    IdealPushforwardComparison B S hS X := by
  intro P hzero h1 Z hZ hint I J hI hsmall hPI
  by_cases hJ : J.1 = ⊥
  · exact hzero _ (isZero_modulePushforward_of_eq_bot B S hS X hZ J hJ)
  have hNW := hasEtaleLocalProperty_isLocallyNoetherian_closedSubfunctor B S hS X hN hZ
  have hKq : ((I.1 ⊓ J.1).toSheafOfModules).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_idealInf B S hS (closedSubfunctorSpace B S hS hZ) I.1 J.1 I.2 J.2
  have hKZ := isCoherent_quasicoherentIdeal B S hS (closedSubfunctorSpace B S hS hZ) hNW
    ⟨I.1 ⊓ J.1, hKq⟩
  have hKX := hcoh Z hZ ⟨I.1 ⊓ J.1, hKq⟩
  have hIimg := moduleSupportSet_idealPushforward_eq_image B S hS X hN hZ hint I hI
  -- the sequence `0 → K → A → A/K → 0` pushed forward along `i`, for `A` one of `I`, `J`
  have side : ∀ (A : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ))
      (C : (SheafOfModules.unit (structureRingSheaf B S hS
        (closedSubfunctorSpace B S hS hZ))).Submodule)
      (f : (I.1 ⊓ J.1).toSheafOfModules ⟶ A.1.toSheafOfModules),
      f ≫ A.1.ι = (I.1 ⊓ J.1).ι → C ≠ ⊥ →
      (∀ V : SmallEtale B S hS (closedSubfunctorSpace B S hS hZ).1, C.obj (op V) = ⊤ →
        ∀ s, ∃ y, f.val.app (op V) y = s) →
      (P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
          A.1.toSheafOfModules) →
        P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
          (I.1 ⊓ J.1).toSheafOfModules)) ∧
      (P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
          (I.1 ⊓ J.1).toSheafOfModules) →
        P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
          A.1.toSheafOfModules)) := by
    intro A C f hf hC hsurj
    have hAZ := isCoherent_quasicoherentIdeal B S hS (closedSubfunctorSpace B S hS hZ) hNW A
    have hAX := hcoh Z hZ A
    have : Mono (I.1 ⊓ J.1).ι := SheafOfModules.Submodule.mono_ι_via_forget _
    have hmf : Mono f := mono_of_mono_fac hf
    have hcokZ := isCoherent_cokernel B S hS _ _ hKZ hAZ f
    have hcokX := isCoherent_cokernel B S hS X.1 X.2 hKX hAX
      ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).map f)
    have hlt : moduleSupportSet B S hS X (cokernel
        ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).map f)) ⊂
        moduleSupportSet B S hS X ((modulePushforward B S hS
          (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) := by
      rw [hIimg, moduleSupportSet_cokernel_modulePushforward B S hS X
        (closedSubfunctorSpace B S hS hZ) (closedSubfunctorι B S hS hZ) hZ.2 _ hcokZ]
      exact lt_of_le_of_lt
        (Set.image_mono (supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS
          (closedSubfunctorSpace B S hS hZ) C f hsurj))
        (image_idealZeroLocus_ssubset B S hS hZ hint C hC)
    have hse := h1 _ (shortExact_cokernelSequence_modulePushforward B S hS X
      (closedSubfunctorSpace B S hS hZ) (closedSubfunctorι B S hS hZ) f hmf) hKX hAX hcokX
    exact ⟨fun h => hse.2.1 h (hsmall _ hcokX hlt), fun h => hse.1 h (hsmall _ hcokX hlt)⟩
  exact (side J I.1 _ (Stacks.SheafOfModules.submoduleInfSnd_ι I.1 J.1) hI
    (fun V hV s => surjective_submoduleInfSnd_app B S hS (closedSubfunctorSpace B S hS hZ)
      I.1 J.1 V hV s)).2
    ((side I J.1 _ (Stacks.SheafOfModules.submoduleInfFst_ι I.1 J.1) hJ
      (fun V hV s => surjective_submoduleInfFst_app B S hS (closedSubfunctorSpace B S hS hZ)
        I.1 J.1 V hV s)).1 hPI)

/-! ### Stacks 07UQ in the shape the minimal-subspace step consumes -/

/-- **Stacks 07UQ, in the shape `AlgebraicGeometry.Space.ExistsIdealInjectionDevissageStep`.**
This discharges that statement on a locally Noetherian algebraic space, granted
`AlgebraicGeometry.Space.IdealPushforwardCoherent` and
`AlgebraicGeometry.Space.ExistsSupportModuleAndGenericTrivialization`, which are the two inputs
the library's Stacks 07UQ itself carries.

Three presentational differences are absorbed, none of them changing the content.

* The library's statement produces the injection out of `i_*(I^{⊕r})`, as the source writes it,
  while the statement consumed here takes the direct sum outside the direct image.  The two are
  identified by `AlgebraicGeometry.Space.modulePushforwardBiproductConstIso`, an isomorphism, so
  injectivity survives composition with it and `q` is still a cokernel of the composite — that
  last point is `CategoryTheory.Limits.CokernelCofork.isColimitOfIsColimitOfIff'`, the
  equivalence `φ ≫ ξ = 0 ↔ e ≫ φ ≫ ξ = 0` holding because `e` is an epimorphism.
* Coherence of the direct sum is `AlgebraicGeometry.Space.isCoherent_biproductConst` applied to
  coherence of `i_*I`, which is `hcoh`.
* The library's statement bounds the support of the cokernel by the image of a closed `T' ⊊ |Z|`,
  which is *not* a strict bound on the nose; it becomes one because a closed immersion is
  injective on points, by
  `AlgebraicGeometry.Space.pointsMap_hom_injective_of_isClosedImmersion`, and because the
  support of `i_*I` is the image of all of `|Z|`, by
  `AlgebraicGeometry.Space.moduleSupportSet_idealPushforward_eq_image`. -/
theorem existsIdealInjectionDevissageStep (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hcoh : IdealPushforwardCoherent B S hS X)
    (hinputs : ExistsSupportModuleAndGenericTrivialization B S hS X) :
    ExistsIdealInjectionDevissageStep B S hS X := by
  intro F hF Z hZ hint hsupp
  obtain ⟨G, eG, T, hT, hTne, r, hr, ψ, hψ⟩ := hinputs F hF Z hZ hint hsupp
  obtain ⟨n, I, hn, hIq, hIb, φ, hmφ, Q, q, hq, ⟨hcol⟩, T', hT'c, hT'ne, hQsupp⟩ :=
    exists_mono_modulePushforward_cokernelCofork_support_subset_image B S hS X
      (closedSubfunctorι B S hS hZ) hZ.2 hint.1 hint.2 F G eG T hT hTne r hr ψ hψ
  have hsum := modulePushforwardBiproductConstIso B S hS X (closedSubfunctorι B S hS hZ) n
    I.toSheafOfModules
  have hmsum : Mono hsum.hom := IsIso.mono_of_iso hsum.hom
  have hesum : Epi hsum.hom := IsIso.epi_of_iso hsum.hom
  have hiff : ∀ ⦃W : Modules.{u, u} B S hS X.1 X.2⦄ (ξ : F ⟶ W),
      φ ≫ ξ = 0 ↔ (hsum.hom ≫ φ) ≫ ξ = 0 := by
    intro W ξ
    rw [Category.assoc]
    refine ⟨fun h => by rw [h, comp_zero], fun h => (cancel_epi hsum.hom).1 ?_⟩
    rw [h, comp_zero]
  refine ⟨n, ⟨I, hIq⟩, hn, hIb,
    isCoherent_biproductConst B S hS X.1 X.2 _ (hcoh Z hZ ⟨I, hIq⟩) n, hsum.hom ≫ φ,
    mono_comp _ _, Q, q, by rw [Category.assoc, hq, comp_zero],
    ⟨CokernelCofork.isColimitOfIsColimitOfIff' hcol _ hiff⟩, ?_⟩
  rw [moduleSupportSet_idealPushforward_eq_image B S hS X hN hZ hint ⟨I, hIq⟩ hIb]
  exact lt_of_le_of_lt hQsupp (image_ssubset_image_univ
    (pointsMap_hom_injective_of_isClosedImmersion B S hS (closedSubfunctorι B S hS hZ) hZ.2)
    hT'ne)

/-! ### From sheaves of ideals to all coherent modules supported in a closed set -/

/-- **The property for every coherent module supported in a prescribed set.**  If the property
`P` holds for the zero module, is closed under extensions of coherent modules, and holds for
every direct image `i_*I` of a quasi-coherent sheaf of ideals on a reduced closed subspace with
irreducible space of points whose support lies in `W`, then it holds for every coherent module
supported in `W`.

This is Stacks 07US applied to the property `fun M => Supp M ⊆ W → P M`; the hypotheses of 07US
transfer because the support of a submodule and of a quotient module are contained in the
support of the module.  The hypothesis `hdev` is the conclusion of Stacks 07UR, which is what
07US consumes. -/
theorem property_of_moduleSupportSet_subset (X : AlgebraicSpaces B S hS)
    (hdev : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
      HasIdealDevissage B S hS X M)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (hext : ClosedUnderCoherentExtensions B S hS X P) (W : Set (points B S hS X.1))
    (hW : ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z),
      IsReducedIrreducible B S hS Z →
      ∀ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ),
        moduleSupportSet B S hS X ((modulePushforward B S hS
            (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) ⊆ W →
          P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M)
    (hMW : moduleSupportSet B S hS X M ⊆ W) : P M := by
  refine property_of_forall_hasIdealDevissage B S hS X hdev
    (fun N => moduleSupportSet B S hS X N ⊆ W → P N) (fun N hN _ => hzero N hN) ?_
    (fun Z hZ hint I => hW Z hZ hint I) M hM hMW
  intro E hE h1 h2 h3 hP1 hP3 hsub
  have hs1 : moduleSupportSet B S hS X E.X₁ ⊆ moduleSupportSet B S hS X E.X₂ :=
    moduleSupportSet_subset_of_mono B S hS X E.f hE.mono_f
  have hs3 : moduleSupportSet B S hS X E.X₃ ⊆ moduleSupportSet B S hS X E.X₂ :=
    moduleSupportSet_subset_of_epi B S hS X E.g hE.epi_g
  exact hext E hE h1 h2 h3 (hP1 (hs1.trans hsub)) (hP3 (hs3.trans hsub))

/-! ### The step at a minimal subspace -/

/-- **The step of Stacks 08AN at a minimal reduced closed subspace.**  Let `Z ⊆ X` be a reduced
closed subspace with `|Z|` irreducible and let `I ⊆ 𝒪_Z` be quasi-coherent.  Granted hypotheses
(1), (2) and (3) for the property `P`, and granted `P` for every coherent module whose support
is strictly smaller than that of `i_*I`, the property holds for `i_*I`.

The zero sheaf of ideals is disposed of by `hzero`.  Otherwise hypothesis (3) provides a
coherent `G` with scheme-theoretic support `Z` and with `P`, Stacks 07UQ provides `r > 0`, a
nonzero `I₀ ⊆ 𝒪_Z` and a short exact sequence `0 → (i_*I₀)^{⊕r} → G → Q → 0` whose last term is
supported strictly inside `|Z|`, which is the support of `i_*I` as well as of `i_*I₀`; so `Q`
has `P` by hypothesis, `(i_*I₀)^{⊕r}` has `P` by the second implication of (1), `i_*I₀` has `P`
by (2), and `i_*I` has `P` by `AlgebraicGeometry.Space.idealPushforwardComparison`, the
comparison of `I₀` with `I` through `I₀ ⊓ I`. -/
theorem property_idealPushforward_of_property_of_lt (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (h07UH : IdealPushforwardCoherent B S hS X)
    (hinputs : ExistsSupportModuleAndGenericTrivialization B S hS X)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (h1 : TwoOutOfThreeCoherent B S hS X P) (h2 : ClosedUnderDirectSumDescent B S hS X P)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ))
    (hsmall : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
      moduleSupportSet B S hS X N ⊂ moduleSupportSet B S hS X
        ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) →
      P N) :
    P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  by_cases hI : I.1 = ⊥
  · exact hzero _ (isZero_modulePushforward_of_eq_bot B S hS X hZ I hI)
  obtain ⟨G, hGcoh, hGsupp, hGP⟩ := h3 Z hZ hint
  obtain ⟨r, I₀, hr, hI₀, hsumcoh, φ, hφ, Q, q, hq, ⟨hcol⟩, hQsupp⟩ :=
    existsIdealInjectionDevissageStep B S hS X hN h07UH hinputs G hGcoh Z hZ hint hGsupp
  have heq := idealPushforwardSupportConstant B S hS X hN Z hZ hint I₀ I hI₀ hI
  have hQcoh : IsCoherent B S hS X.1 X.2 Q :=
    isCoherent_of_iso B S hS X.2
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel φ) hcol)
      (isCoherent_cokernel B S hS X.1 X.2 hsumcoh hGcoh φ)
  have hSE : (ShortComplex.mk φ q hq).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hcol) hφ
      (epi_of_isColimit_cofork hcol)
  have hQP : P Q := hsmall Q hQcoh (heq ▸ hQsupp)
  have hsumP : P (⨁ fun _ : Fin r => (modulePushforward B S hS
      (closedSubfunctorι B S hS hZ)).obj I₀.1.toSheafOfModules) :=
    (h1 (ShortComplex.mk φ q hq) hSE hsumcoh hGcoh hQcoh).2.1 hGP hQP
  refine idealPushforwardComparison B S hS X hN h07UH P hzero h1 Z hZ hint I₀ I hI₀
    (fun N hNc hNlt => hsmall N hNc (heq ▸ hNlt)) (h2 _ r hr hsumP)

/-! ### The Noetherian induction -/

/-- **The Noetherian induction of Stacks 08AN.**  Granted the carried statements, the property
`P` holds for the direct image of every quasi-coherent sheaf of ideals on every reduced closed
subspace with irreducible space of points — which is hypothesis (2) of Stacks 07US.

The induction runs over the closed subsets of `|X|`, a Noetherian topological space because `X`
is a Noetherian algebraic space, and is indexed by the support of `i_*I`.  At a closed set `T`
the inductive hypothesis gives the conclusion for every direct image supported strictly inside
`T`, and `AlgebraicGeometry.Space.property_of_moduleSupportSet_subset` upgrades that to `P` for
every coherent module supported strictly inside `T`, which is what the step at a minimal
subspace consumes. -/
theorem forall_property_idealPushforward (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (hdev : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
      HasIdealDevissage B S hS X M)
    (h07UH : IdealPushforwardCoherent B S hS X)
    (hinputs : ExistsSupportModuleAndGenericTrivialization B S hS X)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (h1 : TwoOutOfThreeCoherent B S hS X P) (h2 : ClosedUnderDirectSumDescent B S hS X P)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ)) :
    P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) := by
  have _ : TopologicalSpace.NoetherianSpace (points B S hS X.1) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X.1 X.2 hX.1 hX.2.2
  have hext : ClosedUnderCoherentExtensions B S hS X P :=
    closedUnderCoherentExtensions_of_twoOutOfThreeCoherent B S hS X P h1
  have key : ∀ T : TopologicalSpace.Closeds (points B S hS X.1),
      ∀ (Z' : Subfunctor X.1) (hZ' : IsClosedSubspace B S hS Z'),
      IsReducedIrreducible B S hS Z' →
      ∀ I' : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ'),
      moduleSupportSet B S hS X ((modulePushforward B S hS
          (closedSubfunctorι B S hS hZ')).obj I'.1.toSheafOfModules) ⊆
        (T : Set (points B S hS X.1)) →
      P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ')).obj
        I'.1.toSheafOfModules) := by
    intro T
    refine wellFounded_lt.induction
      (C := fun T : TopologicalSpace.Closeds (points B S hS X.1) =>
        ∀ (Z' : Subfunctor X.1) (hZ' : IsClosedSubspace B S hS Z'),
        IsReducedIrreducible B S hS Z' →
        ∀ I' : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ'),
        moduleSupportSet B S hS X ((modulePushforward B S hS
            (closedSubfunctorι B S hS hZ')).obj I'.1.toSheafOfModules) ⊆
          (T : Set (points B S hS X.1)) →
        P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ')).obj
          I'.1.toSheafOfModules)) T ?_
    clear T
    intro T IH Z' hZ' hint' I' hsub
    refine property_idealPushforward_of_property_of_lt B S hS X hX.2.2 h07UH hinputs P hzero
      h1 h2 h3 Z' hZ' hint' I' ?_
    intro N hN hNlt
    have hNT : moduleSupportSet B S hS X N ⊂ (T : Set (points B S hS X.1)) :=
      hNlt.trans_le hsub
    exact property_of_moduleSupportSet_subset B S hS X hdev P hzero hext
      (moduleSupportSet B S hS X N)
      (IH ⟨moduleSupportSet B S hS X N, isClosed_moduleSupportSet B S hS X N hN⟩
        (SetLike.coe_ssubset_coe.mp hNT))
      N hN Set.Subset.rfl
  exact key ⊤ Z hZ hint I (Set.subset_univ _)

/-! ### Stacks 08AN -/

/-- **Stacks Project, Tag 08AN.**  Let `X` be a Noetherian algebraic space over a scheme `S`
and let `P` be a property of coherent `𝒪_X`-modules such that

1. for a short exact sequence of coherent modules, if two out of three terms have `P` then so
   does the third;
2. if `P` holds for the direct sum of `r ≥ 1` copies of a module, for some `r ≥ 1`, then it
   holds for that module;
3. for every reduced closed subspace `Z ⊆ X` with `|Z|` irreducible there is a coherent module
   on `X` whose scheme-theoretic support is `Z` and which has `P`.

Then `P` holds for every coherent module on `X`.

Three hypotheses are carried beyond the source's list, and each is discussed in the module
documentation.  None of them is mathematics of Stacks 08AN: each is the conclusion, or a named
clause, of another tag, and each is a statement that tag's own formalization here still carries.

* `hdev`, the conclusion of Stacks 07UR for every coherent module on `X`, which is
  `AlgebraicGeometry.Space.hasIdealDevissage_of_isCoherent`.
* `h07UH`, `AlgebraicGeometry.Space.IdealPushforwardCoherent`: the coherence clause of
  Stacks 07UH at the inclusion of a closed subspace and a quasi-coherent sheaf of ideals on it.
* `hinputs`, `AlgebraicGeometry.Space.ExistsSupportModuleAndGenericTrivialization`: the two
  inputs of Stacks 07UQ, namely the module on the scheme-theoretic support from
  Stacks 07U0 — which rests on the essential-image assertion of Stacks 04CJ part (3) — and the
  generically bijective map of the surjectivity half of Stacks 07UM.

Everything else — the Noetherian induction, the step at a minimal subspace, the equality of the
supports of the direct images of two nonzero sheaves of ideals on `Z`, the last paragraph of the
source's proof in `AlgebraicGeometry.Space.idealPushforwardComparison`, Stacks 07UQ itself in
`AlgebraicGeometry.Space.existsIdealInjectionDevissageStep`, and the passage from sheaves of
ideals to all coherent modules through Stacks 07US — is proved here.

The hypothesis `hzero` is not in the source's list and cannot be dropped, for the reason
recorded at the library's Stacks 07US: on an algebraic space with no points the property
`fun _ => False` satisfies the source's three conditions while the zero module is coherent and
does not have it. -/
@[stacks 08AN "the dévissage principle in its higher-rank form: the Noetherian induction, the \
minimal-subspace step, the support of a nonzero ideal direct image, the ideal-intersection \
paragraph and 07UQ in the shape the step consumes, from 07US, 07UR and 07UQ, carrying the \
conclusion of 07UR, the coherence clause of 07UH for the direct image of a quasi-coherent \
sheaf of ideals, and 07UQ's own two inputs: 07U0's module on the support and the surjectivity \
half of 07UM"]
theorem property_of_integralWitness_and_twoOutOfThree (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (hdev : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
      HasIdealDevissage B S hS X M)
    (h07UH : IdealPushforwardCoherent B S hS X)
    (hinputs : ExistsSupportModuleAndGenericTrivialization B S hS X)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (h1 : TwoOutOfThreeCoherent B S hS X P) (h2 : ClosedUnderDirectSumDescent B S hS X P)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) : P M :=
  property_of_forall_hasIdealDevissage B S hS X hdev P hzero
    (closedUnderCoherentExtensions_of_twoOutOfThreeCoherent B S hS X P h1)
    (fun Z hZ hint I =>
      forall_property_idealPushforward B S hS hZtop X hX hdev h07UH hinputs P hzero
        h1 h2 h3 Z hZ hint I)
    M hM

end AlgebraicGeometry.Space

end
