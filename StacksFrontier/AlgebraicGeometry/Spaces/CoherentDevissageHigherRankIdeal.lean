module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIntersectionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealCoproductGenericIso
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupportIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealMeet
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport

/-!
# The dévissage principle of Stacks 08AN with the coherence clause of 07UH proved

`StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank` states the higher-rank form of
the dévissage principle, [Stacks, Tag 08AN], with three hypotheses beside the source's list: the
conclusion of Stacks 07UR, the coherence clause of Stacks 07UH for the direct image of a
quasi-coherent sheaf of ideals on a closed subspace
(`AlgebraicGeometry.Space.IdealPushforwardCoherent`), and the two inputs of the given-map form of
Stacks 07UQ (`AlgebraicGeometry.Space.ExistsSupportModuleAndGenericTrivialization`). This file
proves the last two, so that only the conclusion of Stacks 07UR stays a hypothesis.

## Main results

* `AlgebraicGeometry.Space.idealPushforwardCoherent`: the coherence clause of Stacks 07UH on a
  locally Noetherian algebraic space.
* `AlgebraicGeometry.Space.existsIdealInjectionDevissageStep'`: Stacks 07UQ in the shape
  `AlgebraicGeometry.Space.ExistsIdealInjectionDevissageStep`, from the form of 07UQ stated at
  the scheme-theoretic support.
* `AlgebraicGeometry.Space.property_idealPushforward_of_property_of_lt'` and
  `AlgebraicGeometry.Space.forall_property_idealPushforward'`: the minimal-subspace step and the
  Noetherian induction over closed subspaces.
* `AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree'`: **Stacks 08AN**, with
  the conclusion of Stacks 07UR the one argument beside the source's list.

## References

* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The coherence clause of Stacks 07UH.**  On a locally Noetherian algebraic space the direct
image of a quasi-coherent sheaf of ideals on a closed subspace is coherent, which is
`AlgebraicGeometry.Space.IdealPushforwardCoherent`.

The inclusion of a closed subspace is a closed immersion, and the direct image of a
quasi-coherent sheaf of ideals along a closed immersion into a locally Noetherian algebraic space
is coherent by `AlgebraicGeometry.Space.isCoherent_modulePushforward_quasicoherentIdeal`, which
is the submodule clause of Stacks 07UD applied to the coherent `i_*𝒪_Z`. -/
theorem idealPushforwardCoherent (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    IdealPushforwardCoherent B S hS X := fun _Z hZ I =>
  isCoherent_modulePushforward_quasicoherentIdeal B S hS hN (closedSubfunctorι B S hS hZ) hZ.2 I

/-- **Stacks 07UQ, in the shape `AlgebraicGeometry.Space.ExistsIdealInjectionDevissageStep`,** on a
Noetherian algebraic space.

It follows from Stacks 07UQ for the scheme-theoretic support of the module,
`AlgebraicGeometry.Space.exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport`; the
closed subspace `Z` of this statement *is* that support, which is what the hypothesis
`schemeTheoreticSupport B S hS X F = Z` says, so no instance of
`AlgebraicGeometry.Space.ExistsSupportModuleAndGenericTrivialization` — the module on the
support of Stacks 07U0 together with the surjectivity half of Stacks 07UM — is needed.

The two statements differ in three presentational points, none of them changing the content.

* The former produces the injection out of `i_*(I^{⊕r})`, as the source writes it, while this
  statement takes the direct sum outside the direct image. The two are identified by
  `AlgebraicGeometry.Space.modulePushforwardBiproductConstIso`, an isomorphism, so injectivity
  survives composition with it and `q` is still a cokernel of the composite — that last point is
  `CategoryTheory.Limits.CokernelCofork.isColimitOfIsColimitOfIff'`, the equivalence
  `φ ≫ ξ = 0 ↔ e ≫ φ ≫ ξ = 0` holding because `e` is an epimorphism. Coherence of the direct sum
  is transported across the same isomorphism, so the coherence clause of Stacks 07UH is not
  needed here either.
* The former bounds the support of the cokernel by the image of a closed `T' ⊊ |Z|`, which is *not*
  a strict bound on the nose; it becomes one because a closed immersion is injective on points, by
  `AlgebraicGeometry.Space.pointsMap_hom_injective_of_isClosedImmersion`, and because the support
  of `i_*I` is the image of all of `|Z|`, by
  `AlgebraicGeometry.Space.moduleSupportSet_idealPushforward_eq_image`.
* The former quantifies the closedness witness for the support existentially, while this
  statement takes it as an argument; `AlgebraicGeometry.Space.IsClosedSubspace` is a
  proposition, so the two witnesses describe the same closed subspace. -/
theorem existsIdealInjectionDevissageStep' (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1) :
    ExistsIdealInjectionDevissageStep B S hS X := by
  intro F hF Z hZ hint hsupp
  subst hsupp
  obtain ⟨hZ', n, I, hIq, hn, hIb, hcohsum, φ, hmφ, Q, q, hq, ⟨hcol⟩, T', hT'c, hT'ne, hQsupp⟩ :=
    exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport B S hS hZtop X hX F hF hint
  obtain rfl : hZ' = hZ := rfl
  have hsum := modulePushforwardBiproductConstIso B S hS X (closedSubfunctorι B S hS hZ') n
      I.toSheafOfModules ≪≫
    ((modulePushforward B S hS (closedSubfunctorι B S hS hZ')).mapIso
      (biproduct.isoProduct fun _ : Fin n => I.toSheafOfModules)).symm
  have hmsum : Mono hsum.hom := IsIso.mono_of_iso hsum.hom
  have hesum : Epi hsum.hom := IsIso.epi_of_iso hsum.hom
  have hiff : ∀ ⦃W : Modules.{u, u} B S hS X.1 X.2⦄ (ξ : F ⟶ W),
      φ ≫ ξ = 0 ↔ (hsum.hom ≫ φ) ≫ ξ = 0 := by
    intro W ξ
    rw [Category.assoc]
    refine ⟨fun h => by rw [h, comp_zero], fun h => (cancel_epi hsum.hom).1 ?_⟩
    rw [h, comp_zero]
  have hmono : Mono (hsum.hom ≫ φ) := mono_comp _ _
  have hcomp : (hsum.hom ≫ φ) ≫ q = 0 := by rw [Category.assoc, hq, comp_zero]
  refine ⟨n, ⟨I, hIq⟩, hn, hIb,
    isCoherent_of_iso B S hS X.2 hsum.symm hcohsum, hsum.hom ≫ φ, hmono, Q, q, hcomp,
    ⟨CokernelCofork.isColimitOfIsColimitOfIff' hcol _ hiff⟩, ?_⟩
  rw [moduleSupportSet_idealPushforward_eq_image B S hS X hX.2.2 hZ' hint ⟨I, hIq⟩ hIb]
  exact lt_of_le_of_lt hQsupp (image_ssubset_image_univ
    (pointsMap_hom_injective_of_isClosedImmersion B S hS (closedSubfunctorι B S hS hZ') hZ'.2)
    hT'ne)

/-! ### From sheaves of ideals to all coherent modules supported in a closed set -/
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
theorem property_idealPushforward_of_property_of_lt' (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
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
  have hN := hX.2.2
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  by_cases hI : I.1 = ⊥
  · exact hzero _ (isZero_modulePushforward_of_eq_bot B S hS X hZ I hI)
  obtain ⟨G, hGcoh, hGsupp, hGP⟩ := h3 Z hZ hint
  obtain ⟨r, I₀, hr, hI₀, hsumcoh, φ, hφ, Q, q, hq, ⟨hcol⟩, hQsupp⟩ :=
    existsIdealInjectionDevissageStep' B S hS hZtop X hX G hGcoh Z hZ hint hGsupp
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
  refine idealPushforwardComparison B S hS X hN (idealPushforwardCoherent B S hS X hN) P hzero
    h1 Z hZ hint I₀ I hI₀ (fun N hNc hNlt => hsmall N hNc (heq ▸ hNlt)) (h2 _ r hr hsumP)

/-! ### The Noetherian induction -/

/-- **The Noetherian induction of Stacks 08AN.** Granted `hdev`, `hzero` and hypotheses (1), (2)
and (3), the property `P` holds for the direct image of every quasi-coherent sheaf of ideals on
every reduced closed subspace with irreducible space of points — which is hypothesis (2) of
Stacks 07US.

The induction runs over the closed subsets of `|X|`, a Noetherian topological space because `X`
is a Noetherian algebraic space, and is indexed by the support of `i_*I`.  At a closed set `T`
the inductive hypothesis gives the conclusion for every direct image supported strictly inside
`T`, and `AlgebraicGeometry.Space.property_of_moduleSupportSet_subset` upgrades that to `P` for
every coherent module supported strictly inside `T`. -/
theorem forall_property_idealPushforward' (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (hdev : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
      HasIdealDevissage B S hS X M)
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
    induction T using WellFoundedLT.induction with
    | _ T IH =>
      intro Z' hZ' hint' I' hsub
      refine property_idealPushforward_of_property_of_lt' B S hS hZtop X hX P hzero
        h1 h2 h3 Z' hZ' hint' I' ?_
      intro N hN hNlt
      have hNT : moduleSupportSet B S hS X N ⊂ (T : Set (points B S hS X.1)) :=
        hNlt.trans_le hsub
      exact property_of_moduleSupportSet_subset B S hS hZtop X hX hdev P hzero hext
        (moduleSupportSet B S hS X N)
        (IH ⟨moduleSupportSet B S hS X N, isClosed_moduleSupportSet B S hS X N hN⟩
          (SetLike.coe_ssubset_coe.mp hNT))
        N hN Set.Subset.rfl
  exact key ⊤ Z hZ hint I (Set.subset_univ _)

/-! ### Stacks 08AN -/

/-- Let `X` be a Noetherian algebraic space over a scheme `S` and let `P` be a property of
coherent `𝒪_X`-modules such that

1. for a short exact sequence of coherent modules, if two out of three terms have `P` then so
   does the third;
2. if `P` holds for the direct sum of `r ≥ 1` copies of a module, for some `r ≥ 1`, then it
   holds for that module;
3. for every reduced closed subspace `Z ⊆ X` with `|Z|` irreducible there is a coherent module
   on `X` whose scheme-theoretic support is `Z` and which has `P`.

Then `P` holds for every coherent module on `X`.

One hypothesis stands beside the source's list, `hdev`: the conclusion of Stacks 07UR for every
coherent module on `X`, which is `AlgebraicGeometry.Space.hasIdealDevissage_of_isCoherent`.  It
is not mathematics of Stacks 08AN — it is the conclusion of another tag, stated in the shape
this proof uses.

Everything else is proved: the Noetherian induction, the step at a minimal subspace, the
equality of the supports of the direct images of two nonzero sheaves of ideals on `Z`, the last
paragraph of the source's proof in `AlgebraicGeometry.Space.idealPushforwardComparison`,
Stacks 07UQ in `AlgebraicGeometry.Space.existsIdealInjectionDevissageStep'`, and the passage
from sheaves of ideals to all coherent modules through Stacks 07US, with the coherence clause of
Stacks 07UH from `AlgebraicGeometry.Space.idealPushforwardCoherent`.

The hypothesis `hzero` is not in the source's list and cannot be dropped, for the reason recorded
at Stacks 07US: on an algebraic space with no points the property `fun _ => False` satisfies the
source's three conditions while the zero module is coherent and does not have it. -/
@[stacks 08AN "the dévissage principle in its higher-rank form: the Noetherian induction, the \
minimal-subspace step, the support of a nonzero ideal direct image, the ideal-intersection \
paragraph and 07UQ in the shape the step consumes, from 07US, 07UR and 07UQ. The one argument \
beside the source's list is the conclusion of 07UR for every coherent module on X"]
theorem property_of_integralWitness_and_twoOutOfThree' (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (hdev : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
      HasIdealDevissage B S hS X M)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (h1 : TwoOutOfThreeCoherent B S hS X P) (h2 : ClosedUnderDirectSumDescent B S hS X P)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) : P M :=
  property_of_forall_hasIdealDevissage B S hS X hdev P hzero
    (closedUnderCoherentExtensions_of_twoOutOfThreeCoherent B S hS X P h1)
    (fun Z hZ hint I =>
      forall_property_idealPushforward' B S hS hZtop X hX hdev P hzero
        h1 h2 h3 Z hZ hint I)
    M hM

end AlgebraicGeometry.Space

end
