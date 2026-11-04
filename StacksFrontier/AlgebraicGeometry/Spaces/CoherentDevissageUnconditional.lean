module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRankIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIrreducibleIdealInjection

/-!
# The dévissage of coherent modules on a Noetherian algebraic space, unconditionally

`AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree` proves Stacks 08AN over
three carried statements: the conclusion of Stacks 07UR, the coherence of the direct image of a
quasi-coherent sheaf of ideals on a closed subspace, and the two inputs of an earlier form of
Stacks 07UQ.  This file discharges all three.

## Main results

* `AlgebraicGeometry.Space.idealPushforwardCoherent` (in
  `StacksFrontier/AlgebraicGeometry/Spaces/CoherentDevissageHigherRankIdeal.lean`): on a locally
  Noetherian algebraic space the direct image of a quasi-coherent sheaf of ideals on a closed
  subspace is coherent.
* `AlgebraicGeometry.Space.existsIdealInjectionDevissageStep_of_isNoetherian`: Stacks 07UQ in
  the shape the dévissage consumes, from
  `AlgebraicGeometry.Space.exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport`.
* `AlgebraicGeometry.Space.property_idealPushforward_of_property_of_lt_of_step` and
  `AlgebraicGeometry.Space.forall_property_idealPushforward_of_coherentWitness`: the step at a
  minimal subspace and the Noetherian induction of the source's proof, with Stacks 07UQ taken in
  the form `AlgebraicGeometry.Space.ExistsIdealInjectionDevissageStep`.
* `AlgebraicGeometry.Space.property_of_isCoherent_of_devissage`: **Stacks 08AN.**

## Implementation notes

The hypothesis `hzero`, that the property holds for zero modules, is not in the source's list.
It cannot be dropped: on an algebraic space with no points the property `fun _ => False`
satisfies the three conditions of the source vacuously (there is no reduced closed subspace
with irreducible space of points), while the zero module is coherent.  On a nonempty `X` it is
implied by the source's conditions (1) and (3), applied to `0 → G → G → 0 → 0`.

## References

* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The step at a minimal subspace and the Noetherian induction, from 07UQ -/

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
theorem property_idealPushforward_of_property_of_lt_of_step (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (h07UH : IdealPushforwardCoherent B S hS X)
    (hstep : ExistsIdealInjectionDevissageStep B S hS X)
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
    hstep G hGcoh Z hZ hint hGsupp
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

/-- **The Noetherian induction of Stacks 08AN.**  Granted the carried statements, the property
`P` holds for the direct image of every quasi-coherent sheaf of ideals on every reduced closed
subspace with irreducible space of points — which is hypothesis (2) of Stacks 07US.

The induction runs over the closed subsets of `|X|`, a Noetherian topological space because `X`
is a Noetherian algebraic space, and is indexed by the support of `i_*I`.  At a closed set `T`
the inductive hypothesis gives the conclusion for every direct image supported strictly inside
`T`, and `AlgebraicGeometry.Space.property_of_moduleSupportSet_subset` upgrades that to `P` for
every coherent module supported strictly inside `T`, which is what the step at a minimal
subspace consumes. -/
theorem forall_property_idealPushforward_of_coherentWitness
    (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (hdev : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
      HasIdealDevissage B S hS X M)
    (h07UH : IdealPushforwardCoherent B S hS X)
    (hstep : ExistsIdealInjectionDevissageStep B S hS X)
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
      refine property_idealPushforward_of_property_of_lt_of_step B S hS X hX.2.2 h07UH hstep P hzero
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

/-- **Stacks 07UQ in the shape consumed by the dévissage of Stacks 08AN**, on a Noetherian
algebraic space.  This is
`AlgebraicGeometry.Space.exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport`, with
the direct sum taken outside the direct image and the support of the cokernel compared with the
support of the direct image of the sheaf of ideals. -/
theorem existsIdealInjectionDevissageStep_of_isNoetherian (hZt : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZt X.1) :
    ExistsIdealInjectionDevissageStep B S hS X := by
  intro F hF Z hZ hint hsupp
  subst hsupp
  obtain ⟨hZ', r, I, hIq, hr, hIb, hcoh, φ, hφ, Q, q, w, ⟨hcol⟩, T, hTc, hTne, hQ⟩ :=
    exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport B S hS hZt X hX F hF hint
  obtain rfl : hZ' = hZ := rfl
  let i := closedSubfunctorι B S hS hZ'
  let e : (⨁ fun _ : Fin r => (modulePushforward B S hS i).obj I.toSheafOfModules) ≅
      (modulePushforward B S hS i).obj (⨁ fun _ : Fin r => I.toSheafOfModules) :=
    modulePushforwardBiproductConstIso B S hS X i r I.toSheafOfModules ≪≫
      (modulePushforward B S hS i).mapIso (biproduct.isoProduct _).symm
  have hiff : ∀ ⦃W : Modules.{u, u} B S hS X.1 X.2⦄ (ξ : F ⟶ W),
      φ ≫ ξ = 0 ↔ (e.hom ≫ φ) ≫ ξ = 0 := by
    intro W ξ
    rw [Category.assoc]
    refine ⟨fun h => by rw [h, comp_zero], fun h => (cancel_epi e.hom).1 ?_⟩
    rw [h, comp_zero]
  have hme : Mono e.hom := IsIso.mono_of_iso _
  have hw : (e.hom ≫ φ) ≫ q = 0 := by rw [Category.assoc, w, comp_zero]
  refine ⟨r, ⟨I, hIq⟩, hr, hIb, isCoherent_of_iso B S hS X.2 e.symm hcoh, e.hom ≫ φ,
    @mono_comp _ _ _ _ _ e.hom hme φ hφ, Q, q, hw,
    ⟨CokernelCofork.isColimitOfIsColimitOfIff' hcol _ hiff⟩, ?_⟩
  rw [moduleSupportSet_idealPushforward_eq_image B S hS X hX.2.2 hZ' hint ⟨I, hIq⟩ hIb]
  exact lt_of_le_of_lt hQ (image_ssubset_image_univ
    (pointsMap_hom_injective_of_isClosedImmersion B S hS i hZ'.2) hTne)

/-- **Stacks Project, Tag 08AN.**  Let `X` be a Noetherian algebraic space over a scheme `S`
and let `P` be a property of coherent `𝒪_X`-modules such that

1. for a short exact sequence of coherent modules, if two out of three terms have `P` then so
   does the third;
2. if `P` holds for the direct sum of `r ≥ 1` copies of a module then it holds for that module;
3. for every reduced closed subspace `Z ⊆ X` with `|Z|` irreducible there is a coherent module
   on `X` whose scheme-theoretic support is `Z` and which has `P`.

Then `P` holds for every coherent module on `X`.

The hypothesis `hzero` is the one correction to the source's statement: see the module
documentation.  Nothing else is carried: the conclusion of Stacks 07UR is
`AlgebraicGeometry.Space.hasIdealDevissage_of_isCoherent`, the coherence of the direct image of
a sheaf of ideals is `AlgebraicGeometry.Space.idealPushforwardCoherent`, and Stacks 07UQ is
`AlgebraicGeometry.Space.existsIdealInjectionDevissageStep_of_isNoetherian`. -/
@[stacks 08AN "with the hypothesis that P holds for zero modules added: without it the \
statement fails on an algebraic space with no points, for the property False"]
theorem property_of_isCoherent_of_devissage (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (h1 : TwoOutOfThreeCoherent B S hS X P) (h2 : ClosedUnderDirectSumDescent B S hS X P)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) : P M := by
  have hdev := hasIdealDevissage_of_isCoherent B S hS hZtop X hX
  refine property_of_forall_hasIdealDevissage B S hS X hdev P hzero
    (closedUnderCoherentExtensions_of_twoOutOfThreeCoherent B S hS X P h1)
    (fun Z hZ hint I => forall_property_idealPushforward_of_coherentWitness B S hS hZtop X hX
      hdev (idealPushforwardCoherent B S hS X hX.2.2)
      (existsIdealInjectionDevissageStep_of_isNoetherian B S hS hZtop X hX) P hzero h1 h2 h3
      Z hZ hint I) M hM

end AlgebraicGeometry.Space

end
