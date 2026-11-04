module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRankIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIrreducibleIdealInjection
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealInjectionDevissageStep

/-!
# The higher-rank dévissage principle on a Noetherian algebraic space

Stacks 08AN is the higher-rank variant of the dévissage principle Stacks 07US.  Where 07US asks
a property `P` of coherent modules on a Noetherian algebraic space `X` to hold for *every*
direct image `i_*I` of a quasi-coherent sheaf of ideals on a reduced closed subspace
`i : Z → X` with `|Z|` irreducible, the variant asks only that

1. for a short exact sequence of coherent modules, two of the three terms having `P` forces the
   third (`AlgebraicGeometry.Space.TwoOutOfThreeCoherent`);
2. `P` descends from a finite direct sum of `r ≥ 1` copies of a coherent module to the module
   (`AlgebraicGeometry.Space.ClosedUnderCoherentDirectSumDescent`);
3. every reduced closed subspace `Z ⊆ X` with `|Z|` irreducible carries *some* coherent module
   on `X` with `P`, namely one whose scheme-theoretic support is `Z`
   (`AlgebraicGeometry.Space.HasCoherentWitnessOnIntegralSubspaces`),

and concludes that `P` holds for every coherent module on `X`.

## Main definitions

* `AlgebraicGeometry.Space.ClosedUnderCoherentDirectSumDescent`: hypothesis (2) of Stacks 08AN,
  that `P` descends from a direct sum of `r ≥ 1` copies of a coherent module to the module.

## Main results

* `AlgebraicGeometry.Space.exists_mono_biproduct_idealPushforward_of_schemeTheoreticSupport_eq`:
  Stacks 07UQ with the direct sum taken outside the direct image: an injection
  `(i_*I)^{⊕r} ⟶ F` whose cokernel has support strictly smaller than that of `i_*I`.
* `AlgebraicGeometry.Space.property_idealPushforward_of_property_of_lt_of_isNoetherian`: for `P`
  holding on zero modules and satisfying (1), (2) and (3), `P` holds for `i_*I` once it holds for
  every coherent module of strictly smaller support.
* `AlgebraicGeometry.Space.forall_property_idealPushforward_of_isNoetherian`: for `P` holding on
  zero modules and satisfying (1), (2) and (3), `P` holds for every `i_*I`, which is hypothesis
  (2) of Stacks 07US.
* `AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree_of_isNoetherian`:
  **Stacks 08AN**, for a property which holds on zero modules.
* `AlgebraicGeometry.Space.forall_isZero_property_of_nonempty`: on an `X` with a point, (1) and
  (3) force `P` on every zero module.
* `AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree_of_nonempty`: Stacks
  08AN for an `X` with a point, with no hypothesis on zero modules.
* `AlgebraicGeometry.Space.not_forall_false_of_isEmpty_points`: on an `X` with no points the
  property `fun _ => False` satisfies (1), (2) and (3) and fails on a coherent module.

## Implementation notes

The source's statement does not ask the property to hold on zero modules, and it is false
without that for an `X` with no points: there the property `fun _ => False` satisfies (1), (2)
and (3), while the zero module is coherent and does not have it.  For an `X` with a point, (1)
and (3) already force `P` on every zero module, so the hypothesis `hzero` of the main statement
only corrects the empty case.

## References

* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Hypothesis (2) of Stacks 08AN -/

/-- **Hypothesis (2) of Stacks 08AN.**  If the property `P` holds for the direct sum of `r ≥ 1`
copies of a coherent module, then it holds for that module. -/
def ClosedUnderCoherentDirectSumDescent (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop) : Prop :=
  ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
    ∀ r : ℕ, 1 ≤ r → P (⨁ fun _ : Fin r => F) → P F

/-! ### Stacks 07UQ, in the shape the step consumes -/

/-- **Stacks 07UQ, in the shape the step of Stacks 08AN consumes.**  Let `X` be a Noetherian
algebraic space over `S`, let `F` be a coherent `𝒪_X`-module, and assume that the
scheme-theoretic support `Z` of `F` is reduced with `|Z|` irreducible.  Then there are an
integer `r > 0`, a nonzero quasi-coherent sheaf of ideals `I ⊆ 𝒪_Z` and an injective map of
coherent modules `φ : (i_*I)^{⊕ r} ⟶ F` whose cokernel `Q` has support strictly smaller than
the support of `i_*I`, which is `|Z|`. -/
theorem exists_mono_biproduct_idealPushforward_of_schemeTheoreticSupport_eq
    (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    {Z : Subfunctor X.1} (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (hsupp : schemeTheoreticSupport B S hS X F = Z) :
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
              I.1.toSheafOfModules) := by
  subst hsupp
  obtain ⟨hZ', r, I, hIq, hr, hI, hcoh, φ, hφ, Q, q, w, ⟨hcol⟩, T, -, hTne, hQ⟩ :=
    exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport B S hS hZtop X hX F hF hint
  let P := modulePushforward B S hS (closedSubfunctorι B S hS hZ)
  let I' : Modules.{u, u} B S hS (closedSubfunctorSpace B S hS hZ).1
      (closedSubfunctorSpace B S hS hZ).2 := I.toSheafOfModules
  let e : (⨁ fun _ : Fin r => P.obj I') ≅ P.obj (⨁ fun _ : Fin r => I') :=
    modulePushforwardBiproductConstIso B S hS X (closedSubfunctorι B S hS hZ) r
        I.toSheafOfModules ≪≫ P.mapIso (biproduct.isoProduct _).symm
  have hq : (e.hom ≫ φ) ≫ q = 0 := by rw [Category.assoc, w, comp_zero]
  have _ : Mono e.hom := IsIso.mono_of_iso e.hom
  have _ : Epi e.hom := IsIso.epi_of_iso e.hom
  refine ⟨r, ⟨I, hIq⟩, hr, hI, isCoherent_of_iso B S hS X.2 e.symm hcoh, e.hom ≫ φ,
    mono_comp e.hom φ, Q, q, hq, ⟨isCokernelEpiComp hcol e.hom rfl⟩, ?_⟩
  rw [moduleSupportSet_idealPushforward_eq_image B S hS X hX.2.2 hZ hint ⟨I, hIq⟩ hI]
  exact hQ.trans_ssubset (image_ssubset_image_univ
    (pointsMap_hom_injective_of_isClosedImmersion B S hS _ hZ.2) hTne)

/-! ### The step at a minimal subspace -/

/-- **The step of Stacks 08AN at a minimal reduced closed subspace.**  Let `Z ⊆ X` be a reduced
closed subspace with `|Z|` irreducible and let `I ⊆ 𝒪_Z` be quasi-coherent.  If the property
`P` holds on zero modules, satisfies hypotheses (1), (2) and (3), and holds for every coherent
module whose support is strictly smaller than that of `i_*I`, then it holds for `i_*I`. -/
theorem property_idealPushforward_of_property_of_lt_of_isNoetherian
    (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (h1 : TwoOutOfThreeCoherent B S hS X P) (h2 : ClosedUnderCoherentDirectSumDescent B S hS X P)
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
    exists_mono_biproduct_idealPushforward_of_schemeTheoreticSupport_eq B S hS hZtop X hX G
      hGcoh hZ hint hGsupp
  have heq := idealPushforwardSupportConstant B S hS X hX.2.2 Z hZ hint I₀ I hI₀ hI
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
  refine idealPushforwardComparison B S hS X hX.2.2
    (idealPushforwardCoherent B S hS X hX.2.2) P hzero h1 Z hZ hint I₀ I hI₀
    (fun N hNc hNlt => hsmall N hNc (heq ▸ hNlt)) (h2 _ ?_ r hr hsumP)
  exact isCoherent_modulePushforward_quasicoherentIdeal B S hS hX.2.2 _ hZ.2 I₀

/-! ### The Noetherian induction -/

/-- **The Noetherian induction of Stacks 08AN.**  If the property `P` holds on zero modules and
satisfies hypotheses (1), (2) and (3), then it holds for the direct image of every quasi-coherent
sheaf of ideals on every reduced closed subspace with irreducible space of points, which is
hypothesis (2) of Stacks 07US. -/
theorem forall_property_idealPushforward_of_isNoetherian (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (h1 : TwoOutOfThreeCoherent B S hS X P)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (h2 : ClosedUnderCoherentDirectSumDescent B S hS X P)
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ)) :
    P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) :=
  forall_property_idealPushforward_of_step B S hS hZtop X hX P hzero
    (closedUnderCoherentExtensions_of_twoOutOfThreeCoherent B S hS X P h1)
    (fun Z' hZ' hint' I' hsmall =>
      property_idealPushforward_of_property_of_lt_of_isNoetherian B S hS hZtop X hX
      P hzero h1 h2 h3 Z' hZ' hint' I' hsmall) Z hZ hint I

/-! ### Stacks 08AN -/

/-- **Stacks Project, Tag 08AN.**  Let `X` be a Noetherian algebraic space over a scheme `S`
and let `P` be a property of coherent `𝒪_X`-modules, holding on zero modules, such that

1. for a short exact sequence of coherent modules, if two out of three terms have `P` then so
   does the third;
2. if `P` holds for the direct sum of `r ≥ 1` copies of a module, for some `r ≥ 1`, then it
   holds for that module;
3. for every reduced closed subspace `Z ⊆ X` with `|Z|` irreducible there is a coherent module
   on `X` whose scheme-theoretic support is `Z` and which has `P`.

Then `P` holds for every coherent module on `X`.

The hypothesis `hzero` is not in the source's list, and the source's statement is false without
it when `X` has no points (`AlgebraicGeometry.Space.not_forall_false_of_isEmpty_points`); when
`X` has a point it follows from (1) and (3), which is
`AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree_of_nonempty`. -/
@[stacks 08AN "for a property which holds on zero modules: the source's statement fails for an \
X with no points, and for X with a point that hypothesis follows from (1) and (3)"]
theorem property_of_integralWitness_and_twoOutOfThree_of_isNoetherian
    (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (h1 : TwoOutOfThreeCoherent B S hS X P) (h2 : ClosedUnderCoherentDirectSumDescent B S hS X P)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) : P M :=
  property_of_forall_hasIdealDevissage B S hS X
    (fun N hN => hasIdealDevissage_of_isCoherent B S hS hZtop X hX N hN) P hzero
    (closedUnderCoherentExtensions_of_twoOutOfThreeCoherent B S hS X P h1)
    (fun Z hZ hint I =>
      forall_property_idealPushforward_of_isNoetherian B S hS hZtop X hX P hzero h1 h3 h2 Z hZ
        hint I)
    M hM

/-! ### The hypothesis on zero modules in Stacks 08AN -/

/-- **On an algebraic space with a point, hypotheses (1) and (3) of Stacks 08AN force the
property on every zero module.** -/
theorem forall_isZero_property_of_nonempty (X : AlgebraicSpaces B S hS)
    (hne : Nonempty (points B S hS X.1)) (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (h1 : TwoOutOfThreeCoherent B S hS X P)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsZero M) : P M := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  obtain ⟨x⟩ := hne
  have hirr : IsIrreducible (closure {x}) := isIrreducible_singleton.closure
  obtain ⟨G, hG, -, hPG⟩ := h3 _
    (isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 _ isClosed_closure)
    (isReducedIrreducible_reducedClosedSubspace B S hS X _ isClosed_closure hirr)
  have hSE : (ShortComplex.mk (0 : M ⟶ G) (𝟙 G) zero_comp).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _
      (KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance hM)) (hM.mono _) inferInstance
  exact (h1 _ hSE (IsCoherent.of_isZero B S hS X.1 X.2 hM) hG hG).2.1 hPG hPG

/-- **Stacks 08AN for an algebraic space with a point**, in the source's form: no hypothesis on
zero modules is needed, since (1) and (3) imply it there
(`AlgebraicGeometry.Space.forall_isZero_property_of_nonempty`). -/
theorem property_of_integralWitness_and_twoOutOfThree_of_nonempty
    (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (hne : Nonempty (points B S hS X.1)) (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (h1 : TwoOutOfThreeCoherent B S hS X P) (h2 : ClosedUnderCoherentDirectSumDescent B S hS X P)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) : P M :=
  property_of_integralWitness_and_twoOutOfThree_of_isNoetherian B S hS hZtop X hX P
    (forall_isZero_property_of_nonempty B S hS X hne P h1 h3) h1 h2 h3 M hM

/-- **Without the hypothesis on zero modules Stacks 08AN fails on an algebraic space with no
points**: there the property `fun _ => False` satisfies hypotheses (1), (2) and (3), while some
coherent module does not have it. -/
theorem not_forall_false_of_isEmpty_points (X : AlgebraicSpaces B S hS)
    (hX : IsEmpty (points B S hS X.1)) :
    TwoOutOfThreeCoherent B S hS X (fun _ => False) ∧
      ClosedUnderCoherentDirectSumDescent B S hS X (fun _ => False) ∧
      HasCoherentWitnessOnIntegralSubspaces B S hS X (fun _ => False) ∧
      ∃ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M ∧ ¬ False := by
  refine ⟨fun _ _ _ _ _ => ⟨fun h _ => h, fun h _ => h, fun h _ => h⟩, fun _ _ _ _ h => h,
    fun Z hZ hint => ?_, ?_⟩
  · exfalso
    have := hint.2
    obtain ⟨z⟩ := (inferInstance : Nonempty (points B S hS Z.toFunctor))
    exact hX.false (pointsMap B S hS Z.toFunctor Z.ι z)
  · obtain ⟨Zobj, hZobj⟩ := HasZeroObject.zero (C := Modules.{u, u} B S hS X.1 X.2)
    exact ⟨Zobj, IsCoherent.of_isZero B S hS X.1 X.2 hZobj, not_false⟩

end AlgebraicGeometry.Space

end
