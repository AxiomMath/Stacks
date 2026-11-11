module

public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImprovementExistenceClosed
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImprovementExistenceCounterexample
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImprovementPullback
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.LowDepthLocusClosure
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksCore.Tactic.StacksAttribute

/-!
# The corrected form of [Stacks, Tag 0DX5]

[Stacks, Tag 0DX5] asserts: for `X` Noetherian, universally catenary, with `(S₁)` formal fibres of
its local rings, `Z ⊆ X` closed and `F` coherent, there is a unique map `F → F''` of coherent
modules such that

1. `F_x → F''_x` is an isomorphism for `x ∉ Z`;
2. `F_x → F''_x` is surjective and `depth(F''_x) = 1` at every `x ∈ Z` *reached from outside*
   `Z` — an immediate specialization `x' ⤳ x` with `x' ∉ Z`, `x' ∈ Ass(F)` exists;
3. `depth(F''_x) ≥ 2` at the remaining `x ∈ Z`;

and its pullback along a Cohen–Macaulay morphism `Y → X` with `Y` Noetherian has the same
properties along the inverse image of `Z`.  In this library these conditions are
`AlgebraicGeometry.IsImprovement`.

## The existence clause is false

**The existence assertion is false at the source's own hypotheses.**  The refutation is the
theorem `Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf` of
`ImprovementExistenceCounterexample.lean` in this directory: `X = Spec k[u, v, w]`,
`Z = V(u, v)`, `F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~`, with all five hypotheses of the source
machine-checked in that file.  The point `(u, v, w)` is reached from `(u, w)`, so condition (2)
forces `F''` to agree there, and hence at its generalization `(u, v)`, with the depth-one quotient
`F'` of [Stacks, Tag 0DX3]; but `(u, v)` is not reached, `F'_{(u,v)}` is the maximal ideal of a
two-dimensional regular local ring, of depth one, and condition (3) asks for depth two.

The obstruction is general.  At a point `x ∈ Z` which *generalizes* a reached point `z`
(`AlgebraicGeometry.GeneralizesReached`), any map satisfying condition (2) at `z` is, at `x`, the
localization of an isomorphism `F'_z ≅ F''_z`, so `depth(F''_x) = depth(F'_x)` is forced, and
condition (3) at `x` holds only if `F'` already has depth two there.  Everything else in the
source survives: uniqueness (`AlgebraicGeometry.improvement_unique`) and the Cohen–Macaulay
pullback (`AlgebraicGeometry.isImprovement_pullback`) are proved as stated.

## The corrected forms

Both are at exactly the source's hypotheses, and change only the conclusion.

* **The existence clause, corrected to a criterion** —
  `AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient`: a map satisfying
  (1), (2) and (3) exists *if and only if* `F'` has depth at least two at every point of `Z` which
  generalizes a reached point without being one.  Together with
  `AlgebraicGeometry.improvement_unique` and `AlgebraicGeometry.isImprovement_pullback` this is
  [Stacks, Tag 0DX5] with its existence assertion, and nothing else, corrected; the counterexample
  is the case where the criterion fails at `(u, v)`.
* **The conditions, corrected so that existence holds** —
  `AlgebraicGeometry.existsUnique_isCorrectedImprovement`: replace condition (3), at the points
  of `Z` which generalize a reached point without being one, by what the counterexample shows to
  be the most that can be asked there, surjectivity on stalks and depth at least one
  (`AlgebraicGeometry.IsCorrectedImprovement`).  Then a map exists and is unique up to a unique
  isomorphism under `F`.  This is the theorem the source's construction proves, once its closed
  subset `Z'` is chosen correctly: the map is `F → F' → j_*(F'|_{X ∖ Z'})` with `Z'` the closure
  of the points of `Z` generalizing no reached point at which `F'` has depth at most one.  Its
  Cohen–Macaulay pullback is `AlgebraicGeometry.correctedImprovement_pullback`.

**Why the first is the primary form.**  The source's notion of an improvement is intrinsic: it is
stable under every Cohen–Macaulay pullback, open immersions included, so it is local on `X`, and
only its existence fails.  The corrected notion of the second form is not local: whether a point
generalizes a reached point depends on its specializations, which leave every neighbourhood.  In
the counterexample, on the open `D(w) ∌ (u, v, w)` nothing is reached any more, so the corrected
conditions for `F|_{D(w)}` demand depth two at `(u, v)`, while the corrected map of `F` restricts
there to a nonzero quotient of the maximal ideal of a two-dimensional regular local ring, which
has depth one.  So for the second form only the weaker pullback statement of
`AlgebraicGeometry.correctedImprovement_pullback` holds, in which the depth-two condition is
asked on the inverse image of the points of `Z` generalizing no reached point *of `X`*.  That the
intrinsic form fails is
`Stacks.ImprovementCounterexample.correctedImprovement_pullback_not_intrinsic` of
`CorrectedImprovementCounterexample.lean`.

## Main results

* `AlgebraicGeometry.closure_subset_specializations_of_lowDepth`: inside a closed subset along
  which a coherent module has depth at least one, the closure of a set of points of depth at most
  one is the union of the closures of its points.  This is [Stacks, Tag 0DWY] at the scheme
  level, and it is the step the source's proof is missing: it is what makes the closure of the
  bad locus avoid every point generalizing a reached point, where the source only controls the
  irreducible components `Z_{i,j}` through the reached points.
* `AlgebraicGeometry.IsCorrectedImprovement`, `AlgebraicGeometry.GeneralizesReached` and
  `AlgebraicGeometry.NotGeneralizingReached`: the corrected conditions.
* `AlgebraicGeometry.correctedImprovement_unique` and
  `AlgebraicGeometry.exists_isCorrectedImprovement_and_depth_eq`: uniqueness, and existence with
  the depth of the target equal to that of `F'` at the points generalizing a reached point.
* `AlgebraicGeometry.existsUnique_isCorrectedImprovement`: the corrected form, existence and
  uniqueness together.
* `AlgebraicGeometry.correctedImprovement_pullback`: its Cohen–Macaulay pullback.
* `AlgebraicGeometry.isCorrectedImprovement_of_isImprovement`: an improvement in the sense of the
  source satisfies the corrected conditions.
* `AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient`: the existence
  clause of the source, corrected to a necessary and sufficient criterion.
* `AlgebraicGeometry.exists_isImprovement_iff_and_unique_and_isImprovement_pullback`: the whole of
  [Stacks, Tag 0DX5] in corrected form, in one statement: the existence criterion, uniqueness and
  the Cohen–Macaulay pullback.

## Implementation notes

The corrected conditions are those of an improvement along the nested pair
`AlgebraicGeometry.NotGeneralizingReached Z F ⊆ Z` (`AlgebraicGeometry.IsNestedImprovement`,
[Stacks, Tag 0EI4]) together with depth exactly one at the reached points, which is automatic
(`AlgebraicGeometry.depth_stalk_le_one_of_reachedFromOutside`).  So uniqueness is
`AlgebraicGeometry.nestedImprovement_unique`, and the pullback is
`AlgebraicGeometry.isNestedImprovement_pullback`, sharpened at the points reached upstairs.

Existence pushes `F'` forward from the complement `U` of the closure of the bad locus
`{x ∈ NotGeneralizingReached Z F | depth(F'_x) ≤ 1}`.  By
`AlgebraicGeometry.closure_subset_specializations_of_lowDepth` every point of that closure
specializes from a point of the bad locus, so it generalizes no reached point; in particular
every reached point lies in `U`, which is the dimension condition of Kollár's criterion
[Stacks, Tag 0AWB], in the form
`AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_notReachedFromOutside`;
and every point generalizing a reached point lies in `U`, where the extension does not change
`F'`.  The ring-level form of the closure statement is
`Stacks.Algebraization.closure_lowDepth_subset_specializations`, transported along an affine open
neighbourhood exactly as in
`AlgebraicGeometry.closure_lowDepthLocus_subset_of_hasDualizingComplex`.

For the criterion, an improvement in the source's sense satisfies the corrected conditions — the
surjectivity at a point generalizing a reached point `z` is the surjectivity at `z` localized
(`Stacks.ImprovementCounterexample.epi_stalkFunctor_map_of_specializes`) — so by uniqueness it is
isomorphic to the corrected map, whose target has the depth of `F'` at those points.

The module structure on a stalk is spelled out as
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier` wherever a
depth appears, as in `AlgebraicGeometry.IsImprovement`.

## References

* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0DWY](https://stacks.math.columbia.edu/tag/0DWY)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0EI4](https://stacks.math.columbia.edu/tag/0EI4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The closure of a set of small depth, along a closed set of positive depth.**  Let `G` be a
coherent module on a locally Noetherian scheme `X` and `Z ⊆ X` a closed subset at every point of
which `depth(G_x) ≥ 1`.  If `B ⊆ Z` consists of points at which `depth(G_x) ≤ 1`, then every point
of the closure of `B` is a specialization of a point of `B`.

This is [Stacks, Tag 0DWY] in the form
`Stacks.Algebraization.closure_lowDepth_subset_specializations`, transported along an affine
open neighbourhood `U ≅ Spec Γ(X, U)` of the point: an open set meets a closure in the closure
taken inside it, and the depth of a stalk is the depth of the localized
sections (`Stacks.ModuleStalkSpecialization.depth_stalk_eq_depth_localizedModule`). -/
public theorem closure_subset_specializations_of_lowDepth {X : Scheme.{u}}
    [IsLocallyNoetherian X]
    (G : X.Modules) [G.IsCoherent] {Z : Set X} (hZ : IsClosed Z)
    (hdepth : ∀ x ∈ Z,
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))
    {B : Set X} (hBZ : B ⊆ Z)
    (hB : ∀ x ∈ B,
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x
      ¬ (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)) :
    closure B ⊆ {y | ∃ x ∈ B, x ⤳ y} := by
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G
  intro w hw
  obtain ⟨V, hV, hwV, -⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show w ∈ (⊤ : X.Opens) from trivial)
  let U : X.affineOpens := ⟨V, hV⟩
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite Γ(X, U.1) Γ(G, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections G U.2
  obtain ⟨f, hfemb, hfe, hfd⟩ :
      ∃ f : PrimeSpectrum Γ(X, U.1) → X, Topology.IsOpenEmbedding f ∧
        (∀ y : U.1, f (U.2.primeIdealOf y) = (y : X)) ∧
        (∀ p : PrimeSpectrum Γ(X, U.1),
          let : Module (X.presheaf.stalk (f p))
              (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f p)) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) G.val (f p)
          Module.depth (X.presheaf.stalk (f p))
              (IsLocalRing.maximalIdeal (X.presheaf.stalk (f p)))
              (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f p)) =
            Module.depth (Localization.AtPrime p.asIdeal)
              (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl Γ(G, U.1))) := by
    refine ⟨fun p => Subtype.val (U.2.isoSpec.hom.homeomorph.symm p),
      U.1.isOpen.isOpenEmbedding_subtypeVal.comp
        U.2.isoSpec.hom.homeomorph.symm.isOpenEmbedding,
      fun y => congrArg Subtype.val (U.2.isoSpec.hom.homeomorph.symm_apply_apply y),
      fun p => ?_⟩
    have hb : U.2.primeIdealOf (U.2.isoSpec.hom.homeomorph.symm p) = p :=
      U.2.isoSpec.hom.homeomorph.apply_symm_apply p
    have h := Stacks.ModuleStalkSpecialization.depth_stalk_eq_depth_localizedModule G U.2
        (U.2.isoSpec.hom.homeomorph.symm p)
    rwa [hb] at h
  have hy : U.2.primeIdealOf ⟨w, hwV⟩ ∈ f ⁻¹' closure B := by
    rwa [Set.mem_preimage, hfe ⟨w, hwV⟩]
  rw [hfemb.isOpenMap.preimage_closure_eq_closure_preimage hfemb.continuous] at hy
  obtain ⟨p, hpB, hpw⟩ := Stacks.Algebraization.closure_lowDepth_subset_specializations
    (M := Γ(G, U.1)) (f ⁻¹' Z) (hZ.preimage hfemb.continuous)
    (fun p hp => (hfd p).symm ▸ hdepth (f p) hp) (f ⁻¹' B) (Set.preimage_mono hBZ)
    (fun p hp => (hfd p).symm ▸ hB (f p) hp) hy
  refine ⟨f p, hpB, ?_⟩
  have h := hpw.map hfemb.continuous
  rwa [hfe ⟨w, hwV⟩] at h

/-- A point `x` *generalizes a reached point* of `Z` for `F` when `x ⤳ z` for some point `z ∈ Z`
reached from outside `Z` for `F`, that is a point at which condition (2) of [Stacks, Tag 0DX5]
is imposed.  At such a point of `Z` an improvement is forced to agree with the depth-one quotient
of `F`, which is what refutes the existence clause of the source. -/
public def GeneralizesReached {X : Scheme.{u}} (Z : Set X) (F : X.Modules) (x : X) : Prop :=
  ∃ z : X, z ∈ Z ∧ ReachedFromOutside Z F z ∧ x ⤳ z

/-- The points of `Z` which generalize no point of `Z` reached from outside `Z` for `F`: the
points at which the corrected conditions keep the source's depth-two condition (3). -/
public def NotGeneralizingReached {X : Scheme.{u}} (Z : Set X) (F : X.Modules) : Set X :=
  {x | x ∈ Z ∧ ¬ GeneralizesReached Z F x}

/-- **The corrected conditions of [Stacks, Tag 0DX5].**  A map `φ : F ⟶ G` to a coherent module
such that

1. `φ` is an isomorphism on the stalks at the points outside `Z`;
2. at a point of `Z` reached from outside `Z`, `φ` is surjective on stalks and `depth(G_x) = 1`;
2'. at a point of `Z` which is not reached but generalizes a reached point, `φ` is surjective on
   stalks and `depth(G_x) ≥ 1`;
3. at the remaining points of `Z`, `depth(G_x) ≥ 2`.

Conditions (1), (2) and (3) are the source's, verbatim (`AlgebraicGeometry.IsImprovement`), except
that (3) is no longer imposed at the points of (2'), where
`Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf` shows it cannot be imposed;
(2') records what is forced there instead. -/
public def IsCorrectedImprovement {X : Scheme.{u}} (Z : Set X) {F G : X.Modules} (φ : F ⟶ G) :
    Prop :=
  G.IsCoherent ∧
    (∀ x : X, x ∉ Z →
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)) ∧
    (∀ x : X, x ∈ Z → ReachedFromOutside Z F x →
      Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) ∧
        (letI : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val x
        Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) = (1 : ℕ∞))) ∧
    (∀ x : X, x ∈ Z → ¬ ReachedFromOutside Z F x → GeneralizesReached Z F x →
      Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) ∧
        (letI : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val x
        (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))) ∧
    (∀ x : X, x ∈ Z → ¬ GeneralizesReached Z F x →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))

/-- A point of `Z` reached from outside `Z` generalizes a reached point, namely itself. -/
public theorem generalizesReached_of_reachedFromOutside {X : Scheme.{u}} {Z : Set X}
    {F : X.Modules} {x : X} (hx : x ∈ Z) (hr : ReachedFromOutside Z F x) :
    GeneralizesReached Z F x :=
  ⟨x, hx, hr, specializes_rfl⟩

/-- The corrected conditions along `Z` give an improvement along the nested pair
`NotGeneralizingReached Z F ⊆ Z`: at the points of `Z` generalizing a reached point both (2) and
(2') give surjectivity and depth at least one. -/
public theorem isNestedImprovement_of_isCorrectedImprovement {X : Scheme.{u}} {Z : Set X}
    {F G : X.Modules} {φ : F ⟶ G} (h : IsCorrectedImprovement Z φ) :
    IsNestedImprovement Z (NotGeneralizingReached Z F) φ := by
  refine ⟨h.1, h.2.1, fun x hx hx' => ?_, fun x hx => h.2.2.2.2 x hx.1 hx.2⟩
  have hg : GeneralizesReached Z F x := not_not.mp fun hc => hx' ⟨hx, hc⟩
  by_cases hr : ReachedFromOutside Z F x
  · exact ⟨(h.2.2.1 x hx hr).1, le_of_eq (h.2.2.1 x hx hr).2.symm⟩
  · exact h.2.2.2.1 x hx hr hg

/-- At a point of `T` reached from outside `T` and outside `T'`, a nested improvement is surjective
on stalks and its target has depth exactly one. -/
private theorem epi_and_depth_eq_one_of_isNestedImprovement {X : Scheme.{u}}
    [IsLocallyNoetherian X] {T T' : Set X} {F G : X.Modules} {φ : F ⟶ G}
    (h : IsNestedImprovement T T' φ) {x : X} (hx : x ∈ T) (hr : ReachedFromOutside T F x)
    (hx' : x ∉ T') :
    Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) ∧
      (letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) = (1 : ℕ∞)) := by
  have : G.IsCoherent := h.1
  exact ⟨(h.2.2.1 x hx hx').1, le_antisymm
    (depth_stalk_le_one_of_reachedFromOutside φ h.2.1 x hr) (h.2.2.1 x hx hx').2⟩

/-- Conversely, an improvement along the nested pair `NotGeneralizingReached Z F ⊆ Z` satisfies
the corrected conditions: the depth at a reached point is at least one by the nested condition and
at most one by `AlgebraicGeometry.depth_stalk_le_one_of_reachedFromOutside`. -/
public theorem isCorrectedImprovement_of_isNestedImprovement {X : Scheme.{u}}
    [IsLocallyNoetherian X] {Z : Set X} {F G : X.Modules} {φ : F ⟶ G}
    (h : IsNestedImprovement Z (NotGeneralizingReached Z F) φ) : IsCorrectedImprovement Z φ := by
  exact ⟨h.1, h.2.1, fun x hx hr => epi_and_depth_eq_one_of_isNestedImprovement h hx hr
      fun hc => hc.2 (generalizesReached_of_reachedFromOutside hx hr),
    fun x hx _ hg => h.2.2.1 x hx fun hc => hc.2 hg, fun x hx hg => h.2.2.2 x ⟨hx, hg⟩⟩

/-- **Uniqueness under the corrected conditions.**  Two maps out of a coherent module satisfying
the corrected conditions along a closed subset are isomorphic by a unique isomorphism under the
module.  This is `AlgebraicGeometry.nestedImprovement_unique` for the nested pair
`NotGeneralizingReached Z F ⊆ Z`; no hypothesis on `X` beyond Noetherianity is used. -/
public theorem correctedImprovement_unique (X : Scheme.{u}) [IsNoetherian X] (Z : Set X)
    (hZ : IsClosed Z) (F G H : X.Modules) [F.IsCoherent] (φ : F ⟶ G) (ψ : F ⟶ H)
    (hφ : IsCorrectedImprovement Z φ) (hψ : IsCorrectedImprovement Z ψ) :
    ∃! e : G ≅ H, φ ≫ e.hom = ψ :=
  nestedImprovement_unique X Z (NotGeneralizingReached Z F) hZ.stableUnderSpecialization F G H φ ψ
    (isNestedImprovement_of_isCorrectedImprovement hφ)
    (isNestedImprovement_of_isCorrectedImprovement hψ)

/-- **Existence under the corrected conditions, at the source's hypotheses.**  On a Noetherian,
universally catenary scheme whose local rings have `(S₁)` formal fibres, a coherent module `F`
admits a map `F ⟶ G` satisfying the corrected conditions along a closed subset `Z`, whose target
has, at every point of `Z` generalizing a reached point, the depth of the depth-one quotient `F'`
of `F` along `Z`.

The map is `F → F' → j_*(F'|_U)` with `U` the complement of the closure of the bad locus
`{x ∈ NotGeneralizingReached Z F | depth(F'_x) ≤ 1}`; see the implementation notes of this
module. -/
public theorem exists_isCorrectedImprovement_and_depth_eq (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : IsClosed Z) (F : X.Modules) [F.IsCoherent]
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsCorrectedImprovement Z φ ∧
      ∀ x : X, x ∈ Z → GeneralizesReached Z F x →
        letI : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val x
        letI : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u})
              (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) (depthOneQuotient X Z hZ.stableUnderSpecialization F).val x
        Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) =
          Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (TopCat.Presheaf.stalk (C := Ab.{u})
              (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x) := by
  have hZs := hZ.stableUnderSpecialization
  have hq := depthOneQuotient_spec X Z hZs F
  have : (depthOneQuotient X Z hZs F).IsCoherent := hq.1
  -- the points far from the reached points at which the depth-one quotient has small depth
  let B : Set X := {x | x ∈ NotGeneralizingReached Z F ∧
    let : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZs F).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (depthOneQuotient X Z hZs F).val x
    ¬ (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZs F).val.presheaf x)}
  have hBZ : B ⊆ Z := fun x hx => hx.1.1
  have hcl : closure B ⊆ {y | ∃ x ∈ B, x ⤳ y} :=
    closure_subset_specializations_of_lowDepth (depthOneQuotient X Z hZs F) hZ
      (fun x hx => hq.2.2.2 x hx) hBZ (fun x hx => hx.2)
  -- the closure of `B` consists of points of `Z` far from the reached points
  have hclNot : closure B ⊆ NotGeneralizingReached Z F := by
    intro y hy
    obtain ⟨x, hxB, hxy⟩ := hcl hy
    refine ⟨closure_minimal hBZ hZ hy, fun ⟨z, hz, hrz, hyz⟩ => hxB.1.2 ⟨z, hz, hrz, hxy.trans hyz⟩⟩
  let U : X.Opens := ⟨(closure B)ᶜ, isClosed_closure.isOpen_compl⟩
  have hUc : ((U : Set X))ᶜ = closure B := compl_compl _
  have hUZ : ((U : Set X))ᶜ ⊆ Z := hUc ▸ fun y hy => (hclNot hy).1
  have hUnr : ((U : Set X))ᶜ ⊆ NotReachedFromOutside Z F := hUc ▸ fun y hy =>
    ⟨(hclNot hy).1, fun hr => (hclNot hy).2 (generalizesReached_of_reachedFromOutside
      (hclNot hy).1 hr)⟩
  have := isCoherent_pushforward_restrict_depthOneQuotient_of_notReachedFromOutside
    X Z hZs F U hUnr hX hFibres
  have hn := isNestedImprovement_toDepthOneQuotient_comp_unit X Z hZs F U hUZ
  -- a point generalizing a reached point lies in `U`
  have hnearU : ∀ x : X, GeneralizesReached Z F x → x ∈ (U : Set X) := fun x hg hc =>
    (hclNot hc).2 hg
  refine ⟨_, _, isCorrectedImprovement_of_isNestedImprovement ⟨hn.1, hn.2.1, ?_, ?_⟩,
    fun x _ hg => ?_⟩
  · intro x hx hx'
    exact hn.2.2.1 x hx fun hc =>
      hc (hnearU x (not_not.mp fun h => hx' ⟨hx, h⟩))
  · -- a far point: either outside `U`, or in `U` and then outside `B`
    intro x hx
    by_cases hxU : x ∈ (U : Set X)
    · have heq := depth_stalk_pushforward_restrict_eq_of_mem (depthOneQuotient X Z hZs F) U x hxU
      dsimp only [Functor.comp_obj] at heq ⊢
      rw [← heq]
      exact not_not.mp fun h => hxU (subset_closure ⟨hx, h⟩)
    · exact hn.2.2.2 x hxU
  · have heq := depth_stalk_pushforward_restrict_eq_of_mem (depthOneQuotient X Z hZs F) U x
      (hnearU x hg)
    dsimp only [Functor.comp_obj] at heq ⊢
    exact heq.symm

/-- Let `φ` satisfy the corrected conditions along `Z` and let `f : Y ⟶ X` be Cohen–Macaulay. A
point of `Y` reached from outside `f^{-1}(Z)` for `f^*F` lies over a point of `Z` generalizing a
reached point: otherwise the pullback would have depth at least two there by the nested pullback,
against the bound of one at a reached point. -/
public theorem notMem_notGeneralizingReached_of_reachedFromOutside_pullback {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {Z : Set X} {F G : X.Modules} (φ : F ⟶ G)
    (hφ : IsCorrectedImprovement Z φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib)
    (y : Y) (hr : ReachedFromOutside (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y) :
    f.base y ∉ NotGeneralizingReached Z F := by
  intro hfar
  have hn := isNestedImprovement_pullback φ (isNestedImprovement_of_isCorrectedImprovement hφ)
    f hfib hcm
  have : ((Scheme.Modules.pullback f).obj G).IsCoherent := hn.1
  exact absurd ((hn.2.2.2 y hfar).trans
    (depth_stalk_le_one_of_reachedFromOutside ((Scheme.Modules.pullback f).map φ) hn.2.1 y hr))
    (by norm_num)

/-- **The Cohen–Macaulay pullback under the corrected conditions.**  Let `φ : F ⟶ G` satisfy the
corrected conditions along `Z` and let `f : Y ⟶ X` be a Cohen–Macaulay morphism of Noetherian
schemes.  Then `f^*φ` has coherent target, is an isomorphism on stalks off `f^{-1}(Z)`, satisfies
condition (2) at the points of `f^{-1}(Z)` reached from outside `f^{-1}(Z)` for `f^*F` and
condition (2') at the points generalizing those, intrinsically upstairs; and it has depth at
least two at the points of `f^{-1}(Z)` lying over a point of `Z` generalizing no reached point.

The last clause is not condition (3) for `f^*F`: that would ask depth two at every point of
`f^{-1}(Z)` generalizing no point reached upstairs, and it fails already for the open immersion
`D(w) ⊆ Spec k[u, v, w]` of the counterexample:
`Stacks.ImprovementCounterexample.correctedImprovement_pullback_not_intrinsic`.

This is `AlgebraicGeometry.isNestedImprovement_pullback` for the nested pair
`NotGeneralizingReached Z F ⊆ Z`, with the points reached upstairs placed over points of `Z`
generalizing a reached point by
`AlgebraicGeometry.notMem_notGeneralizingReached_of_reachedFromOutside_pullback`. -/
@[stacks 0DX5 "corrected form (conditions corrected so that existence holds; the source's \
existence clause is false, Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf): \
the pullback of the corrected map along a Cohen-Macaulay morphism with Noetherian source \
satisfies (1), (2) and the corrected surjectivity-and-depth-one condition along f^{-1}(Z), and the \
depth-two condition on the inverse image of the points of Z generalizing no point as in (2)"]
public theorem correctedImprovement_pullback {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] {Z : Set X} {F G : X.Modules} (φ : F ⟶ G)
    (hφ : IsCorrectedImprovement Z φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib) :
    ((Scheme.Modules.pullback f).obj G).IsCoherent ∧
      (∀ y : Y, y ∉ f.base ⁻¹' Z →
        IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
          ((Scheme.Modules.pullback f).map φ).mapPresheaf)) ∧
      (∀ y : Y, y ∈ f.base ⁻¹' Z →
        ReachedFromOutside (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y →
        Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
          ((Scheme.Modules.pullback f).map φ).mapPresheaf) ∧
          (letI : Module (Y.presheaf.stalk y)
              (TopCat.Presheaf.stalk (C := Ab.{u})
                ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
          Module.depth (Y.presheaf.stalk y) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
            (TopCat.Presheaf.stalk (C := Ab.{u})
              ((Scheme.Modules.pullback f).obj G).val.presheaf y) = (1 : ℕ∞))) ∧
      (∀ y : Y, y ∈ f.base ⁻¹' Z →
        ¬ ReachedFromOutside (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y →
        GeneralizesReached (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y →
        Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
          ((Scheme.Modules.pullback f).map φ).mapPresheaf) ∧
          (letI : Module (Y.presheaf.stalk y)
              (TopCat.Presheaf.stalk (C := Ab.{u})
                ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
          (1 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
            (TopCat.Presheaf.stalk (C := Ab.{u})
              ((Scheme.Modules.pullback f).obj G).val.presheaf y))) ∧
      (∀ y : Y, y ∈ f.base ⁻¹' Z → ¬ GeneralizesReached Z F (f.base y) →
        letI : Module (Y.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u})
              ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
        (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (TopCat.Presheaf.stalk (C := Ab.{u})
            ((Scheme.Modules.pullback f).obj G).val.presheaf y)) := by
  have hn := isNestedImprovement_pullback φ (isNestedImprovement_of_isCorrectedImprovement hφ)
    f hfib hcm
  have : ((Scheme.Modules.pullback f).obj G).IsCoherent := hn.1
  -- a point of the inverse image generalizing a point reached upstairs lies over a point of `Z`
  -- generalizing a reached point
  have hnear : ∀ y : Y, y ∈ f.base ⁻¹' Z →
      GeneralizesReached (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y →
      f.base y ∉ NotGeneralizingReached Z F := by
    rintro y - ⟨y₀, hy₀Z, hr₀, hyy₀⟩ ⟨-, hfar⟩
    have h₀ := notMem_notGeneralizingReached_of_reachedFromOutside_pullback φ hφ f hfib hcm y₀ hr₀
    exact h₀ ⟨hy₀Z, fun ⟨z, hz, hrz, hy₀z⟩ =>
      hfar ⟨z, hz, hrz, (hyy₀.map f.base.hom.continuous).trans hy₀z⟩⟩
  exact ⟨hn.1, hn.2.1, fun y hy hr => epi_and_depth_eq_one_of_isNestedImprovement hn hy hr
      (hnear y hy (generalizesReached_of_reachedFromOutside hy hr)),
    fun y hy _ hg => hn.2.2.1 y hy (hnear y hy hg), fun y hy hg => hn.2.2.2 y ⟨hy, hg⟩⟩

/-- An improvement in the sense of [Stacks, Tag 0DX5] satisfies the corrected conditions: at a
point of `Z` generalizing a reached point `z`, surjectivity is the surjectivity at `z` carried to
the generalization by `Stacks.ImprovementCounterexample.epi_stalkFunctor_map_of_specializes`, and
the depth is at least two, hence at least one, by condition (3). -/
public theorem isCorrectedImprovement_of_isImprovement {X : Scheme.{u}} {Z : Set X}
    {F G : X.Modules} {φ : F ⟶ G} (h : IsImprovement Z φ) : IsCorrectedImprovement Z φ := by
  have : G.IsCoherent := h.1
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  refine ⟨h.1, h.2.1, h.2.2.1, fun x hx hr ⟨z, hz, hrz, hxz⟩ => ⟨?_, ?_⟩,
    fun x hx hg => h.2.2.2 x hx fun hr => hg (generalizesReached_of_reachedFromOutside hx hr)⟩
  · exact Stacks.ImprovementCounterexample.epi_stalkFunctor_map_of_specializes φ hxz
      (h.2.2.1 z hz hrz).1
  · exact le_trans (by norm_num) (h.2.2.2 x hx hr)

/-- **Stacks Project, Tag 0DX5, corrected form: the conditions corrected so that existence
holds.**  The existence clause of the source is false
(`Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf`).  Let `X` be a Noetherian,
universally catenary scheme whose local rings have `(S₁)` formal fibres, `Z ⊆ X` closed and `F`
coherent.  Then there is a map `F ⟶ G` satisfying the corrected conditions
`AlgebraicGeometry.IsCorrectedImprovement` along `Z` — the source's (1), (2) and (3), except that
at the points of `Z` which generalize a point as in (2) without being one, (3) is replaced by
surjectivity on stalks and depth at least one — and any two such maps are isomorphic by a unique
isomorphism under `F`.

This is the theorem the source's construction proves once its closed subset is chosen as the
closure of the bad locus.  Its pullback along a Cohen–Macaulay morphism is
`AlgebraicGeometry.correctedImprovement_pullback`; the source's own conditions, whose existence is
characterized by `AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient`, are
the primary corrected form, for the reason given in the module docstring. -/
@[stacks 0DX5 "corrected form (conditions corrected so that existence holds): the source's \
existence clause is false, refuted by \
Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf; with condition (3) at the \
points of Z which generalize a point as in (2) without being one replaced by surjectivity on \
stalks and depth at least one, a map F -> F'' exists and is unique up to a unique isomorphism \
under F, at exactly the source's hypotheses"]
public theorem existsUnique_isCorrectedImprovement (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : IsClosed Z) (F : X.Modules) [F.IsCoherent]
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsCorrectedImprovement Z φ ∧
      ∀ (H : X.Modules) (ψ : F ⟶ H), IsCorrectedImprovement Z ψ →
        ∃! e : G ≅ H, φ ≫ e.hom = ψ := by
  obtain ⟨G, φ, hφ, -⟩ := exists_isCorrectedImprovement_and_depth_eq X Z hZ F hX hFibres
  exact ⟨G, φ, hφ, fun H ψ hψ => correctedImprovement_unique X Z hZ F G H φ ψ hφ hψ⟩

/-- **Stacks Project, Tag 0DX5, corrected form of the existence clause.**  The existence clause
of the source is false: `Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf` of
`ImprovementExistenceCounterexample.lean` refutes it for `X = Spec k[u, v, w]`, `Z = V(u, v)`,
`F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~`, with every hypothesis of the source witnessed.

Let `X` be a Noetherian, universally catenary scheme whose local rings have `(S₁)` formal fibres,
`Z ⊆ X` closed and `F` coherent, and let `F'` be the depth-one quotient of `F` along `Z`
([Stacks, Tag 0DX3]).  Then a map `F ⟶ F''` of coherent modules satisfying conditions (1), (2)
and (3) of the source exists **if and only if** `depth(F'_x) ≥ 2` at every point `x ∈ Z` which
generalizes a point as in (2) without being one.  In the counterexample this fails at `(u, v)`.

The other assertions of the source hold as stated: uniqueness is
`AlgebraicGeometry.improvement_unique` and the Cohen–Macaulay pullback is
`AlgebraicGeometry.isImprovement_pullback`, so this is [Stacks, Tag 0DX5] with only its existence
assertion corrected.  The criterion is equivalent to the disjointness criterion of
`AlgebraicGeometry.existsUnique_improvement_of_disjoint_closure_lowDepthNotReached`, and is stated
pointwise.

For the forward direction an improvement satisfies the corrected conditions
(`AlgebraicGeometry.isCorrectedImprovement_of_isImprovement`), so it is isomorphic to the map of
`AlgebraicGeometry.exists_isCorrectedImprovement_and_depth_eq`, whose target has the depth of `F'`
at the points in question, and condition (3) bounds that depth below by two.  Conversely, under
the criterion that map satisfies condition (3) there as well. -/
@[stacks 0DX5 "corrected form of the existence clause, which is false as stated (refuted by \
Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf): at exactly the source's \
hypotheses, a map F -> F'' satisfying (1), (2) and (3) exists if and only if the depth-one \
quotient F' of Tag 0DX3 has depth at least two at every point of Z which generalizes a point as in \
(2) without being one; uniqueness and the Cohen-Macaulay pullback hold as stated"]
public theorem exists_isImprovement_iff_two_le_depth_depthOneQuotient (X : Scheme.{u})
    [IsNoetherian X]
    (Z : Set X) (hZ : IsClosed Z) (F : X.Modules) [F.IsCoherent]
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1) :
    (∃ (G : X.Modules) (φ : F ⟶ G), IsImprovement Z φ) ↔
      ∀ x : X, x ∈ Z → ¬ ReachedFromOutside Z F x → GeneralizesReached Z F x →
        letI : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u})
              (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) (depthOneQuotient X Z hZ.stableUnderSpecialization F).val x
        (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u})
            (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x) := by
  obtain ⟨G, φ, hφ, hdep⟩ := exists_isCorrectedImprovement_and_depth_eq X Z hZ F hX hFibres
  constructor
  · rintro ⟨H, ψ, hψ⟩ x hx hr hg
    obtain ⟨e, -, -⟩ := correctedImprovement_unique X Z hZ F G H φ ψ hφ
      (isCorrectedImprovement_of_isImprovement hψ)
    exact ((hdep x hx hg).symm.trans (Scheme.Modules.depth_stalk_congr e x)) ▸
      hψ.2.2.2 x hx hr
  · intro hcrit
    refine ⟨G, φ, hφ.1, hφ.2.1, hφ.2.2.1, fun x hx hr => ?_⟩
    by_cases hg : GeneralizesReached Z F x
    · exact hdep x hx hg ▸ hcrit x hx hr hg
    · exact hφ.2.2.2.2 x hx hg


/-- **Stacks Project, Tag 0DX5, the whole lemma in corrected form.**  Let `X` be a Noetherian,
universally catenary scheme whose local rings have `(S₁)` formal fibres, `Z ⊆ X` closed and `F` a
coherent `𝒪_X`-module, and let `F'` be the depth-one quotient of `F` along `Z`
([Stacks, Tag 0DX3]).  For maps `F ⟶ F''` satisfying conditions (1), (2) and (3) of the source
(`AlgebraicGeometry.IsImprovement`, which includes coherence of `F''`):

* **existence**, corrected: such a map exists if and only if `depth(F'_x) ≥ 2` at every point
  `x ∈ Z` which generalizes a point as in (2) without being one.  The source asserts existence
  unconditionally, which is false:
  `Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf` refutes it at the source's
  hypotheses, and the criterion fails there at `(u, v)`;
* **uniqueness**, as printed: any two such maps are isomorphic by a unique isomorphism under `F`;
* **the pullback**, as printed: for a Cohen–Macaulay morphism `f : Y ⟶ X` with `Y` Noetherian,
  `f^*F ⟶ f^*F''` satisfies (1), (2) and (3) with respect to `f^{-1}(Z) ⊆ Y`.

The three parts are `AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient`,
`AlgebraicGeometry.improvement_unique` and `AlgebraicGeometry.isImprovement_pullback`.  The
correction is the one recorded for 0DX5 in `errata.md`. -/
@[stacks 0DX5 "corrected form of the whole lemma, at exactly the source's hypotheses: the \
existence clause is false as stated (refuted by \
Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf) and is corrected to a \
criterion, a map F -> F'' satisfying (1), (2) and (3) exists if and only if the depth-one quotient \
F' of Tag 0DX3 has depth at least two at every point of Z which generalizes a \
point as in (2) without being one; uniqueness up to a unique isomorphism under F, and the \
assertion that the pullback along a Cohen-Macaulay morphism with Noetherian source satisfies \
(1), (2) and (3) with respect to the inverse image of Z, as printed"]
public theorem exists_isImprovement_iff_and_unique_and_isImprovement_pullback (X : Scheme.{u})
    [IsNoetherian X] (Z : Set X) (hZ : IsClosed Z) (F : X.Modules) [F.IsCoherent]
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1) :
    ((∃ (G : X.Modules) (φ : F ⟶ G), IsImprovement Z φ) ↔
      ∀ x : X, x ∈ Z → ¬ ReachedFromOutside Z F x → GeneralizesReached Z F x →
        letI : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u})
              (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) (depthOneQuotient X Z hZ.stableUnderSpecialization F).val x
        (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u})
            (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x)) ∧
    (∀ (G H : X.Modules) (φ : F ⟶ G) (ψ : F ⟶ H), IsImprovement Z φ → IsImprovement Z ψ →
      ∃! e : G ≅ H, φ ≫ e.hom = ψ) ∧
    (∀ (G : X.Modules) (φ : F ⟶ G), IsImprovement Z φ →
      ∀ (Y : Scheme.{u}) [IsNoetherian Y] (f : Y ⟶ X)
        (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)), f.IsCohenMacaulay hfib →
        IsImprovement (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).map φ)) :=
  ⟨exists_isImprovement_iff_two_le_depth_depthOneQuotient X Z hZ F hX hFibres,
    fun G H φ ψ hφ hψ => improvement_unique X Z hZ F G H φ ψ hφ hψ,
    fun _ φ hφ _ _ f hfib hcm => isImprovement_pullback φ hφ f hfib hcm⟩

end AlgebraicGeometry

end
