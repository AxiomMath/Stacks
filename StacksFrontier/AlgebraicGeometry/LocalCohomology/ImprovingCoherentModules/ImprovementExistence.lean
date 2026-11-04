module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImprovementUniqueness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.PushforwardImprovement
public import StacksCore.Tactic.StacksAttribute

/-!
# Existence of the improvement of a coherent module along a closed subset

Let `X` be a Noetherian scheme, let `Z ⊆ X` be stable under specialization and let `F` be a
coherent `𝒪_X`-module. In the source's construction of the improvement `F → F''` of
[Stacks, Tag 0DX5], `F` is replaced by its depth-one quotient `F'` along `Z`
([Stacks, Tag 0DX3]), and `F'` is then extended across a closed subset `Z' ⊆ Z` by pushing
forward from the open `U = X ∖ Z'`, so that `F'' = j_*(F'|_U)`; coherence of `F''` is Kollár's
criterion [Stacks, Tag 0AWB].

That composite is an improvement along the nested pair `Z' ⊆ Z`. This module upgrades it to an
improvement in the sense of [Stacks, Tag 0DX5] — depth *exactly* one at the points of `Z` reached
from outside `Z`, and at least two at the remaining points of `Z` — for an open `U` which contains
every reached point of `Z` and at whose remaining points of `Z` the depth-one quotient already has
depth at least two.

## Main results

* `AlgebraicGeometry.isImprovement_toDepthOneQuotient_comp_unit`: the composite is an improvement
  of `F` along `Z`.
* `AlgebraicGeometry.isImprovement_pushforward_restrict_depthOneQuotient`: the same, with the
  coherence of the extension discharged by [Stacks, Tag 0AWB], so that the hypotheses on `X` are
  the source's — Noetherian, universally catenary, and `(S₁)` formal fibres of the local rings.
* `AlgebraicGeometry.existsUnique_improvement_of_open`: existence *and* uniqueness together, which
  is the shape in which [Stacks, Tag 0DX5] states its conclusion.

## Implementation notes

The upgrade is `AlgebraicGeometry.isImprovement_of_isNestedImprovement`: an improvement along the
nested pair `AlgebraicGeometry.NotReachedFromOutside Z F ⊆ Z` is an improvement along `Z`, because
the depth at a reached point is at most one automatically. So the two conditions asked of `U` are
exactly what identifies the complement of `U` with `NotReachedFromOutside Z F` as far as the three
clauses can see: every reached point of `Z` lies in `U`, where the first clause of the nested
condition supplies surjectivity and the depth lower bound; and at a point of `Z` inside `U` which
is not reached, the depth at least two is inherited from the depth-one quotient across the
canonical map, which is an isomorphism on the stalks at the points of `U`
(`AlgebraicGeometry.isIso_stalkMap_unit_pullbackPushforward_of_mem`). Outside `U` the depth bound
is [Stacks, Tag 0EY0] part (3).

## Why the existence assertion is not stated unconditionally

The source asserts existence with no hypothesis beyond those on `X`, and that is **false as
literally stated**.  Take `X = Spec k[u, v, w, t]`, `Z = V(u, v)` and
`F = (u, v)~ ⊕ (k[u, v, w, t]/(u, w))~`.  Then `Ass(F) = {(0), (u, w)}` misses `Z`, so the
depth-one quotient is `F' = F`.  The point `(u, v, w)` satisfies condition (2), through the
immediate specialization from `(u, w) ∉ Z`, and condition (2) forces `F_{(u,v,w)} ≅ F''_{(u,v,w)}`
— surjective by the condition, injective because `Ass(F') ∩ Z = ∅`.  Since `(u, v) ⤳ (u, v, w)`,
localizing gives `F''_{(u,v)} = F'_{(u,v)}`, whose depth is `1`: it is the maximal ideal of a
two-dimensional regular local ring.  But `(u, v)` is *not* reached from outside `Z` — its only
associated generalization is `(0)`, which specializes to it through `(u)` — so condition (3)
demands depth at least `2` there.  No such `F''` exists.

Three variables already suffice: the same configuration with `X = Spec k[u, v, w]`, `Z = V(u, v)`
and `F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~` works verbatim. Its ring-theoretic heart is
`Stacks.ImprovementCounterexample.not_exists_two_le_depth_quotient_maximalIdeal`: no
quotient of the maximal ideal of a two-dimensional regular local ring has depth at least two, which
is exactly the incompatibility of clauses (2) and (3) at the point `(u, v)`.

The forced isomorphism above uses only clauses (1), (2) and (3) and nothing about the *shape* of
`F''`, so no alternative construction evades it.  The source's own proof fails at the same point,
and the precise bug is this: the closed subset `Z'` across which the source extends is cut out by
removing the neighbourhoods `V_{i,j}` chosen around the generic points with `d_{i,j} = 1`, and
[Stacks, Tag 0DWY] controls depth only on `Z_{i,j} ∩ V_{i,j}`.  Here the only such generic point is
`(u, v, w)`, so one neighbourhood `V ∋ (u, v, w)` is chosen; `(u, v)` does not lie in that
component `Z_{2,1} = V(u, v, w)`, so no shrinking of `V` ever sees it — and no shrinking could,
since every open containing `(u, v, w)` contains its generalization `(u, v)`.

A sufficient extra hypothesis is `IsClosed (AlgebraicGeometry.NotReachedFromOutside Z F)`, under
which `AlgebraicGeometry.existsUnique_improvement_of_isClosed_notReachedFromOutside` closes the
statement at the source's hypotheses on `X` alone.  It is **only sufficient**, and it is a blunt
instrument — see the sharp criterion below.  This is a defect of the source: [Stacks, Tag 0EI4]
is the later form of the same result, in which the depth-two subset is free data rather than
forced to be the non-reached locus, and it needs no such extra hypothesis.

The subset is asked only to be stable under specialization, which a closed subset is by
`IsClosed.stableUnderSpecialization`; the source states the lemma for a closed subscheme, and only
its underlying closed subset is used.

The two conditions on `U` are what the source produces from [Stacks, Tag 0DWY] applied at the
finitely many generic points of the irreducible components of `Z ∩ Y_i`, `Y_i` the closure of an
associated point of `F'`: the condition on the reached points is the source's observation that
those are exactly the generic points with `d_{i,j} = 1`, and the depth condition at the remaining
points of `Z ∩ U` is the output of [Stacks, Tag 0DWY] on the neighbourhoods `V_{i,j}`.

### Why the choice of `U` is a hypothesis

An open `U` with these two properties need not exist, so the existence assertion of
[Stacks, Tag 0DX5] is carried here with the choice of `U` as a hypothesis rather than
unconditionally, and
`AlgebraicGeometry.existsUnique_improvement_of_isClosed_notReachedFromOutside` makes the choice
under the hypothesis that `AlgebraicGeometry.NotReachedFromOutside Z F` be closed.

That hypothesis is **sufficient but not necessary**: it already fails for `X = Spec k[x, y]`,
`Z = V(x)`, `F = 𝒪_X`, where the only reached point is the generic point `(x)` of `Z`, so the
non-reached locus is `Z ∖ {(x)}`, whose closure is `Z` — not closed.  Yet [Stacks, Tag 0DX5]
holds there with `F'' = F` and `U = X`.  So the closed-locus form does not apply to a line in the
affine plane with its structure sheaf, and in general it fails whenever the generic point of a
positive-dimensional component of `Z` is reached, which is exactly the source's `d_{i,j} = 1` and
so the typical case.

What *is* necessary and sufficient is that the closure of the locus where `F'` still has depth at
most one, away from the reached points, stay clear of the reached points: this is
`AlgebraicGeometry.existsUnique_improvement_of_disjoint_closure_lowDepthNotReached`, with
converse `AlgebraicGeometry.disjoint_closure_lowDepthNotReached_of_open`.  Pointwise, it says that
`F'` has depth at least two at every point of `Z` generalizing a reached point without being one,
and in that form, at exactly the source's hypotheses, it is the corrected form of the existence
clause, `AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient`.

Such a configuration occurs: it is the `X = Spec k[u, v, w, t]`, `Z = V(u, v)` example given above,
where `(u, v)` has depth one, is not reached, and specializes to the reached point `(u, v, w)`.
So the choice of `U` cannot be dropped, and [Stacks, Tag 0EI4] — in which the subset carrying the
depth-two condition is free data rather than read off `Z` and `F` — is the form that holds
unconditionally.

## References

* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0DWY](https://stacks.math.columbia.edu/tag/0DWY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0DX5, existence.** The depth-one quotient of `F` along `Z` followed by
the canonical map of that quotient to the extension of its restriction to `U` is an improvement of
`F` along `Z`, provided `U` contains every point of `Z` reached from outside `Z` and the quotient
already has depth at least two at the remaining points of `Z ∩ U`.

This is the source's construction: `F → F'` is [Stacks, Tag 0DX3] and `F' → F'' = j_*(F'|_U)` is
the canonical map of the extension across the closed complement of `U`, whose coherence is
Kollár's criterion [Stacks, Tag 0AWB].

This grants the choice of `U`, and the existence of a suitable `U` is exactly the content the
existence clause of [Stacks, Tag 0DX5] asserts -- it is equivalent to the disjointness criterion,
by `AlgebraicGeometry.disjoint_closure_lowDepthNotReached_of_open`.  That clause is false as stated
(`Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf`); its corrected form, at the
source's hypotheses with no choice granted, is
`AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient` and
`AlgebraicGeometry.existsUnique_isCorrectedImprovement`. -/
public theorem isImprovement_toDepthOneQuotient_comp_unit
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : StableUnderSpecialization Z)
    (F : X.Modules) [F.IsCoherent] (U : X.Opens) (hUZ : ((U : Set X))ᶜ ⊆ Z)
    (hreached : ∀ x : X, x ∈ Z → ReachedFromOutside Z F x → x ∈ (U : Set X))
    (hdepth : ∀ x : X, x ∈ (U : Set X) → x ∈ Z → ¬ ReachedFromOutside Z F x →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) (depthOneQuotient X Z hZ F).val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x))
    [((Scheme.Modules.pushforward U.ι).obj
        ((Scheme.Modules.pullback U.ι).obj (depthOneQuotient X Z hZ F))).IsCoherent] :
    IsImprovement Z
      (toDepthOneQuotient X Z hZ F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
          (depthOneQuotient X Z hZ F)) := by
  have hn := isNestedImprovement_toDepthOneQuotient_comp_unit X Z hZ F U hUZ
  refine isImprovement_of_isNestedImprovement ⟨hn.1, hn.2.1, ?_, ?_⟩
  · -- at a reached point of `Z`, which lies in `U`
    intro x hx hx'
    have hr := reachedFromOutside_of_notMem_notReachedFromOutside hx hx'
    exact hn.2.2.1 x hx (not_not.mpr (hreached x hx hr))
  · -- at a point of `Z` which is not reached
    intro x hx
    by_cases hxU : x ∈ (U : Set X)
    · have heq := depth_stalk_pushforward_restrict_eq_of_mem (depthOneQuotient X Z hZ F) U x hxU
      dsimp only [Functor.comp_obj] at heq ⊢
      rw [← heq]
      exact hdepth x hxU hx.1 hx.2
    · exact hn.2.2.2 x hxU

/-- **Stacks Project, Tag 0DX5, existence, at the source's hypotheses on `X`.** On a Noetherian,
universally catenary scheme whose local rings have `(S₁)` formal fibres, and under the dimension
condition of [Stacks, Tag 0AWB], the depth-one quotient of `F` along `Z` followed by the canonical
map to the extension of its restriction to `U` is an improvement of `F` along `Z`.

This is `AlgebraicGeometry.isImprovement_toDepthOneQuotient_comp_unit` with its coherence
hypothesis discharged by
`AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_universallyCatenary`, which
is Kollár's criterion.

This grants the choice of `U`, and the existence of a suitable `U` is exactly the content the
existence clause of [Stacks, Tag 0DX5] asserts -- it is equivalent to the disjointness criterion,
by `AlgebraicGeometry.disjoint_closure_lowDepthNotReached_of_open`.  That clause is false as stated
(`Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf`); its corrected form, at the
source's hypotheses with no choice granted, is
`AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient` and
`AlgebraicGeometry.existsUnique_isCorrectedImprovement`. -/
public theorem isImprovement_pushforward_restrict_depthOneQuotient
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : StableUnderSpecialization Z)
    (F : X.Modules) [F.IsCoherent] (U : X.Opens) (hUZ : ((U : Set X))ᶜ ⊆ Z)
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, z ∉ U.ι.opensRange →
      ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1)
    (hdim : ∀ x : U.toScheme,
      x ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback U.ι).obj (depthOneQuotient X Z hZ F)) →
        ∀ y : (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subscheme,
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subschemeι y ∉ U.ι.opensRange →
          2 ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subscheme.presheaf.stalk y))
    (hreached : ∀ x : X, x ∈ Z → ReachedFromOutside Z F x → x ∈ (U : Set X))
    (hdepth : ∀ x : X, x ∈ (U : Set X) → x ∈ Z → ¬ ReachedFromOutside Z F x →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) (depthOneQuotient X Z hZ F).val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x)) :
    IsImprovement Z
      (toDepthOneQuotient X Z hZ F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
          (depthOneQuotient X Z hZ F)) :=
  letI := isCoherent_pushforward_restrict_depthOneQuotient_of_universallyCatenary
    X Z hZ F U hX hFibres hdim
  isImprovement_toDepthOneQuotient_comp_unit X Z hZ F U hUZ hreached hdepth

/-- **Stacks Project, Tag 0DX5.** There exists a map `F → F''` of coherent modules satisfying
conditions (1), (2) and (3) along the closed subset `Z`, and it is unique up to a unique
isomorphism under `F`.

Existence is `AlgebraicGeometry.isImprovement_pushforward_restrict_depthOneQuotient` and
uniqueness is `AlgebraicGeometry.improvement_unique`; this is the conclusion of the source in the
shape the source states it.

This grants the choice of `U`, and the existence of a suitable `U` is exactly the content the
existence clause of [Stacks, Tag 0DX5] asserts -- it is equivalent to the disjointness criterion,
by `AlgebraicGeometry.disjoint_closure_lowDepthNotReached_of_open`.  That clause is false as stated
(`Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf`); its corrected form, at the
source's hypotheses with no choice granted, is
`AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient` and
`AlgebraicGeometry.existsUnique_isCorrectedImprovement`. -/
public theorem existsUnique_improvement_of_open
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : IsClosed Z)
    (F : X.Modules) [F.IsCoherent] (U : X.Opens) (hUZ : ((U : Set X))ᶜ ⊆ Z)
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, z ∉ U.ι.opensRange →
      ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1)
    (hdim : ∀ x : U.toScheme,
      x ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback U.ι).obj
            (depthOneQuotient X Z hZ.stableUnderSpecialization F)) →
        ∀ y : (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subscheme,
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subschemeι y ∉ U.ι.opensRange →
          2 ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subscheme.presheaf.stalk y))
    (hreached : ∀ x : X, x ∈ Z → ReachedFromOutside Z F x → x ∈ (U : Set X))
    (hdepth : ∀ x : X, x ∈ (U : Set X) → x ∈ Z → ¬ ReachedFromOutside Z F x →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u})
            (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) (depthOneQuotient X Z hZ.stableUnderSpecialization F).val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x)) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsImprovement Z φ ∧
      ∀ (H : X.Modules) (ψ : F ⟶ H), IsImprovement Z ψ → ∃! e : G ≅ H, φ ≫ e.hom = ψ :=
  have h := isImprovement_pushforward_restrict_depthOneQuotient X Z
    hZ.stableUnderSpecialization F U hUZ hX hFibres hdim hreached hdepth
  ⟨_, _, h, fun H ψ hψ => improvement_unique X Z hZ F _ H _ ψ h hψ⟩

end AlgebraicGeometry

end
