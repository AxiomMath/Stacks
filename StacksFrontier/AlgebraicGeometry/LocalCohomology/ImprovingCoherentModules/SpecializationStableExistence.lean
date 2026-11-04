module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ClosedSubsetExistence
public import StacksCore.Tactic.StacksAttribute

import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtension
import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence
import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement

/-!
# Existence of the depth-two extension along a specialization-stable subset

Let `X` be a Noetherian scheme which locally has a dualizing complex, let `T ⊆ X` be stable
under specialization and let `F` be a coherent `𝒪_X`-module with `depth(F_x) ≥ 1` at every
`x ∉ T` admitting an immediate specialization into `T`.  Those are the hypotheses of
[Stacks, Tag 0EI3], and
`StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ClosedSubsetExistence`
constructs the depth-two extension from them when `T` is **closed**, as the single pushforward
`j_{Tᶜ,*}(F'|_{Tᶜ})` of the depth-one quotient `F'`.

This module reduces the specialization-stable case to one extra datum: a **closed** `Z ⊆ T`
outside which the depth-one quotient already has depth at least two on `T`.  Given such a `Z`
the extension is the single pushforward `j_{Zᶜ,*}(F'|_{Zᶜ})` and no colimit is needed, exactly
as in the closed case; the source's filtered colimit over the opens whose complement lies in `T`
serves only to produce `Z`, since it stabilizes at `Zᶜ`.

## Main results

* `AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_compl_subset`:
  `j_{V,*}(F'|_V)` is coherent for **every** open `V` whose complement lies in `T`, not only for
  `V = Tᶜ`.
* `AlgebraicGeometry.exists_isDepthTwoExtension_of_isClosed_of_subset`:
  **[Stacks, Tag 0EI3], existence** along a specialization-stable `T`, at the source's two
  hypotheses together with such a `Z`.

## Why the generalized coherence is free

`AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient` is stated for the open
`V = Tᶜ`, and its proof uses that hypothesis in one place only: to know `depth(F'_x) ≥ 1` at a
point `x ∈ V` admitting an immediate specialization outside `V`.  For `x ∉ T` that is the
source's depth hypothesis on `F`, transported across the stalk isomorphism `F_x ≅ F'_x` of
`AlgebraicGeometry.depthOneQuotient_spec`.  For a `V` with only `Vᶜ ⊆ T` the remaining points
`x ∈ V ∩ T` need no new input at all: the depth-one quotient has `depth(F'_x) ≥ 1` at **every**
point of `T` by construction, which is the fourth clause of
`AlgebraicGeometry.IsDepthOneQuotient`.  So the generalization costs one case split and no
hypothesis.

## The three clauses, and where `Z` enters

With `V = Zᶜ` and `G = j_{V,*}(F'|_V)`:

* `G` is coherent by the generalized statement above, since `Vᶜ = Z ⊆ T`.
* `F → G` is a stalk isomorphism away from `T`, because `Tᶜ ⊆ V`: the first factor is
  `AlgebraicGeometry.depthOneQuotient_spec` and the second is
  `AlgebraicGeometry.isIso_stalkFunctor_map_unit_of_mem`.
* `depth(G_x) ≥ 2` for `x ∈ T` splits on `Z`.  At `x ∈ Z`, that is [Stacks, Tag 0EY0] part (3),
  available as `AlgebraicGeometry.two_le_depth_stalk_of_isIso_unit_outside`, applied to the open
  `V` which `x` misses and to `G`, which is the pushforward of its own restriction to `V` by
  `AlgebraicGeometry.isIso_unit_app_pushforward`.  At `x ∈ T ∖ Z` the unit is a stalk
  isomorphism, so the depth is that of `F'`, and the hypothesis on `Z` is exactly the bound
  there.

So `Z` is used only for the points of `T` off it, where the conclusion is about `F'` and not
about any extension; the hypothesis `hZ` below is therefore not a restatement of the conclusion
at those points but the assertion that `F'` already satisfies it there.

## What is still missing: the closed set `Z`

For a closed `T` the datum is free: `Z = T`.  For a merely specialization-stable `T` the
candidate is `Z = Supp(H¹_T(F'))`, and this is the only remaining gap in the existence half of
[Stacks, Tag 0EI3].  The source produces it implicitly, in the step "`F'' = j_*(F'|_V)` for any
sufficiently small `V`": on an affine `Spec(A)` with `F' ↔ M'` the colimit of the pushforwards
is computed by the short exact sequence `0 → M' → M'' → H¹_T(M') → 0`, and `H¹_T(M')` is a
**finite** `A`-module by Faltings' criterion [Stacks, Tag 0EFD] — which in this library is
`Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_le_one_of_depth_immediate`, stated
at exactly the two hypotheses carried below.  A finite `T`-torsion module has closed support
contained in `T`, and `depth(M'_q) ≤ 1` at a `q ∈ T` forces `q` into that support, so its
support is a closed subset of `T` containing the whole locus `hZ` speaks about.

Two things block assembling that into `Z` here.  The first is that `H¹_T` of a coherent module
exists in this library only over a ring, not over a scheme, so the affine-local supports have to
be glued: that part is cheap, since a closed subset of an affine open contained in `T` has its
closure in `X` inside `T` (its finitely many irreducible components have generic points in `T`,
and `T` is stable under specialization).  The second is the implication `depth(M_q) ≤ 1 ⟹
q ∈ Supp(H¹_T(M))` for `q ∈ T`, which needs the vanishing criterion `H^i_T(M) = 0` for
`i < s` iff `depth(M_p) ≥ s` on `T`, together with the compatibility of `H^i_T` with
localization at `q` — neither of which is available.

A second route to `Z`, which avoids local cohomology entirely, goes through
`AlgebraicGeometry.exists_isDepthTwoExtension_of_finite_depthOne_locus` and the finiteness
theorem [Stacks, Tag 0ECN], `AlgebraicGeometry.finite_setOf_depth_eq_and_lt_supportDim`: on a
Noetherian scheme with a dualizing complex, a coherent module satisfying Serre's condition
`(S₁)` has only finitely many points with `depth = 1` and `dim Supp > 1`.  The locus `hZ`
speaks about is contained in that exceptional set, by the following dichotomy.  A point `x ∈ T`
has `depth(F'_x) ≥ 1`, so `depth(F'_x) < 2` means `depth(F'_x) = 1`; and
`dim Supp(F'_x) > 1` then holds, for if some associated prime of `F'_x` had `dim = 1` — which,
`depth ≤ dim(R/𝔭)` holding at every associated prime, is the only alternative — it would be an
associated point `y` of `F'` with `y ⤳ x` *immediate*, hence `depth(F'_y) = 0`, hence `y ∉ T`,
and the depth hypothesis on immediate specializations would force `depth(F_y) ≥ 1`, which is
`depth(F'_y) ≥ 1` since the two stalks agree off `T`.  What
blocks this route is the hypothesis `(S₁)`, which the depth-one quotient need not satisfy: it
kills the associated points inside `T` and leaves any embedded associated point outside `T`
alone, and such a point violates `(S₁)` without violating either hypothesis of
[Stacks, Tag 0EI3] — on `X = Spec k[x, y]` with `T` one closed point `z₀` and
`F = 𝒪_X ⊕ 𝒪_X/𝔪_{z₁}` for a second closed point `z₁`, the depth hypothesis holds, `F' = F`,
and `z₁` is an embedded associated point.  Stacks 0ECN's proof is an induction whose hypothesis
is used globally, through a nonzerodivisor cutting out the non-Cohen--Macaulay locus, so it does
not localize to the points the dichotomy controls; what is needed is that induction run against
the dichotomy instead of against `(S₁)`, and the translation of the dichotomy itself from primes
of the stalk to points of `X`, neither of which is available.

It is worth recording why the obvious cheaper candidate for `Z` does not exist.  The locus
`{x | depth(F'_x) < 2}` itself is **not** closed, and no general closedness theorem about depth
loci can supply `Z`: that locus contains every generic point of `Supp(F')`, since a module over
a zero-dimensional local ring has depth zero, so its closure is all of `Supp(F')` and it is
closed only in the degenerate case where it *is* all of `Supp(F')`.  On `X = Spec(ℤ[t])` with
`F' = 𝒪_X` the locus is the set of points of height at most one, which is dense and not closed.
The closedness theorems about depth are about the non-`(S_k)` locus — where the comparison is
with `depth(F_x) ≥ min(k, dim(F_x))`, a condition the generic points satisfy — and about the
locus `{x | depth(F'_x) + δ(x) ≤ s}` for a dimension function `δ`, which is the union of the
supports of finitely many `Ext` sheaves against a dualizing complex.  Neither is the locus `hZ`
concerns.  What makes `Supp(H¹_T(F'))` work is not closedness of a depth locus but the
finiteness of `H¹_T(F')`, i.e. Faltings' criterion, which is where the two hypotheses of
[Stacks, Tag 0EI3] are consumed.

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Coherence of the pushforward from the complement of any closed subset of `T` -/

/-- The map to the depth-one quotient is a stalk isomorphism over the local ring away from `T`. -/
private theorem isIso_stalkMap_toDepthOneQuotient (X : Scheme.{u}) [IsNoetherian X] (T : Set X)
    (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent] (x : X) (hx : x ∉ T) :
    IsIso (SheafOfModules.stalkMap X.ringCatSheaf x (toDepthOneQuotient X T hT F)) :=
  isIso_stalkMap_of_isIso_stalkFunctor _ _ ((depthOneQuotient_spec X T hT F).2.2.1 x hx)

/-- **The pushforward of the depth-one quotient from an open whose complement lies in `T` is
coherent.** Let `X` be a Noetherian scheme which locally has a dualizing complex, let `T ⊆ X` be
stable under specialization, let `V` be an open of `X` whose complement lies in `T`, and let `F`
be a coherent module whose depth at a point outside `T` is at least one as soon as some point of
`T` is an immediate specialization of it.  Then `j_{V,*}(F'|_V)` is coherent, `F'` being the
depth-one quotient of `F` along `T`.

This is `AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient` with `V = Tᶜ`
relaxed to `Vᶜ ⊆ T`, and it needs no further hypothesis.  Coherence comes from the globalized
Faltings criterion `AlgebraicGeometry.isCoherent_pushforward_of_locallyHasDualizingComplex`,
whose depth bound is checked at a point `x ∈ V` with an omitted immediate specialization `z`.
That `z` lies in `T`, and `x` splits into two cases: for `x ∉ T` the bound is the hypothesis on
`F`, moved to `F'` along the stalk isomorphism of `AlgebraicGeometry.depthOneQuotient_spec`, and
for `x ∈ T` it is the depth-one bound the quotient satisfies at every point of `T`. -/
public theorem isCoherent_pushforward_restrict_depthOneQuotient_of_compl_subset
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (V : X.Opens) (hVT : (V : Set X)ᶜ ⊆ T) (F : X.Modules) [F.IsCoherent]
    (hdual : LocallyHasDualizingComplex X)
    (hdepth : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    ((Scheme.Modules.pushforward V.ι).obj
      ((depthOneQuotient X T hT F).restrict V.ι)).IsCoherent := by
  have hq : (depthOneQuotient X T hT F).IsCoherent := (depthOneQuotient_spec X T hT F).1
  have := hq
  have hres : ((depthOneQuotient X T hT F).restrict V.ι).IsCoherent :=
    Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion V.ι _
  have := hres
  refine isCoherent_pushforward_of_locallyHasDualizingComplex V.ι hdual _ ?_
  intro x z hz himm
  have hzT : z ∈ T := by
    refine hVT ?_
    rw [← Scheme.Opens.opensRange_ι V]
    exact hz
  rw [Scheme.Modules.depth_stalk_restrict V.ι (depthOneQuotient X T hT F) x]
  by_cases hxT : V.ι.base x ∈ T
  · exact (depthOneQuotient_spec X T hT F).2.2.2 (V.ι.base x) hxT
  · have heq := depth_stalk_eq_of_isIso_stalkMap (toDepthOneQuotient X T hT F) (V.ι.base x)
      (isIso_stalkMap_toDepthOneQuotient X T hT F _ hxT)
    exact le_trans (hdepth (V.ι.base x) z hxT hzT himm) (le_of_eq heq)

/-! ### Tag 0EI3, existence along a specialization-stable subset -/

/-- **Stacks Project, Tag 0EI3, existence along a specialization-stable subset.** Let `X` be a
Noetherian scheme which locally has a dualizing complex, let `T ⊆ X` be stable under
specialization and let `F` be a coherent `𝒪_X`-module such that `depth(F_x) ≥ 1` whenever some
point of `T` is an immediate specialization of `x ∉ T`.  Let `Z ⊆ T` be closed and such that the
depth-one quotient `F'` of `F` along `T` already has `depth(F'_x) ≥ 2` at the points of `T`
outside `Z`.  Then `F` admits a depth-two extension along `T`.

No hypothesis about extensions or colimits is left, and the depth-two extension is the single
pushforward `j_{Zᶜ,*}(F'|_{Zᶜ})`: for a closed `T` one may take `Z = T`, recovering
`AlgebraicGeometry.exists_isDepthTwoExtension_of_locallyHasDualizingComplex`.  See the module
documentation for the three clauses and for the status of `Z` itself. -/
@[stacks 0EI3 "existence along a specialization-stable subset, with no hypothesis about \
extensions or colimits, and at the source's hypotheses — the dualizing hypothesis and the depth \
hypothesis on immediate specializations — together with a closed subset of T outside which the \
depth-one quotient already has depth two on T"]
public theorem exists_isDepthTwoExtension_of_isClosed_of_subset
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent]
    (hdual : LocallyHasDualizingComplex X)
    (hdepth : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x))
    (Z : Set X) (hZclosed : IsClosed Z) (hZT : Z ⊆ T)
    (hZ : ∀ x : X, x ∈ T → x ∉ Z →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X T hT F).val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) (depthOneQuotient X T hT F).val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (depthOneQuotient X T hT F).val.presheaf x)) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ := by
  set V : X.Opens := ⟨Zᶜ, hZclosed.isOpen_compl⟩ with hVdef
  set F' := depthOneQuotient X T hT F with hF'def
  have hF'coh : F'.IsCoherent := (depthOneQuotient_spec X T hT F).1
  have := hF'coh
  have hVT : (V : Set X)ᶜ ⊆ T := by
    intro y hy
    exact hZT (not_not.mp hy)
  -- coherence of the single pushforward from the complement of `Z`
  have hres := isCoherent_pushforward_restrict_depthOneQuotient_of_compl_subset X T hT V hVT
    F hdual hdepth
  have := hres
  have e : (Scheme.Modules.pushforward V.ι).obj (F'.restrict V.ι) ≅
      (Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.pullback V.ι).obj F') :=
    (Scheme.Modules.pushforward V.ι).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app F')
  have hcoh : ((Scheme.Modules.pushforward V.ι).obj
      ((Scheme.Modules.pullback V.ι).obj F')).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e.symm
  set G := (Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.pullback V.ι).obj F') with hGdef
  set ψ := (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app F' with hψdef
  have hψ : ∀ x ∈ (V : Set X), IsIso (SheafOfModules.stalkMap X.ringCatSheaf x ψ) := fun x hx =>
    isIso_stalkMap_of_isIso_stalkFunctor _ x (isIso_stalkFunctor_map_unit_of_mem X V F' x hx)
  refine ⟨G, toDepthOneQuotient X T hT F ≫ ψ, hcoh, ?_, ?_⟩
  · -- a stalk isomorphism away from `T`, since the complement of `T` is inside `V`
    intro x hx
    have := isIso_stalkAb_of_isIso_stalkMap _ x (isIso_stalkMap_toDepthOneQuotient X T hT F x hx)
    have := isIso_stalkAb_of_isIso_stalkMap _ x (hψ x fun h => hx (hZT h))
    refine isIso_stalkMap_of_isIso_stalkAb _ x ?_
    erw [Functor.map_comp]
    infer_instance
  · -- depth at least two on `T`, split on `Z`
    intro x hx
    by_cases hxZ : x ∈ Z
    · exact two_le_depth_stalk_of_isIso_unit_outside X V G hcoh
        (isIso_unit_app_pushforward V ((Scheme.Modules.pullback V.ι).obj F')) x
        (fun h => h hxZ)
    · exact le_trans (hZ x hx hxZ) (depth_stalk_eq_of_isIso_stalkMap ψ x (hψ x hxZ)).le

/-- **Stacks Project, Tag 0EI3, existence along a specialization-stable subset, from finiteness
of the depth-one locus.** Same as `exists_isDepthTwoExtension_of_isClosed_of_subset`, with the
closed subset replaced by the hypothesis that the set of points of `T` where the depth-one
quotient `F'` still has depth below two is **finite**.

A finite set of points has closed closure — the union of the finitely many closures of its
points — and that closure stays inside `T` because `T` is stable under specialization.  So the
finite set's closure is a legitimate `Z`, and the remaining gap in the existence half of
[Stacks, Tag 0EI3] is exactly this finiteness.  It is the shape the finiteness theorems about
depth take: [Stacks, Tag 0ECN] (`AlgebraicGeometry.finite_setOf_depth_eq_and_lt_supportDim`)
says that on a Noetherian scheme with a dualizing complex a coherent module satisfying Serre's
condition `(S₁)` has only finitely many points with `depth(F'_x) = 1` and
`dim Supp(F'_x) > 1`. -/
@[stacks 0EI3 "existence along a specialization-stable subset, with no hypothesis about \
extensions or colimits, and at the source's hypotheses — the dualizing hypothesis and the depth \
hypothesis on immediate specializations — together with finiteness of the set of points of T \
where the depth-one quotient still has depth below two"]
public theorem exists_isDepthTwoExtension_of_finite_depthOne_locus
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent]
    (hdual : LocallyHasDualizingComplex X)
    (hdepth : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x))
    (hfin : {x : X | x ∈ T ∧
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X T hT F).val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) (depthOneQuotient X T hT F).val x
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (depthOneQuotient X T hT F).val.presheaf x) < (2 : ℕ∞)}.Finite) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ := by
  classical
  set B : Set X := {x : X | x ∈ T ∧
    let : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X T hT F).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (depthOneQuotient X T hT F).val x
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (depthOneQuotient X T hT F).val.presheaf x) < (2 : ℕ∞)} with hBdef
  refine exists_isDepthTwoExtension_of_isClosed_of_subset X T hT F hdual hdepth
    (⋃ b ∈ B, closure {b}) (hfin.isClosed_biUnion fun _ _ => isClosed_closure) ?_ ?_
  · -- the closure of a point of `B ⊆ T` stays in `T`
    intro y hy
    obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
    exact hT (specializes_iff_mem_closure.mpr hyb) hb.1
  · -- off that closure the depth-one quotient already has depth at least two
    intro x hx hxZ
    have hxB : x ∉ B := fun h =>
      hxZ (Set.mem_iUnion₂.mpr ⟨x, h, subset_closure rfl⟩)
    have hnot : ¬ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (depthOneQuotient X T hT F).val.presheaf x) < (2 : ℕ∞) := fun h => hxB ⟨hx, h⟩
    exact not_lt.mp hnot

end AlgebraicGeometry

end
