module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.Extension
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletionDiscreteValuation

/-!
# Factoring a morphism from a curve through a projective curve, given an ample sheaf

[Stacks, Tag 0BY0] says that a morphism `X ⟶ Y` of varieties over a field `k`, with `Y` proper
and `X` a curve, factors as `X ⟶ X̄ ⟶ Y` with `X ⟶ X̄` an open immersion and `X̄` a projective
curve.

The source's proof is two steps. First [Stacks, Tag 0BXW] produces an open immersion
`j : X ⟶ X̄` with `X̄` H-projective over `k`, with `j(X)` dense and scheme-theoretically dense,
and with `X̄ \ j(X)` a finite set of closed points at which the local rings of `X̄` are discrete
valuation rings. Then [Stacks, Tag 0BXY] — the case of a curve of [Stacks, Tag 0BX7] — extends
`X ⟶ Y` across each of those points, because a discrete valuation ring is a valuation ring and
`Y` is proper over `k`; as there are only finitely many of them, finitely many applications
reach all of `X̄`.

## Main results

* `AlgebraicGeometry.exists_open_extension_of_finset_valuationRing_stalk`: a morphism to a
  proper scheme, defined on a dense open subscheme of a Noetherian scheme whose local rings
  outside that open are valuation rings, extends to an open subscheme containing any prescribed
  finite set of points. This is the finite iteration of [Stacks, Tag 0BX7].
* `AlgebraicGeometry.exists_extension_of_finite_compl_valuationRing_stalk`: the same when the
  complement of the dense open is finite, where the iteration therefore reaches the whole
  scheme.
* `AlgebraicGeometry.exists_isOpenImmersion_isCurve_isProjectiveMorphism_factorization`:
  the factorization of [Stacks, Tag 0BY0] with the superfluous hypothesis `h09NZ`; see below.
  [Stacks, Tag 0BY0] itself, with nothing assumed, is
  `AlgebraicGeometry.exists_isOpenImmersion_isCurve_isProjectiveMorphism_factorization_of_isCurve`
  in `StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCurveFactorizationUnconditional`.

## What is proved, and the superfluous hypothesis

Both clauses of the conclusion are proved of the scheme that is constructed: `X ⟶ X̄` is an open
immersion, and `X̄` is a projective curve, meaning `AlgebraicGeometry.IsCurve` for its structure
morphism together with `AlgebraicGeometry.IsProjectiveMorphism` of that morphism. The
factorization `j ≫ G = g` is part of the conclusion, as are `j ≫ q = pX` and `G ≫ pY = q`, so
both halves of the factorization are morphisms of `k`-schemes.

The hypothesis `h09NZ` is the statement of [Stacks, Tag 09NZ], the existence of an ample
invertible sheaf on a Noetherian separated scheme of dimension at most one. It is passed to
`Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation`, where it is
superfluous as well. The library proves it, as
`Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one`
and in the form of the proposition as
`Stacks.HQuasiProjectiveDimensionOne.ampleOfNoetherianSeparatedDimLEOne`; and for a curve, which
is reduced, the completion is
`Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`,
which needs no ample sheaf as input. Nothing in the present argument uses anything else.

## Implementation notes

**The curve structure on the completion is established here**, since [Stacks, Tag 0BXW] only
asserts H-projectivity of `X̄` and the density and boundary properties of `j`. The four
components of `AlgebraicGeometry.IsVariety` for the structure morphism `q` of `X̄` come out as
follows.

* `AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` of `q` follow from `AlgebraicGeometry.IsProper` of `q`, which
  `AlgebraicGeometry.isProper_of_isProjectiveMorphism` supplies from H-projectivity.
* `AlgebraicGeometry.IsReduced` of `X̄` is
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant.isReduced`
  applied to the inclusion of the dense open `j(X)`: that inclusion is scheme-theoretically
  dominant by [Stacks, Tag 01RD] because `j(X)` is scheme-theoretically dense, it is
  quasi-compact because `X̄` is locally Noetherian, and `j(X)` is reduced because it is
  isomorphic to `X`, which is a variety.
* `IrreducibleSpace` of `X̄` holds because the range of `j` is irreducible, being the continuous
  image of the irreducible space `X`, and dense.

**The dimension of the completion is exactly one.** The inequality `dim X̄ ≤ dim X` is
`Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion`, the
comparison along a dense open immersion of schemes locally of finite type over `k` which
[Stacks, Tag 0BXV] is proved with. The reverse inequality `dim X ≤ dim X̄` is
`Topology.IsInducing.topologicalKrullDim_le` for the open embedding `j`.

**The extension is iterated over a `Finset`, not over the complement as a set.** Each single
step is `AlgebraicGeometry.exists_open_extension_of_valuationRing_stalk`, the library's
[Stacks, Tag 0BX7], which enlarges the open subscheme by one point whose local ring is a
valuation ring; the hypothesis that the point lies in the closure of the current open subscheme
is supplied by density, which is preserved because the open subscheme only grows. The finiteness
hypothesis of [Stacks, Tag 0BX7] is discharged in the `AlgebraicGeometry.IsNoetherian` form, the
second disjunct, since `X̄` is Noetherian.

**Valuation rings, not discrete valuation rings, are what the extension needs.** The two helper
lemmas therefore ask only for `ValuationRing` on the stalks outside the dense open, and the
discrete valuation rings of [Stacks, Tag 0BXW] are converted at the point of use. Following
[Stacks, Tag 0BXW], the hypothesis is spelled `∃ _ : IsDomain _, ValuationRing _`, because
`ValuationRing` cannot be stated without an `IsDomain` instance.

## References

* [Stacks Project, Tag 0BY0](https://stacks.math.columbia.edu/tag/0BY0)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 0BXY](https://stacks.math.columbia.edu/tag/0BXY)
* [Stacks Project, Tag 0BX7](https://stacks.math.columbia.edu/tag/0BX7)
* [Stacks Project, Tag 0BXV](https://stacks.math.columbia.edu/tag/0BXV)
* [Stacks Project, Tag 01RD](https://stacks.math.columbia.edu/tag/01RD)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Iterating the extension of Tag 0BX7 -/

/-- **A morphism to a proper scheme extends across any finite set of points with valuation
local rings.** Let `U` be a dense open subscheme of a Noetherian scheme `Z` over `S`, let `Y` be
proper over `S`, and suppose the local ring of `Z` at every point outside `U` is a valuation
ring. Then a morphism `U ⟶ Y` over `S` extends to an open subscheme of `Z` containing `U` and
any prescribed finite set of points.

This is `AlgebraicGeometry.exists_open_extension_of_valuationRing_stalk`, the library's
[Stacks, Tag 0BX7], applied once for each point of the finite set; density of the open subscheme
persists along the way because it only grows. -/
theorem exists_open_extension_of_finset_valuationRing_stalk
    {S Z Y : Scheme.{u}} (pZ : Z ⟶ S) (pY : Y ⟶ S)
    [AlgebraicGeometry.IsNoetherian Z] [IsProper pY]
    (U : Z.Opens) (hU : Dense (U : Set Z))
    (hstalk : ∀ z : Z, z ∉ (U : Set Z) →
      ∃ _ : IsDomain (Z.presheaf.stalk z), ValuationRing (Z.presheaf.stalk z))
    (f : (U : Scheme.{u}) ⟶ Y) (hf : f ≫ pY = U.ι ≫ pZ) (s : Finset Z) :
    ∃ (V : Z.Opens) (hUV : U ≤ V) (g : (V : Scheme.{u}) ⟶ Y),
      g ≫ pY = V.ι ≫ pZ ∧ Z.homOfLE hUV ≫ g = f ∧ ∀ z ∈ s, z ∈ (V : Set Z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨U, le_rfl, f, hf, by simp, by simp⟩
  | @insert x s _ ih =>
    obtain ⟨V, hUV, g, hg, hgf, hsV⟩ := ih
    by_cases hxV : x ∈ (V : Set Z)
    · refine ⟨V, hUV, g, hg, hgf, fun y hy => ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxV
      · exact hsV y hy
    · obtain ⟨hdom, hval⟩ := hstalk x fun hx => hxV (hUV hx)
      have : IsDomain (Z.presheaf.stalk x) := hdom
      have : ValuationRing (Z.presheaf.stalk x) := hval
      have hVdense : Dense (V : Set Z) := hU.mono fun z hz => hUV hz
      obtain ⟨W, hVW, hxW, gW, hgW, hgext⟩ :=
        exists_open_extension_of_valuationRing_stalk pZ pY x V g hg (hVdense x)
          (Or.inr inferInstance)
      refine ⟨W, hUV.trans hVW, gW, hgW, ?_, fun y hy => ?_⟩
      · rw [← Z.homOfLE_homOfLE hUV hVW, Category.assoc, hgext, hgf]
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxW
        · exact hVW (hsV y hy)

/-- **A morphism to a proper scheme defined on a dense open with finite complement and
valuation local rings along that complement extends to the whole scheme.** The iteration of
`AlgebraicGeometry.exists_open_extension_of_finset_valuationRing_stalk` over the complement
leaves nothing out, so the open subscheme it produces is everything. -/
theorem exists_extension_of_finite_compl_valuationRing_stalk
    {S Z Y : Scheme.{u}} (pZ : Z ⟶ S) (pY : Y ⟶ S)
    [AlgebraicGeometry.IsNoetherian Z] [IsProper pY]
    (U : Z.Opens) (hU : Dense (U : Set Z)) (hfin : ((U : Set Z)ᶜ).Finite)
    (hstalk : ∀ z : Z, z ∉ (U : Set Z) →
      ∃ _ : IsDomain (Z.presheaf.stalk z), ValuationRing (Z.presheaf.stalk z))
    (f : (U : Scheme.{u}) ⟶ Y) (hf : f ≫ pY = U.ι ≫ pZ) :
    ∃ F : Z ⟶ Y, F ≫ pY = pZ ∧ U.ι ≫ F = f := by
  classical
  obtain ⟨V, hUV, g, hg, hgf, hcover⟩ :=
    exists_open_extension_of_finset_valuationRing_stalk pZ pY U hU hstalk f hf hfin.toFinset
  have hVtop : V = ⊤ := by
    refine le_antisymm le_top (SetLike.coe_subset_coe.mp ?_)
    rw [TopologicalSpace.Opens.coe_top]
    intro z _
    by_cases hz : z ∈ (U : Set Z)
    · exact hUV hz
    · exact hcover z (hfin.mem_toFinset.mpr hz)
  subst hVtop
  refine ⟨Z.topIso.inv ≫ g, ?_, ?_⟩
  · rw [Category.assoc, hg, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  · calc U.ι ≫ Z.topIso.inv ≫ g
        = (Z.homOfLE hUV ≫ (⊤ : Z.Opens).ι) ≫ Z.topIso.inv ≫ g := by
          rw [Scheme.homOfLE_ι]
      _ = Z.homOfLE hUV ≫ ((⊤ : Z.Opens).ι ≫ Z.topIso.inv) ≫ g := by
          simp only [Category.assoc]
      _ = Z.homOfLE hUV ≫ g := by rw [Scheme.ι_toIso_inv, Category.id_comp]
      _ = f := hgf

/-! ### The factorization of Tag 0BY0, given an ample sheaf -/

/-- **The factorization of [Stacks, Tag 0BY0], with a superfluous hypothesis.** Let `k` be a
field, let `X` be a curve over `k` and `Y` a proper variety over `k`, and let `g : X ⟶ Y` be a
morphism over `k`. Then there is a factorization `X ⟶ X̄ ⟶ Y` of `g` in which `X ⟶ X̄` is an
open immersion and `X̄` is a projective curve over `k`, that is, a curve whose structure
morphism is H-projective.

The hypothesis `h09NZ`, the statement of [Stacks, Tag 09NZ], is superfluous: the library proves
it as `Stacks.HQuasiProjectiveDimensionOne.ampleOfNoetherianSeparatedDimLEOne`, and
[Stacks, Tag 0BY0] with nothing assumed is
`AlgebraicGeometry.exists_isOpenImmersion_isCurve_isProjectiveMorphism_factorization_of_isCurve`.
See the module documentation.

The variety structure of `Y` is not used, only properness of `pY`. -/
theorem exists_isOpenImmersion_isCurve_isProjectiveMorphism_factorization
    (h09NZ : Stacks.HQuasiProjectiveDimensionOne.AmpleOfNoetherianSeparatedDimLEOne.{u})
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    [IsCurve k pX] [IsProperVariety k pY] (g : X ⟶ Y) (hg : g ≫ pY = pX) :
    ∃ (Xbar : Scheme.{u}) (q : Xbar ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Xbar) (G : Xbar ⟶ Y),
      IsOpenImmersion j ∧ IsCurve k q ∧ IsProjectiveMorphism q ∧
        j ≫ q = pX ∧ G ≫ pY = q ∧ j ≫ G = g := by
  have hdimX : topologicalKrullDim (X : Type u) = 1 :=
    (inferInstance : IsCurve k pX).topologicalKrullDim_eq_one
  -- Step 1: the projective completion with discrete valuation boundary, Tag 0BXW.
  obtain ⟨Xbar, q, j, hj, hjq, hproj, hdom, hsdense, hfin, hbdry⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation
      h09NZ k pX hdimX.le
  have : IsOpenImmersion j := hj
  have : IsDominant j := hdom
  have : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace Xbar := QuasiCompact.compactSpace_of_compactSpace q
  have : AlgebraicGeometry.IsNoetherian Xbar := AlgebraicGeometry.IsNoetherian.mk
  -- Step 2: the data of the dense open `j(X)` which the extension step consumes.
  have hUdense : Dense ((j.opensRange : Xbar.Opens) : Set Xbar) := by
    rw [Scheme.Hom.coe_opensRange]
    exact hdom.denseRange
  have hUfin : (((j.opensRange : Xbar.Opens) : Set Xbar)ᶜ).Finite := by
    simpa only [Scheme.Hom.coe_opensRange] using hfin
  have hUstalk : ∀ z : Xbar, z ∉ ((j.opensRange : Xbar.Opens) : Set Xbar) →
      ∃ _ : IsDomain (Xbar.presheaf.stalk z), ValuationRing (Xbar.presheaf.stalk z) := by
    intro z hz
    obtain ⟨-, hzdom, hzdvr⟩ := hbdry z (by simpa only [Scheme.Hom.coe_opensRange] using hz)
    refine ⟨hzdom, ?_⟩
    have : IsDomain (Xbar.presheaf.stalk z) := hzdom
    have : IsDiscreteValuationRing (Xbar.presheaf.stalk z) := hzdvr
    infer_instance
  have hfV : (j.isoOpensRange.inv ≫ g) ≫ pY = j.opensRange.ι ≫ q := by
    rw [Category.assoc, hg, ← hjq, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  -- Step 3: the extension across the boundary, finitely many applications of Tag 0BX7.
  obtain ⟨G, hGq, hGU⟩ :=
    exists_extension_of_finite_compl_valuationRing_stalk q pY j.opensRange hUdense hUfin
      hUstalk (j.isoOpensRange.inv ≫ g) hfV
  have hjG : j ≫ G = g := by
    calc j ≫ G = (j.isoOpensRange.hom ≫ j.opensRange.ι) ≫ G := by
          rw [Scheme.Hom.isoOpensRange_hom_ι]
      _ = j.isoOpensRange.hom ≫ j.opensRange.ι ≫ G := by rw [Category.assoc]
      _ = j.isoOpensRange.hom ≫ j.isoOpensRange.inv ≫ g := by rw [hGU]
      _ = g := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  -- Step 4: `Xbar` is reduced, because the reduced dense open is scheme-theoretically dense.
  have : IsReduced (j.opensRange : Scheme.{u}) :=
    isReduced_of_isOpenImmersion j.isoOpensRange.inv
  have : IsSchemeTheoreticallyDominant j.opensRange.ι :=
    (Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant
      j.opensRange).mp hsdense
  have : IsReduced Xbar := IsSchemeTheoreticallyDominant.isReduced j.opensRange.ι
  -- Step 5: `Xbar` is irreducible, being the closure of the irreducible dense range of `j`.
  have : IrreducibleSpace Xbar := by
    rw [irreducibleSpace_def]
    have hirr : IsIrreducible (Set.range j.base) := by
      have h := (IrreducibleSpace.isIrreducible_univ (X : Type u)).image j.base
        j.isOpenEmbedding.isInducing.continuous.continuousOn
      rwa [Set.image_univ] at h
    have hclo := hirr.closure
    rw [hdom.denseRange.closure_range] at hclo
    simpa using hclo
  have : IsIntegral Xbar := isIntegral_of_irreducibleSpace_of_isReduced Xbar
  -- Step 6: `dim Xbar = 1`, by comparison in both directions along the dense open immersion.
  have hdimle : topologicalKrullDim (Xbar : Type u) ≤ topologicalKrullDim (X : Type u) :=
    Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion
      k j pX q hjq (by simpa only [Scheme.Hom.coe_opensRange] using hUdense)
  have hdimge : topologicalKrullDim (X : Type u) ≤ topologicalKrullDim (Xbar : Type u) :=
    j.isOpenEmbedding.isInducing.topologicalKrullDim_le
  rw [hdimX] at hdimle hdimge
  have hvar : IsVariety k q := ⟨⟩
  exact ⟨Xbar, q, j, G, hj,
    { toIsVariety := hvar, topologicalKrullDim_eq_one := le_antisymm hdimle hdimge },
    hproj, hjq, hGq, hjG⟩

end AlgebraicGeometry

end
