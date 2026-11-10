module

public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BirationalGenus
public import StacksFrontier.AlgebraicGeometry.F6Rank89.CoheightOfSurface
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.RegularStalkDvr
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProjectiveLineNormal
public import StacksFrontier.AlgebraicGeometry.Surfaces.ContractionPicardDescent
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocusDVR

/-!
# The map of one exceptional curve onto the one below it

This file carries out the geometric half of step 3 of
[Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R) (Resolution of Surfaces, Lemma
54.17.1). In the situation of that step one has a morphism `g' : X' ⟶ Y'`, a curve `E ⊆ X'`
presented as `𝐏¹_k`, and the exceptional curve `E' ⊆ Y'` of the blowup downstairs, with
`g'(E) ⊆ E'` as sets, and the source says: either `E` maps to a point, or it maps onto `E'` by an
isomorphism. This file produces the morphism `γ : E ⟶ E'` and proves the second alternative:
`γ` is an isomorphism as soon as `g'` is an isomorphism on the local ring at the generic point of
`E`, which is the source's parenthesis "as `f'` is an isomorphism in the generic point of `E`".

Everything here is stated for an arbitrary pair of ideal sheaves whose subschemes are presented
as projective lines, so that nothing of the blowup situation enters; the only input beyond the
presentations is the set-theoretic containment `g'(E) ⊆ E'`, which for the exceptional curves of
Tag 0C5R is
`Stacks.ResolutionOfSurfaces.range_subschemeι_comp_subset_range_pointExceptionalCurve`.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_subschemeMap_of_range_subset` — **the morphism
  `γ : E ⟶ E'`**: a morphism carrying the curve upstairs into the curve downstairs, obtained
  because `E` is reduced and its image lies in `E'`.
* `Stacks.ResolutionOfSurfaces.subschemeMap` — that morphism, chosen, with
  `Stacks.ResolutionOfSurfaces.subschemeMap_comp` its defining equation.
* `Stacks.ResolutionOfSurfaces.map_genericPoint_of_not_const` — **the dichotomy at the generic
  point**: if `γ` is not constant then it carries the generic point of `E` to the generic point of
  `E'`. The curve downstairs is a one-dimensional integral scheme, so a point other than its
  generic point is closed, and a curve whose generic point goes to a closed point collapses.
* `Stacks.ResolutionOfSurfaces.isProper_of_comp_subschemeι` — `γ` is proper, properness
  cancelling against the closed immersion of the curve downstairs.
* `Stacks.ResolutionOfSurfaces.isIso_stalkMap_subschemeMap` — the local ring of `E'` at its
  generic point maps isomorphically to that of `E`: the two local rings are the function fields of
  the two curves, the one of `E` is a quotient of the local ring of `X'` at the generic point of
  `E`, and the comparison is surjective because `g'` is an isomorphism there and injective because
  the source is a field.
* `Stacks.ResolutionOfSurfaces.isBirational_subschemeMap` — hence `γ` is birational.
* `Stacks.ResolutionOfSurfaces.isIso_subschemeMap` — **`γ` is an isomorphism**: it is proper and
  birational onto a one-dimensional scheme, hence finite, and a finite birational morphism onto
  the projective line is an isomorphism
  (`Stacks.ResolutionOfSurfaces.isIso_of_isFinite_of_isBirational_of_iso_projectiveLineProj`).

## What is and is not proved

Everything in this file is proved outright; no result of the source is assumed.

The hypothesis `IsIso (g'.stalkMap η)` at the generic point `η` of `E` is *not* a disguised form
of the conclusion: it is a statement about `g'` at a single point of `X'`, and in Tag 0C5R it is
supplied by item (4) of [Stacks, Tag 0BFP] — the local ring of `Y'` at the generic point of the
exceptional curve `E'` is a discrete valuation ring, so that point lies in the maximal open over
which `g'` is an isomorphism. What this file does *not* contain is the remaining half of the
source's step 3, the nonvanishing of the conormal comparison map of the square; see the
neighbouring file `ExceptionalSquareChain.lean`.

**No `@[stacks 0C5R]` attribute is placed here**: this is a step of the proof of that tag, not a
clause of its statement.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X' Y' : Scheme.{u}}

/-! ### The morphism of the curve upstairs into the curve downstairs -/

/-- **The morphism `γ : E ⟶ E'` of the source's step 3.** A curve `E ⊆ X'` presented as the
projective line is reduced, so a morphism out of it whose set-theoretic image lies in a closed
subscheme `E' ⊆ Y'` factors through that subscheme. -/
public theorem exists_subschemeMap_of_range_subset (k : Type u) [Field k]
    {D : X'.IdealSheafData} (D' : Y'.IdealSheafData)
    (e : projectiveLineProj k ≅ D.subscheme) (g' : X' ⟶ Y')
    (hrange : Set.range (D.subschemeι ≫ g').base ⊆ Set.range D'.subschemeι.base) :
    ∃ γ : D.subscheme ⟶ D'.subscheme, γ ≫ D'.subschemeι = D.subschemeι ≫ g' := by
  have : AlgebraicGeometry.IsIntegral D.subscheme :=
    isIntegral_subscheme_of_iso_projectiveLineProj D k e
  refine (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support D'
    (D.subschemeι ≫ g')).2 ?_
  rwa [← Scheme.IdealSheafData.range_subschemeι]

/-! ### The dichotomy at the generic point -/

/-- **A non-constant morphism between curves presented as projective lines carries the generic
point to the generic point.** The target is an integral scheme of dimension one, so every point
other than its generic point is closed; a morphism carrying the generic point of an irreducible
source to a closed point is constant, since the generic point is dense.

This is the source's dichotomy of step 3 read at the generic point: either the curve collapses,
or it dominates the curve below. -/
public theorem map_genericPoint_of_not_const {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    [AlgebraicGeometry.IsIntegral D.subscheme] [AlgebraicGeometry.IsIntegral D'.subscheme]
    (hdim : topologicalKrullDim D'.subscheme = 1) (γ : D.subscheme ⟶ D'.subscheme)
    (hnc : ¬ ∃ y : D'.subscheme, ∀ t : D.subscheme, γ.base t = y) :
    γ.base (genericPoint D.subscheme) = genericPoint D'.subscheme := by
  by_contra hne
  refine hnc ⟨γ.base (genericPoint D.subscheme), fun t => ?_⟩
  have hcl : IsClosed ({γ.base (genericPoint D.subscheme)} : Set D'.subscheme) :=
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint
      D'.subscheme hdim hne
  have hsp : γ.base (genericPoint D.subscheme) ⤳ γ.base t :=
    (genericPoint_specializes t).map γ.continuous
  have hmem : γ.base t ∈ closure ({γ.base (genericPoint D.subscheme)} : Set D'.subscheme) :=
    hsp.mem_closure
  rw [hcl.closure_eq, Set.mem_singleton_iff] at hmem
  exact hmem

/-! ### Properness of the morphism -/

/-- **The morphism `γ : E ⟶ E'` is proper.** The composite `E ⟶ X' ⟶ Y'` is proper, being a
closed immersion followed by a proper morphism, and the closed immersion `E' ⟶ Y'` is separated,
so properness cancels. -/
public theorem isProper_of_comp_subschemeι {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    {g' : X' ⟶ Y'} (hg' : IsProper g') (γ : D.subscheme ⟶ D'.subscheme)
    (hsq : γ ≫ D'.subschemeι = D.subschemeι ≫ g') : IsProper γ := by
  have h1 : IsProper (D.subschemeι ≫ g') :=
    MorphismProperty.comp_mem _ _ _ (inferInstance : IsProper D.subschemeι) hg'
  have h2 : IsProper (γ ≫ D'.subschemeι) := hsq ▸ h1
  exact IsProper.of_comp γ D'.subschemeι

/-! ### The local ring at the generic point -/

/-- **The local rings at the generic points correspond.** Let `γ : E ⟶ E'` be a morphism of
curves over the square `i ≫ g' = γ ≫ i'`, carrying the generic point of `E` to the generic point
of `E'`, and suppose `g'` is an isomorphism on the local ring of `X'` at the generic point `η` of
`E`. Then `γ` is an isomorphism on the local ring at the generic point.

The square of local rings at `η` says `γ^♯ ∘ i'^♯ = i^♯ ∘ (g')^♯`. The right-hand side is
surjective, `i^♯` being the stalk map of a closed immersion and `(g')^♯` an isomorphism, so `γ^♯`
is surjective; and the local ring of `E'` at its generic point is a field, being the function
field of an integral scheme, so `γ^♯` is injective. -/
public theorem isIso_stalkMap_subschemeMap {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    (g' : X' ⟶ Y') [AlgebraicGeometry.IsIntegral D.subscheme]
    [AlgebraicGeometry.IsIntegral D'.subscheme] (γ : D.subscheme ⟶ D'.subscheme)
    (hsq : γ ≫ D'.subschemeι = D.subschemeι ≫ g')
    (hgen : γ.base (genericPoint D.subscheme) = genericPoint D'.subscheme)
    (hstalk : IsIso (g'.stalkMap (D.subschemeι.base (genericPoint D.subscheme)))) :
    IsIso (γ.stalkMap (genericPoint D.subscheme)) := by
  set t : D.subscheme := genericPoint D.subscheme with ht
  have h1 : Function.Surjective ((D.subschemeι ≫ g').stalkMap t) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (D.subschemeι.stalkMap_surjective t).comp
      (ConcreteCategory.bijective_of_isIso (g'.stalkMap (D.subschemeι.base t))).2
  rw [Scheme.Hom.stalkMap_congr_hom (D.subschemeι ≫ g') (γ ≫ D'.subschemeι) hsq.symm t,
    Scheme.Hom.stalkMap_comp] at h1
  have hsurj : Function.Surjective (γ.stalkMap t) := by
    intro y
    obtain ⟨x, hx⟩ := h1 y
    exact ⟨_, hx⟩
  have hinj : Function.Injective (γ.stalkMap t) := by
    have hfield : IsField (D'.subscheme.presheaf.stalk (γ.base t)) := by
      rw [hgen]
      exact isField_stalk_genericPoint D'.subscheme
    have key : Function.Injective (γ.stalkMap t).hom := by
      intro a b hab
      by_contra hne
      obtain ⟨c, hc⟩ := hfield.mul_inv_cancel (sub_ne_zero_of_ne hne)
      have h0 : (γ.stalkMap t).hom (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have h1 := congrArg (γ.stalkMap t).hom hc
      rw [map_one, map_mul, h0, zero_mul] at h1
      exact one_ne_zero h1.symm
    exact key
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩

/-! ### Birationality and the isomorphism -/

/-- **The morphism `γ : E ⟶ E'` is birational.** The two curves are integral, so their generic
points are their only generic points, `γ` matches them by hypothesis, and the local rings there
correspond by `Stacks.ResolutionOfSurfaces.isIso_stalkMap_subschemeMap`. -/
public theorem isBirational_subschemeMap {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    (g' : X' ⟶ Y') [AlgebraicGeometry.IsIntegral D.subscheme]
    [AlgebraicGeometry.IsIntegral D'.subscheme] (γ : D.subscheme ⟶ D'.subscheme)
    (hsq : γ ≫ D'.subschemeι = D.subschemeι ≫ g')
    (hgen : γ.base (genericPoint D.subscheme) = genericPoint D'.subscheme)
    (hstalk : IsIso (g'.stalkMap (D.subschemeι.base (genericPoint D.subscheme)))) :
    IsBirational γ := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    exact Set.bijOn_singleton.2 hgen
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    rw [hx]
    exact isIso_stalkMap_subschemeMap g' γ hsq hgen hstalk

/-- **The morphism `γ : E ⟶ E'` is an isomorphism**, which is the second alternative of step 3 of
[Stacks, Tag 0C5R].

It is proper by `Stacks.ResolutionOfSurfaces.isProper_of_comp_subschemeι` and birational by
`Stacks.ResolutionOfSurfaces.isBirational_subschemeMap`; a proper birational morphism onto a
locally Noetherian scheme of dimension at most one is finite
(`AlgebraicGeometry.isFinite_of_isProper_of_isBirational`); and a finite birational morphism onto
a scheme presented as the projective line is an isomorphism
(`Stacks.ResolutionOfSurfaces.isIso_of_isFinite_of_isBirational_of_iso_projectiveLineProj`),
the projective line being normal. -/
public theorem isIso_subschemeMap (k' : Type u) [Field k'] {D : X'.IdealSheafData}
    {D' : Y'.IdealSheafData} (e' : projectiveLineProj k' ≅ D'.subscheme)
    [IsLocallyNoetherian Y'] {g' : X' ⟶ Y'} (hg' : IsProper g')
    [AlgebraicGeometry.IsIntegral D.subscheme] [AlgebraicGeometry.IsIntegral D'.subscheme]
    (γ : D.subscheme ⟶ D'.subscheme)
    (hsq : γ ≫ D'.subschemeι = D.subschemeι ≫ g')
    (hgen : γ.base (genericPoint D.subscheme) = genericPoint D'.subscheme)
    (hstalk : IsIso (g'.stalkMap (D.subschemeι.base (genericPoint D.subscheme)))) :
    IsIso γ := by
  have : IsLocallyNoetherian D'.subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme D'
  have : IsProper γ := isProper_of_comp_subschemeι hg' γ hsq
  have hbir : IsBirational γ := isBirational_subschemeMap g' γ hsq hgen hstalk
  have : IsFinite γ :=
    isFinite_of_isProper_of_isBirational γ hbir
      (le_of_eq (topologicalKrullDim_eq_one_of_iso_projectiveLineProj k' e'))
  exact isIso_of_isFinite_of_isBirational_of_iso_projectiveLineProj k' γ e' hbir

/-! ### The curve downstairs has codimension one -/

/-- **The generic point of a curve in a surface has codimension one.** Let `E' ⊆ Y'` be a closed
subscheme which is integral of dimension one inside an integral scheme of dimension at most two,
and suppose the generic point `z` of `E'`, seen in `Y'`, is not the generic point of `Y'`. Then
the local ring of `Y'` at `z` has dimension one.

The codimension of `z` is at most two by the dimension of `Y'`; it is not zero because `z` is not
a generic point of `Y'`; and it is not two, since a point of codimension two on a surface is the
only point of any set it is the generic point of
(`AlgebraicGeometry.eq_genericPoint_of_coheight_two`), which would make `E'` a one-point space and
hence zero-dimensional. -/
public theorem coheight_subschemeι_genericPoint_eq_one {D' : Y'.IdealSheafData}
    [AlgebraicGeometry.IsIntegral Y'] [AlgebraicGeometry.IsIntegral D'.subscheme]
    (hdim2 : topologicalKrullDim Y' ≤ 2) (hdim1 : topologicalKrullDim D'.subscheme = 1)
    (hz : D'.subschemeι.base (genericPoint D'.subscheme) ≠ genericPoint Y') :
    Order.coheight (D'.subschemeι.base (genericPoint D'.subscheme)) = 1 := by
  set z := D'.subschemeι.base (genericPoint D'.subscheme) with hzdef
  have hrange : IsGenericPoint z (Set.range D'.subschemeι.base) := by
    refine Set.Subset.antisymm ?_ ?_
    · rw [Scheme.IdealSheafData.range_subschemeι]
      exact (closure_minimal (by
        rw [Set.singleton_subset_iff, hzdef, ← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨genericPoint D'.subscheme, rfl⟩) D'.support.isClosed)
    · rintro - ⟨p, rfl⟩
      exact ((genericPoint_specializes p).map D'.subschemeι.continuous).mem_closure
  have hne0 : Order.coheight z ≠ 0 := by
    intro h0
    have h1 : z ≤ genericPoint Y' := Scheme.le_iff_specializes.mpr (genericPoint_specializes z)
    have h2 : genericPoint Y' ≤ z := Order.coheight_eq_zero.mp h0 h1
    exact hz (inseparable_iff_specializes_and.mpr
      ⟨Scheme.le_iff_specializes.mp h2, Scheme.le_iff_specializes.mp h1⟩).eq
  have hne2 : Order.coheight z ≠ 2 := by
    intro h2
    have : Subsingleton (D'.subscheme : Type u) := by
      refine ⟨fun p q => D'.subschemeι.isEmbedding.injective ?_⟩
      exact (eq_genericPoint_of_coheight_two hdim2 hrange h2 ⟨p, rfl⟩).trans
        (eq_genericPoint_of_coheight_two hdim2 hrange h2 ⟨q, rfl⟩).symm
    have hle := Order.krullDim_nonpos_of_subsingleton (α := (D'.subscheme : Type u))
    rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim,
      hdim1] at hle
    norm_num at hle
  have hco : Order.coheight z ≤ 2 :=
    WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim z).trans hdim2)
  have hfin : Order.coheight z ≠ ⊤ := fun h => by simp [h] at hco
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at hco hne0 hne2 ⊢
  have h1 : n ≤ 2 := by exact_mod_cast hco
  have h2 : n ≠ 0 := fun h => hne0 (by rw [h]; rfl)
  have h3 : n ≠ 2 := fun h => hne2 (by rw [h]; rfl)
  have h4 : n = 1 := by omega
  rw [h4]
  rfl

/-! ### The stalk hypothesis, from the maximal isomorphism open -/

/-- **The source's "as `f'` is an isomorphism in the generic point of `E`".** In the situation of
step 3 of [Stacks, Tag 0C5R], the local ring of `Y'` at the generic point of the curve `E'` below
is a discrete valuation ring, the curve having codimension one on the regular scheme `Y'`; so item
(2) of [Stacks, Tag 0BFP] puts that point in the maximal open over which `g'` is an isomorphism,
and the generic point of `E` lies over it. Hence `g'` is an isomorphism on the local ring at the
generic point of `E`. -/
public theorem isIso_stalkMap_genericPoint {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    [AlgebraicGeometry.IsIntegral Y'] [AlgebraicGeometry.IsNoetherian Y'] [IsReduced X']
    [AlgebraicGeometry.IsIntegral D.subscheme] [AlgebraicGeometry.IsIntegral D'.subscheme]
    (hY' : IsRegular Y') (hdim2 : topologicalKrullDim Y' ≤ 2)
    (hdim1 : topologicalKrullDim D'.subscheme = 1)
    (hz : D'.subschemeι.base (genericPoint D'.subscheme) ≠ genericPoint Y')
    (g' : X' ⟶ Y') (hgp : IsProper g') (hg' : IsBirational g') (U' : Y'.Opens)
    (hU' : IsGreatest { V : Y'.Opens | IsIso (g' ∣_ V) } U') (γ : D.subscheme ⟶ D'.subscheme)
    (hsq : γ ≫ D'.subschemeι = D.subschemeι ≫ g')
    (hgen : γ.base (genericPoint D.subscheme) = genericPoint D'.subscheme) :
    IsIso (g'.stalkMap (D.subschemeι.base (genericPoint D.subscheme))) := by
  have hgp' := hgp
  have : IsDiscreteValuationRing
      (Y'.presheaf.stalk (D'.subschemeι.base (genericPoint D'.subscheme))) :=
    isDiscreteValuationRing_stalk_of_isRegular hY'
      (coheight_subschemeι_genericPoint_eq_one hdim2 hdim1 hz)
  have hmem : D'.subschemeι.base (genericPoint D'.subscheme) ∈ U' :=
    mem_maximal_isomorphism_open_of_isDiscreteValuationRing g' hg' U' hU' _
  have himg : g'.base (D.subschemeι.base (genericPoint D.subscheme))
      = D'.subschemeι.base (genericPoint D'.subscheme) := by
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply, hgen]
  have hmem' : g'.base (D.subschemeι.base (genericPoint D.subscheme)) ∈ U' := by
    rw [himg]; exact hmem
  exact isIso_stalkMap_of_isIso_morphismRestrict g' hU'.1 hmem'

/-! ### The second alternative of step 3, assembled -/

/-- **The second alternative of step 3 of [Stacks, Tag 0C5R], with no hypothesis on the stalks.**
Let `g' : X' ⟶ Y'` be a proper birational morphism of integral schemes with `Y'` regular of
dimension at most two and `X'` reduced, let `E ⊆ X'` be a curve presented as `𝐏¹_k`, let
`E' ⊆ Y'` be a curve presented as `𝐏¹_{k'}` whose generic point is not that of `Y'`, and suppose
`g'` carries `E` into `E'` set-theoretically. Then either `g'` collapses `E` to a point of `Y'`,
or the induced morphism `γ : E ⟶ E'` is an isomorphism.

This is the whole of the source's step 3 except for the nonvanishing of the conormal comparison
map: the morphism `γ` comes from
`Stacks.ResolutionOfSurfaces.exists_subschemeMap_of_range_subset`, the alternative at the generic
point from `Stacks.ResolutionOfSurfaces.map_genericPoint_of_not_const`, the local ring comparison
from `Stacks.ResolutionOfSurfaces.isIso_stalkMap_genericPoint` — which is the source's "as `f'` is
an isomorphism in the generic point of `E`" — and the isomorphy from
`Stacks.ResolutionOfSurfaces.isIso_subschemeMap`. -/
public theorem exists_isIso_subschemeMap_or_const (k k' : Type u) [Field k] [Field k']
    {D : X'.IdealSheafData} {D' : Y'.IdealSheafData} (e : projectiveLineProj k ≅ D.subscheme)
    (e' : projectiveLineProj k' ≅ D'.subscheme)
    [AlgebraicGeometry.IsIntegral Y'] [AlgebraicGeometry.IsNoetherian Y'] [IsReduced X']
    (hY' : IsRegular Y') (hdim2 : topologicalKrullDim Y' ≤ 2)
    (hz : ∀ p : D'.subscheme, D'.subschemeι.base p ≠ genericPoint Y')
    (g' : X' ⟶ Y') (hgp : IsProper g') (hg' : IsBirational g') (U' : Y'.Opens)
    (hU' : IsGreatest { V : Y'.Opens | IsIso (g' ∣_ V) } U')
    (hrange : Set.range (D.subschemeι ≫ g').base ⊆ Set.range D'.subschemeι.base) :
    (∃ y : Y', ∀ t : D.subscheme, g'.base (D.subschemeι.base t) = y) ∨
      ∃ γ : D.subscheme ⟶ D'.subscheme,
        γ ≫ D'.subschemeι = D.subschemeι ≫ g' ∧ IsIso γ := by
  classical
  have : AlgebraicGeometry.IsIntegral D.subscheme :=
    isIntegral_subscheme_of_iso_projectiveLineProj D k e
  have : AlgebraicGeometry.IsIntegral D'.subscheme :=
    isIntegral_subscheme_of_iso_projectiveLineProj D' k' e'
  obtain ⟨γ, hsq⟩ := exists_subschemeMap_of_range_subset k D' e g' hrange
  by_cases hnc : ∃ y : D'.subscheme, ∀ t : D.subscheme, γ.base t = y
  · obtain ⟨y, hy⟩ := hnc
    refine Or.inl ⟨D'.subschemeι.base y, fun t => ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply, hy t]
  · have hgen := map_genericPoint_of_not_const
      (topologicalKrullDim_eq_one_of_iso_projectiveLineProj k' e') γ hnc
    exact Or.inr ⟨γ, hsq, isIso_subschemeMap k' e' hgp γ hsq hgen
      (isIso_stalkMap_genericPoint hY' hdim2
        (topologicalKrullDim_eq_one_of_iso_projectiveLineProj k' e')
        (hz (genericPoint D'.subscheme)) g' hgp hg' U' hU' γ hsq hgen)⟩

end Stacks.ResolutionOfSurfaces

end
