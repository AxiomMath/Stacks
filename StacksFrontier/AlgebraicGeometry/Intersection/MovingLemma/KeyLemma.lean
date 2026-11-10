module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ComponentPoints
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.DisplayIdeals
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProperCone
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.StalkDimensions
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectionDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLinesOfClosedSubset
public import StacksFrontier.RingTheory.Sequence.RegularLocus

/-!
# Stacks 0B0E, the key lemma for the moving lemma

Let `X ⊆ 𝐏^N` be a nonsingular closed subvariety of dimension `n`, let `Z ⊆ X` be a closed
subvariety of dimension `d < n` and let `T_i ⊆ X` be finitely many closed subvarieties of
dimension `d' < n`. Then there is a closed subvariety `C ⊆ 𝐏^N` intersecting `X` properly with

`C · X = [Z] + ∑ m_j [Z_j]`

in the intersection product of Section 0B08, the `Z_j ⊆ X` irreducible of dimension `d`, distinct
from `Z`, with `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` or `dim (Z_j ∩ T_i) + n ≤ d + d'`, and with
strict inequality whenever `Z` does not intersect `T_i` properly in `X`.

The lemma is proved in the generality of Remark 0B61: `X` need not be nonsingular, and `Z` and
the `T_i` are closed subvarieties of an open subscheme `U ⟶ X` inside the nonsingular locus of
`X`, the display being read on `U`; the `T_i` may also have different dimensions.

## Main results

* `exists_intersectProperly_cycleComap_torFormulaCycleIntersectionProduct_eq` of
  `AlgebraicGeometry.ProjectiveSpaceOfModule`: the lemma on an open subscheme `U ⟶ X` inside
  `X^{reg}`, Remark 0B61.
* `exists_intersectProperly_torFormulaCycleIntersectionProduct_eq` of
  `AlgebraicGeometry.ProjectiveSpaceOfModule`: the lemma, Tag 0B0E, the case `U = X`.
* `exists_intersectProperly_torFormulaCycleIntersectionProduct_apply_eq_one_of_isFinite` of
  `AlgebraicGeometry.ProjectiveSpaceOfModule`: the cone over the image of `Z` under a finite
  projection étale at the generic point of `Z`, and the coefficient one of `Z` in `C · X`.
* `exists_isFinite_projection_excess_clauses_of_isOpenImmersion` of
  `AlgebraicGeometry.ProjectiveSpaceOfModule`: the projection of the proof of Tag 0B0E, along
  which every other closed subvariety of `π^{-1}(π(Z))` of dimension `d` has the two dimension
  bounds of the lemma, read in an open subset of the nonsingular locus.

## Implementation notes

**Only the chosen points need to be nonsingular.** The cone `C` is built, and `C · X` computed,
on `X` itself; nonsingularity enters only through the étaleness of the projection at the chosen
points of `Z` and of the `Z ∩ T_i`, which part (2) of Tag 0B1Q gives at nonsingular points. So
the argument runs for `Z` and `T_i` closed in an open subscheme `j₀ : U ⟶ X` with image in
`X^{reg}`, with their closures in `X` fed to the projection and the points chosen in `U`; the
restriction of `C · X` to `U` is its coefficientwise inverse image `Stacks.Chow.cycleComap` along
`U ⟶ X ⟶ 𝐏^N`. Lemma 0B0E is the case `j₀ = 𝟙 X` of a nonsingular `X`.

**The non-strict dimension clause is a disjunction**, namely

`dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)  ∨  dim (Z_j ∩ T_i) + n ≤ d + d'`,

written additively because `WithBot ℕ∞` has no subtraction. This is exactly what condition (4) of
the source's proof yields: that condition supplies `T_i ∩ Z_j ⊆ (T_i ∩ Z) ∪ E_i` with
`dim E_i + n ≤ d + d'`, hence `dim (Z_j ∩ T_i) ≤ max (dim (Z ∩ T_i)) (dim E_i)`, and the two
branches of that maximum are the two disjuncts. Tag 0AZP turns the second disjunct into the first
exactly when `Z ∩ T_i` is nonempty, since only then does 0AZP supply a component of `Z ∩ T_i` and
with it `d + d' ≤ dim (Z ∩ T_i) + n`; so the disjunction implies the source's own
`dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` wherever that holds, and adds no hypothesis.

**The first disjunct alone is false, in the bottom case `Z ∩ T_i = ∅`.** Take `k` algebraically
closed, `N = 3`, `X` a nonsingular quadric surface in `𝐏^3` — so `X ≅ 𝐏^1 × 𝐏^1` and `n = 2` —
and `d = d' = 1` with `Z` and `T = T_1` two distinct lines of the *same* ruling, so that
`Z ∩ T = ∅` and every hypothesis holds. Suppose `C` were as the conclusion asserts with
`Z_j ∩ T = ∅` for every `j`, which is what the first disjunct demands when `dim (Z ∩ T) = ⊥`.
Then `dim C = 2`. Indeed for `dim C ≤ 1` proper intersection forces `dim (C ∩ X) ≤ 0`, so the
coefficient at the generic point of `Z` is `0` and not `1`; and for `C = 𝐏^3` the product `C · X`
is the zero cycle at the delta-dimension `d = 1` at which the statement below is graded — the
Tor-support bound of Section 43.14 fails for that pair, `C ∩ X = X` having dimension `2` — so the
coefficient at the generic point of `Z` is again `0` and not `1` (in the source's grading
`r + s - N = 2` the product is `[X]` instead, whose coefficient at the generic point of `Z` is
also `0`; the case dies in either convention). A surface and a curve in `𝐏^3` meet, so `C` meets
`T ⊆ X`, at `w` say; every component of the intersection of two surfaces in `𝐏^3` has dimension
at least `2 + 2 - 3 = 1`, and proper intersection bounds it above by `1`, so `w` lies on a
component `D` of `C ∩ X` of dimension exactly `1`. `D` is not disjoint from `T`, so it is none of
`Z` or the `Z_j`, all of which are disjoint from `T`; its coefficient in `C · X` is therefore `0`.
But `D` is a proper component of `C ∩ X` of exactly the delta-dimension the product selects, so
its Serre multiplicity is positive. Contradiction. In that bottom case it is the second disjunct
that holds.

**The strict clause needs no guard.** Its hypothesis is
`¬ (dim (Z ∩ T_i) + dim X ≤ dim Z + dim T_i)`, and for `Z ∩ T_i = ∅` the left summand is `⊥`, so
`⊥ + dim X = ⊥` is below everything and the hypothesis is false: the clause is vacuous exactly on
the bottom case, and is registered as the source has it.

**`X ⊂ 𝐏^N` is read as `⊆`, so `dim X = N` is included.** The source's proof builds a chain of
projections away from points `𝐏(V_N) ⇢ ⋯ ⇢ 𝐏(V_n)`, which is the empty chain when `n = N`; and
`⊂` in the Stacks Project does not by itself exclude equality — Tag 0H8A, which this very proof
cites, spells the properness out separately as `Z ≠ X ≠ 𝐏(V)`. The case `n = N` is treated here
on its own: then `X` is the whole of `𝐏(V)`, because a proper closed subset of an irreducible
space of finite dimension has strictly smaller dimension, and the conclusion holds with `C = Z`
and an empty family of `Z_j`. Its one computation is that the coefficient of `Z` in `Z · 𝐏(V)` is
one, which is Tag 0B1J at `I₀ = 𝔪_ξ` and `J₀` the local ideal of `𝐏(V)` at `ξ`: the length-one
hypothesis is `𝔪_ξ ⊔ J₀ = 𝔪_ξ` and the proper-intersection hypothesis is `N + d ≤ d + N`. That
there are no further components is a dimension count — each would be a closed subvariety of `Z`
of dimension `dim Z`, hence `Z` itself, which the decomposition forbids.

**The ambient scheme of the conclusion is `𝐏(V)` and of the hypotheses is `X`.** The conditions
on the projection are proved on `X`
(`exists_submodule_finrank_eq_isFinite_etaleAt_projection` of
`AlgebraicGeometry.ProjectiveSpaceOfModule`), while the cycles of the display live on `𝐏(V)`;
`i_X` is a closed immersion, so its underlying map is an embedding and
`AlgebraicGeometry.topologicalKrullDim_image_eq_of_isEmbedding` transports every dimension across
it. The subvarieties of the statement are therefore the images `i_X(Z)` and `i_X(T_i)`.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1J](https://stacks.math.columbia.edu/tag/0B1J)
* [Stacks Project, Tag 0AZP](https://stacks.math.columbia.edu/tag/0AZP)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
* [Stacks Project, Tag 0H8A](https://stacks.math.columbia.edu/tag/0H8A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow

universe u

namespace AlgebraicGeometry

/-- **A topological embedding preserves the dimension of a subspace.** The embedding is a
homeomorphism onto its range, which carries the subset onto its image. -/
public theorem topologicalKrullDim_image_eq_of_isEmbedding {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hf : Topology.IsEmbedding f) (S : Set A) :
    topologicalKrullDim ↥(f '' S) = topologicalKrullDim ↥S := by
  have h1 : topologicalKrullDim ↥S =
      topologicalKrullDim ↥(hf.toHomeomorph '' S : Set ↥(Set.range f)) :=
    IsHomeomorph.topologicalKrullDim_eq _ (hf.toHomeomorph.image S).isHomeomorph
  have h2 : (hf.toHomeomorph '' S : Set ↥(Set.range f)) =
      (Subtype.val : ↥(Set.range f) → B) ⁻¹' (f '' S) := by
    ext p
    refine ⟨?_, ?_⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, hfa⟩
      exact ⟨a, ha, Subtype.ext hfa⟩
  rw [h1, h2, topologicalKrullDim_preimage_val (Set.range f) (f '' S) (Set.image_subset_range f S)]

/-- **The dimension of the closure of a point is the truncation of its relative dimension.**
This is Tag 02QO applied to the reduced closure of the point, whose space is that closure. -/
public theorem topologicalKrullDim_closure_eq_toNat_relativeDimension (k : Type u) [Field k]
    {X : Scheme.{u}} (q : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] (x : X) :
    topologicalKrullDim ↥(closure ({x} : Set X)) =
      (((relativeDimension (fieldChowSituation k).dimensionFunction q x).toNat : ℕ) :
        WithBot ℕ∞) := by
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hgen : IsGenericPoint (genericPoint (integralComponentAt x).subscheme)
      (Set.univ : Set (integralComponentAt x).subscheme) :=
    (IrreducibleSpace.isIrreducible_univ _).isGenericPoint_genericPoint isClosed_univ
  have hkey := topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fun _ _ ↦ rfl) q (integralComponentAt x).subschemeι
    (genericPoint (integralComponentAt x).subscheme) hgen
  rw [show (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x from
    genericPointOf_integralComponentAt x, ← topologicalKrullDim_support_eq
    (integralComponentAt x), coe_support_integralComponentAt] at hkey
  exact hkey

/-- **The dimension of the closure of a point from its relative dimension.** This is the converse
of `AlgebraicGeometry.relativeDimension_eq_of_topologicalKrullDim_closure_eq`, and is what turns
the delta-dimension in which the intersection product of Section 0B08 is graded into the
dimension `d` the source asserts of each `Z_j`. -/
public theorem topologicalKrullDim_closure_eq_of_relativeDimension_eq (k : Type u) [Field k]
    {X : Scheme.{u}} (q : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] {n : ℕ} {x : X}
    (h : relativeDimension (fieldChowSituation k).dimensionFunction q x = (n : ℤ)) :
    topologicalKrullDim ↥(closure ({x} : Set X)) = (n : WithBot ℕ∞) := by
  rw [topologicalKrullDim_closure_eq_toNat_relativeDimension k q, h]
  simp

/-- A natural number is not `⊤` in `WithBot ℕ∞`. -/
private theorem natCast_ne_top (q : ℕ) : ((q : ℕ) : WithBot ℕ∞) ≠ ⊤ := by
  intro h
  rw [← WithBot.coe_top] at h
  exact (ENat.natCast_ne_top q) (by exact_mod_cast h)

/-- A natural number is not `⊥` in `WithBot ℕ∞`. -/
private theorem natCast_ne_bot (q : ℕ) : ((q : ℕ) : WithBot ℕ∞) ≠ ⊥ := by
  exact_mod_cast WithBot.coe_ne_bot

/-- A natural number is below `⊤` in `WithBot ℕ∞`. -/
private theorem natCast_lt_top (q : ℕ) : ((q : ℕ) : WithBot ℕ∞) < ⊤ :=
  lt_top_iff_ne_top.mpr (natCast_ne_top q)

/-- A closed subset of an irreducible space of the same finite dimension is the whole space. -/
private theorem eq_univ_of_topologicalKrullDim_eq {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {A : Set T} (hA : IsClosed A)
    (h : topologicalKrullDim ↥A = topologicalKrullDim T) (hfin : topologicalKrullDim T < ⊤) :
    A = Set.univ := by
  by_contra hne
  exact (topologicalKrullDim_lt_of_isClosed_ne_univ hA hne hfin).ne h

/-- A closed subset of an irreducible set of the same finite dimension is that set. -/
private theorem eq_of_subset_of_topologicalKrullDim_eq {T : Type*} [TopologicalSpace T]
    {Z W : Set T} (hZ : IsIrreducible Z) (hW : IsClosed W) (hsub : W ⊆ Z)
    (h : topologicalKrullDim ↥W = topologicalKrullDim ↥Z) (hfin : topologicalKrullDim ↥Z < ⊤) :
    W = Z := by
  have : IrreducibleSpace ↥Z := Subtype.irreducibleSpace hZ
  have huniv := eq_univ_of_topologicalKrullDim_eq (hW.preimage continuous_subtype_val)
    (by rw [topologicalKrullDim_preimage_val Z W hsub, h]) hfin
  rw [Set.preimage_eq_univ_iff, Subtype.range_coe] at huniv
  exact Set.Subset.antisymm hsub huniv

namespace ProjectiveSpaceOfModule

/-- The generic point of `𝐏(V)` has relative dimension `N` when `V` has dimension `N + 1`. -/
private theorem relativeDimension_genericPoint_projectiveSpaceOfModule (k V : Type u) [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V] {N : ℕ}
    (hV : Module.finrank k V = N + 1) :
    relativeDimension (fieldChowSituation k).dimensionFunction (projectiveSpaceOfModuleToSpec k V)
      (genericPoint (projectiveSpaceOfModule k V)) = (N : ℤ) := by
  refine relativeDimension_eq_of_topologicalKrullDim_closure_eq k _ ?_
  have hu : closure ({genericPoint (projectiveSpaceOfModule k V)} :
      Set (projectiveSpaceOfModule k V)) = Set.univ :=
    Set.eq_univ_of_forall fun z => specializes_iff_mem_closure.mp (genericPoint_specializes z)
  rw [hu, topologicalKrullDim_univ]
  exact topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV

/-- The Tor-formula product of two prime cycles with a Tor support bound is a cycle of dimension
`d`. -/
private theorem torFormulaCycleIntersectionProduct_single_single_mem_cyclesOfDimension
    (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] [DecidableEq X] (hX : IsRegular X) (d : ℤ) {x y : X}
    (hb : TorFormula.TorSupportBound C f hX d x y) :
    TorFormula.torFormulaCycleIntersectionProduct C f hX d
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) ∈ cyclesOfDimension C f d := by
  rw [TorFormula.torFormulaCycleIntersectionProduct,
    TorFormula.cycleIntersectionProduct_single_single _ x y 1 1,
    TorFormula.torFormulaSubvarietyProductTotal_eq_of_bound C f hX d hb, mul_one, one_smul,
    TorFormula.torSubvarietyProductOfBound]
  exact TorFormula.intersectionProductCycle_mem_cyclesOfDimension C f hX _ _ _ _ d hb

/-- **The regularity of `𝐏(V)`.** Every local ring of the projective space of a finite-dimensional
vector space is regular, and the space is locally Noetherian, which is regularity. -/
public theorem isRegular_projectiveSpaceOfModule (k V : Type u) [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [Nontrivial V] :
    IsRegular (projectiveSpaceOfModule k V) :=
  ((isRegular_tfae (projectiveSpaceOfModule k V)).out 2 1).mp
    (show IsLocallyNoetherian (projectiveSpaceOfModule k V) ∧
        ∀ z : projectiveSpaceOfModule k V,
          IsRegularLocalRing ((projectiveSpaceOfModule k V).presheaf.stalk z) from
      ⟨inferInstance, isRegularLocalRing_stalk_projectiveSpaceOfModule k V⟩)

/-- **The cone of Stacks 0B0E, without regularity of `X`.** Let `X ⊆ 𝐏(V)` be a closed
subvariety of dimension `n < N` of the projective space of a vector space of dimension `N + 1`
over an algebraically closed field, let `W ≤ V` be of dimension `n + 1` with the projection
`π = r_W|_X` finite, and let `Z ⊆ X` be irreducible closed of dimension `d` such that `π` is
étale at the generic point of `Z`. Then there is a closed subvariety `C ⊆ 𝐏(V)` intersecting
`X` properly such that the coefficient of `Z` in `C · X` is one and every point of the support
of `C · X` lies on `C` and is the image of a point `w ∈ π^{-1}(π(Z))` whose closure has
dimension `d`. -/
public theorem exists_intersectProperly_torFormulaCycleIntersectionProduct_apply_eq_one_of_isFinite
    (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] [DecidableEq (projectiveSpaceOfModule k V)]
    {N n d : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞)) (hnN : n < N)
    (W : Submodule k V) (hW : Module.finrank k ↥W = n + 1)
    (j : X ⟶ (projectionDomain k V W).toScheme) (hj : j ≫ (projectionDomain k V W).ι = iX)
    [IsFinite (j ≫ projection k V W)]
    (Z : Set X) (hZcl : IsClosed Z) (hZirr : IsIrreducible Z)
    (hZd : topologicalKrullDim ↥Z = (d : WithBot ℕ∞))
    (het : EtaleAt (j ≫ projection k V W) hZirr.genericPoint)
    (XC : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hXC : (XC : Set (projectiveSpaceOfModule k V)) = Set.range iX.base) :
    ∃ C : IrreducibleCloseds (projectiveSpaceOfModule k V),
      AlgebraicGeometry.IntersectProperly C XC ∧
      TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
          (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
          (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
          (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ))
          (iX.base hZirr.genericPoint) = 1 ∧
      ∀ p : projectiveSpaceOfModule k V,
        TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
            (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
            (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
            (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) p ≠ 0 →
          p ∈ (C : Set (projectiveSpaceOfModule k V)) ∧
          ∃ w : X, w ∈ (j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z) ∧
            iX.base w = p ∧
            topologicalKrullDim ↥(closure ({w} : Set X)) = (d : WithBot ℕ∞) := by
  classical
  set sP : projectiveSpaceOfModule k V ⟶ (fieldChowSituation k).S :=
    projectiveSpaceOfModuleToSpec k V with hsP
  set hP : IsRegular (projectiveSpaceOfModule k V) := isRegular_projectiveSpaceOfModule k V with hhP
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (iX ≫ projectiveSpaceOfModuleToSpec k V)
  have hdimimg : ∀ A : Set X, topologicalKrullDim ↥(iX.base '' A) = topologicalKrullDim ↥A :=
    fun A => topologicalKrullDim_image_eq_of_isEmbedding iX.isClosedEmbedding.isEmbedding A
  have : Nontrivial ↥W := Module.nontrivial_of_finrank_pos (R := k) (by rw [hW]; omega)
  set prj : X ⟶ projectiveSpaceOfModule k ↥W := j ≫ projection k V W with hprj
  have : LocallyOfFiniteType prj := inferInstance
  have : LocallyOfFinitePresentation prj :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType prj
  -- the subvariety `C` and its proper intersection with `X`
  obtain ⟨C, hCXproper, hCnum, hCinter, hCdim, hCset⟩ :=
    exists_coneCl_intersectProperly_inter_eq k V hV iX hdimX hnN W hW j hj Z hZirr hZcl hZd
      XC hXC
  rw [← hprj] at hCinter hCdim hCset
  -- the three generic points
  set ζ := hZirr.genericPoint with hζdef
  have hζZ : closure ({ζ} : Set X) = Z := hZirr.closure_genericPoint hZcl
  set ξ := iX.base ζ with hξdef
  set x := C.isIrreducible.genericPoint with hxdef
  set y := XC.isIrreducible.genericPoint with hydef
  have hCcl : closure ({x} : Set (projectiveSpaceOfModule k V)) =
      (C : Set (projectiveSpaceOfModule k V)) :=
    C.isIrreducible.closure_genericPoint C.isClosed'
  have hXCcl : closure ({y} : Set (projectiveSpaceOfModule k V)) =
      (XC : Set (projectiveSpaceOfModule k V)) :=
    XC.isIrreducible.closure_genericPoint XC.isClosed'
  have hξcl : closure ({ξ} : Set (projectiveSpaceOfModule k V)) = iX.base '' Z := by
    rw [← hζZ, ← Set.image_singleton (f := iX.base) (a := ζ)]
    exact iX.isClosedEmbedding.closure_image_eq _
  -- the three relative dimensions
  have hz : relativeDimension (fieldChowSituation k).dimensionFunction sP ξ = (d : ℤ) := by
    refine relativeDimension_eq_of_topologicalKrullDim_closure_eq k sP ?_
    rw [hξcl, hdimimg, hZd]
  have hgy : relativeDimension (fieldChowSituation k).dimensionFunction sP y = (n : ℤ) := by
    refine relativeDimension_eq_of_topologicalKrullDim_closure_eq k sP ?_
    rw [hXCcl, hXC, topologicalKrullDim_range_eq iX, hdimX]
  have hgpP := relativeDimension_genericPoint_projectiveSpaceOfModule k V hV
  -- the two specializations
  have hζmemZ : ζ ∈ Z := hζZ ▸ subset_closure (Set.mem_singleton ζ)
  have hξC : ξ ∈ (C : Set (projectiveSpaceOfModule k V)) ∩
      (XC : Set (projectiveSpaceOfModule k V)) := by
    rw [hCinter]
    exact ⟨ζ, Set.subset_preimage_image prj.base Z hζmemZ, rfl⟩
  have hzx : ξ ∈ closure ({x} : Set (projectiveSpaceOfModule k V)) := hCcl ▸ hξC.1
  have hzy : ξ ∈ closure ({y} : Set (projectiveSpaceOfModule k V)) := hXCcl ▸ hξC.2
  -- the delta-dimension bound at the one pair, and the ambient dimension bound
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k V) ≤ (N : WithBot ℕ∞) :=
    le_of_eq (topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV)
  have hinterCX : closure ({x} : Set (projectiveSpaceOfModule k V)) ∩
      closure ({y} : Set (projectiveSpaceOfModule k V)) =
      iX.base '' (prj.base ⁻¹' (prj.base '' Z)) := by
    rw [hCcl, hXCcl]; exact hCinter
  have hb : TorFormula.TorSupportBound (fieldChowSituation k) sP hP (d : ℤ) x y := by
    refine TorFormula.torSupportBound_of_topologicalKrullDim_le k sP hP d x y ?_
    rw [hinterCX, hdimimg]
    exact hCdim
  -- the proper-intersection inequality at `ξ`, from `N + d ≤ dim C + dim X`
  have hproper : ringKrullDim ((projectiveSpaceOfModule k V).presheaf.stalk ξ) ≤
      ringKrullDim ((projectiveSpaceOfModule k V).presheaf.stalk ξ ⧸
          TorFormula.localIdealAt x ξ) +
        ringKrullDim ((projectiveSpaceOfModule k V).presheaf.stalk ξ ⧸
          TorFormula.localIdealAt y ξ) := by
    refine ringKrullDim_stalk_le_add_ringKrullDim_quotient_localIdealAt k sP hzx hzy ?_
    rw [hgpP, hz, hgy]
    have hcnat := topologicalKrullDim_closure_eq_toNat_relativeDimension k sP x
    rw [hCcl] at hcnat
    rw [hcnat] at hCnum
    have hnat : d + N ≤
        (relativeDimension (fieldChowSituation k).dimensionFunction sP x).toNat + n := by
      exact_mod_cast hCnum
    have hc0 : 0 ≤ relativeDimension (fieldChowSituation k).dimensionFunction sP x :=
      relativeDimension_nonneg (fieldChowSituation k) (fun _ _ => rfl) sP x
    omega
  -- the kernel of the map of local rings lies in the local ideal of `X`
  have hyXC : y ∈ (XC : Set (projectiveSpaceOfModule k V)) :=
    hXCcl ▸ subset_closure (Set.mem_singleton y)
  have hkerle : RingHom.ker (iX.stalkMap ζ).hom ≤ TorFormula.localIdealAt y (iX.base ζ) := by
    refine ker_stalkMap_le_localIdealAt iX ζ ?_
    rw [Scheme.Hom.support_ker iX]
    exact subset_closure (hXC ▸ hyXC : y ∈ Set.range iX.base)
  -- the image `π(Z)` is closed, and is the closure of the image of the generic point
  have hZim := isClosed_image_and_topologicalKrullDim_image_le k prj
    (iX ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k ↥W)
    (by rw [hprj, Category.assoc, projection_comp_toSpec, ← Category.assoc, hj]) hZcl
  have hprjζ : closure ({prj.base ζ} : Set (projectiveSpaceOfModule k ↥W)) = prj.base '' Z := by
    refine Set.Subset.antisymm (hZim.1.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨ζ, hζmemZ, rfl⟩)) ?_
    rw [← hζZ]
    calc prj.base '' closure ({ζ} : Set X)
        ⊆ closure (prj.base '' ({ζ} : Set X)) := image_closure_subset_closure_image prj.continuous
      _ = closure ({prj.base ζ} : Set (projectiveSpaceOfModule k ↥W)) := by
            rw [Set.image_singleton]
  have hprjle := map_stalkMap_localIdealAt_projection_le k V W iX j hj hZim.1
    (hCcl.trans hCset) hprjζ
  -- the coefficient of `ξ` in the product is one
  have hone : TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP (d : ℤ)
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) ξ = 1 :=
    TorFormula.torFormulaCycleIntersectionProduct_apply_eq_one_of_etaleAt (fieldChowSituation k)
      sP hP (d : ℤ) hb N hdimP hz hzx hzy _ _ le_rfl le_rfl rfl rfl hproper iX prj rfl het
      hkerle hprjle
  have hcycmem := torFormulaCycleIntersectionProduct_single_single_mem_cyclesOfDimension
    (fieldChowSituation k) sP hP (d : ℤ) hb
  refine ⟨C, hCXproper, hone, fun p hp => ?_⟩
  -- a point of the support lies in `C ∩ X = π^{-1}(π(Z))`, and its closure has dimension `d`
  have hmemsupp := TorFormula.support_torFormulaCycleIntersectionProduct_single_single_subset
    (fieldChowSituation k) sP hP (d : ℤ) hb N hdimP hp
  have hpC : p ∈ (C : Set (projectiveSpaceOfModule k V)) := hCcl ▸ hmemsupp.1
  rw [hinterCX] at hmemsupp
  obtain ⟨w, hwmem, hwim⟩ := hmemsupp
  refine ⟨hpC, w, hwmem, hwim, ?_⟩
  rw [← hdimimg, ← iX.isClosedEmbedding.closure_image_eq, Set.image_singleton, hwim]
  exact topologicalKrullDim_closure_eq_of_relativeDimension_eq k sP
    ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) sP (d : ℤ) _).mp hcycmem _ hp)

/-- **The case `X = 𝐏(V)` of the cone of Stacks 0B0E.** If the closed subvariety `X ⊆ 𝐏(V)` has
the dimension `N` of `𝐏(V)`, then it is all of `𝐏(V)`, and a closed subvariety `Z ⊆ X` of
dimension `d` meets it properly with `Z · X = [Z]`. The coefficient of `Z` is Tag 0B1J at the
maximal ideal of the generic point of `Z`; there are no further components because each would
be a closed subvariety of `Z` of dimension `dim Z`. -/
private theorem intersectProperly_torFormulaCycleIntersectionProduct_eq_single_of_eq
    (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] [DecidableEq (projectiveSpaceOfModule k V)]
    {N d : ℕ} (hV : Module.finrank k V = N + 1)
    (ZC XC : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hdimZC : topologicalKrullDim (ZC : Set (projectiveSpaceOfModule k V)) = (d : WithBot ℕ∞))
    (hdimXC : topologicalKrullDim (XC : Set (projectiveSpaceOfModule k V)) = (N : WithBot ℕ∞)) :
    AlgebraicGeometry.IntersectProperly ZC XC ∧
      TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
          (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
          (Function.locallyFinsuppWithin.single ZC.isIrreducible.genericPoint (1 : ℤ))
          (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) =
        Function.locallyFinsuppWithin.single ZC.isIrreducible.genericPoint (1 : ℤ) := by
  classical
  set sP : projectiveSpaceOfModule k V ⟶ (fieldChowSituation k).S :=
    projectiveSpaceOfModuleToSpec k V with hsP
  set hP : IsRegular (projectiveSpaceOfModule k V) := isRegular_projectiveSpaceOfModule k V with hhP
  have hdimPeq : topologicalKrullDim (projectiveSpaceOfModule k V) = (N : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV
  have hNtop : (N : WithBot ℕ∞) < ⊤ := natCast_lt_top N
  have hdtop : (d : WithBot ℕ∞) < ⊤ := natCast_lt_top d
  have hXCuniv : (XC : Set (projectiveSpaceOfModule k V)) = Set.univ :=
    eq_univ_of_topologicalKrullDim_eq XC.isClosed' (hdimXC.trans hdimPeq.symm)
      (by rw [hdimPeq]; exact hNtop)
  set ξ := ZC.isIrreducible.genericPoint with hξdef
  set y := XC.isIrreducible.genericPoint with hydef
  have hZCcl : closure ({ξ} : Set (projectiveSpaceOfModule k V)) =
      (ZC : Set (projectiveSpaceOfModule k V)) :=
    ZC.isIrreducible.closure_genericPoint ZC.isClosed'
  have hXCcl : closure ({y} : Set (projectiveSpaceOfModule k V)) =
      (XC : Set (projectiveSpaceOfModule k V)) :=
    XC.isIrreducible.closure_genericPoint XC.isClosed'
  have hzx : ξ ∈ closure ({ξ} : Set (projectiveSpaceOfModule k V)) :=
    subset_closure (Set.mem_singleton ξ)
  have hzy : ξ ∈ closure ({y} : Set (projectiveSpaceOfModule k V)) := by
    rw [hXCcl, hXCuniv]; trivial
  have hinter : closure ({ξ} : Set (projectiveSpaceOfModule k V)) ∩
      closure ({y} : Set (projectiveSpaceOfModule k V)) =
      (ZC : Set (projectiveSpaceOfModule k V)) := by
    rw [hZCcl, hXCcl, hXCuniv, Set.inter_univ]
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k V) ≤ (N : WithBot ℕ∞) :=
    le_of_eq hdimPeq
  -- the three relative dimensions
  have hz : relativeDimension (fieldChowSituation k).dimensionFunction sP ξ = (d : ℤ) := by
    refine relativeDimension_eq_of_topologicalKrullDim_closure_eq k sP ?_
    rw [hZCcl, hdimZC]
  have hgy : relativeDimension (fieldChowSituation k).dimensionFunction sP y = (N : ℤ) := by
    refine relativeDimension_eq_of_topologicalKrullDim_closure_eq k sP ?_
    rw [hXCcl, hdimXC]
  have hgpP := relativeDimension_genericPoint_projectiveSpaceOfModule k V hV
  -- the delta-dimension bound at the pair, and the coefficient of `ξ` in the product
  have hb : TorFormula.TorSupportBound (fieldChowSituation k) sP hP (d : ℤ) ξ y := by
    refine TorFormula.torSupportBound_of_topologicalKrullDim_le k sP hP d ξ y ?_
    rw [hinter, hdimZC]
  have hproper : ringKrullDim ((projectiveSpaceOfModule k V).presheaf.stalk ξ) ≤
      ringKrullDim ((projectiveSpaceOfModule k V).presheaf.stalk ξ ⧸
          TorFormula.localIdealAt ξ ξ) +
        ringKrullDim ((projectiveSpaceOfModule k V).presheaf.stalk ξ ⧸
          TorFormula.localIdealAt y ξ) := by
    refine ringKrullDim_stalk_le_add_ringKrullDim_quotient_localIdealAt k sP hzx hzy ?_
    rw [hgpP, hz, hgy]
    omega
  have hmult : Module.length ((projectiveSpaceOfModule k V).presheaf.stalk ξ)
      ((projectiveSpaceOfModule k V).presheaf.stalk ξ ⧸
        (TorFormula.localIdealAt ξ ξ ⊔ TorFormula.localIdealAt y ξ)) = 1 :=
    TorFormula.length_quotient_eq_one_of_maximalIdeal_le
      (le_sup_of_le_left (le_of_eq (TorFormula.localIdealAt_self_eq_maximalIdeal ξ).symm))
      (TorFormula.sup_localIdealAt_ne_top hzx hzy)
  have hone : TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP (d : ℤ)
      (Function.locallyFinsuppWithin.single ξ (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) ξ = 1 :=
    TorFormula.torFormulaCycleIntersectionProduct_apply_eq_one (fieldChowSituation k) sP hP
      (d : ℤ) hb N hdimP hz hzx hzy _ _ le_rfl le_rfl hmult rfl rfl hproper
  obtain ⟨S, m, heq, hZS, hm, hsupp⟩ :=
    AlgebraicCycle.exists_finset_irreducibleCloseds_eq_single_add_sum
      (TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP (d : ℤ)
        (Function.locallyFinsuppWithin.single ξ (1 : ℤ))
        (Function.locallyFinsuppWithin.single y (1 : ℤ)))
      (TorFormula.finite_support_of_compactSpace _) ZC hone
  have hcycmem := torFormulaCycleIntersectionProduct_single_single_mem_cyclesOfDimension
    (fieldChowSituation k) sP hP (d : ℤ) hb
  -- every component of the product is a closed subvariety of `Z` of dimension `d`, hence is `Z`
  have hSempty : S = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun W hW => hZS ?_
    have hWdim : topologicalKrullDim (W : Set (projectiveSpaceOfModule k V)) =
        (d : WithBot ℕ∞) := by
      rw [← W.isIrreducible.closure_genericPoint W.isClosed']
      exact topologicalKrullDim_closure_eq_of_relativeDimension_eq k sP
        ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) sP (d : ℤ) _).mp hcycmem
          _ (hsupp W hW))
    have hWsub : (W : Set (projectiveSpaceOfModule k V)) ⊆
        (ZC : Set (projectiveSpaceOfModule k V)) := by
      have hmemsupp := TorFormula.support_torFormulaCycleIntersectionProduct_single_single_subset
        (fieldChowSituation k) sP hP (d : ℤ) hb N hdimP (hsupp W hW)
      rw [hinter] at hmemsupp
      rw [← W.isIrreducible.closure_genericPoint W.isClosed']
      exact ZC.isClosed'.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmemsupp)
    have hWeq := eq_of_subset_of_topologicalKrullDim_eq ZC.isIrreducible W.isClosed' hWsub
      (hWdim.trans hdimZC.symm) (by rw [hdimZC]; exact hdtop)
    exact IrreducibleCloseds.ext hWeq ▸ hW
  subst hSempty
  refine ⟨?_, by rw [heq, Finset.sum_empty, add_zero]⟩
  change topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
      (XC : Set (projectiveSpaceOfModule k V))) +
    topologicalKrullDim (projectiveSpaceOfModule k V) ≤
    topologicalKrullDim (ZC : Set (projectiveSpaceOfModule k V)) +
      topologicalKrullDim (XC : Set (projectiveSpaceOfModule k V))
  have hZCXC : (ZC : Set (projectiveSpaceOfModule k V)) ∩
      (XC : Set (projectiveSpaceOfModule k V)) =
      (ZC : Set (projectiveSpaceOfModule k V)) := by rw [hXCuniv, Set.inter_univ]
  rw [hZCXC, hdimPeq, hdimZC, hdimXC]

/-- **The dimension of the closure in `X` of a closed subvariety of an open subscheme.** For an
open immersion `j₀ : Y ⟶ X` and an irreducible closed `A ⊆ Y`, the closure of `j₀(A)` in `X` has
the dimension of `A`: both are read off the transcendence degree of the residue field at the
generic point, which an open immersion does not change. -/
public theorem topologicalKrullDim_closure_image_of_isOpenImmersion (k : Type u) [Field k]
    {X Y : Scheme.{u}} (q : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q]
    (j₀ : Y ⟶ X) [IsOpenImmersion j₀] {A : Set Y} (hAcl : IsClosed A) (hAirr : IsIrreducible A) :
    topologicalKrullDim ↥(closure (j₀.base '' A)) = topologicalKrullDim ↥A := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ, closure ({ζ} : Set Y) = A :=
    ⟨_, hAirr.closure_genericPoint hAcl⟩
  subst hζ
  rw [closure_image_closure j₀.continuous, Set.image_singleton,
    topologicalKrullDim_closure_eq_toNat_relativeDimension k q,
    ← relativeDimension_comp_isOpenImmersion,
    ← topologicalKrullDim_closure_eq_toNat_relativeDimension k (j₀ ≫ q)]

/-- **A closed subset of an open subscheme is the trace of its closure.** For an open immersion
`j₀ : Y ⟶ X` and a closed `A ⊆ Y`, the inverse image of the closure of `j₀(A)` is `A`. -/
public theorem preimage_closure_image_of_isOpenImmersion {X Y : Scheme.{u}} (j₀ : Y ⟶ X)
    [IsOpenImmersion j₀] {A : Set Y} (hA : IsClosed A) :
    j₀.base ⁻¹' closure (j₀.base '' A) = A := by
  rw [← j₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, hA.closure_eq]

/-- **The excess of every other component of `π^{-1}(π(Z))` drops, read in an open subset of
the nonsingular locus.** Let `X ⊆ 𝐏(V)` be a closed subvariety of dimension `n` of the projective
space of a vector space of dimension `N + 1 > n + 1` over an algebraically closed field, and let
`U ⊆ X` be an open subset contained in the nonsingular locus `X^{reg}`, given as an open immersion
`j₀ : U ⟶ X`. Let `Z ⊆ X` be a closed subvariety of dimension `d < n` meeting `U`, and let
`T i ⊆ X` be finitely many closed subsets of dimensions at most `d' i < n`. Then there is a
submodule `W ≤ V` of dimension `n + 1` whose linear subspace misses `X`, such that the projection
`π = r_W|_X : X ⟶ 𝐏(W)` is finite, étale at the generic point of `Z`, and every closed
subvariety `W' ⊆ π^{-1}(π(Z))` of dimension `d` other than `Z` satisfies, for every `i` and with
all intersections read in `U`,

* `dim (W' ∩ T i) ≤ dim (Z ∩ T i)` or `dim (W' ∩ T i) + n ≤ d + d' i`, and
* `dim (W' ∩ T i) < dim (Z ∩ T i)` when `dim (Z ∩ T i) + n ≤ d + d' i` fails.

This is the version of the key step of Tag 0B0E that Remark 0B61 asks for. The points at which
the projection is chosen étale and locally an isomorphism on `Z` are taken in `U`, where `X` is
nonsingular: a closed point of `Z ∩ U` and a closed point of each component of `Z ∩ T i ∩ U`. -/
public theorem exists_isFinite_projection_excess_clauses_of_isOpenImmersion
    (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [IsAlgClosed k]
    [FiniteDimensional k V] {N n d : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞)) (hnN : n < N) (hd : d < n)
    {Y : Scheme.{u}} (j₀ : Y ⟶ X) [IsOpenImmersion j₀] (hU : Set.range j₀.base ⊆ regularLocus X)
    (Z : Set X) (hZcl : IsClosed Z) (hZirr : IsIrreducible Z) (hZU : (j₀.base ⁻¹' Z).Nonempty)
    (hZd : topologicalKrullDim ↥Z = (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i)) {d' : ι → ℕ}
    (hd' : ∀ i, d' i < n) (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' i : WithBot ℕ∞)) :
    ∃ W : Submodule k V, Module.finrank k ↥W = n + 1 ∧
      ∃ j : X ⟶ (projectionDomain k V W).toScheme,
        j ≫ (projectionDomain k V W).ι = iX ∧
        IsFinite (j ≫ projection k V W) ∧
        EtaleAt (j ≫ projection k V W) hZirr.genericPoint ∧
        ∀ W' : Set X, IsClosed W' → IsIrreducible W' →
          W' ⊆ (j ≫ projection k V W).base ⁻¹' ((j ≫ projection k V W).base '' Z) →
          topologicalKrullDim ↥W' = (d : WithBot ℕ∞) → W' ≠ Z → ∀ i,
            (topologicalKrullDim ↥(j₀.base ⁻¹' W' ∩ j₀.base ⁻¹' T i) ≤
                topologicalKrullDim ↥(j₀.base ⁻¹' Z ∩ j₀.base ⁻¹' T i) ∨
              topologicalKrullDim ↥(j₀.base ⁻¹' W' ∩ j₀.base ⁻¹' T i) + (n : WithBot ℕ∞) ≤
                (d : WithBot ℕ∞) + (d' i : WithBot ℕ∞)) ∧
            (¬ topologicalKrullDim ↥(j₀.base ⁻¹' Z ∩ j₀.base ⁻¹' T i) + (n : WithBot ℕ∞) ≤
                (d : WithBot ℕ∞) + (d' i : WithBot ℕ∞) →
              topologicalKrullDim ↥(j₀.base ⁻¹' W' ∩ j₀.base ⁻¹' T i) <
                topologicalKrullDim ↥(j₀.base ⁻¹' Z ∩ j₀.base ⁻¹' T i)) := by
  classical
  set sX : X ⟶ (fieldChowSituation k).S := iX ≫ projectiveSpaceOfModuleToSpec k V with hsX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (j₀ ≫ sX)
  have : NoetherianSpace Y := j₀.isOpenEmbedding.isInducing.noetherianSpace
  have hdimimgU : ∀ A : Set Y,
      topologicalKrullDim ↥(j₀.base '' A) = topologicalKrullDim ↥A :=
    fun A => topologicalKrullDim_image_eq_of_isEmbedding j₀.isOpenEmbedding.isEmbedding A
  set ZU : Set Y := j₀.base ⁻¹' Z with hZUdef
  have hZUcl : IsClosed ZU := hZcl.preimage j₀.continuous
  have hTUcl : ∀ i, IsClosed (j₀.base ⁻¹' T i) := fun i => (hTcl i).preimage j₀.continuous
  -- the chosen points, all in `U`, closed in `X` and nonsingular on `X`
  obtain ⟨p₀, hp₀Z, hp₀cl⟩ := exists_isClosed_singleton_mem hZU hZUcl
  choose t htfin htsub htcl htmeet using fun i =>
    exists_finite_isClosed_forall_maximal_exists_mem (hZUcl.inter (hTUcl i))
  have : ∀ i, Finite ↥(t i) := fun i => (htfin i).to_subtype
  have hclX : ∀ u : Y, IsClosed ({u} : Set Y) →
      IsClosed ({j₀.base u} : Set X) := by
    intro u hu
    have h : u ∈ j₀.base ⁻¹' closedPoints X := by
      rw [j₀.isOpenEmbedding.preimage_closedPoints]; exact hu
    exact h
  set bU : Unit ⊕ (Σ i : ι, ↥(t i)) → Y :=
    Sum.elim (fun _ => p₀) (fun y => (y.2 : Y)) with hbUdef
  have hbUZ : ∀ s, bU s ∈ ZU := by
    rintro (s | ⟨i, y⟩)
    · exact hp₀Z
    · exact (htsub i y.2).1
  have hbUcl : ∀ s, IsClosed ({bU s} : Set Y) := by
    rintro (s | ⟨i, y⟩)
    · exact hp₀cl
    · exact htcl i _ y.2
  set b : Unit ⊕ (Σ i : ι, ↥(t i)) → X := fun s => j₀.base (bU s) with hbdef
  have hbZ : ∀ s, b s ∈ Z := fun s => hbUZ s
  have hbcl : ∀ s, IsClosed ({b s} : Set X) := fun s => hclX _ (hbUcl s)
  have hbreg : ∀ s, b s ∈ regularLocus X := fun s =>
    hU ⟨bU s, rfl⟩
  -- conditions (1), (2), (3), (4) of the source's proof at the chosen points
  obtain ⟨W, hWrank, -, j, hj, hfin, -, hetb, hsep, hFdata⟩ :=
    exists_submodule_finrank_eq_isFinite_etaleAt_projection_family k V hV iX hdimX hnN
      (α := Empty) (fun w => w.elim) (fun w => w.elim) hd Z hZcl hZirr (le_of_eq hZd)
      T hTcl hd' hTd b hbZ hbcl hbreg
  set prj : X ⟶ projectiveSpaceOfModule k ↥W := j ≫ projection k V W with hprj
  choose F hFcl hFdim hFeq using hFdata
  -- étaleness at the generic point of `Z`, from étaleness at a closed point of `Z`
  have het : EtaleAt prj hZirr.genericPoint := by
    by_contra hcon
    have hsubc : closure ({hZirr.genericPoint} : Set X) ⊆ {z : X | EtaleAt prj z}ᶜ :=
      (isOpen_setOf_etaleAt prj).isClosed_compl.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hcon)
    exact hsubc (by rw [hZirr.closure_genericPoint hZcl]; exact hbZ (Sum.inl ()))
      (hetb (Sum.inl ()))
  refine ⟨W, hWrank, j, hj, hfin, het, ?_⟩
  intro W' hW'cl hW'irr hW'sub hW'dim hW'ne i
  -- the chosen points avoid `W'`
  have hnotW' : ∀ s : Unit ⊕ (Σ i : ι, ↥(t i)), b s ∉ W' := by
    intro s hmemW'
    obtain ⟨O, hOopen, hOmem, hOsub⟩ := hsep s
    have hOW' : O ∩ W' ⊆ Z := fun z hz => hOsub ⟨hz.1, hW'sub hz.2⟩
    have hW'Z : W' ⊆ Z := by
      by_contra hcon
      obtain ⟨q₁, hq₁⟩ := Set.not_subset.mp hcon
      obtain ⟨q, hq⟩ := hW'irr.2 O Zᶜ hOopen hZcl.isOpen_compl ⟨b s, hmemW', hOmem⟩
        ⟨q₁, hq₁.1, hq₁.2⟩
      exact hq.2.2 (hOW' ⟨hq.2.1, hq.1⟩)
    exact hW'ne (eq_of_subset_of_topologicalKrullDim_eq hZirr hW'cl hW'Z (hW'dim.trans hZd.symm)
      (by rw [hZd]; exact natCast_lt_top d))
  -- condition (4), in the form the two dimension clauses need
  have hFn : topologicalKrullDim ↥(F i) + (n : WithBot ℕ∞) ≤
      (d : WithBot ℕ∞) + (d' i : WithBot ℕ∞) := by
    have h := hFdim i
    push_cast at h
    rw [← add_assoc] at h
    exact Stacks.RegularSequence.FibrewiseLocus.le_of_add_le_add_right_of_ne_bot_of_ne_top
      (by norm_num)
      (by
        intro h1; rw [← WithBot.coe_top] at h1
        exact (ENat.natCast_ne_top 1) (by exact_mod_cast h1))
      h
  -- inside `U`, `W' ∩ T i` lies in `(W' ∩ T i ∩ Z) ∪ F i`
  set A' : Set Y := j₀.base ⁻¹' W' ∩ j₀.base ⁻¹' T i with hA'def
  set A : Set Y := ZU ∩ j₀.base ⁻¹' T i with hAdef
  have hA'cl : IsClosed A' := (hW'cl.preimage j₀.continuous).inter (hTUcl i)
  have hmaxU : topologicalKrullDim ↥A' ≤
      max (topologicalKrullDim ↥(A' ∩ ZU)) (topologicalKrullDim ↥(F i)) := by
    have hsubU : A' ⊆ (A' ∩ ZU) ∪ j₀.base ⁻¹' F i := by
      rintro u ⟨huW, huT⟩
      have h1 : j₀.base u ∈ T i ∩ prj.base ⁻¹' (prj.base '' Z) := ⟨huT, hW'sub huW⟩
      rw [hFeq i] at h1
      rcases h1 with ⟨-, hZ⟩ | hF
      · exact Or.inl ⟨⟨huW, huT⟩, hZ⟩
      · exact Or.inr hF
    refine (topologicalKrullDim_le_max_of_subset_union hA'cl (hA'cl.inter hZUcl)
      ((hFcl i).preimage j₀.continuous) hsubU).trans (max_le_max ?_ ?_)
    · exact topologicalKrullDim_le_of_subset fun z hz => hz.2
    · refine (topologicalKrullDim_le_of_subset Set.inter_subset_right).trans ?_
      rw [← hdimimgU]
      exact topologicalKrullDim_le_of_subset (Set.image_preimage_subset _ _)
  refine ⟨?_, fun hns => ?_⟩
  · rcases le_max_iff.mp hmaxU with h | h
    · exact Or.inl (h.trans (topologicalKrullDim_le_of_subset fun z hz => ⟨hz.2, hz.1.2⟩))
    · exact Or.inr ((add_le_add h le_rfl).trans hFn)
  · have hlt : (d : WithBot ℕ∞) + (d' i : WithBot ℕ∞) <
        topologicalKrullDim ↥A + (n : WithBot ℕ∞) := lt_of_not_ge hns
    have hAne : A.Nonempty := by
      rcases Set.eq_empty_or_nonempty A with hempty | hne
      · have hbot : topologicalKrullDim ↥A = ⊥ := by
          have : IsEmpty ↥A := ⟨fun z => (hempty ▸ z.2 : (z : Y) ∈ (∅ : Set _))⟩
          exact (topologicalKrullDim_eq_bot_iff_isEmpty _).mpr inferInstance
        rw [hbot, WithBot.bot_add] at hlt
        exact absurd hlt not_lt_bot
      · exact hne
    have hFlt : topologicalKrullDim ↥(F i) < topologicalKrullDim ↥A := by
      by_contra hcon
      exact absurd ((add_le_add (not_lt.mp hcon) (le_refl (n : WithBot ℕ∞))).trans hFn)
        (not_le.mpr hlt)
    have hAfin : topologicalKrullDim ↥A < ⊤ := by
      refine lt_of_le_of_lt (topologicalKrullDim_le_of_subset Set.inter_subset_left) ?_
      rw [← hdimimgU]
      refine lt_of_le_of_lt (topologicalKrullDim_le_of_subset (Set.image_preimage_subset _ _)) ?_
      rw [hZd]; exact natCast_lt_top d
    have hstrictcore : topologicalKrullDim ↥(A' ∩ ZU) < topologicalKrullDim ↥A := by
      refine topologicalKrullDim_lt_of_forall_notMem (x := fun u : ↥(t i) => (u : Y))
        (hZUcl.inter (hTUcl i)) (hA'cl.inter hZUcl) (fun z hz => ⟨hz.2, hz.1.2⟩) hAne hAfin ?_ ?_
      · intro B hBcl hBirr hBS hBmax
        obtain ⟨u, hu, huB⟩ := htmeet i B hBcl hBirr hBS hBmax
        exact ⟨⟨u, hu⟩, huB⟩
      · intro u hmem
        exact hnotW' (Sum.inr ⟨i, u⟩) hmem.1.1
    exact lt_of_le_of_lt hmaxU (max_lt hstrictcore hFlt)

/-- **Stacks Project, Remark 0B61: the moving lemma on an open subset of the nonsingular locus.**
Let `X ⊆ 𝐏(V)` be a closed subvariety of dimension `n` of the projective space of a vector space
of dimension `N + 1` over an algebraically closed field, let `U ⊆ X` be an open subscheme
contained in the nonsingular locus `X^{reg}`, given as an open immersion `j₀ : U ⟶ X` (written
`Y ⟶ X` below), let `Z ⊆ U` be a closed subvariety of dimension `d < n`, and
let `T_i ⊆ U` be finitely many closed subvarieties, `T_i` of dimension `d' i < n`. Then there is
a closed subvariety `C ⊆ 𝐏(V)` whose prime cycle intersects that of `X` properly, with

`(C · X)|_U = [Z] + ∑ m_j [Z_j]`

in the Tor-formula intersection product of Section 0B08, where `C · X` is supported on `C ∩ X`,
the `Z_j ⊆ U` are irreducible closed of dimension `d`, distinct from `Z`, with nonzero
multiplicities, and where, inside `U`,

* `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` or `dim (Z_j ∩ T_i) + n ≤ d + d' i`, and
* `dim (Z_j ∩ T_i) < dim (Z ∩ T_i)` whenever `Z` does not intersect `T_i` properly in `U`.

The restriction of `C · X` to `U` is its coefficientwise inverse image `Stacks.Chow.cycleComap`
along `U ⟶ X ⟶ 𝐏(V)`. `U = X^{reg}` is the statement of Remark 0B61, `U` a quasi-projective
variety embedded in a closed subvariety `X` of `𝐏(V)` is the form the remark's 0B1U and 0B1V use,
and `j₀ = 𝟙 X` for a nonsingular `X` is Lemma 0B0E; the dimensions `d' i` may vary with `i`, the
source's single `d'` being the constant family.

**The first clause departs from the source's text, because the source's clause is false.** The
source asks for `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` outright. When `Z ∩ T_i = ∅` this demands
`Z_j ∩ T_i = ∅` for every `j`, and that fails already for the projective Lemma 0B0E, where
`U = X = X^{reg}`. Take `X ⊆ 𝐏^3` a nonsingular quadric surface (`n = 2`) and `Z`, `T_1` two
distinct lines of one ruling (`d = d' = 1`), so that `Z ∩ T_1 = ∅`. A `C` as in the conclusion
must be a surface: if `dim C ≤ 1` then `C ∩ X` is finite and `Z` does not occur in `C · X`, and
if `C = 𝐏^3` then `C · X` has no component of dimension `1`. A surface `C` meets the line `T_1`,
and every component of `C ∩ X` through such a point has dimension exactly `1`, so it occurs in
`C · X` with a positive multiplicity and meets `T_1`; it is neither `Z` nor any admissible
`Z_j`. The argument is written out in full in the implementation notes of this module. The
disjunction is what condition (4) of the source's proof gives, and its first disjunct is the
source's inequality whenever `Z ∩ T_i` is nonempty, by Tag 0AZP; in the empty case the second
disjunct `dim (Z_j ∩ T_i) + n ≤ d + d' i` is what holds. The second clause is as the source has
it, and is vacuous exactly in the empty case. -/
@[stacks 0B61 "the variant of the moving lemma 0B0E stated there, for an arbitrary open subscheme \
U ⟶ X of the nonsingular locus of a closed subvariety X ⊆ 𝐏(V) (the source's U = X^reg), with the \
dimensions of the T_i allowed to vary; (C · X)|_U is the coefficientwise inverse image of the \
cycle C · X along U ⟶ X ⟶ 𝐏(V); the non-strict dimension clause is the disjunction \
dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i) or dim (Z_j ∩ T_i) + n ≤ d + d', as for 0B0E, because the \
source's inequality fails when Z ∩ T_i is empty"]
public theorem exists_intersectProperly_cycleComap_torFormulaCycleIntersectionProduct_eq
    (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] [DecidableEq (projectiveSpaceOfModule k V)]
    {N n d : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞)) (hd : d < n)
    {Y : Scheme.{u}} (j₀ : Y ⟶ X) [IsOpenImmersion j₀] (hU : Set.range j₀.base ⊆ regularLocus X)
    [DecidableEq Y]
    (Z : IrreducibleCloseds Y)
    (hZd : topologicalKrullDim (Z : Set Y) = (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → IrreducibleCloseds Y) {d' : ι → ℕ}
    (hd' : ∀ i, d' i < n)
    (hTd : ∀ i, topologicalKrullDim (T i : Set Y) = (d' i : WithBot ℕ∞))
    (XC : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hXC : (XC : Set (projectiveSpaceOfModule k V)) = Set.range iX.base) :
    ∃ (C : IrreducibleCloseds (projectiveSpaceOfModule k V))
      (S : Finset (IrreducibleCloseds Y)) (m : IrreducibleCloseds Y → ℤ),
      AlgebraicCycle.IntersectProperly
          (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
          (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) ∧
        cycleComap j₀ j₀.isOpenEmbedding.injective
            (cycleComap iX iX.isClosedEmbedding.injective
              (TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
                (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V)
                (d : ℤ)
                (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
                (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)))) =
          Function.locallyFinsuppWithin.single Z.isIrreducible.genericPoint (1 : ℤ) +
            ∑ W ∈ S, m W • Function.locallyFinsuppWithin.single
              W.isIrreducible.genericPoint (1 : ℤ) ∧
        (∀ p : projectiveSpaceOfModule k V,
          TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
              (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
              (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
              (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) p ≠
              0 →
            p ∈ (C : Set (projectiveSpaceOfModule k V)) ∩
              (XC : Set (projectiveSpaceOfModule k V))) ∧
        Z ∉ S ∧ (∀ W ∈ S, m W ≠ 0) ∧
        (∀ W ∈ S, topologicalKrullDim (W : Set Y) = (d : WithBot ℕ∞)) ∧
        (∀ W ∈ S, ∀ i,
          topologicalKrullDim ↥((W : Set Y) ∩ (T i : Set Y)) ≤
              topologicalKrullDim ↥((Z : Set Y) ∩ (T i : Set Y)) ∨
            topologicalKrullDim ↥((W : Set Y) ∩ (T i : Set Y)) +
                (n : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) + (d' i : WithBot ℕ∞)) ∧
        (∀ W ∈ S, ∀ i, ¬ AlgebraicGeometry.IntersectProperly Z (T i) →
          topologicalKrullDim ↥((W : Set Y) ∩ (T i : Set Y)) <
            topologicalKrullDim ↥((Z : Set Y) ∩ (T i : Set Y))) := by
  classical
  set sX : X ⟶ (fieldChowSituation k).S := iX ≫ projectiveSpaceOfModuleToSpec k V with hsX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : IsIntegral X := inferInstance
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (j₀ ≫ sX)
  have : NoetherianSpace Y := j₀.isOpenEmbedding.isInducing.noetherianSpace
  have hdimimg : ∀ A : Set X, topologicalKrullDim ↥(iX.base '' A) = topologicalKrullDim ↥A :=
    fun A => topologicalKrullDim_image_eq_of_isEmbedding iX.isClosedEmbedding.isEmbedding A
  have hdimimgU : ∀ A : Set Y,
      topologicalKrullDim ↥(j₀.base '' A) = topologicalKrullDim ↥A :=
    fun A => topologicalKrullDim_image_eq_of_isEmbedding j₀.isOpenEmbedding.isEmbedding A
  have hinj : Function.Injective iX.base := iX.isClosedEmbedding.injective
  have hinjU : Function.Injective j₀.base := j₀.isOpenEmbedding.injective
  -- the closures in `X` of `Z` and of the `T i`
  set Zb : Set X := closure (j₀.base '' (Z : Set Y)) with hZbdef
  have hZbcl : IsClosed Zb := isClosed_closure
  have hZbirr : IsIrreducible Zb :=
    (Z.isIrreducible.image _ j₀.continuous.continuousOn).closure
  have hZbd : topologicalKrullDim ↥Zb = (d : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_image_of_isOpenImmersion k sX j₀ Z.isClosed Z.isIrreducible,
      hZd]
  have hZbpre : j₀.base ⁻¹' Zb = Z := preimage_closure_image_of_isOpenImmersion j₀ Z.isClosed
  set Tb : ι → Set X := fun i => closure (j₀.base '' (T i : Set Y)) with hTbdef
  have hTbcl : ∀ i, IsClosed (Tb i) := fun i => isClosed_closure
  have hTbd : ∀ i, topologicalKrullDim ↥(Tb i) = (d' i : WithBot ℕ∞) := fun i => by
    rw [topologicalKrullDim_closure_image_of_isOpenImmersion k sX j₀ (T i).isClosed
      (T i).isIrreducible, hTd i]
  have hTbpre : ∀ i, j₀.base ⁻¹' Tb i = T i := fun i =>
    preimage_closure_image_of_isOpenImmersion j₀ (T i).isClosed
  -- the generic point of `Zb` is that of `Z`
  set ζU := Z.isIrreducible.genericPoint with hζUdef
  have hζUcl : closure ({ζU} : Set Y) = Z :=
    Z.isIrreducible.closure_genericPoint Z.isClosed
  have hZbgen : hZbirr.genericPoint = j₀.base ζU := by
    refine (hZbirr.isGenericPoint_genericPoint hZbcl).eq ?_
    change closure ({j₀.base ζU} : Set X) = Zb
    rw [hZbdef, ← hζUcl, closure_image_closure j₀.continuous, Set.image_singleton]
  -- `Y` has the dimension `n` of `X`
  obtain ⟨z₀, -⟩ := Z.isIrreducible.nonempty
  have hUne : (Set.range j₀.base).Nonempty := ⟨j₀.base z₀, z₀, rfl⟩
  have hdimU : topologicalKrullDim Y = (n : WithBot ℕ∞) := by
    have hdense : closure (j₀.base '' (Set.univ : Set Y)) = Set.univ := by
      rw [Set.image_univ]
      exact (j₀.isOpenEmbedding.isOpen_range.dense hUne).closure_eq
    have : IrreducibleSpace Y := (irreducibleSpace_def Y).mpr
      ⟨⟨z₀, trivial⟩, by
        simpa using (IrreducibleSpace.isIrreducible_univ X).2.preimage j₀.isOpenEmbedding⟩
    have h := topologicalKrullDim_closure_image_of_isOpenImmersion k sX j₀ isClosed_univ
      (IrreducibleSpace.isIrreducible_univ _)
    rw [hdense] at h
    rw [← topologicalKrullDim_univ, ← h, topologicalKrullDim_univ, hdimX]
  -- `dim X ≤ N`, because `X` is a closed subscheme of `𝐏(V)`
  have hdimPeq : topologicalKrullDim (projectiveSpaceOfModule k V) = (N : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV
  have hdimXC : topologicalKrullDim (XC : Set (projectiveSpaceOfModule k V)) =
      (n : WithBot ℕ∞) := by
    rw [hXC, topologicalKrullDim_range_eq iX, hdimX]
  have hnleN : n ≤ N := by
    have hle : topologicalKrullDim (XC : Set (projectiveSpaceOfModule k V)) ≤
        topologicalKrullDim (projectiveSpaceOfModule k V) :=
      Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le
    rw [hdimXC, hdimPeq] at hle
    exact_mod_cast hle
  by_cases hnN : n < N
  -- `n = N`: `X` is all of `𝐏(V)`, and `C` is the closure of `Z` with no further component
  case neg =>
    have hnNeq : n = N := le_antisymm hnleN (by omega)
    subst hnNeq
    let ZC : IrreducibleCloseds (projectiveSpaceOfModule k V) :=
      ⟨iX.base '' Zb, hZbirr.image _ iX.continuous.continuousOn,
        iX.isClosedEmbedding.isClosedMap _ hZbcl⟩
    have hdimZC : topologicalKrullDim (ZC : Set (projectiveSpaceOfModule k V)) =
        (d : WithBot ℕ∞) := by
      change topologicalKrullDim ↥(iX.base '' Zb) = (d : WithBot ℕ∞)
      rw [hdimimg, hZbd]
    obtain ⟨hprop, hprodeq⟩ :=
      intersectProperly_torFormulaCycleIntersectionProduct_eq_single_of_eq k V hV ZC XC hdimZC
        hdimXC
    have hZCgen : ZC.isIrreducible.genericPoint = iX.base (j₀.base ζU) := by
      refine (ZC.isIrreducible.isGenericPoint_genericPoint ZC.isClosed').eq ?_
      change closure ({iX.base (j₀.base ζU)} : Set (projectiveSpaceOfModule k V)) = iX.base '' Zb
      rw [← hZbgen, ← Set.image_singleton, iX.isClosedEmbedding.closure_image_eq,
        hZbirr.closure_genericPoint hZbcl]
    refine ⟨ZC, ∅, 0, AlgebraicCycle.intersectProperly_single_genericPoint hprop, ?_,
      fun p hp => ?_, by simp, by simp, by simp, by simp, by simp⟩
    swap
    · rw [hprodeq, Function.locallyFinsuppWithin.single_apply] at hp
      have hpeq : p = ZC.isIrreducible.genericPoint := by by_contra h; exact hp (ite_eq_right h)
      rw [hpeq]
      refine ⟨(ZC.isIrreducible.isGenericPoint_genericPoint ZC.isClosed').mem, ?_⟩
      rw [hXC, hZCgen]
      exact ⟨_, rfl⟩
    rw [hprodeq, Finset.sum_empty, add_zero]
    refine Function.locallyFinsuppWithin.ext fun u => ?_
    rw [cycleComap_apply, cycleComap_apply, Function.locallyFinsuppWithin.single_apply,
      Function.locallyFinsuppWithin.single_apply, hZCgen]
    by_cases hu : u = ζU
    · rw [ite_eq_left hu, ite_eq_left (by rw [hu])]
    · rw [ite_eq_right hu, ite_eq_right fun h => hu (hinjU (hinj h))]
  -- `n < N`: a projection finite on `X`, étale at the generic point of `Zb`, along which every
  -- other closed subvariety of `π^{-1}(π(Zb))` of dimension `d` has the excess bounds in `U`
  obtain ⟨W, hWrank, j, hj, hfin, het, hexcess⟩ :=
    exists_isFinite_projection_excess_clauses_of_isOpenImmersion k V hV iX hdimX hnN hd j₀
      hU Zb hZbcl hZbirr
      (by rw [hZbpre]; exact Z.isIrreducible.nonempty) hZbd Tb hTbcl hd'
      (fun i => le_of_eq (hTbd i))
  have := hfin
  have : Nontrivial ↥W := Module.nontrivial_of_finrank_pos (R := k) (by rw [hWrank]; omega)
  set prj : X ⟶ projectiveSpaceOfModule k ↥W := j ≫ projection k V W with hprj
  -- the subvariety `C`, the coefficient one at `Z`, and the support of `C · X`
  obtain ⟨C, hCXproper, hone, hsuppX⟩ :=
    exists_intersectProperly_torFormulaCycleIntersectionProduct_apply_eq_one_of_isFinite k V hV
      iX hdimX hnN W hWrank j hj Zb hZbcl hZbirr hZbd het XC hXC
  rw [hZbgen] at hone
  set E : Set X := prj.base ⁻¹' (prj.base '' Zb) with hEdef
  have hZim := isClosed_image_and_topologicalKrullDim_image_le k prj
    (iX ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k ↥W)
    (by rw [hprj, Category.assoc, projection_comp_toSpec, ← Category.assoc, hj]) hZbcl
  have hEcl : IsClosed E := hZim.1.preimage prj.continuous
  -- the restriction of `C · X` to `U`
  set α : AlgebraicCycle Y ℤ := cycleComap j₀ hinjU (cycleComap iX hinj
    (TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
      (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
      (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
      (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)))) with hαdef
  have hαfin : (Function.support α).Finite :=
    (TorFormula.finite_support_of_compactSpace _).preimage (hinj.comp hinjU).injOn
  obtain ⟨S, m, heq, hZS, hm, hsupp⟩ :=
    AlgebraicCycle.exists_finset_irreducibleCloseds_eq_single_add_sum α hαfin Z hone
  -- every component of the restriction is the trace of a closed subvariety of `X` inside
  -- `π^{-1}(π(Zb))`, of dimension `d` and other than `Zb`
  have hWdata : ∀ V' ∈ S, IsClosed (closure (j₀.base '' (V' : Set Y))) ∧
      IsIrreducible (closure (j₀.base '' (V' : Set Y))) ∧
      closure (j₀.base '' (V' : Set Y)) ⊆ E ∧
      topologicalKrullDim ↥(closure (j₀.base '' (V' : Set Y))) = (d : WithBot ℕ∞) ∧
      closure (j₀.base '' (V' : Set Y)) ≠ Zb := by
    intro V' hV'
    obtain ⟨-, w₀, hw₀E, hw₀eq, hw₀dim⟩ := hsuppX _ (hsupp V' hV')
    have hw₀ : w₀ = j₀.base V'.isIrreducible.genericPoint := hinj hw₀eq
    have hcl : closure (j₀.base '' (V' : Set Y)) = closure ({w₀} : Set X) := by
      have h := closure_image_closure (f := j₀.base) j₀.continuous
        (s := {V'.isIrreducible.genericPoint})
      rw [Set.image_singleton, V'.isIrreducible.closure_genericPoint V'.isClosed'] at h
      rw [hw₀]
      exact h
    refine ⟨isClosed_closure, (V'.isIrreducible.image _ j₀.continuous.continuousOn).closure,
      ?_, ?_, ?_⟩
    · rw [hcl]; exact hEcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hw₀E)
    · rw [hcl]; exact hw₀dim
    · intro hcon
      refine hZS ?_
      have hV'Z : V' = Z := IrreducibleCloseds.ext (by
        rw [← preimage_closure_image_of_isOpenImmersion j₀ V'.isClosed, hcon, hZbpre])
      exact hV'Z ▸ hV'
  have hWdim : ∀ V' ∈ S, topologicalKrullDim (V' : Set Y) = (d : WithBot ℕ∞) :=
    fun V' hV' => by
      rw [← topologicalKrullDim_closure_image_of_isOpenImmersion k sX j₀ V'.isClosed
        V'.isIrreducible]
      exact (hWdata V' hV').2.2.2.1
  refine ⟨C, S, m, AlgebraicCycle.intersectProperly_single_genericPoint hCXproper, heq,
    fun p hp => ?_, hZS, hm, hWdim, fun V' hV' i => ?_, fun V' hV' i hns => ?_⟩
  · obtain ⟨hpC, w, -, hw, -⟩ := hsuppX p hp
    exact ⟨hpC, hXC ▸ ⟨w, hw⟩⟩
  all_goals
    obtain ⟨hW'cl, hW'irr, hW'E, hW'dim, hW'ne⟩ := hWdata V' hV'
    have h := hexcess _ hW'cl hW'irr hW'E hW'dim hW'ne i
    rw [preimage_closure_image_of_isOpenImmersion j₀ V'.isClosed, hZbpre, hTbpre i] at h
  · exact h.1
  · refine h.2 fun hle => hns ?_
    rw [AlgebraicGeometry.intersectProperly_iff, hdimU, hZd, hTd i]
    exact hle

/-- **Stacks Project, Tag 0B0E.** Let `X ⊆ 𝐏(V)` be a nonsingular closed subvariety of dimension
`n` of the projective space of a vector space of dimension `N + 1` over an algebraically closed
field; let `Z ⊆ X` be a closed subvariety of dimension `d < n`, and let `T_i ⊆ X` be finitely
many closed subvarieties of dimension `d' < n`. Then there is a closed subvariety `C ⊆ 𝐏(V)`
whose prime cycle intersects that of `X` properly, with

`C · X = [Z] + ∑ m_j [Z_j]`

in the Tor-formula intersection product of Section 0B08, where the `Z_j ⊆ X` are irreducible
closed of dimension `d`, distinct from `Z`, with nonzero multiplicities, and where

* `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` or `dim (Z_j ∩ T_i) + n ≤ d + d'`, and
* `dim (Z_j ∩ T_i) < dim (Z ∩ T_i)` whenever `Z` does not intersect `T_i` properly inside `X`.

The first clause is the disjunction that condition (4) of the source's proof yields; its first
disjunct is the source's own inequality, which Tag 0AZP supplies from the second whenever
`Z ∩ T_i` is nonempty, and which alone would be false in the bottom case `Z ∩ T_i = ∅` — see the
quadric-surface counterexample in the implementation notes of this module. The second clause is
vacuous exactly on that bottom case and needs no guard. -/
@[stacks 0B0E "the whole lemma. `X ⊂ 𝐏^N` is read as `⊆`, so `dim X = N` is covered: there `X` \
is the whole of `𝐏(V)` and the conclusion holds with `C = Z` and an empty family of `Z_j`, which \
is the empty case of the source's chain of projections. The non-strict dimension clause is \
registered in the disjunctive form `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i) ∨ dim (Z_j ∩ T_i) + n ≤ d + \
d'` — written additively because `WithBot ℕ∞` has no subtraction — which is what condition (4) \
of the source's proof yields and which implies the source's own first inequality wherever Tag \
0AZP makes it true, namely whenever `Z ∩ T_i` is nonempty; in the bottom case `Z ∩ T_i = ∅` the \
source's first inequality is refuted by a nonsingular quadric surface in 𝐏^3 with Z and T_1 two \
distinct lines of one ruling, written out in this module's implementation notes, and the second \
disjunct is what holds there. The strict clause is as the source has it, and is vacuous exactly \
on that bottom case"]
public theorem exists_intersectProperly_torFormulaCycleIntersectionProduct_eq
    (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] [DecidableEq (projectiveSpaceOfModule k V)]
    {N n d d' : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)] (hXreg : IsRegular X)
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞))
    (hd : d < n) (hd' : d' < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZirr : IsIrreducible Z)
    (hZd : topologicalKrullDim ↥Z = (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    (hTirr : ∀ i, IsIrreducible (T i))
    (hTd : ∀ i, topologicalKrullDim ↥(T i) = (d' : WithBot ℕ∞))
    (XC ZC : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (TC : ι → IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hXC : (XC : Set (projectiveSpaceOfModule k V)) = Set.range iX.base)
    (hZC : (ZC : Set (projectiveSpaceOfModule k V)) = iX.base '' Z)
    (hTC : ∀ i, (TC i : Set (projectiveSpaceOfModule k V)) = iX.base '' (T i)) :
    ∃ (C : IrreducibleCloseds (projectiveSpaceOfModule k V))
      (S : Finset (IrreducibleCloseds (projectiveSpaceOfModule k V)))
      (m : IrreducibleCloseds (projectiveSpaceOfModule k V) → ℤ),
      AlgebraicCycle.IntersectProperly
          (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
          (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) ∧
        TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
            (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
            (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
            (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) =
          Function.locallyFinsuppWithin.single ZC.isIrreducible.genericPoint (1 : ℤ) +
            ∑ W ∈ S, m W • Function.locallyFinsuppWithin.single
              W.isIrreducible.genericPoint (1 : ℤ) ∧
        ZC ∉ S ∧ (∀ W ∈ S, m W ≠ 0) ∧
        (∀ W ∈ S, (W : Set (projectiveSpaceOfModule k V)) ⊆
          (XC : Set (projectiveSpaceOfModule k V))) ∧
        (∀ W ∈ S, topologicalKrullDim (W : Set (projectiveSpaceOfModule k V)) =
          (d : WithBot ℕ∞)) ∧
        (∀ W ∈ S, ∀ i,
          topologicalKrullDim ↥((W : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V))) ≤
              topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V))) ∨
            topologicalKrullDim ↥((W : Set (projectiveSpaceOfModule k V)) ∩
                  (TC i : Set (projectiveSpaceOfModule k V))) + (n : WithBot ℕ∞) ≤
              (d : WithBot ℕ∞) + (d' : WithBot ℕ∞)) ∧
        (∀ W ∈ S, ∀ i,
          ¬ (topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
                  (TC i : Set (projectiveSpaceOfModule k V))) +
                topologicalKrullDim (XC : Set (projectiveSpaceOfModule k V)) ≤
              topologicalKrullDim (ZC : Set (projectiveSpaceOfModule k V)) +
                topologicalKrullDim (TC i : Set (projectiveSpaceOfModule k V))) →
            topologicalKrullDim ↥((W : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V))) <
              topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V)))) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (iX ≫ projectiveSpaceOfModuleToSpec k V)
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (iX ≫ projectiveSpaceOfModuleToSpec k V)
  have hXstalk : IsLocallyNoetherian X ∧ ∀ z : X, IsRegularLocalRing (X.presheaf.stalk z) :=
    ((isRegular_tfae X).out 1 2).mp hXreg
  have hXregpt : ∀ z : X, z ∈ regularLocus X := hXstalk.2
  have hdimimg : ∀ A : Set X, topologicalKrullDim ↥(iX.base '' A) = topologicalKrullDim ↥A :=
    fun A => topologicalKrullDim_image_eq_of_isEmbedding iX.isClosedEmbedding.isEmbedding A
  have hinj : Function.Injective iX.base := iX.isClosedEmbedding.injective
  -- `X` is an open subscheme of itself inside its nonsingular locus
  set Z' : IrreducibleCloseds X := ⟨Z, hZirr, hZcl⟩ with hZ'def
  set T' : ι → IrreducibleCloseds X := fun i => ⟨T i, hTirr i, hTcl i⟩ with hT'def
  obtain ⟨C, S, m, hCX, hdisp, hsuppCX, hZS, -, hWd, hle, hlt⟩ :=
    exists_intersectProperly_cycleComap_torFormulaCycleIntersectionProduct_eq k V hV iX hdimX hd
      (𝟙 X) (fun z _ => hXregpt z) Z' hZd T' (fun _ => hd') hTd XC hXC
  -- the closed subvarieties of `X` and their images in `𝐏(V)`
  have hclosure : ∀ A : IrreducibleCloseds X,
      closure ({iX.base A.isIrreducible.genericPoint} : Set (projectiveSpaceOfModule k V)) =
        iX.base '' (A : Set X) := by
    intro A
    rw [← Set.image_singleton, iX.isClosedEmbedding.closure_image_eq,
      A.isIrreducible.closure_genericPoint A.isClosed']
  have hgen : ∀ (A : IrreducibleCloseds X)
      (AC : IrreducibleCloseds (projectiveSpaceOfModule k V)),
      (AC : Set (projectiveSpaceOfModule k V)) = iX.base '' (A : Set X) →
      AC.isIrreducible.genericPoint = iX.base A.isIrreducible.genericPoint := by
    intro A AC hAC
    refine (AC.isIrreducible.isGenericPoint_genericPoint AC.isClosed').eq ?_
    change closure ({iX.base A.isIrreducible.genericPoint} :
      Set (projectiveSpaceOfModule k V)) = AC
    rw [hclosure, hAC]
  have hZCgen := hgen Z' ZC hZC
  have hgpinj : ∀ A B : IrreducibleCloseds X,
      A.isIrreducible.genericPoint = B.isIrreducible.genericPoint → A = B := fun A B h => by
    rw [← AlgebraicCycle.closureSingleton_genericPoint A,
      ← AlgebraicCycle.closureSingleton_genericPoint B, h]
  -- the coefficients of `C · X` at the points of `X`, read off the display
  have heval : ∀ u : X,
      TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
          (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
          (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
          (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ))
          (iX.base u) =
        (if u = Z'.isIrreducible.genericPoint then 1 else 0) +
          ∑ W ∈ S, if u = W.isIrreducible.genericPoint then m W else 0 := by
    intro u
    have h := congrArg (fun c : AlgebraicCycle X ℤ => c u) hdisp
    simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
      Function.locallyFinsuppWithin.coe_single, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h
    exact h
  have hone : TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
      (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
      (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
      (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ))
      ZC.isIrreducible.genericPoint = 1 := by
    rw [hZCgen, heval, ite_eq_left rfl, Finset.sum_eq_zero fun W hW => by
      rw [ite_eq_right]
      intro h
      exact hZS (hgpinj W Z' h.symm ▸ hW), add_zero]
  obtain ⟨SP, mP, heqP, hZSP, hmP, hsuppP⟩ :=
    AlgebraicCycle.exists_finset_irreducibleCloseds_eq_single_add_sum _
      (TorFormula.finite_support_of_compactSpace _) ZC hone
  -- every component of the product is the image of one of the components on `X`
  have hcomp : ∀ W' ∈ SP, ∃ W ∈ S, (W' : Set (projectiveSpaceOfModule k V)) =
      iX.base '' (W : Set X) := by
    intro W' hW'
    have hp := hsuppP W' hW'
    obtain ⟨-, hpXC⟩ := hsuppCX _ hp
    rw [hXC] at hpXC
    obtain ⟨u, hu⟩ := hpXC
    rw [Function.mem_support, ← hu, heval] at hp
    by_cases hu' : u = Z'.isIrreducible.genericPoint
    · refine absurd ?_ hZSP
      have hW'Z : W' = ZC := by
        rw [← AlgebraicCycle.closureSingleton_genericPoint W',
          ← AlgebraicCycle.closureSingleton_genericPoint ZC, hZCgen, ← hu, hu']
      exact hW'Z ▸ hW'
    · rw [ite_eq_right hu', zero_add] at hp
      obtain ⟨W, hW, hWne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
      have huW : u = W.isIrreducible.genericPoint := by by_contra h; exact hWne (ite_eq_right h)
      refine ⟨W, hW, ?_⟩
      rw [← W'.isIrreducible.closure_genericPoint W'.isClosed', ← hu, huW, hclosure]
  have hinter : ∀ (A : IrreducibleCloseds X) (i : ι),
      iX.base '' (A : Set X) ∩ (TC i : Set (projectiveSpaceOfModule k V)) =
        iX.base '' ((A : Set X) ∩ (T' i : Set X)) := by
    intro A i
    rw [hTC i, ← Set.image_inter hinj]
    rfl
  have hdimZT : ∀ i, topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
      (TC i : Set (projectiveSpaceOfModule k V))) =
      topologicalKrullDim ↥((Z' : Set X) ∩ (T' i : Set X)) := fun i => by
    rw [show (ZC : Set (projectiveSpaceOfModule k V)) = iX.base '' (Z' : Set X) from hZC,
      hinter, hdimimg]
  have hdimXC : topologicalKrullDim (XC : Set (projectiveSpaceOfModule k V)) =
      (n : WithBot ℕ∞) := by
    rw [hXC, topologicalKrullDim_range_eq iX, hdimX]
  have hdimZC : topologicalKrullDim (ZC : Set (projectiveSpaceOfModule k V)) =
      (d : WithBot ℕ∞) := by rw [hZC, hdimimg]; exact hZd
  have hdimTC : ∀ i, topologicalKrullDim (TC i : Set (projectiveSpaceOfModule k V)) =
      (d' : WithBot ℕ∞) := fun i => by rw [hTC i, hdimimg]; exact hTd i
  refine ⟨C, SP, mP, hCX, heqP, hZSP, hmP, ?_, ?_, ?_, ?_⟩
  · intro W' hW'
    obtain ⟨W, -, hW'eq⟩ := hcomp W' hW'
    rw [hW'eq, hXC]
    exact Set.image_subset_range _ _
  · intro W' hW'
    obtain ⟨W, hW, hW'eq⟩ := hcomp W' hW'
    rw [hW'eq, hdimimg, hWd W hW]
  · intro W' hW' i
    obtain ⟨W, hW, hW'eq⟩ := hcomp W' hW'
    rw [hW'eq, hinter, hdimimg, hdimZT]
    exact hle W hW i
  · intro W' hW' i hns
    obtain ⟨W, hW, hW'eq⟩ := hcomp W' hW'
    rw [hW'eq, hinter, hdimimg, hdimZT]
    refine hlt W hW i ?_
    have hZ'd : topologicalKrullDim (Z' : Set X) = (d : WithBot ℕ∞) := hZd
    have hT'd : topologicalKrullDim (T' i : Set X) = (d' : WithBot ℕ∞) := hTd i
    rw [AlgebraicGeometry.intersectProperly_iff, hdimX, hZ'd, hT'd]
    rwa [hdimZT, hdimXC, hdimZC, hdimTC i] at hns

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
