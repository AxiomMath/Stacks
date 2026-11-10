module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraicSpaceCoproductFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingStratumFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism

/-!
# Finite presentation of `X' = ∐_{r ≥ 0} X_r ⟶ X`

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `G` be a
quasi-coherent `𝒪_X`-module of finite presentation and let `X ⊇ Z_0 ⊇ Z_1 ⊇ …` be the chain of
closed subspaces cut out by the Fitting ideal sheaves of `G`, with strata
`X_r = Z_{r-1} ∖ Z_r`.  Stacks 0CZA asserts that the disjoint union `X' = ∐_{r ≥ 0} X_r` is of
finite presentation over `X`.

This does **not** follow from finite presentation of the individual strata, which is
`AlgebraicGeometry.Space.isFinitePresentation_ι_fittingRankStratum`: an infinite coproduct of
quasi-compact morphisms need not be quasi-compact.  The extra content is that over an affine
test object only finitely many strata survive, and that is what this file proves: the sections
of `G_T` over the identity chart of an affine `T ⟶ X` are a finite module, so they are spanned
by `N` of them for some `N`, and clause (2) of Stacks 0CZ9 then says that `T` lands in the open
complement `X ∖ Z_N`; every stratum `X_n` with `n > N` lies in `Z_{n-1} ⊆ Z_N`, so its base
change to `T` has no points at all.

## Main results

* `AlgebraicGeometry.Space.exists_range_le_openComplement_fittingClosedSubspace_of_isAffine`:
  an affine test object `T ⟶ X` lands in `X ∖ Z_N` for some `N`.
* `AlgebraicGeometry.Space.preimage_range_pointsMap_fittingRankStratum_eq_empty`: such a `T`
  misses the point set of every stratum `X_n` with `n > N`.
* `AlgebraicGeometry.Space.isFinitePresentation_fittingRankStratificationHom`: **the finite
  presentation of `X' ⟶ X` asserted by Stacks 0CZA.**
* `AlgebraicGeometry.Space.exists_fittingRankStratification_spec`: **Stacks 0CZA except for the
  representability of the flatness functor** — the chain, its three properties, the strata and
  their disjointness and covering, the disjoint union with its structural morphism, local
  freeness of rank `r` on `X_r`, and the finite presentation of `X_r ⟶ X` and of `X' ⟶ X`.
  The representability clause is
  `AlgebraicGeometry.Space.isFlatOver_modulePullback_iff_existsUnique_hom_lift`, and the tag is
  registered on the full statement
  `AlgebraicGeometry.Space.exists_fittingRankStratification_flat_spec` of
  `StacksFrontier/AlgebraicGeometry/Spaces/FittingStratumAssembly.lean`.

## Implementation notes

The three clauses of Stacks 03XP part (3) for `X' ⟶ X` are supplied by
`AlgebraicGeometry.Space.isFinitePresentation_of_isColimit_cofan_of_cofinitely_isEmpty` of
`StacksFrontier/AlgebraicGeometry/Spaces/AlgebraicSpaceCoproductFinitePresentation.lean`, whose
separatedness hypothesis holds because the inclusion of a subspace is a monomorphism
(Stacks 042N) and whose emptiness hypothesis is the content described above.  The coproduct is
formed in the category of algebraic spaces over `S`, and is transported to a coproduct of
sheaves along `AlgebraicGeometry.Space.algebraicSpacesToSheaf`, which creates countable
coproducts.

The spanning family over the identity chart is `Module.Finite.exists_fin` applied to the
sections of `G_T`, finite over the chart ring by
`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`.  No new finiteness
input is used: the identity chart of a represented algebraic space is affine as soon as the
representing object is, and it is surjective on points because its structure morphism is the
identity.

The emptiness is read on points, which is enough:
`AlgebraicGeometry.Space.isEmpty_points_pullback_of_preimage_range_eq_empty` turns the vanishing
of the preimage of a point set into the emptiness of the fibre product, so no statement about
the fibre product itself is needed.

The representability of the functor of flatness of `G_T` is **proved**, in
`StacksFrontier/AlgebraicGeometry/Spaces/FittingStratumAssembly.lean`.  What the tag's own section
means by "`G_T` is flat over `T`" is Stacks 05VV, `AlgebraicGeometry.Space.IsFlatOver` read
along the identity of `T`, as `AlgebraicGeometry.Space.FlatnessSituation.IsFlatAfterBaseChange`
of `StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctor.lean` reads it, and both directions
go through clause (3) of Stacks 0CZ9,
`AlgebraicGeometry.Space.existsUnique_lift_fittingRankStratum_iff`, which is an equivalence
between factoring through `X_r` and local freeness of rank `r`.

Forwards, a rank is produced on a basic-open neighbourhood of every point of an affine test
object by `AlgebraicGeometry.Space.exists_basicOpen_isFiniteLocallyFreeOfRank_of_isFlatOver_id`
(whose own route runs through `isFlatOver_id_of_isFiniteLocallyFreeOfRank` and
`isFlatOver_representedZariskiRestriction_of_isFlatOver_id`, so neither freeness of the
geometric stalk nor an unavailable chart-section flatness is needed), and the local
factorisations glue because the structural morphism is a monomorphism.  Backwards, Stacks 02WO
in the form `AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan` turns the
factorisation into a decomposition of the test object into disjoint open pieces each landing in
one stratum, and `AlgebraicGeometry.Space.isFlatOver_id_of_etale_cover_of_representable`
reassembles flatness from them.

Freeness of the geometric stalk is not needed, and the chart sections do not have to be
identified with the geometric stalk; flatness of the chart sections over the chart ring **is**
available from flatness over the space.  Clause (4) of Stacks 0CZS is stated in
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkFreeness.lean`, as
`AlgebraicGeometry.Space.exists_chartOpen_over_iso_free_of_flat_geometricFibreModuleStalk` and
`AlgebraicGeometry.Space.exists_chartOpen_over_iso_free_iff_flat_geometricFibreModuleStalk`;
clause (3) is not statable there, needing the geometric fibre `X_ȳ` as an algebraic space.  The
passage from a Zariski rank back to site-level `RingedSite.IsFiniteLocallyFreeOfRank` for
algebraic spaces (Stacks 05P2 and 05P9, proved and registered only for schemes) is absent, and
is not needed for Stacks 0CZA either.

None of this is about `AlgebraicGeometry.SheafOfModules.IsFlat`, the tensor-exactness
predicate, whose stalk criterion of Stacks 05NE is indeed proved only for the topology of opens
of a topological space; that predicate is not the one Stacks 05VV defines and the two are not
compared anywhere in this development.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/FiniteLocallyFreeModuleDescent.lean` record the
absence of the implication to *that* predicate, which is a different gap.

## References

* [Stacks Project, Tag 0CZA](https://stacks.math.columbia.edu/tag/0CZA)
* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 042N](https://stacks.math.columbia.edu/tag/042N)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)

/-! ### An affine test object misses some member of the chain -/

/-- **An affine test object of `X` lands in the complement of some member of the chain.**  Let
`G` be a quasi-coherent `𝒪_X`-module of finite type and let `X ⊇ Z_0 ⊇ Z_1 ⊇ …` be the chain of
closed subspaces cut out by its Fitting ideals.  For an affine object `T` of the site and a
morphism `a : T ⟶ X` there is an `N` with the range of `a` inside `X ∖ Z_N`.

The sections of `G_T` over the identity chart of `T` — which is affine, `T` being affine — form
a finite module over the chart ring, hence are spanned by `N` of them for some `N`, and the
identity chart is surjective on points because its structure morphism is the identity.  That is
exactly the condition which clause (2) of Stacks 0CZ9,
`AlgebraicGeometry.Space.existsUnique_lift_openComplement_iff_forall_exists_fin_span`, equates
with factoring through `X ∖ Z_N`. -/
theorem exists_range_le_openComplement_fittingClosedSubspace_of_isAffine
    (hGqc : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (a : yoneda.obj T ⟶ X.1) :
    ∃ N : ℕ, Subfunctor.range a ≤ openComplement B S hS (Z N).1 := by
  let T' : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let f : T' ⟶ X := ObjectProperty.homMk a
  let U : SmallEtale B S hS T'.1 := idChart B S hS T
  have hU : IsAffine ((SmallEtale.toOver B S hS T'.1 ⋙ BigFppfOver.toScheme B S hS).obj U) := hT
  have := module_finite_sections_of_isFiniteTypeOnSite ((modulePullback B S hS f).obj G)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hGqc)
    (isFiniteTypeOnSite_modulePullback B S hS f G hGft) U hU
  obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin
    (R := chartRing B S hS T'.1 T'.2 U)
    (M := ((modulePullback B S hS f).obj G).val.obj (op U))
  refine ⟨N, (existsUnique_lift_iff_range_le B S hS (openComplement B S hS (Z N).1) a).1 ?_⟩
  refine (existsUnique_lift_openComplement_iff_forall_exists_fin_span B S hS G hGqc hGft Z hZ
    N f).1 fun x ↦ ⟨U, s, hU, hs, ?_⟩
  change x ∈ Set.range (pointsMap B S hS (yoneda.obj T) (𝟙 (yoneda.obj T)))
  rw [pointsMap_id]
  exact ⟨x, rfl⟩

/-- **A stratum beyond the one an affine test object reaches is missed by it.**  If the range of
`a : T ⟶ X` lies in `X ∖ Z_N` then for every `n > N` the preimage under `a` of the point set of
the stratum `X_n = Z_{n-1} ∖ Z_n` is empty: the stratum lies in `Z_{n-1}`, which lies in `Z_N`
because the chain decreases, and `a` avoids the point set of `Z_N` altogether. -/
theorem preimage_range_pointsMap_fittingRankStratum_eq_empty
    (Z : ℕ → ClosedSubspaces B S hS X.1) (hanti : Antitone fun r ↦ (Z r).1)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ X.1} {N : ℕ}
    (ha : Subfunctor.range a ≤ openComplement B S hS (Z N).1) {n : ℕ} (hn : N < n) :
    pointsMap B S hS (yoneda.obj T) a ⁻¹'
        Set.range (pointsMap B S hS (fittingRankStratum B S hS X Z n).toFunctor
          (fittingRankStratum B S hS X Z n).ι) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  -- the image of `x` lies in `Z_N`, the stratum `X_n` being inside `Z_{n-1} ⊆ Z_N`
  have hin : pointsMap B S hS (yoneda.obj T) a x ∈
      Set.range (pointsMap B S hS (Z N).1.toFunctor (Z N).1.ι) :=
    range_pointsMap_ι_le B S hS
      (fittingRankStratum_le_of_lt B S hS X Z hanti hn) hx
  -- and in the complement of `Z_N`, the range of `a` being inside it
  have hfac : pointsMap B S hS (yoneda.obj T) a =
      pointsMap B S hS (Subfunctor.range a).toFunctor (Subfunctor.range a).ι ∘
        pointsMap B S hS (yoneda.obj T) (Subfunctor.toRange a) := by
    rw [← pointsMap_comp, Subfunctor.toRange_ι]
  have hout : pointsMap B S hS (yoneda.obj T) a x ∈
      Set.range (pointsMap B S hS (openComplement B S hS (Z N).1).toFunctor
        (openComplement B S hS (Z N).1).ι) :=
    range_pointsMap_ι_le B S hS ha ⟨_, (congrFun hfac x).symm⟩
  rw [range_pointsMap_ι_openComplement] at hout
  exact hout hin

/-! ### Finite presentation of the disjoint union -/

/-- **Stacks 0CZA: `X' = ∐_{r ≥ 0} X_r ⟶ X` is of finite presentation**, for the Fitting rank
strata of a quasi-coherent `𝒪_X`-module of finite presentation.

The three clauses of Stacks 03XP part (3) are supplied by
`AlgebraicGeometry.Space.isFinitePresentation_of_isColimit_cofan_of_cofinitely_isEmpty`.  Each
stratum is of finite presentation over `X` by
`AlgebraicGeometry.Space.isFinitePresentation_ι_fittingRankStratum` and separated over `X`
because its inclusion is a monomorphism (Stacks 042N); the emptiness of all but finitely many
base changes over an affine test object is
`AlgebraicGeometry.Space.preimage_range_pointsMap_fittingRankStratum_eq_empty`, applied to the
index `N`
of `AlgebraicGeometry.Space.exists_range_le_openComplement_fittingClosedSubspace_of_isAffine`.

Quasi-compactness of `X_r ⟶ X` alone would not suffice: the coproduct is infinite. -/
theorem isFinitePresentation_fittingRankStratificationHom
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) :
    IsFinitePresentation B S hS (fittingRankStratificationHom B S hS X Z).hom := by
  -- the coproduct of algebraic spaces, read as a coproduct of sheaves
  let Φ := algebraicSpacesToSheaf B S hS
  let leg : ∀ r : ℕ,
      fittingRankStratumSpace B S hS X Z r ⟶ fittingRankStratification B S hS X Z := fun r ↦
    Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r
  have hsheaf : IsColimit (Cofan.mk (Φ.obj (fittingRankStratification B S hS X Z))
      fun r ↦ Φ.map (leg r)) :=
    isColimitCofanMkObjOfIsColimit Φ _ leg (coproductIsCoproduct _)
  -- the restriction of the structural morphism to the `r`-th summand is the inclusion of `X_r`
  have hres : ∀ r : ℕ, (Φ.map (leg r)).hom ≫ (fittingRankStratificationHom B S hS X Z).hom =
      (fittingRankStratum B S hS X Z r).ι := fun r ↦
    congrArg (fun k : fittingRankStratumSpace B S hS X Z r ⟶ X ↦ k.hom)
      ((isAlgebraicSpace_fittingRankStratification B S hS X Z).2 r)
  refine isFinitePresentation_of_isColimit_cofan_of_cofinitely_isEmpty B S hS
    (fun r ↦ Φ.map (leg r)) hsheaf
    (fun r ↦ (fittingRankStratumSpace B S hS X Z r).property)
    (fittingRankStratification B S hS X Z).property X.2
    (fittingRankStratificationHom B S hS X Z).hom (fun r ↦ ?_) (fun r ↦ ?_) fun T hT a ↦ ?_
  · rw [hres r]
    exact isFinitePresentation_ι_fittingRankStratum B S hS X G hGqc hGfp Z hZ r
  · rw [hres r]
    exact isSeparated_of_mono B S hS (fittingRankStratum B S hS X Z r).ι inferInstance
  · obtain ⟨N, hN⟩ := exists_range_le_openComplement_fittingClosedSubspace_of_isAffine
      B S hS X G hGqc inferInstance Z hZ T hT a
    refine ⟨Set.Iic N, Set.finite_Iic N, fun n hn ↦ ?_⟩
    refine isEmpty_points_pullback_of_preimage_range_eq_empty B S hS a _ ?_
    rw [hres n]
    exact preimage_range_pointsMap_fittingRankStratum_eq_empty B S hS X Z
      (antitone_of_definingIdealSheaf_eq_fittingIdeal B S hS X G Z hZ) hN
      (lt_of_not_ge fun h ↦ hn h)

/-! ### Stacks 0CZA without the flatness functor -/

/-- **Stacks 0CZA, every clause except the representability of the flatness functor.**  Let `X`
be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G` be a
quasi-coherent `𝒪_X`-module of finite presentation.  Then the Fitting ideal sheaves of `G` cut
out a decreasing chain of closed subspaces `X = Z_{-1} ⊇ Z_0 ⊇ Z_1 ⊇ …` with empty
intersection, the strata `X_r = Z_{r-1} ∖ Z_r` are pairwise disjoint locally closed subspaces
of `X` and every point of `X` lies in exactly one of them, the disjoint union
`X' = ∐_{r ≥ 0} X_r` is an algebraic space over `S` whose structural morphism restricts on the
`r`-th summand to the inclusion of `X_r`, the pullback of `G` to `X_r` is finite locally free of
rank `r`, and both `X_r ⟶ X` and `X' ⟶ X` are of finite presentation.

The hypotheses are exactly the ones Stacks 0CZA makes.  What the tag asserts and this does not
is that `X'` represents the functor sending a test object `T ⟶ X` to a one-point set when `G_T`
is flat over `T` and to the empty set otherwise; that clause is
`AlgebraicGeometry.Space.isFlatOver_modulePullback_iff_existsUnique_hom_lift`, and the tag is
registered on `AlgebraicGeometry.Space.exists_fittingRankStratification_flat_spec` of
`StacksFrontier/AlgebraicGeometry/Spaces/FittingStratumAssembly.lean`, which adds it to the
statement below. -/
theorem exists_fittingRankStratification_spec
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G) :
    ∃ Z : ℕ → ClosedSubspaces B S hS X.1,
      (∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) ∧
      (Antitone fun r ↦ (Z r).1) ∧
      (⨅ r : ℕ, (Z r).1) = (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS) ∧
      (∀ r : ℕ, IsLocallyClosedSubspace B S hS (fittingRankStratum B S hS X Z r)) ∧
      (∀ r s : ℕ, r ≠ s →
        fittingRankStratum B S hS X Z r ⊓ fittingRankStratum B S hS X Z s ≤
          (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS)) ∧
      (∀ x : points B S hS X.1, ∃! r : ℕ,
        x ∉ Set.range (pointsMap B S hS (Z r).1.toFunctor (Z r).1.ι) ∧
          ∀ k < r, x ∈ Set.range (pointsMap B S hS (Z k).1.toFunctor (Z k).1.ι)) ∧
      IsAlgebraicSpace B S hS (fittingRankStratification B S hS X Z).obj ∧
      (∀ r : ℕ, Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r ≫
          fittingRankStratificationHom B S hS X Z = fittingRankStratumHom B S hS X Z r) ∧
      (∀ r : ℕ, RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite B S hS (fittingRankStratumSpace B S hS X Z r).1
          (fittingRankStratumSpace B S hS X Z r).2)
        ((modulePullback B S hS (fittingRankStratumHom B S hS X Z r)).obj G) r) ∧
      (∀ r : ℕ, IsFinitePresentation B S hS (fittingRankStratum B S hS X Z r).ι) ∧
      IsFinitePresentation B S hS (fittingRankStratificationHom B S hS X Z).hom := by
  obtain ⟨Z, hZ, hanti, hbot, hlc, hdisj, hcover, halg, hres⟩ :=
    exists_fittingRankStratification_of_isFinitePresentationOnSite B S hS X G hGqc hGfp
  exact ⟨Z, hZ, hanti, hbot, hlc, hdisj, hcover, halg, hres,
    isFiniteLocallyFreeOfRank_modulePullback_fittingRankStratumHom B S hS G hGqc inferInstance Z hZ,
    isFinitePresentation_ι_fittingRankStratum B S hS X G hGqc hGfp Z hZ,
    isFinitePresentation_fittingRankStratificationHom B S hS X G hGqc hGfp Z hZ⟩

end AlgebraicGeometry.Space

end
