module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# A chart with universally bounded fibres has a top degree stratum

Let `X` be an algebraic space over a scheme `S` and let `φ : h_U ⟶ X` be a morphism from a
scheme whose fibres are universally bounded in the sense of Stacks 03JL. The degree
stratification of Stacks 086T attaches to `X` a descending chain of open subspaces
`X = Y 0 ⊇ Y 1 ⊇ …`, a field-valued point factoring through `Y d` exactly when the fibre of
`φ` above it has degree at least `d`. This file shows that the bound of Stacks 03JL *truncates*
that chain: there is an `N` beyond which no field-valued point of `X` has fibre degree at least
`d`, so `Y d` has no points at all.

The consequence used downstream is that inside any nonempty open subspace of `X` the chain
stops: there is a largest `d` for which the stratum meets it, and on that stratum every
field-valued point has fibre degree *exactly* `d` — the chain is above `d` there and not above
`d + 1`. This is the step for which the source of Stacks 03JI uses the closed filtration of
Stacks 07S8; with the bound in hand the open chain of Stacks 086T already supplies it, and the
closed subspaces are not needed.

## Main results

* `AlgebraicGeometry.Space.exists_forall_isFiniteLocallyFreeOfRank_le_of_hasUniversallyBounded`:
  one bound `N` such that above *every* field-valued point of `X` the fibre of `φ` is finite
  locally free of some rank `≤ N`. This is the content of Stacks 03JL transported from the
  presentation it is stated with to the canonical representing object of the fibre.
* `AlgebraicGeometry.Space.exists_bound_not_fibre_degree_ge_of_hasUniversallyBounded`: the same
  bound, in the shape of the degree condition of Stacks 086T — beyond `N` no field-valued point
  has fibre degree at least `d`.
* `AlgebraicGeometry.Space.range_pointsMap_ι_top`: the top subspace has every point.
* `AlgebraicGeometry.Space.exists_max_stratum_meeting`: a chain of open subspaces starting at
  the whole space and characterised by a condition which fails beyond `N` has, inside any
  nonempty set of points, a largest member meeting that set.
* `AlgebraicGeometry.Space.exists_max_degree_stratum_of_hasUniversallyBounded` puts the two
  together: the chain of Stacks 086T for a chart with universally bounded fibres, together with
  an index at which it stops inside a given nonempty set of points.

## Implementation notes

Stacks 03JL is stated through an arbitrary presentation of the fibre: a pullback square over
the cospan `φ`, `Spec k ⟶ X` with a chosen apex in the site. Stacks 086T is stated through the
canonical representing object of that fibre, the one supplied by
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAlgebraicSpace`. The two apexes are
canonically isomorphic, being apexes of pullback squares over one cospan, and that isomorphism
is the Yoneda image of an isomorphism of the site because Yoneda is fully faithful; the rank
condition is invariant under it. That transport is the whole proof of the first result.

That no rank larger than `N` occurs then follows from uniqueness of the rank over a field,
`AlgebraicGeometry.finiteLocallyFree_rank_unique`, and finiteness of the fibre rules out the
other way for the degree condition of Stacks 086T to hold — a fibre which is not finite counts
there as having infinite degree.

## References

* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Pullback instances of `FibreDegreeStratification`, which instance search does not find
under Lean v4.35.0. -/
/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_BoundedChartTopStratum :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_BoundedChartTopStratum
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The bound of Stacks 03JL on the canonical representing object of a fibre -/

/-- **The bound of Stacks 03JL, on the canonical fibre.** If the fibres of `φ : h_U ⟶ X` are
universally bounded then one natural number `N` bounds the rank of the fibre of `φ` above every
field-valued point of `X`, that fibre being finite locally free.

Stacks 03JL presents the fibre by an arbitrary pullback square; the statement here uses the
canonical representing object of
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAlgebraicSpace`, which is what Stacks 086T
speaks about. The two are apexes of pullback squares over the same cospan, hence isomorphic, and
the isomorphism descends to the site because Yoneda is fully faithful. -/
theorem exists_forall_isFiniteLocallyFreeOfRank_le_of_hasUniversallyBounded
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hbdd : HasUniversallyBoundedFibers B S hS U φ) :
    ∃ N : ℕ, ∀ p : FieldValuedPoint B S hS X, ∃ r : ℕ, r ≤ N ∧
      IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
          (yonedaEquiv.symm p.value))) r := by
  obtain ⟨n, hn⟩ := hbdd
  refine ⟨n.toNat, fun p => ?_⟩
  obtain ⟨V, q, i, r, hrn, hrank, hsq⟩ :=
    hn p.carrier p.siteObject (Iso.refl _) (yonedaEquiv.symm p.value)
  set hrep := relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ with hrepdef
  set a := yonedaEquiv.symm p.value with ha
  have hpb := hrep.isPullback a
  have hcomp := hsq.isoIsPullback_hom_snd (yoneda.obj U) (yoneda.obj p.siteObject) hpb
  set e := yoneda.preimageIso (hsq.isoIsPullback (yoneda.obj U) (yoneda.obj p.siteObject) hpb)
    with he
  have hmap : e.hom ≫ hrep.snd a = q := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, he]
    simp only [Functor.preimageIso_hom, Functor.map_preimage]
    exact hcomp
  refine ⟨r, by omega, ?_⟩
  have hfac : (BigFppfOver.toScheme B S hS).map e.hom ≫
      (BigFppfOver.toScheme B S hS).map (hrep.snd a)
      = (BigFppfOver.toScheme B S hS).map q := by
    rw [← Functor.map_comp, hmap]
  have : IsIso ((BigFppfOver.toScheme B S hS).map e.hom) :=
    ((BigFppfOver.toScheme B S hS).mapIso e).isIso_hom
  rw [← hfac] at hrank
  exact ((IsFiniteLocallyFreeOfRank.property.{u} r).cancel_left_of_respectsIso
    ((BigFppfOver.toScheme B S hS).map e.hom)
    ((BigFppfOver.toScheme B S hS).map (hrep.snd a))).1 hrank

/-- **The bound of Stacks 03JL truncates the chain of Stacks 086T.** If the fibres of
`φ : h_U ⟶ X` are universally bounded then there is an `N` such that for every `d > N` no
field-valued point of `X` has fibre degree at least `d`.

The degree condition is the one of Stacks 086T: a fibre which is not finite counts as having
infinite degree, so both disjuncts have to be ruled out. The fibre here is finite locally free
of a rank `≤ N`, which rules out the first, and a rank over a field is unique, which rules out
the second. -/
theorem exists_bound_not_fibre_degree_ge_of_hasUniversallyBounded
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hbdd : HasUniversallyBoundedFibers B S hS U φ) :
    ∃ N : ℕ, ∀ (d : ℕ), N < d → ∀ p : FieldValuedPoint B S hS X,
      ¬ (¬ (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
              (BigFppfOver.toScheme B S hS)).presheaf
              (pullback.fst (yonedaEquiv.symm p.value) φ) ∨
        ∃ r : ℕ, d ≤ r ∧
          (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
            (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.fst (yonedaEquiv.symm p.value) φ)) := by
  obtain ⟨N, hN⟩ :=
    exists_forall_isFiniteLocallyFreeOfRank_le_of_hasUniversallyBounded B S hS hX φ hbdd
  refine ⟨N, fun d hd p => ?_⟩
  set hrep := relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ with hrepdef
  set a := yonedaEquiv.symm p.value with ha
  set g := (BigFppfOver.toScheme B S hS).map (hrep.snd a) with hg
  obtain ⟨r, hrN, hr⟩ := hN p
  have hfin := presheaf_pullback_fst_iff_property_snd B S hS
    (P := @_root_.AlgebraicGeometry.IsFinite.{u}) hrep a
  have hrk (t : ℕ) := presheaf_pullback_fst_iff_property_snd B S hS
    (P := IsFiniteLocallyFreeOfRank.property.{u} t) hrep a
  have hr' : IsFiniteLocallyFreeOfRank g r := hr
  have hflf : IsFiniteLocallyFree g := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree g r
  rintro (hnf | ⟨t, ht, hrt⟩)
  · exact hnf (hfin.2
      ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).1 hflf).1)
  · have : r = t := finiteLocallyFree_rank_unique g r t hr' ((hrk t).1 hrt)
    omega

/-! ### The largest stratum meeting a set of points -/

/-- The whole algebraic space is the point set of its top subspace: the inclusion of the top
subfunctor is an isomorphism, so it is surjective on points. -/
theorem range_pointsMap_ι_top {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    Set.range (pointsMap B S hS (⊤ : Subfunctor F).toFunctor (⊤ : Subfunctor F).ι)
      = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ⟨pointsMap B S hS F (inv (⊤ : Subfunctor F).ι) x, ?_⟩
  rw [show pointsMap B S hS (⊤ : Subfunctor F).toFunctor (⊤ : Subfunctor F).ι
      (pointsMap B S hS F (inv (⊤ : Subfunctor F).ι) x) =
      (pointsMap B S hS (⊤ : Subfunctor F).toFunctor (⊤ : Subfunctor F).ι ∘
        pointsMap B S hS F (inv (⊤ : Subfunctor F).ι)) x from rfl,
    ← pointsMap_comp, IsIso.inv_hom_id, pointsMap_id, id_eq]

/-- A predicate holding at `0` and failing at `k` holds somewhere below `k` while failing at the
successor of that place. -/
private theorem exists_lt_and_not_succ {Q : ℕ → Prop} (h0 : Q 0) :
    ∀ {k : ℕ}, ¬ Q k → ∃ d, d < k ∧ Q d ∧ ¬ Q (d + 1)
  | 0, hk => absurd h0 hk
  | (k + 1), hk => by
    by_cases hQk : Q k
    · exact ⟨k, Nat.lt_succ_self k, hQk, hk⟩
    · obtain ⟨d, hd, hQd, hQd1⟩ := exists_lt_and_not_succ h0 hQk
      exact ⟨d, hd.trans (Nat.lt_succ_self k), hQd, hQd1⟩

/-- **The largest stratum of a truncated chain meeting a nonempty set of points.** Let
`Y 0 ⊇ Y 1 ⊇ …` be open subspaces of an algebraic space `X` through which a field-valued point
factors exactly when some condition `D` holds of it, let `Y 0` be all of `X`, and let `D d` be
unsatisfiable for `d > N`. Then every nonempty set of points of `X` meets `Y d` for some `d ≤ N`
and misses `Y (d + 1)`.

Antitonicity of the chain is not needed, and neither is openness of `Y (d + 1)`; what the
argument uses is that an open set of points determines which field-valued points factor through
it, which is Stacks 03IE. The condition `D` is the degree condition of Stacks 086T when the
chain is the one that tag produces, and `N` is then the bound of
`AlgebraicGeometry.Space.exists_bound_not_fibre_degree_ge_of_hasUniversallyBounded`. -/
theorem exists_max_stratum_meeting
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Y : ℕ → Subfunctor X) (hY0 : Y 0 = ⊤)
    (hYopen : ∀ d, IsOpenSubspace B S hS (Y d))
    (D : ℕ → FieldValuedPoint B S hS X → Prop)
    (hYD : ∀ (d : ℕ) (p : FieldValuedPoint B S hS X),
      (∃ g : yoneda.obj p.siteObject ⟶ (Y d).toFunctor,
        g ≫ (Y d).ι = yonedaEquiv.symm p.value) ↔ D d p)
    (N : ℕ) (hN : ∀ d : ℕ, N < d → ∀ p : FieldValuedPoint B S hS X, ¬ D d p)
    (W : Set (points B S hS X)) (hWne : W.Nonempty) :
    ∃ d : ℕ, d ≤ N ∧
      (W ∩ Set.range (pointsMap B S hS (Y d).toFunctor (Y d).ι)).Nonempty ∧
      W ∩ Set.range (pointsMap B S hS (Y (d + 1)).toFunctor (Y (d + 1)).ι) = ∅ := by
  classical
  set Q : ℕ → Prop :=
    fun d => (W ∩ Set.range (pointsMap B S hS (Y d).toFunctor (Y d).ι)).Nonempty with hQ
  have hQ0 : Q 0 := by
    rw [hQ]
    simp only
    rw [hY0, range_pointsMap_ι_top, Set.inter_univ]
    exact hWne
  have hQN : ∀ d : ℕ, N < d → ¬ Q d := by
    rintro d hd ⟨x, -, hxY⟩
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    refine hN d hd p ((hYD d p).1 ?_)
    refine (factorsThrough_openSubspace_iff_points B S hS hX
      (isAlgebraicSpace_yoneda B S hS p.siteObject) (Y d) (hYopen d)
      (yonedaEquiv.symm p.value)).2 ?_
    rw [range_pointsMap_yonedaEquiv_symm B S hS p]
    exact Set.singleton_subset_iff.2 hxY
  obtain ⟨d, hd, hQd, hQd1⟩ := exists_lt_and_not_succ hQ0 (hQN (N + 1) (Nat.lt_succ_self N))
  exact ⟨d, Nat.lt_succ_iff.1 hd, hQd, Set.not_nonempty_iff_eq_empty.1 hQd1⟩

/-- **The top degree stratum of a chart with universally bounded fibres.** Let `φ : h_U ⟶ X` be
flat, locally of finite presentation, separated and locally quasi-finite from a scheme into an
algebraic space over `S`, with universally bounded fibres. Then the chain of Stacks 086T exists
with all its properties, and inside any nonempty set of points of `X` the chain stops: there is a
`d` for which the stratum meets that set while the next stratum misses it.

On that stratum every field-valued point has fibre degree exactly `d`: the chain says the degree
is at least `d` there, and the next stratum being missed says it is not at least `d + 1`. This is
what the source of Stacks 03JI takes from the closed filtration of Stacks 07S8. -/
theorem exists_max_degree_stratum_of_hasUniversallyBounded
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hflat : IsFlat B S hS φ) (hfp : IsLocallyOfFinitePresentation B S hS φ)
    (hsep : IsSeparated B S hS φ) (hlqf : IsLocallyQuasiFinite B S hS φ)
    (hbdd : HasUniversallyBoundedFibers B S hS U φ)
    (W : Set (points B S hS X)) (hWne : W.Nonempty) :
    ∃ (Y : ℕ → Subfunctor X) (d : ℕ),
      Y 0 = ⊤ ∧ Antitone Y ∧ (∀ e, IsOpenSubspace B S hS (Y e)) ∧
      (∀ (e : ℕ) (p : FieldValuedPoint B S hS X),
        (∃ g : yoneda.obj p.siteObject ⟶ (Y e).toFunctor,
            g ≫ (Y e).ι = yonedaEquiv.symm p.value) ↔
          (¬ (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
                (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm p.value) φ) ∨
            ∃ r : ℕ, e ≤ r ∧
              (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
                (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm p.value) φ))) ∧
      (W ∩ Set.range (pointsMap B S hS (Y d).toFunctor (Y d).ι)).Nonempty ∧
      W ∩ Set.range (pointsMap B S hS (Y (d + 1)).toFunctor (Y (d + 1)).ι) = ∅ := by
  obtain ⟨Y, hY0, hYanti, hYopen, hYdeg⟩ :=
    exists_antitone_isOpenSubspace_iff_fibre_degree_ge B S hS hX φ hflat hfp hsep hlqf
  obtain ⟨N, hN⟩ := exists_bound_not_fibre_degree_ge_of_hasUniversallyBounded B S hS hX φ hbdd
  obtain ⟨d, -, hmeet, hmiss⟩ :=
    exists_max_stratum_meeting B S hS hX Y hY0 hYopen _ hYdeg N hN W hWne
  exact ⟨Y, d, hY0, hYanti, hYopen, hYdeg, hmeet, hmiss⟩

end AlgebraicGeometry.Space

end
