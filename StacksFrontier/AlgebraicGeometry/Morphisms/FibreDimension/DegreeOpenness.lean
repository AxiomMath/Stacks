module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FibreCardinality
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeStratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedQuasiFinite

/-!
# The open locus where the degree of a fibre is at least `d`

Let `f : X ⟶ S` be flat, locally of finite presentation, separated and locally quasi-finite.
Then the points of `S` whose fibre has degree at least `d` form an open subscheme `Uᵈ`, and
these opens decrease with `d`:
```
S = U⁰ ⊇ U¹ ⊇ U² ⊇ …
```
A field-valued point `Spec k ⟶ S` factors through `Uᵈ` exactly when the base change
`X ×_S Spec k` has degree at least `d` over `k`. This is [Stacks Project, Tag 086R]; a fibre
which is not finite counts as having infinite degree, so it belongs to every `Uᵈ`.

The degrees here are the ranks of [Stacks Project, Tag 02KA]:
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank`. The fibres of `f` need not be universally bounded,
so there is no single closed filtration of `S` as in [Stacks Project, Tag 07RY]; what replaces it
is that every *quasi-compact* open of `X` does have universally bounded fibres over `S`, by
[Stacks Project, Tag 03JA], and that the degree of a fibre of `f` is the supremum of the degrees
of the fibres of those opens.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback_fst_of_fiber`: a degree of the fibre of
  `f` above the image of a field-valued point of `S` is a degree of the base change of `f` along
  that point.
* `AlgebraicGeometry.exists_antitone_opens_iff_fiber_degree_ge`: the decreasing opens `Uᵈ` of
  `S` through which a field-valued point factors exactly when the fibre above it has degree at
  least `d`.

## Implementation notes

An open subscheme is a `AlgebraicGeometry.Scheme.Opens`, and a field-valued point factoring
through one is the existence of a morphism to its associated scheme; this is interchangeable with
membership of the image point, `AlgebraicGeometry.factors_through_open_iff_mem`.

"Degree at least `d`" is spelled as the disjunction of non-finiteness of the base change with the
existence of a degree `r ≥ d`, rather than by a bound on a `WithTop ℕ`-valued degree function: a
degree is a rank of a finite locally free morphism, so a fibre which is not finite has no degree
at all, and the source's convention that such a fibre has infinite degree has to be written out.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 07RY](https://stacks.math.columbia.edu/tag/07RY)
* [Stacks Project, Tag 086R](https://stacks.math.columbia.edu/tag/086R)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-! ### Field-valued points and open subschemes -/

/-- A field-valued point of a scheme factors through an open subscheme exactly when its image
point lies in that open. -/
public lemma factors_through_open_iff_mem {S : Scheme.{u}} (k : Type u) [Field k]
    (g : Spec (.of k) ⟶ S) (U : S.Opens) :
    (∃ h : Spec (.of k) ⟶ U.toScheme, h ≫ U.ι = g) ↔ g (default : Spec (.of k)) ∈ U := by
  constructor
  · rintro ⟨h, hh⟩
    rw [← hh]
    exact (h default).property
  · intro hg
    have hsubset : Set.range g.base ⊆ (U : Set S) := by
      rintro _ ⟨t, rfl⟩
      rw [Subsingleton.elim t (default : Spec (.of k))]
      exact hg
    exact ⟨IsOpenImmersion.lift U.ι g (by simpa using hsubset),
      IsOpenImmersion.lift_fac U.ι g (by simpa using hsubset)⟩

/-! ### The degree of a fibre and the degree of a base change -/

/-- A degree of the fibre of `f` above the image of a field-valued point of the base is a degree
of the base change of `f` along that point. -/
public lemma isFiniteLocallyFreeOfRank_pullback_fst_of_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f] (k : Type u) [Field k]
    (g : Spec (.of k) ⟶ S) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField (g (default : Spec (.of k)))) r) :
    IsFiniteLocallyFreeOfRank (pullback.fst g f) r := by
  refine (rank_pullback_symmetry f g r).mpr (rank_of_constant_fiber_rank _ r fun t => ?_)
  refine finiteLocallyFreeOfRank_residueFiber_baseChange f g t r ?_
  rwa [show g t = g (default : Spec (.of k)) from
    congrArg g.base (Subsingleton.elim t (default : Spec (.of k)))]

/-- A flat, locally finitely presented, separated, locally quasi-finite and finite morphism to the
spectrum of a field has a degree. -/
private lemma exists_rank_of_isFinite_over_field {A : Scheme.{u}} (k : Type u) [Field k]
    (p : A ⟶ Spec (.of k)) [Flat p] [LocallyOfFinitePresentation p] [IsSeparated p]
    [LocallyQuasiFinite p] [IsFinite p] :
    ∃ r : ℕ, IsFiniteLocallyFreeOfRank p r := by
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨r, hr, -⟩ := existsUnique_rank_of_bounded_fiber p
    (hasUniversallyBoundedFibers_of_locallyQuasiFinite p) (default : Spec (.of k))
  refine ⟨r, rank_of_constant_fiber_rank p r fun t => ?_⟩
  rwa [Subsingleton.elim t (default : Spec (.of k))]

/-- The number of points of a finite locally free scheme over a field is at most its degree. -/
private lemma cardinalMk_le_rank_over_field {A : Scheme.{u}} (k : Type u) [Field k]
    (p : A ⟶ Spec (.of k)) (r : ℕ) [hr : IsFiniteLocallyFreeOfRank p r] :
    Cardinal.mk A ≤ (r : Cardinal.{u}) := by
  have hbase (l : Type u) [Field l] (g : Spec (.of l) ⟶ Spec (.of k)) :
      ∃ s ≤ r, IsFiniteLocallyFreeOfRank (pullback.fst g p) s :=
    ⟨r, le_rfl, (rank_pullback_symmetry p g r).mpr
      (IsFiniteLocallyFreeOfRank.of_isPullback (IsPullback.of_hasPullback p g))⟩
  have hcard := cardinalMk_pullback_le_of_degree_le p r hbase k (𝟙 _)
  let e : pullback (𝟙 (Spec (.of k))) p ≅ A := asIso (pullback.snd (𝟙 (Spec (.of k))) p)
  rwa [Cardinal.mk_congr (Equiv.ofBijective e.inv.base
    (ConcreteCategory.bijective_of_isIso e.inv.base))]

/-- A finite locally free scheme over a field of degree `r` has no `n` distinct points for
`n > r`. -/
private lemma card_le_rank_of_injective_points_over_field {A : Scheme.{u}} (k : Type u) [Field k]
    (p : A ⟶ Spec (.of k)) (r : ℕ) [IsFiniteLocallyFreeOfRank p r] {n : ℕ} (x : Fin n → A)
    (hx : Function.Injective x) : n ≤ r := by
  have hinj : Function.Injective (x ∘ (Equiv.ulift.{u} (α := Fin n))) :=
    hx.comp Equiv.ulift.injective
  have h : (n : Cardinal.{u}) ≤ (r : Cardinal.{u}) := by
    simpa using (Cardinal.mk_le_of_injective hinj).trans (cardinalMk_le_rank_over_field k p r)
  exact_mod_cast h

/-! ### The quasi-compact case over an affine base -/

/-- For a quasi-compact `f` to an affine base, there are decreasing opens `Uᵈ` of the base through
which a field-valued point factors exactly when the fibre above it has degree at least `d`. -/
private lemma exists_antitone_opens_of_quasiCompact_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f]
    [QuasiCompact f] [IsAffine S] :
    ∃ U : ℕ → S.Opens,
      U 0 = ⊤ ∧ Antitone U ∧
        ∀ (d : ℕ) (k : Type u) [Field k] (g : Spec (.of k) ⟶ S),
          (∃ h : Spec (.of k) ⟶ (U d).toScheme, h ≫ (U d).ι = g) ↔
            (¬ IsFinite (pullback.fst g f) ∨
              ∃ r : ℕ, d ≤ r ∧ IsFiniteLocallyFreeOfRank (pullback.fst g f) r) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hb : HasUniversallyBoundedFibers f := hasUniversallyBoundedFibers_of_locallyQuasiFinite f
  let C : ℕ → Set S := fun d =>
    {s | ∃ r < d, IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) r}
  let U : ℕ → S.Opens := fun d => ⟨(C d)ᶜ, (isClosed_fiber_rank_lt f hb d).isOpen_compl⟩
  have hmem (d : ℕ) (s : S) : s ∈ U d ↔ s ∉ C d := Iff.rfl
  refine ⟨U, ?_, ?_, ?_⟩
  · refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun s => ?_)
    rintro ⟨r, hr, -⟩
    omega
  · intro a b hab s hs
    rw [hmem] at hs ⊢
    rintro ⟨r, hr, hrank⟩
    exact hs ⟨r, by omega, hrank⟩
  · intro d k _ g
    rw [factors_through_open_iff_mem, hmem]
    have hfin : IsFinite (pullback.fst g f) := IsFinite.of_locallyQuasiFinite _
    obtain ⟨m, hm, hmuniq⟩ := existsUnique_rank_of_bounded_fiber f hb
      (g (default : Spec (.of k)))
    have hpull : IsFiniteLocallyFreeOfRank (pullback.fst g f) m :=
      isFiniteLocallyFreeOfRank_pullback_fst_of_fiber f k g m hm
    constructor
    · intro hnot
      refine Or.inr ⟨m, ?_, hpull⟩
      by_contra hlt
      exact hnot ⟨m, by omega, hm⟩
    · rintro (hnotfin | ⟨r, hdr, hr⟩) hC
      · exact hnotfin hfin
      · obtain ⟨r', hr'd, hr'⟩ := hC
        have hrm : r = m := finiteLocallyFree_rank_unique (pullback.fst g f) r m hr hpull
        have hr'm : r' = m := hmuniq r' hr'
        omega

/-! ### Quasi-compact opens of the source detect the fibre degree -/

/-- A finite subset of an open subscheme is contained in a quasi-compact open subscheme of it. -/
private lemma exists_compact_open_cover_finite_set {X : Scheme.{u}} {A : Set X} (hA : A.Finite)
    (O : X.Opens) (hAO : A ⊆ O) :
    ∃ W : X.Opens, IsCompact (W : Set X) ∧ A ⊆ W ∧ W ≤ O := by
  induction A, hA using Set.Finite.induction_on generalizing O with
  | empty => exact ⟨⊥, by simp, by simp, bot_le⟩
  | @insert x A hxa hfin ih =>
    obtain ⟨W, hW, hAW, hWO⟩ := ih O fun y hy => hAO (Set.mem_insert_of_mem x hy)
    obtain ⟨V, hV, hxV, hVO⟩ := exists_isAffineOpen_mem_and_subset (hAO (Set.mem_insert x A))
    refine ⟨W ⊔ V, by simpa using hW.union hV.isCompact, ?_, sup_le hWO hVO⟩
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact (show V ≤ W ⊔ V from le_sup_right) hxV
    · exact (show W ≤ W ⊔ V from le_sup_left) (hAW hy)

/-- A fibre of a locally quasi-finite morphism which is not finite has infinitely many points. -/
private lemma infinite_fiber_points_of_not_isFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyQuasiFinite f] (k : Type u) [Field k] (g : Spec (.of k) ⟶ S)
    (hnot : ¬ IsFinite (pullback.fst g f)) : Infinite (pullback g f : Scheme.{u}) := by
  refine ⟨fun hfinite => ?_⟩
  let : Finite (pullback g f : Scheme.{u}) := hfinite
  let : CompactSpace (pullback g f : Scheme.{u}) := Finite.compactSpace
  have : QuasiCompact (pullback.fst g f) := inferInstance
  exact hnot (IsFinite.of_locallyQuasiFinite (pullback.fst g f))

/-- Points of a fibre whose images lie in an open subscheme of the source lift to the fibre of
the restriction to that open. -/
private lemma lift_injective_fiber_points_to_open {X S : Scheme.{u}} (f : X ⟶ S) (k : Type u)
    [Field k] (g : Spec (.of k) ⟶ S) (W : X.Opens) {n : ℕ}
    (x : Fin n → (pullback g f : Scheme.{u})) (hx : Function.Injective x)
    (hW : ∀ i, (pullback.snd g f) (x i) ∈ W) :
    ∃ y : Fin n → (pullback g (W.ι ≫ f) : Scheme.{u}), Function.Injective y := by
  classical
  let j : pullback (pullback.snd g f) W.ι ⟶ pullback g f := pullback.fst (pullback.snd g f) W.ι
  let e : pullback (pullback.snd g f) W.ι ≅ pullback g (W.ι ≫ f) :=
    pullbackLeftPullbackSndIso g f W.ι
  have hj (i : Fin n) : x i ∈ Set.range j.base := by
    change x i ∈ Set.range (pullback.fst (pullback.snd g f) W.ι).base
    rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]
    exact hW i
  have hz (i : Fin n) : j ((hj i).choose) = x i := (hj i).choose_spec
  have hzi : Function.Injective fun i => (hj i).choose := fun i i' hii' =>
    hx (((hz i).symm.trans (congrArg j hii')).trans (hz i'))
  exact ⟨fun i => e.hom ((hj i).choose),
    (ConcreteCategory.bijective_of_isIso e.hom.base).1.comp hzi⟩

/-- A fibre which is not finite already has degree at least `d` on a quasi-compact open of the
source. -/
private lemma exists_compact_open_rank_ge_of_nonfinite_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f]
    [QuasiSeparatedSpace S] (k : Type u) [Field k] (g : Spec (.of k) ⟶ S)
    (hnot : ¬ IsFinite (pullback.fst g f)) (d : ℕ) :
    ∃ W : {W : X.Opens // QuasiCompact (W.ι ≫ f)}, ∃ r : ℕ, d ≤ r ∧
      IsFiniteLocallyFreeOfRank (pullback.fst g (W.1.ι ≫ f)) r := by
  classical
  let : Infinite (pullback g f : Scheme.{u}) :=
    infinite_fiber_points_of_not_isFinite f k g hnot
  let x : Fin d → (pullback g f : Scheme.{u}) := fun i =>
    Infinite.natEmbedding (pullback g f : Scheme.{u}) i
  have hx : Function.Injective x :=
    (Infinite.natEmbedding (pullback g f : Scheme.{u})).injective.comp Fin.val_injective
  obtain ⟨W, hcompact, hAW, -⟩ := exists_compact_open_cover_finite_set
    (Set.finite_range fun i : Fin d => (pullback.snd g f) (x i)) (⊤ : X.Opens) (by simp)
  let : CompactSpace W := isCompact_iff_compactSpace.mp hcompact
  have hqc : QuasiCompact (W.ι ≫ f) := inferInstance
  have : IsFinite (pullback.fst g (W.ι ≫ f)) := IsFinite.of_locallyQuasiFinite _
  obtain ⟨r, hr⟩ := exists_rank_of_isFinite_over_field k (pullback.fst g (W.ι ≫ f))
  obtain ⟨y, hy⟩ := lift_injective_fiber_points_to_open f k g W x hx fun i => hAW ⟨i, rfl⟩
  let : IsFiniteLocallyFreeOfRank (pullback.fst g (W.ι ≫ f)) r := hr
  exact ⟨⟨W, hqc⟩, r,
    card_le_rank_of_injective_points_over_field k (pullback.fst g (W.ι ≫ f)) r y hy, hr⟩

/-- A fibre over a field-valued point is finite as a topological space as soon as it is finite as
a morphism. -/
private lemma finite_fiber_points {X S : Scheme.{u}} (f : X ⟶ S) (k : Type u) [Field k]
    (g : Spec (.of k) ⟶ S) [IsFinite (pullback.fst g f)] :
    Finite (pullback g f : Scheme.{u}) := by
  have : IsArtinianScheme (pullback g f) :=
    { toIsLocallyArtinian := IsLocallyArtinian.of_locallyQuasiFinite (pullback.fst g f)
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (pullback.fst g f) }
  infer_instance

/-- A finite fibre over a field-valued point of an affine open of the base is contained in a
quasi-compact open subscheme of the source lying above that affine open. -/
private lemma exists_compact_open_containing_finite_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    (k : Type u) [Field k] (g : Spec (.of k) ⟶ S) [IsFinite (pullback.fst g f)]
    (U : S.affineOpens) (hgU : g (default : Spec (.of k)) ∈ U.1) :
    ∃ W : X.Opens, IsCompact (W : Set X) ∧ W ≤ f ⁻¹ᵁ U.1 ∧
      Set.range (pullback.snd g f).base ⊆ W := by
  let : Finite (pullback g f : Scheme.{u}) := finite_fiber_points f k g
  have hAU : Set.range (pullback.snd g f).base ⊆ (f ⁻¹ᵁ U.1 : Set X) := by
    rintro _ ⟨p, rfl⟩
    have h : f ((pullback.snd g f) p) = g ((pullback.fst g f) p) :=
      congrArg (fun q : pullback g f ⟶ S => q.base p) (pullback.condition (f := g) (g := f)).symm
    change f ((pullback.snd g f) p) ∈ (U.1 : Set S)
    rw [h, congrArg g.base
      (Subsingleton.elim ((pullback.fst g f) p) (default : Spec (.of k)))]
    exact hgU
  obtain ⟨W, hW, hAW, hWU⟩ := exists_compact_open_cover_finite_set (Set.finite_range _) _ hAU
  exact ⟨W, hW, hWU, hAW⟩

/-- An open subscheme of the source containing the whole fibre above a field-valued point
computes the degree of that fibre. -/
private lemma rank_of_open_containing_fiber {X S : Scheme.{u}} (f : X ⟶ S) (k : Type u) [Field k]
    (g : Spec (.of k) ⟶ S) (W : X.Opens) (hW : Set.range (pullback.snd g f).base ⊆ W) (r : ℕ)
    (hr : IsFiniteLocallyFreeOfRank (pullback.fst g f) r) :
    IsFiniteLocallyFreeOfRank (pullback.fst g (W.ι ≫ f)) r := by
  have : IsIso (pullback.fst (pullback.snd g f) W.ι) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
    rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι]
    exact Set.eq_univ_of_forall fun p => hW ⟨p, rfl⟩
  let e : pullback g (W.ι ≫ f) ≅ pullback g f :=
    (pullbackLeftPullbackSndIso g f W.ι).symm ≪≫ asIso (pullback.fst (pullback.snd g f) W.ι)
  have he : e.hom ≫ pullback.fst g f = pullback.fst g (W.ι ≫ f) := by
    simpa only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc] using
      pullbackLeftPullbackSndIso_inv_fst g f W.ι
  exact he ▸ (rank_comp_iso e (pullback.fst g f) r).mp hr

/-- A finite fibre of a given degree is already of that degree on a quasi-compact open of the
source. -/
private lemma exists_compact_open_of_finite_fiber_rank {X S : Scheme.{u}}
    [QuasiSeparatedSpace S] (f : X ⟶ S) (k : Type u) [Field k] (g : Spec (.of k) ⟶ S)
    [IsFinite (pullback.fst g f)] (r : ℕ) (hr : IsFiniteLocallyFreeOfRank (pullback.fst g f) r) :
    ∃ W : {W : X.Opens // QuasiCompact (W.ι ≫ f)},
      IsFiniteLocallyFreeOfRank (pullback.fst g (W.1.ι ≫ f)) r := by
  obtain ⟨V, hV, hgV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show g (default : Spec (.of k)) ∈ (⊤ : S.Opens) by trivial)
  obtain ⟨W, hcompact, -, hW⟩ := exists_compact_open_containing_finite_fiber f k g ⟨V, hV⟩ hgV
  let : CompactSpace W := isCompact_iff_compactSpace.mp hcompact
  exact ⟨⟨W, inferInstance⟩, rank_of_open_containing_fiber f k g W hW r hr⟩

/-- The degree of a fibre of a restriction of `f` to an open subscheme of the source is at most
the degree of the fibre of `f`. -/
private lemma rank_le_of_open_fiber {X S : Scheme.{u}} (f : X ⟶ S) (k : Type u) [Field k]
    (g : Spec (.of k) ⟶ S) (W : X.Opens) [IsFinite (pullback.fst g f)]
    [IsFinite (pullback.fst g (W.ι ≫ f))] (r s : ℕ)
    (hr : IsFiniteLocallyFreeOfRank (pullback.fst g f) r)
    (hs : IsFiniteLocallyFreeOfRank (pullback.fst g (W.ι ≫ f)) s) : s ≤ r := by
  let i : pullback g (W.ι ≫ f) ⟶ pullback g f :=
    (pullbackLeftPullbackSndIso g f W.ι).inv ≫ pullback.fst (pullback.snd g f) W.ι
  have : IsOpenImmersion i := by dsimp only [i]; infer_instance
  have hi : i ≫ pullback.fst g f = pullback.fst g (W.ι ≫ f) := by
    simpa only [i, Category.assoc] using pullbackLeftPullbackSndIso_inv_fst g f W.ι
  have : IsFinite (i ≫ pullback.fst g f) := by rw [hi]; infer_instance
  exact finite_open_rank_le_of_field i (pullback.fst g f) r s hr (hi ▸ hs)

/-! ### The affine base case -/

/-- The opens of an affine base detecting the degree of the fibres of the restrictions of `f` to
the quasi-compact opens of its source. -/
private lemma exists_antitone_opens_detecting_compact_open_restrictions {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f]
    [IsAffine S] :
    ∃ U : ℕ → S.Opens,
      U 0 = ⊤ ∧ Antitone U ∧
        ∀ (d : ℕ) (k : Type u) [Field k] (g : Spec (.of k) ⟶ S),
          (∃ h : Spec (.of k) ⟶ (U d).toScheme, h ≫ (U d).ι = g) ↔
            ∃ W : {W : X.Opens // QuasiCompact (W.ι ≫ f)}, ∃ r : ℕ, d ≤ r ∧
              IsFiniteLocallyFreeOfRank (pullback.fst g (W.1.ι ≫ f)) r := by
  classical
  let J := {W : X.Opens // QuasiCompact (W.ι ≫ f)}
  have hbot : QuasiCompact ((⊥ : X.Opens).ι ≫ f) := by
    constructor
    intro A _ _
    convert isCompact_empty using 1
    ext x
    exact False.elim x.property
  let j₀ : J := ⟨⊥, hbot⟩
  let V (j : J) : ℕ → S.Opens := by
    let : QuasiCompact (j.1.ι ≫ f) := j.2
    exact (exists_antitone_opens_of_quasiCompact_of_isAffine (j.1.ι ≫ f)).choose
  have hV (j : J) : V j 0 = ⊤ ∧ Antitone (V j) ∧
      ∀ (d : ℕ) (k : Type u) [Field k] (g : Spec (.of k) ⟶ S),
        (∃ h : Spec (.of k) ⟶ (V j d).toScheme, h ≫ (V j d).ι = g) ↔
          (¬ IsFinite (pullback.fst g (j.1.ι ≫ f)) ∨
            ∃ r : ℕ, d ≤ r ∧
              IsFiniteLocallyFreeOfRank (pullback.fst g (j.1.ι ≫ f)) r) := by
    let : QuasiCompact (j.1.ι ≫ f) := j.2
    exact (exists_antitone_opens_of_quasiCompact_of_isAffine (j.1.ι ≫ f)).choose_spec
  refine ⟨fun d => ⨆ j : J, V j d, ?_, ?_, ?_⟩
  · refine le_antisymm le_top ?_
    calc (⊤ : S.Opens) = V j₀ 0 := (hV j₀).1.symm
      _ ≤ ⨆ j : J, V j 0 := le_iSup (fun j : J => V j 0) j₀
  · exact fun a b hab => iSup_le fun j => le_iSup_of_le j ((hV j).2.1 hab)
  · intro d k _ g
    rw [factors_through_open_iff_mem]
    simp only [TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨j, hj⟩
      have hr := ((hV j).2.2 d k g).mp ((factors_through_open_iff_mem k g (V j d)).mpr hj)
      let : QuasiCompact (j.1.ι ≫ f) := j.2
      exact ⟨j, hr.resolve_left fun h => h (IsFinite.of_locallyQuasiFinite _)⟩
    · rintro ⟨j, r, hdr, hr⟩
      exact ⟨j, (factors_through_open_iff_mem k g (V j d)).mp
        (((hV j).2.2 d k g).mpr (Or.inr ⟨r, hdr, hr⟩))⟩

/-- Over an affine base, there are decreasing opens `Uᵈ` of the base through which a field-valued
point factors exactly when the fibre above it has degree at least `d`. -/
private lemma exists_antitone_opens_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f] [IsAffine S] :
    ∃ U : ℕ → S.Opens,
      U 0 = ⊤ ∧ Antitone U ∧
        ∀ (d : ℕ) (k : Type u) [Field k] (g : Spec (.of k) ⟶ S),
          (∃ h : Spec (.of k) ⟶ (U d).toScheme, h ≫ (U d).ι = g) ↔
            (¬ IsFinite (pullback.fst g f) ∨
              ∃ r : ℕ, d ≤ r ∧ IsFiniteLocallyFreeOfRank (pullback.fst g f) r) := by
  obtain ⟨U, hzero, hanti, hU⟩ := exists_antitone_opens_detecting_compact_open_restrictions f
  refine ⟨U, hzero, hanti, fun d k _ g => ?_⟩
  rw [hU]
  constructor
  · rintro ⟨W, s, hds, hs⟩
    by_cases hfinite : IsFinite (pullback.fst g f)
    · let : IsFinite (pullback.fst g f) := hfinite
      obtain ⟨r, hr⟩ := exists_rank_of_isFinite_over_field k (pullback.fst g f)
      let : QuasiCompact (W.1.ι ≫ f) := W.2
      have : IsFinite (pullback.fst g (W.1.ι ≫ f)) := IsFinite.of_locallyQuasiFinite _
      exact Or.inr ⟨r, hds.trans (rank_le_of_open_fiber f k g W.1 r s hr hs), hr⟩
    · exact Or.inl hfinite
  · rintro (hnot | ⟨r, hdr, hr⟩)
    · exact exists_compact_open_rank_ge_of_nonfinite_fiber f k g hnot d
    · have : IsAffineHom (pullback.fst g f) := IsFiniteLocallyFreeOfRank.toIsAffineHom r
      have : IsFinite (pullback.fst g f) := IsFinite.of_locallyQuasiFinite _
      obtain ⟨W, hW⟩ := exists_compact_open_of_finite_fiber_rank f k g r hr
      exact ⟨W, r, hdr, hW⟩

/-! ### Stacks 086R -/

/-- Restricting the base to an open subscheme changes neither the finiteness nor the degree of a
fibre above a field-valued point of that open. -/
public lemma fiber_degree_ge_iff_base_open {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (k : Type u) [Field k] (g : Spec (.of k) ⟶ U.toScheme) (d : ℕ) :
    (¬ IsFinite (pullback.fst g (pullback.fst U.ι f)) ∨
        ∃ r : ℕ, d ≤ r ∧
          IsFiniteLocallyFreeOfRank (pullback.fst g (pullback.fst U.ι f)) r) ↔
      (¬ IsFinite (pullback.fst (g ≫ U.ι) f) ∨
        ∃ r : ℕ, d ≤ r ∧ IsFiniteLocallyFreeOfRank (pullback.fst (g ≫ U.ι) f) r) := by
  let e := pullbackRightPullbackFstIso U.ι f g
  have he : e.hom ≫ pullback.fst (g ≫ U.ι) f = pullback.fst g (pullback.fst U.ι f) :=
    pullbackRightPullbackFstIso_hom_fst U.ι f g
  have he' : e.inv ≫ pullback.fst g (pullback.fst U.ι f) = pullback.fst (g ≫ U.ι) f := by
    rw [← he]; simp
  have hfinite : IsFinite (pullback.fst g (pullback.fst U.ι f)) ↔
      IsFinite (pullback.fst (g ≫ U.ι) f) := by
    constructor
    · intro h
      let : IsFinite (pullback.fst g (pullback.fst U.ι f)) := h
      have : IsFinite (e.inv ≫ pullback.fst g (pullback.fst U.ι f)) := inferInstance
      simpa only [he'] using this
    · intro h
      let : IsFinite (pullback.fst (g ≫ U.ι) f) := h
      have : IsFinite (e.hom ≫ pullback.fst (g ≫ U.ι) f) := inferInstance
      simpa only [he] using this
  have hrank (r : ℕ) : IsFiniteLocallyFreeOfRank (pullback.fst g (pullback.fst U.ι f)) r ↔
      IsFiniteLocallyFreeOfRank (pullback.fst (g ≫ U.ι) f) r := by
    rw [← he, ← rank_comp_iso e (pullback.fst (g ≫ U.ι) f) r]
  simp only [hfinite, hrank]

/-- A flat, locally finitely presented, separated and locally quasi-finite morphism of schemes has
a decreasing sequence of open subschemes of its target through which a field-valued point factors
exactly when the corresponding fibre has degree at least the index; a fibre which is not finite
counts as having infinite degree. -/
@[stacks 086R]
public theorem exists_antitone_opens_iff_fiber_degree_ge {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f] :
    ∃ U : ℕ → S.Opens,
      U 0 = ⊤ ∧ Antitone U ∧
        ∀ (d : ℕ) (k : Type u) [Field k] (g : Spec (.of k) ⟶ S),
          (∃ h : Spec (.of k) ⟶ (U d).toScheme, h ≫ (U d).ι = g) ↔
            (¬ IsFinite (pullback.fst g f) ∨
              ∃ r : ℕ, d ≤ r ∧ IsFiniteLocallyFreeOfRank (pullback.fst g f) r) := by
  classical
  let V (j : S.affineOpens) : ℕ → j.1.toScheme.Opens := by
    have : IsAffine j.1.toScheme := j.2
    exact (exists_antitone_opens_of_isAffine (pullback.fst j.1.ι f)).choose
  have hV (j : S.affineOpens) : V j 0 = ⊤ ∧ Antitone (V j) ∧
      ∀ (d : ℕ) (k : Type u) [Field k] (g : Spec (.of k) ⟶ j.1.toScheme),
        (∃ h : Spec (.of k) ⟶ (V j d).toScheme, h ≫ (V j d).ι = g) ↔
          (¬ IsFinite (pullback.fst g (pullback.fst j.1.ι f)) ∨
            ∃ r : ℕ, d ≤ r ∧
              IsFiniteLocallyFreeOfRank (pullback.fst g (pullback.fst j.1.ι f)) r) := by
    have : IsAffine j.1.toScheme := j.2
    exact (exists_antitone_opens_of_isAffine (pullback.fst j.1.ι f)).choose_spec
  refine ⟨fun d => ⨆ j : S.affineOpens, j.1.ι ''ᵁ V j d, ?_, ?_, ?_⟩
  · refine le_antisymm le_top ?_
    rw [← iSup_affineOpens_eq_top S]
    refine iSup_le fun j => ?_
    calc (j.1 : S.Opens) = j.1.ι ''ᵁ ⊤ := j.1.ι_image_top.symm
      _ = j.1.ι ''ᵁ V j 0 := by rw [(hV j).1]
      _ ≤ ⨆ j : S.affineOpens, j.1.ι ''ᵁ V j 0 :=
          le_iSup (fun j : S.affineOpens => j.1.ι ''ᵁ V j 0) j
  · exact fun a b hab => iSup_le fun j => le_iSup_of_le j (j.1.ι.image_mono ((hV j).2.1 hab))
  · intro d k _ g
    rw [factors_through_open_iff_mem]
    simp only [TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨g', hgg'⟩ := (factors_through_open_iff_mem k g j.1).mpr (j.1.ι_image_le (V j d) hj)
      have hpoint : j.1.ι (g' (default : Spec (.of k))) = g (default : Spec (.of k)) := by
        rw [← hgg']; rfl
      rw [← hpoint] at hj
      have hlocal := ((hV j).2.2 d k g').mp
        ((factors_through_open_iff_mem k g' (V j d)).mpr (j.1.mem_ι_image_iff.mp hj))
      exact hgg' ▸ (fiber_degree_ge_iff_base_open f j.1 k g' d).mp hlocal
    · intro hglobal
      obtain ⟨W, hW, hgW, -⟩ := exists_isAffineOpen_mem_and_subset
        (show g (default : Spec (.of k)) ∈ (⊤ : S.Opens) by trivial)
      obtain ⟨g', hgg'⟩ := (factors_through_open_iff_mem k g W).mpr hgW
      have hfactor := ((hV ⟨W, hW⟩).2.2 d k g').mpr
        ((fiber_degree_ge_iff_base_open f W k g' d).mpr (by rw [hgg']; exact hglobal))
      have hpoint : W.ι (g' (default : Spec (.of k))) = g (default : Spec (.of k)) := by
        rw [← hgg']; rfl
      exact ⟨⟨W, hW⟩, hpoint ▸ W.mem_ι_image_iff.mpr
        ((factors_through_open_iff_mem k g' (V ⟨W, hW⟩ d)).mp hfactor)⟩

end AlgebraicGeometry

end
