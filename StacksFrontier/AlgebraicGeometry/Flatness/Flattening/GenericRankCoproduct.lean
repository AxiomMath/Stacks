module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericRankBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericRankBound

/-!
# The generic-rank decomposition of the flat-dimension functor

Let `f : X ⟶ S` be a smooth morphism of affine schemes with geometrically irreducible fibres of
dimension `d` and let `F` be a quasi-coherent `𝒪_X`-module of finite presentation. Stacks 05UE
asserts the decomposition
```
F_d = ∐_{p = 0, …, c} H_p
```
for some `c ≥ 0`, where `F_d` is the functor of flatness in dimensions `≥ d` of Stacks 05MT and
`H_p` is the functor of Stacks 05MP testing freeness of rank `p` near the generic points of the
fibres. This file proves it.

## Main results

* `FreeAtGenericPointsSituation.condition_eq_empty_of_gt`: **`H_p = ∅` for `p > c`**, so the
  coproduct is finite.
* `FreeAtGenericPointsSituation.condition_rank_unique`: the `H_p` are pairwise disjoint over a
  scheme with a point, which is the local injectivity of the comparison map.
* `FreeAtGenericPointsSituation.exists_open_condition_of_isFlatInDimensionsGE`:
  a point of `T` at which `F_T` is flat in dimensions `≥ d` has an open neighbourhood over
  which `H_r` holds for some `r ≤ c`, which is the local surjectivity.
* `FreeAtGenericPointsSituation.flatDimensionFunctor_iso_coproduct_freeAtGenericPointsFunctor`:
  **Stacks 05UE**, the decomposition itself, as an isomorphism of Zariski sheaves over `S`.

## Implementation notes

### Why the coproduct is taken in sheaves

The equality of the source cannot hold as an equality of presheaves on `Sch/S`. Both `F_d` and
every `H_p` are subterminal, so they send the empty scheme to a singleton: every condition
holds vacuously over `∅`. The pointwise disjoint union `∐_{p ≤ c} H_p` therefore has `c + 1`
elements over `∅` while `F_d` has one, and no map between them can be bijective. The same
obstruction appears over any `T` that is disconnected with different generic ranks on the
pieces: there `F_d(T)` is a singleton while every `H_p(T)` is empty.

Both discrepancies are exactly the failure of the pointwise disjoint union to be a sheaf, and
both disappear on sheafifying: the empty sieve covers `∅`, so the gluing axiom forces the value
of a sheaf at `∅` to be a singleton, and a section over a disconnected `T` is by definition
given by compatible sections over a cover. So the coproduct of the source is the coproduct in
Zariski sheaves over `S`, and that is what is proved here: the comparison map out of the
pointwise disjoint union is a *local* bijection, hence becomes an isomorphism after
sheafification, and sheafification preserves coproducts, being a left adjoint.

### The two halves of local bijectivity

Local injectivity is that the `H_p` are disjoint, which holds at every `T` with a point: the
fibres of `X_T ⟶ T` are irreducible, so a point `t` of `T` has a fibre with a generic point,
and the rank of a module free of finite rank near a point is determined
(`AlgebraicGeometry.freeAtPointOfRank_unique`). Over an empty `T` the `H_p` are not disjoint,
and this is not a gap: the empty sieve covers an empty scheme, so local injectivity there is
vacuous. This is the same mechanism that repairs the value at `∅`.

Local surjectivity is the content of the lemma. It is the forward direction of Stacks 05UE over
an arbitrary `T`
(`AlgebraicGeometry.FreeAtGenericPointsSituation.exists_mem_baseRankLocus`) together with the
bound `c` (`AlgebraicGeometry.exists_rank_bound_of_compactSpace`): if `F_T` is flat in
dimensions `≥ d` then every `t ∈ T` lies in the image of the rank-`r` free locus for some `r`,
that image is open, and `r ≤ c`. The open neighbourhood over which `H_r` holds outright is
that image itself: the generic-point condition over a scheme over `S` says exactly that the
image is everything
(`AlgebraicGeometry.FreeAtGenericPointsSituation.condition_iff_baseRankLocus_eq_univ`), and the
image pulls back into the image of a further base change
(`AlgebraicGeometry.FreeAtGenericPointsSituation.preimage_baseRankLocus_subset`), so over the
open subscheme cut out by the image the condition holds.

### Universes

`F_d` is valued in `Type` and `H_p` in `Type u`, while sheafification on the big Zariski site
over `S` is available for `Type (u + 1)`. Both functors are therefore composed with
`CategoryTheory.uliftFunctor` before sheafifying. The resulting statement is an isomorphism of
sheaves, so it records naturality in `T` and not merely a bijection at each `T`.

## References

* [Stacks Project, Tag 05UE](https://stacks.math.columbia.edu/tag/05UE)
* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
* [Stacks Project, Tag 05MV](https://stacks.math.columbia.edu/tag/05MV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace FreeAtGenericPointsSituation

/-- Zariski sheaves of `Type (u + 1)` on schemes over `S` have all colimits of size `u + 1`. -/
noncomputable local instance sheafHasColimits (S : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (Scheme.zariskiTopology.over S) (Type (u + 1))) :=
  Sheaf.instHasColimitsOfSize

variable (D : FreeAtGenericPointsSituation.{u})

/-! ### Covering sieves from open neighbourhoods -/

/-- A sieve on a scheme over `S` which contains an open neighbourhood of each point covers: the
chosen neighbourhoods are an open cover. -/
theorem sieve_mem_of_forall_exists_mem {S : Scheme.{u}} (T : Over S) (R : Sieve T)
    (h : ∀ t : T.left, ∃ U : T.left.Opens, t ∈ U ∧
      R (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T)) :
    R ∈ (Scheme.zariskiTopology.over S) T := by
  classical
  choose U ht hU using h
  have hc : IsOpenCover U := .of_sets (fun t ↦ (U t).isOpen) (by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨x, ht x⟩)
  rw [GrothendieckTopology.mem_over_iff, Scheme.mem_grothendieckTopology_iff]
  refine ⟨T.left.openCoverOfIsOpenCover U hc, ?_⟩
  rintro Y f ⟨i⟩
  exact (Sieve.overEquiv_iff R _).2 (hU i)

/-! ### Disjointness of the generic-rank conditions -/

/-- **The `H_p` are pairwise disjoint over any scheme over `S` with a point.** The fibre over a
point of `T` is irreducible, hence has a generic point, and the rank of a module free of finite
rank near a point is determined. -/
theorem condition_rank_unique (T : Over D.S) (t : T.left) {r s : ℕ}
    (hr : D.Condition r T) (hs : D.Condition s T) : r = s := by
  obtain ⟨ξ, hξ⟩ := D.exists_isGenericPoint_fiber_baseChangeMap T t
  exact freeAtPointOfRank_unique (D.baseChangeModule T) (hr t ξ hξ) (hs t ξ hξ)

/-! ### The bound on the ranks that occur -/

/-- **The bound `c` of Stacks Project, Tag 05UE** for the situation of Stacks 05MP on an affine
total space: no base change of the module is free of rank greater than `c` near any point. -/
theorem exists_forall_freeAtPointOfRank_le [IsAffine D.X] :
    ∃ c : ℕ, ∀ (Y : Scheme.{u}) (g : Y ⟶ D.X) (y : Y) (r : ℕ),
      FreeAtPointOfRank ((Scheme.Modules.pullback g).obj D.F) y r → r ≤ c :=
  exists_rank_bound_of_compactSpace D.F

/-- **`H_p = ∅` for `p > c`.** If no pullback of the module is free of rank greater than `c`
near any point, then the generic-point condition of rank `p > c` fails over every scheme over
`S` that has a point. -/
theorem condition_eq_empty_of_gt (c : ℕ)
    (hc : ∀ (Y : Scheme.{u}) (g : Y ⟶ D.X) (y : Y) (r : ℕ),
      FreeAtPointOfRank ((Scheme.Modules.pullback g).obj D.F) y r → r ≤ c)
    {p : ℕ} (hp : c < p) (T : Over D.S) (t : T.left) : ¬ D.Condition p T := by
  intro h
  obtain ⟨ξ, hξ⟩ := D.exists_isGenericPoint_fiber_baseChangeMap T t
  exact absurd (hc _ (pullback.fst D.f T.hom) _ p (h t ξ hξ)) (not_le.mpr hp)

/-! ### Local surjectivity of the comparison map -/

/-- The generic-point condition of rank `r` holds over an open subscheme of `T` whose points
are exactly the image of the free-rank locus: that image pulls back into the image for a
further base change, so over the open it is everything. -/
theorem condition_of_baseRankLocus_eq (r : ℕ) (T : Over D.S) (V : T.left.Opens)
    (hV : (V : Set T.left) = D.baseRankLocus r T) :
    D.Condition r (Over.mk (V.ι ≫ T.hom)) := by
  rw [D.condition_iff_baseRankLocus_eq_univ, Set.eq_univ_iff_forall]
  intro v
  refine D.preimage_baseRankLocus_subset r (Over.homMk V.ι : Over.mk (V.ι ≫ T.hom) ⟶ T) ?_
  exact hV ▸ v.2

/-- **Local surjectivity.** A point of `T` at which `F_T` is flat over `T` in dimensions `≥ d`
has an open neighbourhood over which the generic-point condition of some rank `r ≤ c` holds
outright. -/
theorem exists_open_condition_of_isFlatInDimensionsGE [IsAffine D.X] [IsAffine D.S]
    [D.F.IsFinitePresentation] {d : ℕ} (hd : RelativeDimension D.f d) (c : ℕ)
    (hc : ∀ (Y : Scheme.{u}) (g : Y ⟶ D.X) (y : Y) (r : ℕ),
      FreeAtPointOfRank ((Scheme.Modules.pullback g).obj D.F) y r → r ≤ c)
    (T : Over D.S)
    (hflat : (D.toFlatDimensionSituation d).IsFlatInDimensionsGEAfterBaseChange T)
    (t : T.left) :
    ∃ (V : T.left.Opens), t ∈ V ∧ ∃ r : Fin (c + 1),
      D.Condition r.val (Over.mk (V.ι ≫ T.hom)) := by
  obtain ⟨r, y, hy, hyt⟩ := D.exists_mem_baseRankLocus hd T hflat t
  exact ⟨⟨D.baseRankLocus r T, D.isOpen_baseRankLocus r T⟩, ⟨y, hy, hyt⟩,
    ⟨r, Nat.lt_succ_of_le (hc _ (pullback.fst D.f T.hom) y r hy)⟩,
    D.condition_of_baseRankLocus_eq r T _ rfl⟩

/-! ### The pointwise disjoint union of the `H_p` -/

/-- The pointwise disjoint union of the functors `H_p` for `p ≤ c`, lifted to the universe in
which the big Zariski site over `S` has sheafification. -/
noncomputable def rankSumFunctor (c : ℕ) : (Over D.S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Σ p : Fin (c + 1), (D.freeAtGenericPointsFunctor p.val ⋙ uliftFunctor.{u + 1}).obj T
  map g := ↾fun x ↦ ⟨x.1,
    (D.freeAtGenericPointsFunctor x.1.val ⋙ uliftFunctor.{u + 1}).map g x.2⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The pointwise disjoint union, with the inclusions of its summands. -/
noncomputable def rankSumCofan (c : ℕ) :
    Cofan (fun p : Fin (c + 1) ↦
      D.freeAtGenericPointsFunctor p.val ⋙ uliftFunctor.{u + 1}) :=
  Cofan.mk (D.rankSumFunctor c) fun p ↦
    { app := fun _ ↦ ↾fun x ↦ ⟨p, x⟩
      naturality := by intros; rfl }

/-- The pointwise disjoint union is the coproduct of the `H_p` as presheaves: a coproduct of
presheaves is computed pointwise, and a disjoint union of sets is their coproduct. -/
noncomputable def rankSumCofanIsColimit (c : ℕ) : IsColimit (D.rankSumCofan c) := by
  apply evaluationJointlyReflectsColimits
  intro T
  refine { desc := fun s ↦ ↾fun x ↦ s.ι.app ⟨x.1⟩ x.2, fac := ?_, uniq := ?_ }
  · intro s j
    ext x
    cases j
    rfl
  · intro s m hm
    ext ⟨p, x⟩
    exact ConcreteCategory.congr_hom (hm ⟨p⟩) x

/-! ### The comparison map and its local bijectivity -/

/-- The inclusion `H_p ⊆ F_d` of the source, as a morphism of presheaves on `Sch/S`. -/
noncomputable def conditionToFlatDimension [D.F.IsFinitePresentation] {d : ℕ}
    (hd : RelativeDimension D.f d) (p : ℕ) :
    D.freeAtGenericPointsFunctor p ⋙ uliftFunctor.{u + 1} ⟶
      (D.toFlatDimensionSituation d).flatDimensionFunctor ⋙ uliftFunctor.{u + 1} where
  app T := ↾fun x ↦ ⟨⟨D.isFlatInDimensionsGEAfterBaseChange_of_condition hd p T.unop
    x.down.down.down⟩⟩
  naturality := by
    intros
    ext x
    rfl

/-- The comparison map `∐_{p ≤ c} H_p ⟶ F_d`, assembled from the inclusions. -/
noncomputable def rankSumToFlatDimension [D.F.IsFinitePresentation] {d : ℕ}
    (hd : RelativeDimension D.f d) (c : ℕ) :
    D.rankSumFunctor c ⟶
      (D.toFlatDimensionSituation d).flatDimensionFunctor ⋙ uliftFunctor.{u + 1} where
  app T := ↾fun x ↦ (D.conditionToFlatDimension hd x.1.val).app T x.2
  naturality := by
    intros
    ext x
    rfl

/-- The comparison map is locally injective: at a scheme over `S` with a point the `H_p` are
disjoint and their values are singletons, and a scheme without a point is covered by the empty
sieve. -/
theorem isLocallyInjective_rankSumToFlatDimension [D.F.IsFinitePresentation] {d : ℕ}
    (hd : RelativeDimension D.f d) (c : ℕ) :
    Presheaf.IsLocallyInjective (Scheme.zariskiTopology.over D.S)
      (D.rankSumToFlatDimension hd c) := by
  refine ⟨fun {T} x y _ ↦ sieve_mem_of_forall_exists_mem _ _ fun t ↦ ?_⟩
  obtain ⟨p, x⟩ := x
  obtain ⟨q, y⟩ := y
  obtain rfl : p = q :=
    Fin.ext (D.condition_rank_unique T.unop t x.down.down.down y.down.down.down)
  obtain ⟨⟨⟨hx⟩⟩⟩ := x
  obtain ⟨⟨⟨hy⟩⟩⟩ := y
  exact ⟨⊤, trivial, rfl⟩

/-- The comparison map is locally surjective: this is the content of Stacks 05UE, that flatness
in dimensions `≥ d` is locally the condition of having a fixed generic rank at most `c`. -/
theorem isLocallySurjective_rankSumToFlatDimension [IsAffine D.X] [IsAffine D.S]
    [D.F.IsFinitePresentation] {d : ℕ} (hd : RelativeDimension D.f d) (c : ℕ)
    (hc : ∀ (Y : Scheme.{u}) (g : Y ⟶ D.X) (y : Y) (r : ℕ),
      FreeAtPointOfRank ((Scheme.Modules.pullback g).obj D.F) y r → r ≤ c) :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over D.S)
      (D.rankSumToFlatDimension hd c) := by
  refine ⟨fun {T} h ↦ sieve_mem_of_forall_exists_mem _ _ fun t ↦ ?_⟩
  obtain ⟨V, ht, r, hr⟩ := D.exists_open_condition_of_isFlatInDimensionsGE hd c hc
    T h.down.down t
  exact ⟨V, ht, ⟨r, ⟨⟨⟨hr⟩⟩⟩⟩, rfl⟩

/-! ### The decomposition -/

/-- Let `f : X ⟶ S` be a smooth morphism of affine schemes with geometrically irreducible fibres
of dimension `d` and let `F` be a quasi-coherent `𝒪_X`-module of finite presentation. Then
there is a `c ≥ 0` with
```
F_d = ∐_{p = 0, …, c} H_p
```
where `F_d` is the functor of flatness in dimensions `≥ d` of Stacks 05MT and `H_p` is the
functor of Stacks 05MP, the coproduct being taken in Zariski sheaves over `S`.

The comparison map out of the pointwise disjoint union is locally bijective, hence becomes an
isomorphism after sheafification, and sheafification preserves coproducts.

Sheafifying the left-hand side too is not a weakening: `F_d` is an fpqc sheaf by Stacks 05MV,
a fortiori a Zariski sheaf, so it is isomorphic to its own sheafification. It is written
sheafified here only so that the statement takes no input from that tag. -/
@[stacks 05UE]
theorem flatDimensionFunctor_iso_coproduct_freeAtGenericPointsFunctor [IsAffine D.X]
    [IsAffine D.S] [D.F.IsFinitePresentation] {d : ℕ} (hd : RelativeDimension D.f d) :
    ∃ c : ℕ, Nonempty
      ((presheafToSheaf (Scheme.zariskiTopology.over D.S) (Type (u + 1))).obj
          ((D.toFlatDimensionSituation d).flatDimensionFunctor ⋙ uliftFunctor.{u + 1}) ≅
        ∐ fun p : Fin (c + 1) ↦
          (presheafToSheaf (Scheme.zariskiTopology.over D.S) (Type (u + 1))).obj
            (D.freeAtGenericPointsFunctor p.val ⋙ uliftFunctor.{u + 1})) := by
  obtain ⟨c, hc⟩ := D.exists_forall_freeAtPointOfRank_le
  have hinj := D.isLocallyInjective_rankSumToFlatDimension hd c
  have hsurj := D.isLocallySurjective_rankSumToFlatDimension hd c hc
  have hiso : IsIso ((presheafToSheaf (Scheme.zariskiTopology.over D.S)
      (Type (u + 1))).map (D.rankSumToFlatDimension hd c)) :=
    ((Scheme.zariskiTopology.over D.S).W_iff (D.rankSumToFlatDimension hd c)).mp
      ((Scheme.zariskiTopology.over D.S).W_of_isLocallyBijective
        (D.rankSumToFlatDimension hd c))
  have hsum : D.rankSumFunctor c ≅
      ∐ fun p : Fin (c + 1) ↦
        D.freeAtGenericPointsFunctor p.val ⋙ uliftFunctor.{u + 1} :=
    (D.rankSumCofanIsColimit c).coconePointUniqueUpToIso (coproductIsCoproduct _)
  exact ⟨c, ⟨(asIso ((presheafToSheaf (Scheme.zariskiTopology.over D.S)
      (Type (u + 1))).map (D.rankSumToFlatDimension hd c))).symm ≪≫
    (presheafToSheaf (Scheme.zariskiTopology.over D.S) (Type (u + 1))).mapIso hsum ≪≫
    PreservesCoproduct.iso _ _⟩⟩

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end
