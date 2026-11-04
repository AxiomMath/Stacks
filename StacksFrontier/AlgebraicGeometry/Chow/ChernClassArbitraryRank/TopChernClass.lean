module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.Completion
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.TopChernClass
public import StacksCore.Tactic.StacksAttribute

/-!
# The top Chern class of a finite locally free module of nonconstant rank

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let `ℰ` be a
finite locally free `𝒪_X`-module. Write `X = ∐_r X_r` for the decomposition of `X` into the open
and closed loci where the rank of `ℰ` is `r` (Stacks 0ESW). **Stacks 0FA4** sets

  `c_top(ℰ) = Σ_r c_r(ℰ|_{X_r}) ∈ A^*(X) = ⊕ A^*(X_r)`

when only finitely many `X_r` are nonempty, and

  `c_top(ℰ) = ∏_r c_r(ℰ|_{X_r}) ∈ ∏_r A^r(X_r) ⊂ A^*(X)^∧`

in general. Here `c_r(ℰ|_{X_r}) ∈ A^r(X_r)` is the bivariant Chern class of Stacks 0B7H of the
module `ℰ|_{X_r}`, which has constant rank `r`; the identifications are Stacks 0FDZ, which gives
`A^p(X) = ∏_r A^p(X_r)`, and Stacks 0FE0, which realizes `A^*(X)^∧` inside `∏_p A^p(X)`.

So the degree `p` part of `c_top(ℰ)` is the class in `A^p(X)` whose restriction to `X_r` is
`c_r(ℰ|_{X_r})` if `p = r` and `0` otherwise. On a connected component of `X` the rank is a
constant `r`, so this tuple of classes vanishes there in every degree but `r`: it is an element of
the completed group, and when only finitely many ranks occur, of the graded group itself.

All classes are bivariant classes for the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of
the first Chern class of an invertible module, for which every compatibility used by Stacks 0FDZ
is a theorem, and the Chern classes are the classes `Stacks.Chow.GenuineChern.chernClass` built
from the cap products of Stacks 02U6.

## Main definitions

* `Stacks.Chow.rankLocusTopChernClass` — the class `c_r(ℰ|_{X_r}) ∈ A^r(X_r)`.
* `Stacks.Chow.rankLocusTopChernFamily` — the family on the rank loci in degree `p`:
  `c_r(ℰ|_{X_r})` on `X_r` if `p = r`, zero otherwise.
* `Stacks.Chow.topChernClassComponent` — the degree `p` part of `c_top(ℰ)` in `A^p(X)`.
* `Stacks.Chow.topChernClassOfFinite` — **Stacks 0FA4**, the class `c_top(ℰ) ∈ A^*(X)` when only
  finitely many rank loci are nonempty.
* `Stacks.Chow.topChernClassCompleted` — **Stacks 0FA4**, the class `c_top(ℰ) ∈ A^*(X)^∧`.

## Main results

* `Stacks.Chow.bivariantPieceRestriction_eq_zero_of_le` — a bivariant class restricting to zero on
  a piece of a decomposition restricts to zero on every smaller piece of another one.
* `Stacks.Chow.bivariantConnectedComponentRestriction_topChernClassComponent` — on a connected
  component on which the rank is `r`, the degree `p` part of `c_top(ℰ)` vanishes for `p ≠ r`.
* `Stacks.Chow.topChernClassComponent_eq_zero` — the degree `p` part vanishes unless `X_p` is
  nonempty.
* `Stacks.Chow.completedBivariantSequenceOfInvertible_topChernClassCompleted_eq` — when only
  finitely many rank loci are nonempty the two classes agree: the completed class is the image of
  the graded one.

## References

* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Restriction to a smaller piece -/

section PieceRefinement

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I J I' J' : Type u} (UX : I → X.Opens)
  (UY : J → Y.Opens) (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (i : I)
  (UX' : I' → X.Opens) (UY' : J' → Y.Opens) (a' : I' → J')
  (ha' : ∀ i, UX' i ≤ f ⁻¹ᵁ UY' (a' i)) (i' : I')
  (hX : UX i ≤ UX' i') (hY : UY (a i) ≤ UY' (a' i')) {T : Scheme.{u}}
  (g : T ⟶ (UY (a i) : Scheme.{u}))

/-- For a piece `X_i ⟶ Y_{a(i)}` contained in a piece `X'_{i'} ⟶ Y'_{a'(i')}` of a second
decomposition, the inclusion `X_i ×_{Y_{a(i)}} T ⟶ X'_{i'} ×_{Y'_{a'(i')}} T` of the base changes
along a test morphism `g : T ⟶ Y_{a(i)}`. -/
def pieceRefinementMap :
    pullback (pieceMap f UX UY a ha i) g ⟶
      pullback (pieceMap f UX' UY' a' ha' i') (g ≫ Y.homOfLE hY) :=
  pullback.lift (pullback.fst _ _ ≫ X.homOfLE hX) (pullback.snd _ _) (by
    rw [← cancel_mono (UY' (a' i')).ι]
    simp only [Category.assoc, pieceMap_comp_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]
    rw [← pieceMap_comp_ι f UX UY a ha i, pullback.condition_assoc])

/-- The first projection of `pieceRefinementMap` is the first projection followed by the inclusion
`X_i ⟶ X'_{i'}`. -/
theorem pieceRefinementMap_fst :
    pieceRefinementMap f UX UY a ha i UX' UY' a' ha' i' hX hY g ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ X.homOfLE hX :=
  pullback.lift_fst _ _ _

/-- The second projection of `pieceRefinementMap` is the second projection to `T`. -/
theorem pieceRefinementMap_snd :
    pieceRefinementMap f UX UY a ha i UX' UY' a' ha' i' hX hY g ≫ pullback.snd _ _ =
      pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- Composing `g : T ⟶ Y_{a(i)}` with the inclusion into `Y'_{a'(i')}` and then into `Y` is `g`
followed by the inclusion of `Y_{a(i)}` into `Y`. -/
theorem homOfLE_comp_ι_eq : (g ≫ Y.homOfLE hY) ≫ (UY' (a' i')).ι = g ≫ (UY (a i)).ι := by
  rw [Category.assoc, Scheme.homOfLE_ι]

/-- The comparison of the smaller piece factors through the comparison of the larger one. -/
theorem pieceRefinementMap_comp_pieceComparisonCongr :
    pieceRefinementMap f UX UY a ha i UX' UY' a' ha' i' hX hY g ≫
        pieceComparisonCongr f UX' UY' a' ha' i' (g ≫ Y.homOfLE hY) (g ≫ (UY (a i)).ι)
          (homOfLE_comp_ι_eq UY a i UY' a' i' hY g) =
      pieceComparison f UX UY a ha i g := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pieceComparisonCongr_fst, reassoc_of% pieceRefinementMap_fst,
      Scheme.homOfLE_ι, opensPullbackComparison_fst]
  · rw [Category.assoc, pieceComparisonCongr_snd, pieceRefinementMap_snd,
      opensPullbackComparison_snd]

/-- The map `pieceRefinementMap` is an open immersion. -/
instance isOpenImmersion_pieceRefinementMap :
    IsOpenImmersion (pieceRefinementMap f UX UY a ha i UX' UY' a' ha' i' hX hY g) := by
  have : IsOpenImmersion (pieceRefinementMap f UX UY a ha i UX' UY' a' ha' i' hX hY g ≫
      pieceComparisonCongr f UX' UY' a' ha' i' (g ≫ Y.homOfLE hY) (g ≫ (UY (a i)).ι)
        (homOfLE_comp_ι_eq UY a i UY' a' i' hY g)) := by
    rw [pieceRefinementMap_comp_pieceComparisonCongr]
    infer_instance
  exact IsOpenImmersion.of_comp _
    (pieceComparisonCongr f UX' UY' a' ha' i' (g ≫ Y.homOfLE hY) (g ≫ (UY (a i)).ι)
      (homOfLE_comp_ι_eq UY a i UY' a' i' hY g))

variable (C : ChowSituation.{u}) (G : GysinSystem C) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
  (hgys : G.IsNaturalUnderOpenImmersion)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] in
/-- The map `pieceRefinementMap` commutes with the structure morphisms of both base changes to
`C.S`. -/
theorem pieceRefinementMap_comp_structureMorphism :
    pieceRefinementMap f UX UY a ha i UX' UY' a' ha' i' hX hY g ≫
        (pullback.fst (pieceMap f UX' UY' a' ha' i') (g ≫ Y.homOfLE hY) ≫ ((UX' i').ι ≫ sX)) =
      pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX) := by
  rw [reassoc_of% pieceRefinementMap_fst, Scheme.homOfLE_ι_assoc]

include hX hY in
/-- **Stacks 0FDZ, refinement.** If a bivariant class restricts to zero on a piece
`X'_{i'} ⟶ Y'_{a'(i')}` of one decomposition, it restricts to zero on every piece
`X_i ⟶ Y_{a(i)}` of another decomposition with `X_i ⊆ X'_{i'}` and `Y_{a(i)} ⊆ Y'_{a'(i')}`: both
restrictions are restrictions of the cap operations of the class along open immersions, and the
one for the smaller piece factors through the one for the larger. -/
theorem bivariantPieceRestriction_eq_zero_of_le (c : BivariantClass C G sX sY f hf p)
    (h : bivariantPieceRestriction C G sX sY f hf p UX' UY' a' ha' i' hgys c = 0) :
    bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgys c = 0 := by
  refine BivariantClass.ext C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY) (pieceMap f UX UY a ha i)
    (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i) p ?_
  intro T g _ k β
  have hm := homOfLE_comp_ι_eq UY a i UY' a' i' hY g
  have hY' : (g ≫ Y.homOfLE hY) ≫ ((UY' (a' i')).ι ≫ sY) = g ≫ ((UY (a i)).ι ≫ sY) :=
    (reassoc_of% hm) sY
  have hmY := hY'.trans (Category.assoc _ _ _).symm
  have h0 := congrArg (fun d ↦ d.cap (g ≫ Y.homOfLE hY) k (chowGroupCongr C hY'.symm k β)) h
  simp only [bivariantPieceRestriction_cap, BivariantClass.zero_cap] at h0
  rw [bivariantPieceRestrictionCap_eq C G sX sY f hf p UX' UY' a' ha' i' c (g ≫ Y.homOfLE hY)
    (g ≫ (UY (a i)).ι) hm hmY
    (pieceComparisonCongr f UX' UY' a' ha' i' (g ≫ Y.homOfLE hY) (g ≫ (UY (a i)).ι) hm)
    (pieceComparisonCongr_fst _ _ _ _ _ _ _ _ _) (pieceComparisonCongr_snd _ _ _ _ _ _ _ _ _) k
    (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ _ sX),
    chowGroupCongr_chowGroupCongr] at h0
  have hφ := pieceRefinementMap_comp_pieceComparisonCongr f UX UY a ha i UX' UY' a' ha' i' hX hY g
  have hvw : (pieceRefinementMap f UX UY a ha i UX' UY' a' ha' i' hX hY g ≫
      pieceComparisonCongr f UX' UY' a' ha' i' (g ≫ Y.homOfLE hY) (g ≫ (UY (a i)).ι) hm) ≫
        (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX) =
      pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX) := by
    rw [hφ]
    exact pieceComparison_comp_structureMorphism _ _ _ _ _ _ _ _
  rw [bivariantPieceRestriction_cap, BivariantClass.zero_cap, bivariantPieceRestrictionCap_apply,
    chowGroupRestrict_congr C _ _ _ _ _
      (pieceRefinementMap f UX UY a ha i UX' UY' a' ha' i' hX hY g ≫
        pieceComparisonCongr f UX' UY' a' ha' i' (g ≫ Y.homOfLE hY) (g ≫ (UY (a i)).ι) hm)
      hφ.symm hvw,
    ← chowGroupRestrict_comp C _ _ _
      (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ _ sX) _ _ _
      (pieceRefinementMap_comp_structureMorphism f UX UY a ha i UX' UY' a' ha' i' hX hY g C sX)]
  exact (congrArg _ h0).trans (map_zero _)

end PieceRefinement

/-! ### Bivariant classes on an empty scheme -/

/-- A bivariant class for a morphism out of an empty scheme is zero: every base change of it is
empty, and so are the Chow groups its cap operations land in. -/
theorem BivariantClass.subsingleton_of_isEmpty (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y : Scheme.{u}} [IsEmpty X] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ) :
    Subsingleton (BivariantClass C G sX sY f hf p) :=
  ⟨fun c d ↦ BivariantClass.ext C G sX sY f hf p fun {T} g _ k α ↦ by
    have : IsEmpty ↥(pullback f g) := ⟨fun t ↦ isEmptyElim ((pullback.fst f g).base t)⟩
    have := subsingleton_chowGroup_of_isEmpty C (pullback.fst f g ≫ sX) (k - p)
    exact Subsingleton.elim _ _⟩

/-! ### The top Chern class -/

section TopChernClass

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The top Chern class `c_r(ℰ|_{X_r}) ∈ A^r(X_r)` of the restriction of `ℰ` to its rank-`r`
locus, where it has constant rank `r`: the bivariant Chern class of Stacks 0B7H. -/
def rankLocusTopChernClass (r : ℕ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) ((rankLocus E r).ι ≫ sX) (r : ℤ) :=
  letI := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  GenuineChern.chernClass C ((rankLocus E r).ι ≫ sX)
    ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r (Fin.last r)

/-- The family on the rank loci of the degree `p` part of the top Chern class: `c_r(ℰ|_{X_r})` on
`X_r` when `p = r`, and zero on `X_r` when `p ≠ r`. -/
def rankLocusTopChernFamily (p : ℤ) (r : ℕ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) ((rankLocus E r).ι ≫ sX) p :=
  if h : (r : ℤ) = p then h ▸ rankLocusTopChernClass C sX E r else 0

/-- In degree `r`, the family on the rank-`r` locus is the top Chern class `c_r(ℰ|_{X_r})`. -/
theorem rankLocusTopChernFamily_self (r : ℕ) :
    rankLocusTopChernFamily C sX E (r : ℤ) r = rankLocusTopChernClass C sX E r :=
  dite_eq_left rfl

/-- In a degree `p ≠ r`, the family on the rank-`r` locus is zero. -/
theorem rankLocusTopChernFamily_of_ne {p : ℤ} {r : ℕ} (h : (r : ℤ) ≠ p) :
    rankLocusTopChernFamily C sX E p r = 0 :=
  dite_eq_right h

/-- On an empty rank locus the family vanishes, there being no nonzero class at all. -/
theorem rankLocusTopChernFamily_of_not_nonempty (p : ℤ) {r : ℕ}
    (hr : ¬ (rankLocus E r : Set X).Nonempty) : rankLocusTopChernFamily C sX E p r = 0 := by
  have : IsEmpty (rankLocus E r : Scheme.{u}) := ⟨fun x ↦ hr ⟨x.1, x.2⟩⟩
  have := BivariantClass.subsingleton_of_isEmpty C (gysinSystemOfInvertible C)
    ((rankLocus E r).ι ≫ sX) ((rankLocus E r).ι ≫ sX) (𝟙 _) (Category.id_comp _) p
  exact Subsingleton.elim _ _

/-- The degree `p` part of the top Chern class, `c_top(ℰ)_p ∈ A^p(X)`: the class whose restriction
to `X_r` is `c_r(ℰ|_{X_r})` if `p = r` and zero otherwise, which exists and is unique by
Stacks 0FDZ. -/
def topChernClassComponent (p : ℤ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
  rankLocusAssembly C (gysinSystemOfInvertible C) sX E
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) p (rankLocusTopChernFamily C sX E p)

/-- The restriction of `c_top(ℰ)_p` to `X_r` is the `r`-th member of the family. -/
theorem rankLocusRestriction_topChernClassComponent (p : ℤ) (r : ℕ) :
    rankLocusRestriction C (gysinSystemOfInvertible C) sX E
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p
        (topChernClassComponent C sX E p) r =
      rankLocusTopChernFamily C sX E p r :=
  rankLocusRestriction_rankLocusAssembly C (gysinSystemOfInvertible C) sX E _ _ _ p _ r

/-- `c_top(ℰ)_p` is the only class of degree `p` with these restrictions to the rank loci. -/
theorem eq_topChernClassComponent {p : ℤ}
    {c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p}
    (h : ∀ r : ℕ, rankLocusRestriction C (gysinSystemOfInvertible C) sX E
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p c r =
        rankLocusTopChernFamily C sX E p r) :
    c = topChernClassComponent C sX E p :=
  eq_of_rankLocusRestriction_eq C (gysinSystemOfInvertible C) sX E
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) p fun r ↦
      (h r).trans (rankLocusRestriction_topChernClassComponent C sX E p r).symm

/-- The degree `p` part of the top Chern class vanishes unless the rank-`p` locus is nonempty. -/
theorem topChernClassComponent_eq_zero {p : ℤ}
    (hp : ∀ r : ℕ, (rankLocus E r : Set X).Nonempty → (r : ℤ) ≠ p) :
    topChernClassComponent C sX E p = 0 := by
  have h0 : rankLocusTopChernFamily C sX E p = 0 := funext fun r ↦ by
    by_cases hr : (rankLocus E r : Set X).Nonempty
    · exact rankLocusTopChernFamily_of_ne C sX E (hp r hr)
    · exact rankLocusTopChernFamily_of_not_nonempty C sX E p hr
  rw [topChernClassComponent, h0]
  exact map_zero (rankLocusChowCohomologyEquiv C (gysinSystemOfInvertible C) sX E
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) p).symm

/-- The image of a connected component under the identity is that component. -/
theorem connectedComponentsMap_id_apply (i : _root_.ConnectedComponents X) :
    (Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i = i := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  rfl

/-- A connected component of `X` lies in the rank locus of the rank of `ℰ` on it. -/
theorem connectedComponentOpens_le_rankLocus [IsLocallyNoetherian X]
    (i : _root_.ConnectedComponents X) :
    X.connectedComponentOpens i ≤
      rankLocus E (Scheme.Modules.rankOnConnectedComponent E i) :=
  Scheme.Modules.connectedComponentOpens_le_rankStratum E i

/-- **Stacks 0FA4, componentwise.** On a connected component `X_i` of `X` on which `ℰ` has rank
`r`, the restriction of `c_top(ℰ)_p` vanishes for every `p ≠ r`: the component lies in `X_r`, on
which `c_top(ℰ)_p` restricts to zero. -/
theorem bivariantConnectedComponentRestriction_topChernClassComponent [IsLocallyNoetherian X]
    (i : _root_.ConnectedComponents X) {p : ℤ}
    (hp : p ≠ (Scheme.Modules.rankOnConnectedComponent E i : ℤ)) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (topChernClassComponent C sX E p) i = 0 := by
  set r := Scheme.Modules.rankOnConnectedComponent E i
  have h1 := rankLocusRestriction_topChernClassComponent C sX E p r
  rw [rankLocusTopChernFamily_of_ne C sX E (Ne.symm hp)] at h1
  have h2 := (AddEquiv.map_eq_zero_iff (pieceIdentityCongr C (gysinSystemOfInvertible C) sX
    (rankLociFamily E) (rankLociFamily_le_preimage E) p (ULift.up r)
    (pieceMap_comp_structureMorphism C sX sX (𝟙 X) (Category.id_comp sX) _ _ _ _ _))).1 h1
  have hX : X.connectedComponentOpens i ≤ rankLociFamily E (ULift.up r) :=
    connectedComponentOpens_le_rankLocus E i
  have hY : X.connectedComponentOpens ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i) ≤
      rankLociFamily E (id (ULift.up r)) := by
    rw [connectedComponentsMap_id_apply]
    exact hX
  exact bivariantPieceRestriction_eq_zero_of_le (𝟙 X) X.connectedComponentOpens
    X.connectedComponentOpens (Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap
    (Scheme.Hom.connectedComponentOpens_le_preimage (𝟙 X)) i (rankLociFamily E)
    (rankLociFamily E) id (rankLociFamily_le_preimage E) (ULift.up r) hX hY C
    (gysinSystemOfInvertible C) sX sX (Category.id_comp sX) p
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ h2

/-- The tuple `(c_top(ℰ)_p)_p` lies in the completed group: on each connected component it
vanishes in every degree but the rank there. -/
theorem topChernClassComponent_mem_completedBivariantSubgroup [IsLocallyNoetherian X] :
    topChernClassComponent C sX E ∈
      completedBivariantSubgroupOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) :=
  (mem_completedBivariantSubgroup C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX)
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _).2 fun i ↦
  (Set.finite_singleton (Scheme.Modules.rankOnConnectedComponent E i : ℤ)).subset fun p hp ↦ by
    by_contra hne
    exact hp (bivariantConnectedComponentRestriction_topChernClassComponent C sX E i hne)

/-- **Stacks 0FA4**, general case. The top Chern class
`c_top(ℰ) = ∏_r c_r(ℰ|_{X_r}) ∈ ∏_r A^r(X_r) ⊂ A^*(X)^∧` of a finite locally free module `ℰ` on
`X`, for the decomposition `X = ∐ X_r` by the rank of `ℰ`: the element of the completed bivariant
group of Stacks 0FE0 whose image `(c_p)_p ∈ ∏_p A^p(X)` has, under `A^p(X) = ∏_r A^p(X_r)` of
Stacks 0FDZ, the component `c_r(ℰ|_{X_r})` in `A^r(X_r)` and zero in `A^p(X_r)` for `p ≠ r`. -/
@[stacks 0FA4 "general case: c_top(E) = ∏ c_r(E|_{X_r}) ∈ ∏ A^r(X_r) ⊂ A^*(X)^∧"]
def topChernClassCompleted :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    {c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) //
      (∀ r : ℕ, rankLocusRestriction C (gysinSystemOfInvertible C) sX E
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (r : ℤ)
          (completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) c r) r =
        rankLocusTopChernClass C sX E r) ∧
      ∀ (p : ℤ) (r : ℕ), (r : ℤ) ≠ p →
        rankLocusRestriction C (gysinSystemOfInvertible C) sX E
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p
          (completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) c p) r =
        0} :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hseq := congrArg Subtype.val
    ((completedBivariantGroupEquivOfInvertible C sX sX (𝟙 X) (Category.id_comp sX)).apply_symm_apply
      ⟨topChernClassComponent C sX E, topChernClassComponent_mem_completedBivariantSubgroup C sX E⟩)
  ⟨(completedBivariantGroupEquivOfInvertible C sX sX (𝟙 X) (Category.id_comp sX)).symm
      ⟨topChernClassComponent C sX E, topChernClassComponent_mem_completedBivariantSubgroup C sX E⟩,
    fun r ↦ by
      rw [show completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) _ =
        topChernClassComponent C sX E from hseq, rankLocusRestriction_topChernClassComponent,
        rankLocusTopChernFamily_self],
    fun p r h ↦ by
      rw [show completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) _ =
        topChernClassComponent C sX E from hseq, rankLocusRestriction_topChernClassComponent,
        rankLocusTopChernFamily_of_ne C sX E h]⟩

/-- The completed top Chern class realizes the tuple `(c_top(ℰ)_p)_p` in `∏_p A^p(X)`. -/
theorem completedBivariantSequenceOfInvertible_topChernClassCompleted [IsLocallyNoetherian X] :
    completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX)
        (topChernClassCompleted C sX E).1 =
      topChernClassComponent C sX E :=
  congrArg Subtype.val
    ((completedBivariantGroupEquivOfInvertible C sX sX (𝟙 X) (Category.id_comp sX)).apply_symm_apply
      ⟨topChernClassComponent C sX E, topChernClassComponent_mem_completedBivariantSubgroup C sX E⟩)

/-- The completed top Chern class is the only element of the completed group with the
restrictions to the rank loci of Stacks 0FA4. -/
theorem eq_topChernClassCompleted [IsLocallyNoetherian X]
    {c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX)}
    (h : ∀ (p : ℤ) (r : ℕ), rankLocusRestriction C (gysinSystemOfInvertible C) sX E
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p
      (completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) c p) r =
        rankLocusTopChernFamily C sX E p r) :
    c = (topChernClassCompleted C sX E).1 :=
  completedBivariantSequence_injective C (gysinSystemOfInvertible C) sX sX (𝟙 X)
    (Category.id_comp sX) _ _ _ <| funext fun p ↦
      (eq_topChernClassComponent C sX E (h p)).trans
        (congrFun (completedBivariantSequenceOfInvertible_topChernClassCompleted C sX E) p).symm

/-- **Stacks 0FA4**, finite case. If only finitely many of the rank loci `X_r` are nonempty, the
top Chern class `c_top(ℰ) = Σ_r c_r(ℰ|_{X_r}) ∈ A^*(X) = ⊕ A^*(X_r)`: the element of the graded
group `A^*(X) = ⊕_p A^p(X)` that is the sum, over the ranks `r` that occur, of a class of degree
`r`, and whose degree `p` part has, under `A^p(X) = ∏_r A^p(X_r)` of Stacks 0FDZ, the component
`c_r(ℰ|_{X_r})` in `A^r(X_r)` and zero in `A^p(X_r)` for `p ≠ r`. -/
@[stacks 0FA4 "finite case: c_top(E) = Σ_r c_r(E|_{X_r}) ∈ A^*(X) = ⊕ A^*(X_r)"]
def topChernClassOfFinite (hfin : {r : ℕ | (rankLocus E r : Set X).Nonempty}.Finite) :
    {c : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) //
      c = ∑ r ∈ hfin.toFinset, DirectSum.of _ (r : ℤ) (c r) ∧
      (∀ r : ℕ, rankLocusRestriction C (gysinSystemOfInvertible C) sX E
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (r : ℤ) (c r) r =
        rankLocusTopChernClass C sX E r) ∧
      ∀ (p : ℤ) (r : ℕ), (r : ℤ) ≠ p →
        rankLocusRestriction C (gysinSystemOfInvertible C) sX E
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p (c p) r = 0} :=
  have happly : ∀ p : ℤ,
      (∑ r ∈ hfin.toFinset, DirectSum.of (fun p ↦ chowCohomologyComponent C
        (gysinSystemOfInvertible C) sX p) (r : ℤ) (topChernClassComponent C sX E r)) p =
        topChernClassComponent C sX E p := fun p ↦ by
    rw [DirectSum.sum_apply]
    by_cases hp : ∃ r : ℕ, (rankLocus E r : Set X).Nonempty ∧ (r : ℤ) = p
    · obtain ⟨r, hr, rfl⟩ := hp
      rw [Finset.sum_eq_single r]
      · exact DirectSum.of_eq_same (r : ℤ) _
      · intro b _ hb
        exact DirectSum.of_eq_of_ne (b : ℤ) (r : ℤ) _ fun he ↦ hb (Nat.cast_injective he).symm
      · intro h
        exact absurd (hfin.mem_toFinset.2 hr) h
    · have hp' : ∀ r : ℕ, (rankLocus E r : Set X).Nonempty → (r : ℤ) ≠ p :=
        fun r hr hrp ↦ hp ⟨r, hr, hrp⟩
      rw [topChernClassComponent_eq_zero C sX E hp', Finset.sum_eq_zero]
      intro b hb
      exact DirectSum.of_eq_of_ne (b : ℤ) p _ (hp' b (hfin.mem_toFinset.1 hb)).symm
  ⟨∑ r ∈ hfin.toFinset, DirectSum.of _ (r : ℤ) (topChernClassComponent C sX E r),
    by simp only [happly],
    fun r ↦ by rw [happly, rankLocusRestriction_topChernClassComponent,
      rankLocusTopChernFamily_self],
    fun p r h ↦ by rw [happly, rankLocusRestriction_topChernClassComponent,
      rankLocusTopChernFamily_of_ne C sX E h]⟩

/-- In the finite case the degree `p` part of `c_top(ℰ)` is `c_top(ℰ)_p`. -/
theorem topChernClassOfFinite_apply (hfin : {r : ℕ | (rankLocus E r : Set X).Nonempty}.Finite)
    (p : ℤ) : (topChernClassOfFinite C sX E hfin).1 p = topChernClassComponent C sX E p :=
  eq_topChernClassComponent C sX E fun r ↦ by
    by_cases h : (r : ℤ) = p
    · subst h
      rw [(topChernClassOfFinite C sX E hfin).2.2.1 r, rankLocusTopChernFamily_self]
    · rw [(topChernClassOfFinite C sX E hfin).2.2.2 p r h, rankLocusTopChernFamily_of_ne C sX E h]

/-- **Stacks 0FA4**, the two notations agree. When only finitely many rank loci are nonempty, the
completed top Chern class is the image of the graded one: both have the same degree `p` part in
`A^p(X)` for every `p`. -/
theorem completedBivariantSequenceOfInvertible_topChernClassCompleted_eq [IsLocallyNoetherian X]
    (hfin : {r : ℕ | (rankLocus E r : Set X).Nonempty}.Finite) (p : ℤ) :
    completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX)
        (topChernClassCompleted C sX E).1 p =
      (topChernClassOfFinite C sX E hfin).1 p :=
  (congrFun (completedBivariantSequenceOfInvertible_topChernClassCompleted C sX E) p).trans
    (topChernClassOfFinite_apply C sX E hfin p).symm

end TopChernClass

end Stacks.Chow

end
