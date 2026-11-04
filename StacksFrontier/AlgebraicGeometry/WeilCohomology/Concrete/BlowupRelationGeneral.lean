module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupFormulaGeneral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RegularImmersionGysinPiece
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupRelation
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition

/-!
# Lemma 0FIH for a smooth projective scheme which is not equidimensional

Let `b : X' ⟶ X` be the blowing up of a smooth projective scheme `X` over `k` in a smooth closed
subscheme `i : Z ⟶ X`, with exceptional divisor `j : E ⟶ X'` and `π : E ⟶ Z`. Assume that every
irreducible component of `Z` has codimension `r ≥ 1` in `X`, and that `α ∈ K_0(Vect(X))`
restricts to the class of `𝒞_{Z/X}`. `X` need not be equidimensional. With
`θ = c_{r-1}(b^*α^∨ - [𝒪_{X'}(E)]) ∩ [X'] ∈ CH^{r-1}(X')`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.blowupTheta`) we prove [Stacks, Tag 0FIH]:

  `b^![Z] = [E] · θ`   in `CH^r(X')`   and   `π_*(j^!θ) = [Z]`.

## The proof

Everything is computed part by part. Write `X_d`, `X'_d` for the parts of dimension `d`
(Stacks 02NM) and `E_d = E ×_{X'} X'_d` for the part of `E` over `X'_d`; then `X'_d = b⁻¹(X_d)`,
`Z ∩ X_d` has dimension `d - r` and `E_d` has dimension `d - 1`
(`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimensionParts`). Put
`γ_m = c_{r-1}(𝓕^∨) ∩ π^*[Z]_m ∈ CH_m(E)`.

* `π^*[Z]_m` restricts to `[E_d]_{m+r-1}` on `E_d` when `m = d - r` and to `0` otherwise, so
  `γ_{d-r}` is the pushforward of its restriction to `E_d`.
* On `X'_d`, `b^![Z]` is the restriction of `b^!(i_*[Z]_{d-r}) = j_*γ_{d-r}`, by the blow up
  formula on an arbitrary class of the centre
  (`capTarget_smoothGysinClass_blowupHom_of_codimension`).
* On `X'_d`, `[E] · θ = [E_d] · θ = (E_d ⟶ X')_*(c_{r-1} ∩ [E_d]) = j_*γ_{d-r}` by Tag 0FFE and
  0FF7 for the regular immersion `E_d ⟶ X'` of the equidimensional `E_d`.
* `j^!θ` on `E_d` is `c_{r-1}|_{E_d} ∩ [E_d] = γ_{d-r}|_{E_d}`, and
  `π_*γ_m = [Z]_m` (Stacks 02TW, the computation the source omits).

## The statement

The second relation is stated on each part: for every `e`, the Gysin map of `j` on the part
`X'_{e+1}` (`Stacks.Chow.regularImmersionPartGysin`) carries `θ` to a class of
`CH_{e-(r-1)}(E_{e+1})` whose pushforward to `Z` is `[Z]_{e-(r-1)}`. Since
`CH_*(E) = ⊕_d CH_*(E_d)`, `E_0 = ∅`, and `[Z] = ∑_m [Z]_m` with `[Z]_m` the sum of the
`m`-dimensional components, this family of equalities is the equality `π_*(j^!θ) = [Z]` in
`CH_*(Z) = ⊕_m CH_m(Z)`, `j^!θ` being supported on `E_{m+r}` in degree `m`.

The source writes `[Z]` in `CH^r(Z)`; `π_*j^!θ` has codimension `0` in `Z`, so `[Z]` is the
fundamental class of `Z`, i.e. `[Z] ∈ CH^0(Z)`.

## Main results

In namespace `Stacks.WeilCohomology.SmoothProjectiveScheme`:

* `codimensionGysin_closedSubschemeClass_heq_blowupTheta_of_codimension`: `b^![Z] = [E] · θ`.
* `properChowPushforward_regularImmersionPartGysin_blowupTheta`: `π_*(j^!θ) = [Z]`, part by part.
* `exists_blowup_relations`: **Lemma 0FIH**.

## References

* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
* [Stacks Project, Tag 0FVA](https://stacks.math.columbia.edu/tag/0FVA)
* [Stacks Project, Tag 0FFE](https://stacks.math.columbia.edu/tag/0FFE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-- **Capping with a class of Chow cohomology commutes with restriction along an open
immersion**: `(c ∩ γ)|_V = c|_V ∩ γ|_V`. -/
theorem chowGroupRestrict_chowCohomologyCap_of_isOpenImmersion (C : ChowSituation.{u})
    (G : GysinSystem C) (hgys : G.IsNaturalUnderBaseChangeIso) {Y V : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
    (j : V ⟶ Y) [IsOpenImmersion j] (hj : j ≫ sY = sV) (p : ℤ)
    (c : chowCohomologyComponent C G sY p) (k : ℤ) (γ : chowGroup C sY k) :
    chowGroupRestrict C sY sV j hj (k - p) (chowCohomologyCap C G sY p c k γ) =
      chowCohomologyCap C G sV p (chowCohomologyRestrictionOfEq C sV sY hj G hgys p c) k
        (chowGroupRestrict C sY sV j hj k γ) := by
  rw [← chowCohomologyCap_restrictionOfEq_id C G hgys sY p c k γ,
    chowGroupRestrict_chowCohomologyCap_restrictionOfEq C G hgys sY sY sV p (𝟙 Y)
      (Category.id_comp sY) j hj,
    chowCohomologyRestrictionOfEq_congr C G hgys sY p sV (Category.comp_id j)]

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

/-! ### The parts of the exceptional divisor -/

/-- The part `E_d = E ×_{X'} X'_d` of the exceptional divisor over the part of `X'` of
dimension `d`. -/
abbrev exceptionalPiece (d : ℕ) : Scheme.{u} :=
  Limits.pullback (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom d).ι

/-- The inclusion `E_d ⟶ E`, an open and closed immersion. -/
abbrev exceptionalPieceι (d : ℕ) : exceptionalPiece i d ⟶ (exceptionalObj i).obj.left :=
  pullback.fst (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom d).ι

/-- `E_d ⟶ E` is a closed immersion, `X'_d` being closed in `X'`. -/
instance isClosedImmersion_exceptionalPieceι (d : ℕ) :
    IsClosedImmersion (exceptionalPieceι i d) :=
  haveI := isClosedImmersion_ι_of_isClopen (isClopen_dimPart (blowupObj i) d)
  inferInstanceAs (IsClosedImmersion
    (pullback.fst (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom d).ι))

/-- The pieces `E_d` form a decomposition of `E` into open and closed subschemes. -/
theorem isClopenDecomposition_exceptionalPiece :
    IsClopenDecomposition fun d : ULift.{u} ℕ ↦ (exceptionalPieceι i d.down).opensRange :=
  isClopenDecomposition_pullbackFst_dimPart (blowupObj i).obj.hom (exceptionalHom i).hom.left

/-- **A class of `E` whose restrictions to the parts `E_{d'}`, `d' ≠ d`, vanish is the pushforward
of its restriction to `E_d`.** -/
theorem eq_properChowPushforward_chowGroupRestrict_exceptionalPiece (d : ℕ) (m : ℤ)
    (γ : chowGroup (fieldChowSituation k) (exceptionalObj i).obj.hom m)
    (h : ∀ d' : ℕ, d' ≠ d → chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
      (exceptionalPieceι i d' ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i d') rfl m γ = 0) :
    γ = properChowPushforward (fieldChowSituation k)
      (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalObj i).obj.hom
      (exceptionalPieceι i d) rfl m (properPushforwardDescends _ _ _ _ _ _)
      (chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i d) rfl m γ) := by
  have hdec := isClopenDecomposition_exceptionalPiece i
  refine (chowGroupClopenRestrictEquiv (fieldChowSituation k) (exceptionalObj i).obj.hom
    (fun d' : ULift.{u} ℕ ↦ exceptionalPieceι i d'.down ≫ (exceptionalObj i).obj.hom)
    (fun d' : ULift.{u} ℕ ↦ exceptionalPieceι i d'.down) (fun _ ↦ rfl) hdec m).injective
    (funext fun d' ↦ ?_)
  rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply]
  by_cases hd : d'.down = d
  · obtain ⟨d'⟩ := d'
    obtain rfl : d' = d := hd
    exact (chowGroupRestrict_properChowPushforward_self _ _ _ _ rfl m _ _).symm
  · rw [h d'.down hd]
    refine (chowGroupRestrict_properChowPushforward_of_disjoint _ _ _ _ _ rfl _ rfl ?_ m _ _).symm
    have hdis := hdec.disjoint ⟨d⟩ d' (fun h' ↦ hd (congrArg ULift.down h').symm)
    rw [disjoint_iff] at hdis
    rw [Set.disjoint_iff]
    intro x hx
    have hx' : x ∈ ((exceptionalPieceι i d).opensRange ⊓
        (exceptionalPieceι i d'.down).opensRange : (exceptionalObj i).obj.left.Opens) := hx
    rw [hdis] at hx'
    exact hx'

/-! ### The lift of `E_d ⟶ Z` to `Z ∩ X_d` -/

/-- The projection `E_d ⟶ Z ∩ X_d` of the part of the exceptional divisor over `X'_d` to the part
of the centre over `X_d`. -/
def exceptionalPieceToCentre (d : ℕ) : exceptionalPiece i d ⟶ (centrePart i d).toScheme :=
  IsOpenImmersion.lift (centrePart i d).ι (exceptionalPieceι i d ≫ (exceptionalProj i).hom.left)
    (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      exact exceptionalPiece_mem_dimPart i d t)

/-- `E_d ⟶ Z ∩ X_d ⟶ Z` is `E_d ⟶ E ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem exceptionalPieceToCentre_ι (d : ℕ) :
    exceptionalPieceToCentre i d ≫ (centrePart i d).ι =
      exceptionalPieceι i d ≫ (exceptionalProj i).hom.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- `E_d ⟶ Z ∩ X_d` is the base change of `E_d ⟶ Z` along the open immersion `Z ∩ X_d ⟶ Z`. -/
theorem isPullback_exceptionalPieceToCentre (d : ℕ) :
    IsPullback (𝟙 _) (exceptionalPieceToCentre i d)
      (exceptionalPieceι i d ≫ (exceptionalProj i).hom.left) (centrePart i d).ι :=
  IsPullback.of_horiz_isIso_mono ⟨by simp⟩

/-- `E_d ⟶ Z ∩ X_d` is flat. -/
instance (d : ℕ) : Flat (exceptionalPieceToCentre i d) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_exceptionalPieceToCentre i d)
    inferInstance

/-- `E_d ⟶ Z ∩ X_d` is locally of finite type. -/
instance (d : ℕ) : LocallyOfFiniteType (exceptionalPieceToCentre i d) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (isPullback_exceptionalPieceToCentre i d) inferInstance

/-! ### The flat pullback of `[Z]_m` on the parts of `E` -/

/-- Flat pullback along equal morphisms of equal relative dimensions. -/
theorem _root_.Stacks.Chow.flatPullbackChow_heq_of_hom_eq (C : ChowSituation.{u})
    {A W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] {f f' : A ⟶ W} [LocallyOfFiniteType f] [Flat f]
    [LocallyOfFiniteType f'] [Flat f'] (h : f = f') (hf : f ≫ sW = sA) (hf' : f' ≫ sW = sA)
    {r r' : ℕ} (hrr : r = r') (hr : AlgebraicGeometry.RelativeDimension f r)
    (hr' : AlgebraicGeometry.RelativeDimension f' r') (m : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sW f hf r hr m)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA sW f' hf' r' hr' m)
    (α : chowGroup C sW m) :
    flatPullbackChow C sA sW f hf r hr m hfac α ≍
      flatPullbackChow C sA sW f' hf' r' hr' m hfac' α := by
  subst h hrr
  rfl

variable {r : ℕ}
  (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
    Order.coheight (i.hom.left z) = r)

include hr in
/-- The part `E_d` is empty when `d < r`: it lies over `Z ∩ X_d`. -/
theorem isEmpty_exceptionalPiece_of_lt {d : ℕ} (hd : d < r) : IsEmpty (exceptionalPiece i d) :=
  ⟨fun t ↦ absurd (le_of_mem_centrePart i hr (exceptionalPiece_mem_dimPart i d t)) (by omega)⟩

/-- Any two classes of an empty part `E_d` agree. -/
private theorem chowGroup_exceptionalPiece_eq_of_isEmpty {d : ℕ} [IsEmpty (exceptionalPiece i d)]
    (n : ℤ) (a b : chowGroup (fieldChowSituation k)
      (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) n) : a = b :=
  have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
    (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) n
  Subsingleton.elim _ _

include hr in
/-- `E_d ⟶ Z ∩ X_d` has relative dimension `r - 1`, as `π` does. -/
theorem relativeDimension_exceptionalPieceToCentre (hr0 : 0 < r) (d : ℕ) :
    RelativeDimension (exceptionalPieceToCentre i d) (r - 1) := by
  have h := AlgebraicGeometry.RelativeDimension.comp_of_flat (exceptionalPieceι i d)
    (exceptionalProj i).hom.left (relativeDimension_of_isOpenImmersion _)
    (relativeDimension_exceptionalProj_of_codimension i hr hr0)
  rw [zero_add] at h
  exact RelativeDimension.of_isPullback (isPullback_exceptionalPieceToCentre i d) h

include hr in
/-- **The restriction of `π^*[Z]_m` to `E_d` is the flat pullback of `[Z ∩ X_d]_m` along
`E_d ⟶ Z ∩ X_d`.** -/
theorem chowGroupRestrict_flatPullbackChow_heq (hr0 : 0 < r) (d : ℕ) (m : ℤ) :
    chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i d) rfl
        (m + ((r - 1 : ℕ) : ℤ))
        (flatPullbackChow (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
          (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom) (r - 1)
          (relativeDimension_exceptionalProj_of_codimension i hr hr0) m
          (flatPullbackDescends _ _ _ _ _ _ _ m)
          (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m)) ≍
      flatPullbackChow (fieldChowSituation k) (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom)
        ((centrePart i d).ι ≫ Z.obj.hom) (exceptionalPieceToCentre i d)
        (by rw [exceptionalPieceToCentre_ι_assoc, Over.w (exceptionalProj i).hom]) (r - 1)
        (relativeDimension_exceptionalPieceToCentre i hr hr0 d) m
        (flatPullbackDescends _ _ _ _ _ _ _ m)
        (fundamentalChowClass (fieldChowSituation k) ((centrePart i d).ι ≫ Z.obj.hom) m) := by
  set fst := exceptionalPieceι i d
  set ψ := exceptionalPieceToCentre i d
  set ι := (centrePart i d).ι
  have hπ := relativeDimension_exceptionalProj_of_codimension i hr hr0
  have hψ := relativeDimension_exceptionalPieceToCentre i hr hr0 d
  have h1 := heq_chowGroupRestrict_flatPullbackChow (fieldChowSituation k)
    (exceptionalObj i).obj.hom (fst ≫ (exceptionalObj i).obj.hom) fst rfl
    (relativeDimension_of_isOpenImmersion fst) (m + ((r - 1 : ℕ) : ℤ))
    (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackChow (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
      (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom) (r - 1) hπ m
      (flatPullbackDescends _ _ _ _ _ _ _ m)
      (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m))
  have h2 := flatPullbackChow_comp (fieldChowSituation k) (fst ≫ (exceptionalObj i).obj.hom)
    (exceptionalObj i).obj.hom Z.obj.hom fst (exceptionalProj i).hom.left rfl
    (Over.w (exceptionalProj i).hom) 0 (r - 1) (relativeDimension_of_isOpenImmersion fst) hπ m
    (flatPullbackDescends _ _ _ _ _ _ _ _) (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackDescends _ _ _ _ _ _ _ _)
    (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m)
  have h3 := flatPullbackChow_heq_of_hom_eq (fieldChowSituation k)
    (fst ≫ (exceptionalObj i).obj.hom) Z.obj.hom (exceptionalPieceToCentre_ι i d).symm
    (by rw [Category.assoc, Over.w (exceptionalProj i).hom])
    (by rw [Category.assoc, exceptionalPieceToCentre_ι_assoc, Over.w (exceptionalProj i).hom])
    (show 0 + (r - 1) = r - 1 + 0 by omega)
    (AlgebraicGeometry.RelativeDimension.comp_of_flat fst (exceptionalProj i).hom.left
      (relativeDimension_of_isOpenImmersion fst) hπ)
    (AlgebraicGeometry.RelativeDimension.comp_of_flat ψ ι hψ
      (relativeDimension_of_isOpenImmersion ι)) m
    (flatPullbackDescends _ _ _ _ _ _ _ _) (flatPullbackDescends _ _ _ _ _ _ _ _)
    (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m)
  have h4 := flatPullbackChow_comp (fieldChowSituation k) (fst ≫ (exceptionalObj i).obj.hom)
    (ι ≫ Z.obj.hom) Z.obj.hom ψ ι
    (by rw [exceptionalPieceToCentre_ι_assoc, Over.w (exceptionalProj i).hom]) rfl (r - 1) 0 hψ
    (relativeDimension_of_isOpenImmersion ι) m
    (flatPullbackDescends _ _ _ _ _ _ _ _) (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackDescends _ _ _ _ _ _ _ _)
    (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m)
  have h5 := heq_chowGroupRestrict_flatPullbackChow (fieldChowSituation k) Z.obj.hom
    (ι ≫ Z.obj.hom) ι rfl (relativeDimension_of_isOpenImmersion ι) m
    (flatPullbackDescends _ _ _ _ _ _ _ _) (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m)
  rw [chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion] at h5
  refine h1.trans (h2.trans (h3.trans (h4.symm.trans ?_)))
  exact flatPullbackChow_heq_of_heq _ _ _ _ _ _ (by ring) _ _ h5.symm

include hr in
/-- **`π^*[Z]_{d-r}` restricts to `[E_d]_{d-1}` on `E_d`.** -/
theorem chowGroupRestrict_flatPullbackChow_fundamentalChowClass (hr0 : 0 < r) (d : ℕ) (m : ℤ)
    (hm : m = (d : ℤ) - r) :
    chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i d) rfl
        (m + ((r - 1 : ℕ) : ℤ))
        (flatPullbackChow (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
          (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom) (r - 1)
          (relativeDimension_exceptionalProj_of_codimension i hr hr0) m
          (flatPullbackDescends _ _ _ _ _ _ _ m)
          (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m)) =
      fundamentalChowClass (fieldChowSituation k)
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (m + ((r - 1 : ℕ) : ℤ)) := by
  by_cases hrd : r ≤ d
  · refine eq_of_heq ((chowGroupRestrict_flatPullbackChow_heq i hr hr0 d m).trans
      (heq_of_eq (flatPullbackChow_fundamentalChowClass _ _ _ _ _ _ _ _ _ ?_)))
    have h := schemeDeltaDimension_le_of_relativeDimension _ (relativeDimension_centrePart i hr d)
    rwa [show ((d - r : ℕ) : ℤ) = m by omega] at h
  · have := isEmpty_exceptionalPiece_of_lt i hr (show d < r by omega)
    exact chowGroup_exceptionalPiece_eq_of_isEmpty i _ _ _

include hr in
/-- **`π^*[Z]_m` restricts to `0` on `E_d` when `m ≠ d - r`**: `Z ∩ X_d` has dimension `d - r`. -/
theorem chowGroupRestrict_flatPullbackChow_fundamentalChowClass_of_ne (hr0 : 0 < r) (d : ℕ)
    (m : ℤ) (hm : m ≠ (d : ℤ) - r) :
    chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i d) rfl
        (m + ((r - 1 : ℕ) : ℤ))
        (flatPullbackChow (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
          (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom) (r - 1)
          (relativeDimension_exceptionalProj_of_codimension i hr hr0) m
          (flatPullbackDescends _ _ _ _ _ _ _ m)
          (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m)) = 0 := by
  by_cases hrd : r ≤ d
  · have h0 : fundamentalChowClass (fieldChowSituation k) ((centrePart i d).ι ≫ Z.obj.hom) m =
        0 := by
      have hY : RelativeDimension (𝟙 _ ≫ (centrePart i d).ι ≫ Z.obj.hom) (d - r) := by
        have key : ∀ (q : (centrePart i d).toScheme ⟶ Spec (.of k)) [LocallyOfFiniteType q],
            q = (centrePart i d).ι ≫ Z.obj.hom → RelativeDimension q (d - r) := by
          rintro q _ rfl; exact relativeDimension_centrePart i hr d
        exact key _ (Category.id_comp _)
      rw [fundamentalChowClass, fundamentalCycle,
        cycleAssociatedToClosedSubscheme_eq_zero_of_relativeDimension _ (𝟙 _) hY
          (by omega : m ≠ ((d - r : ℕ) : ℤ)), map_zero]
    refine eq_of_heq ((chowGroupRestrict_flatPullbackChow_heq i hr hr0 d m).trans ?_)
    rw [h0, map_zero]
  · have := isEmpty_exceptionalPiece_of_lt i hr (show d < r by omega)
    exact chowGroup_exceptionalPiece_eq_of_isEmpty i _ _ _

/-! ### The class `γ_m = c_{r-1}(𝓕^∨) ∩ π^*[Z]_m` -/

/-- **`γ_m = c_{r-1}(𝓕^∨) ∩ π^*[Z]_m ∈ CH_m(E)`**, for a centre of pure codimension `r ≥ 1`. -/
def excessPullbackCap (hr0 : 0 < r) (m : ℤ) :
    chowGroup (fieldChowSituation k) (exceptionalObj i).obj.hom
      ((m + ((r - 1 : ℕ) : ℤ)) - ((r - 1 : ℕ) : ℤ)) :=
  chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _)
    (exceptionalObj i).obj.hom ((r - 1 : ℕ) : ℤ)
    (totalChernOfFiniteLocallyFree (fieldChowSituation k) (exceptionalObj i).obj.hom
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (excessConormal i)) (r - 1))
    (m + ((r - 1 : ℕ) : ℤ))
    (flatPullbackChow (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
      (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom) (r - 1)
      (relativeDimension_exceptionalProj_of_codimension i hr hr0) m
      (flatPullbackDescends _ _ _ _ _ _ _ m)
      (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m))

/-- The restriction of `c_{r-1}(𝓕^∨)` to the part `E_d`. -/
abbrev excessChernPiece (d : ℕ) :
    chowCohomologyComponent (fieldChowSituation k) (gysinSystemOfInvertible _)
      (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) ((r - 1 : ℕ) : ℤ) :=
  chowCohomologyRestrictionOfEq (fieldChowSituation k)
    (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalObj i).obj.hom rfl
    (gysinSystemOfInvertible _) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _)
    ((r - 1 : ℕ) : ℤ)
    (totalChernOfFiniteLocallyFree (fieldChowSituation k) (exceptionalObj i).obj.hom
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (excessConormal i)) (r - 1))

include hr in
/-- **`γ_{d-r}` restricts to `c_{r-1}(𝓕^∨)|_{E_d} ∩ [E_d]_{d-1}` on `E_d`.** -/
theorem chowGroupRestrict_excessPullbackCap (hr0 : 0 < r) (d : ℕ) (m : ℤ)
    (hm : m = (d : ℤ) - r) :
    chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i d) rfl _
        (excessPullbackCap i hr hr0 m) =
      chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _)
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) ((r - 1 : ℕ) : ℤ)
        (excessChernPiece (r := r) i d) (m + ((r - 1 : ℕ) : ℤ))
        (fundamentalChowClass (fieldChowSituation k)
          (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (m + ((r - 1 : ℕ) : ℤ))) := by
  rw [excessPullbackCap, chowGroupRestrict_chowCohomologyCap_of_isOpenImmersion _ _
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _),
    chowGroupRestrict_flatPullbackChow_fundamentalChowClass i hr hr0 d m hm]

include hr in
/-- **`γ_m` restricts to `0` on `E_d` when `m ≠ d - r`.** -/
theorem chowGroupRestrict_excessPullbackCap_of_ne (hr0 : 0 < r) (d : ℕ) (m : ℤ)
    (hm : m ≠ (d : ℤ) - r) :
    chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i d) rfl _
        (excessPullbackCap i hr hr0 m) = 0 := by
  rw [excessPullbackCap, chowGroupRestrict_chowCohomologyCap_of_isOpenImmersion _ _
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _),
    chowGroupRestrict_flatPullbackChow_fundamentalChowClass_of_ne i hr hr0 d m hm, map_zero]

include hr in
/-- **`γ_{d-r}` is the pushforward of its restriction to `E_d`.** -/
theorem excessPullbackCap_eq_properChowPushforward (hr0 : 0 < r) (d : ℕ) (m : ℤ)
    (hm : m = (d : ℤ) - r) :
    excessPullbackCap i hr hr0 m = properChowPushforward (fieldChowSituation k)
      (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalObj i).obj.hom
      (exceptionalPieceι i d) rfl _ (properPushforwardDescends _ _ _ _ _ _)
      (chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i d) rfl _
        (excessPullbackCap i hr hr0 m)) :=
  eq_properChowPushforward_chowGroupRestrict_exceptionalPiece i d _ _ fun d' hd' ↦
    chowGroupRestrict_excessPullbackCap_of_ne i hr hr0 d' m (by omega)

include hr in
/-- **`π_*(c_{r-1}(𝓕^∨) ∩ π^*β) = β`** for every class `β` of the centre (Stacks 02TW): `E` is the
projective bundle of `𝒞_{Z/X}` and `𝓕` the kernel of its tautological quotient (Tag 0FUT). This
is the computation the proof of Lemma 0FIH omits. -/
theorem properChowPushforward_chowCohomologyCap_flatPullbackChow (hr0 : 0 < r) (m : ℤ)
    (β : chowGroup (fieldChowSituation k) Z.obj.hom m) :
    properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
        (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom)
        ((m + ((r - 1 : ℕ) : ℤ)) - ((r - 1 : ℕ) : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _)
          (exceptionalObj i).obj.hom ((r - 1 : ℕ) : ℤ)
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) (exceptionalObj i).obj.hom
            (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (excessConormal i)) (r - 1))
          (m + ((r - 1 : ℕ) : ℤ))
          (flatPullbackChow (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
            (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom) (r - 1)
            (relativeDimension_exceptionalProj_of_codimension i hr hr0) m
            (flatPullbackDescends _ _ _ _ _ _ _ m) β)) ≍ β := by
  have hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (excessConormal i) (r - 1) := isFiniteLocallyFreeOfRank_excessConormal_of_codimension i hr hr0
  have hFd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    (excessConormal i) (r - 1) hF
  have h𝒞 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (centreConormal i) (r - 1 + 1) := by
    rw [Nat.sub_add_cancel hr0]
    exact isFiniteLocallyFreeOfRank_centreConormal_of_codimension i hr
  have hM := isInvertible_exceptionalConormal i
  have hπ := relativeDimension_exceptionalProj_of_codimension i hr hr0
  have htower := isLocallyProjectiveTower_exceptionalConormal_of_codimension i hr hr0
  have key := GenuineChern.pushforward_chernFamily_dualKernel_bundlePullback
    (fieldChowSituation k) Z.obj.hom (exceptionalObj i).obj.hom (exceptionalProj i).hom.left
    (Over.w (exceptionalProj i).hom) (r - 1) hπ (centreConormal i) (excessShortComplex i)
    (excessShortComplex_shortExact i) (hF := hF) (hM := hM) (excessShortComplexX₂Iso i) htower m β
  refine HEq.trans ?_ (heq_of_eq key)
  refine properChowPushforward_heq_of_morphism_eq (fieldChowSituation k) _ _ rfl rfl _ _ (by ring) _
      _ ?_
  refine (chowCohomologyCap_totalChernOfFiniteLocallyFree_heq (fieldChowSituation k)
    (exceptionalObj i).obj.hom _ (r - 1) _ _).trans ?_
  exact (chowGroupCast_heq _ _ _ _).symm

/-! ### The second relation: `π_*(j^!θ) = [Z]` -/

open AlgebraicGeometry.VectorBundleKZero in
/-- **`c_{r-1}(b^*α^∨ - [𝒪_{X'}(E)])` restricts to `c_{r-1}(𝓕^∨)` on `E_d`**, for `α` restricting
to `[𝒞_{Z/X}]` (`pullback_blowupKClass`). -/
theorem res_totalChernKClass_blowupKClass_heq (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) (d : ℕ) :
    TotalChowClass.res (exceptionalPieceι i d ≫ (exceptionalHom i).hom.left)
        (Category.assoc _ _ _)
        (totalChernKClass (fieldChowSituation k) (blowupObj i).obj.hom (blowupKClass i α))
        (r - 1) ≍ excessChernPiece (r := r) i d := by
  have e1 : TotalChowClass.res (exceptionalPieceι i d ≫ (exceptionalHom i).hom.left)
      (Category.assoc _ _ _)
      (totalChernKClass (fieldChowSituation k) (blowupObj i).obj.hom (blowupKClass i α)) =
      TotalChowClass.res (exceptionalPieceι i d) rfl
        (totalChernOfFiniteLocallyFree (fieldChowSituation k)
          ((exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom)
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (excessConormal i))) := by
    rw [← TotalChowClass.res_res (exceptionalHom i).hom.left rfl (exceptionalPieceι i d) rfl,
      res_totalChernKClass, pullback_blowupKClass i α hα, totalChernKClass_classOf]
  refine (heq_of_eq (congrFun e1 (r - 1))).trans ?_
  rw [TotalChowClass.res_apply_eq_restrictionOfEq]
  have key : ∀ (q : (exceptionalObj i).obj.left ⟶ (fieldChowSituation k).S)
      [LocallyOfFiniteType q], q = (exceptionalObj i).obj.hom →
      chowCohomologyRestrictionOfEq (fieldChowSituation k) (exceptionalPieceι i d ≫ q) q rfl
          (gysinSystemOfInvertible _) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _)
          ((r - 1 : ℕ) : ℤ)
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) q
            (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (excessConormal i)) (r - 1)) ≍
        excessChernPiece (r := r) i d := by
    rintro q _ rfl; rfl
  exact key _ (Over.w (exceptionalHom i).hom)

/-- Pushing a class of `E_d` forward to `E` and then along `g` is pushing it forward along
`E_d ⟶ E ⟶ W`. -/
private theorem properChowPushforward_properChowPushforward_exceptionalPieceι (d : ℕ)
    {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
    (g : (exceptionalObj i).obj.left ⟶ W) [IsProper g] (hg : g ≫ sW = (exceptionalObj i).obj.hom)
    (n : ℤ) (x : chowGroup (fieldChowSituation k)
      (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) n) :
    properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom sW g hg n
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (properChowPushforward (fieldChowSituation k)
          (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalObj i).obj.hom
          (exceptionalPieceι i d) rfl n (properPushforwardDescends _ _ _ _ _ _) x) =
      properChowPushforward (fieldChowSituation k)
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) sW (exceptionalPieceι i d ≫ g)
        (by rw [Category.assoc, hg]) n
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _) x :=
  congrArg (· x) (properChowPushforward_comp (fieldChowSituation k) _ _ _
    (exceptionalPieceι i d) g rfl hg n (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _))

include hr in
open AlgebraicGeometry.VectorBundleKZero in
/-- **`j^!θ` on the part `E_d` is `γ_{d-r}|_{E_d} = c_{r-1}(𝓕^∨)|_{E_d} ∩ [E_d]`** (the Gysin
map of the regular immersion `j` on the part `X'_d`, Stacks 0FF6 and 0FF7, the piece `E_d` having
dimension `d - 1`). -/
theorem regularImmersionPartGysin_blowupTheta_heq (hr0 : 0 < r) (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) (e : ℕ) :
    regularImmersionPartGysin (blowupObj i).obj.hom (exceptionalHom i).hom.left
        (isRegularImmersion_of_isClosedImmersion (exceptionalHom i)) e (e + 1) ((r - 1 : ℕ) : ℤ)
        (blowupTheta i α r (e + 1)) ≍
      chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
        (exceptionalPieceι i (e + 1) ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i (e + 1))
        rfl _ (excessPullbackCap i hr hr0 ((e : ℤ) - ((r - 1 : ℕ) : ℤ))) := by
  have hP : RelativeDimension (exceptionalPieceι i (e + 1) ≫ (exceptionalHom i).hom.left ≫
      (blowupObj i).obj.hom) e := by
    have h := relativeDimension_exceptionalPiece i (e + 1)
    rwa [Nat.add_sub_cancel] at h
  rw [chowGroupRestrict_excessPullbackCap i hr hr0 (e + 1) _ (by push_cast; omega), blowupTheta,
    regularImmersionPartGysin_totalChowClassCapFundamental _ _ _ e (e + 1) hP]
  have key : ∀ (q : (exceptionalPiece i (e + 1)) ⟶ (fieldChowSituation k).S)
      [LocallyOfFiniteType q], q = exceptionalPieceι i (e + 1) ≫ (exceptionalObj i).obj.hom →
      ∀ (c : chowCohomologyComponent (fieldChowSituation k) (gysinSystemOfInvertible _) q
        ((r - 1 : ℕ) : ℤ)), c ≍ excessChernPiece (r := r) i (e + 1) → ∀ (n n' : ℤ), n = n' →
      chowCohomologyCapFundamentalClass (fieldChowSituation k) (gysinSystemOfInvertible _) q n
          ((r - 1 : ℕ) : ℤ) c ≍
        chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _)
          (exceptionalPieceι i (e + 1) ≫ (exceptionalObj i).obj.hom) ((r - 1 : ℕ) : ℤ)
          (excessChernPiece (r := r) i (e + 1)) n'
          (fundamentalChowClass (fieldChowSituation k)
            (exceptionalPieceι i (e + 1) ≫ (exceptionalObj i).obj.hom) n') := by
    rintro q _ rfl c hc n _ rfl
    cases hc
    rw [chowCohomologyCap_fundamentalChowClass]
  exact key _ (by rw [Over.w (exceptionalHom i).hom]) _
    (res_totalChernKClass_blowupKClass_heq i α hα (e + 1)) _ _ (by ring)

include hr in
open AlgebraicGeometry.VectorBundleKZero in
/-- **The second relation of Lemma 0FIH, part by part: `π_*(j^!θ) = [Z]`.** For every `e`, the
Gysin map of the regular immersion `j : E ⟶ X'` on the part `X'_{e+1}` of `X'` of dimension
`e + 1` (`Stacks.Chow.regularImmersionPartGysin`) carries `θ` to a class of
`CH_{e-(r-1)}(E_{e+1})`, `E_{e+1} = E ×_{X'} X'_{e+1}`, whose pushforward to `Z` is the
fundamental class `[Z]_{e-(r-1)}`, the sum of the components of `Z` of dimension `e - (r - 1)`. -/
theorem properChowPushforward_regularImmersionPartGysin_blowupTheta (hr0 : 0 < r)
    (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) (e : ℕ) :
    properChowPushforward (fieldChowSituation k)
        (exceptionalPieceι i (e + 1) ≫ (exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom)
        Z.obj.hom (exceptionalPieceι i (e + 1) ≫ (exceptionalProj i).hom.left)
        (by rw [Category.assoc, Over.w (exceptionalProj i).hom, Over.w (exceptionalHom i).hom])
        ((e : ℤ) - ((r - 1 : ℕ) : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (regularImmersionPartGysin (blowupObj i).obj.hom (exceptionalHom i).hom.left
          (isRegularImmersion_of_isClosedImmersion (exceptionalHom i)) e (e + 1)
          ((r - 1 : ℕ) : ℤ) (blowupTheta i α r (e + 1))) =
      fundamentalChowClass (fieldChowSituation k) Z.obj.hom ((e : ℤ) - ((r - 1 : ℕ) : ℤ)) := by
  set m : ℤ := (e : ℤ) - ((r - 1 : ℕ) : ℤ)
  have hm : m = ((e + 1 : ℕ) : ℤ) - r := by push_cast; omega
  have h1 := regularImmersionPartGysin_blowupTheta_heq i hr hr0 α hα e
  have h2 := excessPullbackCap_eq_properChowPushforward i hr hr0 (e + 1) m hm
  have h3 : properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
      (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom)
      ((m + ((r - 1 : ℕ) : ℤ)) - ((r - 1 : ℕ) : ℤ))
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
      (excessPullbackCap i hr hr0 m) ≍ fundamentalChowClass (fieldChowSituation k) Z.obj.hom m :=
    properChowPushforward_chowCohomologyCap_flatPullbackChow i hr hr0 m
      (fundamentalChowClass (fieldChowSituation k) Z.obj.hom m)
  rw [h2] at h3
  rw [properChowPushforward_properChowPushforward_exceptionalPieceι] at h3
  refine eq_of_heq (HEq.trans ?_ h3)
  exact properChowPushforward_heq_of_morphism_eq (fieldChowSituation k) _ _ rfl
    (by rw [Over.w (exceptionalHom i).hom]) _ _ (by ring) _ _ h1

/-! ### The first relation: `b^![Z] = [E] · θ` -/

include hr in
/-- **`b^![Z]` on the piece `X'_d ∩ b⁻¹(X_d)`** is the restriction of `j_*γ_{d-r}`: the Gysin
class of `b` capped at the test scheme `X_d ⟶ X` with `[Z] |_{X_d}` is the restriction of
`b^!(i_*[Z]_{d-r})` (Stacks 0B76 (2)), which the blow up formula computes. -/
theorem dimPartPieceGysin_blowupHom_closedSubschemeClass_of_codimension (hr0 : 0 < r) (d : ℕ) :
    dimPartPieceGysin (blowupObj i).obj.hom X.obj.hom (Over.w (blowupHom i).hom) d d (r : ℤ)
        (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ) d) ≍
      chowGroupRestrict (fieldChowSituation k) (blowupObj i).obj.hom
        (dimPartPieceBase (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left d d)
        ((dimPartPiece (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left d d).ι ≫
          (dimPart (blowupObj i).obj.hom d).ι) (by rw [Category.assoc])
        ((((d : ℤ) - r) + ((r - 1 : ℕ) : ℤ)) - ((r - 1 : ℕ) : ℤ))
        (properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom
          (blowupObj i).obj.hom (exceptionalHom i).hom.left (Over.w (exceptionalHom i).hom)
          _ (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (excessPullbackCap i hr hr0 ((d : ℤ) - r))) := by
  -- the class `[Z]` on `X_d` is the restriction of `i_*[Z]_{d-r}`
  have hβ : closedSubschemeClass X.obj.hom i.hom.left (r : ℤ) d =
      chowGroupRestrict (fieldChowSituation k) X.obj.hom ((dimPart X.obj.hom d).ι ≫ X.obj.hom)
        (dimPart X.obj.hom d).ι rfl ((d : ℤ) - r)
        (properChowPushforward (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) X.obj.hom
          i.hom.left rfl ((d : ℤ) - r)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (i.hom.left ≫ X.obj.hom)
            ((d : ℤ) - r))) := by
    rw [closedSubschemeClass_apply,
      mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward (fieldChowSituation k)
        X.obj.hom i.hom.left (i.hom.left ≫ X.obj.hom) rfl _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)]
  -- `b^!` on the piece is `b^!` capped at the test scheme `X_d`, restricted to the piece
  have hL := dimPartPieceGysinClass_capTarget_heq (blowupObj i).obj.hom X.obj.hom
    (Over.w (blowupHom i).hom) d d ((d : ℤ) - r)
    (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ) d)
  rw [hβ, ← BivariantClass.chowGroupRestrict_capTarget, chowGroupRestrict_comp,
    chowGroupRestrict_congr (fieldChowSituation k) _ _ _ _ _
      ((dimPartPiece (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left d d).ι ≫
        (dimPart (blowupObj i).obj.hom d).ι)
      (dimPartPieceToPullback_fst _ _ _ d d) (by rw [Category.assoc])] at hL
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans ((hβ ▸ hL).trans ?_)
  -- `b^! ∩ i_*[Z]_{d-r}` is the blow up formula
  have hdeg : ∀ (q : ℤ) (_ : q = 0) (m : ℤ) (_ : m = (d : ℤ) - r),
      (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
          (Over.w (blowupHom i).hom) q).capTarget (fieldChowSituation k)
          (gysinSystemOfInvertible _) _ _ _ _ q m
          (properChowPushforward (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) X.obj.hom
            i.hom.left rfl m
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
            (fundamentalChowClass (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) m)) ≍
        (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
          (Over.w (blowupHom i).hom) 0).capTarget (fieldChowSituation k)
          (gysinSystemOfInvertible _) _ _ _ _ 0 ((d : ℤ) - r)
          (properChowPushforward (fieldChowSituation k) Z.obj.hom X.obj.hom i.hom.left
            (Over.w i.hom) ((d : ℤ) - r)
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
            (fundamentalChowClass (fieldChowSituation k) Z.obj.hom ((d : ℤ) - r))) := by
    rintro q rfl m rfl
    have key : ∀ (t : Z.obj.left ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType t]
        (ht : i.hom.left ≫ X.obj.hom = t) hd hd',
        (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
            (Over.w (blowupHom i).hom) 0).capTarget (fieldChowSituation k)
            (gysinSystemOfInvertible _) _ _ _ _ 0 ((d : ℤ) - r)
            (properChowPushforward (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) X.obj.hom
              i.hom.left rfl ((d : ℤ) - r) hd
              (fundamentalChowClass (fieldChowSituation k) (i.hom.left ≫ X.obj.hom)
                ((d : ℤ) - r))) ≍
          (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
            (Over.w (blowupHom i).hom) 0).capTarget (fieldChowSituation k)
            (gysinSystemOfInvertible _) _ _ _ _ 0 ((d : ℤ) - r)
            (properChowPushforward (fieldChowSituation k) t X.obj.hom i.hom.left ht
              ((d : ℤ) - r) hd' (fundamentalChowClass (fieldChowSituation k) t ((d : ℤ) - r))) := by
      rintro t _ rfl hd hd'
      rfl
    exact key _ (Over.w i.hom) _ _
  exact chowGroupRestrict_heq_of_heq (fieldChowSituation k) _ _ _ _ (by ring) _ _
    ((hdeg _ (by ring) _ (by ring)).trans
      (capTarget_smoothGysinClass_blowupHom_of_codimension i hr hr0 _ _))

include hr in
/-- **`b^![Z]` on the part `X'_d` of `X'`** is the restriction of `j_*γ_{d-r}`, for every `d`. -/
theorem codimensionGysin_blowupHom_closedSubschemeClass_apply (hr0 : 0 < r) (d : ℕ) :
    codimensionGysin (blowupObj i).obj.hom X.obj.hom (Over.w (blowupHom i).hom) (r : ℤ)
        (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ)) d =
      chowGroupToCodimension (blowupObj i).obj.hom
        ((((d : ℤ) - r) + ((r - 1 : ℕ) : ℤ)) - ((r - 1 : ℕ) : ℤ)) (r : ℤ)
        (properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom
          (blowupObj i).obj.hom (exceptionalHom i).hom.left (Over.w (exceptionalHom i).hom)
          _ (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (excessPullbackCap i hr hr0 ((d : ℤ) - r))) d := by
  refine (chowGroupDimPartPieceEquiv (blowupObj i).obj.hom X.obj.hom (f := (blowupHom i).hom.left)
    d ((d : ℤ) - r)).injective (funext fun t ↦ ?_)
  obtain ⟨t⟩ := t
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  by_cases ht : t = d
  swap
  · have : IsEmpty (dimPartPiece (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left d
        t).toScheme := ⟨fun w ↦ ht ((isClopenDecomposition_dimPart X.obj.hom).eq_of_mem w.2
          (blowupHom_mem_dimPart i w.1.2))⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (dimPartPieceBase (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left d t)
      ((d : ℤ) - r)
    exact Subsingleton.elim _ _
  subst t
  have hM : (((d : ℤ) - r) + ((r - 1 : ℕ) : ℤ)) - ((r - 1 : ℕ) : ℤ) = (d : ℤ) - r := by ring
  refine eq_of_heq ((dimPartPieceGysin_blowupHom_closedSubschemeClass_of_codimension i hr hr0
    d).trans ?_)
  refine HEq.symm ((chowGroupRestrict_heq_of_heq (fieldChowSituation k) _ _ _ rfl hM.symm _ _
    (chowGroupToCodimension_apply_heq _ _ _ _ d hM)).trans ?_)
  rw [chowGroupRestrict_comp]

/-- **`[E] = [E_d]` on the part `X'_d`**: both restrict to the class of `E_d ⊆ X'_d`. -/
theorem closedSubschemeClass_exceptionalHom_apply (d : ℕ) :
    closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left 1 d =
      closedSubschemeClass (blowupObj i).obj.hom
        (exceptionalPieceι i d ≫ (exceptionalHom i).hom.left) 1 d := by
  have hsq : IsPullback (𝟙 _)
      (pullback.snd (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom d).ι)
      (exceptionalPieceι i d ≫ (exceptionalHom i).hom.left) (dimPart (blowupObj i).obj.hom d).ι :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, pullback.condition]⟩
  rw [closedSubschemeClass_apply, closedSubschemeClass_apply,
    chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme_of_isPullback (fieldChowSituation k)
      (blowupObj i).obj.hom (partBase (blowupObj i).obj.hom d) (dimPart (blowupObj i).obj.hom d).ι
      rfl (exceptionalHom i).hom.left _ _ (IsPullback.of_hasPullback _ _),
    chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme_of_isPullback (fieldChowSituation k)
      (blowupObj i).obj.hom (partBase (blowupObj i).obj.hom d) (dimPart (blowupObj i).obj.hom d).ι
      rfl (exceptionalPieceι i d ≫ (exceptionalHom i).hom.left) _ _ hsq]

/-- Restriction of a total class along a morphism, for two ways of writing the structure
morphism of the source. -/
theorem _root_.Stacks.Chow.TotalChowClass.res_apply_heq_of_comp_eq {C : ChowSituation.{u}}
    {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {sT sT' : Y' ⟶ C.S}
    [LocallyOfFiniteType sT] [LocallyOfFiniteType sT'] (h : Y' ⟶ Y) [LocallyOfFiniteType h]
    (hs : h ≫ sY = sT) (hs' : h ≫ sY = sT') (c : TotalChowClass C sY) (p : ℕ) :
    TotalChowClass.res h hs c p ≍ TotalChowClass.res h hs' c p := by
  subst hs hs'
  rfl

include hr in
/-- **`c_{r-1}(𝓕^∨)|_{E_d} ∩ [E_d]_n` is `γ_{d-r}|_{E_d}`** for `n = d - 1`, whatever the
presentation of the structure morphism of `E_d` and of the restricted class. -/
theorem chowCohomologyCapFundamentalClass_heq_excessPullbackCap (hr0 : 0 < r) (d : ℕ)
    (q : exceptionalPiece i d ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q]
    (hq : q = exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom)
    (c : chowCohomologyComponent (fieldChowSituation k) (gysinSystemOfInvertible _) q
      ((r - 1 : ℕ) : ℤ)) (hc : c ≍ excessChernPiece (r := r) i d) (n : ℤ)
    (hn : n = ((d : ℤ) - r) + ((r - 1 : ℕ) : ℤ)) :
    chowCohomologyCapFundamentalClass (fieldChowSituation k) (gysinSystemOfInvertible _) q n
        ((r - 1 : ℕ) : ℤ) c ≍
      chowGroupRestrict (fieldChowSituation k) (exceptionalObj i).obj.hom
        (exceptionalPieceι i d ≫ (exceptionalObj i).obj.hom) (exceptionalPieceι i d) rfl _
        (excessPullbackCap i hr hr0 ((d : ℤ) - r)) := by
  subst hq hn
  cases hc
  rw [chowGroupRestrict_excessPullbackCap i hr hr0 d _ rfl, chowCohomologyCap_fundamentalChowClass]

include hr in
open AlgebraicGeometry.VectorBundleKZero in
/-- **`[E] · θ` on the part `X'_d` of `X'`** is the restriction of `j_*γ_{d-r}`, for `d ≥ r`:
`[E] · θ = [E_d] · θ = (E_d ⟶ X')_*(c_{r-1}|_{E_d} ∩ [E_d])` by Tag 0FFE and 0FF7 for the
regular immersion `E_d ⟶ X'`, and `γ_{d-r}` is the pushforward of `c_{r-1}|_{E_d} ∩ [E_d]`. -/
theorem codimensionIntersectionProduct_exceptional_blowupTheta_apply_heq (hr0 : 0 < r)
    (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) (d : ℕ)
    (hd : r ≤ d) :
    codimensionIntersectionProduct k (blowupObj i).obj.hom 1 ((r - 1 : ℕ) : ℤ)
        (closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left 1)
        (blowupTheta i α r) d ≍
      chowGroupRestrict (fieldChowSituation k) (blowupObj i).obj.hom
        (partBase (blowupObj i).obj.hom d) (dimPart (blowupObj i).obj.hom d).ι rfl _
        (properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom
          (blowupObj i).obj.hom (exceptionalHom i).hom.left (Over.w (exceptionalHom i).hom)
          ((((d : ℤ) - r) + ((r - 1 : ℕ) : ℤ)) - ((r - 1 : ℕ) : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (excessPullbackCap i hr hr0 ((d : ℤ) - r))) := by
  set jd := exceptionalPieceι i d ≫ (exceptionalHom i).hom.left
  have : Smooth (jd ≫ (blowupObj i).obj.hom) := by
    rw [Category.assoc, Over.w (exceptionalHom i).hom]; infer_instance
  have hY : RelativeDimension (jd ≫ (blowupObj i).obj.hom) (d - 1) := by
    have key : ∀ (q : exceptionalPiece i d ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q],
        q = exceptionalPieceι i d ≫ (exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom →
        RelativeDimension q (d - 1) := by
      rintro q _ rfl; exact relativeDimension_exceptionalPiece i d
    exact key _ (Category.assoc _ _ _)
  -- `[E] · θ = [E_d] · θ` on `X'_d`
  have h0 : codimensionIntersectionProduct k (blowupObj i).obj.hom 1 ((r - 1 : ℕ) : ℤ)
      (closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left 1)
      (blowupTheta i α r) d =
      codimensionIntersectionProduct k (blowupObj i).obj.hom 1 ((r - 1 : ℕ) : ℤ)
        (closedSubschemeClass (blowupObj i).obj.hom jd 1) (blowupTheta i α r) d := by
    rw [codimensionIntersectionProduct_apply, codimensionIntersectionProduct_apply,
      closedSubschemeClass_exceptionalHom_apply]
  -- Tag 0FFE for `E_d ⟶ X'`
  have h1 := congrFun (codimensionIntersectionProduct_closedSubschemeClass_one_of_smooth
    (blowupObj i).obj.hom jd (d - 1) hY ((r - 1 : ℕ) : ℤ) (blowupTheta i α r)) d
  -- Tag 0FF7 for `E_d ⟶ X'`
  have h2 := regularImmersionGysin_totalChowClassCapFundamental (blowupObj i).obj.hom jd
    (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth jd (blowupObj i).obj.hom)
    (d - 1) hY (totalChernKClass (fieldChowSituation k) (blowupObj i).obj.hom (blowupKClass i α))
    (r - 1)
  rw [h0, h1]
  have hdeg : (((d - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ)) = (d : ℤ) - (1 + ((r - 1 : ℕ) : ℤ)) := by
    omega
  refine (chowGroupToCodimension_apply_heq _ _ _ _ d hdeg).trans ?_
  refine chowGroupRestrict_heq_of_heq (fieldChowSituation k) _ _ _ _ (by omega) _ _ ?_
  -- `(E_d ⟶ X')_*(c ∩ [E_d]) = j_*γ_{d-r}`
  rw [excessPullbackCap_eq_properChowPushforward i hr hr0 d _ rfl]
  rw [properChowPushforward_properChowPushforward_exceptionalPieceι]
  refine properChowPushforward_heq_of_morphism_eq (fieldChowSituation k) _ _ rfl
    (by rw [Category.assoc, Over.w (exceptionalHom i).hom]) _ _ (by omega) _ _ ?_
  rw [blowupTheta, h2]
  exact chowCohomologyCapFundamentalClass_heq_excessPullbackCap i hr hr0 d _
    (by rw [Category.assoc, Over.w (exceptionalHom i).hom]) _
    ((TotalChowClass.res_apply_heq_of_comp_eq _ _ (Category.assoc _ _ _) _ _).trans
      (res_totalChernKClass_blowupKClass_heq i α hα d)) _ (by omega)

/-- Two classes in equal negative degrees are heterogeneously equal: over a field there are no
cycles of negative dimension. -/
theorem heq_of_neg {T : Scheme.{u}} (q : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q]
    {n n' : ℤ} (hn : n = n') (hneg : n < 0) (a : chowGroup (fieldChowSituation k) q n)
    (b : chowGroup (fieldChowSituation k) q n') : a ≍ b := by
  subst hn
  have h0 : ∀ a : CycleGroup (fieldChowSituation k) q n, a = 0 := fun a ↦ by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    show a.1 x = 0
    by_contra hx
    have h1 := (mem_cyclesOfDimension_iff_forall_point _ q n a.1).1 a.2 x hx
    have h2 := relativeDimension_fieldChowSituation_nonneg k q x
    omega
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [h0 a, h0 b]

include hr in
open AlgebraicGeometry.VectorBundleKZero in
/-- **The first relation of Lemma 0FIH: `b^![Z] = [E] · θ`**, the two sides lying in `CH^r(X')`
and `CH^{1+(r-1)}(X')`, for `X` not necessarily equidimensional: on the part `X'_d` both are the
restriction of `j_*(c_{r-1}(𝓕^∨) ∩ π^*[Z]_{d-r})`. -/
theorem codimensionGysin_closedSubschemeClass_heq_blowupTheta_of_codimension (hr0 : 0 < r)
    (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) :
    codimensionGysin (blowupObj i).obj.hom X.obj.hom (Over.w (blowupHom i).hom) (r : ℤ)
        (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ)) ≍
      codimensionIntersectionProduct k (blowupObj i).obj.hom 1 ((r - 1 : ℕ) : ℤ)
        (closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left 1)
        (blowupTheta i α r) := by
  refine Function.hfunext rfl fun d d' hdd ↦ ?_
  obtain rfl := eq_of_heq hdd
  by_cases hd : r ≤ d
  · rw [codimensionGysin_blowupHom_closedSubschemeClass_apply i hr hr0 d]
    refine (chowGroupToCodimension_apply_heq _ _ _ _ d (by ring)).trans ?_
    exact (codimensionIntersectionProduct_exceptional_blowupTheta_apply_heq i hr hr0 α hα d
      hd).symm
  · exact heq_of_neg _ (by omega) (by omega) _ _

/-! ### Lemma 0FIH -/

open AlgebraicGeometry.VectorBundleKZero in
/-- **Lemma 0FIH.** Let `b : X' ⟶ X` be the blowing up of a smooth projective scheme `X` over `k`
(not necessarily equidimensional) in a smooth closed subscheme `i : Z ⟶ X`, with exceptional
divisor `j : E ⟶ X'` and `π : E ⟶ Z`. Assume that some element of `K_0(Vect(X))` restricts on
`Z` to the class of `𝒞_{Z/X}`, and that every irreducible component of `Z` has codimension
`r ≥ 1` in `X` (its generic point has coheight `r` in `X`). Then there is a cycle
`θ ∈ CH^{r-1}(X')` such that

* `b^![Z] = [E] · θ` in `CH^r(X')`, with `b^!` the Gysin map of Stacks 0FF3 and `·` the
  intersection product of Stacks 0FC0, both graded by codimension; and
* `π_*(j^!θ) = [Z]`: for every `e`, on the part `X'_{e+1}` of `X'` of dimension `e + 1` the
  Gysin map of the regular immersion `j` (`Stacks.Chow.regularImmersionPartGysin`) carries `θ`
  to a class of `CH_{e-(r-1)}(E ×_{X'} X'_{e+1})` whose pushforward to `Z` is the fundamental
  class `[Z]_{e-(r-1)}`, the sum of the components of `Z` of dimension `e - (r - 1)`.

Since `CH_*(E)` is the direct sum of the `CH_*(E ×_{X'} X'_d)`, the piece over `X'_0` is empty,
and `[Z] = ∑_m [Z]_m`, the second family of equalities is `π_*(j^!θ) = [Z]` in
`CH_*(Z) = ⊕_m CH_m(Z)`. The source writes `[Z] ∈ CH^r(Z)`; as `π_*j^!θ` has codimension `0` in
`Z`, this is the fundamental class `[Z] ∈ CH^0(Z)`. The hypothesis `r ≥ 1` is implicit in the
source (`θ ∈ CH^{r-1}(X')`): for `r = 0` and `Z` nonempty, `Z` is a union of components of `X`,
`E` is empty and `π_*(j^!θ) = 0 ≠ [Z]`.

The cycle is `θ = c_{r-1}(b^*α^∨ - [𝒪_{X'}(E)]) ∩ [X']`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.blowupTheta`), as in the source. -/
@[stacks 0FIH]
theorem exists_blowup_relations {r : ℕ} (hr0 : 0 < r)
    (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
      Order.coheight (i.hom.left z) = r)
    (hK : ∃ α : VectorBundleKZero X.obj.left,
      VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) :
    ∃ θ : codimensionChowGroup k (blowupObj i).obj.hom ((r - 1 : ℕ) : ℤ),
      codimensionGysin (blowupObj i).obj.hom X.obj.hom (Over.w (blowupHom i).hom) (r : ℤ)
          (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ)) ≍
        codimensionIntersectionProduct k (blowupObj i).obj.hom 1 ((r - 1 : ℕ) : ℤ)
          (closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left 1) θ ∧
      ∀ e : ℕ, properChowPushforward (fieldChowSituation k)
          (pullback.fst (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom (e + 1)).ι ≫
            (exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom)
          Z.obj.hom
          (pullback.fst (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom (e + 1)).ι ≫
            (exceptionalProj i).hom.left)
          (by rw [Category.assoc, Over.w (exceptionalProj i).hom, Over.w (exceptionalHom i).hom])
          ((e : ℤ) - ((r - 1 : ℕ) : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (regularImmersionPartGysin (blowupObj i).obj.hom (exceptionalHom i).hom.left
            (isRegularImmersion_of_isClosedImmersion (exceptionalHom i)) e (e + 1)
            ((r - 1 : ℕ) : ℤ) (θ (e + 1))) =
        fundamentalChowClass (fieldChowSituation k) Z.obj.hom ((e : ℤ) - ((r - 1 : ℕ) : ℤ)) := by
  obtain ⟨α, hα⟩ := hK
  exact ⟨blowupTheta i α r,
    codimensionGysin_closedSubschemeClass_heq_blowupTheta_of_codimension i hr hr0 α hα,
    properChowPushforward_regularImmersionPartGysin_blowupTheta i hr hr0 α hα⟩

end SmoothProjectiveScheme

end Stacks.WeilCohomology

end
