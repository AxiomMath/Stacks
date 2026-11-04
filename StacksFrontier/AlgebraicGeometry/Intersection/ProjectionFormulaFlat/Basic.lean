module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.LocalComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula for a flat proper morphism

Let `f : X ⟶ Y` be a flat proper morphism of nonsingular varieties over a field and set
`e = dim X - dim Y`. Let `α` be an `r`-cycle on `X` and `β` an `s`-cycle on `Y`, and assume that
`α` and `f^*β` intersect properly. Then `f_*α` and `β` intersect properly and

`f_*(α) · β = f_*(α · f^*β)`.

Cycles are represented by coherent sheaves: `α = [ℱ]_r` and `β = [𝒢]_s`, so that
`f_*α = [f_*ℱ]_r` by Stacks 0AZD and `f^*β = [f^*𝒢]_{s+e}` by Stacks 0AZF, and the intersection
product is given by the Tor formula of Stacks 0AZR. The relative dimension `e` is a natural number
with `dim X = dim Y + e`, and the degree of the intersection product is an arbitrary integer `n`;
the case `n = r + s - dim Y` is the identity above.

## Main results

All in the namespace `Stacks.Intersection.ProjectionFormula`:

* `topologicalKrullDim_image_le`: a closed subset of the image of a closed subset of dimension at
  most `n` has dimension at most `n`.
* `intersectProperly_coherentSheafCycle_pushforward_unconditional`: `f_*α` and `β` intersect
  properly.
* `properPushforward_intersectionProductCycleGroup_unconditional`: the identity
  `f_*α · β = f_*(α · f^*β)`.

## References

* [Stacks Project, Lemma 43.22.1 (Tag 0B10)](https://stacks.math.columbia.edu/tag/0B10)
* [Stacks Project, Tag 0B11](https://stacks.math.columbia.edu/tag/0B11)
* [Stacks Project, Tag 0AZD](https://stacks.math.columbia.edu/tag/0AZD)
* [Stacks Project, Tag 0AZF](https://stacks.math.columbia.edu/tag/0AZF)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Intersection.ProjectionFormula

open Stacks.Chow AlgebraicGeometry.TorFormula

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The dimension of an image -/

/-- Over a field, a closed subset all of whose points have relative dimension at most `n` has
topological dimension at most `n`. -/
theorem topologicalKrullDim_le_of_forall_relativeDimension_le (K : Type u) [Field K]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType sY] [IsLocallyNoetherian Y]
    (T : Set Y) (hT : IsClosed T) (n : ℕ)
    (hpt : ∀ y ∈ T, relativeDimension (fieldChowSituation K).dimensionFunction sY y ≤ (n : ℤ)) :
    topologicalKrullDim T ≤ (n : WithBot ℕ∞) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hT⟩ : Closeds Y) with hI
  set M : Y.Modules :=
    (Scheme.Modules.pushforward I.subschemeι).obj (Stacks.Ample.unitModule _) with hM
  have hsuppM : SheafOfModules.supp M = T := by
    rw [hM, Stacks.Chow.supp_pushforwardStructureSheaf]
    exact (Scheme.IdealSheafData.range_subschemeι I).trans (by simp [hI])
  have hcohM : M.IsCoherent := by rw [hM]; infer_instance
  have hdelta := schemeDeltaDimension_reducedSupport_le (fieldChowSituation K) sY M
    (k := (n : ℤ)) fun y hy => hpt y (hsuppM ▸ hy)
  have hfin := topologicalKrullDim_supp_le_of_field_schemeDeltaDimension_le K sY M n
    (by push_cast; exact hdelta)
  rwa [hsuppM] at hfin

/-- **Dimension does not grow along an image.** Let `f : X ⟶ Y` be a morphism of varieties over a
field, let `T ⊆ X` be closed of dimension at most `n` and let `S ⊆ Y` be a closed subset of the
image of `T`. Then `S` has dimension at most `n`. -/
theorem topologicalKrullDim_image_le (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (T : Set X) (hT : IsClosed T) (n : ℕ)
    (hTn : topologicalKrullDim T ≤ (n : WithBot ℕ∞)) (S : Set Y) (hS : IsClosed S)
    (hST : S ⊆ f.base '' T) :
    topologicalKrullDim S ≤ (n : WithBot ℕ∞) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have hlnY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : JacobsonSpace (fieldChowSituation K).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of K)))
  refine topologicalKrullDim_le_of_forall_relativeDimension_le K sY S hS n fun y hy => ?_
  obtain ⟨x, hxT, hxy⟩ := hST hy
  have hx : relativeDimension (fieldChowSituation K).dimensionFunction sX x ≤ (n : ℤ) :=
    relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation K) (fun _ _ => rfl) sX hT
      hTn hxT
  have hstep := relativeDimension_comp_eq_add_trdeg (fieldChowSituation K).dimensionFunction sY f x
  rw [hbase] at hstep
  rw [← hxy]
  omega

/-! ### Proper intersection after pushforward -/

/-- Let `f : X ⟶ Y` be a flat proper morphism of varieties over a field with `dim X = dim Y + e`,
let `ℱ` be a coherent `𝒪_X`-module with coherent direct image whose support has dimension at most
`r` and `𝒢` a coherent `𝒪_Y`-module whose support has dimension at most `s`, and assume that
`Supp(ℱ)` and `f^{-1}(Supp(𝒢))` meet in dimension at most `r + (s + e) - dim X`. Then the cycles
`f_*[ℱ]_r = [f_*ℱ]_r` and `[𝒢]_s` intersect properly. -/
theorem intersectProperly_coherentSheafCycle_pushforward (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (F : X.Modules)
    [F.IsCoherent] [((Scheme.Modules.pushforward f).obj F).IsCoherent] (G : Y.Modules)
    [G.IsCoherent] (r s : ℕ)
    (hFr : schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport F).subschemeι ≫ sX) ≤ ((r : ℤ) : EInt))
    (hGs : schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport G).subschemeι ≫ sY) ≤ ((s : ℤ) : EInt))
    (hFG : topologicalKrullDim
        (SheafOfModules.supp F ∩ f.base ⁻¹' SheafOfModules.supp G : Set X) +
      topologicalKrullDim X ≤ (r : WithBot ℕ∞) + ((s + e : ℕ) : WithBot ℕ∞)) :
    AlgebraicCycle.IntersectProperly
      (coherentSheafCycle (fieldChowSituation K) sY ((Scheme.Modules.pushforward f).obj F)
        (r : ℤ)
        (schemeDeltaDimension_reducedSupport_pushforward_le (fieldChowSituation K) sX sY f hbase
          F hFr))
      (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ) hGs) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have hftF : F.IsFiniteType := isFiniteType_of_isCoherent F
  have hftG : G.IsFiniteType := isFiniteType_of_isCoherent G
  have hftpF : ((Scheme.Modules.pushforward f).obj F).IsFiniteType :=
    isFiniteType_of_isCoherent ((Scheme.Modules.pushforward f).obj F)
  refine Stacks.Intersection.ReductionToDiagonal.intersectProperly_coherentSheafCycle K sY
    ((Scheme.Modules.pushforward f).obj F) G r s _ hGs ?_
  obtain ⟨dY, hdY⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety K sY
  set S : Set Y := SheafOfModules.supp ((Scheme.Modules.pushforward f).obj F) ∩
    SheafOfModules.supp G with hSdef
  set T : Set X := SheafOfModules.supp F ∩ f.base ⁻¹' SheafOfModules.supp G with hTdef
  have hSclosed : IsClosed S :=
    (SheafOfModules.isClosed_supp _).inter (SheafOfModules.isClosed_supp G)
  have hTclosed : IsClosed T :=
    (SheafOfModules.isClosed_supp F).inter
      ((SheafOfModules.isClosed_supp G).preimage f.base.hom.2)
  have hST : S ⊆ f.base '' T := by
    intro y hy
    obtain ⟨x, hxF, hxy⟩ :=
      supp_pushforward_subset_image f F (SheafOfModules.isClosed_supp F) hy.1
    exact ⟨x, ⟨hxF, by rw [Set.mem_preimage, hxy]; exact hy.2⟩, hxy⟩
  by_cases hempty : IsEmpty S
  · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hempty]
    simp
  · obtain ⟨y, hy⟩ := Set.nonempty_coe_sort.mp (not_isEmpty_iff.mp hempty)
    obtain ⟨x, hxT, -⟩ := hST hy
    have hTbot : topologicalKrullDim T ≠ ⊥ := fun h =>
      ((topologicalKrullDim_eq_bot_iff_isEmpty _).1 h).elim ⟨x, hxT⟩
    have hdimX : topologicalKrullDim X = ((dY + e : ℕ) : WithBot ℕ∞) := by
      rw [he, hdY]; push_cast; rfl
    have hTle : topologicalKrullDim T ≤ ((dY + e : ℕ) : WithBot ℕ∞) := by
      rw [← hdimX]; exact topologicalKrullDim_subspace_le X _
    obtain ⟨nT, hnT, -⟩ :=
      Stacks.Intersection.FlatPullback.exists_natCast_eq_of_le_natCast hTbot hTle
    have hsum : nT + (dY + e) ≤ r + (s + e) := by
      rw [hnT, hdimX] at hFG
      exact_mod_cast hFG
    have hSn : topologicalKrullDim S ≤ (nT : WithBot ℕ∞) :=
      topologicalKrullDim_image_le K sX sY f hbase T hTclosed nT (le_of_eq hnT) S hSclosed hST
    rw [hdY]
    refine (add_le_add hSn le_rfl).trans ?_
    exact_mod_cast (show nT + dY ≤ r + s by omega)

/-! ### Proper pushforward of the intersection product -/

/-- Given isomorphisms `f_*Torᵢ^{𝒪_X}(ℱ, f^*𝒢) ≅ Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)`, if every
`Torᵢ^{𝒪_X}(ℱ, f^*𝒢)` has support of delta-dimension at most `n`, then so has every
`Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)`. -/
theorem schemeDeltaDimension_reducedSupport_torSheaf_pushforward_le (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y)
    (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX) (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (G : Y.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G)
    (hpF : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F)) (n : ℤ)
    (hFn : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)).subschemeι ≫ sX)
          ≤ (n : EInt))
    (hpT : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj
        (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)))
    (hTor : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      (Scheme.Modules.pushforward f).obj
          (torSheaf X F ((Scheme.Modules.pullback f).obj G) i) ≅
        torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i)
    (i : ℕ) :
    haveI := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G hpF
      hG i
    schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i)).subschemeι ≫ sY)
        ≤ (n : EInt) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have hlnX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hcX := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
    (isCoherent_pullback f G) i
  have hcP := hpT i
  have hcY := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G hpF
    hG i
  exact schemeDeltaDimension_reducedSupport_le_of_iso (fieldChowSituation K) sY (hTor i) n
    (schemeDeltaDimension_reducedSupport_pushforward_le (fieldChowSituation K) sX sY f hbase
      (torSheaf X F ((Scheme.Modules.pullback f).obj G) i) (hFn i))

/-- Proper pushforward commutes with the alternating sums of `Tor`-cycles, once the terms
`f_*[Torᵢ^{𝒪_X}(ℱ, f^*𝒢)]_n` and `[Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)]_n` agree. -/
private theorem properPushforward_intersectionProductCycleGroup_of_terms (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y)
    (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX) (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (G : Y.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G)
    (hpF : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F)) (n : ℤ)
    (hFn : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)).subschemeι ≫ sX)
          ≤ (n : EInt))
    (hpT : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj
        (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)))
    (hGn' : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G hpF
        hG i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i)).subschemeι ≫ sY)
          ≤ (n : EInt))
    (hkey : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) i
      haveI := hpT i
      haveI := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G hpF
        hG i
      cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY
          ((Scheme.Modules.pushforward f).obj (torSheaf X F ((Scheme.Modules.pullback f).obj G) i))
          n (schemeDeltaDimension_reducedSupport_pushforward_le (fieldChowSituation K) sX sY f
            hbase (torSheaf X F ((Scheme.Modules.pullback f).obj G) i) (hFn i)) =
        cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY
          (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i) n (hGn' i)) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    properPushforward (fieldChowSituation K) sX sY f hbase n
        (intersectionProductCycleGroup (fieldChowSituation K) sX hX F
          ((Scheme.Modules.pullback f).obj G) hF (isCoherent_pullback f G) n hFn) =
      intersectionProductCycleGroup (fieldChowSituation K) sY hY
        ((Scheme.Modules.pushforward f).obj F) G hpF hG n hGn' := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have hlnX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hcG : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pullback f).obj G) :=
    isCoherent_pullback f G
  have hregX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    ((isRegular_iff_regular_stalks X).1 hX).2
  obtain ⟨dX, hdX⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety K sX
  have hαfin : Function.HasFiniteSupport (fun i : ℕ => ((-1 : ℤ) ^ i) •
      (have := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        hcG i
       cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX
         (torSheaf X F ((Scheme.Modules.pullback f).obj G) i) n (hFn i))) := by
    refine Set.Finite.subset (Set.finite_Iic dX) fun i hi ↦ ?_
    by_contra hle
    refine hi (Subtype.ext ?_)
    exact torSheafCycle_eq_zero_of_lt (fieldChowSituation K) sX hX F
      ((Scheme.Modules.pullback f).obj G) hF hcG n hFn hregX dX (le_of_eq hdX) i
      (by simpa using hle)
  have hterm : ∀ i : ℕ,
      properPushforward (fieldChowSituation K) sX sY f hbase n
          (((-1 : ℤ) ^ i) •
            (have := isCoherent_torSheaf_of_isRegular X hX F
              ((Scheme.Modules.pullback f).obj G) hF hcG i
             cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX
               (torSheaf X F ((Scheme.Modules.pullback f).obj G) i) n (hFn i))) =
        ((-1 : ℤ) ^ i) •
          (have := isCoherent_torSheaf_of_isRegular Y hY
            ((Scheme.Modules.pushforward f).obj F) G hpF hG i
           cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY
             (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i) n (hGn' i)) := by
    intro i
    have hcX := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
      hcG i
    have hcP := hpT i
    have hcY := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G
      hpF hG i
    rw [← properPushforwardHom_apply, map_zsmul, properPushforwardHom_apply,
      properPushforward_cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX sY f hbase
        (torSheaf X F ((Scheme.Modules.pullback f).obj G) i) n (hFn i)]
    exact congrArg _ (hkey i)
  have hγfin : Function.HasFiniteSupport (fun i : ℕ => ((-1 : ℤ) ^ i) •
      (have := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G
        hpF hG i
       cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY
         (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i) n (hGn' i))) := by
    refine Set.Finite.subset hαfin fun i hi ↦ ?_
    simp only [Function.mem_support] at hi ⊢
    intro h
    exact hi (by rw [← hterm i, h, properPushforward_zero])
  rw [intersectionProductCycleGroup_eq_finsum (fieldChowSituation K) sX hX F
      ((Scheme.Modules.pullback f).obj G) hF hcG n hFn hαfin,
    ← properPushforwardHom_apply, AddMonoidHom.map_finsum _ hαfin,
    intersectionProductCycleGroup_eq_finsum (fieldChowSituation K) sY hY
      ((Scheme.Modules.pushforward f).obj F) G hpF hG n hGn' hγfin]
  exact finsum_congr fun i => by rw [properPushforwardHom_apply]; exact hterm i

/-- Let `f : X ⟶ Y` be a flat proper morphism of nonsingular varieties over a field, `ℱ` a
coherent `𝒪_X`-module with coherent direct image and `𝒢` a coherent `𝒪_Y`-module, and suppose
given isomorphisms `f_*Torᵢ^{𝒪_X}(ℱ, f^*𝒢) ≅ Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)`. Then proper pushforward
carries the intersection product of `ℱ` and `f^*𝒢` to the intersection product of `f_*ℱ` and `𝒢`:

`f_*(∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(ℱ, f^*𝒢)]_n) = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)]_n`. -/
theorem properPushforward_intersectionProductCycleGroup (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y)
    (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX) (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (G : Y.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G)
    (hpF : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F)) (n : ℤ)
    (hFn : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)).subschemeι ≫ sX)
          ≤ (n : EInt))
    (hpT : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj
        (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)))
    (hTor : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      (Scheme.Modules.pushforward f).obj
          (torSheaf X F ((Scheme.Modules.pullback f).obj G) i) ≅
        torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    properPushforward (fieldChowSituation K) sX sY f hbase n
        (intersectionProductCycleGroup (fieldChowSituation K) sX hX F
          ((Scheme.Modules.pullback f).obj G) hF (isCoherent_pullback f G) n hFn) =
      intersectionProductCycleGroup (fieldChowSituation K) sY hY
        ((Scheme.Modules.pushforward f).obj F) G hpF hG n
        (schemeDeltaDimension_reducedSupport_torSheaf_pushforward_le K sX sY hX hY f hbase F hF
          G hG hpF n hFn hpT hTor) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have hlnX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  exact properPushforward_intersectionProductCycleGroup_of_terms K sX sY hX hY f hbase F hF G hG hpF
    n hFn hpT _ fun i => by
      have := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G hpF
        hG i
      have := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) i
      have := hpT i
      exact cycleAssociatedToCoherentSheaf_eq_of_iso (fieldChowSituation K) sY (hTor i) n _ _

/-! ### Without hypotheses on the direct image -/

/-- Let `f : X ⟶ Y` be a flat proper morphism of varieties over a field with `dim X = dim Y + e`,
let `ℱ` be a coherent `𝒪_X`-module whose support has dimension at most `r` and `𝒢` a coherent
`𝒪_Y`-module whose support has dimension at most `s`, and assume that `Supp(ℱ)` and
`f^{-1}(Supp(𝒢))` meet in dimension at most `r + (s + e) - dim X`. Then the cycles
`f_*[ℱ]_r = [f_*ℱ]_r` and `[𝒢]_s` intersect properly. -/
@[stacks 0B10 "the properness clause for `α = [ℱ]_r` and `β = [𝒢]_s`"]
theorem intersectProperly_coherentSheafCycle_pushforward_unconditional (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (F : X.Modules)
    [F.IsCoherent] (G : Y.Modules) [G.IsCoherent] (r s : ℕ)
    (hFr : schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport F).subschemeι ≫ sX) ≤ ((r : ℤ) : EInt))
    (hGs : schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport G).subschemeι ≫ sY) ≤ ((s : ℤ) : EInt))
    (hFG : topologicalKrullDim
        (SheafOfModules.supp F ∩ f.base ⁻¹' SheafOfModules.supp G : Set X) +
      topologicalKrullDim X ≤ (r : WithBot ℕ∞) + ((s + e : ℕ) : WithBot ℕ∞)) :
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI := AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    AlgebraicCycle.IntersectProperly
      (coherentSheafCycle (fieldChowSituation K) sY ((Scheme.Modules.pushforward f).obj F)
        (r : ℤ)
        (schemeDeltaDimension_reducedSupport_pushforward_le (fieldChowSituation K) sX sY f hbase
          F hFr))
      (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ) hGs) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  exact intersectProperly_coherentSheafCycle_pushforward K sX sY f hbase e he F G r s hFr hGs hFG

/-- Let `f : X ⟶ Y` be a flat proper morphism of nonsingular varieties over a field. For a
coherent `𝒪_X`-module `ℱ` and a coherent `𝒪_Y`-module `𝒢`, proper pushforward carries the
intersection product of `ℱ` and `f^*𝒢` to the intersection product of `f_*ℱ` and `𝒢`:

`f_*(∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(ℱ, f^*𝒢)]_n) = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)]_n`.

Taking `n = r + s - dim Y`, for supports of dimension at most `r` and `s` and `e = dim X - dim Y`,
this is `f_*([ℱ]_r · [f^*𝒢]_{s+e}) = [f_*ℱ]_r · [𝒢]_s`, that is `f_*(α · f^*β) = f_*(α) · β`. -/
@[stacks 0B10 "the identity `f_*(α) · β = f_*(α · f^*β)` for `α = [ℱ]_r` and `β = [𝒢]_s`, \
both products read by the Tor formula `∑ᵢ (-1)ⁱ [Torᵢ]_n` of Stacks 0AZR"]
theorem properPushforward_intersectionProductCycleGroup_unconditional (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y)
    (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX) (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (G : Y.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : ℤ)
    (hFn : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)).subschemeι ≫ sX)
          ≤ (n : EInt)) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    properPushforward (fieldChowSituation K) sX sY f hbase n
        (intersectionProductCycleGroup (fieldChowSituation K) sX hX F
          ((Scheme.Modules.pullback f).obj G) hF (isCoherent_pullback f G) n hFn) =
      intersectionProductCycleGroup (fieldChowSituation K) sY hY
        ((Scheme.Modules.pushforward f).obj F) G
        (@AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward _ _ f _ _ F hF) hG n
        (schemeDeltaDimension_reducedSupport_torSheaf_pushforward_le_of_bound K sX sY hX hY f
          hbase F hF G hG n hFn) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have hlnX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hlnY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hpF := @AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward _ _ f _ _ F hF
  have hpT : ∀ i : ℕ, _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj
      (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)) := fun i =>
    haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
      (isCoherent_pullback f G) i
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f _
  exact properPushforward_intersectionProductCycleGroup_of_terms K sX sY hX hY f hbase F hF G hG hpF
    n hFn hpT _ fun i => by
      have := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) i
      have := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G hpF
        hG i
      have := hpT i
      exact cycleAssociatedToCoherentSheaf_pushforward_torSheaf_eq K sX sY hX hY f hbase F hF G hG
        n hFn i

end Stacks.Intersection.ProjectionFormula

end
