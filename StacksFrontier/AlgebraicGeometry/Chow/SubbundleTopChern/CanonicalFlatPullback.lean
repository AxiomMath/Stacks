module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.Global
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLoci
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback to a vector bundle of locally constant rank is canonical

Let `ℱ` be a finite locally free module on `X`, of locally constant rank, and let
`p : 𝐕(ℱ^∨) ⟶ X` be the projection of its vector bundle. Over an open `T ⊆ X` on which `ℱ` has
constant rank `r` the restriction `p^{-1}(T) ⟶ T` is flat of relative dimension `r`, and flat
pullback `A_{d-r}(T) ⟶ A_d(p^{-1}(T))` is defined (Stacks 02S1). The flat pullback
`p^* : ∏_m A_m(X) ⟶ ∏_d A_d(𝐕(ℱ^∨))` is the family `x` characterized by

  `x_d|_{p^{-1}(T)} = (p|_{p^{-1}(T)})^*(β_{d-r}|_T)`

for every such `T` (`Stacks.Chow.IsDualBundleFlatPullback`). Such an `x` exists and is unique:
it is unique because `𝐕(ℱ^∨)` is covered by the open and closed pieces lying over the rank loci
of `ℱ`, and it exists because the piecewise construction
`Stacks.Chow.dualBundleFlatPullback` over *any* decomposition of `X` into open and closed pieces
of constant rank satisfies it, flat pullback commuting with restriction to opens (Stacks 02RD).
Consequently the piecewise construction does not depend on the decomposition, and when `ℱ` has
constant rank `r` on all of `X` it is the flat pullback `p^*` of relative dimension `r`.

This makes the `p^*` of Stacks 0FAA the genuine flat pullback, and the tag is restated here with
the canonical `p^*`.

## Main definitions

* `Stacks.Chow.IsDualBundleFlatPullback` — the defining property of `p^*β`.
* `Stacks.Chow.canonicalDualBundleFlatPullback` — `p^*β`, built over the rank loci of `ℱ`.

## Main results

* `Stacks.Chow.isDualBundleFlatPullback_dualBundleFlatPullback` — the piecewise construction over
  any decomposition has the defining property.
* `Stacks.Chow.eq_of_isDualBundleFlatPullback` — the defining property determines `p^*β`.
* `Stacks.Chow.dualBundleFlatPullback_eq_canonical` — the piecewise construction is independent
  of the decomposition.
* `Stacks.Chow.canonicalDualBundleFlatPullback_eq_dualBundlePullback` — for `ℱ` of constant rank
  `r`, `p^*` is the flat pullback of relative dimension `r`.
* `Stacks.Chow.subbundleEmbedding_pushforward_canonicalDualBundleFlatPullback` — **Stacks 0FAA**
  with the canonical flat pullbacks.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Relative dimension is unique on a nonempty source -/

/-- A morphism with nonempty source has at most one relative dimension. -/
theorem RelativeDimension.eq_of_nonempty {A B : Scheme.{u}} {f : A ⟶ B} [LocallyOfFiniteType f]
    [Nonempty A] {r r' : ℕ} (hr : AlgebraicGeometry.RelativeDimension f r)
    (hr' : AlgebraicGeometry.RelativeDimension f r') : r = r' := by
  obtain ⟨a⟩ := ‹Nonempty A›
  have hne : Nonempty (f.fiber (f.base a)) := ⟨f.asFiber a⟩
  exact_mod_cast (hr _ hne).2.symm.trans (hr' _ hne).2

/-! ### Transport lemmas -/

section Congr

variable (C : ChowSituation.{u})

/-- Restriction of a cycle class along an open immersion `j : U ⟶ X` does not depend, up to
`HEq`, on the choice of equal structure morphisms `U ⟶ S`. -/
theorem chowGroupRestrict_heq_structure {X U : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {sU sU' : U ⟶ C.S} [LocallyOfFiniteType sU]
    [LocallyOfFiniteType sU'] (hsU : sU = sU') (j : U ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ sX = sU) (hj' : j ≫ sX = sU') (k : ℤ) (x : chowGroup C sX k) :
    chowGroupRestrict C sX sU j hj k x ≍ chowGroupRestrict C sX sU' j hj' k x := by
  subst hsU
  rfl

/-- Flat pullback along `q` of relative dimension `r` agrees, up to `HEq`, with flat pullback of
relative dimension `r'` when `r = r'`, on classes of degrees `k = k'` that agree up to `HEq`. -/
theorem flatPullbackChowOfRelativeDimension_heq_of_relativeDimension_eq {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (q : A ⟶ B)
    [LocallyOfFiniteType q] [Flat q] (hq : q ≫ sB = sA) {r r' : ℕ} (hrr : r = r')
    (hr : AlgebraicGeometry.RelativeDimension q r) (hr' : AlgebraicGeometry.RelativeDimension q r')
    {k k' : ℤ} (hk : k = k') {x : chowGroup C sB k} {x' : chowGroup C sB k'} (hx : x ≍ x') :
    flatPullbackChowOfRelativeDimension C sA sB q hq r hr k x ≍
      flatPullbackChowOfRelativeDimension C sA sB q hq r' hr' k' x' := by
  subst hrr hk
  cases hx
  rfl

end Congr

/-! ### The defining property of the flat pullback -/

section Characterization

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- **The defining property of the flat pullback `p^*β ∈ ∏_d A_d(𝐕(ℱ^∨))`** of
`β ∈ ∏_m A_m(X)` along the projection `p : 𝐕(ℱ^∨) ⟶ X`. For every open immersion `g : T ⟶ X` and
every presentation of `p^{-1}(T)` as a cartesian square
`T' --m--> 𝐕(ℱ^∨)`, `q : T' ⟶ T`, `p`, `g` with `q` flat of relative dimension `r` (which forces
`ℱ` to have rank `r` on the image of `q`), the restriction of `x_d` to `T'` is the flat pullback
`q^*(β_{d-r}|_T)` of Stacks 02S1. -/
def IsDualBundleFlatPullback (β : ∀ m : ℤ, chowGroup C sX m)
    (x : ∀ d : ℤ, chowGroup C (dualVectorBundleToBase F ≫ sX) d) : Prop :=
  ∀ ⦃T T' : Scheme.{u}⦄ (g : T ⟶ X) [IsOpenImmersion g] (q : T' ⟶ T) [LocallyOfFiniteType q]
    [Flat q] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension q r)
    (m : T' ⟶ dualVectorBundle F) [IsOpenImmersion m]
    (hsq : IsPullback m q (dualVectorBundleToBase F) g) (d : ℤ),
    chowGroupRestrict C (dualVectorBundleToBase F ≫ sX) (q ≫ g ≫ sX) m
        (by rw [← Category.assoc, hsq.w, Category.assoc]) d (x d) =
      chowGroupCast C (q ≫ g ≫ sX) (show d - (r : ℤ) + (r : ℤ) = d by ring)
        (flatPullbackChowOfRelativeDimension C (q ≫ g ≫ sX) (g ≫ sX) q rfl r hr (d - r)
          (chowGroupRestrict C sX (g ≫ sX) g rfl (d - r) (β (d - r))))

variable {C sX F}

/-- **The defining property determines the flat pullback.** Two families with the defining
property agree: they agree over each rank locus of `ℱ`, and those decompose `𝐕(ℱ^∨)`. -/
theorem eq_of_isDualBundleFlatPullback {β : ∀ m : ℤ, chowGroup C sX m}
    {x y : ∀ d : ℤ, chowGroup C (dualVectorBundleToBase F ≫ sX) d}
    (hx : IsDualBundleFlatPullback C sX F β x) (hy : IsDualBundleFlatPullback C sX F β y) :
    x = y := by
  funext d
  refine bundleChow_ext C sX F (rankLociFamily F) (isClopenDecomposition_rankLociFamily F)
    fun i ↦ ?_
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily F i).ι).obj F) i.down :=
    isFiniteLocallyFreeOfRank_pullback_rankLocus F i.down
  have := locallyOfFiniteType_dualVectorBundleToBase
    ((Scheme.Modules.pullback (rankLociFamily F i).ι).obj F) i.down
  have := flat_dualVectorBundleToBase
    ((Scheme.Modules.pullback (rankLociFamily F i).ι).obj F) i.down
  have h := fun z (hz : IsDualBundleFlatPullback C sX F β z) ↦
    hz (rankLociFamily F i).ι _ i.down (relativeDimension_dualVectorBundleToBase _ i.down)
      (dualBundleBaseChangeMap (rankLociFamily F i).ι F)
      (isPullback_dualBundleBaseChangeMap (rankLociFamily F i).ι F) d
  exact (h x hx).trans (h y hy).symm

end Characterization

/-! ### The piecewise construction has the defining property -/

/-- Two iterated restrictions of a Chow class agree when the composite open immersions do. -/
private theorem chowGroupRestrict_comp_congr (C : ChowSituation.{u}) {X U U' V : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sU : U ⟶ C.S} [LocallyOfFiniteType sU]
    {sU' : U' ⟶ C.S} [LocallyOfFiniteType sU'] {sV : V ⟶ C.S} [LocallyOfFiniteType sV]
    {j : U ⟶ X} [IsOpenImmersion j] {i : V ⟶ U} [IsOpenImmersion i] {j' : U' ⟶ X}
    [IsOpenImmersion j'] {i' : V ⟶ U'} [IsOpenImmersion i'] {hj : j ≫ sX = sU}
    {hi : i ≫ sU = sV} {hj' : j' ≫ sX = sU'} {hi' : i' ≫ sU' = sV} (h : i ≫ j = i' ≫ j') {k : ℤ}
    (x : chowGroup C sX k) :
    chowGroupRestrict C sU sV i hi k (chowGroupRestrict C sX sU j hj k x) =
      chowGroupRestrict C sU' sV i' hi' k (chowGroupRestrict C sX sU' j' hj' k x) := by
  rw [chowGroupRestrict_comp, chowGroupRestrict_comp]
  exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _ h _) _

/-- Restriction of a degree-cast class is `HEq` to the restriction of the original class. -/
private theorem chowGroupRestrict_cast_heq (C : ChowSituation.{u}) {X U : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sU : U ⟶ C.S} [LocallyOfFiniteType sU]
    (j : U ⟶ X) [IsOpenImmersion j] {hj : j ≫ sX = sU} {k l : ℤ} (h : k = l)
    (x : chowGroup C sX k) :
    chowGroupRestrict C sX sU j hj l (chowGroupCast C sX h x) ≍
      chowGroupRestrict C sX sU j hj k x := by
  subst h
  rfl

section Existence

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
  {I : Type u} (U : I → X.Opens) (hU : IsClopenDecomposition U) (ρ : I → ℕ)
  (hρ : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((Scheme.Modules.pullback (U i).ι).obj F) (ρ i))

/-- **The piecewise flat pullback has the defining property of `p^*`.** Let `X = ∐ U_i` be any
decomposition into open and closed pieces on which `ℱ` has constant rank `ρ_i`. For an open
`T ⊆ X` with `p^{-1}(T) ⟶ T` flat of relative dimension `r`, cut `p^{-1}(T)` into the pieces
`V_i` over `T ∩ U_i`. On `V_i` the class `(p^*β)_d` restricts to the restriction of
`p_i^*(β_{d-ρ_i}|_{U_i})`, which by Stacks 02RD is the flat pullback along `V_i ⟶ T ∩ U_i` of
`β_{d-ρ_i}|_{T ∩ U_i}`; and `ρ_i = r` as soon as `V_i` is nonempty, the relative dimension of
`V_i ⟶ T ∩ U_i` being both. -/
theorem isDualBundleFlatPullback_dualBundleFlatPullback (β : ∀ m : ℤ, chowGroup C sX m) :
    IsDualBundleFlatPullback C sX F β (dualBundleFlatPullback C sX F U hU ρ hρ β) := by
  intro T T' g _ q _ _ r hr m _ hsq d
  let W : I → T.Opens := fun i ↦ g ⁻¹ᵁ U i
  let V : I → T'.Opens := fun i ↦ q ⁻¹ᵁ W i
  have hV : IsClopenDecomposition fun i ↦ (V i).ι.opensRange := by
    simpa only [Scheme.Opens.opensRange_ι] using (hU.preimage g).preimage q
  rw [← sub_eq_zero]
  refine eq_zero_of_chowGroupRestrict_eq_zero C (q ≫ g ≫ sX) (fun i ↦ (V i).ι ≫ q ≫ g ≫ sX)
    (fun i ↦ (V i).ι) (fun i ↦ rfl) hV d _ fun i ↦ ?_
  rw [map_sub, sub_eq_zero]
  rcases isEmpty_or_nonempty (V i).toScheme with hne | hne
  · have := subsingleton_chowGroup_of_isEmpty C ((V i).ι ≫ q ≫ g ≫ sX) d
    exact Subsingleton.elim _ _
  have := hρ i
  have := locallyOfFiniteType_dualVectorBundleToBase
    ((Scheme.Modules.pullback (U i).ι).obj F) (ρ i)
  have := flat_dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) (ρ i)
  -- the pieces and their squares
  let ψ : (W i).toScheme ⟶ (U i).toScheme := g ∣_ U i
  let qi : (V i).toScheme ⟶ (W i).toScheme := q ∣_ W i
  have sqψ : IsPullback (W i).ι ψ g (U i).ι := (isPullback_morphismRestrict g (U i)).flip
  have sqV : IsPullback (V i).ι qi q (W i).ι := (isPullback_morphismRestrict q (W i)).flip
  have : IsOpenImmersion ψ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqψ ‹_›
  have : LocallyOfFiniteType qi :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqV ‹_›
  have : Flat qi := MorphismProperty.of_isPullback (P := @Flat) sqV ‹_›
  have sqbig : IsPullback ((V i).ι ≫ m) qi (dualVectorBundleToBase F) ((W i).ι ≫ g) :=
    sqV.paste_horiz hsq
  have bsq := isPullback_dualBundleBaseChangeMap (U i).ι F
  have hw : ((V i).ι ≫ m) ≫ dualVectorBundleToBase F = (qi ≫ ψ) ≫ (U i).ι := by
    rw [sqbig.w, Category.assoc, morphismRestrict_ι]
  let φ := bsq.lift ((V i).ι ≫ m) (qi ≫ ψ) hw
  have hφ1 : φ ≫ dualBundleBaseChangeMap (U i).ι F = (V i).ι ≫ m := bsq.lift_fst _ _ hw
  have hφ2 : φ ≫ dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) = qi ≫ ψ :=
    bsq.lift_snd _ _ hw
  have sqφ :
      IsPullback φ qi (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F)) ψ := by
    refine IsPullback.of_right ?_ hφ2 bsq
    rw [hφ1, morphismRestrict_ι]
    exact sqbig
  have : IsOpenImmersion φ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqφ.flip ‹_›
  have hri : AlgebraicGeometry.RelativeDimension qi (ρ i) :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sqφ
      (relativeDimension_dualVectorBundleToBase _ (ρ i))
  have hri' : AlgebraicGeometry.RelativeDimension qi r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sqV hr
  obtain rfl : ρ i = r := RelativeDimension.eq_of_nonempty hri hri'
  -- structure morphisms
  have hψs : ψ ≫ (U i).ι ≫ sX = (W i).ι ≫ g ≫ sX := morphismRestrict_ι_assoc g (U i) sX
  have hqis : qi ≫ (W i).ι ≫ g ≫ sX = (V i).ι ≫ q ≫ g ≫ sX :=
    morphismRestrict_ι_assoc q (W i) (g ≫ sX)
  have hφs : φ ≫ dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫
      (U i).ι ≫ sX = (V i).ι ≫ q ≫ g ≫ sX := by
    rw [reassoc_of% hφ2, hψs, hqis]
  -- the left hand side
  have e1 : chowGroupRestrict C (q ≫ g ≫ sX) ((V i).ι ≫ q ≫ g ≫ sX) (V i).ι rfl d
      (chowGroupRestrict C (dualVectorBundleToBase F ≫ sX) (q ≫ g ≫ sX) m
        (by rw [← Category.assoc, hsq.w, Category.assoc]) d
        (dualBundleFlatPullback C sX F U hU (ρ ·) hρ β d)) =
      chowGroupRestrict C
        (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫ ((U i).ι ≫ sX))
        ((V i).ι ≫ q ≫ g ≫ sX) φ hφs d
        (chowGroupRestrict C (dualVectorBundleToBase F ≫ sX)
          (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫ ((U i).ι ≫ sX))
          (dualBundleBaseChangeMap (U i).ι F)
          (dualBundleBaseChangeMap_comp_structure C sX F (U i).ι) d
          (dualBundleFlatPullback C sX F U hU (ρ ·) hρ β d)) :=
    chowGroupRestrict_comp_congr C hφ1.symm _
  rw [dualBundleFlatPullback_restrict] at e1
  have e2 := chowGroupRestrict_cast_heq C φ (hj := hφs) (show d - (ρ i : ℤ) + (ρ i : ℤ) = d by ring)
    (dualBundlePullback C ((U i).ι ≫ sX) ((Scheme.Modules.pullback (U i).ι).obj F) (ρ i)
      (d - ρ i) (chowGroupRestrict C sX ((U i).ι ≫ sX) (U i).ι rfl (d - ρ i) (β (d - ρ i))))
  have e3 := chowGroupRestrict_flatPullbackChow C
    (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫ ((U i).ι ≫ sX))
    ((U i).ι ≫ sX) ((V i).ι ≫ q ≫ g ≫ sX) ((W i).ι ≫ g ≫ sX)
    (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F)) rfl (ρ i)
    (relativeDimension_dualVectorBundleToBase _ (ρ i)) φ hφs ψ hψs qi hqis sqφ hri (d - ρ i)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (chowGroupRestrict C sX ((U i).ι ≫ sX) (U i).ι rfl (d - ρ i) (β (d - ρ i)))
  -- the right hand side
  have e4 := chowGroupRestrict_cast_heq C (V i).ι (hj := rfl)
    (show d - (ρ i : ℤ) + (ρ i : ℤ) = d by ring)
    (flatPullbackChowOfRelativeDimension C (q ≫ g ≫ sX) (g ≫ sX) q rfl (ρ i) hr (d - ρ i)
      (chowGroupRestrict C sX (g ≫ sX) g rfl (d - ρ i) (β (d - ρ i))))
  have e5 := chowGroupRestrict_flatPullbackChow C (q ≫ g ≫ sX) (g ≫ sX)
    ((V i).ι ≫ q ≫ g ≫ sX) ((W i).ι ≫ g ≫ sX) q rfl (ρ i) hr (V i).ι rfl (W i).ι rfl qi hqis
    sqV hri (d - ρ i)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (chowGroupRestrict C sX (g ≫ sX) g rfl (d - ρ i) (β (d - ρ i)))
  -- the two restrictions of `β` agree
  have e6 : chowGroupRestrict C ((U i).ι ≫ sX) ((W i).ι ≫ g ≫ sX) ψ hψs (d - ρ i)
      (chowGroupRestrict C sX ((U i).ι ≫ sX) (U i).ι rfl (d - ρ i) (β (d - ρ i))) =
      chowGroupRestrict C (g ≫ sX) ((W i).ι ≫ g ≫ sX) (W i).ι rfl (d - ρ i)
        (chowGroupRestrict C sX (g ≫ sX) g rfl (d - ρ i) (β (d - ρ i))) := by
    exact chowGroupRestrict_comp_congr C (morphismRestrict_ι g (U i)) _
  refine eq_of_heq ((heq_of_eq e1).trans (e2.trans ((heq_of_eq e3).trans ?_)))
  refine HEq.trans ?_ e4.symm
  refine HEq.trans ?_ (heq_of_eq e5.symm)
  rw [e6]

end Existence

/-! ### The canonical flat pullback -/

section Canonical

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- **The flat pullback `p^* : ∏_m A_m(X) ⟶ ∏_d A_d(𝐕(ℱ^∨))`** along the projection of the vector
bundle of a finite locally free module of locally constant rank: the family with the defining
property `Stacks.Chow.IsDualBundleFlatPullback`, realized over the decomposition of `X` into the
rank loci of `ℱ`. By `Stacks.Chow.dualBundleFlatPullback_eq_canonical` any other decomposition
into open and closed pieces of constant rank gives the same family. -/
def canonicalDualBundleFlatPullback (β : ∀ m : ℤ, chowGroup C sX m) (d : ℤ) :
    chowGroup C (dualVectorBundleToBase F ≫ sX) d :=
  dualBundleFlatPullback C sX F (rankLociFamily F) (isClopenDecomposition_rankLociFamily F)
    (fun i ↦ i.down) (fun i ↦ isFiniteLocallyFreeOfRank_pullback_rankLocus F i.down) β d

/-- The canonical flat pullback has the defining property. -/
theorem isDualBundleFlatPullback_canonical (β : ∀ m : ℤ, chowGroup C sX m) :
    IsDualBundleFlatPullback C sX F β (canonicalDualBundleFlatPullback C sX F β) :=
  isDualBundleFlatPullback_dualBundleFlatPullback C sX F (rankLociFamily F)
    (isClopenDecomposition_rankLociFamily F) (fun i ↦ i.down)
    (fun i ↦ isFiniteLocallyFreeOfRank_pullback_rankLocus F i.down) β

/-- **`p^*β` is the unique family with the defining property.** -/
theorem isDualBundleFlatPullback_iff (β : ∀ m : ℤ, chowGroup C sX m)
    (x : ∀ d : ℤ, chowGroup C (dualVectorBundleToBase F ≫ sX) d) :
    IsDualBundleFlatPullback C sX F β x ↔ x = canonicalDualBundleFlatPullback C sX F β :=
  ⟨fun hx ↦ eq_of_isDualBundleFlatPullback hx (isDualBundleFlatPullback_canonical C sX F β),
    fun hx ↦ hx ▸ isDualBundleFlatPullback_canonical C sX F β⟩

/-- **The piecewise flat pullback does not depend on the decomposition.** Over any decomposition
`X = ∐ U_i` into open and closed pieces on which `ℱ` has constant rank, the piecewise flat
pullback `Stacks.Chow.dualBundleFlatPullback` is the canonical flat pullback `p^*`. -/
theorem dualBundleFlatPullback_eq_canonical {I : Type u} (U : I → X.Opens)
    (hU : IsClopenDecomposition U) (ρ : I → ℕ)
    (hρ : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (U i).ι).obj F) (ρ i)) (β : ∀ m : ℤ, chowGroup C sX m) :
    dualBundleFlatPullback C sX F U hU ρ hρ β = canonicalDualBundleFlatPullback C sX F β :=
  (isDualBundleFlatPullback_iff C sX F β _).1
    (isDualBundleFlatPullback_dualBundleFlatPullback C sX F U hU ρ hρ β)

/-- The flat pullback along `q` of the restriction of `y` along `𝟙 X` does not depend, up to
`HEq`, on the choice of equal structure morphisms `X ⟶ S`. -/
theorem flatPullbackChowOfRelativeDimension_restrict_id_heq {A : Scheme.{u}} (q : A ⟶ X)
    [LocallyOfFiniteType q] [Flat q] {s s' : X ⟶ C.S} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] [LocallyOfFiniteType (q ≫ s)] [LocallyOfFiniteType (q ≫ s')]
    (hs : s = s') (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension q r) (k : ℤ)
    (h₁ : 𝟙 X ≫ sX = s) (h₂ : 𝟙 X ≫ sX = s') (y : chowGroup C sX k) :
    flatPullbackChowOfRelativeDimension C (q ≫ s) s q rfl r hr k
        (chowGroupRestrict C sX s (𝟙 X) h₁ k y) ≍
      flatPullbackChowOfRelativeDimension C (q ≫ s') s' q rfl r hr k
        (chowGroupRestrict C sX s' (𝟙 X) h₂ k y) := by
  subst hs
  rfl

/-- **For `ℱ` of constant rank `r`, `p^*` is the flat pullback of relative dimension `r`.** The
degree `d` part of `p^*β` is `p^*(β_{d-r})` for the flat pullback
`p^* : A_{d-r}(X) ⟶ A_d(𝐕(ℱ^∨))` of Stacks 02S1 along the projection, which is flat of
relative dimension `r`. -/
theorem canonicalDualBundleFlatPullback_eq_dualBundlePullback (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (β : ∀ m : ℤ, chowGroup C sX m) (d : ℤ) :
    canonicalDualBundleFlatPullback C sX F β d =
      chowGroupCast C _ (show d - (r : ℤ) + (r : ℤ) = d by ring)
        (dualBundlePullback C sX F r (d - r) (β (d - r))) := by
  have := locallyOfFiniteType_dualVectorBundleToBase F r
  have := flat_dualVectorBundleToBase F r
  have key := isDualBundleFlatPullback_canonical C sX F β (𝟙 X) (dualVectorBundleToBase F) r
    (relativeDimension_dualVectorBundleToBase F r) (𝟙 _)
    (IsPullback.id_horiz (dualVectorBundleToBase F)) d
  have hs : 𝟙 X ≫ sX = sX := Category.id_comp sX
  refine eq_of_heq ?_
  refine ((heq_of_eq (chowGroupRestrict_id C (dualVectorBundleToBase F ≫ sX) d _)).symm.trans
    (chowGroupRestrict_heq_structure C (dualVectorBundleToBase F ≫ sX)
      (sU := dualVectorBundleToBase F ≫ sX) (sU' := dualVectorBundleToBase F ≫ 𝟙 X ≫ sX)
      (by rw [hs]) (𝟙 _) (Category.id_comp _) (by rw [hs, Category.id_comp]) d _)).trans ?_
  refine (heq_of_eq key).trans ?_
  refine (chowGroupCast_heq C _ _ _).trans (HEq.trans ?_ (chowGroupCast_heq C _ _ _).symm)
  refine (flatPullbackChowOfRelativeDimension_restrict_id_heq C sX (dualVectorBundleToBase F) hs
    r _ (d - r) rfl hs (β (d - r))).trans ?_
  rw [chowGroupRestrict_id]
  rfl

end Canonical

/-! ### Stacks 0FAA with the canonical flat pullbacks -/

section Global

variable {X : Scheme.{u}} (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 0FAA.** Let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free
`𝒪_X`-modules, let `i : N' = Spec_X(Sym((𝒩')^∨)) ⟶ N = Spec_X(Sym(𝒩^∨))` be the closed embedding
and `p' : N' ⟶ X`, `p : N ⟶ X` the projections. For `α ∈ A_k(X)`,

  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`  in  `∏_d A_d(N)`.

The ranks may vary from component to component (they are locally constant), so `p` and `p'` have
locally constant relative dimension and both sides live in `∏_d A_d(N)`. The morphism `i` is a
closed immersion by `Stacks.Chow.isClosedImmersion_subbundleEmbedding_of_shortExact`, proved from
the short exact sequence. Here `(p')^*` and `p^*` are the flat pullbacks
`Stacks.Chow.canonicalDualBundleFlatPullback`: the unique families whose restriction over every
open of constant rank `r` is the flat pullback of relative dimension `r` of Stacks 02S1
(`Stacks.Chow.isDualBundleFlatPullback_iff`), equal to that flat pullback when the rank is
constant (`Stacks.Chow.canonicalDualBundleFlatPullback_eq_dualBundlePullback`). The class
`c_top(ℰ) ∩ α ∈ ∏_m A_m(X)` is the cap product with the top Chern class of Stacks 0FA4
(`Stacks.Chow.topChernCapFamily`), and `α` is read in `∏_m A_m(X)` in degree `k`. -/
@[stacks 0FAA "i_*(p')^*alpha = p^*(c_top(E) cap alpha) in prod_d CH_d(N), for a short exact \
sequence 0 -> N' -> N -> E -> 0 of finite locally free modules of arbitrary (locally constant) \
ranks and alpha in CH_k(X); p^*, (p')^* are the flat pullbacks along the projections, which have \
locally constant relative dimension, c_top(E) is the class of Tag 0FA4 and c_top(E) cap alpha the \
element of prod_m CH_m(X) with degree m part c_top(E)_{k-m} cap alpha"]
theorem subbundleEmbedding_pushforward_canonicalDualBundleFlatPullback (k : ℤ)
    (α : chowGroup C sX k) :
    haveI := isClosedImmersion_subbundleEmbedding_of_shortExact N' N E inc pr w hseq
    (fun d ↦ chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase N' ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding N' N inc)
        (subbundleEmbedding_comp_base N' N sX inc) d
        (canonicalDualBundleFlatPullback C sX N' (homogeneousChowFamily C sX k α) d)) =
      canonicalDualBundleFlatPullback C sX N (topChernCapFamily C sX E k α) := by
  have h := subbundleEmbedding_pushforward_dualBundleFlatPullback N' N E inc pr w hseq C sX k α
  rwa [dualBundleFlatPullback_eq_canonical, dualBundleFlatPullback_eq_canonical] at h

end Global

end Stacks.Chow

end
