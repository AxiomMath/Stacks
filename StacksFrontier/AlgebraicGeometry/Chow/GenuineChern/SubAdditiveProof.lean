module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Additivity
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleChow
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem

/-!
# The first Chern class along an invertible subsheaf

Let `0 ⟶ ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` be a short exact sequence of finite locally free modules on `X`, with
`ℳ` invertible, `𝒢` of rank `r + 2` and `𝒬` of rank `r + 1`. This file proves
`Stacks.Chow.GenuineChern.SubAdditive`:

  `c₁(𝒢) ∩ α = c₁(𝒬) ∩ α + c₁(ℳ) ∩ α`,

the first Chern class part of [Stacks, Tag 02UH].

The projective bundle `P(𝒬)` is a closed subscheme of `P(𝒢)` over `X`, with `𝒪_{P(𝒢)}(1)`
restricting to `𝒪_{P(𝒬)}(1)`, and it is the zero scheme of a regular section of an invertible
module `ℒ` on `P(𝒢)` with `π^*ℳ ⊗ ℒ ≅ 𝒪_{P(𝒢)}(1)` (the geometric input
`Stacks.Chow.GenuineChern.SubbundleHolds`). On Chow groups this gives

  `c₁(𝒪_{P(𝒢)}(1)) ∩ π_𝒢^*α = ι_*(π_𝒬^*α) + π_𝒢^*(c₁(ℳ) ∩ α)`

by [Stacks, Tag 02SP], [Stacks, Tag 02TR] for the divisor and [Stacks, Tag 02SS] for the twist
by `π^*ℳ`, and `Stacks.Chow.projectiveBundleProjection_succ_eq_of_divisor` turns that into the
displayed identity of first Chern classes.

## Main definitions

* `Stacks.Chow.GenuineChern.SubbundleHolds` — the geometry of `P(𝒬) ⊂ P(𝒢)`.

## Main results

* `Stacks.Chow.cap_flatPullback_eq_of_divisor` — the divisor identity on Chow groups.
* `Stacks.Chow.GenuineChern.subAdditive_of` — `Stacks.Chow.GenuineChern.SubAdditive`.

## References

* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Relative dimension is a property of the morphism, whatever proof of local finite type is
used to state it. -/
theorem relativeDimension_of_eq {A B : Scheme.{u}} {f g : A ⟶ B} [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (h : f = g) {d : ℕ} (hg : AlgebraicGeometry.RelativeDimension g d) :
    AlgebraicGeometry.RelativeDimension f d := by
  subst h; exact hg

section Divisor

variable (C : ChowSituation.{u}) {X PG PQ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sPG : PG ⟶ C.S) [LocallyOfFiniteType sPG] (πG : PG ⟶ X) [LocallyOfFiniteType πG] [Flat πG]
  (hsPG : πG ≫ sX = sPG) (sPQ : PQ ⟶ C.S) [LocallyOfFiniteType sPQ] (πQ : PQ ⟶ X)
  [LocallyOfFiniteType πQ] [Flat πQ] (hsPQ : πQ ≫ sX = sPQ) (q : ℕ)
  (hπG : AlgebraicGeometry.RelativeDimension πG (q + 1 + 1 - 1))
  (hπQ : AlgebraicGeometry.RelativeDimension πQ (q + 1 - 1))
  (hfacG : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPG sX πG hsPG (q + 1 + 1 - 1)
    hπG k)
  (hfacQ : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPQ sX πQ hsPQ (q + 1 - 1)
    hπQ k)
  (ι : PQ ⟶ PG) [IsClosedImmersion ι] (hι : ι ≫ sPG = sPQ) (hιπ : ι ≫ πG = πQ)
  (L : PG.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible PG.sheaf.obj PG.ringCatSheaf.property L]
  (s : L.sections)
  (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor πG
    (Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))))
  (e : (Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subscheme ≅ PQ)
  (he : e.hom ≫ ι = (Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι)

omit [LocallyOfFiniteType πG] [Flat πG] [LocallyOfFiniteType πQ] [Flat πQ]
  [IsClosedImmersion ι] in
include hιπ he in
/-- The structure morphism of the divisor to `X` is the projection of `PQ`, transported along `e`.
-/
theorem zeroScheme_subschemeι_comp_eq :
    (Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι ≫ πG = e.hom ≫ πQ := by
  rw [← he, Category.assoc, hιπ]

omit [Flat πG] [Flat πQ] [IsClosedImmersion ι] in
include hπQ hιπ he in
/-- The divisor has relative dimension `q` over `X`, being isomorphic to `PQ` over `X`. -/
theorem relativeDimension_zeroScheme_comp :
    AlgebraicGeometry.RelativeDimension
      ((Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι ≫ πG) q := by
  have h := AlgebraicGeometry.RelativeDimension.comp_of_flat e.hom πQ
    ((AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero e.hom).mp inferInstance)
    hπQ
  rw [Nat.zero_add] at h
  exact relativeDimension_of_eq (zeroScheme_subschemeι_comp_eq πG πQ ι hιπ L s e he) h

include hD hπQ hιπ he in
/-- **The cap with `ℒ` of a pullback is pushed forward from `PQ`** (Stacks 02TR for the divisor
`Z(s) ≅ PQ`): `c₁(ℒ) ∩ π_𝒢^*α = ι_*(π_𝒬^*α)`, in heterogeneous form. -/
theorem firstChernClassCapChow_eq_properChowPushforward_of_divisor (k : ℤ)
    (α : chowGroup C sX k) (d : ℤ) (hd : d + 1 = k + ((q + 1 + 1 - 1 : ℕ) : ℤ))
    (y : chowGroup C sPG (d + 1))
    (hy : y ≍ projectiveBundlePullback C sX sPG πG hsPG (q + 1 + 1) hπG hfacG k α)
    (z : chowGroup C sPQ d)
    (hz : z ≍ projectiveBundlePullback C sX sPQ πQ hsPQ (q + 1) hπQ hfacQ k α) :
    firstChernClassCapChow C d sPG L y =
      properChowPushforward C sPQ sPG ι hι d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d) z := by
  have := hD.2
  have hq := relativeDimension_zeroScheme_comp πG πQ q hπQ ι hιπ L s e he
  -- Stacks 02TR in the degrees it is stated in
  have h02TR := firstChernClassCapChow_flatPullbackChow_eq_divisor C sPG sX πG hsPG q hπG
    (k - 1) L s hD hq (chowGroupCast C sX (by omega) α)
    (chowGroupCast C sPG (by omega) y)
    ((chowGroupCast_heq C sPG _ y).trans (hy.trans (flatPullbackChow_heq C sPG sX πG hsPG _ hπG
      (fun m ↦ flatPullbackFactorsThroughRationalEquivalence_general C sPG sX πG hsPG _ hπG m)
      (by omega) (chowGroupCast_heq C sX _ α).symm)))
  refine chowGroup_eq_of_heq C sPG ?_
  refine (heq_apply_of_degree C sPG sPG (fun m ↦ m + 1) (fun m ↦ m)
    (fun m ↦ firstChernClassCapChow C m sPG L) (show d = k - 1 + 1 + (q : ℤ) by omega)
    (chowGroupCast_heq C sPG (show d + 1 = k - 1 + 1 + (q : ℤ) + 1 by omega) y).symm).trans ?_
  rw [h02TR]
  -- the pushforward from the divisor factors through `PQ`
  have hDι : (Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι =
      e.hom ≫ ι := he.symm
  have hpush : ∀ (m : ℤ)
      (x : chowGroup C ((Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι ≫ sPG) m),
      properChowPushforward C
          ((Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι ≫ sPG) sPG
          (Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι rfl m
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sPG _ rfl m) x =
        properChowPushforward C sPQ sPG ι hι m
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι m)
          (chowPushforwardOfIso C
            ((Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι ≫ sPG) sPQ e.hom
            (by rw [← hι, ← Category.assoc, he]) m x) := by
    intro m x
    have h := properChowPushforward_comp C
      ((Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι ≫ sPG) sPQ sPG e.hom ι
      (by rw [← hι, ← Category.assoc, he]) hι m
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sPQ _ _ m)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι m)
    have h' := congrFun (congrArg DFunLike.coe h) x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at h'
    rw [chowPushforwardOfIso, h']
    exact properChowPushforward_congr_hom C _ sPG hDι rfl _ m _ _ x
  rw [hpush]
  refine properChowPushforward_heq C sPQ sPG ι hι (by omega) ?_
  -- the pullback to the divisor, pushed to `PQ`, is the pullback to `PQ`
  have hsq : ((Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι ≫ πG) ≫ 𝟙 X =
      e.hom ≫ πQ := by
    rw [Category.comp_id, zeroScheme_subschemeι_comp_eq πG πQ ι hιπ L s e he]
  have hiso := flatPullbackChow_chowPushforwardOfIso C sX
    ((Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι ≫ sPG) sX sPQ (𝟙 X)
    (Category.id_comp sX) e.hom (by rw [← hι, ← Category.assoc, he])
    ((Stacks.Divisors.zeroScheme PG L (s.eval (.op ⊤))).subschemeι ≫ πG)
    (by rw [Category.assoc, hsPG]) πQ hsPQ hsq q hq hπQ (k - 1 + 1)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ _ q hq _)
    (hfacQ (k - 1 + 1)) (chowGroupCast C sX (by omega) α)
  rw [chowPushforwardOfIso_id] at hiso
  refine (heq_of_eq hiso.symm).trans ?_
  refine HEq.trans ?_ hz.symm
  exact flatPullbackChow_heq C sPQ sX πQ hsPQ _ hπQ hfacQ (by omega) (chowGroupCast_heq C sX _ α)

include hD hπQ hιπ he in
/-- **The divisor identity on Chow groups.** If `𝒯 ≅ π_𝒢^*ℳ ⊗ ℒ` with `Z(s) ≅ PQ` for a section `s`
of `ℒ`, then

  `c₁(𝒯) ∩ π_𝒢^*α = ι_*(π_𝒬^*α) + π_𝒢^*(c₁(ℳ) ∩ α)`,

by Stacks 02SP for the tensor product, Stacks 02TR for the divisor and Stacks 02SS for `π_𝒢^*ℳ`.
This is the hypothesis `hdiv` of `Stacks.Chow.projectiveBundleProjection_succ_eq_of_divisor`. -/
theorem cap_flatPullback_eq_of_divisor (T : PG.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible PG.sheaf.obj PG.ringCatSheaf.property T]
    (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (eT : Scheme.Modules.tensorObj ((Scheme.Modules.pullback πG).obj M) L ≅ T) (k : ℤ)
    (α : chowGroup C sX k) (d : ℤ) (hd : d + 1 = k + ((q + 1 + 1 - 1 : ℕ) : ℤ))
    (y : chowGroup C sPG (d + 1))
    (hy : y ≍ projectiveBundlePullback C sX sPG πG hsPG (q + 1 + 1) hπG hfacG k α)
    (z : chowGroup C sPQ d)
    (hz : z ≍ projectiveBundlePullback C sX sPQ πQ hsPQ (q + 1) hπQ hfacQ k α)
    (w : chowGroup C sPG d)
    (hw : w ≍ projectiveBundlePullback C sX sPG πG hsPG (q + 1 + 1) hπG hfacG (k - 1)
      (firstChernClassCapChow C (k - 1) sX M (chowGroupCast C sX (by omega) α))) :
    firstChernClassCapChow C d sPG T y =
      properChowPushforward C sPQ sPG ι hι d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d) z +
        w := by
  have := isInvertible_presheaf_modulePullback M πG
  rw [← firstChernClassCapChow_congr C sPG d eT y, ← firstChernClassCapChow_tensorObj, add_comm,
    firstChernClassCapChow_eq_properChowPushforward_of_divisor C sX sPG πG hsPG sPQ πQ hsPQ q
      hπG hπQ hfacG hfacQ ι hι hιπ L s hD e he k α d hd y hy z hz]
  congr 1
  refine chowGroup_eq_of_heq C sPG ?_
  refine (heq_apply_of_degree C sPG sPG (fun m ↦ m + 1) (fun m ↦ m)
    (fun m ↦ firstChernClassCapChow C m sPG ((Scheme.Modules.pullback πG).obj M))
    (show d = k - 1 + ((q + 1 + 1 - 1 : ℕ) : ℤ) by omega)
    (chowGroupCast_heq C sPG (show d + 1 = k - 1 + ((q + 1 + 1 - 1 : ℕ) : ℤ) + 1 by omega)
      y).symm).trans ?_
  refine HEq.trans ?_ hw.symm
  refine (flatPullbackChow_firstChernClassCapChow_heq C sPG sX πG hsPG _ hπG hfacG M
    ((Scheme.Modules.pullback πG).obj M) (Iso.refl _) (k - 1)
    (chowGroupCast C sX (by omega) α) _ ?_).symm
  exact (chowGroupCast_heq C sPG _ y).trans (hy.trans (flatPullbackChow_heq C sPG sX πG hsPG _
    hπG hfacG (by omega) (chowGroupCast_heq C sX _ α).symm))

end Divisor

namespace GenuineChern

/-- **The geometry of `P(𝒬) ⊂ P(𝒢)`** for a short exact sequence `0 ⟶ ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` of finite
locally free modules with `ℳ` invertible and `𝒬` of positive constant rank: the closed immersion
`Stacks.Chow.GenuineChern.bundleEmbedding` of the surjection `𝒢 ⟶ 𝒬` pulls `𝒪_{P(𝒢)}(1)` back
to `𝒪_{P(𝒬)}(1)`, and its image is the zero scheme of a section `s` of an invertible module `ℒ` on
`P(𝒢)` — a relative effective Cartier divisor over `X`, isomorphic to `P(𝒬)` over `P(𝒢)` — with
`π^*ℳ ⊗ ℒ ≅ 𝒪_{P(𝒢)}(1)`. -/
def SubbundleHolds : Prop :=
  ∀ ⦃X : Scheme.{u}⦄ (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property S.X₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₂]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ (r + 1)],
    haveI : Epi S.g := hS.epi_g
    Nonempty ((Scheme.Modules.pullback (bundleEmbedding S.g)).obj (bundleTwist S.X₂) ≅
        bundleTwist S.X₃) ∧
      ∃ (L : (bundle S.X₂).Modules)
        (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle S.X₂).sheaf.obj
          (bundle S.X₂).ringCatSheaf.property L) (s : L.sections),
        letI := hL
        Stacks.Divisors.IsRelativeEffectiveCartierDivisor (bundleProj S.X₂)
            (Stacks.Divisors.zeroScheme (bundle S.X₂) L (s.eval (.op ⊤))) ∧
          ∃ e : (Stacks.Divisors.zeroScheme (bundle S.X₂) L (s.eval (.op ⊤))).subscheme ≅
              bundle S.X₃,
            e.hom ≫ bundleEmbedding S.g =
                (Stacks.Divisors.zeroScheme (bundle S.X₂) L (s.eval (.op ⊤))).subschemeι ∧
              Nonempty (Scheme.Modules.tensorObj
                ((Scheme.Modules.pullback (bundleProj S.X₂)).obj S.X₁) L ≅ bundleTwist S.X₂)

variable (C : ChowSituation.{u})

/-- **Stacks 02UH for the first Chern class**: `c₁(𝒢) ∩ α = c₁(𝒬) ∩ α + c₁(ℳ) ∩ α` for
`0 ⟶ ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` short exact with `ℳ` invertible and `𝒬` of positive rank, from the top
half of Stacks 02TW and the geometry of `P(𝒬) ⊂ P(𝒢)`. -/
theorem subAdditive_of (H : TopHalf C) (hSub : SubbundleHolds.{u}) : SubAdditive C := by
  intro X sX _ S hS r _ _ _ k α
  have := isInvertible_of_rank_one S.X₁
  have := isFiniteLocallyFree_of_rank S.X₂ (r + 1 + 1)
  have := isFiniteLocallyFree_of_rank S.X₃ (r + 1)
  have : Epi S.g := hS.epi_g
  obtain ⟨⟨eTw⟩, L, hL, s, hD, e, he, ⟨eT⟩⟩ := hSub S hS r
  let := hL
  have := flat_bundleProj S.X₂ (r + 1)
  have := locallyOfFiniteType_bundleProj S.X₂ (r + 1)
  have := flat_bundleProj S.X₃ r
  have := locallyOfFiniteType_bundleProj S.X₃ r
  have hι : bundleEmbedding S.g ≫ (bundleProj S.X₂ ≫ sX) = bundleProj S.X₃ ≫ sX := by
    rw [bundleEmbedding_comp_bundleProj_assoc]
  have key := projectiveBundleProjection_succ_eq_of_divisor C sX (bundleProj S.X₂ ≫ sX)
    (bundleProj S.X₂) rfl (bundleProj S.X₃ ≫ sX) (bundleProj S.X₃) rfl (r + 1)
    (relativeDimension_bundleProj S.X₂ (r + 1)) (relativeDimension_bundleProj S.X₃ r)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
    (bundleTwistCap S.X₂ C sX) (bundleTwistCap S.X₃ C sX) (bundleEmbedding S.g) hι
    (fun d ↦ firstChernClassCapChow C d sX S.X₁) (by omega) (bundleEmbedding_comp_bundleProj S.g)
    (fun d y ↦ properChowPushforward_firstChernClassCapChow_of_isClosedImmersion C _ _
      (bundleEmbedding S.g) hι (bundleTwist S.X₂) (bundleTwist S.X₃) eTw.symm d y)
    (fun k α d hd y hy z hz w hw ↦ cap_flatPullback_eq_of_divisor C sX (bundleProj S.X₂ ≫ sX)
      (bundleProj S.X₂) rfl (bundleProj S.X₃ ≫ sX) (bundleProj S.X₃) rfl r
      (relativeDimension_bundleProj S.X₂ (r + 1)) (relativeDimension_bundleProj S.X₃ r)
      (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
      (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
      (bundleEmbedding S.g) hι (bundleEmbedding_comp_bundleProj S.g) L s hD e he
      (bundleTwist S.X₂) S.X₁ eT k α d hd y hy z hz w hw)
    (fun k β ↦ H sX S.X₂ (r + 1) k β) k α
  rw [firstChern_one sX H S.X₁ k α, firstChern_succ, firstChern_succ]
  simp only [segre, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [key, map_add, chowGroupCast_chowGroupCast, chowGroupCast_chowGroupCast,
    chowGroupCast_rfl]

end GenuineChern

end Stacks.Chow

end
