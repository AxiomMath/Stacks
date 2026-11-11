module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassBivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernBivariantClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaCapPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernClassOfRankOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.TopSegreFlatBaseChange

/-!
# The first Chern class of an invertible module is the bivariant class of Stacks 0ERM

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module. Stacks 0ES0
asserts that the first Chern class `c₁(ℒ) ∈ A^1(X)` of Definition 0ERZ, defined through the
projective bundle `(π : P = 𝐏(ℒ) ⟶ X, 𝒪_P(1))` by the relation of Stacks 0ERY, is the bivariant
class `f ↦ c₁(f^*ℒ) ∩ -` of Stacks 0ERM.

A class in `A^1(X)` is determined by its cap operations on the Chow groups of the good test
spaces `g : Y ⟶ X` (`AlgebraicGeometry.Space.BivariantClassCanonical.ext`). The class
`c₁(ℒ) = AlgebraicGeometry.Space.chernClass` of Stacks 0ERZ (rank `1`, index `1`) acts on
`CH_*(Y)` by the map `c₁(ℒ) ∩ -` characterized by Stacks 0ERY
(`AlgebraicGeometry.Space.chernCap`), read on `X ×_X Y ≅ Y`; the class of Stacks 0ERM
(`AlgebraicGeometry.Space.firstChernBivariantClass`) acts by `c₁(g^*ℒ) ∩ -`, read on `X ×_X Y`.

The proof is that of the source: for an invertible module the projective bundle has relative
dimension `0` over `X` and `𝒪_P(1) = π^*ℒ` (`AlgebraicGeometry.Space.rankOneTestTwistIso`), so by
Stacks 0EQR the family `(id, c₁(g^*ℒ) ∩ -)` satisfies the relation
`(-1)^0 c₁(𝒪_{P'}(1))^0 ∩ π'^*(c₁ ∩ α) + (-1)^1 c₁(𝒪_{P'}(1))^1 ∩ π'^*(c₀ ∩ α) = 0` of
Stacks 0ERY on every test space, hence is the family of Stacks 0ERY by its uniqueness
(`AlgebraicGeometry.Space.chernCap_rank_one_eq_rankOneChernCapFamily`). The two cap operations
then agree on `X ×_X Y` by Stacks 0EQR along `X ×_X Y ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.chernCap_rank_one_eq_rankOneChernCapFamily`: the maps of Stacks 0ERY
  for an invertible module are `id` and `c₁(g^*ℒ) ∩ -`.
* `AlgebraicGeometry.Space.chernClass_one_eq_firstChernBivariantClass`: **Stacks 0ES0**, the
  equality in `A^1(X)` of the classes of Definition 0ERZ and Lemma 0ERM.

## References

* [Stacks Project, Tag 0ES0](https://stacks.math.columbia.edu/tag/0ES0)
* [Stacks Project, Tag 0ERM](https://stacks.math.columbia.edu/tag/0ERM)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

section RankOne

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The candidate maps for Stacks 0ERY in rank one**: on a good test space `g : Y ⟶ X`, the
maps `c_j = c₁(g^*ℒ)^j ∩ - : CH_k(Y) ⟶ CH_{k-j}(Y)`, `j = 0, 1`, so `c₀ = id` and `c₁` is the cap
product with the first Chern class of `g^*ℒ` (Stacks 0EQJ). -/
def rankOneChernCapFamily {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    ∀ (j : Fin (1 + 1)) (k : ℤ), chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ)) :=
  fun j k => bundleFormulaCap D (g ≫ sX) hY (pullbackLine D (g ≫ sX) hY sX hX g L)
    (isInvertibleModule_pullbackLine D (g ≫ sX) hY sX hX g L hL) (j : ℕ) k (k - ((j : ℕ) : ℤ))
    (by omega)

/-- The candidate maps on the class of a cycle. -/
theorem rankOneChernCapFamily_chowClassCanonical {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (j : Fin (1 + 1)) (k : ℤ) (a : CycleGroup D (g ≫ sX) k) :
    rankOneChernCapFamily D sX hX L hL g hY j k (chowClassCanonical.{u + 1} D (g ≫ sX) hY k a) =
      chowClassCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ))
        (firstChernCapPowCycleMap D (g ≫ sX) hY (pullbackLine D (g ≫ sX) hY sX hX g L)
          (isInvertibleModule_pullbackLine D (g ≫ sX) hY sX hX g L hL) (j : ℕ)
          (k - ((j : ℕ) : ℤ)) (cycleGroupCast D (g ≫ sX) (by omega) a)) :=
  rfl

/-- In rank one the pullback `π'^*` of the relation of Stacks 0ERY is the flat pullback of
relative dimension `0` along `π' : P' ⟶ Y`, on the class of a cycle. -/
theorem chernTestPull_one_chowClassCanonical
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) L 1)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hfl : IsFlat D.site D.base D.base_mem (pullback.snd (chernProj D sX hX L 1 hE) g))
    (hrl : HasRelativeDimension 0 D.site D.base D.base_mem
      (pullback.snd (chernProj D sX hX L 1 hE) g))
    (m N : ℤ) (h : m + (((1 : ℕ) : ℤ) - 1) = N) (x : CycleGroup D (g ≫ sX) m) :
    chernTestPull D sX hX L 1 hE g hY m N h (chowClassCanonical.{u + 1} D (g ≫ sX) hY m x) =
      chowClassCanonical.{u + 1} D _ (isGood_chernTestBundle D sX hX L 1 hE g hY) N
        (flatPullbackMap D _ (isGood_chernTestBundle D sX hX L 1 hE g hY) (g ≫ sX) hY
          (pullback.snd (chernProj D sX hX L 1 hE) g) rfl 0 hfl hrl m N (by omega) x) :=
  rfl

include hL in
/-- **`𝒪_{P'}(1) ≅ π'^*g^*ℒ`** on the base change `P' = 𝐏(ℒ) ×_X Y` of the projective bundle of
an invertible module: the tautological surjection `π^*ℒ ⟶ 𝒪_P(1)` is an isomorphism
(`AlgebraicGeometry.Space.PrivateChern.isIso_projectiveBundleTautological`), and
`g'^*π^*ℒ ≅ (π ∘ g')^*ℒ = (g ∘ π')^*ℒ ≅ π'^*g^*ℒ`. -/
def rankOneTestTwistIso [L.IsQuasicoherentOnSite]
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite L)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk
        (pullback.snd (projectiveBundleProj (X := goodSpace hX) L hfree).hom g) :
        projectiveBundleBaseChangeSpace D sX hX L hfree g hY ⟶ ⟨Y, hY.1⟩)).obj
        (pullbackLine D (g ≫ sX) hY sX hX g L) ≅
      projectiveBundleBaseChangeTwist D sX hX L hfree g hY := by
  haveI := isIso_projectiveBundleTautological (Z := goodSpace hX) L hfree hL
  have hcomm : (ObjectProperty.homMk
        (pullback.snd (projectiveBundleProj (X := goodSpace hX) L hfree).hom g) :
        projectiveBundleBaseChangeSpace D sX hX L hfree g hY ⟶ ⟨Y, hY.1⟩) ≫
          goodSpaceHom D sX hX g hY =
      projectiveBundleBaseChangeMap D sX hX L hfree g hY ≫
        projectiveBundleProj (X := goodSpace hX) L hfree :=
    ObjectProperty.hom_ext _ pullback.condition.symm
  exact (modulePullbackCompIso D.site D.base D.base_mem _ (goodSpaceHom D sX hX g hY)).app L ≪≫
    eqToIso (by rw [hcomm]) ≪≫
    ((modulePullbackCompIso D.site D.base D.base_mem
      (projectiveBundleBaseChangeMap D sX hX L hfree g hY)
      (projectiveBundleProj (X := goodSpace hX) L hfree)).app L).symm ≪≫
    (modulePullback D.site D.base D.base_mem
      (projectiveBundleBaseChangeMap D sX hX L hfree g hY)).mapIso
      (asIso (projectiveBundleTautological (X := goodSpace hX) L hfree).hom)

/-- The `0`-fold cap product does not change the underlying coefficients. -/
theorem coe_firstChernCapPowCycleMap_of_eq_zero {Z : D.Ambient} {sZ : Z ⟶ D.space}
    (hZ : D.IsGood sZ) (M : Modules.{u, u} D.site D.base D.base_mem Z hZ.1)
    (hM : IsInvertibleModule (⟨Z, hZ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M) {s : ℕ}
    (hs : s = 0) (m : ℤ) (x : CycleGroup D sZ (m + s)) :
    (firstChernCapPowCycleMap D sZ hZ M hM s m x).1 = x.1 := by
  subst hs
  rfl

/-- **The maps `c_j(ℒ) ∩ -` of Stacks 0ERY for an invertible module** `ℒ`: on every good test
space `g : Y ⟶ X`, `c₀(ℒ) ∩ - = id` and `c₁(ℒ) ∩ - = c₁(g^*ℒ) ∩ -`, the cap product of
Stacks 0EQJ. This is the proof of Stacks 0ES0: `P = 𝐏(ℒ)` has relative dimension `0` over `X` and
`𝒪_P(1) = π^*ℒ`, so the family `(id, c₁(g^*ℒ) ∩ -)` satisfies the relation
`c₁^{new}(ℒ) ∩ α - c₁(𝒪_{P'}(1)) ∩ π'^*α = 0` (Stacks 0EQR), and the maps of Stacks 0ERY are unique
(`AlgebraicGeometry.Space.chernCap_unique`). -/
theorem chernCap_rank_one_eq_rankOneChernCapFamily
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) L 1)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    Space.chernCap D sX hX L 1 hE g hY = rankOneChernCapFamily D sX hX L hL g hY := by
  refine (Space.chernCap_unique D sX hX L 1 hE g hY _ ?_ ?_).symm
  · intro k α
    obtain ⟨a, rfl⟩ : ∃ a, chowClassCanonical.{u + 1} D (g ≫ sX) hY k a = α :=
      QuotientAddGroup.mk'_surjective _ α
    rw [rankOneChernCapFamily_chowClassCanonical, degreeCast_chowClassCanonical]
    rfl
  · intro k α
    obtain ⟨a, rfl⟩ : ∃ a, chowClassCanonical.{u + 1} D (g ≫ sX) hY k a = α :=
      QuotientAddGroup.mk'_surjective _ α
    have hP' := isGood_chernTestBundle D sX hX L 1 hE g hY
    have hfl : IsFlat D.site D.base D.base_mem (pullback.snd (chernProj D sX hX L 1 hE) g) :=
      @isFlat_projectiveBundleBaseChangeProj D X _ sX hX L
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite
        g hY 0 hE
    have hrl : HasRelativeDimension 0 D.site D.base D.base_mem
        (pullback.snd (chernProj D sX hX L 1 hE) g) :=
      @hasRelativeDimension_projectiveBundleBaseChangeProj D X _ sX hX L
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite
        g hY 0 hE
    have hM := isInvertibleModule_pullbackLine D (g ≫ sX) hY sX hX g L hL
    -- Stacks 0EQR along `π'`, followed by `π'^*g^*ℒ ≅ 𝒪_{P'}(1)`
    have key : ∀ (s : ℕ) (m m' : ℤ) (h : m + ((0 : ℕ) : ℤ) = m')
        (x : CycleGroup D (g ≫ sX) (m + s)),
        chowClassCanonical.{u + 1} D _ hP' m'
            (flatPullbackMap D _ hP' (g ≫ sX) hY (pullback.snd (chernProj D sX hX L 1 hE) g) rfl
              0 hfl hrl m m' h
              (firstChernCapPowCycleMap D (g ≫ sX) hY (pullbackLine D (g ≫ sX) hY sX hX g L) hM
                s m x)) =
          chowClassCanonical.{u + 1} D _ hP' m'
            (firstChernCapPowCycleMap D _ hP' (chernTestTwist D sX hX L 1 hE g hY)
              (isInvertibleModule_chernTestTwist D sX hX L 1 hE g hY) s m'
              (flatPullbackMap D _ hP' (g ≫ sX) hY (pullback.snd (chernProj D sX hX L 1 hE) g)
                rfl 0 hfl hrl (m + s) (m' + s) (by omega) x)) := by
      intro s m m' h x
      rw [chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap_modulePullback D _ hP'
          (g ≫ sX) hY (pullback.snd (chernProj D sX hX L 1 hE) g) rfl 0 hfl hrl
          (pullbackLine D (g ≫ sX) hY sX hX g L) hM s m m' h (by omega) x]
      let := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
      exact chowClassCanonical_firstChernCapPowCycleMap_congr_iso D _ hP' _ _ _
        (isInvertibleModule_chernTestTwist D sX hX L 1 hE g hY)
        (rankOneTestTwistIso D sX hX L hL hE.isFiniteLocallyFreeOnSite g hY) s m' _
    change ProjectiveBundleRelation.relationSumAt _ _ _ 1 k _ = 0
    rw [ProjectiveBundleRelation.relationSumAt, Fin.sum_univ_two, add_eq_zero_iff_eq_neg,
      ProjectiveBundleRelation.relationTerm, ProjectiveBundleRelation.relationTerm,
      rankOneChernCapFamily_chowClassCanonical, rankOneChernCapFamily_chowClassCanonical,
      chernTestPull_one_chowClassCanonical D sX hX L hE g hY hfl hrl,
      chernTestPull_one_chowClassCanonical D sX hX L hE g hY hfl hrl, key,
      bundleFormulaCap_chowClassCanonical, bundleFormulaCap_chowClassCanonical]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, neg_neg]
    refine congrArg (chowClassCanonical.{u + 1} D _ hP' _) (Subtype.ext ?_)
    refine (coe_firstChernCapPowCycleMap_of_eq_zero D hP' _ _ (by rfl) _ _).trans ?_
    refine (cycleGroupCast_coe D _ _ _).trans ?_
    refine coe_firstChernCapPowCycleMap_congr D _ hP' _ _ (by decide)
      (by simp) _ _ ?_
    refine Eq.trans ?_ (cycleGroupCast_coe D _ _ _).symm
    exact coe_flatPullbackMap_congr D (g ≫ sX) hY _ hP' _ rfl 0 hfl hrl
      (by simp)
      (by simp) _ _ _ _
      rfl

/-- The cap operation of `c₁(ℒ) ∈ A^1(X)` (Stacks 0ERZ) on a good test space `g : Y ⟶ X`, for `ℒ`
invertible: `c₁(g^*ℒ) ∩ -` on `Y`, read on `X ×_X Y ≅ Y`. -/
theorem chernClass_rank_one_cap
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) L 1)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ) (a : CycleGroup D (g ≫ sX) k) :
    (Space.chernClass D sX hX L 1 hE (Fin.last 1)).cap g hY hXg k
        (chowClassCanonical.{u + 1} D (g ≫ sX) hY k a) =
      testSpacePullbackChowMap D sX hX g hY hXg _
        (chowClassCanonical.{u + 1} D (g ≫ sX) hY (k - ((Fin.last 1) : ℕ))
          (firstChernCapPowCycleMap D (g ≫ sX) hY (pullbackLine D (g ≫ sX) hY sX hX g L)
            (isInvertibleModule_pullbackLine D (g ≫ sX) hY sX hX g L hL)
            ((Fin.last 1) : ℕ) (k - ((Fin.last 1) : ℕ))
            (cycleGroupCast D (g ≫ sX) (by omega) a))) := by
  rw [Space.chernClass_cap, chernCap_rank_one_eq_rankOneChernCapFamily D sX hX L hL hE g hY,
    rankOneChernCapFamily_chowClassCanonical]

/-- The second projection `X ×_X Y ⟶ Y` followed by `g` is the first projection. -/
theorem homMk_pullbackSnd_comp_goodSpaceHom {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) :
    (ObjectProperty.homMk (pullback.snd (𝟙 X) g) :
        (⟨pullback (𝟙 X) g, hXg.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩) ≫
      goodSpaceHom D sX hX g hY = firstChernBivariantFst D sX hX g hXg :=
  ObjectProperty.hom_ext _ (pullback.condition.symm.trans (Category.comp_id _))

/-- `q^*g^*ℒ ≅ ℒ|_{X ×_X Y}` for the second projection `q : X ×_X Y ⟶ Y`. -/
def testSpaceLineIso {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) :
    (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk (pullback.snd (𝟙 X) g) :
        (⟨pullback (𝟙 X) g, hXg.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨Y, hY.1⟩)).obj (pullbackLine D (g ≫ sX) hY sX hX g L) ≅
      (modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hXg)).obj L :=
  (modulePullbackCompIso D.site D.base D.base_mem _ (goodSpaceHom D sX hX g hY)).app L ≪≫
    eqToIso (by rw [homMk_pullbackSnd_comp_goodSpaceHom D sX hX g hY hXg])

/-- The cap operation of `c₁(ℒ) ∈ A^1(X)` (Stacks 0ERZ) on a good test space `g : Y ⟶ X`, read on
`X' = X ×_X Y`: by Stacks 0EQR along `q : X' ⟶ Y`, it is `c₁(q^*g^*ℒ) ∩ q^*α`, and
`q^*g^*ℒ ≅ ℒ|_{X'}`. -/
theorem chernClass_rank_one_cap_eq_firstChernCap
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ) (a : CycleGroup D (g ≫ sX) k) :
    (Space.chernClass D sX hX L 1
        ((isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one (Z := goodSpace hX) L).1 hL)
        (Fin.last 1)).cap g hY hXg k (chowClassCanonical.{u + 1} D (g ≫ sX) hY k a) =
      chowClassCanonical.{u + 1} D _ hXg (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ))
        (firstChernCapPowCycleMap D _ hXg
          ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hXg)).obj L)
          (modulePullbackInvertible (firstChernBivariantFst D sX hX g hXg) L hL)
          ((Fin.last 1 : Fin (1 + 1)) : ℕ) (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ))
          (flatPullbackMap D _ hXg (g ≫ sX) hY (pullback.snd (𝟙 X) g)
            (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0
            (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY hXg).1
            (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY hXg).2
            (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ) + ((Fin.last 1 : Fin (1 + 1)) : ℕ))
            (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ) + ((Fin.last 1 : Fin (1 + 1)) : ℕ)) (by simp)
            (cycleGroupCast D (g ≫ sX) (by omega) a))) := by
  have hsnd := isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY hXg
  have hM := isInvertibleModule_pullbackLine D (g ≫ sX) hY sX hX g L hL
  rw [chernClass_rank_one_cap D sX hX L hL _ g hY hXg k a, testSpacePullbackChowMap,
    flatPullbackChowMapCanonical_chowClassCanonical,
    chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap_modulePullback D _ hXg (g ≫ sX) hY
      (pullback.snd (𝟙 X) g) (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0
      hsnd.1 hsnd.2 (pullbackLine D (g ≫ sX) hY sX hX g L) hM ((Fin.last 1 : Fin (1 + 1)) : ℕ)
      (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ)) (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ))
      (Int.add_zero _) (Int.add_zero _)]
  exact chowClassCanonical_firstChernCapPowCycleMap_congr_iso D _ hXg _ _ _
    (modulePullbackInvertible (firstChernBivariantFst D sX hX g hXg) L hL)
    (testSpaceLineIso D sX hX L g hY hXg) _ _ _

/-- The cap operation of the class of Stacks 0ERM on the class of a cycle. -/
theorem firstChernBivariantClass_cap_chowClassCanonical
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ) (a : CycleGroup D (g ≫ sX) k) :
    (firstChernBivariantClass D sX hX L hL).cap g hY hXg k
        (chowClassCanonical.{u + 1} D (g ≫ sX) hY k a) =
      chowClassCanonical.{u + 1} D _ hXg (k - 1)
        (firstChernCapCycleMap D _ hXg (k - 1) (canonicalFirstChernRule D _ hXg
          ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hXg)).obj L)
          (modulePullbackInvertible (firstChernBivariantFst D sX hX g hXg) L hL) (k - 1))
          (cycleGroupDegreeCongr D _ (Int.sub_add_cancel k 1).symm
            (properCyclePushforward D (g ≫ sX) hY (pullback.fst (𝟙 X) g ≫ sX) hXg
              (firstChernBivariantTestIso_hom_comp D sX g)
              (isProper_of_isIso D.site D.base D.base_mem
                (firstChernBivariantTestIso D g).hom).2.1.2 k a))) := by
  have hdeg : ∀ {l : ℤ} (h : k = l) (x : CycleGroup D (pullback.fst (𝟙 X) g ≫ sX) k),
      chowGroupCanonicalDegreeCongr D _ hXg h (chowClassCanonical.{u + 1} D _ hXg k x) =
        chowClassCanonical.{u + 1} D _ hXg l (cycleGroupDegreeCongr D _ h x) := by
    rintro l rfl x
    rfl
  change firstChernBivariantCap D sX hX L hL g hY hXg k _ = _
  rw [firstChernBivariantCap, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    chowGroupCanonicalProperPushforward_chowClassCanonical, AddEquiv.coe_toAddMonoidHom, hdeg]
  rfl

/-- **Stacks 0ES0.** In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible
`𝒪_X`-module. Then the first Chern class `c₁(ℒ) ∈ A^1(X)` of Definition 0ERZ
(`AlgebraicGeometry.Space.chernClass` at rank `1` and index `1`, the bivariant class whose cap
operations are the maps characterized by the projective bundle relation of Stacks 0ERY) is equal
to the bivariant class `c₁(f^*ℒ) ∩ -` of Lemma 0ERM
(`AlgebraicGeometry.Space.firstChernBivariantClass`), as elements of
`A^1(X) = A^1(X → X)` (`AlgebraicGeometry.Space.chowCohomologyComponentCanonical`). -/
@[stacks 0ES0 "c_1(L) ∈ A^1(X) of Definition 0ERZ (chernClass, characterized by the projective \
bundle relation of Lemma 0ERY) equals the bivariant class c_1(f^*L) ∩ - of Lemma 0ERM, as \
elements of A^1(X), for X/B good and L invertible"]
theorem chernClass_one_eq_firstChernBivariantClass :
    Space.chernClass D sX hX L 1
        ((isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one (Z := goodSpace hX) L).1 hL)
        (Fin.last 1) =
      firstChernBivariantClass D sX hX L hL := by
  apply BivariantClassCanonical.ext
  intro Y g hY hXg k α
  obtain ⟨a, rfl⟩ : ∃ a, chowClassCanonical.{u + 1} D (g ≫ sX) hY k a = α :=
    QuotientAddGroup.mk'_surjective _ α
  rw [chernClass_rank_one_cap_eq_firstChernCap D sX hX L hL g hY hXg k a,
    firstChernBivariantClass_cap_chowClassCanonical D sX hX L hL g hY hXg k a]
  refine congrArg (chowClassCanonical.{u + 1} D _ hXg _) (Subtype.ext ?_)
  have hsnd := isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY hXg
  have hiso := isProper_of_isIso D.site D.base D.base_mem (firstChernBivariantTestIso D g).hom
  have hid := isFlat_and_hasRelativeDimension_zero_of_isIso D (g ≫ sX) hY (𝟙 Y)
  have hcoe : ∀ {l : ℤ} (h : k = l) (x : CycleGroup D (pullback.fst (𝟙 X) g ≫ sX) k),
      (cycleGroupDegreeCongr D _ h x).1 = x.1 := by
    rintro l rfl x
    rfl
  -- `q^*a = (q⁻¹)_*a`: pushing forward along the isomorphism `Y ≅ X ×_X Y` undoes `q^*`
  have hpush := properCyclePushforward_flatPullbackMap_of_isIso D (g ≫ sX) hY
    (pullback.fst (𝟙 X) g ≫ sX) hXg (g ≫ sX) hY (e := (firstChernBivariantTestIso D g).hom)
    (a := 𝟙 Y) (b := pullback.snd (𝟙 X) g) (by simp [firstChernBivariantTestIso])
    (Category.id_comp _) (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g)
    (firstChernBivariantTestIso_hom_comp D sX g) hiso.2.1.2 0 hid.1 hid.2 hsnd.1 hsnd.2 k k
    (by simp) a
  have hc := congrArg Subtype.val hpush
  have hx : (flatPullbackMap D _ hXg (g ≫ sX) hY (pullback.snd (𝟙 X) g)
      (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0 hsnd.1 hsnd.2
      (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ) + ((Fin.last 1 : Fin (1 + 1)) : ℕ))
      (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ) + ((Fin.last 1 : Fin (1 + 1)) : ℕ)) (by simp)
      (cycleGroupCast D (g ≫ sX) (by omega) a)).1 =
      (cycleGroupDegreeCongr D _ (Int.sub_add_cancel k 1).symm
        (properCyclePushforward D (g ≫ sX) hY (pullback.fst (𝟙 X) g ≫ sX) hXg
          (firstChernBivariantTestIso_hom_comp D sX g) hiso.2.1.2 k a)).1 := by
    have h1 : (flatPullbackMap D _ hXg (g ≫ sX) hY (pullback.snd (𝟙 X) g)
        (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0 hsnd.1 hsnd.2
        (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ) + ((Fin.last 1 : Fin (1 + 1)) : ℕ))
        (k - ((Fin.last 1 : Fin (1 + 1)) : ℕ) + ((Fin.last 1 : Fin (1 + 1)) : ℕ)) (by simp)
        (cycleGroupCast D (g ≫ sX) (by omega) a)).1 =
        (flatPullbackMap D _ hXg (g ≫ sX) hY (pullback.snd (𝟙 X) g)
          (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0 hsnd.1 hsnd.2
          k k (by simp) a).1 :=
      coe_flatPullbackMap_congr D (g ≫ sX) hY _ hXg _ _ 0 hsnd.1 hsnd.2
        (by simp) (by simp) _ _ _ _ rfl
    refine h1.trans (hc.symm.trans ?_)
    exact (coe_properCyclePushforward_congr D (pullback.fst (𝟙 X) g ≫ sX) hXg (g ≫ sX) hY _
        (firstChernBivariantTestIso_hom_comp D sX g) hiso.2.1.2 rfl _ _
        (flatPullbackMap_id_coe D (g ≫ sX) hY (Category.id_comp _) hid.1 hid.2 k k (by simp)
          a)).trans (hcoe _ _).symm
  exact coe_firstChernCapPowCycleMap_congr D _ hXg
    ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hXg)).obj L)
    (modulePullbackInvertible (firstChernBivariantFst D sX hX g hXg) L hL)
    (s' := 1) (m' := k - 1) rfl (by simp) _
    (cycleGroupCast D _ (by omega) (cycleGroupDegreeCongr D _ (Int.sub_add_cancel k 1).symm
      (properCyclePushforward D (g ≫ sX) hY (pullback.fst (𝟙 X) g ≫ sX) hXg
        (firstChernBivariantTestIso_hom_comp D sX g) hiso.2.1.2 k a))) hx

end RankOne

end AlgebraicGeometry.Space

end
