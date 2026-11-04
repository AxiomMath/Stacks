module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackSquareCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange

/-!
# Flat pullback as a bivariant class

In Situation 0EDT let `f : X ⟶ Y` be a morphism of good algebraic spaces over `B` which is flat
of relative dimension `r`.  **Stacks 0ERN** says that the rule assigning to a test space
`g : Y' ⟶ Y` the flat pullback `(f')^* : CH_k(Y') ⟶ CH_{k+r}(X')` along the base change
`f' : X' = Y' ×_Y X ⟶ Y'` is a bivariant class of degree `-r`. This file proves it over the
constructed Chow groups `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6, with the
bivariant classes `AlgebraicGeometry.Space.BivariantClassCanonical` of Stacks 0ERJ.

## Main definitions

* `AlgebraicGeometry.Space.flatPullbackBivariantClassCanonical`: **Stacks 0ERN**, the flat
  pullback along the base changes of `f` as a bivariant class of degree `-r`.

## Main results

* `AlgebraicGeometry.Space.bivariantPullbackSnd_comp_base`: the base change
  `f' : Y' ×_Y X ⟶ Y'` of `f` along a test space is a morphism over the base.
* `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_bivariantPullbackSnd`: the base change
  `f'` is flat of relative dimension `r`, the second assertion of Stacks 0EPD.

## References

* [Stacks Project, Tag 0ERN](https://stacks.math.columbia.edu/tag/0ERN)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})

/-- The flat pullback of cycles depends only on the morphism and its relative dimension: two flat
pullbacks along equal morphisms, of equal relative dimensions, are equal. -/
private theorem flatPullbackMap_congr {X Y : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f₁ f₂ : X ⟶ Y} (hf : f₁ = f₂) {r₁ r₂ : ℕ}
    (hr : r₁ = r₂) (hb₁ : f₁ ≫ sY = sX) (hb₂ : f₂ ≫ sY = sX)
    (hfl₁ : IsFlat D.site D.base D.base_mem f₁) (hfl₂ : IsFlat D.site D.base D.base_mem f₂)
    (hr₁ : HasRelativeDimension r₁ D.site D.base D.base_mem f₁)
    (hr₂ : HasRelativeDimension r₂ D.site D.base D.base_mem f₂) (m n : ℤ)
    (h₁ : m + (r₁ : ℤ) = n) (h₂ : m + (r₂ : ℤ) = n) :
    flatPullbackMap D sX hX sY hY f₁ hb₁ r₁ hfl₁ hr₁ m n h₁ =
      flatPullbackMap D sX hX sY hY f₂ hb₂ r₂ hfl₂ hr₂ m n h₂ := by
  subst hf hr
  rfl

/-- **Flat pullbacks around a commuting square.**  For flat morphisms `a : P ⟶ Q`, `b : Q ⟶ S`,
`c : P ⟶ R` and `d : R ⟶ S` over the base with `a ≫ b = c ≫ d` and with relative dimensions
satisfying `r_a + r_b = r_c + r_d`, the composites `a^* ∘ b^*` and `c^* ∘ d^*` of flat pullbacks
of cycles agree. -/
private theorem flatPullbackMap_comp_eq_of_comm {P Q R S : D.Ambient}
    (sP : P ⟶ D.space) (hP : D.IsGood sP) (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ)
    (sR : R ⟶ D.space) (hR : D.IsGood sR) (sS : S ⟶ D.space) (hS : D.IsGood sS)
    {a : P ⟶ Q} {b : Q ⟶ S} {c : P ⟶ R} {d : R ⟶ S} (w : a ≫ b = c ≫ d)
    (ha : a ≫ sQ = sP) (hb : b ≫ sS = sQ) (hc : c ≫ sR = sP) (hd : d ≫ sS = sR)
    {ra rb rc rd : ℕ} (hrr : ra + rb = rc + rd)
    (haf : IsFlat D.site D.base D.base_mem a)
    (har : HasRelativeDimension ra D.site D.base D.base_mem a)
    (hbf : IsFlat D.site D.base D.base_mem b)
    (hbr : HasRelativeDimension rb D.site D.base D.base_mem b)
    (hcf : IsFlat D.site D.base D.base_mem c)
    (hcr : HasRelativeDimension rc D.site D.base D.base_mem c)
    (hdf : IsFlat D.site D.base D.base_mem d)
    (hdr : HasRelativeDimension rd D.site D.base D.base_mem d)
    (k m₁ m₂ n : ℤ) (h₁ : k + (rb : ℤ) = m₁) (h₂ : m₁ + (ra : ℤ) = n)
    (h₃ : k + (rd : ℤ) = m₂) (h₄ : m₂ + (rc : ℤ) = n) :
    (flatPullbackMap D sP hP sQ hQ a ha ra haf har m₁ n h₂).comp
        (flatPullbackMap D sQ hQ sS hS b hb rb hbf hbr k m₁ h₁) =
      (flatPullbackMap D sP hP sR hR c hc rc hcf hcr m₂ n h₄).comp
        (flatPullbackMap D sR hR sS hS d hd rd hdf hdr k m₂ h₃) := by
  subst h₁ h₃
  have hab : k + ((ra + rb : ℕ) : ℤ) = n := by push_cast; omega
  have hcd : k + ((rc + rd : ℕ) : ℤ) = n := by push_cast; omega
  rw [← flatPullbackMap_comp D sP hP sQ hQ sS hS a b ha hb ra rb haf har hbf hbr k n hab,
    ← flatPullbackMap_comp D sP hP sR hR sS hS c d hc hd rc rd hcf hcr hdf hdr k n hcd]
  exact flatPullbackMap_congr D sP hP sS hS w hrr _ _ _ _ _ _ k n hab hcd

/-- The structure morphisms of a base change square commute: for `f : X ⟶ Y` over the base and a
test space `g : Y' ⟶ Y`, the projection `f' : Y' ×_Y X ⟶ Y'` is a morphism over the base. -/
theorem bivariantPullbackSnd_comp_base {X Y Y' : D.Ambient} (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) {f : X ⟶ Y} (hf : f ≫ sY = sX) (g : Y' ⟶ Y) :
    pullback.snd f g ≫ g ≫ sY = pullback.fst f g ≫ sX := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc, hf]

/-- **Stacks 0EPD, second assertion, at a test space.**  For `f : X ⟶ Y` flat of relative
dimension `r` over the base and a good test space `g : Y' ⟶ Y`, the base change
`f' : Y' ×_Y X ⟶ Y'` is flat of relative dimension `r`. -/
theorem isFlat_and_hasRelativeDimension_bivariantPullbackSnd {X Y Y' : D.Ambient}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (g : Y' ⟶ Y)
    (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX)) :
    IsFlat D.site D.base D.base_mem (pullback.snd f g) ∧
      HasRelativeDimension r D.site D.base D.base_mem (pullback.snd f g) :=
  (isFlat_and_hasRelativeDimension_of_isPullback D (pullback.fst f g ≫ sX) hX' (g ≫ sY) hY'
    sX hX sY hY (bivariantPullbackSnd_comp_base D sX sY hf g) hf
    (IsPullback.of_hasPullback f g).flip r
    hflat hr).2

/-- **The flat-pullback axiom of Stacks 0ERJ (2) for the rule of Stacks 0ERN, on cycles.**  Let
`f : X ⟶ Y` be flat of relative dimension `r` over the base, let `g : Y' ⟶ Y` be a test space,
let `h : Y'' ⟶ Y'` be flat of relative dimension `s`, and let `h' : X'' ⟶ X'` be the base change
of `h`, where `X' = Y' ×_Y X` and `X'' = Y'' ×_Y X`.  Writing `f' : X' ⟶ Y'` and
`f'' : X'' ⟶ Y''` for the two base changes of `f`,

  `(f'')^* (h^* α) = (h')^* ((f')^* α)`   in `Z_{k+r+s}(X'')`

for every `k`-cycle `α` on `Y'`. -/
private theorem flatPullbackMap_pullbackSnd_comp_eq {X Y Y' Y'' : D.Ambient}
    (sX : X ⟶ D.space) (sY : Y ⟶ D.space) {f : X ⟶ Y} (r : ℕ)
    (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX))
    (h : Y'' ⟶ Y') (hY'' : D.IsGood ((h ≫ g) ≫ sY))
    (hX'' : D.IsGood (pullback.fst f (h ≫ g) ≫ sX)) (s : ℕ)
    (hh : IsFlat D.site D.base D.base_mem h)
    (hs : HasRelativeDimension s D.site D.base D.base_mem h)
    (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hb' : pullback.snd f g ≫ g ≫ sY = pullback.fst f g ≫ sX)
    (hb'' : pullback.snd f (h ≫ g) ≫ (h ≫ g) ≫ sY = pullback.fst f (h ≫ g) ≫ sX)
    (hbh' : h' ≫ pullback.fst f g ≫ sX = pullback.fst f (h ≫ g) ≫ sX)
    (hf'f : IsFlat D.site D.base D.base_mem (pullback.snd f g))
    (hf'r : HasRelativeDimension r D.site D.base D.base_mem (pullback.snd f g))
    (hf''f : IsFlat D.site D.base D.base_mem (pullback.snd f (h ≫ g)))
    (hf''r : HasRelativeDimension r D.site D.base D.base_mem (pullback.snd f (h ≫ g)))
    (hh' : IsFlat D.site D.base D.base_mem h')
    (hs' : HasRelativeDimension s D.site D.base D.base_mem h')
    (k m₁ m₂ n : ℤ) (h₁ : k + (s : ℤ) = m₁) (h₂ : m₁ + (r : ℤ) = n)
    (h₃ : k + (r : ℤ) = m₂) (h₄ : m₂ + (s : ℤ) = n) (α : CycleGroup D (g ≫ sY) k) :
    flatPullbackMap D (pullback.fst f (h ≫ g) ≫ sX) hX'' ((h ≫ g) ≫ sY) hY''
        (pullback.snd f (h ≫ g)) hb'' r hf''f hf''r m₁ n h₂
        (flatPullbackMap D ((h ≫ g) ≫ sY) hY'' (g ≫ sY) hY' h (Category.assoc h g sY).symm s
          hh hs k m₁ h₁ α) =
      flatPullbackMap D (pullback.fst f (h ≫ g) ≫ sX) hX'' (pullback.fst f g ≫ sX) hX' h' hbh'
        s hh' hs' m₂ n h₄
        (flatPullbackMap D (pullback.fst f g ≫ sX) hX' (g ≫ sY) hY' (pullback.snd f g) hb' r
          hf'f hf'r k m₂ h₃ α) :=
  congrArg (fun φ : CycleGroup D (g ≫ sY) k →+ CycleGroup D (pullback.fst f (h ≫ g) ≫ sX) n =>
      φ α)
    (flatPullbackMap_comp_eq_of_comm D (pullback.fst f (h ≫ g) ≫ sX) hX'' ((h ≫ g) ≫ sY) hY''
      (pullback.fst f g ≫ sX) hX' (g ≫ sY) hY' sq.w hb'' (Category.assoc h g sY).symm hbh' hb'
      (Nat.add_comm r s) hf''f hf''r hh hs hh' hs' hf'f hf'r k m₁ m₂ n h₁ h₂ h₃ h₄)

/-- **The Gysin axiom of Stacks 0ERJ (3) for the rule of Stacks 0ERN, in the Chow group.**  Let
`f : X ⟶ Y` be flat of relative dimension `r`, let `g : Y' ⟶ Y` be a test space with an invertible
`ℒ` and a section `t`, `D' = Z(t) ⊆ Y'`, and let `E' = Z(f'^*t) ⊆ X' = Y' ×_Y X` be the vanishing
locus of the pulled-back section, identified with `Y' ×_Y X ×_{Y'} D' = X ×_Y D'` by `iso`.  Then
for every `α ∈ Z_{k+1}(Y')`

  `iso_* (f'')^* (i^* α) = (i')^* (f')^* α`   in `CH_{k+r}(E')`,

where `f' : X' ⟶ Y'` and `f'' : X ×_Y D' ⟶ D'` are the two base changes of `f`. -/
private theorem chowClassCanonical_properCyclePushforward_flatPullbackMap_gysinCycleMap
    {X Y Y' : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {f : X ⟶ Y} (hf : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (g : Y' ⟶ Y)
    (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX))
    (L : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1) (t : L.sections)
    (hL : IsInvertibleSheaf D (g ≫ sY) hY' L)
    (hXd : D.IsGood (pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX))
    (iso : pullback f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≅
      (vanishingLocus D (pullback.fst f g ≫ sX) hX'
        (pullbackSheaf D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
          (ObjectProperty.homMk (pullback.snd f g)) L)
        (pullbackGlobalSection D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
          (ObjectProperty.homMk (pullback.snd f g)) L t)).1.toFunctor)
    (hiso : iso.hom ≫ (vanishingLocus D (pullback.fst f g ≫ sX) hX'
        (pullbackSheaf D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
          (ObjectProperty.homMk (pullback.snd f g)) L)
        (pullbackGlobalSection D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
          (ObjectProperty.homMk (pullback.snd f g)) L t)).1.ι =
      bivariantBaseChangeMap D f g (vanishingLocus D (g ≫ sY) hY' L t).1.ι)
    (hbase : iso.hom ≫ ((vanishingLocus D (pullback.fst f g ≫ sX) hX'
        (pullbackSheaf D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
          (ObjectProperty.homMk (pullback.snd f g)) L)
        (pullbackGlobalSection D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
          (ObjectProperty.homMk (pullback.snd f g)) L t)).1.ι ≫ pullback.fst f g ≫ sX) =
      pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX)
    (hisoProper : IsProper D.site D.base D.base_mem iso.hom) (k m : ℤ)
    (hm : k + (r : ℤ) = m) (hkm : k + 1 + (r : ℤ) = m + 1)
    (α : CycleGroup D (g ≫ sY) (k + 1)) :
    chowClassCanonical.{u + 1} D _ (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX' _ _) m
        (properCyclePushforward D
          (pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX) hXd
          _ (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX' _ _) hbase
          hisoProper.2.1.2 m
          (flatPullbackMap D (pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX)
            hXd (((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sY)
            (isGood_vanishingLocus D (g ≫ sY) hY' L t)
            (pullback.snd f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g))
            (bivariantPullbackSnd_comp_base D sX sY hf _) r
            (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr _
              (isGood_vanishingLocus D (g ≫ sY) hY' L t) hXd).1
            (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr _
              (isGood_vanishingLocus D (g ≫ sY) hY' L t) hXd).2 k m hm
            (gysinCycleMap D (g ≫ sY) (vanishingLocus D (g ≫ sY) hY' L t)
              (isGood_vanishingLocus D (g ≫ sY) hY' L t) k
              (sectionGysinRule D (g ≫ sY) hY' L t k hL) α))) =
      chowClassCanonical.{u + 1} D _ (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX' _ _) m
        (gysinCycleMap D (pullback.fst f g ≫ sX)
          (vanishingLocus D (pullback.fst f g ≫ sX) hX'
            (pullbackSheaf D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
              (ObjectProperty.homMk (pullback.snd f g)) L)
            (pullbackGlobalSection D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
              (ObjectProperty.homMk (pullback.snd f g)) L t))
          (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX' _ _) m
          (sectionGysinRule D (pullback.fst f g ≫ sX) hX' _ _ m
            (isInvertibleSheaf_pullbackSheaf D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
              (ObjectProperty.homMk (pullback.snd f g)) L hL))
          (flatPullbackMap D (pullback.fst f g ≫ sX) hX' (g ≫ sY) hY' (pullback.snd f g)
            (bivariantPullbackSnd_comp_base D sX sY hf g) r
            (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY'
              hX').1
            (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY'
              hX').2
            (k + 1) (m + 1) hkm α)) := by
  obtain ⟨g₀, hsq⟩ := exists_isPullback_vanishingLocus_pullbackSheaf D (g ≫ sY) hY'
    (pullback.fst f g ≫ sX) hX' (ObjectProperty.homMk (pullback.snd f g)) L t hL
  have hf' := isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g
    hY' hX'
  have hf'' := isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr _
    (isGood_vanishingLocus D (g ≫ sY) hY' L t) hXd
  have hg₀ := isFlat_and_hasRelativeDimension_gysinPullbackProjection D (g ≫ sY) hY'
    (pullback.fst f g ≫ sX) hX' (bivariantPullbackSnd_comp_base D sX sY hf g) r hf'.1 hf'.2 L t hsq
  have hab : iso.hom ≫ g₀ = pullback.snd f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) := by
    rw [← cancel_mono (vanishingLocus D (g ≫ sY) hY' L t).1.ι, Category.assoc, hsq.w,
      ← Category.assoc, hiso]
    simp
  have h6 := chowClassCanonical_gysinCycleMap_flatPullbackMap_of_isPullback D (g ≫ sY) hY'
    (pullback.fst f g ≫ sX) hX' (bivariantPullbackSnd_comp_base D sX sY hf g) r hf'.1 hf'.2 L t hL
    hsq k m hm hkm α
  have h7 := properCyclePushforward_flatPullbackMap_of_isIso D
    (pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX) hXd
    _ (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX' _ _)
    _ (isGood_vanishingLocus D (g ≫ sY) hY' L t) hab
    (bivariantPullbackSnd_comp_base D sX sY hf _)
    (comp_structure_of_isPullback D (g ≫ sY) (pullback.fst f g ≫ sX)
      (bivariantPullbackSnd_comp_base D sX sY hf g) hsq) hbase hisoProper.2.1.2 r hf''.1 hf''.2
    hg₀.1 hg₀.2 k m hm
    (gysinCycleMap D (g ≫ sY) (vanishingLocus D (g ≫ sY) hY' L t)
      (isGood_vanishingLocus D (g ≫ sY) hY' L t) k (sectionGysinRule D (g ≫ sY) hY' L t k hL) α)
  exact (congrArg _ h7).trans h6.symm

section Registration

/-- Transporting a flat pullback along an equality of target degrees gives the flat pullback at
the other spelling of the degree. -/
private theorem cycleGroupDegreeCongr_flatPullbackMap {X Y : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hf : f ≫ sY = sX)
    (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (m n n' : ℤ) (h : n = n')
    (hn : m + (r : ℤ) = n) (hn' : m + (r : ℤ) = n') (α : CycleGroup D sY m) :
    cycleGroupDegreeCongr D sX h (flatPullbackMap D sX hX sY hY f hf r hflat hr m n hn α) =
      flatPullbackMap D sX hX sY hY f hf r hflat hr m n' hn' α := by
  subst h
  rfl

variable {X Y : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
  (hY : D.IsGood sY) {f : X ⟶ Y} (hf : f ≫ sY = sX) (r : ℕ)
  (hflat : IsFlat D.site D.base D.base_mem f)
  (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- In Situation 0EDT let `f : X ⟶ Y` be a morphism of good algebraic spaces over `B` which is
flat of relative dimension `r`. Then the rule that to `g : Y' ⟶ Y` assigns the flat pullback
`(f')^* : CH_k(Y') ⟶ CH_{k+r}(X')` of Stacks 0EQB along the base change
`f' : X' = X ×_Y Y' ⟶ Y'` is a bivariant class of degree `-r`, in the sense of Stacks 0ERJ
(`AlgebraicGeometry.Space.BivariantClassCanonical`, over the constructed Chow groups
`AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6). -/
@[stacks 0ERN "the rule g : Y' → Y ↦ (f')^* : CH_k(Y') → CH_{k+r}(X'), X' = X ×_Y Y', for f
flat of relative dimension r between good spaces over B, is a bivariant class of degree -r"]
def flatPullbackBivariantClassCanonical :
    BivariantClassCanonical.{u + 1} D sX hX sY hY f hf (-(r : ℤ)) where
  cap g hY' hX' k := flatPullbackChowMapCanonical.{u + 1} D (pullback.fst f g ≫ sX) hX' (g ≫ sY)
    hY' (pullback.snd f g) (bivariantPullbackSnd_comp_base D sX sY hf g) r
    (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY' hX').1
    (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY' hX').2
    k (k - -(r : ℤ)) (by omega)
  proper_naturality := by
    intro Y' Y'' g hY' hX' h hY'' hX'' hh h' sq hfst hh' k α
    refine ⟨flatPullbackMap D (pullback.fst f (h ≫ g) ≫ sX) hX'' ((h ≫ g) ≫ sY) hY''
      (pullback.snd f (h ≫ g)) (bivariantPullbackSnd_comp_base D sX sY hf (h ≫ g)) r
      (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr (h ≫ g) hY''
        hX'').1
      (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr (h ≫ g) hY''
        hX'').2 k (k - -(r : ℤ)) (by omega) α, rfl, ?_⟩
    exact congrArg (chowClassCanonical.{u + 1} D (pullback.fst f g ≫ sX) hX' (k - -(r : ℤ)))
      (flatPullback_properPushforward_unconditional D (pullback.fst f (h ≫ g) ≫ sX) hX''
      ((h ≫ g) ≫ sY) hY'' (pullback.fst f g ≫ sX) hX' (g ≫ sY) hY'
      (bivariantPullbackSnd_comp_base D sX sY hf (h ≫ g)) (by rw [← Category.assoc, hfst])
      (Category.assoc h g sY).symm (bivariantPullbackSnd_comp_base D sX sY hf g) r
      (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY' hX').1
      (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY' hX').2
      sq hh k (k - -(r : ℤ)) (by omega) α)
  flat_naturality := by
    intro Y' Y'' g hY' hX' h hY'' hX'' hh s hs h' sq hfst hh' hs' k α
    refine ⟨flatPullbackMap D (pullback.fst f g ≫ sX) hX' (g ≫ sY) hY' (pullback.snd f g)
      (bivariantPullbackSnd_comp_base D sX sY hf g) r
      (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY' hX').1
      (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY' hX').2
      k (k - -(r : ℤ)) (by omega) α, rfl, ?_⟩
    exact congrArg (chowClassCanonical.{u + 1} D (pullback.fst f (h ≫ g) ≫ sX) hX''
      (k + (s : ℤ) - -(r : ℤ)))
      (flatPullbackMap_pullbackSnd_comp_eq D sX sY r g hY' hX' h hY'' hX'' s hh hs h' sq
      _ _ _ _ _ _ _ hh' hs' k (k + (s : ℤ)) (k - -(r : ℤ)) (k + (s : ℤ) - -(r : ℤ))
      rfl (by omega) (by omega) (by omega) α)
  gysin_naturality := by
    intro Y' g hY' hX' L t hL hXd iso hiso hbase hisoProper k α
    refine ⟨flatPullbackMap D (pullback.fst f g ≫ sX) hX' (g ≫ sY) hY' (pullback.snd f g)
      (bivariantPullbackSnd_comp_base D sX sY hf g) r
      (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY' hX').1
      (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr g hY' hX').2
      (k + 1) (k - -(r : ℤ) + 1) (by omega) α,
      flatPullbackMap D (pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX)
        hXd (((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sY)
        (isGood_vanishingLocus D (g ≫ sY) hY' L t)
        (pullback.snd f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g))
        (bivariantPullbackSnd_comp_base D sX sY hf _) r
        (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr _
          (isGood_vanishingLocus D (g ≫ sY) hY' L t) hXd).1
        (isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sY hY hf r hflat hr _
          (isGood_vanishingLocus D (g ≫ sY) hY' L t) hXd).2 k (k - -(r : ℤ)) (by omega)
        (gysinCycleMap D (g ≫ sY) (vanishingLocus D (g ≫ sY) hY' L t)
          (isGood_vanishingLocus D (g ≫ sY) hY' L t) k
          (sectionGysinRule D (g ≫ sY) hY' L t k hL) α), ?_, rfl, ?_⟩
    · exact congrArg (chowClassCanonical.{u + 1} D (pullback.fst f g ≫ sX) hX'
        (k + 1 - -(r : ℤ)))
        (cycleGroupDegreeCongr_flatPullbackMap D (pullback.fst f g ≫ sX) hX' (g ≫ sY) hY'
          (bivariantPullbackSnd_comp_base D sX sY hf g) r _ _ (k + 1) _ _ (by omega) _ _ α).symm
    · exact chowClassCanonical_properCyclePushforward_flatPullbackMap_gysinCycleMap D sX hX sY hY
        hf r hflat hr g hY' hX' L t hL hXd iso hiso hbase hisoProper k (k - -(r : ℤ))
        (by omega) (by omega) α

end Registration

end AlgebraicGeometry.Space

end
