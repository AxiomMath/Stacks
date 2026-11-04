module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalProduct
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionFlatCommute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.SmoothChowCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Associativity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalAssoc
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionAction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField

/-!
# Flat pullback, the canonical intersection product, and Stacks 0FG0 (1) and (4)

Let `k` be a field. The associativity of composition of correspondences (Stacks 0FG0 (1)) is
proved in `StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Associativity` for every
family of diagonal classes whose intersection products satisfy three properties: flat pullback is
multiplicative (Stacks 0FFB for a flat morphism), the projection formula for a flat proper morphism
(Stacks 0FFC) and associativity (Stacks 0FC1). This file proves the first two for the canonical
family of Gysin classes of the diagonals (Stacks 0FBR), and concludes Stacks 0FG0 (1) and (4).

The proofs are the source's proofs of Stacks 0FFB and Stacks 0FFC, carried out for the flat
pullback class `f^*` of Stacks 0B78 in place of the Gysin map: by Stacks 0FC2 every class on `W` is
`c ∩ [W]_N` for some `c ∈ A^*(W)` and `(c ∩ [W]_N) · β = c ∩ β`; `f^*` commutes with every class
and carries `[W]_N` to `[W']_{t+N}`. The arguments for an arbitrary class `F` with these two
properties are `Stacks.Chow.BivariantClass.capTargetHom_selfIntersectionProduct` and
`Stacks.Chow.BivariantClass.properChowPushforward_selfIntersectionProduct_capTargetHom`.

## Main results

* `Stacks.Chow.flatPullbackBivariantClass_capTarget_heq` — the class of Stacks 0B78 caps a class
  on its own target by flat pullback.
* `Stacks.WeilCohomology.DiagonalClassFamily.flatPullbackMul_of`,
  `Stacks.WeilCohomology.DiagonalClassFamily.projectionFormula_of` — the two properties for any
  family satisfying both clauses of Stacks 0FC2 (and, for the second, symmetric).
* `Stacks.WeilCohomology.canonicalDiagonalClassFamily_capEqProduct` — the second clause of
  Stacks 0FC2 for the canonical family, from Stacks 0FBP and Stacks 0FBS.
* `Stacks.WeilCohomology.canonicalDiagonalClassFamily_compositionAssoc` — associativity of
  equidimensional composition for the canonical family.
* `Stacks.WeilCohomology.comp_bilinear_assoc_canonicalDiagonalClassFamily` — **Stacks 0FG0 (1)**.
* `Stacks.WeilCohomology.comp_pullback_pushforward_canonicalDiagonalClassFamily` —
  **Stacks 0FG0 (4)**.

## Implementation notes

The source works with smooth projective schemes. Here the schemes are smooth and separated over
`k`, of arbitrary dimension, and properness is assumed exactly where a pushforward is formed: of
`Y` and `Z` for (1), of `X`, `Y` and `Z` for (4).

## References

* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FFB](https://stacks.math.columbia.edu/tag/0FFB)
* [Stacks Project, Tag 0FFC](https://stacks.math.columbia.edu/tag/0FFC)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section CapTarget

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (r : ℕ)
  (hfr : AlgebraicGeometry.RelativeDimension f r) (hS1 : FlatPullbackDescends C)
  (c : BivariantClass C G sX sY f hf (-(r : ℤ)))
  (hc : IsBivariantFlatPullback C G sX sY f hf r hfr hS1 c)

include hc in
/-- **A class characterized by the rule of Stacks 0B78 caps a class on its own target by flat
pullback**: for `f : X ⟶ Y` flat of relative dimension `r` and `β ∈ CH_k(Y)`, `f^* ∩ β = f^*β`
in `CH_{k+r}(X)`, the cap product being read on `X` through `X ×_Y Y ≅ X`. -/
theorem flatPullbackBivariantClass_capTarget_heq (k : ℤ) (β : chowGroup C sY k) :
    c.capTarget C G sX sY f hf (-(r : ℤ)) k β ≍
      flatPullbackChow C sX sY f hf r hfr k (hS1 _ _ _ _ _ _ k) β := by
  have hcap := hc.cap_heq (𝟙 Y) k (chowGroupCongr C (Category.id_comp sY).symm k β)
  have hf' : f ≫ (𝟙 Y ≫ sY) = sX := by rw [Category.id_comp, hf]
  have key := chowPushforwardOfIso_flatPullbackChow_eq_of_comp C sX
    (pullback.fst f (𝟙 Y) ≫ sX) sX (𝟙 Y ≫ sY) f hf' (pullback.snd f (𝟙 Y))
    (pullbackSnd_comp_structureMorphism hf (𝟙 Y)) (𝟙 X) (Category.id_comp sX)
    (pullbackIdIso f).inv (pullbackIdIso_inv_comp f sX) f (Category.id_comp f)
    (by rw [pullbackIdIso_inv_comp, pullback.condition, Category.comp_id]) r hfr
    (relativeDimension_pullbackSnd f hfr (𝟙 Y)) k
    (hS1 _ _ _ _ _ _ k) (hS1 _ _ _ _ _ _ k) (chowGroupCongr C (Category.id_comp sY).symm k β)
  rw [chowPushforwardOfIso_id] at key
  have hbase : ∀ (s s' : Y ⟶ C.S) [LocallyOfFiniteType s] [LocallyOfFiniteType s'] (hs : s = s')
      (hfs : f ≫ s = sX) (hfs' : f ≫ s' = sX) (x : chowGroup C s k) (x' : chowGroup C s' k),
      x ≍ x' → flatPullbackChow C sX s f hfs r hfr k (hS1 _ _ _ _ _ _ k) x ≍
        flatPullbackChow C sX s' f hfs' r hfr k (hS1 _ _ _ _ _ _ k) x' := by
    intro s s' _ _ hs hfs hfs' x x' hx
    subst hs
    obtain rfl := eq_of_heq hx
    rfl
  unfold BivariantClass.capTarget
  refine (chowPushforwardOfIso_heq _ _ (pullbackIdIso_inv_comp f sX) rfl rfl (by ring)
    hcap).trans ?_
  refine (heq_of_eq key).trans ?_
  exact hbase _ _ (Category.id_comp sY) hf' hf _ _ (chowGroupCongr_heq C _ k β)

include hc in
/-- `Stacks.Chow.flatPullbackBivariantClass_capTarget_heq` for the class read in an equal
degree. -/
theorem flatPullbackBivariantClass_degreeCongr_capTarget_heq {q : ℤ} (h : -(r : ℤ) = q) (k : ℤ)
    (β : chowGroup C sY k) :
    (bivariantClassDegreeCongr C G sX sY f hf h c).capTarget C G sX sY f hf q k β ≍
      flatPullbackChow C sX sY f hf r hfr k (hS1 _ _ _ _ _ _ k) β := by
  subst h
  exact flatPullbackBivariantClass_capTarget_heq C G sX sY f hf r hfr hS1 c hc k β

end CapTarget

end Stacks.Chow

namespace Stacks.WeilCohomology

open Stacks.Chow

variable {k : Type u} [Field k]

/-- A self-intersection product depends on its two arguments only up to heterogeneous equality,
their degrees being allowed to be written differently. -/
theorem selfIntersectionProduct_heq_of_heq {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sW] (D : ℤ)
    (Dc : BivariantClass (fieldChowSituation k) (fieldGysinSystem k) sW
      (selfProductStructure (fieldChowSituation k) sW) (pullback.diagonal sW)
      (diagonal_comp_selfProductStructure (fieldChowSituation k) sW) D)
    {a a' b b' : ℤ} (ha : a = a') (hb : b = b') {x : chowGroup (fieldChowSituation k) sW a}
    {x' : chowGroup (fieldChowSituation k) sW a'} {y : chowGroup (fieldChowSituation k) sW b}
    {y' : chowGroup (fieldChowSituation k) sW b'} (hx : x ≍ x') (hy : y ≍ y') :
    selfIntersectionProduct (fieldChowSituation k)
        (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW D Dc a b x y ≍
      selfIntersectionProduct (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW D Dc a' b' x' y' := by
  subst ha hb
  cases hx
  cases hy
  rfl

/-- The surjective half of the first clause of Stacks 0FC2 for every scheme smooth over `k`
of constant dimension: `c ↦ c ∩ [W]_N` is onto `CH_{N-p}(W)`. -/
def CapFundamentalClassSurjective (k : Type u) [Field k] : Prop :=
  ∀ {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (N : ℕ), RelativeDimension sW N → ∀ p : ℤ,
      Function.Surjective (chowCohomologyCapFundamentalClass (fieldChowSituation k)
        (fieldGysinSystem k) sW N p)

/-- The second clause of Stacks 0FC2 for the products formed with the family `Δ`, in the form of
the action of `A^p(W)` on `CH_*(W)`: `c ∩ β = (c ∩ [W]_N) · β`. -/
def DiagonalClassFamily.CapEqProduct (Δ : DiagonalClassFamily k) : Prop :=
  ∀ {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (N : ℕ) (hN : RelativeDimension sW N) (p : ℤ)
    (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sW p) (m : ℤ)
    (β : chowGroup (fieldChowSituation k) sW m),
    chowCohomologyCap (fieldChowSituation k) (fieldGysinSystem k) sW p c m β =
      chowGroupDegreeEquiv (fieldChowSituation k) sW (by ring : ((N : ℤ) - p) + m - N = m - p)
        (selfIntersectionProduct (fieldChowSituation k)
            (fieldChowSituation_dimensionFunction_of_isClosed k)
          (fieldGysinSystem k) sW N (Δ sW N hN) (N - p) m
          (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sW N p c)
          β)

/-- A scheme smooth over `k` of constant dimension `N` has δ-dimension at most `N`. -/
theorem schemeDeltaDimension_le_of_relativeDimension {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Flat sW] {N : ℕ}
    (hN : RelativeDimension sW N) :
    schemeDeltaDimension (fieldChowSituation k) sW ≤ ((N : ℤ) : EInt) := by
  simpa using schemeDeltaDimension_le_add_of_flat (fieldChowSituation k) sW
    (𝟙 (fieldChowSituation k).S ≫ 𝟙 (fieldChowSituation k).S) sW (by simp) N hN
    (schemeDeltaDimension_fieldChowSituation_base k)

variable {Δ : DiagonalClassFamily k}

/-- The three facts about the degree-shifted flat pullback class `F` of Stacks 0B78 used in the
proofs of Stacks 0FFB and 0FFC: it caps by flat pullback, it carries `[W]_N` to `[W']_{t+N}`
(Stacks 0FF7) and it commutes with every class (Stacks 0FF6). -/
private theorem flatPullbackBivariantClass_cap_facts {W W' : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW] (f : W' ⟶ W)
    [LocallyOfFiniteType f] [Flat f] {t N : ℕ} (ht : RelativeDimension f t)
    (hN : RelativeDimension sW N)
    (F : BivariantClass (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl
      ((N : ℤ) - ((t + N : ℕ) : ℤ)))
    (hF : F = bivariantClassDegreeCongr (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f
      rfl (by push_cast; ring) (flatPullbackBivariantClassOfInvertible (fieldChowSituation k)
        (f ≫ sW) sW f rfl t ht)) :
    (∀ (j : ℤ) (β : chowGroup (fieldChowSituation k) sW j),
      F.capTarget (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl _ j β ≍
        flatPullbackChow (fieldChowSituation k) (f ≫ sW) sW f rfl t ht j
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β) ∧
    F.capTargetHom (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl
      ((N : ℤ) - ((t + N : ℕ) : ℤ)) N (fundamentalChowClass (fieldChowSituation k) sW N) =
      fundamentalChowClass (fieldChowSituation k) (f ≫ sW)
        ((N : ℤ) - ((N : ℤ) - ((t + N : ℕ) : ℤ))) ∧
    ∀ (p : ℤ) (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sW p),
      BivariantCommute (fieldChowSituation k) (fieldGysinSystem k) sW f (𝟙 W)
        ((N : ℤ) - ((t + N : ℕ) : ℤ)) p
        (bivariantClassCongrBase (fieldChowSituation k) (fieldGysinSystem k) f rfl rfl _ F)
        (bivariantClassCongrBase (fieldChowSituation k) (fieldGysinSystem k) (𝟙 W)
          (Category.id_comp sW).symm rfl p c) := by
  have hdeg : -(t : ℤ) = (N : ℤ) - ((t + N : ℕ) : ℤ) := by push_cast; ring
  have hcapF : ∀ (j : ℤ) (β : chowGroup (fieldChowSituation k) sW j),
      F.capTarget (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl _ j β ≍
        flatPullbackChow (fieldChowSituation k) (f ≫ sW) sW f rfl t ht j
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β := by
    subst hF
    exact fun j β ↦ flatPullbackBivariantClass_degreeCongr_capTarget_heq _ _ _ _ f rfl t ht
      (flatPullbackDescends _) _
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible (fieldChowSituation k)
        (f ≫ sW) sW f rfl t ht) hdeg j β
  have h0FF7 : F.capTargetHom (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl
      ((N : ℤ) - ((t + N : ℕ) : ℤ)) N (fundamentalChowClass (fieldChowSituation k) sW N) =
      fundamentalChowClass (fieldChowSituation k) (f ≫ sW)
        ((N : ℤ) - ((N : ℤ) - ((t + N : ℕ) : ℤ))) := by
    rw [BivariantClass.capTargetHom_apply]
    refine eq_of_heq ((hcapF N _).trans ?_)
    rw [flatPullbackChow_fundamentalChowClass _ _ _ _ _ _ _ _ _
      (schemeDeltaDimension_le_of_relativeDimension sW hN)]
    exact fundamentalChowClass_heq _ _ (by push_cast; ring)
  have h0FF6 : ∀ (p : ℤ) (c : chowCohomologyComponent (fieldChowSituation k)
      (fieldGysinSystem k) sW p),
      BivariantCommute (fieldChowSituation k) (fieldGysinSystem k) sW f (𝟙 W)
        ((N : ℤ) - ((t + N : ℕ) : ℤ)) p
        (bivariantClassCongrBase (fieldChowSituation k) (fieldGysinSystem k) f rfl rfl _ F)
        (bivariantClassCongrBase (fieldChowSituation k) (fieldGysinSystem k) (𝟙 W)
          (Category.id_comp sW).symm rfl p c) := by
    subst hF
    exact fun p c ↦ bivariantCommute_bivariantClassDegreeCongr_left _ hdeg
      (bivariantCommute_of_isBivariantFlatPullback _ _ sW f (𝟙 W) t ht (flatPullbackDescends _) p _
        _ (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible (fieldChowSituation k)
          (f ≫ sW) sW f rfl t ht))
  exact ⟨hcapF, h0FF7, h0FF6⟩

/-- **Stacks 0FFB for a flat morphism, from Stacks 0FC2.** If the family `Δ` satisfies both
clauses of Stacks 0FC2 in the form `Stacks.Chow.chowCohomologyCapFundamentalClass` onto and
`c ∩ β = (c ∩ [W]_N) · β`, then flat pullback is multiplicative for its products. The proof is the
source's proof of Stacks 0FFB with the Gysin map replaced by the flat pullback class of
Stacks 0B78: it commutes with every class
(`Stacks.Chow.bivariantCommute_of_isBivariantFlatPullback`) and carries `[W]_N` to `[W']_{t+N}`
(`Stacks.Chow.flatPullbackChow_fundamentalChowClass`). -/
theorem DiagonalClassFamily.flatPullbackMul_of (hsurj : CapFundamentalClassSurjective k)
    (hcap : Δ.CapEqProduct) : Δ.FlatPullbackMul := by
  intro W W' sW _ _ sW' _ _ f _ _ hf t N ht hN hN' n m a b
  subst hf
  have hdeg : -(t : ℤ) = (N : ℤ) - ((t + N : ℕ) : ℤ) := by push_cast; ring
  set F := bivariantClassDegreeCongr (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl
    hdeg (flatPullbackBivariantClassOfInvertible (fieldChowSituation k)
      (f ≫ sW) sW f rfl t ht) with hF
  obtain ⟨hcapF, h0FF7, h0FF6⟩ := flatPullbackBivariantClass_cap_facts sW f ht hN F hF
  have key := BivariantClass.capTargetHom_selfIntersectionProduct (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_of_isClosed k) (f ≫ sW) sW rfl ((t + N : ℕ) : ℤ) N
    (Δ (f ≫ sW) (t + N) hN') (Δ sW N hN) F h0FF7 h0FF6 (hsurj sW N hN) (hcap sW N hN)
    (hcap (f ≫ sW) (t + N) hN') n m a b
  simp only [BivariantClass.capTargetHom_apply] at key
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ((hcapF _ _).symm.trans
    ((heq_of_eq key).trans ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_))))
  exact selfIntersectionProduct_heq_of_heq _ _ _ (by push_cast; ring) (by push_cast; ring)
    (hcapF n a) (hcapF m b)

/-- **Stacks 0FFC for a flat proper morphism, from Stacks 0FC2.** If the family `Δ` satisfies both
clauses of Stacks 0FC2 as in `Stacks.WeilCohomology.DiagonalClassFamily.flatPullbackMul_of` and
its products are symmetric, the projection formula holds for them on both sides. The first
identity is the source's proof of Stacks 0FFC with the Gysin map replaced by the flat pullback
class of Stacks 0B78; the second is the first read through the symmetry of the products. -/
theorem DiagonalClassFamily.projectionFormula_of (hsurj : CapFundamentalClassSurjective k)
    (hcap : Δ.CapEqProduct) (hsymm : Δ.IsSymmetric) : Δ.ProjectionFormula := by
  intro W W' sW _ _ sW' _ _ f _ _ hf t N ht hN hN' n m x y
  subst hf
  have hdeg : -(t : ℤ) = (N : ℤ) - ((t + N : ℕ) : ℤ) := by push_cast; ring
  set F := bivariantClassDegreeCongr (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl
    hdeg (flatPullbackBivariantClassOfInvertible (fieldChowSituation k)
      (f ≫ sW) sW f rfl t ht) with hF
  obtain ⟨hcapF, h0FF7, h0FF6⟩ := flatPullbackBivariantClass_cap_facts sW f ht hN F hF
  -- the first identity, at an arbitrary pair of degrees
  have first : ∀ (n m : ℤ) (x : chowGroup (fieldChowSituation k) (f ≫ sW) n)
      (y : chowGroup (fieldChowSituation k) sW m),
      properChowPushforward (fieldChowSituation k) (f ≫ sW) sW f rfl (n + (m + t) - (t + N : ℕ))
          (properPushforwardDescends _ _ _ _ _ _)
          (selfIntersectionProduct (fieldChowSituation k)
              (fieldChowSituation_dimensionFunction_of_isClosed k)
            (fieldGysinSystem k) (f ≫ sW) ((t + N : ℕ) : ℤ) (Δ (f ≫ sW) (t + N) hN') n (m + t) x
            (flatPullbackChow (fieldChowSituation k) (f ≫ sW) sW f rfl t ht m
              (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) y)) ≍
        selfIntersectionProduct (fieldChowSituation k)
            (fieldChowSituation_dimensionFunction_of_isClosed k)
          (fieldGysinSystem k) sW N (Δ sW N hN) n m
          (properChowPushforward (fieldChowSituation k) (f ≫ sW) sW f rfl n
            (properPushforwardDescends _ _ _ _ _ _) x) y := by
    intro n m x y
    have key := BivariantClass.properChowPushforward_selfIntersectionProduct_capTargetHom
      (fieldChowSituation k) (fieldChowSituation_dimensionFunction_of_isClosed k) (f ≫ sW) sW rfl
      ((t + N : ℕ) : ℤ) N (Δ (f ≫ sW) (t + N) hN') (Δ sW N hN) F h0FF7 h0FF6 (hsurj sW N hN)
      (hcap sW N hN) (hcap (f ≫ sW) (t + N) hN') (hsymm (f ≫ sW) (t + N) hN')
      (hsymm sW N hN) n m x y
    simp only [BivariantClass.capTargetHom_apply] at key
    refine HEq.trans ?_ ((heq_of_eq key).trans (chowGroupDegreeEquiv_heq _ _ _ _))
    exact properChowPushforward_heq_congr _ _ _ f rfl (by push_cast; ring) _ _ _ _
      (selfIntersectionProduct_heq_of_heq _ _ _ rfl (by push_cast; ring) HEq.rfl (hcapF m y).symm)
  refine ⟨eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (first n m x y)), ?_⟩
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
  rw [hsymm sW N hN m n]
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm
  refine HEq.trans ?_ (first n m x y)
  rw [hsymm (f ≫ sW) (t + N) hN' (m + t) n]
  exact properChowPushforward_heq_congr _ _ _ f rfl (by ring) _ _ _ _
    (chowGroupDegreeEquiv_heq _ _ _ _)

/-! ### The canonical family -/

/-- **The surjective half of the first clause of Stacks 0FC2**, for every scheme smooth over `k`
of constant dimension
(`Stacks.Chow.chowCohomologyCapFundamentalClass_bijective_of_smooth_field`). -/
theorem capFundamentalClassSurjective (k : Type u) [Field k] : CapFundamentalClassSurjective k :=
  fun sW _ _ N hN p ↦ (chowCohomologyCapFundamentalClass_bijective_of_smooth_field k sW N hN p).2

/-- **The second clause of Stacks 0FC2 for the canonical family**: `c ∩ β = (c ∩ [W]_N) · β` for
`c ∈ A^p(W)`. This is `Stacks.Chow.chowCohomologyCap_eq_intersectionProduct` at the Gysin class of
the diagonal, which commutes with every class by Stacks 0FBP
(`Stacks.Chow.diagonalGysinClass_bivariantCommute`) and satisfies `Δ^! ∘ pr₂^* = 1` by Stacks 0FBS
(`Stacks.Chow.diagonalGysinClass_compFlatPullbackEqOne_snd`). -/
theorem canonicalDiagonalClassFamily_capEqProduct (k : Type u) [Field k] :
    DiagonalClassFamily.CapEqProduct (canonicalDiagonalClassFamily k) := by
  intro W sW _ _ N hN p c m β
  exact chowCohomologyCap_eq_intersectionProduct k sW N hN
    (diagonalGysinClass (fieldChowSituation k) sW sW hN)
    (fun f₂ _ p₂ c₂ ↦ diagonalGysinClass_bivariantCommute _ sW sW hN f₂ p₂ c₂)
    (diagonalGysinClass_compFlatPullbackEqOne_snd _ sW sW hN (𝟙 _) (Category.comp_id sW)) p c m β

/-- **Flat pullback is multiplicative for the canonical intersection products** (Stacks 0FFB for a
flat morphism of schemes smooth over `k`). -/
theorem canonicalDiagonalClassFamily_flatPullbackMul (k : Type u) [Field k] :
    DiagonalClassFamily.FlatPullbackMul (canonicalDiagonalClassFamily k) :=
  DiagonalClassFamily.flatPullbackMul_of (capFundamentalClassSurjective k)
    (canonicalDiagonalClassFamily_capEqProduct k)

/-- **The projection formula for the canonical intersection products** (Stacks 0FFC for a flat
proper morphism of schemes smooth over `k`), on both sides. -/
theorem canonicalDiagonalClassFamily_projectionFormula (k : Type u) [Field k] :
    DiagonalClassFamily.ProjectionFormula (canonicalDiagonalClassFamily k) :=
  DiagonalClassFamily.projectionFormula_of (capFundamentalClassSurjective k)
    (canonicalDiagonalClassFamily_capEqProduct k) (canonicalDiagonalClassFamily_isSymmetric k)

/-- **Associativity of composition of correspondences between schemes of constant dimension, for
the canonical family**: from Stacks 0FFB and the projection formula of Stacks 0FFC for flat
morphisms and associativity of the product, Stacks 0FC1
(`Stacks.WeilCohomology.canonicalDiagonalClassFamily_intersectionAssoc`). -/
theorem canonicalDiagonalClassFamily_compositionAssoc (k : Type u) [Field k] :
    DiagonalClassFamily.CompositionAssoc (canonicalDiagonalClassFamily k) :=
  DiagonalClassFamily.compositionAssoc_of (canonicalDiagonalClassFamily_flatPullbackMul k)
    (canonicalDiagonalClassFamily_projectionFormula k)
    (canonicalDiagonalClassFamily_intersectionAssoc k)

/-! ### Stacks 0FG0 (1) and (4) -/

section Tags

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sZ : Z ⟶ (fieldChowSituation k).S)
  (sW : W ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]
  [Smooth sZ] [IsSeparated sZ] [Smooth sW] [IsSeparated sW]

/-- **Stacks Project, Tag 0FG0 (1).** For schemes `X`, `Y`, `Z`, `W` smooth over `k`, of arbitrary,
not necessarily constant, dimension, with `Y` and `Z` proper, composition of correspondences
`Corrʳ(X, Y) × Corrˢ(Y, Z) ⟶ Corr^{r+s}(X, Z)` is `ℚ`-bilinear and associative,
`c'' ∘ (c' ∘ c) = (c'' ∘ c') ∘ c`, the two sides compared through `(r + s) + t = r + (s + t)`; the
intersection products are formed with the Gysin classes of the diagonals of Stacks 0FBR. -/
@[stacks 0FG0 "(1): composition of correspondences is Q-bilinear and associative"]
theorem comp_bilinear_assoc_canonicalDiagonalClassFamily [IsProper sY] [IsProper sZ]
    (r s t : ℤ) :
    (∀ (a b : ℚ) (c₁ c₂ : Corr k sX sY r) (c' : Corr k sY sZ s),
      comp k sX sY sZ (canonicalDiagonalClassFamily k) r s (a • c₁ + b • c₂) c' =
        a • comp k sX sY sZ (canonicalDiagonalClassFamily k) r s c₁ c' +
          b • comp k sX sY sZ (canonicalDiagonalClassFamily k) r s c₂ c') ∧
    (∀ (a b : ℚ) (c : Corr k sX sY r) (c'₁ c'₂ : Corr k sY sZ s),
      comp k sX sY sZ (canonicalDiagonalClassFamily k) r s c (a • c'₁ + b • c'₂) =
        a • comp k sX sY sZ (canonicalDiagonalClassFamily k) r s c c'₁ +
          b • comp k sX sY sZ (canonicalDiagonalClassFamily k) r s c c'₂) ∧
    ∀ (c : Corr k sX sY r) (c' : Corr k sY sZ s) (c'' : Corr k sZ sW t),
      corrCongr k sX sW (add_assoc r s t)
          (comp k sX sZ sW (canonicalDiagonalClassFamily k) (r + s) t
            (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s c c') c'') =
        comp k sX sY sW (canonicalDiagonalClassFamily k) r (s + t) c
          (comp k sY sZ sW (canonicalDiagonalClassFamily k) s t c' c'') :=
  comp_bilinear_assoc k sX sY sZ sW (canonicalDiagonalClassFamily k)
    (canonicalDiagonalClassFamily_compositionAssoc k) r s t

/-- **Stacks Project, Tag 0FG0 (4).** For schemes `X`, `Y`, `Z` smooth and proper over `k`, of
arbitrary, not necessarily constant, dimension, composition of correspondences is compatible with
pullback and pushforward of cycles: for `c ∈ Corrʳ(X, Y)` and `c' ∈ Corrˢ(Y, Z)`,

  `(c' ∘ c)^*(α) = c^*((c')^*(α))`  for `α ∈ CH_m(Z) ⊗ ℚ`, and
  `(c' ∘ c)_*(α) = (c')_*(c_*(α))`  for `α ∈ CH^i(X) ⊗ ℚ`,

the degrees `m - (r + s) = (m - s) - r` and `i + (r + s) = (i + r) + s` being identified, the
intersection products being formed with the Gysin classes of the diagonals of Stacks 0FBR. -/
@[stacks 0FG0 "(4): composition of correspondences is compatible with pushforward and pullback \
of cycles"]
theorem comp_pullback_pushforward_canonicalDiagonalClassFamily [IsProper sX] [IsProper sY]
    [IsProper sZ] (r s : ℤ) (c : Corr k sX sY r) (c' : Corr k sY sZ s) :
    (∀ (m : ℤ) (α : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sZ m)),
      Stacks.WeilCohomology.pullback k sX sZ (canonicalDiagonalClassFamily k) (r + s) m
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s c c') α =
        (chowGroupDegreeEquiv _ sX
            (show m - s - r = m - (r + s) by ring)).toIntLinearEquiv.baseChange
          ℤ ℚ _ _ (Stacks.WeilCohomology.pullback k sX sY (canonicalDiagonalClassFamily k) r (m - s)
            c (Stacks.WeilCohomology.pullback k sY sZ (canonicalDiagonalClassFamily k) s m c' α))) ∧
    ∀ (i : ℤ) (α : CodimChow k sX i),
      pushforward k sX sZ (canonicalDiagonalClassFamily k) (r + s) i
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s c c') α =
        codimChowCongr k sZ (add_assoc i r s)
          (pushforward k sY sZ (canonicalDiagonalClassFamily k) s (i + r) c'
            (pushforward k sX sY (canonicalDiagonalClassFamily k) r i c α)) :=
  ⟨fun m α ↦ pullback_comp k sX sY sZ (canonicalDiagonalClassFamily k)
      (canonicalDiagonalClassFamily_compositionAssoc k)
      (canonicalDiagonalClassFamily_isoInvariant k) r s m c c' α,
    fun i α ↦ pushforward_comp k sX sY sZ (canonicalDiagonalClassFamily k)
      (canonicalDiagonalClassFamily_compositionAssoc k)
      (canonicalDiagonalClassFamily_isoInvariant k) (canonicalDiagonalClassFamily_isSymmetric k)
      r s i c c' α⟩

end Tags

end Stacks.WeilCohomology

end
