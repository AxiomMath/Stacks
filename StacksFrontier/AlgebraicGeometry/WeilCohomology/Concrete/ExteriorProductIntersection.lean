module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommutingEveryCap
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionExteriorProduct

/-!
# The exterior product is the intersection product of the two pullbacks

Let `k` be a field and let `X`, `Y` be smooth over `k`, of constant dimensions `d` and `e`, with
projections `p₁ : X ×_k Y ⟶ X` and `p₂ : X ×_k Y ⟶ Y`. Remark 0FHD of the Stacks Project uses,
"omitting the proof", that

  `α × β = p₁^*α · p₂^*β`   in   `CH_*(X ×_k Y)`

for `α ∈ CH_*(X)` and `β ∈ CH_*(Y)`. This file proves it. Writing `β = c ∩ [Y]` with
`c ∈ A^*(Y)` (Stacks 0FC2), the pullback `p₂^*β` is `res(c) ∩ [X ×_k Y]` (flat pullback commutes
with bivariant classes, Stacks 0B76 (2), and carries fundamental classes to fundamental classes),
so `p₁^*α · p₂^*β = res(c) ∩ p₁^*α` (Stacks 0FC2 for the canonical products, and their symmetry).
In the same way `p₁^*α = α × [Y]`, by Stacks 0FBY in the first variable applied to
`[X ×_k Y] = [X] × [Y]`, and then `res(c) ∩ (α × [Y]) = α × (c ∩ [Y]) = α × β` by Stacks 0FBY.

## Main results

* `Stacks.Chow.flatPullbackChow_chowCohomologyCapFundamentalClass`: `f^*(c ∩ [W]) = res(c) ∩ [W']`
  for `f : W' ⟶ W` flat.

## References

* [Stacks Project, Tag 0FHD](https://stacks.math.columbia.edu/tag/0FHD)
* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (fieldGysinSystem
  schemeDeltaDimension_le_of_relativeDimension)

variable {k : Type u} [Field k]

/-- The map of Stacks 0FC2 does not depend on how the degree is written. -/
theorem chowCohomologyCapFundamentalClass_heq_of_eq {C : ChowSituation.{u}} {G : GysinSystem C}
    {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] {d d' : ℤ} (h : d = d') (p : ℤ)
    (c : chowCohomologyComponent C G sW p) :
    chowCohomologyCapFundamentalClass C G sW d p c ≍
      chowCohomologyCapFundamentalClass C G sW d' p c := by
  subst h
  rfl

/-- **Flat pullback of `c ∩ [W]`.** For `f : W' ⟶ W` flat of relative dimension `t` over `k`, `W`
smooth of dimension `N` and `c ∈ A^q(W)`, `f^*(c ∩ [W]_N) = res(c) ∩ [W']_{t+N}`. -/
theorem flatPullbackChow_chowCohomologyCapFundamentalClass {W W' : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW] (f : W' ⟶ W)
    [LocallyOfFiniteType f] [Flat f] {t N : ℕ} (ht : RelativeDimension f t)
    (hN : RelativeDimension sW N) (q : ℤ)
    (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sW q) :
    flatPullbackChow (fieldChowSituation k) (f ≫ sW) sW f rfl t ht ((N : ℤ) - q)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sW N q c) ≍
      chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW)
        ((t + N : ℕ) : ℤ) q
        (chowCohomologyRestrictionOfEq (fieldChowSituation k) (f ≫ sW) sW rfl (fieldGysinSystem k)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) q c) := by
  have hdeg : -(t : ℤ) = (N : ℤ) - ((t + N : ℕ) : ℤ) := by push_cast; ring
  set F := bivariantClassDegreeCongr (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl
    hdeg (flatPullbackBivariantClassOfInvertible (fieldChowSituation k)
      (f ≫ sW) sW f rfl t ht) with hF
  have hcapF : ∀ (j : ℤ) (β : chowGroup (fieldChowSituation k) sW j),
      F.capTarget (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl _ j β ≍
        flatPullbackChow (fieldChowSituation k) (f ≫ sW) sW f rfl t ht j
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β :=
    fun j β ↦ flatPullbackBivariantClass_degreeCongr_capTarget_heq _ _ _ _ f rfl t ht
      (flatPullbackDescends _) _
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible (fieldChowSituation k)
        (f ≫ sW) sW f rfl t ht) hdeg j β
  have h0FF7 : F.capTarget (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) sW f rfl
      ((N : ℤ) - ((t + N : ℕ) : ℤ)) N (fundamentalChowClass (fieldChowSituation k) sW N) ≍
      fundamentalChowClass (fieldChowSituation k) (f ≫ sW) ((t + N : ℕ) : ℤ) := by
    refine (hcapF N _).trans ?_
    rw [flatPullbackChow_fundamentalChowClass _ _ _ _ _ _ _ _ _
      (schemeDeltaDimension_le_of_relativeDimension sW hN)]
    exact fundamentalChowClass_heq _ _ (by push_cast; ring)
  have hcomm : BivariantCommute (fieldChowSituation k) (fieldGysinSystem k) sW f (𝟙 W)
      ((N : ℤ) - ((t + N : ℕ) : ℤ)) q
      (bivariantClassCongrBase (fieldChowSituation k) (fieldGysinSystem k) f rfl rfl _ F)
      (bivariantClassCongrBase (fieldChowSituation k) (fieldGysinSystem k) (𝟙 W)
        (Category.id_comp sW).symm rfl q c) :=
    bivariantCommute_bivariantClassDegreeCongr_left _ hdeg
      (bivariantCommute_of_isBivariantFlatPullback _ _ sW f (𝟙 W) t ht
          (flatPullbackDescends _) q _ _
        (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible (fieldChowSituation k)
          (f ≫ sW) sW f rfl t ht))
  have key := BivariantClass.capTarget_chowCohomologyCap_of_bivariantCommute
    (fieldChowSituation k) (fieldGysinSystem k)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) (f ≫ sW) sW f rfl q _ F c hcomm N
    (fundamentalChowClass (fieldChowSituation k) sW N)
  rw [chowCohomologyCap_fundamentalChowClass] at key
  refine (hcapF _ _).symm.trans
    ((heq_of_eq key).trans ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_))
  have hdegs : (N : ℤ) - ((N : ℤ) - ((t + N : ℕ) : ℤ)) = ((t + N : ℕ) : ℤ) := by ring
  have hcong : ∀ (m : ℤ) (hm : m = ((t + N : ℕ) : ℤ))
      (x : chowGroup (fieldChowSituation k) (f ≫ sW) m),
      x ≍ fundamentalChowClass (fieldChowSituation k) (f ≫ sW) ((t + N : ℕ) : ℤ) →
      chowCohomologyCap (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW) q
          (chowCohomologyRestrictionOfEq (fieldChowSituation k) (f ≫ sW) sW rfl
            (fieldGysinSystem k) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) q c) m x ≍
        chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) (f ≫ sW)
          ((t + N : ℕ) : ℤ) q
          (chowCohomologyRestrictionOfEq (fieldChowSituation k) (f ≫ sW) sW rfl
            (fieldGysinSystem k) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) q c) := by
    intro m hm x hx
    subst hm
    obtain rfl := eq_of_heq hx
    rw [chowCohomologyCap_fundamentalChowClass]
  exact hcong _ hdegs _ h0FF7

/-- `flatPullbackChow_chowCohomologyCapFundamentalClass` with the structure morphism of `W'` given
up to equality. -/
theorem flatPullbackChow_chowCohomologyCapFundamentalClass' {W W' : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW'] (f : W' ⟶ W)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sW = sW') {t N : ℕ} (ht : RelativeDimension f t)
    (hN : RelativeDimension sW N) (q : ℤ)
    (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sW q) :
    flatPullbackChow (fieldChowSituation k) sW' sW f hf t ht ((N : ℤ) - q)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sW N q c) ≍
      chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sW'
        ((t + N : ℕ) : ℤ) q
        (chowCohomologyRestrictionOfEq (fieldChowSituation k) sW' sW hf (fieldGysinSystem k)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) q c) := by
  subst hf
  exact flatPullbackChow_chowCohomologyCapFundamentalClass sW f ht hN q c

/-- For a class of `A^p(Y) = A^p(Y ⟶ Y)` the cap product on a class of `Y`
(`Stacks.Chow.BivariantClass.capTarget`) is the operational action
`Stacks.Chow.chowCohomologyCap`: both are the cap at the test scheme `𝟙 Y`, read on `Y` through
the same isomorphism `Y ×_Y Y ≅ Y`. -/
theorem capTarget_eq_chowCohomologyCap {C : ChowSituation.{u}} {G : GysinSystem C}
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : ℤ)
    (c : chowCohomologyComponent C G sY p) (m : ℤ) (β : chowGroup C sY m) :
    c.capTarget C G sY sY (𝟙 Y) (Category.id_comp sY) p m β =
      chowCohomologyCap C G sY p c m β := by
  have h : (pullbackIdIso (𝟙 Y)).inv = pullback.fst (𝟙 Y) (𝟙 Y) := by
    rw [← cancel_epi (pullbackIdIso (𝟙 Y)).hom, Iso.hom_inv_id, pullbackIdIso_hom_fst]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ h _ _ _ _

/-- **`[X ×_k Y] = [X] × [Y]`** for `X` and `Y` of constant dimensions `d` and `e` over `k`. -/
theorem chowExteriorProduct_fundamentalChowClass {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [Flat sX]
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY] [Flat sY] {d e : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) :
    chowExteriorProduct (fieldChowSituation k)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) sX sY d e
        (fundamentalChowClass (fieldChowSituation k) sX d ⊗ₜ[ℤ]
          fundamentalChowClass (fieldChowSituation k) sY e) =
      fundamentalChowClass (fieldChowSituation k) (pullback.fst sX sY ≫ sX) ((d : ℤ) + e) := by
  rw [fundamentalChowClass, fundamentalChowClass, fundamentalChowClass]
  change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  rw [fundamentalCycle, fundamentalCycle, fundamentalCycle,
    Intersection.exteriorProduct_cycleAssociatedToClosedSubscheme k sX sY (𝟙 X) (𝟙 Y) sX sY
      (Category.id_comp sX) (Category.id_comp sY)
      (Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k sX d hX)
      (schemeDeltaDimension_le_of_relativeDimension sY hY)]
  congr 2
  exact pullback.map_id

/-- A bivariant class caps heterogeneously equal classes in equal degrees to heterogeneously equal
classes. -/
theorem BivariantClass.cap_heq_of_heq_degree {C : ChowSituation.{u}} {G : GysinSystem C}
    {A B : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S}
    [LocallyOfFiniteType sB] {v : A ⟶ B} [LocallyOfFiniteType v] {hv : v ≫ sB = sA} {p : ℤ}
    (c : BivariantClass C G sA sB v hv p) {T : Scheme.{u}} (t : T ⟶ B) [LocallyOfFiniteType t]
    {m m' : ℤ} (h : m = m') {x : chowGroup C (t ≫ sB) m} {x' : chowGroup C (t ≫ sB) m'}
    (hx : x ≍ x') : c.cap t m x ≍ c.cap t m' x' := by
  subst h
  obtain rfl := eq_of_heq hx
  rfl

/-- Flat pullback carries heterogeneously equal classes in equal degrees to heterogeneously equal
classes. -/
theorem flatPullbackChow_heq_of_heq {C : ChowSituation.{u}} {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) {m m' : ℤ} (h : m = m')
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX' sX f hbase r hf m)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sX' sX f hbase r hf m')
    {x : chowGroup C sX m} {x' : chowGroup C sX m'} (hx : x ≍ x') :
    flatPullbackChow C sX' sX f hbase r hf m hfac x ≍
      flatPullbackChow C sX' sX f hbase r hf m' hfac' x' := by
  subst h
  obtain rfl := eq_of_heq hx
  rfl

/-- Every class of `CH_a(W)` is `c ∩ [W]` for some `c ∈ A^{N-a}(W)`, `W` smooth of dimension `N`. -/
private theorem exists_chowCohomologyCapFundamentalClass_heq {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW] {N : ℕ}
    (hN : RelativeDimension sW N) {a : ℤ} (α : chowGroup (fieldChowSituation k) sW a) :
    ∃ c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sW ((N : ℤ) - a),
      chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sW N
        ((N : ℤ) - a) c ≍ α := by
  obtain ⟨c, hc⟩ := Stacks.WeilCohomology.capFundamentalClassSurjective k sW N hN ((N : ℤ) - a)
    (chowGroupDegreeEquiv (fieldChowSituation k) sW (by ring : a = (N : ℤ) - ((N : ℤ) - a)) α)
  exact ⟨c, (heq_of_eq hc).trans (chowGroupDegreeEquiv_heq _ _ _ _)⟩

/-- The exterior product of pure tensors of heterogeneously equal classes in equal degrees is
heterogeneously equal. -/
private theorem chowExteriorProduct_tmul_heq {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY] {a a' b b' : ℤ}
    (ha : a = a') (hb : b = b') {x : chowGroup (fieldChowSituation k) sX a}
    {x' : chowGroup (fieldChowSituation k) sX a'} (hx : x ≍ x')
    {y : chowGroup (fieldChowSituation k) sY b} {y' : chowGroup (fieldChowSituation k) sY b'}
    (hy : y ≍ y') :
    chowExteriorProduct (fieldChowSituation k)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) sX sY a b (x ⊗ₜ[ℤ] y) ≍
      chowExteriorProduct (fieldChowSituation k)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) sX sY a' b'
        (x' ⊗ₜ[ℤ] y') := by
  subst ha hb
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rfl

section Product

variable {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
  [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY] [Smooth sY]
  {d e : ℕ} (hX : RelativeDimension sX d) (hY : RelativeDimension sY e)

include hX in
/-- **`p₁^*α = α × [Y]`**: flat pullback along the first projection `X ×_k Y ⟶ X` is the exterior
product with the fundamental class of `Y`, for `X` and `Y` smooth over `k` of constant dimensions
`d` and `e`. -/
theorem flatPullbackChow_fst_eq_chowExteriorProduct (a : ℤ)
    (α : chowGroup (fieldChowSituation k) sX a) :
    flatPullbackChow (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl
        e (Stacks.WeilCohomology.relativeDimension_fst k sX sY hY) a
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α =
      chowExteriorProduct (fieldChowSituation k)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) sX sY a e
        (α ⊗ₜ[ℤ] fundamentalChowClass (fieldChowSituation k) sY e) := by
  have hgys : (fieldGysinSystem k).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso (fieldChowSituation k)
  obtain ⟨c, hα⟩ := exists_chowCohomologyCapFundamentalClass_heq sX hX α
  -- the left-hand side is `res₁(c) ∩ [X ×_k Y]`
  have hL := flatPullbackChow_chowCohomologyCapFundamentalClass' sX (pullback.fst sX sY ≫ sX)
    (pullback.fst sX sY) rfl (Stacks.WeilCohomology.relativeDimension_fst k sX sY hY) hX
    ((d : ℤ) - a) c
  rw [← chowCohomologyCap_fundamentalChowClass (sX := pullback.fst sX sY ≫ sX),
    chowCohomologyCap_restrictionOfEq (fieldChowSituation k) (fieldGysinSystem k) hgys sX
      (pullback.fst sX sY ≫ sX)] at hL
  -- the right-hand side is `c ∩ ([X] × [Y])`, by Stacks 0FBY in the first variable
  have hR := chowExteriorProduct_capTarget_eq_capExteriorProductFst_of_field k sY sX sX (𝟙 X)
    (Category.id_comp sX) ((d : ℤ) - a) c d e (fundamentalChowClass (fieldChowSituation k) sX d)
    (fundamentalChowClass (fieldChowSituation k) sY e)
  rw [capTarget_eq_chowCohomologyCap, chowCohomologyCap_fundamentalChowClass] at hR
  unfold capExteriorProductFst at hR
  rw [chowExteriorProduct_fundamentalChowClass sX sY hX hY] at hR
  have hαR := chowExteriorProduct_tmul_heq sX sY (by ring) rfl hα.symm
    (HEq.refl (fundamentalChowClass (fieldChowSituation k) sY e))
  refine eq_of_heq (HEq.trans (flatPullbackChow_heq_of_heq _ _ _ _ _ _ (by ring) _ _ hα.symm)
    (hL.trans (HEq.trans ?_ ((heq_of_eq hR.symm).trans hαR.symm))))
  have hiso : (identityBaseChangeIso (pullback.fst sX sY)).hom =
      (exteriorCapFstIso sY sX (𝟙 X) (Category.id_comp sX)).hom := by
    refine pullback.hom_ext ?_ ?_
    · simp [← pullback.condition]
    · simp
  refine HEq.trans
    (heq_of_eq (chowPushforwardOfIso_congr_apply (fieldChowSituation k) _ _ _ _ hiso _
      (exteriorCapFstIso_hom_comp_structureMorphism sY sX (𝟙 X) (Category.id_comp sX)) _ _))
    (chowPushforwardOfIso_heq_congr (fieldChowSituation k) _ _ _ _ (by push_cast; ring) _ _ ?_)
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm
  exact BivariantClass.cap_heq_of_heq_degree c _ (by push_cast; ring)
    ((chowGroupCongr_heq _ _ _ _).trans (fundamentalChowClass_heq _ _ (by push_cast; ring)))

include hX hY in
/-- **Remark 0FHD, the omitted identity: `α × β = p₁^*α · p₂^*β`.** For `X` and `Y` smooth over
`k` of constant dimensions `d` and `e`, `α ∈ CH_a(X)` and `β ∈ CH_b(Y)`, the exterior product
`α × β ∈ CH_{a+b}(X ×_k Y)` is the intersection product, formed with the canonical Gysin class of
the diagonal of `X ×_k Y`, of the flat pullbacks `p₁^*α ∈ CH_{a+e}` and `p₂^*β ∈ CH_{b+d}`. -/
theorem selfIntersectionProduct_flatPullbackChow_fst_snd (a b : ℤ)
    (α : chowGroup (fieldChowSituation k) sX a) (β : chowGroup (fieldChowSituation k) sY b) :
    selfIntersectionProduct (fieldChowSituation k)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) (pullback.fst sX sY ≫ sX) ((e + d : ℕ) : ℤ)
        (Stacks.WeilCohomology.canonicalDiagonalClassFamily k (pullback.fst sX sY ≫ sX) (e + d)
          (Stacks.WeilCohomology.relativeDimension_prodBase k sX sY hX hY)) (a + e) (b + d)
        (flatPullbackChow (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY)
          rfl e (Stacks.WeilCohomology.relativeDimension_fst k sX sY hY) a
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α)
        (flatPullbackChow (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
          pullback.condition.symm d (Stacks.WeilCohomology.relativeDimension_snd k sX sY hX) b
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β) ≍
      chowExteriorProduct (fieldChowSituation k)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) sX sY a b
        (α ⊗ₜ[ℤ] β) := by
  have hgys : (fieldGysinSystem k).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso (fieldChowSituation k)
  have hW := Stacks.WeilCohomology.relativeDimension_prodBase k sX sY hX hY
  have hp₂ := Stacks.WeilCohomology.relativeDimension_snd k sX sY hX
  obtain ⟨c, hβ⟩ := exists_chowCohomologyCapFundamentalClass_heq sY hY β
  set r := chowCohomologyRestrictionOfEq (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sY
    pullback.condition.symm (fieldGysinSystem k) hgys ((e : ℤ) - b) c with hr
  -- `p₂^*β = res₂(c) ∩ [X ×_k Y]`
  have hpβ := flatPullbackChow_chowCohomologyCapFundamentalClass' sY (pullback.fst sX sY ≫ sX)
    (pullback.snd sX sY) pullback.condition.symm hp₂ hY ((e : ℤ) - b) c
  have hpβ' : flatPullbackChow (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sY
      (pullback.snd sX sY) pullback.condition.symm d hp₂ b
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β ≍
      chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k)
        (pullback.fst sX sY ≫ sX) ((e + d : ℕ) : ℤ) ((e : ℤ) - b) r :=
    (flatPullbackChow_heq_of_heq _ _ _ _ _ _ (by ring) _ _ hβ.symm).trans
      (hpβ.trans (chowCohomologyCapFundamentalClass_heq_of_eq _ (by push_cast; ring) _ _))
  -- `p₁^*α · p₂^*β = res₂(c) ∩ p₁^*α`
  have hprod := Stacks.WeilCohomology.canonicalDiagonalClassFamily_capEqProduct k
    (pullback.fst sX sY ≫ sX) (e + d) hW ((e : ℤ) - b) r (a + e)
    (flatPullbackChow (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY)
      rfl e (Stacks.WeilCohomology.relativeDimension_fst k sX sY hY) a
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α)
  rw [Stacks.WeilCohomology.canonicalDiagonalClassFamily_isSymmetric k]
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans ?_
  refine (Stacks.WeilCohomology.selfIntersectionProduct_heq_of_heq _ _ _ (by push_cast; ring) rfl
    hpβ' HEq.rfl).trans ?_
  refine (chowGroupDegreeEquiv_heq _ _ _ _).symm.trans ((heq_of_eq hprod).symm.trans ?_)
  -- `res₂(c) ∩ (α × [Y]) = α × (c ∩ [Y]) = α × β`
  rw [flatPullbackChow_fst_eq_chowExteriorProduct sX sY hX hY,
    chowCohomologyCap_restrictionOfEq (fieldChowSituation k) (fieldGysinSystem k) hgys]
  have hR := commutesExteriorProductCapAt_of_field k sX sY sY (𝟙 Y) (Category.id_comp sY)
    ((e : ℤ) - b) c a e α (fundamentalChowClass (fieldChowSituation k) sY e)
  unfold exteriorProductCap capExteriorProduct exteriorProductOnTarget at hR
  rw [capTarget_eq_chowCohomologyCap, chowCohomologyCap_fundamentalChowClass] at hR
  have hext := chowExteriorProduct_tmul_heq sX sY rfl (by ring) (HEq.refl α) hβ
  refine HEq.trans ?_ ((heq_of_eq hR).symm.trans hext)
  have hiso : (identityBaseChangeIso (pullback.snd sX sY)).hom =
      (exteriorCapIso sX sY (𝟙 Y) (Category.id_comp sY)).hom := by
    refine pullback.hom_ext ?_ ?_
    · simp
    · simp [← pullback.condition]
  refine HEq.trans
    (heq_of_eq (chowPushforwardOfIso_congr_apply (fieldChowSituation k) _ _ _ _ hiso _
      (exteriorCapIso_hom_comp_structureMorphism sX sY (𝟙 Y) (Category.id_comp sY)) _ _))
    (chowPushforwardOfIso_heq_congr (fieldChowSituation k) _ _ _ _ (by ring) _ _ ?_)
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm
  exact BivariantClass.cap_heq_of_heq_degree c _ (by ring)
    ((chowGroupCongr_heq _ _ _ _).trans (chowGroupCongr_heq _ _ _ _).symm)

end Product

end Stacks.Chow

end
