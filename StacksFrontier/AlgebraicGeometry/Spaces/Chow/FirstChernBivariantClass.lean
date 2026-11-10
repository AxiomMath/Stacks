module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackSquareCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RelativeDimensionIso

/-!
# The first Chern class as a bivariant class

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module. Stacks 0ERM
asserts that `c₁(f^*ℒ) ∩ -` is a bivariant class of degree `1`. This module constructs the cap
operation `c₁ ∩ - : CH_k(Y') ⟶ CH_{k-1}(X')` on every good test space `g : Y' ⟶ X` and proves its
three compatibilities, the fields of Stacks 0ERJ at `f = 𝟙 X` and `p = 1`.

## Main definitions

* `AlgebraicGeometry.Space.firstChernBivariantCap`: the cap operation of Stacks 0ERM on a test
  space.
* `AlgebraicGeometry.Space.firstChernBivariantClass`: **Stacks 0ERM**, `c₁(f^*ℒ) ∩ -` as a
  bivariant class of degree `1` over the constructed Chow groups
  (`AlgebraicGeometry.Space.BivariantClassCanonical`).

## Main results

* `AlgebraicGeometry.Space.firstChernBivariantCap_proper_naturality`,
  `AlgebraicGeometry.Space.firstChernBivariantCap_flat_naturality` and
  `AlgebraicGeometry.Space.firstChernBivariantCap_gysin_naturality`: the fields (1), (2) and (3)
  of Stacks 0ERJ for the cap operation, at `f = 𝟙 X` and `p = 1`.

## References

* [Stacks Project, Tag 0ERM](https://stacks.math.columbia.edu/tag/0ERM)
* [Stacks Project, Tag 0ERB](https://stacks.math.columbia.edu/tag/0ERB)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The cap operation of Stacks 0ERM and proper pushforward -/

section Cap

open CategoryTheory.Limits

variable (D : BaseSpaceDimensionSituation.{u})

/-- Transporting a class along an equality of degrees is transporting a representative. -/
private theorem chowGroupCanonicalDegreeCongr_chowClassCanonical {Y : D.Ambient}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {k l : ℤ} (h : k = l) (x : CycleGroup D sY k) :
    chowGroupCanonicalDegreeCongr D sY hY h (chowClassCanonical.{u + 1} D sY hY k x) =
      chowClassCanonical.{u + 1} D sY hY l (cycleGroupDegreeCongr D sY h x) := by
  subst h
  rfl

/-- Proper pushforward commutes with the transport along an equality of degrees. -/
private theorem properCyclePushforward_cycleGroupDegreeCongr {Y Z : D.Ambient} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) {q : Y ⟶ Z} (hqB : q ≫ sZ = sY)
    (hq : IsQuasiCompact D.site D.base D.base_mem q) {k l : ℤ} (h : k = l)
    (x : CycleGroup D sY k) :
    properCyclePushforward D sY hY sZ hZ hqB hq l (cycleGroupDegreeCongr D sY h x) =
      cycleGroupDegreeCongr D sZ h (properCyclePushforward D sY hY sZ hZ hqB hq k x) := by
  subst h
  rfl

/-- Flat pullback commutes with the transport along equalities of degrees. -/
private theorem flatPullbackMap_cycleGroupDegreeCongr {Y Z : D.Ambient} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (q : Y ⟶ Z) (hqB : q ≫ sZ = sY)
    (r : ℕ) (hq : IsFlat D.site D.base D.base_mem q)
    (hr : HasRelativeDimension r D.site D.base D.base_mem q) {m m' n n' : ℤ} (hm : m = m')
    (hn : n = n') (hmn : m + (r : ℤ) = n) (hmn' : m' + (r : ℤ) = n') (x : CycleGroup D sZ m) :
    cycleGroupDegreeCongr D sY hn (flatPullbackMap D sY hY sZ hZ q hqB r hq hr m n hmn x) =
      flatPullbackMap D sY hY sZ hZ q hqB r hq hr m' n' hmn' (cycleGroupDegreeCongr D sZ hm x) := by
  subst hm hn
  rfl

/-- Flat pullback of cycles along the identity is the identity. -/
private theorem flatPullbackMap_id {Y : D.Ambient} (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hfl : IsFlat D.site D.base D.base_mem (𝟙 Y))
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem (𝟙 Y)) (k : ℤ)
    (hkk : k + ((0 : ℕ) : ℤ) = k) (α : CycleGroup D sY k) :
    flatPullbackMap D sY hY sY hY (𝟙 Y) (Category.id_comp sY) 0 hfl hr k k hkk α = α := by
  have hmult : ∀ W T : IntegralClosedSubspace D.site D.base D.base_mem Y,
      flatPullbackMult D sY hY sY hY (𝟙 Y) (Category.id_comp sY) 0 hfl hr W T =
        integralCycleCoeff D W T := fun W T => by
    change cycleCoeffOfClosedSubspace D sY hY (W.subspace.preimage (𝟙 Y)) _ _
      (canonicalGeometricPoint D.site D.base D.base_mem _) T = _
    rw [cycleCoeffOfClosedSubspace_eq_of_subfunctor_eq D sY hY _ _ W.isClosedSubspace
        (Subfunctor.preimage_id _),
      cycleCoeffOfClosedSubspace_integralClosedSubspace D sY hY W _ (by simp)]
  refine Subtype.ext (funext fun T => ?_)
  rw [flatPullbackMap_apply, finsum_eq_single _ T fun W hW => by
      rw [hmult, integralCycleCoeff, ite_eq_right (Ne.symm hW), mul_zero],
    hmult, integralCycleCoeff, ite_eq_left rfl, mul_one]

/-- **Stacks 0EQR at a representative, into an arbitrary degree.**  The form of
`AlgebraicGeometry.Space.chowClassCanonical_flatPullbackMap_firstChernCapCycleMap` whose target
degree `n` is only propositionally `k + r`. -/
private theorem chowClassCanonical_flatPullbackMap_firstChernCapCycleMap_of_eq {Y Z : D.Ambient}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (q : Y ⟶ Z)
    (hqB : q ≫ sZ = sY) (r : ℕ) (hq : IsFlat D.site D.base D.base_mem q)
    (hr : HasRelativeDimension r D.site D.base D.base_mem q)
    (M : Modules.{u, u} D.site D.base D.base_mem Z hZ.1)
    (hM : IsInvertibleModule (⟨Z, hZ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M) (k n : ℤ)
    (hkn : k + (r : ℤ) = n) (hkn' : k + 1 + (r : ℤ) = n + 1) (x : CycleGroup D sZ (k + 1)) :
    chowClassCanonical.{u + 1} D sY hY n
        (flatPullbackMap D sY hY sZ hZ q hqB r hq hr k n hkn
          (firstChernCapCycleMap D sZ hZ k (canonicalFirstChernRule D sZ hZ M hM k) x)) =
      canonicalFirstChernCapCanonical.{u + 1} D sY hY
        ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk q : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨Z, hZ.1⟩)).obj M)
        (modulePullbackInvertible
          (ObjectProperty.homMk q : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨Z, hZ.1⟩) M hM) n
        (flatPullbackMap D sY hY sZ hZ q hqB r hq hr (k + 1) (n + 1) hkn' x) := by
  subst hkn
  exact chowClassCanonical_flatPullbackMap_firstChernCapCycleMap D sY hY sZ hZ q hqB r hq hr M hM
    k x

variable {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)

/-- The identification `Y' ≅ X' = X ×_X Y'` of a test space `g : Y' ⟶ X` with its base change
along `𝟙 X`, the inverse of the second projection. -/
def firstChernBivariantTestIso {Y' : D.Ambient} (g : Y' ⟶ X) : Y' ≅ pullback (𝟙 X) g :=
  (asIso (pullback.snd (𝟙 X) g)).symm

/-- The identification `Y' ≅ X'` is one over the base. -/
theorem firstChernBivariantTestIso_hom_comp {Y' : D.Ambient} (g : Y' ⟶ X) :
    (firstChernBivariantTestIso D g).hom ≫ (pullback.fst (𝟙 X) g ≫ sX) = g ≫ sX := by
  rw [← Category.assoc, ← Category.comp_id (pullback.fst (𝟙 X) g), pullback.condition]
  simp [firstChernBivariantTestIso]

/-- The projection `X' = X ×_X Y' ⟶ X`, as a morphism of algebraic spaces. -/
abbrev firstChernBivariantFst {Y' : D.Ambient} (g : Y' ⟶ X)
    (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) :
    (⟨pullback (𝟙 X) g, hX'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩ :=
  ObjectProperty.homMk (pullback.fst (𝟙 X) g)

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The cap operation of Stacks 0ERM** on a good test space `g : Y' ⟶ X`:
`c₁(g^*ℒ) ∩ - : CH_k(Y') ⟶ CH_{k-1}(X')`, `X' = X ×_X Y'`.  It is the pushforward along the
isomorphism `Y' ≅ X'` (Stacks 0EQC), followed by the cap product with the first Chern class of
the inverse image of `ℒ` to `X'` (Stacks 0EQY), the Chow groups being those of Stacks 0EQ6 at the
canonical embeddings of Stacks 0ENK. -/
def firstChernBivariantCap {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX))
    (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ) :
    chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k →+
      chowGroupCanonical.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX' (k - 1) :=
  (canonicalFirstChernCapCanonicalChowMap D (pullback.fst (𝟙 X) g ≫ sX) hX' (k - 1)
      ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L)
      (modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL)).comp
    ((chowGroupCanonicalDegreeCongr D _ hX' (Int.sub_add_cancel k 1).symm).toAddMonoidHom.comp
      (chowGroupCanonicalProperPushforward.{u + 1} D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX)
        hX' (firstChernBivariantTestIso_hom_comp D sX g)
        (isProper_of_isIso D.site D.base D.base_mem (firstChernBivariantTestIso D g).hom) k))

/-- The cap operation of Stacks 0ERM on the class of a cycle. -/
private theorem firstChernBivariantCap_chowClassCanonical {Y' : D.Ambient} (g : Y' ⟶ X)
    (hY' : D.IsGood (g ≫ sX)) (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ)
    (α : CycleGroup D (g ≫ sX) k) :
    firstChernBivariantCap D sX hX L hL g hY' hX' k (chowClassCanonical.{u + 1} D _ hY' k α) =
      canonicalFirstChernCapCanonical.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX'
        ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L)
        (modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL) (k - 1)
        (cycleGroupDegreeCongr D _ (Int.sub_add_cancel k 1).symm
          (properCyclePushforward D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
            (firstChernBivariantTestIso_hom_comp D sX g)
            (isProper_of_isIso D.site D.base D.base_mem
              (firstChernBivariantTestIso D g).hom).2.1.2 k α)) := by
  rw [firstChernBivariantCap, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    chowGroupCanonicalProperPushforward_chowClassCanonical, AddEquiv.coe_toAddMonoidHom,
    chowGroupCanonicalDegreeCongr_chowClassCanonical]
  rfl

/-- A base change square of test spaces gives a pullback square of the identifications
`Y' ≅ X'`. -/
private theorem isPullback_firstChernBivariantTestIso {Y' Y'' : D.Ambient} (g : Y' ⟶ X)
    (h : Y'' ⟶ Y') (h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g)
    (sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g)) :
    IsPullback h (firstChernBivariantTestIso D (h ≫ g)).hom
      (firstChernBivariantTestIso D g).hom h' := by
  refine IsPullback.of_vert_isIso ⟨?_⟩
  have hw : (firstChernBivariantTestIso D (h ≫ g)).inv ≫ h =
      h' ≫ (firstChernBivariantTestIso D g).inv := sq.w
  rw [← Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The cap product with the first Chern class of the inverse image of `ℒ` to `X''` is the one
with the inverse image along `q : X'' ⟶ X'` of the inverse image of `ℒ` to `X'`. -/
private theorem chowClassCanonical_firstChernCapCycleMap_modulePullback_firstChernBivariantFst
    {Y' Y'' : D.Ambient} (g : Y' ⟶ X) (g' : Y'' ⟶ X) (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (hX'' : D.IsGood (pullback.fst (𝟙 X) g' ≫ sX))
    (q : (⟨pullback (𝟙 X) g', hX''.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨pullback (𝟙 X) g, hX'.1⟩)
    (hq : q ≫ firstChernBivariantFst D sX hX g hX' = firstChernBivariantFst D sX hX g' hX'')
    (k : ℤ) (z : CycleGroup D (pullback.fst (𝟙 X) g' ≫ sX) (k + 1)) :
    chowClassCanonical.{u + 1} D _ hX'' k
        (firstChernCapCycleMap D _ hX'' k (canonicalFirstChernRule D _ hX''
          ((modulePullback D.site D.base D.base_mem q).obj
            ((modulePullback D.site D.base D.base_mem
              (firstChernBivariantFst D sX hX g hX')).obj L))
          (modulePullbackInvertible q _
            (modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL)) k) z) =
      chowClassCanonical.{u + 1} D _ hX'' k
        (firstChernCapCycleMap D _ hX'' k (canonicalFirstChernRule D _ hX''
          ((modulePullback D.site D.base D.base_mem
            (firstChernBivariantFst D sX hX g' hX'')).obj L)
          (modulePullbackInvertible (firstChernBivariantFst D sX hX g' hX'') L hL) k) z) :=
  canonicalFirstChernCapCanonical_congr_iso hX'' _ _ _ _
    ((modulePullbackCompIso D.site D.base D.base_mem q
      (firstChernBivariantFst D sX hX g hX')).app L ≪≫ eqToIso (by rw [hq])) k z

/-- **Stacks 0ERJ (1) for the cap operation of Stacks 0ERM: compatibility with proper
pushforward.**  For good test spaces `Y'' --h--> Y' --g--> X` with `h` proper, and
`h' : X'' ⟶ X'` the induced proper morphism of base changes, there is a cycle `β` representing
`c₁ ∩ [α]` on `X''` such that `c₁ ∩ [h_*α] = [h'_*β]` on `X'`.  This is the shape of the field
`proper_naturality` of Stacks 0ERJ, at `f = 𝟙 X` and `p = 1`. -/
theorem firstChernBivariantCap_proper_naturality {Y' Y'' : D.Ambient} (g : Y' ⟶ X)
    (hY' : D.IsGood (g ≫ sX)) (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (h : Y'' ⟶ Y')
    (hY'' : D.IsGood ((h ≫ g) ≫ sX)) (hX'' : D.IsGood (pullback.fst (𝟙 X) (h ≫ g) ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g)
    (sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g))
    (hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g))
    (hh' : IsProper D.site D.base D.base_mem h') (k : ℤ) (α : CycleGroup D ((h ≫ g) ≫ sX) k) :
    ∃ β : CycleGroup D (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (k - 1),
      firstChernBivariantCap D sX hX L hL (h ≫ g) hY'' hX'' k
          (chowClassCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY'' k α) =
        chowClassCanonical.{u + 1} D (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) hX'' (k - 1) β ∧
      firstChernBivariantCap D sX hX L hL g hY' hX' k
          (chowClassCanonical.{u + 1} D (g ≫ sX) hY' k
            (properCyclePushforward D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY'
              (Category.assoc h g sX).symm hh.2.1.2 k α)) =
        chowClassCanonical.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX' (k - 1)
          (properCyclePushforward D (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) hX''
            (pullback.fst (𝟙 X) g ≫ sX) hX' (by rw [← Category.assoc, hfst]) hh'.2.1.2 (k - 1)
            β) := by
  have he' := isProper_of_isIso D.site D.base D.base_mem (firstChernBivariantTestIso D g).hom
  have he'' := isProper_of_isIso D.site D.base D.base_mem
    (firstChernBivariantTestIso D (h ≫ g)).hom
  have hhB : h' ≫ pullback.fst (𝟙 X) g ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX := by
    rw [← Category.assoc, hfst]
  set z := cycleGroupDegreeCongr D _ (Int.sub_add_cancel k 1).symm
    (properCyclePushforward D ((h ≫ g) ≫ sX) hY'' (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) hX''
      (firstChernBivariantTestIso_hom_comp D sX (h ≫ g)) he''.2.1.2 k α) with hz
  refine ⟨firstChernCapCycleMap D _ hX'' (k - 1) (canonicalFirstChernRule D _ hX''
      ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX (h ≫ g) hX'')).obj
        L) (modulePullbackInvertible (firstChernBivariantFst D sX hX (h ≫ g) hX'') L hL) (k - 1))
      z, ?_, ?_⟩
  · rw [firstChernBivariantCap_chowClassCanonical, canonicalFirstChernCapCanonical,
      AddMonoidHom.comp_apply]
  rw [firstChernBivariantCap_chowClassCanonical]
  have hsq := (isPullback_firstChernBivariantTestIso D g h h' sq).w
  have hcomm : properCyclePushforward D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
        (firstChernBivariantTestIso_hom_comp D sX g) he'.2.1.2 k
        (properCyclePushforward D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY'
          (Category.assoc h g sX).symm hh.2.1.2 k α) =
      properCyclePushforward D (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) hX''
        (pullback.fst (𝟙 X) g ≫ sX) hX' hhB hh'.2.1.2 k
        (properCyclePushforward D ((h ≫ g) ≫ sX) hY'' (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) hX''
          (firstChernBivariantTestIso_hom_comp D sX (h ≫ g)) he''.2.1.2 k α) := by
    rw [properCyclePushforward_comp D _ _ _ hY'' hY' hX' (Category.assoc h g sX).symm
        (firstChernBivariantTestIso_hom_comp D sX g) hh he',
      properCyclePushforward_comp D _ _ _ hY'' hX'' hX'
        (firstChernBivariantTestIso_hom_comp D sX (h ≫ g)) hhB he'' hh']
    exact properCyclePushforward_congr D _ hY'' _ hX' hsq _ _ _ _ k α
  rw [hcomm, ← properCyclePushforward_cycleGroupDegreeCongr, ← hz]
  let q : (⟨pullback (𝟙 X) (h ≫ g), hX''.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨pullback (𝟙 X) g, hX'.1⟩ := ObjectProperty.homMk h'
  have hq : IsProper D.site D.base D.base_mem q.hom := hh'
  rw [← chowClassCanonical_properPushforward_canonicalFirstChernCap_of_component D hX'' hX'
    q hhB hq
    ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L)
    (modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL) (k - 1)
    (fun β hβ => isRationallyEquivalentToZeroCanonical_properCyclePushforward D _ hX'' _ hX' hhB
      hq (k - 1) β hβ) z,
    ← chowGroupCanonicalProperPushforward_chowClassCanonical D _ hX'' _ hX' hhB hq,
    ← chowGroupCanonicalProperPushforward_chowClassCanonical D _ hX'' _ hX' hhB hq,
    chowClassCanonical_firstChernCapCycleMap_modulePullback_firstChernBivariantFst D sX hX L hL g
      (h ≫ g) hX' hX'' q (ObjectProperty.hom_ext _ hfst)]

/-- **Stacks 0ERJ (2) for the cap operation of Stacks 0ERM: compatibility with flat pullback.**
For good test spaces `Y'' --h--> Y' --g--> X` with `h` flat of relative dimension `r`, and
`h' : X'' ⟶ X'` the induced flat morphism of base changes, there is a cycle `β` representing
`c₁ ∩ [α]` on `X'` such that `c₁ ∩ [h^*α] = [h'^*β]` on `X''`.  This is the shape of the field
`flat_naturality` of Stacks 0ERJ, at `f = 𝟙 X` and `p = 1`. -/
theorem firstChernBivariantCap_flat_naturality {Y' Y'' : D.Ambient} (g : Y' ⟶ X)
    (hY' : D.IsGood (g ≫ sX)) (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (h : Y'' ⟶ Y')
    (hY'' : D.IsGood ((h ≫ g) ≫ sX)) (hX'' : D.IsGood (pullback.fst (𝟙 X) (h ≫ g) ≫ sX))
    (hh : IsFlat D.site D.base D.base_mem h) (r : ℕ)
    (hr : HasRelativeDimension r D.site D.base D.base_mem h)
    (h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g)
    (sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g))
    (hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g))
    (hh' : IsFlat D.site D.base D.base_mem h')
    (hr' : HasRelativeDimension r D.site D.base D.base_mem h') (k : ℤ)
    (α : CycleGroup D (g ≫ sX) k) :
    ∃ β : CycleGroup D (pullback.fst (𝟙 X) g ≫ sX) (k - 1),
      firstChernBivariantCap D sX hX L hL g hY' hX' k
          (chowClassCanonical.{u + 1} D (g ≫ sX) hY' k α) =
        chowClassCanonical.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX' (k - 1) β ∧
      firstChernBivariantCap D sX hX L hL (h ≫ g) hY'' hX'' (k + (r : ℤ))
          (chowClassCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY'' (k + (r : ℤ))
            (flatPullbackMap D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY' h
              (Category.assoc h g sX).symm r hh hr k (k + (r : ℤ)) rfl α)) =
        chowClassCanonical.{u + 1} D (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) hX''
          (k + (r : ℤ) - 1)
          (flatPullbackMap D (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) hX''
            (pullback.fst (𝟙 X) g ≫ sX) hX' h' (by rw [← Category.assoc, hfst]) r hh' hr'
            (k - 1) (k + (r : ℤ) - 1) (by omega) β) := by
  have he' := isProper_of_isIso D.site D.base D.base_mem (firstChernBivariantTestIso D g).hom
  have hhB : h' ≫ pullback.fst (𝟙 X) g ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX := by
    rw [← Category.assoc, hfst]
  set x := cycleGroupDegreeCongr D _ (Int.sub_add_cancel k 1).symm
    (properCyclePushforward D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
      (firstChernBivariantTestIso_hom_comp D sX g) he'.2.1.2 k α) with hx
  refine ⟨firstChernCapCycleMap D _ hX' (k - 1) (canonicalFirstChernRule D _ hX'
      ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L)
      (modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL) (k - 1)) x, ?_, ?_⟩
  · rw [firstChernBivariantCap_chowClassCanonical, canonicalFirstChernCapCanonical,
      AddMonoidHom.comp_apply]
  rw [firstChernBivariantCap_chowClassCanonical]
  have hpb := isPullback_firstChernBivariantTestIso D g h h' sq
  have h0EPD := flatPullback_properPushforward_unconditional D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY'
    (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) hX'' (pullback.fst (𝟙 X) g ≫ sX) hX'
    (Category.assoc h g sX).symm (firstChernBivariantTestIso_hom_comp D sX (h ≫ g))
    (firstChernBivariantTestIso_hom_comp D sX g) hhB r hh' hr' hpb he' k (k + (r : ℤ)) rfl α
  rw [← h0EPD, flatPullbackMap_cycleGroupDegreeCongr D _ hX'' _ hX' h' hhB r hh' hr'
      (Int.sub_add_cancel k 1).symm (by omega : k + (r : ℤ) = k + (r : ℤ) - 1 + 1) rfl (by omega),
    ← hx, chowClassCanonical_flatPullbackMap_firstChernCapCycleMap_of_eq D _ hX'' _ hX' h' hhB r
      hh' hr' _ _ (k - 1) (k + (r : ℤ) - 1) (by omega) (by omega) x]
  exact (chowClassCanonical_firstChernCapCycleMap_modulePullback_firstChernBivariantFst D sX hX L
    hL g (h ≫ g) hX' hX'' (ObjectProperty.homMk h') (ObjectProperty.hom_ext _ hfst)
    (k + (r : ℤ) - 1) _).symm

end Cap

/-! ### The cap operation of Stacks 0ERM and the refined Gysin maps -/

section GysinNaturality

open CategoryTheory.Limits

variable (D : BaseSpaceDimensionSituation.{u})

/-- Two transports along equalities of degrees compose to the transport along the composite. -/
private theorem cycleGroupDegreeCongr_cycleGroupDegreeCongr {Y : D.Ambient} (sY : Y ⟶ D.space)
    {a b c : ℤ} (h₁ : a = b) (h₂ : b = c) (x : CycleGroup D sY a) :
    cycleGroupDegreeCongr D sY h₂ (cycleGroupDegreeCongr D sY h₁ x) =
      cycleGroupDegreeCongr D sY (h₁.trans h₂) x := by
  subst h₁ h₂
  rfl

/-- The cap product of Stacks 0EQJ at the canonical rule commutes with the transport along an
equality of degrees. -/
private theorem cycleGroupDegreeCongr_firstChernCapCycleMap {Y : D.Ambient} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    {m n : ℤ} (h : m = n) (h₁ : m + 1 = n + 1) (x : CycleGroup D sY (m + 1)) :
    cycleGroupDegreeCongr D sY h
        (firstChernCapCycleMap D sY hY m (canonicalFirstChernRule D sY hY M hM m) x) =
      firstChernCapCycleMap D sY hY n (canonicalFirstChernRule D sY hY M hM n)
        (cycleGroupDegreeCongr D sY h₁ x) := by
  subst h
  rfl

/-- **Stacks 0EQT along a proper `q`, for an inverse image of `ℒ` through `q`.**  Let
`q : P ⟶ Q` be proper over the base, `i : Q ⟶ R` and `f : R ⟶ T` morphisms of algebraic spaces,
`f' : P ⟶ T` with `q ≫ i ≫ f = f'`, and `ℒ` invertible on `T`.  Then for `y ∈ Z_{k+1}(P)`

  `[q_*(c₁(f'^*ℒ) ∩ y)] = c₁(i^*f^*ℒ) ∩ [q_* y]`   in `CH_k(Q)`. -/
private theorem chowClassCanonical_properCyclePushforward_firstChernCapCycleMap_modulePullback
    {P Q : D.Ambient} (sP : P ⟶ D.space) (hP : D.IsGood sP) (sQ : Q ⟶ D.space)
    (hQ : D.IsGood sQ) {R T : AlgebraicSpaces D.site D.base D.base_mem}
    (q : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Q, hQ.1⟩)
    (hqB : q.hom ≫ sQ = sP) (hq : IsProper D.site D.base D.base_mem q.hom)
    (i : (⟨Q, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ R) (f : R ⟶ T)
    (f' : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ T)
    (hcomp : (q ≫ i) ≫ f = f') (L : Modules.{u, u} D.site D.base D.base_mem T.1 T.2)
    (hL : IsInvertibleModule T L) (k : ℤ) (y : CycleGroup D sP (k + 1)) :
    chowClassCanonical.{u + 1} D sQ hQ k
        (properCyclePushforward D sP hP sQ hQ hqB hq.2.1.2 k
          (firstChernCapCycleMap D sP hP k (canonicalFirstChernRule D sP hP
            ((modulePullback D.site D.base D.base_mem f').obj L)
            (modulePullbackInvertible f' L hL) k) y)) =
      canonicalFirstChernCapCanonical.{u + 1} D sQ hQ
        ((modulePullback D.site D.base D.base_mem i).obj
          ((modulePullback D.site D.base D.base_mem f).obj L))
        (modulePullbackInvertible i _ (modulePullbackInvertible f L hL)) k
        (properCyclePushforward D sP hP sQ hQ hqB hq.2.1.2 (k + 1) y) := by
  have e : (modulePullback D.site D.base D.base_mem q).obj
        ((modulePullback D.site D.base D.base_mem i).obj
          ((modulePullback D.site D.base D.base_mem f).obj L)) ≅
      (modulePullback D.site D.base D.base_mem f').obj L :=
    (modulePullbackCompIso D.site D.base D.base_mem q i).app _ ≪≫
      (modulePullbackCompIso D.site D.base D.base_mem (q ≫ i) f).app L ≪≫
      eqToIso (by rw [hcomp])
  have hc := canonicalFirstChernCapCanonical_congr_iso hP _ _
    (modulePullbackInvertible q _ (modulePullbackInvertible i _ (modulePullbackInvertible f L hL)))
    (modulePullbackInvertible f' L hL) e k y
  rw [canonicalFirstChernCapCanonical, canonicalFirstChernCapCanonical, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply] at hc
  rw [← chowClassCanonical_properPushforward_canonicalFirstChernCap_of_component D hP hQ q hqB hq
    _ _ k (fun β hβ => isRationallyEquivalentToZeroCanonical_properCyclePushforward D _ hP _ hQ
      hqB hq k β hβ) y]
  exact congrArg (chowGroupCanonicalProperPushforward.{u + 1} D _ hP _ hQ hqB hq k) hc.symm

variable {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)

/-- The projection `X' = X ×_X Y' ⟶ Y'` is a morphism over the base. -/
private theorem pullbackSnd_id_comp {Y' : D.Ambient} (g : Y' ⟶ X) :
    pullback.snd (𝟙 X) g ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX := by
  rw [← Category.assoc, ← pullback.condition, Category.comp_id]

/-- **Pushing forward along `Y' ≅ X'` is the flat pullback along `X' ⟶ Y'`**, the projection
`X' = X ×_X Y' ⟶ Y'` being an isomorphism, flat of relative dimension `0`. -/
private theorem properCyclePushforward_firstChernBivariantTestIso {Y' : D.Ambient}
    (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (n : ℤ) (x : CycleGroup D (g ≫ sX) n) :
    properCyclePushforward D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
        (firstChernBivariantTestIso_hom_comp D sX g)
        (isProper_of_isIso D.site D.base D.base_mem
          (firstChernBivariantTestIso D g).hom).2.1.2 n x =
      flatPullbackMap D (pullback.fst (𝟙 X) g ≫ sX) hX' (g ≫ sX) hY' (pullback.snd (𝟙 X) g)
        (pullbackSnd_id_comp D sX g) 0
        (isFlat_of_isEtale D.site D.base D.base_mem
          (isEtale_of_isIso D.site D.base D.base_mem (pullback.snd (𝟙 X) g)))
        (hasRelativeDimension_zero_of_isIso D.site D.base D.base_mem (pullback.snd (𝟙 X) g)
          hY'.1) n n (Int.add_zero n) x := by
  have hid := flatPullbackMap_id D (g ≫ sX) hY'
    (isFlat_of_isEtale D.site D.base D.base_mem (isEtale_of_isIso D.site D.base D.base_mem (𝟙 Y')))
    (hasRelativeDimension_zero_of_isIso D.site D.base D.base_mem (𝟙 Y') hY'.1) n (Int.add_zero n) x
  have hab : (firstChernBivariantTestIso D g).hom ≫ pullback.snd (𝟙 X) g = 𝟙 Y' := by
    simp [firstChernBivariantTestIso]
  exact (congrArg _ hid.symm).trans <| properCyclePushforward_flatPullbackMap_of_isIso D (g ≫ sX)
    hY' (pullback.fst (𝟙 X) g ≫ sX) hX' (g ≫ sX) hY' hab (Category.id_comp _)
    (pullbackSnd_id_comp D sX g) (firstChernBivariantTestIso_hom_comp D sX g)
    (isProper_of_isIso D.site D.base D.base_mem (firstChernBivariantTestIso D g).hom).2.1.2 0
    _ _ _ _ n n (Int.add_zero n) x

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX))
    (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (M : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1) (t : M.sections)
    (hM : IsInvertibleSheaf D (g ≫ sX) hY' M)

local notation "𝔻" => vanishingLocus D (g ≫ sX) hY' M t
local notation "h𝔻" => isGood_vanishingLocus D (g ≫ sX) hY' M t
local notation "𝕃'" => pullbackSheaf D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
  (ObjectProperty.homMk (pullback.snd (𝟙 X) g)) M
local notation "𝕤'" => pullbackGlobalSection D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
  (ObjectProperty.homMk (pullback.snd (𝟙 X) g)) M t
local notation "h𝕃'" => isInvertibleSheaf_pullbackSheaf D (g ≫ sX) hY'
  (pullback.fst (𝟙 X) g ≫ sX) hX' (ObjectProperty.homMk (pullback.snd (𝟙 X) g)) M hM
local notation "𝔼'" => vanishingLocus D (pullback.fst (𝟙 X) g ≫ sX) hX'
  (pullbackSheaf D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
    (ObjectProperty.homMk (pullback.snd (𝟙 X) g)) M)
  (pullbackGlobalSection D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
    (ObjectProperty.homMk (pullback.snd (𝟙 X) g)) M t)
local notation "h𝔼'" => isGood_vanishingLocus D (pullback.fst (𝟙 X) g ≫ sX) hX'
  (pullbackSheaf D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
    (ObjectProperty.homMk (pullback.snd (𝟙 X) g)) M)
  (pullbackGlobalSection D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
    (ObjectProperty.homMk (pullback.snd (𝟙 X) g)) M t)

/-- **The pushforward along `X'' ≅ E'` of the pushed-forward Gysin pullback is a flat pullback.**
With `g₀ : E' ⟶ D'` the projection of Stacks 0ER3, `iso_*(e''_* w) = g₀^* w` for every cycle `w`
on `D'`, where `e'' : D' ≅ X''`. -/
private theorem properCyclePushforward_iso_firstChernBivariantTestIso
    (hXd : D.IsGood (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX))
    (iso : pullback (𝟙 X) ((𝔻).1.ι ≫ g) ≅ (𝔼').1.toFunctor)
    (hbase : iso.hom ≫ ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) =
      pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX)
    (hisoProper : IsProper D.site D.base D.base_mem iso.hom)
    (g₀ : (𝔼').1.toFunctor ⟶ (𝔻).1.toFunctor)
    (hab : iso.hom ≫ g₀ = pullback.snd (𝟙 X) ((𝔻).1.ι ≫ g))
    (hg₀B : g₀ ≫ (𝔻).1.ι ≫ g ≫ sX = (𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX)
    (hg₀f : IsFlat D.site D.base D.base_mem g₀)
    (hg₀r : HasRelativeDimension 0 D.site D.base D.base_mem g₀) (k : ℤ)
    (w : CycleGroup D ((𝔻).1.ι ≫ g ≫ sX) k) :
    properCyclePushforward D (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX) hXd
        ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' hbase hisoProper.2.1.2 (k - 1 + 1)
        (cycleGroupDegreeCongr D _ (Int.sub_add_cancel k 1).symm
          (properCyclePushforward D (((𝔻).1.ι ≫ g) ≫ sX) h𝔻
            (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX) hXd
            (firstChernBivariantTestIso_hom_comp D sX ((𝔻).1.ι ≫ g))
            (isProper_of_isIso D.site D.base D.base_mem
              (firstChernBivariantTestIso D ((𝔻).1.ι ≫ g)).hom).2.1.2 k w)) =
      flatPullbackMap D ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' ((𝔻).1.ι ≫ g ≫ sX) h𝔻 g₀
        hg₀B 0 hg₀f hg₀r k (k - 1 + 1) (Int.add_zero k |>.trans (Int.sub_add_cancel k 1).symm)
        w :=
  (properCyclePushforward_cycleGroupDegreeCongr D _ hXd _ h𝔼' hbase hisoProper.2.1.2
    (Int.sub_add_cancel k 1).symm _).trans <|
  (congrArg (fun x => cycleGroupDegreeCongr D _ (Int.sub_add_cancel k 1).symm
    (properCyclePushforward D _ hXd _ h𝔼' hbase hisoProper.2.1.2 k x))
    (properCyclePushforward_firstChernBivariantTestIso D sX ((𝔻).1.ι ≫ g) h𝔻 hXd k w)).trans <|
  (congrArg (cycleGroupDegreeCongr D _ (Int.sub_add_cancel k 1).symm)
    (properCyclePushforward_flatPullbackMap_of_isIso D _ hXd _ h𝔼' _ h𝔻 hab
      (pullbackSnd_id_comp D sX _) hg₀B hbase hisoProper.2.1.2 0 _ _ hg₀f hg₀r k k
      (Int.add_zero k) w)).trans <|
  flatPullbackMap_cycleGroupDegreeCongr D _ h𝔼' _ h𝔻 _ _ 0 hg₀f hg₀r (rfl : k = k)
    (Int.sub_add_cancel k 1).symm (Int.add_zero k) _ w

include hL in
/-- **The Gysin square of Stacks 0ERJ (3) for the cap operation of Stacks 0ERM, in
`CH_{k-1}(E')`.**  For `a = e'_* α = (X' ⟶ Y')^* α` on `X'` and `y = e''_*(i^* α)` on `X''` (with
`iso_* y = g₀^*(i^*α)`),

  `[iso_*(c₁(fst''^*ℒ) ∩ y)] = [(i')^*(c₁(fst'^*ℒ) ∩ a)]`. -/
private theorem chowClassCanonical_properCyclePushforward_firstChernCap_eq_gysin
    (hXd : D.IsGood (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX))
    (iso : pullback (𝟙 X) ((𝔻).1.ι ≫ g) ≅ (𝔼').1.toFunctor)
    (hbase : iso.hom ≫ ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) =
      pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX)
    (hisoProper : IsProper D.site D.base D.base_mem iso.hom)
    (hfst : iso.hom ≫ (𝔼').1.ι ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g))
    (g₀ : (𝔼').1.toFunctor ⟶ (𝔻).1.toFunctor)
    (hsq : IsPullback g₀ (𝔼').1.ι (𝔻).1.ι (pullback.snd (𝟙 X) g))
    (hsndf : IsFlat D.site D.base D.base_mem (pullback.snd (𝟙 X) g))
    (hsndr : HasRelativeDimension 0 D.site D.base D.base_mem (pullback.snd (𝟙 X) g))
    (hg₀f : IsFlat D.site D.base D.base_mem g₀)
    (hg₀r : HasRelativeDimension 0 D.site D.base D.base_mem g₀) (k : ℤ)
    (α : CycleGroup D (g ≫ sX) (k + 1))
    (a : CycleGroup D (pullback.fst (𝟙 X) g ≫ sX) (k - 1 + 1 + 1))
    (ha : a = flatPullbackMap D (pullback.fst (𝟙 X) g ≫ sX) hX' (g ≫ sX) hY'
      (pullback.snd (𝟙 X) g) (pullbackSnd_id_comp D sX g) 0 hsndf hsndr (k + 1) (k - 1 + 1 + 1)
      ((Int.add_zero (k + 1)).trans (congrArg (· + 1) (Int.sub_add_cancel k 1).symm)) α)
    (y : CycleGroup D (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX) (k - 1 + 1))
    (hy : properCyclePushforward D (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX) hXd
        ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' hbase hisoProper.2.1.2 (k - 1 + 1) y =
      flatPullbackMap D ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' ((𝔻).1.ι ≫ g ≫ sX) h𝔻 g₀
        (comp_structure_of_isPullback D (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX)
          (pullbackSnd_id_comp D sX g) hsq) 0 hg₀f hg₀r k (k - 1 + 1)
        (Int.add_zero k |>.trans (Int.sub_add_cancel k 1).symm)
        (gysinCycleMap D (g ≫ sX) 𝔻 h𝔻 k (sectionGysinRule D (g ≫ sX) hY' M t k hM) α)) :
    chowClassCanonical.{u + 1} D ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' (k - 1)
        (properCyclePushforward D (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX) hXd
          ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' hbase hisoProper.2.1.2 (k - 1)
          (firstChernCapCycleMap D _ hXd (k - 1) (canonicalFirstChernRule D _ hXd
            ((modulePullback D.site D.base D.base_mem
              (firstChernBivariantFst D sX hX ((𝔻).1.ι ≫ g) hXd)).obj L)
            (modulePullbackInvertible (firstChernBivariantFst D sX hX ((𝔻).1.ι ≫ g) hXd) L hL)
            (k - 1)) y)) =
      chowClassCanonical.{u + 1} D ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' (k - 1)
        (gysinCycleMap D (pullback.fst (𝟙 X) g ≫ sX) 𝔼' h𝔼' (k - 1)
          (sectionGysinRule D (pullback.fst (𝟙 X) g ≫ sX) hX' 𝕃' 𝕤' (k - 1) h𝕃')
          (firstChernCapCycleMap D _ hX' (k - 1 + 1) (canonicalFirstChernRule D _ hX'
            ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L)
            (modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL) (k - 1 + 1))
            a)) := by
  have hN := modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL
  have hNE := isInvertibleModule_closedSubspaceRestrictSheaf D (pullback.fst (𝟙 X) g ≫ sX) hX'
    𝔼' _ hN
  have h0ERB := chowClassCanonical_gysinCycleMap_firstChernCapCycleMap.{u, u + 1} D
    (pullback.fst (𝟙 X) g ≫ sX) hX' 𝕃' h𝕃' 𝕤' _ hN (k - 1) a
  refine Eq.trans ?_ h0ERB.symm
  have h6₀ := chowClassCanonical_gysinCycleMap_flatPullbackMap_of_isPullback D (g ≫ sX) hY'
    (pullback.fst (𝟙 X) g ≫ sX) hX' (pullbackSnd_id_comp D sX g) 0 hsndf hsndr M t hM hsq k
    (k - 1 + 1) (Int.add_zero k |>.trans (Int.sub_add_cancel k 1).symm)
    ((Int.add_zero (k + 1)).trans (congrArg (· + 1) (Int.sub_add_cancel k 1).symm)) α
  rw [← ha, ← hy] at h6₀
  have h6 := congrArg (canonicalFirstChernCapCanonicalChowMap D
    ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' (k - 1)
      (closedSubspaceRestrictSheaf D (pullback.fst (𝟙 X) g ≫ sX) hX'
        ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L)
        𝔼') hNE) h6₀
  rw [canonicalFirstChernCapCanonicalChowMap_chowClassCanonical,
    canonicalFirstChernCapCanonicalChowMap_chowClassCanonical] at h6
  refine Eq.trans ?_ h6.symm
  exact chowClassCanonical_properCyclePushforward_firstChernCapCycleMap_modulePullback D
    _ hXd _ h𝔼' (ObjectProperty.homMk iso.hom) hbase hisoProper
    (closedSubspaceInclusion D.site D.base D.base_mem ⟨pullback (𝟙 X) g, hX'.1⟩ 𝔼')
    (firstChernBivariantFst D sX hX g hX') (firstChernBivariantFst D sX hX ((𝔻).1.ι ≫ g) hXd)
    (ObjectProperty.hom_ext _ hfst) L hL (k - 1) y

/-- **Stacks 0ERJ (3) for the cap operation of Stacks 0ERM: compatibility with the refined Gysin
maps.**  Let `g : Y' ⟶ X` be a good test space, `(ℳ, t, i : D' → Y')` a triple as in Stacks 0ER1
on it, `E' ⊆ X' = X ×_X Y'` the vanishing locus of the pulled-back section, identified with
`X'' = X ×_X D'` by `iso` over `X'`.  For every `α ∈ Z_{k+1}(Y')` there are cycles `β` on `X'`
and `γ` on `X''` with

  `c₁ ∩ [α] = [β]`,   `c₁ ∩ [i^*α] = [γ]`   and   `[iso_* γ] = [(i')^* β]`  in `CH_{k-1}(E')`,

where `c₁ ∩ -` is `AlgebraicGeometry.Space.firstChernBivariantCap` and `i^*`, `(i')^*` are the
refined Gysin maps of Stacks 0ER1.  This is the shape of the field `gysin_naturality` of Stacks
0ERJ at `f = 𝟙 X` and `p = 1`, with the transport of `CH_{k-1+1}` to `CH_{k+1-1}` written on Chow
groups (`AlgebraicGeometry.Space.chowGroupCanonicalDegreeCongr`). -/
theorem firstChernBivariantCap_gysin_naturality
    (hXd : D.IsGood (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX))
    (iso : pullback (𝟙 X) ((𝔻).1.ι ≫ g) ≅ (𝔼').1.toFunctor)
    (hiso : iso.hom ≫ (𝔼').1.ι = bivariantBaseChangeMap D (𝟙 X) g (𝔻).1.ι)
    (hbase : iso.hom ≫ ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) =
      pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX)
    (hisoProper : IsProper D.site D.base D.base_mem iso.hom) (k : ℤ)
    (α : CycleGroup D (g ≫ sX) (k + 1)) :
    ∃ (β : CycleGroup D (pullback.fst (𝟙 X) g ≫ sX) (k - 1 + 1))
      (γ : CycleGroup D (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX) (k - 1)),
      firstChernBivariantCap D sX hX L hL g hY' hX' (k + 1)
          (chowClassCanonical.{u + 1} D (g ≫ sX) hY' (k + 1) α) =
        chowGroupCanonicalDegreeCongr D (pullback.fst (𝟙 X) g ≫ sX) hX'
          ((Int.sub_add_cancel k 1).trans (Int.add_sub_cancel k 1).symm)
          (chowClassCanonical.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX' (k - 1 + 1) β) ∧
      firstChernBivariantCap D sX hX L hL ((𝔻).1.ι ≫ g) h𝔻 hXd k
          (chowClassCanonical.{u + 1} D ((𝔻).1.ι ≫ g ≫ sX) h𝔻 k
            (gysinCycleMap D (g ≫ sX) 𝔻 h𝔻 k (sectionGysinRule D (g ≫ sX) hY' M t k hM) α)) =
        chowClassCanonical.{u + 1} D (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX) hXd (k - 1) γ ∧
      chowClassCanonical.{u + 1} D ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' (k - 1)
          (properCyclePushforward D (pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) ≫ sX) hXd
            ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' hbase hisoProper.2.1.2 (k - 1) γ) =
        chowClassCanonical.{u + 1} D ((𝔼').1.ι ≫ pullback.fst (𝟙 X) g ≫ sX) h𝔼' (k - 1)
          (gysinCycleMap D (pullback.fst (𝟙 X) g ≫ sX) 𝔼' h𝔼' (k - 1)
            (sectionGysinRule D (pullback.fst (𝟙 X) g ≫ sX) hX' 𝕃' 𝕤' (k - 1) h𝕃') β) := by
  have he' := isProper_of_isIso D.site D.base D.base_mem (firstChernBivariantTestIso D g).hom
  have hN := modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL
  have hsndf := isFlat_of_isEtale D.site D.base D.base_mem
    (isEtale_of_isIso D.site D.base D.base_mem (pullback.snd (𝟙 X) g))
  have hsndr := hasRelativeDimension_zero_of_isIso D.site D.base D.base_mem
    (pullback.snd (𝟙 X) g) hY'.1
  have ha := (congrArg (cycleGroupDegreeCongr D _ (congrArg (· + 1) (Int.sub_add_cancel k 1).symm))
      (properCyclePushforward_firstChernBivariantTestIso D sX g hY' hX' (k + 1) α)).trans
    (flatPullbackMap_cycleGroupDegreeCongr D _ hX' _ hY' _ (pullbackSnd_id_comp D sX g) 0 hsndf
      hsndr (rfl : k + 1 = k + 1) (congrArg (· + 1) (Int.sub_add_cancel k 1).symm)
      (Int.add_zero _)
      ((Int.add_zero (k + 1)).trans (congrArg (· + 1) (Int.sub_add_cancel k 1).symm)) α)
  obtain ⟨g₀, hsq⟩ := exists_isPullback_vanishingLocus_pullbackSheaf D (g ≫ sX) hY'
    (pullback.fst (𝟙 X) g ≫ sX) hX' (ObjectProperty.homMk (pullback.snd (𝟙 X) g)) M t hM
  have hg₀ := isFlat_and_hasRelativeDimension_gysinPullbackProjection D (g ≫ sX) hY'
    (pullback.fst (𝟙 X) g ≫ sX) hX' (pullbackSnd_id_comp D sX g) 0 hsndf hsndr M t hsq
  have hab : iso.hom ≫ g₀ = pullback.snd (𝟙 X) ((𝔻).1.ι ≫ g) := by
    rw [← cancel_mono (𝔻).1.ι, Category.assoc, hsq.w, ← Category.assoc, hiso]
    simp
  have hfst : iso.hom ≫ (𝔼').1.ι ≫ pullback.fst (𝟙 X) g =
      pullback.fst (𝟙 X) ((𝔻).1.ι ≫ g) := by
    rw [← Category.assoc, hiso]
    simp
  have hy := properCyclePushforward_iso_firstChernBivariantTestIso D sX g hY' hX' M t hXd iso
    hbase hisoProper g₀ hab (comp_structure_of_isPullback D (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX)
      (pullbackSnd_id_comp D sX g) hsq) hg₀.1 hg₀.2 k
    (gysinCycleMap D (g ≫ sX) 𝔻 h𝔻 k (sectionGysinRule D (g ≫ sX) hY' M t k hM) α)
  refine ⟨_, _, ?_, ?_, chowClassCanonical_properCyclePushforward_firstChernCap_eq_gysin D sX hX
    L hL g hY' hX' M t hM hXd iso hbase hisoProper hfst g₀ hsq hsndf hsndr hg₀.1 hg₀.2 k α _ ha _
    hy⟩
  · rw [firstChernBivariantCap_chowClassCanonical, chowGroupCanonicalDegreeCongr_chowClassCanonical,
      canonicalFirstChernCapCanonical, AddMonoidHom.comp_apply,
      cycleGroupDegreeCongr_firstChernCapCycleMap D _ hX' _ hN
        ((Int.sub_add_cancel k 1).trans (Int.add_sub_cancel k 1).symm)
        (congrArg (· + 1) ((Int.sub_add_cancel k 1).trans (Int.add_sub_cancel k 1).symm)),
      cycleGroupDegreeCongr_cycleGroupDegreeCongr]
  · exact firstChernBivariantCap_chowClassCanonical D sX hX L hL ((𝔻).1.ι ≫ g) h𝔻 hXd k _

end GysinNaturality

/-! ### Stacks 0ERM -/

section Registration

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module. Then the
rule that to `f : X' ⟶ X` assigns `c₁(f^*ℒ) ∩ - : CH_k(X') ⟶ CH_{k-1}(X')` is a bivariant class
of degree `1`, in the sense of Stacks 0ERJ (`AlgebraicGeometry.Space.BivariantClassCanonical` for
`𝟙 X`, over the constructed Chow groups `AlgebraicGeometry.Space.chowGroupCanonical` of
Stacks 0EQ6). The cap operation is `AlgebraicGeometry.Space.firstChernBivariantCap`. -/
@[stacks 0ERM "the rule f : X' → X ↦ c_1(f^*L) ∩ - : CH_k(X') → CH_{k-1}(X'), for X/B good and
L an invertible O_X-module, is a bivariant class of degree 1"]
def firstChernBivariantClass :
    BivariantClassCanonical.{u + 1} D sX hX sX hX (𝟙 X) (Category.id_comp sX) 1 where
  cap g hY' hX' k := firstChernBivariantCap D sX hX L hL g hY' hX' k
  proper_naturality g hY' hX' h hY'' hX'' hh h' sq hfst hh' k α :=
    firstChernBivariantCap_proper_naturality D sX hX L hL g hY' hX' h hY'' hX'' hh h' sq hfst
      hh' k α
  flat_naturality g hY' hX' h hY'' hX'' hh r hr h' sq hfst hh' hr' k α :=
    firstChernBivariantCap_flat_naturality D sX hX L hL g hY' hX' h hY'' hX'' hh r hr h' sq hfst
      hh' hr' k α
  gysin_naturality g hY' hX' M t hM hXd iso hiso hbase hisoProper k α := by
    obtain ⟨β, γ, h₁, h₂, h₃⟩ := firstChernBivariantCap_gysin_naturality D sX hX L hL g hY' hX'
      M t hM hXd iso hiso hbase hisoProper k α
    exact ⟨β, γ, h₁.trans (chowGroupCanonicalDegreeCongr_chowClassCanonical D _ hX' _ β), h₂, h₃⟩

end Registration

end AlgebraicGeometry.Space

end
