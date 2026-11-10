module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerIsomLimit
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.DisjointGluing
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack
public import StacksFrontier.CategoryTheory.Sites.Stack.LiftGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# Effectivity of towers is étale local on the top of an étale limit tower

Let `𝒳` be a stack in groupoids over the big fppf site of `S` whose `Isom` sheaves are algebraic
spaces, let `Wₙ ⟶ V` be an étale limit tower, and let `y₀ → y₁ → ⋯` be a tower of objects over the
levels. Suppose that after an étale covering `{qᵢ : Qᵢ ⟶ V}` by affines the tower becomes
effective: there are objects `Ŷᵢ` over `Qᵢ` with compatible morphisms `yₙ|_{Qᵢ ×_V Wₙ} ⟶ Ŷᵢ`. Then
the tower is effective over `V`. The local limit objects carry a descent datum by the full
faithfulness of restriction to the levels
(`AlgebraicGeometry.C1590Private.IsEtaleLimitTower.existsUnique_mor`), with its cocycle condition
by the same uniqueness, and the descended object restricts to the levels because the `Isom`
presheaves are sheaves.

## Main definitions

* `AlgebraicGeometry.C1590Private.TowerChartData`: local effectivity data of a tower.
* `AlgebraicGeometry.C1590Private.TowerIsEffective`: effectivity of a tower.

## Main results

* `AlgebraicGeometry.C1590Private.TowerChartData.towerIsEffective`: a tower which is effective on
  an étale covering of the top by affines is effective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Functor

universe u v w

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

section Data

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) [p.IsFibered]
  {V : BigFppfOver B S hS} {W : ℕ → BigFppfOver B S hS} {κ : ∀ n, W n ⟶ V}
  {ℓ : ∀ n, W n ⟶ W (n + 1)} (hW : IsEtaleLimitTower W κ ℓ)
  (y : ℕ → X) (hy : ∀ n, p.obj (y n) = W n)

/-- **Local effectivity data of a tower of objects.** An étale covering `qᵢ : Qᵢ ⟶ V` of the top
of an étale limit tower by affines, objects `Ŷᵢ` over `Qᵢ`, and morphisms
`jᵢₙ : yₙ|_{Qᵢ ×_V Wₙ} ⟶ Ŷᵢ` over the projections `Qᵢ ×_V Wₙ ⟶ Qᵢ`, compatible with the
transitions of the tower: `jᵢₙ = uᵢₙ ≫ jᵢ,ₙ₊₁` for the morphism `uᵢₙ` induced by `yₙ ⟶ yₙ₊₁` on
the chosen restrictions. -/
structure TowerChartData (t : ∀ n, y n ⟶ y (n + 1)) where
  /-- The index set of the covering. -/
  I : Type u
  /-- The members of the covering. -/
  Q : I → BigFppfOver B S hS
  /-- The covering morphisms. -/
  q : ∀ i, Q i ⟶ V
  /-- The covering morphisms are étale. -/
  etale : ∀ i, Etale ((𝒯).map (q i))
  /-- The members of the covering are affine. -/
  isAffine : ∀ i, IsAffine ((𝒯).obj (Q i))
  /-- The covering morphisms are jointly surjective. -/
  covers : ∀ v : (𝒯).obj V, ∃ i, v ∈ Set.range ((𝒯).map (q i))
  /-- The local limit objects. -/
  Y : I → X
  /-- The local limit object `Ŷᵢ` lies over `Qᵢ`. -/
  hY : ∀ i, p.obj (Y i) = Q i
  /-- The comparison morphisms from the restricted levels. -/
  j : ∀ i n, (pullbackFiber p ⟨y n, hy n⟩ (pullback.snd (q i) (κ n))).1 ⟶ Y i
  /-- The comparison morphism `jᵢₙ` lies over the projection `Qᵢ ×_V Wₙ ⟶ Qᵢ`. -/
  isHomLift_j : ∀ i n, p.IsHomLift (pullback.fst (q i) (κ n)) (j i n)
  /-- The comparison morphisms are compatible with the transitions of the tower. -/
  compat : ∀ i n (u : (pullbackFiber p ⟨y n, hy n⟩ (pullback.snd (q i) (κ n))).1 ⟶
      (pullbackFiber p ⟨y (n + 1), hy (n + 1)⟩ (pullback.snd (q i) (κ (n + 1)))).1),
    p.IsHomLift (towerPullbackMap hW (q i) n) u →
    u ≫ IsPreFibered.pullbackMap (hy (n + 1)) (pullback.snd (q i) (κ (n + 1))) =
      IsPreFibered.pullbackMap (hy n) (pullback.snd (q i) (κ n)) ≫ t n →
    u ≫ j i (n + 1) = j i n

/-- **Effectivity of a tower of objects** over the levels of a tower `Wₙ ⟶ V`: an object `ŷ` over
`V` with compatible morphisms `yₙ ⟶ ŷ` over `κₙ`. -/
def TowerIsEffective (κ : ∀ n, W n ⟶ V) (t : ∀ n, y n ⟶ y (n + 1)) : Prop :=
  ∃ (ŷ : X) (_ : p.obj ŷ = V) (ψ : ∀ n, y n ⟶ ŷ),
    (∀ n, p.IsHomLift (κ n) (ψ n)) ∧ ∀ n, t n ≫ ψ (n + 1) = ψ n

end Data

/-! ### Comparison of the chart objects with the levels -/

section Level

variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} [p.IsFibered]
  (hp : p.IsFiberedInGroupoids)
  {V : BigFppfOver B S hS} {W : ℕ → BigFppfOver B S hS} {κ : ∀ n, W n ⟶ V}
  {ℓ : ∀ n, W n ⟶ W (n + 1)} {hW : IsEtaleLimitTower W κ ℓ}
  {y : ℕ → X} {hy : ∀ n, p.obj (y n) = W n} {t : ∀ n, y n ⟶ y (n + 1)}
  (D : TowerChartData p hW y hy t)

/-- The restriction of the `n`-th level to the `i`-th chart. -/
abbrev TowerChartData.res (i : D.I) (n : ℕ) : X :=
  (pullbackFiber p ⟨y n, hy n⟩ (pullback.snd (D.q i) (κ n))).1

/-- The projection of the restriction of the `n`-th level to the `n`-th level. -/
abbrev TowerChartData.resπ (i : D.I) (n : ℕ) : D.res i n ⟶ y n :=
  IsPreFibered.pullbackMap (hy n) (pullback.snd (D.q i) (κ n))

include hp in
/-- The comparison morphism `jᵢₙ` is strongly cartesian over the projection `Qᵢ ×_V Wₙ ⟶ Qᵢ`. -/
theorem TowerChartData.isStronglyCartesian_j (i : D.I) (n : ℕ) :
    p.IsStronglyCartesian (pullback.fst (D.q i) (κ n)) (D.j i n) :=
  have := D.isHomLift_j i n
  hp.isStronglyCartesian_homLift _ _

/-- A morphism to the `i`-th chart object, over `a : Z ⟶ Qᵢ` with `a` lying over `d : Z ⟶ Wₙ`,
factored through the restriction of the `n`-th level. -/
def TowerChartData.lift (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS} {z : X} (a : Z ⟶ D.Q i)
    (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n) (ζ : z ⟶ D.Y i) [p.IsHomLift a ζ] :
    z ⟶ D.res i n :=
  haveI := D.isStronglyCartesian_j hp i n
  IsStronglyCartesian.map p (pullback.fst (D.q i) (κ n)) (D.j i n)
    (g := pullback.lift a d h) (pullback.lift_fst _ _ _).symm ζ

/-- `TowerChartData.lift` lies over the induced morphism `Z ⟶ Qᵢ ×_V Wₙ`. -/
instance TowerChartData.isHomLift_lift (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS} {z : X}
    (a : Z ⟶ D.Q i) (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n) (ζ : z ⟶ D.Y i)
    [p.IsHomLift a ζ] : p.IsHomLift (pullback.lift a d h) (D.lift hp i n a d h ζ) := by
  have := D.isStronglyCartesian_j hp i n
  unfold TowerChartData.lift
  infer_instance

/-- `TowerChartData.lift` followed by `jᵢₙ` is the given morphism to `Ŷᵢ`. -/
@[reassoc (attr := simp)]
theorem TowerChartData.lift_j (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS} {z : X}
    (a : Z ⟶ D.Q i) (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n) (ζ : z ⟶ D.Y i)
    [p.IsHomLift a ζ] : D.lift hp i n a d h ζ ≫ D.j i n = ζ := by
  have := D.isStronglyCartesian_j hp i n
  exact IsStronglyCartesian.fac p _ _ _ _

/-- The morphism to the `n`-th level attached to a morphism to the `i`-th chart object. -/
def TowerChartData.level (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS} {z : X} (a : Z ⟶ D.Q i)
    (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n) (ζ : z ⟶ D.Y i) [p.IsHomLift a ζ] : z ⟶ y n :=
  D.lift hp i n a d h ζ ≫ D.resπ i n

/-- `TowerChartData.level` lies over `d : Z ⟶ Wₙ`. -/
instance TowerChartData.isHomLift_level (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS} {z : X}
    (a : Z ⟶ D.Q i) (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n) (ζ : z ⟶ D.Y i)
    [p.IsHomLift a ζ] : p.IsHomLift d (D.level hp i n a d h ζ) := by
  have := (inferInstance : p.IsHomLift (pullback.lift a d h ≫ pullback.snd (D.q i) (κ n))
    (D.lift hp i n a d h ζ ≫ D.resπ i n))
  rw [pullback.lift_snd] at this
  exact this

omit [p.IsFibered] in
/-- A morphism lying over `f` lies over every `f'` equal to `f`. -/
theorem isHomLift_of_eq {R R' : BigFppfOver B S hS} {a b : X} {f f' : R ⟶ R'} (φ : a ⟶ b)
    (h : f = f') [p.IsHomLift f φ] : p.IsHomLift f' φ := h ▸ inferInstance

/-- `TowerChartData.lift` commutes with precomposition by a morphism `χ` over `c`. -/
theorem TowerChartData.lift_comp (i : D.I) (n : ℕ) {Z Z' : BigFppfOver B S hS} {z z' : X}
    (a : Z ⟶ D.Q i) (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n) (ζ : z ⟶ D.Y i)
    [p.IsHomLift a ζ] (c : Z' ⟶ Z) (χ : z' ⟶ z) [p.IsHomLift c χ]
    [p.IsHomLift (c ≫ a) (χ ≫ ζ)] :
    D.lift hp i n (c ≫ a) (c ≫ d) (by simp only [Category.assoc, h]) (χ ≫ ζ) =
      χ ≫ D.lift hp i n a d h ζ := by
  have := D.isStronglyCartesian_j hp i n
  have hw : (c ≫ a) ≫ D.q i = (c ≫ d) ≫ κ n := by simp only [Category.assoc, h]
  have hb : c ≫ pullback.lift a d h = pullback.lift (c ≫ a) (c ≫ d) hw := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have : p.IsHomLift (pullback.lift (c ≫ a) (c ≫ d) hw) (χ ≫ D.lift hp i n a d h ζ) :=
    isHomLift_of_eq _ hb
  refine IsStronglyCartesian.ext p (pullback.fst (D.q i) (κ n)) (D.j i n)
    (pullback.lift (c ≫ a) (c ≫ d) hw) ?_
  rw [D.lift_j, Category.assoc, D.lift_j]

/-- `TowerChartData.level` commutes with precomposition by a morphism `χ` over `c`. -/
theorem TowerChartData.level_comp (i : D.I) (n : ℕ) {Z Z' : BigFppfOver B S hS} {z z' : X}
    (a : Z ⟶ D.Q i) (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n) (ζ : z ⟶ D.Y i)
    [p.IsHomLift a ζ] (c : Z' ⟶ Z) (χ : z' ⟶ z) [p.IsHomLift c χ]
    [p.IsHomLift (c ≫ a) (χ ≫ ζ)] :
    D.level hp i n (c ≫ a) (c ≫ d) (by simp only [Category.assoc, h]) (χ ≫ ζ) =
      χ ≫ D.level hp i n a d h ζ := by
  unfold TowerChartData.level
  rw [D.lift_comp hp i n a d h ζ c χ, Category.assoc]

/-- A morphism to `Ŷᵢ` over `a` is determined by its morphism to the `n`-th level. -/
theorem TowerChartData.level_injective (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS} {z : X}
    (a : Z ⟶ D.Q i) (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n) (ζ ζ' : z ⟶ D.Y i)
    [p.IsHomLift a ζ] [p.IsHomLift a ζ']
    (e : D.level hp i n a d h ζ = D.level hp i n a d h ζ') : ζ = ζ' := by
  have : D.lift hp i n a d h ζ = D.lift hp i n a d h ζ' :=
    IsStronglyCartesian.ext p (pullback.snd (D.q i) (κ n)) (D.resπ i n) (pullback.lift a d h) e
  rw [← D.lift_j hp i n a d h ζ, ← D.lift_j hp i n a d h ζ', this]

/-- Every morphism to the `n`-th level over `d` is `TowerChartData.level` of a morphism to `Ŷᵢ`
over `a`. -/
theorem TowerChartData.exists_level_eq (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS} {z : X}
    (a : Z ⟶ D.Q i) (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n) (η : z ⟶ y n)
    [p.IsHomLift d η] :
    ∃ (ζ : z ⟶ D.Y i) (_ : p.IsHomLift a ζ), D.level hp i n a d h ζ = η := by
  let μ : z ⟶ D.res i n := IsStronglyCartesian.map p (pullback.snd (D.q i) (κ n)) (D.resπ i n)
    (g := pullback.lift a d h) (pullback.lift_snd _ _ _).symm η
  have : p.IsHomLift (pullback.lift a d h) μ := by unfold μ; infer_instance
  have := D.isHomLift_j i n
  have : p.IsHomLift a (μ ≫ D.j i n) :=
    isHomLift_of_eq _ (pullback.lift_fst a d h)
  refine ⟨μ ≫ D.j i n, inferInstance, ?_⟩
  have := D.isStronglyCartesian_j hp i n
  have : D.lift hp i n a d h (μ ≫ D.j i n) = μ :=
    IsStronglyCartesian.ext p (pullback.fst (D.q i) (κ n)) (D.j i n) (pullback.lift a d h)
      (by simp)
  unfold TowerChartData.level
  rw [this]
  exact IsStronglyCartesian.fac p _ _ _ _

/-- The morphism to the level `n + 1` over `d ≫ ℓₙ` is the morphism to the level `n` over `d`
followed by the transition `tₙ : yₙ ⟶ yₙ₊₁`. -/
theorem TowerChartData.level_succ (ht : ∀ n, p.IsHomLift (ℓ n) (t n)) (i : D.I) (n : ℕ)
    {Z : BigFppfOver B S hS} {z : X} (a : Z ⟶ D.Q i) (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n)
    (ζ : z ⟶ D.Y i) [p.IsHomLift a ζ] :
    D.level hp i (n + 1) a (d ≫ ℓ n) (by rw [h, Category.assoc, hW.comp]) ζ =
      D.level hp i n a d h ζ ≫ t n := by
  have := ht n
  have hu : pullback.snd (D.q i) (κ n) ≫ ℓ n =
      towerPullbackMap hW (D.q i) n ≫ pullback.snd (D.q i) (κ (n + 1)) := by
    rw [towerPullbackMap, pullback.lift_snd]
  let u : D.res i n ⟶ D.res i (n + 1) :=
    IsStronglyCartesian.map p (pullback.snd (D.q i) (κ (n + 1))) (D.resπ i (n + 1))
      (g := towerPullbackMap hW (D.q i) n) hu (D.resπ i n ≫ t n)
  have : p.IsHomLift (towerPullbackMap hW (D.q i) n) u := by unfold u; infer_instance
  have hu1 : u ≫ D.resπ i (n + 1) = D.resπ i n ≫ t n := IsStronglyCartesian.fac p _ _ _ _
  have hcomp := D.compat i n u inferInstance hu1
  have hw : a ≫ D.q i = (d ≫ ℓ n) ≫ κ (n + 1) := by rw [h, Category.assoc, hW.comp]
  have hb : pullback.lift a d h ≫ towerPullbackMap hW (D.q i) n =
      pullback.lift a (d ≫ ℓ n) hw := by
    apply pullback.hom_ext
    · rw [Category.assoc, towerPullbackMap, pullback.lift_fst, Category.comp_id,
        pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, towerPullbackMap, pullback.lift_snd, ← Category.assoc,
        pullback.lift_snd, pullback.lift_snd]
  have : p.IsHomLift (pullback.lift a (d ≫ ℓ n) hw) (D.lift hp i n a d h ζ ≫ u) :=
    isHomLift_of_eq _ hb
  have := D.isStronglyCartesian_j hp i (n + 1)
  have hl : D.lift hp i (n + 1) a (d ≫ ℓ n) hw ζ = D.lift hp i n a d h ζ ≫ u :=
    IsStronglyCartesian.ext p (pullback.fst (D.q i) (κ (n + 1))) (D.j i (n + 1))
      (pullback.lift a (d ≫ ℓ n) hw) (by rw [D.lift_j, Category.assoc, hcomp, D.lift_j])
  unfold TowerChartData.level
  rw [hl, Category.assoc, hu1, Category.assoc]

end Level

/-- The chosen pullback of an object, as a restriction. -/
def restrictionOfPullbackFiber {𝒞 : Type*} {𝒮 : Type*} [Category 𝒞] [Category 𝒮] {p : 𝒮 ⥤ 𝒞}
    [p.IsFibered] (hp : p.IsFiberedInGroupoids) {W U : 𝒞} (f : W ⟶ U) (x : 𝒮)
    (hx : p.obj x = U) : Restriction p f x hx where
  pt := (pullbackFiber p ⟨x, hx⟩ f).1
  hpt := (pullbackFiber p ⟨x, hx⟩ f).2
  hom := IsPreFibered.pullbackMap hx f
  isHomLift := inferInstance
  isCart := hp.isStronglyCartesian_homLift _ _

/-- The comparison morphism from a restriction along `g` to the trivial restriction along `𝟙 U` is
its structure morphism. -/
theorem restriction_compTo_id {𝒞 : Type*} {𝒮 : Type*} [Category 𝒞] [Category 𝒮] {p : 𝒮 ⥤ 𝒞}
    {W U : 𝒞} (g : W ⟶ U) {x : 𝒮} (hx : p.obj x = U) (xrW : Restriction p g x hx)
    (hg : g = g ≫ 𝟙 U) :
    Restriction.compTo p g (𝟙 U) hg (Restriction.id p x hx) xrW = xrW.hom :=
  (Category.comp_id _).symm.trans (Restriction.compTo_hom p g (𝟙 U) hg _ xrW)

/-! ### Morphisms between chart objects compatible with the levels -/

section Char

variable {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} [𝒳.val.p.IsFibered]
  {V : BigFppfOver B S hS} {W : ℕ → BigFppfOver B S hS} {κ : ∀ n, W n ⟶ V}
  {ℓ : ∀ n, W n ⟶ W (n + 1)} {hW : IsEtaleLimitTower W κ ℓ}
  {y : ℕ → 𝒳.val.obj} {hy : ∀ n, 𝒳.val.p.obj (y n) = W n} {t : ∀ n, y n ⟶ y (n + 1)}
  (D : TowerChartData 𝒳.val.p hW y hy t)

/-- **Compatibility with the levels.** A morphism `φ : x ⟶ x'` over `O` between objects mapping to
the chart objects `Ŷᵢ` and `Ŷₖ` over `a : O ⟶ Qᵢ` and `b : O ⟶ Qₖ` is compatible with the levels if
for every morphism `χ : z ⟶ x` over `c : Z ⟶ O` with `c` lying over a level `Wₙ`, the two
morphisms `z ⟶ yₙ` read off `χ` through `Ŷᵢ` and through `φ` and `Ŷₖ` agree. -/
def TowerChartData.IsLevelCompatible {O : BigFppfOver B S hS} {i k : D.I} (a : O ⟶ D.Q i)
    (b : O ⟶ D.Q k) {x x' : 𝒳.val.obj} (πx : x ⟶ D.Y i) (πx' : x' ⟶ D.Y k) (φ : x ⟶ x') :
    Prop :=
  ∀ (n : ℕ) {Z : BigFppfOver B S hS} {z : 𝒳.val.obj} (c : Z ⟶ O) (d : Z ⟶ W n)
    (h₁ : (c ≫ a) ≫ D.q i = d ≫ κ n) (h₂ : (c ≫ b) ≫ D.q k = d ≫ κ n) (χ : z ⟶ x),
    𝒳.val.p.IsHomLift c χ → ∀ (ζ : z ⟶ D.Y i) (ζ' : z ⟶ D.Y k) [𝒳.val.p.IsHomLift (c ≫ a) ζ]
      [𝒳.val.p.IsHomLift (c ≫ b) ζ'], ζ = χ ≫ πx → ζ' = χ ≫ φ ≫ πx' →
      D.level 𝒳.isFiberedInGroupoids i n (c ≫ a) d h₁ ζ =
        D.level 𝒳.isFiberedInGroupoids k n (c ≫ b) d h₂ ζ'

/-- `TowerChartData.level` respects equalities of the base morphisms `a` and `d`. -/
theorem TowerChartData.level_congr₂ (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS}
    {z : 𝒳.val.obj} {a a' : Z ⟶ D.Q i} (e : a = a') {d d' : Z ⟶ W n} (e' : d = d')
    (h : a ≫ D.q i = d ≫ κ n) (h' : a' ≫ D.q i = d' ≫ κ n) (ζ : z ⟶ D.Y i)
    [𝒳.val.p.IsHomLift a ζ] [𝒳.val.p.IsHomLift a' ζ] :
    D.level 𝒳.isFiberedInGroupoids i n a d h ζ =
      D.level 𝒳.isFiberedInGroupoids i n a' d' h' ζ := by
  subst e e'
  rfl

/-- `TowerChartData.level` respects equality of the morphism to the chart object. -/
theorem TowerChartData.level_congr_ζ (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS}
    {z : 𝒳.val.obj} (a : Z ⟶ D.Q i) (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n)
    {ζ ζ' : z ⟶ D.Y i} (e : ζ = ζ') [𝒳.val.p.IsHomLift a ζ] [𝒳.val.p.IsHomLift a ζ'] :
    D.level 𝒳.isFiberedInGroupoids i n a d h ζ = D.level 𝒳.isFiberedInGroupoids i n a d h ζ' := by
  subst e
  rfl

/-- `TowerChartData.level` respects equality of the base morphism `a`. -/
theorem TowerChartData.level_congr (i : D.I) (n : ℕ) {Z : BigFppfOver B S hS} {z : 𝒳.val.obj}
    {a a' : Z ⟶ D.Q i} (e : a = a') (d : Z ⟶ W n) (h : a ≫ D.q i = d ≫ κ n)
    (h' : a' ≫ D.q i = d ≫ κ n) (ζ : z ⟶ D.Y i) [𝒳.val.p.IsHomLift a ζ]
    [𝒳.val.p.IsHomLift a' ζ] :
    D.level 𝒳.isFiberedInGroupoids i n a d h ζ = D.level 𝒳.isFiberedInGroupoids i n a' d h' ζ := by
  subst e
  rfl

/-- Level compatibility is stable under restriction. -/
theorem TowerChartData.IsLevelCompatible.restrict {O O' : BigFppfOver B S hS} {i k : D.I}
    {a : O ⟶ D.Q i} {b : O ⟶ D.Q k} {x x' : 𝒳.val.obj} {πx : x ⟶ D.Y i} {πx' : x' ⟶ D.Y k}
    {φ : x ⟶ x'} (hφ : D.IsLevelCompatible a b πx πx' φ) (r : O' ⟶ O) {x₁ x₁' : 𝒳.val.obj}
    (r₁ : x₁ ⟶ x) (r₁' : x₁' ⟶ x') [𝒳.val.p.IsHomLift r r₁] (φ₁ : x₁ ⟶ x₁')
    (hφ₁ : φ₁ ≫ r₁' = r₁ ≫ φ) :
    D.IsLevelCompatible (r ≫ a) (r ≫ b) (r₁ ≫ πx) (r₁' ≫ πx') φ₁ := by
  intro n Z z c d h₁ h₂ χ hχ ζ ζ' _ _ hζ hζ'
  have := hχ
  have : 𝒳.val.p.IsHomLift ((c ≫ r) ≫ a) ζ := isHomLift_of_eq _ (Category.assoc _ _ _).symm
  have : 𝒳.val.p.IsHomLift ((c ≫ r) ≫ b) ζ' := isHomLift_of_eq _ (Category.assoc _ _ _).symm
  have h₁' : ((c ≫ r) ≫ a) ≫ D.q i = d ≫ κ n := by simpa only [Category.assoc] using h₁
  have h₂' : ((c ≫ r) ≫ b) ≫ D.q k = d ≫ κ n := by simpa only [Category.assoc] using h₂
  have e := hφ n (c ≫ r) d h₁' h₂' (χ ≫ r₁) inferInstance ζ ζ'
    (by rw [hζ, Category.assoc]) (by simp only [hζ', reassoc_of% hφ₁, Category.assoc])
  rw [D.level_congr i n (Category.assoc c r a).symm d h₁ h₁', e,
    D.level_congr k n (Category.assoc c r b) d h₂' h₂]

/-- Level compatibility is stable under composition. -/
theorem TowerChartData.IsLevelCompatible.comp {O : BigFppfOver B S hS} {i j k : D.I}
    {a : O ⟶ D.Q i} {b : O ⟶ D.Q j} {e : O ⟶ D.Q k} {x x' x'' : 𝒳.val.obj}
    {πx : x ⟶ D.Y i} {πx' : x' ⟶ D.Y j} {πx'' : x'' ⟶ D.Y k} [𝒳.val.p.IsHomLift b πx']
    {φ : x ⟶ x'} {φ' : x' ⟶ x''} [𝒳.val.p.IsHomLift (𝟙 O) φ]
    (hab : a ≫ D.q i = b ≫ D.q j)
    (hφ : D.IsLevelCompatible a b πx πx' φ) (hφ' : D.IsLevelCompatible b e πx' πx'' φ') :
    D.IsLevelCompatible a e πx πx'' (φ ≫ φ') := by
  intro n Z z c d h₁ h₂ χ hχ ζ ζ'' _ _ hζ hζ''
  have := hχ
  have hb : (c ≫ b) ≫ D.q j = d ≫ κ n := by
    rw [Category.assoc, ← hab, ← Category.assoc, h₁]
  have : 𝒳.val.p.IsHomLift c (χ ≫ φ) := by simpa using (inferInstance :
    𝒳.val.p.IsHomLift (c ≫ 𝟙 O) (χ ≫ φ))
  have : 𝒳.val.p.IsHomLift (c ≫ b) (χ ≫ φ ≫ πx') := by
    simpa only [Category.assoc] using (inferInstance :
      𝒳.val.p.IsHomLift (c ≫ b) ((χ ≫ φ) ≫ πx'))
  rw [hφ n c d h₁ hb χ hχ ζ (χ ≫ φ ≫ πx') hζ rfl,
    hφ' n c d hb h₂ (χ ≫ φ) inferInstance _ ζ'' (by rw [Category.assoc])
      (by simp only [hζ'', Category.assoc])]

/-- **Level-compatible morphisms are unique** over an affine object étale over the top of the
tower. -/
theorem TowerChartData.IsLevelCompatible.ext (hI : Stack.IsAlgebraicSpaceIsomPresheaf B S hS 𝒳)
    {O : BigFppfOver B S hS} {i k : D.I} {a : O ⟶ D.Q i} {b : O ⟶ D.Q k}
    (hab : a ≫ D.q i = b ≫ D.q k)
    (hO : IsEtaleLimitTower (fun n => pullback (a ≫ D.q i) (κ n))
      (fun n => pullback.fst (a ≫ D.q i) (κ n)) (towerPullbackMap hW (a ≫ D.q i)))
    {x x' : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = O) {πx : x ⟶ D.Y i} {πx' : x' ⟶ D.Y k}
    (hπx : 𝒳.val.p.IsHomLift a πx) (hπx' : 𝒳.val.p.IsHomLift b πx') {φ₁ φ₂ : x ⟶ x'}
    (hφ₁ : 𝒳.val.p.IsHomLift (𝟙 O) φ₁) (hφ₂ : 𝒳.val.p.IsHomLift (𝟙 O) φ₂)
    (h₁ : D.IsLevelCompatible a b πx πx' φ₁) (h₂ : D.IsLevelCompatible a b πx πx' φ₂) :
    φ₁ = φ₂ := by
  have := hπx
  have := hπx'
  have := hφ₁
  have := hφ₂
  have hp := 𝒳.isFiberedInGroupoids
  have hx' : 𝒳.val.p.obj x' = O := IsHomLift.codomain_eq 𝒳.val.p (𝟙 O) φ₁
  let e := a ≫ D.q i
  let π : ∀ n, (pullbackFiber 𝒳.val.p ⟨x, hx⟩ (pullback.fst e (κ n))).1 ⟶ x := fun n =>
    IsPreFibered.pullbackMap hx (pullback.fst e (κ n))
  have hπφ : ∀ (n : ℕ) (φ : x ⟶ x') [𝒳.val.p.IsHomLift (𝟙 O) φ],
      𝒳.val.p.IsHomLift (pullback.fst e (κ n)) (π n ≫ φ) := fun n φ _ => by
    simpa using (inferInstance : 𝒳.val.p.IsHomLift (pullback.fst e (κ n) ≫ 𝟙 O) (π n ≫ φ))
  have hn : ∀ n, π n ≫ φ₁ = π n ≫ φ₂ := by
    intro n
    have hc₁ : (pullback.fst e (κ n) ≫ a) ≫ D.q i = pullback.snd e (κ n) ≫ κ n := by
      rw [Category.assoc]; exact pullback.condition
    have hc₂ : (pullback.fst e (κ n) ≫ b) ≫ D.q k = pullback.snd e (κ n) ≫ κ n := by
      rw [Category.assoc, ← hab]; exact pullback.condition
    have := hπφ n φ₁
    have := hπφ n φ₂
    have l₁ := h₁ n (pullback.fst e (κ n)) (pullback.snd e (κ n)) hc₁ hc₂ (π n) inferInstance
      (π n ≫ πx) (π n ≫ φ₁ ≫ πx') rfl rfl
    have l₂ := h₂ n (pullback.fst e (κ n)) (pullback.snd e (κ n)) hc₁ hc₂ (π n) inferInstance
      (π n ≫ πx) (π n ≫ φ₂ ≫ πx') rfl rfl
    have l := D.level_injective hp k n _ _ hc₂ _ _ (l₁.symm.trans l₂)
    have := hp.isStronglyCartesian_homLift b πx'
    exact IsStronglyCartesian.ext 𝒳.val.p b πx' (pullback.fst e (κ n))
      (by simpa only [Category.assoc] using l)
  obtain ⟨φ₀, -, huniq⟩ := hO.existsUnique_mor 𝒳 hI ⟨x, hx⟩ ⟨x', hx'⟩ (fun n => π n ≫ φ₁)
    (fun n => hπφ n φ₁) (fun n => by
      rw [← Category.assoc]
      exact congrArg (· ≫ φ₁) (pullbackFiberMap_fac _ ⟨x, hx⟩ _))
  let π₀ := IsPreFibered.pullbackMap hx (𝟙 O)
  have : 𝒳.val.p.IsHomLift (𝟙 O) (π₀ ≫ φ₁) := by
    simpa using (inferInstance : 𝒳.val.p.IsHomLift (𝟙 O ≫ 𝟙 O) (π₀ ≫ φ₁))
  have : 𝒳.val.p.IsHomLift (𝟙 O) (π₀ ≫ φ₂) := by
    simpa using (inferInstance : 𝒳.val.p.IsHomLift (𝟙 O ≫ 𝟙 O) (π₀ ≫ φ₂))
  have e₁ := huniq (π₀ ≫ φ₁) ⟨inferInstance, fun n => by
    rw [← Category.assoc]
    exact congrArg (· ≫ φ₁) (pullbackFiberMap_fac _ ⟨x, hx⟩ _)⟩
  have e₂ := huniq (π₀ ≫ φ₂) ⟨inferInstance, fun n => by
    rw [← Category.assoc, hn n]
    exact congrArg (· ≫ φ₂) (pullbackFiberMap_fac _ ⟨x, hx⟩ _)⟩
  have : IsIso π₀ := IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝟙 O) π₀
  exact (cancel_epi π₀).1 (e₁.trans e₂.symm)

/-- **Existence of a level-compatible morphism** between the restrictions of two chart objects to
an affine object `O` étale over the top of the tower. -/
theorem TowerChartData.exists_isLevelCompatible (hI : Stack.IsAlgebraicSpaceIsomPresheaf B S hS 𝒳)
    (ht : ∀ n, 𝒳.val.p.IsHomLift (ℓ n) (t n))
    {O : BigFppfOver B S hS} {i k : D.I} (a : O ⟶ D.Q i) (b : O ⟶ D.Q k)
    (hab : a ≫ D.q i = b ≫ D.q k)
    (hO : IsEtaleLimitTower (fun n => pullback (a ≫ D.q i) (κ n))
      (fun n => pullback.fst (a ≫ D.q i) (κ n)) (towerPullbackMap hW (a ≫ D.q i))) :
    ∃ φ : (pullbackFiber 𝒳.val.p ⟨D.Y i, D.hY i⟩ a).1 ⟶
        (pullbackFiber 𝒳.val.p ⟨D.Y k, D.hY k⟩ b).1,
      𝒳.val.p.IsHomLift (𝟙 O) φ ∧
        D.IsLevelCompatible a b (IsPreFibered.pullbackMap (D.hY i) a)
          (IsPreFibered.pullbackMap (D.hY k) b) φ := by
  have hp := 𝒳.isFiberedInGroupoids
  let P := 𝒳.val.p
  let xF : P.Fiber O := pullbackFiber P ⟨D.Y i, D.hY i⟩ a
  let x'F : P.Fiber O := pullbackFiber P ⟨D.Y k, D.hY k⟩ b
  let πx : xF.1 ⟶ D.Y i := IsPreFibered.pullbackMap (D.hY i) a
  let πx' : x'F.1 ⟶ D.Y k := IsPreFibered.pullbackMap (D.hY k) b
  let e := a ≫ D.q i
  let κ' := fun n => pullback.fst e (κ n)
  let bb := fun n => pullback.snd e (κ n)
  let πA := fun n => IsPreFibered.pullbackMap xF.2 (κ' n)
  have hc₁ : ∀ n, (κ' n ≫ a) ≫ D.q i = bb n ≫ κ n := fun n => by
    rw [Category.assoc]; exact pullback.condition
  have hc₂ : ∀ n, (κ' n ≫ b) ≫ D.q k = bb n ≫ κ n := fun n => by
    rw [Category.assoc, ← hab]; exact pullback.condition
  have hζ : ∀ n, P.IsHomLift (κ' n ≫ a) (πA n ≫ πx) := fun n => inferInstance
  let η := fun n => D.level hp i n (κ' n ≫ a) (bb n) (hc₁ n) (πA n ≫ πx)
  have hex : ∀ n, ∃ (ζ' : (pullbackFiber P xF (κ' n)).1 ⟶ D.Y k)
      (_ : P.IsHomLift (κ' n ≫ b) ζ'), D.level hp k n (κ' n ≫ b) (bb n) (hc₂ n) ζ' = η n :=
    fun n => D.exists_level_eq hp k n _ _ (hc₂ n) (η n)
  choose ζ' hζ' hζ'η using hex
  let ψ := fun n => IsStronglyCartesian.map P b πx' (g := κ' n) rfl (ζ' n)
  have hψ : ∀ n, P.IsHomLift (κ' n) (ψ n) := fun n => by unfold ψ; infer_instance
  have hψπ : ∀ n, ψ n ≫ πx' = ζ' n := fun n => IsStronglyCartesian.fac P b πx' _ (ζ' n)
  let pf := fun n => pullbackFiberMap P xF
    (Over.homMk (towerPullbackMap hW e n) (hO.comp n) : Over.mk (κ' n) ⟶ Over.mk (κ' (n + 1)))
  have hpf : ∀ n, P.IsHomLift (towerPullbackMap hW e n) (pf n) := fun n =>
    pullbackFiberMap_isHomLift P xF
      (Over.homMk (towerPullbackMap hW e n) (hO.comp n) : Over.mk (κ' n) ⟶ Over.mk (κ' (n + 1)))
  have hpfπ : ∀ n, pf n ≫ πA (n + 1) = πA n := fun n => pullbackFiberMap_fac P xF _
  have hκc : ∀ n, towerPullbackMap hW e n ≫ κ' (n + 1) = κ' n := hO.comp
  have hbc : ∀ n, towerPullbackMap hW e n ≫ bb (n + 1) = bb n ≫ ℓ n := fun n => by
    simp only [towerPullbackMap, bb]
    rw [pullback.lift_snd]
  have key : ∀ (r : D.I) (br : O ⟶ D.Q r) (n : ℕ) (h₀ : (κ' n ≫ br) ≫ D.q r = bb n ≫ κ n)
      (h₁ : (κ' (n + 1) ≫ br) ≫ D.q r = bb (n + 1) ≫ κ (n + 1))
      (ξ : (pullbackFiber P xF (κ' (n + 1))).1 ⟶ D.Y r) [P.IsHomLift (κ' (n + 1) ≫ br) ξ]
      [P.IsHomLift (κ' n ≫ br) (pf n ≫ ξ)],
      D.level hp r n (κ' n ≫ br) (bb n) h₀ (pf n ≫ ξ) ≫ t n =
        pf n ≫ D.level hp r (n + 1) (κ' (n + 1) ≫ br) (bb (n + 1)) h₁ ξ := by
    intro r br n h₀ h₁ ξ _ _
    have := hpf n
    rw [← D.level_succ hp ht r n (κ' n ≫ br) (bb n) h₀ (pf n ≫ ξ)]
    have ea : κ' n ≫ br = towerPullbackMap hW e n ≫ κ' (n + 1) ≫ br := by
      rw [← Category.assoc, hκc]
    have : P.IsHomLift (towerPullbackMap hW e n ≫ κ' (n + 1) ≫ br) (pf n ≫ ξ) :=
      isHomLift_of_eq _ ea
    rw [D.level_congr₂ r (n + 1) ea (hbc n).symm _ (by simp only [Category.assoc, h₁])]
    exact D.level_comp hp r (n + 1) (κ' (n + 1) ≫ br) (bb (n + 1)) h₁ ξ
      (towerPullbackMap hW e n) (pf n)
  have hc : ∀ n, pf n ≫ ψ (n + 1) = ψ n := fun n => by
    have := hψ n
    have := hψ (n + 1)
    have := hpf n
    have : P.IsHomLift (κ' n) (pf n ≫ ψ (n + 1)) := isHomLift_of_eq _ (hκc n)
    refine IsStronglyCartesian.ext P b πx' (κ' n) ?_
    rw [Category.assoc, hψπ, hψπ]
    have := hζ' n
    have := hζ' (n + 1)
    have : P.IsHomLift (κ' n ≫ b) (pf n ≫ ζ' (n + 1)) :=
      isHomLift_of_eq (f := towerPullbackMap hW e n ≫ κ' (n + 1) ≫ b) _
        (by rw [← Category.assoc, hκc])
    apply D.level_injective hp k n (κ' n ≫ b) (bb n) (hc₂ n)
    rw [hζ'η n]
    have := ht n
    have : P.IsStronglyCartesian (ℓ n) (t n) := hp.isStronglyCartesian_homLift _ _
    refine IsStronglyCartesian.ext P (ℓ n) (t n) (bb n) ?_
    rw [key k b n (hc₂ n) (hc₂ (n + 1)) (ζ' (n + 1)), hζ'η (n + 1)]
    have : P.IsHomLift (κ' n ≫ a) (pf n ≫ πA (n + 1) ≫ πx) :=
      isHomLift_of_eq (f := towerPullbackMap hW e n ≫ κ' (n + 1) ≫ a) _
        (by rw [← Category.assoc, hκc])
    rw [← key i a n (hc₁ n) (hc₁ (n + 1)) (πA (n + 1) ≫ πx)]
    congr 1
    exact D.level_congr_ζ i n _ _ (hc₁ n) (by rw [← Category.assoc, hpfπ])
  obtain ⟨φ₀, ⟨hφ₀, hφ₀n⟩, -⟩ := hO.existsUnique_mor 𝒳 hI xF x'F ψ hψ hc
  let π₀ := IsPreFibered.pullbackMap xF.2 (𝟙 O)
  have : IsIso π₀ := IsStronglyCartesian.isIso_of_base_isIso P (𝟙 O) π₀
  have := hφ₀
  refine ⟨inv π₀ ≫ φ₀, by
    simpa using (inferInstance : P.IsHomLift (𝟙 O ≫ 𝟙 O) (inv π₀ ≫ φ₀)), ?_⟩
  have hπinv : ∀ n, πA n ≫ inv π₀ = pullbackFiberMap P xF
      (Over.homMk (κ' n) (Category.comp_id _) : Over.mk (κ' n) ⟶ Over.mk (𝟙 O)) := fun n => by
    rw [IsIso.comp_inv_eq]
    exact (pullbackFiberMap_fac P xF
      (Over.homMk (κ' n) (Category.comp_id _) : Over.mk (κ' n) ⟶ Over.mk (𝟙 O))).symm
  intro n Z z c d h₁ h₂ χ hχ ζ ζ'' _ _ hζe hζ''e
  have := hχ
  have hcd : c ≫ e = d ≫ κ n := by rw [← Category.assoc]; exact h₁
  let m := pullback.lift c d hcd
  have : P.IsHomLift (m ≫ κ' n) χ := isHomLift_of_eq (f := c) _ (pullback.lift_fst _ _ _).symm
  let χ' := IsStronglyCartesian.map P (κ' n) (πA n) (g := m) rfl χ
  have : P.IsHomLift m χ' := by unfold χ'; infer_instance
  have hχ' : χ' ≫ πA n = χ := IsStronglyCartesian.fac P (κ' n) (πA n) _ χ
  have ea : c ≫ a = m ≫ κ' n ≫ a := by rw [← Category.assoc, pullback.lift_fst]
  have eb : c ≫ b = m ≫ κ' n ≫ b := by rw [← Category.assoc, pullback.lift_fst]
  have ed : d = m ≫ bb n := (pullback.lift_snd _ _ _).symm
  have : P.IsHomLift (m ≫ κ' n ≫ a) ζ := isHomLift_of_eq (f := c ≫ a) _ ea
  have : P.IsHomLift (m ≫ κ' n ≫ b) ζ'' := isHomLift_of_eq (f := c ≫ b) _ eb
  have lhs : D.level hp i n (c ≫ a) d h₁ ζ = χ' ≫ η n := by
    rw [D.level_congr₂ i n ea ed h₁ (by simp only [Category.assoc, hc₁ n]),
      D.level_congr_ζ i n _ _ _ (show ζ = χ' ≫ πA n ≫ πx by rw [hζe, ← Category.assoc, hχ'])]
    exact D.level_comp hp i n (κ' n ≫ a) (bb n) (hc₁ n) (πA n ≫ πx) m χ'
  have hζ'' : ζ'' = χ' ≫ ζ' n := by
    rw [hζ''e, ← hχ', ← hψπ, ← hφ₀n]
    simp only [Category.assoc]
    rw [← Category.assoc (πA n), hπinv]
  have rhs : D.level hp k n (c ≫ b) d h₂ ζ'' = χ' ≫ η n := by
    rw [D.level_congr₂ k n eb ed h₂ (by simp only [Category.assoc, hc₂ n]),
      D.level_congr_ζ k n _ _ _ hζ'', D.level_comp hp k n (κ' n ≫ b) (bb n) (hc₂ n) (ζ' n) m χ',
      hζ'η n]
  exact lhs.trans rhs.symm

/-- `TowerChartData.IsLevelCompatible` respects equalities of the base morphisms `a` and `b`. -/
theorem TowerChartData.isLevelCompatible_congr {O : BigFppfOver B S hS} {i k : D.I}
    {a a' : O ⟶ D.Q i} (e : a = a') {b b' : O ⟶ D.Q k} (e' : b = b') {x x' : 𝒳.val.obj}
    (πx : x ⟶ D.Y i) (πx' : x' ⟶ D.Y k) (φ : x ⟶ x') :
    D.IsLevelCompatible a b πx πx' φ ↔ D.IsLevelCompatible a' b' πx πx' φ := by
  subst e e'
  rfl

/-- The étale limit tower over an overlap `Qᵢ ×_V Qⱼ`. -/
theorem TowerChartData.overlapTower (i j : D.I) :
    IsEtaleLimitTower (fun n => pullback (pullback.fst (D.q i) (D.q j) ≫ D.q i) (κ n))
      (fun n => pullback.fst (pullback.fst (D.q i) (D.q j) ≫ D.q i) (κ n))
      (towerPullbackMap hW (pullback.fst (D.q i) (D.q j) ≫ D.q i)) := by
  have := D.isAffine i
  have := D.isAffine j
  have := hW.isAffine
  have := D.etale i
  have := D.etale j
  have := etale_toScheme_pullback_fst (D.q i) (D.q j)
  refine hW.pullbackTower _ (by rw [Functor.map_comp]; infer_instance) ?_
  exact IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS) (D.q i) (D.q j)).hom

/-- A covering sieve indexed by `ULift ι` is a covering sieve indexed by `ι`. -/
private theorem ofArrows_mem_of_uLift {C : Type*} [Category C] (J : GrothendieckTopology C)
    {X : C} {ι : Type u} {Y : ι → C} (f : ∀ i, Y i ⟶ X)
    (h : Sieve.ofArrows (fun i : ULift.{u + 1} ι => Y i.down) (fun i => f i.down) ∈ J X) :
    Sieve.ofArrows Y f ∈ J X := by
  have he : Presieve.ofArrows (fun i : ULift.{u + 1} ι => Y i.down) (fun i => f i.down) =
      Presieve.ofArrows Y f := by
    funext Y f
    exact propext ⟨fun ⟨i⟩ => ⟨i.down⟩,
      fun ⟨i⟩ => Presieve.ofArrows.mk (ι := ULift.{u + 1} ι) ⟨i⟩⟩
  rwa [Sieve.ofArrows, he] at h

/-- **Gluing the chart objects**: the chart objects of local effectivity data descend to an object
`ŷ` over the top of the tower, with morphisms `Ŷᵢ ⟶ ŷ` over `qᵢ` intertwined on the overlaps by
every level-compatible morphism. -/
theorem TowerChartData.exists_glue (hst : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hI : Stack.IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) (ht : ∀ n, 𝒳.val.p.IsHomLift (ℓ n) (t n)) :
    ∃ (ŷ : 𝒳.val.obj) (_ : 𝒳.val.p.obj ŷ = V) (g : ∀ i, D.Y i ⟶ ŷ),
      (∀ i, 𝒳.val.p.IsHomLift (D.q i) (g i)) ∧
      ∀ (i j : D.I) (φ : (pullbackFiber 𝒳.val.p ⟨D.Y i, D.hY i⟩ (pullback.fst (D.q i) (D.q j))).1 ⟶
          (pullbackFiber 𝒳.val.p ⟨D.Y j, D.hY j⟩ (pullback.snd (D.q i) (D.q j))).1),
        𝒳.val.p.IsHomLift (𝟙 (pullback (D.q i) (D.q j))) φ →
        D.IsLevelCompatible (pullback.fst (D.q i) (D.q j)) (pullback.snd (D.q i) (D.q j))
          (IsPreFibered.pullbackMap (D.hY i) _) (IsPreFibered.pullbackMap (D.hY j) _) φ →
        IsPreFibered.pullbackMap (D.hY i) (pullback.fst (D.q i) (D.q j)) ≫ g i =
          φ ≫ IsPreFibered.pullbackMap (D.hY j) (pullback.snd (D.q i) (D.q j)) ≫ g j := by
  have hp := 𝒳.isFiberedInGroupoids
  let P := 𝒳.val.p
  have hsg : IsStackInGroupoids.{u} P (BigFppfOver.topology B S hS) := hst.isStackInGroupoids hp
  choose φ hφh hφc using fun i j => D.exists_isLevelCompatible hI ht (pullback.fst (D.q i) (D.q j))
    (pullback.snd (D.q i) (D.q j)) pullback.condition (D.overlapTower i j)
  let xrij : ∀ i j, Restriction P (pullback.fst (D.q i) (D.q j)) (D.Y i) (D.hY i) := fun i j =>
    restrictionOfPullbackFiber hp _ _ _
  let xrji : ∀ i j, Restriction P (pullback.snd (D.q i) (D.q j)) (D.Y j) (D.hY j) := fun i j =>
    restrictionOfPullbackFiber hp _ _ _
  have hφF : ∀ i j, FibreHom P (xrij i j).pt (xrji i j).pt (xrij i j).hpt (xrji i j).hpt
      (φ i j) := fun i j => (fibreHom_iff _ _ _).2 (hφh i j)
  let q₁ : ∀ i j k,
      pullback (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)) ⟶ D.Q i :=
    fun i j k ↦ pullback.fst (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)) ≫
      pullback.fst (D.q i) (D.q j)
  let q₂ : ∀ i j k,
      pullback (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)) ⟶ D.Q j :=
    fun i j k ↦ pullback.fst (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)) ≫
      pullback.snd (D.q i) (D.q j)
  let q₃ : ∀ i j k,
      pullback (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)) ⟶ D.Q k :=
    fun i j k ↦ pullback.snd (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)) ≫
      pullback.snd (D.q j) (D.q k)
  have hq : ∀ i j k, q₁ i j k ≫ D.q i = q₃ i j k ≫ D.q k := by
    intro i j k
    simp only [q₁, q₃, Category.assoc]
    rw [pullback.condition (f := D.q i) (g := D.q j), ← Category.assoc, pullback.condition,
      Category.assoc, pullback.condition (f := D.q j) (g := D.q k)]
  have hq₁₂ : ∀ i j k, q₁ i j k ≫ D.q i = q₂ i j k ≫ D.q j := by
    intro i j k
    simp only [q₁, q₂, Category.assoc]
    rw [pullback.condition (f := D.q i) (g := D.q j)]
  let s₁₃ : ∀ i j k, pullback (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)) ⟶
      pullback (D.q i) (D.q k) := fun i j k ↦ pullback.lift (q₁ i j k) (q₃ i j k) (hq i j k)
  let wi : ∀ i j k, Restriction P (q₁ i j k) (D.Y i) (D.hY i) := fun i j k ↦
    Restriction.ofIsFiberedInGroupoids P hp _ _ _
  let wj : ∀ i j k, Restriction P (q₂ i j k) (D.Y j) (D.hY j) := fun i j k ↦
    Restriction.ofIsFiberedInGroupoids P hp _ _ _
  let wk : ∀ i j k, Restriction P (q₃ i j k) (D.Y k) (D.hY k) := fun i j k ↦
    Restriction.ofIsFiberedInGroupoids P hp _ _ _
  choose αij hαijF hαijR using fun i j k ↦ exists_isRestrictionOf hp
    (pullback.fst (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)))
    (rfl : q₁ i j k = _) (rfl : q₂ i j k = _) (xrij i j) (xrji i j) (wi i j k) (wj i j k) (φ i j)
    (hφF i j)
  choose αjk hαjkF hαjkR using fun i j k ↦ exists_isRestrictionOf hp
    (pullback.snd (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)))
    (pullback.condition : q₂ i j k = _) (rfl : q₃ i j k = _) (xrij j k) (xrji j k) (wj i j k)
    (wk i j k) (φ j k) (hφF j k)
  choose αik hαikF hαikR using fun i j k ↦ exists_isRestrictionOf hp (s₁₃ i j k)
    (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm (xrij i k) (xrji i k)
    (wi i j k) (wk i j k) (φ i k) (hφF i k)
  have hφc' : ∀ i j,
      D.IsLevelCompatible (pullback.fst (D.q i) (D.q j)) (pullback.snd (D.q i) (D.q j))
      (xrij i j).hom (xrji i j).hom (φ i j) := hφc
  have hcoc : ∀ i j k, αik i j k = αij i j k ≫ αjk i j k := by
    intro i j k
    let s₁₂ := pullback.fst (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k))
    let s₂₃ := pullback.snd (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k))
    have := Restriction.isHomLift_compTo (p := P) s₁₂ (pullback.fst (D.q i) (D.q j)) rfl
      (xrij i j) (wi i j k)
    have := Restriction.isHomLift_compTo (p := P) s₂₃ (pullback.fst (D.q j) (D.q k))
      (pullback.condition : q₂ i j k = _) (xrij j k) (wj i j k)
    have := Restriction.isHomLift_compTo (p := P) (s₁₃ i j k) (pullback.fst (D.q i) (D.q k))
      (pullback.lift_fst _ _ _).symm (xrij i k) (wi i j k)
    have c₁ : D.IsLevelCompatible (q₁ i j k) (q₂ i j k) (wi i j k).hom (wj i j k).hom
        (αij i j k) := by
      have h := (hφc' i j).restrict D s₁₂ _ _ (αij i j k) (hαijR i j k)
      rwa [Restriction.compTo_hom, Restriction.compTo_hom] at h
    have c₂ : D.IsLevelCompatible (q₂ i j k) (q₃ i j k) (wj i j k).hom (wk i j k).hom
        (αjk i j k) := by
      have h := (hφc' j k).restrict D s₂₃ _ _ (αjk i j k) (hαjkR i j k)
      rw [Restriction.compTo_hom, Restriction.compTo_hom] at h
      exact (D.isLevelCompatible_congr (pullback.condition (f := pullback.snd (D.q i) (D.q j))
        (g := pullback.fst (D.q j) (D.q k))).symm rfl _ _ _).1 h
    have c₃ : D.IsLevelCompatible (q₁ i j k) (q₃ i j k) (wi i j k).hom (wk i j k).hom
        (αik i j k) := by
      have h := (hφc' i k).restrict D (s₁₃ i j k) _ _ (αik i j k) (hαikR i j k)
      rw [Restriction.compTo_hom, Restriction.compTo_hom] at h
      exact (D.isLevelCompatible_congr (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
        _ _ _).1 h
    have := Restriction.isHomLift_hom (wi i j k)
    have := Restriction.isHomLift_hom (wj i j k)
    have := Restriction.isHomLift_hom (wk i j k)
    have := (fibreHom_iff _ _ _).1 (hαijF i j k)
    have := (fibreHom_iff _ _ _).1 (hαjkF i j k)
    have := (fibreHom_iff _ _ _).1 (hαikF i j k)
    have c₁₂ := c₁.comp D (hq₁₂ i j k) c₂
    have := D.isAffine i
    have := D.isAffine j
    have := D.isAffine k
    have := D.etale i
    have := D.etale j
    have := D.etale k
    have := hW.isAffine
    have : IsAffine ((𝒯).obj (pullback (D.q i) (D.q j))) :=
      IsAffine.of_isIso (PreservesPullback.iso 𝒯 (D.q i) (D.q j)).hom
    have : IsAffine ((𝒯).obj (pullback (D.q j) (D.q k))) :=
      IsAffine.of_isIso (PreservesPullback.iso 𝒯 (D.q j) (D.q k)).hom
    have := etale_toScheme_pullback_fst (D.q i) (D.q j)
    have := etale_toScheme_pullback_fst (D.q j) (D.q k)
    have :=
      etale_toScheme_pullback_fst (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k))
    have hT := hW.pullbackTower (q₁ i j k ≫ D.q i) (by
        simp only [q₁, Functor.map_comp]; infer_instance)
      (IsAffine.of_isIso (PreservesPullback.iso 𝒯 (pullback.snd (D.q i) (D.q j))
        (pullback.fst (D.q j) (D.q k))).hom)
    exact TowerChartData.IsLevelCompatible.ext D hI (hq i j k) hT (wi i j k).hpt
      (Restriction.isHomLift_hom (wi i j k)) (Restriction.isHomLift_hom (wk i j k))
      inferInstance inferInstance c₃ c₁₂
  have hcov : Sieve.ofArrows D.Q D.q ∈ BigFppfOver.topology B S hS V :=
    ofArrows_mem_of_uLift _ _ (BigFppfOver.ofArrows_mem_topology_of_etale B S hS
      (fun i : ULift.{u + 1} D.I => D.Q i.down) (fun i => D.q i.down) (fun i => D.etale i.down)
      (fun v => let ⟨i, hi⟩ := D.covers v; ⟨⟨i⟩, hi⟩))
  let Dd : Functor.DescentDatum P D.Q D.q (fun i j ↦ pullback (D.q i) (D.q j))
      (fun i j ↦ pullback.fst (D.q i) (D.q j)) (fun i j ↦ pullback.snd (D.q i) (D.q j))
      (fun i j ↦ IsPullback.of_hasPullback (D.q i) (D.q j))
      (fun i j k ↦ pullback (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)))
      (fun i j k ↦ pullback.fst (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)))
      (fun i j k ↦ pullback.snd (pullback.snd (D.q i) (D.q j)) (pullback.fst (D.q j) (D.q k)))
      (fun i j k ↦ IsPullback.of_hasPullback _ _) q₁ q₂ q₃ (fun _ _ _ ↦ rfl)
      (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) :=
    { x := D.Y
      hx := D.hY
      xrij := xrij
      xrji := xrji
      φ := φ
      φ_fibreHom := hφF
      φ_iso := fun i j ↦ isIso_of_fibreHom hp (hφF i j)
      wi := wi
      wj := wj
      wk := wk
      αij := αij
      αjk := αjk
      αik := αik
      αij_restr := hαijR
      αjk_restr := hαjkR
      s₁₃ := s₁₃
      hs₁₃₁ := fun i j k ↦ pullback.lift_fst _ _ _
      hs₁₃₂ := fun i j k ↦ pullback.lift_snd _ _ _
      αik_restr := hαikR
      cocycle := hcoc }
  obtain ⟨ŷ, hŷ, xr, ψ, hψF, hψI, hcomp⟩ := hsg.effective_descent D.Q D.q hcov _ _ _
    (fun i j ↦ IsPullback.of_hasPullback (D.q i) (D.q j)) _ _ _
    (fun i j k ↦ IsPullback.of_hasPullback _ _)
    q₁ q₂ q₃ (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) Dd
  have := hψI
  refine ⟨ŷ, hŷ, fun i => inv (ψ i) ≫ (xr i).hom, fun i => ?_, fun i j φ' hφ'h hφ'c => ?_⟩
  · have := (fibreHom_iff _ _ _).1 (hψF i)
    have := Restriction.isHomLift_hom (xr i)
    simpa using (inferInstance : P.IsHomLift (𝟙 _ ≫ D.q i) (inv (ψ i) ≫ (xr i).hom))
  · have := hφ'h
    have : 𝒳.val.p.IsHomLift (pullback.fst (D.q i) (D.q j))
        (IsPreFibered.pullbackMap (D.hY i) (pullback.fst (D.q i) (D.q j))) :=
      Restriction.isHomLift_hom (xrij i j)
    have : 𝒳.val.p.IsHomLift (pullback.snd (D.q i) (D.q j))
        (IsPreFibered.pullbackMap (D.hY j) (pullback.snd (D.q i) (D.q j))) :=
      Restriction.isHomLift_hom (xrji i j)
    have := hφh i j
    have hφeq : φ' = φ i j := TowerChartData.IsLevelCompatible.ext D hI pullback.condition
      (D.overlapTower i j) (xrij i j).hpt (Restriction.isHomLift_hom (xrij i j))
      (Restriction.isHomLift_hom (xrji i j)) hφ'h (hφh i j) hφ'c (hφc i j)
    rw [hφeq]
    obtain ⟨xrij', ψir, ψjr, -, -, hir, hjr, hri, hrj, hφ⟩ := hcomp i j
    have := hir
    apply (cancel_epi ψir).1
    have e1 := hri
    have e2 := hrj
    unfold IsRestrictionOf at e1 e2
    rw [restriction_compTo_id] at e1 e2
    change ψir ≫ (xrij i j).hom = _ at e1
    change ψjr ≫ (xrji i j).hom = _ at e2
    change ψir ≫ (xrij i j).hom ≫ inv (ψ i) ≫ (xr i).hom =
      ψir ≫ φ i j ≫ (xrji i j).hom ≫ inv (ψ j) ≫ (xr j).hom
    have hφ' : ψir ≫ φ i j = ψjr := hφ
    have L : ψir ≫ (xrij i j).hom ≫ inv (ψ i) ≫ (xr i).hom = xrij'.hom := by
      rw [reassoc_of% e1]
      simp [Restriction.compTo_hom]
    have R : ψir ≫ φ i j ≫ (xrji i j).hom ≫ inv (ψ j) ≫ (xr j).hom = xrij'.hom := by
      calc ψir ≫ φ i j ≫ (xrji i j).hom ≫ inv (ψ j) ≫ (xr j).hom
          = (ψir ≫ φ i j) ≫ (xrji i j).hom ≫ inv (ψ j) ≫ (xr j).hom := (Category.assoc _ _ _).symm
        _ = ψjr ≫ (xrji i j).hom ≫ inv (ψ j) ≫ (xr j).hom :=
          congrArg (· ≫ (xrji i j).hom ≫ inv (ψ j) ≫ (xr j).hom) hφ'
        _ = (ψjr ≫ (xrji i j).hom) ≫ inv (ψ j) ≫ (xr j).hom := (Category.assoc _ _ _).symm
        _ = _ := congrArg (· ≫ inv (ψ j) ≫ (xr j).hom) e2
        _ = xrij'.hom := by simp [Restriction.compTo_hom]
    exact L.trans R.symm

/-- The restrictions of the levels to the charts cover each level. -/
theorem TowerChartData.levelCover (n : ℕ) :
    Sieve.ofArrows (fun i => pullback (D.q i) (κ n)) (fun i => pullback.snd (D.q i) (κ n)) ∈
      BigFppfOver.topology B S hS (W n) :=
  ofArrows_mem_of_uLift _ _ (BigFppfOver.ofArrows_mem_topology_of_etale B S hS
    (fun i : ULift.{u + 1} D.I => pullback (D.q i.down) (κ n))
    (fun i => pullback.snd (D.q i.down) (κ n))
    (fun i => by have := D.etale i.down; exact etale_toScheme_pullback_snd _ _)
    (fun w => by
      obtain ⟨i, v, hv⟩ := D.covers ((𝒯).map (κ n) w)
      obtain ⟨z, -, hz⟩ := exists_preimage_toScheme_pullback (D.q i) (κ n) v w hv
      exact ⟨⟨i⟩, z, hz⟩))

/-- **Two chart presentations of one morphism to a level give one morphism to the glued
object.** -/
theorem TowerChartData.comp_eq_of_level_eq (hI : Stack.IsAlgebraicSpaceIsomPresheaf B S hS 𝒳)
    (ht : ∀ n, 𝒳.val.p.IsHomLift (ℓ n) (t n)) {ŷ : 𝒳.val.obj} (g : ∀ i, D.Y i ⟶ ŷ)
    (hov : ∀ (i j : D.I)
      (φ : (pullbackFiber 𝒳.val.p ⟨D.Y i, D.hY i⟩ (pullback.fst (D.q i) (D.q j))).1 ⟶
        (pullbackFiber 𝒳.val.p ⟨D.Y j, D.hY j⟩ (pullback.snd (D.q i) (D.q j))).1),
      𝒳.val.p.IsHomLift (𝟙 (pullback (D.q i) (D.q j))) φ →
      D.IsLevelCompatible (pullback.fst (D.q i) (D.q j)) (pullback.snd (D.q i) (D.q j))
        (IsPreFibered.pullbackMap (D.hY i) _) (IsPreFibered.pullbackMap (D.hY j) _) φ →
      IsPreFibered.pullbackMap (D.hY i) (pullback.fst (D.q i) (D.q j)) ≫ g i =
        φ ≫ IsPreFibered.pullbackMap (D.hY j) (pullback.snd (D.q i) (D.q j)) ≫ g j)
    (n : ℕ) {Z : BigFppfOver B S hS} {z : 𝒳.val.obj} (i j : D.I) (a : Z ⟶ D.Q i)
    (a' : Z ⟶ D.Q j) (c : Z ⟶ W n) (h : a ≫ D.q i = c ≫ κ n) (h' : a' ≫ D.q j = c ≫ κ n)
    (ζ : z ⟶ D.Y i) (ζ' : z ⟶ D.Y j) [𝒳.val.p.IsHomLift a ζ] [𝒳.val.p.IsHomLift a' ζ']
    (hl : D.level 𝒳.isFiberedInGroupoids i n a c h ζ =
      D.level 𝒳.isFiberedInGroupoids j n a' c h' ζ') : ζ ≫ g i = ζ' ≫ g j := by
  have hp := 𝒳.isFiberedInGroupoids
  obtain ⟨φ, hφh, hφc⟩ := D.exists_isLevelCompatible hI ht (pullback.fst (D.q i) (D.q j))
    (pullback.snd (D.q i) (D.q j)) pullback.condition (D.overlapTower i j)
  have hm : a ≫ D.q i = a' ≫ D.q j := h.trans h'.symm
  let m := pullback.lift a a' hm
  let πi := IsPreFibered.pullbackMap (D.hY i) (pullback.fst (D.q i) (D.q j))
  let πj := IsPreFibered.pullbackMap (D.hY j) (pullback.snd (D.q i) (D.q j))
  have : 𝒳.val.p.IsHomLift (m ≫ pullback.fst (D.q i) (D.q j)) ζ :=
    isHomLift_of_eq (f := a) _ (pullback.lift_fst _ _ _).symm
  let μ := IsStronglyCartesian.map 𝒳.val.p (pullback.fst (D.q i) (D.q j)) πi (g := m) rfl ζ
  have : 𝒳.val.p.IsHomLift m μ := by unfold μ; infer_instance
  have hμ : μ ≫ πi = ζ := IsStronglyCartesian.fac _ _ _ _ _
  have := hφh
  have h₁ : (m ≫ pullback.fst (D.q i) (D.q j)) ≫ D.q i = c ≫ κ n := by
    rw [pullback.lift_fst]; exact h
  have h₂ : (m ≫ pullback.snd (D.q i) (D.q j)) ≫ D.q j = c ≫ κ n := by
    rw [pullback.lift_snd]; exact h'
  have : 𝒳.val.p.IsHomLift (m ≫ pullback.snd (D.q i) (D.q j)) (μ ≫ φ ≫ πj) := by
    simpa using (inferInstance : 𝒳.val.p.IsHomLift (m ≫ 𝟙 _ ≫ pullback.snd (D.q i) (D.q j))
      (μ ≫ φ ≫ πj))
  have : 𝒳.val.p.IsHomLift (m ≫ pullback.snd (D.q i) (D.q j)) ζ' :=
    isHomLift_of_eq (f := a') _ (pullback.lift_snd _ _ _).symm
  have hlc := hφc n m c h₁ h₂ μ inferInstance ζ (μ ≫ φ ≫ πj) hμ.symm rfl
  have e₁ : D.level hp i n (m ≫ pullback.fst (D.q i) (D.q j)) c h₁ ζ = D.level hp i n a c h ζ :=
    D.level_congr i n (pullback.lift_fst _ _ _) c h₁ h ζ
  have e₂ : D.level hp j n (m ≫ pullback.snd (D.q i) (D.q j)) c h₂ ζ' =
      D.level hp j n a' c h' ζ' := D.level_congr j n (pullback.lift_snd _ _ _) c h₂ h' ζ'
  have hζ' : μ ≫ φ ≫ πj = ζ' :=
    D.level_injective hp j n _ c h₂ _ _ (hlc.symm.trans (e₁.trans (hl.trans e₂.symm)))
  rw [← hζ', ← hμ]
  simp only [Category.assoc]
  rw [hov i j φ hφh hφc]

include D in
/-- **A tower which is effective on an étale covering of the top is effective.** -/
theorem TowerChartData.towerIsEffective (hst : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hI : Stack.IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) (ht : ∀ n, 𝒳.val.p.IsHomLift (ℓ n) (t n)) :
    TowerIsEffective 𝒳.val.p y κ t := by
  have hp := 𝒳.isFiberedInGroupoids
  obtain ⟨ŷ, hŷ, g, hg, hov⟩ := D.exists_glue hst hI ht
  have hagree := D.comp_eq_of_level_eq hI ht g hov
  let πŷ := fun n => IsPreFibered.pullbackMap hŷ (κ n)
  let Q : ∀ (n : ℕ) ⦃x' : 𝒳.val.obj⦄, (x' ⟶ y n) → (x' ⟶ (pullbackFiber 𝒳.val.p ⟨ŷ, hŷ⟩ (κ n)).1) →
      Prop := fun n x' φ ψ =>
    ∃ (i : D.I) (a : 𝒳.val.p.obj x' ⟶ D.Q i) (c : 𝒳.val.p.obj x' ⟶ W n)
      (h : a ≫ D.q i = c ≫ κ n) (ζ : x' ⟶ D.Y i) (_ : 𝒳.val.p.IsHomLift a ζ),
      𝒳.val.p.IsHomLift c φ ∧ 𝒳.val.p.IsHomLift c ψ ∧ D.level hp i n a c h ζ = φ ∧
        ψ ≫ πŷ n = ζ ≫ g i
  have hloc : ∀ n ⦃V' : BigFppfOver B S hS⦄ (g' : V' ⟶ W n),
      Sieve.ofArrows (fun i => pullback (D.q i) (κ n)) (fun i => pullback.snd (D.q i) (κ n)) g' →
      ∃ (x' : 𝒳.val.obj) (φ : x' ⟶ y n) (ψ : x' ⟶ (pullbackFiber 𝒳.val.p ⟨ŷ, hŷ⟩ (κ n)).1),
        𝒳.val.p.IsHomLift g' φ ∧ Q n φ ψ := by
    intro n V' g' hg'
    obtain ⟨i, a₀, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg'
    let x' := (pullbackFiber 𝒳.val.p ⟨y n, hy n⟩ (a₀ ≫ pullback.snd (D.q i) (κ n))).1
    have hx' : 𝒳.val.p.obj x' = V' := (pullbackFiber 𝒳.val.p ⟨y n, hy n⟩ _).2
    let φ := IsPreFibered.pullbackMap (hy n) (a₀ ≫ pullback.snd (D.q i) (κ n))
    let a := eqToHom hx' ≫ a₀ ≫ pullback.fst (D.q i) (κ n)
    let c := eqToHom hx' ≫ a₀ ≫ pullback.snd (D.q i) (κ n)
    have h : a ≫ D.q i = c ≫ κ n := by simp only [a, c, Category.assoc, pullback.condition]
    have : 𝒳.val.p.IsHomLift c φ := inferInstance
    obtain ⟨ζ, hζ, hζl⟩ := D.exists_level_eq hp i n a c h φ
    have := hζ
    have := hg i
    let ψ := IsStronglyCartesian.map 𝒳.val.p (κ n) (πŷ n) (g := c) h (ζ ≫ g i)
    have : 𝒳.val.p.IsHomLift c ψ := by unfold ψ; infer_instance
    exact ⟨x', φ, ψ, inferInstance, i, a, c, h, ζ, hζ, inferInstance, inferInstance, hζl,
      IsStronglyCartesian.fac _ _ _ _ _⟩
  have hm : ∀ n, ∃ m : y n ⟶ (pullbackFiber 𝒳.val.p ⟨ŷ, hŷ⟩ (κ n)).1,
      𝒳.val.p.IsHomLift (𝟙 (W n)) m ∧
      ∀ ⦃V' : BigFppfOver B S hS⦄ ⦃x' : 𝒳.val.obj⦄ (g' : V' ⟶ W n) (φ : x' ⟶ y n)
        (ψ : x' ⟶ (pullbackFiber 𝒳.val.p ⟨ŷ, hŷ⟩ (κ n)).1), 𝒳.val.p.IsHomLift g' φ →
        Q n φ ψ → ψ = φ ≫ m := by
    intro n
    refine hst.exists_hom_of_locally hp (hy n) (pullbackFiber 𝒳.val.p ⟨ŷ, hŷ⟩ (κ n)).2 (Q n)
      ?_ ?_ ?_ (D.levelCover n) (hloc n)
    · intro V' x' g' φ ψ ψ' hφ ⟨i, a, c, h, ζ, hζ, hcφ, hcψ, hl, hψ⟩
        ⟨j, a', c', h', ζ', hζ', hcφ', hcψ', hl', hψ'⟩
      have e1 : c = c' := Functor.eq_of_isHomLift_of_isHomLift hcφ hcφ'
      subst e1
      have := hcψ
      have := hcψ'
      have := hζ
      have := hζ'
      refine IsStronglyCartesian.ext 𝒳.val.p (κ n) (πŷ n) c ?_
      rw [hψ, hψ']
      exact hagree n i j a a' c h h' ζ ζ' (hl.trans hl'.symm)
    · intro x' x'' χ φ ψ ⟨i, a, c, h, ζ, hζ, hcφ, hcψ, hl, hψ⟩
      have := hζ
      have := hcφ
      have := hcψ
      have : 𝒳.val.p.IsHomLift (𝒳.val.p.map χ) χ := IsHomLift.map _ χ
      refine ⟨i, 𝒳.val.p.map χ ≫ a, 𝒳.val.p.map χ ≫ c, by simp only [Category.assoc, h],
        χ ≫ ζ, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
      · rw [D.level_comp hp i n a c h ζ (𝒳.val.p.map χ) χ, hl]
      · rw [Category.assoc, hψ, Category.assoc]
    · intro V' x' g' φ ψ ⟨i, a, c, h, ζ, hζ, hcφ, hcψ, hl, hψ⟩ hg'
      have hV := IsHomLift.domain_eq 𝒳.val.p g' φ
      subst hV
      have e1 := Functor.eq_of_isHomLift_of_isHomLift hcφ hg'
      subst e1
      exact hcψ
  choose m hm₁ hm₂ using hm
  have hmκ : ∀ n, 𝒳.val.p.IsHomLift (κ n) (m n ≫ πŷ n) := fun n => by
    have := hm₁ n
    simpa using (inferInstance : 𝒳.val.p.IsHomLift (𝟙 (W n) ≫ κ n) (m n ≫ πŷ n))
  refine ⟨ŷ, hŷ, fun n => m n ≫ πŷ n, hmκ, fun n => ?_⟩
  · have := ht n
    have := hm₁ (n + 1)
    have := hmκ n
    have : 𝒳.val.p.IsHomLift (κ n) (t n ≫ m (n + 1) ≫ πŷ (n + 1)) := by
      have := (inferInstance : 𝒳.val.p.IsHomLift (ℓ n ≫ 𝟙 (W (n + 1)) ≫ κ (n + 1))
        (t n ≫ m (n + 1) ≫ πŷ (n + 1)))
      rwa [Category.id_comp, hW.comp] at this
    refine hst.eq_of_locally hp (g := κ n) (t n ≫ m (n + 1) ≫ πŷ (n + 1)) (m n ≫ πŷ n)
      (D.levelCover n) (fun V' c' hc' => ?_)
    obtain ⟨x', φ, ψ₀, hφ, hQ⟩ := hloc n c' hc'
    have hψ₀ := hm₂ n c' φ ψ₀ hφ hQ
    obtain ⟨i, a, c, h, ζ, hζ, hcφ, hcψ, hl, hψ⟩ := hQ
    have := hζ
    have := hcφ
    have := hg i
    have h' : a ≫ D.q i = (c ≫ ℓ n) ≫ κ (n + 1) := by rw [h, Category.assoc, hW.comp]
    let ψ₁ := IsStronglyCartesian.map 𝒳.val.p (κ (n + 1)) (πŷ (n + 1)) (g := c ≫ ℓ n) h'
      (ζ ≫ g i)
    have : 𝒳.val.p.IsHomLift (c ≫ ℓ n) ψ₁ := by unfold ψ₁; infer_instance
    have hQ₁ : Q (n + 1) (φ ≫ t n) ψ₁ := ⟨i, a, c ≫ ℓ n, h', ζ, hζ, inferInstance, inferInstance,
      (D.level_succ hp ht i n a c h ζ).trans (by rw [hl]), IsStronglyCartesian.fac _ _ _ _ _⟩
    have hψ₁ := hm₂ (n + 1) (c ≫ ℓ n) (φ ≫ t n) ψ₁ inferInstance hQ₁
    refine ⟨x', φ, hφ, ?_⟩
    calc φ ≫ t n ≫ m (n + 1) ≫ πŷ (n + 1) = ((φ ≫ t n) ≫ m (n + 1)) ≫ πŷ (n + 1) := by
          simp only [Category.assoc]
      _ = ζ ≫ g i := by rw [← hψ₁]; exact IsStronglyCartesian.fac _ _ _ _ _
      _ = ψ₀ ≫ πŷ n := hψ.symm
      _ = φ ≫ m n ≫ πŷ n := by rw [hψ₀, Category.assoc]

end Char

end AlgebraicGeometry.C1590Private

end
