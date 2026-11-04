module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.ULift
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Limits.Colimits
public import StacksFrontier.Topology.Algebra.GroupColimits

/-!
# Different colimit topologies

There is a sequence of abelian topological groups whose colimit topology as topological spaces is
not the topology of their colimit as topological groups: the forgetful functor from topological
groups to topological spaces does not preserve this colimit.

The sequence is `Gₙ = ℚ × ℝⁿ`, with `Gₙ → Gₙ₊₁` the extension of a vector by a zero coordinate.
Consider the set of points `(q, x₀, x₁, …)` with `|xⱼ| < |q - √2/(j+1)|` for every `j`. Its
preimage in each `Gₙ` is a finite intersection of open conditions, hence open, so it is open for
the colimit topology on the underlying spaces. It is not open in the group colimit: a
neighbourhood of the identity there must absorb a product of a small rational `q` close to
`√2/(j+1)` taken from `G₀` with a small real coordinate taken from `G_{j+1}`, and such a product
violates the defining inequality at index `j`.

## Main definitions

* `TopGrp.forgetToTopCat`: the forgetful functor from topological groups to topological spaces.

## Main results

* `Stacks.Examples.exists_sequential_colimit_not_preserved`: a sequence of abelian topological
  groups whose colimit is not preserved by the forgetful functor to spaces.

## Implementation notes

Nonpreservation of this particular colimit says that the canonical comparison from the colimit of
the underlying spaces to the underlying space of the group colimit is not a homeomorphism. The
sequence is indexed by the ordered natural numbers; its first object corresponds to the first term
of the source's sequence after an index shift. The groups are written multiplicatively through
`Multiplicative`, since `TopGrp` is the category of topological groups.

## References

* [Stacks Project, Tag 0B2Z](https://stacks.math.columbia.edu/tag/0B2Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopGrp

/-- The forgetful functor from topological groups to topological spaces. -/
public def forgetToTopCat : TopGrp.{u} ⥤ TopCat.{u} where
  obj G := TopCat.of G
  map f := TopCat.ofHom ⟨f, f.continuous⟩
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl

end TopGrp

namespace Stacks.Examples

noncomputable section

/-- The `n`th finite-dimensional stage of the counterexample sequence. -/
private abbrev Stage (n : ℕ) :=
  Multiplicative (ULift.{u} (ℚ × (Fin n → ℝ)))

private instance liftIsTopologicalAddGroup (n : ℕ) :
    IsTopologicalAddGroup (ULift.{u} (ℚ × (Fin n → ℝ))) where
  continuous_add := by fun_prop
  continuous_neg := by fun_prop

private def stageExtend {m n : ℕ} :
    (ℚ × (Fin m → ℝ)) →+ (ℚ × (Fin n → ℝ)) where
  toFun x := (x.1, fun k => if hk : k.val < m then x.2 ⟨k.val, hk⟩ else 0)
  map_zero' := by
    ext k
    · rfl
    · simp
  map_add' x y := by
    ext k
    · rfl
    · by_cases hk : k.val < m <;> simp [hk]

private def stageLiftExtend {m n : ℕ} :
    ULift.{u} (ℚ × (Fin m → ℝ)) →+ ULift.{u} (ℚ × (Fin n → ℝ)) where
  toFun x := ULift.up (stageExtend x.down)
  map_zero' := by apply ULift.ext; exact stageExtend.map_zero
  map_add' x y := by apply ULift.ext; exact stageExtend.map_add _ _

private lemma stageExtend_comp {m n k : ℕ} (hmn : m ≤ n) :
    (stageExtend (m := n) (n := k)).comp (stageExtend (m := m) (n := n)) =
      stageExtend (m := m) (n := k) := by
  ext x i
  · rfl
  · by_cases hi : i.val < m
    · simp [stageExtend, hi, Nat.lt_of_lt_of_le hi hmn]
    · by_cases hin : i.val < n <;> simp [stageExtend, hi, hin]

private lemma stageExtend_id (n : ℕ) :
    stageExtend (m := n) (n := n) = AddMonoidHom.id (ℚ × (Fin n → ℝ)) := by
  ext x i
  · rfl
  · simp [stageExtend]

private lemma continuous_coord_or_zero (m k : ℕ) :
    Continuous (fun x : Fin m → ℝ => if hk : k < m then x ⟨k, hk⟩ else 0) := by
  by_cases hk : k < m
  · simp only [dite_eq_left hk]
    exact continuous_apply (⟨k, hk⟩ : Fin m)
  · simp only [dite_eq_right hk]
    exact continuous_const

private lemma continuous_stageExtend {m n : ℕ} :
    Continuous (stageExtend (m := m) (n := n)) :=
  continuous_fst.prodMk (continuous_pi fun k => (continuous_coord_or_zero m k.val).comp
    continuous_snd)

private def firstCoordinateAdd (n : ℕ) :
    ULift.{u} (ℚ × (Fin n → ℝ)) →+ ULift.{u} ℚ where
  toFun x := ULift.up x.down.1
  map_zero' := rfl
  map_add' _ _ := rfl

private def realCoordinateAdd (n j : ℕ) :
    ULift.{u} (ℚ × (Fin n → ℝ)) →+ ULift.{u} ℝ where
  toFun x := ULift.up (if h : j < n then x.down.2 ⟨j, h⟩ else 0)
  map_zero' := by
    apply ULift.ext
    change (if h : j < n then (0 : ℝ) else 0) = 0
    split <;> simp
  map_add' x y := by
    apply ULift.ext
    change (if h : j < n then x.down.2 ⟨j, h⟩ + y.down.2 ⟨j, h⟩ else 0) =
      (if h : j < n then x.down.2 ⟨j, h⟩ else 0) +
        (if h : j < n then y.down.2 ⟨j, h⟩ else 0)
    split <;> simp

private def firstCoordinate (n : ℕ) :
    Stage.{u} n →* Multiplicative (ULift.{u} ℚ) :=
  (firstCoordinateAdd n).toMultiplicative

private def realCoordinate (n j : ℕ) :
    Stage.{u} n →* Multiplicative (ULift.{u} ℝ) :=
  (realCoordinateAdd n j).toMultiplicative

private def stageHom (m n : ℕ) :
    TopGrp.of (Stage.{u} m) ⟶ TopGrp.of (Stage.{u} n) :=
  ⟨(stageLiftExtend (m := m) (n := n)).toMultiplicative, by
    exact continuous_ofAdd.comp (continuous_uliftUp.comp
      (continuous_stageExtend.comp (continuous_uliftDown.comp continuous_toAdd)))⟩

private lemma stageHom_id (n : ℕ) : stageHom n n = 𝟙 (TopGrp.of (Stage.{u} n)) := by
  apply TopGrp.hom_ext
  intro x
  change Multiplicative.ofAdd (ULift.up (stageExtend (ULift.down (Multiplicative.toAdd x)))) = x
  rw [stageExtend_id]
  rfl

private lemma stageHom_comp {m n k : ℕ} (hmn : m ≤ n) :
    (stageHom n k).comp (stageHom m n) = stageHom m k := by
  apply TopGrp.hom_ext
  intro x
  change Multiplicative.ofAdd (ULift.up
      (stageExtend (stageExtend (ULift.down (Multiplicative.toAdd x))))) =
    Multiplicative.ofAdd (ULift.up (stageExtend (ULift.down (Multiplicative.toAdd x))))
  rw [← stageExtend_comp (k := k) hmn]
  rfl

/-- The sequential system of finite-dimensional real vector groups. -/
private def sequentialDiagram : ℕ ⥤ TopGrp.{u} where
  obj n := TopGrp.of (Stage.{u} n)
  map _f := stageHom _ _
  map_id n := stageHom_id n
  map_comp f _g := (stageHom_comp f.le).symm

/-- Topological groups have colimits of sequential diagrams, since they have all small
colimits. -/
local instance : HasColimitsOfShape ℕ TopGrp.{u} :=
  HasColimitsOfShape.of_small TopGrp.{u} ℕ

private def firstCocone : Cocone sequentialDiagram where
  pt := TopGrp.indiscreteObj.{u} (GrpCat.of.{u} (Multiplicative (ULift.{u} ℚ)))
  ι :=
    { app := fun n => ⟨firstCoordinate n, continuous_top⟩
      naturality := by
        intro m n f
        apply TopGrp.hom_ext
        intro x
        change Multiplicative.ofAdd (ULift.up
            ((stageExtend (ULift.down (Multiplicative.toAdd x))).1)) =
          Multiplicative.ofAdd (ULift.up ((ULift.down (Multiplicative.toAdd x)).1))
        rfl }

private def realCocone (j : ℕ) : Cocone sequentialDiagram where
  pt := TopGrp.indiscreteObj.{u} (GrpCat.of.{u} (Multiplicative (ULift.{u} ℝ)))
  ι :=
    { app := fun n => ⟨realCoordinate n j, continuous_top⟩
      naturality := by
        intro m n f
        apply TopGrp.hom_ext
        intro x
        dsimp [realCoordinate, realCoordinateAdd, stageHom, stageLiftExtend]
        change Multiplicative.ofAdd (ULift.up
            (if h : j < n then
              (stageExtend (ULift.down (Multiplicative.toAdd x))).2 ⟨j, h⟩ else 0)) =
          Multiplicative.ofAdd (ULift.up
            (if h : j < m then (ULift.down (Multiplicative.toAdd x)).2 ⟨j, h⟩ else 0))
        apply congrArg Multiplicative.ofAdd
        apply congrArg ULift.up
        by_cases hj : j < m
        · have hjn : j < n := lt_of_lt_of_le hj f.le
          simp [stageExtend, hj, hjn]
        · simp [stageExtend, hj] }

private noncomputable def firstColimitCoordinate :
    (colimit sequentialDiagram : TopGrp.{u}) →* Multiplicative (ULift.{u} ℚ) :=
  (colimit.desc sequentialDiagram firstCocone).toMonoidHom

private noncomputable def realColimitCoordinate (j : ℕ) :
    (colimit sequentialDiagram : TopGrp.{u}) →* Multiplicative (ULift.{u} ℝ) :=
  (colimit.desc sequentialDiagram (realCocone j)).toMonoidHom

private noncomputable def center (j : ℕ) : ℝ := √2 / ((j + 1 : ℕ) : ℝ)

private def badSet : Set (colimit sequentialDiagram : TopGrp.{u}) :=
  {x | ∀ j : ℕ,
    |((realColimitCoordinate j x).toAdd.down)| <
      |((firstColimitCoordinate x).toAdd.down : ℝ) - center j|}

private def stageCarrierEquiv (n : ℕ) :
    (sequentialDiagram.obj n).carrier ≃ Stage.{u} n := Equiv.refl _

@[simp] private lemma stageCarrierEquiv_apply (n : ℕ)
    (x : (sequentialDiagram.obj n).carrier) : stageCarrierEquiv n x = x := rfl

private lemma firstColimitCoordinate_ι (n : ℕ) (x : (sequentialDiagram.obj n).carrier) :
    firstColimitCoordinate (colimit.ι sequentialDiagram n x) =
      firstCoordinate n (stageCarrierEquiv n x) := by
  change ((colimit.ι sequentialDiagram n ≫ colimit.desc sequentialDiagram firstCocone) x) = _
  rw [colimit.ι_desc]
  rfl

private lemma realColimitCoordinate_ι (j n : ℕ) (x : (sequentialDiagram.obj n).carrier) :
    realColimitCoordinate j (colimit.ι sequentialDiagram n x) =
      realCoordinate n j (stageCarrierEquiv n x) := by
  change ((colimit.ι sequentialDiagram n ≫ colimit.desc sequentialDiagram (realCocone j)) x) = _
  rw [colimit.ι_desc]
  rfl

private lemma center_pos (j : ℕ) : 0 < center j := by
  unfold center
  positivity

private lemma center_irrational (j : ℕ) : Irrational (center j) := by
  unfold center
  rw [irrational_div_natCast_iff]
  exact ⟨by omega, irrational_sqrt_two⟩

private def stageFirstValue (n : ℕ) (x : Stage.{u} n) : ℝ :=
  ((firstCoordinate n x).toAdd.down : ℝ)

private def stageRealValue (n j : ℕ) (x : Stage.{u} n) : ℝ :=
  (realCoordinate n j x).toAdd.down

private def stageGood (n : ℕ) : Set (Stage.{u} n) :=
  {x | ∀ j : Fin n,
    |(realCoordinate n j.val x).toAdd.down| <
      |((firstCoordinate n x).toAdd.down : ℝ) - center j.val|}

private def stageGoodCarrier (n : ℕ) : Set (sequentialDiagram.obj n).carrier :=
  (stageCarrierEquiv n) ⁻¹' stageGood n

private lemma continuous_stageFirstValue (n : ℕ) :
    Continuous (stageFirstValue n) := by
  unfold stageFirstValue firstCoordinate firstCoordinateAdd
  exact Rat.continuous_coe_real.comp
    (continuous_fst.comp (continuous_uliftDown.comp continuous_toAdd))

private lemma continuous_stageRealValue (n j : ℕ) :
    Continuous (stageRealValue n j) := by
  unfold stageRealValue realCoordinate realCoordinateAdd
  exact (continuous_coord_or_zero n j).comp
    (continuous_snd.comp (continuous_uliftDown.comp continuous_toAdd))

private lemma isOpen_stageIneq (n j : ℕ) :
    IsOpen {x : Stage.{u} n |
      |stageRealValue n j x| < |stageFirstValue n x - center j|} :=
  isOpen_lt (continuous_abs.comp (continuous_stageRealValue n j))
    (continuous_abs.comp ((continuous_stageFirstValue n).sub continuous_const))

private lemma isOpen_stageGood (n : ℕ) : IsOpen (stageGood n) := by
  rw [stageGood]
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j : Fin n => isOpen_stageIneq n j.val

private lemma badSet_preimage (n : ℕ) :
    (colimit.ι sequentialDiagram n) ⁻¹' badSet = stageGoodCarrier n := by
  ext x
  change (∀ j : ℕ,
      |(realColimitCoordinate j ((colimit.ι sequentialDiagram n) x)).toAdd.down| <
        |((firstColimitCoordinate ((colimit.ι sequentialDiagram n) x)).toAdd.down : ℝ) -
          center j|) ↔
    (∀ j : Fin n,
      |(realCoordinate n j.val (stageCarrierEquiv n x)).toAdd.down| <
        |((firstCoordinate n (stageCarrierEquiv n x)).toAdd.down : ℝ) - center j.val|)
  refine ⟨fun hx j => ?_, fun hx j => ?_⟩
  · simpa [stageCarrierEquiv, realColimitCoordinate_ι, firstColimitCoordinate_ι] using hx j.val
  · rw [realColimitCoordinate_ι j n x, firstColimitCoordinate_ι n x]
    by_cases hj : j < n
    · simpa [stageCarrierEquiv] using hx ⟨j, hj⟩
    · have hne : ((firstCoordinate n (stageCarrierEquiv n x)).toAdd.down : ℝ) ≠ center j :=
        ne_comm.mp ((center_irrational j).ne_rat _)
      have hz' : (realCoordinate n j x).toAdd.down = 0 := by
        simp [realCoordinate, AddMonoidHom.toMultiplicative, realCoordinateAdd, hj]
      simpa only [stageCarrierEquiv_apply, hz', abs_zero] using
        (abs_pos.mpr (sub_ne_zero.mpr hne) :
          0 < |((firstCoordinate n (stageCarrierEquiv n x)).toAdd.down : ℝ) - center j|)

private def rationalStagePoint (q : ℚ) : Stage.{u} 0 :=
  Multiplicative.ofAdd (ULift.up (q, fun _ : Fin 0 => (0 : ℝ)))

private def coordinateStagePoint (j : ℕ) (r : ℝ) : Stage.{u} (j + 1) :=
  Multiplicative.ofAdd (ULift.up
    (0, fun i : Fin (j + 1) => if i.val = j then r else 0))

private def rationalStageCarrierPoint (q : ℚ) : (sequentialDiagram.obj 0).carrier :=
  rationalStagePoint q

private def coordinateStageCarrierPoint (j : ℕ) (r : ℝ) :
    (sequentialDiagram.obj (j + 1)).carrier :=
  coordinateStagePoint j r

private lemma multiplicativeUliftZero {α : Type*} [Zero α] :
    Multiplicative.ofAdd (ULift.up (0 : α)) = (1 : Multiplicative (ULift α)) := by
  rw [← ofAdd_zero]
  apply Multiplicative.ofAdd.injective
  rfl

private lemma continuous_rationalStagePoint : Continuous rationalStagePoint := by
  unfold rationalStagePoint
  exact continuous_ofAdd.comp (continuous_uliftUp.comp
    (continuous_prodMk.2 ⟨continuous_id, continuous_const⟩))

private lemma continuous_coordinateStagePoint (j : ℕ) :
    Continuous (coordinateStagePoint j) := by
  unfold coordinateStagePoint
  exact continuous_ofAdd.comp (continuous_uliftUp.comp (continuous_prodMk.2 ⟨continuous_const,
    continuous_pi fun _ =>
      continuous_if_const _ (fun _ => continuous_id) fun _ => continuous_const⟩))

private lemma badSet_not_open : ¬ IsOpen badSet := by
  intro hopen
  have hone : (1 : (colimit sequentialDiagram).carrier) ∈ badSet := by
    rw [badSet, Set.mem_ofPred_eq]
    intro j
    simp only [map_one, toAdd_one, ULift.zero_down, abs_zero, Rat.cast_zero, zero_sub,
      abs_neg, abs_pos, ne_eq]
    exact ne_of_gt (center_pos j)
  obtain ⟨V, hVopen, honeV, hVV⟩ :=
    exists_open_nhds_one_mul_subset (hopen.mem_nhds hone)
  have key : ∀ {α : Type} [PseudoMetricSpace α] [Zero α] {n : ℕ}
      (p : α → (sequentialDiagram.obj n).carrier), Continuous p → p 0 = 1 →
      ∃ ε > 0, ∀ a ∈ Metric.ball (0 : α) ε, colimit.ι sequentialDiagram n (p a) ∈ V := by
    intro α _ _ n p hp h0
    have hopen : IsOpen (p ⁻¹' ((colimit.ι sequentialDiagram n) ⁻¹' V)) :=
      hVopen.preimage ((colimit.ι sequentialDiagram n).continuous.comp hp)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0
      (by simp only [Set.mem_preimage]; rw [h0, map_one]; exact honeV)
    exact ⟨ε, hε, fun a ha => hball ha⟩
  obtain ⟨ε, hε, hεball⟩ := key rationalStageCarrierPoint continuous_rationalStagePoint rfl
  obtain ⟨j, hj⟩ := exists_nat_gt (2 * Real.sqrt 2 / ε)
  have hcSmall : center j < ε / 2 := by
    have hj' : 2 * Real.sqrt 2 / ε < (j : ℝ) := hj
    have hj'' : 2 * Real.sqrt 2 < ε * (j : ℝ) := by
      nlinarith [(div_lt_iff₀ hε).mp hj']
    have hj''' : 2 * Real.sqrt 2 < ε * ((j + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le hj'' (mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.le_succ j) (le_of_lt hε))
    unfold center
    rw [div_lt_iff₀ (by positivity : 0 < ((j + 1 : ℕ) : ℝ))]
    nlinarith
  have hpoint : coordinateStageCarrierPoint j 0 = 1 := by
    apply Multiplicative.ofAdd.injective
    apply ULift.ext
    apply Prod.ext
    · rfl
    · funext i
      change (if i.val = j then (0 : ℝ) else 0) = 0
      split <;> rfl
  obtain ⟨δ, hδ, hδball⟩ := key _ (continuous_coordinateStagePoint j) hpoint
  let r : ℝ := δ / 2
  have hrpos : 0 < r := half_pos hδ
  have hrball : r ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hrpos]
    exact half_lt_self hδ
  let η : ℝ := min (r / 2) (ε / 2 - center j)
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (show center j - η < center j + η by linarith)
  have hqclose : |(q : ℝ) - center j| < r := by
    rw [abs_lt]
    constructor <;> linarith [(min_le_left _ _ : η ≤ r / 2)]
  have hqsmall : |(q : ℝ)| < ε := by
    rw [abs_lt]
    constructor <;> linarith [(min_le_right _ _ : η ≤ ε / 2 - center j), center_pos j]
  have hqball : (q : ℚ) ∈ Metric.ball (0 : ℚ) ε := by
    rw [Metric.mem_ball, Rat.dist_eq]
    simpa using hqsmall
  have hprod :
      colimit.ι sequentialDiagram 0 (rationalStageCarrierPoint q) *
        colimit.ι sequentialDiagram (j + 1) (coordinateStageCarrierPoint j r) ∈ badSet :=
    hVV (Set.mem_mul.mpr ⟨_, hεball q hqball, _, hδball r hrball, rfl⟩)
  have hfirst : firstColimitCoordinate
      (colimit.ι sequentialDiagram 0 (rationalStageCarrierPoint q) *
        colimit.ι sequentialDiagram (j + 1) (coordinateStageCarrierPoint j r)) =
        Multiplicative.ofAdd (ULift.up q) := by
    rw [map_mul, firstColimitCoordinate_ι, firstColimitCoordinate_ι]
    change firstCoordinate 0 (rationalStagePoint q) *
      firstCoordinate (j + 1) (coordinateStagePoint j r) = _
    simp [firstCoordinate, firstCoordinateAdd, rationalStagePoint, coordinateStagePoint,
      AddMonoidHom.toMultiplicative, multiplicativeUliftZero]
  have hreal : realColimitCoordinate j
      (colimit.ι sequentialDiagram 0 (rationalStageCarrierPoint q) *
        colimit.ι sequentialDiagram (j + 1) (coordinateStageCarrierPoint j r)) =
        Multiplicative.ofAdd (ULift.up r) := by
    rw [map_mul, realColimitCoordinate_ι, realColimitCoordinate_ι]
    change realCoordinate 0 j (rationalStagePoint q) *
      realCoordinate (j + 1) j (coordinateStagePoint j r) = _
    simp [realCoordinate, realCoordinateAdd, rationalStagePoint, coordinateStagePoint,
      AddMonoidHom.toMultiplicative, multiplicativeUliftZero]
  rw [badSet, Set.mem_ofPred_eq] at hprod
  have hineq := hprod j
  rw [hfirst, hreal] at hineq
  change |r| < |(q : ℚ) - center j| at hineq
  rw [abs_of_pos hrpos] at hineq
  exact lt_asymm hineq hqclose

/-- A sequential diagram of abelian topological groups for which the colimit topology as spaces
differs from the colimit topology as groups. -/
@[stacks 0B2Z]
public theorem exists_sequential_colimit_not_preserved :
    ∃ F : ℕ ⥤ TopGrp.{u},
      (∀ n : ℕ, ∀ x y : F.obj n, x * y = y * x) ∧
        ¬ PreservesColimit F TopGrp.forgetToTopCat := by
  refine ⟨sequentialDiagram, ?_, ?_⟩
  · intro n x y
    let : CommGroup (Stage.{u} n) := inferInstance
    change (x : Stage.{u} n) * (y : Stage.{u} n) = (y : Stage.{u} n) * (x : Stage.{u} n)
    exact @mul_comm (Stage.{u} n) (inferInstance : CommMagma (Stage.{u} n))
      (x : Stage.{u} n) (y : Stage.{u} n)
  · intro hpres
    have htop : IsOpen badSet := by
      have hcolim := isColimitOfPreserves TopGrp.forgetToTopCat
        (colimit.isColimit sequentialDiagram)
      change IsOpen (badSet : Set (TopGrp.forgetToTopCat.obj
        (colimit sequentialDiagram)))
      refine (TopCat.isOpen_iff_of_isColimit
        (TopGrp.forgetToTopCat.mapCocone (colimit.cocone sequentialDiagram)) hcolim
        badSet).2 ?_
      intro n
      change IsOpen ((colimit.ι sequentialDiagram n) ⁻¹' badSet)
      rw [badSet_preimage n]
      change IsOpen (stageGood n)
      exact isOpen_stageGood n
    exact badSet_not_open htop

end

end Stacks.Examples

end
