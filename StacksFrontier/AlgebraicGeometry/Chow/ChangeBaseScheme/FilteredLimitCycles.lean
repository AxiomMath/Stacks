module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Injective
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Limits.EmptyFibreAtStage
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection

/-!
# Cycles under a filtered limit of base schemes

In the situation of Stacks 0FVQ, the base-change homomorphism on cycle groups is transported
along an identification of the base change, which makes the cycle groups `Z_k(X_i)` into a
system over the index category with compatible maps to `Z_k(X')`.

## Main definitions

* `Stacks.Chow.cycleGroupCongr` — the identification of cycle groups of equal delta-dimension.
* `Stacks.Chow.baseChangeCyclePullbackOfIsPullback` — the base-change homomorphism on cycle
  groups for a flat base change with vanishing dimension shift, written for an arbitrary
  cartesian square realizing the base change rather than for the chosen fibre product.
* `Stacks.Chow.FilteredBaseChangeSystem.transitionBaseChange` — the flat base change of Chow
  situations attached to a transition morphism of the system.
* `Stacks.Chow.FilteredBaseChangeSystem.stageCyclePullback` — the homomorphism
  `Z_k(X_i) ⟶ Z_k(X')`.
* `Stacks.Chow.FilteredBaseChangeSystem.transitionCyclePullback` — the homomorphism
  `Z_k(X_j) ⟶ Z_k(X_i)` attached to a transition `i ⟶ j`.

## Main results

* `Stacks.Chow.FilteredBaseChangeSystem.isPullback_stageTransition` — `X_i` is the base change
  of `X_j` along the transition `S_i ⟶ S_j`.
* `Stacks.Chow.baseChangeCyclePullbackOfIsPullback_cycleAssociatedToClosedSubscheme` — Stacks
  0FVI part (1) along an arbitrary cartesian square: the base change of the fundamental cycle
  of a closed subscheme is the fundamental cycle of its base change.
* `Stacks.Chow.FilteredBaseChangeSystem.exists_stage_cycleAssociatedToClosedSubscheme` — the
  fundamental cycle of an integral closed subscheme of `X'` comes from every sufficiently late
  stage.
* `Stacks.Chow.FilteredBaseChangeSystem.exists_stageCyclePullback_eq` — **Stacks 0FVQ,
  surjectivity for cycle groups**: every `k`-cycle on `X'` is the image of a `k`-cycle on some
  `X_i`.
* `Stacks.Chow.FilteredBaseChangeSystem.exists_transitionCyclePullback_eq_zero` — **Stacks
  0FVQ, eventual injectivity for cycle groups**: a `k`-cycle on `X_j` whose image in `Z_k(X')`
  vanishes is already annihilated by the transition to some `X_i`.

The statement for Chow groups is not proved here.

## Implementation notes

The base-change homomorphism of `Stacks.Chow.baseChangeCyclePullback` lands in the cycle group
of the chosen fibre product `X ×_S S'`. In the filtered situation the relevant base change is
presented by a different cartesian square — `X'` as the base change of `X_i` along `S' ⟶ S_i` —
so the homomorphism is composed with the pushforward along the comparison isomorphism, which is
an isomorphism over the base and therefore only relabels coefficients.

## References

* [Stacks Project, Tag 0FVQ](https://stacks.math.columbia.edu/tag/0FVQ)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace Stacks.Chow

/-! ### Cycle groups of equal delta-dimension -/

/-- Cycle groups of equal delta-dimension are the same group. -/
def cycleGroupCongr (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {j k : ℤ} (h : j = k) : CycleGroup C f j ≃+ CycleGroup C f k where
  toFun z := ⟨z.1, h ▸ z.2⟩
  invFun z := ⟨z.1, h ▸ z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The isomorphism `cycleGroupCongr` does not change the underlying function of a cycle. -/
@[simp]
theorem cycleGroupCongr_apply_coe (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {j k : ℤ} (h : j = k) (z : CycleGroup C f j) :
    (cycleGroupCongr C f h z).1 = z.1 :=
  rfl

/-! ### Base change along an arbitrary cartesian square -/

/-- The comparison isomorphism of a cartesian square is compatible with the structure morphisms
to the new base. -/
theorem isoPullback_inv_comp_snd (B : FlatBaseChangeSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ B.base.S) {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S} (sq : IsPullback p q f B.g) :
    sq.isoPullback.inv ≫ q = pullback.snd f B.g :=
  (Iso.inv_comp_eq _).2 sq.isoPullback_hom_snd.symm

/-- The base-change homomorphism `Z_k(X) ⟶ Z_k(Y)` of cycle groups attached to a flat base
change of Chow situations with vanishing dimension shift and to a cartesian square realizing
`Y` as the base change of `X`. -/
def baseChangeCyclePullbackOfIsPullback (B : FlatBaseChangeSituation.{u}) (hc : B.c = 0)
    {X Y : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ) :
    CycleGroup B.base f k →+ CycleGroup B.baseChange q k :=
  (properPushforwardHom B.baseChange (pullback.snd f B.g) q sq.isoPullback.inv
      (isoPullback_inv_comp_snd B f sq) k).comp
    (((cycleGroupCongr B.baseChange (pullback.snd f B.g)
        (show k + B.c = k by rw [hc, add_zero])).toAddMonoidHom).comp
      (baseChangeCyclePullback B f k))

/-- The coefficient of the base change of a cycle along an arbitrary cartesian square, at a
point of the source of the square. -/
theorem baseChangeCyclePullbackOfIsPullback_apply (B : FlatBaseChangeSituation.{u})
    (hc : B.c = 0) {X Y : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ)
    (z : CycleGroup B.base f k) (y : Y) :
    (baseChangeCyclePullbackOfIsPullback B hc f sq k z).1 y =
      (baseChangeCyclePullback B f k z).1 (sq.isoPullback.hom.base y) := by
  have hy : sq.isoPullback.inv.base (sq.isoPullback.hom.base y) = y :=
    congrArg (fun m : Y ⟶ Y ↦ m.base y) sq.isoPullback.hom_inv_id
  have hmain := properPushforward_apply_of_isIso B.baseChange (pullback.snd f B.g) q
    sq.isoPullback.inv (isoPullback_inv_comp_snd B f sq) k
    ((cycleGroupCongr B.baseChange (pullback.snd f B.g)
      (show k + B.c = k by rw [hc, add_zero])) (baseChangeCyclePullback B f k z))
    (sq.isoPullback.hom.base y)
  rwa [hy] at hmain

/-- The coefficient of the base change of a cycle along an arbitrary cartesian square: the
coefficient of the cycle at the image point, times the multiplicity of the point in the inverse
image of the reduced closure of that image. -/
theorem baseChangeCyclePullbackOfIsPullback_apply' (B : FlatBaseChangeSituation.{u})
    (hc : B.c = 0) {X Y : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ)
    (z : CycleGroup B.base f k) (y : Y) :
    (baseChangeCyclePullbackOfIsPullback B hc f sq k z).1 y =
      z.1 (p.base y) * flatPullbackWeight B.baseChange q p k y := by
  have hpt : (pullback.fst f B.g).base (sq.isoPullback.hom.base y) = p.base y := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m : Y ⟶ X ↦ m.base y) sq.isoPullback_hom_fst
  have hw := flatPullbackWeight_eq_of_isIso B.baseChange q (pullback.snd f B.g)
    (𝟙 X) sq.isoPullback.hom sq.isoPullback_hom_snd p (pullback.fst f B.g)
    ((Category.comp_id p).trans sq.isoPullback_hom_fst.symm) k y
  rw [baseChangeCyclePullbackOfIsPullback_apply B hc f sq k z y,
    baseChangeCyclePullback_apply B f k z (sq.isoPullback.hom.base y), hc, add_zero, hpt, hw]

/-- If the base change of a cycle along a cartesian square realizing the base change vanishes,
then so does its base change to the chosen fibre product: the two differ by the relabelling of
coefficients along the comparison isomorphism. -/
private theorem baseChangeCyclePullback_eq_zero_of_isPullback (B : FlatBaseChangeSituation.{u})
    (hc : B.c = 0) {X Y : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ)
    (z : CycleGroup B.base f k)
    (hz : baseChangeCyclePullbackOfIsPullback B hc f sq k z = 0) :
    baseChangeCyclePullback B f k z = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  have heval := congrArg (fun c ↦ c.1 (sq.isoPullback.inv.base x)) hz
  rwa [baseChangeCyclePullbackOfIsPullback_apply B hc f sq k z,
    Scheme.inv_hom_apply sq.isoPullback x] at heval

/-- Pulling back `ι` along the two sides of a cartesian square gives isomorphic schemes, compatibly
with the projections to the new base. -/
private theorem exists_iso_pullback_pullback_fst {X Y Z S T : Scheme.{u}} {f : X ⟶ S}
    {g : T ⟶ S} {p : Y ⟶ X} {q : Y ⟶ T} (sq : IsPullback p q f g) (ι : Z ⟶ X) :
    ∃ e : (pullback ι p : Scheme.{u}) ≅ (pullback ι (pullback.fst f g) : Scheme.{u}),
      e.hom ≫ pullback.snd ι (pullback.fst f g) = pullback.snd ι p ≫ sq.isoPullback.hom :=
  ⟨asIso (pullback.map ι p ι (pullback.fst f g) (𝟙 Z) sq.isoPullback.hom (𝟙 X)
    ((Category.comp_id ι).trans (Category.id_comp ι).symm)
    ((Category.comp_id p).trans sq.isoPullback_hom_fst.symm)), pullback.lift_snd _ _ _⟩

/-- **Stacks Project, Tag 0FVI, part (1), along an arbitrary cartesian square.** The base change
of the cycle of a closed subscheme `Z ⊆ X` of delta-dimension at most `k` is the cycle of the
base change of `Z`. -/
theorem baseChangeCyclePullbackOfIsPullback_cycleAssociatedToClosedSubscheme
    (B : FlatBaseChangeSituation.{u}) (hc : B.c = 0) {X Y Z : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q]
    (sq : IsPullback p q f B.g) (ι : Z ⟶ X) [IsClosedImmersion ι] (k : ℤ)
    (hZ : schemeDeltaDimension B.base (ι ≫ f) ≤ (k : EInt)) :
    baseChangeCyclePullbackOfIsPullback B hc f sq k
        (cycleAssociatedToClosedSubscheme B.base f ι k) =
      cycleAssociatedToClosedSubscheme B.baseChange q (pullback.snd ι p) k := by
  obtain ⟨e, hcomp⟩ := exists_iso_pullback_pullback_fst sq ι
  have h0 := baseChangeCyclePullback_cycleAssociatedToClosedSubscheme B f ι k hZ
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [baseChangeCyclePullbackOfIsPullback_apply B hc f sq k _ y, h0, hc, add_zero]
  change closedSubschemeCycleCoeff B.baseChange (pullback.snd f B.g)
      (pullback.snd ι (pullback.fst f B.g)) k (sq.isoPullback.hom.base y) =
    closedSubschemeCycleCoeff B.baseChange q (pullback.snd ι p) k y
  rw [closedSubschemeCycleCoeff_of_isIso_ambient B.baseChange q (pullback.snd f B.g)
    sq.isoPullback.hom sq.isoPullback_hom_snd (pullback.snd ι p) k y]
  exact (closedSubschemeCycleCoeff_eq_of_iso B.baseChange (pullback.snd f B.g)
    (pullback.snd ι p ≫ sq.isoPullback.hom) (pullback.snd ι (pullback.fst f B.g))
    e hcomp k (sq.isoPullback.hom.base y)).symm

/-- **Stacks Project, Tag 0FVI, part (1), dimension bound, along an arbitrary cartesian
square.** -/
theorem schemeDeltaDimension_baseChangeOfIsPullback_le (B : FlatBaseChangeSituation.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g)
    (ι : Z ⟶ X) [IsClosedImmersion ι] {k : ℤ}
    (hZ : schemeDeltaDimension B.base (ι ≫ f) ≤ (k : EInt)) :
    schemeDeltaDimension B.baseChange (pullback.snd ι p ≫ q) ≤ ((k + B.c : ℤ) : EInt) := by
  obtain ⟨e, hcomp⟩ := exists_iso_pullback_pullback_fst sq ι
  have he : e.hom ≫ (pullback.snd ι (pullback.fst f B.g) ≫ pullback.snd f B.g) =
      pullback.snd ι p ≫ q := by
    rw [← Category.assoc, hcomp, Category.assoc, sq.isoPullback_hom_snd]
  rw [← schemeDeltaDimension_congr B.baseChange he,
    schemeDeltaDimension_comp_iso B.baseChange e]
  exact schemeDeltaDimension_baseChange_closedSubscheme_le B f ι hZ

/-- Base changing a closed subscheme twice is base changing it once along the composite. -/
theorem cycleAssociatedToClosedSubscheme_pullback_comp (C : ChowSituation.{u})
    {X Y₁ Y₂ Z : Scheme.{u}} (sY₂ : Y₂ ⟶ C.S) [LocallyOfFiniteType sY₂]
    (ι : Z ⟶ X) [IsClosedImmersion ι] (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ Y₁) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C sY₂ (pullback.snd (pullback.snd ι p₁) p₂) k =
      cycleAssociatedToClosedSubscheme C sY₂ (pullback.snd ι (p₂ ≫ p₁)) k :=
  cycleAssociatedToClosedSubscheme_eq_of_iso C sY₂ _ _ (pullbackLeftPullbackSndIso ι p₁ p₂)
    (pullbackLeftPullbackSndIso_hom_snd ι p₁ p₂) k

namespace FilteredBaseChangeSystem

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (s : FilteredBaseChangeSystem.{w, v, u} I)

/-! ### The flat base change attached to a transition morphism -/

/-- **Stacks Project, Tag 0FVQ, hypothesis (3).** A transition morphism of the inverse system of
bases is a flat base change of Chow situations with vanishing dimension shift: the dimension
functions on both stages are pulled back from `S`, and the transition morphism commutes with the
structure morphisms to `S`. -/
@[reducible] def transitionBaseChange {i j : I} (f : i ⟶ j) : FlatBaseChangeSituation.{u} where
  base := s.stageSituation j
  baseChange := s.stageSituation i
  g := s.diagram.map f
  flat := s.transitionFlat f
  c := 0
  dimensionFunction_eq_add := by
    intro t t'
    have h3 : s.stageToBase i t'.1.1 = s.stageToBase j t := by
      rw [← s.stageToBase_naturality f]
      simpa using congrArg (s.stageToBase j) t'.1.2
    change s.stageDimension i t'.1.1 = s.stageDimension j t + 0
    rw [add_zero, s.stageDimension_eq i t'.1.1, s.stageDimension_eq j t, h3]

/-- The base of `transitionBaseChange f` is the Chow situation of the target stage. -/
@[simp]
theorem transitionBaseChange_base {i j : I} (f : i ⟶ j) :
    (s.transitionBaseChange f).base = s.stageSituation j :=
  rfl

/-- The base change of `transitionBaseChange f` is the Chow situation of the source stage. -/
@[simp]
theorem transitionBaseChange_baseChange {i j : I} (f : i ⟶ j) :
    (s.transitionBaseChange f).baseChange = s.stageSituation i :=
  rfl

/-- The morphism of bases of `transitionBaseChange f` is the transition morphism `S_i ⟶ S_j`. -/
@[simp]
theorem transitionBaseChange_g {i j : I} (f : i ⟶ j) :
    (s.transitionBaseChange f).g = s.diagram.map f :=
  rfl

/-- The dimension shift of `transitionBaseChange f` is zero. -/
@[simp]
theorem transitionBaseChange_c {i j : I} (f : i ⟶ j) : (s.transitionBaseChange f).c = 0 := rfl

/-- **`X_i` is the base change of `X_j` along the transition `S_i ⟶ S_j`.** -/
theorem isPullback_stageTransition {i j : I} (f : i ⟶ j) :
    IsPullback (s.stageTransition f) (pullback.snd s.X.hom (s.stageToBase i))
      (pullback.snd s.X.hom (s.stageToBase j)) (s.diagram.map f) := by
  refine IsPullback.of_right ?_ (s.stageTransition_comp_snd f)
    (IsPullback.of_hasPullback s.X.hom (s.stageToBase j))
  rw [s.stageTransition_comp_fst f, s.stageToBase_naturality f]
  exact IsPullback.of_hasPullback s.X.hom (s.stageToBase i)

/-! ### The homomorphisms on cycle groups -/

/-- The homomorphism `Z_k(X_i) ⟶ Z_k(X')` on cycle groups induced by the projection from the
limit base to the stage `i`. -/
def stageCyclePullback (i : I) (k : ℤ) :
    CycleGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k →+
      CycleGroup s.limitBaseChange.baseChange (pullback.snd s.X.hom s.limitBaseChange.g) k :=
  baseChangeCyclePullbackOfIsPullback (s.stageToLimitBaseChange i) rfl
    (pullback.snd s.X.hom (s.stageToBase i)) (s.isPullback_stageProjection i) k

/-- The homomorphism `Z_k(X_j) ⟶ Z_k(X_i)` on cycle groups induced by a transition morphism
`i ⟶ j` of the inverse system of bases. -/
def transitionCyclePullback {i j : I} (f : i ⟶ j) (k : ℤ) :
    CycleGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k →+
      CycleGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k :=
  baseChangeCyclePullbackOfIsPullback (s.transitionBaseChange f) rfl
    (pullback.snd s.X.hom (s.stageToBase j)) (s.isPullback_stageTransition f) k

/-- `stageCyclePullback i k` is the base change of cycles along the cartesian square realizing
`X'` as the base change of `X_i`. -/
theorem stageCyclePullback_def (i : I) (k : ℤ) :
    s.stageCyclePullback i k = baseChangeCyclePullbackOfIsPullback (s.stageToLimitBaseChange i)
      rfl (pullback.snd s.X.hom (s.stageToBase i)) (s.isPullback_stageProjection i) k :=
  rfl

/-! ### Descent of a fundamental cycle -/

/-- **Stacks Project, Tag 0FVQ, surjectivity on fundamental cycles.** The fundamental cycle of
an integral closed subscheme of `X'` of delta-dimension `k` is, at every sufficiently late
stage, the image of the fundamental cycle of a closed subscheme of `X_i`.

The integral closed subscheme descends to a stage `i₀` by
`Stacks.Chow.FilteredBaseChangeSystem.exists_integral_closedSubscheme_model`; at a later stage
`i` one takes its base change, whose fundamental cycle is carried to the fundamental cycle of
the base change to `X'` by Stacks 0FVI part (1), and base changing twice along
`X' ⟶ X_i ⟶ X_{i₀}` is base changing once along `X' ⟶ X_{i₀}`. -/
theorem exists_stage_cycleAssociatedToClosedSubscheme (k : ℤ)
    (x : (pullback s.X.hom s.limitBaseChange.g : Scheme.{u}))
    (hx : schemeDeltaDimension s.limitBaseChange.baseChange
      ((integralComponentAt x).subschemeι ≫ pullback.snd s.X.hom s.limitBaseChange.g) =
        (k : EInt)) :
    ∃ i₀ : I, ∀ (i : I), (i ⟶ i₀) →
      ∃ (W : Scheme.{u}) (ι : W ⟶ (pullback s.X.hom (s.stageToBase i) : Scheme.{u}))
        (_ : IsClosedImmersion ι),
        schemeDeltaDimension (s.stageSituation i)
            (ι ≫ pullback.snd s.X.hom (s.stageToBase i)) ≤ (k : EInt) ∧
          s.stageCyclePullback i k (cycleAssociatedToClosedSubscheme (s.stageSituation i)
              (pullback.snd s.X.hom (s.stageToBase i)) ι k) =
            cycleAssociatedToClosedSubscheme s.limitBaseChange.baseChange
              (pullback.snd s.X.hom s.limitBaseChange.g) (integralComponentAt x).subschemeι k := by
  let _ : IsClosedImmersion (Over.mk (integralComponentAt x).subschemeι).hom :=
    inferInstanceAs (IsClosedImmersion (integralComponentAt x).subschemeι)
  let _ : IsIntegral (Over.mk (integralComponentAt x).subschemeι).left :=
    isIntegral_integralComponentAt x
  obtain ⟨i₀, Zᵢ, hclosed, hintegral, hdim, ⟨e⟩⟩ :=
    s.exists_integral_closedSubscheme_model (Over.mk (integralComponentAt x).subschemeι) k hx
  let _ : IsClosedImmersion Zᵢ.hom := hclosed
  refine ⟨i₀, fun i f ↦ ?_⟩
  have hbound : schemeDeltaDimension (s.stageSituation i)
      (pullback.snd Zᵢ.hom (s.stageTransition f) ≫
        pullback.snd s.X.hom (s.stageToBase i)) ≤ (k : EInt) := by
    simpa using schemeDeltaDimension_baseChangeOfIsPullback_le (s.transitionBaseChange f)
      (pullback.snd s.X.hom (s.stageToBase i₀)) (s.isPullback_stageTransition f) Zᵢ.hom
      (le_of_eq hdim)
  refine ⟨pullback Zᵢ.hom (s.stageTransition f), pullback.snd Zᵢ.hom (s.stageTransition f),
    inferInstance, hbound, ?_⟩
  rw [s.stageCyclePullback_def i k,
    baseChangeCyclePullbackOfIsPullback_cycleAssociatedToClosedSubscheme
      (s.stageToLimitBaseChange i) rfl (pullback.snd s.X.hom (s.stageToBase i))
      (s.isPullback_stageProjection i) (pullback.snd Zᵢ.hom (s.stageTransition f)) k hbound,
    cycleAssociatedToClosedSubscheme_pullback_comp s.limitBaseChange.baseChange
      (pullback.snd s.X.hom s.limitBaseChange.g) Zᵢ.hom (s.stageTransition f)
      (s.stageProjection i) k,
    s.stageProjection_comp_stageTransition f]
  exact (cycleAssociatedToClosedSubscheme_eq_of_iso s.limitBaseChange.baseChange
    (pullback.snd s.X.hom s.limitBaseChange.g) (integralComponentAt x).subschemeι
    (pullback.snd Zᵢ.hom (s.stageProjection i₀))
    ((Over.forget (pullback s.X.hom s.limitBaseChange.g)).mapIso e) e.hom.w k).symm

/-! ### Surjectivity -/

/-- **Stacks Project, Tag 0FVQ, surjectivity for cycle groups.** Every `k`-cycle on `X'` is the
image of a `k`-cycle on `X_i` for some finite stage `i`.

Since `X'` is quasi-compact the cycle has finite support, so it is a finite integral combination
of fundamental cycles of integral closed subschemes of `X'`. Each of those descends to a finite
stage by `Stacks.Chow.FilteredBaseChangeSystem.exists_stage_cycleAssociatedToClosedSubscheme`,
and the index category being cofiltered, one stage serves for all of them at once. -/
@[stacks 0FVQ "cycle groups, surjectivity: every k-cycle on X' is the image of a k-cycle on X_i"]
theorem exists_stageCyclePullback_eq (k : ℤ)
    (z : CycleGroup s.limitBaseChange.baseChange (pullback.snd s.X.hom s.limitBaseChange.g) k) :
    ∃ (i : I) (w : CycleGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k),
      s.stageCyclePullback i k w = z := by
  classical
  let _ : Fintype (cycleSupportIndex z) := (finite_support_of_compactSpace
    s.limitBaseChange.baseChange (pullback.snd s.X.hom s.limitBaseChange.g) k z).fintype
  choose idx hidx using fun x : cycleSupportIndex z ↦
    s.exists_stage_cycleAssociatedToClosedSubscheme k x.1
      (schemeDeltaDimension_cycleSupportIndex z x)
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.image idx Finset.univ)
  choose W ι hci hbound heq using fun x : cycleSupportIndex z ↦
    hidx x i (hi (Finset.mem_image_of_mem idx (Finset.mem_univ x))).some
  refine ⟨i, ∑ x : cycleSupportIndex z, (z.1 x.1) •
    cycleAssociatedToClosedSubscheme (s.stageSituation i)
      (pullback.snd s.X.hom (s.stageToBase i)) (ι x) k, ?_⟩
  simp only [map_sum, map_zsmul, heq]
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hsum : (∑ x : cycleSupportIndex z, (z.1 x.1) •
      cycleAssociatedToClosedSubscheme s.limitBaseChange.baseChange
        (pullback.snd s.X.hom s.limitBaseChange.g)
        (integralComponentAt x.1).subschemeι k).1 y =
      ∑ x : cycleSupportIndex z, (z.1 x.1) *
        (cycleAssociatedToClosedSubscheme s.limitBaseChange.baseChange
          (pullback.snd s.X.hom s.limitBaseChange.g)
          (integralComponentAt x.1).subschemeι k).1 y := by
    simp [zsmul_eq_mul]
  rw [hsum, ← finsum_eq_sum_of_fintype]
  exact (cycle_eq_finsum_primeCycles z y).symm

/-! ### Eventual injectivity -/

/-- The identification of the objects of the inverse system of base changes of `X` with the
fibre products `X_i` carries the transition morphisms of the system to the transition morphisms
`X_i ⟶ X_j`. -/
private theorem stageSchemeDiagram_map_comp_stageSchemeObjectIso_hom {i j : I} (g : i ⟶ j) :
    s.stageSchemeDiagram.map g ≫ (s.stageSchemeObjectIso j).hom =
      (s.stageSchemeObjectIso i).hom ≫ s.stageTransition g := by
  apply pullback.hom_ext
  · rw [Category.assoc,
      show (s.stageSchemeObjectIso j).hom ≫ pullback.fst s.X.hom (s.stageToBase j) =
        pullback.snd (s.stageToBase j) s.X.hom from
          pullbackSymmetry_hom_comp_fst (s.stageToBase j) s.X.hom,
      Category.assoc, s.stageTransition_comp_fst g,
      show (s.stageSchemeObjectIso i).hom ≫ pullback.fst s.X.hom (s.stageToBase i) =
        pullback.snd (s.stageToBase i) s.X.hom from
          pullbackSymmetry_hom_comp_fst (s.stageToBase i) s.X.hom]
    exact pullback.lift_snd _ _ _
  · rw [Category.assoc,
      show (s.stageSchemeObjectIso j).hom ≫ pullback.snd s.X.hom (s.stageToBase j) =
        pullback.fst (s.stageToBase j) s.X.hom from
          pullbackSymmetry_hom_comp_snd (s.stageToBase j) s.X.hom,
      Category.assoc, s.stageTransition_comp_snd g, ← Category.assoc,
      show (s.stageSchemeObjectIso i).hom ≫ pullback.snd s.X.hom (s.stageToBase i) =
        pullback.fst (s.stageToBase i) s.X.hom from
          pullbackSymmetry_hom_comp_snd (s.stageToBase i) s.X.hom]
    exact pullback.lift_fst _ _ _

/-- **Stacks Project, Tag 0FVQ, eventual injectivity for cycle groups.** A `k`-cycle on `X_j`
whose image in `Z_k(X')` vanishes is annihilated by the transition to some finite stage
`X_i ⟶ X_j`.

A point of `X_j` carrying a nonzero coefficient cannot lie in the image of `X'`: otherwise the
base-changed cycle would have a nonzero coefficient at a generic point of the inverse image of
the reduced closure of that point, by
`Stacks.Chow.eq_zero_of_baseChangeCyclePullback_eq_zero_of_mem_range`. The cycle has finite
support because `X_j` is quasi-compact, and `X'` is the limit of the `X_i` along affine
transition morphisms, so finitely many points outside the image of `X'` are already outside the
image of a single `X_i`; every coefficient of the transition of the cycle to that stage is a
coefficient of the cycle at a point of that image, hence vanishes. -/
@[stacks 0FVQ "cycle groups, eventual injectivity: a k-cycle on X_j killed by base change to X'
is killed by some transition X_i -> X_j"]
theorem exists_transitionCyclePullback_eq_zero (j : I) (k : ℤ)
    (z : CycleGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k)
    (hz : s.stageCyclePullback j k z = 0) :
    ∃ (i : I) (f : i ⟶ j), s.transitionCyclePullback f k z = 0 := by
  classical
  have hinit : InitiallySmall.{u} I := CategoryTheory.initiallySmall_of_essentiallySmall I
  let _ {a b : I} (f : a ⟶ b) : IsAffineHom (s.stageSchemeDiagram.map f) :=
    s.stageSchemeTransition_isAffineHom f
  have hzlim : baseChangeCyclePullback (s.stageToLimitBaseChange j)
      (pullback.snd s.X.hom (s.stageToBase j)) k z = 0 :=
    baseChangeCyclePullback_eq_zero_of_isPullback (s.stageToLimitBaseChange j) rfl
      (pullback.snd s.X.hom (s.stageToBase j)) (s.isPullback_stageProjection j) k z hz
  have hsupp : ∀ x ∈ Function.support
      (z.1 : (pullback s.X.hom (s.stageToBase j) : Scheme.{u}) → ℤ),
      (s.stageSchemeObjectIso j).inv.base x ∉ Set.range (s.stageSchemeCone.π.app j).base := by
    rintro x hx ⟨y, hy⟩
    refine Function.mem_support.mp hx ?_
    have h2 : (s.stageSchemeObjectIso j).inv.base ((s.stageProjection j).base y) =
        (s.stageSchemeObjectIso j).inv.base x := by
      have h3 := congrArg (fun m : (pullback s.X.hom s.limitBaseChange.g : Scheme.{u}) ⟶
          s.stageSchemeDiagram.obj j ↦ m.base y)
        (s.stageProjection_comp_stageSchemeObjectIso_inv j)
      simpa only [Scheme.Hom.comp_apply] using h3.trans hy
    have h1 : (s.stageProjection j).base y = x := by
      have h4 := congrArg (s.stageSchemeObjectIso j).hom.base h2
      rwa [Scheme.inv_hom_apply, Scheme.inv_hom_apply] at h4
    refine eq_zero_of_baseChangeCyclePullback_eq_zero_of_mem_range
      (s.stageToLimitBaseChange j) (pullback.snd s.X.hom (s.stageToBase j)) k z hzlim x
      ⟨(s.isPullback_stageProjection j).isoPullback.hom.base y, ?_⟩
    rw [← h1]
    simpa only [Scheme.Hom.comp_apply] using congrArg
      (fun m : (pullback s.X.hom s.limitBaseChange.g : Scheme.{u}) ⟶
        (pullback s.X.hom (s.stageToBase j) : Scheme.{u}) ↦ m.base y)
      (s.isPullback_stageProjection j).isoPullback_hom_fst
  obtain ⟨i, g, hg⟩ := exists_forall_notMem_range_map_of_finite s.stageSchemeDiagram
    s.stageSchemeCone s.isLimit_stageSchemeCone j
    ((finite_support_of_compactSpace (s.stageSituation j)
      (pullback.snd s.X.hom (s.stageToBase j)) k z).image
      (s.stageSchemeObjectIso j).inv.base)
    (by rintro _ ⟨x, hx, rfl⟩; exact hsupp x hx)
  refine ⟨i, g, ?_⟩
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hy : z.1 ((s.stageTransition g).base y) = 0 := by
    by_contra hne
    refine hg ((s.stageSchemeObjectIso j).inv.base ((s.stageTransition g).base y))
      (Set.mem_image_of_mem _ (Function.mem_support.mpr hne))
      ⟨(s.stageSchemeObjectIso i).inv.base y, ?_⟩
    have hsq : (s.stageSchemeObjectIso j).hom.base
        ((s.stageSchemeDiagram.map g).base ((s.stageSchemeObjectIso i).inv.base y)) =
        (s.stageTransition g).base y := by
      have h5 := congrArg (fun m : s.stageSchemeDiagram.obj i ⟶
          (pullback s.X.hom (s.stageToBase j) : Scheme.{u}) ↦
          m.base ((s.stageSchemeObjectIso i).inv.base y))
        (s.stageSchemeDiagram_map_comp_stageSchemeObjectIso_hom g)
      simpa only [Scheme.Hom.comp_apply, Scheme.inv_hom_apply] using h5
    rw [← hsq, Scheme.hom_inv_apply]
  rw [transitionCyclePullback,
    baseChangeCyclePullbackOfIsPullback_apply' (s.transitionBaseChange g) rfl
      (pullback.snd s.X.hom (s.stageToBase j)) (s.isPullback_stageTransition g) k z y,
    hy, zero_mul]
  rfl

end FilteredBaseChangeSystem

end Stacks.Chow

end
