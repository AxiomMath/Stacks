module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-! # Nonempty finite limits

Stacks 04AU: a category has all finite limits indexed by a *nonempty* diagram iff it has binary
products and equalizers, iff it has binary products and pullbacks.
`HasNonemptyFiniteLimits` packages the hypothesis and `nonempty_finite_limits_tfae` states the
equivalence. The substantive direction builds discrete limits over `Fin (n + 1)` by induction —
the base case `finOneCone` and the step `optionCone`, which pairs `F.obj ⟨none⟩` with the limit
over the remaining index — transfers them to any finite nonempty index type along
`Discrete.equivalence`, and then uses `hasLimit_of_equalizer_and_product`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C]

/--
`HasNonemptyFiniteLimits C` says that the category `C` has all limits of shape `J`
where `J` is a small, finite, nonempty category. Equivalently, all finite limits
indexed by a nonempty diagram exist in `C`.
-/
@[sga "4 Vbis 5.1.0"]
class HasNonemptyFiniteLimits : Prop where
  out : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J], HasLimitsOfShape J C

/-! ### Step 1: From nonempty finite limits to binary products and equalizers. -/

/-- **Stacks 04AU**, direction `1 → 2` (first half). Binary products are the limits of shape
`Discrete WalkingPair`, which is finite and nonempty, so they are among the limits granted by
`HasNonemptyFiniteLimits`. -/
lemma hasBinaryProducts_of_hasNonemptyFiniteLimits
    [HasNonemptyFiniteLimits C] : HasBinaryProducts C :=
  HasNonemptyFiniteLimits.out (Discrete WalkingPair)

/-- **Stacks 04AU**, direction `1 → 2` (second half). Equalizers are the limits of shape
`WalkingParallelPair`, which is finite and nonempty. -/
lemma hasEqualizers_of_hasNonemptyFiniteLimits
    [HasNonemptyFiniteLimits C] : HasEqualizers C :=
  HasNonemptyFiniteLimits.out WalkingParallelPair

/-! ### Step 2: From binary products and equalizers to nonempty finite limits. -/

/-- The candidate limit cone for any functor `F : Discrete (Fin 1) ⥤ C` has apex
`F.obj ⟨⟨0, _⟩⟩` with projections defined via the unique morphism `i = 0` in `Fin 1`. -/
@[implicit_reducible]
def finOneCone (F : Discrete (Fin 1) ⥤ C) : Cone F where
  pt := F.obj ⟨⟨0, by omega⟩⟩
  π := Discrete.natTrans fun ⟨⟨_, _⟩⟩ => F.map ⟨by omega⟩

/-- The candidate cone `finOneCone C F` is a limit cone. -/
def isLimitFinOneCone (F : Discrete (Fin 1) ⥤ C) : IsLimit (finOneCone C F) where
  lift s := s.π.app ⟨⟨0, by omega⟩⟩
  fac := by
    rintro s ⟨⟨i, _⟩⟩
    obtain rfl : i = 0 := by omega
    simp [finOneCone, Discrete.natTrans]
  uniq := by
    rintro s m h
    simpa [finOneCone, Discrete.natTrans] using h ⟨⟨0, by omega⟩⟩

/-- Base case of the induction on `n` producing discrete limits over `Fin (n + 1)`: a one-object
product is its unique factor, witnessed by `finOneCone` and `isLimitFinOneCone`. Needs no
hypothesis on `C`. -/
lemma hasLimitsOfShape_discrete_fin_one : HasLimitsOfShape (Discrete (Fin 1)) C :=
  ⟨fun F => ⟨⟨⟨finOneCone C F, isLimitFinOneCone C F⟩⟩⟩⟩

/-- Restriction of `F : Discrete (Option α) ⥤ C` to `Discrete α` along `some`. -/
@[implicit_reducible]
noncomputable def auxFunctor {α : Type} (F : Discrete (Option α) ⥤ C) :
    Discrete α ⥤ C :=
  Discrete.functor fun i => F.obj ⟨some i⟩

/-- The candidate limit cone for `F : Discrete (Option α) ⥤ C` with apex
`F.obj ⟨none⟩ ⨯ limit (auxFunctor F)`. -/
@[implicit_reducible]
noncomputable def optionCone [HasBinaryProducts C] {α : Type}
    [HasLimitsOfShape (Discrete α) C] (F : Discrete (Option α) ⥤ C) : Cone F where
  pt := F.obj ⟨none⟩ ⨯ limit (auxFunctor C F)
  π := Discrete.natTrans fun
    | ⟨none⟩ => prod.fst
    | ⟨some i⟩ => prod.snd ≫ limit.π (auxFunctor C F) ⟨i⟩

/-- The leg of `optionCone C F` at `none` is the first projection `prod.fst`. -/
lemma optionCone_π_app_none [HasBinaryProducts C] {α : Type}
    [HasLimitsOfShape (Discrete α) C] (F : Discrete (Option α) ⥤ C) :
    (optionCone C F).π.app ⟨none⟩ = prod.fst :=
  rfl

/-- The leg of `optionCone C F` at `some i` is `prod.snd` followed by the limit projection
`limit.π (auxFunctor C F) ⟨i⟩`. -/
lemma optionCone_π_app_some [HasBinaryProducts C] {α : Type}
    [HasLimitsOfShape (Discrete α) C] (F : Discrete (Option α) ⥤ C) (i : α) :
    (optionCone C F).π.app ⟨some i⟩ = prod.snd ≫ limit.π (auxFunctor C F) ⟨i⟩ :=
  rfl

/-- Auxiliary cone over `auxFunctor C F` built from a cone `s` over `F`. -/
@[implicit_reducible]
noncomputable def restrictedCone {α : Type} (F : Discrete (Option α) ⥤ C)
    (s : Cone F) : Cone (auxFunctor C F) where
  pt := s.pt
  π := Discrete.natTrans fun ⟨i⟩ => s.π.app ⟨some i⟩

/-- The candidate lift for the limit construction. -/
noncomputable def optionLift [HasBinaryProducts C] {α : Type}
    [HasLimitsOfShape (Discrete α) C] (F : Discrete (Option α) ⥤ C)
    (s : Cone F) : s.pt ⟶ (optionCone C F).pt :=
  prod.lift (s.π.app ⟨none⟩) (limit.lift (auxFunctor C F) (restrictedCone C F s))

/-- The candidate cone `optionCone C F` is a limit cone. -/
noncomputable def isLimitOptionCone [HasBinaryProducts C] {α : Type}
    [HasLimitsOfShape (Discrete α) C] (F : Discrete (Option α) ⥤ C) :
    IsLimit (optionCone C F) := by
  refine ⟨optionLift C F, ?_, ?_⟩
  · rintro s ⟨j⟩
    have hL_fst : optionLift C F s ≫ prod.fst = s.π.app ⟨none⟩ := by
      unfold optionLift; exact prod.lift_fst _ _
    have hL_snd : optionLift C F s ≫ prod.snd =
                limit.lift (auxFunctor C F) (restrictedCone C F s) := by
      unfold optionLift; exact prod.lift_snd _ _
    cases j with
    | none =>
      rw [optionCone_π_app_none]
      exact hL_fst
    | some i =>
      rw [optionCone_π_app_some, ← Category.assoc, hL_snd]
      exact limit.lift_π (restrictedCone C F s) ⟨i⟩
  · rintro s m h
    have hL_fst : optionLift C F s ≫ prod.fst = s.π.app ⟨none⟩ := by
      unfold optionLift; exact prod.lift_fst _ _
    have hL_snd : optionLift C F s ≫ prod.snd =
                limit.lift (auxFunctor C F) (restrictedCone C F s) := by
      unfold optionLift; exact prod.lift_snd _ _
    refine Limits.prod.hom_ext ?_ ?_
    · have h0 : m ≫ prod.fst = s.π.app ⟨none⟩ := h ⟨none⟩
      exact h0.trans hL_fst.symm
    · refine limit.hom_ext fun ⟨i⟩ => ?_
      have hi : m ≫ prod.snd ≫ limit.π (auxFunctor C F) ⟨i⟩ = s.π.app ⟨some i⟩ := h ⟨some i⟩
      have h_left : (m ≫ prod.snd) ≫ limit.π (auxFunctor C F) ⟨i⟩ = s.π.app ⟨some i⟩ := by
        rw [Category.assoc]; exact hi
      have h_right : (optionLift C F s ≫ prod.snd) ≫ limit.π (auxFunctor C F) ⟨i⟩ =
          s.π.app ⟨some i⟩ := by
        rw [hL_snd]; exact limit.lift_π (restrictedCone C F s) ⟨i⟩
      exact h_left.trans h_right.symm

/-- Induction step for discrete limits: a product indexed by `Option α` is the binary product of
the `none` factor with a product indexed by `α`, so one binary product extends
`Discrete α`-limits to `Discrete (Option α)`-limits (`optionCone`, `isLimitOptionCone`). -/
lemma hasLimitsOfShape_discrete_option
    [HasBinaryProducts C] (α : Type) [HasLimitsOfShape (Discrete α) C] :
    HasLimitsOfShape (Discrete (Option α)) C :=
  ⟨fun F => HasLimit.mk ⟨optionCone C F, isLimitOptionCone C F⟩⟩

/-- Products indexed by `Fin (n + 1)` exist as soon as binary products do: induction on `n`, with
`hasLimitsOfShape_discrete_fin_one` as base case and the step transported along
`finSuccEquiv (k + 1) : Fin (k + 2) ≃ Option (Fin (k + 1))`. -/
lemma hasLimitsOfShape_discrete_fin_succ [HasBinaryProducts C] (n : ℕ) :
    HasLimitsOfShape (Discrete (Fin (n + 1))) C := by
  induction n with
  | zero => exact hasLimitsOfShape_discrete_fin_one C
  | succ k _ =>
    have : HasLimitsOfShape (Discrete (Option (Fin (k + 1)))) C :=
      hasLimitsOfShape_discrete_option C (Fin (k + 1))
    exact hasLimitsOfShape_of_equivalence (Discrete.equivalence (finSuccEquiv (k + 1)).symm)

/-- Products indexed by an arbitrary nonempty finite type `ι`: such an `ι` is equivalent to
`Fin (n + 1)` for `n + 1 = Fintype.card ι`, so `hasLimitsOfShape_discrete_fin_succ` transports
along `Discrete.equivalence`. -/
@[ega "I 3.3.5" "more general"]
lemma hasProductsOfShape_of_finite_nonempty
    [HasBinaryProducts C] (ι : Type) [Finite ι] [Nonempty ι] :
    HasLimitsOfShape (Discrete ι) C := by
  let := Fintype.ofFinite ι
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 :=
    ⟨Fintype.card ι - 1, by have := Fintype.card_pos (α := ι); omega⟩
  have := hasLimitsOfShape_discrete_fin_succ C n
  exact hasLimitsOfShape_of_equivalence
    (Discrete.equivalence ((finCongr hn.symm).trans (Fintype.equivFin ι).symm))

/-- **Stacks 04AU**, direction `2 → 1`, the substantive one. For a finite nonempty `J`, both index
types of the standard equalizer-of-products presentation of a limit — `J` itself and
`Σ p : J × J, p.1 ⟶ p.2`, nonempty because it contains `𝟙 j` — admit products by
`hasProductsOfShape_of_finite_nonempty`, so `hasLimit_of_equalizer_and_product` applies. -/
lemma hasNonemptyFiniteLimits_of_hasBinaryProducts_and_hasEqualizers
    [HasBinaryProducts C] [HasEqualizers C] : HasNonemptyFiniteLimits C := by
  refine ⟨fun J _ _ _ => ⟨fun F => ?_⟩⟩
  have : Fintype J := FinCategory.fintypeObj
  have := hasProductsOfShape_of_finite_nonempty C J
  have : Nonempty (Σ p : J × J, p.1 ⟶ p.2) :=
    let ⟨j⟩ := ‹Nonempty J›
    ⟨⟨(j, j), 𝟙 j⟩⟩
  have := hasProductsOfShape_of_finite_nonempty C (Σ p : J × J, p.1 ⟶ p.2)
  exact hasLimit_of_equalizer_and_product F

/-! ### Main statement. -/

/-- **Stacks 04AU**. For a category `C`, having every limit indexed by a finite nonempty shape is
equivalent to having binary products together with equalizers, and equivalent to having binary
products together with pullbacks. -/
@[stacks 04AU]
theorem nonempty_finite_limits_tfae :
    List.TFAE
      [ HasNonemptyFiniteLimits C,
        HasBinaryProducts C ∧ HasEqualizers C,
        HasBinaryProducts C ∧ HasPullbacks C ] := by
  tfae_have 1 → 2 := fun _ =>
    ⟨hasBinaryProducts_of_hasNonemptyFiniteLimits C,
      hasEqualizers_of_hasNonemptyFiniteLimits C⟩
  tfae_have 2 → 1 := fun ⟨_, _⟩ =>
    hasNonemptyFiniteLimits_of_hasBinaryProducts_and_hasEqualizers C
  tfae_have 2 → 3 := fun ⟨_, _⟩ =>
    ⟨inferInstance, hasPullbacks_of_hasBinaryProducts_of_hasEqualizers C⟩
  tfae_have 3 → 2 := fun ⟨_, _⟩ =>
    ⟨inferInstance, hasEqualizers_of_hasPullbacks_and_binary_products⟩
  tfae_finish

