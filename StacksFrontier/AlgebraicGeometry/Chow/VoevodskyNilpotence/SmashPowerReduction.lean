module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtensionFiniteStageDivisibility
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FiniteFieldExtensionDivisibility
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerExpansion
public import StacksFrontier.AlgebraicGeometry.ClosurePointDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.ProjectiveDivisorReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsBaseChange
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsClosedImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsDimensionZero

/-!
# The two reduction steps of Stacks 0FH9

Stacks 0FH9 (Voevodsky's smash nilpotence for zero-cycles) says that for `X` smooth,
geometrically irreducible and projective over a field `k` and two `k`-rational points `x, x'`,
the exterior powers `([x] - [x'])^{×n}` in `CH_0(X^n)` are torsion for `n` large. Its proof
reduces twice before doing any work:

1. **to `k` algebraically closed**: if the statement holds after base change to an algebraic
   closure `K` of `k`, it holds over `k`, because the kernel of `CH_0(X^n) ⟶ CH_0(X^n_K)` is
   torsion (Stacks 0FH8);
2. **to a curve**: over an algebraically closed field, of dimension at least one, `x` and `x'`
   lie on a smooth projective curve `C ⊆ X` (Bertini), and pushing forward along
   `C^n ⟶ X^n` carries the smash powers on `C` to those on `X`.

This file proves both, so that 0FH9 follows from its curve case,
`Stacks.Chow.SmashNilpotenceCurveCase`.

## Main definitions

* `Stacks.Chow.SmashNilpotenceCurveCase`: the curve case of 0FH9, over an algebraically closed
  field.
* `Stacks.Chow.smashClosedImmersion`: the closed immersion `C^n ⟶ X^n` induced by `C ⊆ X`.
* `Stacks.Chow.smashBaseChangeProjection`: the projection `(X_K)^n ⟶ X^n`, which exhibits
  `(X_K)^n` as the base change of `X^n` (`Stacks.Chow.isPullback_smashBaseChangeProjection`).

## Main results

* `Stacks.Chow.smashPointDifference_cycle_eq_chowPushforwardOfIsClosedImmersion`: the smash power
  on `X` is the pushforward of the smash power on `C`.
* `Stacks.Chow.baseChangeChowPullbackOfIsPullback_smashPointDifference`: the base change of the
  smash power over `k` is the smash power over `K` of the base-changed points.
* `Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_baseChange`: torsion descends along an
  algebraic extension.
* `Stacks.Chow.exists_isOfFinAddOrder_smashPointDifference_of_isAlgClosed`: 0FH9 over an
  algebraically closed field, from the curve case.
* `Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_curveCase`: 0FH9, from the curve case.

## Implementation notes

Both compatibilities are reduced to rational points by the expansion
`Stacks.Chow.smashPointDifference_cycle_eq_sum`, which writes the `n`-th smash power as the signed
sum of the classes of the `2^n` rational points of `X^n` with coordinates in `{x, x'}`. Pushforward
along a closed immersion and base change along a field extension both carry the class of a
rational point to the class of the corresponding rational point
(`Stacks.WeilCohomology.chowPushforwardOfIsClosedImmersion_rationalPointChowClass`,
`Stacks.WeilCohomology.baseChangeChowPullbackOfIsPullback_rationalPointChowClass`), so no
compatibility of the exterior product with base change or pushforward in general is needed.

The descent uses Stacks 0FH8 in the form it is proved in: base change to a finite subextension
`E/k` already kills a multiple of the class, by
`Stacks.Chow.exists_finiteSubextension_baseChangeChowPullback_eq_zsmul`, and push-pull along
`E/k`, by
`Stacks.Chow.exists_finrank_zsmul_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul`,
kills a further multiple over `k`.

H-projectivity is `AlgebraicGeometry.IsProjectiveMorphism`. The curve case enters as the
hypothesis `Stacks.Chow.SmashNilpotenceCurveCase`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0FH8](https://stacks.math.columbia.edu/tag/0FH8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology

attribute [local instance] SmashPowerData.finiteType

/-- A lift followed by a map of pullbacks is the lift of the composites. -/
private theorem pullback_lift_comp_map {X Y Z X' Y' Z' W : Scheme.{u}} (f₁ : X ⟶ Z) (g₁ : Y ⟶ Z)
    (f₂ : X' ⟶ Z') (g₂ : Y' ⟶ Z') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
    (e₁ : f₁ ≫ i₃ = i₁ ≫ f₂) (e₂ : g₁ ≫ i₃ = i₂ ≫ g₂) (a : W ⟶ X) (b : W ⟶ Y)
    (h : a ≫ f₁ = b ≫ g₁) :
    pullback.lift a b h ≫ pullback.map f₁ g₁ f₂ g₂ i₁ i₂ i₃ e₁ e₂ =
      pullback.lift (a ≫ i₁) (b ≫ i₂) (by simp only [Category.assoc, ← e₁, ← e₂, reassoc_of% h]) :=
  by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]

/-! ### Pushforward along a closed immersion -/

section Pushforward

variable (k : Type u) [Field k] {X C : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType f] (ι : C ⟶ X) [IsClosedImmersion ι]
  (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)
  (xC xC' : (fieldChowSituation k).S ⟶ C) (hxC : xC ≫ ι ≫ f = 𝟙 _) (hxC' : xC' ≫ ι ≫ f = 𝟙 _)

/-- The closed immersions `C^n ⟶ X^n` induced by a closed immersion `ι : C ⟶ X` over `k`, on the
fibre powers carrying the smash powers, bundled with their compatibility with the structure
morphisms. -/
def smashClosedImmersionAux : (n : ℕ) →
    { j : (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).Y.left ⟶
        (smashPointDifference k f x x' hx hx' n).Y.left //
      j ≫ (smashPointDifference k f x x' hx hx' n).Y.hom =
          (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).Y.hom ∧ IsClosedImmersion j }
  | 0 => ⟨𝟙 _, Category.id_comp _, inferInstanceAs (IsClosedImmersion (𝟙 (fieldChowSituation k).S))⟩
  | n + 1 =>
    let j := smashClosedImmersionAux n
    ⟨pullback.map (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).Y.hom (ι ≫ f)
        (smashPointDifference k f x x' hx hx' n).Y.hom f j.1 ι (𝟙 _)
        (by rw [Category.comp_id, j.2.1]) (Category.comp_id _), by
      change pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ _ = pullback.fst _ _ ≫ _
      rw [pullback.lift_fst_assoc, Category.assoc, j.2.1], by
      have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
        MorphismProperty.IsMultiplicative.toIsStableUnderComposition
      exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) j.2.2 inferInstance
        j.2.1.symm rfl⟩

/-- The closed immersion `ι^n : C^n ⟶ X^n`. -/
def smashClosedImmersion (n : ℕ) :
    (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).Y.left ⟶
      (smashPointDifference k f x x' hx hx' n).Y.left :=
  (smashClosedImmersionAux k f ι x x' hx hx' xC xC' hxC hxC' n).1

/-- `ι^n` is a morphism over `k`. -/
theorem smashClosedImmersion_comp (n : ℕ) :
    smashClosedImmersion k f ι x x' hx hx' xC xC' hxC hxC' n ≫
        (smashPointDifference k f x x' hx hx' n).Y.hom =
      (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).Y.hom :=
  (smashClosedImmersionAux k f ι x x' hx hx' xC xC' hxC hxC' n).2.1

/-- `ι^n` is a closed immersion. -/
instance (n : ℕ) : IsClosedImmersion (smashClosedImmersion k f ι x x' hx hx' xC xC' hxC hxC' n) :=
  (smashClosedImmersionAux k f ι x x' hx hx' xC xC' hxC hxC' n).2.2

/-- The recursion defining `ι^n`: `ι^{n+1} = ι^n × ι`. -/
theorem smashClosedImmersion_succ (n : ℕ) :
    smashClosedImmersion k f ι x x' hx hx' xC xC' hxC hxC' (n + 1) =
      pullback.map (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).Y.hom (ι ≫ f)
        (smashPointDifference k f x x' hx hx' n).Y.hom f
        (smashClosedImmersion k f ι x x' hx hx' xC xC' hxC hxC' n) ι (𝟙 _)
        (by rw [Category.comp_id, smashClosedImmersion_comp]) (Category.comp_id _) :=
  rfl

/-- `ι^n` carries the rational point `P_s` of `C^n` built from `x_C, x'_C` to the rational point
`P_s` of `X^n` built from `x, x'`. -/
theorem smashPoint_comp_smashClosedImmersion (hfac : xC ≫ ι = x) (hfac' : xC' ≫ ι = x')
    (n : ℕ) (s : Fin n → Bool) :
    smashPoint k (ι ≫ f) xC xC' hxC hxC' n s ≫
        smashClosedImmersion k f ι x x' hx hx' xC xC' hxC hxC' n =
      smashPoint k f x x' hx hx' n s := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
    refine (pullback_lift_comp_map
      (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).Y.hom (ι ≫ f)
      (smashPointDifference k f x x' hx hx' n).Y.hom f
      (smashClosedImmersion k f ι x x' hx hx' xC xC' hxC hxC' n) ι (𝟙 _)
      (by rw [Category.comp_id, smashClosedImmersion_comp]) (Category.comp_id _)
      (smashPoint k (ι ≫ f) xC xC' hxC hxC' n (Fin.init s)) (cond (s (Fin.last n)) xC' xC)
      ((smashPoint_comp k (ι ≫ f) xC xC' hxC hxC' n _).trans
        (cond_comp_eq_id k (ι ≫ f) xC xC' hxC hxC' _).symm)).trans ?_
    change _ = pullback.lift _ _ _
    congr 1
    · exact ih _
    · cases s (Fin.last n) <;> assumption

/-- **The smash power on `X` is the pushforward of the smash power on `C`.** For a closed
immersion `ι : C ⟶ X` over `k` and rational points `x_C, x'_C` of `C` over `x, x'`,

  `([x] - [x'])^{×n} = (ι^n)_* ([x_C] - [x'_C])^{×n}` in `CH_0(X^n)`. -/
theorem smashPointDifference_cycle_eq_chowPushforwardOfIsClosedImmersion
    (hfac : xC ≫ ι = x) (hfac' : xC' ≫ ι = x') (n : ℕ) :
    (smashPointDifference k f x x' hx hx' n).cycle =
      chowPushforwardOfIsClosedImmersion (fieldChowSituation k)
        (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).Y.hom
        (smashPointDifference k f x x' hx hx' n).Y.hom
        (smashClosedImmersion k f ι x x' hx hx' xC xC' hxC hxC' n)
        (smashClosedImmersion_comp k f ι x x' hx hx' xC xC' hxC hxC' n) 0
        (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).cycle := by
  rw [smashPointDifference_cycle_eq_sum, smashPointDifference_cycle_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_zsmul, chowPushforwardOfIsClosedImmersion_rationalPointChowClass k _ _ _
    (smashClosedImmersion_comp k f ι x x' hx hx' xC xC' hxC hxC' n) _
    (smashPoint_comp k (ι ≫ f) xC xC' hxC hxC' n s) _
    (smashPoint_comp_smashClosedImmersion k f ι x x' hx hx' xC xC' hxC hxC' hfac hfac' n s)
    (smashPoint_comp k f x x' hx hx' n s)]

/-- Torsion of a smash power on a closed subscheme `C ⊆ X` through the two points implies torsion
of the smash power on `X`. -/
theorem isOfFinAddOrder_smashPointDifference_of_closedImmersion
    (hfac : xC ≫ ι = x) (hfac' : xC' ≫ ι = x') (n : ℕ)
    (h : IsOfFinAddOrder (smashPointDifference k (ι ≫ f) xC xC' hxC hxC' n).cycle) :
    IsOfFinAddOrder (smashPointDifference k f x x' hx hx' n).cycle := by
  rw [smashPointDifference_cycle_eq_chowPushforwardOfIsClosedImmersion k f ι x x' hx hx' xC xC'
    hxC hxC' hfac hfac' n]
  exact AddMonoidHom.isOfFinAddOrder _ h

end Pushforward

/-! ### Base change along a field extension -/

section BaseChange

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
  (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)

/-- The rational point of `X_K` induced by a rational point of `X`. -/
abbrev fieldBaseChangePoint (y : (fieldChowSituation k).S ⟶ X) (hy : y ≫ f = 𝟙 _) :
    (fieldChowSituation K).S ⟶ pullback f (fieldExtensionBaseChangeSituation k K).g :=
  pullback.lift ((fieldExtensionBaseChangeSituation k K).g ≫ y) (𝟙 _)
    (by rw [Category.assoc, hy, Category.comp_id, Category.id_comp])

omit [LocallyOfFiniteType f] in
/-- The induced point of `X_K` is a `K`-rational point. -/
theorem fieldBaseChangePoint_comp (y : (fieldChowSituation k).S ⟶ X) (hy : y ≫ f = 𝟙 _) :
    fieldBaseChangePoint k K f y hy ≫ pullback.snd f (fieldExtensionBaseChangeSituation k K).g =
      𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The smash powers over `K` of the base-changed points, on `(X_K)^n`. -/
abbrev smashPointDifferenceBaseChange (n : ℕ) : SmashPowerData K :=
  smashPointDifference K (pullback.snd f (fieldExtensionBaseChangeSituation k K).g)
    (fieldBaseChangePoint k K f x hx) (fieldBaseChangePoint k K f x' hx')
    (fieldBaseChangePoint_comp k K f x hx) (fieldBaseChangePoint_comp k K f x' hx') n

/-- The projections `(X_K)^n ⟶ X^n`, bundled with their compatibility with the structure
morphisms. -/
def smashBaseChangeProjectionAux : (n : ℕ) →
    { pr : (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.left ⟶
        (smashPointDifference k f x x' hx hx' n).Y.left //
      pr ≫ (smashPointDifference k f x x' hx hx' n).Y.hom =
        (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.hom ≫
          (fieldExtensionBaseChangeSituation k K).g }
  | 0 => ⟨(fieldExtensionBaseChangeSituation k K).g,
      (Category.comp_id _).trans (Category.id_comp _).symm⟩
  | n + 1 =>
    let pr := smashBaseChangeProjectionAux n
    ⟨pullback.map (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.hom
        (pullback.snd f (fieldExtensionBaseChangeSituation k K).g)
        (smashPointDifference k f x x' hx hx' n).Y.hom f pr.1
        (pullback.fst f (fieldExtensionBaseChangeSituation k K).g)
        (fieldExtensionBaseChangeSituation k K).g pr.2.symm pullback.condition.symm, by
      change pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ _ = (pullback.fst _ _ ≫ _) ≫ _
      rw [pullback.lift_fst_assoc, Category.assoc, pr.2, Category.assoc]⟩

/-- The projection `(X_K)^n ⟶ X^n`. -/
def smashBaseChangeProjection (n : ℕ) :
    (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.left ⟶
      (smashPointDifference k f x x' hx hx' n).Y.left :=
  (smashBaseChangeProjectionAux k K f x x' hx hx' n).1

/-- The projection `(X_K)^n ⟶ X^n` lies over `Spec K ⟶ Spec k`. -/
theorem smashBaseChangeProjection_comp (n : ℕ) :
    smashBaseChangeProjection k K f x x' hx hx' n ≫
        (smashPointDifference k f x x' hx hx' n).Y.hom =
      (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.hom ≫
        (fieldExtensionBaseChangeSituation k K).g :=
  (smashBaseChangeProjectionAux k K f x x' hx hx' n).2

/-- **`(X_K)^n` is the base change of `X^n`.** The square formed by the projection
`(X_K)^n ⟶ X^n`, the two structure morphisms and `Spec K ⟶ Spec k` is cartesian. -/
theorem isPullback_smashBaseChangeProjection (n : ℕ) :
    IsPullback (smashBaseChangeProjection k K f x x' hx hx' n)
      (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.hom
      (smashPointDifference k f x x' hx hx' n).Y.hom (fieldExtensionBaseChangeSituation k K).g := by
  induction n with
  | zero =>
    have : IsIso (smashPointDifferenceBaseChange k K f x x' hx hx' 0).Y.hom :=
      inferInstanceAs (IsIso (𝟙 (fieldChowSituation K).S))
    have : IsIso (smashPointDifference k f x x' hx hx' 0).Y.hom :=
      inferInstanceAs (IsIso (𝟙 (fieldChowSituation k).S))
    exact IsPullback.of_vert_isIso ⟨smashBaseChangeProjection_comp k K f x x' hx hx' 0⟩
  | succ n ih =>
    set g := (fieldExtensionBaseChangeSituation k K).g
    set YK := smashPointDifferenceBaseChange k K f x x' hx hx' n
    set Y := smashPointDifference k f x x' hx hx' n
    set pr := smashBaseChangeProjection k K f x x' hx hx' n
    have hpr := smashBaseChangeProjection_comp k K f x x' hx hx' n
    let m := pullback.map YK.Y.hom (pullback.snd f g) Y.Y.hom f pr (pullback.fst f g) g
      hpr.symm pullback.condition.symm
    have hm₂ : m ≫ pullback.snd Y.Y.hom f =
        pullback.snd YK.Y.hom (pullback.snd f g) ≫ pullback.fst f g :=
      pullback.lift_snd _ _ _
    have outer : IsPullback (m ≫ pullback.snd Y.Y.hom f)
        (pullback.fst YK.Y.hom (pullback.snd f g)) f (pr ≫ Y.Y.hom) := by
      rw [hm₂, hpr]
      exact (IsPullback.of_hasPullback YK.Y.hom (pullback.snd f g)).flip.paste_horiz
        (IsPullback.of_hasPullback f g)
    exact (IsPullback.of_right outer (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback Y.Y.hom f).flip).paste_vert ih

/-- The projection `(X_K)^n ⟶ X^n` carries the point `P_s` built from the base-changed points to
the base change of the point `P_s` built from `x, x'`. -/
theorem smashPoint_comp_smashBaseChangeProjection (n : ℕ) (s : Fin n → Bool) :
    smashPoint K (pullback.snd f (fieldExtensionBaseChangeSituation k K).g)
        (fieldBaseChangePoint k K f x hx) (fieldBaseChangePoint k K f x' hx')
        (fieldBaseChangePoint_comp k K f x hx) (fieldBaseChangePoint_comp k K f x' hx') n s ≫
        smashBaseChangeProjection k K f x x' hx hx' n =
      (fieldExtensionBaseChangeSituation k K).g ≫ smashPoint k f x x' hx hx' n s := by
  induction n with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ n ih =>
    set g := (fieldExtensionBaseChangeSituation k K).g
    refine (pullback_lift_comp_map
      (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.hom (pullback.snd f g)
      (smashPointDifference k f x x' hx hx' n).Y.hom f
      (smashBaseChangeProjection k K f x x' hx hx' n) (pullback.fst f g) g
      (smashBaseChangeProjection_comp k K f x x' hx hx' n).symm pullback.condition.symm
      (smashPoint K (pullback.snd f g) (fieldBaseChangePoint k K f x hx)
        (fieldBaseChangePoint k K f x' hx') (fieldBaseChangePoint_comp k K f x hx)
        (fieldBaseChangePoint_comp k K f x' hx') n (Fin.init s))
      (cond (s (Fin.last n)) (fieldBaseChangePoint k K f x' hx') (fieldBaseChangePoint k K f x hx))
      ((smashPoint_comp K (pullback.snd f g) _ _ (fieldBaseChangePoint_comp k K f x hx)
        (fieldBaseChangePoint_comp k K f x' hx') n _).trans
        (cond_comp_eq_id K (pullback.snd f g) _ _ (fieldBaseChangePoint_comp k K f x hx)
          (fieldBaseChangePoint_comp k K f x' hx') _).symm)).trans ?_
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ih]
      exact (congrArg (g ≫ ·) (smashPoint_succ_fst k f x x' hx hx' n s)).symm.trans
        (Category.assoc _ _ _).symm
    · rw [pullback.lift_snd]
      refine (?_ : _ = g ≫ cond (s (Fin.last n)) x' x).trans
        ((congrArg (g ≫ ·) (smashPoint_succ_snd k f x x' hx hx' n s)).symm.trans
          (Category.assoc _ _ _).symm)
      cases s (Fin.last n) <;> exact pullback.lift_fst _ _ _

/-- The identification of `(X_K)^n` with the base change `X^n ×_k K` of `X^n`. -/
abbrev smashBaseChangeIso (n : ℕ) :
    (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.left ≅
      pullback (smashPointDifference k f x x' hx hx' n).Y.hom
        (fieldExtensionBaseChangeSituation k K).g :=
  (isPullback_smashBaseChangeProjection k K f x x' hx hx' n).isoPullback

/-- The identification `(X_K)^n ≅ X^n ×_k K` is an isomorphism over `K`. -/
theorem smashBaseChangeIso_hom_snd (n : ℕ) :
    (smashBaseChangeIso k K f x x' hx hx' n).hom ≫
        pullback.snd (smashPointDifference k f x x' hx hx' n).Y.hom
          (fieldExtensionBaseChangeSituation k K).g =
      (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.hom :=
  IsPullback.isoPullback_hom_snd _

/-- **Base change of a smash power is the smash power of the base-changed points.** The base
change to `K` of `([x] - [x'])^{×n}` in `CH_0(X^n ×_k K)` is, under the identification
`(X_K)^n ≅ X^n ×_k K`, the `n`-th smash power of `[x_K] - [x'_K]`. -/
theorem baseChangeChowPullbackOfIsPullback_smashPointDifference (n : ℕ) :
    baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl
        (smashPointDifference k f x x' hx hx' n).Y.hom
        (IsPullback.of_hasPullback (smashPointDifference k f x x' hx hx' n).Y.hom
          (fieldExtensionBaseChangeSituation k K).g) 0
        (smashPointDifference k f x x' hx hx' n).cycle =
      chowPushforwardOfIsClosedImmersion (fieldChowSituation K)
        (smashPointDifferenceBaseChange k K f x x' hx hx' n).Y.hom
        (pullback.snd (smashPointDifference k f x x' hx hx' n).Y.hom
          (fieldExtensionBaseChangeSituation k K).g)
        (smashBaseChangeIso k K f x x' hx hx' n).hom
        (smashBaseChangeIso_hom_snd k K f x x' hx hx' n) 0
        (smashPointDifferenceBaseChange k K f x x' hx hx' n).cycle := by
  rw [smashPointDifference_cycle_eq_sum, smashPointDifference_cycle_eq_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  set e := smashBaseChangeIso k K f x x' hx hx' n
  set P := smashPoint K (pullback.snd f (fieldExtensionBaseChangeSituation k K).g)
    (fieldBaseChangePoint k K f x hx) (fieldBaseChangePoint k K f x' hx')
    (fieldBaseChangePoint_comp k K f x hx) (fieldBaseChangePoint_comp k K f x' hx') n s
  have hP := smashPoint_comp K (pullback.snd f (fieldExtensionBaseChangeSituation k K).g)
    (fieldBaseChangePoint k K f x hx) (fieldBaseChangePoint k K f x' hx')
    (fieldBaseChangePoint_comp k K f x hx) (fieldBaseChangePoint_comp k K f x' hx') n s
  have hy : (P ≫ e.hom) ≫ pullback.snd (smashPointDifference k f x x' hx hx' n).Y.hom
      (fieldExtensionBaseChangeSituation k K).g = 𝟙 _ := by
    rwa [Category.assoc, smashBaseChangeIso_hom_snd]
  have hxy : (P ≫ e.hom) ≫ pullback.fst (smashPointDifference k f x x' hx hx' n).Y.hom
      (fieldExtensionBaseChangeSituation k K).g =
        (fieldExtensionBaseChangeSituation k K).g ≫ smashPoint k f x x' hx hx' n s := by
    rw [Category.assoc, IsPullback.isoPullback_hom_fst]
    exact smashPoint_comp_smashBaseChangeProjection k K f x x' hx hx' n s
  rw [map_zsmul, map_zsmul, baseChangeChowPullbackOfIsPullback_rationalPointChowClass k K _ _ _
      (smashPoint_comp k f x x' hx hx' n s) _ hy hxy,
    chowPushforwardOfIsClosedImmersion_rationalPointChowClass K _ _ _ _ _ hP _ rfl hy]

/-- The fibre powers carrying the smash powers are quasi-compact over `k` when `X` is. -/
theorem quasiCompact_smashPointDifference [QuasiCompact f] :
    ∀ n, QuasiCompact (smashPointDifference k f x x' hx hx' n).Y.hom
  | 0 => inferInstanceAs (QuasiCompact (𝟙 (fieldChowSituation k).S))
  | n + 1 => by
    have := quasiCompact_smashPointDifference n
    exact inferInstanceAs (QuasiCompact
      (pullback.fst (smashPointDifference k f x x' hx hx' n).Y.hom f ≫
        (smashPointDifference k f x x' hx hx' n).Y.hom))

/-- **Descent of torsion along an algebraic extension (Stacks 0FH8).** If the `n`-th smash power
of `[x_K] - [x'_K]` is torsion in `CH_0((X_K)^n)` for an algebraic extension `K/k`, then the
`n`-th smash power of `[x] - [x']` is torsion in `CH_0(X^n)`. -/
theorem isOfFinAddOrder_smashPointDifference_of_baseChange [Algebra.IsAlgebraic k K]
    [QuasiCompact f] (n : ℕ)
    (h : IsOfFinAddOrder (smashPointDifferenceBaseChange k K f x x' hx hx' n).cycle) :
    IsOfFinAddOrder (smashPointDifference k f x x' hx hx' n).cycle := by
  set Y := (smashPointDifference k f x x' hx hx' n).Y
  have : QuasiCompact Y.hom := quasiCompact_smashPointDifference k f x x' hx hx' n
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  obtain ⟨m, hm, hm0⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 h
  have hbc : baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl Y.hom
      (IsPullback.of_hasPullback Y.hom (fieldExtensionBaseChangeSituation k K).g) 0
        (m • (smashPointDifference k f x x' hx hx' n).cycle) = (0 : ℤ) • 0 := by
    rw [map_nsmul, baseChangeChowPullbackOfIsPullback_smashPointDifference, ← map_nsmul, hm0,
      map_zero, zero_smul]
  obtain ⟨E, δ, hE⟩ := exists_finiteSubextension_baseChangeChowPullback_eq_zsmul k K Y 0 0 _ 0 hbc
  have : FiniteDimensional k E.1 := E.2
  obtain ⟨β, hβ⟩ := exists_finrank_zsmul_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul
    k E.1 Y.hom 0 0 _ δ hE
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨Module.finrank k E.1 * m, Nat.mul_pos Module.finrank_pos hm, ?_⟩
  rwa [zero_smul, natCast_zsmul, ← mul_nsmul'] at hβ

end BaseChange

/-! ### The reductions -/

/-- **The curve case of Stacks 0FH9.** For every smooth, geometrically irreducible, H-projective
curve `X` over an algebraically closed field `k` and any two `k`-rational points `x, x'` of it, a
sufficiently high exterior power of `[x] - [x']` is torsion in the Chow group of zero-cycles of
the corresponding fibre power of `X`. -/
def SmashNilpotenceCurveCase : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ (fieldChowSituation k).S)
    [GeometricallyIrreducible f] [Smooth f], IsProjectiveMorphism f → ∀ [LocallyOfFiniteType f],
    topologicalKrullDim X = 1 →
    ∀ (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _),
      ∃ N : ℕ, ∀ n ≥ N, IsOfFinAddOrder (smashPointDifference k f x x' hx hx' n).cycle

open Stacks.SectionsVanishingOnSubscheme in
/-- **Stacks 0FH9 over an algebraically closed field, from the curve case.** Over an
algebraically closed field, the curve case implies smash nilpotence for every smooth,
geometrically irreducible, H-projective `X`. -/
theorem exists_isOfFinAddOrder_smashPointDifference_of_isAlgClosed
    (h : SmashNilpotenceCurveCase.{u}) (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    (f : X ⟶ (fieldChowSituation k).S) [GeometricallyIrreducible f] [Smooth f]
    (hproj : IsProjectiveMorphism f) [LocallyOfFiniteType f]
    (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ N : ℕ, ∀ n ≥ N, IsOfFinAddOrder (smashPointDifference k f x x' hx hx' n).cycle := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  obtain ⟨d, hdim⟩ := exists_topologicalKrullDim_eq_natCast_of_isProper k f
    (Nonempty.map (fun p ↦ x.base p) inferInstance)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : GeometricallyReduced f := geometricallyReduced_of_smooth f
    have : GeometricallyIntegral f :=
      GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
    have : IsIso f := isIso_of_topologicalKrullDim_eq_zero k f (by simpa using hdim)
    obtain rfl : x = x' := (cancel_mono f).mp (hx.trans hx'.symm)
    refine ⟨1, fun n hn ↦ ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    change IsOfFinAddOrder (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) _ f 0 0
      ((smashPointDifference k f x x hx hx' m).cycle ⊗ₜ pointDifference k f x x hx hx'))
    rw [show pointDifference k f x x hx hx' = 0 from sub_self _, TensorProduct.tmul_zero, map_zero]
    exact IsOfFinAddOrder.zero
  · obtain ⟨C, ι, hι, hsm, hgi, hprojC, hdimC, xC, xC', hfac, hfac'⟩ :=
      exists_projective_smooth_geometricallyIrreducible_curve_pair k d hd f hproj hdim x x' hx hx'
    have hxC : xC ≫ ι ≫ f = 𝟙 _ := by rw [← Category.assoc, hfac, hx]
    have hxC' : xC' ≫ ι ≫ f = 𝟙 _ := by rw [← Category.assoc, hfac', hx']
    obtain ⟨N, hN⟩ := h k C (ι ≫ f) hprojC hdimC xC xC' hxC hxC'
    exact ⟨N, fun n hn ↦ isOfFinAddOrder_smashPointDifference_of_closedImmersion k f ι x x' hx hx'
      xC xC' hxC hxC' hfac hfac' n (hN n hn)⟩

/-- **Stacks 0FH9, from the curve case.** Let `X` be smooth, geometrically irreducible and
H-projective over a field `k`, and let `x, x'` be `k`-rational points. Granted the curve case
`Stacks.Chow.SmashNilpotenceCurveCase`, a sufficiently high exterior power of `[x] - [x']` is
torsion in `CH_0(X^n)`. -/
theorem isOfFinAddOrder_smashPointDifference_of_curveCase (h : SmashNilpotenceCurveCase.{u})
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ (fieldChowSituation k).S)
    [GeometricallyIrreducible f] [Smooth f] (hproj : IsProjectiveMorphism f)
    [LocallyOfFiniteType f] (x x' : (fieldChowSituation k).S ⟶ X)
    (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ N : ℕ, ∀ n ≥ N, IsOfFinAddOrder (smashPointDifference k f x x' hx hx' n).cycle := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  set K := AlgebraicClosure k
  obtain ⟨N, hN⟩ := exists_isOfFinAddOrder_smashPointDifference_of_isAlgClosed h K _
    (pullback.snd f (fieldExtensionBaseChangeSituation k K).g)
    (hproj.baseChange (fieldExtensionBaseChangeSituation k K).g)
    (fieldBaseChangePoint k K f x hx) (fieldBaseChangePoint k K f x' hx')
    (fieldBaseChangePoint_comp k K f x hx) (fieldBaseChangePoint_comp k K f x' hx')
  exact ⟨N, fun n hn ↦
    isOfFinAddOrder_smashPointDifference_of_baseChange k K f x x' hx hx' n (hN n hn)⟩

end Stacks.Chow

end
