module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerLeft

/-!
# The successor equation for the integer addition law at a negative second exponent

`Stacks.TensorPowers.TensorInverse.addIso` is the addition law
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` of the integer tensor powers of an object `L` carrying a
two-sided tensor inverse.  It recurses on its **second** exponent, upwards from the degree `0`
through `Stacks.TensorPowers.TensorInverse.addNatIso` and downwards through
`Stacks.TensorPowers.TensorInverse.subNatIso`, and
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/IntegerLeft.lean` records exactly one thing as
missing:

> the successor equation for `addIso` at a negative integer second exponent; the associativity
> constraint in any degree where the second or third exponent is negative is interderivable with
> it.

This file proves it.  The downward clause adds a factor of `L⁻¹` by
`Stacks.TensorPowers.TensorInverse.predIso`, which is built from `TensorInverse.mulIso`; reading
it as an upward clause means undoing that by
`Stacks.TensorPowers.TensorInverse.succIso`, which is built from `TensorInverse.mulIso'`.  That
step is **not formal**: a bare `Stacks.TensorPowers.TensorInverse` carries two inverse laws with
no relation between them, and rescaling `mulIso'` by an automorphism of the unit object rescales
`succIso` while leaving `predIso` alone, so the equation fails for the rescaled datum.  What it
needs, and all it needs, is that the two laws are *snake-compatible*,

`(α_ L L⁻¹ L).hom ≫ L ◁ mulIso' ≫ (ρ_ L).hom = mulIso ▷ L ≫ (λ_ L).hom`,

which is what `Stacks.Monoidal.braiding_eval_snake` supplies for an object whose self-braiding is
trivial and whose second law is the first one precomposed with the braiding — the shape
`Stacks.TensorPowers.tensorInverseOfTensorLeft` produces, and so the shape every tensor inverse of
an invertible sheaf of modules in this repository has.  It is a hypothesis here, not an instance,
because the abstract powers are defined for arbitrary data and no braiding is available at them;
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/IntegerSuccSheaf.lean` discharges it for the
chosen tensor inverse of an invertible sheaf of modules, where it is free.

## Main results

* `Stacks.TensorPowers.TensorInverse.subNatIso_succ`: **the successor equation at a negative
  second exponent.**  Multiplication by `L ^⊗ (-j)` is recovered from multiplication by
  `L ^⊗ (-(j+1))` through the successor comparisons, exactly as
  `Stacks.TensorPowers.TensorInverse.addNatIso_succ` recovers multiplication by `L ^⊗ (k+1)` from
  multiplication by `L ^⊗ k`.
* `Stacks.TensorPowers.TensorInverse.predIso_zigzag`: **the zig-zag identity**, which is its
  content.  In every integer degree, `predIso` whiskered by `L` and contracted against `mulIso'`
  is `succIso` one degree down, run backwards.  This is the one place where
  snake-compatibility is consumed.
* `Stacks.TensorPowers.TensorInverse.addIso_neg_natCast`: the addition law at a nonpositive second
  exponent is the subtraction recursion, so the successor equation above is an equation about
  `addIso`.
* `Stacks.Monoidal.succ_of_pred_step`: **one step down, undone by one step up**, with every
  object and morphism free — the monoidal algebra that turns a clause of `subNatIso` into a clause
  of `addNatIso` once the two zig-zag identities are supplied.
* `Stacks.Monoidal.contract_naturality`, `Stacks.Monoidal.contract_whiskerLeft` and
  `Stacks.Monoidal.inv_contract_whiskerRight`: the three pieces it is built from — the naturality
  of the contraction against an inverse law, its behaviour under left whiskering, and the
  cancellation of an inserted inverse law against the opposite one.
* `Stacks.TensorPowers.TensorInverse.predIso_zero`,
  `Stacks.TensorPowers.TensorInverse.predIso_natCast_succ`,
  `Stacks.TensorPowers.TensorInverse.predIso_neg_natCast_succ`,
  `Stacks.TensorPowers.TensorInverse.succIso_zero_sub_one` and
  `Stacks.TensorPowers.TensorInverse.succIso_neg_natCast_succ_sub_one`: the clauses of the two
  recursions, restated as equations.  Both are defined by pattern matching on the constructors of
  `Int`, so their defining clauses are not rewrite rules until they are restated; each holds by
  `rfl`.

## Implementation notes

**Every step is run through free-object helpers.**  Exactly as in
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/IntegerLeft.lean`, each case is closed by `exact`
against a lemma in which every object and morphism is a variable, with the places where a
comparison in a nonnegative degree is an identity supplied as hypotheses discharged by
`MonoidalCategory.id_whiskerRight` at objects that are equal by `rfl`.  No `rw` crosses the two
spellings `natTensorPow L (k + 1)` and `intTensorPow L h.inv (k + 1)`, which are the same object
but not the same term, and under which `simp` rejects a goal after it has rewritten part of it.
The two successor comparisons of `subNatIso_succ` are free variables pinned by hypotheses for the
same reason.

**Why the zig-zag has three cases and not two.** `predIso` is the identity in every degree `≤ 0`
but the two branches of `Int` reach that range differently: at `0` the successor comparison one
degree down ends in `λ_ (𝟙_ C)` where in a negative degree it ends in `ρ_`, so the degree zero
needs `CategoryTheory.MonoidalCategory.unitors_equal` and a negative degree does not.  Only the
positive case has content.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## What is not done

**The successor equation restated uniformly in `m : ℤ`**, i.e. `addIso n (m + 1)` written in terms
of `addIso n m` for a variable integer `m`.  That is bookkeeping rather than mathematics — it is
`Stacks.TensorPowers.TensorInverse.addNatIso_succ` and `subNatIso_succ` glued along
`addIso_neg_natCast` — but the gluing is not free: `Int.negSucc k + 1` and `-(k : ℤ)` are the same
integer and not the same term, and neither reduces for a variable `k`, so the uniform statement
needs the case split the two recursions already carry.

Consequently the three things the successor equation was wanted for are also not here: the
associativity constraint of `addIso` in an arbitrary integer bidegree, the commutativity of the
two inverse laws of `L ^⊗ n` (equivalently the snake-compatibility of
`Stacks.TensorPowers.TensorInverse.tensorInversePow`), and the multiplicativity of
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt` in an arbitrary integer bidegree.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Stacks.TensorPowers

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The contraction against an inverse law is natural.**  Reassociating `(U ⊗ Iv) ⊗ Lb` and
cancelling `Iv ⊗ Lb` against `e'` commutes with a morphism out of `U`. -/
theorem contract_naturality {U V Iv Lb : C} (e' : Iv ⊗ Lb ⟶ 𝟙_ C) (f : U ⟶ V) :
    ((f ▷ Iv) ▷ Lb) ≫ (α_ V Iv Lb).hom ≫ V ◁ e' ≫ (ρ_ V).hom =
      ((α_ U Iv Lb).hom ≫ U ◁ e' ≫ (ρ_ U).hom) ≫ f := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality,
    Category.assoc, Category.assoc]

/-- The contraction at `A ⊗ B`, with the `Iv` factor inserted into `B` by a morphism `w`, is the
contraction at `B` whiskered into `A`.  Pure coherence: the pentagon moves the `A` across the two
associators and the triangle turns the right unitor of `A ⊗ B` into that of `B`. -/
private theorem contract_whiskerLeft_aux {A B Iv Lb : C} (e' : Iv ⊗ Lb ⟶ 𝟙_ C) :
    (α_ A (B ⊗ Iv) Lb).inv ≫ ((α_ A B Iv).inv ▷ Lb) ≫
        (α_ (A ⊗ B) Iv Lb).hom ≫ (A ⊗ B) ◁ e' ≫ (ρ_ (A ⊗ B)).hom =
      A ◁ (α_ B Iv Lb).hom ≫ A ◁ (B ◁ e') ≫ A ◁ (ρ_ B).hom := by
  monoidal

/-- **The contraction against an inverse law, whiskered on the left.**  Inserting the factor `Iv`
into `B` along `w : Bm ⟶ B ⊗ Iv`, reassociating out of `A` and contracting at `A ⊗ B` is the same
operation performed at `B` and whiskered into `A`. -/
theorem contract_whiskerLeft {A B Bm Iv Lb : C} (e' : Iv ⊗ Lb ⟶ 𝟙_ C) (w : Bm ⟶ B ⊗ Iv) :
    (α_ A Bm Lb).inv ≫ (((A ◁ w) ≫ (α_ A B Iv).inv) ▷ Lb) ≫
        (α_ (A ⊗ B) Iv Lb).hom ≫ (A ⊗ B) ◁ e' ≫ (ρ_ (A ⊗ B)).hom =
      A ◁ (w ▷ Lb ≫ (α_ B Iv Lb).hom ≫ B ◁ e' ≫ (ρ_ B).hom) := by
  rw [MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc ((α_ A Bm Lb).inv), ← MonoidalCategory.associator_inv_naturality_middle]
  simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp]
  rw [contract_whiskerLeft_aux]

/-- **Inserting an inverse law and contracting with the opposite one is the identity.**  Let
`e : Lb ⊗ Iv ≅ 𝟙` and `e' : Iv ⊗ Lb ⟶ 𝟙` be snake-compatible.  Then the comparison
`N ≅ (N ⊗ Lb) ⊗ Iv` that `e` produces, whiskered by `Lb` and followed by the contraction of
`((N ⊗ Lb) ⊗ Iv) ⊗ Lb` against `e'`, is the identity of `N ⊗ Lb`.

This is the one place where snake-compatibility is used: `contract_whiskerLeft` carries the
hypothesis from `Lb` to `N ⊗ Lb`, `e` cancels against `e.inv`, and the triangle removes the two
unitors. -/
theorem inv_contract_whiskerRight {N Lb Iv : C} (e : Lb ⊗ Iv ≅ 𝟙_ C) (e' : Iv ⊗ Lb ⟶ 𝟙_ C)
    (hs : (α_ Lb Iv Lb).hom ≫ Lb ◁ e' ≫ (ρ_ Lb).hom = e.hom ▷ Lb ≫ (λ_ Lb).hom) :
    (((ρ_ N).inv ≫ N ◁ e.inv ≫ (α_ N Lb Iv).inv) ▷ Lb) ≫
        (α_ (N ⊗ Lb) Iv Lb).hom ≫ (N ⊗ Lb) ◁ e' ≫ (ρ_ (N ⊗ Lb)).hom = 𝟙 (N ⊗ Lb) := by
  have hcancel : e.inv ▷ Lb ≫ (α_ Lb Iv Lb).hom ≫ Lb ◁ e' ≫ (ρ_ Lb).hom = (λ_ Lb).hom := by
    rw [hs, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight, e.inv_hom_id,
      MonoidalCategory.id_whiskerRight, Category.id_comp]
  have hw := contract_whiskerLeft (A := N) (B := Lb) (Bm := 𝟙_ C) e' e.inv
  rw [hcancel] at hw
  rw [comp_whiskerRight, Category.assoc, (Iso.inv_comp_eq _).mp hw, triangle,
    ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]

/-- **One step down, undone by one step up.**  Let `dd` be built from `f : A ⊗ B ⟶ R` by
inserting the factor `Iv` into `B` along `pB`, reassociating, and transporting the result along
`pRinv`.  If `pRinv` is a section of `pR`, if `sR` is `pR` whiskered by `Lb` and contracted
against `e'`, and if `sBinv` is a retraction of `pB` whiskered by `Lb` and contracted against
`e'`, then the same construction run with `sBinv`, `dd` and `sR` returns `f`.

This is the step that turns a recursion clause of
`Stacks.TensorPowers.TensorInverse.subNatIso` — one factor of `L⁻¹` added — into the
corresponding clause of `Stacks.TensorPowers.TensorInverse.addNatIso` — one factor of `L` added —
with the two zig-zag identities supplied as `hzB` and `hzR`.  Nothing but monoidal algebra is
used: the naturality of the contraction moves `f` out of it and
`Stacks.Monoidal.contract_whiskerLeft` moves the rest onto `B`. -/
theorem succ_of_pred_step {A B Bm Iv Lb R Rm : C} (e' : Iv ⊗ Lb ⟶ 𝟙_ C)
    (f : A ⊗ B ⟶ R) (pB : Bm ⟶ B ⊗ Iv) (pRinv : R ⊗ Iv ⟶ Rm) (pR : Rm ⟶ R ⊗ Iv)
    (sBinv : B ⟶ Bm ⊗ Lb) (sR : Rm ⊗ Lb ⟶ R) (dd : A ⊗ Bm ⟶ Rm)
    (hd : dd = A ◁ pB ≫ (α_ A B Iv).inv ≫ (f ▷ Iv) ≫ pRinv)
    (hpR : pRinv ≫ pR = 𝟙 (R ⊗ Iv))
    (hzR : (pR ▷ Lb) ≫ (α_ R Iv Lb).hom ≫ R ◁ e' ≫ (ρ_ R).hom = sR)
    (hzB : sBinv ≫ ((pB ▷ Lb) ≫ (α_ B Iv Lb).hom ≫ B ◁ e' ≫ (ρ_ B).hom) = 𝟙 B) :
    A ◁ sBinv ≫ (α_ A Bm Lb).inv ≫ (dd ▷ Lb) ≫ sR = f := by
  have step : (α_ A Bm Lb).inv ≫ ((A ◁ pB) ▷ Lb) ≫ ((α_ A B Iv).inv ▷ Lb) ≫
      (α_ (A ⊗ B) Iv Lb).hom ≫ (A ⊗ B) ◁ e' ≫ (ρ_ (A ⊗ B)).hom =
      A ◁ ((pB ▷ Lb) ≫ (α_ B Iv Lb).hom ≫ B ◁ e' ≫ (ρ_ B).hom) := by
    rw [← Category.assoc ((A ◁ pB) ▷ Lb), ← MonoidalCategory.comp_whiskerRight]
    exact contract_whiskerLeft e' pB
  subst hd hzR
  simp only [comp_whiskerRight, Category.assoc]
  rw [← Category.assoc (pRinv ▷ Lb), ← comp_whiskerRight, hpR, id_whiskerRight,
    Category.id_comp, contract_naturality]
  simp only [Category.assoc]
  rw [reassoc_of% step, ← whiskerLeft_comp_assoc, hzB, whiskerLeft_id, Category.id_comp]

end Stacks.Monoidal

namespace Stacks.TensorPowers.TensorInverse

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TensorPowers.intTensorPow

/-- The clause of `Stacks.TensorPowers.TensorInverse.predIso` in a positive degree: there the
comparison is the inverse law `TensorInverse.mulIso` cancelling the last factor of `L`, after the
transport between the two spellings `(k + 1) - 1` and `k` of the degree. -/
theorem predIso_natCast_succ {L : C} (h : TensorInverse L) (k : ℕ) :
    h.predIso ((k : ℤ) + 1) =
      reindex L h.inv (show ((k : ℤ) + 1) - 1 = (k : ℤ) from by omega) ≪≫
        (α_ (natTensorPow L k) L h.inv ≪≫ whiskerLeftIso _ h.mulIso ≪≫ ρ_ _).symm := rfl

/-- The clause of `Stacks.TensorPowers.TensorInverse.predIso` in a negative degree: there the
powers are powers of the inverse object and the comparison is the identity. -/
theorem predIso_neg_natCast_succ {L : C} (h : TensorInverse L) (k : ℕ) :
    h.predIso (-((k : ℤ) + 1)) = Iso.refl _ := rfl

/-- The clause of `Stacks.TensorPowers.TensorInverse.predIso` in the degree zero. -/
theorem predIso_zero {L : C} (h : TensorInverse L) : h.predIso (0 : ℤ) = Iso.refl _ := rfl

/-- The clause of `Stacks.TensorPowers.TensorInverse.succIso` one degree below zero.  It ends in
the left unitor of the unit object, where in a negative degree the same clause ends in the right
unitor. -/
theorem succIso_zero_sub_one {L : C} (h : TensorInverse L) :
    h.succIso ((0 : ℤ) - 1) =
      (α_ (𝟙_ C) h.inv L ≪≫ whiskerLeftIso (𝟙_ C) h.mulIso' ≪≫ λ_ (𝟙_ C)).symm := rfl

/-- The clause of `Stacks.TensorPowers.TensorInverse.succIso` in a negative degree: there the
comparison is the inverse law `TensorInverse.mulIso'` cancelling an `L⁻¹ ⊗ L`. -/
theorem succIso_neg_natCast_succ_sub_one {L : C} (h : TensorInverse L) (k : ℕ) :
    h.succIso (-((k : ℤ) + 1) - 1) =
      (α_ (natTensorPow h.inv (k + 1)) h.inv L ≪≫
        whiskerLeftIso _ h.mulIso' ≪≫ ρ_ _).symm := rfl

/-- The two degrees in which the predecessor comparison is an identity, with every object and
morphism free. -/
private theorem zigzag_id_free {B Iv Lb : C} (e' : Iv ⊗ Lb ⟶ 𝟙_ C)
    (u : (B ⊗ Iv) ⊗ Lb ⟶ (B ⊗ Iv) ⊗ Lb) (hu : u = 𝟙 _)
    (s : (B ⊗ Iv) ⊗ Lb ⟶ B) (t : B ⟶ B) (ht : t = 𝟙 B) (w : B ⊗ 𝟙_ C ⟶ B)
    (hw : w = (ρ_ B).hom) (hs : s = (α_ B Iv Lb).hom ≫ B ◁ e' ≫ w) :
    u ≫ (α_ B Iv Lb).hom ≫ B ◁ e' ≫ (ρ_ B).hom = s ≫ t := by
  rw [hu, ht, hs, hw, Category.id_comp, Category.comp_id]

/-- The assembly of the positive degree, with every object and morphism free: a transport
preceding a comparison whose whiskering the contraction cancels. -/
private theorem zigzag_comp_free {A B D Lb : C} (pr : A ⟶ B) (xi xi' : B ⟶ D)
    (hxi : xi = xi') (cc : D ⊗ Lb ⟶ B ⊗ Lb) (hz : (xi' ▷ Lb) ≫ cc = 𝟙 (B ⊗ Lb))
    (rhs : A ⊗ Lb ⟶ B ⊗ Lb) (hrhs : rhs = pr ▷ Lb) :
    ((pr ≫ xi) ▷ Lb) ≫ cc = rhs := by
  rw [hxi, MonoidalCategory.comp_whiskerRight, Category.assoc, hz, Category.comp_id, hrhs]

omit [MonoidalCategory C] in
/-- Two identities stripped off the two ends of a composite. -/
private theorem strip_two_free {A B D : C} (f : A ⟶ B) (i : B ⟶ B) (g : A ⟶ D) (t : D ⟶ B)
    (u : B ⟶ B) (hi : i = 𝟙 B) (hu : u = 𝟙 B) (key : f ≫ i = g ≫ t ≫ u) : g ≫ t = f := by
  rw [hi, Category.comp_id, hu, Category.comp_id] at key
  exact key.symm

/-- The zig-zag in the degree zero.  Both sides are the contraction of `(𝟙 ⊗ L⁻¹) ⊗ L` against
the second inverse law; they differ only in which unitor of the unit object closes it, and
`CategoryTheory.MonoidalCategory.unitors_equal` identifies the two. -/
theorem predIso_zigzag_zero {L : C} (h : TensorInverse L) :
    ((h.predIso (0 : ℤ)).hom ▷ L) ≫ (α_ (intTensorPow L h.inv 0) h.inv L).hom ≫
        intTensorPow L h.inv 0 ◁ h.mulIso'.hom ≫ (ρ_ (intTensorPow L h.inv 0)).hom =
      (h.succIso ((0 : ℤ) - 1)).inv ≫
        (reindex L h.inv (show (0 : ℤ) - 1 + 1 = 0 from by omega)).hom :=
  zigzag_id_free h.mulIso'.hom _ (MonoidalCategory.id_whiskerRight _ _) _ _ rfl _
    MonoidalCategory.unitors_equal rfl

/-- The zig-zag in a negative degree.  Both comparisons are then clauses of the recursion on
powers of the inverse object: the predecessor comparison is the identity and the successor
comparison is the contraction itself, so the two sides are the same term. -/
theorem predIso_zigzag_neg_natCast_succ {L : C} (h : TensorInverse L) (k : ℕ) :
    ((h.predIso (-((k : ℤ) + 1))).hom ▷ L) ≫
        (α_ (intTensorPow L h.inv (-((k : ℤ) + 1))) h.inv L).hom ≫
        intTensorPow L h.inv (-((k : ℤ) + 1)) ◁ h.mulIso'.hom ≫
          (ρ_ (intTensorPow L h.inv (-((k : ℤ) + 1)))).hom =
      (h.succIso (-((k : ℤ) + 1) - 1)).inv ≫
        (reindex L h.inv (show -((k : ℤ) + 1) - 1 + 1 = -((k : ℤ) + 1) from by omega)).hom :=
  zigzag_id_free h.mulIso'.hom _ (MonoidalCategory.id_whiskerRight _ _) _ _ rfl _ rfl rfl

/-- **The zig-zag in a positive degree** — the case with content.  There the predecessor
comparison inserts the first inverse law and the contraction cancels it against the second one,
which is `Stacks.Monoidal.inv_contract_whiskerRight`, while the successor comparison one degree
down is an identity carrying only the transport between the two spellings `(k + 1) - 1` and `k`
of the degree, which is `Stacks.TensorPowers.TensorInverse.reindex_whiskerRight_succIso`. -/
theorem predIso_zigzag_natCast_succ {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (k : ℕ) :
    ((h.predIso ((k : ℤ) + 1)).hom ▷ L) ≫
        (α_ (intTensorPow L h.inv ((k : ℤ) + 1)) h.inv L).hom ≫
        intTensorPow L h.inv ((k : ℤ) + 1) ◁ h.mulIso'.hom ≫
          (ρ_ (intTensorPow L h.inv ((k : ℤ) + 1))).hom =
      (h.succIso ((k : ℤ) + 1 - 1)).inv ≫
        (reindex L h.inv (show (k : ℤ) + 1 - 1 + 1 = (k : ℤ) + 1 from by omega)).hom := by
  have hk : ((k : ℤ) + 1) - 1 = (k : ℤ) := by omega
  have hR := strip_two_free
    ((reindex L h.inv hk).hom ▷ L) _ _ _ _
    (by rw [succIso_natCast]; exact Category.id_comp _) rfl
    (reindex_whiskerRight_succIso h
      hk
      (show (k : ℤ) + 1 = (k : ℤ) + 1 from rfl)
      (show (k : ℤ) + 1 - 1 + 1 = (k : ℤ) + 1 from by omega)
      (show ((k : ℤ) + 1 : ℤ) = (k : ℤ) + 1 from rfl))
  refine zigzag_comp_free
    (reindex L h.inv hk).hom
    (α_ (natTensorPow L k) L h.inv ≪≫ whiskerLeftIso _ h.mulIso ≪≫
      ρ_ (natTensorPow L k)).symm.hom
    ((ρ_ (natTensorPow L k)).inv ≫ natTensorPow L k ◁ h.mulIso.inv ≫
      (α_ (natTensorPow L k) L h.inv).inv) ?_ _ ?_ _ hR
  · rw [Iso.symm_hom, Iso.trans_inv, Iso.trans_inv, whiskerLeftIso_inv, Category.assoc]
  · exact Stacks.Monoidal.inv_contract_whiskerRight (N := natTensorPow L k) h.mulIso
      h.mulIso'.hom hs

/-- **The zig-zag identity: going down a degree and back up again is the identity.**  In every
integer degree `m`, the predecessor comparison `L ^⊗ (m - 1) ≅ L ^⊗ m ⊗ L⁻¹` whiskered by `L`,
reassociated and contracted against the second inverse law is the successor comparison
`L ^⊗ (m - 1 + 1) ≅ L ^⊗ (m - 1) ⊗ L` run backwards.

The hypothesis is the compatibility of the two inverse laws of `L` itself, and it is not
removable: rescaling `TensorInverse.mulIso'` by an automorphism of the unit object rescales
`succIso` and leaves `predIso` alone.  For a tensor inverse produced by
`Stacks.TensorPowers.tensorInverseOfTensorLeft` the second law is the first precomposed with the
braiding, and then `Stacks.Monoidal.braiding_eval_snake` discharges it from the triviality of the
self-braiding of `L`. -/
theorem predIso_zigzag {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (m : ℤ) :
    ((h.predIso m).hom ▷ L) ≫ (α_ (intTensorPow L h.inv m) h.inv L).hom ≫
        intTensorPow L h.inv m ◁ h.mulIso'.hom ≫ (ρ_ (intTensorPow L h.inv m)).hom =
      (h.succIso (m - 1)).inv ≫
        (reindex L h.inv (show m - 1 + 1 = m from by omega)).hom := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ :
      (∃ k : ℕ, m = (k : ℤ)) ∨ (∃ k : ℕ, m = -((k : ℤ) + 1)) := by
    rcases m with k | k
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, Int.negSucc_eq k⟩
  · cases k with
    | zero => exact predIso_zigzag_zero h
    | succ k => exact predIso_zigzag_natCast_succ h hs k
  · exact predIso_zigzag_neg_natCast_succ h k

/-- **The successor equation for the addition law at a negative second exponent.**  The clause of
`Stacks.TensorPowers.TensorInverse.subNatIso` that adds one factor of `L⁻¹` can be read backwards
as a clause that adds one factor of `L`: multiplication by `L ^⊗ (-j)` is recovered from
multiplication by `L ^⊗ (-(j+1))` by the successor comparisons, exactly as
`Stacks.TensorPowers.TensorInverse.addNatIso_succ` recovers multiplication by `L ^⊗ (k+1)` from
multiplication by `L ^⊗ k`.

The two comparisons are free variables pinned by `hsB` and `hsR` rather than substituted values,
which is the idiom of `StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/IntegerLeft.lean`: a goal
naming both `natTensorPow` and `intTensorPow` at the same object is rejected once `rw` has
unfolded part of it.

Both hypotheses of the ambient snake-compatibility are consumed through
`Stacks.TensorPowers.TensorInverse.predIso_zigzag`, once at the second exponent and once at the
total degree. -/
theorem subNatIso_succ {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (n : ℤ) (j : ℕ)
    (sBinv : intTensorPow L h.inv (-(j : ℤ)) ⟶ intTensorPow L h.inv (-((j : ℤ) + 1)) ⊗ L)
    (sR : intTensorPow L h.inv (n - ((j + 1 : ℕ) : ℤ)) ⊗ L ⟶
      intTensorPow L h.inv (n - (j : ℤ)))
    (hsB : sBinv ≫
        ((reindex L h.inv (show -((j : ℤ) + 1) = -(j : ℤ) - 1 from by omega)).hom ▷ L) ≫
          (h.succIso (-(j : ℤ) - 1)).inv ≫
            (reindex L h.inv (show -(j : ℤ) - 1 + 1 = -(j : ℤ) from by omega)).hom = 𝟙 _)
    (hsR : sR =
      ((reindex L h.inv
            (show n - ((j + 1 : ℕ) : ℤ) = n - (j : ℤ) - 1 from by omega)).hom ▷ L) ≫
        (h.succIso (n - (j : ℤ) - 1)).inv ≫
          (reindex L h.inv (show n - (j : ℤ) - 1 + 1 = n - (j : ℤ) from by omega)).hom) :
    intTensorPow L h.inv n ◁ sBinv ≫
        (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv (-((j : ℤ) + 1))) L).inv ≫
          ((h.subNatIso n (j + 1)).hom ▷ L) ≫ sR = (h.subNatIso n j).hom := by
  refine Stacks.Monoidal.succ_of_pred_step h.mulIso'.hom (h.subNatIso n j).hom
    ((reindex L h.inv (show -((j : ℤ) + 1) = -(j : ℤ) - 1 from by omega)).hom ≫
      (h.predIso (-(j : ℤ))).hom)
    ((h.predIso (n - (j : ℤ))).inv ≫
      (reindex L h.inv
        (show n - (j : ℤ) - 1 = n - ((j + 1 : ℕ) : ℤ) from by omega)).hom)
    ((reindex L h.inv
        (show n - ((j + 1 : ℕ) : ℤ) = n - (j : ℤ) - 1 from by omega)).hom ≫
      (h.predIso (n - (j : ℤ))).hom)
    sBinv sR _ rfl ?_ ?_ ?_
  · simp [reindex]
  · rw [hsR, MonoidalCategory.comp_whiskerRight, Category.assoc,
      predIso_zigzag h hs (n - (j : ℤ))]
  · rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      predIso_zigzag h hs (-(j : ℤ))]
    simpa only [Category.assoc] using hsB

/-- The addition law at a nonpositive second exponent is the subtraction recursion. -/
theorem addIso_neg_natCast {L : C} (h : TensorInverse L) (n : ℤ) (j : ℕ) :
    (h.addIso n (-(j : ℤ))).hom =
      (h.subNatIso n j).hom ≫
        (reindex L h.inv (show n - (j : ℤ) = n + -(j : ℤ) from by omega)).hom := by
  cases j with
  | zero =>
      rw [show (h.addIso n (-((0 : ℕ) : ℤ))).hom =
            (ρ_ (intTensorPow L h.inv n)).hom ≫
              (reindex L h.inv (show n = n + ((0 : ℕ) : ℤ) from by omega)).hom from rfl,
        show (h.subNatIso n 0).hom =
            (ρ_ (intTensorPow L h.inv n)).hom ≫
              (reindex L h.inv (show n = n - ((0 : ℕ) : ℤ) from by omega)).hom from rfl]
      simp only [reindex, eqToIso.hom, Category.assoc, eqToHom_trans]
  | succ j =>
      rw [show (h.addIso n (-((j + 1 : ℕ) : ℤ))).hom =
            (intTensorPow L h.inv n ◁ 𝟙 (intTensorPow L h.inv (-((j : ℤ) + 1)))) ≫
              (h.subNatIso n (j + 1)).hom ≫
                (reindex L h.inv
                  (show n - ((j + 1 : ℕ) : ℤ) = n + -((j + 1 : ℕ) : ℤ) from by omega)).hom
          from rfl, MonoidalCategory.whiskerLeft_id, Category.id_comp]

end Stacks.TensorPowers.TensorInverse

end
