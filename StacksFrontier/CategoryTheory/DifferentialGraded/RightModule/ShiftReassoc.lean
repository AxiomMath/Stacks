module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Shift

/-!
# Reassociating a degree shift, and the strict coherences of the shift of a right module

The shift `M⟦n⟧` of a right differential graded module replaces the degree-`i` part by the
degree-`(i + n)` part, so every proof about it has to move a `+ n` past a `+ 1` or a `+ p`:
the single arithmetic fact `(i + n) + 1 = (i + 1) + n`, and its companion
`(i + n) + p = (i + p) + n`, occur in essentially every clause. This file names those two
equalities and the three normalisations of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Hom` specialised to them, so that a
downstream proof cites a lemma instead of re-deriving the arithmetic with `omega` — which
matters, because two invocations of `omega` do not produce the same proof term and a mismatched
degree proof blocks the rewrite that needs it.

It then proves that the shift is *strictly* coherent: `M⟦0⟧ = M` and
`M⟦n + m⟧ = (M⟦m⟧)⟦n⟧` as equalities of right differential graded modules. These are not
reflexivities — the underlying type families `fun i => M.obj x (i + 0)` and
`fun i => M.obj x i` are different functions, equal only propositionally — so they are proved
from an extensionality principle for `DGCategory.RightModule` which reduces an equality of
modules to an equality of the type families together with heterogeneous equalities of the
differential and the action. The sign `(-1)^n` on the differential of the shift is what makes
the second equality hold: the signs of `M⟦n + m⟧` and of `(M⟦m⟧)⟦n⟧` agree exactly because the
Koszul sign is multiplicative.

## Main definitions

None; this file only proves lemmas.

## Main results

* `DGCategory.RightModule.shiftIndex_succ` and `DGCategory.RightModule.shiftIndex_add`: the two
  reassociations of a degree shift, as named proofs.
* `DGCategory.RightModule.act_d_shift`, `DGCategory.RightModule.app_d_shift` and
  `DGCategory.RightModule.d_app_shift`: the normalisations of `DGCategory.RightModule.act_d`,
  `DGCategory.RightModule.app_d` and `DGCategory.RightModule.d_app` along those
  reassociations.
* `DGCategory.RightModule.ext'`: an equality of right differential graded modules follows from
  an equality of the underlying type families and heterogeneous equalities of the differential
  and the action.
* `DGCategory.RightModule.shift_zero` and `DGCategory.RightModule.shift_add`: the shift by `0`
  is the identity and the shift by a sum is the composite of the two shifts, both as equalities
  of right differential graded modules.

## Implementation notes

`DGCategory.RightModule.ext'` is stated with the differential and the action compared
*pointwise* under a heterogeneous equality of their arguments, rather than with heterogeneous
equalities of the two whole dependent functions. This is deliberate: once the type families are
substituted, the two differentials have literally the same type, so the pointwise hypotheses
assemble into an ordinary `funext` and no heterogeneous function extensionality is needed.

The three heterogeneous congruences `DGCategory.RightModule.d_heq`,
`DGCategory.RightModule.act_heq` and `DGCategory.RightModule.smul_heq` are the only tools used
to discharge those hypotheses; each is proved by substituting the equalities of degrees, which
is possible precisely because the degrees of `DGCategory.RightModule` are parameters constrained
by a proof rather than canonical expressions.
-/

@[expose] public section

namespace DGCategory.RightModule

universe w v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-! ### The two reassociations of a degree shift -/

/-- The reassociation `(i + n) + 1 = (i + 1) + n`: shifting a degree past the differential.
Named rather than produced by `omega` at each use, so that the degree proofs of two
matching clauses are the same term. -/
theorem shiftIndex_succ (i n : ℤ) : i + n + 1 = i + 1 + n := by omega

/-- The reassociation `(i + n) + p = (i + p) + n`: shifting a degree past a degree-`p`
morphism or a degree-`p` action. -/
theorem shiftIndex_add (i n p : ℤ) : i + n + p = i + p + n := by omega

variable (M : RightModule.{w} C)

/-- `DGCategory.RightModule.act_d` along `DGCategory.RightModule.shiftIndex_succ`: inside an
action, the differential of a shifted degree is the canonical differential. -/
theorem act_d_shift {x y : C.Obj} {i n q l : ℤ} (h : i + 1 + n + q = l)
    (h' : i + n + 1 + q = l) (a : M.obj y (i + n)) (f : C.Hom x y q) :
    M.act h (M.d (shiftIndex_succ i n) a) f = M.act h' (M.d rfl a) f :=
  act_d M (shiftIndex_succ i n) h h' a f

variable {M} {N : RightModule.{w} C} {p : ℤ}

/-- `DGCategory.RightModule.app_d` along `DGCategory.RightModule.shiftIndex_succ`: inside a
homogeneous morphism, the differential of a shifted degree is the canonical differential. -/
theorem app_d_shift (φ : HomogeneousMap M N p) {x : C.Obj} {i n j : ℤ}
    (h : i + 1 + n + p = j) (h' : i + n + 1 + p = j) (a : M.obj x (i + n)) :
    app φ h (M.d (shiftIndex_succ i n) a) = app φ h' (M.d rfl a) :=
  app_d φ (shiftIndex_succ i n) h h' a

/-- `DGCategory.RightModule.d_app` along `DGCategory.RightModule.shiftIndex_add`: the
differential of the value of a homogeneous morphism at a reassociated target degree is its
value at the canonical one. -/
theorem d_app_shift (φ : HomogeneousMap M N p) {x : C.Obj} {i n l : ℤ}
    (h : i + p + n + 1 = l) (h' : i + n + p + 1 = l) (a : M.obj x (i + n)) :
    N.d h (app φ (shiftIndex_add i n p) a) = N.d h' (app φ rfl a) :=
  d_app φ (shiftIndex_add i n p) h h' a

/-! ### Heterogeneous congruences for the differential and the action -/

/-- The value of a dependent function at two equal indices, heterogeneously. -/
theorem heq_apply_of_eq {ι : Sort*} {β : ι → Sort*} (f : ∀ i, β i) {i j : ι} (h : i = j) :
    HEq (f i) (f j) := by subst h; rfl

/-- The differential of heterogeneously equal elements at equal degrees agree. -/
theorem d_heq (M : RightModule.{w} C) {x : C.Obj} {i i' j j' : ℤ} (hi : i = i') (hj : j = j')
    {h : i + 1 = j} {h' : i' + 1 = j'} {a : M.obj x i} {a' : M.obj x i'} (ha : HEq a a') :
    HEq (M.d h a) (M.d h' a') := by
  subst hi; subst hj
  obtain rfl := eq_of_heq ha
  rfl

/-- The action on heterogeneously equal elements at equal degrees agree. -/
theorem act_heq (M : RightModule.{w} C) {x y : C.Obj} {i i' q k k' : ℤ} (hi : i = i')
    (hk : k = k') {h : i + q = k} {h' : i' + q = k'} {a : M.obj y i} {a' : M.obj y i'}
    (ha : HEq a a') (f : C.Hom x y q) : HEq (M.act h a f) (M.act h' a' f) := by
  subst hi; subst hk
  obtain rfl := eq_of_heq ha
  rfl

/-- Scalar multiples of heterogeneously equal elements agree. -/
theorem smul_heq (M : RightModule.{w} C) {x : C.Obj} {i i' : ℤ} (hi : i = i') (c : R)
    {a : M.obj x i} {a' : M.obj x i'} (ha : HEq a a') : HEq (c • a) (c • a') := by
  subst hi
  obtain rfl := eq_of_heq ha
  rfl

/-! ### Extensionality for right differential graded modules -/

/-- Two right differential graded modules with the same type families, the same differential and
the same action are equal. The remaining fields are propositions, so they carry no information
beyond the four compared here. -/
theorem ext' {M N : RightModule.{w} C} (hobj : M.obj = N.obj)
    (hgrp : ∀ (x : C.Obj) (i : ℤ), HEq (M.addCommGroup x i) (N.addCommGroup x i))
    (hmod : ∀ (x : C.Obj) (i : ℤ), HEq (M.module x i) (N.module x i))
    (hd : ∀ {x : C.Obj} {i j : ℤ} (h : i + 1 = j) (a : M.obj x i) (b : N.obj x i),
      HEq a b → HEq (M.d h a) (N.d h b))
    (hact : ∀ {x y : C.Obj} {i q k : ℤ} (h : i + q = k) (a : M.obj y i) (b : N.obj y i)
      (f : C.Hom x y q), HEq a b → HEq (M.act h a f) (N.act h b f)) : M = N := by
  obtain ⟨o₁, g₁, m₁, d₁, _, _, _, c₁, _, _, _, _, _, _, _⟩ := M
  obtain ⟨o₂, g₂, m₂, d₂, _, _, _, c₂, _, _, _, _, _, _, _⟩ := N
  dsimp only at hobj hgrp hmod hd hact
  subst hobj
  obtain rfl : g₁ = g₂ := funext fun x => funext fun i => eq_of_heq (hgrp x i)
  obtain rfl : m₁ = m₂ := funext fun x => funext fun i => eq_of_heq (hmod x i)
  have hD : @Eq (∀ (x : C.Obj) (i j : ℤ), i + 1 = j → o₁ x i → o₁ x j) (@d₁) (@d₂) := by
    funext x i j h a
    exact eq_of_heq (hd h a a HEq.rfl)
  have hC : @Eq (∀ (x y : C.Obj) (i q k : ℤ), i + q = k → o₁ y i → C.Hom x y q → o₁ x k)
      (@c₁) (@c₂) := by
    funext x y i q k h a f
    exact eq_of_heq (hact h a a f HEq.rfl)
  subst hD
  subst hC
  rfl

/-! ### The strict coherences of the shift -/

/-- The shift by `0` is the identity: `M⟦0⟧ = M`, as an equality of right differential graded
modules. -/
theorem shift_zero (M : RightModule.{w} C) : shift M 0 = M := by
  refine ext' ?_ ?_ ?_ ?_ ?_
  · funext x i
    exact congrArg (M.obj x) (add_zero i)
  · intro x i
    exact heq_apply_of_eq (fun t => M.addCommGroup x t) (add_zero i)
  · intro x i
    exact heq_apply_of_eq (fun t => M.module x t) (add_zero i)
  · intro x i j h a b hab
    change HEq ((-1 : R) ^ (0 : ℤ).natAbs •
      M.d (show i + 0 + 1 = j + 0 by omega) a) (M.d h b)
    rw [Int.natAbs_zero, pow_zero, one_smul]
    exact d_heq M (add_zero i) (add_zero j) hab
  · intro x y i q k h a b f hab
    change HEq (M.act (show i + 0 + q = k + 0 by omega) a f) (M.act h b f)
    exact act_heq M (add_zero i) (add_zero k) hab f

/-- The shift by a sum is the composite of the two shifts: `M⟦n + m⟧ = (M⟦m⟧)⟦n⟧`, as an
equality of right differential graded modules. The signs match because the Koszul sign is
multiplicative. -/
theorem shift_add (M : RightModule.{w} C) (n m : ℤ) :
    shift M (n + m) = shift (shift M m) n := by
  have hs : (-1 : R) ^ (n + m).natAbs = (-1 : R) ^ n.natAbs * (-1 : R) ^ m.natAbs :=
    neg_one_pow_natAbs_add n m
  have e (i : ℤ) : i + (n + m) = i + n + m := by omega
  refine ext' ?_ ?_ ?_ ?_ ?_
  · funext x i
    exact congrArg (M.obj x) (e i)
  · intro x i
    exact heq_apply_of_eq (fun t => M.addCommGroup x t) (e i)
  · intro x i
    exact heq_apply_of_eq (fun t => M.module x t) (e i)
  · intro x i j h a b hab
    change HEq ((-1 : R) ^ (n + m).natAbs •
        M.d (show i + (n + m) + 1 = j + (n + m) by omega) a)
      ((-1 : R) ^ n.natAbs • ((-1 : R) ^ m.natAbs •
        M.d (show i + n + m + 1 = j + n + m by omega) b))
    rw [hs, ← smul_smul]
    exact smul_heq M (e j) _
      (smul_heq M (e j) _
        (d_heq M (e i)
          (e j) hab))
  · intro x y i q k h a b f hab
    change HEq (M.act (show i + (n + m) + q = k + (n + m) by omega) a f)
      (M.act (show i + n + m + q = k + n + m by omega) b f)
    exact act_heq M (e i)
      (e k) hab f

end DGCategory.RightModule
