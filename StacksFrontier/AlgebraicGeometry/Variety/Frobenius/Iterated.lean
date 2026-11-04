module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Endomorphism
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Iterated Frobenius twists and the iterated relative Frobenius

Let `S` be a scheme of prime characteristic `p`. The `n`-fold Frobenius twist of an `S`-scheme
`X` is the base change of `X` along the `n`-th power of the absolute Frobenius of `S`, and the
`n`-fold relative Frobenius is the morphism to it whose projections are the `n`-fold absolute
Frobenius of `X` and the structure morphism of `X`.

The iterated relative Frobenius decomposes in two ways: as the composite of the relative
Frobenius morphisms of the successive twists, and as the composite of the successive Frobenius
base changes of the relative Frobenius of `X` itself. The two decompositions are related by the
canonical identification of the two orders of Frobenius base change.

## Main definitions

* `AlgebraicGeometry.absoluteFrobeniusPow`: the `n`-fold composite of the absolute Frobenius.
* `AlgebraicGeometry.nFoldFrobeniusTwist`: the `n`-fold Frobenius twist of a scheme over `S`.
* `AlgebraicGeometry.nFoldRelativeFrobenius`: the iterated relative Frobenius morphism.
* `AlgebraicGeometry.successiveTwistIso`: the identification of a twist of an iterated twist
  with the next iterated twist.
* `AlgebraicGeometry.successiveRelativeFrobenius`: the composite of the relative Frobenius
  morphisms of the successive twists.
* `AlgebraicGeometry.frobeniusTwistCommIso`: the identification between the two orders of
  Frobenius base change.
* `AlgebraicGeometry.twistedRelativeFrobeniusComposite`: the composite of the base changes of
  the relative Frobenius of `X` through the successive Frobenius twists.

## Main results

* `AlgebraicGeometry.nFoldRelativeFrobenius_fst` and
  `AlgebraicGeometry.nFoldRelativeFrobenius_snd`: the two components of the iterated relative
  Frobenius.
* `AlgebraicGeometry.nFoldRelativeFrobenius_eq_successiveRelativeFrobenius`: the iterated
  relative Frobenius is the composite of the relative Frobenius morphisms of the successive
  twists.
* `AlgebraicGeometry.relativeFrobenius_nFoldFrobeniusTwist`: relative Frobenius on an iterated
  twist is the corresponding base change of relative Frobenius on `X`.
* `AlgebraicGeometry.nFoldRelativeFrobenius_eq_twistedRelativeFrobeniusComposite`: the iterated
  relative Frobenius is the composite of the successive Frobenius base changes.

## References

* [Stacks Project, Tag 0CCG](https://stacks.math.columbia.edu/tag/0CCG)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

namespace AlgebraicGeometry

/-- The `n`-fold composite of the absolute Frobenius endomorphism. -/
public noncomputable abbrev absoluteFrobeniusPow (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) : S ⟶ S :=
  End.asHom ((End.of (absoluteFrobenius S p hS)) ^ n)

/-- The `n`-fold Frobenius twist of an `S`-scheme is its base change along the `n`-fold absolute
Frobenius of `S`, regarded as an `S`-scheme via the second projection. -/
@[stacks 0CCG "n_fold_frobenius_twist",
  sga "3 VIIA 4.1" "X^{(p/S)} for S-schemes",
  sga "3 VIIA 4.1.3" "special case",
  sga "3 VIIA 4.3.1",
  sga "3 VIIB 4.1.1" "more general",
  sga "3 XVII 4.3.2" "Notation X^(p^n)"]
public noncomputable abbrev nFoldFrobeniusTwist (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) : Over S :=
  (Over.pullback (absoluteFrobeniusPow S p hS n)).obj X

add_to_stacks 0CCG "twist_functor" CategoryTheory.Over.pullback

/-- The morphism from an `S`-scheme to its `n`-fold Frobenius twist, with components the `n`-fold
absolute Frobenius and the structure morphism. -/
@[stacks 0CCG "n_fold_relative_frobenius",
  implicit_reducible,
  sga "3 VIIA 4.1" "Fr(X/S) for S-schemes",
  sga "3 VIIA 4.1.3" "special case",
  sga "5 XII 7.3" "more general",
  sga "5 XV 1.Definition3" "more general"]
public noncomputable def nFoldRelativeFrobenius (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    X ⟶ nFoldFrobeniusTwist S p hS n X := by
  have hX : IsInCharacteristic X.left p := by
    change (p : Γ(X.left, ⊤)) = 0
    simpa only [map_natCast, map_zero] using congrArg X.hom.appTop.hom hS
  have hnat : ∀ n : ℕ,
      absoluteFrobeniusPow X.left p hX n ≫ X.hom =
        X.hom ≫ absoluteFrobeniusPow S p hS n := by
    intro m
    induction m with
    | zero => simp [absoluteFrobeniusPow]
    | succ m ih =>
        simp only [absoluteFrobeniusPow, pow_succ, End.mul_def]
        change (absoluteFrobenius X.left p hX ≫
            absoluteFrobeniusPow X.left p hX m) ≫ X.hom =
          X.hom ≫ (absoluteFrobenius S p hS ≫ absoluteFrobeniusPow S p hS m)
        rw [Category.assoc, ih, ← Category.assoc,
          absoluteFrobenius_naturality X.hom p hX hS, Category.assoc]
  exact Over.homMk (pullback.lift (absoluteFrobeniusPow X.left p hX n) X.hom (hnat n))
    (pullback.lift_snd _ _ _)

/-- The first component of the iterated relative Frobenius is the iterated absolute
Frobenius of `X`. -/
@[simp]
public theorem nFoldRelativeFrobenius_fst (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    (nFoldRelativeFrobenius S p hS n X).left ≫
      pullback.fst X.hom (absoluteFrobeniusPow S p hS n) =
        absoluteFrobeniusPow X.left p
          (by
            change (p : Γ(X.left, ⊤)) = 0
            simpa only [map_natCast, map_zero] using congrArg X.hom.appTop.hom hS) n := by
  simp only [nFoldRelativeFrobenius]
  exact pullback.lift_fst _ _ _

/-- The second component of the iterated relative Frobenius is the structure morphism
of `X` over `S`. -/
@[simp]
public theorem nFoldRelativeFrobenius_snd (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    (nFoldRelativeFrobenius S p hS n X).left ≫
      pullback.snd X.hom (absoluteFrobeniusPow S p hS n) = X.hom := by
  simp only [nFoldRelativeFrobenius]
  exact pullback.lift_snd _ _ _

private theorem eqToHom_pullback_fst {A B C : Scheme.{u}} (f : A ⟶ C)
    {g h : B ⟶ C} (e : g = h) :
    eqToHom (show pullback f g = pullback f h from by cases e; rfl) ≫
      pullback.fst f h = pullback.fst f g := by
  cases e
  simp

private theorem eqToHom_pullback_snd {A B C : Scheme.{u}} (f : A ⟶ C)
    {g h : B ⟶ C} (e : g = h) :
    eqToHom (show pullback f g = pullback f h from by cases e; rfl) ≫
      pullback.snd f h = pullback.snd f g := by
  cases e
  simp

private theorem absoluteFrobeniusPow_succ (X : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) (n : ℕ) :
    absoluteFrobenius X p hX ≫ absoluteFrobeniusPow X p hX n =
      absoluteFrobeniusPow X p hX (n + 1) := by
  simp [absoluteFrobeniusPow, pow_succ]

private theorem pullbackComp_hom_fst_fst_app {A B C : Scheme.{u}} (f : A ⟶ B)
    (g : B ⟶ C) (Y : Over C) :
    Over.Hom.left ((Over.pullbackComp f g).app Y).hom ≫
      pullback.fst (pullback.snd Y.hom g) f ≫ pullback.fst Y.hom g =
        pullback.fst Y.hom (f ≫ g) := by
  have hh := CategoryTheory.conjugateEquiv_counit
    (Over.mapPullbackAdj (f ≫ g)) ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    ((Over.mapComp f g).symm).hom Y
  simpa [Over.pullbackComp, Category.assoc] using congrArg Over.Hom.left hh

private theorem pullbackComp_inv_fst_fst_app {A B C : Scheme.{u}} (f : A ⟶ B)
    (g : B ⟶ C) (Y : Over C) :
    Over.Hom.left ((Over.pullbackComp f g).app Y).symm.hom ≫
      pullback.fst Y.hom (f ≫ g) =
      pullback.fst (pullback.snd Y.hom g) f ≫ pullback.fst Y.hom g := by
  rw [← pullbackComp_hom_fst_fst_app f g Y, ← Category.assoc, ← Over.comp_left]
  simp

/-- The canonical base-change identification of the Frobenius twist of the
`n`-fold twist with the `(n+1)`-fold twist. -/
public noncomputable def successiveTwistIso (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    (frobeniusTwist S p hS).obj (nFoldFrobeniusTwist S p hS n X) ≅
      nFoldFrobeniusTwist S p hS (n + 1) X :=
  ((Over.pullbackComp (absoluteFrobenius S p hS)
    (absoluteFrobeniusPow S p hS n)).app X).symm ≪≫
      eqToIso (by congr 1)

private theorem successiveTwistIso_left_fst (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    (successiveTwistIso S p hS n X).hom.left ≫
        pullback.fst X.hom (absoluteFrobeniusPow S p hS (n + 1)) =
      pullback.fst (pullback.snd X.hom (absoluteFrobeniusPow S p hS n))
          (absoluteFrobenius S p hS) ≫
        pullback.fst X.hom (absoluteFrobeniusPow S p hS n) := by
  have hp : absoluteFrobenius S p hS ≫ absoluteFrobeniusPow S p hS n =
      absoluteFrobeniusPow S p hS (n + 1) :=
    absoluteFrobeniusPow_succ S p hS n
  dsimp [successiveTwistIso]
  rw [Category.assoc, Over.eqToHom_left, eqToHom_pullback_fst X.hom hp]
  simpa [hp] using pullbackComp_inv_fst_fst_app
    (absoluteFrobenius S p hS) (absoluteFrobeniusPow S p hS n) X

private theorem successiveTwistIso_left_snd (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    (successiveTwistIso S p hS n X).hom.left ≫
        pullback.snd X.hom (absoluteFrobeniusPow S p hS (n + 1)) =
      pullback.snd (pullback.snd X.hom (absoluteFrobeniusPow S p hS n))
        (absoluteFrobenius S p hS) := by
  simpa [nFoldFrobeniusTwist, frobeniusTwist] using Over.w (successiveTwistIso S p hS n X).hom

/-- The composite of `n+1` successive relative Frobenius morphisms, beginning
with that of `X` and using the canonical base-change identifications between
successive twists. -/
public noncomputable def successiveRelativeFrobenius (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (X : Over S) :
    (n : ℕ) → X ⟶ nFoldFrobeniusTwist S p hS (n + 1) X
  | 0 => relativeFrobenius S p hS X ≫ (eqToIso (by congr 1)).hom
  | n + 1 => successiveRelativeFrobenius S p hS X n ≫
      relativeFrobenius S p hS (nFoldFrobeniusTwist S p hS (n + 1) X) ≫
        (successiveTwistIso S p hS (n + 1) X).hom

/-- The `1`-fold relative Frobenius is `successiveRelativeFrobenius S p hS X 0`. -/
private theorem nFoldRelativeFrobenius_one_eq_successive (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (X : Over S) :
    nFoldRelativeFrobenius S p hS (0 + 1) X =
      successiveRelativeFrobenius S p hS X 0 := by
  have hpowS : absoluteFrobeniusPow S p hS 1 = absoluteFrobenius S p hS := by
    simp [absoluteFrobeniusPow]
  have hX : IsInCharacteristic X.left p := isInCharacteristic_of_hom X.hom p hS
  have hpowX : absoluteFrobeniusPow X.left p hX 1 =
      absoluteFrobenius X.left p hX := by
    simp [absoluteFrobeniusPow]
  ext
  apply pullback.hom_ext
  · simp [successiveRelativeFrobenius, nFoldRelativeFrobenius,
      eqToHom_pullback_fst X.hom hpowS.symm, relativeFrobenius_fst, hpowX,
      pullback.lift_fst]
  · simp [successiveRelativeFrobenius, nFoldRelativeFrobenius,
      eqToHom_pullback_snd X.hom hpowS.symm, relativeFrobenius_snd,
      pullback.lift_snd]

/-- The first component of the `(n + 2)`-fold relative Frobenius is that of the `(n + 1)`-fold
relative Frobenius followed by relative Frobenius of the `(n + 1)`-fold twist and the
identification `successiveTwistIso`. -/
private theorem nFoldRelativeFrobenius_succ_left_fst (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    (nFoldRelativeFrobenius S p hS (n + 1 + 1) X).left ≫
        pullback.fst X.hom (absoluteFrobeniusPow S p hS (n + 1 + 1)) =
      (nFoldRelativeFrobenius S p hS (n + 1) X).left ≫
        (relativeFrobenius S p hS (nFoldFrobeniusTwist S p hS (n + 1) X)).left ≫
        (successiveTwistIso S p hS (n + 1) X).hom.left ≫
          pullback.fst X.hom (absoluteFrobeniusPow S p hS (n + 1 + 1)) := by
  have hX : IsInCharacteristic X.left p := isInCharacteristic_of_hom X.hom p hS
  have hY : IsInCharacteristic
      (nFoldFrobeniusTwist S p hS (n + 1) X).left p :=
    isInCharacteristic_of_hom (nFoldFrobeniusTwist S p hS (n + 1) X).hom p hS
  calc
    _ = absoluteFrobeniusPow X.left p hX (n + 1 + 1) :=
      nFoldRelativeFrobenius_fst S p hS (n + 1 + 1) X
    _ = absoluteFrobenius X.left p hX ≫
          absoluteFrobeniusPow X.left p hX (n + 1) :=
      (absoluteFrobeniusPow_succ X.left p hX (n + 1)).symm
    _ = absoluteFrobenius X.left p hX ≫
          ((nFoldRelativeFrobenius S p hS (n + 1) X).left ≫
            pullback.fst X.hom (absoluteFrobeniusPow S p hS (n + 1))) := by
      rw [nFoldRelativeFrobenius_fst]
    _ = (nFoldRelativeFrobenius S p hS (n + 1) X).left ≫
          (absoluteFrobenius (nFoldFrobeniusTwist S p hS (n + 1) X).left p hY ≫
            pullback.fst X.hom (absoluteFrobeniusPow S p hS (n + 1))) := by
      rw [← Category.assoc,
        absoluteFrobenius_naturality
          (nFoldRelativeFrobenius S p hS (n + 1) X).left p hX hY]
      simp only [Category.assoc]
    _ = (nFoldRelativeFrobenius S p hS (n + 1) X).left ≫
          ((relativeFrobenius S p hS
              (nFoldFrobeniusTwist S p hS (n + 1) X)).left ≫
            pullback.fst (nFoldFrobeniusTwist S p hS (n + 1) X).hom
              (absoluteFrobenius S p hS) ≫
            pullback.fst X.hom (absoluteFrobeniusPow S p hS (n + 1))) := by
      rw [← relativeFrobenius_fst S p hS (nFoldFrobeniusTwist S p hS (n + 1) X)]
      simp only [Category.assoc]
    _ = _ := by
      rw [successiveTwistIso_left_fst]
      rfl

/-- The second component of the `(n + 2)`-fold relative Frobenius is that of the `(n + 1)`-fold
relative Frobenius followed by relative Frobenius of the `(n + 1)`-fold twist and the
identification `successiveTwistIso`. -/
private theorem nFoldRelativeFrobenius_succ_left_snd (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    (nFoldRelativeFrobenius S p hS (n + 1 + 1) X).left ≫
        pullback.snd X.hom (absoluteFrobeniusPow S p hS (n + 1 + 1)) =
      (nFoldRelativeFrobenius S p hS (n + 1) X).left ≫
        (relativeFrobenius S p hS (nFoldFrobeniusTwist S p hS (n + 1) X)).left ≫
        (successiveTwistIso S p hS (n + 1) X).hom.left ≫
          pullback.snd X.hom (absoluteFrobeniusPow S p hS (n + 1 + 1)) := by
  calc
    _ = X.hom :=
      nFoldRelativeFrobenius_snd S p hS (n + 1 + 1) X
    _ = _ := by
      rw [successiveTwistIso_left_snd S p hS (n + 1) X]
      show X.hom =
        (nFoldRelativeFrobenius S p hS (n + 1) X).left ≫
          (relativeFrobenius S p hS
            (nFoldFrobeniusTwist S p hS (n + 1) X)).left ≫
          pullback.snd
            (nFoldFrobeniusTwist S p hS (n + 1) X).hom
            (absoluteFrobenius S p hS)
      rw [relativeFrobenius_snd S p hS (nFoldFrobeniusTwist S p hS (n + 1) X)]
      show X.hom =
        (nFoldRelativeFrobenius S p hS (n + 1) X).left ≫
          pullback.snd X.hom (absoluteFrobeniusPow S p hS (n + 1))
      exact (nFoldRelativeFrobenius_snd S p hS (n + 1) X).symm

/-- The `(n+1)`-fold relative Frobenius is the composite of the relative Frobenius morphisms of
`X` and its first `n` successive twists, under the canonical identifications. -/
@[stacks 0CCG "successive_composition"]
public theorem nFoldRelativeFrobenius_eq_successiveRelativeFrobenius
    (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    nFoldRelativeFrobenius S p hS (n + 1) X =
      successiveRelativeFrobenius S p hS X n := by
  induction n with
  | zero => exact nFoldRelativeFrobenius_one_eq_successive S p hS X
  | succ n ih =>
      simp only [successiveRelativeFrobenius]
      rw [← ih]
      ext
      apply pullback.hom_ext
      · simpa only [Over.comp_left, Category.assoc] using
          nFoldRelativeFrobenius_succ_left_fst S p hS n X
      · simpa only [Over.comp_left, Category.assoc] using
          nFoldRelativeFrobenius_succ_left_snd S p hS n X

private theorem eqToPullback_fst {S : Scheme.{u}} {f g : S ⟶ S} (h : f = g)
    (X : Over S) :
    Over.Hom.left (eqToIso (by rw [h] : (Over.pullback f).obj X =
      (Over.pullback g).obj X)).hom ≫ pullback.fst X.hom g =
        pullback.fst X.hom f := by
  cases h
  rfl

/-- The canonical identification between first twisting and then twisting `m`
more times, and doing these twists in the opposite order. -/
public noncomputable def frobeniusTwistCommIso (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (m : ℕ) (X : Over S) :
    (nFoldFrobeniusTwist S p hS m ((frobeniusTwist S p hS).obj X)) ≅
      (frobeniusTwist S p hS).obj (nFoldFrobeniusTwist S p hS m X) := by
  let f := absoluteFrobenius S p hS
  let fm := absoluteFrobeniusPow S p hS m
  have hcomm : fm ≫ f = f ≫ fm := by
    change ((End.of f) * (End.of f) ^ m).asHom =
      ((End.of f) ^ m * End.of f).asHom
    congr 1
    rw [← pow_succ', ← pow_succ]
  let e : (Over.pullback (fm ≫ f)).obj X ≅
      (Over.pullback (f ≫ fm)).obj X := eqToIso (by rw [hcomm])
  exact ((Over.pullbackComp fm f).app X).symm ≪≫ e ≪≫ (Over.pullbackComp f fm).app X

/-- Under the canonical identification of the two orders of Frobenius twisting, relative
Frobenius on the `m`-fold twist is the `m`-fold base change of relative Frobenius on `X`. -/
@[stacks 0CCG "frobenius_on_twists", sga "3 VIIA 4.3.2" "more general"]
public theorem relativeFrobenius_nFoldFrobeniusTwist (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hS : IsInCharacteristic S p) (m : ℕ) (X : Over S) :
    (Over.pullback (absoluteFrobeniusPow S p hS m)).map
        (relativeFrobenius S p hS X) ≫
      (frobeniusTwistCommIso S p hS m X).hom =
        relativeFrobenius S p hS (nFoldFrobeniusTwist S p hS m X) := by
  let f := absoluteFrobenius S p hS
  let fm := absoluteFrobeniusPow S p hS m
  have hcomm : fm ≫ f = f ≫ fm := by
    show ((End.of f) * (End.of f) ^ m).asHom =
      ((End.of f) ^ m * (End.of f)).asHom
    congr 1
    rw [← pow_succ', ← pow_succ]
  let Z := nFoldFrobeniusTwist S p hS m X
  let g : Z ⟶ (frobeniusTwist S p hS).obj Z :=
    (Over.pullback fm).map (relativeFrobenius S p hS X) ≫
      (frobeniusTwistCommIso S p hS m X).hom
  show g = relativeFrobenius S p hS Z
  apply eq_relativeFrobenius S p hS Z g
  · apply pullback.hom_ext
    · dsimp [g]
      simp only [Over.pullback_map_left]
      dsimp only [frobeniusTwistCommIso]
      simp only [Iso.trans_hom, Over.comp_left, Z, nFoldFrobeniusTwist,
        Over.pullback_obj_hom, Category.assoc]
      rw [pullbackComp_hom_fst_fst_app, eqToPullback_fst hcomm X,
        pullbackComp_inv_fst_fst_app]
      let h := pullback.fst X.hom fm ≫ (relativeFrobenius S p hS X).left
      let k := pullback.snd X.hom fm
      have hw : h ≫ pullback.snd X.hom f = k ≫ fm := by
        dsimp [h, k]
        calc
          (pullback.fst X.hom fm ≫ (relativeFrobenius S p hS X).left) ≫
              pullback.snd X.hom f = pullback.fst X.hom fm ≫ X.hom := by
                rw [Category.assoc, relativeFrobenius_snd]
          _ = pullback.snd X.hom fm ≫ fm := pullback.condition
      calc
        _ = h ≫ pullback.fst X.hom f := by
                show (pullback.lift h k hw ≫
                  pullback.fst (pullback.snd X.hom f) fm) ≫
                  pullback.fst X.hom f = _
                rw [pullback.lift_fst]
        _ = pullback.fst X.hom fm ≫ absoluteFrobenius X.left p
              (isInCharacteristic_of_hom X.hom p hS) := by
                rw [Category.assoc, relativeFrobenius_fst]
        _ = absoluteFrobenius ((Over.pullback fm).obj X).left p
              (isInCharacteristic_of_hom (pullback.snd X.hom fm) p hS) ≫
                pullback.fst X.hom fm :=
          (absoluteFrobenius_naturality
            (pullback.fst X.hom fm) p
            (isInCharacteristic_of_hom (pullback.snd X.hom fm) p hS)
            (isInCharacteristic_of_hom X.hom p hS)).symm
    · have hZ : IsInCharacteristic Z.left p := isInCharacteristic_of_hom Z.hom p hS
      show (g.left ≫ pullback.fst Z.hom f) ≫ Z.hom =
        absoluteFrobenius Z.left p hZ ≫ Z.hom
      calc
        (g.left ≫ pullback.fst Z.hom f) ≫ Z.hom =
            g.left ≫ (pullback.fst Z.hom f ≫ Z.hom) := Category.assoc _ _ _
        _ = g.left ≫ (pullback.snd Z.hom f ≫ f) := by rw [pullback.condition]
        _ = (g.left ≫ pullback.snd Z.hom f) ≫ f := (Category.assoc _ _ _).symm
        _ = Z.hom ≫ f := by
          simpa [Category.assoc, frobeniusTwist_obj_hom] using
            congrArg (fun k => k ≫ f) (Over.w g)
        _ = absoluteFrobenius Z.left p hZ ≫ Z.hom :=
          (absoluteFrobenius_naturality Z.hom p hZ hS).symm
  · simpa [frobeniusTwist_obj_hom] using Over.w g

/-- The composite of the successive Frobenius base changes of the relative
Frobenius of `X`, with canonical identifications of successive twists. -/
public noncomputable def twistedRelativeFrobeniusComposite
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    (n : ℕ) → X ⟶ nFoldFrobeniusTwist S p hS (n + 1) X
  | 0 => relativeFrobenius S p hS X ≫ (eqToIso (by congr 1)).hom
  | n + 1 => twistedRelativeFrobeniusComposite S p hS X n ≫
      (Over.pullback (absoluteFrobeniusPow S p hS (n + 1))).map
        (relativeFrobenius S p hS X) ≫
      (frobeniusTwistCommIso S p hS (n + 1) X).hom ≫
      (successiveTwistIso S p hS (n + 1) X).hom

/-- The `(n+1)`-fold relative Frobenius is the composite of the first `n+1` Frobenius base
changes of the relative Frobenius of `X`. -/
@[stacks 0CCG "twisted_composition"]
public theorem nFoldRelativeFrobenius_eq_twistedRelativeFrobeniusComposite
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    nFoldRelativeFrobenius S p hS (n + 1) X =
      twistedRelativeFrobeniusComposite S p hS X n := by
  induction n with
  | zero => rw [nFoldRelativeFrobenius_eq_successiveRelativeFrobenius]; rfl
  | succ n ih =>
      rw [nFoldRelativeFrobenius_eq_successiveRelativeFrobenius]
      simp only [successiveRelativeFrobenius, twistedRelativeFrobeniusComposite,
        ← relativeFrobenius_nFoldFrobeniusTwist, Category.assoc]
      rw [← nFoldRelativeFrobenius_eq_successiveRelativeFrobenius S p hS n X, ih]

end AlgebraicGeometry

end
