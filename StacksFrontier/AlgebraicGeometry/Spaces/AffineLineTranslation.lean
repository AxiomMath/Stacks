module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelation

/-!
# Translation of the affine line by the integers

Over a field `k` the integers act on the affine line `𝔸¹_k` by translation, the generator
sending the standard coordinate to that coordinate plus one. In characteristic zero no
nonidentity translation fixes a point of `𝔸¹_k` together with the residue field there, which
is the hypothesis under which the fppf sheaf quotient of a group action is an algebraic
space.

## Main definitions

* `AlgebraicGeometry.AffineLineTranslation.translationByOne` is translation by one on the
  affine line over `k`.
* `AlgebraicGeometry.AffineLineTranslation.translationAction` is the resulting action of the
  integers.

## Main results

* `AlgebraicGeometry.AffineLineTranslation.translationAction_apply` identifies the action of
  an integer with translation of the standard coordinate by that integer.

## Implementation notes

The affine line is Mathlib's affine space with a singleton coordinate index, reusing
`AlgebraicGeometry.AffineLineInvolution.affineLine`. The action of the additive integers is
written as an action of `Multiplicative ℤ`, so that its group law is addition.

## References

* [Stacks Project, Tag 02Z7](https://stacks.math.columbia.edu/tag/02Z7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Multiplicative

universe u

namespace AlgebraicGeometry

/-- Transporting the evaluation of a global section at a point along an equality of points
is the evaluation at the other point. -/
theorem Scheme.residueFieldCongr_Γevaluation_apply {X : Scheme.{u}} {x y : X} (h : x = y)
    (s : Γ(X, ⊤)) :
    (X.residueFieldCongr h).hom (X.Γevaluation x s) = X.Γevaluation y s := by
  subst h
  rfl

namespace AffineLineTranslation

open AffineLineInvolution

variable (k : Type u) [Field k]

/-- Translation by one on the affine line over `k`, sending the standard coordinate to that
coordinate plus one. -/
def translationByOne : Aut (affineLine k) :=
  .of <| Over.isoMk
    { hom := AffineSpace.homOfVector (affineLine k).hom
        (fun _ => AffineSpace.coord (Spec (.of k)) PUnit.unit +
          (1 : Γ(AffineSpace PUnit.{u + 1} (Spec (.of k)), ⊤)))
      inv := AffineSpace.homOfVector (affineLine k).hom
        (fun _ => AffineSpace.coord (Spec (.of k)) PUnit.unit -
          (1 : Γ(AffineSpace PUnit.{u + 1} (Spec (.of k)), ⊤)))
      hom_inv_id := by
        apply AffineSpace.hom_ext
        · simp [affineLine]
        · intro i
          simp [AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord]
      inv_hom_id := by
        apply AffineSpace.hom_ext
        · simp [affineLine]
        · intro i
          simp [AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord] }
    (AffineSpace.homOfVector_over _ _)

/-- **Stacks 02Z7.** The action of the integers on the affine line over `k` by
translation. -/
@[stacks 02Z7 "translation_quotient"]
def translationAction : Multiplicative ℤ →* Aut (affineLine k) :=
  zpowersHom _ (translationByOne k)

/-- **Stacks 02Z7.** The integer `n` acts on the standard coordinate of the affine line by
`x ↦ x + n`. -/
@[stacks 02Z7 "translation_quotient"]
theorem translationAction_apply (n : ℤ) :
    ((translationAction k (Multiplicative.ofAdd n)).asIso.hom.left).appTop
      (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      AffineSpace.coord (Spec (.of k)) PUnit.unit +
        (n : Γ(AffineSpace PUnit.{u + 1} (Spec (.of k)), ⊤)) := by
  let a := translationByOne k
  let c : Γ((affineLine k).left, ⊤) := AffineSpace.coord (Spec (.of k)) PUnit.unit
  change ((a ^ n).asIso.hom.left).appTop c = c + (n : Γ((affineLine k).left, ⊤))
  have hgen : a.asIso.hom.left.appTop c = c + ((1 : ℤ) : Γ((affineLine k).left, ⊤)) := by
    change ((translationByOne k).asIso.hom.left).appTop c = _
    simp [c, translationByOne]
  have hgen_inv : a⁻¹.asIso.hom.left.appTop c = c + ((-1 : ℤ) : Γ((affineLine k).left, ⊤)) := by
    change ((translationByOne k).asIso.inv.left).appTop c = _
    simp [c, translationByOne, sub_eq_add_neg]
  have hmul : ∀ (x y : Aut (affineLine k)) (p q : ℤ),
      x.asIso.hom.left.appTop c = c + p → y.asIso.hom.left.appTop c = c + q →
        (x * y).asIso.hom.left.appTop c = c + (p + q : ℤ) := by
    intro x y p q hx hy
    change (y.asIso.hom.left ≫ x.asIso.hom.left).appTop c = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hx, map_add, map_intCast, hy]
    push_cast
    ring
  induction n using Int.induction_on with
  | zero =>
      rw [zpow_zero]
      change Scheme.Hom.appTop (𝟙 (affineLine k).left) c = _
      simp
  | succ i ih =>
      rw [zpow_add_one]
      simpa using hmul _ _ i 1 ih hgen
  | pred i ih =>
      rw [zpow_sub_one]
      simpa [sub_eq_add_neg] using hmul _ _ (-i) (-1) ih hgen_inv

/-- The affine line over `k` as an object of a big fppf site over `Spec k` containing it. -/
def siteAffineLine (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (hU : B.Contains (affineLine k).left) : BigFppfOver B (Spec (.of k)) hS :=
  Over.mk (ObjectProperty.homMk (affineLine k).hom : B.obj hU ⟶ B.obj hS)

/-- **Stacks 02Z7.** The fppf sheaf quotient of the affine line over `k` by integer
translations. -/
@[stacks 02Z7 "translation_quotient"]
abbrev translationQuotient (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (hU : B.Contains (affineLine k).left)
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u :=
  Space.actionQuotient (Multiplicative ℤ) B hS (siteAffineLine k B hS hU)
    (translationAction k)

/-- In characteristic zero no nonidentity translation of the affine line fixes a point
together with the residue field there. -/
theorem translationAction_residueFieldFaithful [CharZero k] :
    Space.ActsNontriviallyOnFixedResidueFields (affineLine k) (Multiplicative ℤ)
      (translationAction k) := by
  intro g x hx hne hres
  have hn : g.toAdd ≠ 0 := by
    intro hzero
    exact hne (by simpa [hzero] using (ofAdd_toAdd g).symm)
  have hg : Multiplicative.ofAdd g.toAdd = g := by simp
  set U : Scheme.{u} := AffineSpace PUnit.{u + 1} (Spec (.of k)) with hU
  set f : U ⟶ U := (translationAction k g).asIso.hom.left with hf
  have heval : U.Γevaluation x (f.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) =
      U.Γevaluation x (AffineSpace.coord (Spec (.of k)) PUnit.unit) := by
    calc
      U.Γevaluation x (f.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) =
          (f.residueFieldMap x).hom (U.Γevaluation (f x)
            (AffineSpace.coord (Spec (.of k)) PUnit.unit)) :=
        (Scheme.Γevaluation_naturality_apply f x _).symm
      _ = (U.residueFieldCongr hx).hom (U.Γevaluation (f x)
            (AffineSpace.coord (Spec (.of k)) PUnit.unit)) :=
        congrArg (fun φ : CommRingCat.Hom _ _ =>
          φ.hom (U.Γevaluation (f x) (AffineSpace.coord (Spec (.of k)) PUnit.unit))) hres
      _ = U.Γevaluation x (AffineSpace.coord (Spec (.of k)) PUnit.unit) :=
        Scheme.residueFieldCongr_Γevaluation_apply hx _
  have hformula : f.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      AffineSpace.coord (Spec (.of k)) PUnit.unit + (g.toAdd : Γ(U, ⊤)) := by
    simpa [hf, hg] using translationAction_apply k g.toAdd
  have hcoord := congrArg (fun s : Γ(U, ⊤) => U.Γevaluation x s) hformula
  simp only [map_add, map_intCast] at hcoord
  rw [heval] at hcoord
  have hzero : U.Γevaluation x ((g.toAdd : ℤ) : Γ(U, ⊤)) = 0 := by
    simp only [map_intCast]
    linear_combination -hcoord
  have hunit : IsUnit ((g.toAdd : ℤ) : Γ(U, ⊤)) := by
    simpa using IsUnit.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop).hom : k →+* Γ(U, ⊤))
      (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hn))
  exact (IsUnit.map (U.Γevaluation x).hom hunit).ne_zero hzero

/-- The affine line over `k` satisfies the size cutoff of any big fppf site containing
`Spec k`. -/
theorem contains_affineLine (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k))) :
    B.Contains (affineLine k).left := by
  rw [affineLine]
  change (AffineSpace PUnit.{u + 1} (Spec (.of k))).size < B.cutoff
  rw [Scheme.size_congr (AffineSpace.SpecIso PUnit.{u + 1} (.of k))]
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k
    (MvPolynomial PUnit.{u + 1} k) hS

end AffineLineTranslation

end AlgebraicGeometry

end
