module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Infinity

/-!
# The closed points of the projective line over an algebraically closed field

Let `Kf` be an algebraically closed field and `S = Spec Kf`. The closed points of `ℙ¹_S` are
exactly the point of the affine chart attached to a global function `t` on the base
(`Stacks.Chow.lineSection`) and the point at infinity (`Stacks.Chow.lineInfinitySection`).

A closed point of `ℙ¹_S` gives an `S`-point by `AlgebraicGeometry.pointOfClosedPoint`: `ℙ¹_S ⟶ S`
is locally of finite type and `Kf` is algebraically closed, so the residue field at a closed point
is `Kf` itself.

## Main definitions

* `Stacks.Chow.closedPointLineSection`: the `S`-point of `ℙ¹_S` at a closed point of `ℙ¹_S`.
* `Stacks.Chow.closedPointSection`: the section `X ⟶ X ×_S ℙ¹_S` of the family at that point.

## Main results

* `Stacks.Chow.eq_affineLineSection_of_comp_eq`: every `S`-point of `𝔸¹_S` is the section at its
  own coordinate.
* `Stacks.Chow.exists_eq_lineSection_or_eq_lineInfinitySection`: every `S`-point of `ℙ¹_S` over
  the spectrum of an algebraically closed field is a point of the affine chart or the point at
  infinity.
* `Stacks.Chow.exists_closedPointSection_eq_pointSection_or_eq_infinitySection`: the section of
  the family at a closed point of `ℙ¹_S` is `Stacks.Chow.pointSection` at a global function on the
  base, or `Stacks.Chow.infinitySection`.
* `Stacks.Chow.closedPointSection_ne`: distinct closed points give distinct sections.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The `S`-points of the affine chart -/

/-- A ring map out of `ULift ℤ` is unique. -/
private theorem ringHom_uliftInt_ext {A : Type u} [Ring A]
    (f g : ULift.{u} ℤ →+* A) : f = g := by
  refine RingHom.ext fun a ↦ ?_
  have h : ((a.down : ℤ) : ULift.{u} ℤ) = a := rfl
  rw [← h, map_intCast, map_intCast]

/-- A ring map out of `ℤ[T]` is determined by the image of the coordinate. -/
private theorem polynomial_uliftInt_ringHom_ext {A : Type u} [Ring A]
    (f g : Polynomial (ULift.{u} ℤ) →+* A) (h : f Polynomial.X = g Polynomial.X) : f = g :=
  Polynomial.ringHom_ext
    (fun a ↦ RingHom.congr_fun (ringHom_uliftInt_ext (f.comp Polynomial.C)
      (g.comp Polynomial.C)) a) h

/-- Two morphisms to the affine chart `𝔸¹_S` over `S` with the same coordinate agree. -/
theorem hom_ext_of_appTop_affineCoordinate {T S : Scheme.{u}} (f g : T ⟶ affineLineOver S)
    (hfst : f ≫ affineLineOverHom S = g ≫ affineLineOverHom S)
    (hcoord : f.appTop (affineCoordinate S) = g.appTop (affineCoordinate S)) : f = g := by
  refine pullback.hom_ext hfst ?_
  refine ext_to_Spec (R := Polynomial (ULift.{u} ℤ))
    (CommRingCat.hom_ext (polynomial_uliftInt_ringHom_ext _ _ ?_))
  exact hcoord

/-- Every `S`-point of the affine chart `𝔸¹_S` is the section at its own coordinate. -/
theorem eq_affineLineSection_of_comp_eq {S : Scheme.{u}} (τ : S ⟶ affineLineOver S)
    (hτ : τ ≫ affineLineOverHom S = 𝟙 S) :
    τ = affineLineSection S (τ.appTop (affineCoordinate S)) := by
  refine hom_ext_of_appTop_affineCoordinate τ _ ?_ ?_
  · rw [hτ, affineLineSection_comp]
  · rw [affineLineSection_appTop_affineCoordinate]

/-! ### The `S`-points of the projective line over a field -/

section Field

variable (Kf : Type u) [Field Kf] [IsAlgClosed Kf]

/-- Every `S`-point of `ℙ¹_S`, for `S` the spectrum of an algebraically closed field, is a point of
the affine chart or the point at infinity. -/
theorem exists_eq_lineSection_or_eq_lineInfinitySection {S : Scheme.{u}}
    (hS : S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
    (σ : S ⟶ relativeProjectiveLine S)
    (hσ : σ ≫ (relativeProjectiveLine S ↘ S) = 𝟙 S) :
    (∃ t : Γ(S, ⊤), σ = lineSection S t) ∨ σ = lineInfinitySection S := by
  subst hS
  revert σ
  set K := AlgebraicGeometry.Spec (CommRingCat.of Kf)
  intro σ hσ
  by_cases hmem : σ.base default ∈ Set.range (affineChart K).base
  · have hrange : Set.range σ.base ⊆ Set.range (affineChart K).base := by
      rintro z ⟨x, rfl⟩
      rw [Subsingleton.elim x default]
      exact hmem
    have hfac : IsOpenImmersion.lift (affineChart K) σ hrange ≫ affineChart K = σ :=
      IsOpenImmersion.lift_fac _ _ _
    have hτ : IsOpenImmersion.lift (affineChart K) σ hrange ≫ affineLineOverHom K = 𝟙 _ := by
      rw [show affineLineOverHom K = affineChart K ≫ (relativeProjectiveLine K ↘ K) from
        (affineChart_comp _).symm, ← Category.assoc, hfac, hσ]
    refine Or.inl ⟨(IsOpenImmersion.lift (affineChart K) σ hrange).appTop (affineCoordinate K), ?_⟩
    rw [lineSection, ← eq_affineLineSection_of_comp_eq _ hτ, hfac]
  · refine Or.inr ?_
    obtain ⟨x, hx⟩ : σ.base default ∈ Set.range (lineInfinitySection K).base := by
      rw [← compl_range_affineChart]
      exact hmem
    refine ext_of_apply_closedPoint_eq (relativeProjectiveLine K ↘ K) hσ
      (lineInfinitySection_comp _) ?_
    have h1 := congrArg (fun z : ↥K ↦ σ.base z)
      (Subsingleton.elim (IsLocalRing.closedPoint Kf) (default : ↥K))
    have h2 := congrArg (fun z : ↥K ↦ (lineInfinitySection K).base z)
      (Subsingleton.elim x (IsLocalRing.closedPoint Kf))
    exact h1.trans (hx.symm.trans h2)

end Field

/-! ### The section at a closed point -/

section ClosedPoint

variable (Kf : Type u) [Field Kf] [IsAlgClosed Kf] {X S : Scheme.{u}}
  (hS : S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
  (a : relativeProjectiveLine S) (ha : IsClosed {a})

/-- The `S`-point of `ℙ¹_S` at a closed point of `ℙ¹_S`: the `Kf`-point
`AlgebraicGeometry.pointOfClosedPoint`, read on the base through `hS`. -/
def closedPointLineSection : S ⟶ relativeProjectiveLine S :=
  haveI : LocallyOfFiniteType ((relativeProjectiveLine S ↘ S) ≫ eqToHom hS) := inferInstance
  eqToHom hS ≫ pointOfClosedPoint ((relativeProjectiveLine S ↘ S) ≫ eqToHom hS) a ha

/-- The point at a closed point is a section of the structure morphism of `ℙ¹_S`. -/
theorem closedPointLineSection_comp :
    closedPointLineSection Kf hS a ha ≫ (relativeProjectiveLine S ↘ S) = 𝟙 S := by
  have : LocallyOfFiniteType ((relativeProjectiveLine S ↘ S) ≫ eqToHom hS) := inferInstance
  have h := pointOfClosedPoint_comp ((relativeProjectiveLine S ↘ S) ≫ eqToHom hS) a ha
  rw [← cancel_mono (eqToHom hS), closedPointLineSection, Category.id_comp]
  simp only [Category.assoc]
  rw [h, Category.comp_id]

/-- The point at a closed point lands at that point. -/
theorem closedPointLineSection_apply (x : S) :
    (closedPointLineSection Kf hS a ha).base x = a := by
  have : LocallyOfFiniteType ((relativeProjectiveLine S ↘ S) ≫ eqToHom hS) := inferInstance
  exact pointOfClosedPoint_apply ((relativeProjectiveLine S ↘ S) ≫ eqToHom hS) a ha _

/-- The section `X ⟶ X ×_S ℙ¹_S` of the family at a closed point of `ℙ¹_S`. -/
def closedPointSection (f : X ⟶ S) : X ⟶ projectiveLineProduct f :=
  pullback.lift (𝟙 X) (f ≫ closedPointLineSection Kf hS a ha) (by
    rw [Category.id_comp, Category.assoc, closedPointLineSection_comp, Category.comp_id])

/-- The section at a closed point composed with the first projection is the identity of `X`. -/
@[simp]
theorem closedPointSection_comp_fst (f : X ⟶ S) :
    closedPointSection Kf hS a ha f ≫ pullback.fst f (relativeProjectiveLine S ↘ S) = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The section at a closed point composed with the second projection is `f` followed by the
`S`-point `closedPointLineSection` of `ℙ¹_S`. -/
@[simp]
theorem closedPointSection_comp_snd (f : X ⟶ S) :
    closedPointSection Kf hS a ha f ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      f ≫ closedPointLineSection Kf hS a ha :=
  pullback.lift_snd _ _ _

/-- The section of the family at a closed point of `ℙ¹_S` is the section at a point of the affine
chart, or the infinity section. -/
theorem exists_closedPointSection_eq_pointSection_or_eq_infinitySection (f : X ⟶ S) :
    (∃ t : Γ(S, ⊤), closedPointSection Kf hS a ha f = pointSection f t) ∨
      closedPointSection Kf hS a ha f = infinitySection f := by
  have hext : ∀ s : X ⟶ projectiveLineProduct f, s ≫ pullback.fst f (relativeProjectiveLine S ↘ S)
      = 𝟙 X → s ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
        f ≫ closedPointLineSection Kf hS a ha → closedPointSection Kf hS a ha f = s :=
    fun s h₁ h₂ ↦ pullback.hom_ext (by rw [closedPointSection_comp_fst, h₁])
      (by rw [closedPointSection_comp_snd, h₂])
  rcases exists_eq_lineSection_or_eq_lineInfinitySection Kf hS (closedPointLineSection Kf hS a ha)
    (closedPointLineSection_comp Kf hS a ha) with ⟨t, ht⟩ | ht
  · exact Or.inl ⟨t, hext _ (pointSection_comp_fst f t) (by rw [pointSection_comp_snd, ht])⟩
  · exact Or.inr (hext _ (infinitySection_comp_fst f) (by rw [infinitySection_comp_snd, ht]))

/-- Distinct closed points of `ℙ¹_S` give distinct sections of the family. -/
theorem closedPointSection_ne (f : X ⟶ S) [Nonempty X] (b : relativeProjectiveLine S)
    (hb : IsClosed {b}) (hab : a ≠ b) :
    closedPointSection Kf hS a ha f ≠ closedPointSection Kf hS b hb f := by
  intro h
  refine hab ?_
  have h' : f ≫ closedPointLineSection Kf hS a ha = f ≫ closedPointLineSection Kf hS b hb := by
    rw [← closedPointSection_comp_snd Kf hS a ha f, ← closedPointSection_comp_snd Kf hS b hb f, h]
  have hx := congrArg (fun g : X ⟶ relativeProjectiveLine S ↦ g.base (Classical.arbitrary X)) h'
  rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, closedPointLineSection_apply,
    closedPointLineSection_apply] at hx

end ClosedPoint

end Stacks.Chow

end
