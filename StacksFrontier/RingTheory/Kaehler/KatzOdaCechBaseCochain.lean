module

public import StacksFrontier.RingTheory.Kaehler.KatzOdaCechMul

/-!
# The base cochain of a form, given by restrictions of a global section

In the setting of `Stacks.KatzOda.Cech` (algebras `B_t` over the Čech intersections of a covering,
and a complex `P` of presheaves whose terms over the intersections are identified with the Kähler
forms of `B_t`), the base cochain of a form `ν` of the base is the Čech `0`-cochain whose value
over `U_t` is the pull-back of `ν`. When a family of sections over the intersections is known to
be carried to the pull-backs of `ν`, it is the base cochain.

## Main definitions

* `Stacks.KatzOda.Cech.FormsBaseData`: forms data together with sections over the intersections
  that are identified with the pull-backs of forms of the base.

## Main results

* `Stacks.KatzOda.Cech.FormsBaseData.baseCochain_eq`: the base cochain is the given family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.CechComplex

universe w v u

namespace Stacks.KatzOda.Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} [Fintype ι]
  [DecidableEq ι] {U : ι → C} {R A : CommRingCat.{w}} {gR : R ⟶ A} (D : ChartData (ι := ι) gR)
  {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ}

/-- **Forms with sections representing the forms of the base**: forms data together with, for
every form `ν` of the base, sections over the intersections that are identified with the
pull-backs of `ν`. -/
structure FormsBaseData extends FormsData U D D.ψ D.ψ_ρ P where
  /-- The section over the intersection selected by `t` attached to a form of the base. -/
  base : ∀ (b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι),
    ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR) → (P.X b).obj (op (inter U t))
  /-- The identifications with Kähler forms carry these sections to the pull-backs. -/
  e'_base : ∀ (b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
      (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)),
    letI := instAddCommGroup b t
    letI := instModule b t
    e' b t (s b t (base b t ν)) = baseForm D b t ν

variable {D}

omit [Fintype ι] [DecidableEq ι] in
/-- **The base cochain of a form is the given family of sections.** -/
theorem FormsBaseData.baseCochain_eq (BD : FormsBaseData (U := U) D (P := P)) (b : ℕ)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) :
    baseCochain D BD.toFormsData b ν = fun t => BD.base b t ν :=
  funext fun t => ((BD.toFormsData.e b t).symm_apply_eq).2 (BD.e'_base b t ν).symm

end Stacks.KatzOda.Cech

end
