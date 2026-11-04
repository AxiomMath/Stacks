module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback

/-!
# A unital homomorphism is invertible in degree zero

Let `A` and `B` be sheaves of graded algebras over a sheaf of rings `R`, each of whose degree-zero
pieces is the free rank-one sheaf `R` by an isomorphism carrying the algebra unit to `1`. Then
**every** unital homomorphism `A ⟶ B` is invertible in degree zero, whatever it does in the other
degrees: on a local section it is determined by unitality and linearity, a degree-zero section
being `c • 1` for a unique function `c` on the base.

This is the degree-zero half of a degreewise comparison of graded algebras, and it is the half
that carries no information about the comparison map — exactly as the negative degrees carry none,
both sides vanishing there. Only the positive degrees are a real computation.

## Main results

* `SheafOfModules.GradedAlgebra.pieceZeroIsoUnit_smul_one` and
  `SheafOfModules.GradedAlgebra.inv_pieceZeroIsoUnit_apply`: the identification of degree zero with
  the unit sheaf recovers the scalar, and its inverse multiplies the algebra unit by it.
* `SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero`: **a unital homomorphism between graded
  algebras whose degree-zero pieces are both the unit sheaf is invertible in degree zero.**

## Implementation notes

**The proof is that one composite is the identity of the unit sheaf, read on sections.** A section
of the unit sheaf over `U` is a function `c` on `U`; it is carried by the inverse of the first
identification to `c • 1_A`, by the homomorphism to `c • 1_B` — linearity and unitality — and by
the second identification back to `c`. The composite being the identity, the degree-zero component
is the composite of the two identifications, hence invertible.

**The hypotheses are the shape
`SheafOfModules.GradedAlgebra.bijective_smul_one_of_pieceZeroIsoUnit` already uses**, so a graded
algebra for which that lemma is available satisfies these too with no further work.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **The identification of degree zero with the unit sheaf recovers the scalar.** It carries
`c • 1` to `c`, by linearity and the normalisation of the unit. -/
theorem pieceZeroIsoUnit_smul_one (A : GradedAlgebra.{w, w} R)
    (e : A.piece 0 ≅ SheafOfModules.unit R)
    (he : ∀ U : Cᵒᵖ, e.hom.val.app U (A.one.eval U) = (1 : R.obj.obj U)) (U : Cᵒᵖ)
    (c : R.obj.obj U) : e.hom.val.app U (c • A.one.eval U) = c := by
  rw [map_smul, he]
  exact _root_.mul_one c

/-- **The inverse of the degree-zero identification multiplies the algebra unit.** -/
theorem inv_pieceZeroIsoUnit_apply (A : GradedAlgebra.{w, w} R)
    (e : A.piece 0 ≅ SheafOfModules.unit R)
    (he : ∀ U : Cᵒᵖ, e.hom.val.app U (A.one.eval U) = (1 : R.obj.obj U)) (U : Cᵒᵖ)
    (c : R.obj.obj U) : e.inv.val.app U c = c • A.one.eval U := by
  refine Eq.trans (congrArg (e.inv.val.app U)
    (pieceZeroIsoUnit_smul_one A e he U c).symm) ?_
  exact congrFun (congrArg (fun g => ⇑(ConcreteCategory.hom
    ((SheafOfModules.Hom.val g).app U))) e.hom_inv_id) (c • A.one.eval U)

/-- **A unital homomorphism between graded algebras whose degree-zero pieces are both the unit
sheaf is invertible in degree zero.** Nothing is assumed about the homomorphism beyond unitality;
the degree-zero component is forced to be the composite of the two identifications. -/
theorem isIso_unitalHom_app_zero {A B : GradedAlgebra.{w, w} R}
    (e₁ : A.piece 0 ≅ SheafOfModules.unit R)
    (he₁ : ∀ U : Cᵒᵖ, e₁.hom.val.app U (A.one.eval U) = (1 : R.obj.obj U))
    (e₂ : B.piece 0 ≅ SheafOfModules.unit R)
    (he₂ : ∀ U : Cᵒᵖ, e₂.hom.val.app U (B.one.eval U) = (1 : R.obj.obj U))
    (g : UnitalHom A B) : IsIso (g.app 0) := by
  have hsec : ∀ (U : Cᵒᵖ) (c : R.obj.obj U),
      e₂.hom.val.app U ((g.app 0).val.app U (e₁.inv.val.app U c)) = c := by
    intro U c
    refine Eq.trans (congrArg (fun z => e₂.hom.val.app U ((g.app 0).val.app U z))
      (inv_pieceZeroIsoUnit_apply A e₁ he₁ U c)) ?_
    refine Eq.trans (congrArg (e₂.hom.val.app U) (map_smul _ c (A.one.eval U))) ?_
    refine Eq.trans (congrArg (fun z => e₂.hom.val.app U (c • z)) (g.map_one U)) ?_
    exact pieceZeroIsoUnit_smul_one B e₂ he₂ U c
  have key : e₁.inv ≫ g.app 0 ≫ e₂.hom = 𝟙 (SheafOfModules.unit R) :=
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext (hsec U)))
  have hX : g.app 0 ≫ e₂.hom = e₁.hom :=
    ((Iso.inv_comp_eq e₁).mp key).trans (Category.comp_id _)
  rw [(Iso.eq_comp_inv e₂).mpr hX]
  infer_instance

end SheafOfModules.GradedAlgebra

end
