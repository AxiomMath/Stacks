module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymSectionsHom

/-!
# The degree-one generator of `Sym(ℰ)` on the sections over an affine open

For a quasi-coherent module `ℰ` on a scheme `X` and an affine open `V`, the identification
`Γ(V, Sym ℰ) ≅ Sym_{Γ(X, V)}(Γ(ℰ, V))` (`Stacks.SymGraded.AffinePieces.symSectionRingEquiv`)
carries the degree-one element attached to a section `t ∈ Γ(ℰ, V)` by the generator
`ℰ ⟶ Sym¹(ℰ)` of `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra` to `ι t`.

## Main results

* `Stacks.SymGraded.AffinePieces.symmetricAlgebraGen_app_eq`: the generator on sections over an
  affine open is the sheafification unit of `ι`.
* `Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of_symmetricAlgebraGen`: the
  identification of sections carries the degree-one element attached to `t` to `ι t`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.SymGraded.AffinePieces

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)

omit [E.IsQuasicoherent] in
/-- The inverse of the counit `(ℰ.val)^# ⟶ ℰ` is the sheafification unit, on sections. -/
theorem sheafificationIso_inv_app (U : X.Opens) (t : Γ(E, U)) :
    ((Scheme.Modules.sheafificationIso X E).inv.val.app (op U)) t =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) E.val)
        (op U) t := by
  have h : ((Scheme.Modules.sheafificationIso X E).hom.val.app (op U))
      (PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) E.val)
        (op U) t) = t :=
    congrArg (fun φ => PresheafOfModules.Hom.app φ (op U) t)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).right_triangle_components E)
  conv_lhs => rw [← h]
  exact congrArg (fun φ => (φ.val.app (op U))
      (PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) E.val)
        (op U) t)) (Scheme.Modules.sheafificationIso X E).hom_inv_id

omit [E.IsQuasicoherent] in
/-- **The generator on sections**: the degree-one element attached to `t` by the generator of
`Sym(ℰ)` is the image under the sheafification unit of the sectionwise generator, `ι t`. -/
theorem symmetricAlgebraGen_app_eq (U : X.Opens) (t : Γ(E, U)) :
    ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U)) t =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
          (PresheafOfModules.symPowInt 1 E.val)) (op U)
        (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen E.val) (op U) t) := by
  have h1 : ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U)) t =
      ((PresheafOfModules.symPowIntGradedAlgebra E.val).sheafifyGen (𝟙 X.ringCatSheaf.obj)
        (PresheafOfModules.symPowIntGen E.val)).val.app (op U)
        (((Scheme.Modules.sheafificationIso X E).inv.val.app (op U)) t) := rfl
  rw [h1, sheafificationIso_inv_app]
  exact Stacks.GradedAlgebra.sheafifyGen_unit _ _ _ (op U) t

/-- **The identification of sections carries the degree-one element of `t` to `ι t`.** -/
theorem symSectionRingEquiv_of_symmetricAlgebraGen (hqc : IsQuasicoherentPieces E)
    (t : Γ(E, V)) :
    symSectionRingEquiv E hV hqc
        (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) 1
          (((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)) t)) =
      SymmetricAlgebra.ι _ _ t := by
  refine (symSectionRingEquiv_of E hV hqc 1 _).trans ?_
  have h : ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)) t =
      pieceSectionsEquiv E hV ((1 : ℕ) : ℤ)
        (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen E.val) (op V) t) :=
    symmetricAlgebraGen_app_eq E V t
  refine (congrArg (fun z => ((pieceSectionsEquiv E hV ((1 : ℕ) : ℤ)).symm z :
    SymmetricAlgebra Γ(X, V) Γ(E, V))) h).trans ?_
  exact (congrArg Subtype.val ((pieceSectionsEquiv E hV ((1 : ℕ) : ℤ)).symm_apply_apply
    (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen E.val) (op V) t))).trans rfl

end Stacks.SymGraded.AffinePieces

end
