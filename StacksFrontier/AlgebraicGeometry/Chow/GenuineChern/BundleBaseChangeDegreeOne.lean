module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Epi
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# The base-change identification of symmetric algebras in degree one

Let `g : X' ⟶ X` be a morphism of schemes, `ℰ` a quasi-coherent module on `X` and `ℰ'` one on
`X'` with `ℰ' ≅ g^*ℰ`. The identification `g^* Sym(ℰ) ≅ Sym(ℰ')` of
`Stacks.RelativeProj.symmetricSituationPullbackHom` is, in degree one, the given isomorphism
`g^*ℰ ≅ ℰ'` read through the degree-one generators (Stacks 01CI). On sections: the pullback along
`g` of the degree-one element of `Γ(W, Sym ℰ)` attached to a section `x ∈ Γ(W, ℰ)` is carried to
the degree-one element of `Γ(W', Sym ℰ')` attached to the pullback of `x`, transported along
`ℰ' ≅ g^*ℰ`, for every open `W' ⊆ g⁻¹W`.

## Main results

* `Stacks.ProjectiveBundle.symmetricSituationPullbackHom_one_pullbackSection`: the
  identification on the pullback of a degree-one section.
* `Stacks.ProjectiveBundle.baseChangeGradedHom_of_one`: the same on the graded rings of sections
  over affine opens, for the base-change homomorphism `Γ(W, Sym ℰ) ⟶ Γ(W', Sym ℰ')`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.ProjectiveBundle

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (E' : X'.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- In degree one the base-change identification of symmetric algebras is the given isomorphism
`g^*ℰ ≅ ℰ'` followed by the degree-one generator of `Sym(ℰ')`: the pulled-back generator of
`Sym(ℰ)` composed with it is `hE.inv ≫ gen`. -/
theorem pullback_map_schemeSymGen_comp_symmetricSituationPullbackHom_one :
    (Scheme.Modules.pullback g).map (Scheme.Modules.symmetricAlgebraGen X E) ≫
        (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app 1 =
      hE.inv ≫ Scheme.Modules.symmetricAlgebraGen X' E' :=
  Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator g E E' hE

/-- **The base-change identification of symmetric algebras on a pulled-back degree-one
section.** For `x ∈ Γ(W, ℰ)` and an open `W' ⊆ g⁻¹W`, the identification carries the pullback
of the degree-one element `x` of `Γ(W, Sym ℰ)` to the degree-one element of `Γ(W', Sym ℰ')`
attached to the pullback of `x`, transported along `ℰ' ≅ g^*ℰ` and restricted to `W'`. -/
theorem symmetricSituationPullbackHom_one_pullbackSection (W : X.Opens) (W' : X'.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (x : Γ(E, W)) :
    ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app 1).val.app (op W')
        (Scheme.Modules.pullbackSection g ((Stacks.SymGraded.symSituation E).algebra.piece 1) W
          W' h ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op W) x)) =
      (Scheme.Modules.symmetricAlgebraGen X' E').val.app (op W')
        (E'.val.map (homOfLE h).op
          (hE.inv.val.app (op (g ⁻¹ᵁ W))
            (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection g E W x))) := by
  set Φ := (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app 1
  have hunit := (Scheme.Modules.unit_app_val_app_naturality g
    (Scheme.Modules.symmetricAlgebraGen X E) W x).symm
  have hgen := congrArg (fun φ => φ.val.app (op (g ⁻¹ᵁ W))
      (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection g E W x))
    (pullback_map_schemeSymGen_comp_symmetricSituationPullbackHom_one g E E' hE)
  simp only at hgen
  have hsec : Scheme.Modules.pullbackSection g ((Stacks.SymGraded.symSituation E).algebra.piece 1)
      W W' h ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op W) x) =
      ((Scheme.Modules.pullback g).obj
          ((Stacks.SymGraded.symSituation E).algebra.piece 1)).val.map (homOfLE h).op
        (((Scheme.Modules.pullback g).map (Scheme.Modules.symmetricAlgebraGen X E)).val.app
          (op (g ⁻¹ᵁ W))
          (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection g E W x)) :=
    congrArg (fun y => ((Scheme.Modules.pullback g).obj
      ((Stacks.SymGraded.symSituation E).algebra.piece 1)).val.map (homOfLE h).op y) hunit
  rw [hsec]
  refine (PresheafOfModules.naturality_apply Φ.val (homOfLE h).op _).trans ?_
  refine (congrArg _ hgen).trans ?_
  exact (PresheafOfModules.naturality_apply (Scheme.Modules.symmetricAlgebraGen X' E').val
    (homOfLE h).op _).symm

omit [E.IsQuasicoherent] [E'.IsQuasicoherent] in
/-- The transpose of a morphism `g^*ℰ ⟶ ℰ'`, read on a section: its value at `x` is the
pulled-back section of `x` carried along the morphism. -/
theorem homEquiv_val_app (φ : (Scheme.Modules.pullback g).obj E ⟶ E') (W : X.Opens)
    (x : Γ(E, W)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ φ).val.app (op W)) x =
      φ.val.app (op (g ⁻¹ᵁ W))
        (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection g E W x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

variable (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E')

/-- **The base-change homomorphism of graded rings of sections on a degree-one element.** The
degree-one element of `Γ(W, Sym ℰ)` attached to `x ∈ Γ(W, ℰ)` is carried to the degree-one
element of `Γ(W', Sym ℰ')` attached to the restriction to `W'` of the transpose of `hE.inv` at
`x`. -/
theorem baseChangeGradedHom_of_one (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) (x : Γ(E, W.toOpens)) :
    baseChangeGradedHom g E hqc E' hqc' hE W W' h
        (DirectSum.of ((Stacks.SymGraded.situationSheafGradedAlgebra E hqc).sectionPieces
          W.toOpens) 1 ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op W.toOpens) x)) =
      DirectSum.of ((Stacks.SymGraded.situationSheafGradedAlgebra E' hqc').sectionPieces
          W'.toOpens) 1
        ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op W'.toOpens)
          (E'.val.map (homOfLE h).op
            (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ hE.inv).val.app
              (op W.toOpens) x))) :=
  (baseChangeGradedHom_of g E hqc E' hqc' hE W W' h 1 _).trans
    (congrArg (DirectSum.of ((Stacks.SymGraded.situationSheafGradedAlgebra E' hqc').sectionPieces
      W'.toOpens) 1)
      ((symmetricSituationPullbackHom_one_pullbackSection g E E' hE W.toOpens W'.toOpens h x).trans
        (congrArg (fun y => (Scheme.Modules.symmetricAlgebraGen X' E').val.app (op W'.toOpens)
          (E'.val.map (homOfLE h).op y)) (homEquiv_val_app g E E' hE.inv W.toOpens x).symm)))

end Stacks.ProjectiveBundle

end
