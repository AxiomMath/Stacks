module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StabilizerTrivial
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent

/-!
# Stabilisers of rational functions: functoriality

The right stabiliser condition `AlgebraicGeometry.RightStabilises` is a subfunctor: if `h : T ⟶ G`
right-stabilises a function `f` on an open `U`, then so does `φ ≫ h` for every `φ : T' ⟶ T`
(Perrin's thesis I §2, IV §1).

## Main definitions

* `AlgebraicGeometry.stabilizerBaseChange`: the base change `G ×_k T' ⟶ G ×_k T` along
  `φ : T' ⟶ T`.

## Main results

* `AlgebraicGeometry.rightStabilizerLocus_le_preimage`: the stabiliser locus of `φ ≫ h` lies in
  the preimage of the stabiliser locus of `h` under `stabilizerBaseChange φ`.
* `AlgebraicGeometry.RightStabilises.comp`: right stabilisers are stable under base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {G T T' : Over (Spec (.of k))} [GrpObj G]

/-- The base change `G ×_k T' ⟶ G ×_k T` along `φ : T' ⟶ T`. -/
noncomputable def stabilizerBaseChange (φ : T' ⟶ T) : G ⊗ T' ⟶ G ⊗ T :=
  lift (fst G T') (snd G T' ≫ φ)

omit [GrpObj G] in
/-- The base change `G ×_k T' ⟶ G ×_k T` commutes with the projections to `G`. -/
theorem stabilizerBaseChange_fst (φ : T' ⟶ T) :
    stabilizerBaseChange (G := G) φ ≫ fst G T = fst G T' :=
  lift_fst _ _

/-- Composing the base change along `φ` with right translation by `h` is right translation by
`φ ≫ h`. -/
theorem stabilizerBaseChange_rightTranslate (φ : T' ⟶ T) (h : T ⟶ G) :
    stabilizerBaseChange φ ≫ rightTranslate h = rightTranslate (φ ≫ h) := by
  simp [stabilizerBaseChange, rightTranslate, MonObj.comp_mul]

/-- The stabiliser locus of `φ ≫ h` in `U` is contained in the preimage, under
`stabilizerBaseChange φ`, of the stabiliser locus of `h` in `U`. -/
theorem rightStabilizerLocus_le_preimage (φ : T' ⟶ T) (h : T ⟶ G) (U : G.left.Opens) :
    rightStabilizerLocus (φ ≫ h) U ≤
      (stabilizerBaseChange φ).left ⁻¹ᵁ rightStabilizerLocus h U := by
  intro x hx
  refine ⟨?_, ?_⟩
  · show ((stabilizerBaseChange φ ≫ fst G T).left) x ∈ U
    rw [stabilizerBaseChange_fst]
    exact hx.1
  · show ((stabilizerBaseChange φ ≫ rightTranslate h).left) x ∈ U
    rw [stabilizerBaseChange_rightTranslate]
    exact hx.2

/-- **Right stabilisers are stable under base change**: if `h` right-stabilises `f` on `U`, then
so does `φ ≫ h` for every `φ : T' ⟶ T`. -/
theorem RightStabilises.comp {h : T ⟶ G} {U : G.left.Opens} {f : Γ(G.left, U)}
    (hst : RightStabilises h U f) (φ : T' ⟶ T) : RightStabilises (φ ≫ h) U f := by
  have e := congrArg ((stabilizerBaseChange φ).left.appLE (rightStabilizerLocus h U)
    (rightStabilizerLocus (φ ≫ h) U) (rightStabilizerLocus_le_preimage φ h U)).hom hst
  simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE] at e
  unfold RightStabilises
  refine Eq.trans ?_ (e.trans ?_)
  · exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_congr_hom
      ((congrArg Over.Hom.left (stabilizerBaseChange_fst φ)).symm.trans
        (Over.comp_left _ _ _ _ _)) _ _ _ _) f
  · exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_congr_hom
      ((Over.comp_left _ _ _ _ _).symm.trans
        (congrArg Over.Hom.left (stabilizerBaseChange_rightTranslate φ h))) _ _ _ _) f

end AlgebraicGeometry

end
