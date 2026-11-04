module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.QuasiFiniteSubalgebraSystem
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.ResidueFieldIntegral

/-!
# The levels `Spec B_D` as a directed system of affine schemes over an affine scheme

Let `T` be an affine scheme, `O` a `Γ(T)`-algebra, `T₀ ⊆ O` finite and `ψ : L → O` a ring map from
a field. The levels `B_D = Γ(T)[D ∪ ψ(L)] ⊆ O` of `AlgebraicGeometry.levelAlg`, indexed by the
directed set `AlgebraicGeometry.QFSubalgebras T₀`, give a cofiltered system `D ↦ Spec B_D` of
affine schemes over `T`, and `Spec O` with the maps `Spec O → Spec B_D` is its limit when `O` is
covered by finitely generated quasi-finite subalgebras. The structure maps `Spec B_D → T` have
integral residue field extensions under the hypothesis of
`AlgebraicGeometry.isIntegral_residueFieldMap_levelAlg`.

This is the presentation `X ×_Y Spec(𝒪^{sh}_{Y,y}) = lim X ×_Y Spec(B_D)` of the proof of
[Stacks, Tag 0F0X].

## Main definitions

* `AlgebraicGeometry.levelSystem`: the system `D ↦ Spec B_D` over `T`.
* `AlgebraicGeometry.levelLimitCone`: the cone with vertex `Spec O`.

## Main results

* `AlgebraicGeometry.isLimitLevelLimitCone`: `Spec O = lim Spec B_D` over `T`.
* `AlgebraicGeometry.isIntegral_residueFieldMap_levelSystem`: the structure maps have integral
  residue field extensions.

## References

* [Stacks Project, Tag 0F0X](https://stacks.math.columbia.edu/tag/0F0X)
* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

universe u

namespace AlgebraicGeometry

variable (T : Scheme.{u}) [IsAffine T] {O : Type u} [CommRing O] [Algebra Γ(T, ⊤) O]
  (T₀ : Set O) {L : Type u} [Field L] (ψ : L →+* O)

/-- The levels `D ↦ Spec B_D`, as a diagram of schemes. -/
abbrev levelSchemeDiagram : (QFSubalgebras (R := Γ(T, ⊤)) T₀)ᵒᵖ ⥤ Scheme.{u} :=
  (levelRingDiagram (R := Γ(T, ⊤)) (T₀ := T₀) ψ).op ⋙ Scheme.Spec

/-- The structure maps `Spec B_D → T`. -/
def levelStructure : levelSchemeDiagram T T₀ ψ ⟶ (Functor.const _).obj T where
  app D := Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (levelAlg ψ D.unop.1))) ≫
    T.isoSpec.inv
  naturality D₁ D₂ h := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    change Spec.map _ ≫ _ = _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

/-- **The system of levels `D ↦ Spec B_D` over `T`.** -/
def levelSystem : (QFSubalgebras (R := Γ(T, ⊤)) T₀)ᵒᵖ ⥤ Over T :=
  Over.lift (levelSchemeDiagram T T₀ ψ) (levelStructure T T₀ ψ)

/-- Each level `Spec B_D` of `AlgebraicGeometry.levelSystem` is an affine scheme. -/
instance isAffine_levelSystem_obj (D : (QFSubalgebras (R := Γ(T, ⊤)) T₀)ᵒᵖ) :
    IsAffine ((levelSystem T T₀ ψ).obj D).left :=
  inferInstanceAs (IsAffine (Spec (.of (levelAlg ψ D.unop.1))))

/-- The structure map of the vertex `Spec O → T`. -/
abbrev levelVertexHom : Spec (.of O) ⟶ T :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) O)) ≫ T.isoSpec.inv

/-- The composite `Spec O → Spec B_D → T` is the structure map `Spec O → T`. -/
theorem levelStructure_fac (D : (QFSubalgebras (R := Γ(T, ⊤)) T₀)ᵒᵖ) :
    (Scheme.Spec.mapCone (levelRingCocone (R := Γ(T, ⊤)) (T₀ := T₀) ψ).op).π.app D ≫
      (levelStructure T T₀ ψ).app D = levelVertexHom T (O := O) := by
  show Spec.map _ ≫ Spec.map _ ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- **The cone of the levels with vertex `Spec O`.** -/
def levelLimitCone : Cone (levelSystem T T₀ ψ) :=
  Over.liftCone (levelSchemeDiagram T T₀ ψ) (levelStructure T T₀ ψ)
    (Scheme.Spec.mapCone (levelRingCocone (R := Γ(T, ⊤)) (T₀ := T₀) ψ).op)
    (levelVertexHom T (O := O)) (levelStructure_fac T T₀ ψ)

/-- The vertex of the cone of levels is `Spec O` over `T`. -/
theorem levelLimitCone_pt_hom :
    (levelLimitCone T T₀ ψ).pt.hom = levelVertexHom T (O := O) :=
  rfl

/-- **`Spec O` is the limit of the levels over `T`**, when `T₀` is finite and every element of
`O` lies in a finitely generated `Γ(T)`-subalgebra quasi-finite over `Γ(T)`: `O` is the filtered
colimit of the `B_D` (`AlgebraicGeometry.isColimit_levelRingCocone`), `Spec` is a right adjoint,
and a limit cone lifts to a limit cone over `T`. -/
def isLimitLevelLimitCone (hT₀ : T₀.Finite)
    (hcov : ∀ o : O, ∃ D : Subalgebra Γ(T, ⊤) O, D.FG ∧ Algebra.QuasiFinite Γ(T, ⊤) D ∧ o ∈ D) :
    IsLimit (levelLimitCone T T₀ ψ) := by
  haveI := QFSubalgebras.nonempty hT₀ hcov
  haveI : Nonempty (QFSubalgebras (R := Γ(T, ⊤)) T₀)ᵒᵖ := ⟨op (Classical.arbitrary _)⟩
  have hc := isColimit_levelRingCocone (R := Γ(T, ⊤)) ψ hT₀ hcov
  haveI : PreservesLimitsOfSize.{u, u} Scheme.Spec.{u} :=
    ΓSpec.adjunction.rightAdjoint_preservesLimits
  exact Over.isLimitLiftCone _ _ _ _ _ (isLimitOfPreserves Scheme.Spec hc.op)

/-- **The structure maps of the levels have integral residue field extensions**, under the
hypothesis of `AlgebraicGeometry.isIntegral_residueFieldMap_levelAlg`. -/
theorem isIntegral_residueFieldMap_levelSystem
    (hL : ∀ ℓ : L, ∃ p : O[X], (∀ n, p.coeff n ∈ Algebra.adjoin Γ(T, ⊤) T₀) ∧
      (∃ c : L, c ≠ 0 ∧ p.leadingCoeff = ψ c) ∧ p.eval (ψ ℓ) = 0)
    (D : (QFSubalgebras (R := Γ(T, ⊤)) T₀)ᵒᵖ) (x : Spec (.of (levelAlg ψ D.unop.1))) :
    (((levelStructure T T₀ ψ).app D).residueFieldMap x).hom.IsIntegral := by
  have h₁ := isIntegral_residueFieldMap_Spec_map
    (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (levelAlg ψ D.unop.1)))
    (fun P _ => isIntegral_residueFieldMap_levelAlg ψ hL D.unop P) x
  exact isIntegral_residueFieldMap_comp
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (levelAlg ψ D.unop.1)))) T.isoSpec.inv x h₁
    (isIntegral_residueFieldMap_of_isIso _ _)

end AlgebraicGeometry

end
