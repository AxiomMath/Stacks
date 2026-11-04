module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ConeChern
public import StacksFrontier.AlgebraicGeometry.Modules.GlobalSmulPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier

/-!
# The deformation of a mapping cone to a direct sum over the affine line

Let `Y` be a scheme and let `φ : P₃ ⟶ P₁` be a map of complexes of `𝒪_Y`-modules. On the affine
line `π : 𝐀¹_Y ⟶ Y`, with coordinate `t`, the proof of Stacks 0FBD considers the mapping cone
`C^•` of `t · π^*φ`. Its fibre at the section of coordinate `a` is the mapping cone of `a · φ`:
the direct sum `P₁ ⊕ P₃[1]` at `a = 0` and the mapping cone of `φ` at `a = 1`.

## Main definitions

* `Stacks.Chow.complexSmul` — multiplication by a global function on a complex.
* `Stacks.Chow.deformationCone` — the mapping cone of `t · π^*φ` on `𝐀¹_Y`.

## Main results

* `Stacks.Chow.pullbackComplex_complexSmul` — `σ^*(b ·) = (σ^♯ b) ·` on complexes.
* `Stacks.Chow.pullbackComplexMappingConeSmulIso` — the fibre of the mapping cone of `b · π^*φ`
  at a section `σ` of `π` is the mapping cone of `σ^♯ b · φ`.
* `Stacks.Chow.deformationConeFibreZero`, `Stacks.Chow.deformationConeFibreOne` — the fibres of
  `C^•` at `t = 0` and `t = 1` are the mapping cones of `0` and of `φ`.

## References

* [Stacks Project, Tag 0FBD](https://stacks.math.columbia.edu/tag/0FBD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- **Multiplication by a global function `b ∈ Γ(X, 𝒪_X)` on a complex of `𝒪_X`-modules.** -/
def complexSmul (b : Γ(X, ⊤)) (P : CochainComplex X.Modules ℤ) : P ⟶ P where
  f n := (Stacks.RegularSequence.globalSmulCenter X b).app (P.X n)
  comm' i j _ := ((Stacks.RegularSequence.globalSmulCenter X b).naturality (P.d i j)).symm

/-- The degree-`n` component of `complexSmul b P` is multiplication by `b` on `P.X n`. -/
@[simp]
theorem complexSmul_f (b : Γ(X, ⊤)) (P : CochainComplex X.Modules ℤ) (n : ℤ) :
    (complexSmul b P).f n = (Stacks.RegularSequence.globalSmulCenter X b).app (P.X n) :=
  rfl

/-- Multiplication by `0` is zero. -/
theorem globalSmulCenter_zero_app (M : X.Modules) :
    (Stacks.RegularSequence.globalSmulCenter X 0).app M = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  rw [Stacks.RegularSequence.globalSmulCenter_app_app, map_zero, zero_smul]
  rfl

/-- Multiplication by `1` is the identity. -/
theorem globalSmulCenter_one_app (M : X.Modules) :
    (Stacks.RegularSequence.globalSmulCenter X 1).app M = 𝟙 M := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  rw [Stacks.RegularSequence.globalSmulCenter_app_app, map_one, one_smul]
  rfl

/-- Multiplication by `0` on a complex is the zero map. -/
theorem complexSmul_zero (P : CochainComplex X.Modules ℤ) : complexSmul 0 P = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact globalSmulCenter_zero_app (P.X n)

/-- Multiplication by `1` on a complex is the identity. -/
theorem complexSmul_one (P : CochainComplex X.Modules ℤ) : complexSmul 1 P = 𝟙 P := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact globalSmulCenter_one_app (P.X n)

/-- Multiplication by a global function commutes with maps of complexes. -/
@[reassoc]
theorem comp_complexSmul {P Q : CochainComplex X.Modules ℤ} (φ : P ⟶ Q) (b : Γ(X, ⊤)) :
    φ ≫ complexSmul b Q = complexSmul b P ≫ φ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, complexSmul_f, complexSmul_f]
  exact (Stacks.RegularSequence.globalSmulCenter X b).naturality (φ.f n)

/-- **Pullback of multiplication by a global function on complexes**: `σ^*(b ·) = (σ^♯ b) ·`. -/
theorem pullbackComplex_complexSmul {Y : Scheme.{u}} (σ : Y ⟶ X) (b : Γ(X, ⊤))
    (P : CochainComplex X.Modules ℤ) :
    ((Scheme.Modules.pullback σ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (complexSmul b P) = complexSmul (σ.appTop b) (pullbackComplex σ P) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact Stacks.RegularSequence.pullback_map_globalSmulCenter σ b (P.X n)

/-! ### Pulling back along a section -/

section Section

variable {Y : Scheme.{u}} (σ : Y ⟶ X) (π : X ⟶ Y) (hσ : σ ≫ π = 𝟙 Y)

/-- For a section `σ` of `π`, pulling back along `π` and then along `σ` is the identity on
complexes of modules. -/
def pullbackComplexSectionIso :
    (Scheme.Modules.pullback π).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pullback σ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex Y.Modules ℤ) :=
  Functor.mapHomologicalComplexCompIso
    (Scheme.Modules.pullbackComp σ π ≪≫ Scheme.Modules.pullbackCongr hσ ≪≫
      Scheme.Modules.pullbackId Y) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso Y.Modules (ComplexShape.up ℤ)

variable {P₁ P₃ : CochainComplex Y.Modules ℤ} (φ : P₃ ⟶ P₁) (b : Γ(X, ⊤))

/-- **The fibre of the mapping cone of `b · π^*φ` at a section `σ` of `π`** is the mapping cone
of `σ^♯ b · φ`. -/
def pullbackComplexMappingConeSmulIso :
    pullbackComplex σ (CochainComplex.mappingCone (C := X.Modules)
        (((Scheme.Modules.pullback π).mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫
          complexSmul b (pullbackComplex π P₁))) ≅
      CochainComplex.mappingCone (C := Y.Modules) (φ ≫ complexSmul (σ.appTop b) P₁) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso _ (Scheme.Modules.pullback σ) ≪≫
    HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by simp⟩)
      (Arrow.isoMk ((pullbackComplexSectionIso σ π hσ).app P₃)
        ((pullbackComplexSectionIso σ π hσ).app P₁) (by
          have h1 := (pullbackComplexSectionIso σ π hσ).hom.naturality φ
          have h2 : complexSmul (σ.appTop b) (pullbackComplex σ (pullbackComplex π P₁)) ≫
              (pullbackComplexSectionIso σ π hσ).hom.app P₁ =
              (pullbackComplexSectionIso σ π hσ).hom.app P₁ ≫ complexSmul (σ.appTop b) P₁ :=
            (comp_complexSmul (P := pullbackComplex σ (pullbackComplex π P₁)) (Q := P₁)
              ((pullbackComplexSectionIso σ π hσ).hom.app P₁) (σ.appTop b)).symm
          dsimp only [Arrow.mk_hom, Iso.app_hom]
          rw [Functor.map_comp, pullbackComplex_complexSmul, Category.assoc, h2,
            ← Category.assoc]
          exact (congrArg (· ≫ complexSmul (σ.appTop b) P₁) h1).symm.trans (Category.assoc _ _ _)))

end Section

/-! ### The deformation over the affine line -/

section Deformation

variable {Y : Scheme.{u}} {P₁ P₃ : CochainComplex Y.Modules ℤ} (φ : P₃ ⟶ P₁)

/-- **The deformation of Stacks 0FBD**: on the affine line `π : 𝐀¹_Y ⟶ Y` with coordinate `t`,
the mapping cone of `t · π^*φ`. -/
def deformationCone : CochainComplex (affineLineOver Y).Modules ℤ :=
  CochainComplex.mappingCone (C := (affineLineOver Y).Modules)
    (((Scheme.Modules.pullback (affineLineOverHom Y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ ≫
      complexSmul (affineCoordinate Y) (pullbackComplex (affineLineOverHom Y) P₁))

/-- Mapping cones of equal morphisms are isomorphic. -/
def mappingConeCongr {A B : CochainComplex Y.Modules ℤ} {ψ ψ' : A ⟶ B} (h : ψ = ψ') :
    CochainComplex.mappingCone (C := Y.Modules) ψ ≅
      CochainComplex.mappingCone (C := Y.Modules) ψ' :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by simp⟩)
    (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by simp [h]))

/-- **The fibre of the deformation at `t = 0`** is the mapping cone of the zero map, a direct sum
of `P₁` and the shift of `P₃`. -/
def deformationConeFibreZero :
    pullbackComplex (affineLineConstantSection Y integralAffineZeroSection) (deformationCone φ) ≅
      CochainComplex.mappingCone (C := Y.Modules) (0 : P₃ ⟶ P₁) :=
  pullbackComplexMappingConeSmulIso _ (affineLineOverHom Y)
      (affineLineConstantSection_comp_fst Y integralAffineZeroSection) φ (affineCoordinate Y) ≪≫
    mappingConeCongr (by
      rw [affineLineConstantSection_appTop_affineCoordinate_zero, complexSmul_zero,
        Limits.comp_zero])

/-- **The fibre of the deformation at `t = 1`** is the mapping cone of `φ`. -/
def deformationConeFibreOne :
    pullbackComplex (affineLineSection Y 1) (deformationCone φ) ≅
      CochainComplex.mappingCone (C := Y.Modules) φ :=
  pullbackComplexMappingConeSmulIso _ (affineLineOverHom Y) (affineLineSection_comp Y 1) φ
      (affineCoordinate Y) ≪≫
    mappingConeCongr (by
      rw [affineLineSection_appTop_affineCoordinate, complexSmul_one, Category.comp_id])

end Deformation

end Stacks.Chow

end
