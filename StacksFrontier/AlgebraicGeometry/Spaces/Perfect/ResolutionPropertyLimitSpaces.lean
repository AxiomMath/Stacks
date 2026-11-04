module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpenSubspaceCoveringLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffineMain

/-!
# The resolution property of a limit of algebraic spaces

Let `X = lim X_i` be the limit of a cofiltered system of quasi-compact and quasi-separated
algebraic spaces over `S` with affine transition morphisms.  Stacks 0GV2 asserts that `X` has the
resolution property if and only if some `X_i` has it.

## Main results

* `AlgebraicGeometry.Space.hasResolutionProperty_limitAlgebraicSpace_of_stage`: the direction
  from a stage to the limit.

## References

* [Stacks Project, Tag 0GV2](https://stacks.math.columbia.edu/tag/0GV2)
* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-- **The direction of Stacks 0GV2 from a stage to the limit.**  If a stage `X_i` of the system
is quasi-compact, quasi-separated and has the resolution property, so does the limit. -/
theorem hasResolutionProperty_limitAlgebraicSpace_of_stage (i : I)
    (hqc : IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hres : HasResolutionProperty.{u, u} B S hS (D.obj i) (hD i)) :
    HasResolutionProperty.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2 :=
  hasResolutionProperty_source_of_isAffineHom hZ
    (limitProjection B S hS D hSize hHomSize hD hAffine i)
    (isAffineHom_limitπ B S hS D hSize hHomSize hAffine i) hqc hqs hres

/-- The limit of a system of quasi-compact algebraic spaces is quasi-compact. -/
theorem isQuasiCompactSpace_limitAlgebraicSpace
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) :
    IsQuasiCompactSpace B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1 :=
  isQuasiCompactSpace_limit B S hS D hSize hHomSize hD hAffine hqc

/-- The limit of the system is quasi-separated when some stage is. -/
theorem isAbsolutelyQuasiSeparated_limitAlgebraicSpace (i : I)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) :
    IsAbsolutelyQuasiSeparated B S hS hZ
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1 :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2 hqs
    (isQuasiSeparated_of_isAffineHom_hom (limitProjection B S hS D hSize hHomSize hD hAffine i)
      (isAffineHom_limitπ B S hS D hSize hHomSize hAffine i))

omit [IsCofiltered I] in
/-- **Iterated inverse images along transitions are the inverse image along the composite.** -/
noncomputable def modulePullbackStageTransitionCompIso {i j k : I} (e : j ⟶ k) (e' : i ⟶ j) :
    modulePullback B S hS (stageTransition B S hS D hD e) ⋙
        modulePullback B S hS (stageTransition B S hS D hD e') ≅
      modulePullback B S hS (stageTransition B S hS D hD (e' ≫ e)) :=
  modulePullbackCompIso B S hS _ _ ≪≫
    eqToIso (congrArg (modulePullback B S hS) (stageTransition_comp B S hS D hD e' e))

omit [IsCofiltered I] in
/-- **A chain of six inverse images along transitions is the inverse image along the
composite.** -/
noncomputable def modulePullbackStageTransitionChainIso {i₀ k j₀ j₁ j₂ j₃ j₄ : I} (b : k ⟶ i₀)
    (e₀ : j₀ ⟶ k) (e₁ : j₁ ⟶ j₀) (e₂ : j₂ ⟶ j₁) (e₃ : j₃ ⟶ j₂) (e₄ : j₄ ⟶ j₃) :
    modulePullback B S hS (stageTransition B S hS D hD b) ⋙
        (modulePullback B S hS (stageTransition B S hS D hD e₀) ⋙
          modulePullback B S hS (stageTransition B S hS D hD e₁) ⋙
            modulePullback B S hS (stageTransition B S hS D hD e₂) ⋙
              modulePullback B S hS (stageTransition B S hS D hD e₃) ⋙
                modulePullback B S hS (stageTransition B S hS D hD e₄)) ≅
      modulePullback B S hS (stageTransition B S hS D hD (e₄ ≫ e₃ ≫ e₂ ≫ e₁ ≫ e₀ ≫ b)) :=
  let P := fun {x y : I} (e : x ⟶ y) => modulePullback B S hS (stageTransition B S hS D hD e)
  let i₃ : P e₃ ⋙ P e₄ ≅ P (e₄ ≫ e₃) := modulePullbackStageTransitionCompIso B S hS D hD e₃ e₄
  let i₂ : P e₂ ⋙ P e₃ ⋙ P e₄ ≅ P (e₄ ≫ e₃ ≫ e₂) :=
    Functor.isoWhiskerLeft (P e₂) i₃ ≪≫
      modulePullbackStageTransitionCompIso B S hS D hD e₂ (e₄ ≫ e₃) ≪≫
        eqToIso (by rw [Category.assoc])
  let i₁ : P e₁ ⋙ P e₂ ⋙ P e₃ ⋙ P e₄ ≅ P (e₄ ≫ e₃ ≫ e₂ ≫ e₁) :=
    Functor.isoWhiskerLeft (P e₁) i₂ ≪≫
      modulePullbackStageTransitionCompIso B S hS D hD e₁ (e₄ ≫ e₃ ≫ e₂) ≪≫
        eqToIso (by simp only [P, Category.assoc])
  let i₀' : P e₀ ⋙ P e₁ ⋙ P e₂ ⋙ P e₃ ⋙ P e₄ ≅ P (e₄ ≫ e₃ ≫ e₂ ≫ e₁ ≫ e₀) :=
    Functor.isoWhiskerLeft (P e₀) i₁ ≪≫
      modulePullbackStageTransitionCompIso B S hS D hD e₀ (e₄ ≫ e₃ ≫ e₂ ≫ e₁) ≪≫
        eqToIso (by simp only [P, Category.assoc])
  Functor.isoWhiskerLeft (P b) i₀' ≪≫
    modulePullbackStageTransitionCompIso B S hS D hD b (e₄ ≫ e₃ ≫ e₂ ≫ e₁ ≫ e₀) ≪≫
      eqToIso (by simp only [Category.assoc])

/-- **An isomorphism of functors identifies the images of a morphism, as arrows.** -/
noncomputable def arrowIsoOfNatIso {C C' : Type*} [Category* C] [Category* C'] {F G : C ⥤ C'}
    (η : F ≅ G) {a b : C} (c : a ⟶ b) : Arrow.mk (F.map c) ≅ Arrow.mk (G.map c) :=
  Arrow.isoMk (η.app a) (η.app b) (η.hom.naturality c).symm

end AlgebraicGeometry.Space

end
