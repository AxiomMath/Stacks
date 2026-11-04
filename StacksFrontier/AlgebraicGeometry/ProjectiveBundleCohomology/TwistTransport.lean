module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BundleIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.GradedIsoCohomology
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Multiplication
public import StacksFrontier.AlgebraicGeometry.PsiCompat.Basic
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Glue
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Opens
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Twists along an isomorphism of projective bundles

Let `χ : A ⟶ A'` be a homomorphism of quasi-coherent graded algebras on a scheme `S` which is
an isomorphism in every degree, and let `f : Proj_S(A') ⟶ Proj_S(A)` be the induced isomorphism
of relative projective spectra over `S`. The twists `𝒪(n)` of `Proj_S(A)` restrict along `f` to
twists of `Proj_S(A')`: over the chart of an affine open `U` of `S` the restriction of `𝒪(n)` is
the twist of `Γ(U, A)` restricted along `Proj Γ(U, χ)`, which is the twist of `Γ(U, A')`.
By the uniqueness of twists (Tag 01NR) the restriction of `𝒪_{Proj_S(A)}(n)` along `f` is
therefore `𝒪_{Proj_S(A')}(n)`, compatibly with the products and the homogeneous-section maps.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.restrictAlgebra`: a sheaf of graded
  algebras restricted along an open immersion.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.absTwistIso`: for an isomorphism of
  graded rings `σ : 𝒜 ≅ ℬ`, the twist `𝒪_{Proj 𝒜}(n)` restricted along `Proj σ` is
  `𝒪_{Proj ℬ}(n)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

/-! ### Restricting a graded algebra along an open immersion -/

section Restrict

variable {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h] (B : SchemeGradedAlgebra Y)

/-- **A sheaf of graded algebras restricted along an open immersion**: the pieces are the
restrictions, and the product of two local sections over `V` is their product over `h ''ᵁ V`. -/
@[ega "II 8.14.6" "more general"]
public def restrictAlgebra : SchemeGradedAlgebra X where
  piece n := Scheme.Modules.restrict (B.piece n) h
  mul i j :=
    { app V := (B.mul i j).app (op (h ''ᵁ V.unop))
      map_smul_left V r x y := (B.mul i j).map_smul_left _ ((h.appIso V.unop).inv r) x y
      map_smul_right V r x y := (B.mul i j).map_smul_right _ ((h.appIso V.unop).inv r) x y
      naturality {_ _} g x y := (B.mul i j).naturality
        (homOfLE (Scheme.Hom.image_mono _ (leOfHom g.unop))).op x y }
  one := PresheafOfModules.sectionsMk (fun V => B.one.eval (op (h ''ᵁ V.unop)))
    (fun {_ _} g => B.one.property (homOfLE (Scheme.Hom.image_mono _ (leOfHom g.unop))).op)
  mul_assoc i j k V x y z := B.mul_assoc i j k (op (h ''ᵁ V.unop)) x y z
  one_mul i V x := B.one_mul i (op (h ''ᵁ V.unop)) x
  mul_one i V x := B.mul_one i (op (h ''ᵁ V.unop)) x

/-- The pieces of the restricted algebra are the restricted pieces. -/
public theorem restrictAlgebra_piece (n : ℤ) :
    (restrictAlgebra h B).piece n = Scheme.Modules.restrict (B.piece n) h := rfl

/-- The product of the restricted algebra over `V` is the product over `h ''ᵁ V`. -/
public theorem restrictAlgebra_mul_app (i j : ℤ) (V : X.Opens) (x y) :
    ((restrictAlgebra h B).mul i j).app (op V) x y = (B.mul i j).app (op (h ''ᵁ V)) x y := rfl

/-- The unit of the restricted algebra over `V` is the unit over `h ''ᵁ V`. -/
public theorem restrictAlgebra_one_eval (V : X.Opens) :
    (restrictAlgebra h B).one.eval (op V) = B.one.eval (op (h ''ᵁ V)) := rfl

end Restrict

/-! ### The twist of a graded ring isomorphism -/

section Absolute

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜) (hφχ : ∀ b, φ (χ b) = b)

/-- `Proj` of a graded ring isomorphism is an open immersion. -/
public theorem isOpenImmersion_projMap_inverse (hχφ : ∀ a, χ (φ a) = a) :
    IsOpenImmersion (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ)) :=
  have := isIso_projMap_of_inverse φ χ hφχ hχφ
  inferInstance

/-- **The twist of `Proj 𝒜` restricted along `Proj φ` is the twist of `Proj ℬ`**, for a graded
ring isomorphism `φ : 𝒜 ≅ ℬ`: on sections over `V` it is the pointwise localization of `φ` on
degree-`n` fractions over the image of `V`. -/
public def absTwistIso (hχφ : ∀ a, χ (φ a) = a)
    [IsOpenImmersion (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))] (n : ℤ) :
    (Scheme.Modules.restrictFunctor (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))).obj
      (twistingSheaf 𝒜 n) ≅
      twistingSheaf ℬ n :=
  have hθ := isIso_twistMap_of_inverse φ χ hφχ hχφ n
  haveI : IsIso (((Scheme.Modules.restrictAdjunction
      (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))).homEquiv _ _).symm
      (Stacks.ProjTwistComparison.pushforwardTwistMap φ
        (irrelevant_le_map_of_inverse φ χ hφχ) n)) := by
    have h := Stacks.AlgebraicGeometry.TwistChartLocality.homEquiv_symm_eq_restrict
      (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ)) (twistingSheaf 𝒜 n) (twistingSheaf ℬ n)
      (Stacks.ProjTwistComparison.pushforwardTwistMap φ (irrelevant_le_map_of_inverse φ χ hφχ) n)
    have h' : ((Scheme.Modules.restrictAdjunction
        (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))).homEquiv _ _).symm
        (Stacks.ProjTwistComparison.pushforwardTwistMap φ
          (irrelevant_le_map_of_inverse φ χ hφχ) n) =
        (Scheme.Modules.restrictFunctorIsoPullback _).hom.app _ ≫
          Stacks.ProjTwistComparison.twistMap φ (irrelevant_le_map_of_inverse φ χ hφχ) n := by
      rw [Stacks.ProjTwistComparison.twistMap, h]
      exact (Iso.hom_inv_id_app_assoc _ _ _).symm
    rw [h']
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      ((Scheme.Modules.restrictFunctorIsoPullback _).app _).isIso_hom hθ
  asIso (((Scheme.Modules.restrictAdjunction
      (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))).homEquiv _ _).symm
      (Stacks.ProjTwistComparison.pushforwardTwistMap φ (irrelevant_le_map_of_inverse φ χ hφχ) n))

/-- **The twist along a graded ring isomorphism, pointwise**: the value at a point `y` of the
image of a section `x` over the image of `V` is the localization of `φ` applied to the value of `x`
at the image of `y`. -/
public theorem absTwistIso_hom_app_apply (hχφ : ∀ a, χ (φ a) = a)
    [IsOpenImmersion (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))] (n : ℤ)
    (V : (AlgebraicGeometry.Proj ℬ).Opens)
    (x : Γ((Scheme.Modules.restrictFunctor
      (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))).obj (twistingSheaf 𝒜 n), V))
    (y : V) :
    ((absTwistIso φ χ hφχ hχφ n).hom.app V x).1 y =
      Stacks.ProjTwistComparison.fibreMap φ (irrelevant_le_map_of_inverse φ χ hφχ) y.1
        ((x : (twistingSheaf 𝒜 n).val.obj
          (op (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V))).1
            ⟨_, ⟨y.1, y.2, rfl⟩⟩) := by
  have h : (absTwistIso φ χ hφχ hχφ n).hom =
      (Scheme.Modules.restrictFunctor (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))).map
        (Stacks.ProjTwistComparison.pushforwardTwistMap φ
          (irrelevant_le_map_of_inverse φ χ hφχ) n) ≫
      (Scheme.Modules.restrictAdjunction
        (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))).counit.app (twistingSheaf ℬ n) :=
    Adjunction.homEquiv_counit _ _ _ _
  rw [h]
  rfl

/-- `absTwistIso_hom_app_apply` on the underlying presheaves. -/
public theorem absTwistIso_hom_val_app_apply (hχφ : ∀ a, χ (φ a) = a)
    [IsOpenImmersion (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))] (n : ℤ)
    (V : (AlgebraicGeometry.Proj ℬ).Opens)
    (x : (twistingSheaf 𝒜 n).val.obj
      (op (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V))) (y : V) :
    ((absTwistIso φ χ hφχ hχφ n).hom.val.app (op V) x).1 y =
      Stacks.ProjTwistComparison.fibreMap φ (irrelevant_le_map_of_inverse φ χ hφχ) y.1
        (x.1 ⟨_, ⟨y.1, y.2, rfl⟩⟩) :=
  absTwistIso_hom_app_apply φ χ hφχ hχφ n V x y

end Absolute

/-! ### Twists transported along an isomorphism of relative projective spectra -/

open Stacks.AlgebraicGeometry.RelativeProjTwistGlue Stacks.AlgebraicGeometry.ProjTwistSections

/-- Three restriction maps of a presheaf on the opens of a space compose to one. -/
public theorem presheaf_map_comp₃ {X : TopCat.{u}} {C : Type*} [Category C]
    (P : (Opens X)ᵒᵖ ⥤ C) {a b c d : (Opens X)ᵒᵖ} (f₁ : a ⟶ b) (f₂ : b ⟶ c) (f₃ : c ⟶ d)
    (g : a ⟶ d) : P.map f₁ ≫ P.map f₂ ≫ P.map f₃ = P.map g := by
  rw [← P.map_comp, ← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

/-- The comparison of two iterated restrictions along two factorizations of one open immersion. -/
public def restrictChain {X₁ X₂ X₃ Y : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ Y)
    (c : X₁ ⟶ X₃) (d : X₃ ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    [IsOpenImmersion d] (h : a ≫ b = c ≫ d) (M : Y.Modules) :
    Scheme.Modules.restrict (Scheme.Modules.restrict M b) a ≅
      Scheme.Modules.restrict (Scheme.Modules.restrict M d) c :=
  (Scheme.Modules.restrictFunctorComp a b).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorCongr h).app M ≪≫
    (Scheme.Modules.restrictFunctorComp c d).app M

/-- The comparison of two iterated restrictions along two factorizations of one open immersion,
on sections: the restriction map along the equality of the two image opens. -/
public theorem restrictChain_hom_app {X₁ X₂ X₃ Y : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ Y)
    (c : X₁ ⟶ X₃) (d : X₃ ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    [IsOpenImmersion d] (h : a ≫ b = c ≫ d) (M : Y.Modules) (V : X₁.Opens)
    (hV : d ''ᵁ (c ''ᵁ V) = b ''ᵁ (a ''ᵁ V))
    (x : Γ(Scheme.Modules.restrict (Scheme.Modules.restrict M b) a, V)) :
    (restrictChain a b c d h M).hom.app V x = M.presheaf.map (eqToHom hV).op x := by
  simp only [restrictChain, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  exact ConcreteCategory.congr_hom (presheaf_map_comp₃ M.presheaf _ _ _ _) x

/-- `restrictChain_hom_app` on the underlying presheaves. -/
public theorem restrictChain_hom_val_app {X₁ X₂ X₃ Y : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ Y)
    (c : X₁ ⟶ X₃) (d : X₃ ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    [IsOpenImmersion d] (h : a ≫ b = c ≫ d) (M : Y.Modules) (V : X₁.Opens)
    (hV : d ''ᵁ (c ''ᵁ V) = b ''ᵁ (a ''ᵁ V))
    (x : (Scheme.Modules.restrict (Scheme.Modules.restrict M b) a).val.obj (op V)) :
    (restrictChain a b c d h M).hom.val.app (op V) x = M.val.map (eqToHom hV).op x :=
  restrictChain_hom_app a b c d h M V hV x

section Iso

variable {S : Scheme.{u}} {A A' : SheafGradedAlgebra S}
  (f : (relativeProj A').scheme ⟶ (relativeProj A).scheme) [IsOpenImmersion f]
  (σ : ∀ U : S.Opens, A.grading U →+*ᵍ A'.grading U)
  (χ : ∀ U : S.Opens, A'.grading U →+*ᵍ A.grading U)
  (hσχ : ∀ U b, σ U (χ U b) = b) (hχσ : ∀ U a, χ U (σ U a) = a)

/-- The morphism of charts `Proj Γ(U, A') ⟶ Proj Γ(U, A)` of a graded ring isomorphism. -/
public abbrev isoChartMap (U : S.Opens) :
    AlgebraicGeometry.Proj (A'.grading U) ⟶ AlgebraicGeometry.Proj (A.grading U) :=
  Proj.map (σ U) (irrelevant_le_map_of_inverse _ _ (hσχ U))

variable [∀ U, IsOpenImmersion (isoChartMap σ χ hσχ U)]
  (hchart : ∀ (U : S.Opens) (hU : IsAffineOpen U),
    (relativeProj A').chart U hU ≫ f = isoChartMap σ χ hσχ U ≫ (relativeProj A).chart U hU)

include hchart in
/-- The image of an open of a chart of `Proj_S(A')` in `Proj_S(A)`, computed in the two ways. -/
public theorem image_chart_iso (U : S.Opens) (hU : IsAffineOpen U)
    (V : (AlgebraicGeometry.Proj (A'.grading U)).Opens) :
    (relativeProj A).chart U hU ''ᵁ (isoChartMap σ χ hσχ U ''ᵁ V) =
      f ''ᵁ ((relativeProj A').chart U hU ''ᵁ V) := by
  rw [← Scheme.Hom.comp_image, ← Scheme.Hom.comp_image]
  exact Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.image_congr_morphism (hchart U hU).symm V

variable (D : TwistData A)

/-- **The chart identification of the transported twists**: over the chart of an affine open `U`
of `S`, the restriction of `𝒪_{Proj_S(A)}(n)` to `Proj_S(A')` is the twist of `Γ(U, A')`. -/
public def transportChartIso (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ) :
    Scheme.Modules.restrict ((restrictAlgebra f D.algebra).piece n)
        ((relativeProj A').chart U hU) ≅ twistingSheaf (A'.grading U) n :=
  restrictChain _ _ _ _ (hchart U hU) (D.algebra.piece n) ≪≫
    (Scheme.Modules.restrictFunctor (isoChartMap σ χ hσχ U)).mapIso (D.chartData.chartIso U hU n) ≪≫
    absTwistIso _ _ (hσχ U) (hχσ U) n

/-- **The transported chart identification on sections**: restrict to the image of the open in
the chart of `Proj_S(A)`, apply the chart identification there, then localize along `σ`. -/
public theorem transportChartIso_hom_app (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A'.grading U)).Opens)
    (x : (D.algebra.piece n).val.obj (op (f ''ᵁ ((relativeProj A').chart U hU ''ᵁ V)))) :
    (transportChartIso f σ χ hσχ hχσ hchart D U hU n).hom.val.app (op V) x =
      (absTwistIso _ _ (hσχ U) (hχσ U) n).hom.val.app (op V)
        ((D.chartData.chartIso U hU n).hom.val.app (op (isoChartMap σ χ hσχ U ''ᵁ V))
          ((D.algebra.piece n).val.map
            (eqToHom (image_chart_iso f σ χ hσχ hchart U hU V)).op x)) := by
  have h := restrictChain_hom_val_app _ _ _ _ (hchart U hU) (D.algebra.piece n) V
    (image_chart_iso f σ χ hσχ hchart U hU V) x
  rw [← h]
  rfl

end Iso

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
