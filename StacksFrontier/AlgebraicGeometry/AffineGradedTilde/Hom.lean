module

public import StacksFrontier.AlgebraicGeometry.AffineGradedTilde.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom

/-!
# Homomorphisms of graded algebras on an affine scheme

A homomorphism `φ : A ⟶ B` of graded `R`-algebras which preserves the gradings induces a
homomorphism of the associated quasi-coherent graded `𝒪_{Spec R}`-algebras
`⨁ (𝒜 n)~ ⟶ ⨁ (ℬ n)~`, degreewise the map `tilde.map` of the restriction of `φ`.

## Main definitions

* `Stacks.AffineGradedTilde.gradedPieceMap`: the restriction of `φ` to a graded piece.
* `Stacks.AffineGradedTilde.sheafGradedAlgebraHom`: the induced homomorphism of relative `Proj`
  data.

## Main results

* `Stacks.AffineGradedTilde.presheafMap_mulSec`: `φ` commutes with the multiplication of the
  base changes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.GradedProperCohomology (intExtend)
open Stacks.SpecGraded (specGradedAlgebra pieceModule pieceCmp piecePresheaf mulSec mulₗ gOne
  specGradedAlgebra_mul_toTilde specGradedAlgebra_one_eval mulSec_tmul)
open scoped TensorProduct

universe u

namespace Stacks.AffineGradedTilde


variable {R : CommRingCat.{u}} {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
  [Algebra R B] (𝒜 : ℕ → Submodule R A) [_root_.GradedAlgebra 𝒜]
  (ℬ : ℕ → Submodule R B) [_root_.GradedAlgebra ℬ]
  (φ : A →ₐ[R] B) (hφ : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → φ a ∈ ℬ n)

local notation "𝒜~" => specGradedAlgebra (intExtend 𝒜)
local notation "ℬ~" => specGradedAlgebra (intExtend ℬ)

omit [_root_.GradedAlgebra 𝒜] [_root_.GradedAlgebra ℬ] in
include hφ in
/-- A grading-preserving `φ` maps the degree-`n` piece of `intExtend 𝒜` into that of
`intExtend ℬ`, for every `n : ℤ`. -/
theorem map_mem_intExtend (n : ℤ) {a : A} (ha : a ∈ intExtend 𝒜 n) :
    φ a ∈ intExtend ℬ n := by
  match n with
  | .ofNat k => exact hφ k a ha
  | .negSucc _ =>
      rw [show a = 0 from ha, map_zero]
      exact Submodule.zero_mem _

/-- The restriction of `φ` to the degree-`n` graded pieces. -/
def gradedPieceMap (n : ℤ) : intExtend 𝒜 n →ₗ[R] intExtend ℬ n :=
  φ.toLinearMap.restrict fun _ ha => map_mem_intExtend 𝒜 ℬ φ hφ n ha

omit [_root_.GradedAlgebra 𝒜] [_root_.GradedAlgebra ℬ] in
/-- The underlying element of `gradedPieceMap 𝒜 ℬ φ hφ n x` is `φ x`. -/
@[simp]
theorem gradedPieceMap_coe (n : ℤ) (x : intExtend 𝒜 n) :
    ((gradedPieceMap 𝒜 ℬ φ hφ n x : intExtend ℬ n) : B) = φ x := rfl

/-- The restriction of `φ`, as a morphism of `R`-modules. -/
abbrev pieceModuleMap (n : ℤ) : pieceModule (intExtend 𝒜) n ⟶ pieceModule (intExtend ℬ) n :=
  ModuleCat.ofHom (gradedPieceMap 𝒜 ℬ φ hφ n)

/-- `φ` commutes with the multiplication of the base changes. -/
theorem presheafMap_mulSec (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] intExtend 𝒜 i)
    (y : Γ(Spec R, U.unop) ⊗[R] intExtend 𝒜 j) :
    AffineBaseChange.presheafMapₗ (pieceModuleMap 𝒜 ℬ φ hφ (i + j)) U.unop
        (mulSec (intExtend 𝒜) U i j x y) =
      mulSec (intExtend ℬ) U i j
        (AffineBaseChange.presheafMapₗ (pieceModuleMap 𝒜 ℬ φ hφ i) U.unop x)
        (AffineBaseChange.presheafMapₗ (pieceModuleMap 𝒜 ℬ φ hφ j) U.unop y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
          rw [mulSec_tmul, AffineBaseChange.presheafMapₗ_tmul,
            AffineBaseChange.presheafMapₗ_tmul, AffineBaseChange.presheafMapₗ_tmul,
            mulSec_tmul]
          exact congrArg (fun z : intExtend ℬ (i + j) => (a * b) ⊗ₜ[R] z)
            (Subtype.ext (map_mul φ (x : A) (y : A)))
      | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

omit [_root_.GradedAlgebra 𝒜] [_root_.GradedAlgebra ℬ] in
/-- `tilde.map` of the restriction of `φ` on the comparison image of a base-changed section. -/
theorem tildeMap_cmp (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : (piecePresheaf (intExtend 𝒜) n).obj U) :
    (tilde.map (pieceModuleMap 𝒜 ℬ φ hφ n)).val.app U
        (PresheafOfModules.Hom.app (pieceCmp (intExtend 𝒜) n) U x) =
      PresheafOfModules.Hom.app (pieceCmp (intExtend ℬ) n) U
        (AffineBaseChange.presheafMapₗ (pieceModuleMap 𝒜 ℬ φ hφ n) U.unop x) :=
  AffineBaseChange.toTilde_map_app _ U x

/-- `tilde.map` of the restriction of `φ` is multiplicative on local sections. -/
theorem tildeMap_mul (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (a : ((𝒜~).piece i).val.obj U) (b : ((𝒜~).piece j).val.obj U) :
    (tilde.map (pieceModuleMap 𝒜 ℬ φ hφ (i + j))).val.app U (((𝒜~).mul i j).app U a b) =
      ((ℬ~).mul i j).app U
        ((tilde.map (pieceModuleMap 𝒜 ℬ φ hφ i)).val.app U a)
        ((tilde.map (pieceModuleMap 𝒜 ℬ φ hφ j)).val.app U b) := by
  refine Stacks.eq_of_isSeparated ((ℬ~).piece (i + j))
    (GrothendieckTopology.intersection_covering _
      (Stacks.cmpSieve_mem (pieceCmp (intExtend 𝒜) i) a)
      (Stacks.cmpSieve_mem (pieceCmp (intExtend 𝒜) j) b)) ?_
  rintro Y f ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
  have ht1 : PresheafOfModules.Hom.app (pieceCmp (intExtend 𝒜) i) (op Y) t =
    ((𝒜~).piece i).val.map f.op a := ht
  have ht2 : PresheafOfModules.Hom.app (pieceCmp (intExtend 𝒜) j) (op Y) t' =
    ((𝒜~).piece j).val.map f.op b := ht'
  have hnat (n : ℤ) (s : ((𝒜~).piece n).val.obj U) :
      ((ℬ~).piece n).val.map f.op
          ((tilde.map (pieceModuleMap 𝒜 ℬ φ hφ n)).val.app U s) =
        (tilde.map (pieceModuleMap 𝒜 ℬ φ hφ n)).val.app (op Y)
          (((𝒜~).piece n).val.map f.op s) :=
    (PresheafOfModules.naturality_apply (tilde.map (pieceModuleMap 𝒜 ℬ φ hφ n)).val f.op s).symm
  have hmulA : ((𝒜~).piece (i + j)).val.map f.op
      (((𝒜~).mul i j).app U a b) =
      PresheafOfModules.Hom.app (pieceCmp (intExtend 𝒜) (i + j)) (op Y)
        (mulSec (intExtend 𝒜) (op Y) i j t t') := by
    refine (((𝒜~).mul i j).naturality f.op a b).trans ?_
    refine Eq.trans ?_ (specGradedAlgebra_mul_toTilde (intExtend 𝒜) i j (op Y) t t')
    rw [ht1, ht2]
  have hmulB : ((ℬ~).piece (i + j)).val.map f.op (((ℬ~).mul i j).app U
      ((tilde.map (pieceModuleMap 𝒜 ℬ φ hφ i)).val.app U a)
      ((tilde.map (pieceModuleMap 𝒜 ℬ φ hφ j)).val.app U b)) =
      PresheafOfModules.Hom.app (pieceCmp (intExtend ℬ) (i + j)) (op Y)
        (mulSec (intExtend ℬ) (op Y) i j
        (AffineBaseChange.presheafMapₗ (pieceModuleMap 𝒜 ℬ φ hφ i) Y t)
        (AffineBaseChange.presheafMapₗ (pieceModuleMap 𝒜 ℬ φ hφ j) Y t')) := by
    refine (((ℬ~).mul i j).naturality f.op _ _).trans ?_
    refine Eq.trans ?_ (specGradedAlgebra_mul_toTilde (intExtend ℬ) i j (op Y) _ _)
    rw [hnat, hnat, ← ht1, ← ht2]
    exact congrArg₂ (fun u v => ((ℬ~).mul i j).app (op Y) u v)
      (tildeMap_cmp 𝒜 ℬ φ hφ i (op Y) t) (tildeMap_cmp 𝒜 ℬ φ hφ j (op Y) t')
  refine (hnat (i + j) _).trans ?_
  refine Eq.trans ?_ hmulB.symm
  rw [hmulA]
  exact (tildeMap_cmp 𝒜 ℬ φ hφ (i + j) (op Y) _).trans
    (congrArg _ (presheafMap_mulSec 𝒜 ℬ φ hφ (op Y) i j t t'))

/-- **The homomorphism of relative `Proj` data induced by `φ`**: degreewise `tilde.map` of the
restriction of `φ`. -/
def sheafGradedAlgebraHom :
    SheafGradedAlgebraHom (sheafGradedAlgebra 𝒜) (sheafGradedAlgebra ℬ) where
  app n := tilde.map (pieceModuleMap 𝒜 ℬ φ hφ n)
  app_mul i j U a b := tildeMap_mul 𝒜 ℬ φ hφ i j (op U) a b
  app_one U := by
    change (tilde.map (pieceModuleMap 𝒜 ℬ φ hφ 0)).val.app (op U)
      (PresheafOfModules.Hom.app (pieceCmp (intExtend 𝒜) 0) (op U)
        ((1 : Γ(Spec R, U)) ⊗ₜ[R] gOne (intExtend 𝒜))) =
      PresheafOfModules.Hom.app (pieceCmp (intExtend ℬ) 0) (op U)
        ((1 : Γ(Spec R, U)) ⊗ₜ[R] gOne (intExtend ℬ))
    refine (tildeMap_cmp 𝒜 ℬ φ hφ 0 (op U) _).trans ?_
    rw [AffineBaseChange.presheafMapₗ_tmul]
    exact congrArg (fun z : intExtend ℬ 0 =>
      PresheafOfModules.Hom.app (pieceCmp (intExtend ℬ) 0) (op U) ((1 : Γ(Spec R, U)) ⊗ₜ[R] z))
      (Subtype.ext (map_one φ))

/-- The degree-`n` component of `sheafGradedAlgebraHom` is `tilde.map` of the restriction of `φ`
to the degree-`n` pieces. -/
theorem sheafGradedAlgebraHom_app (n : ℤ) :
    (sheafGradedAlgebraHom 𝒜 ℬ φ hφ).app n = tilde.map (pieceModuleMap 𝒜 ℬ φ hφ n) := rfl

end Stacks.AffineGradedTilde

end
