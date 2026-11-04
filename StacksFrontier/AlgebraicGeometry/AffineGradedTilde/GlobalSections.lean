module

public import StacksFrontier.AlgebraicGeometry.AffineGradedTilde.Hom

/-!
# The graded ring of global sections of the sheaf associated to a graded algebra

Let `A = ⨁ 𝒜 n` be a commutative graded `R`-algebra. **The graded ring of global sections of the
associated quasi-coherent graded `𝒪_{Spec R}`-algebra `⨁ (𝒜 n)~` is `A` itself**, as graded rings,
and under this identification the homomorphism induced by a graded homomorphism `φ : A ⟶ B` on
global sections is `φ`.

## Main definitions

* `Stacks.AffineGradedTilde.globalPieceEquiv`: `𝒜 n ≃ₗ[R] Γ(Spec R, (𝒜 n)~)`.
* `Stacks.AffineGradedTilde.globalSectionsRingEquiv`: `A ≃+* Γ(⨁ (𝒜 n)~, ⊤)`.
* `Stacks.AffineGradedTilde.gradedGlobalSectionsHom` and `gradedGlobalSectionsInv`: the same as
  mutually inverse graded ring homomorphisms.

## Main results

* `Stacks.AffineGradedTilde.sectionHom_globalSectionsRingEquiv`: the homomorphism of section rings
  induced by `φ` is `φ`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.GradedProperCohomology (intExtend)
open Stacks.SpecGraded (specGradedAlgebra pieceModule pieceCmp piecePresheaf mulSec mulₗ gOne
  specGradedAlgebra_mul_toTilde specGradedAlgebra_one_eval mulSec_tmul)
open scoped TensorProduct DirectSum

universe u

namespace Stacks.AffineGradedTilde

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [_root_.GradedAlgebra 𝒜]

/-! ### The degreewise comparison -/

omit [_root_.GradedAlgebra 𝒜] in
/-- On global sections, the comparison map of the degree `n` piece sends `1 ⊗ x` to the global
section of `(𝒜 n)~` determined by `x`. -/
theorem pieceCmp_top_one_tmul (n : ℤ) (x : intExtend 𝒜 n) :
    PresheafOfModules.Hom.app (pieceCmp (intExtend 𝒜) n) (op (⊤ : (Spec R).Opens))
        ((1 : Γ(Spec R, (⊤ : (Spec R).Opens))) ⊗ₜ[R] x) =
      AffineBaseChange.toOpenₗ (pieceModule (intExtend 𝒜) n) ⊤ x := by
  rw [AffineBaseChange.toTilde_app, AffineBaseChange.toTildeₗ_tmul, one_smul]

/-- The global section of `(𝒜 0)~` determined by `1 ∈ 𝒜 0` is the unit of the sheaf of graded
algebras. -/
theorem toOpenₗ_oneG :
    AffineBaseChange.toOpenₗ (pieceModule (intExtend 𝒜) 0) ⊤ (gOne (intExtend 𝒜)) =
      (specGradedAlgebra (intExtend 𝒜)).one.eval (op (⊤ : (Spec R).Opens)) := by
  rw [← pieceCmp_top_one_tmul]
  exact (specGradedAlgebra_one_eval (intExtend 𝒜) (op (⊤ : (Spec R).Opens))).symm

/-- The global section of `(𝒜 (i + j))~` determined by a product `x * y` is the product of the
global sections determined by `x` and by `y`. -/
theorem toOpenₗ_mulₗ (i j : ℤ) (x : intExtend 𝒜 i) (y : intExtend 𝒜 j) :
    AffineBaseChange.toOpenₗ (pieceModule (intExtend 𝒜) (i + j)) ⊤
        (mulₗ (intExtend 𝒜) i j x y) =
      ((specGradedAlgebra (intExtend 𝒜)).mul i j).app (op (⊤ : (Spec R).Opens))
        (AffineBaseChange.toOpenₗ (pieceModule (intExtend 𝒜) i) ⊤ x)
        (AffineBaseChange.toOpenₗ (pieceModule (intExtend 𝒜) j) ⊤ y) := by
  have h := specGradedAlgebra_mul_toTilde (intExtend 𝒜) i j (op (⊤ : (Spec R).Opens))
    ((1 : Γ(Spec R, (⊤ : (Spec R).Opens))) ⊗ₜ[R] x)
    ((1 : Γ(Spec R, (⊤ : (Spec R).Opens))) ⊗ₜ[R] y)
  rw [mulSec_tmul, one_mul] at h
  rw [← pieceCmp_top_one_tmul, ← pieceCmp_top_one_tmul, ← pieceCmp_top_one_tmul]
  exact h.symm

/-- **The degreewise comparison** `𝒜 n ≃ Γ(Spec R, (𝒜 n)~)`. -/
def globalPieceEquiv (n : ℕ) :
    intExtend 𝒜 (n : ℤ) ≃ₗ[R] (sheafGradedAlgebra 𝒜).sectionPieces ⊤ n :=
  LinearEquiv.ofBijective (AffineBaseChange.toOpenₗ (pieceModule (intExtend 𝒜) (n : ℤ)) ⊤)
    (ConcreteCategory.bijective_of_isIso (tilde.toOpen (pieceModule (intExtend 𝒜) (n : ℤ)) ⊤))

/-- `globalPieceEquiv 𝒜 n x` is the global section of `(𝒜 n)~` determined by `x`. -/
theorem globalPieceEquiv_apply (n : ℕ) (x : intExtend 𝒜 (n : ℤ)) :
    globalPieceEquiv 𝒜 n x = AffineBaseChange.toOpenₗ (pieceModule (intExtend 𝒜) (n : ℤ)) ⊤ x :=
  rfl

/-- `globalPieceEquiv 𝒜 0` sends `1` to the global unit section. -/
theorem globalPieceEquiv_one :
    globalPieceEquiv 𝒜 0 (gOne (intExtend 𝒜)) = (sheafGradedAlgebra 𝒜).one ⊤ :=
  toOpenₗ_oneG 𝒜

/-- The degreewise comparisons are multiplicative: the image of `x * y` in degree `i + j` is the
product of the images of `x` and `y`. -/
theorem globalPieceEquiv_mul (i j : ℕ) (x : intExtend 𝒜 (i : ℤ)) (y : intExtend 𝒜 (j : ℤ)) :
    globalPieceEquiv 𝒜 (i + j) (mulₗ (intExtend 𝒜) (i : ℤ) (j : ℤ) x y) =
      ((sheafGradedAlgebra 𝒜).mul (i : ℤ) (j : ℤ)).app ⊤
        (globalPieceEquiv 𝒜 i x) (globalPieceEquiv 𝒜 j y) :=
  toOpenₗ_mulₗ 𝒜 (i : ℤ) (j : ℤ) x y

/-! ### The graded ring of global sections -/

/-- The degreewise comparison, assembled on the direct sum of the homogeneous pieces. -/
def globalSectionsDirectSumEquiv :
    (⨁ n : ℕ, 𝒜 n) ≃+ (sheafGradedAlgebra 𝒜).sectionRing ⊤ :=
  DirectSum.congrAddEquiv fun n => (globalPieceEquiv 𝒜 n).toAddEquiv

/-- `globalSectionsDirectSumEquiv` acts on the summand of degree `n` by `globalPieceEquiv 𝒜 n`. -/
theorem globalSectionsDirectSumEquiv_of (n : ℕ) (x : 𝒜 n) :
    globalSectionsDirectSumEquiv 𝒜 (DirectSum.of _ n x) =
      DirectSum.of _ n (globalPieceEquiv 𝒜 n x) :=
  DirectSum.map_of (fun n => (globalPieceEquiv 𝒜 n).toAddEquiv.toAddMonoidHom) n x

/-- `globalSectionsDirectSumEquiv` is multiplicative. -/
theorem globalSectionsDirectSumEquiv_mul (a b : ⨁ n : ℕ, 𝒜 n) :
    globalSectionsDirectSumEquiv 𝒜 (a * b) =
      globalSectionsDirectSumEquiv 𝒜 a * globalSectionsDirectSumEquiv 𝒜 b := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of i x =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | of j y =>
          rw [DirectSum.of_mul_of, globalSectionsDirectSumEquiv_of,
            globalSectionsDirectSumEquiv_of, globalSectionsDirectSumEquiv_of,
            DirectSum.of_mul_of]
          exact congrArg (DirectSum.of _ (i + j)) (globalPieceEquiv_mul 𝒜 i j x y)
      | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]

/-- **The graded ring of global sections of `⨁ (𝒜 n)~` is `A`.** -/
def globalSectionsRingEquiv : A ≃+* (sheafGradedAlgebra 𝒜).sectionRing ⊤ :=
  (DirectSum.decomposeRingEquiv 𝒜).trans
    { globalSectionsDirectSumEquiv 𝒜 with
      map_mul' := globalSectionsDirectSumEquiv_mul 𝒜 }

/-- `globalSectionsRingEquiv 𝒜 x` is the image under `globalSectionsDirectSumEquiv` of the
decomposition of `x` into homogeneous components. -/
theorem globalSectionsRingEquiv_apply (x : A) :
    globalSectionsRingEquiv 𝒜 x =
      globalSectionsDirectSumEquiv 𝒜 (DirectSum.decompose 𝒜 x) :=
  rfl

/-- A homogeneous element `x ∈ 𝒜 n` is sent to the global section of `(𝒜 n)~` it determines, placed
in degree `n`. -/
theorem globalSectionsRingEquiv_of_mem {n : ℕ} {x : A} (hx : x ∈ 𝒜 n) :
    globalSectionsRingEquiv 𝒜 x =
      DirectSum.of _ n (globalPieceEquiv 𝒜 n ⟨x, hx⟩) := by
  rw [globalSectionsRingEquiv_apply, DirectSum.decompose_of_mem 𝒜 hx,
    globalSectionsDirectSumEquiv_of]
  rfl

/-- `globalSectionsRingEquiv` sends elements of degree `n` to global sections of degree `n`. -/
theorem globalSectionsRingEquiv_mem_grading {n : ℕ} {x : A} (hx : x ∈ 𝒜 n) :
    globalSectionsRingEquiv 𝒜 x ∈ (sheafGradedAlgebra 𝒜).grading ⊤ n := by
  rw [globalSectionsRingEquiv_of_mem 𝒜 hx]
  exact SheafGradedAlgebra.of_mem_grading _ _ _

/-- The inverse of `globalSectionsRingEquiv` sends global sections of degree `n` to elements of
`𝒜 n`. -/
theorem globalSectionsRingEquiv_symm_mem {n : ℕ} {z : (sheafGradedAlgebra 𝒜).sectionRing ⊤}
    (hz : z ∈ (sheafGradedAlgebra 𝒜).grading ⊤ n) :
    (globalSectionsRingEquiv 𝒜).symm z ∈ 𝒜 n := by
  obtain ⟨y, rfl⟩ := hz
  have h : globalSectionsRingEquiv 𝒜 ((globalPieceEquiv 𝒜 n).symm y : A) =
      DirectSum.of ((sheafGradedAlgebra 𝒜).sectionPieces ⊤) n y := by
    rw [globalSectionsRingEquiv_of_mem 𝒜 ((globalPieceEquiv 𝒜 n).symm y).2]
    exact congrArg (DirectSum.of _ n) ((globalPieceEquiv 𝒜 n).apply_symm_apply y)
  rw [← h, (globalSectionsRingEquiv 𝒜).symm_apply_apply]
  exact ((globalPieceEquiv 𝒜 n).symm y).2

/-- The identification `A ≅ Γ(⨁ (𝒜 n)~, ⊤)` as a graded ring homomorphism. -/
def gradedGlobalSectionsHom : 𝒜 →+*ᵍ (sheafGradedAlgebra 𝒜).grading ⊤ where
  toRingHom := (globalSectionsRingEquiv 𝒜).toRingHom
  map_mem hx := globalSectionsRingEquiv_mem_grading 𝒜 hx

/-- The inverse of `Stacks.AffineGradedTilde.gradedGlobalSectionsHom`. -/
def gradedGlobalSectionsInv : (sheafGradedAlgebra 𝒜).grading ⊤ →+*ᵍ 𝒜 where
  toRingHom := (globalSectionsRingEquiv 𝒜).symm.toRingHom
  map_mem hz := globalSectionsRingEquiv_symm_mem 𝒜 hz

/-- `gradedGlobalSectionsHom 𝒜` is `globalSectionsRingEquiv 𝒜` as a function. -/
theorem gradedGlobalSectionsHom_apply (x : A) :
    gradedGlobalSectionsHom 𝒜 x = globalSectionsRingEquiv 𝒜 x := rfl

/-- `gradedGlobalSectionsInv 𝒜` is the inverse of `globalSectionsRingEquiv 𝒜` as a function. -/
theorem gradedGlobalSectionsInv_apply (z : (sheafGradedAlgebra 𝒜).sectionRing ⊤) :
    gradedGlobalSectionsInv 𝒜 z = (globalSectionsRingEquiv 𝒜).symm z := rfl

/-! ### Compatibility with homomorphisms -/

variable {B : Type u} [CommRing B] [Algebra R B] (ℬ : ℕ → Submodule R B) [_root_.GradedAlgebra ℬ]
  (φ : A →ₐ[R] B) (hφ : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → φ a ∈ ℬ n)

/-- A graded homomorphism of graded `R`-algebras, as a graded ring homomorphism. -/
def gradedRingHom : 𝒜 →+*ᵍ ℬ where
  toRingHom := φ.toRingHom
  map_mem {n a} ha := hφ n a ha

/-- **On global sections, the homomorphism induced by `φ` is `φ`.** -/
theorem sectionHom_globalSectionsRingEquiv (x : A) :
    (sheafGradedAlgebraHom 𝒜 ℬ φ hφ).sectionHom ⊤ (globalSectionsRingEquiv 𝒜 x) =
      globalSectionsRingEquiv ℬ (φ x) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous n m =>
      obtain ⟨a, ha⟩ := m
      rw [globalSectionsRingEquiv_of_mem 𝒜 ha, SheafGradedAlgebraHom.sectionHom_of,
        globalSectionsRingEquiv_of_mem ℬ (hφ n a ha)]
      exact congrArg (DirectSum.of _ n)
        (AffineBaseChange.tildeMapₗ_toOpenₗ (pieceModuleMap 𝒜 ℬ φ hφ (n : ℤ)) ⊤ ⟨a, ha⟩)
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

end Stacks.AffineGradedTilde

end
