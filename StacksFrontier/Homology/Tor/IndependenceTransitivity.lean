module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PushoutBaseChange

/-!
# Tor independence along a tower of rings

Let `R → B → A` and `R → C` be homomorphisms of commutative rings. If `B` and `C` are Tor
independent over `R`, a projective resolution `P` of `C` over `R` becomes, after extension of
scalars, a projective resolution `B ⊗_R P` of `B ⊗_R C` over `B`, and
`A ⊗_B (B ⊗_R P) = A ⊗_R P`. Hence `Tor_i^R(A, C) = Tor_i^B(A, B ⊗_R C)`, and Tor independence
of `A` and `B ⊗_R C` over `B` gives Tor independence of `A` and `C` over `R`.

## Main results

* `RingTheory.TorIndependence.torIndependent_of_torIndependent_tensorProduct`: Tor independence
  of `B`, `C` over `R` and of `A`, `B ⊗_R C` over `B` gives Tor independence of `A`, `C` over `R`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

variable {R B A C : Type u} [CommRing R] [CommRing B] [CommRing A] [CommRing C]
  [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] [Algebra R C]

theorem algebraMap_smul_tensorProduct (M : Type u) [AddCommGroup M] [Module R M] (r : R)
    (y : B ⊗[R] M) : (algebraMap R B r) • y = r • y :=
  algebraMap_smul B r y

/-- The restriction of `B ⊗_R M` to `R` is the tensor product `B ⊗_R M` of `R`-modules. -/
def baseChangeRestrictScalarsLinearEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars.{u} (algebraMap R B)).obj
        ((baseChangeFunctor R B).obj M) ≃ₗ[R]
      (ModuleCat.of R B ⊗ M : ModuleCat.{u} R) where
  toFun := fun x => (x : B ⊗[R] M)
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun r x => algebraMap_smul_tensorProduct M r x

/-- Base change followed by restriction of scalars is the tensor product with `B` over `R`. -/
def baseChangeFunctorCompRestrictScalarsIso :
    baseChangeFunctor R B ⋙ ModuleCat.restrictScalars.{u} (algebraMap R B) ≅
      (tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R B) :=
  NatIso.ofComponents (fun M => (baseChangeRestrictScalarsLinearEquiv M).toModuleIso)
    (fun {M N} f => by
      ext x
      rfl)

/-- Base change preserves projective modules. -/
theorem projective_baseChangeFunctor_obj (M : ModuleCat.{u} R) [Projective M] :
    Projective ((baseChangeFunctor R B).obj M) :=
  ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of B (B ⊗[R] M))

/-- If `Tor_i^R(B, M)` vanishes in positive degrees, base change carries a projective resolution
of `M` over `R` to a projective resolution of `B ⊗_R M` over `B`. -/
def baseChangeProjectiveResolution {M : ModuleCat.{u} R} (P : ProjectiveResolution M)
    (h : ∀ n : ℕ, 0 < n → IsZero (((Tor (ModuleCat.{u} R) n).obj (ModuleCat.of R B)).obj M)) :
    ProjectiveResolution ((baseChangeFunctor R B).obj M) where
  complex := ((baseChangeFunctor R B).mapHomologicalComplex _).obj P.complex
  projective n := projective_baseChangeFunctor_obj (P.complex.X n)
  π := ((baseChangeFunctor R B).mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex (baseChangeFunctor R B)
      (ComplexShape.down ℕ) 0).hom.app M
  quasiIso := by
    have ht : QuasiIso ((((tensoringLeft (ModuleCat.{u} R)).obj
        (ModuleCat.of R B)).mapHomologicalComplex (ComplexShape.down ℕ)).map P.π) :=
      quasiIso_tensor_map_projectiveResolution_of_isZero_Tor _ _ P h
    have he : QuasiIso (((baseChangeFunctor R B ⋙
        ModuleCat.restrictScalars.{u} (algebraMap R B)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map P.π) :=
      (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
        ((NatIso.mapHomologicalComplex baseChangeFunctorCompRestrictScalarsIso _).app _)
        ((NatIso.mapHomologicalComplex baseChangeFunctorCompRestrictScalarsIso _).app _)
        ((NatIso.mapHomologicalComplex baseChangeFunctorCompRestrictScalarsIso
          (ComplexShape.down ℕ)).hom.naturality P.π).symm)).2 ht
    have hb : QuasiIso (((baseChangeFunctor R B).mapHomologicalComplex
        (ComplexShape.down ℕ)).map P.π) :=
      (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
        (ModuleCat.restrictScalars.{u} (algebraMap R B))).1 he
    infer_instance

/-- `A ⊗_B (B ⊗_R M) = A ⊗_R M`, natural in the `R`-module `M`. -/
theorem cancelBaseChange_comp_lTensor_baseChange {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B A N).toLinearMap ∘ₗ
        (f.baseChange B).lTensor A =
      (f.baseChange A).restrictScalars B ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B A M).toLinearMap := by
  refine TensorProduct.ext' fun a x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add] at hx hy ⊢; rw [hx, hy]

/-- The restriction to `R` of `A ⊗_B (B ⊗_R M)` is `A ⊗_R M`. -/
def tensorBaseChangeRestrictScalarsLinearEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars.{u} (algebraMap R B)).obj
        ((tensoringLeft (ModuleCat.{u} B)).obj (ModuleCat.of B A) |>.obj
          ((baseChangeFunctor R B).obj M)) ≃ₗ[R]
      (ModuleCat.of R A ⊗ M : ModuleCat.{u} R) where
  toFun := fun x => TensorProduct.AlgebraTensorModule.cancelBaseChange R B B A M x
  invFun := fun y => (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B A M).symm y
  left_inv := fun x => (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B A M).symm_apply_apply x
  right_inv := fun y => (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B A M).apply_symm_apply y
  map_add' := fun x y => map_add _ x y
  map_smul' := fun r x =>
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R B B A M).map_smul
      (algebraMap R B r) x).trans (algebraMap_smul B r _)

/-- Base change to `B`, tensoring with `A` over `B` and restricting to `R` is tensoring with `A`
over `R`. -/
def baseChangeTensorRestrictScalarsIso :
    baseChangeFunctor R B ⋙ (tensoringLeft (ModuleCat.{u} B)).obj (ModuleCat.of B A) ⋙
        ModuleCat.restrictScalars.{u} (algebraMap R B) ≅
      (tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R A) :=
  NatIso.ofComponents (fun M => (tensorBaseChangeRestrictScalarsLinearEquiv (A := A) M).toModuleIso)
    (fun {M N} f => by
      ext x
      exact LinearMap.congr_fun (cancelBaseChange_comp_lTensor_baseChange (R := R) (B := B)
        (A := A) f.hom) x)

/-- **Tor independence along a tower.** If `B` and `C` are Tor independent over `R`, and `A`
and `B ⊗_R C` are Tor independent over `B`, then `A` and `C` are Tor independent over `R`. -/
theorem torIndependent_of_torIndependent_tensorProduct (h₁ : TorIndependent R B C)
    (h₂ : TorIndependent B A (B ⊗[R] C)) : TorIndependent R A C := by
  rw [torIndependent_iff_isZero_tor] at h₁ h₂ ⊢
  intro n hn
  let P := projectiveResolution (ModuleCat.of R C)
  let Q := baseChangeProjectiveResolution (B := B) P h₁
  let TB := (tensoringLeft (ModuleCat.{u} B)).obj (ModuleCat.of B A)
  let TR := (tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R A)
  let G := ModuleCat.restrictScalars.{u} (algebraMap R B)
  have hB : IsZero ((TB.leftDerived n).obj ((baseChangeFunctor R B).obj
      (ModuleCat.of R C))) := h₂ n hn
  have hQ : ((TB.mapHomologicalComplex _).obj Q.complex).ExactAt n := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hB.of_iso (Q.isoLeftDerivedObj TB n).symm
  have hG : ((G.mapHomologicalComplex _).obj ((TB.mapHomologicalComplex _).obj
      Q.complex)).ExactAt n := by
    rw [HomologicalComplex.exactAt_iff] at hQ ⊢
    exact hQ.map G
  let e : (G.mapHomologicalComplex _).obj ((TB.mapHomologicalComplex _).obj Q.complex) ≅
      (TR.mapHomologicalComplex _).obj P.complex :=
    HomologicalComplex.Hom.isoOfComponents
      (fun k => (baseChangeTensorRestrictScalarsIso (A := A) (B := B)).app (P.complex.X k))
      (fun i j _ => ((baseChangeTensorRestrictScalarsIso (A := A) (B := B)).hom.naturality
        (P.complex.d i j)).symm)
  have hP : ((TR.mapHomologicalComplex _).obj P.complex).ExactAt n := hG.of_iso e
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hP
  exact hP.of_iso (P.isoLeftDerivedObj TR n)

end RingTheory.TorIndependence

end
