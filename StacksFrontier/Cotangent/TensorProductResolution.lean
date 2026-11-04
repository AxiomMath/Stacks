module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity
public import StacksFrontier.Cotangent.ResolutionTorBaseChange
public import StacksFrontier.Cotangent.StandardResolutionIsResolution

/-!
# The tensor product of two standard resolutions

Let `A` and `B` be algebras over a ring `R`, and let `P_• ⟶ A` and `Q_• ⟶ B` be their standard
resolutions over `R`. The degreewise tensor product `P_• ⊗_R Q_•` is a simplicial `R`-algebra
augmented to `A ⊗_R B`, each of whose terms is a polynomial algebra. When `A` and `B` are Tor
independent over `R` it is a resolution of `A ⊗_R B` over `R` in the sense of [Stacks, Tag 08QI].

## Main definitions

* `CommAlgCat.tensorStandardResolution`: the simplicial `R`-algebra `P_• ⊗_R Q_•`.
* `CommAlgCat.tensorStandardResolutionAugmentation`: its augmentation `ε ⊗ ε` to `A ⊗_R B`.

## Main results

* `CommAlgCat.isResolution_tensorStandardResolution`: if `A` and `B` are Tor independent over
  `R`, then `P_• ⊗_R Q_• ⟶ A ⊗_R B` is a resolution.

## Implementation notes

The criterion of [Stacks, Tag 08QI] reduces the resolution property to a quasi-isomorphism of
Moore complexes, which is checked on the factorization
`P_• ⊗_R Q_• ⟶ A ⊗_R Q_• ⟶ A ⊗_R B`. The second map is the base change of the resolution
`Q_• ⟶ B` along `R → A`, a quasi-isomorphism by Tor independence
(`CommAlgCat.quasiIso_moore_augmentationBaseChange`). The first is `ε ⊗ Q_•`: the terms of `Q_•`
are free `R`-modules, so tensoring with `Q_•` preserves the surjective quasi-isomorphism
`P_• ⟶ A` (`StacksDraft.SimplicialTensor.quasiIso_whiskerLeft_of_quasiIso`, after the braiding).
No Eilenberg–Zilber comparison is needed.

## References

* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 09DA](https://stacks.math.columbia.edu/tag/09DA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u

namespace CommAlgCat

variable (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The degreewise tensor product `P_• ⊗_R Q_•` of the standard resolutions of `A` and of `B`
over `R`. -/
abbrev tensorStandardResolution : SimplicialObject (CommAlgCat.{u} R) :=
  (standardResolution.{u, u} R (CommAlgCat.of R A)).left ⊗
    (standardResolution.{u, u} R (CommAlgCat.of R B)).left

/-- The augmentation `P_• ⊗_R Q_• ⟶ A ⊗_R B`, the tensor product of the two augmentations. -/
def tensorStandardResolutionAugmentation :
    tensorStandardResolution R A B ⟶
      (SimplicialObject.const (CommAlgCat.{u} R)).obj (CommAlgCat.of R (A ⊗[R] B)) where
  app n := CommAlgCat.ofHom (Algebra.TensorProduct.map
    ((standardResolution.{u, u} R (CommAlgCat.of R A)).hom.app n).hom
    ((standardResolution.{u, u} R (CommAlgCat.of R B)).hom.app n).hom)
  naturality m m' f := by
    have hA := (standardResolution.{u, u} R (CommAlgCat.of R A)).hom.naturality f
    have hB := (standardResolution.{u, u} R (CommAlgCat.of R B)).hom.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hA hB
    apply CommAlgCat.hom_ext
    apply Algebra.TensorProduct.ext'
    intro p q
    change Algebra.TensorProduct.map _ _
      (((standardResolution.{u, u} R (CommAlgCat.of R A)).left.map f).hom p ⊗ₜ[R]
        ((standardResolution.{u, u} R (CommAlgCat.of R B)).left.map f).hom q) =
      Algebra.TensorProduct.map _ _ (p ⊗ₜ[R] q)
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    exact congrArg₂ (· ⊗ₜ[R] ·) (ConcreteCategory.congr_hom hA p)
      (ConcreteCategory.congr_hom hB q)

/-- In each degree, the augmentation `P_• ⊗_R Q_• ⟶ A ⊗_R B` sends `p ⊗ q` to `ε p ⊗ ε q`. -/
@[simp]
lemma tensorStandardResolutionAugmentation_app_tmul (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj n)
    (q : (standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj n) :
    ((tensorStandardResolutionAugmentation R A B).app n).hom (p ⊗ₜ[R] q) =
      ((standardResolution.{u, u} R (CommAlgCat.of R A)).hom.app n).hom p ⊗ₜ[R]
        ((standardResolution.{u, u} R (CommAlgCat.of R B)).hom.app n).hom q :=
  rfl

/-- A tensor product of polynomial algebras is a polynomial algebra: `R[ι] ⊗_R R[κ] = R[κ ⊕ ι]`. -/
theorem isPolynomialAlgebra_tensorObj {P Q : CommAlgCat.{u} R} (hP : IsPolynomialAlgebra R P)
    (hQ : IsPolynomialAlgebra R Q) : IsPolynomialAlgebra R (P ⊗ Q) := by
  obtain ⟨ι, ⟨e⟩⟩ := hP
  obtain ⟨κ, ⟨f⟩⟩ := hQ
  refine ⟨κ ⊕ ι, ⟨?_⟩⟩
  exact (MvPolynomial.sumAlgEquiv R κ ι).trans
    (((MvPolynomial.algebraTensorAlgEquiv R (MvPolynomial ι R)).restrictScalars R).symm.trans
      (Algebra.TensorProduct.congr e f))

/-- Each term of `P_• ⊗_R Q_•` is a polynomial algebra over `R`. -/
theorem isPolynomialAlgebra_tensorStandardResolution (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebra R ((tensorStandardResolution R A B).obj n) :=
  isPolynomialAlgebra_tensorObj R
    ((standardResolution_isResolution.{u, u} R (CommAlgCat.of R A)).isPolynomialAlgebra n)
    ((standardResolution_isResolution.{u, u} R (CommAlgCat.of R B)).isPolynomialAlgebra n)

/-- In each degree, the augmentation of the standard resolution of `C` over `R` is surjective. -/
theorem surjective_standardResolution_hom_app (C : CommAlgCat.{u} R) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((standardResolution.{u, u} R C).hom.app n).hom :=
  surjective_app_of_surjective_app_zero _ (SSet.surjective_app_zero_of_trivialKanFibrations
    (standardResolution_isResolution.{u, u} R C).trivialKanFibration) n

/-- In each degree, the augmentation `P_• ⊗_R Q_• ⟶ A ⊗_R B` is surjective. -/
theorem surjective_tensorStandardResolutionAugmentation_app (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((tensorStandardResolutionAugmentation R A B).app n).hom :=
  Algebra.TensorProduct.map_surjective _ _
    (surjective_standardResolution_hom_app R _ n) (surjective_standardResolution_hom_app R _ n)

/-! ### The resolution property -/

attribute [local instance] Functor.preservesHomologyOfExact

/-- A morphism of simplicial `R`-modules induces a quasi-isomorphism of Moore complexes exactly
when it does so after forgetting to abelian groups. -/
private lemma quasiIso_alternatingFaceMapComplex_forget₂_iff
    {X Y : SimplicialObject (ModuleCat.{u} R)} (g : X ⟶ Y) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} R)).map g) ↔
      QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (Functor.whiskerRight g (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))) := by
  have hiso := alternatingFaceMapComplexCompMapHomologicalComplexIso
    (C := ModuleCat.{u} R) (D := AddCommGrpCat.{u})
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((alternatingFaceMapComplex (ModuleCat.{u} R)).map g)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})]
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (hiso.app X) (hiso.app Y) (hiso.hom.naturality g).symm)

/-- The Moore complex of the augmentation of a standard resolution is a quasi-isomorphism. -/
private lemma quasiIso_moore_standardResolution (C : CommAlgCat.{u} R) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (standardResolution.{u, u} R C).hom (toAddCommGrpCat R))) :=
  ((isResolution_quasiIso_homotopyEquivalence_tfae R (C : Type u) _ _
    (standardResolution_isResolution.{u, u} R C).isPolynomialAlgebra
    (surjective_standardResolution_hom_app R C)).out 1 2).1
      (standardResolution_isResolution.{u, u} R C)

/-- Each term of a standard resolution is a flat module over the base. -/
private lemma flat_standardResolution (C : CommAlgCat.{u} R) (n : SimplexCategoryᵒᵖ) :
    Module.Flat R (((standardResolution.{u, u} R C).left ⋙ toModuleCat R).obj n) := by
  obtain ⟨ι, ⟨e⟩⟩ := (standardResolution_isResolution.{u, u} R C).isPolynomialAlgebra n
  have : Module.Free R ((standardResolution.{u, u} R C).left.obj n) :=
    Module.Free.of_equiv e.toLinearEquiv
  exact inferInstanceAs (Module.Flat R ((standardResolution.{u, u} R C).left.obj n))

/-- The first factor `P_• ⊗_R Q_• ⟶ A ⊗_R Q_•` of the augmentation, in `R`-modules. -/
private lemma quasiIso_moduleAugmentation_whiskerRight :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} R)).map
      (moduleAugmentation (standardResolution.{u, u} R (CommAlgCat.of R A)).hom ▷
        ((standardResolution.{u, u} R (CommAlgCat.of R B)).left ⋙ toModuleCat R))) := by
  have hq : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} R)).map
      (moduleAugmentation (standardResolution.{u, u} R (CommAlgCat.of R A)).hom)) :=
    (quasiIso_mooreComplex_map_iff _).2 (quasiIso_moore_standardResolution R _)
  have hw := StacksDraft.SimplicialTensor.quasiIso_whiskerLeft_of_quasiIso
    ((standardResolution.{u, u} R (CommAlgCat.of R B)).left ⋙ toModuleCat R)
    (flat_standardResolution R _)
    (moduleAugmentation (standardResolution.{u, u} R (CommAlgCat.of R A)).hom)
    (fun k => surjective_standardResolution_hom_app R _ (op ⦋k⦌)) hq
  have h : moduleAugmentation (standardResolution.{u, u} R (CommAlgCat.of R A)).hom ▷
        ((standardResolution.{u, u} R (CommAlgCat.of R B)).left ⋙ toModuleCat R) =
      (β_ _ _).hom ≫ (((standardResolution.{u, u} R (CommAlgCat.of R B)).left ⋙ toModuleCat R) ◁
        moduleAugmentation (standardResolution.{u, u} R (CommAlgCat.of R A)).hom) ≫
          (β_ _ _).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact BraidedCategory.braiding_naturality_left _ _
  rw [h, Functor.map_comp, Functor.map_comp, quasiIso_iff_comp_left, quasiIso_iff_comp_right]
  exact hw

/-- In `A ⊗_R B`, `(a ⊗ 1) * (1 ⊗ x) = a ⊗ x`. -/
private lemma tmul_one_mul_one_tmul_eq (a : A) (x : B) :
    (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] x) = a ⊗ₜ[R] x := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The base change `R → A` carries `B` to `A ⊗_R B` by the identity: the map
`A ⊗_R B → A ⊗_R B`, `a ⊗ x ↦ a · (1 ⊗ x)`, is the identity. -/
private lemma baseChangeUnit_includeRight :
    baseChangeUnit (B := CommAlgCat.of R B)
          (B' := CommAlgCat.of A (A ⊗[R] B))
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) = AlgHom.id A (A ⊗[R] B) := by
  apply Algebra.TensorProduct.ext'
  intro a x
  rw [baseChangeUnit_tmul]
  exact tmul_one_mul_one_tmul_eq R A B a x

/-- `P_• ⊗_R Q_•` forgotten to abelian groups is the tensor product of the underlying simplicial
`R`-modules, forgotten to abelian groups. -/
private def tensorForgetIso :
    tensorStandardResolution R A B ⋙ toAddCommGrpCat R ≅
      (((standardResolution.{u, u} R (CommAlgCat.of R A)).left ⋙ toModuleCat R) ⊗
        ((standardResolution.{u, u} R (CommAlgCat.of R B)).left ⋙ toModuleCat R)) ⋙
          forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- `A ⊗_R Q_•`, formed in simplicial `R`-modules, is the base change of `Q_•` along `R → A`,
forgotten to abelian groups. -/
private def baseChangeForgetIso :
    ((SimplicialObject.const (ModuleCat.{u} R)).obj
        ((toModuleCat R).obj (standardResolution.{u, u} R (CommAlgCat.of R A)).right) ⊗
      ((standardResolution.{u, u} R (CommAlgCat.of R B)).left ⋙ toModuleCat R)) ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      simplicialBaseChange (B := CommAlgCat.of R B)
          (B' := CommAlgCat.of A (A ⊗[R] B))
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
        (standardResolution.{u, u} R (CommAlgCat.of R B)).hom ⋙ toAddCommGrpCat A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The constant simplicial abelian group `A ⊗_R B`, read from `A`-algebras and from
`R`-algebras. -/
private def constForgetIso :
    (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A (A ⊗[R] B)) ⋙
        toAddCommGrpCat A ≅
      (SimplicialObject.const (CommAlgCat.{u} R)).obj (CommAlgCat.of R (A ⊗[R] B)) ⋙
        toAddCommGrpCat R :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The augmentation `P_• ⊗_R Q_• ⟶ A ⊗_R B` factors through `A ⊗_R Q_•`, read in abelian
groups. -/
private lemma whiskerRight_tensorStandardResolutionAugmentation :
    Functor.whiskerRight (tensorStandardResolutionAugmentation R A B) (toAddCommGrpCat R) =
      (tensorForgetIso R A B).hom ≫
        Functor.whiskerRight
          (moduleAugmentation (standardResolution.{u, u} R (CommAlgCat.of R A)).hom ▷
            ((standardResolution.{u, u} R (CommAlgCat.of R B)).left ⋙ toModuleCat R))
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≫ (baseChangeForgetIso R A B).hom ≫
        Functor.whiskerRight (augmentationBaseChange (B := CommAlgCat.of R B)
          (B' := CommAlgCat.of A (A ⊗[R] B))
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
          (standardResolution.{u, u} R (CommAlgCat.of R B)).hom) (toAddCommGrpCat A) ≫
        (constForgetIso R A B).hom := by
  ext n x
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul p q =>
      change ((standardResolution.{u, u} R (CommAlgCat.of R A)).hom.app n).hom p ⊗ₜ[R]
          ((standardResolution.{u, u} R (CommAlgCat.of R B)).hom.app n).hom q =
        ((augmentationBaseChange (B := CommAlgCat.of R B)
          (B' := CommAlgCat.of A (A ⊗[R] B))
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
          (standardResolution.{u, u} R (CommAlgCat.of R B)).hom).app n).hom
            (((standardResolution.{u, u} R (CommAlgCat.of R A)).hom.app n).hom p ⊗ₜ[R] q)
      rw [augmentationBaseChange_app_tmul]
      change _ = (_ ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] _)
      rw [tmul_one_mul_one_tmul_eq]
      rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)

/-- **The tensor product of the standard resolutions of two Tor independent algebras is a
resolution of their tensor product.** If `A` and `B` are Tor independent over `R`, the
augmentation `P_• ⊗_R Q_• ⟶ A ⊗_R B` is a resolution in the sense of [Stacks, Tag 08QI]. -/
theorem isResolution_tensorStandardResolution
    (hTor : RingTheory.TorIndependence.TorIndependent R A B) :
    IsResolution R (A ⊗[R] B) (tensorStandardResolution R A B)
      (tensorStandardResolutionAugmentation R A B) := by
  have hφ : Function.Bijective
      (baseChangeUnit (B := CommAlgCat.of R B)
          (B' := CommAlgCat.of A (A ⊗[R] B))
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)) := by
    rw [baseChangeUnit_includeRight]
    exact Function.bijective_id
  have h₂ := quasiIso_moore_augmentationBaseChange (B := CommAlgCat.of R B)
          (B' := CommAlgCat.of A (A ⊗[R] B))
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
    (standardResolution.{u, u} R (CommAlgCat.of R B)).hom
    (standardResolution_isResolution.{u, u} R _).isPolynomialAlgebra
    (quasiIso_moore_standardResolution R _) hTor hφ
  have h₁ := (quasiIso_alternatingFaceMapComplex_forget₂_iff R _).1
    (quasiIso_moduleAugmentation_whiskerRight R A B)
  have hq : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (tensorStandardResolutionAugmentation R A B)
        (toAddCommGrpCat R))) := by
    rw [whiskerRight_tensorStandardResolutionAugmentation]
    simp only [Functor.map_comp]
    infer_instance
  exact ((isResolution_quasiIso_homotopyEquivalence_tfae R (A ⊗[R] B) _ _
    (isPolynomialAlgebra_tensorStandardResolution R A B)
    (surjective_tensorStandardResolutionAugmentation_app R A B)).out 2 1).1 hq

end CommAlgCat

end
