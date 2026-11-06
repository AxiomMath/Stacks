module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.LeftResolution
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse

/-!
# Derived tensor products of inverse systems of modules

For an inverse system of commutative rings, the derived category of compatible module systems
has a canonical derived tensor product. A componentwise K-flat representative computes it
as the entire pointwise total-tensor system, including the induced transition maps.

## Main definitions

* `ModuleSystemKFlatComparison.totalTensorSystem`: the actual total-tensor bifunctor on
  complexes of systems.
* `ModuleSystemKFlatComparison.DerivedTensorProduct`: the derived tensor bifunctor, its natural
  whole-system and evaluation comparisons, symmetry, and exactness.

## Main results

* `ModuleSystemKFlatComparison.derivedTensorProduct`: existence of the canonical derived tensor
  product of inverse systems of modules.

## Implementation notes

An inverse system of commutative rings is represented by a functor from `ℕᵒᵖ`. Compatibility with
the functor to the derived category at an index is recorded by an isomorphism after choosing a
representative whose component there is K-flat. When every component is K-flat, these are the
evaluations of one natural comparison in the derived category of systems. Its model is the
total complex of `systemTensor`, whose transition maps tensor the two semilinear transition
maps. The total-complex evaluation comparison is fixed on every homogeneous summand.
The ring and module universes are independent; modules use `max u v`, as for K-flatness.
Source index `n + 1` is represented by Lean index `n`.

## References

* [Stacks Project, Tag 091H](https://stacks.math.columbia.edu/tag/091H)
-/

/-! ### The concrete pointwise tensor model and the derived tensor datum -/

open Stacks.HomologyColimit

section Definitions

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u v w

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

attribute [local instance] HasDerivedCategory.standard


namespace ModuleSystemKFlatComparison

/-- Compatible module systems, in a universe containing the ring universe. -/
abbrev Systems (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :=
  PresheafOfModules.{max u v} (A ⋙ forget₂ CommRingCat RingCat)

section TensorModel

variable (A : ℕᵒᵖ ⥤ CommRingCat.{u})

/-- The ring of sections of `A ⋙ forget₂ CommRingCat RingCat` at `n` is commutative. -/
noncomputable instance commRingObjForget₂ (n : ℕᵒᵖ) :
    CommRing ((A ⋙ forget₂ CommRingCat RingCat).obj n) :=
  inferInstanceAs (CommRing (A.obj n))

/-- Pointwise tensor product, with the tensor products of the semilinear transition maps. -/
noncomputable def tensorSystem (M N : Systems.{u, v} A) : Systems.{u, v} A where
  obj n := ModuleCat.of (A.obj n) (M.obj n ⊗[A.obj n] N.obj n)
  map f := ConcreteCategory.ofHom (C := ModuleCat _)
    { toFun := TensorProduct.map (M.restrictₛₗ f) (N.restrictₛₗ f)
      map_add' := map_add _
      map_smul' := fun r x => (TensorProduct.map (M.restrictₛₗ f)
        (N.restrictₛₗ f)).map_smulₛₗ r x }
  map_id n := by
    ext x y
    simp [PresheafOfModules.restrictₛₗ]
    rfl
  map_comp f g := by
    ext x y
    simp [PresheafOfModules.restrictₛₗ]
    rfl

/-- Tensoring maps of systems degreewise. -/
noncomputable def tensorSystemMap {M M' N N' : Systems.{u, v} A}
    (f : M ⟶ M') (g : N ⟶ N') : tensorSystem A M N ⟶ tensorSystem A M' N' where
  app n := ModuleCat.ofHom (TensorProduct.map (f.app n).hom (g.app n).hom)
  naturality φ := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact congrArg₂ (fun x y => x ⊗ₜ[A.obj _] y)
      (PresheafOfModules.naturality_apply f φ x)
      (PresheafOfModules.naturality_apply g φ y)

/-- The ordinary tensor bifunctor on compatible module systems. -/
noncomputable def systemTensor : Systems.{u, v} A ⥤ Systems.{u, v} A ⥤ Systems.{u, v} A where
  obj M :=
    { obj := tensorSystem A M
      map := fun f => tensorSystemMap A (𝟙 M) f
      map_id := by
        intros
        apply PresheafOfModules.hom_ext
        intro n
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        rfl
      map_comp := by
        intros
        apply PresheafOfModules.hom_ext
        intro n
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        rfl }
  map f :=
    { app := fun N => tensorSystemMap A f (𝟙 N)
      naturality := by
        intros
        apply PresheafOfModules.hom_ext
        intro n
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        rfl }
  map_id := by
    intros
    apply NatTrans.ext
    funext N
    apply PresheafOfModules.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  map_comp := by
    intros
    apply NatTrans.ext
    funext N
    apply PresheafOfModules.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

/-- The tensor bifunctor `systemTensor A` is additive in its first variable. -/
instance : (systemTensor.{u, v} A).Additive where
  map_add := by
    intros
    apply NatTrans.ext
    funext N
    apply PresheafOfModules.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact TensorProduct.add_tmul _ _ _

/-- For each system `M`, the functor `M ⊗ -` on systems is additive. -/
instance (M : Systems.{u, v} A) : ((systemTensor A).obj M).Additive where
  map_add := by
    intros
    apply PresheafOfModules.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact TensorProduct.tmul_add _ _ _

/-- The total complex of the pointwise tensor bicomplex, with its Koszul differential
and induced transition maps. -/
noncomputable def totalTensorSystem :
    CochainComplex (Systems.{u, v} A) ℤ ⥤
      CochainComplex (Systems.{u, v} A) ℤ ⥤ CochainComplex (Systems.{u, v} A) ℤ :=
  (systemTensor A).map₂CochainComplex

end TensorModel

/-- A derived tensor product on the derived category of compatible module systems over an inverse
system of commutative rings. Its K-flat comparison identifies the entire system with the
concrete total-tensor model and agrees with the canonical comparisons at every index. -/
public structure DerivedTensorProduct
    (A : Functor ℕᵒᵖ CommRingCat.{u})
    [HasDerivedCategory.{w}
      (PresheafOfModules.{max u v} (A ⋙ forget₂ CommRingCat RingCat))] where
  /-- The derived tensor bifunctor. -/
  tensor :
    DerivedCategory (PresheafOfModules.{max u v} (A ⋙ forget₂ CommRingCat RingCat)) ⥤
      DerivedCategory (PresheafOfModules.{max u v} (A ⋙ forget₂ CommRingCat RingCat)) ⥤
        DerivedCategory (PresheafOfModules.{max u v} (A ⋙ forget₂ CommRingCat RingCat))
  /-- The derived tensor product is symmetric. -/
  symmetry : tensor ≅ tensor.flip
  /-- Tensoring in the first variable commutes with shifts. -/
  commShift_left : ∀ L, (tensor.flip.obj L).CommShift ℤ
  /-- Tensoring in the second variable commutes with shifts. -/
  commShift_right : ∀ K, (tensor.obj K).CommShift ℤ
  /-- Tensoring in the first variable is exact. -/
  exact_left : ∀ L, letI := commShift_left L; (tensor.flip.obj L).IsTriangulated
  /-- Tensoring in the second variable is exact. -/
  exact_right : ∀ K, letI := commShift_right K; (tensor.obj K).IsTriangulated
  /-- Evaluation at an index computes the derived tensor product by tensoring a K-flat component
  with the other component and taking the total complex. -/
  evaluationIso : ∀
      (M N : CochainComplex
        (PresheafOfModules.{max u v} (A ⋙ forget₂ CommRingCat RingCat)) ℤ)
      (n : ℕ),
      CochainComplex.KFlat
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from
          ((PresheafOfModules.evaluation
            (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) → (
        ((PresheafOfModules.evaluation
          (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapDerivedCategory).obj
            ((tensor.obj (DerivedCategory.Q.obj M)).obj (DerivedCategory.Q.obj N)) ≅
          DerivedCategory.Q.obj
            ((TleftCochain
              (((PresheafOfModules.evaluation
                (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj M)).obj
              (((PresheafOfModules.evaluation
                (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj N)))
  /-- The componentwise computation is natural in the arbitrary representative. -/
  evaluationIso_naturality_right : ∀
      (M N N' : CochainComplex
        (PresheafOfModules.{max u v} (A ⋙ forget₂ CommRingCat RingCat)) ℤ)
      (n : ℕ)
      (hM : CochainComplex.KFlat
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from
          ((PresheafOfModules.evaluation
            (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M))
      (f : N ⟶ N'),
      (evaluationIso M N n hM).hom ≫
          DerivedCategory.Q.map
            ((TleftCochain
              (((PresheafOfModules.evaluation
                (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj M)).map
              (((PresheafOfModules.evaluation
                (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map f)) =
        ((PresheafOfModules.evaluation
          (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapDerivedCategory).map
            ((tensor.obj (DerivedCategory.Q.obj M)).map (DerivedCategory.Q.map f)) ≫
          (evaluationIso M N' n hM).hom
  /-- The componentwise computation is natural between K-flat representatives in the first
  variable. -/
  evaluationIso_naturality_left : ∀
      (M M' N : CochainComplex
        (PresheafOfModules.{max u v} (A ⋙ forget₂ CommRingCat RingCat)) ℤ)
      (n : ℕ)
      (hM : CochainComplex.KFlat
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from
          ((PresheafOfModules.evaluation
            (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M))
      (hM' : CochainComplex.KFlat
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from
          ((PresheafOfModules.evaluation
            (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M'))
      (f : M ⟶ M'),
      (evaluationIso M N n hM).hom ≫
          DerivedCategory.Q.map
            ((TrightCochain
              (((PresheafOfModules.evaluation
                (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj N)).map
              (((PresheafOfModules.evaluation
                (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map f)) =
        ((PresheafOfModules.evaluation
          (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapDerivedCategory).map
            ((tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj N)) ≫
          (evaluationIso M' N n hM').hom

  /-- The ordinary tensor-total comparison at an index. The next field fixes it on each
  homogeneous summand, so it is the canonical coproduct comparison. -/
  totalTensorEvaluationIso : ∀
      (M N : CochainComplex (Systems.{u, v} A) ℤ) (n : ℕ),
      let E := (PresheafOfModules.evaluation
        (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex (ComplexShape.up ℤ)
      E.obj (((totalTensorSystem A).obj M).obj N) ≅
        (TleftCochain (E.obj M)).obj (E.obj N)
  /-- Evaluation of the total complex identifies the same tensor summand on both sides. -/
  totalTensorEvaluationIso_ι : ∀
      (M N : CochainComplex (Systems.{u, v} A) ℤ) (n : ℕ)
      (p q k : ℤ) (h : p + q = k),
      let E := PresheafOfModules.evaluation (A ⋙ forget₂ CommRingCat RingCat) (op n)
      let EC := E.mapHomologicalComplex (ComplexShape.up ℤ)
      E.map (HomologicalComplex.ιMapBifunctor M N (systemTensor A)
          (ComplexShape.up ℤ) p q k h) ≫
        (totalTensorEvaluationIso M N n).hom.f k =
      HomologicalComplex.ιMapBifunctor
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from EC.obj M)
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from EC.obj N)
        (curriedTensor (ModuleCat.{max u v} (A.obj (op n))))
          (ComplexShape.up ℤ) p q k h
  /-- A componentwise K-flat representative computes the entire derived module system,
  including its transition maps, by the actual pointwise total-tensor system. -/
  comparison : ∀ (M N : CochainComplex (Systems.{u, v} A) ℤ),
      (∀ n : ℕ, CochainComplex.KFlat
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from
          ((PresheafOfModules.evaluation
            (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) →
      ((tensor.obj (DerivedCategory.Q.obj M)).obj (DerivedCategory.Q.obj N) ≅
        DerivedCategory.Q.obj (((totalTensorSystem A).obj M).obj N))
  /-- The whole-system comparison is natural in both representatives. -/
  comparison_naturality : ∀
      (M M' N N' : CochainComplex (Systems.{u, v} A) ℤ)
      (hM : ∀ n : ℕ, CochainComplex.KFlat
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from
          ((PresheafOfModules.evaluation
            (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M))
      (hM' : ∀ n : ℕ, CochainComplex.KFlat
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from
          ((PresheafOfModules.evaluation
            (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M'))
      (f : M ⟶ M') (g : N ⟶ N'),
      (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj N) ≫
          (tensor.obj (DerivedCategory.Q.obj M')).map (DerivedCategory.Q.map g) ≫
          (comparison M' N' hM').hom =
        (comparison M N hM).hom ≫ DerivedCategory.Q.map
          (((totalTensorSystem A).map f).app N ≫ ((totalTensorSystem A).obj M').map g)
  /-- The existing evaluation isomorphisms are the evaluations of the whole-system
  comparison. In particular they respect every index transition, with the restriction of
  scalars built into `PresheafOfModules`. -/
  evaluationIso_eq_comparison : ∀
      (M N : CochainComplex (Systems.{u, v} A) ℤ)
      (hM : ∀ n : ℕ, CochainComplex.KFlat
        (show CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ from
          ((PresheafOfModules.evaluation
            (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M))
      (n : ℕ),
      let E := PresheafOfModules.evaluation (A ⋙ forget₂ CommRingCat RingCat) (op n)
      evaluationIso M N n (hM n) =
        E.mapDerivedCategory.mapIso (comparison M N hM) ≪≫
          E.mapDerivedCategoryFactors.app (((totalTensorSystem A).obj M).obj N) ≪≫
          DerivedCategory.Q.mapIso (totalTensorEvaluationIso M N n)

end ModuleSystemKFlatComparison
end

end Definitions
