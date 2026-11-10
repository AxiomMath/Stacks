module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product is linear over multiplication by a local section

Let `(𝒞, 𝒪)` be a ringed site and let `a` be a compatible family of local sections of `𝒪`,
giving the central endomorphism `a ·` of `Mod(𝒪)`. This file proves that the derived tensor
product carries that endomorphism to itself in its second variable:

`(K ⊗^𝐋_𝒪 -) (a ·) = a ·`.

This is the tensor-side counterpart of
`AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd`, which the library has for
the derived internal Hom. It is what [Stacks, Tag 0CQH] needs in order to run the source's
reason for the derived completeness of `K ⊗^𝐋_𝒪 𝒪/ℐⁿ` — that the object is annihilated by
powers of the local sections of `ℐ`.

## Main results

* `Stacks.SheafOfModules.Tensor.sheafTensor_obj_map_globalSectionToEnd`: the ordinary tensor
  product of sheaves of modules is linear over multiplication by a compatible family of local
  sections, in its second variable.
* `Stacks.SheafOfModules.Tensor.mapBifunctorMap_smul_id`: the same for the total tensor complex.
* `Stacks.SheafOfModules.Tensor.derivedTensor_map_globalSectionToEnd`: the same for the derived
  tensor product of [Stacks, Tag 06YU].

## Implementation notes

The proof is the one `Stacks.DerivedTensor.AdicKoszul.tensor_map_smul_id` uses over a ring,
transported to a ringed site. Three levels:

* **Sheaves.** `⊗_𝒪` is the sheafification of the objectwise tensor product, so both sides are
  morphisms out of a sheafification and agree as soon as their adjoint transposes do. Against
  the unit of `PresheafOfModules.sheafificationAdjunction` the left-hand side is the objectwise
  statement `x ⊗ (a · y) = a · (x ⊗ y)` — `TensorProduct.tmul_smul` — and the right-hand side is
  the `𝒪`-linearity of that unit. This mirrors
  `AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd`, which is the same
  statement in the *first* variable for the other construction of the tensor product.
* **Complexes.** The total tensor complex is a coproduct of objectwise tensor products in each
  degree, and the whiskered map is objectwise the sheaf-level one, so extensionality on the
  summands of the total complex reduces the complex-level statement to the sheaf-level one.
* **The derived category.** Every object of `D(𝒪)` is the class of a K-flat complex, and on a
  K-flat *right* representative the derived tensor product is the total tensor complex,
  naturally and with no flatness asked of the left factor —
  `Stacks.SheafOfModules.DerivedTensorProduct.comparisonRight_naturality`. Cancelling that
  comparison isomorphism transports the complex-level statement to the two classes, and
  `AlgebraicGeometry.RingedSite.map_smul_id_of_iso` and `map_smul_id_of_natIso` spread it from
  the chosen representatives to all of `D(𝒪)`.

Everything here is stated at the `ringSheaf X.O` spelling of the
structure sheaf, which is the one `sheafTensor`, `tensorComplex` and
`Stacks.SheafOfModules.DerivedTensorProduct` are stated at. It is the same sheaf of rings as
`AlgebraicGeometry.RingedSite.ringSheaf X`, but only up to the proof-irrelevant
`HasSheafCompose` instance each supplies, so the two are interchangeable in term mode and *not*
by `rw` or `simp`, whose motive and keyed-matching checks compare the instance arguments
syntactically. The proofs below rewrite, so they stay inside one spelling throughout; consumers
stated at the other spelling take these results as arguments, which type-checks by defeq.

No linearity of `⊗_𝒪` over anything other than these central endomorphisms is used, and no
hypothesis on an ideal sheaf — nilpotence, finite type or global generation — appears anywhere
here.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u d

namespace Stacks.SheafOfModules.Tensor

variable (X : AlgebraicGeometry.RingedSite.{u, u, u}) [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The structure sheaf of a ringed site is a sheaf of commutative rings. -/
theorem isMulCommutative_tensorRingSheaf (V : X.Cᵒᵖ) :
    IsMulCommutative ((ringSheaf X.O).obj.obj V) := by
  change IsMulCommutative (X.O.obj.obj V)
  infer_instance

attribute [local instance] isMulCommutative_tensorRingSheaf

/-- Sheaves of modules are linear over the centre of their own category; this is the linear
structure the derived-completeness predicate of [Stacks, Tag 0999] uses. -/
abbrev linearCatCenterTensorRingSheaf :
    Linear (CatCenter (SheafOfModules.{u} (ringSheaf X.O)))
      (SheafOfModules.{u} (ringSheaf X.O)) :=
  Linear.ofRingMorphism (RingHom.id _)

attribute [local instance] linearCatCenterTensorRingSheaf

/-- **The tensor product of sheaves of modules is linear over multiplication by a compatible
family of local sections of `𝒪`, in its second variable.** Both sides are morphisms out of a
sheafification, so they agree as soon as their adjoint transposes do; against the unit of the
sheafification adjunction the statement is `x ⊗ (a · y) = a · (x ⊗ y)`. -/
theorem sheafTensor_obj_map_globalSectionToEnd
    (a : ((ringSheaf X.O).obj ⋙ forget RingCat.{u}).sections)
    (M N : SheafOfModules.{u} (ringSheaf X.O)) :
    ((sheafTensor.{u, u, u, u, u} X.O).obj M).map
        ((globalSectionToEnd
          (ringSheaf X.O) a).asHom.app N) =
      (globalSectionToEnd
        (ringSheaf X.O) a).asHom.app (((sheafTensor.{u, u, u, u, u} X.O).obj M).obj N) := by
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheaf X.O).obj)).homEquiv _ _).injective ?_
  refine (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf X.O).obj)).unit.naturality
    (PresheafOfModules.tensorHom (𝟙 M.val)
      ((globalSectionToEnd
        (ringSheaf X.O) a).asHom.app N).val)).symm).trans ?_
  refine PresheafOfModules.hom_ext fun U => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
  refine Eq.trans ?_ ((((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj M.val N.val)).app U).hom.map_smul
    (a.val U) (x ⊗ₜ y))
  exact congrArg _ (TensorProduct.tmul_smul
    (R' := ToType ((X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U)) (a.val U) x y)

/-- The same statement with multiplication by `a` written as the action of the central element
it defines on an identity morphism, which is the form the linear structure of [Stacks, Tag 0999]
uses. -/
theorem sheafTensor_obj_map_smul_id
    (a : ((ringSheaf X.O).obj ⋙ forget RingCat.{u}).sections)
    (M N : SheafOfModules.{u} (ringSheaf X.O)) :
    ((sheafTensor.{u, u, u, u, u} X.O).obj M).map
        (globalSectionToEnd (ringSheaf X.O) a • 𝟙 N) =
      globalSectionToEnd (ringSheaf X.O) a •
        𝟙 (((sheafTensor.{u, u, u, u, u} X.O).obj M).obj N) :=
  (congrArg ((sheafTensor.{u, u, u, u, u} X.O).obj M).map
      (Category.comp_id
        ((globalSectionToEnd
          (ringSheaf X.O) a).asHom.app N))).trans
    ((sheafTensor_obj_map_globalSectionToEnd X a M N).trans
      (Category.comp_id
        ((globalSectionToEnd
            (ringSheaf X.O) a).asHom.app
          (((sheafTensor.{u, u, u, u, u} X.O).obj M).obj N))).symm)

/-- **The total tensor complex is linear over multiplication by a compatible family of local
sections of `𝒪`, in its second variable.** Each degree of the total complex is a coproduct of
objectwise tensor products, on whose summands the whiskered map is the sheaf-level one. -/
theorem mapBifunctorMap_smul_id
    (a : ((ringSheaf X.O).obj ⋙ forget RingCat.{u}).sections)
    (P Q : CochainComplex
      (SheafOfModules.{u} (ringSheaf X.O)) ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 P)
        (globalSectionToEnd (ringSheaf X.O) a • 𝟙 Q)
        (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) =
      globalSectionToEnd (ringSheaf X.O) a •
        𝟙 (HomologicalComplex.mapBifunctor P Q (sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ)) := by
  apply HomologicalComplex.hom_ext
  intro j
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, HomologicalComplex.smul_f_apply,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Linear.comp_smul,
    Category.comp_id]
  change ((sheafTensor.{u, u, u, u, u} X.O).obj (P.X i₁)).map
        ((globalSectionToEnd (ringSheaf X.O) a).asHom.app (Q.X i₂) ≫ 𝟙 (Q.X i₂)) ≫
      HomologicalComplex.ιMapBifunctor P Q (sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ) i₁ i₂ j h =
    (globalSectionToEnd (ringSheaf X.O) a).asHom.app
        (((sheafTensor.{u, u, u, u, u} X.O).obj (P.X i₁)).obj (Q.X i₂)) ≫
      HomologicalComplex.ιMapBifunctor P Q (sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ) i₁ i₂ j h
  exact (congrArg
      (fun φ => ((sheafTensor.{u, u, u, u, u} X.O).obj (P.X i₁)).map φ ≫
        HomologicalComplex.ιMapBifunctor P Q (sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ) i₁ i₂ j h)
      (Category.comp_id ((globalSectionToEnd (ringSheaf X.O) a).asHom.app (Q.X i₂)))).trans
    (congrArg
      (fun φ => φ ≫ HomologicalComplex.ιMapBifunctor P Q (sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ) i₁ i₂ j h)
      (sheafTensor_obj_map_globalSectionToEnd X a (P.X i₁) (Q.X i₂)))

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (ringSheaf X.O))]

/-- Every object of `D(𝒪)` is the class of a K-flat complex, by [Stacks, Tag 06YS]. -/
theorem exists_kFlat_representative
    (L : DerivedCategory
      (SheafOfModules.{u} (ringSheaf X.O))) :
    ∃ P : CochainComplex
        (SheafOfModules.{u} (ringSheaf X.O)) ℤ,
      Stacks.SheafOfModules.IsKFlat X.O P ∧ Nonempty (DerivedCategory.Q.obj P ≅ L) := by
  obtain ⟨P, p, hP, hp⟩ :=
    Stacks.SheafOfModules.exists_kFlat_quasiIso X (DerivedCategory.Q.objPreimage L)
  have := hp
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso L⟩⟩

/-- The derived tensor product is linear over multiplication by a family of local sections at
the classes of a K-flat right representative, where it is the total tensor complex. -/
theorem derivedTensor_map_smul_id_representatives
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)
    (a : ((ringSheaf X.O).obj ⋙ forget RingCat.{u}).sections)
    (P Q : CochainComplex
      (SheafOfModules.{u} (ringSheaf X.O)) ℤ)
    (hQ : Stacks.SheafOfModules.IsKFlat X.O Q) :
    (T.tensor.obj (DerivedCategory.Q.obj P)).map
        (globalSectionToEnd (ringSheaf X.O) a •
          𝟙 (DerivedCategory.Q.obj Q)) =
      globalSectionToEnd (ringSheaf X.O) a •
        𝟙 ((T.tensor.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q)) := by
  have hQc : DerivedCategory.Q.map (globalSectionToEnd (ringSheaf X.O) a • 𝟙 Q) =
      globalSectionToEnd (ringSheaf X.O) a • 𝟙 (DerivedCategory.Q.obj Q) := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  have hQt : DerivedCategory.Q.map (globalSectionToEnd (ringSheaf X.O) a •
        𝟙 (HomologicalComplex.mapBifunctor P Q (sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ))) =
      globalSectionToEnd (ringSheaf X.O) a •
        𝟙 (DerivedCategory.Q.obj
          (HomologicalComplex.mapBifunctor P Q (sheafTensor.{u, u, u, u, u} X.O)
            (ComplexShape.up ℤ))) := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  have h := (T.comparisonRight_naturality (𝟙 P)
      (globalSectionToEnd (ringSheaf X.O) a • 𝟙 Q) hQ hQ).trans
    (congrArg (fun φ => (T.comparisonRight P Q hQ).hom ≫ φ)
      ((congrArg DerivedCategory.Q.map (mapBifunctorMap_smul_id X a P Q)).trans hQt))
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  rw [hQc] at h
  exact AlgebraicGeometry.RingedSite.eq_smul_id_of_mono h

/-- **The derived tensor product is linear over multiplication by a compatible family of local
sections of `𝒪`, in its second variable.** This is the tensor-side counterpart of
`AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd`, and the statement the
derived completeness of [Stacks, Tag 0CQH] runs on. -/
theorem derivedTensor_map_globalSectionToEnd
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)
    (a : ((ringSheaf X.O).obj ⋙ forget RingCat.{u}).sections)
    (K L : DerivedCategory
      (SheafOfModules.{u} (ringSheaf X.O))) :
    (T.tensor.obj K).map
        (globalSectionToEnd (ringSheaf X.O) a • 𝟙 L) =
      globalSectionToEnd (ringSheaf X.O) a •
        𝟙 ((T.tensor.obj K).obj L) := by
  obtain ⟨P, _, ⟨eP⟩⟩ := exists_kFlat_representative X K
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := exists_kFlat_representative X L
  exact AlgebraicGeometry.RingedSite.map_smul_id_of_natIso (T.tensor.mapIso eP) _ L
    (AlgebraicGeometry.RingedSite.map_smul_id_of_iso _ _ eQ
      (derivedTensor_map_smul_id_representatives X T a P Q hQ))

end Stacks.SheafOfModules.Tensor

end
