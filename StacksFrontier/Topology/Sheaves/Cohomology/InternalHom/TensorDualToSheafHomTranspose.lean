module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationRightUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafModulesMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLawGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionReduction

/-!
# The transpose of the canonical map `M ⊗^L L^∨ ⟶ RSheafHom(L, M)`

Let `(X, O_X)` be a ringed space and `L, M ∈ D(O_X)`.  Under the tensor–internal-hom bijection of
Stacks 08DI the canonical map `M ⊗^L L^∨ ⟶ RSheafHom(L, M)` of Stacks 08I1 is the contraction

`(M ⊗^L L^∨) ⊗^L L ⟶ M ⊗^L (L^∨ ⊗^L L) ⟶ M ⊗^L O_X ⟶ M`

of the associativity constraint, the evaluation and the right unit constraint of Tag 0FPT.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_derivedTensorDualToSheafHom`
* `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_toEquiv_derivedTensorDualToSheafHom`: the
  same, with the bijection read as a bijection of sets, together with the naturality of that
  bijection in its two variables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
  Opposite AlgebraicGeometry
open scoped CategoryTheory.Prod

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

-- `derivedSheafHomCounit Rc` and the monoidal structure are stated over
-- `StructureSheafModules Rc`, while the ringed-site statements are over
-- `Tensor.ringSheaf (ringedSite Rc).O`; the attribute below lets instance search and `rw` see that
-- these are the same sheaf of rings.
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

-- The monoidal structure `⊗_{O_X}` on `Mod(O_X)`, with its symmetric, preadditive and closed
-- refinements.
attribute [local instance] monoidalSpace' symmetricSpace'
  monoidalPreadditiveSpace'
  monoidalClosedSpace'

variable [(Tensor.sheafTensor.{u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

attribute [local instance 10000] CochainComplex.symmetricCategory

section Monoidal

attribute [local instance] derivedMonoidalStructure

/-- **The transpose of the canonical map of Stacks 08I1 is the contraction against the
evaluation.**  Under the bijection of Stacks 08DI, `M ⊗^L L^∨ ⟶ RSheafHom(L, M)` corresponds to
the associativity constraint, the evaluation `L^∨ ⊗^L L ⟶ O_X` and the right unit constraint. -/
theorem derivedSheafHomTensorEquiv_derivedTensorDualToSheafHom
    (L M : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafHomTensorEquiv Rc _ L M (derivedTensorDualToSheafHom Rc L M) =
      derivedAssociatorHom Rc M (derivedDual Rc L) L ≫
        ((derivedTensor Rc).obj M).map
          (derivedSheafHomCounit Rc L (RingedSite.derivedStructureSheaf (ringedSite Rc))) ≫
          derivedRightUnitorHom Rc M := by
  rw [← derivedSheafHomCounit_whiskerRight_eq']
  exact derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_compositionLaw Rc L M
    (derivedSheafHomCounit Rc L (RingedSite.derivedStructureSheaf (ringedSite Rc)))
    (compositionApplicationLaw Rc L (RingedSite.derivedStructureSheaf (ringedSite Rc)) M)

end Monoidal

/-! ### The bijection of Stacks 08DI read as a bijection -/

/-- The bijection of Stacks 08DI, read as a bijection, at the identity is the evaluation. -/
theorem derivedSheafHomTensorEquiv_toEquiv_id (K M : DerivedCategory (StructureSheafModules Rc)) :
    (derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op K)).obj M) K M).toEquiv
        (𝟙 _) = derivedSheafHomCounit Rc K M :=
  rfl

/-- The bijection of Stacks 08DI, read as a bijection, is the evaluation after tensoring. -/
theorem derivedSheafHomTensorEquiv_toEquiv_apply
    (A K M : DerivedCategory (StructureSheafModules Rc))
    (y : A ⟶ ((derivedSheafHom Rc).obj (op K)).obj M) :
    (derivedSheafHomTensorEquiv Rc A K M).toEquiv y =
      (Functor.uncurry.obj (derivedTensor Rc)).map (y ×ₘ 𝟙 K) ≫ derivedSheafHomCounit Rc K M :=
  (derivedTensor_map_app_comp_derivedSheafHomCounit Rc A K M y).symm.trans
    (congrArg (· ≫ derivedSheafHomCounit Rc K M) (by simp [Functor.uncurry]))

/-- **The bijection of Stacks 08DI, read as a bijection, is natural in its source variable.** -/
theorem derivedSheafHomTensorEquiv_toEquiv_naturality_source
    (A A' B C : DerivedCategory (StructureSheafModules Rc)) (φ : A ⟶ A')
    (ψ : A' ⟶ ((derivedSheafHom Rc).obj (op B)).obj C) :
    (derivedSheafHomTensorEquiv Rc A B C).toEquiv (φ ≫ ψ) =
      (Functor.uncurry.obj (derivedTensor Rc)).map (φ ×ₘ 𝟙 B) ≫
        (derivedSheafHomTensorEquiv Rc A' B C).toEquiv ψ := by
  rw [derivedSheafHomTensorEquiv_toEquiv_apply, derivedSheafHomTensorEquiv_toEquiv_apply,
    ← Category.assoc, ← Functor.map_comp, prod_comp, Category.comp_id]

/-- **The bijection of Stacks 08DI, read as a bijection, is natural in its target variable.** -/
theorem derivedSheafHomTensorEquiv_toEquiv_naturality_target
    (A B C C' : DerivedCategory (StructureSheafModules Rc))
    (f : A ⟶ ((derivedSheafHom Rc).obj (op B)).obj C) (g : C ⟶ C') :
    (derivedSheafHomTensorEquiv Rc A B C').toEquiv (f ≫ ((derivedSheafHom Rc).obj (op B)).map g) =
      (derivedSheafHomTensorEquiv Rc A B C).toEquiv f ≫ g :=
  derivedSheafHomTensorEquiv_naturality_target Rc A B g f

/-- **The transpose of the canonical map of Stacks 08I1, read as a bijection.** -/
theorem derivedSheafHomTensorEquiv_toEquiv_derivedTensorDualToSheafHom
    (L M : DerivedCategory (StructureSheafModules Rc)) :
    (derivedSheafHomTensorEquiv Rc _ L M).toEquiv (derivedTensorDualToSheafHom Rc L M) =
      derivedAssociatorHom Rc M (derivedDual Rc L) L ≫
        (Functor.uncurry.obj (derivedTensor Rc)).map (𝟙 M ×ₘ
          (derivedSheafHomTensorEquiv Rc _ L
            (RingedSite.derivedStructureSheaf (ringedSite Rc))).toEquiv (𝟙 _)) ≫
          derivedRightUnitorHom Rc M := by
  rw [derivedSheafHomTensorEquiv_toEquiv_id]
  refine (derivedSheafHomTensorEquiv_derivedTensorDualToSheafHom Rc L M).trans ?_
  congr 2
  simp [Functor.uncurry]

/-! ### Maps with the same transpose up to the right unit constraint -/

/-- The inverse of the right unit constraint of Stacks 0FPT, at the bifunctor spelling of its
target. -/
def derivedRightUnitorInv (K : DerivedCategory (StructureSheafModules Rc)) :
    K ⟶ ((derivedTensor Rc).obj K).obj (RingedSite.derivedStructureSheaf (ringedSite Rc)) :=
  letI := derivedMonoidalStructure Rc
  (ρ_ K).inv

/-- The right unit constraint followed by its inverse is the identity. -/
@[reassoc (attr := simp)]
theorem derivedRightUnitorHom_inv (K : DerivedCategory (StructureSheafModules Rc)) :
    derivedRightUnitorHom Rc K ≫ derivedRightUnitorInv Rc K = 𝟙 _ :=
  let := derivedMonoidalStructure Rc
  (ρ_ K).hom_inv_id

/-- The inverse of the right unit constraint followed by the constraint is the identity. -/
@[reassoc (attr := simp)]
theorem derivedRightUnitorInv_hom (K : DerivedCategory (StructureSheafModules Rc)) :
    derivedRightUnitorInv Rc K ≫ derivedRightUnitorHom Rc K = 𝟙 _ :=
  let := derivedMonoidalStructure Rc
  (ρ_ K).inv_hom_id

/-- The inverse of the right unit constraint is an isomorphism. -/
instance (K : DerivedCategory (StructureSheafModules Rc)) : IsIso (derivedRightUnitorInv Rc K) :=
  ⟨⟨derivedRightUnitorHom Rc K, derivedRightUnitorInv_hom Rc K, derivedRightUnitorHom_inv Rc K⟩⟩

/-- **The transpose of the canonical map of Stacks 08I1, precomposed with any map**, read as a
bijection: the contraction against the evaluation. -/
theorem derivedSheafHomTensorEquiv_toEquiv_comp_derivedTensorDualToSheafHom
    (L M A : DerivedCategory (StructureSheafModules Rc))
    (c : A ⟶ ((derivedTensor Rc).obj M).obj (derivedDual Rc L)) :
    (derivedSheafHomTensorEquiv Rc A L M).toEquiv (c ≫ derivedTensorDualToSheafHom Rc L M) =
      (Functor.uncurry.obj (derivedTensor Rc)).map (c ×ₘ 𝟙 L) ≫
        derivedAssociatorHom Rc M (derivedDual Rc L) L ≫
          (Functor.uncurry.obj (derivedTensor Rc)).map (𝟙 M ×ₘ
            derivedSheafHomCounit Rc L (RingedSite.derivedStructureSheaf (ringedSite Rc))) ≫
            derivedRightUnitorHom Rc M := by
  rw [derivedSheafHomTensorEquiv_toEquiv_naturality_source,
    derivedSheafHomTensorEquiv_toEquiv_derivedTensorDualToSheafHom,
    derivedSheafHomTensorEquiv_toEquiv_id]

end Stacks.SheafOfModules

end
