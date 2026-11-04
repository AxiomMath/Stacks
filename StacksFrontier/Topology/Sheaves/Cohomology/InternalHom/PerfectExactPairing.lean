module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationRightUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafModulesMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLawGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation

/-!
# The triangle identities for the dual of a perfect object of `D(O_X)`

Let `(X, O_X)` be a ringed space and `K` a perfect object of `D(O_X)`, with
`K^∨ = RSheafHom(K, O_X)`. The coevaluation `η : O_X ⟶ K ⊗^L K^∨` and the application morphism
`ev : K^∨ ⊗^L K ⟶ O_X` of Stacks 08J8 satisfy the first triangle identity
`(η ▷ K) ≫ α ≫ (K ◁ ev) = λ ≫ ρ⁻¹`, and an endomorphism `c` of `K^∨` with `c ▷ K ≫ ev = ev` is
the identity. The exact pairing of `K` with `K^∨` itself is
`Stacks.SheafOfModules.exactPairingDerivedDual`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
  Opposite AlgebraicGeometry

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

/-- If `c : K^∨ ⟶ K^∨` satisfies `c ▷ K ≫ ev = ev` for the application morphism
`ev : RSheafHom(K, O_X) ⊗^L K ⟶ O_X` of Stacks 08J8, then `c` is the identity. -/
theorem eq_id_of_whiskerRight_comp_derivedSheafHomCounit
    (K : DerivedCategory (StructureSheafModules Rc))
    (c : ((derivedSheafHom Rc).obj (op K)).obj (RingedSite.derivedStructureSheaf (ringedSite Rc)) ⟶
      ((derivedSheafHom Rc).obj (op K)).obj (RingedSite.derivedStructureSheaf (ringedSite Rc)))
    (hc : c ▷ K ≫ derivedSheafHomCounit Rc K (RingedSite.derivedStructureSheaf (ringedSite Rc)) =
      derivedSheafHomCounit Rc K (RingedSite.derivedStructureSheaf (ringedSite Rc))) :
    c = 𝟙 _ := by
  refine (derivedSheafHomTensorEquiv Rc _ K
    (RingedSite.derivedStructureSheaf (ringedSite Rc))).injective ?_
  rw [← derivedSheafHomCounit_whiskerRight_eq', hc]
  rfl

/-- The first triangle identity for the application morphism: for a perfect `K`, the
coevaluation `η : O_X ⟶ K ⊗^L K^∨` of `Stacks.SheafOfModules.derivedDualCoevaluation` and the
application morphism `ev : K^∨ ⊗^L K ⟶ O_X` of Stacks 08J8 satisfy
`(η ▷ K) ≫ α ≫ (K ◁ ev) = λ ≫ ρ⁻¹`. -/
theorem derivedDualCoevaluation_triangle_derivedSheafHomCounit
    (K : DerivedCategory (StructureSheafModules Rc)) (hK : (ringedSite Rc).IsPerfect K) :
    derivedDualCoevaluation Rc K hK ▷ K ≫ (α_ K (derivedDual Rc K) K).hom ≫
        K ◁ derivedSheafHomCounit Rc K (RingedSite.derivedStructureSheaf (ringedSite Rc)) =
      (λ_ K).hom ≫ (ρ_ K).inv := by
  have happ := derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_compositionLaw
    Rc K K (derivedSheafHomCounit Rc K (RingedSite.derivedStructureSheaf (ringedSite Rc)))
    (compositionApplicationLaw Rc K (RingedSite.derivedStructureSheaf (ringedSite Rc)) K)
  have hι : (show 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
        ((derivedSheafHom Rc).obj (op K)).obj K from
      RingedSite.derivedIdentitySection (ringedSite Rc) K) ▷ K ≫
      derivedSheafHomCounit Rc K K = (λ_ K).hom := by
    rw [derivedSheafHomCounit_unit_law_monoidal' Rc K K, RingedSite.derivedIdentitySection_eq,
      AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply, Category.comp_id]
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rwa [← happ, ← Category.assoc, ← comp_whiskerRight, derivedDualCoevaluation_comp]

end Monoidal

end Stacks.SheafOfModules

end
