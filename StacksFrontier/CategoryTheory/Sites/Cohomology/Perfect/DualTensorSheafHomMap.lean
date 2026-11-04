module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom

/-!
# The map of Stacks 08JJ for an arbitrary dualized object

For a ringed site `(C, O)` and objects `K, M` of `D(O)`, the map
`M ⊗^L_O K^∨ ⟶ RSheafHom_O(K, M)`: the diagonal of Stacks 0BYS followed by the internal Hom out of
`K` of the right unit constraint. It is natural in both variables, and invertible when `K` is
perfect.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomMap`: the map
  `M ⊗^L_O K^∨ ⟶ RSheafHom_O(K, M)`.
* `AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomTrans`: the same map as a transformation
  of bifunctors.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedDualTensorSheafHomMap_of_isPerfect`: the map is
  invertible when `K` is perfect.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- The map underlying the isomorphism of Stacks 08JJ, `M ⊗^L_O K^∨ ⟶ RSheafHom_O(K, M)`, defined
for every `K`: the diagonal of Stacks 0BYS followed by the internal Hom out of `K` of the right
unit constraint. -/
def derivedDualTensorSheafHomMap
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).obj (derivedDual X K) ⟶
      ((derivedSheafHomBifunctor X).obj (op K)).obj M :=
  derivedTensorHomDiagonal X M (derivedStructureSheaf X) K ≫
    ((derivedSheafHomBifunctor X).obj (op K)).map
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
        (canonicalRingedSiteDerivedTensorProduct X) M).hom

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The map of Stacks 08JJ is natural in `M`. -/
theorem derivedDualTensorSheafHomMap_natural
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : M ⟶ M') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app (derivedDual X K) ≫
        derivedDualTensorSheafHomMap X K M' =
      derivedDualTensorSheafHomMap X K M ≫ ((derivedSheafHomBifunctor X).obj (op K)).map f := by
  have hu : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app
          (derivedStructureSheaf X) ≫
        (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
          (canonicalRingedSiteDerivedTensorProduct X) M').hom =
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
          (canonicalRingedSiteDerivedTensorProduct X) M).hom ≫ f :=
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality X
      (canonicalRingedSiteDerivedTensorProduct X) f
  exact comp_square_row (derivedTensorHomDiagonal_natural_left X (derivedStructureSheaf X) K f)
    ((((derivedSheafHomBifunctor X).obj (op K)).map_comp _ _).symm.trans
      ((((derivedSheafHomBifunctor X).obj (op K)).congr_map hu).trans
        (((derivedSheafHomBifunctor X).obj (op K)).map_comp _ _)))

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The map of Stacks 08JJ is contravariantly natural in the dualized object. -/
theorem derivedDualTensorSheafHomMap_natural_dual
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g : K' ⟶ K) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).map
          (((derivedSheafHomBifunctor X).map g.op).app (derivedStructureSheaf X)) ≫
        derivedDualTensorSheafHomMap X K' M =
      derivedDualTensorSheafHomMap X K M ≫ ((derivedSheafHomBifunctor X).map g.op).app M := by
  exact comp_square_row (derivedTensorHomDiagonal_natural_hom X M (derivedStructureSheaf X) g)
    (((derivedSheafHomBifunctor X).map g.op).naturality
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
        (canonicalRingedSiteDerivedTensorProduct X) M).hom).symm

/-- **The map of Stacks 08JJ as a transformation of bifunctors**, natural in the dualized object
`K` (contravariantly) and in `M`: `M ⊗^L_O K^∨ ⟶ RSheafHom_O(K, M)`. -/
def derivedDualTensorSheafHomTrans :
    (derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X) ⋙
        (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip ⟶
      derivedSheafHomBifunctor X where
  app K :=
    { app M := derivedDualTensorSheafHomMap X K.unop M
      naturality _ _ f := derivedDualTensorSheafHomMap_natural X K.unop f }
  naturality _ _ g := by
    ext M
    exact derivedDualTensorSheafHomMap_natural_dual X M g.unop

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The components of `derivedDualTensorSheafHomTrans` are the maps
`derivedDualTensorSheafHomMap`. -/
@[simp]
lemma derivedDualTensorSheafHomTrans_app_app
    (K : (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedDualTensorSheafHomTrans X).app K).app M = derivedDualTensorSheafHomMap X K.unop M :=
  rfl

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- The map of Stacks 08JJ is invertible when the dualized object is perfect. -/
theorem isIso_derivedDualTensorSheafHomMap_of_isPerfect
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    IsIso (derivedDualTensorSheafHomMap X K M) :=
  (derivedDualTensorSheafHomIso X K M hK).isIso_hom

end AlgebraicGeometry.RingedSite

end
