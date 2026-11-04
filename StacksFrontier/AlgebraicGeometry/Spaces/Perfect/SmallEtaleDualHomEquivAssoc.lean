module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualHomEquiv
public import StacksFrontier.Algebra.Homology.HomBicomplexExt

/-!
# `Hom(𝒪_X, (E^∨ ⊗^L P) ⊗^L N) ≅ Hom(E, P ⊗^L N)` for a perfect `E`

The associativity of `⊗^L` followed by
`AlgebraicGeometry.Space.smallEtaleHomAddEquivUnitTensorDual`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorAssocNatIso`: the associator of `⊗^L` as an
  isomorphism of functors in the third variable.
* `AlgebraicGeometry.Space.smallEtaleHomAddEquivUnitTensorDualAssoc`, and as an isomorphism of
  functors, `AlgebraicGeometry.Space.smallEtaleUnitTensorDualAssocNatIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The associativity of `⊗^L` on `D(𝒪_X)` in its third variable**, as an isomorphism of
functors `(P ⊗^L Q) ⊗^L - ≅ P ⊗^L (Q ⊗^L -)` at the spelling
`AlgebraicGeometry.Space.smallEtaleDerivedTensor`: the associator
`Stacks.SheafOfModules.DerivedTensorProduct.associatorGeneral` and its naturality. -/
def smallEtaleDerivedTensorAssocNatIso
    (P Q : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS X).obj (((smallEtaleDerivedTensor B S hS X).obj P).obj Q) ≅
      (smallEtaleDerivedTensor B S hS X).obj Q ⋙ (smallEtaleDerivedTensor B S hS X).obj P :=
  NatIso.ofComponents (fun N => (smallEtaleDerivedTensorProduct B S hS X).associatorGeneral P Q N)
    (fun q => (smallEtaleDerivedTensorProduct B S hS X).associatorGeneral_naturality_right P Q q)

/-- **`Hom(𝒪_X, (E^∨ ⊗^L P) ⊗^L N) ≃+ Hom(E, P ⊗^L N)` for a perfect `E`.** -/
def smallEtaleHomAddEquivUnitTensorDualAssoc
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (P N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (structureDerived X ⟶ ((smallEtaleDerivedTensor B S hS X).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj P)).obj
          N) ≃+
      (E ⟶ ((smallEtaleDerivedTensor B S hS X).obj P).obj N) :=
  (CochainComplex.HomBicomplex.postcompAddEquiv (X := structureDerived X)
      ((smallEtaleDerivedTensorAssocNatIso B S hS X (smallEtaleDerivedDual B S hS X E) P).app
        N)).trans
    (smallEtaleHomAddEquivUnitTensorDual B S hS X E hE _).symm

/-- The identification `smallEtaleHomAddEquivUnitTensorDualAssoc` is natural in `N`. -/
theorem smallEtaleHomAddEquivUnitTensorDualAssoc_naturality
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {N N' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (q : N ⟶ N')
    (x : structureDerived X ⟶ ((smallEtaleDerivedTensor B S hS X).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj P)).obj
          N) :
    smallEtaleHomAddEquivUnitTensorDualAssoc B S hS X E hE P N'
        (x ≫ ((smallEtaleDerivedTensor B S hS X).obj
          (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj P)).map
            q) =
      smallEtaleHomAddEquivUnitTensorDualAssoc B S hS X E hE P N x ≫
        ((smallEtaleDerivedTensor B S hS X).obj P).map q := by
  apply (smallEtaleHomAddEquivUnitTensorDual B S hS X E hE _).injective
  simp only [smallEtaleHomAddEquivUnitTensorDualAssoc, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, CochainComplex.HomBicomplex.postcompAddEquiv_apply,
    smallEtaleHomAddEquivUnitTensorDual_naturality, Category.assoc, Iso.app_hom]
  congr 1
  exact (smallEtaleDerivedTensorAssocNatIso B S hS X (smallEtaleDerivedDual B S hS X E)
    P).hom.naturality q

/-- **`Hom(𝒪_X, (E^∨ ⊗^L P) ⊗^L -) ≅ Hom(E, P ⊗^L -)` for a perfect `E`**, as an isomorphism of
functors `D(𝒪_X) ⥤ Ab`. -/
def smallEtaleUnitTensorDualAssocNatIso
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS X).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj P) ⋙
        preadditiveCoyoneda.obj (op (structureDerived X)) ≅
      (smallEtaleDerivedTensor B S hS X).obj P ⋙ preadditiveCoyoneda.obj (op E) :=
  NatIso.ofComponents
    (fun N => (smallEtaleHomAddEquivUnitTensorDualAssoc B S hS X E hE P N).toAddCommGrpIso)
    (fun {N N'} q => by
      ext x
      exact smallEtaleHomAddEquivUnitTensorDualAssoc_naturality B S hS X E hE P q x)

end AlgebraicGeometry.Space

end
