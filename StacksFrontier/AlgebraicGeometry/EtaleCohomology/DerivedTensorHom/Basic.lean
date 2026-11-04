module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ConstantRingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomBijectionNatural
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomAdjunctionTransport

/-!
# Derived tensor product and derived internal Hom on `D(X_étale, Λ)`

Let `X` be a scheme and `Λ` a commutative ring. The derived category `D(X_étale, Λ)` of sheaves of
`Λ`-modules on the small étale site of `X` carries the derived tensor product `- ⊗^L_Λ -` and the
derived internal Hom `RHom_Λ(-, -)`, tied together by the bijection

`Hom(A, RHom_Λ(B, M)) = Hom(A ⊗^L_Λ B, M)`

of [Stacks, Tag 08J8], natural in all three objects. In the source, `D(X_étale, Λ)` is by
definition the derived category of modules over the ringed site `(X_étale, Λ̲)`; here it is
`DerivedCategory (EtaleModules Λ X)`, and the three structures are those of the ringed site
`Stacks.EtaleCohomology.etaleRingedSite Λ X` read through the equivalence
`Stacks.EtaleCohomology.etaleDerivedEquivalence`.

## Main definitions

* `Stacks.EtaleCohomology.etaleDerivedTensor`: `- ⊗^L_Λ -` on `D(X_étale, Λ)`.
* `Stacks.EtaleCohomology.etaleDerivedHom`: `RHom_Λ(-, -)` on `D(X_étale, Λ)`.
* `Stacks.EtaleCohomology.etaleTensorHomAdjunction`: the tensor–internal-Hom adjunction of
  [Stacks, Tag 08J8] between them, with its naturality ([Stacks, Tag 08J9]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- **The derived tensor product `- ⊗^L_Λ -` on `D(X_étale, Λ)`**: the derived tensor product of
modules over the constant ringed site `(X_étale, Λ̲)`, read on `D(X_étale, Λ)`. -/
abbrev etaleDerivedTensor :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory (EtaleModules.{u, r} Λ X) :=
  TensorHomAdjunction.transportTensor (etaleDerivedEquivalence.{u, r} Λ X)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ X).O)

/-- **The derived internal Hom `RHom_Λ(-, -)` on `D(X_étale, Λ)`**: the derived internal Hom of
modules over the constant ringed site `(X_étale, Λ̲)`, read on `D(X_étale, Λ)`. -/
abbrev etaleDerivedHom :
    (DerivedCategory (EtaleModules.{u, r} Λ X))ᵒᵖ ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory (EtaleModules.{u, r} Λ X) :=
  TensorHomAdjunction.transportHom (etaleDerivedEquivalence.{u, r} Λ X)
    (RingedSite.derivedSheafHomBifunctor (etaleRingedSite.{u, r} Λ X))

/-- **The tensor–internal-Hom adjunction of [Stacks, Tag 08J8] on `D(X_étale, Λ)`**, natural in
the three objects ([Stacks, Tag 08J9]): `Hom(A, RHom_Λ(B, M)) ≃ Hom(A ⊗^L_Λ B, M)`. -/
def etaleTensorHomAdjunction :
    TensorHomAdjunction (etaleDerivedTensor.{u, r} Λ X) (etaleDerivedHom.{u, r} Λ X) :=
  TensorHomAdjunction.transport (etaleDerivedEquivalence.{u, r} Λ X)
    (derivedTensorHomAdjunction (etaleRingedSite.{u, r} Λ X))

end Stacks.EtaleCohomology

end
