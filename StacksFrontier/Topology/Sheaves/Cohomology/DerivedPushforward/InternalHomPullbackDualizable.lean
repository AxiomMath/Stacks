module

public import StacksFrontier.CategoryTheory.Monoidal.PairingInternalHomComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackMonoidalFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonBraiding
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkTransportClauses
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomEquivalenceTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeComparisonMaps

/-!
# Stacks 08I3 at a dualizable object

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `E` be an object of `D(𝒪_Y)`
with a left dual `E'` for the symmetric monoidal structure of Stacks 0FPT (for instance a perfect
`E` and `E' = E^∨`, Stacks 0FPC). The functor `- ⊗^L E` then has the two right adjoints
`- ⊗^L E'` and `R𝓗om(E, -)`, whence a canonical isomorphism

`θ_M : M ⊗^L E' ⟶ R𝓗om(E, M)`

(`Stacks.Cohomology.DerivedInternalHomPullback.dualTensorToSheafHom`). This file proves that the
canonical map of Stacks 08I3, `Lh^*R𝓗om(E, M) ⟶ R𝓗om(Lh^*E, Lh^*M)`, is identified by `θ` with
the monoidality comparison of Stacks 079U, and deduces that the base-change comparison for a
derived internal hom out of `E` is identified with the base-change comparison for a derived tensor
product with `E'`.

## Main results

All names below are in the namespace `Stacks.Cohomology.DerivedInternalHomPullback`.

* `isIso_dualTensorToSheafHom`: `θ` is an isomorphism.
* `map_dualTensorToSheafHom_comp_derivedPullbackSheafHomMap`:
  `Lh^*(θ_M) ≫ c = (Lh^*(M ⊗^L E') ≅ Lh^*M ⊗^L Lh^*E') ≫ θ_{Lh^*M}`.
* `map_dualTensorToSheafHom_comp_baseChangeSheafHomComparison` and
  `map_kflatBraiding_comp_baseChangeComparison`: the base-change comparison of a derived internal
  hom out of `E` is, through `θ` and the commutativity constraint, the one of a derived tensor
  product with `E'`.

## Implementation notes

The monoidal structure `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` and the
monoidal structure of `Lh^*` (`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal`)
are stated at a spelling of `D(𝒪_Z)` whose category instance is recognised as the one the derived
pullback and the derived internal hom are stated at only under the reducibility attributes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackMonoidalFunctor`, while under
those attributes the tensor–internal-hom bijection of Stacks 08DI no longer unifies with its own
naturality statements. So the `Bridge` section re-reads the monoidal structures, the pairings and
the commutativity constraint at the internal-hom spelling (`kflatMonoidal`,
`kflatPullbackMonoidal`, `kflatExactPairing`, `kflatPullbackExactPairing`, `kflatBraiding`), and
everything after it is stated there.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open scoped CategoryTheory.Prod
open AlgebraicGeometry
open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

section Bridge

attribute [local implicit_reducible]
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Sheaf TopCat.Presheaf.IsSheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable (Z : RingedSpace.{u, u})

/-- The symmetric monoidal structure of Stacks 0FPT on `D(𝒪_Z)`, re-seated on the derived tensor
product of Stacks 06YU (`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`), read
on the spelling `DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)` of `D(𝒪_Z)` at
which the derived pullback and the derived internal hom are stated. -/
@[instance_reducible]
def kflatMonoidal :
    MonoidalCategory (DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) :=
  canonicalDerivedMonoidal Z.sheaf

/-- An exact pairing for `canonicalDerivedMonoidal`, read for `kflatMonoidal`. -/
@[instance_reducible]
def kflatExactPairing {E E' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)}
    (p : @ExactPairing _ _ (canonicalDerivedMonoidal Z.sheaf) E E') :
    @ExactPairing _ _ (kflatMonoidal Z) E E' := p

/-- The identification of the tensor product of the canonical monoidal structure on `D(𝒪_Z)`,
which is the derived tensor product at which Stacks 079U is stated, with the derived tensor
product at which the derived internal hom of Stacks 08DI is stated: the component of
`Stacks.Cohomology.DerivedInternalHomPullback.tensorBridge`. -/
def tensorBridgeApp (A B : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (@MonoidalCategoryStruct.tensorObj _ _
      (kflatMonoidal Z).toMonoidalCategoryStruct A B) ≅
      (internalHomTensorUncurried Z).obj (A, B) :=
  (tensorBridge Z).app (A, B)

/-- `tensorBridgeApp` is natural in the first factor. -/
theorem tensorBridgeApp_naturality_left
    {A A' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)} (f : A ⟶ A')
    (B : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (@MonoidalCategoryStruct.whiskerRight _ _
      (kflatMonoidal Z).toMonoidalCategoryStruct _ _ f B) ≫
        (tensorBridgeApp Z A' B).hom =
      (tensorBridgeApp Z A B).hom ≫ (internalHomTensorUncurried Z).map (f ×ₘ 𝟙 B) := by
  have h := (tensorBridge Z).hom.naturality (f ×ₘ 𝟙 B)
  rw [EquivalenceTranspose.uncurryObj_map_mkHom_id] at h
  exact h

/-- The monoidal structure of `Lh^*` of Stacks 079U
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal`), for `kflatMonoidal`. -/
@[instance_reducible]
def kflatPullbackMonoidal {X Y : RingedSpace.{u, u}} (h : X ⟶ Y) :
    @Functor.Monoidal _ _ (kflatMonoidal Y) _ _ (kflatMonoidal X) (derivedPullbackFunctor h) :=
  Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal h

/-- The oplax structure of `kflatPullbackMonoidal` is the comparison of Stacks 079U. -/
theorem kflatPullbackMonoidal_δ {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)
    (A B : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Y)) :
    @Functor.OplaxMonoidal.δ _ _ (kflatMonoidal Y) _ _ (kflatMonoidal X)
        (derivedPullbackFunctor h) (kflatPullbackMonoidal h).toOplaxMonoidal A B =
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso h).hom.app (A, B) :=
  rfl

/-- The image under `Lh^*` of a left dual, for `kflatMonoidal`: `CategoryTheory.ExactPairing.map`
along `kflatPullbackMonoidal`. -/
@[instance_reducible]
def kflatPullbackExactPairing {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)
    (E E' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Y))
    (pE : @ExactPairing _ _ (kflatMonoidal Y) E E') :
    @ExactPairing _ _ (kflatMonoidal X) ((derivedPullbackFunctor h).obj E)
      ((derivedPullbackFunctor h).obj E') :=
  @ExactPairing.map _ _ _ _ (kflatMonoidal Y) (kflatMonoidal X)
    (derivedPullbackFunctor h) (kflatPullbackMonoidal h) E E' pE

/-- The comparison `pullbackTensorIso` of Stacks 079U at the internal-hom spelling of the
derived tensor product matches the oplax structure of the monoidal functor `Lh^*` under
`tensorBridgeApp`. -/
theorem map_tensorBridgeApp_comp_pullbackTensorIso {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)
    (A B : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (derivedPullbackFunctor h).map (tensorBridgeApp Y A B).hom ≫
        (pullbackTensorIso h).hom.app (A, B) =
      @Functor.OplaxMonoidal.δ _ _ (kflatMonoidal Y) _ _ (kflatMonoidal X)
          (derivedPullbackFunctor h) (kflatPullbackMonoidal h).toOplaxMonoidal A B ≫
        (tensorBridgeApp X ((derivedPullbackFunctor h).obj A)
          ((derivedPullbackFunctor h).obj B)).hom := by
  rw [kflatPullbackMonoidal_δ]
  simp only [pullbackTensorIso, tensorBridgeApp, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Iso.app_hom, Functor.prod_obj,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  exact (congrArg (· ≫ _) ((derivedPullbackFunctor h).map_id _)).trans (Category.id_comp _)


/-- The commutativity constraint of Stacks 0FPT on the derived tensor product
(`Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`), read on the spelling
`DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)` of `D(𝒪_Z)`. -/
def kflatBraiding (Z : RingedSpace.{u, u})
    (A B : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) :
    ((((derivedTensorProductFunctor Z.sheaf).obj A).obj B :
        DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) ⟶
      ((derivedTensorProductFunctor Z.sheaf).obj B).obj A) :=
  canonicalBraidingHom Z.sheaf A B

/-- `kflatBraiding` is invertible. -/
theorem isIso_kflatBraiding (Z : RingedSpace.{u, u})
    (A B : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) :
    IsIso (kflatBraiding Z A B) :=
  let := canonicalDerivedMonoidal Z.sheaf
  let := canonicalDerivedSymmetric Z.sheaf
  (β_ A B).isIso_hom

/-- `kflatBraiding` is natural in its second variable. -/
theorem kflatBraiding_naturality_right (Z : RingedSpace.{u, u})
    (A : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z))
    {K K' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)} (φ : K ⟶ K') :
    @CategoryStruct.comp (DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) _ _ _ _
      (((derivedTensorProductFunctor Z.sheaf).obj A).map φ) (kflatBraiding Z A K') =
      @CategoryStruct.comp (DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) _ _ _ _
        (kflatBraiding Z A K) (((derivedTensorProductFunctor Z.sheaf).map φ).app A) := by
  have hβ := Stacks.Cohomology.DerivedPullbackTensor.canonicalBraidingHom_naturality Z (𝟙 A) φ
  rw [EquivalenceTranspose.uncurryObj_map_id_mkHom,
    EquivalenceTranspose.uncurryObj_map_mkHom_id] at hβ
  exact hβ

/-- The comparison of Stacks 079U carries `kflatBraiding` to `kflatBraiding`. -/
theorem map_kflatBraiding_comp_derivedPullbackTensorIso {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)
    (A B : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Y)) :
    @CategoryStruct.comp (DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X)) _ _ _ _
      ((derivedPullbackFunctor h).map (kflatBraiding Y A B))
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso h).hom.app (B, A)) =
      @CategoryStruct.comp (DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X)) _ _ _ _
        ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso h).hom.app (A, B))
        (kflatBraiding X ((derivedPullbackFunctor h).obj A) ((derivedPullbackFunctor h).obj B)) :=
  Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding h A B

end Bridge

attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

section OneSpace

variable (Z : RingedSpace.{u, u})

/-- **The derived internal hom out of a dualizable object.** For a left dual `E'` of `E` in the
monoidal structure of Stacks 0FPT re-seated on the derived tensor product, the canonical map
`M ⊗^L E' ⟶ R𝓗om(E, M)`: the transpose under Stacks 08DI of the contraction against the
evaluation of the pairing. -/
abbrev dualTensorToSheafHom (E E' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z))
    [pE : @ExactPairing _ _ (kflatMonoidal Z) E E']
    (M : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) :
    ((((derivedTensorProductFunctor Z.sheaf).obj M).obj E' :
        DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj M) :=
  Transpose.pairingToInternalHom
    (C := DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z))
    (mC := kflatMonoidal Z)
    (Stacks.SheafOfModules.derivedSheafHom Z.sheaf) (internalHomTensorUncurried Z)
    (tensorHomEquiv Z) (tensorBridgeApp Z) E E' M

/-- `dualTensorToSheafHom` is an isomorphism. -/
theorem isIso_dualTensorToSheafHom
    (E E' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z))
    [pE : @ExactPairing _ _ (kflatMonoidal Z) E E']
    (M : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)) :
    IsIso (dualTensorToSheafHom Z E E' M) :=
  Transpose.isIso_pairingToInternalHom
    (C := DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z))
    (mC := kflatMonoidal Z)
    (H := Stacks.SheafOfModules.derivedSheafHom Z.sheaf) (T := internalHomTensorUncurried Z)
    (e := tensorHomEquiv Z) (b := tensorBridgeApp Z)
    (tensorHomEquivNaturalLeft_ringedSpace Z) (fun f B => tensorBridgeApp_naturality_left Z f B)
    E E' M

/-- `dualTensorToSheafHom` is natural in `M`. -/
theorem dualTensorToSheafHom_naturality
    (E E' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z))
    [pE : @ExactPairing _ _ (kflatMonoidal Z) E E']
    {M M' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z)} (f : M ⟶ M') :
    dualTensorToSheafHom Z E E' M ≫
        ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).map f =
      ((derivedTensorProductFunctor Z.sheaf).map f).app E' ≫ dualTensorToSheafHom Z E E' M' :=
  Transpose.pairingToInternalHom_naturality
    (C := DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z))
    (mC := kflatMonoidal Z)
    (H := Stacks.SheafOfModules.derivedSheafHom Z.sheaf) (T := internalHomTensorUncurried Z)
    (e := tensorHomEquiv Z) (b := tensorBridgeApp Z)
    (tensorHomEquivNaturalLeft_ringedSpace Z)
    (curriedTargetNatural_ringedSpace Z)
    (fun f B => tensorBridgeApp_naturality_left Z f B) E E' f

end OneSpace

section Pullback

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- **Stacks 08I3 at a dualizable object.** For a left dual `E'` of `E`, the canonical map
`Lh^*R𝓗om(E, M) ⟶ R𝓗om(Lh^*E, Lh^*M)` is, under `dualTensorToSheafHom` on each side and with
`Lh^*E'` the left dual of `Lh^*E` given by the monoidal functor `Lh^*`, the comparison of
Stacks 079U:

`Lh^*(θ_M) ≫ c = (Lh^*(M ⊗^L E') ≅ Lh^*M ⊗^L Lh^*E') ≫ θ_{Lh^*M}`. -/
theorem map_dualTensorToSheafHom_comp_derivedPullbackSheafHomMap
    (E E' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Y))
    [pE : @ExactPairing _ _ (kflatMonoidal Y) E E']
    (M : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Y)) :
    letI := kflatPullbackExactPairing h E E' pE
    (derivedPullbackFunctor h).map (dualTensorToSheafHom Y E E' M) ≫
        derivedPullbackSheafHomMap h E M =
      @Functor.OplaxMonoidal.δ _ _ (kflatMonoidal Y) _ _ (kflatMonoidal X)
          (derivedPullbackFunctor h) (kflatPullbackMonoidal h).toOplaxMonoidal M E' ≫
        dualTensorToSheafHom X ((derivedPullbackFunctor h).obj E)
          ((derivedPullbackFunctor h).obj E') ((derivedPullbackFunctor h).obj M) :=
  @Transpose.map_pairingToInternalHom_comp_homComparison _ _ _ _
    (kflatMonoidal Y) (kflatMonoidal X)
    (derivedPullbackFunctor h) (kflatPullbackMonoidal h)
    _ _ _ _ _ _ (pullbackTensorIso h) (tensorBridgeApp Y) (tensorBridgeApp X)
    (tensorHomEquivNaturalLeft_ringedSpace Y) (tensorHomEquivNaturalLeft_ringedSpace X)
    (fun f B => tensorBridgeApp_naturality_left X f B)
    (map_tensorBridgeApp_comp_pullbackTensorIso h) E E' pE M

end Pullback

section BaseChange

/-- Pasting a commuting square `a ≫ b = c ≫ d` with a commuting square `d ≫ ψ = ψ' ≫ e`. -/
private theorem comp_comp_eq_of_comp_eq_of_comp_eq {C : Type*} [Category C] {A B D F H K : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ F} {d : F ⟶ D} {ψ : D ⟶ K} {ψ' : F ⟶ H} {e : H ⟶ K}
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ ψ = ψ' ≫ e) : a ≫ b ≫ ψ = (c ≫ ψ') ≫ e := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

variable {X' X : RingedSpace.{u, u}} (h : X' ⟶ X)

/-- **The base-change comparison for a derived internal hom out of a dualizable object is the
base-change comparison for a derived tensor product.** For a left dual `E'` of `E` and
`φ : Lh^*K ⟶ K'`, the isomorphism `θ : K ⊗^L E' ≅ R𝓗om(E, K)` on `X` and its counterpart
`K' ⊗^L Lh^*E' ≅ R𝓗om(Lh^*E, K')` on `X'` (with `Lh^*E'` the image left dual) carry the
comparison `Lh^*(K ⊗^L E') ⟶ K' ⊗^L Lh^*E'` — the comparison of Stacks 079U followed by
`φ ⊗^L Lh^*E'` — to the comparison `Lh^*R𝓗om(E, K) ⟶ R𝓗om(Lh^*E, K')`. -/
theorem map_dualTensorToSheafHom_comp_baseChangeSheafHomComparison
    (E E' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X))
    [pE : @ExactPairing _ _ (kflatMonoidal X) E E']
    (K : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X))
    (K' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X'))
    (φ : (derivedPullbackFunctor h).obj K ⟶ K') :
    letI := kflatPullbackExactPairing h E E' pE
    (derivedPullbackFunctor h).map (dualTensorToSheafHom X E E' K) ≫
        Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison h E K K' φ =
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso h).hom.app (K, E') ≫
        ((derivedTensorProductFunctor X'.sheaf).map φ).app ((derivedPullbackFunctor h).obj E')) ≫
        dualTensorToSheafHom X' ((derivedPullbackFunctor h).obj E)
          ((derivedPullbackFunctor h).obj E') K' := by
  let := kflatPullbackExactPairing h E E' pE
  have hc := map_dualTensorToSheafHom_comp_derivedPullbackSheafHomMap h E E' K
  rw [kflatPullbackMonoidal_δ] at hc
  exact comp_comp_eq_of_comp_eq_of_comp_eq hc
    (dualTensorToSheafHom_naturality X' ((derivedPullbackFunctor h).obj E)
      ((derivedPullbackFunctor h).obj E') φ)

/-- **The base-change comparison for a derived tensor product commutes with the commutativity
constraint.** For `φ : Lh^*K ⟶ K'`, the commutativity constraints `E' ⊗^L K ≅ K ⊗^L E'` and
`Lh^*E' ⊗^L K' ≅ K' ⊗^L Lh^*E'` carry the comparison `Lh^*(E' ⊗^L K) ⟶ Lh^*E' ⊗^L K'` to the
comparison `Lh^*(K ⊗^L E') ⟶ K' ⊗^L Lh^*E'`. -/
theorem map_kflatBraiding_comp_baseChangeComparison
    (E' K : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X))
    (K' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X'))
    (φ : (derivedPullbackFunctor h).obj K ⟶ K') :
    (derivedPullbackFunctor h).map (kflatBraiding X E' K) ≫
        ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso h).hom.app (K, E') ≫
          ((derivedTensorProductFunctor X'.sheaf).map φ).app ((derivedPullbackFunctor h).obj E')) =
      Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison h E' K K' φ ≫
        kflatBraiding X' ((derivedPullbackFunctor h).obj E') K' := by
  exact comp_comp_eq_of_comp_eq_of_comp_eq (map_kflatBraiding_comp_derivedPullbackTensorIso h E' K)
    (kflatBraiding_naturality_right X' ((derivedPullbackFunctor h).obj E') φ).symm

end BaseChange

end Stacks.Cohomology.DerivedInternalHomPullback
