module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDualGroupsAbelianExt
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.ThickeningLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSymmNaturality

/-!
# The coefficient identifications `𝒫 ⊗ ℱ ≅ ℱ ⊗ p^*K̃` and their naturality

For an object `x = (Spec A, ℱ)` of `Coh_{X/B}` over a chart, the coefficients of its obstruction
classes and of its tangent identification (second proof of Stacks 08WA) are modules `𝒫 ⊗ ℱ` on
`X_A` with `𝒫` identified with the pullback `p^*K̃` of the module associated to an `A`-module
`K`; they are identified with the coefficient `ℱ ⊗ p^*K̃` of
`AlgebraicGeometry.Space.CoherentSituation.extGroup`
(`AlgebraicGeometry.Space.CoherentSituation.coefficientIsoOfIdealAt`). This file shows that
these identifications are natural for any map `𝒫₁ ⟶ 𝒫₂` matching a map `K₁ ⟶ K₂`
(`AlgebraicGeometry.Space.CoherentSituation.coefficientIsoOfIdealAt_hom_naturality`).

This module is a helper and carries no `@[stacks]` attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u

namespace Stacks.FlatChangeOfRings

open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Exchanging the factors of `𝒫 ⊗ ℱ` along identifications is natural.** For identifications
`ιᵢ : 𝒫ᵢ ≅ 𝒬ᵢ` and `εᵢ : 𝒬ᵢ ≅ ℛᵢ` carrying `l : 𝒫₁ ⟶ 𝒫₂` to `m` and `m` to `m'`, the composites
`𝒫ᵢ ⊗ ℱ ≅ 𝒬ᵢ ⊗ ℱ ≅ ℱ ⊗ 𝒬ᵢ ≅ ℱ ⊗ ℛᵢ` carry `l ⊗ ℱ` to `ℱ ⊗ m'`. -/
theorem sheafTensorSymmIso_trans_naturality (O : Sheaf J CommRingCat.{u})
    (F : SheafOfModules.{u} (ringSheaf O))
    {P₁ P₂ Q₁ Q₂ R₁ R₂ : SheafOfModules.{u} (ringSheaf O)} (l : P₁ ⟶ P₂) (m : Q₁ ⟶ Q₂)
    (m' : R₁ ⟶ R₂) (ι₁ : P₁ ≅ Q₁) (ι₂ : P₂ ≅ Q₂) (ε₁ : Q₁ ≅ R₁) (ε₂ : Q₂ ≅ R₂)
    (hl : l ≫ ι₂.hom = ι₁.hom ≫ m) (hm : m ≫ ε₂.hom = ε₁.hom ≫ m') :
    ((sheafTensor O).flip.obj F).map l ≫
        (((sheafTensor O).flip.obj F).mapIso ι₂ ≪≫ sheafTensorSymmIso O F Q₂ ≪≫
          ((sheafTensor O).obj F).mapIso ε₂).hom =
      (((sheafTensor O).flip.obj F).mapIso ι₁ ≪≫ sheafTensorSymmIso O F Q₁ ≪≫
          ((sheafTensor O).obj F).mapIso ε₁).hom ≫ ((sheafTensor O).obj F).map m' := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, hl, Functor.map_comp_assoc,
    reassoc_of% (sheafTensorRight_map_comp_sheafTensorSymmIso_hom O F m), ← Functor.map_comp, hm,
    Functor.map_comp]

end Stacks.FlatChangeOfRings

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
  (x : CoherentObject D) [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
  {A : Type u} [CommRing A] (e : A ≃+* D.baseRing x)

section Coefficient

variable {P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)}
  {K : ModuleCat.{u} A}

/-- **The coefficient identification `𝒫 ⊗ ℱ ≅ ℱ ⊗ ψ^*K̃`** of an identification `𝒫 ≅ φ^*K̃`, for
equal morphisms `φ = ψ` of ringed topoi `X_T ⟶ T`. -/
def coefficientIsoOfIdealAt (φ ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left))) (h : φ = ψ)
    (ι : P ≅ φ.pullbackModules.obj
      ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e K))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
        (objectToposModule x)).obj P ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).obj
        (objectToposModule x)).obj (ψ.pullbackModules.obj
          ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e K))) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
      (objectToposModule x)).mapIso ι ≪≫
    Stacks.FlatChangeOfRings.sheafTensorSymmIso.{u, u + 1, u} _ _ _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).obj
        (objectToposModule x)).mapIso
      (eqToIso (congrArg (fun χ : Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left)) =>
        χ.pullbackModules.obj
          ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e K))) h))

/-- **The coefficient identifications are natural**: a map `𝒫₁ ⟶ 𝒫₂` matching a map `K₁ ⟶ K₂`
of `A`-modules under `𝒫ᵢ ≅ φ^*K̃ᵢ` induces, under `𝒫ᵢ ⊗ ℱ ≅ ℱ ⊗ ψ^*K̃ᵢ`, the map
`ℱ ⊗ ψ^*K̃₁ ⟶ ℱ ⊗ ψ^*K̃₂`. -/
theorem coefficientIsoOfIdealAt_hom_naturality
    (φ ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left))) (h : φ = ψ)
    {P₁ P₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)}
    {K₁ K₂ : ModuleCat.{u} A} (κ : K₁ ⟶ K₂) (l : P₁ ⟶ P₂)
    (ι₁ : P₁ ≅ φ.pullbackModules.obj
      ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e K₁)))
    (ι₂ : P₂ ≅ φ.pullbackModules.obj
      ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e K₂)))
    (hl : l ≫ ι₂.hom = ι₁.hom ≫ φ.pullbackModules.map
      ((representedAffineAssociated B S hS x.T.left).map
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map κ))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
        (objectToposModule x)).map l ≫ (D.coefficientIsoOfIdealAt x e φ ψ h ι₂).hom =
      (D.coefficientIsoOfIdealAt x e φ ψ h ι₁).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).obj
          (objectToposModule x)).map (ψ.pullbackModules.map
            ((representedAffineAssociated B S hS x.T.left).map
            ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map κ))) := by
  subst h
  exact Stacks.FlatChangeOfRings.sheafTensorSymmIso_trans_naturality
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O (objectToposModule x) l
    (φ.pullbackModules.map ((representedAffineAssociated B S hS x.T.left).map
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map κ)))
    (φ.pullbackModules.map ((representedAffineAssociated B S hS x.T.left).map
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map κ)))
    ι₁ ι₂ (eqToIso rfl) (eqToIso rfl) hl (by simp)

end Coefficient

end AlgebraicGeometry.Space.CoherentSituation

end
