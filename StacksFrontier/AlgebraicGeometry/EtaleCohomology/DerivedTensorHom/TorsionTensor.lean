module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionRepresentative

/-!
# Derived tensor products with torsion objects of `D(X_étale, ℤ)`

Let `X` be a scheme. If `E ∈ D(X_étale, ℤ)` has torsion cohomology sheaves, then so does
`E ⊗^L_ℤ K` for every `K ∈ D(X_étale, ℤ)`, without any boundedness assumption.

The proof runs on the constant ringed site `(X_étale, ℤ̲)`
(`Stacks.EtaleCohomology.etaleRingedSite`),
where the derived tensor product is defined. By [Stacks, Tag 0DD7]
(`Stacks.Torsion.exists_torsion_complex_of_equivalence`) `E` is represented by a complex with
torsion terms, and the derived tensor product of such a complex with anything has torsion
cohomology (`Stacks.Torsion.torsionModules_homology_tensor`). Torsion is compared on the two
sides of `Stacks.EtaleCohomology.etaleModulesEquivalence` by
`Stacks.EtaleCohomology.isTorsionEtaleModule_etaleModulesEquivalence_inverse_obj_iff`.

## Main results

* `isTorsionEtaleModule_etaleModulesEquivalence_inverse_obj_iff` and
  `isTorsionEtaleModule_iff_torsionModules_etaleModulesEquivalence_functor_obj`: torsion read on
  sheaves of `Λ`-modules and on modules over the constant ringed site agree.
* `isTorsionEtaleModule_homology_etaleDerivedTensor`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Torsion

universe u r

namespace Stacks.EtaleCohomology

section Comparison

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- Being a torsion sheaf of modules on the small étale site is invariant under isomorphism. -/
private theorem isTorsionEtaleModule_of_iso {Λ' : Type r} [CommRing Λ'] {X' : Scheme.{u}}
    {F G : EtaleModules.{u, r} Λ' X'} (e : F ≅ G) (h : IsTorsionEtaleModule.{u, r} Λ' X' F) :
    IsTorsionEtaleModule.{u, r} Λ' X' G :=
  torsionSheafProperty_of_iso X'.smallEtaleTopology ((etaleModuleForgetAb.{u, r} Λ' X').mapIso e) h

/-- **Torsion on the two sides of `etaleModulesEquivalence`.** A module over the constant ringed
site `(X_étale, Λ̲)` is torsion exactly when the corresponding sheaf of `Λ`-modules on the small
étale site is. -/
theorem isTorsionEtaleModule_etaleModulesEquivalence_inverse_obj_iff
    (M : EtaleRingedModules.{u, r} Λ X) :
    IsTorsionEtaleModule.{u, r} Λ X ((etaleModulesEquivalence.{u, r} Λ X).inverse.obj M) ↔
      torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf (etaleRingedSite.{u, r} Λ X).O) M := by
  let E := (AsSmall.equiv : X.Etale ≌ AsSmall.{max (u + 1) r} X.Etale)
  let S := E.sheafCongr X.smallEtaleTopology (etaleSmallModelTopology.{u, r} X)
    AddCommGrpCat.{max (u + 1) r}
  refine ⟨fun h => ?_, torsionSheafProperty_sheafPushforwardContinuous E.functor _⟩
  have h' : torsionSheafProperty (etaleSmallModelTopology.{u, r} X)
      (S.functor.obj (S.inverse.obj ((SheafOfModules.toSheaf _).obj M))) :=
    torsionSheafProperty_sheafPushforwardContinuous E.inverse _ h
  exact torsionSheafProperty_of_iso _ (S.counitIso.app _) h'

/-- **Torsion on the two sides of `etaleModulesEquivalence`**, read through its functor. -/
theorem isTorsionEtaleModule_iff_torsionModules_etaleModulesEquivalence_functor_obj
    (F : EtaleModules.{u, r} Λ X) :
    IsTorsionEtaleModule.{u, r} Λ X F ↔
      torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf (etaleRingedSite.{u, r} Λ X).O)
        ((etaleModulesEquivalence.{u, r} Λ X).functor.obj F) := by
  rw [← isTorsionEtaleModule_etaleModulesEquivalence_inverse_obj_iff]
  let e := (etaleModulesEquivalence.{u, r} Λ X).unitIso.app F
  exact ⟨isTorsionEtaleModule_of_iso e, isTorsionEtaleModule_of_iso e.symm⟩

end Comparison

section DerivedTensor

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **The derived tensor product with an object of `D(X_étale, ℤ)` with torsion cohomology has
torsion cohomology.** If every cohomology sheaf of `E` is torsion, then so is every cohomology
sheaf of `E ⊗^L_ℤ K`, for every `K`; neither object is assumed bounded. -/
theorem isTorsionEtaleModule_homology_etaleDerivedTensor
    (E K : DerivedCategory (EtaleModules.{u, 0} ℤ X))
    (hE : ∀ n : ℤ,
      IsTorsionEtaleModule.{u, 0} ℤ X ((DerivedCategory.homologyFunctor _ n).obj E))
    (n : ℤ) :
    IsTorsionEtaleModule.{u, 0} ℤ X
      ((DerivedCategory.homologyFunctor _ n).obj
        (((etaleDerivedTensor.{u, 0} ℤ X).obj E).obj K)) := by
  let : HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1, u, u + 1}
      X.smallEtaleTopology
  let eM := etaleModulesEquivalence.{u, 0} ℤ X
  let eD := etaleDerivedEquivalence.{u, 0} ℤ X
  let Φ := Sheaf.coefficientEquivalence X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence
  let G := eM.symm.trans Φ
  have : G.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : G.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have hE' : ∀ m : ℤ, torsionSheafProperty X.smallEtaleTopology
      (G.functor.obj ((DerivedCategory.homologyFunctor _ m).obj (eD.functor.obj E))) := fun m =>
    isTorsionEtaleModule_of_iso (eM.inverse.mapIso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso eM.functor m).app
        E) ≪≫ (eM.unitIso.app _).symm).symm (hE m)
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    exists_torsion_complex_of_equivalence X.smallEtaleTopology G (eD.functor.obj E) hE'
  have hP' : ∀ p, torsionModules
      (Stacks.SheafOfModules.Tensor.ringSheaf (etaleRingedSite.{u, 0} ℤ X).O) (P.X p) := fun p =>
    (isTorsionEtaleModule_etaleModulesEquivalence_inverse_obj_iff ℤ X _).1 (hP p)
  let T := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    (etaleRingedSite.{u, 0} ℤ X).O
  have hZ := torsionModules_homology_tensor _ T P hP' (eD.functor.obj K) n
  rw [← isTorsionEtaleModule_etaleModulesEquivalence_inverse_obj_iff] at hZ
  exact isTorsionEtaleModule_of_iso
    (eM.inverse.mapIso ((DerivedCategory.homologyFunctor _ n).mapIso
        ((T.tensor.mapIso eP).app (eD.functor.obj K))) ≪≫
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso eM.inverse n).app
        _).symm) hZ

end DerivedTensor

end Stacks.EtaleCohomology
