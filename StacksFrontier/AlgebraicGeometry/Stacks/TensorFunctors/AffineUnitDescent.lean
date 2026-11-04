module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelDescent

/-!
# A locally bijective map between cartesian modules is bijective over affine objects

Let `η : P ⟶ N` be a morphism of presheaves of modules on the fppf site associated with a
category fibred in groupoids, both cartesian on affine objects, and locally bijective (for
instance a sheafification unit).  Then `η` is bijective on the sections over every affine object.
This is faithfully flat descent along a finite fppf covering family of affine objects refining the
sieves supplied by local injectivity and local surjectivity: the product of the rings of the
members is faithfully flat, and cartesianness identifies the base changes of the sections over
the object with the sections over the members.

## Main results

* `AlgebraicGeometry.FibredSite.bijective_app_of_isLocallyBijective_of_isCartesianOnAffines`.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u v w

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)

/-- The sections map of a morphism of presheaves of modules, as a linear map over the commutative
ring of sections. -/
noncomputable def sectionLinearMap {P N : PresheafOfModules.{u}
    (ringStructureSheafCore B S hS p hp .fppf).obj} (η : P ⟶ N) (x : 𝒳) :
    letI := sectionModule hp P x
    letI := sectionModule hp N x
    P.obj (op x) →ₗ[sectionRing hp x] N.obj (op x) :=
  letI := sectionModule hp P x
  letI := sectionModule hp N x
  { toFun := η.app (op x)
    map_add' := map_add _
    map_smul' := fun c m => (η.app (op x)).hom.map_smul c m }

/-- **A locally bijective morphism between presheaves of modules cartesian on affine objects is
bijective on the sections over an affine object.** -/
theorem bijective_app_of_isLocallyBijective_of_isCartesianOnAffines
    {P N : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf).obj} (η : P ⟶ N)
    [PresheafOfModules.IsLocallyInjective (BigFppfOver.associatedTopology B S hS p .fppf) η]
    [PresheafOfModules.IsLocallySurjective (BigFppfOver.associatedTopology B S hS p .fppf) η]
    (hP : IsCartesianOnAffines hp P) (hN : IsCartesianOnAffines hp N) {x : 𝒳}
    (hx : IsAffineOver B S hS (p.obj x)) : Function.Bijective (η.app (op x)) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := hx
  constructor
  · intro m m' hmm'
    have hS' := Presheaf.equalizerSieve_mem (BigFppfOver.associatedTopology B S hS p .fppf)
      ((PresheafOfModules.toPresheaf _).map η) (X := op x) m m' hmm'
    obtain ⟨n, z, φ, haff, hmem, -, hfppf⟩ :=
      exists_finite_affine_fppf_ofArrows_le B S hS p hp hx hS'
    let : ∀ i, Algebra (sectionRing hp x) (sectionRing hp (z i)) :=
      fun i => sectionAlgebra hp (φ i)
    have : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (z i))) := haff
    have : Module.FaithfullyFlat (sectionRing hp x) (∀ i, sectionRing hp (z i)) :=
      _root_.AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage _ hfppf
        (fun _ => rfl)
    let := sectionModule hp P x
    have hinj := PresheafOfModules.injective_map_of_forall_injective_baseChange (N := P) φ
      (sectionRing hp x) (fun i => sectionRing hp (z i))
      (fun i => (restrictionBaseChangeMap hp P (φ i)).toAddMonoidHom)
      (fun i => (hP (φ i) hx (haff i)).1) (fun i n => by
        simp [restrictionBaseChangeMap, restrictionLinearMap]
        rfl)
    exact hinj (funext fun i => hmem i)
  · intro nx
    have hS' := Presheaf.imageSieve_mem (BigFppfOver.associatedTopology B S hS p .fppf)
      ((PresheafOfModules.toPresheaf _).map η) (U := op x) nx
    obtain ⟨n, z, φ, haff, hmem, -, hfppf⟩ :=
      exists_finite_affine_fppf_ofArrows_le B S hS p hp hx hS'
    let : ∀ i, Algebra (sectionRing hp x) (sectionRing hp (z i)) :=
      fun i => sectionAlgebra hp (φ i)
    have : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (z i))) := haff
    have : Module.FaithfullyFlat (sectionRing hp x) (∀ i, sectionRing hp (z i)) :=
      _root_.AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage _ hfppf
        (fun _ => rfl)
    let := sectionModule hp P x
    let := sectionModule hp N x
    let : ∀ i, Module (sectionRing hp (z i)) (P.obj (op (z i))) :=
      fun i => sectionModule hp P (z i)
    let : ∀ i, Module (sectionRing hp (z i)) (N.obj (op (z i))) :=
      fun i => sectionModule hp N (z i)
    let : ∀ i, Module (sectionRing hp x) (P.obj (op (z i))) :=
      fun i => sectionModuleAlong hp P (φ i)
    let : ∀ i, Module (sectionRing hp x) (N.obj (op (z i))) :=
      fun i => sectionModuleAlong hp N (φ i)
    have : ∀ i, IsScalarTower (sectionRing hp x) (sectionRing hp (z i)) (P.obj (op (z i))) :=
      fun i => sectionIsScalarTower hp P (φ i)
    have : ∀ i, IsScalarTower (sectionRing hp x) (sectionRing hp (z i)) (N.obj (op (z i))) :=
      fun i => sectionIsScalarTower hp N (φ i)
    exact Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange
      (sectionRing hp x) (fun i => sectionRing hp (z i)) (sectionLinearMap hp η x)
      (fun i => sectionLinearMap hp η (z i)) (fun i => restrictionLinearMap hp P (φ i))
      (fun i => restrictionLinearMap hp N (φ i))
      (fun i q => (PresheafOfModules.naturality_apply η (φ i).op q).symm)
      (fun i => (hP (φ i) hx (haff i)).2) (fun i => (hN (φ i) hx (haff i)).1)
      (n := nx) hmem

end AlgebraicGeometry.FibredSite
