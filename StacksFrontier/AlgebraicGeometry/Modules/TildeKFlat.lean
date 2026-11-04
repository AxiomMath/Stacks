module

public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.Functoriality
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.PseudoCoherentRelative.TildePseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackOnRingedSpaces
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensorRing
import StacksCore.Tactic.StacksAttribute

/-!
# K-flatness of the sheaf associated to a complex of modules

Let `A` be a commutative ring and `K` a cochain complex of `A`-modules. Applying the affine
associated-sheaf construction `M ↦ M̃` in each degree gives a cochain complex of
`𝒪_{Spec A}`-modules. This file proves that if `K` is K-flat then so is `K̃`.

The proof is the source's. K-flatness of a complex of sheaves of modules on a ringed space is
detected on stalks, and the stalk of `K̃` at a point `x` is the base change of `K` along the
structural map `A → 𝒪_{Spec A, x}`, which is a localization of `A`; extension of scalars
preserves K-flatness.

## Main definitions

* `AlgebraicGeometry.specCommRingSheaf`: the structure sheaf of `Spec A`, read as a sheaf of
  commutative rings on the site of open subsets.
* `AlgebraicGeometry.toSpecStructureStalk`: the structural ring map `A → 𝒪_{Spec A, x}` into the
  `RingCat`-valued stalk.
* `AlgebraicGeometry.tildeStalkIso`: the stalk of `M̃` at `x` is `𝒪_{Spec A, x} ⊗_A M`.
* `AlgebraicGeometry.tildeStalkComplexIso`: the same for complexes.

## Main results

* `AlgebraicGeometry.kFlat_tilde`: **Stacks 08DV.**
* `AlgebraicGeometry.isLocalization_specStructureStalk`: the `RingCat`-valued stalk of the
  structure sheaf of `Spec A` at `x` is the localization of `A` at `x`.
* `AlgebraicGeometry.isBaseChange_tilde_toStalk`: the stalk of `M̃` is the base change of `M`
  along `A → 𝒪_{Spec A, x}`.

## Implementation notes

**Two spellings of the structure sheaf.** K-flatness of complexes of sheaves of modules is
stated for a sheaf of commutative rings on `Opens.grothendieckTopology X`, whereas
`AlgebraicGeometry.Scheme.sheaf` has type `TopCat.Sheaf CommRingCat X`. The two are the same
data, `TopCat.Sheaf` being a `def` over `CategoryTheory.Sheaf`, but they are not
interchangeable: instance search will not unfold a `def` at the transparency it uses, so no
instance stated for the site spelling is found at `(Spec A).sheaf`, and elaborating a statement
that forces the unfolding repeatedly does not terminate within the default heartbeat budget.
`specCommRingSheaf` performs the passage once, and `specCommRingSheaf_eq` records that it
changes nothing.

**Two stalk rings, and the `Ring` instance on them.** `AlgebraicGeometry.SheafOfModules.
stalkFunctor` takes its modules over the `RingCat`-valued stalk of the underlying sheaf of
rings, which carries only a `Ring` instance, while the localization machinery needs a
commutative one; `StacksDraft.StalkTensor.commRing_stalk_ringSheaf` supplies it, and
`commRing_specStructureStalk` seats that instance at the `Spec` spelling. The two `Ring`
structures on the stalk — `RingCat`'s and the one derived from that `CommRing` — are
definitionally equal but not syntactically, so `ModuleCat.isModule` is not *found* for a module
over the stalk once the `CommRing` is in scope. Every module structure this file needs is
therefore declared rather than inferred, with the body being the instance
`AlgebraicGeometry.SheafOfModules.stalkObj` itself used. For the same reason `one_smul` is not
synthesizable on a stalk, and `one_smul_tildeStalk` derives it from
`toSpecStructureStalk_smul` instead.

The data-carrying instances are `local`: the `Algebra` and `Module` structures below are the
canonical ones but are deliberately not instances in Mathlib, and seating them globally would
put a second copy in the path of every file that builds its own.

## References

* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

universe u

noncomputable section

namespace AlgebraicGeometry

/-- The structure sheaf of `Spec A`, read as a sheaf of commutative rings on the site of open
subsets of `Spec A`. This is the shape in which the tensor product of sheaves of modules, and
hence K-flatness, is stated. -/
def specCommRingSheaf (A : CommRingCat.{u}) :
    CategoryTheory.Sheaf.{u, u, u, u + 1}
      (Opens.grothendieckTopology (Spec.topObj A)) CommRingCat.{u} :=
  (Spec A).sheaf

/-- `specCommRingSheaf A` is the structure sheaf of `Spec A`: the passage between the site
spelling and `TopCat.Sheaf` changes no data. -/
theorem specCommRingSheaf_eq (A : CommRingCat.{u}) :
    specCommRingSheaf A = (Spec A).sheaf :=
  rfl

/-- The category of sheaves of `𝒪_{Spec A}`-modules, in the spelling K-flatness is stated
for. -/
abbrev SpecModules (A : CommRingCat.{u}) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (specCommRingSheaf A))

variable {A : CommRingCat.{u}} (x : PrimeSpectrum (A : Type u))

/-- The stalk of the structure sheaf of `Spec A` at `x`, as the `RingCat`-valued stalk that
`AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its modules over. -/
abbrev specStructureStalk : RingCat.{u} :=
  TopCat.Presheaf.stalk (C := RingCat.{u})
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (specCommRingSheaf A)).obj x

/-- Taking the stalk at `x` of a sheaf of `𝒪_{Spec A}`-modules. -/
abbrev specStalkFunctor :
    SpecModules A ⥤ ModuleCat.{u} (↑(specStructureStalk x) : Type u) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (specCommRingSheaf A)) x

/-- The sheaf `M̃` of Mathlib's `AlgebraicGeometry.tilde`, read in `SpecModules A`. -/
abbrev tildeMod (M : ModuleCat.{u} A) : SpecModules A := AlgebraicGeometry.tilde M

/-- The structural ring map `A → 𝒪_{Spec A, x}` into the
`RingCat`-valued stalk: Mathlib's `StructureSheaf.toStalk` followed by the comparison of the
`RingCat`-valued and `CommRingCat`-valued stalks. -/
def toSpecStructureStalk : (A : Type u) →+* (↑(specStructureStalk x) : Type u) :=
  (SemilinearStalk.commStalkRingEquiv
      (Spec.structureSheaf (A : Type u)).obj x).symm.toRingHom.comp
    (StructureSheaf.toStalk (A : Type u) x).hom

/-- The `RingCat`-valued stalk of the structure sheaf of `Spec A` is a commutative ring. -/
@[instance_reducible]
def commRing_specStructureStalk : CommRing (↑(specStructureStalk x) : Type u) :=
  StacksDraft.StalkTensor.commRing_stalk_ringSheaf (specCommRingSheaf A) x

attribute [local instance] commRing_specStructureStalk

/-- `𝒪_{Spec A, x}` is an `A`-algebra through `toSpecStructureStalk`. -/
@[instance_reducible]
def algebra_specStructureStalk : Algebra (A : Type u) (↑(specStructureStalk x) : Type u) :=
  (toSpecStructureStalk x).toAlgebra

attribute [local instance] algebra_specStructureStalk

/-- The stalk of `M̃` at `x` is a module over the `RingCat`-valued stalk of the structure
sheaf. This is the structure `AlgebraicGeometry.SheafOfModules.stalkObj` carries, seated at the
spelling Mathlib's `tilde` API states its localization instance in. -/
@[instance_reducible]
def module_specStructureStalk_tildeStalk (M : ModuleCat.{u} A) :
    Module (↑(specStructureStalk x) : Type u)
      ((AlgebraicGeometry.tilde M).presheaf.stalk x : Type u) :=
  (AlgebraicGeometry.SheafOfModules.stalkObj
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (specCommRingSheaf A)) x
    (tildeMod M)).isModule

attribute [local instance] module_specStructureStalk_tildeStalk

/-- `module_specStructureStalk_tildeStalk` at the spelling the stalk functor produces. -/
@[instance_reducible]
def module_specStructureStalk_stalkObj (M : ModuleCat.{u} A) :
    Module (↑(specStructureStalk x) : Type u)
      (((specStalkFunctor x).obj (tildeMod M)) : Type u) :=
  ((specStalkFunctor x).obj (tildeMod M)).isModule

attribute [local instance] module_specStructureStalk_stalkObj

/-- The `CommRingCat`-valued stalk of the structure sheaf of `Spec A` is an `A`-algebra. -/
@[instance_reducible]
def algebra_commStructureStalk : Algebra (A : Type u)
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u})
      (Spec.structureSheaf (A : Type u)).obj x)) :=
  StructureSheaf.stalkAlgebra (A : Type u) x

attribute [local instance] algebra_commStructureStalk

/-- The stalk of `M̃` at `x` as a module over the `CommRingCat`-valued stalk of the structure
sheaf. -/
@[instance_reducible]
def module_commStructureStalk_tildeStalk (M : ModuleCat.{u} A) :
    Module (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u})
        (Spec.structureSheaf (A : Type u)).obj x))
      ((AlgebraicGeometry.tilde M).presheaf.stalk x : Type u) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (id (AlgebraicGeometry.tilde M).val : PresheafOfModules.{u}
      ((Spec.structureSheaf (A : Type u)).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) x

attribute [local instance] module_commStructureStalk_tildeStalk

/-- On the stalk of `M̃`, the action of `r : A` is the action of its image in the stalk ring.
The two actions of the two stalk rings agree through
`AlgebraicGeometry.SheafOfModules.commStalk_smul_eq`, and the `A`-action of
`StructureSheaf.toStalk r` is the `A`-action of `r` on the nose. -/
theorem toSpecStructureStalk_smul (M : ModuleCat.{u} A) (r : (A : Type u))
    (m : ((AlgebraicGeometry.tilde M).presheaf.stalk x : Type u)) :
    toSpecStructureStalk x r • m = r • m :=
  have h1 : (SemilinearStalk.commStalkRingEquiv (Spec.structureSheaf (A : Type u)).obj x)
      (toSpecStructureStalk x r) • m = toSpecStructureStalk x r • m :=
    AlgebraicGeometry.SheafOfModules.commStalk_smul_eq
      (Spec.structureSheaf (A : Type u)).obj x (AlgebraicGeometry.tilde M).val
      (toSpecStructureStalk x r) m
  have h2 : (SemilinearStalk.commStalkRingEquiv (Spec.structureSheaf (A : Type u)).obj x)
      (toSpecStructureStalk x r) = (StructureSheaf.toStalk (A : Type u) x).hom r :=
    RingEquiv.apply_symm_apply _ _
  h1.symm.trans ((congrArg (fun s => s • m) h2).trans rfl)

/-- `1` acts as the identity on the stalk of `M̃`. This is `one_smul`, which is not
synthesizable at the stalk-ring spelling, derived from `toSpecStructureStalk_smul` and
`RingHom.map_one`. -/
theorem one_smul_tildeStalk (M : ModuleCat.{u} A)
    (y : ((AlgebraicGeometry.tilde M).presheaf.stalk x : Type u)) :
    (1 : (↑(specStructureStalk x) : Type u)) • y = y :=
  (congrArg (fun s => s • y) (toSpecStructureStalk x).map_one.symm).trans
    ((toSpecStructureStalk_smul x M 1 y).trans (one_smul _ _))

/-- The `A`-action on the stalk of `M̃` is the restriction of the stalk-ring action. -/
instance isScalarTower_specStructureStalk (M : ModuleCat.{u} A) :
    IsScalarTower (A : Type u) (↑(specStructureStalk x) : Type u)
      ((AlgebraicGeometry.tilde M).presheaf.stalk x : Type u) :=
  IsScalarTower.of_algebraMap_smul (fun r m => toSpecStructureStalk_smul x M r m)

/-- The comparison of the `RingCat`-valued and `CommRingCat`-valued stalks of the structure
sheaf of `Spec A`, as an equivalence of `A`-algebras. -/
def specStalkAlgEquiv : (↑(specStructureStalk x) : Type u) ≃ₐ[(A : Type u)]
    ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u})
      (Spec.structureSheaf (A : Type u)).obj x) :=
  { SemilinearStalk.commStalkRingEquiv (Spec.structureSheaf (A : Type u)).obj x with
    commutes' := fun _ => RingEquiv.apply_symm_apply _ _ }

/-- The `RingCat`-valued stalk of the structure sheaf of `Spec A` at `x` is the localization of
`A` at the prime `x`. This is the content of Stacks 01HV at the stalk spelling the tensor
product of sheaves of modules uses; it is
`StructureSheaf.IsLocalization.to_stalk`, transported along `specStalkAlgEquiv`. -/
instance isLocalization_specStructureStalk :
    IsLocalization.AtPrime (↑(specStructureStalk x) : Type u) x.asIdeal :=
  haveI : IsLocalization.AtPrime (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u})
      (Spec.structureSheaf (A : Type u)).obj x)) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (A : Type u) x
  IsLocalization.isLocalization_of_algEquiv _ (specStalkAlgEquiv x).symm

/-- The stalk of `M̃` at `x` is the base change of `M` along the structural map
`A → 𝒪_{Spec A, x}`: the stalk is the localization of `M` at `x`
(`AlgebraicGeometry.tilde.toStalk`, Stacks 01HV) and the stalk ring is the localization of
`A`. -/
theorem isBaseChange_tilde_toStalk (M : ModuleCat.{u} A) :
    IsBaseChange (↑(specStructureStalk x) : Type u)
      (AlgebraicGeometry.tilde.toStalk M x).hom :=
  IsLocalizedModule.isBaseChange x.asIdeal.primeCompl (↑(specStructureStalk x) : Type u)
    (AlgebraicGeometry.tilde.toStalk M x).hom

/-- The stalk of `M̃` at `x` is `𝒪_{Spec A, x} ⊗_A M`, as modules over the stalk ring. -/
def tildeStalkIso (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars.{u, u, u} (toSpecStructureStalk x)).obj M ≅
      (specStalkFunctor x).obj (tildeMod M) :=
  (isBaseChange_tilde_toStalk x M).equiv.toModuleIso

/-- `tildeStalkIso` is the base-change equivalence of `isBaseChange_tilde_toStalk`. -/
theorem tildeStalkIso_hom_apply (M : ModuleCat.{u} A)
    (y : ((ModuleCat.extendScalars.{u, u, u} (toSpecStructureStalk x)).obj M : Type u)) :
    ((tildeStalkIso x M).hom).hom y = (isBaseChange_tilde_toStalk x M).equiv y :=
  rfl

/-- `tildeStalkIso` is natural in `M`: both composites send `1 ⊗ m` to the germ at `x` of the
image of `m`, by `AlgebraicGeometry.tilde.toStalk_map`. -/
theorem tildeStalkIso_naturality {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    (ModuleCat.extendScalars.{u, u, u} (toSpecStructureStalk x)).map g ≫
        (tildeStalkIso x N).hom =
      (tildeStalkIso x M).hom ≫
        (specStalkFunctor x).map ((AlgebraicGeometry.tilde.functor A).map g) := by
  have key (P : ModuleCat.{u} A) (m : P) :
      (tildeStalkIso x P).hom.hom ((1 : specStructureStalk x) ⊗ₜ[A] m) =
        (AlgebraicGeometry.tilde.toStalk P x).hom m :=
    ((tildeStalkIso_hom_apply x P _).trans
      ((isBaseChange_tilde_toStalk x P).equiv_tmul 1 m)).trans (one_smul_tildeStalk x P _)
  refine ModuleCat.ExtendScalars.hom_ext (fun m => (key N (g.hom m)).trans ?_)
  exact ((AlgebraicGeometry.tilde.toStalk_map g x
      ((AlgebraicGeometry.tilde.toStalk M x).hom m)).trans
    (IsLocalizedModule.map_apply x.asIdeal.primeCompl (AlgebraicGeometry.tilde.toStalk M x).hom
      (AlgebraicGeometry.tilde.toStalk N x).hom g.hom m)).symm.trans
    (congrArg (fun y => (ConcreteCategory.hom ((specStalkFunctor x).map
      ((AlgebraicGeometry.tilde.functor A).map g))) y) (key M m).symm)

section Complexes

/-- The tensor product of sheaves of `𝒪_{Spec A}`-modules is additive in its first variable. -/
instance specSheafTensor_additive (A : CommRingCat.{u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (specCommRingSheaf A)).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u} (specCommRingSheaf A)

/-- The tensor product of sheaves of `𝒪_{Spec A}`-modules is additive in its second
variable. -/
instance specSheafTensor_obj_additive (A : CommRingCat.{u}) (M : SpecModules A) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (specCommRingSheaf A)).obj
      M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u} (specCommRingSheaf A) M

/-- The total tensor complex of two complexes of sheaves of `𝒪_{Spec A}`-modules exists. -/
instance hasMapBifunctor_specSheafTensor (A : CommRingCat.{u})
    (K₁ K₂ : CochainComplex (SpecModules A) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (specCommRingSheaf A))
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, u, u} (specCommRingSheaf A) K₁ K₂

/-- The complex `K̃` of sheaves of `𝒪_{Spec A}`-modules associated degreewise to a complex `K`
of `A`-modules, read in `SpecModules A`. -/
abbrev tildeComplexMod (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (SpecModules A) ℤ :=
  Stacks.AffineTilde.tildeComplex K

/-- The stalk complex of `K̃` at `x` is the base change of `K` along `A → 𝒪_{Spec A, x}`. It is
`tildeStalkIso` in each degree; the differentials match by `tildeStalkIso_naturality`. -/
def tildeStalkComplexIso (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (CochainComplex.extendScalarsLarge.{u, u, u} (toSpecStructureStalk x)).obj K ≅
      AlgebraicGeometry.SheafOfModules.stalkComplex (specCommRingSheaf A) x
        (tildeComplexMod K) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => tildeStalkIso x (K.X n))
    (fun i j _ => (tildeStalkIso_naturality x (K.d i j)).symm)

/-- **Stacks Project, Tag 08DV.** If `K` is a K-flat complex of `A`-modules, then `K̃` is a
K-flat complex of `𝒪_{Spec A}`-modules.

By the stalk criterion for K-flatness (Stacks 06YB) it suffices that the stalk complex of `K̃`
at every point `x` be K-flat over the stalk ring. That stalk complex is the extension of
scalars of `K` along `A → 𝒪_{Spec A, x}` (`tildeStalkComplexIso`), and extension of scalars
preserves K-flatness (Stacks 06Y1). -/
@[stacks 08DV]
theorem kFlat_tilde (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) :
    Stacks.SheafOfModules.IsKFlat (specCommRingSheaf A) (tildeComplexMod K) := by
  refine (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise
    (specCommRingSheaf A) (tildeComplexMod K)).2 fun y => ?_
  exact CochainComplex.KFlat.of_iso (tildeStalkComplexIso y K)
    (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars (toSpecStructureStalk y) K hK)

end Complexes

end AlgebraicGeometry

end

end
