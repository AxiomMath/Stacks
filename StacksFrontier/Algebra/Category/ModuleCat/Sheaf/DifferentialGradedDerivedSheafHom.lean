module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorHom
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardSheafHomExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRightDerivedExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedSumsProducts
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFactorization
public import StacksFrontier.CategoryTheory.Functor.Derived.Absolute
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived internal hom of sheaves of differential graded modules

Let `(C, O)` be a ringed site, let `𝒜` and `ℬ` be sheaves of differential graded `O`-algebras and
let `𝒩` be a differential graded `(𝒜, ℬ)`-bimodule. The derived internal hom

`RSheafHom_ℬ(𝒩, -) : D(ℬ, d) ⥤ D(𝒜, d)`

is the right derived extension of the internal hom functor `SheafHom^dg_ℬ(𝒩, -)` of homotopy
categories ([Stacks, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP) (1)), and it is right
adjoint to the derived tensor product `- ⊗^𝐋_𝒜 𝒩 : D(𝒜, d) ⥤ D(ℬ, d)` of [Stacks, Tag 0FTG]
([Stacks, Tag 0FTQ](https://stacks.math.columbia.edu/tag/0FTQ)).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyTensorProductSheafHomAdjunction`: the
  adjunction `K(- ⊗_𝒜 𝒩) ⊣ K(SheafHom^dg_ℬ(𝒩, -))` of homotopy categories (Tag 0FRS), with the
  tensor product functor the one the derived tensor product is derived from.
* `SheafOfModules.DifferentialGradedModule.derivedSheafHom`: **the derived internal hom
  `RSheafHom_ℬ(𝒩, -)`.**
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductSheafHomAdjunction`: **the
  adjunction `- ⊗^𝐋_𝒜 𝒩 ⊣ RSheafHom_ℬ(𝒩, -)`.**

## Implementation notes

The source deduces Tag 0FTQ from the underived adjunction (Tag 0FRS) and the derivation of
adjunctions (Derived Categories, Tag 0FND). The latter is Mathlib's
`CategoryTheory.Adjunction.derived`, which asks the two derived functors to be *absolute*: the
composite `RSheafHom_ℬ(𝒩, -) ∘ (- ⊗^𝐋_𝒜 𝒩)` must still be a left derived functor and the composite
`(- ⊗^𝐋_𝒜 𝒩) ∘ RSheafHom_ℬ(𝒩, -)` still a right derived functor. Both hold because each of the
two is computed on a resolving class: the derived tensor product on flat and K-flat modules
(`LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions`), the derived internal
hom on graded injective K-injective ones, into which the localization is bijective on morphisms
(`Functor.isRightDerivedFunctor_comp_of_coresolutions`).

The sites, the algebras, the bimodule and the modules are taken in one universe, which is where
the derived categories are localizations with a calculus of fractions and where the relative
tensor product is constructed.

## References

* [Stacks Project, Tag 0FTQ](https://stacks.math.columbia.edu/tag/0FTQ)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
* [Stacks Project, Tag 0FND](https://stacks.math.columbia.edu/tag/0FND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (N : DifferentialGradedBimodule.{u, u, u} A B)

/-- The internal hom functor `K(SheafHom^dg_ℬ(𝒩, -)) : K(Mod(ℬ, d)) ⥤ K(Mod(𝒜, d))` of homotopy
categories. -/
abbrev homotopySheafHom : HomotopyCategory.{u, u, u} B ⥤ HomotopyCategory.{u, u, u} A :=
  homotopySheafHomFunctor (sheafHomHomotopyExtension N)

/-- The functor of homotopy categories from which the derived tensor product is derived is the
functor `K(- ⊗_𝒜 𝒩)` induced by the tensor product: along the identity of the ringed site a module
is its own pullback. -/
theorem pullbackTensor_tensorData_eq :
    HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N) =
      homotopyTensorFunctor (tensorData N) := by
  symm
  refine HomotopyCategory.eq_pullbackTensor _ _ _ ?_
  rw [homotopyTensorFunctor, HomotopyCategory.quotient_comp_descend, pullbackTensorFunctor,
    idPullbackData_functor_eq, Functor.id_comp]

/-- **The tensor-hom adjunction on homotopy categories** (Tag 0FRS): `K(- ⊗_𝒜 𝒩)` is left adjoint
to `K(SheafHom^dg_ℬ(𝒩, -))`, the tensor product functor being the one the derived tensor product
`- ⊗^𝐋_𝒜 𝒩` is derived from. -/
def homotopyTensorProductSheafHomAdjunction :
    HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N) ⊣
      homotopySheafHom N :=
  (homotopyTensorSheafHomAdjunction (tensorData N) (sheafHomHomotopyExtension N)).ofNatIsoLeft
    (eqToIso (pullbackTensor_tensorData_eq N).symm)

/-- **The derived internal hom** `RSheafHom_ℬ(𝒩, -) : D(ℬ, d) ⥤ D(𝒜, d)` of a differential graded
`(𝒜, ℬ)`-bimodule `𝒩` on a ringed site (Tag 0FTP (1)): the right derived extension of the internal
hom functor `ℳ ↦ SheafHom^dg_ℬ(𝒩, ℳ)` of homotopy categories followed by the localization
`K(Mod(𝒜, d)) ⥤ D(𝒜, d)` (Tag 0FTN). -/
def derivedSheafHom : derivedCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A :=
  rightDerivedExtension.{u, u, u} (homotopySheafHom N ⋙ toDerivedCategory.{u, u, u} A)

/-- The comparison `SheafHom^dg_ℬ(𝒩, ℳ) ⟶ RSheafHom_ℬ(𝒩, ℳ)` of the derived internal hom with the
internal hom, natural in the object of `K(Mod(ℬ, d))`. -/
def derivedSheafHomUnit :
    homotopySheafHom N ⋙ toDerivedCategory.{u, u, u} A ⟶
      toDerivedCategory.{u, u, u} B ⋙ derivedSheafHom N :=
  rightDerivedExtensionUnit.{u, u, u} (homotopySheafHom N ⋙ toDerivedCategory.{u, u, u} A)

/-- The derived internal hom, with its comparison map, is the right derived functor of the
internal hom followed by the localization. -/
instance isRightDerivedFunctor_derivedSheafHom :
    (derivedSheafHom N).IsRightDerivedFunctor (derivedSheafHomUnit N)
      (quasiIsomorphisms.{u, u, u} B) :=
  isRightDerivedFunctor_rightDerivedExtension.{u, u, u} _

/-- On a graded injective K-injective module the derived internal hom is the internal hom: the
comparison map is invertible there. -/
theorem isIso_derivedSheafHomUnit_app {I : DifferentialGradedModule.{u, u, u} B}
    (hI : IsDGInjective I) :
    IsIso ((derivedSheafHomUnit N).app ((HomotopyCategory.quotient B).obj I)) :=
  isIso_rightDerivedExtensionUnit_app.{u, u, u} _ hI

variable (B) in
/-- Every object of `K(Mod(ℬ, d))` has a quasi-isomorphism into an object into which the
localization is bijective on morphisms (Tag 0FT0). -/
theorem exists_quasiIso_bijective_toDerivedCategory_map (Z : HomotopyCategory.{u, u, u} B) :
    ∃ (I : HomotopyCategory.{u, u, u} B) (s : Z ⟶ I), quasiIsomorphisms.{u, u, u} B s ∧
      ∀ Y : HomotopyCategory.{u, u, u} B,
        Function.Bijective ((toDerivedCategory.{u, u, u} B).map : (Y ⟶ I) → _) := by
  obtain ⟨I, s, hs, hKI, hGI⟩ := exists_quasiIso_isDGInjective.{u, u, u} B Z
  exact ⟨I, s, hs, fun Y => bijective_toDerivedCategory_map
    (hasKInjectiveResolutions_dg.{u, u, u} B) Y hKI hGI⟩

/-- The absoluteness of the derived tensor product needed to derive the adjunction:
`RSheafHom_ℬ(𝒩, -) ∘ (- ⊗^𝐋_𝒜 𝒩)` is still a left derived functor, the derived tensor product being
computed on flat and K-flat modules. -/
instance isLeftDerivedFunctor_derivedTensorProduct_comp_derivedSheafHom :
    (derivedTensorProduct N ⋙ derivedSheafHom N).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedTensorProductCounit N) (derivedSheafHom N))
      (quasiIsomorphisms.{u, u, u} A) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions
    (quasiIsomorphisms.{u, u, u} A) (tensorGood (A := A)).objectProperty
    (tensorGood (A := A)).exists_objectProperty _
    (fun s hs hX hY => isIso_pullbackTensor_map_of_objectProperty idPullbackDataHomotopyExtension
      (tensorExactnessData N) s hs hX hY)
    (toDerivedCategory.{u, u, u} A) (derivedTensorProduct N) (derivedTensorProductCounit N)
    (derivedSheafHom N)

/-- The absoluteness of the derived internal hom needed to derive the adjunction:
`(- ⊗^𝐋_𝒜 𝒩) ∘ RSheafHom_ℬ(𝒩, -)` is still a right derived functor, the derived internal hom being
computed on graded injective K-injective modules. -/
instance isRightDerivedFunctor_derivedSheafHom_comp_derivedTensorProduct :
    (derivedSheafHom N ⋙ derivedTensorProduct N).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedSheafHomUnit N) (derivedTensorProduct N) ≫
        (Functor.associator _ _ _).hom)
      (quasiIsomorphisms.{u, u, u} B) :=
  Functor.isRightDerivedFunctor_comp_of_coresolutions (quasiIsomorphisms.{u, u, u} B)
    (derivedSheafHomUnit N) (derivedTensorProduct N)
    (exists_quasiIso_bijective_toDerivedCategory_map B)

/-- **Stacks 0FTQ**: let `(C, O)` be a ringed site, let `𝒜` and `ℬ` be sheaves of differential
graded `O`-algebras and let `𝒩` be a differential graded `(𝒜, ℬ)`-bimodule. Then the derived
internal hom `RSheafHom_ℬ(𝒩, -) : D(ℬ, d) ⥤ D(𝒜, d)` is right adjoint to the derived tensor
product `- ⊗^𝐋_𝒜 𝒩 : D(𝒜, d) ⥤ D(ℬ, d)`.

The adjunction is derived (Tag 0FND, `CategoryTheory.Adjunction.derived`) from the tensor-hom
adjunction of homotopy categories (Tag 0FRS). -/
@[stacks 0FTQ, sga "5 IIIB 5.2" "more general"]
def derivedTensorProductSheafHomAdjunction : derivedTensorProduct N ⊣ derivedSheafHom N :=
  (homotopyTensorProductSheafHomAdjunction N).derived (quasiIsomorphisms.{u, u, u} A)
    (quasiIsomorphisms.{u, u, u} B) (derivedTensorProductCounit N) (derivedSheafHomUnit N)

end SheafOfModules.DifferentialGradedModule

end
