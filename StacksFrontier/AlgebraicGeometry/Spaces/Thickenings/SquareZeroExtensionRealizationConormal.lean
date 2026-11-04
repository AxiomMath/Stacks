module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowerFactorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalMapOfSubspaceInclusions
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSquareZeroExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealizationOfCharts
public import StacksFrontier.Deformation.AlgebraExtension.InducedKernelMap

/-!
# The conormal module of a realization of a square-zero extension

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝒜` an extension of `f⁻¹𝒪_Y`-algebras of
`𝒪_X` by a quasi-coherent `𝒪_X`-module `ℳ` (the data of Stacks 05ZT). A realization of `𝒜` is a
first-order thickening `X ⊂ X'` with `i⁻¹𝒪_{X'} ≅ 𝒜` over `𝒪_X`. This file shows that the
conormal module `𝒞_{X/X'}` of the thickening, read on `X`, is `ℳ`: the identification
`i⁻¹𝒪_{X'} ≅ 𝒜` is an isomorphism of middle terms over `𝒪_X` between the extension
`0 → 𝒞_{X/X'} → i⁻¹𝒪_{X'} → 𝒪_X → 0` of the thickening
(`AlgebraicGeometry.Space.restrictedFirstOrderExtension`) and `𝒜`, so it induces an isomorphism
of the kernels. In the proof of [Stacks Project, Tag 0D3X] this is the step "the ideal of
`X₀ ⊂ X` is `f^*𝒞_{Y₀/Y}`" for the thickening built from a solution of the tower problem.

## Main definitions

* `AlgebraicGeometry.Space.EtaleSquareZeroExtension.Realization.closedSpaceIso`: `X ≅ X ⊂ X'`.
* `AlgebraicGeometry.Space.EtaleSquareZeroExtension.Realization.extensionIso`: `𝒜 ≅ i⁻¹𝒪_{X'}` as
  an isomorphism of middle terms.
* `AlgebraicGeometry.Space.EtaleSquareZeroExtension.Realization.kernelConormalIso`: `ℳ ≅ 𝒞_{X/X'}`.

## Main results

* `Deformation.AlgebraExtension.isIso_inducedKernelMap`: an isomorphism of middle terms over `𝒪`
  induces an isomorphism of the kernels.
* `AlgebraicGeometry.Space.isIso_of_isIso_etaleRestrictionModule_map`: restriction of modules
  along an isomorphism of algebraic spaces reflects isomorphisms.
* `Space.isIso_conormalMapOfImmersions_of_isIso_modulePullback_map_idealSheafMap`: the conormal map
  of a square of closed subspaces is invertible once the map of defining ideals is, pulled back to
  the closed subspace and read on a space isomorphic to it.
* `AlgebraicGeometry.Space.EtaleSquareZeroExtension.Realization.algebraMap_comp_extensionIso_hom`:
  the algebra map of `𝒜`, read in `i⁻¹𝒪_{X'}`, is the inverse image of `h^♯`.
* `AlgebraicGeometry.Space.EtaleSquareZeroExtension.Realization.incl_kernelConormalIso_hom`: the
  isomorphism `ℳ ≅ 𝒞_{X/X'}` is the one through `𝒜 ≅ i⁻¹𝒪_{X'}` on the kernels.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Deformation.AlgebraExtension

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A A' O : Sheaf J CommRingCat.{u}} {a : A ⟶ O} {a' : A' ⟶ O}
  {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

/-- **An isomorphism of middle terms over `𝒪` induces an isomorphism of the kernels.** The induced
map is injective because `h` and the inclusion of `ℳ` are, and surjective because `h⁻¹` carries
the image of a section of `𝒩` into the kernel of the reduction of `P`. -/
theorem isIso_inducedKernelMap (P : AlgebraExtension a M) (Q : AlgebraExtension a' N)
    (h : P.extension ⟶ Q.extension) [IsIso h] (hh : h ≫ Q.reduction = P.reduction) :
    IsIso (inducedKernelMap P Q h hh) := by
  refine Stacks.SheafOfModules.isIso_of_bijective_val_app _ fun U =>
    ⟨fun m n hmn => ?_, fun n => ?_⟩
  · have hl : ∀ x, (inv h).hom.app U (h.hom.app U x) = x := fun x =>
      congrArg (fun k : P.extension ⟶ P.extension => k.hom.app U x) (IsIso.hom_inv_id h)
    refine P.incl_injective ?_
    rw [← hl (P.incl m), ← hl (P.incl n), hom_incl P Q h hh m, hom_incl P Q h hh n]
    exact congrArg (fun k => (inv h).hom.app U (Q.incl k)) hmn
  · have hr : ∀ y, h.hom.app U ((inv h).hom.app U y) = y := fun y =>
      congrArg (fun k : Q.extension ⟶ Q.extension => k.hom.app U y) (IsIso.inv_hom_id h)
    have hx : P.reduction.hom.app U ((inv h).hom.app U (Q.incl n)) = 0 := by
      rw [← congrArg (fun k : P.extension ⟶ O => k.hom.app U ((inv h).hom.app U (Q.incl n))) hh]
      exact (congrArg (Q.reduction.hom.app U) (hr (Q.incl n))).trans (Q.reduction_incl n)
    obtain ⟨m, hm⟩ := P.exists_incl _ hx
    refine ⟨m, Q.incl_injective ?_⟩
    rw [← hom_incl P Q h hh m, hm]
    exact hr _

/-- **The isomorphism of kernels induced by an isomorphism of middle terms over `𝒪`.** -/
def inducedKernelIso (P : AlgebraExtension a M) (Q : AlgebraExtension a' N)
    (h : P.extension ≅ Q.extension) (hh : h.hom ≫ Q.reduction = P.reduction) : M ≅ N :=
  haveI := isIso_inducedKernelMap P Q h.hom hh
  asIso (inducedKernelMap P Q h.hom hh)

/-- The forward map of `inducedKernelIso P Q h hh` is `inducedKernelMap P Q h.hom hh`. -/
theorem inducedKernelIso_hom (P : AlgebraExtension a M) (Q : AlgebraExtension a' N)
    (h : P.extension ≅ Q.extension) (hh : h.hom ≫ Q.reduction = P.reduction) :
    (inducedKernelIso P Q h hh).hom = inducedKernelMap P Q h.hom hh :=
  rfl

end Deformation.AlgebraExtension

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Inverse image of modules along an isomorphism reflects isomorphisms**: `e⁻¹^*e^* ≅
(e⁻¹ ≫ e)^* = 𝟙^* ≅ 𝟭` (Stacks 03LU). -/
theorem isIso_of_isIso_modulePullback_map {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (φ : M ⟶ N)
    [IsIso ((modulePullback B S hS e.hom).map φ)] : IsIso φ := by
  have h : IsIso ((modulePullback B S hS e.hom ⋙ modulePullback B S hS e.inv).map φ) :=
    inferInstanceAs (IsIso ((modulePullback B S hS e.inv).map
      ((modulePullback B S hS e.hom).map φ)))
  exact (NatIso.isIso_map_iff (modulePullbackCompIso B S hS e.inv e.hom ≪≫
    eqToIso (congrArg (modulePullback B S hS) e.inv_hom_id) ≪≫ modulePullbackIdIso B S hS Y)
    φ).1 h

/-- **Restriction of modules along an isomorphism of algebraic spaces reflects isomorphisms**:
it is the inverse image (Stacks 03LW). -/
theorem isIso_of_isIso_etaleRestrictionModule_map {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (φ : M ⟶ N)
    (h : IsIso ((etaleRestrictionModule B S hS e.hom (isEtale_hom_of_iso B S hS e)).map φ)) :
    IsIso φ := by
  have := (NatIso.isIso_map_iff (modulePullbackIsoEtaleRestrictionModule B S hS e.hom
    (isEtale_hom_of_iso B S hS e)) φ).2 h
  exact isIso_of_isIso_modulePullback_map B S hS e φ

/-- **The conormal map of a square of closed subspaces is invertible once the map of defining
ideals is, pulled back to `Z` and read on a space `A ≅ Z`**: by
`AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isIso_map_idealSheafMap`, and since
inverse image along `A ≅ Z` reflects isomorphisms. -/
theorem isIso_conormalMapOfImmersions_of_isIso_modulePullback_map_idealSheafMap
    {X X' A : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (ρ : A ≅ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (h : IsIso ((modulePullback B S hS ρ.hom).map
      ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map
        (idealSheafMap B S hS Z Z' g f hsq)))) :
    IsIso (conormalMapOfImmersions B S hS (subspaceInclusion B S hS X Z)
      (subspaceInclusion B S hS X' Z') f g (isImmersion_subspaceInclusion B S hS X Z)
      (isImmersion_subspaceInclusion B S hS X' Z') hsq) :=
  isIso_conormalMapOfImmersions_of_isIso_map_idealSheafMap Z Z' g f hsq
    (isIso_of_isIso_modulePullback_map B S hS ρ _)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.EtaleSquareZeroExtension.Realization

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)}
  {P : Deformation.AlgebraExtension (J := SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f) M} {hM : M.IsQuasicoherentOnSite}
  (R : Realization (SquareZeroExtension.ofAlgebraExtension f P hM))

/-- The closed subspace `X ⊂ X'` of a realization. -/
abbrev closedSubspace : ClosedSubspaces B S hS R.ambient.1 :=
  ⟨R.closed, R.firstOrder.fst.1⟩

/-- **`X ≅ (X ⊂ X')`**, as algebraic spaces. -/
abbrev closedSpaceIso :
    X ≅ (⟨R.closedSubspace.1.toFunctor, R.closedSubspace.2.1⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.isoMk _ R.closedIso

/-- The inclusion `i : X ⟶ X'` of a realization is `X ≅ (X ⊂ X') ⊆ X'`. -/
theorem immersion_eq_closedSpaceIso_hom_comp :
    R.immersion = R.closedSpaceIso.hom ≫ subspaceInclusion B S hS R.ambient R.closedSubspace :=
  ObjectProperty.hom_ext _ R.immersion_eq

/-- **`𝒜 ≅ i⁻¹𝒪_{X'}`**, the inverse of the identification of a realization, read in the middle
term of the extension of the first-order thickening `X ⊂ X'` restricted to `X`. -/
def extensionIso :
    P.extension ≅ (restrictedFirstOrderExtension B S hS R.closedSubspace R.firstOrder
      R.closedSpaceIso R.toBase).extension :=
  R.sheafIso.symm ≪≫ eqToIso (congrArg (inverseImageStructureSheaf B S hS)
      R.immersion_eq_closedSpaceIso_hom_comp) ≪≫
    restrictedFirstOrderExtensionIso B S hS R.closedSubspace R.firstOrder R.closedSpaceIso
      R.toBase

/-- `𝒜 ≅ i⁻¹𝒪_{X'}` is over `𝒪_X`. -/
theorem extensionIso_hom_comp_reduction :
    R.extensionIso.hom ≫ (restrictedFirstOrderExtension B S hS R.closedSubspace R.firstOrder
      R.closedSpaceIso R.toBase).reduction = P.reduction := by
  have h1 := restrictedFirstOrderExtensionIso_hom_comp_reduction B S hS R.closedSubspace
    R.firstOrder R.closedSpaceIso R.toBase
  have h2 := structureSharpInverseImage_eqToHom B S hS R.immersion_eq_closedSpaceIso_hom_comp
  have h3 : R.sheafIso.inv ≫ structureSharpInverseImage B S hS R.immersion = P.reduction :=
    (Iso.inv_comp_eq _).2 R.quotient_compatibility.symm
  exact (Category.assoc _ _ _).trans ((congrArg (R.sheafIso.inv ≫ ·)
    ((Category.assoc _ _ _).trans ((congrArg (eqToHom _ ≫ ·) h1).trans h2))).trans h3)

/-- **The algebra structure of `𝒜`, read in `i⁻¹𝒪_{X'}`, is the inverse image of `h^♯`**: the
algebra map `f⁻¹𝒪_Y ⟶ 𝒜` followed by `𝒜 ≅ i⁻¹𝒪_{X'}` is `f⁻¹𝒪_Y = (i ≫ h)⁻¹𝒪_Y ≅ i⁻¹h⁻¹𝒪_Y`
(Stacks 03G8) followed by `i⁻¹(h^♯)`, read in the middle term of the restricted thickening. -/
theorem algebraMap_comp_extensionIso_hom :
    P.algebraMap ≫ R.extensionIso.hom =
      eqToHom (congrArg (fun φ ↦ (smallEtaleRingedToposHom B S hS φ).toToposHom.inverseImageRing.obj
          (smallEtaleRingedTopos B S hS Y).O) R.over_base.symm) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS R.immersion R.toBase).inv.app
            (smallEtaleRingedTopos B S hS Y).O ≫
        (smallEtaleInverseImageRing B S hS R.immersion).map
          (smallEtaleRingedToposHom B S hS R.toBase).fSharpInverseImage ≫
        eqToHom (congrArg (inverseImageStructureSheaf B S hS)
          R.immersion_eq_closedSpaceIso_hom_comp) ≫
        (restrictedFirstOrderExtensionIso B S hS R.closedSubspace R.firstOrder R.closedSpaceIso
          R.toBase).hom := by
  have key : ∀ {C : Type _} [Category.{_} C] {W X₁ X₂ X₃ A X₄ Z : C} (a : W ⟶ X₁)
      (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (σ : X₃ ≅ A) (τ : X₃ ≅ X₄) (ι : X₄ ≅ Z),
      (a ≫ b ≫ c ≫ σ.hom) ≫ (σ.symm ≪≫ τ ≪≫ ι).hom = a ≫ b ≫ c ≫ τ.hom ≫ ι.hom := by
    intros; simp
  exact (congrArg (· ≫ R.extensionIso.hom) R.algebra_compatibility).trans (key _ _ _ _ _ _)

/-- **The conormal module of a realization is the ideal of the extension**: `ℳ ≅ 𝒞_{X/X'}`, read
on `X`, induced on the kernels by `𝒜 ≅ i⁻¹𝒪_{X'}`. -/
def kernelConormalIso : M ≅ restrictedConormalModule B S hS R.closedSubspace R.closedSpaceIso :=
  Deformation.AlgebraExtension.inducedKernelIso.{u, u + 1, u} P
    (restrictedFirstOrderExtension B S hS R.closedSubspace R.firstOrder R.closedSpaceIso R.toBase)
    R.extensionIso R.extensionIso_hom_comp_reduction

/-- The isomorphism `ℳ ≅ 𝒞_{X/X'}` is the one through `𝒜 ≅ i⁻¹𝒪_{X'}` on the kernels. -/
theorem incl_kernelConormalIso_hom {U : (SmallEtale B S hS X.1)ᵒᵖ} (m : M.val.obj U) :
    (restrictedFirstOrderExtension B S hS R.closedSubspace R.firstOrder R.closedSpaceIso
      R.toBase).incl ((R.kernelConormalIso).hom.val.app U m) =
      R.extensionIso.hom.hom.app U (P.incl m) :=
  (Deformation.AlgebraExtension.hom_incl.{u, u + 1, u} P
    (restrictedFirstOrderExtension B S hS R.closedSubspace R.firstOrder R.closedSpaceIso R.toBase)
    R.extensionIso.hom R.extensionIso_hom_comp_reduction m).symm

end AlgebraicGeometry.Space.EtaleSquareZeroExtension.Realization

end
