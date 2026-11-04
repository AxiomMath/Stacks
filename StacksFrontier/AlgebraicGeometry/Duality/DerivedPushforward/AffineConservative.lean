module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# Derived direct image along an affine morphism is conservative on `D_QCoh`

Let `g : W ⟶ Y` be an affine morphism of schemes. On complexes with quasi-coherent cohomology,
`H^i(Rg_*E) = 0` exactly when `H^i(E) = 0`; consequently a morphism of `D_QCoh(𝒪_W)` is
invertible as soon as its derived direct image is. The statements are at the locally small model
of `D(𝒪_W)`, transported from the standard one along
`StacksDraft.DerivedModel.derivedPushforwardModelIso`.

## Main results

* `Stacks.Duality.homologyFunctorModelIso` — cohomology sheaves are the same at the two models.
* `Stacks.Duality.isZero_homology_of_isZero_homology_derivedPushforward_of_isAffineHom`.
* `Stacks.Duality.isIso_of_isIso_derivedPushforward_map_of_isAffineHom` — conservativity.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality

section Model

variable (C : Type (u + 1)) [Category.{u} C] [Abelian C] [IsGrothendieckAbelian.{u} C]

/-- **The cohomology functors of the two models agree** along the comparison equivalence: both
lift the cohomology of complexes along the localization, and the comparison matches the two
localization functors on the nose. -/
def homologyFunctorModelIso (n : ℤ) :
    (Stacks.Injectives.grothendieckModelEquiv.{u} C).functor ⋙
        @DerivedCategory.homologyFunctor C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C) n ≅
      @DerivedCategory.homologyFunctor C _ _ (HasDerivedCategory.standard C) n :=
  letI : Localization.Lifting (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      ((Stacks.Injectives.grothendieckModelEquiv.{u} C).functor ⋙
        @DerivedCategory.homologyFunctor C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C) n) :=
    ⟨@DerivedCategory.homologyFunctorFactors C _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C) n⟩
  letI : Localization.Lifting (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      (@DerivedCategory.homologyFunctor C _ _ (HasDerivedCategory.standard C) n) :=
    ⟨@DerivedCategory.homologyFunctorFactors C _ _ (HasDerivedCategory.standard C) n⟩
  Localization.liftNatIso (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) _ _ (Iso.refl _)

end Model

section Affine

variable {W Y : Scheme.{u}} (g : W ⟶ Y) [IsAffineHom g]

/-- **A degree in which `Rg_*E` has no cohomology is one in which `E` has none**, for `g` affine
and `E` with quasi-coherent cohomology, at the locally small model. -/
theorem isZero_homology_of_isZero_homology_derivedPushforward_of_isAffineHom
    (E : DerivedCategory W.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W.Modules i).obj E).IsQuasicoherent)
    (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward g).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj E) := by
  let CW := SheafOfModules.{u} (_root_.structureSheafRing W.toRingedSpace)
  let CY := SheafOfModules.{u} (_root_.structureSheafRing Y.toRingedSpace)
  let E' : @DerivedCategory CW _ _ (HasDerivedCategory.standard CW) := E
  have e₁ := (homologyFunctorModelIso CW i).app E'
  have e₂ := (StacksDraft.DerivedModel.derivedPushforwardModelIso g.toLRSHom.toShHom).app E'
  have e₃ := (homologyFunctorModelIso CY i).app
    (@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward _ _ g.toLRSHom.toShHom
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) |>.obj E')
  show IsZero (((Stacks.Injectives.grothendieckModelEquiv.{u} CW).functor ⋙
    @DerivedCategory.homologyFunctor CW _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} CW) i).obj E')
  refine IsZero.of_iso ?_ e₁
  open Stacks.AlgebraicGeometry.AffinePushforwardTExactness in
  refine isZero_homology_of_isZero_homology_derivedPushforward
    g E' (fun j => (SheafOfModules.isQuasicoherent (_root_.structureSheafRing W.toRingedSpace)
      ).prop_of_iso ((homologyFunctorModelIso CW j).app E') (hE j)) ?_
  change IsZero (@DerivedCategory.homologyFunctor CY _ _
    (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} CY) i |>.obj
      (((Stacks.Injectives.grothendieckModelEquiv.{u} CW).functor ⋙
        @Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward _ _
          g.toLRSHom.toShHom
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} CW)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} CY)).obj E')) at h
  exact IsZero.of_iso h (e₃.symm ≪≫
    (@DerivedCategory.homologyFunctor CY _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} CY) i).mapIso e₂)

/-- **Derived direct image along an affine morphism reflects isomorphisms of `D_QCoh`**, at the
locally small model: if `Rg_*φ` is invertible then so is `φ`. -/
theorem isIso_of_isIso_derivedPushforward_map_of_isAffineHom
    {E F : quasiCoherentDerivedCategory W} (φ : E ⟶ F)
    [IsIso ((derivedPushforward g).map φ.hom)] : IsIso φ := by
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle φ.hom
  have hC : DerivedCategoryB.derivedCategoryB (A := W.Modules)
      (SheafOfModules.isQuasicoherent W.ringCatSheaf) C :=
    DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre W) _
      (rot_of_distTriang _ hT) F.property
      (DerivedCategoryB.derivedCategoryB_shift_mem _
        (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre W)
        1 E.property)
  have hT' := (derivedPushforward g).map_distinguished _ hT
  have hzero : IsZero ((derivedPushforward g).obj C) :=
    Triangle.isZero₃_of_isIso₁ _ hT' (inferInstanceAs (IsIso ((derivedPushforward g).map φ.hom)))
  have hCz : IsZero C := Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj C fun n =>
    isZero_homology_of_isZero_homology_derivedPushforward_of_isAffineHom g C hC n
      ((DerivedCategory.homologyFunctor Y.Modules n).map_isZero hzero)
  have : IsIso ((ObjectProperty.ι _).map φ) := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hCz
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map φ

end Affine

end Stacks.Duality
