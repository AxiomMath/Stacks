module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirschBasis
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.StalkKoszulDescription
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareCube
public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars
public import StacksFrontier.Homology.PseudoCoherent.Local
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.Perfect.Saturation

/-!
# Perfect complexes are detected by their derived fibres at the points

Let `Y` be a scheme and `C` a perfect object of `D(𝒪_Y)`. For a point `y` write
`i_y : Spec κ(y) ⟶ Y`. If the derived pullback `Li_y^* C` vanishes for every `y`, then `C` is
zero; consequently a morphism of perfect objects is an isomorphism as soon as its derived pullback
to every point is.

This is the step of the proof of [Stacks, Tag 0FMP] that turns the fibrewise hypothesis into the
global conclusion (More on Algebra, Lemma 0BCD, read through the derived fibres of
Derived Categories of Schemes, Lemmas 06Z0 and 08EB).

## Main results

* `AlgebraicGeometry.DerivedFibreDetection.isZero_homology_of_isZero_extendScalars_field`: derived
  extension of scalars along a homomorphism of fields reflects zero cohomology.
* `AlgebraicGeometry.DerivedFibreDetection.isZero_residueFibreHomology_of_isZero_derivedPullback`:
  if `Lf^* E` vanishes then the derived fibre of `E` at the image `f x` of any point has no
  cohomology.
* `AlgebraicGeometry.DerivedFibreDetection.isZero_of_forall_isZero_derivedPullback`: a perfect
  object whose derived pullback to every point vanishes is zero.
* `AlgebraicGeometry.DerivedFibreDetection.isIso_of_forall_isIso_derivedPullback`: a morphism
  between perfect objects is an isomorphism as soon as its derived pullback to every point is.

## Implementation notes

The derived stalk of `Lf^* E` at `x` is the derived base change of the derived stalk of `E` at
`f x` along the local homomorphism `φ = f^♯_x : 𝒪_{Y,f x} ⟶ 𝒪_{X,x}`
(`AlgebraicGeometry.derivedPullbackStalkIso`). Composing with the residue map of `𝒪_{X,x}` and
using `ρ_X ∘ φ = κ(φ) ∘ ρ_Y`, the vanishing of `Lf^* E` makes the derived base change of the
derived fibre `E_{f x} ⊗ᴸ κ(f x)` along the field homomorphism `κ(φ)` vanish, and a field
homomorphism is faithfully flat. The local Nakayama criterion
`AlgebraicGeometry.DeRhamLerayHirsch.isIso_of_forall_isZero_derivedFibreHomology` then concludes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open CochainComplex.DerivedExtensionScalars

universe u

namespace AlgebraicGeometry.DerivedFibreDetection

attribute [local instance 2000] HasDerivedCategory.standard

/-- Transport a zero object along a functor preserving zero morphisms and an isomorphism. -/
private theorem isZero_of_iso_map {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (G : C ⥤ D) [G.PreservesZeroMorphisms] {X : C} {Z : D} (h : IsZero X)
    (e : G.obj X ≅ Z) : IsZero Z :=
  (G.map_isZero h).of_iso e.symm

/-! ### Extension of scalars along a homomorphism of fields -/

section Field

variable {K L : Type u} [Field K] [Field L] (ψ : K →+* L)

/-- Extension of scalars along a homomorphism of fields kills no nonzero module. -/
theorem subsingleton_of_subsingleton_extendScalars (M : ModuleCat.{u} K)
    (h : Subsingleton ((ModuleCat.extendScalars.{u, u, u} ψ).obj M)) : Subsingleton M := by
  let := ψ.toAlgebra
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (R := K) (M := M)
    (Algebra.linearMap K L) ψ.injective
  have hsub : Subsingleton (TensorProduct K L M) := h
  exact ⟨fun a b => (TensorProduct.lid K M).symm.injective (hinj (Subsingleton.elim _ _))⟩

/-- **Derived extension of scalars along a homomorphism of fields reflects zero cohomology.** -/
theorem isZero_homology_of_isZero_extendScalars_field (F : DerivedCategory (ModuleCat.{u} K))
    (h : IsZero ((totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj F)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).obj F) := by
  let := ψ.toAlgebra
  have hflat : ψ.Flat := by
    change Module.Flat K L
    infer_instance
  have := StacksDraft.PseudoCoherence.preservesFiniteLimits_extendScalars_of_flat.{u, u, u} ψ hflat
  have hadd : (ModuleCat.extendScalars.{u, u, u} ψ).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} ψ); infer_instance)
  have h1 : IsZero ((ModuleCat.extendScalars.{u, u, u} ψ).mapDerivedCategory.obj F) :=
    h.of_iso ((RingTheory.TorIndependence.totalDerivedExtensionScalarsIsoMapDerivedCategory ψ
      (ModuleCat.extendScalars.{u, u, u} ψ) (Iso.refl _)).app F).symm
  have h2 : IsZero ((ModuleCat.extendScalars.{u, u, u} ψ).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).obj F)) :=
    isZero_of_iso_map (DerivedCategory.homologyFunctor (ModuleCat.{u} L) i) h1
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (ModuleCat.extendScalars.{u, u, u} ψ) i).app F)
  rw [ModuleCat.isZero_iff_subsingleton] at h2 ⊢
  exact subsingleton_of_subsingleton_extendScalars ψ _ h2

end Field

/-! ### The derived fibre at the image of a point -/

/-- **A vanishing derived pullback kills the derived fibre at the image of every point.** If
`Lf^* E = 0` for a morphism of schemes `f : X ⟶ Y`, then for every point `x` of `X` the derived
fibre `E_{f x} ⊗ᴸ κ(f x)` has no cohomology. -/
theorem isZero_residueFibreHomology_of_isZero_derivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory Y.Modules)
    (h : IsZero ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj E)) (x : X) (y : Y) (hxy : f x = y) (i : ℤ) :
    IsZero (DeRhamLerayHirsch.derivedFibreHomology E y i) := by
  subst hxy
  let φ := (f.stalkMap x).hom
  let D := (derivedStalkFunctor (f x)).obj E
  have h0 : IsZero ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj D) :=
    isZero_of_iso_map (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory h
      ((derivedPullbackStalkIso f x).app E)
  let ρX := IsLocalRing.residue (X.presheaf.stalk x)
  let ρY := IsLocalRing.residue (Y.presheaf.stalk (f x))
  let κφ := IsLocalRing.ResidueField.map φ
  have hcomm : ρX.comp φ = κφ.comp ρY := by
    ext r
    exact (IsLocalRing.ResidueField.map_residue φ r).symm
  have h1 : IsZero ((totalDerivedExtensionScalars.{u, u, u} (ρX.comp φ)).functor.obj D) :=
    isZero_of_iso_map _ h0 ((totalDerivedExtensionScalarsComp.{u, u} φ ρX).app D)
  rw [hcomm] at h1
  have h3 : IsZero ((totalDerivedExtensionScalars.{u, u, u} κφ).functor.obj
      ((totalDerivedExtensionScalars.{u, u, u} ρY).functor.obj D)) :=
    h1.of_iso ((totalDerivedExtensionScalarsComp.{u, u} ρY κφ).app D)
  exact isZero_homology_of_isZero_extendScalars_field κφ _ h3 i

/-! ### Detection -/

/-- **A perfect object whose derived pullback to every point vanishes is zero.** -/
theorem isZero_of_forall_isZero_derivedPullback {Y : Scheme.{u}} (C : DerivedCategory Y.Modules)
    (hC : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) C)
    (h : ∀ y : Y, IsZero ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (Y.fromSpecResidueField y).toLRSHom.toShHom).obj C)) :
    IsZero C := by
  let T := contractibleTriangle C
  have hT : T.invRotate ∈ distTriang (DerivedCategory Y.Modules) :=
    inv_rot_of_distTriang _ (contractible_distinguished C)
  have hiso := DeRhamLerayHirsch.isIso_of_forall_isZero_derivedFibreHomology hT
    (fun y => StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _
      (isPerfect_derivedStalk_of_isPerfect y C hC))
    (fun y i => isZero_residueFibreHomology_of_isZero_derivedPullback
      (Y.fromSpecResidueField y) C (h y)
      (IsLocalRing.closedPoint (Y.residueField y))
      y (Scheme.fromSpecResidueField_apply y _) i)
  have h0 : IsZero T.invRotate.obj₁ :=
    (Functor.map_isZero (shiftFunctor (DerivedCategory Y.Modules) (-1 : ℤ)) (isZero_zero _))
  exact h0.of_iso (asIso T.invRotate.mor₁).symm

/-- **A morphism of perfect objects is an isomorphism as soon as its derived pullback to every
point is.** -/
theorem isIso_of_forall_isIso_derivedPullback {Y : Scheme.{u}}
    {A B : DerivedCategory Y.Modules} (a : A ⟶ B)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) A)
    (hB : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) B)
    (h : ∀ y : Y, IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (Y.fromSpecResidueField y).toLRSHom.toShHom).map a)) :
    IsIso a := by
  obtain ⟨Z, b, c, hT⟩ := distinguished_cocone_triangle a
  have hZ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) Z :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
      (X := Y.toRingedSpace) _ hT hA hB
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  refine isZero_of_forall_isZero_derivedPullback Z hZ fun y => ?_
  let F := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (Y.fromSpecResidueField y).toLRSHom.toShHom
  exact (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished _ hT)).2 (h y)

end AlgebraicGeometry.DerivedFibreDetection

end
