module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirschBasis
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalkPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres
public import StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Residue
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.Perfect.Saturation
public import StacksFrontier.Homology.Perfect.DerivedReduction
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.StalkKoszulDescription

/-!
# Derived Nakayama for perfect objects on a scheme

Let `X` be a scheme and `F` a perfect object of `D(𝒪_X)`. If every derived fibre
`L i_x^* F`, `i_x : Spec κ(x) ⟶ X`, vanishes, then `F` is zero.

The proof is local on `X`. The derived stalk of `L i_x^* F` at the point of `Spec κ(x)` is the
derived base change `F_x ⊗^L_{𝒪_{X,x}} 𝒪_{Spec κ(x)}` of the derived stalk `F_x`
(`AlgebraicGeometry.derivedPullbackStalkIso`), along a local homomorphism of local rings. The
ring-level statement is then derived Nakayama over a local ring: if `φ : R → S` is a local
homomorphism and `K` is a pseudo-coherent object of `D(R)` with `K ⊗^L_R S = 0`, then
`K ⊗^L_R κ(R)` becomes zero after the field extension `κ(R) → κ(S)`, hence is zero, and a
pseudo-coherent object over a local ring with vanishing derived fibre is zero
(`AlgebraicGeometry.DeRhamLerayHirsch.isZero_of_forall_isZero_residueFibreHomology`). An object of
`D(𝒪_X)` all of whose derived stalks vanish is zero.

## Main results

* `StacksDraft.Perfect.isZero_of_isZero_totalDerivedExtensionScalars_of_field`: derived extension
  of scalars from a field to a nonzero ring reflects zero objects.
* `StacksDraft.Perfect.isZero_of_isZero_totalDerivedExtensionScalars_of_isLocalHom`: derived
  Nakayama over a local ring, along a local homomorphism.
* `AlgebraicGeometry.isZero_of_forall_isZero_derivedStalkFunctor`: an object of `D(𝒪_X)` with
  vanishing derived stalks is zero.
* `AlgebraicGeometry.isZero_derivedStalkFunctor_obj_of_isZero_derivedPullback`: the derived stalk
  of a perfect object vanishes where its derived fibre does.
* `AlgebraicGeometry.isZero_of_forall_isZero_derivedPullback_fromSpecResidueField`: derived
  Nakayama on a scheme.

## References

* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- **Derived extension of scalars to a nonzero algebra over a field reflects zero objects.** If
`ψ : k → L` is a homomorphism from a field to a nonzero ring and `M ∈ D(k)` becomes zero in `D(L)`,
then `M` is zero. -/
theorem isZero_of_isZero_totalDerivedExtensionScalars_of_field {k L : Type u} [Field k]
    [CommRing L] [Nontrivial L] (ψ : k →+* L) (M : DerivedCategory (ModuleCat.{u} k))
    (h : IsZero ((totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj M)) : IsZero M := by
  obtain ⟨P, hP, -, ⟨e⟩⟩ := exists_kFlat_representative.{u, u} M
  let D := totalDerivedExtensionScalars.{u, u, u} ψ
  let F := ModuleCat.extendScalars.{u, u, u} ψ
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  have hflat : ψ.Flat := by
    let := ψ.toAlgebra
    change Module.Flat k L
    infer_instance
  have : F.PreservesHomology := extendScalars_preservesHomology_of_flat.{u, u} ψ hflat
  have hQ : IsZero (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    h.of_iso (D.functor.mapIso e ≪≫ asIso (D.comparison.app P)).symm
  rw [DerivedCategory.isZero_iff_forall_isZero_homology] at hQ ⊢
  intro n
  have h₁ : IsZero (F.obj (P.homology n)) :=
    ((hQ n).of_iso ((DerivedCategory.homologyFunctorFactors _ n).app _).symm).of_iso
      ((P.sc n).mapHomologyIso F).symm
  have h₂ : IsZero (P.homology n) := by
    let := Module.compHom L ψ
    have hs : Subsingleton (TensorProduct k L (P.homology n)) :=
      ModuleCat.isZero_iff_subsingleton.mp h₁
    have : Module.Free k L := Module.Free.of_divisionRing k L
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ((Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k L).mp hs)
  exact h₂.of_iso (((DerivedCategory.homologyFunctor _ n).mapIso e) ≪≫
    (DerivedCategory.homologyFunctorFactors _ n).app P)

/-- **Derived Nakayama over a local ring.** Let `φ : R → S` be a local homomorphism of local rings
and let `K` be a pseudo-coherent object of `D(R)`. If the derived base change `K ⊗_R^L S` is zero,
then `K` is zero. -/
theorem isZero_of_isZero_totalDerivedExtensionScalars_of_isLocalHom {R S : Type u} [CommRing R]
    [IsLocalRing R] [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : PseudoCoherence.IsPseudoCoherent K)
    (h : IsZero ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj K)) : IsZero K := by
  set res := IsLocalRing.residue R
  set ψ := IsLocalRing.ResidueField.map φ
  have hcomp : ψ.comp res = (IsLocalRing.residue S).comp φ := by
    ext x
    exact IsLocalRing.ResidueField.map_residue φ x
  have h₁ : IsZero ((totalDerivedExtensionScalars.{u, u, u}
      ((IsLocalRing.residue S).comp φ)).functor.obj K) :=
    (Functor.map_isZero _ h).of_iso
      ((totalDerivedExtensionScalarsComp.{u, u} φ (IsLocalRing.residue S)).app K).symm
  rw [← hcomp] at h₁
  have h₂ : IsZero ((totalDerivedExtensionScalars.{u, u, u} res).functor.obj K) :=
    isZero_of_isZero_totalDerivedExtensionScalars_of_field ψ _
      (h₁.of_iso ((totalDerivedExtensionScalarsComp.{u, u} res ψ).app K))
  exact AlgebraicGeometry.DeRhamLerayHirsch.isZero_of_forall_isZero_residueFibreHomology K hK
    fun i ↦ Functor.map_isZero _ h₂

end StacksDraft.Perfect

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **An object of `D(𝒪_X)` is zero as soon as all its derived stalks are.** -/
theorem isZero_of_forall_isZero_derivedStalkFunctor (F : DerivedCategory X.Modules)
    (h : ∀ x : X, IsZero ((derivedStalkFunctor x).obj F)) : IsZero F := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  refine isZero_of_forall_modulesStalk _ fun x ↦ ?_
  exact (Functor.map_isZero _ (h x)).of_iso
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryHomologyIso n).app
      F).symm

/-- **The derived stalk of a perfect object is pseudo-coherent** over the local ring. -/
theorem isPseudoCoherent_derivedStalkFunctor_obj (F : DerivedCategory X.Modules)
    (hF : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) F) (x : X) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedStalkFunctor x).obj F) :=
  StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _
    (isPerfect_derivedStalk_of_isPerfect x F hF)

/-- **Derived Nakayama at a point.** If the derived fibre `L i_x^* F` of a perfect object `F` of
`D(𝒪_X)` at a point `x` vanishes, then so does the derived stalk `F_x`. -/
theorem isZero_derivedStalkFunctor_obj_of_isZero_derivedPullback (F : DerivedCategory X.Modules)
    (hF : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) F) (x : X)
    (h : IsZero ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.fromSpecResidueField x).toLRSHom.toShHom).obj F)) :
    IsZero ((derivedStalkFunctor x).obj F) := by
  set f := X.fromSpecResidueField x
  set pt := IsLocalRing.closedPoint (X.residueField x)
  have hpt : f.base pt = x := X.fromSpecResidueField_apply x pt
  have : (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec (X.residueField x)) pt).Additive :=
    modulesStalkFunctor_additive (X := Spec (X.residueField x)) pt
  have : PreservesFiniteLimits
      (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec (X.residueField x)) pt) :=
    modulesStalkFunctor_preservesFiniteLimits (X := Spec (X.residueField x)) pt
  have : PreservesFiniteColimits
      (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec (X.residueField x)) pt) :=
    have := modulesStalkFunctor_preservesColimits (X := Spec (X.residueField x)) pt
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : IsLocalRing ((Spec (X.residueField x)).presheaf.stalk pt) :=
    (Spec (X.residueField x)).toLocallyRingedSpace.isLocalRing pt
  have : IsLocalHom (f.stalkMap pt).hom := f.prop pt
  have h₀ : IsZero ((derivedStalkFunctor pt).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).obj F)) :=
    Functor.map_isZero
      (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec (X.residueField x))
        pt).mapDerivedCategory h
  have h₁ := h₀.of_iso ((derivedPullbackStalkIso f pt).app F).symm
  have key : IsZero ((derivedStalkFunctor (f.base pt)).obj F) :=
    StacksDraft.Perfect.isZero_of_isZero_totalDerivedExtensionScalars_of_isLocalHom
      (f.stalkMap pt).hom _ (isPseudoCoherent_derivedStalkFunctor_obj F hF _) h₁
  exact hpt ▸ key

/-- **Derived Nakayama on a scheme.** A perfect object of `D(𝒪_X)` all of whose derived fibres
`L i_x^* F`, `i_x : Spec κ(x) ⟶ X`, vanish is zero. -/
theorem isZero_of_forall_isZero_derivedPullback_fromSpecResidueField
    (F : DerivedCategory X.Modules)
    (hF : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) F)
    (h : ∀ x : X, IsZero ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.fromSpecResidueField x).toLRSHom.toShHom).obj F)) : IsZero F :=
  isZero_of_forall_isZero_derivedStalkFunctor F fun x ↦
    isZero_derivedStalkFunctor_obj_of_isZero_derivedPullback F hF x (h x)

end AlgebraicGeometry

end
