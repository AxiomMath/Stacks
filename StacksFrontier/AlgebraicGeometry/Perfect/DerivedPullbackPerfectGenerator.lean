module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundedBelowGenerator
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceModulesAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace

/-!
# The derived pullback of a perfect generator along an affine morphism

Let `f : Y ⟶ X` be a morphism of schemes and let `G` be a perfect object of `D(𝒪_X)`. The derived
pullback `Lf^*G` is a perfect object of `D(𝒪_Y)`, perfectness being read at the ringed site of
opens. If `f` is affine and `G` generates `D_QCoh(𝒪_X)`, then `Lf^*G` generates `D_QCoh(𝒪_Y)`:
this is the case "`f` affine" of Stacks 0BQT, implication (1) ⇒ (3), with condition (1) supplied
by Stacks 08I8 in the form that the derived direct image along an affine morphism detects
vanishing of cohomology on `D_QCoh`.

## Main results

* `AlgebraicGeometry.isPerfect_ringedSite_derivedPullback`: `Lf^*G` is perfect.
* `AlgebraicGeometry.isZero_of_forall_shift_derivedPullback_hom_eq_zero`: `Lf^*G` generates
  `D_QCoh(𝒪_Y)` when `f` is affine and `G` generates `D_QCoh(𝒪_X)`.

## Implementation notes

Generation is stated in the shape the perfect-generator criteria of
`StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundedBelowGenerator` take it: an object `L` of
`D_QCoh` receiving only zero morphisms from all shifts of the generator is zero. The proof is the
source's: by the adjunction `Lf^* ⊣ Rf_*` the hypothesis on `L` is the same hypothesis on
`Rf_*L`, which lies in `D_QCoh(𝒪_X)` because `H^i(Rf_*L) = f_*H^i(L)` for `f` affine; so
`Rf_*L = 0`, and then every `H^i(L)` vanishes, `f_*` detecting vanishing on quasi-coherent
modules.

## References

* [Stacks Project, Remark 36.38.6 (Tag 0BQT)](https://stacks.math.columbia.edu/tag/0BQT)
* [Stacks Project, Lemma 36.5.4 (Tag 08I8)](https://stacks.math.columbia.edu/tag/08I8)
* [Stacks Project, Lemma 20.46.4 (Tag 09UA)](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
  Stacks.AssociatedSheaf.abelianModulesRingSheaf

/-- **The derived pullback of a perfect object is perfect**, perfectness of objects of the
derived categories of the two schemes being read at their ringed sites of opens. This is Stacks
09UA, transported along the equivalence of the ringed-space and the ringed-site notions of
perfectness. -/
theorem isPerfect_ringedSite_derivedPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G) :
    (ringedSite Y.sheaf).IsPerfect ((derivedPullback f.toLRSHom.toShHom).obj G) :=
  Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect Y.toRingedSpace _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback f.toLRSHom.toShHom G
      (Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace G hG))

/-- **The derived pullback of a generator along an affine morphism is a generator.** Let
`f : Y ⟶ X` be an affine morphism of schemes and let `G` be an object of `D(𝒪_X)` generating
`D_QCoh(𝒪_X)`, in the sense that an object of `D_QCoh(𝒪_X)` receiving only zero morphisms from
the shifts of `G` is zero. Then `Lf^*G` generates `D_QCoh(𝒪_Y)` in the same sense.

This is the case of an affine morphism of Stacks 0BQT, implication (1) ⇒ (3). -/
theorem isZero_of_forall_shift_derivedPullback_hom_eq_zero {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] (G : DerivedCategory (StructureSheafModules X.sheaf))
    (hgen : ∀ L : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj L).IsQuasicoherent) →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ L), g = 0) → IsZero L)
    (L : DerivedCategory (StructureSheafModules Y.sheaf))
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules Y.sheaf) i).obj L).IsQuasicoherent)
    (h : ∀ (n : ℤ) (g : (shiftFunctor (DerivedCategory (StructureSheafModules Y.sheaf)) n).obj
      ((derivedPullback f.toLRSHom.toShHom).obj G) ⟶ L), g = 0) :
    IsZero L := by
  have hpush : IsZero ((derivedPushforward f.toLRSHom.toShHom).obj L) := by
    refine hgen _ (fun i => ?_) (fun n g => ?_)
    · exact ObjectProperty.prop_of_iso
        (P := fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsQuasicoherent)
        (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.homologyDerivedPushforwardIso
          f L hL i).symm
        (ProperCoherentFiniteType.isQuasicoherent_pushforward f _ (hL i))
    · let e := ((derivedAdjunction f.toLRSHom.toShHom).homEquiv _ _).symm.trans
        ((((derivedPullback f.toLRSHom.toShHom).commShiftIso n).app G).homCongr (Iso.refl L))
      exact e.injective ((h n (e g)).trans (h n (e 0)).symm)
  refine (DerivedCategory.isZero_iff_forall_isZero_homology L).2 fun i => ?_
  open Stacks.AlgebraicGeometry.AffinePushforwardTExactness in
  exact isZero_homology_of_isZero_homology_derivedPushforward f L hL
    ((DerivedCategory.homologyFunctor _ i).map_isZero hpush)

end AlgebraicGeometry

end
