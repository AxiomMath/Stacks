module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitPerfectObjects
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Homology.Perfect.Colimit
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# Perfect objects along a directed limit of affine schemes

Let `i ↦ R_i` be a filtered system of commutative rings whose colimit `R` is computed on underlying
sets, so that `Spec R` is the limit of the affine schemes `Spec R_i`. Every perfect object of
`D(𝒪_{Spec R})` is then the derived pullback, along the projection `Spec R ⟶ Spec R_i` for some
stage `i`, of a perfect object of `D(𝒪_{Spec R_i})`. This is the affine base case of the
essential-surjectivity half of Stacks 09RF.

## Main results

* `AlgebraicGeometry.AffinePerfectLimit.exists_isPerfect_stage`: a perfect object over the colimit
  ring is, up to isomorphism, the derived pullback of a perfect object at some stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (isPerfect_derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe v u

namespace AlgebraicGeometry.AffinePerfectLimit

/-- **Stacks 09RF**, the affine base case of essential surjectivity. Let `i ↦ R_i` be a filtered
diagram of commutative rings whose colimit is computed on underlying sets, with colimit cocone `c`,
and write `R = c.pt`, so that `Spec R` is the limit of the affine schemes `Spec R_i`. Then every
perfect object `E` of `D(𝒪_{Spec R})` is, for some stage `i`, the derived pullback along
`Spec R ⟶ Spec R_i` of a perfect object of `D(𝒪_{Spec R_i})`. -/
@[stacks 09RF "essential surjectivity of the comparison out of the colimit, in the affine base \
case of the source's induction: for a filtered system of rings with colimit R, every perfect \
object of D(𝒪_{Spec R}) is derived pullback of a perfect object at a stage. The induction over \
the quasi-compact opens of S_0 that globalises it is not included, and neither is full \
faithfulness"]
theorem exists_isPerfect_stage {J : Type u} [Category.{u} J] [IsFiltered J]
    (A : J ⥤ CommRingCat.{u}) [PreservesColimit A (forget CommRingCat.{u})]
    (c : Cocone A) (hc : IsColimit c) (E : DerivedCategory (Spec c.pt).Modules)
    (hE : IsPerfect (X := (Spec c.pt).toRingedSpace) E) :
    ∃ (j : J) (Ej : DerivedCategory (Spec (A.obj j)).Modules),
      IsPerfect (X := (Spec (A.obj j)).toRingedSpace) Ej ∧
        Nonempty ((derivedPullback (Spec.map (c.ι.app j)).toLRSHom.toShHom).obj Ej ≅ E) := by
  have hqc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec c.pt).Modules n).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent (Spec c.pt) E
      (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect E hE)
  obtain ⟨M, ⟨eM⟩⟩ := StandardModel.exists_iso_mapDerivedCategory c.pt E hqc
  have hM : StacksDraft.Perfect.IsPerfect M :=
    (isPerfect_tilde_iff M).1
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
        (X := (Spec c.pt).toRingedSpace) (K := E)
        (L := (tilde.functor c.pt).mapDerivedCategory.obj M) eM.symm hE)
  obtain ⟨j, Mj, hMj, ⟨eMj⟩⟩ :=
    (StacksDraft.Perfect.perfectComplexes_filteredColimit A c hc).1 M hM
  refine ⟨j, (tilde.functor (A.obj j)).mapDerivedCategory.obj Mj,
    (isPerfect_tilde_iff Mj).2 hMj, ⟨?_⟩⟩
  exact (StandardModel.affinePullbackComparison (A.obj j) c.pt (c.ι.app j)).app Mj ≪≫
    (tilde.functor c.pt).mapDerivedCategory.mapIso eMj.symm ≪≫ eM

end AlgebraicGeometry.AffinePerfectLimit

end
