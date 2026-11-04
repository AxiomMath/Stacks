module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.LowerSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.SepClosedComponents
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.StructureSheafUnit
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.DerivedPushforwardToField
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.GeometricFibres
public import Mathlib.Topology.LocallyConstant.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local constancy of the number of geometric connected components of the fibres

[Stacks, Tag 0E0N]: for `f : X ⟶ S` proper, flat, of finite presentation, with geometrically
reduced fibres, the number `n_{X/S}(s)` of geometric connected components of `X_s` is a locally
constant function of `s`.

The source's proof: `n_{X/S}` is lower semicontinuous ([Stacks, Tag 0BUI]); it equals
`s ↦ dim_{κ(s)} H⁰(X_s, 𝒪_{X_s})` by [Stacks, Tag 0BUG], the fibres being geometrically reduced;
and that function is upper semicontinuous by [Stacks, Tag 0BDN]. Here the middle identification
is made on a geometric fibre `X_{\bar s}` over the separable closure of `κ(s)`, where the global
functions count the connected components
(`Stacks.AlgebraicGeometry.ProperSectionsGeom.finrank_globalSections_eq_card_connectedComponents`),
and the dimension of `H⁰(X_{\bar s}, 𝒪)` is read as the degree-zero derived-fibre Betti number of
`Rf_*𝒪_X` at `s` through the base change of [Stacks, Tag 0B91]; the upper semicontinuity of the
latter is part (2) of [Stacks, Tag 0BDI], which is what [Stacks, Tag 0BDN] reduces to.

[Stacks, Tag 0A1H] (behind [Stacks, Tag 0B91]) is
`AlgebraicGeometry.isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap`.
Part (2) of [Stacks, Tag 0BDI] is
`AlgebraicGeometry.DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti`.

## Main results

* `AlgebraicGeometry.numGeometricConnectedComponents_eq_derivedFiberBetti`: `n_{X/S}` is the
  degree-zero derived-fibre Betti function of `Rf_*𝒪_X`.
* `AlgebraicGeometry.isLocallyConstant_numGeometricConnectedComponents`: [Stacks, Tag 0E0N].

## References

* [Stacks Project, Tag 0E0N](https://stacks.math.columbia.edu/tag/0E0N)
* [Stacks Project, Tag 0BUI](https://stacks.math.columbia.edu/tag/0BUI)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0BDN](https://stacks.math.columbia.edu/tag/0BDN)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedStructureUnit

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- The structure sheaf of a scheme, as a complex concentrated in degree zero, is perfect. -/
private theorem isPerfect_singleFunctor_unit (X : Scheme.{u}) :
    RingedSpace.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace))) :=
  AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree X _
    (Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso.{u, u, u}
      (Stacks.SheafOfModules.Site.freePUnitIso (R := X.ringCatSheaf)))

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor) in
/-- **The number of geometric connected components of a fibre is the dimension of the degree-zero
cohomology of the derived fibre of `Rf_*𝒪_X`**, for `f` proper, flat, of finite presentation,
with geometrically reduced fibres: base change ([Stacks, Tag 0B91], from 0A1H) identifies the
derived fibre at a geometric point over `s` with `RΓ(X_{\bar s}, 𝒪)`, and on the geometric fibre
the global functions count the connected components. -/
theorem numGeometricConnectedComponents_eq_derivedFiberBetti
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyReduced f]
    (hpc : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit (structureSheafRing X.toRingedSpace))))) (s : S) :
    numGeometricConnectedComponents f s =
      (DerivedFibreBetti.derivedFiberBetti S _ hpc 0 s : ℕ∞) := by
  obtain ⟨hlfp, hqc, hqs⟩ : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have hE := isPerfect_singleFunctor_unit X
  let κ := S.residueField s
  let K := SeparableClosure κ
  let φ : κ ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap κ K)
  let Y := geometricFiber f s K
  let q : Y ⟶ Spec (CommRingCat.of K) := pullback.snd (f.fiberToSpecResidueField s) (Spec.map φ)
  have hsq : IsPullback (pullback.fst (f.fiberToSpecResidueField s) (Spec.map φ) ≫ f.fiberι s) q
      f (Spec.map φ ≫ S.fromSpecResidueField s) :=
    (IsPullback.of_hasPullback (f.fiberToSpecResidueField s) (Spec.map φ)).paste_horiz
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
  have hbc :=
    (ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat
      f ⟨hlfp, hqc, hqs⟩ ‹_› ‹_› _ hE).2 _ q _ hsq
  have : IsProper q := MorphismProperty.of_isPullback (P := @IsProper) hsq ‹_›
  have : GeometricallyReduced q := MorphismProperty.of_isPullback (P := @GeometricallyReduced)
    hsq ‹_›
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  have h₁ := SpecField.finrank_derivedPullback (Field.toIsField _) (Field.toIsField _) φ
    ((derivedPullback (S.fromSpecResidueField s).toLRSHom.toShHom).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit (structureSheafRing X.toRingedSpace))))) 0
  obtain ⟨β, -⟩ := @exists_derivedPullback_map_structureUnit_eq _ _ _ _
    (pullback.fst (f.fiberToSpecResidueField s) (Spec.map φ) ≫ f.fiberι s).toLRSHom.toShHom
    q.toLRSHom.toShHom f.toLRSHom.toShHom (Spec.map φ ≫ S.fromSpecResidueField s).toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w) hbc
  have hc : (Spec.map φ).toLRSHom.toShHom ≫ (S.fromSpecResidueField s).toLRSHom.toShHom =
      (Spec.map φ ≫ S.fromSpecResidueField s).toLRSHom.toShHom := by
    simp only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom]
  let e := (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (Spec.map φ).toLRSHom.toShHom (S.fromSpecResidueField s).toLRSHom.toShHom).app
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit (structureSheafRing X.toRingedSpace)))) ≪≫
    eqToIso (congrArg (fun k => (derivedPullback k).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit (structureSheafRing X.toRingedSpace))))) hc) ≪≫ β
  have h₂ := ((moduleSpecΓFunctor (R := CommRingCat.of K)).mapIso
    ((DerivedCategory.homologyFunctor _ 0).mapIso e)).toLinearEquiv.finrank_eq
  have h₃ := finrank_homology_derivedPushforward_eq_finrank_cohomologyOverField K q
    (SheafOfModules.unit Y.ringCatSheaf) 0
  have h₄ :=
    open Stacks.AlgebraicGeometry.ProperSectionsGeom in
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections K q
  have h₅ :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.finrank_globalSections_eq_card_connectedComponents
    K q
  have := (Stacks.AlgebraicGeometry.ProperSectionsGeom.componentwiseArtinianDecomposition K
    q).finite_connectedComponents
  change ENat.card (_root_.ConnectedComponents Y) = _
  rw [ENat.card_eq_coe_natCard]
  norm_cast
  exact h₅.symm.trans (h₄.symm.trans (h₃.symm.trans (h₂.symm.trans h₁)))

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor) in
/-- **The number of geometric connected components of the fibres is locally constant**, for
`f : X ⟶ S` proper, flat, of finite presentation, with geometrically reduced fibres.

It is lower semicontinuous by [Stacks, Tag 0BUI], and it is the degree-zero derived-fibre Betti
function of the perfect object `Rf_*𝒪_X` (`numGeometricConnectedComponents_eq_derivedFiberBetti`),
which is upper semicontinuous by part (2) of [Stacks, Tag 0BDI]
(`DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti`). The hypothesis `hred` that the
geometric fibres are reduced asks this of the base change of `f` to the spectrum of every
algebraically closed field; it gives Mathlib's `GeometricallyReduced f`, reducedness after base
change to every field, by `geometricallyReduced_iff_forall_isAlgClosed`. -/
@[stacks 0E0N, ega "IV 15.5.7" "Flat", ega "IV 15.5.9" "(ii), special case"]
theorem isLocallyConstant_numGeometricConnectedComponents
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hred : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
      IsReduced (pullback f s)) :
    IsLocallyConstant (numGeometricConnectedComponents f) := by
  have : GeometricallyReduced f := (geometricallyReduced_iff_forall_isAlgClosed f).2 hred
  have hE := isPerfect_singleFunctor_unit X
  obtain ⟨hperf, -⟩ :=
    ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat
      f ⟨inferInstance, inferInstance, inferInstance⟩ ‹_› ‹_› _ hE
  have hpc := RingedSpace.IsPerfect.isPseudoCoherent hperf
  have key := numGeometricConnectedComponents_eq_derivedFiberBetti f hpc
  have husc := DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti S _ hpc 0
  have hlsc := lowerSemicontinuous_numGeometricConnectedComponents f
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have h₁ := husc s _ (Nat.lt_succ_self _)
  have h₂ : ∀ᶠ t in nhds s, (DerivedFibreBetti.derivedFiberBetti S _ hpc 0 s : ℕ∞) ≤
      numGeometricConnectedComponents f t := by
    rcases Nat.eq_zero_or_eq_succ_pred (DerivedFibreBetti.derivedFiberBetti S _ hpc 0 s) with
      h | h
    · exact Filter.Eventually.of_forall fun t => by rw [h]; exact bot_le
    · have hy : ((DerivedFibreBetti.derivedFiberBetti S _ hpc 0 s).pred : ℕ∞) <
          numGeometricConnectedComponents f s :=
        (show ((DerivedFibreBetti.derivedFiberBetti S _ hpc 0 s).pred : ℕ∞) <
            (DerivedFibreBetti.derivedFiberBetti S _ hpc 0 s : ℕ∞) by
          exact_mod_cast Nat.pred_lt (by omega)).trans_eq (key s).symm
      filter_upwards [hlsc s _ hy] with t ht
      have := Order.add_one_le_of_lt ht
      rwa [show ((DerivedFibreBetti.derivedFiberBetti S _ hpc 0 s).pred : ℕ∞) + 1 =
        (DerivedFibreBetti.derivedFiberBetti S _ hpc 0 s : ℕ∞) by
          exact_mod_cast (Nat.succ_pred_eq_of_pos (by omega))] at this
  filter_upwards [h₁, h₂] with t ht₁ ht₂
  have h₃ : DerivedFibreBetti.derivedFiberBetti S _ hpc 0 s ≤
      DerivedFibreBetti.derivedFiberBetti S _ hpc 0 t := by
    exact_mod_cast ht₂.trans_eq (key t)
  exact (key t).trans ((congrArg (fun n : ℕ => (n : ℕ∞))
    (le_antisymm (Nat.lt_succ_iff.mp ht₁) h₃)).trans (key s).symm)

end AlgebraicGeometry

end
