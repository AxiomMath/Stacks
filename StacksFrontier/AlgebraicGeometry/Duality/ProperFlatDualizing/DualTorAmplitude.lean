module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DualOfAPerfectComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenComplexModel
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexCharts
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeBoundedComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# The dual of a perfect complex with bounded Tor amplitude

Let `P` be a perfect object of `D(𝒪_Z)` on a scheme `Z` and let `P^∨ = R𝓗om(P, 𝒪_Z)` be its
derived dual. If `P` has Tor amplitude in `[a, b]` on every affine open, then the cohomology
sheaves of `P^∨` vanish in degrees `> -a`.

The proof is local and uses no representative of `P`. Over a quasi-compact scheme `W` the dual is
bounded above, and `P^∨` is a left dual of `P` in the monoidal derived category, so that
`Hom(P^∨, F[-n]) = Hom(𝒪_W, P ⊗^L F[-n])` for an `𝒪_W`-module `F`. Tor amplitude puts
`P ⊗^L F[-n]` in degrees `≥ a + n`, hence the group vanishes as soon as `n > -a`, and a
descending induction on an upper bound of `P^∨` concludes. The general case is the restriction
of `R𝓗om` to affine opens ([Stacks, Tag 08DL]).

## Main results

* `Stacks.Duality.StandardModel.isLE_derivedDual_of_hasTorAmplitude` — on a quasi-compact
  scheme, `P^∨` lies in degrees `≤ -a`.
* `Stacks.Duality.StandardModel.isZero_homology_derivedDual_of_hasTorAmplitude` — on any scheme,
  with the Tor amplitude read on affine opens, `H^i(P^∨) = 0` for `i > -a`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite

universe u

namespace Stacks.Duality.StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

open Stacks.SheafOfModules in
/-- **The dual of a perfect object of Tor amplitude `[a, b]` lies in degrees `≤ -a`**, on a
quasi-compact scheme. -/
theorem isLE_derivedDual_of_hasTorAmplitude {W : Scheme.{u}} [CompactSpace W]
    (P : DerivedCategory W.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) P) (a b : ℤ)
    (h : Stacks.Cohomology.TorAmplitude.HasTorAmplitude W.toRingedSpace P a b) :
    (derivedDual W.sheaf P).IsLE (-a) := by
  let P' : DerivedCategory (StructureSheafModules W.sheaf) := P
  let := derivedMonoidalStructure W.sheaf
  let : ExactPairing P' (derivedDual W.sheaf P') :=
    exactPairingDerivedDual W.sheaf P'
      (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect W.toRingedSpace P hP)
  let T := Stacks.Cohomology.TorAmplitude.derTensor W.toRingedSpace
  let ε : derivedTensor W.sheaf ≅ T.tensor :=
    (DerivedMonoidal.derivedBifunctorTensorIso W.sheaf (derivedTensorAsSiteDatum W.sheaf)).symm ≪≫
      DerivedMonoidal.derivedBifunctorTensorIso W.sheaf T
  have : ∀ F : StructureSheafModules W.sheaf, ∀ n : ℤ, -a < n →
      ∀ x : 𝟙_ (DerivedCategory (StructureSheafModules W.sheaf)) ⟶
        P' ⊗ (DerivedCategory.singleFunctor _ n).obj F, x = 0 := by
    intro F n hn x
    have h1 : (𝟙_ (DerivedCategory (StructureSheafModules W.sheaf))).IsLE 0 := by
      change ((DerivedCategory.singleFunctor _ 0).obj _).IsLE 0
      exact DerivedCategory.instIsLEObjSingleFunctor _ _
    let := T.commShift₂.commShiftObj P'
    let X₀ := (T.tensor.obj P').obj ((DerivedCategory.singleFunctor _ 0).obj F)
    have hX₀ : X₀.IsGE a := (DerivedCategory.isGE_iff _ a).2 fun i hi =>
      h F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega)
    have hX₁ : DerivedCategory.TStructure.t.ge (a + n) (X₀⟦-n⟧) :=
      DerivedCategory.TStructure.t.ge_shift a (-n) (a + n) (by omega) X₀ hX₀.1
    let e : P' ⊗ (DerivedCategory.singleFunctor _ n).obj F ≅ X₀⟦-n⟧ :=
      (ε.app P').app _ ≪≫ (T.tensor.obj P').mapIso
          (((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app F).symm ≪≫
        ((T.tensor.obj P').commShiftIso (-n)).app _
    have hY : (P' ⊗ (DerivedCategory.singleFunctor _ n).obj F).IsGE 1 :=
      ⟨DerivedCategory.TStructure.t.ge_antitone (show 1 ≤ a + n by omega) _
        ((DerivedCategory.TStructure.t.ge (a + n)).prop_of_iso e.symm hX₁)⟩
    exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE x 0 1 (by omega) h1 hY
  let D' : DerivedCategory (StructureSheafModules W.sheaf) := derivedDual W.sheaf P'
  have hkey : ∀ n : ℤ, -a < n → ∀ (F : StructureSheafModules W.sheaf)
      (g : D' ⟶ (DerivedCategory.singleFunctor _ n).obj F), g = 0 := by
    intro n hn F g
    let e := tensorLeftHomEquiv (𝟙_ (DerivedCategory (StructureSheafModules W.sheaf))) P' D'
      ((DerivedCategory.singleFunctor _ n).obj F)
    exact (cancel_epi (ρ_ D').hom).1 (e.injective ((this F n hn _).trans (this F n hn _).symm))
  have hstep : ∀ n : ℤ, -a < n → D'.IsLE n → D'.IsLE (n - 1) := by
    intro n hn hD
    refine Stacks.Sites.FibredCategory.isLE_of_forall_hom_eq_zero DerivedCategory.TStructure.t D'
      (n - 1) n (by omega) fun Y hY f => ?_
    obtain ⟨F, ⟨i⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((DerivedCategory.TStructure.t.truncLE n).obj Y) n
    have h0 : DerivedCategory.TStructure.t.liftTruncLE f n ≫ i.hom = 0 := hkey n hn F _
    rw [← DerivedCategory.TStructure.t.liftTruncLE_ι f n,
      show DerivedCategory.TStructure.t.liftTruncLE f n = 0 by
        simpa using (cancel_mono i.hom).1 (h0.trans zero_comp.symm), zero_comp]
  obtain ⟨c, hc⟩ := Stacks.DerivedQCoh.exists_isLE_derivedDual W P hP
  have hind : ∀ m : ℕ, D'.IsLE (-a + m) → D'.IsLE (-a) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      have h' := hstep (-a + (m + 1 : ℕ)) (by omega) hm
      rw [show -a + ((m + 1 : ℕ) : ℤ) - 1 = -a + m by push_cast; ring] at h'
      exact ih h'
  exact hind (c + a).toNat
    ⟨DerivedCategory.TStructure.t.le_monotone (show c ≤ -a + ((c + a).toNat : ℤ) by omega) _ hc.1⟩

open Stacks.SheafOfModules in
/-- Restriction along an open immersion carries `𝒪_Z` in degree zero to `𝒪_U` in degree zero. -/
def restrictDerivedStructureSheafIsoStandard {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
        (RingedSite.derivedStructureSheaf (ringedSite Z.sheaf)) ≅
      RingedSite.derivedStructureSheaf (ringedSite U.sheaf) :=
  (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor j)
        (ComplexShape.up ℤ) 0).app _ ≪≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
          (Scheme.Modules.restrictUnitIso j))

open Stacks.SheafOfModules in
/-- **The dual of a perfect complex of Tor amplitude `[a, b]` on affine opens has no cohomology
above degree `-a`.** Let `P` be a perfect object of `D(𝒪_Z)` whose restriction to every affine
open `V` has Tor amplitude in `[a, b_V]`. Then `H^i(R𝓗om(P, 𝒪_Z)) = 0` for every `i > -a`. -/
theorem isZero_homology_derivedDual_of_hasTorAmplitude {Z : Scheme.{u}}
    (P : DerivedCategory Z.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z.toRingedSpace) P) (a : ℤ)
    (h : ∀ V : Z.affineOpens, ∃ b : ℤ,
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude
        (Z.toRingedSpace.restrict (V : Z.Opens).isOpenEmbedding)
        ((Scheme.Modules.restrictFunctor (V : Z.Opens).ι).mapDerivedCategory.obj P) a b)
    (i : ℤ) (hi : -a < i) :
    IsZero ((DerivedCategory.homologyFunctor Z.Modules i).obj (derivedDual Z.sheaf P)) := by
  refine isZero_of_forall_isZero_stalk _ fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  refine (Scheme.Modules.isZero_restrict_iff_forall_isZero_stalk V _).1 ?_ x hxV
  have : IsAffine V.toScheme := hV
  obtain ⟨b, hb⟩ := h ⟨V, hV⟩
  have := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := Z.ringCatSheaf) V
  have := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := Z.ringCatSheaf) V
  let PV := (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj P
  have hle := isLE_derivedDual_of_hasTorAmplitude PV
    (ComplexAndDivisorSituation.isPerfect_restrictFunctor_mapDerivedCategory V.ι hP) a b hb
  let c : (Scheme.Modules.restrictFunctor V.ι).obj
        ((DerivedCategory.homologyFunctor Z.Modules i).obj (derivedDual Z.sheaf P)) ≅
      (DerivedCategory.homologyFunctor V.toScheme.Modules i).obj
        (derivedDual V.toScheme.sheaf PV) :=
    (((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategoryHomologyIso i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor V.toScheme.Modules i).mapIso
        (derivedSheafHomSchemeRestrictionIso V P _ ≪≫
          ((RingedSite.derivedSheafHomBifunctor (ringedSite V.toScheme.sheaf)).obj
            (op PV)).mapIso (restrictDerivedStructureSheafIsoStandard V.ι))
  exact (DerivedCategory.isZero_of_isLE _ (-a) i hi (hX := hle)).of_iso c

end Stacks.Duality.StandardModel

end
