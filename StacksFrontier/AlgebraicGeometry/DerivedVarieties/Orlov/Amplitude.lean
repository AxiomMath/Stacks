module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.EssentialImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Exact autoequivalences fixing closed-point skyscrapers preserve the standard t-structure

Let `X` be a proper regular scheme over a field `k` and `F : D_perf(𝒪_X) ≌ D_perf(𝒪_X)` an exact
equivalence with `F(𝒪_x) ≅ 𝒪_x` for every closed point `x`, where `𝒪_x` is the residue-field
skyscraper. Then `F` and its inverse preserve `D^{≤ b}` and `D^{≥ b}` for every `b`; in particular
`F` carries a coherent module placed in degree zero to a coherent module placed in degree zero.
These are the first two steps of the proof of [Stacks, Tag 0G27].

For `D^{≤ b}`: a perfect complex `K` lies in degrees `≤ b` exactly when `Hom(K, 𝒪_x[-i]) = 0` for
all closed points `x` and all `i > b` ([Stacks, Tag 0GWZ], here through the derived stalk), and
`Hom(F(K), 𝒪_x[-i]) ≅ Hom(F(K), F(𝒪_x)[-i]) ≅ Hom(K, 𝒪_x[-i])`. For `D^{≥ b}`: the truncation
`τ_{< b}F(K) ⟶ F(K)` corresponds to a map `F^{-1}(τ_{< b}F(K)) ⟶ K` from an object in degrees
`< b` to one in degrees `≥ b`, which vanishes ([Stacks, Tag 06XS]); and `τ_{< b}F(K) ⟶ F(K)` is an
isomorphism on cohomology in degrees `< b`. The truncation is perfect because `X` is regular.

## Main results

All names below are in the namespace `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov`.

* `isZero_of_isCoherent_of_forall_isClosed`: a coherent module on a Noetherian scheme with zero
  stalks at the closed points is zero.
* `isLE_of_forall_hom_pointSheaf_shift`: the closed-point test for `D^{≤ b}`.
* `isLE_obj_of_fixes_perfectPointSheaf`: a fully faithful exact endofunctor of `D_perf(𝒪_X)`
  fixing every closed-point skyscraper preserves `D^{≤ b}`.
* `isGE_obj_of_isLE_inverse`: an exact autoequivalence of `D_perf(𝒪_X)` whose inverse preserves
  every `D^{≤ b}` preserves every `D^{≥ b}`.
* `exists_isCoherent_iso_single_of_fixes_perfectPointSheaf`: an exact autoequivalence of
  `D_perf(𝒪_X)` fixing every closed-point skyscraper carries a coherent module placed in degree
  zero to a coherent module placed in degree zero.

## References

* [Stacks Project, Tag 0G27](https://stacks.math.columbia.edu/tag/0G27)
* [Stacks Project, Tag 0GWZ](https://stacks.math.columbia.edu/tag/0GWZ)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Stacks.Cohomology.PerfectComplexes
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-! ### Vanishing by stalks -/

/-- A sheaf of `𝒪_X`-modules with zero stalks is zero. -/
theorem isZero_of_forall_isZero_stalkFunctor (M : X.Modules)
    (h : ∀ y : X, IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf y).obj M)) : IsZero M := by
  let K := (DerivedCategory.singleFunctor X.Modules 0).obj M
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0
  have : IsIso (0 : K ⟶ K) := by
    refine Stacks.Cohomology.StalkwiseIso.isIso_of_forall_stalk_isIso X.ringCatSheaf _
      fun i y => ?_
    have hz : IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf y).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := by
      by_cases hi : i = 0
      · subst hi
        exact (h y).of_iso ((SheafOfModules.stalkFunctor X.ringCatSheaf y).mapIso (ε.app M))
      · refine Functor.map_isZero _ ?_
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE K 0 i hi
        · exact DerivedCategory.isZero_of_isLE K 0 i hi
    exact ⟨0, hz.eq_of_src _ _, hz.eq_of_src _ _⟩
  exact (Functor.map_isZero (DerivedCategory.homologyFunctor X.Modules 0)
    (IsZero.of_epi_zero K K)).of_iso (ε.app M).symm

/-- **A coherent module on a Noetherian scheme whose stalks at the closed points vanish is zero**:
its support is closed, and a nonempty closed subset of a quasi-compact scheme contains a closed
point. -/
theorem isZero_of_isCoherent_of_forall_isClosed [IsNoetherian X] (M : X.Modules)
    (hM : M.IsCoherent)
    (h : ∀ z : X, IsClosed ({z} : Set X) →
      IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf z).obj M)) : IsZero M := by
  refine isZero_of_forall_isZero_stalkFunctor X M fun y => ?_
  have : M.IsFiniteType := hM.isFiniteType
  by_contra hy
  have hyS : y ∈ SheafOfModules.supp M := (mem_supp_iff_not_isZero_stalkFunctor X M y).2 hy
  obtain ⟨z, hz, hzclosed⟩ := (isClosed_closure (s := ({y} : Set X))).exists_closed_singleton
    ⟨y, subset_closure rfl⟩
  exact (mem_supp_iff_not_isZero_stalkFunctor X M z).1 (closure_minimal
    (Set.singleton_subset_iff.2 hyS)
    (Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp X.sheaf M) hz) (h z hzclosed)

/-! ### The closed-point test for `D^{≤ b}` -/

/-- **The closed-point test for `D^{≤ b}`** ([Stacks, Tag 0GWZ], globally): a perfect complex `K`
on a Noetherian scheme lies in degrees `≤ b` as soon as `Hom(K, 𝒪_x[-i]) = 0` for every closed
point `x` and every `i > b`. -/
theorem isLE_of_forall_hom_pointSheaf_shift [IsNoetherian X] (K : DerivedCategory X.Modules)
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) (b : ℤ)
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∀ i : ℤ, b < i →
      Subsingleton (K ⟶ (pointSheaf X x)⟦-i⟧)) :
    K.IsLE b := by
  have hbc := Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK
  rw [DerivedCategory.isLE_iff]
  intro j hj
  refine isZero_of_isCoherent_of_forall_isClosed X _ (hbc.2 j) fun z hz => ?_
  have hpc := @Stacks.AlgebraicGeometry.DerivedStalk.isPseudoCoherent_derivedStalk_of_isPerfect
    X inferInstance z (StacksDraft.StalkRingComparison.isNoetherianRing_stalkRing X z) K hK
  obtain ⟨hbdd, hfin⟩ :=
    (@StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (ToType (StacksDraft.StalkRingComparison.stalkRing X z)) _
      (StacksDraft.StalkRingComparison.isNoetherianRing_stalkRing X z) _
      ((derivedStalk X z).obj K) 0 (ToType (StacksDraft.StalkRingComparison.stalkRing X z))
      _ _).2.1.1 hpc
  have hLE := isLE_of_forall_hom_shift_residueField _ b hbdd hfin
    (fun i hi => by
      have := h z hz i hi
      exact (homPointSheafShiftEquiv X z K (-i)).symm.injective.subsingleton)
  exact (DerivedCategory.isZero_of_isLE (hX := hLE) _ b j hj).of_iso
    (((SheafOfModules.stalkFunctor X.ringCatSheaf z).mapDerivedCategoryHomologyIso j).app K).symm

/-! ### Functors fixing the closed-point skyscrapers -/

section Fixing

variable (hX : IsRegular X) [IsNoetherian X]

/-- **A fully faithful exact endofunctor of `D_perf(𝒪_X)` fixing every closed-point skyscraper
preserves `D^{≤ b}`.** -/
theorem isLE_obj_of_fixes_perfectPointSheaf
    (F : PerfectDerivedCategory X ⥤ PerfectDerivedCategory X) [F.CommShift ℤ]
    (hFF : F.FullyFaithful)
    (hfix : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      Nonempty (F.obj (perfectPointSheaf X hX x hx) ≅ perfectPointSheaf X hX x hx))
    (E : PerfectDerivedCategory X) (b : ℤ) (hE : E.obj.IsLE b) : (F.obj E).obj.IsLE b := by
  refine isLE_of_forall_hom_pointSheaf_shift X _ (F.obj E).property b fun x hx i hi => ?_
  obtain ⟨e⟩ := hfix x hx
  let P := perfectPointSheaf X hX x hx
  have h0 : Subsingleton (E.obj ⟶ P.obj⟦-i⟧) := by
    have : (P.obj⟦-i⟧).IsGE i := by
      show ((pointSheaf X x)⟦-i⟧).IsGE i
      have : DerivedCategory.TStructure.t.IsGE (pointSheaf X x) 0 :=
        inferInstanceAs (((DerivedCategory.singleFunctor X.Modules 0).obj
          (show X.Modules from residueFieldSkyscraperSheaf X x)).IsGE 0)
      exact DerivedCategory.TStructure.t.isGE_shift _ 0 (-i) i (by omega)
    exact subsingleton_of_forall_eq 0 fun f => DerivedCategory.TStructure.t.zero f b i hi
  have h1 : Subsingleton (E ⟶ P⟦-i⟧) := (perfectHomShiftEquiv X E P (-i)).injective.subsingleton
  let φ : (F.obj E ⟶ P⟦-i⟧) ≃ (E ⟶ P⟦-i⟧) :=
    (Iso.homCongr (Iso.refl _) ((shiftFunctor _ (-i)).mapIso e.symm ≪≫
      ((F.commShiftIso (-i)).app P).symm)).trans hFF.homEquiv.symm
  have h2 : Subsingleton (F.obj E ⟶ P⟦-i⟧) := φ.injective.subsingleton
  exact (perfectHomShiftEquiv X (F.obj E) P (-i)).symm.injective.subsingleton

/-- On a regular Noetherian scheme the truncation `τ_{< b}` of a perfect complex is perfect. -/
theorem isPerfect_truncLT (hX : IsRegular X) (K : DerivedCategory X.Modules)
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) (b : ℤ) :
    IsPerfect.{u, u, u + 1} (X := X.toRingedSpace)
      ((DerivedCategory.TStructure.t.truncLT b).obj K) :=
  Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular hX _
    (DerivedCategoryB.derivedCategoryBBounded_truncLT_obj _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass
        (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)) b K
      (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK))

/-- **An exact autoequivalence of `D_perf(𝒪_X)` whose inverse preserves every `D^{≤ b}` preserves
every `D^{≥ b}`.** The truncation `τ_{< b}F(E) ⟶ F(E)` corresponds under the equivalence to a map
from an object in degrees `< b` to `E`, which is in degrees `≥ b`, so it vanishes; and it is an
isomorphism on cohomology in degrees `< b`. -/
theorem isGE_obj_of_isLE_inverse (hX : IsRegular X)
    (e : PerfectDerivedCategory X ≌ PerfectDerivedCategory X)
    (hinv : ∀ (E : PerfectDerivedCategory X) (b : ℤ), E.obj.IsLE b → (e.inverse.obj E).obj.IsLE b)
    (E : PerfectDerivedCategory X) (b : ℤ) (hE : E.obj.IsGE b) : (e.functor.obj E).obj.IsGE b := by
  let K := (e.functor.obj E).obj
  let T : PerfectDerivedCategory X :=
    ⟨(DerivedCategory.TStructure.t.truncLT b).obj K, isPerfect_truncLT X hX K
      (e.functor.obj E).property b⟩
  let ι : T ⟶ e.functor.obj E :=
    ObjectProperty.homMk ((DerivedCategory.TStructure.t.truncLTι b).app K)
  have hT : T.obj.IsLE (b - 1) := by
    show ((DerivedCategory.TStructure.t.truncLT b).obj K).IsLE (b - 1)
    exact DerivedCategory.TStructure.t.isLE_truncLT_obj ..
  have hι : ι = 0 := by
    have h2 : (e.symm.toAdjunction.homEquiv T E).symm ι = 0 := by
      apply (ObjectProperty.fullyFaithfulι _).map_injective
      rw [Functor.map_zero]
      have : DerivedCategory.TStructure.t.IsLE
          ((ObjectProperty.ι _).obj (e.symm.functor.obj T)) (b - 1) := hinv T (b - 1) hT
      have : DerivedCategory.TStructure.t.IsGE ((ObjectProperty.ι _).obj E) b := hE
      exact DerivedCategory.TStructure.t.zero _ (b - 1) b (by omega)
    rw [← (e.symm.toAdjunction.homEquiv T E).apply_symm_apply ι, h2, Adjunction.homEquiv_unit,
      Functor.map_zero, Limits.comp_zero]
  rw [DerivedCategory.isGE_iff]
  intro j hj
  have := DerivedCategory.isIso_homologyFunctor_map_truncLTι b j hj K
  have h0 : (DerivedCategory.homologyFunctor X.Modules j).map
      ((DerivedCategory.TStructure.t.truncLTι b).app K) = 0 := by
    show (DerivedCategory.homologyFunctor X.Modules j).map ((ObjectProperty.ι _).map ι) = 0
    rw [hι, Functor.map_zero, Functor.map_zero]
  have hiso : IsIso (0 : (DerivedCategory.homologyFunctor X.Modules j).obj T.obj ⟶
      (DerivedCategory.homologyFunctor X.Modules j).obj K) := h0 ▸ inferInstance
  exact IsZero.of_epi_zero ((DerivedCategory.homologyFunctor X.Modules j).obj T.obj) _

/-- **An exact autoequivalence of `D_perf(𝒪_X)` fixing every closed-point skyscraper, whose inverse
does too, carries a coherent module placed in degree zero to a coherent module placed in degree
zero.** Both the equivalence and its inverse preserve `D^{≤ 0}`, hence the equivalence preserves
`D^{≥ 0}`; an object in `D^{≤ 0} ∩ D^{≥ 0}` is its `H^0` placed in degree zero, and `H^0` of a
perfect complex on a Noetherian scheme is coherent. -/
theorem exists_isCoherent_iso_single_of_fixes_perfectPointSheaf
    (e : PerfectDerivedCategory X ≌ PerfectDerivedCategory X) [e.functor.CommShift ℤ]
    [e.inverse.CommShift ℤ]
    (hfix : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      Nonempty (e.functor.obj (perfectPointSheaf X hX x hx) ≅ perfectPointSheaf X hX x hx))
    (hfix' : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      Nonempty (e.inverse.obj (perfectPointSheaf X hX x hx) ≅ perfectPointSheaf X hX x hx))
    (E : PerfectDerivedCategory X) (hE0 : E.obj.IsLE 0) (hE0' : E.obj.IsGE 0) :
    ∃ N : X.Modules, N.IsCoherent ∧
      Nonempty ((e.functor.obj E).obj ≅ (DerivedCategory.singleFunctor X.Modules 0).obj N) := by
  have hLE :=
    isLE_obj_of_fixes_perfectPointSheaf X hX e.functor e.fullyFaithfulFunctor hfix E 0 hE0
  have hGE := isGE_obj_of_isLE_inverse X hX e
    (fun E b hE => isLE_obj_of_fixes_perfectPointSheaf X hX e.inverse e.fullyFaithfulInverse
      hfix' E b hE) E 0 hE0'
  obtain ⟨N, ⟨eN⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (e.functor.obj E).obj 0
  exact ⟨N, @ObjectProperty.prop_of_iso _ _
    (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)
    AlgebraicGeometry.CoherentAbelian.coherentModules_isClosedUnderIsomorphisms _ _
    ((DerivedCategory.homologyFunctor X.Modules 0).mapIso eN ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app N)
    ((Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X _
      (e.functor.obj E).property).2 0), ⟨eN⟩⟩

end Fixing

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
