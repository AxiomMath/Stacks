module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PointDual
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.EssentialImage
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkInvertibility
public import StacksFrontier.RingTheory.Dualizing.RegularLocalFiniteLengthDuality
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Detecting zero perfect complexes by maps out of residue-field skyscrapers

Let `X` be a regular Noetherian scheme, `x` a closed point, `𝒪_x` the skyscraper sheaf at `x`
with value `κ(x)` and `K` a perfect object of `D(𝒪_X)`. If `Hom(𝒪_x, K[i]) = 0` for every
`i ∈ ℤ`, then `K` is zero on an open neighbourhood of `x`: this is [Stacks, Tag 0G03] part (2).
Its global consequence -- `K = 0` as soon as this holds at every closed point -- is the
input (hypothesis (2) of [Stacks, Tag 0G24]) of the criterion [Stacks, Tag 0G25] in
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.FixingZeroDimensional`.

## The proof

The source deduces part (2) from part (1), which rests on the duality [Stacks, Tag 0G02] for a
coherent sheaf supported at `x`. Here the duality is applied at the stalk instead. Write
`D = R𝓗om(-, 𝒪_X)` for the dual of [Stacks, Tag 08DQ]; `𝒪_x` is perfect, `X` being regular.

1. On perfect complexes `D` is fully faithful up to the biduality isomorphisms, so
   `Hom(𝒪_x, K[i]) = 0` gives `Hom(D K, (D 𝒪_x)[i]) = 0`
   (`subsingleton_hom_dual_of_subsingleton_hom`, with `D(𝒪_x[-i]) = (D 𝒪_x)[i]`).
2. By [Stacks, Tag 0GM8] the stalk of `D M` at `y` is `RHom_{𝒪_{X,y}}(M_y, 𝒪_{X,y})` for `M`
   perfect. As `(𝒪_x)_y = 0` for `y ≠ x`, `D 𝒪_x` is supported at `x`, hence is the derived
   skyscraper of its stalk `N = RHom_{𝒪_{X,x}}(κ(x), 𝒪_{X,x})`, and by the stalk-skyscraper
   adjunction `Hom((D K)_x, N[i]) = 0` for all `i`.
3. Over the regular local ring `A = 𝒪_{X,x}` Matlis duality gives `N ≅ κ'[-d]` for the Matlis
   dual `κ' = Hom_A(κ, E)`, which contains `κ`. The pseudo-coherent complex `(D K)_x` therefore
   has no nonzero map to any shift of a module containing the residue field, so it is zero.
4. Then `K_x = ((D K)^∨)_x = RHom((D K)_x, A) = 0` by [Stacks, Tag 0GM8] again, and a perfect
   complex with zero stalk at `x` vanishes near `x`, its cohomology sheaves being coherent.

## Main results

* `isZero_of_forall_hom_shift_derivedHom_residueField`: over a regular local ring, a bounded
  above complex with finite cohomology and no nonzero map to any shift of `RHom_A(κ, A)` is zero.
* `isZero_derivedStalk_of_forall_pointSheaf_hom_shift`: the vanishing of the stalk at `x`.
* `exists_mem_forall_stalkHomology_isZero_of_pointSheaf_hom_shift`: [Stacks, Tag 0G03] part (2).
* `isZero_of_forall_pointSheaf_hom_shift` and `isZero_of_forall_perfectPointSheaf_hom_shift`: the
  global form, in `D(𝒪_X)` and in `D_perf(𝒪_X)`.

## References

* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.PerfectComplexes
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

section Local

variable {A : Type u} [CommRing A]

/-- **Derived Hom out of a zero object vanishes.** -/
theorem isZero_derivedHom_obj_of_isZero (d : StacksDraft.DerivedHom.DerivedHomAdjunction A)
    {Z : DerivedCategory (ModuleCat.{u} A)} (hZ : IsZero Z)
    (M : DerivedCategory (ModuleCat.{u} A)) :
    IsZero (d.hom.obj (op Z, M)) := by
  have : ∀ T, Subsingleton (Z ⟶ T) := fun T => ⟨hZ.eq_of_src⟩
  have : Subsingleton (d.tensor.obj (d.hom.obj (op Z, M), Z) ⟶ M) :=
    ((Iso.homCongr (d.tensorSwap _ Z) (Iso.refl M)).trans
      (d.homEquiv Z _ M).symm.toEquiv).injective.subsingleton
  exact (IsZero.iff_id_eq_zero _).2 ((d.homEquiv _ Z M).injective (Subsingleton.elim _ _))

variable [IsLocalRing A]

/-- Having at most one map to `B'` passes to an isomorphic target `B`. -/
private theorem subsingleton_hom_of_iso_right {C : Type*} [Category C] {A B B' : C} (e : B ≅ B')
    (h : Subsingleton (A ⟶ B')) : Subsingleton (A ⟶ B) :=
  (Iso.homCongr (Iso.refl A) e).subsingleton

/-- The residue field `κ = A_𝔪/𝔪A_𝔪` of a local ring has finite length over `A`. -/
theorem isFiniteLength_residueFieldObj : IsFiniteLength A (residueFieldObj A) := by
  unfold residueFieldObj residueFieldModuleCat
  have hsurj : Function.Surjective (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField) := by
    intro c
    obtain ⟨q, rfl⟩ := (IsLocalRing.maximalIdeal A).bijective_algebraMap_quotient_residueField.2 c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨a, IsScalarTower.algebraMap_apply A (A ⧸ IsLocalRing.maximalIdeal A) _ a⟩
  have : IsSimpleModule A (IsLocalRing.maximalIdeal A).ResidueField :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective hsurj).2 inferInstance
  exact Module.length_ne_top_iff.1 (by rw [Module.length_eq_one]; exact ENat.one_ne_top)

/-- **The residue field embeds into the Matlis dual of the residue field**: for an embedding
`κ ⊆ E`, the map `c ↦ (t ↦ c t)` is an injective `A`-linear map `κ ⟶ Hom_A(κ, E)`. -/
theorem exists_injective_residueFieldObj_hom (E : ModuleCat.{u} A)
    (i : (ModuleCat.uliftFunctor.{u} A).obj (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono i] :
    ∃ j : residueFieldObj A ⟶ ModuleCat.of A (residueFieldObj A ⟶ E), Function.Injective j.hom := by
  unfold residueFieldObj residueFieldModuleCat
  let κ := (IsLocalRing.maximalIdeal A).ResidueField
  let ι : IsLocalRing.ResidueField A →ₗ[A] κ :=
    (IsScalarTower.toAlgHom A (A ⧸ IsLocalRing.maximalIdeal A) κ).toLinearMap
  let e := LinearEquiv.ofBijective ι
    (IsLocalRing.maximalIdeal A).bijective_algebraMap_quotient_residueField
  let φ : κ →ₗ[A] E := i.hom ∘ₗ ULift.moduleEquiv.symm.toLinearMap ∘ₗ e.symm.toLinearMap
  have hφ : Function.Injective φ := ((ModuleCat.mono_iff_injective i).1 inferInstance).comp
    (ULift.moduleEquiv.symm.injective.comp e.symm.injective)
  let J : κ →ₗ[A] (κ →ₗ[A] E) := LinearMap.llcomp A κ κ E φ ∘ₗ LinearMap.mul A κ
  refine ⟨ModuleCat.ofHom ((ModuleCat.homLinearEquiv (S := A)).symm.toLinearMap ∘ₗ J), ?_⟩
  intro c c' h
  have h1 := congrArg (fun f : ModuleCat.of A κ ⟶ E => f.hom 1) h
  simp only [J, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply] at h1
  simpa using hφ h1

/-- **Over a regular local ring, a bounded above complex with finite cohomology admitting no
nonzero map to any shift of `RHom_A(κ, A)` is zero.** By Matlis duality
`RHom_A(κ, A) ≅ κ'[-d]` for the Matlis dual `κ' = Hom_A(κ, E)`, which contains `κ`. -/
theorem isZero_of_forall_hom_shift_derivedHom_residueField [IsRegularLocalRing A]
    (P : DerivedCategory (ModuleCat.{u} A))
    (hbdd : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (hfin : ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (h : ∀ i : ℤ, Subsingleton (P ⟶
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).hom.obj
        (op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (residueFieldObj A)),
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))⟦i⟧)) :
    IsZero P := by
  obtain ⟨E, i, hmono, hhull⟩ := Module.exists_isInjectiveHull A
    ((ModuleCat.uliftFunctor.{u} A).obj (ModuleCat.of A (IsLocalRing.ResidueField A)) :
      ModuleCat.{u} A)
  -- The regular module is dualizing, `A` being Gorenstein; normalize it by a shift.
  obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, u}
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
    (Dualizing.IsRegularLocalRing.isGorensteinLocalRing A)
  obtain ⟨e⟩ := Dualizing.nonempty_derivedHom_single_iso_matlisDual_shift.{u, u} A
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) (-m) hm E i hhull
    (residueFieldObj A) (ModuleCat.of A (residueFieldObj A ⟶ E)) isFiniteLength_residueFieldObj
    ⟨Iso.refl _⟩
  set d := -m
  obtain ⟨j, hj⟩ := exists_injective_residueFieldObj_hom E i
  refine isZero_of_forall_hom_shift_of_injective P _ j hj hbdd hfin fun n => ?_
  have e' := (shiftFunctor _ (n + d)).mapIso e ≪≫
    ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) (-d) (n + d) n (by omega)).app _).symm
  exact subsingleton_hom_of_iso_right e'.symm (h (n + d))

end Local

variable (X : Scheme.{u})

/-- The biduality map at a perfect complex is an isomorphism, at the scheme spelling. -/
@[sga "6 I 7.2" "special case"]
theorem isIso_derivedBidualNatTrans_app {A : DerivedCategory X.Modules}
    (hA : IsPerfect (X := X.toRingedSpace) A) :
    IsIso ((Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).app A) :=
  Stacks.SheafOfModules.isIso_derivedBidualMap_of_isPerfectSpace (X := X.toRingedSpace) A hA

/-- **The dual reflects vanishing of `Hom` between perfect complexes**: `Hom(B^∨, A^∨) = 0` as
soon as `Hom(A, B) = 0`. -/
theorem subsingleton_hom_dual_of_subsingleton_hom {A B : DerivedCategory X.Modules}
    (hA : IsPerfect (X := X.toRingedSpace) A) (hB : IsPerfect (X := X.toRingedSpace) B)
    (h : Subsingleton (A ⟶ B)) :
    Subsingleton ((DualOverField.dual X).obj (op B) ⟶ (DualOverField.dual X).obj (op A)) := by
  have hDA : IsPerfect (X := X.toRingedSpace) ((DualOverField.dual X).obj (op A)) :=
    Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace A hA
  have hiA := isIso_derivedBidualNatTrans_app X hA
  have hiB := isIso_derivedBidualNatTrans_app X hB
  refine ⟨fun f g => dual_map_injective_of_isPerfect X hDA ?_⟩
  have key : ((Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).app A ≫
      (DualOverField.dual X).map f.op ≫
        @inv _ _ _ _ ((Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).app B) hiB : A ⟶ B) =
      (Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).app A ≫
        (DualOverField.dual X).map g.op ≫
          @inv _ _ _ _ ((Stacks.SheafOfModules.derivedBidualNatTrans X.sheaf).app B) hiB :=
    Subsingleton.elim _ _
  exact (@cancel_mono _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (@IsIso.inv_isIso _ _ _ _ _ hiB))).1
    ((@cancel_epi _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ hiA)).1 key)

variable (x : X)

/-- **The 0GM8 stalk isomorphism at the scheme spelling**: for `K` perfect,
`R𝓗om(K, M)_x ≅ RHom_{𝒪_{X,x}}(K_x, M_x)`. -/
def derivedStalkSheafHomIso (K M : DerivedCategory X.Modules)
    (hK : IsPerfect (X := X.toRingedSpace) K) :
    (derivedStalk X x).obj (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).obj M) ≅
      (Stacks.Cohomology.DerivedInternalHomStalk.stalkDerivedHom X.toRingedSpace x).obj
        (op ((derivedStalk X x).obj K), (derivedStalk X x).obj M) :=
  @asIso _ _ _ _ _
    (Stacks.Cohomology.DerivedInternalHomStalk.isIso_stalkSheafHomMap_of_isPerfect _ x K M hK)

/-- **The dual of a perfect complex with zero stalk at `x` has zero stalk at `x`.** -/
theorem isZero_derivedStalk_dual_of_isZero (K : DerivedCategory X.Modules)
    (hK : IsPerfect (X := X.toRingedSpace) K) (h : IsZero ((derivedStalk X x).obj K)) :
    IsZero ((derivedStalk X x).obj ((DualOverField.dual X).obj (op K))) :=
  (isZero_derivedHom_obj_of_isZero _ h _).of_iso (derivedStalkSheafHomIso X x K _ hK)

/-- The derived stalk of `𝒪_x` vanishes away from the closed point `x`. -/
theorem isZero_derivedStalk_pointSheaf_of_ne (hx : IsClosed ({x} : Set X)) {y : X} (hy : y ≠ x) :
    IsZero ((derivedStalk X y).obj (pointSheaf X x)) :=
  ((DerivedCategory.singleFunctor _ 0).map_isZero
    (isZero_stalkFunctor_residueFieldSkyscraperSheaf_of_ne X x hx hy)).of_iso
      (((SheafOfModules.stalkFunctor X.ringCatSheaf y).mapDerivedCategorySingleFunctor 0).app _)

/-- The derived stalk of `𝒪_x` at `x` is `κ(x)` in degree zero. -/
def derivedStalkPointSheafIso :
    (derivedStalk X x).obj (pointSheaf X x) ≅
      (DerivedCategory.singleFunctor _ 0).obj (residueFieldStalkModule X x) :=
  ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (SheafOfModules.skyscraperStalkIsoObj X.ringCatSheaf x (residueFieldStalkModule X x))

/-- The derived stalk of the structure sheaf at `x` is `𝒪_{X,x}` in degree zero. -/
def derivedStalkStructureSheafIso :
    (derivedStalk X x).obj
        (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (ToType (StacksDraft.StalkRingComparison.stalkRing X x))
          (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) :=
  ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (AlgebraicGeometry.stalkUnitLinearEquiv X.ringCatSheaf x).toModuleIso

/-- The local ring of a regular scheme at a point, in the spelling of the stalk functor on sheaves
of modules, is a regular local ring. -/
theorem isRegularLocalRing_stalkRing (hX : IsRegular X) :
    IsRegularLocalRing (ToType (StacksDraft.StalkRingComparison.stalkRing X x)) :=
  have := ((isRegular_iff_regular_stalks X).1 hX).2 x
  IsRegularLocalRing.of_ringEquiv (StacksDraft.StalkRingComparison.stalkRingEquiv X x).symm

/-- **The stalk at `x` of the dual of `𝒪_x` is `RHom_{𝒪_{X,x}}(κ(x), 𝒪_{X,x})`**, by
[Stacks, Tag 0GM8] for the perfect complex `𝒪_x`. -/
def derivedStalkDualPointSheafIso (hP : IsPerfect (X := X.toRingedSpace) (pointSheaf X x)) :
    (derivedStalk X x).obj ((DualOverField.dual X).obj (op (pointSheaf X x))) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1}
          (ToType (StacksDraft.StalkRingComparison.stalkRing X x))).hom.obj
        (op ((DerivedCategory.singleFunctor _ 0).obj (residueFieldStalkModule X x)),
          (DerivedCategory.singleFunctor _ 0).obj
            (ModuleCat.of (ToType (StacksDraft.StalkRingComparison.stalkRing X x))
              (ToType (StacksDraft.StalkRingComparison.stalkRing X x)))) :=
  derivedStalkSheafHomIso X x _ _ hP ≪≫
    (Stacks.Cohomology.DerivedInternalHomStalk.stalkDerivedHom X.toRingedSpace x).mapIso
      (Iso.prod (derivedStalkPointSheafIso X x).symm.op (derivedStalkStructureSheafIso X x))

/-- **[Stacks, Tag 0G03] part (2) at the stalk**: on a regular Noetherian scheme, a perfect
complex `K` with `Hom(𝒪_x, K[i]) = 0` for every `i ∈ ℤ`, `x` a closed point, has zero derived
stalk at `x`. -/
theorem isZero_derivedStalk_of_forall_pointSheaf_hom_shift (hX : IsRegular X) [IsNoetherian X]
    (hx : IsClosed ({x} : Set X)) (K : DerivedCategory X.Modules)
    (hK : IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ i : ℤ, Subsingleton (pointSheaf X x ⟶ K⟦i⟧)) :
    IsZero ((derivedStalk X x).obj K) := by
  have hP : IsPerfect (X := X.toRingedSpace) (pointSheaf X x) :=
    isPerfect_single_of_isCoherent X hX _ (isCoherent_residueFieldSkyscraperSheaf X x hx)
  have hDK : IsPerfect (X := X.toRingedSpace) ((DualOverField.dual X).obj (op K)) :=
    Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace K hK
  -- `Hom(K^∨, (𝒪_x)^∨[i]) = 0`, the dual reflecting vanishing of `Hom` between perfect complexes.
  have h1 : ∀ i : ℤ, Subsingleton ((DualOverField.dual X).obj (op K) ⟶
      ((DualOverField.dual X).obj (op (pointSheaf X x)))⟦i⟧) := by
    intro i
    have h0 : Subsingleton ((pointSheaf X x)⟦-i⟧ ⟶ K) :=
      @Function.Injective.subsingleton _ _ _
        ((shiftEquiv (DerivedCategory X.Modules) i).symm.toAdjunction.homEquiv _ _).injective (h i)
    exact subsingleton_hom_of_iso_right
      (Stacks.SheafOfModules.derivedSheafHomSourceShiftIso' X.sheaf
        (pointSheaf X x) _ (-i) i (by omega)).symm
      (subsingleton_hom_dual_of_subsingleton_hom X
        (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift.{u, u + 1} hP (-i)) hK h0)
  -- `(𝒪_x)^∨` is the derived skyscraper at `x` of its stalk, its stalks elsewhere vanishing.
  have hu : IsIso ((derivedStalkAdjunction X x).unit.app
      ((DualOverField.dual X).obj (op (pointSheaf X x)))) :=
    isIso_derivedStalkAdjunction_unit_app X x hx _ fun y hy =>
      isZero_derivedStalk_dual_of_isZero X y _ hP (isZero_derivedStalk_pointSheaf_of_ne X x hx hy)
  -- So maps out of `K^∨` into its shifts are maps out of the stalk `(K^∨)_x`.
  have h3 : ∀ i : ℤ, Subsingleton ((derivedStalk X x).obj ((DualOverField.dual X).obj (op K)) ⟶
      ((derivedStalk X x).obj ((DualOverField.dual X).obj (op (pointSheaf X x))))⟦i⟧) := by
    intro i
    let e : ((DualOverField.dual X).obj (op (pointSheaf X x)))⟦i⟧ ≅
        (derivedSkyscraper X x).obj
          (((derivedStalk X x).obj ((DualOverField.dual X).obj (op (pointSheaf X x))))⟦i⟧) :=
      (shiftFunctor _ i).mapIso (@asIso _ _ _ _ _ hu) ≪≫
        (((SheafOfModules.skyscraperFunctor X.ringCatSheaf x).mapDerivedCategory.commShiftIso
          i).app _).symm
    have := subsingleton_hom_of_iso_right e.symm (h1 i)
    exact ((derivedStalkAdjunction X x).homEquiv _ _).injective.subsingleton
  -- `(K^∨)_x = 0` by Matlis duality over the regular local ring `𝒪_{X,x}`.
  have := isRegularLocalRing_stalkRing X x hX
  have hpc := @Stacks.AlgebraicGeometry.DerivedStalk.isPseudoCoherent_derivedStalk_of_isPerfect
    X inferInstance x (StacksDraft.StalkRingComparison.isNoetherianRing_stalkRing X x) _ hDK
  obtain ⟨hbdd, hfin⟩ :=
    (@StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    (ToType (StacksDraft.StalkRingComparison.stalkRing X x)) _
    (StacksDraft.StalkRingComparison.isNoetherianRing_stalkRing X x) _
    ((derivedStalk X x).obj ((DualOverField.dual X).obj (op K))) 0
    (ToType (StacksDraft.StalkRingComparison.stalkRing X x)) _ _).2.1.1 hpc
  have hDKx : IsZero ((derivedStalk X x).obj ((DualOverField.dual X).obj (op K))) :=
    isZero_of_forall_hom_shift_derivedHom_residueField _ hbdd hfin fun i => by
      exact subsingleton_hom_of_iso_right ((shiftFunctor _ i).mapIso
        (derivedStalkDualPointSheafIso X x hP)).symm (h3 i)
  -- Hence `K_x = ((K^∨)^∨)_x = RHom((K^∨)_x, 𝒪_{X,x}) = 0`.
  exact (isZero_derivedStalk_dual_of_isZero X x _ hDK hDKx).of_iso ((derivedStalk X x).mapIso
    (@asIso _ _ _ _ _ (isIso_derivedBidualNatTrans_app X hK)))

/-- **A perfect complex on a Noetherian scheme with zero derived stalk at `x` is zero on a
neighbourhood of `x`**: its finitely many nonzero cohomology sheaves are coherent with zero stalk
at `x`, so each vanishes near `x` ([Stacks, Tag 01Y3]). -/
theorem exists_mem_forall_isZero_stalkObj_of_isZero_derivedStalk [IsNoetherian X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K)
    (hx : IsZero ((derivedStalk X x).obj K)) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := by
  classical
  have hbc := Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hbc.1
  have hout : ∀ i : ℤ, (i < a ∨ b < i) → ∀ y : X, IsZero (SheafOfModules.stalkObj
      X.ringCatSheaf y ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := fun i hi y =>
    Functor.map_isZero (SheafOfModules.stalkFunctor X.ringCatSheaf y) (hi.elim (ha i) (hb i))
  have hstep : ∀ i : ℤ, ∃ U : TopologicalSpace.Opens X, x ∈ U ∧ ∀ y : X, y ∈ U →
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := by
    intro i
    have : ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsFiniteType :=
      (hbc.2 i).isFiniteType
    have hxi : IsZero (SheafOfModules.stalkObj X.ringCatSheaf x
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :=
      (Functor.map_isZero (DerivedCategory.homologyFunctor _ i) hx).of_iso
        (((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategoryHomologyIso i).app
          K).symm
    obtain ⟨U, hxU, hU⟩ :=
      Stacks.AlgebraicGeometry.Tag01Y3LocalIso.exists_forall_stalk_isZero_of_stalk_isZero
        (R := X.ringCatSheaf) ((DerivedCategory.homologyFunctor X.Modules i).obj K) x
        ((SheafOfModules.isZero_stalkFunctor_obj_iff X.ringCatSheaf x _).1 hxi)
    exact ⟨U, hxU, fun y hy =>
      (SheafOfModules.isZero_stalkFunctor_obj_iff X.ringCatSheaf y _).2 (hU y hy)⟩
  choose V hxV hV using hstep
  refine ⟨⟨⋂ i ∈ (Finset.Icc a b : Finset ℤ), (V i : Set X),
    isOpen_biInter_finset fun i _ => (V i).isOpen⟩, Set.mem_biInter fun i _ => hxV i, ?_⟩
  intro y hy i
  by_cases hi : a ≤ i ∧ i ≤ b
  · exact hV i y (Set.mem_iInter₂.1 hy i (Finset.mem_Icc.2 hi))
  · exact hout i (by omega) y

/-- **[Stacks, Tag 0G03] part (2).** Let `X` be a regular Noetherian scheme, `x` a closed point
of `X`, `𝒪_x` the skyscraper sheaf at `x` with value `κ(x)` and `K` a perfect object of
`D(𝒪_X)`. If `Hom(𝒪_x, K[i]) = 0` for every `i ∈ ℤ`, then `K` is zero on an open neighbourhood of
`x`: every cohomology sheaf of `K` has vanishing stalk at every point of that neighbourhood. -/
@[stacks 0G03 "part (2), for `X` a regular Noetherian scheme (a regular scheme of finite type \
over a field, the source's hypothesis, is one) and `K` perfect: `K` being zero in an open \
neighbourhood of `x` is read as the vanishing of every cohomology stalk at every point of the \
neighbourhood"]
theorem exists_mem_forall_stalkHomology_isZero_of_pointSheaf_hom_shift (hX : IsRegular X)
    [IsNoetherian X] (hx : IsClosed ({x} : Set X)) (K : DerivedCategory X.Modules)
    (hK : IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ i : ℤ, Subsingleton (pointSheaf X x ⟶ K⟦i⟧)) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :=
  exists_mem_forall_isZero_stalkObj_of_isZero_derivedStalk X x K hK
    (isZero_derivedStalk_of_forall_pointSheaf_hom_shift X x hX hx K hK h)

/-- **[Stacks, Tag 0G03] part (2), globally**: on a regular Noetherian scheme, a perfect complex
`K` with `Hom(𝒪_x, K[i]) = 0` for every closed point `x` and every `i ∈ ℤ` is zero. -/
theorem isZero_of_forall_pointSheaf_hom_shift (hX : IsRegular X) [IsNoetherian X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∀ i : ℤ, Subsingleton (pointSheaf X x ⟶ K⟦i⟧)) :
    IsZero K :=
  isZero_of_forall_isClosed_isZero_derivedStalk X K hK fun x hx =>
    isZero_derivedStalk_of_forall_pointSheaf_hom_shift X x hX hx K hK (h x hx)

/-- **[Stacks, Tag 0G03] part (2), globally, in `D_perf(𝒪_X)`**: on a regular Noetherian scheme, a
perfect complex receiving no nonzero map from any shift of any closed-point skyscraper is zero.
This is hypothesis (2) of [Stacks, Tag 0G24] in
`fullyFaithful_iff_bijective_ext_perfectPointSheaf`. -/
theorem isZero_of_forall_perfectPointSheaf_hom_shift (hX : IsRegular X) [IsNoetherian X]
    (K : PerfectDerivedCategory X)
    (h : ∀ (x : X) (hx : IsClosed ({x} : Set X)) (i : ℤ),
      Subsingleton (perfectPointSheaf X hX x hx ⟶ K⟦i⟧)) :
    IsZero K := by
  have hK : IsZero K.obj := isZero_of_forall_pointSheaf_hom_shift X hX K.obj K.property
    fun x hx i => @Function.Injective.subsingleton _ _ _
      (perfectHomShiftEquiv X (perfectPointSheaf X hX x hx) K i).symm.injective (h x hx i)
  exact IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) K hK

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
