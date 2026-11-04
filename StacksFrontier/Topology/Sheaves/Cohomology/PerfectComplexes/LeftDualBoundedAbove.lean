module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualLocalRetract
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TotalComplexMono
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTermsSurjective

/-!
# Objects with a left dual are locally bounded above

An object `M` of the derived category `D(O_X)` of a ringed space `X` that has a left dual is,
locally on `X`, concentrated in degrees `≤ b` for some `b`.

## Main results

* `DerivedCategory.isLE_of_retract`: A retract of an object concentrated in degrees `≤ n` is
  concentrated in degrees `≤ n`.
* `Stacks.Cohomology.LeftDualPerfect.exists_isLE_restrict`: If `M` has a left dual, then every
  point has an open neighbourhood over which `M` is bounded above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open TopologicalSpace Opposite Stacks.SheafOfModules.DerivedMonoidal
open Stacks.Cohomology.MonoidalDerived
open Stacks.Cohomology.MonoidalComplexes

universe u d d'

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A retract of an object of `D(C)` concentrated in degrees `≤ n` is concentrated in degrees
`≤ n`. -/
theorem isLE_of_retract {A B : DerivedCategory C} (r : Retract A B) (n : ℤ) (hB : B.IsLE n) :
    A.IsLE n := by
  rw [isLE_iff] at hB ⊢
  intro i hi
  have r' := r.map (homologyFunctor C i)
  rw [IsZero.iff_id_eq_zero, ← r'.retract, (hB i hi).eq_of_src r'.r 0, comp_zero]

end DerivedCategory

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor carries a complex concentrated in degrees `≤ n` to an object of the derived
category concentrated in degrees `≤ n`. -/
theorem isLE_mapDerivedCategory_obj_Q_obj (K : CochainComplex A ℤ) (n : ℤ)
    [K.IsStrictlyLE n] : (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)).IsLE n := by
  have : CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n :=
    inferInstance
  have h : (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).IsLE n :=
    inferInstance
  rw [DerivedCategory.isLE_iff] at h ⊢
  exact fun i hi => (h i hi).of_iso ((DerivedCategory.homologyFunctor B i).mapIso
    (F.mapDerivedCategoryFactors.app K))

end CategoryTheory.Functor

namespace Stacks.Cohomology.LeftDualPerfect

variable (X : RingedSpace.{u, u})

/-- The first coordinates of the elements of a finite set of pairs `(i, j)` with `i + j = 0` are
bounded above. -/
theorem exists_bound_of_finset (S : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = 0}) :
    ∃ c : ℤ, ∀ ij ∈ S, ij.1.1 ≤ c :=
  ⟨S.sum fun ij => |ij.1.1|, fun _ hij => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = 0} => |ij.1.1|)
      (fun _ _ => abs_nonneg _) hij)⟩

/-- **The first truncation of the proof of Stacks 0FPD.** If `M` has a left dual in `D(O_X)`,
then every point has an open neighbourhood over which `M` is concentrated in degrees `≤ b` for
some `b`: `M|_U` is a retract of the canonical truncation `τ_{≤ b} M^•|_U` of a K-flat
representative. -/
theorem exists_isLE_restrict [HasDerivedCategory.{d} (Mod X.sheaf)]
    [∀ W : Opens X, HasDerivedCategory.{d'} (Mod (X.restrict W.isOpenEmbedding).sheaf)]
    (M N : DerivedModules X.sheaf)
    (pair : letI := derivedCategoryMonoidalCategory X; ExactPairing M N) (x : X) :
    ∃ V : Opens X, x ∈ V ∧ ∃ b : ℤ, ((restrictMod X V).mapDerivedCategory.obj M).IsLE b := by
  obtain ⟨Mc, pM, hMk, -, hpM, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution X
      (DerivedCategory.Q.objPreimage M)
  obtain ⟨Nc, pN, hNk, hNflat, hpN, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution X
      (DerivedCategory.Q.objPreimage N)
  have : IsIso (DerivedCategory.Q.map pM) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := Mod X.sheaf) pM).2 hpM
  have : IsIso (DerivedCategory.Q.map pN) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := Mod X.sheaf) pN).2 hpN
  obtain ⟨U, hxU, S, n, a, hR⟩ := exists_local_retract X M N pair Mc Nc
    (asIso (DerivedCategory.Q.map pM) ≪≫ DerivedCategory.Q.objObjPreimageIso M)
    (asIso (DerivedCategory.Q.map pN) ≪≫ DerivedCategory.Q.objObjPreimageIso N) hMk hNk x
  obtain ⟨c, hc⟩ := exists_bound_of_finset S
  refine ⟨U, hxU, c + 1, ?_⟩
  let := cochainComplexMonoidalCategory X
  set ι := Mc.ιTruncLE (c + 1)
  have : Mono ((ι ▷ Nc).f 1) := mono_mapBifunctorMap_f (R := X.sheaf) ι hNflat 1
  have hiso : ∀ (ij : S), IsIso (ι.f ij.1.1.1) := fun ij =>
    CochainComplex.isIso_ιTruncLE_f Mc (c + 1) _ (by have := hc ij.1 ij.2; omega)
  obtain ⟨r⟩ := hR U le_rfl (Mc.truncLE (c + 1)) ι fun ij k =>
    ⟨(@inv _ _ _ _ (ι.f _) (hiso ij)).val.app _ (res _ _ (a ij k)),
      congrArg (fun ψ => ψ.val.app _ (res _ (le_topOpen_of_le X le_rfl) (a ij k)))
        (@IsIso.inv_hom_id _ _ _ _ _ (hiso ij))⟩
  exact DerivedCategory.isLE_of_retract r _
    ((restrictMod X U).isLE_mapDerivedCategory_obj_Q_obj (Mc.truncLE (c + 1)) (c + 1))

end Stacks.Cohomology.LeftDualPerfect
