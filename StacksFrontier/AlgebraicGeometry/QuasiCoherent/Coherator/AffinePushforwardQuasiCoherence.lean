module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardBounds

/-!
# The derived direct image along an affine morphism has quasi-coherent cohomology

Let `f : X ⟶ Y` be an affine morphism of schemes and let `E` be an object of `D(𝒪_X)` whose
cohomology sheaves are quasi-coherent. Then every cohomology sheaf of `Rf_*E` is quasi-coherent.
This is part (1) of [Stacks, Tag 08D5] for an affine morphism.

## Main results

* `Stacks.SmallDerivedCategory.isGE_obj_of_isGE` — a total right derived functor computed by the
  K-injective complexes preserves lower cohomological bounds.
* `Stacks.SmallDerivedCategory.prop_homologyFunctor_obj_singleFunctor_obj` — the cohomology of
  such a functor at a single object placed in one degree inherits any isomorphism-closed property
  of the higher right derived functors of the underlying functor.
* `AlgebraicGeometry.isGE_derivedPushforward_obj` — `Rf_*` preserves lower cohomological bounds,
  for an arbitrary morphism of schemes.
* `AlgebraicGeometry.isIso_homologyFunctor_map_derivedPushforward_truncLEι` — **[Stacks, Tag
  08D4] part (1) at `Rf_*`:** `H^i(Rf_*(τ_{≤ a}E)) ⟶ H^i(Rf_*E)` is invertible for `i ≤ a`, for
  an arbitrary morphism of schemes.
* `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward_singleFunctor_obj` — the
  cohomology sheaves of `Rf_*` of a quasi-coherent sheaf placed in one degree are quasi-coherent,
  for `f` affine.
* `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom` —
  **[Stacks, Tag 08D5] part (1) for an affine morphism.**

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit isIso_derivedPushforwardUnit_app_of_isKInjective)
open Stacks.Cohomology.Affine.HigherDirectImage
  (isQuasicoherent_rightDerivedPlus_pushforward_of_isAffineHom)

universe u

namespace Stacks.SmallDerivedCategory

/-! ### Two general facts about a right derived functor computed by K-injective complexes -/

section KInjectiveComputation

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
    IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))

include hcomp in
/-- **[Stacks, Tag 05TC] part (1) for an unbounded right derived functor.** If the structure map
`β` of `(R, β)` is invertible at every K-injective complex and `E` lives in degrees `≥ a`, then so
does `R(E)`. -/
public theorem isGE_obj_of_isGE (E : DerivedCategory A) (a : ℤ) (hE : E.IsGE a) :
    (R.obj E).IsGE a := by
  let E' : DerivedCategory.Plus A := ⟨E, ⟨a, hE⟩⟩
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    F R β hcomp E' a hE
  have h : DerivedCategory.TStructure.t.IsGE (F.rightDerivedFunctorPlus.obj E').obj a :=
    (DerivedCategory.Plus.isGE_ι_obj_iff (F.rightDerivedFunctorPlus.obj E') a).2
      (@Functor.isGE_rightDerivedFunctorPlus_obj _ _ _ _ _ _ _ _ F _ _ E' a
        ((DerivedCategory.Plus.isGE_ι_obj_iff E' a).1 hE))
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a

include hcomp in
/-- **The cohomology of `R` at a single object placed in one degree is a higher right derived
functor of `F`.** If every `R^pF(M)` has an isomorphism-closed property `Q`, then so does
`H^i(R(M[-n]))`, for every `n` and `i`. -/
public theorem prop_homologyFunctor_obj_singleFunctor_obj [R.CommShift ℤ]
    (Q : ObjectProperty B) [Q.IsClosedUnderIsomorphisms] (M : A)
    (hM : ∀ p : ℤ, Q ((F.rightDerivedPlus p).obj M)) (n i : ℤ) :
    Q ((DerivedCategory.homologyFunctor B i).obj
      (R.obj ((DerivedCategory.singleFunctor A n).obj M))) := by
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    F R β hcomp ((DerivedCategory.Plus.singleFunctor A 0).obj M) 0 (by
      show ((DerivedCategory.singleFunctor A 0).obj M).IsGE 0
      infer_instance)
  have eshift : R.obj ((DerivedCategory.singleFunctor A n).obj M) ≅
      (R.obj ((DerivedCategory.singleFunctor A 0).obj M))⟦-n⟧ :=
    (R.mapIso (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app M)).symm ≪≫
      ((R.commShiftIso (-n)).app ((DerivedCategory.singleFunctor A 0).obj M))
  exact Q.prop_of_iso (((DerivedCategory.homologyFunctor B (-n + i)).mapIso e).symm ≪≫
    (((DerivedCategory.homologyFunctor B 0).shiftIso (-n) i (-n + i) rfl).app _).symm ≪≫
    (DerivedCategory.homologyFunctor B i).mapIso eshift.symm) (hM (-n + i))

end KInjectiveComputation

end Stacks.SmallDerivedCategory

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnboundedHigherDirectImage.isGrothendieckAbelian_moduleSheaves

variable {X Y : Scheme.{u}}

/-! ### Lower cohomological bounds for the derived direct image -/

/-- **The derived direct image preserves lower cohomological bounds.** For any morphism of
schemes `f` and any object `E` of `D(𝒪_X)` living in degrees `≥ a`, the object `Rf_*E` lives in
degrees `≥ a`. -/
public theorem isGE_derivedPushforward_obj (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (a : ℤ)
    (hE : E.IsGE a) : ((derivedPushforward f.toLRSHom.toShHom).obj E).IsGE a :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward f.toLRSHom.toShHom)
    (derivedPushforward f.toLRSHom.toShHom) (derivedPushforwardUnit f.toLRSHom.toShHom)
    (isIso_derivedPushforwardUnit_app_of_isKInjective f.toLRSHom.toShHom) E a hE

/-- **[Stacks, Tag 08D4] part (1) at the derived direct image.** For any morphism of schemes `f`
and any object `E` of `D(𝒪_X)`, the canonical map `H^i(Rf_*(τ_{≤ a}E)) ⟶ H^i(Rf_*E)` is an
isomorphism for every `i ≤ a`. -/
public theorem isIso_homologyFunctor_map_derivedPushforward_truncLEι (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (a i : ℤ)
    (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
      ((derivedPushforward f.toLRSHom.toShHom).map
        ((DerivedCategory.TStructure.t.truncLEι a).app E))) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X.toRingedSpace)
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f.toLRSHom.toShHom).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated
      (modulePushforward f.toLRSHom.toShHom) _ (derivedPushforwardUnit f.toLRSHom.toShHom)
  let T := (derivedPushforward f.toLRSHom.toShHom).mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E)
  have hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :=
    (derivedPushforward f.toLRSHom.toShHom).map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E)
  have hg : T.obj₃.IsGE (a + 1) :=
    isGE_derivedPushforward_obj f ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E) (a + 1)
      inferInstance
  have : Epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0)
        |>.homologySequence_epi_shift_map_mor₁_iff T hT i).2
      ((T.obj₃.isZero_of_isGE (a + 1) i (by omega)).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0)
        |>.homologySequence_mono_shift_map_mor₁_iff T hT (i - 1) i (by omega)).2
      ((T.obj₃.isZero_of_isGE (a + 1) (i - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₁)

/-! ### Quasi-coherence of the cohomology sheaves -/

/-- **The derived direct image of a quasi-coherent sheaf placed in one degree.** For `f` affine
and `M` a quasi-coherent `𝒪_X`-module, every cohomology sheaf of `Rf_*(M[-n])` is
quasi-coherent. -/
public theorem isQuasicoherent_homologyFunctor_derivedPushforward_singleFunctor_obj (f : X ⟶ Y)
    [IsAffineHom f] (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : M.IsQuasicoherent) (n i : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj
            M))).IsQuasicoherent := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X.toRingedSpace)
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) ℤ
  exact Stacks.SmallDerivedCategory.prop_homologyFunctor_obj_singleFunctor_obj
    (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (isIso_derivedPushforwardUnit_app_of_isKInjective f.toLRSHom.toShHom)
    (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)) M
    (fun p => @isQuasicoherent_rightDerivedPlus_pushforward_of_isAffineHom X Y f M ‹_› hM p) n i

/-- **[Stacks, Tag 08D5] part (1) for an affine morphism.** Let `f : X ⟶ Y` be an affine morphism
of schemes and let `E` be an object of `D(𝒪_X)` whose cohomology sheaves are quasi-coherent. Then
every cohomology sheaf of `Rf_*E` is quasi-coherent; that is, `Rf_*` carries `D_QCoh(𝒪_X)` into
`D_QCoh(𝒪_Y)`. -/
public theorem isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom (f : X ⟶ Y)
    [IsAffineHom f] (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj E)).IsQuasicoherent := by
  have hP := containsZero_isQuasicoherent X
  let PX := SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)
  let PY := SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)
  let E₁ := (DerivedCategory.TStructure.t.truncGE i).obj E
  have hcoh₁ : ∀ j : ℤ, PX ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E₁) := fun j =>
    @Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj _ _ _ _ PX _ hP E hcoh i j
  let E₂ := (DerivedCategory.TStructure.t.truncLE i).obj E₁
  have hcoh₂ : ∀ j : ℤ, PX ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E₂) := fun j =>
    @Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj _ _ _ _ PX _ hP E₁ hcoh₁ i j
  have _ : E₂.IsGE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsGE i)
  have _ : E₂.IsLE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsLE i)
  obtain ⟨M, ⟨e⟩⟩ := E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i
  have hM : M.IsQuasicoherent := PX.prop_of_iso
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).app M) (hcoh₂ i)
  have transfer : ∀ {A B : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))} (φ : A ⟶ B)
      [IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((derivedPushforward f.toLRSHom.toShHom).map φ))],
      PY ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj A)) ↔
      PY ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj B)) := fun φ _ =>
    let e := asIso ((DerivedCategory.homologyFunctor _ i).map
      ((derivedPushforward f.toLRSHom.toShHom).map φ))
    ⟨PY.prop_of_iso e, PY.prop_of_iso e.symm⟩
  have hι := isIso_homologyFunctor_map_derivedPushforward_truncLEι f E₁ i i le_rfl
  have hπ := isIso_homologyFunctor_map_derivedPushforward_truncGEπ f E hcoh i i le_rfl
  exact (transfer ((DerivedCategory.TStructure.t.truncGEπ i).app E)).2
    ((transfer ((DerivedCategory.TStructure.t.truncLEι i).app E₁)).1 ((transfer e.hom).2
    (isQuasicoherent_homologyFunctor_derivedPushforward_singleFunctor_obj f M hM i i)))

end AlgebraicGeometry

end
