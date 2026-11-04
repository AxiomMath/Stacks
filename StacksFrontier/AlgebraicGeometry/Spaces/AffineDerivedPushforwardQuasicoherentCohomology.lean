module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardUpperBound
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# The derived direct image along an affine morphism of algebraic spaces preserves `D_QCoh`

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` and let `E` be an
object of `D(𝒪_X)` whose cohomology sheaves are quasi-coherent. Then every cohomology sheaf of
`Rf_*E` is quasi-coherent: `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. This is part (1) of
[Stacks, Tag 08D5] for an affine morphism, transported to algebraic spaces; it is what makes the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` in [Stacks, Tag 0E58] and
[Stacks, Tag 0GG3] meaningful for an affine morphism.

The argument is the one of
`AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom` for schemes,
read in a single degree `i`:

* from above, `H^i(Rf_*(τ_{≤ i}F)) ≅ H^i(Rf_*F)` for every `F`, because `Rf_*` preserves lower
  cohomological bounds (the K-injective complexes compute it);
* from below, `H^i(Rf_*E) ≅ H^i(Rf_*(τ_{≥ i}E))`, because `Rf_*(τ_{≤ i - 1}E)` lives in degrees
  `≤ i - 1` — the upper bound
  `AlgebraicGeometry.Space.isLE_derivedModulePushforward_obj_of_isAffineHom`, part (2) of
  [Stacks, Tag 08D5] for an affine morphism of algebraic spaces;
* and on a quasi-coherent sheaf `M` placed in one degree `Rf_*` is `f_*M` placed in that degree,
  because a complex of quasi-coherent modules computes its own derived direct image
  (`AlgebraicGeometry.Space.isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite`),
  and `f_*M` is quasi-coherent ([Stacks, Tag 07U8]).

## Main results

* `AlgebraicGeometry.Space.isGE_obj_of_isRightDerivedFunctor_modulePushforward` — `Rf_*` preserves
  lower cohomological bounds.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homologyFunctor_derivedPushforward_of_isAffineHom`
  — **`Rf_*` preserves `D_QCoh` along an affine morphism.**

## Implementation notes

`Rf_*` is an arbitrary total right derived functor `(Rf, α)` of the direct image of modules, as in
`AlgebraicGeometry.Space.isLE_derivedModulePushforward_obj_of_isAffineHom`, whose statement is at
the standard derived category `CategoryTheory.HasDerivedCategory.standard`; the statements here
are at the same derived category, so that they compose with it.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0E58](https://stacks.math.columbia.edu/tag/0E58)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

/-- The derived categories of the `𝒪`-modules of algebraic spaces used here are the standard
ones, those at which `AlgebraicGeometry.Space.isLE_derivedModulePushforward_obj_of_isAffineHom`
is stated. -/
abbrev spaceModulesHasDerivedCategory (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasDerivedCategory (Modules.{u, u} B S hS F hF) :=
  HasDerivedCategory.standard _

attribute [local instance] spaceModulesHasDerivedCategory
attribute [local instance] enoughInjectives_modules_ringUniverse
attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
attribute [local instance 5000] modulePushforward_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  [Rf.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]

include α in
/-- **`Rf_*` preserves lower cohomological bounds**, for every morphism of algebraic spaces. -/
theorem isGE_obj_of_isRightDerivedFunctor_modulePushforward
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a : ℤ) (hE : E.IsGE a) :
    (Rf.obj E).IsGE a :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward B S hS f) Rf α
    (fun I hI => isIso_app_of_isKInjective_modulePushforward B S hS f DerivedCategory.Qh Rf α I hI)
    E a hE

include α in
/-- `Rf_*` is a triangulated functor. -/
theorem isTriangulated_of_isRightDerivedFunctor_modulePushforward :
    letI := Functor.IsRightDerivedFunctor.commShift Rf α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
    Rf.IsTriangulated :=
  Stacks.Injectives.rightDerivedFunctor_isTriangulated (modulePushforward B S hS f) Rf α

include α in
/-- **[Stacks, Tag 08D4] part (1) at `Rf_*`:** `H^i(Rf_*(τ_{≤ a}E)) ⟶ H^i(Rf_*E)` is invertible
for `i ≤ a`. -/
theorem isIso_homologyFunctor_map_truncLEι_of_isRightDerivedFunctor
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map
      (Rf.map ((DerivedCategory.TStructure.t.truncLEι a).app E))) := by
  let := Functor.IsRightDerivedFunctor.commShift Rf α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : Rf.IsTriangulated :=
    isTriangulated_of_isRightDerivedFunctor_modulePushforward B S hS f Rf α
  let T := Rf.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E)
  have hT : T ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :=
    Rf.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E)
  have hg : T.obj₃.IsGE (a + 1) :=
    isGE_obj_of_isRightDerivedFunctor_modulePushforward B S hS f Rf α
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E) (a + 1) inferInstance
  have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj T.obj₃) :=
    T.obj₃.isZero_of_isGE (a + 1) i (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor _ (i - 1)).obj T.obj₃) :=
    T.obj₃.isZero_of_isGE (a + 1) (i - 1) (by omega)
  have : Epi ((DerivedCategory.homologyFunctor _ i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor _ 0).homologySequence_epi_shift_map_mor₁_iff
      T hT i).2 (hz.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor _ i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor _ 0).homologySequence_mono_shift_map_mor₁_iff
      T hT (i - 1) i (by omega)).2 (hz'.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ i).map T.mor₁)

include α in
/-- **[Stacks, Tag 08D4] part (2) at `Rf_*`, for an affine morphism:**
`H^i(Rf_*E) ⟶ H^i(Rf_*(τ_{≥ i}E))` is invertible when `E` has quasi-coherent cohomology. -/
theorem isIso_homologyFunctor_map_truncGEπ_of_isAffineHom (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) i).obj E).IsQuasicoherentOnSite) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map
      (Rf.map ((DerivedCategory.TStructure.t.truncGEπ i).app E))) := by
  let := Functor.IsRightDerivedFunctor.commShift Rf α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : Rf.IsTriangulated :=
    isTriangulated_of_isRightDerivedFunctor_modulePushforward B S hS f Rf α
  let T := Rf.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE (i - 1) i
    (by omega)).obj E)
  have hT : T ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :=
    Rf.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (i - 1) i (by omega) E)
  have hcoh₁ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) j).obj
      ((DerivedCategory.TStructure.t.truncLE (i - 1)).obj E)).IsQuasicoherentOnSite := fun j =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj
      (P := SheafOfModules.isQuasicoherentOnSite _) E hcoh (i - 1) j
  have hl : T.obj₁.IsLE (i - 1) :=
    isLE_derivedModulePushforward_obj_of_isAffineHom B S hS f hf Rf α _ hcoh₁ (i - 1)
      inferInstance
  have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj T.obj₁) :=
    T.obj₁.isZero_of_isLE (i - 1) i (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor _ (i + 1)).obj T.obj₁) :=
    T.obj₁.isZero_of_isLE (i - 1) (i + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor _ i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor _ 0).homologySequence_mono_shift_map_mor₂_iff
      T hT i).2 (hz.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor _ i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor _ 0).homologySequence_epi_shift_map_mor₂_iff
      T hT i (i + 1) (by omega)).2 (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ i).map T.mor₂)

/-- Every term of a quasi-coherent module placed in one degree is quasi-coherent. -/
theorem isQuasicoherentOnSite_singleFunctor_obj_X {Z : AlgebraicSpaces B S hS} (n : ℤ)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (hM : M.IsQuasicoherentOnSite) (k : ℤ) :
    (((CochainComplex.singleFunctor (Modules.{u, u} B S hS Z.1 Z.2) n).obj M).X
      k).IsQuasicoherentOnSite := by
  by_cases hk : k = n
  · subst hk
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k M).symm hM
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n M k hk)

include α in
/-- **`Rf_*` of a quasi-coherent sheaf placed in one degree, along an affine morphism**, has
quasi-coherent cohomology sheaves: it is `f_*M` placed in that degree. -/
theorem isQuasicoherentOnSite_homologyFunctor_obj_singleFunctor_of_isAffineHom
    (hf : IsAffineHom B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (n i : ℤ) :
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
      (Rf.obj ((DerivedCategory.singleFunctor _ n).obj M))).IsQuasicoherentOnSite := by
  let K := (CochainComplex.singleFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj M
  have hK := isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite B S hS f hf Rf α K
    (isQuasicoherentOnSite_singleFunctor_obj_X B S hS n M hM)
  have e₁ : Rf.obj ((DerivedCategory.singleFunctor _ n).obj M) ≅
      DerivedCategory.Q.obj (((modulePushforward B S hS f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    Rf.mapIso (((DerivedCategory.singleFunctorIsoCompQ _ n).app M) ≪≫
        ((DerivedCategory.quotientCompQhIso _).app K).symm) ≪≫
      (asIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  have e₂ : ((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      (CochainComplex.singleFunctor _ n).obj ((modulePushforward B S hS f).obj M) :=
    (HomologicalComplex.singleMapHomologicalComplex (modulePushforward B S hS f)
      (ComplexShape.up ℤ) n).app M
  have hpush := pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf M hM
  refine (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso (e₁ ≪≫ DerivedCategory.Q.mapIso e₂ ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (Modules.{u, u} B S hS Y.1 Y.2) n).app
        ((modulePushforward B S hS f).obj M)).symm)).symm ?_
  by_cases hin : i = n
  · subst hin
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app _).symm hpush
  · refine SheafOfModules.IsQuasicoherentOnSite.of_isZero ?_
    rcases lt_or_gt_of_ne hin with h | h
    · exact DerivedCategory.isZero_of_isGE _ n i h
    · exact DerivedCategory.isZero_of_isLE _ n i h

include α in
/-- **[Stacks, Tag 08D5] part (1) for an affine morphism of algebraic spaces.** Let
`f : X ⟶ Y` be an affine morphism of algebraic spaces and let `E` be an object of `D(𝒪_X)` whose
cohomology sheaves are quasi-coherent. Then every cohomology sheaf of `Rf_*E` is quasi-coherent;
that is, `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. -/
theorem isQuasicoherentOnSite_homologyFunctor_derivedPushforward_of_isAffineHom
    (hf : IsAffineHom B S hS f.hom) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) i).obj E).IsQuasicoherentOnSite) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
      (Rf.obj E)).IsQuasicoherentOnSite := by
  let PX := SheafOfModules.isQuasicoherentOnSite
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let PY := SheafOfModules.isQuasicoherentOnSite
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  let E₁ := (DerivedCategory.TStructure.t.truncGE i).obj E
  have hcoh₁ : ∀ j : ℤ, PX ((DerivedCategory.homologyFunctor _ j).obj E₁) := fun j =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj (P := PX) E hcoh i j
  let E₂ := (DerivedCategory.TStructure.t.truncLE i).obj E₁
  have hcoh₂ : ∀ j : ℤ, PX ((DerivedCategory.homologyFunctor _ j).obj E₂) := fun j =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj (P := PX) E₁ hcoh₁ i j
  have _ : E₂.IsGE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsGE i)
  have _ : E₂.IsLE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsLE i)
  obtain ⟨M, ⟨e⟩⟩ := E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i
  have hM : M.IsQuasicoherentOnSite := PX.prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app M) (hcoh₂ i)
  have h₂ : PY ((DerivedCategory.homologyFunctor _ i).obj (Rf.obj E₂)) :=
    PY.prop_of_iso (((DerivedCategory.homologyFunctor _ i).mapIso (Rf.mapIso e)).symm)
      (isQuasicoherentOnSite_homologyFunctor_obj_singleFunctor_of_isAffineHom B S hS f Rf α hf
        M hM i i)
  have hι := isIso_homologyFunctor_map_truncLEι_of_isRightDerivedFunctor B S hS f Rf α E₁ i i
    le_rfl
  have h₁ : PY ((DerivedCategory.homologyFunctor _ i).obj (Rf.obj E₁)) :=
    PY.prop_of_iso (asIso ((DerivedCategory.homologyFunctor _ i).map
      (Rf.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁)))) h₂
  have hπ := isIso_homologyFunctor_map_truncGEπ_of_isAffineHom B S hS f Rf α hf E hcoh i
  exact PY.prop_of_iso (asIso ((DerivedCategory.homologyFunctor _ i).map
    (Rf.map ((DerivedCategory.TStructure.t.truncGEπ i).app E)))).symm h₁

end AlgebraicGeometry.Space

end
