module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.Homology.DerivedCategory.IsZero
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image along an affine morphism of algebraic spaces reflects isomorphisms

Let `S` be a scheme and let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S`.
[Stacks, Tag 08II] asserts that `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` reflects isomorphisms.  This
file proves it, together with the t-exactness statement it rests on: for `E` in `D_QCoh(𝒪_X)`,
`H^i(Rf_*E) ≅ f_*H^i(E)` in every degree, with no boundedness hypothesis on `E`.

## Main results

* `AlgebraicGeometry.Space.homologyDerivedModulePushforwardIsoOfIsAffineHom`:
  `H^i(Rf_*E) ≅ f_*H^i(E)` for `E` in `D_QCoh(𝒪_X)` and `f` affine.
* `AlgebraicGeometry.Space.affineQuasicoherentDerivedPushforward`: the restriction
  `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.
* `AlgebraicGeometry.Space.isIso_of_isIso_derivedModulePushforward_map_of_isAffineHom`: a morphism
  of `D(𝒪_X)` between objects with quasi-coherent cohomology sheaves is invertible once its image
  under `Rf_*` is.
* `AlgebraicGeometry.Space.reflectsIsomorphisms_affineQuasicoherentDerivedPushforward`:
  **[Stacks, Tag 08II]**, with no hypothesis beyond the source's.

## Proof

The source checks the assertion on cohomology sheaves, localizes on `Y` to an affine target and
reads the affine case off the case of schemes ([Stacks, Tag 08I8]) through
[Stacks, Tag 071Q] and [Stacks, Remark 08GH].  Here the argument the library uses for
[Stacks, Tag 08I8] itself
(`Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isIso_of_isIso_derivedPushforward`) is
run directly on the small étale site of `X`, so no comparison with schemes is needed.

*The cone.*  Quasi-coherence of modules on the small étale site of an algebraic space is a weak
Serre class (`AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass_schemeUniverse`), so
`D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)` and a morphism `E ⟶ F` of it has a cone
`C` in it.  `Rf_*` is triangulated, being a right derived functor out of a Grothendieck abelian
category (`Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor`), so
`Rf_*C = 0` when `Rf_*` of the morphism is invertible.

*T-exactness.*  Fix `i` and cut `E` down to `H^i(E)[-i]` by the two canonical truncations,
neither of which changes `H^i(Rf_*-)`: from below because `Rf_*` does not raise cohomological
degree on `D_QCoh(𝒪_X)` for `f` affine
(`AlgebraicGeometry.Space.isLE_derivedModulePushforward_obj_of_isAffineHom`, part (2) of
[Stacks, Tag 08D5] with `N = 1`), from above because `Rf_*` does not lower it
(`Stacks.SmallDerivedCategory.isGE_obj_of_isGE`).  On a single quasi-coherent module a complex of
quasi-coherent modules computes its own derived direct image
(`AlgebraicGeometry.Space.isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite`,
[Stacks, Tag 0G9N] for an affine morphism, from [Stacks, Tag 073H]), so
`Rf_*(M[-i]) = (f_*M)[-i]`.

*Conservativity.*  `f_*` is conservative on quasi-coherent `𝒪_X`-modules
(`AlgebraicGeometry.Space.eq_zero_of_modulePushforward_map_eq_zero`, computed on affine étale
charts).  So each `f_*H^i(C) = H^i(Rf_*C)` vanishes, `C = 0`, and the morphism is invertible.

## Implementation notes

**`Rf_*` is a binder.**  As in the neighbouring [Stacks, Tag 08GY]
(`StacksFrontier/AlgebraicGeometry/Spaces/AffineDerivedQuasicoherentPushforward.lean`), the
statements are given for an arbitrary total right derived functor `Rf` of the direct image of
all modules, `AlgebraicGeometry.Space.modulePushforward`, together with its derivation unit `α`;
such a pair exists for every morphism of algebraic spaces, by
`AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward`, and the source's `Rf_*` is
one of them.

**The model of the derived categories.**  The upper bound of [Stacks, Tag 08D5] (2) and
[Stacks, Tag 0G9N] for an affine morphism of algebraic spaces, which the t-exactness consumes,
are available only at `CategoryTheory.HasDerivedCategory.standard`, so the statements here are
read at that model too, made a local instance at default priority exactly as in the file of
[Stacks, Tag 08GY] whose binder `Rf` they share.  The category `D_QCoh(𝒪_X)` is
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` ([Stacks, Tag 071X]) at module universe
`u`.

## References

* [Stacks Project, Tag 08II](https://stacks.math.columbia.edu/tag/08II)
* [Stacks Project, Tag 08I8](https://stacks.math.columbia.edu/tag/08I8)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_modules
attribute [local instance] enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The direct image along an affine morphism is conservative on quasi-coherent modules.** -/
theorem isZero_of_isZero_modulePushforward_obj_of_isAffineHom (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (h : IsZero ((modulePushforward B S hS f).obj M)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact eq_zero_of_modulePushforward_map_eq_zero f hf
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM) (𝟙 M)
    (h.eq_of_src _ _)

section Pushforward

variable (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
  (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  [Rf.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]

include hf in
/-- **The derived direct image of a quasi-coherent module placed in one degree** is its direct
image placed there: `(f_*M)[-n] ≅ Rf_*(M[-n])` for `f` affine and `M` quasi-coherent. -/
def rightDerivedModulePushforwardSingleIsoOfIsAffineHom (n : ℤ)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    (DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj
        ((modulePushforward B S hS f).obj M) ≅
      Rf.obj ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj M) :=
  let P := modulePushforward B S hS f
  let K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ :=
    (CochainComplex.singleFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj M
  have := isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite B S hS f hf Rf α K
    (isQuasicoherentOnSite_singleFunctor_obj_X B S hS n M hM)
  (DerivedCategory.singleFunctorIsoCompQ (Modules.{u, u} B S hS Y.1 Y.2) n).app (P.obj M) ≪≫
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) n).app M)).symm ≪≫
    ((DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS Y.1 Y.2)).app
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (DerivedCategory.Qh.mapIso ((P.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)).symm ≪≫
    asIso (α.app ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
      (ComplexShape.up ℤ)).obj K)) ≪≫
    Rf.mapIso ((DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS X.1 X.2)).app K ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (Modules.{u, u} B S hS X.1 X.2) n).app M).symm)

/-- The cohomology sheaves of the derived direct image of a quasi-coherent module placed in
degree `n`: `H^n(Rf_*(M[-n])) ≅ f_*M`. -/
def homologyRightDerivedModulePushforwardSingleIsoOfIsAffineHom (n : ℤ)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj
        (Rf.obj ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj M)) ≅
      (modulePushforward B S hS f).obj M :=
  ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).mapIso
      (rightDerivedModulePushforwardSingleIsoOfIsAffineHom B S hS f hf Rf α n M hM)).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules.{u, u} B S hS Y.1 Y.2) n).app
      ((modulePushforward B S hS f).obj M)

include hf α in
/-- **`Rf_*` does not see a truncation from below in high degrees**, for `f` affine: for `E` in
`D_QCoh(𝒪_X)` the map `H^i(Rf_*E) ⟶ H^i(Rf_*(τ_{≥ b}E))` is invertible for `i ≥ b`.  The first
vertex of the image of the truncation triangle lies in degrees `≤ b - 1`, by the upper bound
`AlgebraicGeometry.Space.isLE_derivedModulePushforward_obj_of_isAffineHom`. -/
theorem isIso_homologyFunctor_map_derivedModulePushforward_truncGEπ
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) i).obj E).IsQuasicoherentOnSite)
    (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map
      (Rf.map ((DerivedCategory.TStructure.t.truncGEπ b).app E))) := by
  let _ := Functor.IsRightDerivedFunctor.commShift Rf α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : Rf.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS f) Rf α
  let T := Rf.mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E)
  have hT : T ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :=
    Rf.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E)
  have hl : T.obj₁.IsLE (b - 1) :=
    isLE_derivedModulePushforward_obj_of_isAffineHom B S hS f hf Rf α _
      (Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        E hcoh (b - 1)) (b - 1)
      (DerivedCategory.TStructure.t.isLE_truncLE_obj E (b - 1) (b - 1) le_rfl)
  have : Mono ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0
      ).homologySequence_mono_shift_map_mor₂_iff T hT i).2
        ((T.obj₁.isZero_of_isLE (b - 1) i (by omega)).eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0
      ).homologySequence_epi_shift_map_mor₂_iff T hT i (i + 1) rfl).2
        ((T.obj₁.isZero_of_isLE (b - 1) (i + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map T.mor₂)

include hf in
/-- **The derived direct image along an affine morphism commutes with cohomology on
`D_QCoh(𝒪_X)`**: `H^i(Rf_*E) ≅ f_*H^i(E)` for every `i`, with no boundedness hypothesis on
`E`. -/
def homologyDerivedModulePushforwardIsoOfIsAffineHom
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) i).obj E).IsQuasicoherentOnSite) (i : ℤ) :
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj (Rf.obj E) ≅
      (modulePushforward B S hS f).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E) := by
  let PA := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let HA := DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i
  let HB := DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i
  let E₁ := (DerivedCategory.TStructure.t.truncGE i).obj E
  have hcoh₁ : ∀ j : ℤ, PA ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) j).obj E₁) := fun j =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj PA E hcoh i j
  let E₂ := (DerivedCategory.TStructure.t.truncLE i).obj E₁
  have hcoh₂ : ∀ j : ℤ, PA ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) j).obj E₂) := fun j =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj PA E₁ hcoh₁ i j
  have _ : E₂.IsGE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsGE i)
  have _ : E₂.IsLE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsLE i)
  let M := (E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i).choose
  let e : E₂ ≅ (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj M :=
    (E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i).choose_spec.some
  let eM : HA.obj E₂ ≅ M := HA.mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules.{u, u} B S hS X.1 X.2) i).app M
  have hM : M.IsQuasicoherentOnSite := PA.prop_of_iso eM (hcoh₂ i)
  have hπ := isIso_homologyFunctor_map_derivedModulePushforward_truncGEπ B S hS f hf Rf α
    E hcoh i i le_rfl
  have hι :=
    isIso_homologyFunctor_map_truncLEι_of_isRightDerivedFunctor B S hS f Rf α E₁ i i le_rfl
  have hgπ := DerivedCategory.isIso_homologyFunctor_map_truncGEπ i i le_rfl E
  have hgι := Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_truncLEι E₁ i i le_rfl
  let eE : HA.obj E ≅ M :=
    asIso (HA.map ((DerivedCategory.TStructure.t.truncGEπ i).app E)) ≪≫
      (asIso (HA.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁))).symm ≪≫ eM
  exact asIso (HB.map (Rf.map ((DerivedCategory.TStructure.t.truncGEπ i).app E))) ≪≫
      (asIso (HB.map (Rf.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁)))).symm ≪≫
      HB.mapIso (Rf.mapIso e) ≪≫
      homologyRightDerivedModulePushforwardSingleIsoOfIsAffineHom B S hS f hf Rf α i M hM ≪≫
      ((modulePushforward B S hS f).mapIso eE).symm

include hf α in
/-- **The derived direct image along an affine morphism detects vanishing on `D_QCoh(𝒪_X)`.** If
`E` has quasi-coherent cohomology sheaves and `Rf_*E = 0`, then `E = 0`: each
`H^i(Rf_*E) = f_*H^i(E)` vanishes, and `f_*` is conservative on quasi-coherent modules. -/
theorem isZero_of_isZero_derivedModulePushforward_obj
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) i).obj E).IsQuasicoherentOnSite)
    (h : IsZero (Rf.obj E)) : IsZero E := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro i
  exact isZero_of_isZero_modulePushforward_obj_of_isAffineHom B S hS f hf _ (hcoh i)
    ((Functor.map_isZero _ h).of_iso
      (homologyDerivedModulePushforwardIsoOfIsAffineHom B S hS f hf Rf α E hcoh i).symm)

include hf α in
/-- **The derived direct image along an affine morphism reflects isomorphisms between objects of
`D_QCoh(𝒪_X)`**, stated on morphisms of `D(𝒪_X)`. -/
theorem isIso_of_isIso_derivedModulePushforward_map_of_isAffineHom
    {E F : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) i).obj E).IsQuasicoherentOnSite)
    (hF : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) i).obj F).IsQuasicoherentOnSite)
    (φ : E ⟶ F) (h : IsIso (Rf.map φ)) : IsIso φ := by
  let := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS X.1 X.2
  let _ := Functor.IsRightDerivedFunctor.commShift Rf α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : Rf.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS f) Rf α
  obtain ⟨C, hC, b, c, hT⟩ := ObjectProperty.distinguished_cocone_triangle
    (P := DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    φ hE hF
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_derivedModulePushforward_obj B S hS f hf Rf α C hC
      ((Triangle.isZero₃_iff_isIso₁ _ (Rf.map_distinguished _ hT)).2 h))

/-- **`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`** for an affine morphism `f`: the derived direct image
carries an object with quasi-coherent cohomology sheaves to one, because `H^i(Rf_*E) ≅ f_*H^i(E)`
(`AlgebraicGeometry.Space.homologyDerivedModulePushforwardIsoOfIsAffineHom`) and the direct image
of a quasi-coherent module along an affine morphism is quasi-coherent ([Stacks, Tag 07U8]). -/
def affineQuasicoherentDerivedPushforward :
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 :=
  (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).lift
    ((DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⋙ Rf)
    fun E i => (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).prop_of_iso
      (homologyDerivedModulePushforwardIsoOfIsAffineHom B S hS f hf Rf α E.obj E.property i).symm
      (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS f hf _
        (E.property i))

/-- **[Stacks, Tag 08II].**  Let `S` be a scheme and let `f : X ⟶ Y` be an affine morphism of
algebraic spaces over `S`.  Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` reflects isomorphisms.

Here `Rf_*` is any total right derived functor of the direct image of `𝒪_X`-modules, with its
derivation unit `α`, restricted to `D_QCoh` as
`AlgebraicGeometry.Space.affineQuasicoherentDerivedPushforward`.  The proof is
`AlgebraicGeometry.Space.isIso_of_isIso_derivedModulePushforward_map_of_isAffineHom`: the cone `C`
of a morphism `E ⟶ F` of `D_QCoh(𝒪_X)` lies in `D_QCoh(𝒪_X)`, `Rf_*C = 0` when `Rf_*` of the
morphism is invertible, and `H^i(Rf_*C) = f_*H^i(C)` with `f_*` conservative on quasi-coherent
modules forces `C = 0`. -/
@[stacks 08II]
theorem reflectsIsomorphisms_affineQuasicoherentDerivedPushforward :
    (affineQuasicoherentDerivedPushforward B S hS f hf Rf α).ReflectsIsomorphisms where
  reflects {E F} φ hφ := by
    let ιX := (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι
    let ιY := (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι
    have h : IsIso (Rf.map (ιX.map φ)) :=
      Functor.map_isIso ιY ((affineQuasicoherentDerivedPushforward B S hS f hf Rf α).map φ)
    have : IsIso (ιX.map φ) :=
      isIso_of_isIso_derivedModulePushforward_map_of_isAffineHom B S hS f hf Rf α
        E.property F.property (ιX.map φ) h
    exact isIso_of_reflects_iso φ ιX

end Pushforward

end AlgebraicGeometry.Space

end
