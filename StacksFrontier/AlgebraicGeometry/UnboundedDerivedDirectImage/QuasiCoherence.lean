module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.DerivedBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QcqsQuasiCoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.UniformBound
import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded derived direct image preserves quasi-coherent cohomology

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. Then `Rf_*` carries
`D_QCoh(𝒪_X)` into `D_QCoh(𝒪_S)`: the cohomology sheaves of `Rf_*E` are quasi-coherent whenever
those of `E` are. This is [Stacks, Tag 08D5] part (1).

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_derivedPushforward_singleFunctor` — the case of a
  quasi-coherent module placed in a single degree.
* `AlgebraicGeometry.isQuasicoherent_homology_derivedPushforward_of_bounded` — the case of a
  bounded object.
* `AlgebraicGeometry.isQuasicoherent_derivedPushforward_affineLocal` — **[Stacks, Tag 08D5]
  part (1)**, proved by the affine-local reduction.

## Implementation notes

The dévissage is the one of the source, in three steps.

*A single degree.* On a bounded below object the unbounded derived direct image agrees with the
bounded below one (`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`,
the K-injective complexes computing both), and there the cohomology of `Rf_*` of a module is its
higher direct image, which is quasi-coherent by [Stacks, Tag 01XJ]. The degree is moved by the
shift, under which `D_QCoh(𝒪_S)` is stable.

*A bounded object.* Induction on the length of the window. The canonical truncation triangle of
[Stacks, Tag 08J5] splits off one degree at a time, `Rf_*` is exact, and `D_QCoh(𝒪_S)` is a
triangulated subcategory of `D(𝒪_S)` — the quasi-coherent modules being a weak Serre subcategory
(`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre`) — so the middle
vertex of the image triangle has quasi-coherent cohomology once the two others do.

*An arbitrary object.* Fix a degree `n`. Truncating from above costs nothing in that degree, by
[Stacks, Tag 08D4] part (1), which carries no vanishing hypothesis and may therefore be used with
target the `𝒪_S`-modules. Truncating from below costs nothing either, once the truncation is deep
enough: by `AlgebraicGeometry.exists_isZero_homology_derivedPushforward` the part cut off has
`Rf_*` concentrated in degrees `≥ a - 1 + N`, which the long exact homology sequence of the
truncation triangle turns into an isomorphism in degree `n` as soon as `a ≤ n + 1 - N`. What is
left is bounded.

The question is local on `S` — that is
`AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_affineTarget`, which reduces it to an
affine target — so the quasi-compactness of `S` that the uniform bound needs is not a hypothesis
of the final statement.

Every imported statement used here — [Stacks, Tag 08D4], the convergence of the tower of
truncations it rests on, and the affine-locality of quasi-coherence — is baked at
`CategoryTheory.HasDerivedCategory.standard`, so that model is forced throughout. The locally
small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` arrives with the imports
as a competing instance, and an object of `D(𝒪_X)` taken at that model is not an object of the
same category; the standard model is therefore given a raised instance priority for this file.

The two spellings `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules (structureSheafRing X.toRingedSpace)` of the category of
`𝒪_X`-modules are definitionally equal but carry separately declared instances, and instance
search does not cross between them. `AlgebraicGeometry.derivedPushforwardModules` and its unit
fix the first spelling by a type ascription, which is what makes the statements of
[Stacks, Tag 08D4] applicable.

[Stacks, Tag 08D4] is stated with its source spelled `SheafOfModules X.ringCatSheaf`, so applying
it to `Rf_*` mixes the two spellings: the hypotheses that `f_*` is additive and that `Rf_*` is its
right derived functor are then asked for at a category spelled one way and an instance spelled the
other, and no instance can answer that — the mixed instance arguments come out of *unification*
with the type of `Rf_*`, not out of a search. The two applications below therefore name those two
hypotheses explicitly, which lets them be crossed by unification, where `Scheme.Modules` does
unfold.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry

universe u

-- Every imported statement used here is baked at `CategoryTheory.HasDerivedCategory.standard`,
-- and the locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`
-- arrives
-- with the imports as a competing instance of the same priority; raising the priority of the
-- standard model is what puts the two sides of every comparison below in one category.
attribute [local instance 2000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]

/-! ### The derived direct image read on `Scheme.Modules` -/

/-- **The unbounded derived direct image** `Rf_* : D(𝒪_X) ⥤ D(𝒪_S)`, read as a functor between
the derived categories of `AlgebraicGeometry.Scheme.Modules`.

This is `AlgebraicGeometry.RingedSpace.derivedPushforward` of the underlying morphism of ringed
spaces; the type ascription is the crossing between the two interchangeable spellings of the
category of modules on a scheme. -/
abbrev derivedPushforwardModules : DerivedCategory X.Modules ⥤ DerivedCategory S.Modules :=
  RingedSpace.derivedPushforward f.toLRSHom.toShHom

/-- The canonical comparison from degreewise pushforward to `derivedPushforwardModules`. -/
abbrev derivedPushforwardModulesUnit :
    (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedPushforwardModules f :=
  RingedSpace.derivedPushforwardUnit f.toLRSHom.toShHom

/-- `derivedPushforwardModules` is a right derived functor of degreewise pushforward. -/
instance derivedPushforwardModules_isRightDerivedFunctor :
    (derivedPushforwardModules f).IsRightDerivedFunctor (derivedPushforwardModulesUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  RingedSpace.derivedPushforward_isRightDerivedFunctor f.toLRSHom.toShHom

/-- The unbounded derived direct image commutes with the shift, by the universal property of a
right derived functor. -/
instance derivedPushforwardModules_commShift : (derivedPushforwardModules f).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _ (derivedPushforwardModulesUnit f)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ

/-- The unbounded derived direct image is an exact functor of triangulated categories: it is a
total right derived functor out of the homotopy category of a Grothendieck abelian category. -/
instance derivedPushforwardModules_isTriangulated :
    (derivedPushforwardModules f).IsTriangulated :=
  Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
    (Scheme.Modules.pushforward f) (derivedPushforwardModules f)
    (derivedPushforwardModulesUnit f)

/-! ### A module in a single degree -/

/-- **The derived direct image of a quasi-coherent module in degree zero has quasi-coherent
cohomology.** On a bounded below object the unbounded derived direct image agrees with the bounded
below one, and the cohomology of that is the higher direct image, which is quasi-coherent by
[Stacks, Tag 01XJ]. -/
theorem isQuasicoherent_homology_derivedPushforward_single_zero (M : X.Modules)
    (hM : M.IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor S.Modules i).obj
      ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj M))).IsQuasicoherent := by
  have : M.IsQuasicoherent := hM
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f) (derivedPushforwardModules f)
    (derivedPushforwardModulesUnit f)
    (fun I hI ↦ @isIso_app_isKInjective_of_isRightDerivedFunctor X _ _ _ _ _
      (Scheme.Modules.pushforward f)
      (inferInstanceAs (Scheme.Modules.pushforward f).Additive)
      (derivedPushforwardModules f) (derivedPushforwardModulesUnit f)
      (derivedPushforwardModules_isRightDerivedFunctor f) I hI)
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) 0 (by
      change ((DerivedCategory.singleFunctor X.Modules 0).obj M).IsGE 0
      infer_instance)
  exact isQuasicoherent_of_iso S _ _ ((DerivedCategory.homologyFunctor S.Modules i).mapIso e).symm
    (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage f M i)

/-- Being in `D_QCoh(𝒪_S)` is invariant under isomorphism. -/
private theorem derivedCategoryB_of_iso (S : Scheme.{u}) {A B : DerivedCategory S.Modules}
    (e : A ≅ B)
    (h : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf) A) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf) B :=
  fun i ↦ (DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre S)).of_iso
    e h i

/-- **The derived direct image of a quasi-coherent module in a single degree has quasi-coherent
cohomology.** `M[-c]` is a shift of `M[0]`, the derived direct image commutes with the shift, and
`D_QCoh(𝒪_S)` is stable under the shift. -/
theorem isQuasicoherent_homology_derivedPushforward_singleFunctor (M : X.Modules)
    (hM : M.IsQuasicoherent) (c i : ℤ) :
    ((DerivedCategory.homologyFunctor S.Modules i).obj
      ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules c).obj M))).IsQuasicoherent := by
  have hzero : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj M)) :=
    fun j ↦ isQuasicoherent_homology_derivedPushforward_single_zero f M hM j
  have hshift := DerivedCategoryB.derivedCategoryB_shift_mem
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre S) (-c) hzero
  exact derivedCategoryB_of_iso S
    ((((derivedPushforwardModules f).commShiftIso (-c)).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)).symm ≪≫
    (derivedPushforwardModules f).mapIso
      (((DerivedCategory.singleFunctors X.Modules).shiftIso (-c) c 0 (by omega)).app M)) hshift i

/-! ### An object concentrated in one degree -/

/-- **The derived direct image of an object of `D_QCoh(𝒪_X)` concentrated in one degree has
quasi-coherent cohomology.** Such an object is a quasi-coherent module placed in that degree. -/
theorem isQuasicoherent_homology_derivedPushforward_of_pure (a : ℤ)
    (E : DerivedCategory X.Modules)
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (hGE : E.IsGE a) (hLE : E.IsLE a) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((derivedPushforwardModules f).obj E) := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE E a
  have hM : M.IsQuasicoherent :=
    isQuasicoherent_of_iso X _ M ((DerivedCategory.homologyFunctor X.Modules a).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules a).app M) (hE a)
  exact derivedCategoryB_of_iso S ((derivedPushforwardModules f).mapIso e.symm)
    (isQuasicoherent_homology_derivedPushforward_singleFunctor f M hM a)

/-! ### A bounded object -/

/-- **The derived direct image of a bounded object with quasi-coherent cohomology has
quasi-coherent cohomology.** Induction on the length of the window: the canonical truncation
triangle splits off the bottom degree, whose derived direct image is covered by
`isQuasicoherent_homology_derivedPushforward_singleFunctor`, and `D_QCoh(𝒪_S)` is a triangulated
subcategory of `D(𝒪_S)`, so the middle vertex of the image triangle is accounted for by the two
others. -/
theorem isQuasicoherent_homology_derivedPushforward_of_bounded :
    ∀ (k : ℕ) (a : ℤ) (E : DerivedCategory X.Modules),
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent) →
      E.IsGE a → E.IsLE (a + (k : ℤ)) →
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)
        ((derivedPushforwardModules f).obj E) := by
  intro k
  induction k with
  | zero =>
    intro a E hE hGE hLE
    have hLE' : E.IsLE a :=
      DerivedCategory.TStructure.t.isLE_of_le E (a + ((0 : ℕ) : ℤ)) a (by omega)
    exact isQuasicoherent_homology_derivedPushforward_of_pure f a E hE hGE hLE'
  | succ k ih =>
    intro a E hE hGE hLE
    have hT : (DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E ∈
        distTriang (DerivedCategory X.Modules) :=
      DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E
    have h₁ : DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)
        ((derivedPushforwardModules f).obj
          ((DerivedCategory.TStructure.t.truncLE a).obj E)) :=
      isQuasicoherent_homology_derivedPushforward_of_pure f a _
        (isQuasicoherent_homology_truncLE X E hE a) inferInstance inferInstance
    have h₃ : DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)
        ((derivedPushforwardModules f).obj
          ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E)) := by
      have hb : ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E).IsLE
          (a + 1 + (k : ℤ)) :=
        DerivedCategory.TStructure.t.isLE_of_le _ (a + ((k + 1 : ℕ) : ℤ)) (a + 1 + (k : ℤ))
          (by push_cast; omega)
      exact ih (a + 1) _ (isQuasicoherent_homology_truncGE X E hE (a + 1)) inferInstance hb
    exact DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre S)
      ((derivedPushforwardModules f).mapTriangle.obj
        ((DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E))
      ((derivedPushforwardModules f).map_distinguished _ hT) h₁ h₃

/-! ### Stacks 08D5, part (1) -/

/-- The derived direct image preserves quasi-coherent cohomology when the target is affine: an
affine scheme is quasi-compact and quasi-separated. -/
@[ega "III 6.2.3" "affine target Y"]
theorem preservesQuasicoherentOnAffineTarget : PreservesQuasicoherentOnAffineTarget.{u} :=
  PreservesQuasicoherentOnAffineTarget.of_compactTarget preservesQuasicoherentOnCompactTarget

/-- **[Stacks, Tag 08D5], part (1).** For a quasi-compact and quasi-separated morphism of schemes
`f : X ⟶ S` the unbounded derived direct image `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_S)`:
the cohomology sheaves of `Rf_*E` are quasi-coherent whenever those of `E` are.

The question is local on `S`, and over an affine open of `S` it is the quasi-compact-target case
`AlgebraicGeometry.preservesQuasicoherentOnCompactTarget`; the name records that affine-local
route, the same statement being reached by the compact-target route in
`AlgebraicGeometry.isQuasicoherent_derivedPushforward`. -/
@[stacks 08D5 "part (1)"]
theorem isQuasicoherent_derivedPushforward_affineLocal
    (E : QuasicoherentDerivedCategory X) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E.obj) :=
  isQuasicoherent_derivedPushforward_of_affineTarget preservesQuasicoherentOnAffineTarget f E

end AlgebraicGeometry

end
