module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.ChartFlatness
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.Globalization
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# The base-change conclusion of [Stacks, Tag 0D4E]

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` quasi-compact and quasi-separated and let `ℱ` be an
`𝒪_X`-module of finite presentation, flat over `S`. Then the composition

`Lg^*Rf_*ℱ ⟶ Rf'_*L(g')^*ℱ ⟶ Rf'_*(g')^*ℱ`

of the derived base-change map of [Stacks, Tag 08HY] with the derived-to-ordinary comparison is
an isomorphism, with nothing granted. That is the derived statement the second conclusion of
[Stacks, Tag 0D4E] reads its ordinary comparison off.

## Main results

* `…VanishingHigherDirectImages.isIso_derivedBaseChangeComp_single_of_isFlatOver`: the display
  above, [Stacks, Tag 0A1D] with the tensor factor cancelled.
* `…VanishingHigherDirectImages.isIso_homologyFunctor_map_derivedPushforwardUnit_app_single`:
  **`R⁰h_* = h_*` at the canonical comparison**, for an arbitrary morphism of ringed spaces.
* `…VanishingHigherDirectImages.isIso_baseChangeNatTrans_app_of_vanishing`: **the `H⁰`
  identification**, the single sentence of the source proof — the mate of the two derived
  pullback-pushforward adjunctions and the mate of the two ordinary ones agree in degree `0`,
  so the display above gives `g^* f_* ℱ ≅ f'_* (g')^* ℱ`.
* `…VanishingHigherDirectImages.ordinaryBaseChangeOfTensorFlatBaseChange`: the second of the two
  inputs named by `StacksFrontier/AlgebraicGeometry/Perfect/VanishingHigherDirectImages.lean`,
  proved.
* `…VanishingHigherDirectImages.isIso_baseChange_app_of_isZero_higherDirectImage`: **the second
  conclusion of [Stacks, Tag 0D4E]**, the comparison map `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is an
  isomorphism, with no hypothesis beyond the source's own.

## Implementation notes

**No unit coherence is needed.** The library's form of [Stacks, Tag 0A1D] is
`AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback`, whose map is the composition
above for `E ⊗^L_{𝒪_X} 𝒢^•` rather than for `𝒢^•`. Transporting that to `𝒢^•` would mean
transporting along a unit constraint of the *derived* tensor product, and the unit coherence of
[Stacks, Tag 079U] that such a transport rests on is proved only on the right
(`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_unitObject`), whereas this
instance needs it on the left: `𝒪_X` in degree `0` satisfies
`AlgebraicGeometry.FlatProperSupportFinitelyPresented f` only for a proper flat `f`, so `𝒢^•`
has to be `ℱ` in degree `0` and the unit is the left factor.

None of that is used. The *chart* form of the tag,
`AlgebraicGeometry.isIso_derivedBaseChangeComp_totalTensor_of_charts`, is stated for the
**ordinary total tensor complex** `Tot(P ⊗_{𝒪_X} 𝒢^•)` of two actual complexes rather than for a
derived tensor product. At `P = 𝒪_X` in degree zero — K-flat, by
`Stacks.SheafOfModules.isKFlat_single_unit` — that complex is isomorphic to `𝒢^•` by the Koszul
flip `Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` followed by the right unit law
`Stacks.SheafOfModules.tensorComplexUnitIso`, two isomorphisms *of complexes* with no coherence
attached; and the composition depends on the complex only up to isomorphism, which is
`Stacks.Cohomology.BaseChangeCover.isIso_bc_derivedPullbackNatTrans_iff_of_iso` and rests on
nothing but the naturality of the comparison. The chart hypothesis is
`AlgebraicGeometry.kFlat_sectionsComplex_pullback_fromSpec`, which is where flatness of `ℱ` over
`S` enters.

**Reading the ordinary comparison off it.** The derived statement is not yet the ordinary
comparison `g^* f_* ℱ ⟶ f'_* (g')^* ℱ`; that is the `H⁰` identification, and it is
`isIso_baseChangeNatTrans_app_of_vanishing` of this file. Its inputs are
`isIso_derivedPushforwardUnit_app_quotient_single_of_vanishing`,
`isIso_homologyFunctor_map_derivedPushforwardUnit_app_single` and
`…TopDegreeBaseChange.isIso_homologyFunctor_map_derivedPullbackComparison_app`, assembled in the
square `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_Qh_comparison`.

## References

* [Stacks Project, Tag 0D4E](https://stacks.math.columbia.edu/tag/0D4E)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  isIso_derivedPushforwardUnit_app_of_isKInjective pushforwardToDerivedCategory)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.AlgebraicGeometry.ProperSupportCoherent
  (nonempty_homology_derivedPushforward_single_zero)
open Stacks.AlgebraicGeometry.ProperSupportCoherent
  (nonempty_homology_derivedPushforward_single_zero)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)

universe u

namespace Stacks.AlgebraicGeometry.VanishingHigherDirectImages

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 0A1D] with the tensor factor cancelled.** For a cartesian square of schemes
with `f` quasi-compact and quasi-separated and an `𝒪_X`-module `ℱ` of finite presentation, flat
over `S`, the composition

`Lg^*Rf_*ℱ ⟶ Rf'_*L(g')^*ℱ ⟶ Rf'_*(g')^*ℱ`

is an isomorphism, the second map being the derived-to-ordinary comparison. The module
documentation of this file says why no unit coherence for [Stacks, Tag 079U] is needed. -/
public theorem isIso_derivedBaseChangeComp_single_of_isFlatOver {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w)
        (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F)) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app
          (ProperFlatBaseChange.singleDegreeComplex F))) := by
  have hGfp := ProperFlatBaseChange.isFinitePresentation_singleDegreeComplex F inferInstance
  have hGqcoh : ∀ n : ℤ,
      ((ProperFlatBaseChange.singleDegreeComplex F).X n).IsQuasicoherent := fun n =>
    let := hGfp n
    isQuasicoherent_of_isFinitePresentation _
  have hchart := isIso_derivedBaseChangeComp_totalTensor_of_charts hsq
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)))
    (ProperFlatBaseChange.singleDegreeComplex F)
    (Stacks.SheafOfModules.isKFlat_single_unit X.toRingedSpace.sheaf)
    (fun n => Stacks.Blowup.isQuasicoherent_homology_Q_single X _
      (isQuasicoherent_of_isFinitePresentation
        (_root_.SheafOfModules.unit X.ringCatSheaf)) n)
    hGqcoh
    (fun U V hU hV hUV => kFlat_sectionsComplex_pullback_fromSpec f hU hV hUV
      (ProperFlatBaseChange.singleDegreeComplex F)
      ((CochainComplex.minus_iff _).2 ⟨0, inferInstance⟩) hGqcoh
      (ProperFlatBaseChange.isFlatOver_singleDegreeComplex f F hflat))
  -- `Tot(𝒪_X[0] ⊗ 𝒢^•) ≅ 𝒢^•`: the Koszul flip of complexes followed by the right unit law of
  -- the ordinary total tensor complex. Both are isomorphisms of complexes with no coherence
  -- attached — the two that `…DerivedTensorProduct.braidingIso` and `…rightUnitIso` descend to
  -- the derived category — and the type is left to unification so that the total tensor complex
  -- never has to be written out.
  refine (Stacks.Cohomology.BaseChangeCover.isIso_bc_derivedPullbackNatTrans_iff_of_iso
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w) ?_).1 hchart
  exact Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.toRingedSpace.sheaf _ _ ≪≫
    Stacks.SheafOfModules.tensorComplexUnitIso X.toRingedSpace.sheaf _

/-- **`R⁰h_* = h_*` at the canonical comparison.** For any morphism of ringed spaces `h : X ⟶ Y`
and any `𝒪_X`-module `M`, the comparison `h_* M ⟶ Rh_*(M[0])` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit` is invertible on
degree-zero cohomology.

This is `Stacks.DerivedFunctor.isIso_singleUnitHomology_app`, the statement that the degree-zero
comparison of a right derived functor of a *left exact* functor is invertible, at the derived
direct image: `h_*` is a right adjoint, hence left exact; `Rh_*` carries `D^{≥0}` into `D^{≥0}`
by `Stacks.SmallDerivedCategory.isGE_obj_of_isGE`, [Stacks, Tag 05TC] (1), because the comparison
is invertible at every K-injective complex; and that same invertibility gives the comparison at a
complex of injectives. No hypothesis on `h` at all. -/
public theorem isIso_homologyFunctor_map_derivedPushforwardUnit_app_single
    {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y)) 0).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit h).app
        ((HomotopyCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj M))) := by
  let : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).CommShift ℤ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift h
  have : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
      h).IsTriangulated :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated h
  have hkinj := fun (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
      (hI : I.IsKInjective) =>
    isIso_derivedPushforwardUnit_app_of_isKInjective h I hI
  have hGE := fun N : SheafOfModules.{u} (structureSheafRing X) =>
    Stacks.SmallDerivedCategory.isGE_obj_of_isGE
      (RingedSpaceModuleAdjunction.modulePushforward h)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit h) hkinj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).obj N) 0 inferInstance
  have hinj := fun (J : SheafOfModules.{u} (structureSheafRing X)) (hJ : Injective J) =>
    Stacks.DerivedFunctor.isIso_unit_app_single_of_injective
      (RingedSpaceModuleAdjunction.modulePushforward h)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit h)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X) J hJ
  exact Stacks.DerivedFunctor.isIso_singleUnitHomology_app
    (RingedSpaceModuleAdjunction.modulePushforward h)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit h) hGE hinj M

/-! ### From the class of a map of modules in degree zero back to the map -/

/-- **The degreewise image of a natural transformation at a module in degree zero is the single
complex of its component.** For additive `T₁, T₂ : A ⥤ B` and `β : T₁ ⟶ T₂`, conjugating
`(NatTrans.mapHomologicalComplex β).app (F[j])` by the comparisons of `single` with `T₁` and `T₂`
gives `(single B c j).map (β.app F)`. Degreewise this is the naturality square of `β` at
`HomologicalComplex.singleObjXSelf`. -/
public theorem singleMapHomologicalComplex_natTrans_app_single {A : Type*} {B : Type*}
    [Category* A] [Category* B] [Abelian A] [Abelian B] {T₁ T₂ : A ⥤ B} [T₁.Additive]
    [T₂.Additive] (β : T₁ ⟶ T₂) (j : ℤ) (F : A) :
    (HomologicalComplex.singleMapHomologicalComplex T₁ (ComplexShape.up ℤ) j).inv.app F ≫
        (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) j).obj F) ≫
        (HomologicalComplex.singleMapHomologicalComplex T₂ (ComplexShape.up ℤ) j).hom.app F =
      (HomologicalComplex.single B (ComplexShape.up ℤ) j).map (β.app F) := by
  ext i
  by_cases hi : i = j
  · subst hi
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp [HomologicalComplex.single_map_f_self]
  · exact ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j (T₁.obj F) i
      hi).eq_of_src _ _)

/-- **A map of modules whose class in degree zero is invertible on degree-zero cohomology is
invertible.** `DerivedCategory.singleFunctorIsoCompQ` identifies the class of
`(single B c 0).map v` with `singleFunctor B 0` applied to `v`, and
`DerivedCategory.singleFunctorCompHomologyFunctorIso` writes `v` itself as `H⁰` of that between
two isomorphisms. -/
public theorem isIso_of_isIso_homologyFunctor_map_Q_single_map {B : Type*} [Category* B]
    [Abelian B] [HasDerivedCategory B] {M N : B} (v : M ⟶ N)
    (h : IsIso ((DerivedCategory.homologyFunctor B 0).map
      (DerivedCategory.Q.map ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map v)))) :
    IsIso v := by
  have e : (DerivedCategory.singleFunctor B 0).map v =
      (DerivedCategory.singleFunctorIsoCompQ B 0).hom.app M ≫
        DerivedCategory.Q.map ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map v) ≫
        (DerivedCategory.singleFunctorIsoCompQ B 0).inv.app N :=
    (NatIso.naturality_2 (DerivedCategory.singleFunctorIsoCompQ B 0) v).symm
  have hv : IsIso ((DerivedCategory.homologyFunctor B 0).map
      ((DerivedCategory.singleFunctor B 0).map v)) := by
    rw [e, (DerivedCategory.homologyFunctor B 0).map_comp,
      (DerivedCategory.homologyFunctor B 0).map_comp]
    have := h
    infer_instance
  have : IsIso ((DerivedCategory.singleFunctor B 0 ⋙
      DerivedCategory.homologyFunctor B 0).map v) := hv
  have key : (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app M ≫
      (DerivedCategory.singleFunctor B 0 ⋙ DerivedCategory.homologyFunctor B 0).map v ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app N = v :=
    NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0) v
  rw [← key]
  infer_instance

/-- **A natural transformation is invertible at `F` as soon as the class in `D(B)` of its
degreewise image at `F[0]` is invertible on degree-zero cohomology.** This is
`singleMapHomologicalComplex_natTrans_app_single` followed by
`isIso_of_isIso_homologyFunctor_map_Q_single_map`, with the bridge between `Qh ∘ quotient` and
`Q` supplied by `DerivedCategory.quotientCompQhIso`. -/
public theorem isIso_natTrans_app_of_isIso_homologyFunctor_map_Qh_quotient {A : Type*}
    {B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory B]
    {T₁ T₂ : A ⥤ B} [T₁.Additive] [T₂.Additive] (β : T₁ ⟶ T₂) (F : A)
    (h : IsIso ((DerivedCategory.homologyFunctor B 0).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F)))))) :
    IsIso (β.app F) := by
  refine isIso_of_isIso_homologyFunctor_map_Q_single_map _ ?_
  rw [← singleMapHomologicalComplex_natTrans_app_single β 0 F]
  have e := NatIso.naturality_1 (DerivedCategory.quotientCompQhIso B)
    ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F))
  have hmid : IsIso ((DerivedCategory.homologyFunctor B 0).map
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F)))) := by
    rw [← e, (DerivedCategory.homologyFunctor B 0).map_comp,
      (DerivedCategory.homologyFunctor B 0).map_comp]
    have h' : IsIso ((DerivedCategory.homologyFunctor B 0).map
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
          ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app
            ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F)))) := h
    have := ((DerivedCategory.homologyFunctor B 0).mapIso
      ((DerivedCategory.quotientCompQhIso B).app
        ((T₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F)))).isIso_inv
    have := ((DerivedCategory.homologyFunctor B 0).mapIso
      ((DerivedCategory.quotientCompQhIso B).app
        ((T₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F)))).isIso_hom
    infer_instance
  rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp,
    (DerivedCategory.homologyFunctor B 0).map_comp,
    (DerivedCategory.homologyFunctor B 0).map_comp]
  infer_instance

/-- **Off degree zero the class of a module placed in degree zero has no cohomology.** -/
public theorem isZero_homologyFunctor_obj_Q_single {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] (M : B) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor B n).obj
      (DerivedCategory.Q.obj ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M))) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor B n).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ B 0).app M)).symm
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact (DerivedCategory.isGE_iff ((DerivedCategory.singleFunctor B 0).obj M) 0).1
      inferInstance n hlt
  · exact (DerivedCategory.isLE_iff ((DerivedCategory.singleFunctor B 0).obj M) 0).1
      inferInstance n hgt

/-! ### The two mates agree in degree zero -/

/-- Cancelling an invertible right factor. The invertibility of `v` is an explicit argument, not
an instance: at the spellings below, instance search does not find it. -/
public theorem isIso_of_isIso_comp_right {C : Type*} [Category* C] {A B D : C} (u : A ⟶ B)
    (v : B ⟶ D) (hv : IsIso v) (h : IsIso (u ≫ v)) : IsIso u := by
  have := hv
  have := h
  have e : (u ≫ v) ≫ inv v = u := by simp
  rw [← e]
  infer_instance

/-- Cancelling an invertible left factor, with the invertibility of `u` explicit. -/
public theorem isIso_of_isIso_comp_left {C : Type*} [Category* C] {A B D : C} (u : A ⟶ B)
    (v : B ⟶ D) (hu : IsIso u) (h : IsIso (u ≫ v)) : IsIso v := by
  have := hu
  have := h
  exact IsIso.of_isIso_comp_left u v

/-- Any morphism between zero objects is invertible. -/
public theorem isIso_of_isZero_of_isZero {C : Type*} [Category* C] {A B : C} (hA : IsZero A)
    (hB : IsZero B) (u : A ⟶ B) : IsIso u :=
  ⟨⟨(hA.iso hB).inv, hA.eq_of_src _ _, hB.eq_of_src _ _⟩⟩

/-- **The comparison `f_* ℱ ⟶ Rf_* ℱ` is invertible when the higher direct images vanish.** Away
from degree zero both sides have no cohomology — the source because it is a module in degree
zero, the target by the vanishing hypothesis above degree zero and by [Stacks, Tag 05TD] (1)
below it — and in degree zero the comparison is invertible by
`isIso_homologyFunctor_map_derivedPushforwardUnit_app_single`. `DerivedCategory.isIso_iff`
assembles the degrees. -/
public theorem isIso_derivedPushforwardUnit_app_quotient_single_of_vanishing {X S : Scheme.{u}}
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    (hvanish : ∀ i : ℤ, 0 < i →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F)) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
        f.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F))) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  by_cases hn : n = 0
  · subst hn
    exact isIso_homologyFunctor_map_derivedPushforwardUnit_app_single f.toLRSHom.toShHom F
  · have hRn : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus n).obj F) := by
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f F n hlt
      · exact hvanish n hgt
    refine isIso_of_isZero_of_isZero ?_ ?_ _
    · refine IsZero.of_iso (isZero_homologyFunctor_obj_Q_single
        ((RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom).obj F) n hn)
        ((DerivedCategory.homologyFunctor _ n).mapIso ?_)
      exact (DerivedCategory.quotientCompQhIso _).app _ ≪≫
        DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
          (RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom)
          (ComplexShape.up ℤ) 0).app F)
    · obtain ⟨eR⟩ := nonempty_homology_derivedPushforward_single_zero f F n
      refine IsZero.of_iso hRn (?_ ≪≫ eR)
      exact (DerivedCategory.homologyFunctor _ n).mapIso
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          f.toLRSHom.toShHom).mapIso
          ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
            ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F).symm))

/-- **[Stacks, Tag 0D4E], the second conclusion, with nothing granted.** For a cartesian square
of schemes with `f` of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation, flat
over `S`, with `R ⁱ f_* ℱ = 0` for `i > 0`, the canonical comparison
`g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is an isomorphism.

The proof is the source's single sentence, made precise. The derived statement is
`isIso_derivedBaseChangeComp_single_of_isFlatOver`. The square
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_Qh_comparison` compares it with the
degreewise base-change map, whose class is `baseChangeNatTrans` by
`…underivedBaseChangeSquare_app_quotient_eq` and `…moduleBaseChange_eq`; its first edge is
invertible by `isIso_derivedPushforwardUnit_app_quotient_single_of_vanishing`, and its two
remaining edges are invertible in degree zero by
`…TopDegreeBaseChange.isIso_homologyFunctor_map_derivedPullbackComparison_app`
and by `isIso_homologyFunctor_map_derivedPushforwardUnit_app_single`. -/
public theorem isIso_baseChangeNatTrans_app_of_vanishing {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hvanish : ∀ i : ℤ, 0 < i →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F)) :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app F) := by
  have : QuasiCompact f := hf.quasiCompact
  have : QuasiSeparated f := hf.quasiSeparated
  have h1 := isIso_derivedPushforwardUnit_app_quotient_single_of_vanishing f F hvanish
  have h2 := (Stacks.Cohomology.BaseChangeCover.isIso_bc_derivedPullbackNatTrans_iff
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w) (ProperFlatBaseChange.singleDegreeComplex F)).1
    (isIso_derivedBaseChangeComp_single_of_isFlatOver f g f' g' hsq F hflat)
  have hsquare := Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_Qh_comparison
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w)
    ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F))
  have h2' : IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
        f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w)
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F))) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
          g'.toLRSHom.toShHom).app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F)))) := h2
  have hlhs : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g.toLRSHom.toShHom).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
        f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F))) ≫
      derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w)
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
              (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F))) ≫
        (derivedPushforward f'.toLRSHom.toShHom).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
            g'.toLRSHom.toShHom).app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
              (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F)))) := by
    infer_instance
  rw [hsquare] at hlhs
  -- pass to degree zero and split the three edges
  have hH : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) 0).map
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        g.toLRSHom.toShHom).app
        (((RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F))) ≫
      DerivedCategory.Qh.map
          ((Stacks.Cohomology.DerivedBaseChange.underivedBaseChangeSquare g'.toLRSHom.toShHom
            f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
            (comp_toShHom_of_comm hsq.w)).app ((HomotopyCategory.quotient
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F))) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
          f'.toLRSHom.toShHom).app
          (((RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F))))) := by
    infer_instance
  rw [Functor.map_comp, Functor.map_comp] at hH
  have hHd := TopDegreeBaseChange.isIso_homologyFunctor_map_derivedPullbackComparison_app
    g.toLRSHom.toShHom
    (((RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F)) 0
    (by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact (RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i (by omega)))
  have hHh : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) 0).map
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
      f'.toLRSHom.toShHom).app
      (((RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)).obj (ProperFlatBaseChange.singleDegreeComplex F))))) := by
    have hnat := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
        f'.toLRSHom.toShHom).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex
              (RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom)
              (ComplexShape.up ℤ) 0).hom.app F))
    have hmap : ∀ G : HomotopyCategory _ (ComplexShape.up ℤ) ⥤
        DerivedCategory (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)),
        IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) 0).map
          (G.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex
              (RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom)
              (ComplexShape.up ℤ) 0).hom.app F)))) := fun G =>
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) 0).mapIso
        (G.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex
            (RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom)
            (ComplexShape.up ℤ) 0).app F)))).isIso_hom
    have hA := hmap (pushforwardToDerivedCategory f'.toLRSHom.toShHom)
    have hB : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) 0).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
          f'.toLRSHom.toShHom).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom ⋙
              HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)))) :=
      isIso_homologyFunctor_map_derivedPushforwardUnit_app_single f'.toLRSHom.toShHom _
    have hH0nat := congrArg (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) 0).map hnat
    rw [Functor.map_comp, Functor.map_comp] at hH0nat
    have hstep : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) 0).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
        f'.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
            (RingedSpaceModuleAdjunction.modulePullback
              g'.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)))) := by
      refine isIso_of_isIso_comp_right _ _ (hmap (DerivedCategory.Qh ⋙ derivedPushforward
        f'.toLRSHom.toShHom)) ?_
      rw [← hH0nat]
      infer_instance
    exact hstep
  have hmid := isIso_of_isIso_comp_left _ _ hHd hH
  have he := isIso_of_isIso_comp_right _ _ hHh hmid
  -- identify the middle edge with `baseChangeNatTrans`
  have heq := Stacks.Cohomology.DerivedBaseChange.underivedBaseChangeSquare_app_quotient_eq
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w) (ProperFlatBaseChange.singleDegreeComplex F)
  rw [Stacks.Cohomology.DerivedBaseChange.moduleBaseChange_eq hsq.w] at heq
  rw [heq] at he
  exact isIso_natTrans_app_of_isIso_homologyFunctor_map_Qh_quotient
    (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w) F he

/-- **`OrdinaryBaseChangeOfTensorFlatBaseChange`, proved.** The input the second conclusion of
[Stacks, Tag 0D4E] used to be granted. It is now a theorem, and strictly so: the engine
hypothesis it quantifies over — invertibility of the base-change map of [Stacks, Tag 0A1D] in the
tensor form — is not used, because the derived statement this conclusion needs is
`isIso_derivedBaseChangeComp_single_of_isFlatOver`, which is the same tag read at the ordinary
total tensor complex and needs no unit constraint. -/
public theorem ordinaryBaseChangeOfTensorFlatBaseChange :
    OrdinaryBaseChangeOfTensorFlatBaseChange.{u} := by
  intro X X' S S' f g f' g' hsq _ hf
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  intro F hfp hflat _ hvanish _
  have := hfp
  exact isIso_baseChangeNatTrans_app_of_vanishing f g f' g' hsq hf F hflat hvanish

/-- **[Stacks, Tag 0D4E], the second conclusion, with nothing granted.** Let `f : X ⟶ S` be a
morphism of schemes of finite presentation and let `ℱ` be an `𝒪_X`-module of finite presentation,
flat over `S`, whose support is proper over `S`, with `R ⁱ f_* ℱ = 0` for all `i > 0`. Then the
formation of `f_* ℱ` commutes with arbitrary base change: for every cartesian square with
`g' : X' ⟶ X`, `f' : X' ⟶ S'` and `g : S' ⟶ S`, the canonical comparison map

`g^* f_* ℱ ⟶ f'_* (g')^* ℱ`

is an isomorphism. This is the meaning the source's proof gives the phrase: *commutation with
base change means that `g^* f_* ℱ = f'_* (g')^* ℱ`*. The comparison is
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the mate of the two
pullback-pushforward adjunctions, which is the only canonical map of that shape.

The proof is `isIso_baseChangeNatTrans_app_of_vanishing`. -/
public theorem isIso_baseChange_app_of_isZero_higherDirectImage {X X' S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    (_ : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (_ : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp F ⊆ (Z : Set X))
    (hvanish : ∀ i : ℤ, 0 < i →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F)) :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app F) :=
  isIso_baseChangeNatTrans_app_of_vanishing f g f' g' hsq hf F hflat hvanish

end Stacks.AlgebraicGeometry.VanishingHigherDirectImages

end
