module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewisePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkFinitePresentation
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.AlgebraicGeometry.Flatness.ThickeningBaseChange

/-!
# The fibrewise criterion for flatness, on schemes

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, let `F` be a quasi-coherent
`𝒪_X`-module of finite presentation and let `x` be a point of `X` whose stalk `F_x` is nonzero.
Write `s = g (f x)`. The fibrewise criterion for flatness (Stacks Tag 039C) compares

1. `F` is flat over `S` at `x`, and the restriction of `F` to the fibre `X_s` is flat over the
   fibre `Y_s` at the point of `X_s` corresponding to `x`;
2. `Y` is flat over `S` at `f x`, and `F` is flat over `Y` at `x`.

This file states the two conditions on the fibre schemes themselves and proves them equivalent.
The local content — the same comparison with the fibre ring written as a quotient of stalks — is
`Stacks.Flatness.flat_and_flat_quotient_smul_top_iff`; what is added here is the identification
of the quotient `𝒪_{X,x}/𝔪_s 𝒪_{X,x}` with the stalk of the fibre scheme
(`AlgebraicGeometry.quotientStalkEquivFiberStalk`) and of the fibre module with the stalk of the
pullback of `F` to `X_s` (`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`),
transported along the point identification `X_s ∋ x ↦ x`.

## Main definitions

* `Stacks.Flatness.fiberHom` is the morphism `X_s ⟶ Y_s` induced by `f` on fibres over `s`.
* `Stacks.Flatness.IsFlatOverBaseAndFiberAt` and
  `Stacks.Flatness.IsFlatOverIntermediateAt` are conditions (1) and (2).

## Main results

* `Stacks.Flatness.isFlatOverBaseAndFiberAt_iff` is the criterion.
* `Stacks.Flatness.isFlatOverBaseAndFiberAt_iff_of_isLocallyNoetherian` is its Noetherian form
  (Stacks Tag 039B): the same equivalence for a coherent module on locally Noetherian schemes.

## Implementation notes

Finite presentation of the stalk `F_x` over `𝒪_{X,x}` is derived, not assumed: it is
`Stacks.SheafOfModules.finitePresentation_stalk`, which takes a section-level presentation of `F`
near `x` (`Stacks.SheafOfModules.nonempty_localPresentation`) and applies `germ` to its generators
and relations. No localization theory is involved.

The restriction of `F` to the fibre is its canonical pullback along the fibre inclusion
`X_s ⟶ X`. The point of `X_s` corresponding to `x` is `(f ≫ g).asFiber x`, and its image in
`Y_s` is `fiberHom f g s ((f ≫ g).asFiber x)`; the equality of that image with
`g.asFiber (f x)`, transported along `g (f x) = s`, is what makes the fibre ring of the local
statement agree with the stalk of `Y_s`.

The Noetherian criterion is not an instance of the finitely presented one: locally Noetherian
schemes `X`, `Y`, `S` need not make `X ⟶ S` locally of finite presentation or `Y ⟶ S` locally of
finite type (take `S = Spec k`, `X = Y = Spec K` for a field extension `K/k` of infinite
transcendence degree). Its local input is therefore Tag 00MP,
`Module.flat_and_flat_of_flat_quotient_maximalIdeal_of_flat`, whose finiteness hypothesis is
`Module.Finite 𝒪_{X,x} F_x` — supplied by `SheafOfModules.finite_stalk` from coherence of `F` —
and whose Noetherian hypotheses are the stalks of locally Noetherian schemes. The identification
of the fibre data with quotients of stalks is the same for both and is
`Stacks.Flatness.flat_quotient_smul_top_of_fiber`.

## References

* [Stacks Project, Tag 039B](https://stacks.math.columbia.edu/tag/039B)
* [Stacks Project, Tag 039C](https://stacks.math.columbia.edu/tag/039C)
* [Stacks Project, Tag 00MP](https://stacks.math.columbia.edu/tag/00MP)
* [Stacks Project, Tag 05UV](https://stacks.math.columbia.edu/tag/05UV)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Flatness

/-- The canonical morphism from the fibre of a composite `X ⟶ Y ⟶ S`
to the corresponding fibre of `Y ⟶ S`. -/
public noncomputable def fiberHom {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (s : S) : (f ≫ g).fiber s ⟶ g.fiber s :=
  Limits.pullback.lift ((f ≫ g).fiberι s ≫ f) ((f ≫ g).fiberToSpecResidueField s)
    ((f ≫ g).fiber_fac s)

/-- The canonical module structure of the stalk of an `𝒪_X`-module over the local ring of the
ringed space at the point. -/
@[instance_reducible]
public noncomputable def stalkModule {X : RingedSpace.{u, u}}
    (F : SheafOfModules.{u} (structureSheafRing X)) (x : X) :
    Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

/-- The composite of `fiberHom f g s` with the fibre inclusion `g.fiberι s` is the fibre
inclusion of `f ≫ g` followed by `f`. -/
lemma fiberHom_fiberι {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (s : S) :
    fiberHom f g s ≫ g.fiberι s = (f ≫ g).fiberι s ≫ f :=
  Limits.pullback.lift_fst ..

/-- The composite of `fiberHom f g s` with the structure morphism of the fibre of `g` to
`Spec κ(s)` is the structure morphism of the fibre of `f ≫ g`. -/
lemma fiberHom_fiberToSpecResidueField {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    fiberHom f g s ≫ g.fiberToSpecResidueField s =
      (f ≫ g).fiberToSpecResidueField s :=
  Limits.pullback.lift_snd ..

/-- The square formed by `fiberHom f g s`, the fibre inclusions over `s` of `f ≫ g` and of `g`,
and `f` is a pullback square: the fibre of `f ≫ g` over `s` is the base change of `f` to the
fibre of `g` over `s`. -/
lemma isPullback_fiberHom {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (s : S) :
    IsPullback (fiberHom f g s) ((f ≫ g).fiberι s) (g.fiberι s) f := by
  refine IsPullback.of_right ?_ (fiberHom_fiberι f g s)
    (IsPullback.of_hasPullback g (S.fromSpecResidueField s)).flip
  change IsPullback (fiberHom f g s ≫ g.fiberToSpecResidueField s)
    ((f ≫ g).fiberι s) (S.fromSpecResidueField s) (f ≫ g)
  rw [fiberHom_fiberToSpecResidueField]
  exact (IsPullback.of_hasPullback (f ≫ g) (S.fromSpecResidueField s)).flip

/-- The stalk map at a point, read on germs, transported along an equality of morphisms. -/
private lemma stalkMap_hom_apply_congr {V W : Scheme.{u}} (p q : V ⟶ W) (h : p = q) (v : V)
    (b : W.presheaf.stalk (p v)) :
    (p.stalkMap v).hom b =
      (q.stalkMap v).hom
        ((W.presheaf.stalkCongr (.of_eq (congrArg (fun k : V ⟶ W => k v) h))).hom b) := by
  cases h
  simp

private lemma stalkMap_pointEq {X Y : RingedSpace.{u, u}} (p : X ⟶ Y)
    {x' x : X} (h : x' = x) :
    (Y.presheaf.stalkCongr (.of_eq (congrArg p.hom.base h))).hom ≫
        p.hom.stalkMap x =
      p.hom.stalkMap x' ≫ (X.presheaf.stalkCongr (.of_eq h)).hom := by
  cases h
  simp

private lemma stalkCongr_hom_comp {X : TopCat.{u}}
    (F : X.Presheaf CommRingCat.{u}) {x y z : X}
    (hxy : x = y) (hyz : y = z) :
    (F.stalkCongr (.of_eq hxy)).hom ≫ (F.stalkCongr (.of_eq hyz)).hom =
      (F.stalkCongr (.of_eq (hxy.trans hyz))).hom := by
  cases hxy
  cases hyz
  simp [TopCat.Presheaf.stalkCongr]

private lemma stalkCongr_inv_hom {X : TopCat.{u}}
    (F : X.Presheaf CommRingCat.{u}) {x y : X} (h : x = y) :
    (F.stalkCongr (.of_eq h)).inv =
      (F.stalkCongr (.of_eq h.symm)).hom := by
  cases h
  simp [TopCat.Presheaf.stalkCongr]

/-- Finite presentation of the stalk of a sheaf of modules transported along an equality of
points. -/
private theorem finitePresentation_stalk_pointEq {X : Scheme.{u}}
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {x' x : X} (h : x' = x)
    (hfp : letI := stalkModule F x
      Module.FinitePresentation (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) :
    letI := stalkModule F x'
    Module.FinitePresentation (X.presheaf.stalk x')
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x') := by
  cases h
  exact hfp

private lemma flatOverAt_pointEq {X Y : RingedSpace.{u, u}}
    (p : X ⟶ Y) (F : SheafOfModules.{u} (structureSheafRing X))
    {x' x : X} (h : x' = x) (hflat : AlgebraicGeometry.IsFlatOverAt p F x) :
    AlgebraicGeometry.IsFlatOverAt p F x' := by
  let eR := (Y.presheaf.stalkCongr (.of_eq (congrArg p.hom.base h))).commRingCatIsoToRingEquiv
  let eM := CategoryTheory.Iso.addCommGroupIsoToAddEquiv
    (TopCat.Presheaf.stalkCongr F.val.presheaf (.of_eq h))
  let _mx := stalkModule F x
  let _mx' := stalkModule F x'
  let : Module (Y.presheaf.stalk (p.hom.base x'))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x') :=
    Module.compHom _ (p.hom.stalkMap x').hom
  let : Module (Y.presheaf.stalk (p.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) :=
    Module.compHom _ (p.hom.stalkMap x).hom
  have hlin : ∀ a m, eM (a • m) = eR a • eM m := by
    intro a m
    cases h
    simp [eM, eR, TopCat.Presheaf.stalkCongr,
      CategoryTheory.Iso.addCommGroupIsoToAddEquiv,
      CategoryTheory.Iso.commRingCatIsoToRingEquiv]
  change Module.Flat (Y.presheaf.stalk (p.hom.base x))
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) at hflat
  let : Module.Flat (Y.presheaf.stalk (p.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) := hflat
  change Module.Flat (Y.presheaf.stalk (p.hom.base x'))
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x')
  exact Stacks.Flatness.flat_of_ringEquiv eR eM hlin

private lemma flatAt_pointEq {X Y : RingedSpace.{u, u}} (p : X ⟶ Y)
    {x' x : X} (h : x' = x)
    (hflat : AlgebraicGeometry.IsFlatAt p x) : AlgebraicGeometry.IsFlatAt p x' := by
  let eR := (Y.presheaf.stalkCongr (.of_eq (congrArg p.hom.base h))).commRingCatIsoToRingEquiv
  let eB := (X.presheaf.stalkCongr (.of_eq h)).commRingCatIsoToRingEquiv
  let φ := (p.hom.stalkMap x').hom
  let φ₀ := (p.hom.stalkMap x).hom
  let : Module (Y.presheaf.stalk (p.hom.base x')) (X.presheaf.stalk x') :=
    Module.compHom (X.presheaf.stalk x') φ
  let : Module (Y.presheaf.stalk (p.hom.base x)) (X.presheaf.stalk x) :=
    Module.compHom (X.presheaf.stalk x) φ₀
  have hmap (a : Y.presheaf.stalk (p.hom.base x')) :
      eB (φ a) = φ₀ (eR a) := by
    have hn := congrArg (fun q => q.hom a) (stalkMap_pointEq p h)
    change (X.presheaf.stalkCongr (.of_eq h)).hom (φ a) =
      φ₀ ((Y.presheaf.stalkCongr (.of_eq (congrArg p.hom.base h))).hom a)
    exact hn.symm
  have hlin : ∀ a b, eB (φ a * b) = φ₀ (eR a) * eB b := by
    intro a b
    rw [map_mul, hmap]
  change Module.Flat (Y.presheaf.stalk (p.hom.base x)) (X.presheaf.stalk x) at hflat
  let : Module.Flat (Y.presheaf.stalk (p.hom.base x)) (X.presheaf.stalk x) := hflat
  change Module.Flat (Y.presheaf.stalk (p.hom.base x')) (X.presheaf.stalk x')
  exact Stacks.Flatness.flat_of_ringEquiv eR eB.toAddEquiv hlin

private noncomputable def fiberStalkRingEquivOfEq {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ≃+*
      ((f.fiber y).presheaf.stalk (h ▸ f.asFiber x)) := by
  cases h
  exact RingEquiv.refl _

private theorem fiberι_asFiber_cast {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y) :
    f.fiberι y (h ▸ f.asFiber x) = x := by
  cases h
  exact Scheme.Hom.fiberι_asFiber f x

private theorem fiberι_stalkMap_baseEq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y) (a : X.presheaf.stalk x) :
    fiberStalkRingEquivOfEq f x y h
        ((((f.fiberι (f x)).stalkMap (f.asFiber x)).hom)
          ((X.presheaf.stalkCongr
            (.of_eq (f.fiberι_asFiber x).symm)).hom a)) =
      ((f.fiberι y).stalkMap (h ▸ f.asFiber x)).hom
        ((X.presheaf.stalkCongr
          (.of_eq (fiberι_asFiber_cast f x y h).symm)).hom a) := by
  cases h
  simp [fiberStalkRingEquivOfEq]

private noncomputable def modulePullbackStalkLinearEquiv
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((modulePullback f).obj G).val
    let : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    let : Module (Y.presheaf.stalk (f.hom.base x))
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) G'.presheaf (f.hom.base x)) :=
      stalkModule G (f.hom.base x)
    let : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P'.presheaf x) :=
      stalkModule ((modulePullback f).obj G) x
    ↑(TopCat.Presheaf.stalk P'.presheaf x) ≃ₗ[X.presheaf.stalk x]
      TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) := by
  intro _ _ _ _ _
  exact (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f G x).choose

/-- Condition (1) of the fibrewise criterion: `F` is flat over the base at
`x`, and its restriction to the fibre is flat over the corresponding fibre of
the intermediate scheme. -/
public noncomputable def IsFlatOverBaseAndFiberAt {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (x : X) : Prop :=
  AlgebraicGeometry.IsFlatOverAt (f ≫ g).toLRSHom.toShHom F x ∧
    AlgebraicGeometry.IsFlatOverAt (fiberHom f g (g (f x))).toLRSHom.toShHom
      ((modulePullback ((f ≫ g).fiberι (g (f x))).toLRSHom.toShHom).obj F)
      ((f ≫ g).asFiber x)

/-- Condition (2) of the fibrewise criterion: the intermediate scheme is flat
over the base at the image of `x`, and `F` is flat over the intermediate
scheme at `x`. -/
public noncomputable def IsFlatOverIntermediateAt {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (x : X) : Prop :=
  AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom (f x) ∧
    AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x

open scoped _root_.TensorProduct

private theorem flatOver_fiber_of_flatOver {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [F.IsQuasicoherent] (x : X)
    (hf : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x) :
    AlgebraicGeometry.IsFlatOverAt (fiberHom f g (g (f x))).toLRSHom.toShHom
      ((modulePullback ((f ≫ g).fiberι (g (f x))).toLRSHom.toShHom).obj F)
      ((f ≫ g).asFiber x) :=
  AlgebraicGeometry.modulePullback_isFlatOverAt
    (isPullback_fiberHom f g (g (f x))).flip F ((f ≫ g).asFiber x)
    (((f ≫ g).fiberι_asFiber x).symm ▸ hf)

/-- The fibre half of condition (1), read on local rings: flatness of the restriction of `F` to
the fibre `X_s` over the fibre `Y_s` is flatness of the fibre module `F_x/𝔪_s F_x` over the
fibre ring `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}`. -/
private theorem flat_quotient_smul_top_of_fiber {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (x x' : X) (hx' : x' = (f ≫ g).fiberι ((f ≫ g) x) ((f ≫ g).asFiber x))
    (hfiberFlat : AlgebraicGeometry.IsFlatOverAt (fiberHom f g (g (f x))).toLRSHom.toShHom
      ((modulePullback ((f ≫ g).fiberι (g (f x))).toLRSHom.toShHom).obj F)
      ((f ≫ g).asFiber x)) :
    letI := stalkModule F x'
    letI : Module (Y.presheaf.stalk (f x'))
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x') :=
      Module.compHom _ (f.stalkMap x').hom
    Module.Flat
      (Y.presheaf.stalk (f x') ⧸
        Ideal.map (g.stalkMap (f x')).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (g (f x')))))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x' ⧸
        (Ideal.map (g.stalkMap (f x')).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (g (f x')))) •
          (⊤ : Submodule (Y.presheaf.stalk (f x'))
            (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x')))) := by
  subst hx'
  let sFiber := (f ≫ g) x
  let z : (f ≫ g).fiber sFiber := (f ≫ g).asFiber x
  let iX := (f ≫ g).fiberι sFiber
  have hzx : iX z = x := (f ≫ g).fiberι_asFiber x
  let x' := iX z
  let y := f x'
  have hSPoint : (f ≫ g) x' = sFiber := congrArg (f ≫ g) hzx
  have hYbase : g y = sFiber := by
    simpa only [y, Scheme.Hom.comp_apply] using hSPoint
  let R := S.presheaf.stalk ((f ≫ g) x')
  let B := Y.presheaf.stalk y
  let A := X.presheaf.stalk x'
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x'
  let : Module A M := stalkModule F x'
  let : Algebra B A := (f.stalkMap x').hom.toAlgebra
  let : Module B M := Module.compHom _ (f.stalkMap x').hom
  have : IsScalarTower B A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let φ : R →+* B := (g.stalkMap y).hom
  let ψ : B →+* A := (f.stalkMap x').hom
  have hψφ : ((f ≫ g).stalkMap x').hom = ψ.comp φ :=
    Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x'
  let J := Ideal.map φ (IsLocalRing.maximalIdeal R)
  let Q : Type u := M ⧸ (J • (⊤ : Submodule B M))
  let : Module (B ⧸ J) Q :=
    (Module.isTorsionBySet_quotient_ideal_smul M J).module
  let Pf := ((modulePullback iX.toLRSHom.toShHom).obj F).val
  let P := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Pf.presheaf z
  let Af : Type u := ((f ≫ g).fiber sFiber).presheaf.stalk z
  let hfiber := fiberHom f g sFiber
  let wf := hfiber z
  let Bf : Type u := (g.fiber sFiber).presheaf.stalk wf
  let : Algebra Bf Af := (hfiber.stalkMap z).hom.toAlgebra
  let : Module Af P :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      Pf z
  let : Module Bf P := Module.compHom P (hfiber.stalkMap z).hom
  let K := Ideal.map (Scheme.Hom.stalkMap (f ≫ g) x').hom
    (IsLocalRing.maximalIdeal R)
  let : Module (A ⧸ K) (M ⧸ (K • (⊤ : Submodule A M))) :=
    (Module.isTorsionBySet_quotient_ideal_smul M K).module
  have hK : K = Ideal.map ψ J := by
    change Ideal.map ((f ≫ g).stalkMap x').hom (IsLocalRing.maximalIdeal R)
      = Ideal.map ψ (Ideal.map φ (IsLocalRing.maximalIdeal R))
    rw [Ideal.map_map, hψφ]
  have hzFiber' : hSPoint ▸ (f ≫ g).asFiber x' = z := by
    apply iX.isEmbedding.injective
    change iX _ = x'
    simpa [iX] using fiberι_asFiber_cast (f ≫ g) x' sFiber hSPoint
  let eC₀ := AlgebraicGeometry.quotientStalkEquivFiberStalk (f ≫ g) x'
  let eCF := fiberStalkRingEquivOfEq (f ≫ g) x' sFiber hSPoint
  let eCP := ((f ≫ g).fiber sFiber).presheaf.stalkCongr (.of_eq hzFiber')
  let eCFinal := eCF.trans eCP.commRingCatIsoToRingEquiv
  let eC : (A ⧸ K) ≃+* Af := eC₀.trans eCFinal
  let eB := AlgebraicGeometry.quotientStalkEquivFiberStalk g y
  have hSub : (K • (⊤ : Submodule A M)).restrictScalars B =
      J • (⊤ : Submodule B M) := by
    rw [hK]
    simpa [RingHom.algebraMap_toAlgebra] using
      (Ideal.smul_restrictScalars (R := B) (S := A) J
        (⊤ : Submodule A M))
  let : Module B (M ⧸ (K • (⊤ : Submodule A M))) :=
    Module.compHom _ ψ
  have hTors : Module.IsTorsionBySet B
      (M ⧸ (K • (⊤ : Submodule A M))) J := by
    intro t j
    induction t using Submodule.Quotient.induction_on with
    | _ m =>
      have hjK : ψ (j : B) ∈ K := by
        rw [hK]
        exact Ideal.mem_map_of_mem ψ j.2
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact Submodule.smul_mem_smul hjK Submodule.mem_top
  let : Module (B ⧸ J) (M ⧸ (K • (⊤ : Submodule A M))) := hTors.module
  let eQ : Q ≃ₗ[B] M ⧸ (K • (⊤ : Submodule A M)) :=
    Submodule.quotEquivOfEq (M := M) (p := J • (⊤ : Submodule B M))
      (p' := (K • (⊤ : Submodule A M)).restrictScalars B) hSub.symm ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv B (K • (⊤ : Submodule A M))
  let eT₀ : (A ⧸ K) ⊗[A] M ≃ₗ[A] M ⧸ (K • (⊤ : Submodule A M)) :=
    TensorProduct.quotTensorEquivQuotSMul M K
  have hdom (a : A) (t : (A ⧸ K) ⊗[A] M) : (Ideal.Quotient.mk K a) • t = a • t := by
    induction t using TensorProduct.inductionOn with
    | tmul c m =>
      simp only [TensorProduct.smul_tmul']
      congr 1
    | add t₁ t₂ h₁ h₂ => simp [h₁, h₂]
  have hcod (a : A) (m : M ⧸ (K • (⊤ : Submodule A M))) :
      (Ideal.Quotient.mk K a) • m = a • m :=
    Module.IsTorsionBySet.mk_smul (Module.isTorsionBySet_quotient_ideal_smul M K) a m
  let eT : (A ⧸ K) ⊗[A] M ≃ₗ[A ⧸ K] M ⧸ (K • (⊤ : Submodule A M)) := {
    __ := eT₀
    map_smul' := by
      intro q t
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      calc
        eT₀ ((Ideal.Quotient.mk K a) • t) = eT₀ (a • t) := congrArg eT₀ (hdom a t)
        _ = a • eT₀ t := eT₀.map_smul a t
        _ = (Ideal.Quotient.mk K a) • eT₀ t := (hcod a _).symm
  }
  have hcomm : (f ≫ g).fiberι sFiber ≫ f = hfiber ≫ g.fiberι sFiber :=
    (fiberHom_fiberι f g sFiber).symm
  have hwf' : hYbase ▸ g.asFiber y = hfiber z := by
    apply (g.fiberι sFiber).isEmbedding.injective
    change (g.fiberι sFiber) (hYbase ▸ g.asFiber y) = (hfiber ≫ g.fiberι sFiber) z
    rw [← hcomm]
    exact fiberι_asFiber_cast g y sFiber hYbase
  let eBG := fiberStalkRingEquivOfEq g y sFiber hYbase
  let eBP := (g.fiber sFiber).presheaf.stalkCongr (.of_eq hwf')
    |>.commRingCatIsoToRingEquiv
  let eBf := eB.trans (eBG.trans eBP)
  have hBmk (b : B) : eB (Ideal.Quotient.mk J b) =
      ((g.fiberι (g y)).stalkMap (g.asFiber y)).hom
        ((Y.presheaf.stalkCongr
          (.of_eq (g.fiberι_asFiber y).symm)).hom b) := by
    change (AlgebraicGeometry.quotientStalkEquivFiberStalk g y)
      (Ideal.Quotient.mk
        (Ideal.map (g.stalkMap y).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (g y)))) b) = _
    exact AlgebraicGeometry.quotientStalkEquivFiberStalk_mk g y b
  let ρ : A →+* Af :=
    (iX.stalkMap z).hom
  have hA (a : A) : eC (Ideal.Quotient.mk K a) = ρ a := by
    calc
      eC (Ideal.Quotient.mk K a) =
          eCFinal (eC₀ (Ideal.Quotient.mk K a)) := rfl
      _ = eCFinal (
            (((f ≫ g).fiberι ((f ≫ g) x')).stalkMap
              ((f ≫ g).asFiber x')).hom
              ((X.presheaf.stalkCongr
                (.of_eq ((f ≫ g).fiberι_asFiber x').symm)).hom a)) :=
          congrArg eCFinal (AlgebraicGeometry.quotientStalkEquivFiberStalk_mk (f ≫ g) x' a)
      _ = eCP.commRingCatIsoToRingEquiv
            (eCF ((((f ≫ g).fiberι ((f ≫ g) x')).stalkMap
              ((f ≫ g).asFiber x')).hom
                ((X.presheaf.stalkCongr
                  (.of_eq ((f ≫ g).fiberι_asFiber x').symm)).hom a))) := by
          rfl
      _ = eCP.commRingCatIsoToRingEquiv
            ((iX.stalkMap (hSPoint ▸ (f ≫ g).asFiber x')).hom
              ((X.presheaf.stalkCongr
                (.of_eq (fiberι_asFiber_cast (f ≫ g) x' sFiber hSPoint).symm)).hom a)) :=
          congrArg eCP.commRingCatIsoToRingEquiv
            (fiberι_stalkMap_baseEq (f ≫ g) x' sFiber hSPoint a)
      _ = ρ a := by
        let q := hSPoint ▸ (f ≫ g).asFiber x'
        let hcast := fiberι_asFiber_cast (f ≫ g) x' sFiber hSPoint
        let eTarget := X.presheaf.stalkCongr (.of_eq hcast)
        have hNat := Scheme.Hom.stalkMap_congr_point iX q z hzFiber'
        have hNatApp := congrArg (fun k => k.hom (eTarget.inv.hom a)) hNat
        have hAeq : eCP.hom.hom
            ((iX.stalkMap q).hom (eTarget.inv.hom a)) =
              (iX.stalkMap z).hom
                (eTarget.hom.hom (eTarget.inv.hom a)) := by
          simpa only [ConcreteCategory.comp_apply, eTarget, eCP] using hNatApp
        exact hAeq.trans (congrArg _ (eTarget.inv_hom_id_apply a))
  have hRing (b : B) :
      eC (Ideal.Quotient.mk K (ψ b)) =
        (hfiber.stalkMap z).hom
          (eBf (Ideal.Quotient.mk J b)) := by
    rw [hA]
    change (iX.stalkMap z).hom (ψ b) =
      (hfiber.stalkMap z).hom (eBP (eBG (eB (Ideal.Quotient.mk J b))))
    rw [hBmk]
    let q := hYbase ▸ g.asFiber y
    let hYcast := fiberι_asFiber_cast g y sFiber hYbase
    let eY := Y.presheaf.stalkCongr (.of_eq hYcast)
    let hSourcePoint := congrArg (g.fiberι sFiber) hwf'
    let hYpoint : y = (g.fiberι sFiber) (hfiber z) :=
      (hSourcePoint.symm.trans hYcast).symm
    have hBase := fiberι_stalkMap_baseEq g y sFiber hYbase b
    have hBmove : eBP (eBG
        (((g.fiberι (g y)).stalkMap (g.asFiber y)).hom
          ((Y.presheaf.stalkCongr
            (.of_eq (g.fiberι_asFiber y).symm)).hom b))) =
          ((g.fiberι sFiber).stalkMap (hfiber z)).hom
          ((Y.presheaf.stalkCongr (.of_eq hYpoint)).hom b) := by
      rw [hBase]
      have hYmap : eY.inv ≫
          (Y.presheaf.stalkCongr (.of_eq hSourcePoint)).hom =
            (Y.presheaf.stalkCongr (.of_eq hYpoint)).hom := by
        change (Y.presheaf.stalkCongr (.of_eq hYcast)).inv ≫
            (Y.presheaf.stalkCongr (.of_eq hSourcePoint)).hom =
              (Y.presheaf.stalkCongr (.of_eq hYpoint)).hom
        have hinv : eY.inv =
            (Y.presheaf.stalkCongr (.of_eq hYcast.symm)).hom :=
          stalkCongr_inv_hom Y.presheaf hYcast
        rw [hinv]
        have hcomp := stalkCongr_hom_comp Y.presheaf
          hYcast.symm hSourcePoint
        have hh : hYcast.symm.trans hSourcePoint = hYpoint :=
          Subsingleton.elim _ _
        simpa [hh] using hcomp
      have hNat := Scheme.Hom.stalkMap_congr_point
        (g.fiberι sFiber) q (hfiber z) hwf'
      have hNatApp := congrArg (fun k => k.hom (eY.inv.hom b)) hNat
      change eBP
          (((g.fiberι sFiber).stalkMap q).hom (eY.inv.hom b)) =
        ((g.fiberι sFiber).stalkMap (hfiber z)).hom
          (((Y.presheaf.stalkCongr (.of_eq hSourcePoint)).hom)
            (eY.inv.hom b)) at hNatApp
      change eBP
          (((g.fiberι sFiber).stalkMap q).hom (eY.inv.hom b)) =
        ((g.fiberι sFiber).stalkMap (hfiber z)).hom
          ((Y.presheaf.stalkCongr (.of_eq hYpoint)).hom b)
      rw [← hYmap]
      exact hNatApp
    have hmid : ((iX ≫ f).stalkMap z).hom b
        = ((hfiber ≫ g.fiberι sFiber).stalkMap z).hom
          ((Y.presheaf.stalkCongr (.of_eq hYpoint)).hom b) :=
      stalkMap_hom_apply_congr (iX ≫ f) (hfiber ≫ g.fiberι sFiber) hcomm z b
    have hleft : ((iX ≫ f).stalkMap z).hom b
        = (iX.stalkMap z).hom ((f.stalkMap (iX z)).hom b) :=
      RingHom.congr_fun (Stacks.ModuleSkyscraper.stalkMap_hom_comp iX f z) b
    have hright : ((hfiber ≫ g.fiberι sFiber).stalkMap z).hom
          ((Y.presheaf.stalkCongr (.of_eq hYpoint)).hom b)
        = (hfiber.stalkMap z).hom
          (((g.fiberι sFiber).stalkMap (hfiber z)).hom
            ((Y.presheaf.stalkCongr (.of_eq hYpoint)).hom b)) :=
      RingHom.congr_fun (Stacks.ModuleSkyscraper.stalkMap_hom_comp hfiber (g.fiberι sFiber) z) _
    rw [hBmove]
    exact hleft.symm.trans (hmid.trans hright)
  let : Algebra A Af := ρ.toAlgebra
  let : Module A P := Module.compHom P ρ
  let : IsScalarTower A Af P := IsScalarTower.of_algebraMap_smul fun a p => rfl
  let eCA : (A ⧸ K) ≃ₗ[A] Af :=
    eC.toAddEquiv.toLinearEquiv (fun a q => by
      obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective q
      change eC (Ideal.Quotient.mk K (a * a')) = a • eC (Ideal.Quotient.mk K a')
      rw [map_mul (Ideal.Quotient.mk K), map_mul, hA, hA]
      change ρ a * ρ a' = (algebraMap A Af) a * ρ a'
      rfl)
  let eTen : (A ⧸ K) ⊗[A] M ≃ₗ[A] Af ⊗[A] M :=
    TensorProduct.congr eCA (LinearEquiv.refl A M)
  let ePull : P ≃ₗ[Af] Af ⊗[A] M :=
    modulePullbackStalkLinearEquiv iX.toLRSHom.toShHom F z
  let ePullA : P ≃+ Af ⊗[A] M := ePull.toAddEquiv
  let α : Bf →+* Af := (hfiber.stalkMap z).hom
  let : Module Bf (Af ⊗[A] M) := Module.compHom _ α
  have hTen (q : A ⧸ K) (t : (A ⧸ K) ⊗[A] M) :
      eTen (q • t) = eCA q • eTen t := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    calc
      eTen ((Ideal.Quotient.mk K a) • t) = eTen (a • t) :=
        congrArg eTen (hdom a t)
      _ = a • eTen t := eTen.map_smul a t
      _ = eCA (Ideal.Quotient.mk K a) • eTen t := by
        change a • eTen t = eC (Ideal.Quotient.mk K a) • eTen t
        rw [hA]
        change a • eTen t = algebraMap A Af a • eTen t
        exact (IsScalarTower.algebraMap_smul (R := A) (A := Af) a (eTen t)).symm
  let φQ : Q ≃+ P :=
    eQ.toAddEquiv.trans
      (eT.symm.toAddEquiv.trans (eTen.toAddEquiv.trans ePullA.symm))
  have hφQ : ∀ (q : B ⧸ J) (m : Q),
      φQ (q • m) = eBf q • φQ m := by
    intro q m
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    apply ePullA.injective
    have hscalar : eCA (Ideal.Quotient.mk K (ψ b)) =
        α (eBf (Ideal.Quotient.mk J b)) := hRing b
    have hmain' : eTen (eT.symm (b • eQ m)) =
        α (eBf (Ideal.Quotient.mk J b)) •
          eTen (eT.symm (eQ m)) := by
      change eTen (eT.symm (ψ b • eQ m)) = _
      rw [← hcod (ψ b), eT.symm.map_smul, hTen, hscalar]
    simp only [Module.IsTorsionBySet.mk_smul, AddEquiv.trans_apply, AddEquiv.coe_mk,
      AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk, map_smul, LinearEquiv.symm_symm,
      AddEquiv.apply_symm_apply, φQ]
    calc
      eTen (eT.symm (b • eQ m)) =
          α (eBf (Ideal.Quotient.mk J b)) •
            eTen (eT.symm (eQ m)) := hmain'
      _ = ePullA (eBf (Ideal.Quotient.mk J b) •
            ePullA.symm (eTen (eT.symm (eQ m)))) := by
        change eBf (Ideal.Quotient.mk J b) •
            eTen (eT.symm (eQ m)) = _
        calc
          _ = eBf (Ideal.Quotient.mk J b) •
              ePullA (ePullA.symm (eTen (eT.symm (eQ m)))) := by
            rw [ePullA.apply_symm_apply]
          _ = _ := (ePull.map_smul (algebraMap Bf Af (eBf (Ideal.Quotient.mk J b))) _).symm
  have : Module.Flat Bf P := hfiberFlat
  exact Stacks.Flatness.flat_of_ringEquiv eBf φQ hφQ

/-- At a point where a quasi-coherent module of finite presentation has nonzero stalk, flatness
over the base together with flatness on the fibre is equivalent to flatness of the intermediate
scheme over the base together with flatness over the intermediate scheme. -/
@[stacks 039C "fibrewise criterion", ega "IV 11.3.10" "2°) a) ⇔ b)"]
public theorem isFlatOverBaseAndFiberAt_iff {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [LocallyOfFinitePresentation (f ≫ g)] [F.IsFinitePresentation]
    [LocallyOfFiniteType g]
    (x : X)
    (hx : ∃ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x,
      a ≠ 0) :
    IsFlatOverBaseAndFiberAt f g F x ↔ IsFlatOverIntermediateAt f g F x := by
  constructor
  · intro h
    let sFiber := (f ≫ g) x
    let z : (f ≫ g).fiber sFiber := (f ≫ g).asFiber x
    let iX := (f ≫ g).fiberι sFiber
    have hzx : iX z = x := (f ≫ g).fiberι_asFiber x
    let x' := iX z
    let y := f x'
    have hYPoint : y = f x := congrArg f hzx
    have hSPoint : (f ≫ g) x' = sFiber := congrArg (f ≫ g) hzx
    have hYbase : g y = sFiber := by
      simpa only [y, Scheme.Hom.comp_apply] using hSPoint
    let R := S.presheaf.stalk ((f ≫ g) x')
    let B := Y.presheaf.stalk y
    let A := X.presheaf.stalk x'
    let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x'
    have : Nontrivial M := by
      obtain ⟨a, ha⟩ := hx
      let eM := CategoryTheory.Iso.addCommGroupIsoToAddEquiv
        (TopCat.Presheaf.stalkCongr F.val.presheaf (.of_eq hzx))
      exact ⟨eM.symm a, 0, fun he => ha (by simpa using congrArg eM he)⟩
    let : Module A M := stalkModule F x'
    have : Module.FinitePresentation A M :=
      finitePresentation_stalk_pointEq F hzx (Stacks.SheafOfModules.finitePresentation_stalk F x)
    let : Algebra R B := (g.stalkMap y).hom.toAlgebra
    let : Algebra B A := (f.stalkMap x').hom.toAlgebra
    let : Algebra R A := ((f ≫ g).stalkMap x').hom.toAlgebra
    have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq' (by
      change ((f ≫ g).stalkMap x').hom =
        (f.stalkMap x').hom.comp (g.stalkMap y).hom
      exact congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f g x'))
    let : Module B M := Module.compHom _ (f.stalkMap x').hom
    let : Module R M := Module.compHom _ ((f ≫ g).stalkMap x').hom
    have : IsScalarTower B A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsScalarTower R B M := IsScalarTower.of_algebraMap_smul fun (r : R) (m : M) => by
      change (f.stalkMap x').hom ((g.stalkMap y).hom r) • m =
        ((f ≫ g).stalkMap x').hom r • m
      rw [Scheme.Hom.stalkMap_comp]
      rfl
    have : IsLocalHom (algebraMap R B) := inferInstanceAs (IsLocalHom (g.stalkMap y).hom)
    have : IsLocalHom (algebraMap B A) := inferInstanceAs (IsLocalHom (f.stalkMap x').hom)
    have : Algebra.EssFiniteType R B := LocallyOfFiniteType.stalkMap g y
    have : Module.Flat R M := flatOverAt_pointEq (f ≫ g).toLRSHom.toShHom F hzx h.1
    have : Module.Flat (B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B))
        (M ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R B) • (⊤ : Submodule B M))) :=
      flat_quotient_smul_top_of_fiber f g F x x' rfl h.2
    have hess : (algebraMap R A).EssentiallyOfFinitePresentation :=
      LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap (f ≫ g) x'
    obtain ⟨_, hB, hM⟩ :=
      Module.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient_maximalIdeal
        (R := R) (S := B) (S' := A) (M := M) hess
    exact ⟨flatAt_pointEq g.toLRSHom.toShHom hYPoint.symm hB,
      flatOverAt_pointEq f.toLRSHom.toShHom F hzx.symm hM⟩
  · exact fun h => ⟨isFlatOverAt_comp f g F x h.2 h.1, flatOver_fiber_of_flatOver f g F x h.2⟩

/-- For morphisms `f : X ⟶ Y` and `g : Y ⟶ S` of locally Noetherian schemes and a coherent
`𝒪_X`-module `F` with nonzero stalk at `x`, flatness over the base together with flatness on the
fibre is equivalent to flatness of `Y` over the base at `f x` together with flatness of `F` over
`Y` at `x`. -/
@[stacks 039B "Noetherian fibrewise criterion", ega "IV 11.3.10" "1°) a) ⇔ b)"]
public theorem isFlatOverBaseAndFiberAt_iff_of_isLocallyNoetherian {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [F.IsQuasicoherent] [Stacks.SheafOfModules.IsCoherent F]
    (x : X)
    (hx : ∃ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x,
      a ≠ 0) :
    IsFlatOverBaseAndFiberAt f g F x ↔ IsFlatOverIntermediateAt f g F x := by
  constructor
  · intro h
    let sFiber := (f ≫ g) x
    let z : (f ≫ g).fiber sFiber := (f ≫ g).asFiber x
    let iX := (f ≫ g).fiberι sFiber
    have hzx : iX z = x := (f ≫ g).fiberι_asFiber x
    let x' := iX z
    let y := f x'
    have hYPoint : y = f x := congrArg f hzx
    let R := S.presheaf.stalk ((f ≫ g) x')
    let B := Y.presheaf.stalk y
    let A := X.presheaf.stalk x'
    let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x'
    have : Nontrivial M := by
      obtain ⟨a, ha⟩ := hx
      let eM := CategoryTheory.Iso.addCommGroupIsoToAddEquiv
        (TopCat.Presheaf.stalkCongr F.val.presheaf (.of_eq hzx))
      exact ⟨eM.symm a, 0, fun he => ha (by simpa using congrArg eM he)⟩
    let : Module A M := stalkModule F x'
    have hfinite : Module.Finite A M :=
      have hft : F.IsFiniteType := Stacks.SheafOfModules.IsCoherent.isFiniteType
      @SheafOfModules.finite_stalk _ X.sheaf F hft x'
    let : Algebra R B := (g.stalkMap y).hom.toAlgebra
    let : Algebra B A := (f.stalkMap x').hom.toAlgebra
    let : Module B M := Module.compHom _ (f.stalkMap x').hom
    let : Module R M := Module.compHom _ ((f ≫ g).stalkMap x').hom
    have : IsScalarTower B A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsScalarTower R B M := IsScalarTower.of_algebraMap_smul fun (r : R) (m : M) => by
      change (f.stalkMap x').hom ((g.stalkMap y).hom r) • m =
        ((f ≫ g).stalkMap x').hom r • m
      rw [Scheme.Hom.stalkMap_comp]
      rfl
    have : IsLocalHom (algebraMap R B) := inferInstanceAs (IsLocalHom (g.stalkMap y).hom)
    have : IsLocalHom (algebraMap B A) := inferInstanceAs (IsLocalHom (f.stalkMap x').hom)
    have : Module.Flat R M := flatOverAt_pointEq (f ≫ g).toLRSHom.toShHom F hzx h.1
    have : Module.Flat (B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B))
        (M ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R B) • (⊤ : Submodule B M))) :=
      flat_quotient_smul_top_of_fiber f g F x x' rfl h.2
    obtain ⟨hB, hM⟩ :=
      Module.flat_and_flat_of_flat_quotient_maximalIdeal_of_flat
        (R := R) (S := B) (S' := A) (M := M)
    exact ⟨flatAt_pointEq g.toLRSHom.toShHom hYPoint.symm hB,
      flatOverAt_pointEq f.toLRSHom.toShHom F hzx.symm hM⟩
  · exact fun h => ⟨isFlatOverAt_comp f g F x h.2 h.1, flatOver_fiber_of_flatOver f g F x h.2⟩

end Stacks.Flatness

end
