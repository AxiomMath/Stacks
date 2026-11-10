module

public import StacksFrontier.CategoryTheory.Abelian.ExtTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.CategoryTheory.Abelian.ExtDirectedSystem
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionSectionsCorepresentation

/-!
# `Ext` along a directed system of schemes over a base

Let `S` be a scheme, `G` an abelian sheaf on `S_étale` and `(Y_i, y_i : Y_i ⟶ S)` a directed
system of schemes over `S`. For an abelian sheaf `M` on `S_étale` the groups
`Ext^m(y_i⁻¹M, y_i⁻¹G)` form a directed system of contravariant cohomology theories in `M`, whose
transition maps are restriction along `Y_{i'} ⟶ Y_i` read through the comparison of inverse images
along a composite. For `M = ℤ` these are the cohomology groups `H^m(Y_i, y_i⁻¹G)` of Stacks 09YQ.
This file sets up that system: the restriction maps `resK`, their functoriality (`resK_resK`),
their naturality in `M` and compatibility with connecting maps, and the restriction along a map
of systems which changes the base (`resK_restrictBase`), the device by which the cohomology of an
open subscheme enters the Mayer–Vietoris argument for Stacks 09YQ.

## Main definitions

* `Stacks.EtaleCohomology.LimitExt.resK`: restriction of `Ext^m(y⁻¹M, y⁻¹G)` along `f`, with
  `y' = f ≫ y`.
* `Stacks.EtaleCohomology.LimitExt.restrictBase`: restriction along `j' : W' ⟶ X'` from the
  system over `S` to a system over `W`, for `j : W ⟶ S` and a map `η : A ⟶ j⁻¹Q`.

## Main results

* `Stacks.EtaleCohomology.LimitExt.resK_resK`: restriction is functorial.
* `Stacks.EtaleCohomology.LimitExt.resK_restrictBase`: restriction along a map of systems commutes
  with the transition maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- The comparison `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` of inverse images of abelian étale sheaves, with the
composite carried as a named morphism. -/
abbrev K {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : fg = f ≫ g) :=
  etaleAbelianInverseImageCompIso'.{u, 0} f g fg h

/-- **The associativity pentagon, at a component.** -/
theorem K_hom_eq {X₀ X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₀) (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂)
    (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁) (hq : q = j ≫ i) (p : X₃ ⟶ X₀)
    (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a) (M : Sheaf X₀.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (K q f p hp₁).hom.app M =
      (K j a p hp₂).hom.app M ≫ (etaleAbelianInverseImage.{u, 0} j).map ((K i f a ha).hom.app M) ≫
        (K j i q hq).inv.app ((etaleAbelianInverseImage.{u, 0} f).obj M) := by
  have h := congrArg (fun e => e.inv.app M)
    (etaleAbelianInverseImageCompIso'_assoc.{u, 0} f i j a ha q hq p hp₁ hp₂)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.associator_hom_app] at h
  rw [← cancel_mono ((K j i q hq).hom.app ((etaleAbelianInverseImage.{u, 0} f).obj M)), h]
  simp

/-- The inverse form of `K_hom_eq`. -/
theorem K_inv_eq {X₀ X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₀) (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂)
    (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁) (hq : q = j ≫ i) (p : X₃ ⟶ X₀)
    (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a) (M : Sheaf X₀.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (K q f p hp₁).inv.app M =
      (K j i q hq).hom.app ((etaleAbelianInverseImage.{u, 0} f).obj M) ≫
        (etaleAbelianInverseImage.{u, 0} j).map ((K i f a ha).inv.app M) ≫
          (K j a p hp₂).inv.app M := by
  rw [← cancel_epi ((K q f p hp₁).hom.app M), Iso.hom_inv_id_app,
    K_hom_eq f i j a ha q hq p hp₁ hp₂ M]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

/-- Restriction of `Ext^m(y⁻¹M, y⁻¹G)` along `f`, for `y' = f ≫ y`: apply `f⁻¹` and read the
result through the comparison `y'⁻¹ ≅ y⁻¹ ⋙ f⁻¹`. -/
def resK {S X Y : Scheme.{u}} (f : Y ⟶ X) (y : X ⟶ S) (y' : Y ⟶ S) (h : y' = f ≫ y)
    (M G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj M)
        ((etaleAbelianInverseImage.{u, 0} y).obj G) n →+
      Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y').obj M)
        ((etaleAbelianInverseImage.{u, 0} y').obj G) n :=
  Stacks.ExtTransport.transport (etaleAbelianInverseImage.{u, 0} f) ((K f y y' h).hom.app M)
    ((K f y y' h).inv.app G) n

/-- **Restriction is functorial.** -/
theorem resK_resK {S X Y Z : Scheme.{u}} (f₁ : Y ⟶ X) (f₂ : Z ⟶ Y) (q : Z ⟶ X) (hq : q = f₂ ≫ f₁)
    (y : X ⟶ S) (a : Y ⟶ S) (ha : a = f₁ ≫ y) (p : Z ⟶ S) (hp : p = f₂ ≫ a) (hp' : p = q ≫ y)
    (M G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj M)
      ((etaleAbelianInverseImage.{u, 0} y).obj G) n) :
    resK f₂ a p hp M G n (resK f₁ y a ha M G n x) = resK q y p hp' M G n x := by
  simp only [resK]
  rw [Stacks.ExtTransport.transport_transport _ _ (etaleAbelianInverseImage.{u, 0} q)
    (K f₂ f₁ q hq)]
  rw [← K_hom_eq y f₁ f₂ a ha q hq p hp' hp M, ← K_inv_eq y f₁ f₂ a ha q hq p hp' hp G]

/-- Restriction is natural in the first variable. -/
theorem resK_mk₀_comp {S X Y : Scheme.{u}} (f : Y ⟶ X) (y : X ⟶ S) (y' : Y ⟶ S)
    (h : y' = f ≫ y) {B C G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (v : B ⟶ C)
    (n : ℕ) (x : Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj C)
      ((etaleAbelianInverseImage.{u, 0} y).obj G) n) :
    resK f y y' h B G n ((Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} y).map v)).comp x
        (zero_add n)) =
      (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} y').map v)).comp (resK f y y' h C G n x)
        (zero_add n) := by
  simp only [resK]
  have e : (K f y y' h).hom.app B ≫ (etaleAbelianInverseImage.{u, 0} f).map
      ((etaleAbelianInverseImage.{u, 0} y).map v) =
      (etaleAbelianInverseImage.{u, 0} y').map v ≫ (K f y y' h).hom.app C :=
    ((K f y y' h).hom.naturality v).symm
  rw [Stacks.ExtTransport.transport_mk₀_comp, e, Stacks.ExtTransport.transport_comp_left]

/-- Restriction commutes with the connecting maps of a short exact sequence. -/
theorem resK_extClass {S X Y : Scheme.{u}} (f : Y ⟶ X) (y : X ⟶ S) (y' : Y ⟶ S)
    (h : y' = f ≫ y) {T : ShortComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hT : T.ShortExact) (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj T.X₁)
      ((etaleAbelianInverseImage.{u, 0} y).obj G) n) :
    resK f y y' h T.X₃ G (n + 1)
        ((hT.map_of_exact (etaleAbelianInverseImage.{u, 0} y)).extClass.comp x (add_comm 1 n)) =
      (hT.map_of_exact (etaleAbelianInverseImage.{u, 0} y')).extClass.comp
        (resK f y y' h T.X₁ G n x) (add_comm 1 n) := by
  simp only [resK, Stacks.ExtTransport.transport_apply]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact Stacks.ExtTransport.sandwich_extClass_comp
    (hT.map_of_exact (etaleAbelianInverseImage.{u, 0} y'))
    ((hT.map_of_exact (etaleAbelianInverseImage.{u, 0} y)).map_of_exact
      (etaleAbelianInverseImage.{u, 0} f))
    (ShortComplex.mapNatTrans T (K f y y' h).hom) _ n _

/-- The cohomology class attached to a class of `Ext^n(y⁻¹ℤ, y⁻¹G)`, through the comparison
`y⁻¹ℤ ≅ ℤ`. -/
def toH {S Y : Scheme.{u}} (y : Y ⟶ S) (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) :
    Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj (zSheaf S))
        ((etaleAbelianInverseImage.{u, 0} y).obj G) n →+
      Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj G) n :=
  (Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} y).app
    (AddCommGrpCat.of (ULift ℤ))).inv).precomp _ (zero_add n)

/-- `toH y G n x` is the composite of `x` with the class of the comparison `ℤ ≅ y⁻¹ℤ`. -/
theorem toH_apply {S Y : Scheme.{u}} (y : Y ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj (zSheaf S))
      ((etaleAbelianInverseImage.{u, 0} y).obj G) n) :
    toH y G n x = (Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} y).app
      (AddCommGrpCat.of (ULift ℤ))).inv).comp x (zero_add n) := rfl

/-- The map `toH` from `Ext^n(y⁻¹ℤ, y⁻¹G)` to `H^n(Y, y⁻¹G)` is bijective. -/
theorem toH_bijective {S Y : Scheme.{u}} (y : Y ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Bijective (toH y G n) := by
  have e : (toH y G n : _ → _) = Stacks.ExtTransport.sandwich
      ((etaleAbelianInverseImageConstantIso.{u, 0} y).app (AddCommGrpCat.of (ULift ℤ))).inv
      (𝟙 ((etaleAbelianInverseImage.{u, 0} y).obj G)) n := by
    funext x
    rw [Stacks.ExtTransport.sandwich_apply, Ext.comp_mk₀_id, toH_apply]
  rw [e]
  exact Stacks.ExtTransport.sandwich_bijective _ _ n

/-- **Restriction on `Ext` out of `y⁻¹ℤ` is restriction on cohomology.** -/
theorem toH_resK {S X Y : Scheme.{u}} (f : Y ⟶ X) (y : X ⟶ S) (y' : Y ⟶ S) (h : y' = f ≫ y)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj (zSheaf S))
      ((etaleAbelianInverseImage.{u, 0} y).obj G) n) :
    toH y' G n (resK f y y' h (zSheaf S) G n x) =
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} f _ n (toH y G n x)).comp
        (Ext.mk₀ ((K f y y' h).inv.app G)) (add_zero n) := by
  have hc := etaleAbelianInverseImageConstantIso_comp.{u, 0} y f y' h (AddCommGrpCat.of (ULift ℤ))
  have hc' : ((etaleAbelianInverseImageConstantIso.{u, 0} y').app
        (AddCommGrpCat.of (ULift ℤ))).inv ≫ (K f y y' h).hom.app (zSheaf S) =
      ((etaleAbelianInverseImageConstantIso.{u, 0} f).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (etaleAbelianInverseImage.{u, 0} f).map
          ((etaleAbelianInverseImageConstantIso.{u, 0} y).app
            (AddCommGrpCat.of (ULift ℤ))).inv := by
    have hiso : (etaleAbelianInverseImage.{u, 0} f).mapIso
          ((etaleAbelianInverseImageConstantIso.{u, 0} y).app (AddCommGrpCat.of (ULift ℤ))) ≪≫
        (etaleAbelianInverseImageConstantIso.{u, 0} f).app (AddCommGrpCat.of (ULift ℤ)) =
        ((K f y y' h).app (zSheaf S)).symm ≪≫
          (etaleAbelianInverseImageConstantIso.{u, 0} y').app (AddCommGrpCat.of (ULift ℤ)) :=
      Iso.ext (by simpa using hc)
    have := congrArg Iso.inv hiso
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv, Iso.app_hom] at this
    exact this.symm
  rw [toH_apply, toH_apply, etaleCohomologyRestrictionMap_apply]
  simp only [resK, Stacks.ExtTransport.transport_apply, Stacks.ExtTransport.sandwich_apply]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, hc', ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
  simp only [Ext.comp_assoc_of_third_deg_zero]

/-- Changing the base along `s : S ⟶ S'`: `Ext^n(y'⁻¹M, y'⁻¹G)` for `y' = y ≫ s` is
`Ext^n(y⁻¹(s⁻¹M), y⁻¹(s⁻¹G))`, through the comparison of inverse images. -/
def conjBase {S S' Y : Scheme.{u}} (y : Y ⟶ S) (s : S ⟶ S') (y' : Y ⟶ S') (h : y' = y ≫ s)
    (M G : Sheaf S'.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y').obj M)
        ((etaleAbelianInverseImage.{u, 0} y').obj G) n →+
      Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj
          ((etaleAbelianInverseImage.{u, 0} s).obj M))
        ((etaleAbelianInverseImage.{u, 0} y).obj ((etaleAbelianInverseImage.{u, 0} s).obj G)) n :=
  Stacks.ExtTransport.sandwich ((K y s y' h).inv.app M) ((K y s y' h).hom.app G) n

/-- The change of base `conjBase` is bijective. -/
theorem conjBase_bijective {S S' Y : Scheme.{u}} (y : Y ⟶ S) (s : S ⟶ S') (y' : Y ⟶ S')
    (h : y' = y ≫ s) (M G : Sheaf S'.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Bijective (conjBase y s y' h M G n) :=
  Stacks.ExtTransport.sandwich_bijective _ _ n

/-- Changing the base commutes with restriction. -/
theorem resK_conjBase {S S' X Y : Scheme.{u}} (f : Y ⟶ X) (s : S ⟶ S') (y₁ : X ⟶ S)
    (y₂ : Y ⟶ S) (hy : y₂ = f ≫ y₁) (y₁' : X ⟶ S') (h₁ : y₁' = y₁ ≫ s) (y₂' : Y ⟶ S')
    (h₂ : y₂' = y₂ ≫ s) (hy' : y₂' = f ≫ y₁')
    (M G : Sheaf S'.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y₁').obj M)
      ((etaleAbelianInverseImage.{u, 0} y₁').obj G) n) :
    resK f y₁ y₂ hy _ _ n (conjBase y₁ s y₁' h₁ M G n x) =
      conjBase y₂ s y₂' h₂ M G n (resK f y₁' y₂' hy' M G n x) := by
  simp only [resK, conjBase]
  rw [Stacks.ExtTransport.transport_sandwich, Stacks.ExtTransport.sandwich_transport]
  have hα : (K f y₁ y₂ hy).hom.app ((etaleAbelianInverseImage.{u, 0} s).obj M) ≫
      (etaleAbelianInverseImage.{u, 0} f).map ((K y₁ s y₁' h₁).inv.app M) =
      (K y₂ s y₂' h₂).inv.app M ≫ (K f y₁' y₂' hy').hom.app M := by
    rw [K_inv_eq s y₁ f y₁' h₁ y₂ hy y₂' h₂ hy' M]
    simp
  have hβ : (etaleAbelianInverseImage.{u, 0} f).map ((K y₁ s y₁' h₁).hom.app G) ≫
      (K f y₁ y₂ hy).inv.app ((etaleAbelianInverseImage.{u, 0} s).obj G) =
      (K f y₁' y₂' hy').inv.app G ≫ (K y₂ s y₂' h₂).hom.app G := by
    rw [K_hom_eq s y₁ f y₁' h₁ y₂ hy y₂' h₂ hy' G]
    simp
  rw [hα, hβ]

/-- **Restriction to a system over another base.** For `j : W ⟶ S`, a map `η : A ⟶ j⁻¹Q` and a
commutative square `t = e ≫ j = j' ≫ g` with `j' : W' ⟶ X`, `g : X ⟶ S`, `e : W' ⟶ W`: restrict a
class of `Ext^n(g⁻¹Q, g⁻¹G)` along `j'`, precompose with `e⁻¹η` and read the result in
`Ext^n(e⁻¹A, e⁻¹(j⁻¹G))`. -/
def restrictBase {S W X W' : Scheme.{u}} (j : W ⟶ S) (g : X ⟶ S) (e : W' ⟶ W) (j' : W' ⟶ X)
    (t : W' ⟶ S) (ht₁ : t = e ≫ j) (ht₂ : t = j' ≫ g)
    {Q G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} j).obj Q) (n : ℕ) :
    Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} g).obj Q)
        ((etaleAbelianInverseImage.{u, 0} g).obj G) n →+
      Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} e).obj A)
        ((etaleAbelianInverseImage.{u, 0} e).obj ((etaleAbelianInverseImage.{u, 0} j).obj G)) n :=
  Stacks.ExtTransport.transport (etaleAbelianInverseImage.{u, 0} j')
    ((etaleAbelianInverseImage.{u, 0} e).map η ≫ (K e j t ht₁).inv.app Q ≫
      (K j' g t ht₂).hom.app Q)
    ((K j' g t ht₂).inv.app G ≫ (K e j t ht₁).hom.app G) n

/-- **Restriction to a system over another base commutes with the transition maps.** -/
theorem resK_restrictBase {S W X₁ X₂ W₁ W₂ : Scheme.{u}} (j : W ⟶ S) (g₁ : X₁ ⟶ S)
    (g₂ : X₂ ⟶ S) (f : X₂ ⟶ X₁) (hg : g₂ = f ≫ g₁) (e₁ : W₁ ⟶ W) (e₂ : W₂ ⟶ W) (f' : W₂ ⟶ W₁)
    (he : e₂ = f' ≫ e₁) (j₁ : W₁ ⟶ X₁) (j₂ : W₂ ⟶ X₂) (t₁ : W₁ ⟶ S) (ht₁ : t₁ = e₁ ≫ j)
    (ht₁' : t₁ = j₁ ≫ g₁) (t₂ : W₂ ⟶ S) (ht₂ : t₂ = e₂ ≫ j) (ht₂' : t₂ = j₂ ≫ g₂)
    (s : W₂ ⟶ X₁) (hs₁ : s = f' ≫ j₁) (hs₂ : s = j₂ ≫ f)
    {Q G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} j).obj Q) (n : ℕ)
    (x : Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} g₁).obj Q)
      ((etaleAbelianInverseImage.{u, 0} g₁).obj G) n) :
    resK f' e₁ e₂ he A _ n (restrictBase j g₁ e₁ j₁ t₁ ht₁ ht₁' η n x) =
      restrictBase j g₂ e₂ j₂ t₂ ht₂ ht₂' η n (resK f g₁ g₂ hg Q G n x) := by
  have ht₂f : t₂ = f' ≫ t₁ := by rw [ht₂, he, ht₁, Category.assoc]
  have hsg : t₂ = s ≫ g₁ := by rw [ht₂', hg, hs₂, Category.assoc]
  simp only [resK, restrictBase]
  rw [Stacks.ExtTransport.transport_transport _ _ (etaleAbelianInverseImage.{u, 0} s)
      (K f' j₁ s hs₁),
    Stacks.ExtTransport.transport_transport _ _ (etaleAbelianInverseImage.{u, 0} s)
      (K j₂ f s hs₂)]
  have h1 := K_hom_eq g₁ f j₂ g₂ hg s hs₂ t₂ hsg ht₂' Q
  have h2 := K_inv_eq j e₁ f' t₁ ht₁ e₂ he t₂ ht₂ ht₂f Q
  have h3 := K_hom_eq g₁ j₁ f' t₁ ht₁' s hs₁ t₂ hsg ht₂f Q
  have hnat := (K f' e₁ e₂ he).hom.naturality η
  simp only [Functor.comp_map] at hnat
  have hα : (K f' e₁ e₂ he).hom.app A ≫ (etaleAbelianInverseImage.{u, 0} f').map
      ((etaleAbelianInverseImage.{u, 0} e₁).map η ≫ (K e₁ j t₁ ht₁).inv.app Q ≫
        (K j₁ g₁ t₁ ht₁').hom.app Q) ≫ (K f' j₁ s hs₁).inv.app _ =
      ((etaleAbelianInverseImage.{u, 0} e₂).map η ≫ (K e₂ j t₂ ht₂).inv.app Q ≫
        (K j₂ g₂ t₂ ht₂').hom.app Q) ≫ (etaleAbelianInverseImage.{u, 0} j₂).map
          ((K f g₁ g₂ hg).hom.app Q) ≫ (K j₂ f s hs₂).inv.app _ := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← h1, h2, h3, ← reassoc_of% hnat]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have h4 := K_inv_eq g₁ f j₂ g₂ hg s hs₂ t₂ hsg ht₂' G
  have h5 := K_inv_eq g₁ j₁ f' t₁ ht₁' s hs₁ t₂ hsg ht₂f G
  have h6 := K_hom_eq j e₁ f' t₁ ht₁ e₂ he t₂ ht₂ ht₂f G
  have hβ : (K f' j₁ s hs₁).hom.app _ ≫ (etaleAbelianInverseImage.{u, 0} f').map
      ((K j₁ g₁ t₁ ht₁').inv.app G ≫ (K e₁ j t₁ ht₁).hom.app G) ≫ (K f' e₁ e₂ he).inv.app _ =
      (K j₂ f s hs₂).hom.app _ ≫ (etaleAbelianInverseImage.{u, 0} j₂).map
          ((K f g₁ g₂ hg).inv.app G) ≫ (K j₂ g₂ t₂ ht₂').inv.app G ≫
        (K e₂ j t₂ ht₂).hom.app G := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% h4, h5, h6]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hα, hβ]

/-! ### The theory of a system with a least index -/

/-- The group `Ext^m(y⁻¹M, y⁻¹G)`. -/
abbrev Th {S Y : Scheme.{u}} (y : Y ⟶ S) (M G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (m : ℕ) : Type (u + 1) :=
  Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} y).obj M)
    ((etaleAbelianInverseImage.{u, 0} y).obj G) m

section System

variable {J : Type u} [Preorder J] [OrderBot J] [IsDirected J (· ≤ ·)] (E : Jᵒᵖ ⥤ Scheme.{u})
  (c : Cone E)

/-- The map from a stage to the least stage. -/
abbrev toBot (i : J) : E.obj (op i) ⟶ E.obj (op ⊥) := E.map (homOfLE bot_le).op

/-- The transition map of the system. -/
abbrev trans {i i' : J} (h : i ≤ i') : E.obj (op i') ⟶ E.obj (op i) := E.map (homOfLE h).op

/-- The categories of abelian sheaves on the stages. -/
abbrev ShE (i : J) : Type (u + 2) := Sheaf (E.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}

/-- Inverse image to a stage. -/
def invBot (i : J) : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ ShE E i :=
  etaleAbelianInverseImage.{u, 0} (toBot E i)

/-- The inverse image `invBot E i` is additive. -/
instance invBot_additive (i : J) : (invBot E i).Additive :=
  inferInstanceAs (etaleAbelianInverseImage.{u, 0} (toBot E i)).Additive

/-- The inverse image `invBot E i` preserves finite limits. -/
instance invBot_preservesFiniteLimits (i : J) : PreservesFiniteLimits (invBot E i) :=
  inferInstanceAs (PreservesFiniteLimits (etaleAbelianInverseImage.{u, 0} (toBot E i)))

/-- The inverse image `invBot E i` preserves finite colimits. -/
instance invBot_preservesFiniteColimits (i : J) : PreservesFiniteColimits (invBot E i) :=
  inferInstanceAs (PreservesFiniteColimits (etaleAbelianInverseImage.{u, 0} (toBot E i)))

/-- Inverse image to the limit. -/
def invLim : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  etaleAbelianInverseImage.{u, 0} (c.π.app (op ⊥))

/-- The inverse image `invLim E c` is additive. -/
instance invLim_additive : (invLim E c).Additive :=
  inferInstanceAs (etaleAbelianInverseImage.{u, 0} (c.π.app (op ⊥))).Additive

/-- The inverse image `invLim E c` preserves finite limits. -/
instance invLim_preservesFiniteLimits : PreservesFiniteLimits (invLim E c) :=
  inferInstanceAs (PreservesFiniteLimits (etaleAbelianInverseImage.{u, 0} (c.π.app (op ⊥))))

/-- The inverse image `invLim E c` preserves finite colimits. -/
instance invLim_preservesFiniteColimits : PreservesFiniteColimits (invLim E c) :=
  inferInstanceAs (PreservesFiniteColimits (etaleAbelianInverseImage.{u, 0} (c.π.app (op ⊥))))

omit [IsDirected J (· ≤ ·)] in
/-- The map from stage `i'` to the least stage factors through the transition map to stage `i`. -/
theorem toBot_eq {i i' : J} (h : i ≤ i') : toBot E i' = trans E h ≫ toBot E i := by
  rw [← E.map_comp]
  exact congrArg E.map (Subsingleton.elim _ _)

omit [OrderBot J] [IsDirected J (· ≤ ·)] in
/-- The transition maps compose: `trans E (h.trans h') = trans E h' ≫ trans E h`. -/
theorem trans_trans {i i' i'' : J} (h : i ≤ i') (h' : i' ≤ i'') :
    trans E (h.trans h') = trans E h' ≫ trans E h := by
  rw [← E.map_comp]
  exact congrArg E.map (Subsingleton.elim _ _)

omit [IsDirected J (· ≤ ·)] in
/-- The cone projection to the least stage factors through the projection to stage `i`. -/
theorem cone_toBot (i : J) : c.π.app (op ⊥) = c.π.app (op i) ≫ toBot E i :=
  (c.w _).symm

omit [OrderBot J] [IsDirected J (· ≤ ·)] in
/-- The cone projection to stage `i` factors through the projection to stage `i'` and the
transition map. -/
theorem cone_trans {i i' : J} (h : i ≤ i') : c.π.app (op i) = c.π.app (op i') ≫ trans E h :=
  (c.w _).symm

/-- The comparison of `colim_i Ext^m(f_i⁻¹M, f_i⁻¹G)` with `Ext^m(f⁻¹M, f⁻¹G)` is an
isomorphism in every degree, where `f_i : E_i ⟶ E_⊥` and `f : lim E ⟶ E_⊥`: every class over the
limit comes from a stage, and a class at a stage vanishing over the limit vanishes at a later
stage. -/
abbrev Good (M G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  Stacks.ExtDirectedSystem.Good.{u + 1, u + 1, u + 1, u + 1, u + 2, u + 2, u + 2, u} (J := J)
    (𝒜 := Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (𝒞 := ShE E)
    (𝒞L := Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (invBot E) (invLim E c) G
    (fun h M m => resK (trans E h) _ _ (toBot_eq E h) M G m)
    (fun i M m => resK (c.π.app (op i)) _ _ (cone_toBot E c i) M G m) M

variable {E c}

omit [IsDirected J (· ≤ ·)] in
/-- Restriction along the transition maps of the system is functorial. -/
theorem resK_trans_trans {i i' i'' : J} (h : i ≤ i') (h' : i' ≤ i'')
    (M G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}) (m : ℕ) (x) :
    resK (trans E h') (toBot E i') (toBot E i'') (toBot_eq E h') M G m
        (resK (trans E h) (toBot E i) (toBot E i') (toBot_eq E h) M G m x) =
      resK (trans E (h.trans h')) (toBot E i) (toBot E i'') (toBot_eq E _) M G m x :=
  resK_resK _ _ _ (trans_trans E h h') _ _ _ _ _ _ _ _ _ _

omit [IsDirected J (· ≤ ·)] in
/-- Restriction along a transition map followed by restriction to the limit is restriction to
the limit. -/
theorem resK_cone_trans {i i' : J} (h : i ≤ i')
    (M G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}) (m : ℕ) (x) :
    resK (c.π.app (op i')) (toBot E i') (c.π.app (op ⊥)) (cone_toBot E c i') M G m
        (resK (trans E h) (toBot E i) (toBot E i') (toBot_eq E h) M G m x) =
      resK (c.π.app (op i)) (toBot E i) (c.π.app (op ⊥)) (cone_toBot E c i) M G m x :=
  resK_resK _ _ _ (cone_trans E c h) _ _ _ _ _ _ _ _ _ _

omit [IsDirected J (· ≤ ·)] in
/-- The comparison being an isomorphism for `M` implies the same for any `M'` isomorphic to `M`. -/
theorem good_of_iso {M M' G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : M ≅ M') (h : Good E c M G) : Good E c M' G := by
  refine Stacks.ExtDirectedSystem.good_of_iso.{u + 1, u + 1, u + 1, u + 1, u + 2, u + 2, u + 2, u}
    (J := J)
    (𝒜 := Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (𝒞 := ShE E)
    (𝒞L := Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (P := invBot E)
    (PL := invLim E c) (G := G)
    (τ := fun h M m => resK (trans E h) _ _ (toBot_eq E h) M G m)
    (lm := fun i M m => resK (c.π.app (op i)) _ _ (cone_toBot E c i) M G m)
    (fun {_ _} _ {_ _} v m x => resK_mk₀_comp _ _ _ _ v m x)
    (fun _ {_ _} v m x => resK_mk₀_comp _ _ _ _ v m x) e h

/-- **The five lemma for the system.** -/
theorem good_of_shortExact {T : ShortComplex (Sheaf (E.obj (op ⊥)).smallEtaleTopology
      AddCommGrpCat.{u + 1})} (hT : T.ShortExact)
    (G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (h₁ : Good E c T.X₁ G) (h₂ : Good E c T.X₂ G) : Good E c T.X₃ G := by
  refine Stacks.ExtDirectedSystem.good_of_shortExact.{u + 1, u + 1, u + 1, u + 1,
      u + 2, u + 2, u + 2, u} (J := J)
    (𝒜 := Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (𝒞 := ShE E)
    (𝒞L := Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (P := invBot E) (PL := invLim E c) (G := G)
    (τ := fun h M m => resK (trans E h) _ _ (toBot_eq E h) M G m)
    (lm := fun i M m => resK (c.π.app (op i)) _ _ (cone_toBot E c i) M G m)
    (fun h h' M m x => resK_trans_trans h h' M G m x)
    (fun hii' M m x => resK_cone_trans hii' M G m x)
    (fun {_ _} _ {_ _} v m x => resK_mk₀_comp _ _ _ _ v m x)
    (fun _ {_ _} v m x => resK_mk₀_comp _ _ _ _ v m x)
    (fun {_ _} _ {_} hT m x => resK_extClass _ _ _ _ hT G m x)
    (fun _ {_} hT m x => resK_extClass _ _ _ _ hT G m x) hT h₁ h₂

/-- The comparison passes to a direct sum. -/
theorem good_biprod {M₁ M₂ G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (h₁ : Good E c M₁ G) (h₂ : Good E c M₂ G) : Good E c (M₁ ⊞ M₂) G := by
  refine Stacks.ExtDirectedSystem.good_biprod.{u + 1, u + 1, u + 1, u + 1, u + 2, u + 2, u + 2, u}
    (J := J)
    (𝒜 := Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (𝒞 := ShE E)
    (𝒞L := Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (P := invBot E) (PL := invLim E c) (G := G)
    (τ := fun h M m => resK (trans E h) _ _ (toBot_eq E h) M G m)
    (lm := fun i M m => resK (c.π.app (op i)) _ _ (cone_toBot E c i) M G m) 
    (fun h h' M m x => resK_trans_trans h h' M G m x)
    (fun hii' M m x => resK_cone_trans hii' M G m x)
    (fun {_ _} _ {_ _} v m x => resK_mk₀_comp _ _ _ _ v m x)
    (fun _ {_ _} v m x => resK_mk₀_comp _ _ _ _ v m x) h₁ h₂

end System

end Stacks.EtaleCohomology.LimitExt
