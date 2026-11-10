module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityStalkGenerators
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf

/-!
# The Frobenius traces of the Tate twist `F(-1)`

Let `F` be a lisse ℓ-adic sheaf on a scheme `X` over a field in which `ℓ` is invertible, and `x`
a point of `X` with finite residue field `κ(x)`, `q = #κ(x)`. Pairing with compatible germs of
primitive `ℓⁿ⁺¹`-th roots of unity at the geometric point `x̄` identifies the level-`n` stalks of
`F(-1)` with those of `F`, compatibly with the transitions, so the ℓ-adic stalks are isomorphic;
under this isomorphism the geometric Frobenius `π_x` of `F(-1)` is `q` times that of `F`
(`Stacks.Kummer.twistNegOneFiberPairing_presheafFiber_hom`). Hence
`Tr(π_x^m | F(-1)) = q^m Tr(π_x^m | F)`
(`Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_twistNegOne_pow`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.SmallEtale GrothendieckTopology Stacks.InverseSystem
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section FiberTransition

variable {X : Scheme.{u}} (Φ : Point.{u} X.smallEtaleTopology) {R R' : Type} [Ring R] [Ring R']
  {P' : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R} {P : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R'}
  (t : ∀ U : X.Etale, ToType (P'.obj (op U)) → ToType (P.obj (op U)))
  (ht : ∀ {U V : X.Etale} (g : V ⟶ U) (z : ToType (P'.obj (op U))),
    t V (P'.map g.op z) = P.map g.op (t U z))

include ht in
/-- Germs of the images under `t` of sections with equal germs are equal. -/
theorem toPresheafFiber_app_eq_of_eq {U U' : X.Etale} (u : Φ.fiber.obj U) (u' : Φ.fiber.obj U')
    (z : ToType (P'.obj (op U))) (z' : ToType (P'.obj (op U')))
    (h : Φ.toPresheafFiber U u P' z = Φ.toPresheafFiber U' u' P' z') :
    Φ.toPresheafFiber U u P (t U z) = Φ.toPresheafFiber U' u' P (t U' z') := by
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u, u} R
  obtain ⟨W, w, g, g', rfl, rfl⟩ := Stacks.Kummer.exists_fiber_cone Φ u u'
  rw [Stacks.Kummer.toPresheafFiber_fiber_map Φ P' g,
    Stacks.Kummer.toPresheafFiber_fiber_map Φ P' g'] at h
  rw [Stacks.Kummer.toPresheafFiber_fiber_map Φ P g, Stacks.Kummer.toPresheafFiber_fiber_map Φ P g',
    ← ht, ← ht]
  obtain ⟨Y, f, y, rfl, hf⟩ := (Φ.toPresheafFiber_eq_iff' W _ _ _).1 h
  rw [Stacks.Kummer.toPresheafFiber_fiber_map Φ P f, Stacks.Kummer.toPresheafFiber_fiber_map Φ P f,
    ← ht, ← ht, hf]

/-- Every element of the stalk of `P'` at `Φ` is the germ of a section over some neighbourhood. -/
theorem exists_fiberTransition (y : ToType (Φ.presheafFiber.obj P')) :
    ∃ c : (U : X.Etale) × Φ.fiber.obj U × ToType (P'.obj (op U)),
      Φ.toPresheafFiber c.1 c.2.1 P' c.2.2 = y := by
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u, u} R
  obtain ⟨U, u, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective y
  exact ⟨⟨U, u, z⟩, rfl⟩

/-- **A natural family of maps of sections on stalks**: the germ of `t z` for a representative
`z`. -/
def fiberTransition (y : ToType (Φ.presheafFiber.obj P')) : ToType (Φ.presheafFiber.obj P) :=
  Φ.toPresheafFiber (exists_fiberTransition Φ y).choose.1 (exists_fiberTransition Φ y).choose.2.1 P
    (t _ (exists_fiberTransition Φ y).choose.2.2)

include ht in
/-- `fiberTransition` on germs. -/
theorem fiberTransition_germ {U : X.Etale} (u : Φ.fiber.obj U) (z : ToType (P'.obj (op U))) :
    fiberTransition Φ t (Φ.toPresheafFiber U u P' z) = Φ.toPresheafFiber U u P (t U z) :=
  toPresheafFiber_app_eq_of_eq Φ t ht _ _ _ _
    (exists_fiberTransition Φ (Φ.toPresheafFiber U u P' z)).choose_spec

end FiberTransition

section Levels

attribute [local instance] moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **The transition of an ℓ-adic sheaf on Mathlib's site, read back on Stacks 021B**: through
the units of the two equivalences it is the transition of the ℓ-adic sheaf. -/
theorem LAdicSheaf.unit_comp_inverse_map_etaleTransition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).unit.app
        (F.level (n + 1)) ≫
      (SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).inverse.map
          (LAdicSheaf.etaleTransition B X ℓ F n) =
    F.transition n ≫ (sheafCompose (SmallEtale.topology B X.1 X.property)
      (ModuleCat.restrictScalars.{u + 1} (levelCast ℓ n))).map
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).unit.app
          (F.level n)) := by
  let e' := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))
  let e := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
  let sc := sheafCompose (SmallEtale.topology B X.1 X.property)
    (ModuleCat.restrictScalars.{u + 1} (levelCast ℓ n))
  have h := sheafEquiv_inverse_map_sheafEquivRestrictScalarsIso_hom_app.{u} B X.1 X.property
    (levelCast ℓ n) (F.level n)
  have hnat : F.transition n ≫ e'.unit.app (sc.obj (F.level n)) =
      e'.unit.app (F.level (n + 1)) ≫ e'.inverse.map (e'.functor.map (F.transition n)) :=
    e'.unit.naturality (F.transition n)
  have hsc : sc.map (e.unit.app (F.level n)) ≫ sc.map (e.unitIso.inv.app (F.level n)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [LAdicSheaf.etaleTransition, Functor.map_comp, ← Category.assoc]
  refine (Iso.comp_inv_eq (e'.inverse.mapIso ((sheafEquivRestrictScalarsIso.{u} B X.1 X.property
    (levelCast ℓ n)).app (F.level n)))).2 ?_
  change _ = _ ≫ e'.inverse.map ((sheafEquivRestrictScalarsIso.{u} B X.1 X.property
    (levelCast ℓ n)).hom.app (F.level n))
  rw [h, ← hnat]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (F.transition n ≫ ·) ?_
  exact ((congrArg (· ≫ e'.unitIso.hom.app (sc.obj (F.level n))) hsc).trans
    (Category.id_comp _)).symm.trans (Category.assoc _ _ _)

section Stalks

variable (t : GeometricPoint X.1)

/-- The germ of a section of a level of an ℓ-adic sheaf, as an element of the finite-level
stalk. -/
def LAdicSheaf.levelGerm (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    (U : SmallEtale B X.1 X.property) (x : (geometricPointFiber B X.1 X.property t).obj U)
    (σ : ToType ((F.level n).obj.obj (op U))) : finiteLevelStalk B X ℓ F t n :=
  (geometricSitePoint B X t).toPresheafFiber U x (F.level n).obj σ

/-- **The transition between finite-level stalks on germs.** -/
theorem LAdicSheaf.stalkTransition_germ (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    (U : SmallEtale B X.1 X.property) (x : (geometricPointFiber B X.1 X.property t).obj U)
    (σ : ToType ((F.level (n + 1)).obj.obj (op U))) :
    LAdicSheaf.stalkTransition B X ℓ F t n
        ((geometricSitePoint B X t).toPresheafFiber U x (F.level (n + 1)).obj σ) =
      (geometricSitePoint B X t).toPresheafFiber U x (F.level n).obj
        ((F.transition n).hom.app (op U) σ) := by
  have h3 : (geometricSitePoint B X t).toPresheafFiber U x (F.level (n + 1)).obj ≫
      finiteLevelStalkTransition B X ℓ F t n =
        (F.transition n).hom.app (op U) ≫ (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
          ((geometricSitePoint B X t).toPresheafFiber U x (F.level n).obj) := by
    change colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.property t)).op ⋙
        (F.level (n + 1)).obj) (op ((geometricPointFiber B X.1 X.property t).elementsMk U x)) ≫
          finiteLevelStalkTransition B X ℓ F t n =
      (F.transition n).hom.app (op U) ≫ (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
        (colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.property t)).op ⋙
          (F.level n).obj) (op ((geometricPointFiber B X.1 X.property t).elementsMk U x)))
    let R := ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)
    let E := (Functor.Elements.π (geometricPointFiber B X.1 X.property t)).op ⋙ (F.level n).obj
    let w := Functor.whiskerLeft
      (Functor.Elements.π (geometricPointFiber B X.1 X.property t)).op (F.transition n).hom
    let L := op ((geometricPointFiber B X.1 X.property t).elementsMk U x)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (preservesColimitIso R E).inv)
      (colimit.ι_map w L)).trans ((Category.assoc _ _ _).trans
        (congrArg (w.app L ≫ ·) (ι_preservesColimitIso_inv R E L))))
  exact ConcreteCategory.congr_hom h3 σ

omit [AlgebraicGeometry.IsNoetherian X.1] in
/-- **The stalk comparison of the two small étale sites on germs**, in the direction from
Mathlib's site. -/
theorem sheafEquivCompSheafFiberIso_hom_germ (Λ : Type) [CommRing Λ]
    (P : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
    (U : SmallEtale B X.1 X.property) (x : (geometricPointFiber B X.1 X.property t).obj U)
    (σ : ToType (P.obj.obj (op U))) :
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).hom.app P)
        ((Scheme.pointSmallEtale t.hom).toPresheafFiber
          ((SmallEtale.toEtaleSite B X.1 X.property).obj U)
          ((toEtaleSiteFiberIso B X.1 X.property t).inv.app U x)
          ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).functor.obj P).obj
          (((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).unit.app P).hom.app
            (op U) σ)) =
      (geometricSitePoint B X t).toPresheafFiber U x P.obj σ := by
  have h := toPresheafFiber_sheafEquivCompSheafFiberIso_inv.{u, u + 1, 0} B X Λ t P U x
  have e1 := ConcreteCategory.congr_hom h σ
  have e2 := ConcreteCategory.congr_hom
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).app P).inv_hom_id
    ((geometricSitePoint B X t).toPresheafFiber U x P.obj σ)
  exact (congrArg ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).hom.app P) e1.symm).trans e2

omit [AlgebraicGeometry.IsNoetherian X.1] in
/-- **The stalk comparison intertwines the actions of an endomorphism of the geometric point.** -/
theorem sheafEquivCompSheafFiberIso_hom_presheafFiber_hom (Λ : Type) [CommRing Λ]
    (a : GeometricPoint.Hom t t)
    (P : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
    (y : ToType ((Scheme.pointSmallEtale t.hom).presheafFiber.obj
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).functor.obj P).obj)) :
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).hom.app P)
        ((Point.Hom.presheafFiber (smallEtalePointHom X.1 a)).app
          ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).functor.obj P).obj y) =
      ((geometricPointStalkMap B X.1 X.property a (ModuleCat.{u + 1} Λ)).app P.obj)
        (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).hom.app P) y) := by
  have hn := NatTrans.congr_app (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B X Λ a) P
  have e1 := ConcreteCategory.congr_hom hn
    (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).hom.app P) y)
  have e2 := ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).app P).hom_inv_id_apply y
  have e3 := ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).app P).inv_hom_id_apply
    (((geometricPointStalkMap B X.1 X.property a (ModuleCat.{u + 1} Λ)).app P.obj)
      (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).hom.app P) y))
  change ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).inv.app P ≫ _) _ =
    (_ ≫ (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).inv.app P) _ at e1
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e1
  change ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).inv.app P)
    (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).hom.app P) y) = y at e2
  change ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).hom.app P)
    (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).inv.app P) _) = _ at e3
  rw [e2] at e1
  exact (congrArg ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).hom.app P) e1).trans e3

/-- The transition `Fₙ₊₁ ⟶ res Fₙ` on Mathlib's site, on sections. -/
def LAdicSheaf.etaleTransitionFun (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) (U : X.1.Etale)
    (z : ToType ((LAdicSheaf.etaleLevel B X ℓ F (n + 1)).obj.obj (op U))) :
    ToType ((LAdicSheaf.etaleLevel B X ℓ F n).obj.obj (op U)) :=
  (LAdicSheaf.etaleTransition B X ℓ F n).hom.app (op U) z

/-- `Stacks.EtaleCohomology.LAdicSheaf.etaleTransitionFun` commutes with restriction of
sections. -/
theorem LAdicSheaf.etaleTransitionFun_naturality (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    {U V : X.1.Etale} (g : V ⟶ U)
    (z : ToType ((LAdicSheaf.etaleLevel B X ℓ F (n + 1)).obj.obj (op U))) :
    LAdicSheaf.etaleTransitionFun F n V ((LAdicSheaf.etaleLevel B X ℓ F (n + 1)).obj.map g.op z) =
      (LAdicSheaf.etaleLevel B X ℓ F n).obj.map g.op (LAdicSheaf.etaleTransitionFun F n U z) :=
  NatTrans.naturality_apply (LAdicSheaf.etaleTransition B X ℓ F n).hom g.op z

/-- **The transition of finite-level stalks, read on Mathlib's site**: under the stalk comparison
it is the map of stalks induced by `Fₙ₊₁ ⟶ res Fₙ` on Mathlib's site. -/
theorem LAdicSheaf.stalkTransition_sheafEquivCompSheafFiberIso (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (n : ℕ) (y : ToType ((Scheme.pointSmallEtale t.hom).presheafFiber.obj
      (LAdicSheaf.etaleLevel B X ℓ F (n + 1)).obj)) :
    LAdicSheaf.stalkTransition B X ℓ F t n
        (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1 + 1))) t).hom.app
          (F.level (n + 1))) y) =
      ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).hom.app (F.level n))
        (fiberTransition (Scheme.pointSmallEtale t.hom) (LAdicSheaf.etaleTransitionFun F n) y) := by
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u, u}
    (ZMod (ℓ ^ (n + 1 + 1)))
  obtain ⟨U, x, σ, hb⟩ := (geometricSitePoint B X t).toPresheafFiber_jointly_surjective
    (P := (F.level (n + 1)).obj)
    (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1 + 1))) t).hom.app
      (F.level (n + 1))) y)
  have hy : y = (Scheme.pointSmallEtale t.hom).toPresheafFiber
      ((SmallEtale.toEtaleSite B X.1 X.property).obj U)
      ((toEtaleSiteFiberIso B X.1 X.property t).inv.app U x)
      ((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).functor.obj (F.level (n + 1))).obj
      (((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).unit.app (F.level (n + 1))).hom.app
          (op U) σ) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1 + 1))) t).hom.app
        (F.level (n + 1)))).1
    exact hb.symm.trans (sheafEquivCompSheafFiberIso_hom_germ t _ (F.level (n + 1)) U x σ).symm
  have hs := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom
    (LAdicSheaf.unit_comp_inverse_map_etaleTransition F n)) (op U)) σ
  have hs' : (LAdicSheaf.etaleTransition B X ℓ F n).hom.app
      (op ((SmallEtale.toEtaleSite B X.1 X.property).obj U))
      (((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).unit.app (F.level (n + 1))).hom.app
          (op U) σ) =
      ((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).unit.app (F.level n)).hom.app (op U)
          ((F.transition n).hom.app (op U) σ) := hs
  have hf : fiberTransition (Scheme.pointSmallEtale t.hom) (LAdicSheaf.etaleTransitionFun F n) y =
        (Scheme.pointSmallEtale t.hom).toPresheafFiber
          ((SmallEtale.toEtaleSite B X.1 X.property).obj U)
          ((toEtaleSiteFiberIso B X.1 X.property t).inv.app U x)
          ((SmallEtale.sheafEquiv B X.1 X.property
            (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.obj (F.level n)).obj
          (((SmallEtale.sheafEquiv B X.1 X.property
            (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).unit.app (F.level n)).hom.app (op U)
              ((F.transition n).hom.app (op U) σ)) := by
    rw [hy]
    exact (fiberTransition_germ _ _ (LAdicSheaf.etaleTransitionFun_naturality F n) _ _).trans
      (congrArg _ hs')
  rw [hf]
  exact ((congrArg (LAdicSheaf.stalkTransition B X ℓ F t n) hb.symm).trans
    (LAdicSheaf.stalkTransition_germ t F n U x σ)).trans
      (sheafEquivCompSheafFiberIso_hom_germ t _ (F.level n) U x _).symm

omit [AlgebraicGeometry.IsNoetherian X.1] in
/-- **A comparison of stalks through `P ⟶ e⁻¹ T` and the counit intertwines the actions of an
endomorphism of the geometric point.** -/
theorem stalkComparison_stalkEnd (Λ : Type) [CommRing Λ] (a : GeometricPoint.Hom t t)
    (P : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
    (T : Sheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : P ⟶ (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).inverse.obj T)
    (y : ToType ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ t).obj P)) :
    ((Scheme.pointSmallEtale t.hom).sheafFiber.map
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).counit.app T))
      (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).inv.app _)
        (((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ t).map φ)
          (((geometricPointStalkMap B X.1 X.property a (ModuleCat.{u + 1} Λ)).app P.obj) y))) =
      (Point.Hom.presheafFiber (smallEtalePointHom X.1 a)).app T.obj
        (((Scheme.pointSmallEtale t.hom).sheafFiber.map
          ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).counit.app T))
          (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).inv.app _)
            (((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ t).map φ) y))) := by
  let e := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)
  have hA := ConcreteCategory.congr_hom
    ((geometricPointStalkMap B X.1 X.property a (ModuleCat.{u + 1} Λ)).naturality φ.hom) y
  have hB := ConcreteCategory.congr_hom (NatTrans.congr_app
    (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B X Λ a) (e.inverse.obj T))
    (((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ t).map φ) y)
  have hC := ConcreteCategory.congr_hom
    ((Point.Hom.presheafFiber (A := ModuleCat.{u + 1} Λ) (smallEtalePointHom X.1 a)).naturality
      (e.counit.app T).hom)
    (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).inv.app _)
      (((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ t).map φ) y))
  exact (congrArg (fun z => ((Scheme.pointSmallEtale t.hom).sheafFiber.map (e.counit.app T))
    (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ t).inv.app _) z)) hA.symm).trans
      ((congrArg ((Scheme.pointSmallEtale t.hom).sheafFiber.map (e.counit.app T)) hB.symm).trans
        hC.symm)

end Stalks

section Twist

attribute [local instance] neZero_pow_of_fact_prime neZero_natCast_pow

variable {k : Type u} [Field k] (fX : X.1 ⟶ Spec (.of k)) [NeZero (ℓ : k)]
  {F : LAdicSheaf.{u, u + 1} B X ℓ} (hF : F.IsLisse) (t : GeometricPoint X.1)

/-- **The level-`n` stalk of `F(-1)` is the stalk of `𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` on Mathlib's site.** -/
def LAdicSheaf.twistNegOneStalkIso (n : ℕ) :
    finiteLevelStalk B X ℓ (LAdicSheaf.twistNegOne fX hF) t n ≅
      (Scheme.pointSmallEtale t.hom).presheafFiber.obj (LAdicSheaf.twistNegOneLevel F n).obj :=
  (etaleModuleStalkFunctor.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).mapIso
      (LAdicSheaf.strictTowerLevelTwistIso fX F n) ≪≫
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).app _).symm ≪≫
    (Scheme.pointSmallEtale t.hom).sheafFiber.mapIso
      ((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).counitIso.app
          (LAdicSheaf.twistNegOneLevel F n))

/-- The germ formula for `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneStalkIso`: the germ of a
section `σ` of `𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` at a neighbourhood of the bounded site goes to its germ at the
same neighbourhood of Mathlib's site. -/
theorem LAdicSheaf.twistNegOneStalkIso_hom_germ (n : ℕ) (U : SmallEtale B X.1 X.property)
    (x : (geometricPointFiber B X.1 X.property t).obj U)
    (σ : ToType ((LAdicSheaf.twistNegOneLevel F n).obj.obj
      (op ((SmallEtale.toEtaleSite B X.1 X.property).obj U)))) :
    (LAdicSheaf.twistNegOneStalkIso fX hF t n).hom
        ((geometricSitePoint B X t).toPresheafFiber U x
          ((LAdicSheaf.twistNegOne fX hF).level n).obj σ) =
      (Scheme.pointSmallEtale t.hom).toPresheafFiber
        ((SmallEtale.toEtaleSite B X.1 X.property).obj U)
        ((toEtaleSiteFiberIso B X.1 X.property t).inv.app U x)
        (LAdicSheaf.twistNegOneLevel F n).obj σ := by
  let e := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
  let T := LAdicSheaf.twistNegOneLevel F n
  have e1 : ((etaleModuleStalkFunctor.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).map
      (LAdicSheaf.strictTowerLevelTwistIso fX F n).hom)
        ((geometricSitePoint B X t).toPresheafFiber U x
          ((LAdicSheaf.twistNegOne fX hF).level n).obj σ) =
      (geometricSitePoint B X t).toPresheafFiber U x (e.inverse.obj T).obj σ :=
    Point.toPresheafFiber_naturality_apply (geometricSitePoint B X t)
      (LAdicSheaf.strictTowerLevelTwistIso fX F n).hom.hom U x σ
  have e2 := ConcreteCategory.congr_hom
    (toPresheafFiber_sheafEquivCompSheafFiberIso_inv.{u, u + 1, 0}
      B X (ZMod (ℓ ^ (n + 1))) t (e.inverse.obj T) U x) σ
  have e3 := Point.toPresheafFiber_naturality_apply (Scheme.pointSmallEtale t.hom)
    (e.counit.app T).hom ((SmallEtale.toEtaleSite B X.1 X.property).obj U)
    ((toEtaleSiteFiberIso B X.1 X.property t).inv.app U x)
    ((e.unit.app (e.inverse.obj T)).hom.app (op U) σ)
  have e4 : (e.counit.app T).hom.app (op ((SmallEtale.toEtaleSite B X.1 X.property).obj U))
      ((e.unit.app (e.inverse.obj T)).hom.app (op U) σ) = σ :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg InducedCategory.Hom.hom (e.unit_inverse_comp T)) (op U)) σ
  exact (congrArg ((Scheme.pointSmallEtale t.hom).sheafFiber.map (e.counit.app T))
    ((congrArg ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).inv.app
      (e.inverse.obj T)) e1).trans e2)).trans (e3.trans (congrArg _ e4))

/-- The transition of `F(-1)` on sections is the transition of the twisted tower. -/
theorem LAdicSheaf.twistNegOne_transition_app (n : ℕ) (U : SmallEtale B X.1 X.property)
    (σ : ToType (((LAdicSheaf.twistNegOne fX hF).level (n + 1)).obj.obj (op U))) :
    ((LAdicSheaf.twistNegOne fX hF).transition n).hom.app (op U) σ =
      (LAdicSheaf.twistNegOneTransition fX F n).hom.app
        (op ((SmallEtale.toEtaleSite B X.1 X.property).obj U)) σ := by
  have h := congrArg (fun φ => (φ.hom.app (op U)).hom σ)
    (underlyingLevelFunctor_map_strictTowerTransition (LAdicSheaf.twistNegOneTower fX F)
      (LAdicSheaf.twistNegOneTower_isStrict fX F) n)
  refine h.trans ?_
  change ((LAdicSheaf.twistNegOneTower fX F).map (homOfLE (n.le_add_right 1)).op).hom.app
    (op ((SmallEtale.toEtaleSite B X.1 X.property).obj U)) σ = _
  rw [LAdicSheaf.twistNegOneTower_map_succ fX F n]
  rfl

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
variable (ℓ) in
include fX in
/-- There are points `vₙ` of the stalk at `t` over the cyclotomic covers and exponents `jₙ` making
`ζₙ ^ jₙ` primitive `ℓⁿ⁺¹`-th roots of unity, such that the germs at `vₙ` of the corresponding root
sections are compatible under the `ℓ`-th power maps `μ_{ℓⁿ⁺²} ⟶ μ_{ℓⁿ⁺¹}`. -/
theorem LAdicSheaf.exists_twistGens :
    ∃ (v : ∀ n : ℕ, (Scheme.pointSmallEtale t.hom).fiber.obj
        (Stacks.Kummer.cyclotomicBaseChange fX (ℓ ^ (n + 1)) (Scheme.Etale.mk (𝟙 X.1)))) (j : ℕ → ℕ)
      (hj : ∀ n, IsPrimitiveRoot (Stacks.Kummer.cyclotomicZeta (k := k) ℓ n ^ j n) (ℓ ^ (n + 1))),
      ∀ n, (Scheme.pointSmallEtale t.hom).toPresheafFiber _ (v (n + 1))
          (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))).obj
          ((Stacks.Kummer.rootsOfUnityModulePowMap.{u, 0} X.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1))
            (pow_succ' ℓ (n + 1)).symm).hom.app (op _)
            (Stacks.Kummer.rootSection (ℓ ^ (n + 1 + 1))
              (Stacks.Kummer.cyclotomicBaseChangeStructMap fX (ℓ ^ (n + 1 + 1))
                (Scheme.Etale.mk (𝟙 X.1)))
              (hj (n + 1)) 1)) =
        (Scheme.pointSmallEtale t.hom).toPresheafFiber _ (v n)
          (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))).obj
          (Stacks.Kummer.rootSection (ℓ ^ (n + 1))
            (Stacks.Kummer.cyclotomicBaseChangeStructMap fX (ℓ ^ (n + 1)) (Scheme.Etale.mk (𝟙 X.1)))
            (hj n) 1) :=
  Stacks.Kummer.exists_compatible_rootGerms t.hom fX ℓ (U₀ := Scheme.Etale.mk (𝟙 X.1))
    (Over.homMk t.hom)

variable (ℓ) in
/-- The lifts of the compatible germs of primitive roots of unity at `t`. -/
noncomputable def LAdicSheaf.twistGenV (fX : X.1 ⟶ Spec (.of k)) (t : GeometricPoint X.1) (n : ℕ) :
    (Scheme.pointSmallEtale t.hom).fiber.obj
      (Stacks.Kummer.cyclotomicBaseChange fX (ℓ ^ (n + 1)) (Scheme.Etale.mk (𝟙 X.1))) :=
  (LAdicSheaf.exists_twistGens ℓ fX t).choose n

variable (ℓ) in
/-- The exponents of the compatible germs of primitive roots of unity at `t`. -/
noncomputable def LAdicSheaf.twistGenJ (fX : X.1 ⟶ Spec (.of k)) (t : GeometricPoint X.1) (n : ℕ) :
    ℕ := (LAdicSheaf.exists_twistGens ℓ fX t).choose_spec.choose n

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
variable (ℓ) in
/-- `ζₙ ^ twistGenJ n` is a primitive `ℓⁿ⁺¹`-th root of unity. -/
theorem LAdicSheaf.twistGen_isPrimitiveRoot (n : ℕ) :
    IsPrimitiveRoot (Stacks.Kummer.cyclotomicZeta (k := k) ℓ n ^ LAdicSheaf.twistGenJ ℓ fX t n)
      (ℓ ^ (n + 1)) :=
  (LAdicSheaf.exists_twistGens ℓ fX t).choose_spec.choose_spec.choose n

variable (ℓ) in
/-- **The compatible generators `eₙ` of the stalks of `μ_{ℓⁿ⁺¹}` at `t`.** -/
noncomputable def LAdicSheaf.twistGen (n : ℕ) :
    ToType ((Scheme.pointSmallEtale t.hom).presheafFiber.obj
      (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))).obj) :=
  (Scheme.pointSmallEtale t.hom).toPresheafFiber _ (LAdicSheaf.twistGenV ℓ fX t n)
    (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))).obj
    (Stacks.Kummer.rootSection (ℓ ^ (n + 1))
      (Stacks.Kummer.cyclotomicBaseChangeStructMap fX (ℓ ^ (n + 1)) (Scheme.Etale.mk (𝟙 X.1)))
      (LAdicSheaf.twistGen_isPrimitiveRoot ℓ fX t n) 1)

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
variable (ℓ) in
/-- The `ℓ`-th power map `μ_{ℓⁿ⁺²} ⟶ μ_{ℓⁿ⁺¹}` carries the generator `eₙ₊₁` to `eₙ` on stalks. -/
theorem LAdicSheaf.twistGen_compat (n : ℕ) :
    (Scheme.pointSmallEtale t.hom).toPresheafFiber _ (LAdicSheaf.twistGenV ℓ fX t (n + 1))
        (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))).obj
        ((Stacks.Kummer.rootsOfUnityModulePowMap.{u, 0} X.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1))
          (pow_succ' ℓ (n + 1)).symm).hom.app (op _)
          (Stacks.Kummer.rootSection (ℓ ^ (n + 1 + 1))
            (Stacks.Kummer.cyclotomicBaseChangeStructMap fX (ℓ ^ (n + 1 + 1))
              (Scheme.Etale.mk (𝟙 X.1)))
              (LAdicSheaf.twistGen_isPrimitiveRoot ℓ fX t (n + 1)) 1)) =
      LAdicSheaf.twistGen ℓ fX t n :=
  (LAdicSheaf.exists_twistGens ℓ fX t).choose_spec.choose_spec.choose_spec n

variable (ℓ) in
/-- The `ℓ`-th power map `μ_{ℓⁿ⁺²} ⟶ μ_{ℓⁿ⁺¹}` on sections. -/
def rootsPowFun (n : ℕ) (V : X.1.Etale)
    (r : ToType ((Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1 + 1))).obj.obj (op V))) :
    ToType ((Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))).obj.obj (op V)) :=
  (Stacks.Kummer.rootsOfUnityModulePowMap.{u, 0} X.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1))
    (pow_succ' ℓ (n + 1)).symm).hom.app (op V) r

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
variable (ℓ) in
/-- `Stacks.EtaleCohomology.rootsPowFun` commutes with restriction of sections. -/
theorem rootsPowFun_naturality (n : ℕ) {U V : X.1.Etale} (g : V ⟶ U)
    (r : ToType ((Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1 + 1))).obj.obj (op U))) :
    rootsPowFun (X := X) ℓ n V
        ((Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1 + 1))).obj.map g.op r) =
      (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))).obj.map g.op
        (rootsPowFun (X := X) ℓ n U r) :=
  NatTrans.naturality_apply (Stacks.Kummer.rootsOfUnityModulePowMap.{u, 0} X.1 ℓ (ℓ ^ (n + 1))
    (ℓ ^ (n + 1 + 1)) (pow_succ' ℓ (n + 1)).symm).hom g.op r

variable (F) in
/-- The transition of the twisted tower on sections. -/
def LAdicSheaf.twistTransitionFun (n : ℕ) (U : X.1.Etale)
    (z : ToType ((LAdicSheaf.twistNegOneLevel F (n + 1)).obj.obj (op U))) :
    ToType ((LAdicSheaf.twistNegOneLevel F n).obj.obj (op U)) :=
  (LAdicSheaf.twistNegOneTransition fX F n).hom.app (op U) z

variable (F) in
/-- `Stacks.EtaleCohomology.LAdicSheaf.twistTransitionFun` commutes with restriction of
sections. -/
theorem LAdicSheaf.twistTransitionFun_naturality (n : ℕ) {U V : X.1.Etale} (g : V ⟶ U)
    (z : ToType ((LAdicSheaf.twistNegOneLevel F (n + 1)).obj.obj (op U))) :
    LAdicSheaf.twistTransitionFun fX F n V
        ((LAdicSheaf.twistNegOneLevel F (n + 1)).obj.map g.op z) =
      (LAdicSheaf.twistNegOneLevel F n).obj.map g.op (LAdicSheaf.twistTransitionFun fX F n U z) :=
  NatTrans.naturality_apply (LAdicSheaf.twistNegOneTransition fX F n).hom g.op z

variable (F) in
/-- **The transitions of the twist and of `F` on stalks are compatible with the pairings** with
germs `e` and `e^ℓ` of roots of unity. -/
theorem LAdicSheaf.fiberTransition_twistPairing (n : ℕ)
    (b : ToType ((Scheme.pointSmallEtale t.hom).presheafFiber.obj
      (LAdicSheaf.twistNegOneLevel F (n + 1)).obj)) {V : X.1.Etale}
    (v : (Scheme.pointSmallEtale t.hom).fiber.obj V)
    (r : ToType ((Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1 + 1))).obj.obj (op V))) :
    fiberTransition (Scheme.pointSmallEtale t.hom) (LAdicSheaf.etaleTransitionFun F n)
        (Stacks.Kummer.fiberPairing (Scheme.pointSmallEtale t.hom)
          (fun U α s => Stacks.Kummer.twistNegOneModulePairing.{u, 0} X.1 (ℓ ^ (n + 1 + 1))
            (LAdicSheaf.etaleLevel B X ℓ F (n + 1)) U α s) b
          ((Scheme.pointSmallEtale t.hom).toPresheafFiber V v
            (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1 + 1))).obj r)) =
      Stacks.Kummer.fiberPairing (Scheme.pointSmallEtale t.hom)
        (fun U α s => Stacks.Kummer.twistNegOneModulePairing.{u, 0} X.1 (ℓ ^ (n + 1))
          (LAdicSheaf.etaleLevel B X ℓ F n) U α s)
        (fiberTransition (Scheme.pointSmallEtale t.hom) (LAdicSheaf.twistTransitionFun fX F n) b)
        ((Scheme.pointSmallEtale t.hom).toPresheafFiber V v
          (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))).obj
          (rootsPowFun (X := X) ℓ n V r)) := by
  let Φ := Scheme.pointSmallEtale t.hom
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u, u}
    (ZMod (ℓ ^ (n + 1 + 1)))
  obtain ⟨U, u, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective b
  obtain ⟨W, w, g, h, rfl, rfl⟩ := Stacks.Kummer.exists_fiber_cone Φ u v
  rw [Stacks.Kummer.toPresheafFiber_fiber_map Φ _ g, Stacks.Kummer.toPresheafFiber_fiber_map Φ _ h,
    Stacks.Kummer.toPresheafFiber_fiber_map Φ _ h,
    (rootsPowFun_naturality (X := X) ℓ n h r).symm,
    Stacks.Kummer.fiberPairing_germ Φ _
      (Stacks.Kummer.twistNegOneModulePairing_naturality.{u, 0} _ _ _),
    fiberTransition_germ _ _ (LAdicSheaf.etaleTransitionFun_naturality F n),
    fiberTransition_germ _ _ (LAdicSheaf.twistTransitionFun_naturality fX F n),
    Stacks.Kummer.fiberPairing_germ Φ _
      (Stacks.Kummer.twistNegOneModulePairing_naturality.{u, 0} _ _ _)]
  exact congrArg _ (Stacks.Kummer.twistNegOneModulePairing_transition.{u} ℓ _ _
    (mul_pow_succ_eq ℓ n) fX
    (LAdicSheaf.etaleLevel B X ℓ F n) (LAdicSheaf.etaleLevel B X ℓ F (n + 1))
    (LAdicSheaf.etaleTransition B X ℓ F n) W _ _).symm

/-- The pairing with `eₙ` on the stalk of `𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` at `t`. -/
def LAdicSheaf.twistPairingGen (n : ℕ)
    (b : ToType ((Scheme.pointSmallEtale t.hom).presheafFiber.obj
      (LAdicSheaf.twistNegOneLevel F n).obj)) :
    ToType ((Scheme.pointSmallEtale t.hom).presheafFiber.obj
      (LAdicSheaf.etaleLevel B X ℓ F n).obj) :=
  Stacks.Kummer.fiberPairing (Scheme.pointSmallEtale t.hom)
    (fun U α s => Stacks.Kummer.twistNegOneModulePairing.{u, 0} X.1 (ℓ ^ (n + 1))
      (LAdicSheaf.etaleLevel B X ℓ F n) U α s) b (LAdicSheaf.twistGen ℓ fX t n)

/-- **The comparison of the level-`n` stalks of `F(-1)` and `F` at `t`**: through the stalks on
Mathlib's site, pairing with the generator `eₙ` of the stalk of `μ_{ℓⁿ⁺¹}`. -/
def LAdicSheaf.twistStalkMap (n : ℕ)
    (a : finiteLevelStalk B X ℓ (LAdicSheaf.twistNegOne fX hF) t n) :
    finiteLevelStalk B X ℓ F t n :=
  ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).hom.app (F.level n))
    (LAdicSheaf.twistPairingGen fX t n ((LAdicSheaf.twistNegOneStalkIso fX hF t n).hom a))

/-- The germ formula for `Stacks.EtaleCohomology.LAdicSheaf.twistStalkMap`: on the germ of a
section `σ` it is the stalk comparison applied to the pairing with `eₙ` of the germ of `σ` on
Mathlib's site. -/
theorem LAdicSheaf.twistStalkMap_germ (n : ℕ) (U : SmallEtale B X.1 X.property)
    (x : (geometricPointFiber B X.1 X.property t).obj U)
    (σ : ToType ((LAdicSheaf.twistNegOneLevel F n).obj.obj
      (op ((SmallEtale.toEtaleSite B X.1 X.property).obj U)))) :
    LAdicSheaf.twistStalkMap fX hF t n
        ((geometricSitePoint B X t).toPresheafFiber U x
          ((LAdicSheaf.twistNegOne fX hF).level n).obj σ) =
      ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).hom.app (F.level n))
        (LAdicSheaf.twistPairingGen fX t n ((Scheme.pointSmallEtale t.hom).toPresheafFiber
          ((SmallEtale.toEtaleSite B X.1 X.property).obj U)
          ((toEtaleSiteFiberIso B X.1 X.property t).inv.app U x)
          (LAdicSheaf.twistNegOneLevel F n).obj σ)) :=
  congrArg (fun b => ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).hom.app
    (F.level n)) (LAdicSheaf.twistPairingGen fX t n b))
    (LAdicSheaf.twistNegOneStalkIso_hom_germ fX hF t n U x σ)

/-- The section of `F(-1)` over a neighbourhood of the bounded site, as a section of
`𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` on Mathlib's site. -/
def LAdicSheaf.twistSectionCast (n : ℕ) (U : SmallEtale B X.1 X.property)
    (σ : ToType (((LAdicSheaf.twistNegOne fX hF).level n).obj.obj (op U))) :
    ToType ((LAdicSheaf.twistNegOneLevel F n).obj.obj
      (op ((SmallEtale.toEtaleSite B X.1 X.property).obj U))) := σ

/-- The comparison commutes with the transitions, on germs. -/
theorem LAdicSheaf.stalkTransition_twistStalkMap_germ (n : ℕ) (U : SmallEtale B X.1 X.property)
    (x : (geometricPointFiber B X.1 X.property t).obj U)
    (σ : ToType (((LAdicSheaf.twistNegOne fX hF).level (n + 1)).obj.obj (op U))) :
    LAdicSheaf.stalkTransition B X ℓ F t n (LAdicSheaf.twistStalkMap fX hF t (n + 1)
        (LAdicSheaf.levelGerm t (LAdicSheaf.twistNegOne fX hF) (n + 1) U x σ)) =
      LAdicSheaf.twistStalkMap fX hF t n
        (LAdicSheaf.stalkTransition B X ℓ (LAdicSheaf.twistNegOne fX hF) t n
          (LAdicSheaf.levelGerm t (LAdicSheaf.twistNegOne fX hF) (n + 1) U x σ)) := by
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u, u}
    (ZMod (ℓ ^ (n + 1 + 1)))
  let Φ := Scheme.pointSmallEtale t.hom
  let Ut := (SmallEtale.toEtaleSite B X.1 X.property).obj U
  let xt := (toEtaleSiteFiberIso B X.1 X.property t).inv.app U x
  let c :=
    (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).hom.app (F.level n)
  let σc := LAdicSheaf.twistSectionCast fX hF (n + 1) U σ
  let ts := (LAdicSheaf.twistNegOneTransition fX F n).hom.app (op Ut) σc
  refine (congrArg (LAdicSheaf.stalkTransition B X ℓ F t n)
    (LAdicSheaf.twistStalkMap_germ fX hF t (n + 1) U x σc)).trans ?_
  refine (LAdicSheaf.stalkTransition_sheafEquivCompSheafFiberIso t F n _).trans ?_
  refine (congrArg c (LAdicSheaf.fiberTransition_twistPairing fX F t n _
    (LAdicSheaf.twistGenV ℓ fX t (n + 1)) _)).trans ?_
  refine (congrArg₂ (fun b m => c (Stacks.Kummer.fiberPairing Φ
    (fun U α s => Stacks.Kummer.twistNegOneModulePairing.{u, 0} X.1 (ℓ ^ (n + 1))
      (LAdicSheaf.etaleLevel B X ℓ F n) U α s) b m))
    (fiberTransition_germ _ _ (LAdicSheaf.twistTransitionFun_naturality fX F n) _ _)
    (LAdicSheaf.twistGen_compat ℓ fX t n)).trans ?_
  refine (LAdicSheaf.twistStalkMap_germ fX hF t n U x ts).symm.trans ?_
  exact congrArg (LAdicSheaf.twistStalkMap fX hF t n)
    ((congrArg _ (LAdicSheaf.twistNegOne_transition_app fX hF n U σ)).symm.trans
      (LAdicSheaf.stalkTransition_germ t (LAdicSheaf.twistNegOne fX hF) n U x σ).symm)

/-- **The comparison commutes with the transitions.** -/
theorem LAdicSheaf.stalkTransition_twistStalkMap (n : ℕ)
    (a : finiteLevelStalk B X ℓ (LAdicSheaf.twistNegOne fX hF) t (n + 1)) :
    LAdicSheaf.stalkTransition B X ℓ F t n (LAdicSheaf.twistStalkMap fX hF t (n + 1) a) =
      LAdicSheaf.twistStalkMap fX hF t n
        (LAdicSheaf.stalkTransition B X ℓ (LAdicSheaf.twistNegOne fX hF) t n a) := by
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u, u}
    (ZMod (ℓ ^ (n + 1 + 1)))
  obtain ⟨U, x, σ, rfl⟩ := (geometricSitePoint B X t).toPresheafFiber_jointly_surjective
    (P := ((LAdicSheaf.twistNegOne fX hF).level (n + 1)).obj) a
  exact LAdicSheaf.stalkTransition_twistStalkMap_germ fX hF t n U x σ

/-- **The comparison of the level stalks is bijective.** -/
theorem LAdicSheaf.bijective_twistStalkMap (n : ℕ) :
    Function.Bijective (LAdicSheaf.twistStalkMap fX hF t n) := by
  have h1 := ConcreteCategory.bijective_of_isIso (LAdicSheaf.twistNegOneStalkIso fX hF t n).hom
  have h2 := ConcreteCategory.bijective_of_isIso
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).hom.app (F.level n))
  have h3 := Stacks.Kummer.bijective_twistNegOneFiberPairing_root.{u, u}
    (Scheme.pointSmallEtale t.hom) (ℓ ^ (n + 1)) (LAdicSheaf.etaleLevel B X ℓ F n)
    (LAdicSheaf.twistGenV ℓ fX t n)
    (Stacks.Kummer.cyclotomicBaseChangeStructMap fX (ℓ ^ (n + 1)) (Scheme.Etale.mk (𝟙 X.1)))
    (LAdicSheaf.twistGen_isPrimitiveRoot ℓ fX t n)
  exact h2.comp (h3.comp h1)

/-- **The comparison of the level stalks is additive.** -/
theorem LAdicSheaf.twistStalkMap_add (n : ℕ)
    (a a' : finiteLevelStalk B X ℓ (LAdicSheaf.twistNegOne fX hF) t n) :
    LAdicSheaf.twistStalkMap fX hF t n (a + a') =
      LAdicSheaf.twistStalkMap fX hF t n a + LAdicSheaf.twistStalkMap fX hF t n a' := by
  unfold LAdicSheaf.twistStalkMap LAdicSheaf.twistPairingGen
  rw [map_add, Stacks.Kummer.fiberPairing_add_left.{u, u} _ _
    (Stacks.Kummer.twistNegOneModulePairing_naturality.{u, 0} _ _ _)
    (fun U z z' s => (Stacks.Kummer.twistNegOneModulePairing.{u, 0} X.1 _ _ U).map_add₂ z z' s)]
  exact map_add ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).hom.app
    (F.level n)).hom _ _

/-- The comparison of the level stalks is `ℤ_ℓ`-linear, being additive between `ℤ/ℓⁿ⁺¹`-modules. -/
theorem LAdicSheaf.twistStalkMap_smul (n : ℕ) (c : ℤ_[ℓ])
    (a : finiteLevelStalk B X ℓ (LAdicSheaf.twistNegOne fX hF) t n) :
    LAdicSheaf.twistStalkMap fX hF t n (c • a) = c • LAdicSheaf.twistStalkMap fX hF t n a := by
  let f :
      finiteLevelStalk B X ℓ (LAdicSheaf.twistNegOne fX hF) t n →+ finiteLevelStalk B X ℓ F t n :=
    AddMonoidHom.mk' (LAdicSheaf.twistStalkMap fX hF t n) (LAdicSheaf.twistStalkMap_add fX hF t n)
  change f ((PadicInt.toZModPow (n + 1) c) • a) = (PadicInt.toZModPow (n + 1) c) • f a
  rw [zmod_smul_eq_val_nsmul, zmod_smul_eq_val_nsmul, map_nsmul]

/-- **The ℓ-adic stalks of `F(-1)` and `F` at `t` are isomorphic**, level by level by the
comparison of the level stalks. -/
def LAdicSheaf.twistStalkEquiv :
    LAdicSheaf.stalk B X ℓ (LAdicSheaf.twistNegOne fX hF) t ≃ₗ[ℤ_[ℓ]] LAdicSheaf.stalk B X ℓ F t :=
  LinearEquiv.ofBijective
    { toFun := fun v => ⟨fun n => LAdicSheaf.twistStalkMap fX hF t n (v.1 n), fun n => by
        rw [LAdicSheaf.stalkTransition_twistStalkMap, v.2 n]⟩
      map_add' := fun v w =>
        Subtype.ext (funext fun n => LAdicSheaf.twistStalkMap_add fX hF t n _ _)
      map_smul' := fun c v =>
        Subtype.ext (funext fun n => LAdicSheaf.twistStalkMap_smul fX hF t n c _) }
    (by
      have hb := LAdicSheaf.bijective_twistStalkMap fX hF t
      refine ⟨fun v w hvw => Subtype.ext (funext fun n => (hb n).1 ?_), fun w => ?_⟩
      · exact congrArg (fun z : LAdicSheaf.stalk B X ℓ F t => z.1 n) hvw
      · choose v hv using fun n => (hb n).2 (w.1 n)
        refine ⟨⟨v, fun n => (hb n).1 ?_⟩, Subtype.ext (funext fun n => hv n)⟩
        rw [← LAdicSheaf.stalkTransition_twistStalkMap, hv, hv]
        exact w.2 n)

section Frobenius

variable (x : X.1) [Finite (X.1.residueField x)]

/-- **The geometric Frobenius on the level stalks of `F(-1)` is `#κ(x)` times that of `F`**, under
the comparison of the level stalks. -/
theorem LAdicSheaf.twistStalkMap_finiteLevelStalkEnd (n : ℕ)
    (y : finiteLevelStalk B X ℓ (LAdicSheaf.twistNegOne fX hF) (geometricPointAt X.1 x) n) :
    LAdicSheaf.twistStalkMap fX hF (geometricPointAt X.1 x) n
        ((finiteLevelStalkEnd B X ℓ (LAdicSheaf.twistNegOne fX hF) (frobeniusPointHom X.1 x) n).hom
          y) =
      Nat.card (X.1.residueField x) • (finiteLevelStalkEnd B X ℓ F (frobeniusPointHom X.1 x) n).hom
        (LAdicSheaf.twistStalkMap fX hF (geometricPointAt X.1 x) n y) := by
  let t := geometricPointAt X.1 x
  let π := frobeniusPointHom X.1 x
  let φ := (residueGeometricFrobenius X.1 x).toAlgHom.toRingHom
  have hf : ∀ (U : X.1.Etale) (u : (Scheme.pointSmallEtale t.hom).fiber.obj U),
      Stacks.Kummer.fiberLift t.hom ((smallEtalePointHom X.1 π).hom.app U u) =
        Spec.map (CommRingCat.ofHom φ) ≫ Stacks.Kummer.fiberLift t.hom u := fun _ _ => rfl
  have hq : ∀ z, φ z ^ Nat.card (X.1.residueField x) = z := fun z => by
    rw [← residueGeometricFrobenius_symm_apply]
    exact (residueGeometricFrobenius X.1 x).symm_apply_apply z
  have hκ : (LAdicSheaf.twistNegOneStalkIso fX hF t n).hom
      ((finiteLevelStalkEnd B X ℓ (LAdicSheaf.twistNegOne fX hF) π n).hom y) =
        (Point.Hom.presheafFiber (smallEtalePointHom X.1 π)).app
          (LAdicSheaf.twistNegOneLevel F n).obj
          ((LAdicSheaf.twistNegOneStalkIso fX hF t n).hom y) :=
    stalkComparison_stalkEnd t (ZMod (ℓ ^ (n + 1))) π ((LAdicSheaf.twistNegOne fX hF).level n)
      (LAdicSheaf.twistNegOneLevel F n) (LAdicSheaf.strictTowerLevelTwistIso fX F n).hom y
  have hΦ := Stacks.Kummer.twistNegOneFiberPairing_presheafFiber_hom t.hom (ℓ ^ (n + 1))
    (LAdicSheaf.etaleLevel B X ℓ F n) (smallEtalePointHom X.1 π) φ hf _ hq
    (LAdicSheaf.twistGenV ℓ fX t n)
    (Stacks.Kummer.cyclotomicBaseChangeStructMap fX (ℓ ^ (n + 1)) (Scheme.Etale.mk (𝟙 X.1)))
    (LAdicSheaf.twistGen_isPrimitiveRoot ℓ fX t n)
    ((LAdicSheaf.twistNegOneStalkIso fX hF t n).hom y)
  have hc := sheafEquivCompSheafFiberIso_hom_presheafFiber_hom t (ZMod (ℓ ^ (n + 1))) π (F.level n)
    (LAdicSheaf.twistPairingGen fX t n ((LAdicSheaf.twistNegOneStalkIso fX hF t n).hom y))
  change
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).hom.app (F.level n))
      (LAdicSheaf.twistPairingGen fX t n ((LAdicSheaf.twistNegOneStalkIso fX hF t n).hom
        ((finiteLevelStalkEnd B X ℓ (LAdicSheaf.twistNegOne fX hF) π n).hom y))) = _
  rw [hκ]
  exact ((congrArg ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) t).hom.app
    (F.level n)) hΦ).trans (map_nsmul ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X
      (ZMod (ℓ ^ (n + 1))) t).hom.app (F.level n)).hom _ _)).trans
    (congrArg (Nat.card (X.1.residueField x) • ·) hc)

/-- **The ℓ-adic stalk isomorphism carries the geometric Frobenius of `F(-1)` to `#κ(x)` times that
of `F`.** -/
theorem LAdicSheaf.twistStalkEquiv_stalkEnd
    (v : LAdicSheaf.stalk B X ℓ (LAdicSheaf.twistNegOne fX hF) (geometricPointAt X.1 x)) :
    LAdicSheaf.twistStalkEquiv fX hF (geometricPointAt X.1 x)
        (LAdicSheaf.stalkEnd B X ℓ (LAdicSheaf.twistNegOne fX hF) (frobeniusPointHom X.1 x) v) =
      (Nat.card (X.1.residueField x) : ℤ_[ℓ]) •
        LAdicSheaf.stalkEnd B X ℓ F (frobeniusPointHom X.1 x)
          (LAdicSheaf.twistStalkEquiv fX hF (geometricPointAt X.1 x) v) := by
  refine Subtype.ext (funext fun n => ?_)
  change LAdicSheaf.twistStalkMap fX hF (geometricPointAt X.1 x) n
      ((finiteLevelStalkEnd B X ℓ (LAdicSheaf.twistNegOne fX hF) (frobeniusPointHom X.1 x) n).hom
        (v.1 n)) = (Nat.card (X.1.residueField x) : ℤ_[ℓ]) •
      (finiteLevelStalkEnd B X ℓ F (frobeniusPointHom X.1 x) n).hom
        (LAdicSheaf.twistStalkMap fX hF (geometricPointAt X.1 x) n (v.1 n))
  rw [LAdicSheaf.twistStalkMap_finiteLevelStalkEnd, Nat.cast_smul_eq_nsmul]

/-- Conjugation by a linear equivalence commutes with powers. -/
theorem LinearEquiv.conj_pow' {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) (g : Module.End R M) (m : ℕ) :
    e.conj g ^ m = e.conj (g ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (LinearEquiv.conj_id e).symm
  | succ m ih => rw [pow_succ, pow_succ, ih, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearEquiv.conj_comp]

omit [Finite (X.1.residueField x)] in
/-- **The trace formula for the Tate twist**: `Tr(π_x^m | F(-1)) = #κ(x)^m Tr(π_x^m | F)` on the
rational stalks at a point with finite residue field. -/
theorem LAdicSheaf.trace_rationalStalkFrobenius_twistNegOne_pow (hx : Finite (X.1.residueField x))
    (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.twistNegOne fX hF)
        x hx ^ m) =
      (Nat.card (X.1.residueField x) : ℚ_[ℓ]) ^ m *
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ F x hx ^ m) := by
  let t := geometricPointAt X.1 x
  let q := Nat.card (X.1.residueField x)
  let e := (LAdicSheaf.twistStalkEquiv fX hF t).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _
  let rT := LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.twistNegOne fX hF) x hx
  let rF := LAdicSheaf.rationalStalkFrobenius B X ℓ F x hx
  have key : ∀ z, e (rT z) = (q : ℚ_[ℓ]) • rF (e z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a w =>
      change e (LAdicSheaf.rationalStalkEnd B X ℓ (LAdicSheaf.twistNegOne fX hF)
        (frobeniusPointHom X.1 x) (a ⊗ₜ w)) =
          (q : ℚ_[ℓ]) • LAdicSheaf.rationalStalkEnd B X ℓ F (frobeniusPointHom X.1 x) (e (a ⊗ₜ w))
      rw [LAdicSheaf.rationalStalkEnd_tmul, LinearEquiv.baseChange_tmul,
        LinearEquiv.baseChange_tmul, LAdicSheaf.rationalStalkEnd_tmul,
        LAdicSheaf.twistStalkEquiv_stalkEnd, TensorProduct.tmul_smul, Nat.cast_smul_eq_nsmul,
        Nat.cast_smul_eq_nsmul]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add, smul_add]
  have hconj : rT = e.symm.conj ((q : ℚ_[ℓ]) • rF) := by
    refine LinearMap.ext fun z => ?_
    change rT z = e.symm (((q : ℚ_[ℓ]) • rF) (e.symm.symm z))
    rw [LinearEquiv.symm_symm, LinearMap.smul_apply, ← key, LinearEquiv.symm_apply_apply]
  change LinearMap.trace ℚ_[ℓ] _ (rT ^ m) = (q : ℚ_[ℓ]) ^ m * LinearMap.trace ℚ_[ℓ] _ (rF ^ m)
  rw [hconj, LinearEquiv.conj_pow', LinearMap.trace_conj', smul_pow, map_smul, smul_eq_mul]

end Frobenius

end Twist

end Levels

end Stacks.EtaleCohomology

end
