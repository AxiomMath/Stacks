module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteEtaleSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusStalk
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FrobeniusRestrictionCoherence
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical Frobenius twist at a rational point

Let `k` be a finite field, `Y` a scheme over `k`, `k̄` an algebraically closed extension of `k`,
and `x` a rational point of `Y`.  The geometric point `ȳ = (x̄, id)` of `Y_k̄` over `x` is fixed by
`π̄ = π_Y × id`.  This file compares the canonical Frobenius twist `C|_{Y_k̄} ⟶ π̄_*(C|_{Y_k̄})` at
`ȳ` with the geometric Frobenius `π_x` acting on the stalk `C_x̄`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleStalkPullbackIso` — the stalk at `s` of the inverse image
  `g⁻¹ F` of a sheaf of modules is the stalk of `F` at `s ≫ g`.

## Main results

* `Stacks.EtaleCohomology.toPresheafFiber_comp_etaleModuleStalkPullbackIso_inv` — the germ
  formula for that identification: on the germ at `s ≫ g` of a section over `W` it is the unit of
  `g⁻¹ ⊣ g_*` followed by the germ at the corresponding lift of `s` to `W ×_X X'`.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-! ### Stalks of an inverse image of sheaves of modules -/

section StalkPullback

variable (Λ : Type r) [Ring Λ] {X X' : Scheme.{u}} (g : X' ⟶ X) {Ω : Type u} [Field Ω]
  [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X')

/-- **Stalks of an inverse image of sheaves of modules.**  For `g : X' ⟶ X` and a geometric point
`s : Spec Ω ⟶ X'`, the stalk at `s` of `g⁻¹ F` is the stalk of `F` at `s ≫ g`, naturally in the
sheaf of `Λ`-modules `F`. -/
def etaleModuleStalkPullbackIso :
    etaleModuleInverseImage.{u, r} Λ g ⋙
        (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ) ≅
      (Scheme.pointSmallEtale (s ≫ g)).sheafFiber :=
  ((Scheme.pointSmallEtale s).sheafFiberComapIso (smallEtaleBaseChange g)
      (coverPreserving_smallEtaleBaseChange g) (ModuleCat.{max (u + 1) r} Λ)).symm ≪≫
    (Point.sheafFiberIsoOfFiberIso (A := ModuleCat.{max (u + 1) r} Λ)
      (Scheme.pointSmallEtale (s ≫ g))
      ((Scheme.pointSmallEtale s).comap (smallEtaleBaseChange g)
        (coverPreserving_smallEtaleBaseChange g)) (pointSmallEtaleComapFiberIso g s)).symm

/-- **The germ formula for the stalk of an inverse image.**  On the germ at `s ≫ g` of a section
of `F` over an étale neighbourhood `W`, the inverse of the comparison is the unit of
`g⁻¹ ⊣ g_*` followed by the germ at the corresponding lift of `s` to `W ×_X X'`. -/
theorem toPresheafFiber_comp_etaleModuleStalkPullbackIso_inv (F : EtaleModules.{u, r} Λ X)
    (W : X.Etale) (v : (Scheme.pointSmallEtale (s ≫ g)).fiber.obj W) :
    (Scheme.pointSmallEtale (s ≫ g)).toPresheafFiber W v F.obj ≫
        (etaleModuleStalkPullbackIso Λ g s).inv.app F =
      ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app F).hom.app (op W) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber ((smallEtaleBaseChange g).obj W)
          ((pointSmallEtaleComapFiberIso g s).hom.app W v)
          ((etaleModuleInverseImage.{u, r} Λ g).obj F).obj := by
  have h1 := Point.toPresheafFiber_presheafFiberIsoOfFiberIso (A := ModuleCat.{max (u + 1) r} Λ)
    (Scheme.pointSmallEtale (s ≫ g))
    ((Scheme.pointSmallEtale s).comap (smallEtaleBaseChange g)
      (coverPreserving_smallEtaleBaseChange g)) (pointSmallEtaleComapFiberIso g s) F.obj W v
  have h2 := Point.toSheafFiber_sheafFiberComapIso_hom (Scheme.pointSmallEtale s)
    (smallEtaleBaseChange g) (coverPreserving_smallEtaleBaseChange g) F W
    ((pointSmallEtaleComapFiberIso g s).hom.app W v)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ((Scheme.pointSmallEtale s).sheafFiberComapIso (smallEtaleBaseChange g)
      (coverPreserving_smallEtaleBaseChange g) (ModuleCat.{max (u + 1) r} Λ)).hom.app F) h1).trans
      h2)

end StalkPullback

/-! ### Equal geometric points -/

section EqPoint

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Two equal geometric points have the same lifts, by the identity on the underlying
morphisms. -/
def pointSmallEtaleFiberIsoOfEq {s s' : Spec (.of Ω) ⟶ S} (h : s = s') :
    (Scheme.pointSmallEtale s).fiber ≅ (Scheme.pointSmallEtale s').fiber :=
  NatIso.ofComponents (fun U => Equiv.toIso
    { toFun := fun w => CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk s')
        (V := (Scheme.Etale.forget S).obj U) w.left (by
          rw [← h]; exact CategoryTheory.Over.w w)
      invFun := fun w => CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk s)
        (V := (Scheme.Etale.forget S).obj U) w.left (by
          rw [h]; exact CategoryTheory.Over.w w)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by
    intro U V g
    rfl)

/-- The forward map of `pointSmallEtaleFiberIsoOfEq` is the identity on underlying morphisms. -/
@[simp]
lemma pointSmallEtaleFiberIsoOfEq_hom_app_left {s s' : Spec (.of Ω) ⟶ S} (h : s = s')
    (U : S.Etale) (w : (Scheme.pointSmallEtale s).fiber.obj U) :
    ((pointSmallEtaleFiberIsoOfEq h).hom.app U w).left = w.left :=
  rfl

/-- The inverse map of `pointSmallEtaleFiberIsoOfEq` is the identity on underlying morphisms. -/
@[simp]
lemma pointSmallEtaleFiberIsoOfEq_inv_app_left {s s' : Spec (.of Ω) ⟶ S} (h : s = s')
    (U : S.Etale) (w : (Scheme.pointSmallEtale s').fiber.obj U) :
    ((pointSmallEtaleFiberIsoOfEq h).inv.app U w).left = w.left :=
  rfl

end EqPoint

/-! ### The rational point of the base change over a rational point -/

section RationalPoint

open Stacks.Frobenius

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (x : Spec (.of k) ⟶ Y.left) (hx : x ≫ Y.hom = 𝟙 _)

/-- **The `k̄`-point `ȳ = (x̄, id)` of `Y_k̄` over a rational point `x` of `Y`.** -/
def rationalPointBaseChangeLift : Spec (.of kbar) ⟶ fieldBaseChange Y kbar :=
  pullback.lift (specAlgebraMap k kbar ≫ x) (𝟙 _)
    (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])

omit [Fintype k] in
/-- The first projection of `rationalPointBaseChangeLift` is `x̄ = Spec k̄ ⟶ Spec k ⟶ Y`. -/
@[reassoc (attr := simp)]
lemma rationalPointBaseChangeLift_fst :
    rationalPointBaseChangeLift Y kbar x hx ≫ pullback.fst Y.hom (specAlgebraMap k kbar) =
      specAlgebraMap k kbar ≫ x :=
  pullback.lift_fst _ _ _

omit [Fintype k] in
/-- The second projection of `rationalPointBaseChangeLift` is the identity of `Spec k̄`. -/
@[reassoc (attr := simp)]
lemma rationalPointBaseChangeLift_snd :
    rationalPointBaseChangeLift Y kbar x hx ≫ pullback.snd Y.hom (specAlgebraMap k kbar) = 𝟙 _ :=
  pullback.lift_snd _ _ _

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The geometric Frobenius fixes the rational points.**  A rational point `x` of `Y` satisfies
`x ≫ π_Y = x`. -/
lemma rationalPoint_comp_geometricFrobenius :
    x ≫ (geometricFrobenius Y p q hcard).left = x := by
  have hk : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_of_over (CategoryTheory.Over.mk (𝟙 (Spec (.of k))))
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id k)) =
      absoluteFrobeniusPow (Spec (.of k)) p hk q :=
    specMap_eq_absoluteFrobeniusPow (RingHom.id k) p q hk (fun a => by
      rw [RingHom.id_apply, ← hcard, FiniteField.pow_card])
  have hnat := absoluteFrobeniusPow_naturality x p hk (isInCharacteristic_of_over Y) q
  rw [geometricFrobenius_left_eq_absoluteFrobeniusPow, ← hnat, ← hid]
  exact (congrArg (· ≫ x) (Spec.map_id (CommRingCat.of k))).trans (Category.id_comp x)

/-- **The `k̄`-point over a rational point is fixed by `π̄ = π_Y × id`.** -/
@[reassoc (attr := simp), sga "5 III 6.13" "Inclusion X0(F_q) ⊆ X^F"]
lemma rationalPointBaseChangeLift_comp_geometricFrobeniusBaseChange :
    rationalPointBaseChangeLift Y kbar x hx ≫ geometricFrobeniusBaseChange Y kbar p q hcard =
      rationalPointBaseChangeLift Y kbar x hx := by
  apply pullback.hom_ext
  · rw [Category.assoc, geometricFrobeniusBaseChange_comp_fst,
      rationalPointBaseChangeLift_fst_assoc, rationalPoint_comp_geometricFrobenius,
      rationalPointBaseChangeLift_fst]
  · rw [Category.assoc, geometricFrobeniusBaseChange_comp_snd]

end RationalPoint


/-! ### Auxiliary identities -/

section Aux

variable (Λ : Type r) [Ring Λ]

/-- The inverse of the composition isomorphism for direct images of sheaves of modules is
restriction of sections along the inverse of the base change comparison. -/
lemma etaleModuleDirectImageComp_inv_app_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (F : EtaleModules.{u, r} Λ X) (U : (Z.Etale)ᵒᵖ) :
    ((etaleModuleDirectImageComp.{u, r} Λ f g fg hfg).inv.app F).hom.app U =
      F.obj.map (op ((smallEtaleBaseChangeComp' f g fg hfg).inv.app U.unop)) := by
  have h₁ : ((etaleModuleDirectImageComp.{u, r} Λ f g fg hfg).inv.app F).hom.app U ≫
      ((etaleModuleDirectImageComp.{u, r} Λ f g fg hfg).hom.app F).hom.app U = 𝟙 _ := by
    have := congrArg (fun φ => φ.hom.app U)
      ((etaleModuleDirectImageComp.{u, r} Λ f g fg hfg).inv_hom_id_app F)
    exact this
  have h₂ : F.obj.map ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U.unop).op ≫
      F.obj.map ((smallEtaleBaseChangeComp' f g fg hfg).inv.app U.unop).op = 𝟙 _ := by
    rw [← F.obj.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id, F.obj.map_id]
  rw [etaleModuleDirectImageComp_hom_app_hom_app] at h₁
  exact (Category.comp_id _).symm.trans ((congrArg (fun φ => _ ≫ φ) h₂.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans (Category.id_comp _))))

/-- **Sections of the adjoint of the base change twist.**  Over an étale `Y`-scheme `W`, the
adjoint `L ⟶ g_* a_* g^{-1} L` of the base change twist is `ψ` at `W`, then the unit of
`g^{-1} ⊣ g_*` at `b^* W`, then restriction along the two base-change comparisons
`a^* g^* W ⟶ (a ≫ g)^* W ⟶ g^* b^* W`. -/
lemma etaleModuleBaseChangeTwistAdj_app_hom_app {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y' ⟶ Y')
    (b : Y ⟶ Y) (w : a ≫ g = g ≫ b)
    (ψ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b)
    (L : EtaleModules.{u, r} Λ Y) (W : Y.Etale) :
    ((etaleModuleBaseChangeTwistAdj.{u, r} Λ g a b w ψ).app L).hom.app (op W) =
      (ψ.app L).hom.app (op W) ≫
        ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app L).hom.app
          (op ((smallEtaleBaseChange b).obj W)) ≫
        ((etaleModuleInverseImage.{u, r} Λ g).obj L).obj.map
          ((smallEtaleBaseChangeComp' g b (a ≫ g) w).hom.app W).op ≫
        ((etaleModuleInverseImage.{u, r} Λ g).obj L).obj.map
          ((smallEtaleBaseChangeComp' a g (a ≫ g) rfl).inv.app W).op := by
  simp only [etaleModuleBaseChangeTwistAdj, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    etaleModuleDirectImageComp_hom_app_hom_app, etaleModuleDirectImageComp_inv_app_hom_app]
  rfl

end Aux

/-! ### The canonical twist at a rational point -/

section Diagonal

open Stacks.Frobenius

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  [Etale Y.hom] (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
  (x : Spec (.of k) ⟶ Y.left) (hx : x ≫ Y.hom = 𝟙 _)

/-- The `k̄`-point over a rational point is étale over `Y_k̄`. -/
instance etale_rationalPointBaseChangeLift : Etale (rationalPointBaseChangeLift Y kbar x hx) :=
  etale_of_section (pullback.snd Y.hom (specAlgebraMap k kbar)) _
    (rationalPointBaseChangeLift_snd Y kbar x hx)

/-- The `k̄`-point over a rational point, as an object of the small étale site of `Y_k̄`. -/
abbrev rationalPointBaseChangeObj : (fieldBaseChange Y kbar).Etale :=
  Scheme.Etale.mk (rationalPointBaseChangeLift Y kbar x hx)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The morphism `ȳ ⟶ π̄^*(ȳ)` of étale `Y_k̄`-schemes given by the fixedness `ȳ ≫ π̄ = ȳ`. -/
def rationalPointFrobeniusLift :
    rationalPointBaseChangeObj Y kbar x hx ⟶
      (smallEtaleBaseChange (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
        (rationalPointBaseChangeObj Y kbar x hx) :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 _) (rationalPointBaseChangeLift Y kbar x hx) (by
      rw [Category.id_comp]
      exact (rationalPointBaseChangeLift_comp_geometricFrobeniusBaseChange Y kbar x hx p q
        hcard).symm))
    (pullback.lift_snd _ _ _)

omit [IsAlgClosed kbar] in
/-- The first projection of the underlying morphism of `rationalPointFrobeniusLift` is the
identity. -/
@[reassoc (attr := simp)]
lemma rationalPointFrobeniusLift_left_fst :
    (rationalPointFrobeniusLift Y kbar x hx p q hcard).left ≫
        pullback.fst (rationalPointBaseChangeLift Y kbar x hx)
          (geometricFrobeniusBaseChange Y kbar p q hcard) = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- **The canonical Frobenius twist at the `k̄`-point over a rational point**: the endomorphism of
the sections of `C|_{Y_k̄}` over `ȳ` given by the twist `C|_{Y_k̄} ⟶ π̄_*(C|_{Y_k̄})` followed by
restriction along `ȳ ⟶ π̄^*(ȳ)`, natural in `C`. -/
def rationalPointFrobeniusEndo :
    etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⋙
        sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
        (CategoryTheory.evaluation (fieldBaseChange Y kbar).Etaleᵒᵖ
          (ModuleCat.{max (u + 1) r} Λ)).obj (op (rationalPointBaseChangeObj Y kbar x hx)) ⟶
      etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⋙
        sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
        (CategoryTheory.evaluation (fieldBaseChange Y kbar).Etaleᵒᵖ
          (ModuleCat.{max (u + 1) r} Λ)).obj (op (rationalPointBaseChangeObj Y kbar x hx)) where
  app L := ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app L).hom.app
      (op (rationalPointBaseChangeObj Y kbar x hx)) ≫
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj.map
      (rationalPointFrobeniusLift Y kbar x hx p q hcard).op
  naturality L L' φ := by
    have h₁ := congrArg (fun ψ => ψ.hom.app (op (rationalPointBaseChangeObj Y kbar x hx)))
      ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).naturality φ)
    have h₂ :=
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map φ).hom.naturality
        (rationalPointFrobeniusLift Y kbar x hx p q hcard).op
    simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h₁
    change ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map φ).hom.app _ ≫
        ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app L').hom.app _ ≫ _ =
      (((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app L).hom.app _ ≫ _) ≫
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map φ).hom.app _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂.symm).trans
        (Category.assoc _ _ _).symm)))

/-- **The sections over the `k̄`-point over `x` are the stalk at the geometric point over `x`.** -/
def rationalPointSectionsStalkIso :
    etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⋙
        sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
        (CategoryTheory.evaluation (fieldBaseChange Y kbar).Etaleᵒᵖ
          (ModuleCat.{max (u + 1) r} Λ)).obj (op (rationalPointBaseChangeObj Y kbar x hx)) ≅
      (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ) :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (presheafFiberSelfIso (rationalPointBaseChangeLift Y kbar x hx)
        (ModuleCat.{max (u + 1) r} Λ))) ≪≫
    etaleModuleStalkPullbackIso Λ (fieldBaseChangeProj Y kbar)
      (rationalPointBaseChangeLift Y kbar x hx) ≪≫
    Point.sheafFiberIsoOfFiberIso _ _
      (pointSmallEtaleFiberIsoOfEq (rationalPointBaseChangeLift_fst Y kbar x hx))

/-- The morphism `ȳ ⟶ W ×_Y Y_k̄` of étale `Y_k̄`-schemes attached to a lift `w` of the geometric
point over `x` to an étale `Y`-scheme `W`. -/
abbrev rationalPointRestrictionHom (W : Y.left.Etale)
    (w : (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).fiber.obj W) :
    rationalPointBaseChangeObj Y kbar x hx ⟶
      (smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj W :=
  pointSmallEtaleSelfHom (rationalPointBaseChangeLift Y kbar x hx)
    ((pointSmallEtaleComapFiberIso (fieldBaseChangeProj Y kbar)
      (rationalPointBaseChangeLift Y kbar x hx)).hom.app W
      ((pointSmallEtaleFiberIsoOfEq (rationalPointBaseChangeLift_fst Y kbar x hx)).inv.app W w))

omit [Fintype k] in
/-- The underlying morphism of `rationalPointRestrictionHom` followed by the first projection to
`W` is that of `w`. -/
@[reassoc (attr := simp)]
lemma rationalPointRestrictionHom_left_fst (W : Y.left.Etale)
    (w : (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).fiber.obj W) :
    (rationalPointRestrictionHom Y kbar x hx W w).left ≫
        pullback.fst W.hom (fieldBaseChangeProj Y kbar) = w.left :=
  pointSmallEtaleComapFiberIso_hom_app_left_fst _ _ _ _

omit [Fintype k] in
/-- **The germ formula for the sections-stalk comparison**: on the germ of a section of `C` over
an étale neighbourhood `W` of the geometric point over `x`, the inverse comparison is the unit
of `pr^{-1} ⊣ pr_*` followed by restriction along `ȳ ⟶ W ×_Y Y_k̄`. -/
lemma toPresheafFiber_comp_rationalPointSectionsStalkIso_inv (L : EtaleModules.{u, r} Λ Y.left)
    (W : Y.left.Etale) (w : (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).fiber.obj W) :
    (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).toPresheafFiber W w L.obj ≫
        (rationalPointSectionsStalkIso Λ Y kbar x hx).inv.app L =
      ((etaleModuleInverseImageAdj.{u, r} Λ (fieldBaseChangeProj Y kbar)).unit.app L).hom.app
          (op W) ≫
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj.map
          (rationalPointRestrictionHom Y kbar x hx W w).op := by
  have h₁ := Point.toPresheafFiber_presheafFiberIsoOfFiberIso_inv
    (A := ModuleCat.{max (u + 1) r} Λ)
    (Scheme.pointSmallEtale (rationalPointBaseChangeLift Y kbar x hx ≫ fieldBaseChangeProj Y kbar))
    (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x))
    (pointSmallEtaleFiberIsoOfEq (rationalPointBaseChangeLift_fst Y kbar x hx)) L.obj W w
  have h₂ := toPresheafFiber_comp_etaleModuleStalkPullbackIso_inv Λ (fieldBaseChangeProj Y kbar)
    (rationalPointBaseChangeLift Y kbar x hx) L W
    ((pointSmallEtaleFiberIsoOfEq (rationalPointBaseChangeLift_fst Y kbar x hx)).inv.app W w)
  have h₃ := toPresheafFiber_comp_presheafFiberSelfIso_inv
    (rationalPointBaseChangeLift Y kbar x hx) (ModuleCat.{max (u + 1) r} Λ)
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj
    ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj W)
    ((pointSmallEtaleComapFiberIso (fieldBaseChangeProj Y kbar)
      (rationalPointBaseChangeLift Y kbar x hx)).hom.app W
      ((pointSmallEtaleFiberIsoOfEq (rationalPointBaseChangeLift_fst Y kbar x hx)).inv.app W w))
  show (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).toPresheafFiber W w L.obj ≫
      ((Point.presheafFiberIsoOfFiberIso _ _
        (pointSmallEtaleFiberIsoOfEq (rationalPointBaseChangeLift_fst Y kbar x hx))).inv.app L.obj ≫
      (etaleModuleStalkPullbackIso Λ (fieldBaseChangeProj Y kbar)
        (rationalPointBaseChangeLift Y kbar x hx)).inv.app L ≫
      (presheafFiberSelfIso (rationalPointBaseChangeLift Y kbar x hx)
        (ModuleCat.{max (u + 1) r} Λ)).inv.app
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj) = _
  rw [reassoc_of% h₁]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₃)))

omit [Etale Y.hom] [IsAlgClosed kbar] in
/-- The unit of `pr^{-1} ⊣ pr_*` followed by `pr_*` of the Frobenius twist is the adjoint of the
twist. -/
lemma unit_comp_frobeniusBaseChangeTwist (L : EtaleModules.{u, r} Λ Y.left) :
    (etaleModuleInverseImageAdj.{u, r} Λ (fieldBaseChangeProj Y kbar)).unit.app L ≫
        (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map
          ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app L) =
      (etaleModuleBaseChangeTwistAdj.{u, r} Λ (fieldBaseChangeProj Y kbar)
        (geometricFrobeniusBaseChange Y kbar p q hcard) (geometricFrobenius Y p q hcard).left
        (geometricFrobeniusBaseChange_comp_fst Y kbar p q hcard)
        (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom).app L :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans
    ((congrArg _ (etaleModuleBaseChangeTwist_app.{u, r} Λ (fieldBaseChangeProj Y kbar)
      (geometricFrobeniusBaseChange Y kbar p q hcard) (geometricFrobenius Y p q hcard).left
      (geometricFrobeniusBaseChange_comp_fst Y kbar p q hcard)
      (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom L)).trans
      (Equiv.apply_symm_apply _ _))

variable [CharP kbar p]

/-- The lift of the geometric point over `x` translated by the geometric Frobenius `σ⁻¹` of
`k̄`. -/
abbrev frobeniusTranslatedLift (W : Y.left.Etale)
    (w : (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).fiber.obj W) :
    (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).fiber.obj W :=
  (smallEtalePointHom Y.left
    (galoisPointHom kbar (arithmeticFrobenius k kbar p q hcard).symm x)).hom.app W w

omit [Etale Y.hom] [CharP k p] in
/-- The underlying morphism of `frobeniusTranslatedLift` is `Spec(σ⁻¹)` followed by that of
`w`. -/
lemma frobeniusTranslatedLift_left (W : Y.left.Etale)
    (w : (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).fiber.obj W) :
    (frobeniusTranslatedLift Y kbar x p q hcard W w).left =
      Spec.map (CommRingCat.ofHom (arithmeticFrobenius k kbar p q hcard).symm.toAlgHom.toRingHom) ≫
        w.left :=
  rfl

/-- A diagram chase in an arbitrary category: the composite `ℓ ≫ A ≫ c₂ ≫ c₁ ≫ fst` is a lift `u`
with `u ≫ F = w`, and `S ≫ u = u ≫ F` with `S'` inverse to `S` gives `u = S' ≫ w`. -/
private lemma frobeniusLiftChase {C : Type*} [Category C] {P Q R T Z M N V : C}
    (ℓ : P ⟶ Q) (A : Q ⟶ R) (c₂ : R ⟶ T) (c₁ : T ⟶ Z) (B : Z ⟶ M) (fM : M ⟶ V)
    (fZ : Z ⟶ N) (fN : N ⟶ V) (fT : T ⟶ V) (fR : R ⟶ M) (fQ : Q ⟶ P) (lw : P ⟶ M)
    (w : P ⟶ V) (γi : N ⟶ V) (γh : V ⟶ N) (F : V ⟶ V) (S S' : P ⟶ P)
    (h1 : c₁ ≫ fZ ≫ fN = fT) (h2 : c₂ ≫ fT = fR ≫ fM) (h3 : A ≫ fR = fQ ≫ lw)
    (h4 : ℓ ≫ fQ = 𝟙 P) (h5 : lw ≫ fM = w) (h6 : B ≫ fM = fZ ≫ γi)
    (hγ : γi ≫ γh = 𝟙 N) (hγf : γh ≫ fN = F) (hnat : ∀ g : P ⟶ V, S ≫ g = g ≫ F)
    (hinv : S' ≫ S = 𝟙 P) :
    (ℓ ≫ A ≫ c₂ ≫ c₁ ≫ B) ≫ fM = S' ≫ w := by
  have hu : (ℓ ≫ A ≫ c₂ ≫ c₁ ≫ fZ ≫ γi) ≫ F = w := by
    simp only [Category.assoc, ← hγf, reassoc_of% hγ, h1, h2, reassoc_of% h3,
      reassoc_of% h4, h5]
  rw [← hu, ← hnat, reassoc_of% hinv]
  simp only [Category.assoc, h6]

/-- The fixed point `ȳ ⟶ π̄^*(ȳ)`, followed by the base change along `π̄` of `ȳ ⟶ W ×_Y Y_k̄`, the
identification of the iterated base changes, and the base change along `pr` of `γ_W^{-1}`, is the
morphism `ȳ ⟶ W ×_Y Y_k̄` attached to the lift of the geometric point translated by the geometric
Frobenius of `k̄`. -/
lemma rationalPointFrobeniusLift_comp_restriction (W : Y.left.Etale)
    (w : (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).fiber.obj W) :
    rationalPointFrobeniusLift Y kbar x hx p q hcard ≫
        (smallEtaleBaseChange (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          (rationalPointRestrictionHom Y kbar x hx W w) ≫
        (smallEtaleBaseChangeComp' (geometricFrobeniusBaseChange Y kbar p q hcard)
          (fieldBaseChangeProj Y kbar)
          (geometricFrobeniusBaseChange Y kbar p q hcard ≫ fieldBaseChangeProj Y kbar) rfl).inv.app
            W ≫
        (smallEtaleBaseChangeComp' (fieldBaseChangeProj Y kbar)
          (geometricFrobenius Y p q hcard).left
          (geometricFrobeniusBaseChange Y kbar p q hcard ≫ fieldBaseChangeProj Y kbar)
          (geometricFrobeniusBaseChange_comp_fst Y kbar p q hcard)).hom.app W ≫
        (smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).map
          ((geometricFrobeniusEtaleSiteIso Y p q hcard).inv.app W) =
      rationalPointRestrictionHom Y kbar x hx W
        (frobeniusTranslatedLift Y kbar x p q hcard W w) := by
  refine smallEtaleBaseChange_hom_ext (fieldBaseChangeProj Y kbar) ?_
  refine Eq.trans ?_ ((rationalPointRestrictionHom_left_fst Y kbar x hx W _).trans
    (frobeniusTranslatedLift_left Y kbar x p q hcard W w)).symm
  have h6 := smallEtaleBaseChange_map_left_fst (fieldBaseChangeProj Y kbar)
    ((geometricFrobeniusEtaleSiteIso Y p q hcard).inv.app W)
  have h1 := smallEtaleBaseChangeComp'_fst_fst (fieldBaseChangeProj Y kbar)
    (geometricFrobenius Y p q hcard).left
    (geometricFrobeniusBaseChange Y kbar p q hcard ≫ fieldBaseChangeProj Y kbar)
    (geometricFrobeniusBaseChange_comp_fst Y kbar p q hcard) W
  have h2 := smallEtaleBaseChangeComp'_inv_fst (geometricFrobeniusBaseChange Y kbar p q hcard)
    (fieldBaseChangeProj Y kbar)
    (geometricFrobeniusBaseChange Y kbar p q hcard ≫ fieldBaseChangeProj Y kbar) rfl W
  have h3 := smallEtaleBaseChange_map_left_fst (geometricFrobeniusBaseChange Y kbar p q hcard)
    (rationalPointRestrictionHom Y kbar x hx W w)
  have h4 := rationalPointFrobeniusLift_left_fst Y kbar x hx p q hcard
  have h5 := rationalPointRestrictionHom_left_fst Y kbar x hx W w
  have hγ : ((geometricFrobeniusEtaleSiteIso Y p q hcard).inv.app W).left ≫
      ((geometricFrobeniusEtaleSiteIso Y p q hcard).hom.app W).left = 𝟙 _ :=
    congrArg (fun f => f.left) ((geometricFrobeniusEtaleSiteIso Y p q hcard).inv_hom_id_app W)
  have hγf := geometricFrobeniusEtaleSiteIso_hom_app_left_fst Y p q hcard W
  have hk : IsInCharacteristic (Spec (.of kbar)) p := isInCharacteristic_specAlgebraMap k kbar p
  have hσ : Spec.map (CommRingCat.ofHom (arithmeticFrobenius k kbar p q hcard).toAlgHom.toRingHom) =
      absoluteFrobeniusPow (Spec (.of kbar)) p hk q :=
    specMap_eq_absoluteFrobeniusPow _ p q hk (fun a => by
      simp [arithmeticFrobenius, iterateFrobenius_def])
  have hinv : Spec.map (CommRingCat.ofHom
        (arithmeticFrobenius k kbar p q hcard).symm.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (arithmeticFrobenius k kbar p q hcard).toAlgHom.toRingHom) =
        𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of kbar)
    ext a
    simp [-arithmeticFrobenius_apply]
  exact frobeniusLiftChase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 hγ hγf
    (fun g => hσ ▸ absoluteFrobeniusPow_naturality g p hk _ q) hinv

/-- In an arbitrary category, the relations `hl`, `h1`, `hE`, `h2`, `hτ`, `hadj` and `hη` give
`g ≫ π ≫ e = g ≫ e ≫ t ≫ l`. -/
private lemma twistGermChase {C : Type*} [Category C] {S₀ S₁ F₀ A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (g g' : S₀ ⟶ F₀) (π : F₀ ⟶ F₀) (e : F₀ ⟶ A₀) (t : A₀ ⟶ A₁) (l : A₁ ⟶ A₀)
    (n : S₀ ⟶ B₀) (lw lw' : B₀ ⟶ A₀) (t' : B₀ ⟶ A₂) (Pl : A₂ ⟶ A₁) (m : S₀ ⟶ S₁)
    (n₂ : S₁ ⟶ B₁) (c₁ : B₁ ⟶ B₂) (c₂ : B₂ ⟶ A₂) (Gm : B₀ ⟶ B₁)
    (hl : g ≫ π = g') (h1 : g' ≫ e = n ≫ lw') (hE : (((Gm ≫ c₁) ≫ c₂) ≫ Pl) ≫ l = lw')
    (h2 : g ≫ e = n ≫ lw) (hτ : lw ≫ t = t' ≫ Pl) (hadj : n ≫ t' = m ≫ n₂ ≫ c₁ ≫ c₂)
    (hη : m ≫ n₂ = n ≫ Gm) :
    g ≫ π ≫ e = g ≫ e ≫ t ≫ l := by
  rw [reassoc_of% hl, h1, ← hE, reassoc_of% h2, reassoc_of% hτ, reassoc_of% hadj,
    reassoc_of% hη]
  simp only [Category.assoc]

/-- **The canonical twist at the fixed point is the geometric Frobenius on the stalk**, in the
inverse direction: on the stalk `C_x̄`, the geometric Frobenius `π_x` followed by the comparison
with the sections over `ȳ` is the comparison followed by the twist at `ȳ`. -/
lemma geometricFrobeniusStalkFunctor_comp_rationalPointSectionsStalkIso_inv
    (L : EtaleModules.{u, r} Λ Y.left) :
    (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) kbar p q hcard x).app L ≫
        (rationalPointSectionsStalkIso Λ Y kbar x hx).inv.app L =
      (rationalPointSectionsStalkIso Λ Y kbar x hx).inv.app L ≫
        (rationalPointFrobeniusEndo Λ Y kbar x hx p q hcard).app L := by
  refine Point.presheafFiber_hom_ext _ (fun W w => ?_)
  set G := ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj
  set η := ((etaleModuleInverseImageAdj.{u, r} Λ (fieldBaseChangeProj Y kbar)).unit.app L).hom
  set τ := ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app L).hom
  set γ := geometricFrobeniusEtaleSiteIso Y p q hcard
  have hl : (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).toPresheafFiber W w L.obj ≫
      (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) kbar p q hcard x).app L =
        (Scheme.pointSmallEtale (specAlgebraMap k kbar ≫ x)).toPresheafFiber W
          (frobeniusTranslatedLift Y kbar x p q hcard W w) L.obj := by
    show _ ≫ Point.presheafFiberDesc (A := ModuleCat.{max (u + 1) r} Λ) _ _ _ = _
    exact Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _
  have hτ := τ.naturality (rationalPointRestrictionHom Y kbar x hx W w).op
  have hη := η.naturality ((γ.inv.app W).op)
  have hadj := congrArg (fun φ => φ.hom.app (op W)) (unit_comp_frobeniusBaseChangeTwist Λ Y kbar p q
    hcard L)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hadj
  rw [etaleModuleBaseChangeTwistAdj_app_hom_app, geometricFrobeniusPushforwardIso_hom_app_hom_app]
    at hadj
  have hE := congrArg (fun φ => G.map φ.op)
    (rationalPointFrobeniusLift_comp_restriction Y kbar x hx p q hcard W w)
  simp only [op_comp, Functor.map_comp] at hE
  have h1 := toPresheafFiber_comp_rationalPointSectionsStalkIso_inv Λ Y kbar x hx L W
    (frobeniusTranslatedLift Y kbar x p q hcard W w)
  have h2 := toPresheafFiber_comp_rationalPointSectionsStalkIso_inv Λ Y kbar x hx L W w
  exact twistGermChase (hl := hl) (h1 := h1) (hE := hE) (h2 := h2) (hτ := hτ) (hadj := hadj)
    (hη := hη)

/-- **The canonical Frobenius twist at a fixed point is `π_x`.**  Under the
identification `C|_{Y_k̄}(ȳ) ≅ C_x̄` of the sections over the `k̄`-point `ȳ = (x̄, id)` with the
stalk at the geometric point over the rational point `x`, the canonical Frobenius twist at `ȳ`
is the geometric Frobenius `π_x` of [Stacks, Tag 03SW]. -/
theorem rationalPointFrobeniusEndo_comp_rationalPointSectionsStalkIso_hom
    (L : EtaleModules.{u, r} Λ Y.left) :
    (rationalPointFrobeniusEndo Λ Y kbar x hx p q hcard).app L ≫
        (rationalPointSectionsStalkIso Λ Y kbar x hx).hom.app L =
      (rationalPointSectionsStalkIso Λ Y kbar x hx).hom.app L ≫
        (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) kbar p q hcard x).app L := by
  have h := geometricFrobeniusStalkFunctor_comp_rationalPointSectionsStalkIso_inv Λ Y kbar x hx p
    q hcard L
  calc (rationalPointFrobeniusEndo Λ Y kbar x hx p q hcard).app L ≫
        (rationalPointSectionsStalkIso Λ Y kbar x hx).hom.app L
      = (rationalPointSectionsStalkIso Λ Y kbar x hx).hom.app L ≫
          ((rationalPointSectionsStalkIso Λ Y kbar x hx).inv.app L ≫
            (rationalPointFrobeniusEndo Λ Y kbar x hx p q hcard).app L) ≫
          (rationalPointSectionsStalkIso Λ Y kbar x hx).hom.app L := by
        simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    _ = _ := by
        rw [← h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end Diagonal

end Stacks.EtaleCohomology

end
