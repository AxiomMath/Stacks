module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPullbackSquare
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# `ε^*` commutes with pullback, compatibly with composition

For morphisms `p : X ⟶ Y` and `q : Y ⟶ Z` of the big fppf site over `S`, the square
`AlgebraicGeometry.Space.representedZariskiModulePullbackCompIso` of `ε^*` and the pullbacks along
the represented morphism and along the underlying morphism of schemes (the module form of the
square of Stacks 08GH) is compatible with composition: the square along `p ≫ q` is the pasting of
the squares along `q` and `p`, read through the composition law `modulePullbackCompIso` of
Stacks 03LU on the spaces and `Scheme.Modules.pullbackComp` on the schemes.

The square is pasted from three identifications, each of which composes:
`representedModulePullbackIso`
(`AlgebraicGeometry.Space.representedModulePullbackIso_hom_comp_of_eq`), the associated module
of Stacks 03LC (1) (`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp`), and the
identification of `ε^*` with the associated module, which enters only through its inverse and
cancels.

## Main results

* `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalencePullbackIso_comp`.
* `AlgebraicGeometry.Space.representedZariskiModulePullbackCompIso_comp`.
* `AlgebraicGeometry.Space.representedZariskiModulePullbackCompIso_congr`: transport along an
  equality of morphisms of the site.
* `AlgebraicGeometry.Space.representedZariskiModulePullbackCompIso_cube`: **the cube**: along a
  commutative square `p ≫ q = r ≫ s` of the site the two pastings of the squares agree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Beta

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- `representedSmallEtaleModuleEquivalencePullbackIso` at one module. -/
theorem representedSmallEtaleModuleEquivalencePullbackIso_hom_app
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)) :
    (representedSmallEtaleModuleEquivalencePullbackIso B S hS g).hom.app M =
      (representedSmallEtaleModuleEquivalence B S hS T').counitInv.app
          ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
            ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj M)) ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((representedModulePullbackIso B S hS g
                (relativelyRepresentable_yoneda_map B S hS g)).hom.app
              ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj M) ≫
            (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map
              ((representedSmallEtaleModuleEquivalence B S hS T).unitInv.app M)) := by
  rw [representedSmallEtaleModuleEquivalencePullbackIso]
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
    (Stacks.CategoryTheory.SquareComposition.equivalenceSquare_hom_app
    (representedSmallEtaleModuleEquivalence B S hS T)
    (representedSmallEtaleModuleEquivalence B S hS T')
    (modulePullback B S hS (representedSpaceMap B S hS g))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g))
    (representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)) M))
    (by heq_congr)))

/-- `representedZariskiModulePullbackCompIso` at one module. -/
theorem representedZariskiModulePullbackCompIso_hom_app
    (M : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    (representedZariskiModulePullbackCompIso B S hS g).hom.app M =
      (modulePullback B S hS (representedSpaceMap B S hS g)).map
          (((representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
              B S hS T) ≪≫
            Functor.isoWhiskerLeft
              (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
              (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS T)).hom.app
            M) ≫
        (representedSmallEtaleModuleEquivalencePullbackIso B S hS g).hom.app
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj M) ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
            (associatedBigEtaleSite B) (g).left).inv.app M) ≫
        ((representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
            B S hS T') ≪≫
          Functor.isoWhiskerLeft
            (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
            (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS T')).inv.app
          ((Scheme.Modules.pullback (B.inclusion.map (g).left)).obj M) := by
  rw [representedZariskiModulePullbackCompIso]
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
    (Stacks.CategoryTheory.SquareComposition.pastedSquare_hom_app
      (modulePullback B S hS (representedSpaceMap B S hS g))
      (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g))
      (Scheme.Modules.pullback (B.inclusion.map (g).left))
      (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS T)
      (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS T)
      (representedSmallEtaleModuleEquivalencePullbackIso B S hS g)
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
        (associatedBigEtaleSite B) (g).left)
      (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS T')
      (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS T') M))
    (by heq_congr)))

/-- `representedZariskiModulePullbackCompIso` along equal morphisms of the site. -/
theorem representedZariskiModulePullbackCompIso_congr {g' : T' ⟶ T} (hg : g = g')
    (F : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    (representedZariskiModulePullbackCompIso B S hS g).hom.app F ≫
        (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T').map
          ((Scheme.Modules.pullbackCongr
            (congrArg (fun k : T' ⟶ T => B.inclusion.map k.left) hg)).hom.app F) =
      (eqToIso (congrArg
          (fun k : T' ⟶ T => modulePullback B S hS (representedSpaceMap B S hS k)) hg)).hom.app
          ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj F) ≫
        (representedZariskiModulePullbackCompIso B S hS g').hom.app F := by
  subst hg
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  exact (congrArg ((representedZariskiModulePullbackCompIso B S hS g).hom.app F ≫ ·)
    ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T').map_id _)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

end Beta

section Comp

variable {X Y Z : BigFppfOver B S hS} (p : X ⟶ Y) (q : Y ⟶ Z)

/-- **The composition law of the identification of inverse images across the equivalences of small
étale sites** (`representedSmallEtaleModuleEquivalencePullbackIso`). -/
theorem representedSmallEtaleModuleEquivalencePullbackIso_comp
    (h : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q =
      representedSpaceMap B S hS (p ≫ q)) :
    Functor.whiskerRight (representedSmallEtaleModuleEquivalencePullbackIso B S hS q).hom
          (modulePullback B S hS (representedSpaceMap B S hS p)) ≫
        Functor.whiskerLeft
          (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS q))
          (representedSmallEtaleModuleEquivalencePullbackIso B S hS p).hom ≫
        Functor.whiskerRight
          (SmallEtale.smallEtalePullbackCompIso (associatedBigEtaleSite B) p.left q.left).hom
          (representedSmallEtaleModuleEquivalence B S hS X).functor =
      Functor.whiskerLeft (representedSmallEtaleModuleEquivalence B S hS Z).functor
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
            (representedSpaceMap B S hS q)).hom ≫ eqToHom (congrArg (modulePullback B S hS) h)) ≫
        (representedSmallEtaleModuleEquivalencePullbackIso B S hS (p ≫ q)).hom :=
  Stacks.CategoryTheory.SquareComposition.equivalenceSquare_comp
    (representedSmallEtaleModuleEquivalence B S hS X)
    (representedSmallEtaleModuleEquivalence B S hS Y)
    (representedSmallEtaleModuleEquivalence B S hS Z)
    (modulePullback B S hS (representedSpaceMap B S hS p))
    (modulePullback B S hS (representedSpaceMap B S hS q))
    (modulePullback B S hS (representedSpaceMap B S hS (p ≫ q)))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS p))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS q))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS (p ≫ q)))
    (representedModulePullbackIso B S hS p (relativelyRepresentable_yoneda_map B S hS p))
    (representedModulePullbackIso B S hS q (relativelyRepresentable_yoneda_map B S hS q))
    (representedModulePullbackIso B S hS (p ≫ q)
      (relativelyRepresentable_yoneda_map B S hS (p ≫ q)))
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
      (representedSpaceMap B S hS q)).hom ≫ eqToHom (congrArg (modulePullback B S hS) h))
    (SmallEtale.smallEtalePullbackCompIso (associatedBigEtaleSite B) p.left q.left).hom
    (representedModulePullbackIso_hom_comp_of_eq B S hS p q h)
    (representedSmallEtaleModuleEquivalencePullbackIso B S hS p)
    (representedSmallEtaleModuleEquivalencePullbackIso B S hS q)
    (representedSmallEtaleModuleEquivalencePullbackIso B S hS (p ≫ q))
    (representedSmallEtaleModuleEquivalencePullbackIso_hom_app B S hS p)
    (representedSmallEtaleModuleEquivalencePullbackIso_hom_app B S hS q)
    (representedSmallEtaleModuleEquivalencePullbackIso_hom_app B S hS (p ≫ q))

/-- **The composition law of `representedZariskiModulePullbackCompIso`**: the square of
`ε^*` along `p ≫ q` is the pasting of the squares along `q` and `p`, read through the composition
laws of Stacks 03LU and of the pullbacks of modules on the schemes. -/
theorem representedZariskiModulePullbackCompIso_comp
    (h : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q =
      representedSpaceMap B S hS (p ≫ q)) :
    Functor.whiskerRight (representedZariskiModulePullbackCompIso B S hS q).hom
          (modulePullback B S hS (representedSpaceMap B S hS p)) ≫
        Functor.whiskerLeft (Scheme.Modules.pullback (B.inclusion.map (q).left))
          (representedZariskiModulePullbackCompIso B S hS p).hom ≫
        Functor.whiskerRight
          (Scheme.Modules.pullbackComp (B.inclusion.map p.left) (B.inclusion.map q.left)).hom
          (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS X) =
      Functor.whiskerLeft (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS Z)
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
            (representedSpaceMap B S hS q)).hom ≫ eqToHom (congrArg (modulePullback B S hS) h)) ≫
        (representedZariskiModulePullbackCompIso B S hS (p ≫ q)).hom :=
  Stacks.CategoryTheory.SquareComposition.pastedSquare_comp
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS X)
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS Y)
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS Z)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj X) X.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj Y) Y.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj Z) Z.left.property)
    (representedSmallEtaleModuleEquivalence B S hS X).functor
    (representedSmallEtaleModuleEquivalence B S hS Y).functor
    (representedSmallEtaleModuleEquivalence B S hS Z).functor
    ((representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS X) ≪≫
      Functor.isoWhiskerLeft
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj X) X.left.property)
        (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS X))
    ((representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS Y) ≪≫
      Functor.isoWhiskerLeft
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj Y) Y.left.property)
        (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS Y))
    ((representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS Z) ≪≫
      Functor.isoWhiskerLeft
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj Z) Z.left.property)
        (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS Z))
    (modulePullback B S hS (representedSpaceMap B S hS p))
    (modulePullback B S hS (representedSpaceMap B S hS q))
    (modulePullback B S hS (representedSpaceMap B S hS (p ≫ q)))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS p))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS q))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS (p ≫ q)))
    (Scheme.Modules.pullback (B.inclusion.map (p).left))
    (Scheme.Modules.pullback (B.inclusion.map (q).left))
    (Scheme.Modules.pullback (B.inclusion.map ((p ≫ q)).left))
    (representedSmallEtaleModuleEquivalencePullbackIso B S hS p)
    (representedSmallEtaleModuleEquivalencePullbackIso B S hS q)
    (representedSmallEtaleModuleEquivalencePullbackIso B S hS (p ≫ q))
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso (associatedBigEtaleSite B)
      (p).left)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso (associatedBigEtaleSite B)
      (q).left)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso (associatedBigEtaleSite B)
      ((p ≫ q)).left)
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
      (representedSpaceMap B S hS q)).hom ≫ eqToHom (congrArg (modulePullback B S hS) h))
    (SmallEtale.smallEtalePullbackCompIso (associatedBigEtaleSite B) p.left q.left).hom
    (Scheme.Modules.pullbackComp (B.inclusion.map p.left) (B.inclusion.map q.left)).hom
    (representedSmallEtaleModuleEquivalencePullbackIso_comp B S hS p q h)
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (Stacks.CategoryTheory.SquareComposition.whiskered_inv_comp _ _ _ _ _
        (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp
          (associatedBigEtaleSite B) p.left q.left))) (by heq_congr))))
    (representedZariskiModulePullbackCompIso B S hS p)
    (representedZariskiModulePullbackCompIso B S hS q)
    (representedZariskiModulePullbackCompIso B S hS (p ≫ q))
    (fun M => eq_of_heq (HEq.trans (by heq_congr) (HEq.trans
      (heq_of_eq (representedZariskiModulePullbackCompIso_hom_app B S hS p M)) (by heq_congr))))
    (fun M => eq_of_heq (HEq.trans (by heq_congr) (HEq.trans
      (heq_of_eq (representedZariskiModulePullbackCompIso_hom_app B S hS q M)) (by heq_congr))))
    (fun M => eq_of_heq (HEq.trans (by heq_congr) (HEq.trans
      (heq_of_eq
        (representedZariskiModulePullbackCompIso_hom_app B S hS (p ≫ q) M)) (by heq_congr))))

end Comp

/-- `representedZariskiModulePullbackCompIso` along equal morphisms of the site, as natural
transformations. -/
theorem representedZariskiModulePullbackCompIso_congr_hom {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {g' : T' ⟶ T} (hg : g = g') :
    (representedZariskiModulePullbackCompIso B S hS g).hom ≫
        Functor.whiskerRight (Scheme.Modules.pullbackCongr
          (congrArg (fun k : T' ⟶ T => B.inclusion.map k.left) hg)).hom
          (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T') =
      Functor.whiskerLeft (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T)
          (eqToHom (congrArg
            (fun k : T' ⟶ T => modulePullback B S hS (representedSpaceMap B S hS k)) hg)) ≫
        (representedZariskiModulePullbackCompIso B S hS g').hom := by
  subst hg
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom]
  exact (congrArg ((representedZariskiModulePullbackCompIso B S hS g).hom ≫ ·)
    (Functor.whiskerRight_id' _)).trans ((Category.comp_id _).trans
      ((congrArg (· ≫ (representedZariskiModulePullbackCompIso B S hS g).hom)
        (Functor.whiskerLeft_id' _)).trans (Category.id_comp _)).symm)

section Cube

variable {W' W T' T : BigFppfOver B S hS} (p : W' ⟶ W) (q : W ⟶ T) (r : W' ⟶ T') (s : T' ⟶ T)
  (w : p ≫ q = r ≫ s)
  (hw : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q =
    representedSpaceMap B S hS r ≫ representedSpaceMap B S hS s)
  (w₀ : B.inclusion.map p.left ≫ B.inclusion.map q.left =
    B.inclusion.map r.left ≫ B.inclusion.map s.left)

include w in
/-- **The cube of `representedZariskiModulePullbackCompIso`**: along a commutative square
`p ≫ q = r ≫ s` of the site, the two pastings of the squares of `ε^*` agree, read through the
composition laws of Stacks 03LU on the spaces and of the pullbacks of modules on the schemes. -/
theorem representedZariskiModulePullbackCompIso_cube
    (F : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    (modulePullback B S hS (representedSpaceMap B S hS p)).map
        ((representedZariskiModulePullbackCompIso B S hS q).hom.app F) ≫
      (representedZariskiModulePullbackCompIso B S hS p).hom.app
        ((Scheme.Modules.pullback (B.inclusion.map (q).left)).obj F) ≫
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS W').map
        (((Scheme.Modules.pullbackComp (B.inclusion.map p.left) (B.inclusion.map q.left)).hom ≫
          (Scheme.Modules.pullbackCongr w₀).hom ≫
          (Scheme.Modules.pullbackComp (B.inclusion.map r.left) (B.inclusion.map s.left)).inv).app
            F) =
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
          (representedSpaceMap B S hS q)).hom ≫
        eqToHom (congrArg (modulePullback B S hS) hw) ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS r)
          (representedSpaceMap B S hS s)).inv).app
        ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj F) ≫
      (modulePullback B S hS (representedSpaceMap B S hS r)).map
        ((representedZariskiModulePullbackCompIso B S hS s).hom.app F) ≫
      (representedZariskiModulePullbackCompIso B S hS r).hom.app
        ((Scheme.Modules.pullback (B.inclusion.map (s).left)).obj F) := by
  have hpq := representedZariskiModulePullbackCompIso_comp B S hS p q
    (ObjectProperty.hom_ext _ (yoneda.map_comp p q)).symm
  have hrs := representedZariskiModulePullbackCompIso_comp B S hS r s
    (ObjectProperty.hom_ext _ (yoneda.map_comp r s)).symm
  have ht := representedZariskiModulePullbackCompIso_congr_hom B S hS (p ≫ q) w
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
    (Stacks.CategoryTheory.SquareComposition.pastedSquare_cube
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
          (representedSpaceMap B S hS q)).hom ≫
        eqToHom (congrArg (modulePullback B S hS) hw) ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS r)
          (representedSpaceMap B S hS s)).inv) hpq hrs ht
      (Stacks.CategoryTheory.SquareComposition.comp_eqToHom_eq_comp_inv_comp _ _ _ _ _ _) F))
    (by heq_congr)))

end Cube

end AlgebraicGeometry.Space
