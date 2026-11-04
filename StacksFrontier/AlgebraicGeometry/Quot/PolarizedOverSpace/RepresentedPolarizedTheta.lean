module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedFunctor

/-!
# The comparison `RepresentedPolarized ⥤ Polarized` over the site

The comparison `AlgebraicGeometry.PolarizedOverSpace.toPolarizedMap` restricts the comparison of
modules of a morphism of `AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized` (a module on
the small étale site of a representable algebraic space) to the Zariski site of the representing
scheme, through `AlgebraicGeometry.Space.representedZariskiModulePullbackIso`. It is a functor
`Θ`, and a functor over the site.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.toPolarized`: the functor `Θ`.
* `AlgebraicGeometry.PolarizedOverSpace.toPolarizedBased`: `Θ` as a functor over the site.

## Main results

* `CategoryTheory.comparison_comp_law`: the composition law of a comparison of pullbacks with
  restrictions, at variable categories.
* `AlgebraicGeometry.PolarizedOverSpace.toPolarizedLineBundleIso_comp_hom`: the composition law of
  the comparisons of polarizations.

## Implementation notes

Every hypothesis fed to `CategoryTheory.comparison_comp_law` is first stated, as its own lemma, in
exactly the form the abstract lemma expects once instantiated (the objects of every composite are
written out by type ascriptions): a composite whose implicit objects are only definitionally equal
to the expected ones is compared by the kernel through the category structure of sheaves of
modules, which is unaffordable. The inverse images, the equivalence of small étale sites and the
restriction to the Zariski site are irreducible for elaboration here for the same reason.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

-- Elaboration compares arguments of the large functors below rather than unfolding them.
attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso
        Scheme.Modules.pullback
  Space.representedSmallEtaleModuleEquivalence SmallEtale.restrictModule

/-- **The composition law of a comparison of pullbacks with restrictions**, at variable
categories. Let `c` be a comparison `P(R M) ≅ R(Q M)` of pullbacks `P` with restrictions `R`,
natural (`nat`) and compatible with the contractions `pc` of the `P`'s and `qhom` of the `Q`'s
(`law`). Then the comparison at a composite, followed by the restriction of the composite of the
comparisons of modules, is the contraction followed by the two comparisons. -/
theorem _root_.CategoryTheory.comparison_comp_law {DZ DY DX GZ GY GX EZ EY EX : Type*}
    [Category DZ] [Category DY] [Category DX] [Category GZ] [Category GY] [Category GX]
    [Category EZ] [Category EY] [Category EX]
    (Pa : DY ⥤ DX) (Pb : DZ ⥤ DY) (Pab : DZ ⥤ DX) (pc : Pb ⋙ Pa ≅ Pab)
    (Qa : EY ⥤ EX) (Qb : EZ ⥤ EY) (QQ Qab : EZ ⥤ EX)
    (R1Z : EZ ⥤ GZ) (R2Z : GZ ⥤ DZ) (R1Y : EY ⥤ GY) (R2Y : GY ⥤ DY) (R1X : EX ⥤ GX)
    (R2X : GX ⥤ DX) (MZ : EZ) (MY : EY) (MX : EX)
    (qhom : QQ.obj MZ ⟶ Qab.obj MZ) (qinv : Qab.obj MZ ⟶ QQ.obj MZ)
    (hq : qhom ≫ qinv = 𝟙 _)
    (cb : Pb.obj (R2Z.obj (R1Z.obj MZ)) ≅ R2Y.obj (R1Y.obj (Qb.obj MZ)))
    (caQ : Pa.obj (R2Y.obj (R1Y.obj (Qb.obj MZ))) ≅ R2X.obj (R1X.obj (QQ.obj MZ)))
    (caM : Pa.obj (R2Y.obj (R1Y.obj MY)) ≅ R2X.obj (R1X.obj (Qa.obj MY)))
    (cab : Pab.obj (R2Z.obj (R1Z.obj MZ)) ≅ R2X.obj (R1X.obj (Qab.obj MZ)))
    (ψ : Qb.obj MZ ⟶ MY) (ψ' : QQ.obj MZ ⟶ Qa.obj MY) (φ : Qa.obj MY ⟶ MX)
    (nat : Pa.map (R2Y.map (R1Y.map ψ)) ≫ caM.hom = caQ.hom ≫ R2X.map (R1X.map ψ'))
    (law : Pa.map cb.hom ≫ caQ.hom ≫ R2X.map (R1X.map qhom) =
      pc.hom.app (R2Z.obj (R1Z.obj MZ)) ≫ cab.hom) :
    cab.hom ≫ R2X.map (R1X.map (qinv ≫ ψ' ≫ φ)) =
      pc.inv.app (R2Z.obj (R1Z.obj MZ)) ≫ Pa.map (cb.hom ≫ R2Y.map (R1Y.map ψ)) ≫ caM.hom ≫
        R2X.map (R1X.map φ) := by
  have hcab : cab.hom = pc.inv.app (R2Z.obj (R1Z.obj MZ)) ≫ Pa.map cb.hom ≫ caQ.hom ≫
      R2X.map (R1X.map qhom) := by
    rw [law, Iso.inv_hom_id_app_assoc]
  have hq' : R2X.map (R1X.map qhom) ≫ R2X.map (R1X.map qinv) = 𝟙 _ := by
    rw [← R2X.map_comp, ← R1X.map_comp, hq, R1X.map_id, R2X.map_id]
  rw [hcab]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nat, reassoc_of% hq']


/-- The cancellation `(a ≫ L b ≫ e) ≫ e' ≫ L b⁻¹ ≫ a⁻¹ = 𝟙` given `e ≫ e' = 𝟙`, at variable
categories. -/
theorem _root_.CategoryTheory.comp_inv_cancel_aux {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) {X : D} {Y W : C} {V : D} (a : X ⟶ L.obj Y) (ha : IsIso a) (b : Y ⟶ W)
    (hb : IsIso b) (e : L.obj W ⟶ V) (e' : V ⟶ L.obj W) (he : e ≫ e' = 𝟙 _) :
    (a ≫ L.map b ≫ e) ≫ e' ≫ L.map (inv b) ≫ inv a = 𝟙 X := by
  simp [reassoc_of% he]

section CompLaw

variable {B : BigFppfSite.{u}} {X Y Z : RepresentedPolarized B} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The inverse of the comparison of modules of a composite, in the fibre categories. -/
theorem inv_fiber_comp_eq : inv (I := isIso_fiber (f ≫ g)) (f ≫ g).hom.hom.fiber =
    ((arrowModules B).mapComp g.hom.hom.base.op.toLoc f.hom.hom.base.op.toLoc).hom.toNatTrans.app
        Z.obj.obj.fiber ≫
      ((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor.map
        (inv (I := isIso_fiber g) g.hom.hom.fiber) ≫ inv (I := isIso_fiber f) f.hom.hom.fiber := by
  have := isIso_fiber f
  have := isIso_fiber g
  have := isIso_fiber (f ≫ g)
  apply IsIso.inv_eq_of_hom_inv_id
  refine (congrArg (fun x => x ≫ _) (fiber_comp f g)).trans ?_
  exact _root_.CategoryTheory.comp_inv_cancel_aux
    ((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor
    f.hom.hom.fiber (isIso_fiber f) g.hom.hom.fiber (isIso_fiber g) _ _
    (Cat.Hom.inv_hom_id_toNatTrans_app _ _)

/-- Modules on the small étale site of `yoneda Z`, read on the small étale site of `Z`. -/
abbrev etaleInverse (A : Arrow (Site B)) :=
  (Space.representedSmallEtaleModuleEquivalence B integerBase (hZ B) A.left).inverse

/-- Restriction from the small étale site of `Z` to its Zariski site. -/
abbrev zariskiRestriction (A : Arrow (Site B)) :=
  _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B integerBase (hZ B)).obj A.left) A.left.left.property

/-- Naturality of the comparison at the inverse of the comparison of modules of `g`. -/
theorem toPolarizedNaturalityModules : (Scheme.Modules.pullback (sch B f.hom.hom.base.left)).map
        ((zariskiRestriction Y.obj.obj.base).map ((etaleInverse Y.obj.obj.base).map
          (inv (I := isIso_fiber g) g.hom.hom.fiber :
            (Space.modulePullback B integerBase (hZ B)
              (Space.representedSpaceMap B integerBase (hZ B) g.hom.hom.base.left)).obj
                Z.obj.obj.fiber ⟶ Y.obj.obj.fiber))) ≫
        (Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
          (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) Y.obj.obj.fiber
          Y.obj.property.quasicoherent).hom =
      (Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
          (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) _
          (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ B)
            g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
            Z.obj.obj.fiber Z.obj.property.quasicoherent)).hom ≫
        (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map
          ((Space.modulePullback B integerBase (hZ B)
            (Space.representedSpaceMap B integerBase (hZ B) f.hom.hom.base.left)).map
          (inv (I := isIso_fiber g) g.hom.hom.fiber :
            (Space.modulePullback B integerBase (hZ B)
              (Space.representedSpaceMap B integerBase (hZ B) g.hom.hom.base.left)).obj
                Z.obj.obj.fiber ⟶ Y.obj.obj.fiber))) :=
  Space.representedZariskiModulePullbackIso_naturality B integerBase (hZ B)
    f.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
    (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ B)
      g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
      Z.obj.obj.fiber Z.obj.property.quasicoherent)
    Y.obj.property.quasicoherent (inv (I := isIso_fiber g) g.hom.hom.fiber)

/-- `toPolarizedNaturalityModules`, with the inverse image of the fibre category. -/
theorem toPolarizedNaturalityFibre : (Scheme.Modules.pullback (sch B f.hom.hom.base.left)).map
        ((zariskiRestriction Y.obj.obj.base).map ((etaleInverse Y.obj.obj.base).map
          (inv (I := isIso_fiber g) g.hom.hom.fiber))) ≫
        (Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
          (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) Y.obj.obj.fiber
          Y.obj.property.quasicoherent).hom =
      (Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
          (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) _
          (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ B)
            g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
            Z.obj.obj.fiber Z.obj.property.quasicoherent)).hom ≫
        (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map
          (((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor.map
            (inv (I := isIso_fiber g) g.hom.hom.fiber))) :=
  (toPolarizedNaturalityModules f g).trans (congrArg (fun x => _ ≫
    (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map x))
    (arrowModules_map_map B f.hom.hom.base (inv (I := isIso_fiber g) g.hom.hom.fiber)).symm)

/-- The composition law of the comparison at the module of `Z`. -/
theorem toPolarizedCompLawFibre : (Scheme.Modules.pullback (sch B f.hom.hom.base.left)).map
        (Space.representedZariskiModulePullbackIso B integerBase (hZ B) g.hom.hom.base.left
          (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) Z.obj.obj.fiber
          Z.obj.property.quasicoherent).hom ≫
      (Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
          (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) _
          (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ B)
            g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
            Z.obj.obj.fiber Z.obj.property.quasicoherent)).hom ≫
        (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map
          ((Space.representedModulePullbackCompIso B integerBase (hZ B)
      f.hom.hom.base.left g.hom.hom.base.left).hom.app Z.obj.obj.fiber :
        ((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor.obj
          (((arrowModules B).map g.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber) ⟶
        ((arrowModules B).map (g.hom.hom.base.op.toLoc ≫ f.hom.hom.base.op.toLoc)).toFunctor.obj
          Z.obj.obj.fiber)) =
      (Scheme.Modules.pullbackComp (sch B f.hom.hom.base.left)
          (sch B g.hom.hom.base.left)).hom.app ((zariskiRestriction Z.obj.obj.base).obj
            ((etaleInverse Z.obj.obj.base).obj Z.obj.obj.fiber)) ≫
        (Space.representedZariskiModulePullbackIso B integerBase (hZ B)
          (f.hom.hom.base.left ≫ g.hom.hom.base.left)
          (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) Z.obj.obj.fiber
          Z.obj.property.quasicoherent).hom :=
  Space.representedZariskiModulePullbackIso_comp B integerBase (hZ B)
    f.hom.hom.base.left g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase
        (hZ B) _)
    (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
    (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) Z.obj.obj.fiber
    Z.obj.property.quasicoherent

omit f in
/-- The comparison of polarizations of a morphism, written out. -/
theorem toPolarizedLineBundleIso_hom_eq (f : X ⟶ Y) :
    (toPolarizedLineBundleIso B f).hom =
      (Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) Y.obj.obj.fiber
        Y.obj.property.quasicoherent).hom ≫
        (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map
          (inv (I := isIso_fiber f) f.hom.hom.fiber)) := rfl

/-- `toPolarizedNaturalityFibre` in the form `CategoryTheory.comparison_comp_law` takes. -/
theorem toPolarizedNaturality : ((Scheme.Modules.pullback (sch B f.hom.hom.base.left)).map
        ((zariskiRestriction Y.obj.obj.base).map ((etaleInverse Y.obj.obj.base).map (inv (I :=
        isIso_fiber g) g.hom.hom.fiber))) :
        (Scheme.Modules.pullback (sch B f.hom.hom.base.left)).obj ((zariskiRestriction
        Y.obj.obj.base).obj ((etaleInverse Y.obj.obj.base).obj (((arrowModules B).map
        g.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber))) ⟶ (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj Y.obj.obj.fiber))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) Y.obj.obj.fiber Y.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj Y.obj.obj.fiber)) ⟶ ((zariskiRestriction X.obj.obj.base).obj
        ((etaleInverse X.obj.obj.base).obj (((arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Y.obj.obj.fiber)))) =
    ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) _ (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ
        B) g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent)).hom : (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc).toFunctor.obj
        Z.obj.obj.fiber))) ⟶ ((zariskiRestriction X.obj.obj.base).obj ((etaleInverse
        X.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc ≫ (arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber)))) ≫
      (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map (((arrowModules
        B).map f.hom.hom.base.op.toLoc).toFunctor.map (inv (I := isIso_fiber g) g.hom.hom.fiber) :
        (((arrowModules B).map g.hom.hom.base.op.toLoc ≫ (arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber) ⟶ (((arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Y.obj.obj.fiber))) :=
  toPolarizedNaturalityFibre f g

/-- `toPolarizedCompLawFibre` with the objects of `CategoryTheory.comparison_comp_law`. -/
theorem toPolarizedCompLawAux : ((Scheme.Modules.pullback (sch B f.hom.hom.base.left)).map
        ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) g.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) Z.obj.obj.fiber Z.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        g.hom.hom.base.left)).obj ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse
        Z.obj.obj.base).obj Z.obj.obj.fiber)) ⟶ ((zariskiRestriction Y.obj.obj.base).obj
        ((etaleInverse Y.obj.obj.base).obj (((arrowModules B).map
        g.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber))))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) _ (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ
        B) g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent)).hom : (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc).toFunctor.obj
        Z.obj.obj.fiber))) ⟶ ((zariskiRestriction X.obj.obj.base).obj ((etaleInverse
        X.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc ≫ (arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber)))) ≫
      (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map
        (((Space.representedModulePullbackCompIso B integerBase (hZ B) f.hom.hom.base.left
        g.hom.hom.base.left).hom.app Z.obj.obj.fiber) : (((arrowModules
        B).map g.hom.hom.base.op.toLoc ≫ (arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber) ⟶ (((arrowModules B).map
        (g.hom.hom.base.op.toLoc ≫ f.hom.hom.base.op.toLoc)).toFunctor.obj Z.obj.obj.fiber))) =
    ((Scheme.Modules.pullbackComp (sch B f.hom.hom.base.left) (sch B g.hom.hom.base.left)).hom.app
        ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse Z.obj.obj.base).obj
        Z.obj.obj.fiber)) : ((Scheme.Modules.pullback (sch B
        g.hom.hom.base.left)) ⋙ (Scheme.Modules.pullback (sch B f.hom.hom.base.left))).obj
        ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse Z.obj.obj.base).obj
        Z.obj.obj.fiber)) ⟶ (Scheme.Modules.pullback (sch B (f.hom.hom.base.left ≫
        g.hom.hom.base.left))).obj ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse
        Z.obj.obj.base).obj Z.obj.obj.fiber))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) (f.hom.hom.base.left ≫
        g.hom.hom.base.left) (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        (f.hom.hom.base.left ≫ g.hom.hom.base.left))).obj ((zariskiRestriction Z.obj.obj.base).obj
        ((etaleInverse Z.obj.obj.base).obj Z.obj.obj.fiber)) ⟶ ((zariskiRestriction
        X.obj.obj.base).obj ((etaleInverse X.obj.obj.base).obj (((arrowModules B).map
        (g.hom.hom.base.op.toLoc ≫ f.hom.hom.base.op.toLoc)).toFunctor.obj Z.obj.obj.fiber)))) :=
  toPolarizedCompLawFibre f g

/-- The composition law of the comparison, through the composition comparison of
`arrowModules`, in the form `CategoryTheory.comparison_comp_law` takes. -/
theorem toPolarizedCompLaw : ((Scheme.Modules.pullback (sch B f.hom.hom.base.left)).map
        ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) g.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) Z.obj.obj.fiber Z.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        g.hom.hom.base.left)).obj ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse
        Z.obj.obj.base).obj Z.obj.obj.fiber)) ⟶ ((zariskiRestriction Y.obj.obj.base).obj
        ((etaleInverse Y.obj.obj.base).obj (((arrowModules B).map
        g.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber))))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) _ (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ
        B) g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent)).hom : (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc).toFunctor.obj
        Z.obj.obj.fiber))) ⟶ ((zariskiRestriction X.obj.obj.base).obj ((etaleInverse
        X.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc ≫ (arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber)))) ≫
      (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map (((arrowModules
        B).mapComp g.hom.hom.base.op.toLoc f.hom.hom.base.op.toLoc).inv.toNatTrans.app
        Z.obj.obj.fiber)) =
    ((Scheme.Modules.pullbackComp (sch B f.hom.hom.base.left) (sch B g.hom.hom.base.left)).hom.app
        ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse Z.obj.obj.base).obj
        Z.obj.obj.fiber)) : ((Scheme.Modules.pullback (sch B
        g.hom.hom.base.left)) ⋙ (Scheme.Modules.pullback (sch B f.hom.hom.base.left))).obj
        ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse Z.obj.obj.base).obj
        Z.obj.obj.fiber)) ⟶ (Scheme.Modules.pullback (sch B (f.hom.hom.base.left ≫
        g.hom.hom.base.left))).obj ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse
        Z.obj.obj.base).obj Z.obj.obj.fiber))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) (f.hom.hom.base.left ≫
        g.hom.hom.base.left) (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        (f.hom.hom.base.left ≫ g.hom.hom.base.left))).obj ((zariskiRestriction Z.obj.obj.base).obj
        ((etaleInverse Z.obj.obj.base).obj Z.obj.obj.fiber)) ⟶ ((zariskiRestriction
        X.obj.obj.base).obj ((etaleInverse X.obj.obj.base).obj (((arrowModules B).map
        (g.hom.hom.base.op.toLoc ≫ f.hom.hom.base.op.toLoc)).toFunctor.obj Z.obj.obj.fiber)))) := by
  have law := toPolarizedCompLawAux f g
  rw [← arrowModules_mapComp_inv_app B f.hom.hom.base g.hom.hom.base Z.obj.obj.fiber] at law
  exact law

/-- `CategoryTheory.comparison_comp_law` at a composite of `RepresentedPolarized`. -/
theorem toPolarizedLineBundleIso_comp_key (nat : ((Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).map ((zariskiRestriction Y.obj.obj.base).map ((etaleInverse
        Y.obj.obj.base).map (inv (I := isIso_fiber g) g.hom.hom.fiber))) :
        (Scheme.Modules.pullback (sch B f.hom.hom.base.left)).obj ((zariskiRestriction
        Y.obj.obj.base).obj ((etaleInverse Y.obj.obj.base).obj (((arrowModules B).map
        g.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber))) ⟶ (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj Y.obj.obj.fiber))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) Y.obj.obj.fiber Y.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj Y.obj.obj.fiber)) ⟶ ((zariskiRestriction X.obj.obj.base).obj
        ((etaleInverse X.obj.obj.base).obj (((arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Y.obj.obj.fiber)))) =
    ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) _ (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ
        B) g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent)).hom : (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc).toFunctor.obj
        Z.obj.obj.fiber))) ⟶ ((zariskiRestriction X.obj.obj.base).obj ((etaleInverse
        X.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc ≫ (arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber)))) ≫
      (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map (((arrowModules
        B).map f.hom.hom.base.op.toLoc).toFunctor.map (inv (I := isIso_fiber g) g.hom.hom.fiber) :
        (((arrowModules B).map g.hom.hom.base.op.toLoc ≫ (arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber) ⟶ (((arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Y.obj.obj.fiber)))) (law : ((Scheme.Modules.pullback
        (sch B f.hom.hom.base.left)).map ((Space.representedZariskiModulePullbackIso B integerBase
        (hZ B) g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) Z.obj.obj.fiber Z.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        g.hom.hom.base.left)).obj ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse
        Z.obj.obj.base).obj Z.obj.obj.fiber)) ⟶ ((zariskiRestriction Y.obj.obj.base).obj
        ((etaleInverse Y.obj.obj.base).obj (((arrowModules B).map
        g.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber))))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) _ (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ
        B) g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent)).hom : (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc).toFunctor.obj
        Z.obj.obj.fiber))) ⟶ ((zariskiRestriction X.obj.obj.base).obj ((etaleInverse
        X.obj.obj.base).obj (((arrowModules B).map g.hom.hom.base.op.toLoc ≫ (arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber)))) ≫
      (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map (((arrowModules
        B).mapComp g.hom.hom.base.op.toLoc f.hom.hom.base.op.toLoc).inv.toNatTrans.app
        Z.obj.obj.fiber)) =
    ((Scheme.Modules.pullbackComp (sch B f.hom.hom.base.left) (sch B g.hom.hom.base.left)).hom.app
        ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse Z.obj.obj.base).obj
        Z.obj.obj.fiber)) : ((Scheme.Modules.pullback (sch B
        g.hom.hom.base.left)) ⋙ (Scheme.Modules.pullback (sch B f.hom.hom.base.left))).obj
        ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse Z.obj.obj.base).obj
        Z.obj.obj.fiber)) ⟶ (Scheme.Modules.pullback (sch B (f.hom.hom.base.left ≫
        g.hom.hom.base.left))).obj ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse
        Z.obj.obj.base).obj Z.obj.obj.fiber))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) (f.hom.hom.base.left ≫
        g.hom.hom.base.left) (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        (f.hom.hom.base.left ≫ g.hom.hom.base.left))).obj ((zariskiRestriction Z.obj.obj.base).obj
        ((etaleInverse Z.obj.obj.base).obj Z.obj.obj.fiber)) ⟶ ((zariskiRestriction
        X.obj.obj.base).obj ((etaleInverse X.obj.obj.base).obj (((arrowModules B).map
        (g.hom.hom.base.op.toLoc ≫ f.hom.hom.base.op.toLoc)).toFunctor.obj Z.obj.obj.fiber))))) :
    ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) (f.hom.hom.base.left ≫
        g.hom.hom.base.left) (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        (f.hom.hom.base.left ≫ g.hom.hom.base.left))).obj ((zariskiRestriction Z.obj.obj.base).obj
        ((etaleInverse Z.obj.obj.base).obj Z.obj.obj.fiber)) ⟶ ((zariskiRestriction
        X.obj.obj.base).obj ((etaleInverse X.obj.obj.base).obj (((arrowModules B).map
        (g.hom.hom.base.op.toLoc ≫ f.hom.hom.base.op.toLoc)).toFunctor.obj Z.obj.obj.fiber)))) ≫
      (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map ((((arrowModules
        B).mapComp g.hom.hom.base.op.toLoc f.hom.hom.base.op.toLoc).hom.toNatTrans.app
        Z.obj.obj.fiber) ≫ (((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor.map (inv (I :=
        isIso_fiber g) g.hom.hom.fiber) : (((arrowModules B).map g.hom.hom.base.op.toLoc ≫
        (arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber) ⟶
        (((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor.obj Y.obj.obj.fiber)) ≫ (inv (I
        := isIso_fiber f) f.hom.hom.fiber))) =
    ((Scheme.Modules.pullbackComp (sch B f.hom.hom.base.left) (sch B g.hom.hom.base.left)).inv.app
        ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse Z.obj.obj.base).obj
        Z.obj.obj.fiber)) : (Scheme.Modules.pullback (sch B (f.hom.hom.base.left ≫
        g.hom.hom.base.left))).obj ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse
        Z.obj.obj.base).obj Z.obj.obj.fiber)) ⟶ ((Scheme.Modules.pullback (sch B
        g.hom.hom.base.left)) ⋙ (Scheme.Modules.pullback (sch B f.hom.hom.base.left))).obj
        ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse Z.obj.obj.base).obj
        Z.obj.obj.fiber))) ≫
      (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).map (((Space.representedZariskiModulePullbackIso B integerBase (hZ B)
        g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) Z.obj.obj.fiber Z.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        g.hom.hom.base.left)).obj ((zariskiRestriction Z.obj.obj.base).obj ((etaleInverse
        Z.obj.obj.base).obj Z.obj.obj.fiber)) ⟶ ((zariskiRestriction Y.obj.obj.base).obj
        ((etaleInverse Y.obj.obj.base).obj (((arrowModules B).map
        g.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber)))) ≫
        (zariskiRestriction Y.obj.obj.base).map ((etaleInverse Y.obj.obj.base).map (inv (I :=
        isIso_fiber g) g.hom.hom.fiber))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) Y.obj.obj.fiber Y.obj.property.quasicoherent).hom : (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)).obj ((zariskiRestriction Y.obj.obj.base).obj ((etaleInverse
        Y.obj.obj.base).obj Y.obj.obj.fiber)) ⟶ ((zariskiRestriction X.obj.obj.base).obj
        ((etaleInverse X.obj.obj.base).obj (((arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Y.obj.obj.fiber)))) ≫
      (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map (inv (I :=
        isIso_fiber f) f.hom.hom.fiber)) :=
  _root_.CategoryTheory.comparison_comp_law (Scheme.Modules.pullback (sch B
        f.hom.hom.base.left)) (Scheme.Modules.pullback (sch B g.hom.hom.base.left))
        (Scheme.Modules.pullback (sch B (f.hom.hom.base.left ≫ g.hom.hom.base.left)))
        (Scheme.Modules.pullbackComp (sch B f.hom.hom.base.left) (sch B g.hom.hom.base.left))
        ((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor ((arrowModules B).map
        g.hom.hom.base.op.toLoc).toFunctor ((arrowModules B).map g.hom.hom.base.op.toLoc ≫
        (arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor ((arrowModules B).map
        (g.hom.hom.base.op.toLoc ≫ f.hom.hom.base.op.toLoc)).toFunctor
    (etaleInverse Z.obj.obj.base) (zariskiRestriction Z.obj.obj.base) (etaleInverse
        Y.obj.obj.base) (zariskiRestriction Y.obj.obj.base)
    (etaleInverse X.obj.obj.base) (zariskiRestriction
        X.obj.obj.base) Z.obj.obj.fiber Y.obj.obj.fiber X.obj.obj.fiber
    (((arrowModules B).mapComp g.hom.hom.base.op.toLoc f.hom.hom.base.op.toLoc).inv.toNatTrans.app
        Z.obj.obj.fiber) (((arrowModules B).mapComp g.hom.hom.base.op.toLoc
        f.hom.hom.base.op.toLoc).hom.toNatTrans.app Z.obj.obj.fiber)
        (Cat.Hom.inv_hom_id_toNatTrans_app _ _) (Space.representedZariskiModulePullbackIso B
        integerBase (hZ B) g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B
        integerBase (hZ B) _) Z.obj.obj.fiber Z.obj.property.quasicoherent)
        (Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) _
        (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ B)
        g.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
        Z.obj.obj.fiber Z.obj.property.quasicoherent)) (Space.representedZariskiModulePullbackIso B
        integerBase (hZ B) f.hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B
        integerBase (hZ B) _) Y.obj.obj.fiber Y.obj.property.quasicoherent)
        (Space.representedZariskiModulePullbackIso B integerBase (hZ B) (f.hom.hom.base.left ≫
        g.hom.hom.base.left) (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
        Z.obj.obj.fiber Z.obj.property.quasicoherent) (inv (I := isIso_fiber g) g.hom.hom.fiber)
        (((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor.map (inv (I := isIso_fiber g)
        g.hom.hom.fiber) : (((arrowModules B).map g.hom.hom.base.op.toLoc ≫ (arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Z.obj.obj.fiber) ⟶ (((arrowModules B).map
        f.hom.hom.base.op.toLoc).toFunctor.obj Y.obj.obj.fiber)) (inv (I := isIso_fiber f)
        f.hom.hom.fiber)
    nat law

/-- The comparison of polarizations of a composite, written out. -/
theorem toPolarizedLineBundleIso_comp_hom_eq : (toPolarizedLineBundleIso B (f ≫ g)).hom =
    (Space.representedZariskiModulePullbackIso B integerBase (hZ B) (f ≫ g).hom.hom.base.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) Z.obj.obj.fiber Z.obj.property.quasicoherent).hom ≫
      (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map
        (((arrowModules B).mapComp g.hom.hom.base.op.toLoc
        f.hom.hom.base.op.toLoc).hom.toNatTrans.app
          Z.obj.obj.fiber ≫
        ((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor.map
          (inv (I := isIso_fiber g) g.hom.hom.fiber) ≫ inv (I := isIso_fiber f) f.hom.hom.fiber)) :=
  (toPolarizedLineBundleIso_hom_eq (f ≫ g)).trans (congrArg (fun x => _ ≫
    (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map x))
    (inv_fiber_comp_eq f g))

/-- The comparison at the base of a composite is the comparison at the composite of bases. -/
theorem zariskiPullbackIso_comp_base : Space.representedZariskiModulePullbackIso B integerBase (hZ
        B)
      (f ≫ g).hom.hom.base.left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B)
        _) Z.obj.obj.fiber Z.obj.property.quasicoherent =
    Space.representedZariskiModulePullbackIso B integerBase (hZ B) (f.hom.hom.base.left ≫
        g.hom.hom.base.left) (Space.relativelyRepresentable_yoneda_map B integerBase (hZ
        B) _) Z.obj.obj.fiber
      Z.obj.property.quasicoherent :=
  rfl

/-- **The composition law of the comparisons of polarizations.** -/
theorem toPolarizedLineBundleIso_comp_hom :
    (toPolarizedLineBundleIso B (f ≫ g)).hom =
      (Scheme.Modules.pullbackComp (sch B f.hom.hom.base.left) (sch B g.hom.hom.base.left)).inv.app
          (zariskiPolarization B Z.obj.obj) ≫
        (Scheme.Modules.pullback (sch B f.hom.hom.base.left)).map
          (toPolarizedLineBundleIso B g).hom ≫ (toPolarizedLineBundleIso B f).hom := by
  rw [toPolarizedLineBundleIso_comp_hom_eq f g, toPolarizedLineBundleIso_hom_eq g,
    toPolarizedLineBundleIso_hom_eq f, zariskiPullbackIso_comp_base f g]
  exact toPolarizedLineBundleIso_comp_key f g (toPolarizedNaturality f g) (toPolarizedCompLaw f g)

end CompLaw

section Functor

variable (B : BigFppfSite.{u})

/-- **`Θ` preserves composition.** -/
theorem toPolarizedMap_comp {X Y Z : RepresentedPolarized B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toPolarizedMap B (f ≫ g) = toPolarizedMap B f ≫ toPolarizedMap B g := by
  show toPolarizedMap B (f ≫ g) = PolarizedFamily.comp (toPolarizedMap B f) (toPolarizedMap B g)
  refine PolarizedFamily.Hom.ext ((BigFppfOver.forget B integerBase (hZ B)).map_comp _ _)
    ((BigFppfOver.toScheme B integerBase (hZ B)).map_comp _ _) (heq_of_eq (Iso.ext ?_))
  simp only [PolarizedFamily.comp, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
  exact toPolarizedLineBundleIso_comp_hom f g

/-- **`Θ` preserves identities.** -/
theorem toPolarizedMap_id (X : RepresentedPolarized B) : toPolarizedMap B (𝟙 X) = 𝟙 _ :=
  PolarizedFamily.eq_id_of_comp_self _ ((BigFppfOver.forget B integerBase (hZ B)).map_id _)
    ((BigFppfOver.toScheme B integerBase (hZ B)).map_id _)
    ((toPolarizedMap_comp B (𝟙 X) (𝟙 X)).symm.trans
      (congrArg (toPolarizedMap B) (Category.id_comp _)))

/-- **The comparison `Θ : RepresentedPolarized ⥤ Polarized`**: a polarized family of schemes of
the site with its polarization on the small étale site goes to the polarized family with the
restriction of the polarization to the Zariski site. -/
def toPolarized : RepresentedPolarized B ⥤ PolarizedFamily B where
  obj := toPolarizedObj B
  map := toPolarizedMap B
  map_id := toPolarizedMap_id B
  map_comp := toPolarizedMap_comp B

/-- `Θ` keeps the base of a family. -/
theorem toPolarized_comp_polarizedProjection :
    toPolarized B ⋙ polarizedProjection B =
      representedPolarizedProjection B ⋙ BigFppfOver.forget B integerBase (hZ B) :=
  rfl

/-- **`Θ` as a functor over the site**, to `Polarized` read over `Spec(ℤ)`. -/
def toPolarizedBased : BasedCategory.ofFunctor (representedPolarizedProjection B) ⥤ᵇ
    BasedCategory.ofFunctor (polarizedProjection B ⋙ schemeOverIntegers B) where
  toFunctor := toPolarized B
  w := by
    change (toPolarized B ⋙ polarizedProjection B) ⋙ schemeOverIntegers B = _
    rw [toPolarized_comp_polarizedProjection, Functor.assoc, forget_comp_schemeOverIntegers,
      Functor.comp_id]
    rfl

end Functor

end AlgebraicGeometry.PolarizedOverSpace

end
