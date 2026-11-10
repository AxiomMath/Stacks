module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Pullback of a free module of finite rank

The pullback of the free module of rank `n` on a scheme along a morphism of schemes is
canonically the free module of rank `n` on the source, and this identification is
compatible with identities and composition.

## Main definitions

* `AlgebraicGeometry.Grassmannian.pullbackFreeIso`: the identification of the pullback of
  a finite-rank free module with the free module of the same rank.

## Main results

* `AlgebraicGeometry.Grassmannian.pullbackFreeIso_id`: the identification for an identity
  morphism is the one coming from `Scheme.Modules.pullbackId`.
* `AlgebraicGeometry.Grassmannian.pullbackFreeIso_comp_inv`: the identifications for two
  composable morphisms compose to the one for the composite.

## Implementation notes

Both compatibilities are checked on the coproduct cofan of the free module, so each
reduces to a statement about the canonical map `SheafOfModules.pullbackObjUnitToUnit`
out of the pullback of the unit module. For the identity that map is the component of
`Scheme.Modules.pullbackId`, and for a composite the corresponding square commutes; both
are obtained by transporting the defining adjunction isomorphism rather than by
rewriting across it.

## References

* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Grassmannian

open Limits TopologicalSpace

/-- The canonical identification of the pullback of a finite-rank free module
with the free module of the same rank. -/
public noncomputable def pullbackFreeIso {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    (Scheme.Modules.pullback f).obj
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) ≅
      SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin n)) := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  exact SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (ULift.{u} (Fin n))

/-- On the `i`-th summand of the free module, `pullbackFreeIso` is the canonical map out of
the pullback of the unit module. -/
public theorem pullback_map_ιFree_comp_pullbackFreeIso_hom {S T : Scheme.{u}} (f : T ⟶ S)
    (n : ℕ) [(SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint]
    (i : ULift.{u} (Fin n)) :
    (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) ≫
        (pullbackFreeIso f n).hom =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
        SheafOfModules.ιFree i := by
  let : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  change (SheafOfModules.pullback f.toRingCatSheafHom).map (SheafOfModules.ιFree i) ≫
      (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom
        (ULift.{u} (Fin n))).hom = _
  exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
    (φ := f.toRingCatSheafHom) (i := i)

/-- The adjunction isomorphism sends the canonical map out of the pullback of the unit module
to the canonical map into the pushforward of the unit module. -/
private theorem homEquiv_pullbackObjUnitToUnit {S T : Scheme.{u}} (f : T ⟶ S)
    [(SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint] :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (φ := f.toRingCatSheafHom)

/-- The adjoint of the composite of the two canonical maps out of pullbacks of the unit
module. -/
private theorem pullbackUnitComp_left {S T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T)
    [(SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint]
    [(SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint] :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction g)).homEquiv
        (SheafOfModules.unit (R := S.ringCatSheaf))
        (SheafOfModules.unit (R := U.ringCatSheaf)))
        ((Scheme.Modules.pullback g).map
            (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
          SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) := by
  let adjF := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjG := Scheme.Modules.pullbackPushforwardAdjunction g
  have e1 : (adjG.homEquiv ((Scheme.Modules.pullback f).obj
          (SheafOfModules.unit (R := S.ringCatSheaf)))
        (SheafOfModules.unit (R := U.ringCatSheaf)))
        ((Scheme.Modules.pullback g).map
            (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
          SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
        SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    (adjG.homEquiv_naturality_left _ _).trans
      (congrArg (fun m ↦ SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫ m)
        (homEquiv_pullbackObjUnitToUnit g))
  have e2 : (adjF.homEquiv (SheafOfModules.unit (R := S.ringCatSheaf))
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit (R := U.ringCatSheaf))))
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
          SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) :=
    (adjF.homEquiv_naturality_right _ _).trans
      (congrArg
        (fun m ↦ m ≫ (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom))
        (homEquiv_pullbackObjUnitToUnit f))
  exact (congrArg (adjF.homEquiv _ _) e1).trans e2

/-- The adjoint of the canonical map out of the pullback of the unit module along a
composite, precomposed with the comparison of iterated pullbacks. -/
private theorem pullbackUnitComp_right {S T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T)
    [(SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint]
    [(SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint]
    [(SheafOfModules.pushforward.{u} (g ≫ f).toRingCatSheafHom).IsRightAdjoint] :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction g)).homEquiv
        (SheafOfModules.unit (R := S.ringCatSheaf))
        (SheafOfModules.unit (R := U.ringCatSheaf)))
        ((Scheme.Modules.pullbackComp g f).hom.app
            (SheafOfModules.unit (R := S.ringCatSheaf)) ≫
          SheafOfModules.pullbackObjUnitToUnit (g ≫ f).toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) := by
  let adjComp := (Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.pullbackPushforwardAdjunction g)
  let adjH := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)
  let beta := (Scheme.Modules.pullbackComp g f).hom
  let compPF := Scheme.Modules.pushforwardComp g f
  have hα : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp g f).hom.app
          (SheafOfModules.unit (R := U.ringCatSheaf)) =
      SheafOfModules.unitToPushforwardObjUnit (g ≫ f).toRingCatSheafHom := by
    ext V
    rfl
  have hmate : (conjugateEquiv adjH adjComp beta) = compPF.inv := by
    apply (cancel_mono compPF.hom).1
    calc
      (conjugateEquiv adjH adjComp beta) ≫ compPF.hom = 𝟙 _ := by
        rw [← Scheme.Modules.conjugateEquiv_pullbackComp_inv g f]
        exact conjugateEquiv_comm adjH adjComp (by simp [beta])
      _ = compPF.inv ≫ compPF.hom := by simp [compPF]
  have htransport := Stacks.CategoryTheory.homEquiv_conjugate' adjH adjComp beta
    (X := SheafOfModules.unit (R := S.ringCatSheaf))
    (Y := SheafOfModules.unit (R := U.ringCatSheaf))
    (SheafOfModules.pullbackObjUnitToUnit (g ≫ f).toRingCatSheafHom)
  rw [homEquiv_pullbackObjUnitToUnit (g ≫ f), hmate] at htransport
  have hlast : SheafOfModules.unitToPushforwardObjUnit (g ≫ f).toRingCatSheafHom ≫
      compPF.inv.app (SheafOfModules.unit (R := U.ringCatSheaf)) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) := by
    rw [← hα]
    cat_disch
  exact htransport.trans hlast

/-- The canonical maps out of the pullbacks of the unit module are compatible with the
comparison of iterated pullbacks. -/
private theorem pullbackUnitComp {S T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T)
    [(SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint]
    [(SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint]
    [(SheafOfModules.pushforward.{u} (g ≫ f).toRingCatSheafHom).IsRightAdjoint] :
    (Scheme.Modules.pullback g).map
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
      SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom =
    (Scheme.Modules.pullbackComp g f).hom.app
        (SheafOfModules.unit (R := S.ringCatSheaf)) ≫
      SheafOfModules.pullbackObjUnitToUnit (g ≫ f).toRingCatSheafHom :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.pullbackPushforwardAdjunction g)).homEquiv _ _).injective
    ((pullbackUnitComp_left f g).trans (pullbackUnitComp_right f g).symm)

/-- The canonical map out of the pullback of the unit module along an identity is the
corresponding component of `Scheme.Modules.pullbackId`. -/
private theorem pullbackObjUnitToUnit_id {S : Scheme.{u}}
    [(SheafOfModules.pushforward.{u} (𝟙 S : S ⟶ S).toRingCatSheafHom).IsRightAdjoint] :
    SheafOfModules.pullbackObjUnitToUnit (𝟙 S : S ⟶ S).toRingCatSheafHom =
      (Scheme.Modules.pullbackId S).hom.app
        (SheafOfModules.unit (R := S.ringCatSheaf)) := by
  have hpush : SheafOfModules.unitToPushforwardObjUnit (𝟙 S : S ⟶ S).toRingCatSheafHom =
      (Scheme.Modules.pushforwardId S).inv.app
        (SheafOfModules.unit (R := S.ringCatSheaf)) := by
    ext : 3
    rfl
  exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit
        (φ := (𝟙 S : S ⟶ S).toRingCatSheafHom)).symm.trans
      (((congrArg
          ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S : S ⟶ S)).homEquiv
            (SheafOfModules.unit (R := S.ringCatSheaf))
            (SheafOfModules.unit (R := S.ringCatSheaf))).symm hpush).trans
        (Adjunction.homEquiv_symm_apply
          (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S : S ⟶ S))
          (SheafOfModules.unit (R := S.ringCatSheaf))
          (SheafOfModules.unit (R := S.ringCatSheaf))
          ((Scheme.Modules.pushforwardId S).inv.app
            (SheafOfModules.unit (R := S.ringCatSheaf))))).trans
        (Adjunction.leftAdjointIdIso_hom_app
          (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S : S ⟶ S))
          (Scheme.Modules.pushforwardId S)
          (SheafOfModules.unit (R := S.ringCatSheaf))).symm)

/-- The identification of the pullback of a free module along an identity is the one
coming from `Scheme.Modules.pullbackId`. -/
public theorem pullbackFreeIso_id {S : Scheme.{u}} (n : ℕ) :
    pullbackFreeIso (𝟙 S) n =
      (Scheme.Modules.pullbackId S).app
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) := by
  let f : S ⟶ S := 𝟙 S
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact Iso.ext <| Cofan.IsColimit.hom_ext
      (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback (𝟙 S)) _ _
        (SheafOfModules.isColimitFreeCofan (R := S.ringCatSheaf)
          (ULift.{u} (Fin n))))
      (pullbackFreeIso (𝟙 S) n).hom
      ((Scheme.Modules.pullbackId S).hom.app
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))))
      (fun i ↦ by
        have h₂ : SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
            SheafOfModules.ιFree i =
          (Scheme.Modules.pullbackId S).hom.app
            (SheafOfModules.unit (R := S.ringCatSheaf)) ≫ SheafOfModules.ιFree i :=
          congrArg (fun m ↦ m ≫ SheafOfModules.ιFree i) pullbackObjUnitToUnit_id
        exact (pullback_map_ιFree_comp_pullbackFreeIso_hom f n i).trans
          (h₂.trans ((Scheme.Modules.pullbackId S).hom.naturality
            (SheafOfModules.ιFree i)).symm))

/-- The left-hand side of `pullbackFreeIso_comp`, evaluated on the `i`-th summand. -/
private theorem pullbackFreeIso_comp_left {S T U : Scheme.{u}}
    (f : T ⟶ S) (g : U ⟶ T) (n : ℕ)
    [(SheafOfModules.pushforward.{u} (g ≫ f).toRingCatSheafHom).IsRightAdjoint]
    (i : ULift.{u} (Fin n)) :
    ((Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
        (Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) ≫
        (pullbackFreeIso (g ≫ f) n).hom =
      ((Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.unit (R := S.ringCatSheaf)) ≫
        SheafOfModules.pullbackObjUnitToUnit (g ≫ f).toRingCatSheafHom) ≫
        SheafOfModules.ιFree i := by
  have hNat' :
      (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
        (Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) =
      (Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.unit (R := S.ringCatSheaf)) ≫
        (Scheme.Modules.pullback (g ≫ f)).map (SheafOfModules.ιFree i) :=
    (Scheme.Modules.pullbackComp g f).hom.naturality (SheafOfModules.ιFree i)
  calc
    ((Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
        (Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) ≫
          (pullbackFreeIso (g ≫ f) n).hom =
      ((Scheme.Modules.pullbackComp g f).hom.app
            (SheafOfModules.unit (R := S.ringCatSheaf)) ≫
          (Scheme.Modules.pullback (g ≫ f)).map (SheafOfModules.ιFree i)) ≫
            (pullbackFreeIso (g ≫ f) n).hom :=
        congrArg (fun m ↦ m ≫ (pullbackFreeIso (g ≫ f) n).hom) hNat'
    _ = (Scheme.Modules.pullbackComp g f).hom.app
            (SheafOfModules.unit (R := S.ringCatSheaf)) ≫
          ((Scheme.Modules.pullback (g ≫ f)).map (SheafOfModules.ιFree i) ≫
            (pullbackFreeIso (g ≫ f) n).hom) := by cat_disch
    _ = (Scheme.Modules.pullbackComp g f).hom.app
            (SheafOfModules.unit (R := S.ringCatSheaf)) ≫
          (SheafOfModules.pullbackObjUnitToUnit (g ≫ f).toRingCatSheafHom ≫
            SheafOfModules.ιFree i) :=
        congrArg _ (pullback_map_ιFree_comp_pullbackFreeIso_hom (g ≫ f) n i)
    _ = ((Scheme.Modules.pullbackComp g f).hom.app
            (SheafOfModules.unit (R := S.ringCatSheaf)) ≫
          SheafOfModules.pullbackObjUnitToUnit (g ≫ f).toRingCatSheafHom) ≫
            SheafOfModules.ιFree i := by cat_disch

/-- The right-hand side of `pullbackFreeIso_comp`, evaluated on the `i`-th summand. -/
private theorem pullbackFreeIso_comp_right {S T U : Scheme.{u}}
    (f : T ⟶ S) (g : U ⟶ T) (n : ℕ)
    [(SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint]
    [(SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint]
    [(SheafOfModules.pushforward.{u} (g ≫ f).toRingCatSheafHom).IsRightAdjoint]
    (i : ULift.{u} (Fin n)) :
    (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
        ((Scheme.Modules.pullback g).map (pullbackFreeIso f n).hom ≫
          (pullbackFreeIso g n).hom) =
      ((Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.unit (R := S.ringCatSheaf)) ≫
        SheafOfModules.pullbackObjUnitToUnit (g ≫ f).toRingCatSheafHom) ≫
        SheafOfModules.ιFree i := by
  have hmap₁ := congrArg (fun m ↦ m ≫ (pullbackFreeIso g n).hom)
    ((Scheme.Modules.pullback g).map_comp
      ((Scheme.Modules.pullback f).map (SheafOfModules.ιFree i))
      (pullbackFreeIso f n).hom).symm
  have hmap₂ := congrArg
    (fun m ↦ (Scheme.Modules.pullback g).map m ≫ (pullbackFreeIso g n).hom)
    (pullback_map_ιFree_comp_pullbackFreeIso_hom f n i)
  have hmap₃ := congrArg (fun m ↦ m ≫ (pullbackFreeIso g n).hom)
    ((Scheme.Modules.pullback g).map_comp
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
      (SheafOfModules.ιFree i))
  have hmap₀ :
      (Scheme.Modules.pullback g).map
            ((Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
          ((Scheme.Modules.pullback g).map (pullbackFreeIso f n).hom ≫
            (pullbackFreeIso g n).hom) =
        ((Scheme.Modules.pullback g).map
              ((Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
            (Scheme.Modules.pullback g).map (pullbackFreeIso f n).hom) ≫
          (pullbackFreeIso g n).hom := by cat_disch
  have hmap₄ :
      ((Scheme.Modules.pullback g).map
              (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
            (Scheme.Modules.pullback g).map (SheafOfModules.ιFree i)) ≫
          (pullbackFreeIso g n).hom =
        ((Scheme.Modules.pullback g).map
              (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
            SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
          SheafOfModules.ιFree i := by
    rw [Category.assoc, pullback_map_ιFree_comp_pullbackFreeIso_hom g n i]
    cat_disch
  have hmap₅ := congrArg (fun m ↦ m ≫ SheafOfModules.ιFree i) (pullbackUnitComp f g)
  exact hmap₀.trans (hmap₁.trans (hmap₂.trans (hmap₃.trans (hmap₄.trans hmap₅))))

/-- The identifications of the pullbacks of a free module along two composable morphisms
compose to the identification along the composite. -/
public theorem pullbackFreeIso_comp {S T U : Scheme.{u}}
    (f : T ⟶ S) (g : U ⟶ T) (n : ℕ) :
    (Scheme.Modules.pullbackComp g f).hom.app
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) ≫
      (pullbackFreeIso (g ≫ f) n).hom =
    (Scheme.Modules.pullback g).map (pullbackFreeIso f n).hom ≫
      (pullbackFreeIso g n).hom := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  let : (SheafOfModules.pushforward (g ≫ f).toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).isRightAdjoint
  let cFree := SheafOfModules.isColimitFreeCofan (R := S.ringCatSheaf)
    (ULift.{u} (Fin n))
  let cF := isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _ cFree
  let cGF := isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback g) _ _ cF
  exact Cofan.IsColimit.hom_ext cGF _ _ (fun i ↦
    (pullbackFreeIso_comp_left f g n i).trans
      (pullbackFreeIso_comp_right f g n i).symm)

/-- The inverse form of `pullbackFreeIso_comp`. -/
public theorem pullbackFreeIso_comp_inv {S T U : Scheme.{u}}
    (f : T ⟶ S) (g : U ⟶ T) (n : ℕ) :
    (pullbackFreeIso g n).inv ≫
      (Scheme.Modules.pullback g).map (pullbackFreeIso f n).inv ≫
      (Scheme.Modules.pullbackComp g f).hom.app
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) =
    (pullbackFreeIso (g ≫ f) n).inv := by
  apply (cancel_mono (pullbackFreeIso (g ≫ f) n).hom).1
  calc
    ((pullbackFreeIso g n).inv ≫
        (Scheme.Modules.pullback g).map (pullbackFreeIso f n).inv ≫
        (Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) ≫
        (pullbackFreeIso (g ≫ f) n).hom =
      (pullbackFreeIso g n).inv ≫
        (Scheme.Modules.pullback g).map (pullbackFreeIso f n).inv ≫
        ((Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) ≫
          (pullbackFreeIso (g ≫ f) n).hom) := by cat_disch
    _ = (pullbackFreeIso g n).inv ≫
          (Scheme.Modules.pullback g).map (pullbackFreeIso f n).inv ≫
          ((Scheme.Modules.pullback g).map (pullbackFreeIso f n).hom ≫
            (pullbackFreeIso g n).hom) := by rw [pullbackFreeIso_comp f g n]
    _ = 𝟙 _ := by
          calc
            _ = (pullbackFreeIso g n).inv ≫
                  (((Scheme.Modules.pullback g).map (pullbackFreeIso f n).inv ≫
                    (Scheme.Modules.pullback g).map (pullbackFreeIso f n).hom) ≫
                    (pullbackFreeIso g n).hom) := by cat_disch
            _ = (pullbackFreeIso g n).inv ≫
                  ((Scheme.Modules.pullback g).map
                    ((pullbackFreeIso f n).inv ≫ (pullbackFreeIso f n).hom) ≫
                    (pullbackFreeIso g n).hom) := by
                    rw [← (Scheme.Modules.pullback g).map_comp]
            _ = 𝟙 _ := by simp
    _ = (pullbackFreeIso (g ≫ f) n).inv ≫
          (pullbackFreeIso (g ≫ f) n).hom := by simp

end AlgebraicGeometry.Grassmannian

end
