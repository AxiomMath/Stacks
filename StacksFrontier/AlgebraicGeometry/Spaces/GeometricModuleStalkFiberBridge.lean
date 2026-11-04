module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChart
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm

/-!
# The fibre and the geometric module stalk, compared

The stalk of an `𝒪_X`-module at a geometric point appears in this development in two forms:
the fibre `Stacks.sheafModuleFiberOfCommRing` at the point of the small étale site, a module over
the stalk of the structure sheaf, and the geometric module stalk
`AlgebraicGeometry.Space.geometricModuleStalk`, a module over the étale local ring.  Stacks 05V5
is proved for the first (`AlgebraicGeometry.Space.modulePullbackFiberIso`) and Stacks 05VQ for
the second (`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`).  This file identifies the
two stalks additively, naturally in the module, and shows that the two base-change formulas
correspond.

## Main results

* `AlgebraicGeometry.Space.fiberStalkAddEquiv`: the additive identification.
* `AlgebraicGeometry.Space.fiberStalkAddEquiv_naturality`: it is natural.
* `AlgebraicGeometry.Space.geometricModuleStalkPullbackIso_inv_tmul`: it carries the inverse of
  Stacks 05V5 to the inverse of Stacks 05VQ on pure tensors with first factor `1`.

## References

* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.StalkPullback
open scoped ChangeOfRings

universe u

/-- Transport along an equality of ring homomorphisms of an extension of scalars is the identity
on pure tensors. The rings and the module may live in different universes, which is how it is used
below; `ModuleCat.eqToHom_extendScalars_tmul` is the same statement for `extendScalars.{u, u, u}`,
phrased through `.hom`. -/
theorem ModuleCat.eqToHom_extendScalars_apply_tmul {R : Type*} {T : Type*} [CommRing R] [CommRing T]
    {φ ψ : R →+* T} (h : φ = ψ) (M : ModuleCat R) (t : T) (m : M) :
    (eqToHom (congrArg (fun φ => (ModuleCat.extendScalars φ).obj M) h)) (t ⊗ₜ[R,φ] m) =
      t ⊗ₜ[R,ψ] m := by
  subst h
  rfl

namespace ModuleCat

/-- **The two-step base-change comparison on a pure tensor.**  This is the shape of the
base-change formula of Stacks 05VQ for geometric module stalks, stated over abstract rings so that
it can be evaluated on an element: the iso built from an identification `φ : L' ≅ A ⊗_R M'`, the
two comparisons `L ≅ L'` and `M ≅ M'`, and the ring isomorphisms carrying `R → A` to `R' → A'`,
sends `1 ⊗ eL⁻¹(φ⁻¹(1 ⊗ m'))` to `1 ⊗ (1 ⊗ eM⁻¹ m')`. -/
theorem baseChangeComparison_hom_tmul {R A : Type u} {R' A' : Type (u + 1)} [CommRing R]
    [CommRing A] [CommRing R'] [CommRing A'] (ρ : R →+* A) (ρ' : R' →+* A') (eA : A ≃+* A')
    (eR : R ≃+* R') (h : eA.toRingHom.comp ρ = ρ'.comp eR.toRingHom)
    {L L' : ModuleCat.{u} A} {M M' : ModuleCat.{u} R} (eL : L ≅ L') (eM : M ≅ M')
    (φ : L' ≅ (ModuleCat.extendScalars ρ).obj M') (m' : M') :
    ((ModuleCat.extendScalars eA.toRingHom).mapIso
          (eL ≪≫ φ ≪≫ (ModuleCat.extendScalars ρ).mapIso eM.symm) ≪≫
        ModuleCat.extendScalarsCompObjIso.{u, u, u + 1, u} ρ eA.toRingHom M ≪≫
        eqToIso (congrArg (fun ψ => (ModuleCat.extendScalars ψ).obj M) h) ≪≫
        (ModuleCat.extendScalarsCompObjIso.{u, u + 1, u + 1, u} eR.toRingHom ρ' M).symm).hom
      (ModuleCat.extendScalarsRingEquivAddEquiv eA L (eL.inv (φ.inv ((1 : A) ⊗ₜ[R, ρ] m')))) =
      (1 : A') ⊗ₜ[R', ρ'] ModuleCat.extendScalarsRingEquivAddEquiv eR M (eM.inv m') := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, eqToIso.hom, Functor.map_comp,
    Category.assoc]
  rw [ModuleCat.extendScalarsRingEquivAddEquiv_apply]
  have key : (ModuleCat.extendScalars ρ).map eM.inv
      (φ.hom (eL.hom (eL.inv (φ.inv ((1 : A) ⊗ₜ[R, ρ] m'))))) =
      (1 : A) ⊗ₜ[R, ρ] eM.inv m' := by
    rw [Iso.inv_hom_id_apply]
    erw [Iso.inv_hom_id_apply]
    rfl
  have hB : (ModuleCat.extendScalarsCompObjIso.{u, u, u + 1, u} ρ eA.toRingHom M).hom
      ((1 : A') ⊗ₜ[A, eA.toRingHom] ((1 : A) ⊗ₜ[R, ρ] eM.inv m' :
        (ModuleCat.extendScalars ρ).obj M)) =
      (1 : A') ⊗ₜ[R, eA.toRingHom.comp ρ] eM.inv m' := by
    change (eA.toRingHom (1 : A) * (1 : A')) ⊗ₜ[R, eA.toRingHom.comp ρ] eM.inv m' = _
    rw [map_one, one_mul]
  have hD : (ModuleCat.extendScalarsCompObjIso.{u, u + 1, u + 1, u} eR.toRingHom ρ' M).inv
      ((1 : A') ⊗ₜ[R, ρ'.comp eR.toRingHom] eM.inv m') =
      (1 : A') ⊗ₜ[R', ρ'] ModuleCat.extendScalarsRingEquivAddEquiv eR M (eM.inv m') := by
    rw [ModuleCat.extendScalarsRingEquivAddEquiv_apply]
    rfl
  change (ModuleCat.extendScalarsCompObjIso.{u, u + 1, u + 1, u} eR.toRingHom ρ' M).inv
        ((eqToHom (congrArg (fun ψ => (ModuleCat.extendScalars ψ).obj M) h))
          ((ModuleCat.extendScalarsCompObjIso.{u, u, u + 1, u} ρ eA.toRingHom M).hom
            ((1 : A') ⊗ₜ[A, eA.toRingHom] ((ModuleCat.extendScalars ρ).map eM.inv
              (φ.hom (eL.hom (eL.inv (φ.inv ((1 : A) ⊗ₜ[R, ρ] m')))))
              : (ModuleCat.extendScalars ρ).obj M)))) = _
  rw [key]
  exact (congrArg (fun v => (ModuleCat.extendScalarsCompObjIso.{u, u + 1, u + 1, u} eR.toRingHom ρ'
      M).inv ((eqToHom (congrArg (fun ψ => (ModuleCat.extendScalars ψ).obj M) h)) v)) hB).trans
    ((congrArg (fun v => (ModuleCat.extendScalarsCompObjIso.{u, u + 1, u + 1, u} eR.toRingHom ρ'
      M).inv v) (ModuleCat.eqToHom_extendScalars_apply_tmul h M (1 : A') (eM.inv m'))).trans hD)

end ModuleCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fibre and the geometric module stalk are the same additive group.** -/
def fiberStalkAddEquiv (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).obj F ≃+ geometricModuleStalk B S hS X x F :=
  (Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O F).symm.toAddEquiv.trans
    (geometricModuleStalkAddEquiv B S hS X x F)

/-- `AlgebraicGeometry.Space.fiberStalkAddEquiv` sends a fibre element `m` to `1 ⊗ m'`, where `m'`
is the element of the large module stalk corresponding to `m`. -/
theorem fiberStalkAddEquiv_apply (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (m : (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).obj F) :
    fiberStalkAddEquiv B S hS X x F m =
      (1 : etaleLocalRing B S hS X.1 x) ⊗ₜ[_, (pointStalkRingEquiv B S hS X x).toRingHom]
        (Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O F).symm m :=
  ModuleCat.extendScalarsRingEquivAddEquiv_apply _ _ _

/-- **The identification of the fibre with the geometric module stalk is natural.** -/
theorem fiberStalkAddEquiv_naturality (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    (m : (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).obj F) :
    fiberStalkAddEquiv B S hS X x G
        ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O).map φ m) =
      geometricModuleStalkMap B S hS X x φ (fiberStalkAddEquiv B S hS X x F m) := by
  obtain ⟨z, rfl⟩ := (Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O F).surjective m
  obtain ⟨U, ξ, s, rfl⟩ := Stacks.moduleStalkLargeGerm_jointly_surjective
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O F z
  have e1 := Stacks.moduleStalkLargeLinearEquiv_germ (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O F U ξ s
  have e2 := Stacks.moduleStalkLargeLinearEquiv_germ (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O G U ξ ((φ.val.app (op U)).hom s)
  have e3 := Stacks.toPresheafModuleFiber_naturality (etaleSitePoint B S hS X.1 x X.2) φ.val U ξ s
  have h1 : (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).map φ
        ((Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O F)
          (Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O F U ξ s)) =
      (Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O G)
        (Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O G U ξ ((φ.val.app (op U)).hom s)) :=
    ((congrArg (fun w => (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).map φ w) e1).trans e3).trans e2.symm
  refine (congrArg (fiberStalkAddEquiv B S hS X x G) h1).trans ?_
  refine (congrArg (geometricModuleStalkAddEquiv B S hS X x G)
    (LinearEquiv.symm_apply_apply _ _)).trans ?_
  refine (congrArg (geometricModuleStalkAddEquiv B S hS X x G)
    (Stacks.moduleStalkLargeAddMap_germ (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O φ U ξ s).symm).trans ?_
  refine (congrArg (fun w => geometricModuleStalkAddEquiv B S hS X x G
    (Stacks.moduleStalkLargeAddMap (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O φ w))
    ((geometricModuleStalkAddEquiv B S hS X x F).symm_apply_apply _).symm).trans ?_
  exact congrArg (fun w => geometricModuleStalkMap B S hS X x φ
    (geometricModuleStalkAddEquiv B S hS X x F w)) (LinearEquiv.symm_apply_apply _ _).symm

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)
  (G : Modules.{u, u} B S hS Y.1 Y.2)

/-- The base-change isomorphism of geometric module stalks, in the shape of
`ModuleCat.baseChangeComparison_hom_tmul`. -/
theorem geometricModuleStalkPullbackIso_eq :
    geometricModuleStalkPullbackIso B S hS f x G =
      (ModuleCat.extendScalars (pointStalkRingEquiv B S hS X x).toRingHom).mapIso
          (Stacks.moduleStalkLargeIso (etaleSitePoint B S hS X.1 x X.2)
              (smallEtaleRingedTopos B S hS X).O ((modulePullback B S hS f).obj G) ≪≫
            (stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS f)
              (etaleSitePoint B S hS X.1 x X.2)
              (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
              (smallEtaleInverseImageFiberIso B S hS f x)).app G ≪≫
            (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f x)).mapIso
              (Stacks.moduleStalkLargeIso
                (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
                (smallEtaleRingedTopos B S hS Y).O G).symm) ≪≫
        ModuleCat.extendScalarsCompObjIso.{u, u, u + 1, u}
          (smallEtaleStalkPullbackRingMap B S hS f x) (pointStalkRingEquiv B S hS X x).toRingHom
          (Stacks.moduleStalkLarge (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
            (smallEtaleRingedTopos B S hS Y).O G) ≪≫
        eqToIso (congrArg (fun φ => (ModuleCat.extendScalars φ).obj
          (Stacks.moduleStalkLarge (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
            (smallEtaleRingedTopos B S hS Y).O G))
          (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS f x)) ≪≫
        (ModuleCat.extendScalarsCompObjIso.{u, u + 1, u + 1, u}
          (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom
          (etaleLocalRingMap X.2 f.hom x)
          (Stacks.moduleStalkLarge (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
            (smallEtaleRingedTopos B S hS Y).O G)).symm := rfl

/-- **Stacks 05V5 and Stacks 05VQ correspond.**  The base-change isomorphism of geometric module
stalks carries the image of `(f^*G)_x̄ ∋ e⁻¹(1 ⊗ m)` — the inverse of the base-change isomorphism
of fibres applied to `1 ⊗ m` — to `1 ⊗ m`, both read through
`AlgebraicGeometry.Space.fiberStalkAddEquiv`. -/
theorem geometricModuleStalkPullbackIso_hom_fiberStalkAddEquiv
    (m : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleRingedTopos B S hS Y).O).obj G) :
    (geometricModuleStalkPullbackIso B S hS f x G).hom
        (ModuleCat.extendScalarsRingEquivAddEquiv (pointStalkRingEquiv B S hS X x) _
          ((Stacks.moduleStalkLargeIso (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O ((modulePullback B S hS f).obj G)).inv
          (((stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS f)
            (etaleSitePoint B S hS X.1 x X.2)
            (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
            (smallEtaleInverseImageFiberIso B S hS f x)).app G).inv
            ((1 : Stacks.ringFiber (etaleSitePoint B S hS X.1 x X.2)
              (smallEtaleRingedTopos B S hS X).O.obj) ⊗ₜ[_,
                smallEtaleStalkPullbackRingMap B S hS f x] m)))) =
      (1 : etaleLocalRing B S hS X.1 x) ⊗ₜ[_, etaleLocalRingMap X.2 f.hom x]
        ModuleCat.extendScalarsRingEquivAddEquiv
          (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)) _
          ((Stacks.moduleStalkLargeIso
            (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
            (smallEtaleRingedTopos B S hS Y).O G).inv m) := by
  have key := ModuleCat.baseChangeComparison_hom_tmul (smallEtaleStalkPullbackRingMap B S hS f x)
    (etaleLocalRingMap X.2 f.hom x) (pointStalkRingEquiv B S hS X x)
    (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x))
    (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS f x)
    (Stacks.moduleStalkLargeIso (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O ((modulePullback B S hS f).obj G))
    (Stacks.moduleStalkLargeIso (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
      (smallEtaleRingedTopos B S hS Y).O G)
    ((stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS f)
      (etaleSitePoint B S hS X.1 x X.2)
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
      (smallEtaleInverseImageFiberIso B S hS f x)).app G) m
  rw [geometricModuleStalkPullbackIso_eq]
  exact key

/-- **Stacks 05V5 and Stacks 05VQ correspond**, inverse form. -/
theorem geometricModuleStalkPullbackIso_inv_tmul'
    (m : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleRingedTopos B S hS Y).O).obj G) :
    (geometricModuleStalkPullbackIso B S hS f x G).inv
        ((1 : etaleLocalRing B S hS X.1 x) ⊗ₜ[_, etaleLocalRingMap X.2 f.hom x]
          ModuleCat.extendScalarsRingEquivAddEquiv
            (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)) _
            ((Stacks.moduleStalkLargeIso
              (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
              (smallEtaleRingedTopos B S hS Y).O G).inv m)) =
      ModuleCat.extendScalarsRingEquivAddEquiv (pointStalkRingEquiv B S hS X x) _
          ((Stacks.moduleStalkLargeIso (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O ((modulePullback B S hS f).obj G)).inv
          (((stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS f)
            (etaleSitePoint B S hS X.1 x X.2)
            (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
            (smallEtaleInverseImageFiberIso B S hS f x)).app G).inv
            ((1 : Stacks.ringFiber (etaleSitePoint B S hS X.1 x X.2)
              (smallEtaleRingedTopos B S hS X).O.obj) ⊗ₜ[_,
                smallEtaleStalkPullbackRingMap B S hS f x] m))) :=
  (congrArg (geometricModuleStalkPullbackIso B S hS f x G).inv
    (geometricModuleStalkPullbackIso_hom_fiberStalkAddEquiv B S hS f x G m)).symm.trans
    (Iso.hom_inv_id_apply (geometricModuleStalkPullbackIso B S hS f x G) _)

/-- The component at `G` of the inverse of `AlgebraicGeometry.Space.modulePullbackFiberIso` is the
inverse of the fibre comparison `stalkFunctorIso` of the inverse image of modules at `G`. -/
theorem modulePullbackFiberIso_inv_app :
    (modulePullbackFiberIso B S hS f x).inv.app G =
      ((stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS f)
        (etaleSitePoint B S hS X.1 x X.2)
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleInverseImageFiberIso B S hS f x)).app G).inv := rfl

/-- `AlgebraicGeometry.Space.fiberStalkAddEquiv` is the inverse of the large module stalk
isomorphism followed by extension of scalars along the stalk ring equivalence. -/
theorem fiberStalkAddEquiv_eq (F : Modules.{u, u} B S hS X.1 X.2)
    (m : (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).obj F) :
    fiberStalkAddEquiv B S hS X x F m =
      ModuleCat.extendScalarsRingEquivAddEquiv (pointStalkRingEquiv B S hS X x) _
        ((Stacks.moduleStalkLargeIso (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O F).inv m) := rfl

/-- `AlgebraicGeometry.Space.fiberStalkAddEquiv_eq` under `1 ⊗ -`, base changed along the map of
étale local rings. -/
theorem tmul_fiberStalkAddEquiv_eq
    (m : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleRingedTopos B S hS Y).O).obj G) :
    ((1 : etaleLocalRing B S hS X.1 x) ⊗ₜ[_, etaleLocalRingMap X.2 f.hom x]
          fiberStalkAddEquiv B S hS Y (geometricPointMap f.hom x) G m :
        (ModuleCat.extendScalars (etaleLocalRingMap X.2 f.hom x)).obj
          (geometricModuleStalk B S hS Y (geometricPointMap f.hom x) G)) =
      (1 : etaleLocalRing B S hS X.1 x) ⊗ₜ[_, etaleLocalRingMap X.2 f.hom x]
        ModuleCat.extendScalarsRingEquivAddEquiv
          (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)) _
          ((Stacks.moduleStalkLargeIso
            (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
            (smallEtaleRingedTopos B S hS Y).O G).inv m) := rfl

/-- **Stacks 05V5 and Stacks 05VQ correspond**, inverse form, through
`AlgebraicGeometry.Space.fiberStalkAddEquiv`. -/
theorem geometricModuleStalkPullbackIso_inv_tmul
    (m : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleRingedTopos B S hS Y).O).obj G) :
    (geometricModuleStalkPullbackIso B S hS f x G).inv
        ((1 : etaleLocalRing B S hS X.1 x) ⊗ₜ[_, etaleLocalRingMap X.2 f.hom x]
          fiberStalkAddEquiv B S hS Y (geometricPointMap f.hom x) G m) =
      fiberStalkAddEquiv B S hS X x ((modulePullback B S hS f).obj G)
        ((modulePullbackFiberIso B S hS f x).inv.app G
          ((1 : Stacks.ringFiber (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O.obj) ⊗ₜ[_, smallEtaleStalkPullbackRingMap B S hS f x]
              m)) := by
  rw [tmul_fiberStalkAddEquiv_eq, fiberStalkAddEquiv_eq, modulePullbackFiberIso_inv_app]
  exact geometricModuleStalkPullbackIso_inv_tmul' B S hS f x G m

end AlgebraicGeometry.Space

end
