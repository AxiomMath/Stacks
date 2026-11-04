module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Normalization
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The length of the normalization quotient stalk is the delta invariant

Let `X` be a reduced scheme whose quasi-compact opens have finitely many irreducible components
and let `ν : X^ν ⟶ X` be its normalization.  The stalk at `x` of the cokernel
`ν_* 𝒪_{X^ν} / 𝒪_X` is the quotient of the normalization stalk `A' = (ν_* 𝒪_{X^ν})_x` by the
image of the local ring `A = 𝒪_{X,x}`, because taking stalks is exact.  By Tag 0C3B(2) that
quotient is the one defining the delta invariant of `A`, so the stalk has finite length equal to
the delta invariant.  This is the quantitative half of
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)(2).

## Main results

* `normalizationQuotientStalk_linearEquiv_quotient_range`: the quotient stalk is `A' / A`.
* `length_normalizationQuotientStalk`: its length is the delta invariant of `A`.
* `isFiniteLength_normalizationQuotientStalk`: on a one-dimensional Nagata scheme that length is
  finite.

## Implementation notes

The stalk functor on sheaves of modules used here is
`AlgebraicGeometry.SheafOfModules.stalkFunctor` (Tag 01AH), which lands in modules over the
`RingCat`-valued stalk of the structure sheaf; `SemilinearStalk.commStalkRingEquiv` transports it
to modules over `𝒪_{X,x}`, and `SemilinearStalk.comm_smul_eq` says the two scalar actions agree,
which is what makes `stalkModuleIso` — the comparison with `OXModule.stalk`, over which
`normalizationQuotientStalk` is defined — the identity on underlying types.

Exactness is only needed for cokernels, so what is extracted from Tag 01AH is preservation of
colimits over `WalkingParallelPair`; `preservesCokernelIso` turns that into the comparison
`cokernel (F.map φ) ≅ F.obj (cokernel φ)` for the module map `φ : 𝒪_X ⟶ ν_* 𝒪_{X^ν}`.  The
source and target of `F.map φ` are identified with `A` and `A'` by
`LocallyFreeRank.unitStalkLEquiv`, and under those identifications `F.map φ` is the structure
map `A ⟶ A'`: it sends the germ of `1` to the germ of `1`, and both sides are `A`-linear.

Neither the dimension of `X` nor closedness of the point is used for the identification or for
the length computation; the dimension hypothesis enters only in the finiteness statement, and
there through the dimension of the local ring at `x`.  Points whose local ring is a field are
covered: there the local ring is already integrally closed, so the quotient vanishes.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0C3T](https://stacks.math.columbia.edu/tag/0C3T)
* [Stacks Project, Tag 0C3S](https://stacks.math.columbia.edu/tag/0C3S)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotient

open Stacks.NormalizationStalkAmbient

/-- The component of the `RingCat`-valued sheaf map attached to a morphism of schemes is the
component of its `CommRingCat`-valued one. -/
private theorem schemeHom_ringCat_component {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (s : Y.presheaf.obj (op U)) :
    ((Scheme.Hom.toRingCatSheafHom f).hom.app (op U)).hom s =
      ((forget₂ CommRingCat RingCat).map (f.c.app (op U))) s := rfl

/-- `LocallyFreeRank.unitStalkLEquiv` matches the germ maps: the stalk of the unit module is the
ring stalk, by the identity on germs. -/
private theorem unitStalkLEquiv_germ {X : TopCat.{u}} (R : TopCat.Presheaf RingCat.{u} X) (x : X)
    (U : Opens X) (hx : x ∈ U)
    (s : ToType ((PresheafOfModules.unit R).presheaf.obj (op U))) :
    LocallyFreeRank.unitStalkLEquiv R x
        (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x hx s) =
      R.germ U x hx s := by
  let pIso : (forget₂ RingCat.{u} AddCommGrpCat.{u}).obj (R.stalk x) ≅
      TopCat.Presheaf.stalk (PresheafOfModules.unit R).presheaf x :=
    preservesColimitIso (forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R)
  let addE : ToType (TopCat.Presheaf.stalk (PresheafOfModules.unit R).presheaf x) ≃+
      ToType (R.stalk x) := pIso.symm.addCommGroupIsoToAddEquiv
  show addE (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x hx s) = _
  have h := ι_preservesColimitIso_inv (forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R) (op ⟨U, hx⟩)
  let s' : ToType (R.obj (op U)) := s
  have h' := congrArg (fun f => (ConcreteCategory.hom f) s') h
  change (ConcreteCategory.hom pIso.inv)
      ((ConcreteCategory.hom (colimit.ι (((OpenNhds.inclusion x).op ⋙ R) ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u}) (op ⟨U, hx⟩))) s') =
    (ConcreteCategory.hom ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map
      (colimit.ι ((OpenNhds.inclusion x).op ⋙ R) (op ⟨U, hx⟩)))) s' at h'
  exact h'

/-- The identification of the unit module stalk with the local ring matches the germ maps. -/
private theorem commStalkRingEquiv_unitStalkLEquiv_germ {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (x : X) (U : Opens X) (hx : x ∈ U)
    (s : ToType ((PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf.obj
      (op U))) :
    SemilinearStalk.commStalkRingEquiv R x (LocallyFreeRank.unitStalkLEquiv
      (R ⋙ forget₂ CommRingCat RingCat) x (TopCat.Presheaf.germ (PresheafOfModules.unit
        (R ⋙ forget₂ CommRingCat RingCat)).presheaf U x hx s)) = R.germ U x hx s := by
  rw [unitStalkLEquiv_germ]
  exact SemilinearStalk.commStalkRingEquiv_germ R x U hx s

/-- The stalk of a sheaf of rings, as an additive group, is the additive stalk. -/
private def commStalkAddEquiv {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X) (x : X) :
    ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x) ≃+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (R ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) x) :=
  (preservesColimitIso
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R)).addCommGroupIsoToAddEquiv

/-- `commStalkAddEquiv` matches the germ maps. -/
private theorem commStalkAddEquiv_germ {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (x : X) (U : Opens X) (hx : x ∈ U)
    (r : R.obj (op U)) :
    commStalkAddEquiv R x (R.germ U x hx r) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (R ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) U x hx r := by
  let pIso : (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}).obj
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x) ≅
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (R ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) x :=
    preservesColimitIso
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R)
  have h := ι_preservesColimitIso_inv
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R) (op ⟨U, hx⟩)
  rw [← show pIso = preservesColimitIso
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R) from rfl] at h
  have h' := congrArg (fun φ => (ConcreteCategory.hom φ) r) h
  change (ConcreteCategory.hom pIso.inv)
      ((ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (R ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) U x hx)) r) =
      (ConcreteCategory.hom (R.germ U x hx)) r at h'
  show (ConcreteCategory.hom pIso.hom) ((ConcreteCategory.hom (R.germ U x hx)) r) =
    (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      (R ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) U x hx)) r
  simpa using congrArg (ConcreteCategory.hom pIso.hom) h'.symm

/-- Taking the stalk at `x` of a sheaf of `𝒪_X`-modules, as a module over the local ring
`𝒪_{X,x}`: the Tag 01AH stalk functor followed by the restriction of scalars along
`SemilinearStalk.commStalkRingEquiv`. -/
private def stalkModuleFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor (OXModule.ringSheaf X.toRingedSpace) x ⋙
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u}
      (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm).functor

/-- `stalkModuleFunctor` preserves cokernels, since the Tag 01AH stalk functor preserves all
colimits and restriction of scalars along a ring equivalence is an equivalence. -/
private theorem stalkModuleFunctor_preservesParallelPairColimits (X : Scheme.{u}) (x : X) :
    PreservesColimitsOfShape WalkingParallelPair (stalkModuleFunctor X x) := by
  let O := OXModule.ringSheaf X.toRingedSpace
  let e := SemilinearStalk.commStalkRingEquiv X.presheaf x
  let B := TopCat.Presheaf.stalk (C := RingCat) O.obj x
  let F : SheafOfModules O ⥤ ModuleCat.{u} B :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor O x
  let E : ModuleCat.{u} B ≌ ModuleCat.{u} (X.presheaf.stalk x) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u} e.symm
  let : UnivLE.{0, u} := univLE_max
  let : PreservesColimits F :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits O x
  let : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  let : PreservesColimits E.functor := E.toAdjunction.leftAdjoint_preservesColimits
  let : PreservesColimitsOfSize.{0, 0} E.functor := preservesColimitsOfSize_shrink E.functor
  have hF : PreservesColimitsOfShape WalkingParallelPair F := inferInstance
  have hE : PreservesColimitsOfShape WalkingParallelPair E.functor := inferInstance
  show PreservesColimitsOfShape WalkingParallelPair (F ⋙ E.functor)
  exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ _ _

/-- The additive stalk of the unit presheaf of modules is the local ring, `𝒪_{X,x}`-linearly. -/
private def unitStalkLinearEquiv (X : Scheme.{u}) (x : X) :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.unit
          (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf x) ≃ₗ[
        ToType (X.presheaf.stalk x)] ToType (X.presheaf.stalk x) := by
  let R := X.presheaf
  let RR := R ⋙ forget₂ CommRingCat.{u} RingCat.{u}
  refine
    { toFun := fun z => SemilinearStalk.commStalkRingEquiv R x (LocallyFreeRank.unitStalkLEquiv
        RR x z)
      invFun := fun a => (LocallyFreeRank.unitStalkLEquiv RR x).symm
        ((SemilinearStalk.commStalkRingEquiv R x).symm a)
      left_inv := fun z => by
        simp only [RingEquiv.symm_apply_apply]
        exact (LocallyFreeRank.unitStalkLEquiv RR x).symm_apply_apply z
      right_inv := fun a => by
        dsimp only
        rw [(LocallyFreeRank.unitStalkLEquiv RR x).apply_symm_apply]
        exact (SemilinearStalk.commStalkRingEquiv R x).apply_symm_apply a
      map_add' := fun z w => by
        rw [map_add]
        exact (SemilinearStalk.commStalkRingEquiv R x).map_add _ _
      map_smul' := ?_ }
  intro a z
  let b : ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) RR x) :=
    (SemilinearStalk.commStalkRingEquiv R x).symm a
  have hact : a • z = b • z := by
    rw [show a = SemilinearStalk.commStalkRingEquiv R x b from
      ((SemilinearStalk.commStalkRingEquiv R x).apply_symm_apply a).symm]
    exact SemilinearStalk.comm_smul_eq R x (PresheafOfModules.unit RR) b z
  change SemilinearStalk.commStalkRingEquiv R x
    (LocallyFreeRank.unitStalkLEquiv RR x (a • z)) = _
  rw [hact, map_smul]
  change SemilinearStalk.commStalkRingEquiv R x
    (b * LocallyFreeRank.unitStalkLEquiv RR x z) = _
  rw [map_mul, show SemilinearStalk.commStalkRingEquiv R x b = a from
    (SemilinearStalk.commStalkRingEquiv R x).apply_symm_apply a]
  rfl

private def pushedUnitStalkLinearEquiv (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    let Xnorm := Scheme.normalizationScheme X hX
    let ν := Scheme.normalization X hX
    let A := X.presheaf.stalk x
    let A' := (TopCat.Presheaf.stalkFunctor CommRingCat x).obj
      ((TopCat.Sheaf.pushforward CommRingCat ν.base).obj Xnorm.sheaf).presheaf
    letI : Algebra A A' :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map ν.c).hom.toAlgebra
    (stalkModuleFunctor X x).obj
      ((SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom ν)).obj
          (SheafOfModules.unit Xnorm.ringCatSheaf)) ≃ₗ[
        A] A' := by
  classical
  dsimp only
  let Xnorm := Scheme.normalizationScheme X hX
  let ν := Scheme.normalization X hX
  let A := X.presheaf.stalk x
  let R' := ((TopCat.Sheaf.pushforward CommRingCat ν.base).obj Xnorm.sheaf).presheaf
  let A' := (TopCat.Presheaf.stalkFunctor CommRingCat x).obj R'
  letI : Algebra A A' :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map ν.c).hom.toAlgebra
  letI : CommRing (ToType A) := CommRingCat.commRing A
  letI : CommRing (ToType A') := CommRingCat.commRing A'
  let R : TopCat.Presheaf RingCat.{u} X := X.ringCatSheaf.obj
  let R'R : TopCat.Presheaf RingCat.{u} X := R' ⋙ forget₂ CommRingCat RingCat
  let B := TopCat.Presheaf.stalk (C := RingCat) R x
  let B' := TopCat.Presheaf.stalk (C := RingCat) R'R x
  let e := SemilinearStalk.commStalkRingEquiv X.presheaf x
  let e' : ToType B' ≃+* ToType A' := SemilinearStalk.commStalkRingEquiv R' x
  let F := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  let M : X.Modules :=
    (SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom ν)).obj
      (SheafOfModules.unit Xnorm.ringCatSheaf)
  let V := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x
  let N₀ : ModuleCat.{u} B := F.obj M
  letI : Module (ToType B) V := N₀.isModule
  letI : SMul (ToType B) V := N₀.isModule.toSMul
  let N := (stalkModuleFunctor X x).obj M
  letI : SMul (ToType B) ↑N := N₀.isModule.toSMul
  let u := LocallyFreeRank.unitStalkLEquiv R'R x
  let ρ := (TopCat.Presheaf.stalkFunctor RingCat x).map
    (Scheme.Hom.toRingCatSheafHom ν).hom
  let ψ := (TopCat.Presheaf.stalkFunctor CommRingCat x).map ν.c
  have hcompat (b : B) : e' (ρ b) = ψ (e b) := by
    obtain ⟨U, hxU, s, hs⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf (e b)
    let t : R.obj (op U) := s
    have hrgerm : e (R.germ U x hxU t) = X.presheaf.germ U x hxU s := by
      change SemilinearStalk.commStalkRingEquiv X.presheaf x
        (TopCat.Presheaf.germ (C := RingCat)
          (X.presheaf ⋙ forget₂ CommRingCat RingCat) U x hxU s) = _
      exact SemilinearStalk.commStalkRingEquiv_germ X.presheaf x U hxU s
    have hb : b = R.germ U x hxU t := e.injective (hrgerm.trans hs).symm
    rw [hb, TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
        (Scheme.Hom.toRingCatSheafHom ν).hom t, hrgerm,
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU ν.c s,
      schemeHom_ringCat_component ν U s]
    change (SemilinearStalk.commStalkRingEquiv R' x)
      (TopCat.Presheaf.germ (C := RingCat) (R' ⋙ forget₂ CommRingCat RingCat)
        U x hxU ((forget₂ CommRingCat RingCat).map (ν.c.app (op U)) s)) = _
    exact SemilinearStalk.commStalkRingEquiv_germ R' x U hxU (ν.c.app (op U) s)
  let ι := (Scheme.Hom.toRingCatSheafHom ν).hom
  have hscalar (b : B) (z : V) :
      e' (u (b • z)) = e' (ρ b) * e' (u z) := by
    obtain ⟨U₁, hU₁, r₁, hr⟩ := TopCat.Presheaf.exists_germ_eq R b
    obtain ⟨U₂, hU₂, m₂, hm⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf z
    let U : Opens X := U₁ ⊓ U₂
    have hU : x ∈ U := ⟨hU₁, hU₂⟩
    have hr' : R.germ U x hU (R.map (homOfLE inf_le_left).op r₁) = b := by
      rwa [TopCat.Presheaf.germ_res_apply]
    have hm' : TopCat.Presheaf.germ M.val.presheaf U x hU
        (M.val.presheaf.map (homOfLE inf_le_right).op m₂) = z := by
      rwa [TopCat.Presheaf.germ_res_apply]
    let iL : U ⟶ U₁ := homOfLE inf_le_left
    let iR : U ⟶ U₂ := homOfLE inf_le_right
    let a := R.map iL.op r₁
    let m := M.val.presheaf.map iR.op m₂
    let S := (((Opens.map ν.base).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Xnorm)).obj
        Xnorm.ringCatSheaf).obj.obj (op U)
    let : Ring (ToType S) := RingCat.ring S
    let : Module (ToType S) (ToType S) := inferInstance
    let m' : ToType S := m
    have hsec : (a • m : ToType (M.val.obj (op U))) =
        ((ι.app (op U)).hom a * m' : ToType S) := by
      change ((ι.app (op U)).hom a) • m' = (ι.app (op U)).hom a * m'
      dsimp [M, Scheme.Modules.pushforward, SheafOfModules.pushforward,
        PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
        PresheafOfModules.pushforward₀Obj]
    have hu (t : M.val.obj (op U)) :
        u (TopCat.Presheaf.germ M.val.presheaf U x hU t) = R'R.germ U x hU t := by
      change u (TopCat.Presheaf.germ (PresheafOfModules.unit R'R).presheaf U x hU t) = _
      exact unitStalkLEquiv_germ R'R x U hU t
    have hz : u z = R'R.germ U x hU m := by
      rw [← hm']
      exact hu m
    have hρ : ρ b = R'R.germ U x hU ((ι.app (op U)).hom a) := by
      rw [← hr']
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU ι a
    have hbstalk : b • z = TopCat.Presheaf.germ M.val.presheaf U x hU (a • m) := by
      rw [← hr', ← hm']
      exact (PresheafOfModules.germ_ringCat_smul M.val x U hU a m).symm
    calc
      e' (u (b • z)) = e' (R'R.germ U x hU (((ι.app (op U)).hom a) * m')) := by
        rw [hbstalk, hsec]
        exact congrArg e' (hu _)
      _ = e' (R'R.germ U x hU ((ι.app (op U)).hom a)) * e' (R'R.germ U x hU m) :=
        (congrArg e' (map_mul (RingCat.Hom.hom (R'R.germ U x hU))
          ((ι.app (op U)).hom a) m)).trans (map_mul e' _ _)
      _ = e' (ρ b) * e' (u z) := by rw [← hρ, ← hz]
  refine
    { toFun := fun z => e' (u z)
      invFun := fun a => u.symm (e'.symm a)
      left_inv := by
        intro z
        change u.symm (e'.symm (e' (u z))) = z
        rw [e'.symm_apply_apply]
        exact u.symm_apply_apply z
      right_inv := by
        intro a
        calc
          e' (u (u.symm (e'.symm a))) = e' (e'.symm a) :=
            congrArg e' (u.apply_symm_apply _)
          _ = a := e'.apply_symm_apply a
      map_add' := by
        intro z w
        calc
          e' (u (z + w)) = e' (u z + u w) := congrArg e' (u.map_add z w)
          _ = e' (u z) + e' (u w) := e'.map_add _ _
      map_smul' := ?_ }
  intro a z
  let b : ToType B := e.symm a
  have hact : a • z = b • (show V from z) := rfl
  calc
    e' (u (a • z)) = e' (u (b • (show V from z))) :=
      congrArg (fun w : ↑N => e' (u w)) hact
    _ = e' (ρ b) * e' (u (show V from z)) := hscalar b _
    _ = a • e' (u (show V from z)) := by
      rw [hcompat b, show e b = a from e.apply_symm_apply a, Algebra.smul_def]
      congr 1

/-- `stalkModuleFunctor` agrees with `OXModule.stalk`: the two differ only in which of the two
equal scalar actions on the underlying additive stalk is recorded. -/
private def stalkModuleIso (X : Scheme.{u}) (x : X) (M : X.Modules) :
    (stalkModuleFunctor X x).obj M ≅ OXModule.stalk M x := by
  let A := X.presheaf.stalk x
  let e := SemilinearStalk.commStalkRingEquiv X.presheaf x
  let N : ModuleCat.{u} A := (stalkModuleFunctor X x).obj M
  let S := OXModule.stalk M x
  let O := OXModule.ringSheaf X.toRingedSpace
  let B := TopCat.Presheaf.stalk (C := RingCat)
    (X.presheaf ⋙ forget₂ CommRingCat RingCat) x
  let F : SheafOfModules O ⥤ ModuleCat.{u} B :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor O x
  let N₀ : ModuleCat.{u} B := F.obj M
  let : Module B ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) M.val.presheaf x) := N₀.isModule
  let : Module A ↑N := N.isModule
  let : Module A ↑S := S.isModule
  let : Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) M.val.presheaf x) :=
    inferInstanceAs (Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk
        (id M.val : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x))
  have h : ∀ (a : A) (z : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) M.val.presheaf x)),
      (e.symm a) • z = a • z := fun a z => by
    have hz := SemilinearStalk.comm_smul_eq X.presheaf x M.val (e.symm a) z
    rw [e.apply_symm_apply] at hz
    exact hz.symm
  let f : ↑N →ₗ[A] ↑S :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := h }
  let g : ↑S →ₗ[A] ↑N :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun a z => (h a z).symm }
  refine
    { hom := @ModuleCat.ofHom.{u, u} A inferInstance ↑N ↑S
        N.isAddCommGroup N.isModule S.isAddCommGroup S.isModule f
      inv := @ModuleCat.ofHom.{u, u} A inferInstance ↑S ↑N
        S.isAddCommGroup S.isModule N.isAddCommGroup N.isModule g
      hom_inv_id := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
      inv_hom_id := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) }

/-- The stalk of the structure sheaf as a module over itself is the local ring. -/
private def unitStalkFunctorLinearEquiv (X : Scheme.{u}) (x : X) :
    (stalkModuleFunctor X x).obj (SheafOfModules.unit X.ringCatSheaf) ≃ₗ[
      X.presheaf.stalk x] X.presheaf.stalk x :=
  (stalkModuleIso X x (SheafOfModules.unit X.ringCatSheaf)).toLinearEquiv.trans
    (unitStalkLinearEquiv X x)

/-- A functor preserving cokernel diagrams and zero morphisms carries a cokernel to a
cokernel. -/
private def preservesCokernelIso {C D : Type u} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (F : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair F]
    [F.PreservesZeroMorphisms] {M N : C} (f : M ⟶ N) [HasCokernel f] [HasCokernel (F.map f)] :
    cokernel (F.map f) ≅ F.obj (cokernel f) := by
  let π := cokernel.π f
  have w : f ≫ π = 0 ≫ π := by simp [π]
  have hc : IsColimit (F.mapCocone (Cofork.ofπ π w)) :=
    isColimitOfPreserves F (cokernelIsCokernel f)
  have hc1 := (isColimitMapCoconeCoforkEquiv F w) hc
  let dIso : parallelPair (F.map f) (F.map 0) ≅ parallelPair (F.map f) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp)
      (by simp [CategoryTheory.Functor.map_zero])
  let c1 : Cofork (F.map f) (F.map 0) :=
    Cofork.ofπ (F.map π) (by simpa using congrArg F.map w)
  have hc1' : IsColimit c1 := by simpa [c1] using hc1
  exact (cokernelIsCokernel (F.map f)).coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv dIso.symm c1).symm hc1')

/-- **Stacks Project, Tag 0C1R.** The stalk of the normalization quotient `ν_* 𝒪_{X^ν} / 𝒪_X`
at a point of a reduced scheme is the normalization stalk modulo the image of the local ring.

Neither the Nagata hypothesis, nor the dimension of `X`, nor closedness of the point is
needed. -/
@[stacks 0C1R "delta_length"]
public theorem normalizationQuotientStalk_linearEquiv_quotient_range
    (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    Nonempty (normalizationQuotientStalk X hX x ≃ₗ[X.presheaf.stalk x]
      (normalizationPushforwardStalk X hX x ⧸
        LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X hX x)))) := by
  classical
  let f := normalizationModuleMap X hX
  let F := stalkModuleFunctor X x
  let F₀ := AlgebraicGeometry.SheafOfModules.stalkFunctor
    (OXModule.ringSheaf X.toRingedSpace) x
  have : F₀.Additive := by
    refine ⟨?_⟩
    intro M N f g
    apply ModuleCat.hom_ext
    ext z
    show (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (OXModule.ringSheaf X.toRingedSpace).obj).map
          (f.val + g.val)))) z =
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (OXModule.ringSheaf X.toRingedSpace).obj).map f.val))) z +
        (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (OXModule.ringSheaf X.toRingedSpace).obj).map g.val))) z
    simp only [Functor.map_add]
    rfl
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u}
    (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm
  have : E.functor.Additive := by
    dsimp [E]
    infer_instance
  have : F.Additive := by
    refine ⟨?_⟩
    intro M N f g
    show E.functor.map (F₀.map (f + g)) =
      E.functor.map (F₀.map f) + E.functor.map (F₀.map g)
    exact (congrArg E.functor.map (Functor.map_add F₀)).trans (Functor.map_add E.functor)
  have : F.PreservesZeroMorphisms := inferInstance
  let : PreservesColimitsOfShape WalkingParallelPair F :=
    stalkModuleFunctor_preservesParallelPairColimits X x
  let qiso := preservesCokernelIso F f
  let Xnorm := Scheme.normalizationScheme X hX
  let ν := Scheme.normalization X hX
  let A := X.presheaf.stalk x
  let A' := (TopCat.Presheaf.stalkFunctor CommRingCat x).obj
    ((TopCat.Sheaf.pushforward CommRingCat ν.base).obj Xnorm.sheaf).presheaf
  let : Algebra A A' :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map ν.c).hom.toAlgebra
  let es := unitStalkFunctorLinearEquiv X x
  let et := pushedUnitStalkLinearEquiv X hX x
  let g : A →ₗ[A] A' := et.toLinearMap.comp
    ((F.map f).hom.comp es.symm.toLinearMap)
  have hg : g = Algebra.linearMap A A' := by
    ext
    let M₁ := SheafOfModules.unit X.ringCatSheaf
    let P := (Scheme.Modules.toPresheaf X).obj M₁
    let s : ToType (X.presheaf.obj (op ⊤)) := 1
    have hxt : x ∈ (⊤ : Opens X) := by trivial
    let z := TopCat.Presheaf.germ P ⊤ x hxt s
    have hz : es z = (1 : A) := by
      show unitStalkLinearEquiv X x z = 1
      rw [show unitStalkLinearEquiv X x z = _ from
        commStalkRingEquiv_unitStalkLEquiv_germ X.presheaf x ⊤ hxt s]
      exact map_one _
    have hsrc : es.symm (1 : A) = z := es.symm_apply_eq.mpr hz.symm
    show et ((F.map f).hom (es.symm (1 : A))) = algebraMap A A' 1
    rw [hsrc]
    have hmap : (F.map f).hom z =
        TopCat.Presheaf.germ
          ((SheafOfModules.pushforward
            (Scheme.Hom.toRingCatSheafHom ν)).obj
              (SheafOfModules.unit Xnorm.ringCatSheaf)).val.presheaf
          ⊤ x hxt (((Scheme.Hom.toRingCatSheafHom ν).hom.app (op ⊤)).hom s) := by
      show (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((Scheme.Modules.toPresheaf X).map f))) z = _
      dsimp only [z]
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x hxt
        ((Scheme.Modules.toPresheaf X).map f) s
    rw [hmap]
    dsimp [et, pushedUnitStalkLinearEquiv]
    let R' := ((TopCat.Sheaf.pushforward CommRingCat ν.base).obj Xnorm.sheaf).presheaf
    let R'R := R' ⋙ forget₂ CommRingCat RingCat
    let one : ToType (R'R.obj (op ⊤)) := 1
    have hsec : ((Scheme.Hom.toRingCatSheafHom ν).hom.app (op ⊤)).hom s = one := by
      rw [schemeHom_ringCat_component]
      dsimp [s, one]
      exact map_one _
    rw [hsec]
    refine (commStalkRingEquiv_unitStalkLEquiv_germ R' x ⊤ hxt one).trans ?_
    exact (map_one (R'.germ ⊤ x hxt).hom).trans (map_one _).symm
  have hrange : (LinearMap.range (F.map f).hom).map et.toLinearMap =
      LinearMap.range g := by
    rw [← LinearMap.range_comp]
    show LinearMap.range (et.toLinearMap.comp (F.map f).hom) =
      LinearMap.range (et.toLinearMap.comp ((F.map f).hom.comp es.symm.toLinearMap))
    rw [← LinearMap.comp_assoc,
      LinearMap.range_comp_of_range_eq_top _ es.symm.range]
  let eq₁ := Submodule.Quotient.equiv (LinearMap.range (F.map f).hom)
    (LinearMap.range g) et hrange
  let eq₂ := Submodule.quotEquivOfEq (LinearMap.range g)
    (LinearMap.range (Algebra.linearMap A A')) (congrArg LinearMap.range hg)
  exact ⟨(stalkModuleIso X x (normalizationQuotient X hX)).toLinearEquiv.symm.trans
    (qiso.symm.toLinearEquiv.trans
      ((ModuleCat.cokernelIsoRangeQuotient (F.map f)).toLinearEquiv.trans (eq₁.trans eq₂)))⟩

/-- The quotient stalk is the quotient defining the delta invariant of the local ring: by Tag
0C3B(2) the normalization stalk is the integral closure of the local ring in its total ring of
fractions. -/
private theorem normalizationQuotientStalkEquiv_deltaQuotient
    (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    Nonempty (normalizationQuotientStalk X hX x ≃ₗ[X.presheaf.stalk x]
      (↑(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) ⧸
        LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
          ↑(integralClosure (X.presheaf.stalk x)
            (FractionRing (X.presheaf.stalk x)))))) := by
  classical
  let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  let A := X.presheaf.stalk x
  let A' := normalizationPushforwardStalk X hX x
  obtain ⟨e₁⟩ := normalizationQuotientStalk_linearEquiv_quotient_range X hX x
  let IC := integralClosure A (FractionRing A)
  let e₂ : A' ≃ₐ[A] IC := normalizationStalkAlgEquivIntegralClosureSelf X hX x
  have hrange : (LinearMap.range (Algebra.linearMap A A')).map e₂.toLinearMap =
      LinearMap.range (Algebra.linearMap A IC) := by
    refine Submodule.ext fun y => ⟨?_, ?_⟩
    · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, (e₂.commutes a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨algebraMap A A' a, ⟨a, rfl⟩, e₂.commutes a⟩
  exact ⟨e₁.trans (Submodule.Quotient.equiv _ _ e₂.toLinearEquiv hrange)⟩

/-- **Stacks Project, Tag 0C1R.** The length of the stalk of the normalization quotient is the
delta invariant of the local ring.

Neither the Nagata hypothesis, nor the dimension of `X`, nor closedness of the point is needed;
without them both sides may be infinite. -/
@[stacks 0C1R "delta_length"]
public theorem length_normalizationQuotientStalk (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    Module.length (X.presheaf.stalk x) (normalizationQuotientStalk X hX x) =
      Ring.deltaInvariant (X.presheaf.stalk x) :=
  (normalizationQuotientStalkEquiv_deltaQuotient X hX x).some.length_eq

/-- For a reduced Nagata local ring of dimension at most one, the quotient of its integral
closure in the total ring of fractions by the ring itself has finite length.  In dimension zero
the ring is a field and the quotient vanishes. -/
@[ega "IV 7.6.1" "finiteness of A' over A"]
private theorem isFiniteLength_integralClosure_quotient_of_dim_le_one (A : Type u) [CommRing A]
    [IsLocalRing A] [_root_.IsReduced A] (hA : IsNagataRing A) (hdim : ringKrullDim A ≤ 1) :
    IsFiniteLength A (↑(integralClosure A (FractionRing A)) ⧸
      LinearMap.range (Algebra.linearMap A ↑(integralClosure A (FractionRing A)))) := by
  have : IsNoetherianRing A := hA.1
  by_cases hfield : IsField A
  · let : Field A := hfield.toField
    have hsurj : Function.Surjective
        (algebraMap A ↑(integralClosure A (FractionRing A))) := fun z => by
      obtain ⟨a, ha⟩ := IsFractionRing.surjective_iff_isField.mpr hfield (z : FractionRing A)
      exact ⟨a, Subtype.ext ha⟩
    have : Subsingleton (↑(integralClosure A (FractionRing A)) ⧸
        LinearMap.range (Algebra.linearMap A ↑(integralClosure A (FractionRing A)))) :=
      Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hsurj)
    exact IsFiniteLength.of_subsingleton
  · have hdim1 : ringKrullDim A = 1 := by
      refine le_antisymm hdim ?_
      have hpos : ¬ ringKrullDim A ≤ 0 := fun hzero => by
        have : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr hzero
        exact hfield Ring.KrullDimLE.isField_of_isReduced
      cases h : ringKrullDim A with
      | bot => exact absurd (by simp [h] : ringKrullDim A ≤ 0) hpos
      | coe d =>
        refine WithBot.coe_le_coe.mpr (Order.one_le_iff_ne_zero.mpr fun hd => ?_)
        exact hpos (by simp [h, hd])
    exact isFiniteLength_integralClosure_quotient hA hdim1

/-- **Stacks Project, Tag 0C1R.** On a reduced Nagata scheme of dimension one the stalk of the
normalization quotient has finite length.

Closedness of the point is not needed, and the dimension hypothesis is used only through the
dimension of the local ring at `x`. -/
@[stacks 0C1R "delta_length"]
public theorem isFiniteLength_normalizationQuotientStalk (X : Scheme.{u}) [IsReduced X]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X = 1)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    IsFiniteLength (X.presheaf.stalk x) (normalizationQuotientStalk X hX x) := by
  have : _root_.IsReduced (X.presheaf.stalk x) :=
    AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  have hdimA : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
    (ringKrullDim_stalk_le_topologicalKrullDim X x).trans_eq hdim
  obtain ⟨e⟩ := normalizationQuotientStalkEquiv_deltaQuotient X hX x
  exact e.symm.isFiniteLength (isFiniteLength_integralClosure_quotient_of_dim_le_one
    (X.presheaf.stalk x) (stalk_isNagataRing X hNagata x) hdimA)

end Stacks.AlgebraicGeometry.NormalizationQuotient

end
