module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialsPresheafFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Differentials
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.InverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of differentials on ringed spaces

A commutative square of ringed spaces
```
  X' --f--> X
  |h'       |h
  v         v
  S' --g--> S
```
induces a canonical morphism from the pullback of the relative differentials of `h` to the
relative differentials of `h'`. It is uniquely determined by carrying the differential of a
local section to the differential of its pullback.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.compositeDerivation`: the relative derivation obtained
  from the upper-left corner of the square.
* `AlgebraicGeometry.SheafOfModules.pushforwardDifferentialMap`: the canonical morphism
  `Ω_{X/S} ⟶ f_* Ω_{X'/S'}`.
* `AlgebraicGeometry.SheafOfModules.IsDifferentialMap`: compatibility of a morphism of
  relative differentials with the universal derivations.
* `AlgebraicGeometry.SheafOfModules.differentialMap`: the canonical morphism
  `f^* Ω_{X/S} ⟶ Ω_{X'/S'}`.
* `AlgebraicGeometry.SheafOfModules.inverseImageToPullback`: the canonical morphism from the
  inverse image of a module to the restriction of its extension of scalars.
* `AlgebraicGeometry.SheafOfModules.inverseImageDifferentialMap`: the canonical morphism
  `f⁻¹Ω_{X/S} ⟶ Ω_{X'/S'}` of `f⁻¹𝒪_X`-modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.existsUnique_compositeDerivation`: the composite of the
  structural ring map with the pushforward of the universal derivation is the unique relative
  derivation with the expected value on local sections.
* `AlgebraicGeometry.SheafOfModules.existsUnique_differentialMap`: existence and uniqueness
  of the canonical morphism of differentials.
* `AlgebraicGeometry.SheafOfModules.differentialMap_adjoint`: the pullback description and
  the pushforward description of that morphism correspond under the adjunction.
* `AlgebraicGeometry.SheafOfModules.inverseImageDifferentialMap_eq`: the inverse-image
  morphism factors the scalar-extended one through the canonical comparison.

## Implementation notes

The characterizing condition is stated on the adjoint morphism into the pushforward of the
differentials, which simultaneously pins down the pullback and the pushforward descriptions.
The inverse-image description is a morphism of modules over `f⁻¹𝒪_X`, with the target carrying
its scalars restricted along `f⁻¹𝒪_X ⟶ 𝒪_{X'}`.

The structural morphism `h⁻¹ 𝒪_S ⟶ 𝒪_X` and the comorphism `𝒪_S ⟶ h_* 𝒪_X` it is adjoint to
are `Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap` and
`Stacks.Sheaves.RingedSpaceDifferentials.structureSheafMap`; only those two names are opened
from that namespace, so the differentials vocabulary of this file stays unambiguously in
`AlgebraicGeometry.SheafOfModules`.

Where the two spellings `(f ≫ g).base` and `f.base ≫ g.base` of a composite continuous map
meet, they are definitionally equal, so the comparison morphisms are stated without a
transport; a transport is used only across the genuinely non-trivial commutativity hypothesis
of the square.

## References

* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageStructureMap structureSheafMap)

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- The inverse image functor on sheaves of commutative rings is compatible with
composition. -/
private noncomputable def pullbackCompIso {A B C : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    TopCat.Sheaf.pullback CommRingCat (f ≫ g) ≅
      TopCat.Sheaf.pullback CommRingCat g ⋙ TopCat.Sheaf.pullback CommRingCat f :=
  Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat (f ≫ g))
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f))

/-- Transposing a composite of structural morphisms across the inverse-image/pushforward
adjunctions is the composite of the transposes, up to the comparison of inverse images. -/
private theorem pullbackTranspose_comp {A B C : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (F : TopCat.Sheaf CommRingCat.{u} C) (G : TopCat.Sheaf CommRingCat.{u} B)
    (H : TopCat.Sheaf CommRingCat.{u} A)
    (α : G ⟶ (TopCat.Sheaf.pushforward CommRingCat f).obj H)
    (β : F ⟶ (TopCat.Sheaf.pushforward CommRingCat g).obj G) :
    (pullbackCompIso f g).hom.app F ≫
      (TopCat.Sheaf.pullback CommRingCat f).map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).homEquiv F G).symm β) ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f).homEquiv G H).symm α =
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat (f ≫ g)).homEquiv F H).symm
      (β ≫ (TopCat.Sheaf.pushforward CommRingCat g).map α) := by
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat (f ≫ g)
  let b := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f)
  have hi := Adjunction.homEquiv_leftAdjointUniq_hom_app a b F
  apply (a.homEquiv F H).injective
  rw [a.homEquiv_naturality_right]
  show a.homEquiv F _ ((Adjunction.leftAdjointUniq a b).hom.app F) ≫ _ = _
  rw [hi]
  show b.homEquiv F H _ = _
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp [a]
  rfl

/-- The structural morphism is compatible with composition, through the comparison of
inverse images. -/
private theorem inverseImageStructureMap_comp {A B C : RingedSpace.{u, u}} (f : A ⟶ B)
    (g : B ⟶ C) :
    (pullbackCompIso f.hom.base g.hom.base).hom.app C.sheaf ≫
        (TopCat.Sheaf.pullback CommRingCat f.hom.base).map (inverseImageStructureMap g) ≫
        inverseImageStructureMap f =
      inverseImageStructureMap (f ≫ g) := by
  have hcomp : structureSheafMap g ≫
      (TopCat.Sheaf.pushforward CommRingCat g.hom.base).map (structureSheafMap f) =
      structureSheafMap (f ≫ g) := rfl
  have h := pullbackTranspose_comp f.hom.base g.hom.base C.sheaf B.sheaf A.sheaf
    (structureSheafMap f) (structureSheafMap g)
  exact h.trans (congrArg (fun q => ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (f.hom.base ≫ g.hom.base)).homEquiv C.sheaf A.sheaf).symm q) hcomp)

/-- The underlying continuous maps of a commutative square of ringed spaces commute. -/
private theorem baseComm {X' X S' S : RingedSpace.{u, u}} (f : X' ⟶ X) (h : X ⟶ S)
    (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    f.hom.base ≫ h.hom.base = h'.hom.base ≫ g.hom.base := by
  simpa only [AlgebraicGeometry.SheafedSpace.comp_hom_base] using
    congrArg (fun q => q.hom.base) hcomm

/-- The base-change morphism `f⁻¹h⁻¹𝒪_S ⟶ h'⁻¹𝒪_{S'}` of a commutative square. -/
private noncomputable def inverseImageBaseChangeMap {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    (TopCat.Sheaf.pullback CommRingCat f.hom.base).obj
        ((TopCat.Sheaf.pullback CommRingCat h.hom.base).obj S.sheaf) ⟶
      (TopCat.Sheaf.pullback CommRingCat h'.hom.base).obj S'.sheaf :=
  (pullbackCompIso f.hom.base h.hom.base).inv.app S.sheaf ≫
    eqToHom (congrArg (fun q : X'.carrier ⟶ S.carrier =>
      (TopCat.Sheaf.pullback CommRingCat q).obj S.sheaf) (baseComm f h h' g hcomm)) ≫
    (pullbackCompIso h'.hom.base g.hom.base).hom.app S.sheaf ≫
    (TopCat.Sheaf.pullback CommRingCat h'.hom.base).map (inverseImageStructureMap g)

/-- The transpose of `inverseImageBaseChangeMap` across the adjunction for `f`. -/
private noncomputable def inverseImageBaseChangeStructureMap
    {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    (TopCat.Sheaf.pullback CommRingCat h.hom.base).obj S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat f.hom.base).obj
        ((TopCat.Sheaf.pullback CommRingCat h'.hom.base).obj S'.sheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).homEquiv _ _)
    (inverseImageBaseChangeMap f h h' g hcomm)

/-- The structural morphism transports along an equality of morphisms of ringed spaces. -/
private theorem inverseImageStructureMap_cast {X S : RingedSpace.{u, u}} (p q : X ⟶ S)
    (hpq : p = q) :
    eqToHom (congrArg (fun b : X.carrier ⟶ S.carrier =>
      (TopCat.Sheaf.pullback CommRingCat b).obj S.sheaf)
      (congrArg (fun k : X ⟶ S => k.hom.base) hpq)) ≫
        inverseImageStructureMap q = inverseImageStructureMap p := by
  cases hpq
  rfl

/-- The base-change morphism of a commutative square makes the square of structural
morphisms commute. -/
private theorem inverseImageBaseChangeStructureMap_compat {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    inverseImageStructureMap h ≫ structureSheafMap f =
    inverseImageBaseChangeStructureMap f h h' g hcomm ≫
        (TopCat.Sheaf.pushforward CommRingCat f.hom.base).map
          (inverseImageStructureMap h') := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base
  let E := adj.homEquiv ((TopCat.Sheaf.pullback CommRingCat h.hom.base).obj S.sheaf)
    X'.sheaf
  apply E.symm.injective
  have hleft : E.symm (inverseImageStructureMap h ≫ structureSheafMap f) =
      (TopCat.Sheaf.pullback CommRingCat f.hom.base).map
        (inverseImageStructureMap h) ≫ inverseImageStructureMap f :=
    adj.homEquiv_naturality_left_symm (inverseImageStructureMap h)
      (structureSheafMap f)
  have hright : E.symm (inverseImageBaseChangeStructureMap f h h' g hcomm ≫
      (TopCat.Sheaf.pushforward CommRingCat f.hom.base).map
        (inverseImageStructureMap h')) =
      inverseImageBaseChangeMap f h h' g hcomm ≫ inverseImageStructureMap h' := by
    calc
      _ = (adj.homEquiv ((TopCat.Sheaf.pullback CommRingCat h.hom.base).obj S.sheaf)
            ((TopCat.Sheaf.pullback CommRingCat h'.hom.base).obj S'.sheaf)).symm
            (inverseImageBaseChangeStructureMap f h h' g hcomm) ≫
          inverseImageStructureMap h' :=
        adj.homEquiv_naturality_right_symm
          (inverseImageBaseChangeStructureMap f h h' g hcomm)
          (inverseImageStructureMap h')
      _ = _ := by
        congr 1
        simp [inverseImageBaseChangeStructureMap, adj]
  rw [hleft, hright]
  refine (cancel_epi ((pullbackCompIso f.hom.base h.hom.base).hom.app S.sheaf)).mp ?_
  rw [inverseImageStructureMap_comp f h]
  dsimp only [inverseImageBaseChangeMap]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [inverseImageStructureMap_comp h' g]
  exact (inverseImageStructureMap_cast (f ≫ h) (h' ≫ g) hcomm).symm

/-- The composite of `f^♯` with the pushforward of the universal derivation is an
`S`-derivation, and it is the unique one whose value on every local section `a` is the
universal derivation of `f^♯ a`. -/
@[stacks 08RU "composite derivation"]
theorem existsUnique_compositeDerivation {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S)
    (hcomm : f ≫ h = h' ≫ g) :
    ∃! D : SheafDerivation (inverseImageStructureMap h)
      ((RingedSpaceModuleAdjunction.modulePushforward f).obj
        (moduleOfDifferentials (inverseImageStructureMap h'))),
      ∀ (U : Opens X.carrier) (a : X.presheaf.obj (.op U)),
        D.d a = (universalDerivation
          (inverseImageStructureMap h')).d ((f.hom.c.app (.op U)).hom a) := by
  let M' := moduleOfDifferentials (inverseImageStructureMap h')
  have hsq' := congrArg (fun q => q.hom)
    (inverseImageBaseChangeStructureMap_compat f h h' g hcomm)
  let φ := (structureSheafMap f).hom
  let ψ := (inverseImageBaseChangeStructureMap f h h' g hcomm).hom
  let ι' := ((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map
    (inverseImageStructureMap h')).hom
  let Ωpush := PresheafOfModules.pushforward₀OfCommRingCat
    (Opens.map f.hom.base) X'.presheaf |>.obj M'.val
  let dpush : Ωpush.Derivation (F := 𝟭 (Opens X.carrier)) ι' := {
    d := fun {U} => (universalDerivation
      (inverseImageStructureMap h')).d (X := (Opens.map f.hom.base).op.obj U)
    d_mul {U} a b := (universalDerivation (inverseImageStructureMap h')).d_mul
      (X := (Opens.map f.hom.base).op.obj U) a b
    d_map i a := (universalDerivation (inverseImageStructureMap h')).d_map
      ((Opens.map f.hom.base).op.map i) a
    d_app {U} a := (universalDerivation (inverseImageStructureMap h')).d_app
      (X := (Opens.map f.hom.base).op.obj U) a
  }
  let D : SheafDerivation (inverseImageStructureMap h)
      ((RingedSpaceModuleAdjunction.modulePushforward f).obj M') := by
    show (PresheafOfModules.restrictScalars
      (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))).obj Ωpush |>.Derivation'
        (inverseImageStructureMap h).hom
    exact SheafDifferentials.compDeriv dpush φ ψ hsq'
  refine ⟨D, ?_, ?_⟩
  · intro U a
    show (SheafDifferentials.compDeriv dpush φ ψ
      hsq').d a = _
    exact SheafDifferentials.compDeriv_d dpush φ ψ
      hsq' (U := .op U) a
  · intro D' hD'
    apply PresheafOfModules.Derivation.ext
    ext U a
    show D'.d a = (SheafDifferentials.compDeriv dpush φ ψ
      hsq').d a
    rw [hD' U.unop a]
    exact (SheafDifferentials.compDeriv_d dpush φ ψ
      hsq' (U := U) a).symm

/-- The relative derivation obtained from the upper-left corner of the square. -/
noncomputable def compositeDerivation {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    SheafDerivation (inverseImageStructureMap h)
      ((RingedSpaceModuleAdjunction.modulePushforward f).obj
        (moduleOfDifferentials (inverseImageStructureMap h'))) :=
  Classical.choose (existsUnique_compositeDerivation f h h' g hcomm)

/-- The composite derivation takes the expected value on local sections. -/
private theorem compositeDerivation_d {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g)
    (U : Opens X.carrier) (a : X.presheaf.obj (.op U)) :
    (compositeDerivation f h h' g hcomm).d a = (universalDerivation
      (inverseImageStructureMap h')).d ((f.hom.c.app (.op U)).hom a) :=
  (Classical.choose_spec (existsUnique_compositeDerivation f h h' g hcomm)).1 U a

/-- The universal map `Ω_{X/S} ⟶ f_* Ω_{X'/S'}`. -/
@[stacks 08RU "map to pushforward differentials"]
noncomputable def pushforwardDifferentialMap {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    moduleOfDifferentials (inverseImageStructureMap h) ⟶
      (RingedSpaceModuleAdjunction.modulePushforward f).obj
        (moduleOfDifferentials (inverseImageStructureMap h')) :=
  Classical.choose ((universalDerivation_isUniversal
    (inverseImageStructureMap h)) _ (compositeDerivation f h h' g hcomm))

/-- A map of relative differentials is compatible with universal derivations on
each open subset of the target space. -/
def IsDifferentialMap {X' X S' S : RingedSpace.{u, u}} (f : X' ⟶ X) (h : X ⟶ S)
    (h' : X' ⟶ S')
    (c : (RingedSpaceModuleAdjunction.modulePullback f).obj
      (moduleOfDifferentials (inverseImageStructureMap h)) ⟶
        moduleOfDifferentials (inverseImageStructureMap h')) : Prop :=
  ∀ (U : Opens X.carrier) (a : X.presheaf.obj (.op U)),
    (((RingedSpaceModuleAdjunction.homEquiv f
      (moduleOfDifferentials (inverseImageStructureMap h'))
      (moduleOfDifferentials (inverseImageStructureMap h))) c).val.app (.op U)).hom
        ((universalDerivation (inverseImageStructureMap h)).d a) =
      (universalDerivation (inverseImageStructureMap h')).d
        ((f.hom.c.app (.op U)).hom a)

/-- The canonical morphism of differentials for a commutative square of ringed spaces exists
and is uniquely determined by its action on differentials of local sections. -/
@[stacks 08RU "canonical map and uniqueness", ega "IV 16.4.3" "(16.4.3.6),(16.4.3.7)"]
theorem existsUnique_differentialMap {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S)
    (hcomm : f ≫ h = h' ≫ g) :
    ∃! c : (RingedSpaceModuleAdjunction.modulePullback f).obj
        (moduleOfDifferentials (inverseImageStructureMap h)) ⟶
      moduleOfDifferentials (inverseImageStructureMap h'),
      IsDifferentialMap f h h' c := by
  let Ω := moduleOfDifferentials (inverseImageStructureMap h)
  let Ω' := moduleOfDifferentials (inverseImageStructureMap h')
  let d := universalDerivation (inverseImageStructureMap h)
  let D := compositeDerivation f h h' g hcomm
  let e := RingedSpaceModuleAdjunction.homEquiv f Ω' Ω
  obtain ⟨m, hm, hmunique⟩ := universalDerivation_isUniversal
    (inverseImageStructureMap h) ((RingedSpaceModuleAdjunction.modulePushforward f).obj Ω') D
  let c := e.symm m
  have hc : e c = m := Equiv.apply_symm_apply e m
  refine ⟨c, ?_, ?_⟩
  · intro U a
    have hfac' : (m.val.app (.op U)).hom (d.d a) = D.d a := congrArg (fun δ : SheafDerivation
        (inverseImageStructureMap h) ((RingedSpaceModuleAdjunction.modulePushforward f).obj Ω') =>
          δ.d a) hm
    have hcomp := compositeDerivation_d f h h' g hcomm U a
    show (((e c).val.app (.op U)).hom) (d.d a) =
      (universalDerivation (inverseImageStructureMap h')).d
        ((f.hom.c.app (.op U)).hom a)
    rw [hc]
    exact hfac'.trans hcomp
  · intro c' hc'
    have hfac' : d.postcomp (e c').val = D := by
      ext U a
      have hc := hc' U.unop a
      show ((e c').val.app U).hom (d.d a) = D.d a
      exact hc.trans (compositeDerivation_d f h h' g hcomm U.unop a).symm
    exact e.injective ((hmunique (e c') hfac').trans hc.symm)

/-- The canonical map `f^* Ω_{X/S} ⟶ Ω_{X'/S'}`. -/
noncomputable def differentialMap {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    (RingedSpaceModuleAdjunction.modulePullback f).obj
      (moduleOfDifferentials (inverseImageStructureMap h)) ⟶
        moduleOfDifferentials (inverseImageStructureMap h') :=
  Classical.choose (existsUnique_differentialMap f h h' g hcomm)

/-- The pullback map on differentials is adjoint to the canonical map into
pushforward differentials. -/
@[stacks 08RU "agreement under adjunction"]
theorem differentialMap_adjoint {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S)
    (hcomm : f ≫ h = h' ≫ g) :
    (RingedSpaceModuleAdjunction.homEquiv f
      (moduleOfDifferentials (inverseImageStructureMap h'))
      (moduleOfDifferentials (inverseImageStructureMap h)))
        (differentialMap f h h' g hcomm) =
      pushforwardDifferentialMap f h h' g hcomm := by
  let Ω := moduleOfDifferentials (inverseImageStructureMap h)
  let Ω' := moduleOfDifferentials (inverseImageStructureMap h')
  let d := universalDerivation (inverseImageStructureMap h)
  let D := compositeDerivation f h h' g hcomm
  have hfactor : d.postcomp (pushforwardDifferentialMap f h h' g hcomm).val = D := by
    dsimp [D, pushforwardDifferentialMap]
    exact (Classical.choose_spec ((universalDerivation_isUniversal
      (inverseImageStructureMap h)) _ (compositeDerivation f h h' g hcomm))).1
  have hAdjFactor : d.postcomp ((RingedSpaceModuleAdjunction.homEquiv f Ω' Ω)
        (differentialMap f h h' g hcomm)).val = D := by
    ext U a
    have hmap := (Classical.choose_spec
      (existsUnique_differentialMap f h h' g hcomm)).1 U.unop a
    show (((RingedSpaceModuleAdjunction.homEquiv f Ω' Ω)
      (differentialMap f h h' g hcomm)).val.app U).hom
      (d.d a) = D.d a
    simpa only [differentialMap, IsDifferentialMap, Ω, Ω', d] using
      (hmap.trans (compositeDerivation_d f h h' g hcomm U.unop a).symm)
  have hu := (Classical.choose_spec ((universalDerivation_isUniversal
    (inverseImageStructureMap h)) _ D)).2
  exact (hu _ hAdjFactor).trans (hu _ hfactor).symm

/-- The canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair `X ⟶ Y ⟶ S`, obtained from
the canonical map of the square whose horizontal edges are the identity of `X` and `g`. -/
noncomputable def toRelativeDifferentials {X Y S : RingedSpace.{u, u}} (f : X ⟶ Y)
    (g : Y ⟶ S) :
    moduleOfDifferentials (inverseImageStructureMap (f ≫ g)) ⟶
      moduleOfDifferentials (inverseImageStructureMap f) :=
  ((_root_.SheafOfModules.pullbackId (structureSheafRing X)).inv.app
      (moduleOfDifferentials (inverseImageStructureMap (f ≫ g)))) ≫
    differentialMap (𝟙 X) (f ≫ g) f g (by simp)

/-- The structural homomorphism `f⁻¹𝒪_X ⟶ 𝒪_{X'}` after forgetting commutativity. -/
noncomputable def inverseImageStructureRingMap {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) :
    underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat f.hom.base).obj X.sheaf) ⟶
      structureSheafRing X' :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X'.carrier)
    (forget₂ CommRingCat.{u} RingCat.{u})).map
    (inverseImageStructureMap f)

/-- `Ω_{X'/S'}` viewed as a module over `f⁻¹𝒪_X`. -/
noncomputable abbrev inverseImageDifferentialTarget {X' X S' : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h' : X' ⟶ S') :
    _root_.SheafOfModules.{u} (underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat f.hom.base).obj X.sheaf)) :=
  (_root_.SheafOfModules.restrictScalars (inverseImageStructureRingMap f)).obj
    (moduleOfDifferentials (inverseImageStructureMap h'))

/-- The inverse-image structural morphism of sheaves of rings is the pushforward transpose of
the structure morphism of `f`. -/
private theorem inverseImageRingHom_comp_structureSheafHom {X' X : RingedSpace.{u, u}}
    (f : X' ⟶ X) :
    inverseImageRingHom f.hom.base X.sheaf ≫
      ((RingedSpaceModuleAdjunction.opensMap f).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology X'.carrier)).map (inverseImageStructureRingMap f) =
      RingedSpaceModuleAdjunction.structureSheafHom f := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base
  have hcomm :
      adj.unit.app X.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat f.hom.base).map
          (inverseImageStructureMap f) =
        ObjectProperty.homMk f.hom.c := by
    let E := adj.homEquiv X.sheaf X'.sheaf
    have hn := adj.homEquiv_naturality_right (𝟙 _) (inverseImageStructureMap f)
    rw [adj.homEquiv_id] at hn
    have hmap : E (inverseImageStructureMap f) = ObjectProperty.homMk f.hom.c := by
      dsimp [E]
      rw [inverseImageStructureMap]
      exact Equiv.apply_symm_apply _ _
    have h1 : adj.unit.app X.sheaf ≫
          (TopCat.Sheaf.pushforward CommRingCat f.hom.base).map
            (inverseImageStructureMap f) = E (𝟙 _ ≫ inverseImageStructureMap f) := hn.symm
    have h2 : E (𝟙 _ ≫ inverseImageStructureMap f) = E (inverseImageStructureMap f) :=
      congrArg E (Category.id_comp (inverseImageStructureMap f))
    exact h1.trans (h2.trans hmap)
  apply Sheaf.hom_ext
  ext U a
  have hU := congrArg (fun m => m.hom.app U) hcomm
  change (adj.unit.app X.sheaf).hom.app U ≫
      ((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map
        (inverseImageStructureMap f)).hom.app U =
    (structureSheafMap f).hom.app U at hU
  have hUa := congrArg (fun q : CommRingCat.Hom _ _ => q.hom a) hU
  simp only [TopCat.Sheaf.pushforward_map, TopCat.Sheaf.pushforward_obj_val,
    TopCat.Presheaf.pushforward_map_app', TopCat.Presheaf.pushforward_obj_obj,
    structureSheafMap] at hUa
  show ((((inverseImageStructureMap f).hom.app
      ((Opens.map f.hom.base).op.obj U)).hom)
        (((adj.unit.app X.sheaf).hom.app U).hom a)) =
    ((f.hom.c.app U).hom a)
  exact hUa

/-- The canonical morphism from the inverse image of a module to the restriction of its
extension of scalars is characterized on local sections coming from the module. These
sections locally generate the inverse-image sheaf. -/
theorem existsUnique_inverseImageToPullback {X' X : RingedSpace.{u, u}} (f : X' ⟶ X)
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    ∃! t : inverseImageModule f.hom.base X.sheaf M ⟶
      (_root_.SheafOfModules.restrictScalars (inverseImageStructureRingMap f)).obj
        ((RingedSpaceModuleAdjunction.modulePullback f).obj M),
      ∀ (U : Opens X.carrier) (a : M.val.obj (.op U)),
        (t.val.app (.op ((Opens.map f.hom.base).obj U))).hom
          (((inverseImageModuleUnit f.hom.base X.sheaf M).val.app (.op U)).hom a) =
          (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).unit.app
            M).val.app (.op U)).hom a := by
  let α := inverseImageRingHom f.hom.base X.sheaf
  let γ := inverseImageStructureRingMap f
  let β := RingedSpaceModuleAdjunction.structureSheafHom f
  have hcompat : α ≫
      ((RingedSpaceModuleAdjunction.opensMap f).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology X'.carrier)).map γ = β :=
    inverseImageRingHom_comp_structureSheafHom f
  let _ : (PresheafOfModules.pushforward α.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let _ : (_root_.SheafOfModules.pushforward α).IsRightAdjoint :=
    _root_.SheafOfModules.instIsRightAdjointPushforward α
  let P := (RingedSpaceModuleAdjunction.modulePullback f).obj M
  let N := (_root_.SheafOfModules.restrictScalars γ).obj P
  let Q := (RingedSpaceModuleAdjunction.modulePushforward f).obj P
  let R := (_root_.SheafOfModules.pushforward α).obj N
  let κval : Q.val ⟶ R.val := {
    app := fun U => by
      let V := (Opens.map f.hom.base).op.obj U
      have hgf' : (β.hom.app U).hom =
          (γ.hom.app V).hom.comp (α.hom.app U).hom := by
        ext r
        exact congrArg (fun φ => (φ.hom.app U) r) hcompat.symm
      exact (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom
        (γ.hom.app V).hom (β.hom.app U).hom hgf' (P.val.obj V)).hom
    naturality := by
      intro U V i
      ext x
      rfl
  }
  let κ : Q ⟶ R := (_root_.SheafOfModules.fullyFaithfulForget _).preimage κval
  let ηβ := (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).unit.app M
  let ηα := inverseImageModuleUnit f.hom.base X.sheaf M
  let adjα := _root_.SheafOfModules.pullbackPushforwardAdjunction α
  let transposed := ηβ ≫ κ
  let t := (adjα.homEquiv M N).symm transposed
  have hκ (U : (Opens X.carrier)ᵒᵖ) (x : Q.val.obj U) :
      (κ.val.app U).hom x = x := by
    show (κval.app U).hom x = x
    simp [κval]
    rfl
  have ht : (adjα.homEquiv M N) t = transposed := Equiv.apply_symm_apply _ _
  have hη : ηα = adjα.unit.app M := by
    dsimp [ηα, inverseImageModuleUnit, adjα, inverseImageModule]
  have hunit (s : _) : (adjα.homEquiv M N) s =
      ηα ≫ (_root_.SheafOfModules.pushforward α).map s := by
    rw [hη]
    exact Adjunction.homEquiv_unit adjα (X := M) (Y := N) s
  have htrans : ηα ≫ (_root_.SheafOfModules.pushforward α).map t = transposed :=
    (hunit t).symm.trans ht
  refine ⟨t, ?_, ?_⟩
  · intro U a
    have hcomp := congrArg (fun φ => (φ.val.app (.op U)).hom a) htrans
    change (((ηα.val.app (.op U) ≫
          ((_root_.SheafOfModules.pushforward α).map t).val.app (.op U)).hom) a) =
      ((ηβ.val.app (.op U) ≫ κ.val.app (.op U)).hom) a at hcomp
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
    change (t.val.app (.op ((Opens.map f.hom.base).obj U))).hom
          ((ηα.val.app (.op U)).hom a) =
        (κ.val.app (.op U)).hom ((ηβ.val.app (.op U)).hom a) at hcomp
    show (t.val.app (.op ((Opens.map f.hom.base).obj U))).hom
        ((ηα.val.app (.op U)).hom a) =
      (ηβ.val.app (.op U)).hom a
    simpa only [hκ] using hcomp
  · intro t' ht'
    have htrans' : ηα ≫ (_root_.SheafOfModules.pushforward α).map t' = transposed := by
      apply _root_.SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext a
      show (t'.val.app (.op ((Opens.map f.hom.base).obj U.unop))).hom
          ((ηα.val.app U).hom a) = (ηβ.val.app U).hom a
      exact ht' U.unop a
    apply (adjα.homEquiv M N).injective
    exact (hunit t').trans (htrans'.trans ht.symm)

/-- The tensor-unit map from the inverse image of a module to the restriction
of its extension of scalars `f* M`. -/
noncomputable def inverseImageToPullback {X' X : RingedSpace.{u, u}} (f : X' ⟶ X)
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    inverseImageModule f.hom.base X.sheaf M ⟶
      (_root_.SheafOfModules.restrictScalars (inverseImageStructureRingMap f)).obj
        ((RingedSpaceModuleAdjunction.modulePullback f).obj M) :=
  Classical.choose (existsUnique_inverseImageToPullback f M)

/-- The canonical map `f⁻¹Ω_{X/S} ⟶ Ω_{X'/S'}` of `f⁻¹𝒪_X`-modules.
The target carries its restricted scalar action. -/
@[stacks 08RU "inverse-image map"]
noncomputable def inverseImageDifferentialMap {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    inverseImageModule f.hom.base X.sheaf
      (moduleOfDifferentials (inverseImageStructureMap h)) ⟶
        inverseImageDifferentialTarget f h' :=
  inverseImageToPullback f (moduleOfDifferentials (inverseImageStructureMap h)) ≫
    (_root_.SheafOfModules.restrictScalars (inverseImageStructureRingMap f)).map
      (differentialMap f h h' g hcomm)

/-- The inverse-image differential map is the restriction of the scalar-extended
map `c_f`, after the canonical tensor-unit map `f⁻¹Ω ⟶ f*Ω`. -/
@[stacks 08RU "inverse-image and tensor comparison"]
theorem inverseImageDifferentialMap_eq {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    inverseImageDifferentialMap f h h' g hcomm =
      inverseImageToPullback f (moduleOfDifferentials (inverseImageStructureMap h)) ≫
      (_root_.SheafOfModules.restrictScalars (inverseImageStructureRingMap f)).map
        (differentialMap f h h' g hcomm) := rfl

end AlgebraicGeometry.SheafOfModules
