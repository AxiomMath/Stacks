module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Subfield
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.TorCriterion
public import StacksFrontier.RingTheory.Tor.Vanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.TensorExtension
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.Construction
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.TensorExtension

/-!
# Divided power envelopes: base change

This file defines the canonical divided power morphism `Crystalline.baseChangeDPMorphism`
between an envelope and the envelope of the base-changed ideal, and proves that the
base-changed envelope is the envelope of the base-changed ideal
(`Crystalline.dividedPowerEnvelope_baseChange`).
-/

@[expose] public section

namespace Crystalline

section BaseChange

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

variable {A : DividedPowerRing} {B B' : Type u} [CommRing B] [CommRing B']

/-- The canonical divided power morphism from a divided power envelope to the envelope after
base change. -/
public noncomputable def baseChangeDPMorphism {A : DividedPowerRing.{max u v}}
    (f : A →+* B) (g : B →+* B') (J : Ideal B)
    (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A (g.comp f) (J.map g) (map_baseIdeal_le_map f g J hJ)) :
    DividedPowers.DPMorphism D.object.dividedPowers D'.object.dividedPowers := by
  let p : IdealPair.Hom J D'.object.ideal :=
    IdealPair.Hom.comp D'.algebraMap
      (IdealPair.Hom.ofRingHom g le_rfl)
  have hp : IdealPair.Hom.comp p (IdealPair.Hom.ofRingHom f hJ) =
      IdealPair.Hom.ofDPMorphism D'.structureMap :=
    IdealPair.Hom.ext_toRingHom _ _ D'.algebraMap_comp
  exact ((D.homEquiv D'.object D'.structureMap).symm ⟨p, hp⟩).1

private lemma baseChangeDPMorphism_comp_structureMap (f : A →+* B)
    (g : B →+* B') (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A (g.comp f) (J.map g)
      (map_baseIdeal_le_map f g J hJ)) :
    (baseChangeDPMorphism f g J hJ D D').comp D.structureMap =
      D'.structureMap := by
  unfold baseChangeDPMorphism
  exact ((D.homEquiv D'.object D'.structureMap).symm
    ⟨IdealPair.Hom.comp D'.algebraMap
      (IdealPair.Hom.ofRingHom g le_rfl),
      IdealPair.Hom.ext_toRingHom _ _ D'.algebraMap_comp⟩).2

/-- The restriction of a morphism out of an envelope, obtained from the universal property, to
the base ring is the given morphism of ring--ideal pairs. -/
private lemma homEquiv_symm_comp_algebraMap {A : DividedPowerRing.{v}}
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) (D : DividedPowerEnvelope A f J hJ)
    (C : DividedPowerRing.{max u v})
    (a : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers)
    (t : IdealPair.HomOver (IdealPair.Hom.ofRingHom f hJ) (IdealPair.Hom.ofDPMorphism a)) :
    ((D.homEquiv C a).symm t).1.toRingHom.comp D.algebraMap.toRingHom = t.1.toRingHom :=
  congrArg IdealPair.Hom.toRingHom
    ((D.homEquiv_apply C a ((D.homEquiv C a).symm t)).symm.trans
      (congrArg Subtype.val ((D.homEquiv C a).apply_symm_apply t)))

/-- The base-change divided power morphism agrees with the two maps out of the base ring. -/
private lemma baseChangeDPMorphism_comp_algebraMap (f : A →+* B) (g : B →+* B')
    (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A (g.comp f) (J.map g)
      (map_baseIdeal_le_map f g J hJ)) :
    (baseChangeDPMorphism f g J hJ D D').toRingHom.comp D.algebraMap.toRingHom =
      D'.algebraMap.toRingHom.comp g := by
  unfold baseChangeDPMorphism
  exact homEquiv_symm_comp_algebraMap f J hJ D D'.object D'.structureMap _

/-- The ring map induced by the canonical divided power map and the map from the new base. -/
private noncomputable def baseChangeTensorRingHom [Algebra B B']
    (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ) [Algebra B D.object]
    (hDalg : algebraMap B D.object = D.algebraMap.toRingHom)
    (D' : DividedPowerEnvelope A ((algebraMap B B').comp f)
      (J.map (algebraMap B B'))
      (map_baseIdeal_le_map f (algebraMap B B') J hJ)) :
    (D.object ⊗[B] B') →+* D'.object := by
  let : Algebra B' D'.object := D'.algebraMap.toRingHom.toAlgebra
  let : Algebra B D'.object :=
    (D'.algebraMap.toRingHom.comp (algebraMap B B')).toAlgebra
  let : IsScalarTower B B' D'.object := IsScalarTower.of_algebraMap_eq' rfl
  let δ := baseChangeDPMorphism f (algebraMap B B') J hJ D D'
  let φ : D.object →ₐ[B] D'.object :=
    { toRingHom := δ.toRingHom
      commutes' := fun b => by
        change δ.toRingHom (algebraMap B D.object b) = algebraMap B D'.object b
        have hb := congrArg (fun k : B →+* D'.object => k b)
          (baseChangeDPMorphism_comp_algebraMap f (algebraMap B B') J hJ D D')
        calc
          δ (algebraMap B D.object b) =
              δ (D.algebraMap.toRingHom b) := by rw [hDalg]
          _ = D'.algebraMap.toRingHom (algebraMap B B' b) := by
            simpa only [δ, RingHom.comp_apply,
              DividedPowers.DPMorphism.toRingHom_apply] using hb
          _ = algebraMap B D'.object b := rfl }
  exact (Algebra.TensorProduct.lift φ
    (IsScalarTower.toAlgHom B B' D'.object) (fun _ _ => Commute.all _ _)).toRingHom

/-- On pure tensors the canonical tensor map is multiplication of the two structural images. -/
private lemma baseChangeTensorRingHom_tmul [Algebra B B']
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ) [Algebra B D.object]
    (hDalg : algebraMap B D.object = D.algebraMap.toRingHom)
    (D' : DividedPowerEnvelope A ((algebraMap B B').comp f)
      (J.map (algebraMap B B'))
      (map_baseIdeal_le_map f (algebraMap B B') J hJ))
    (x : D.object) (y : B') :
    baseChangeTensorRingHom f J hJ D hDalg D' (TensorProduct.tmul B x y) =
      (baseChangeDPMorphism f (algebraMap B B') J hJ D D').toRingHom x *
        D'.algebraMap.toRingHom y := by
  let : Algebra B' D'.object := D'.algebraMap.toRingHom.toAlgebra
  have halg : algebraMap B' D'.object = D'.algebraMap.toRingHom := rfl
  simp [baseChangeTensorRingHom, Algebra.TensorProduct.lift_tmul,
    RingHom.toAlgebra, halg]

/-- Morphisms out of a divided power envelope agree when they agree on its two
structural maps. -/
private lemma envelopeDPMorphism_ext {A : DividedPowerRing.{v}}
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) (D : DividedPowerEnvelope A f J hJ)
    (C : DividedPowerRing.{max u v})
    (a : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers)
    (p q : DividedPowers.DPMorphism D.object.dividedPowers C.dividedPowers)
    (hpA : p.comp D.structureMap = a) (hqA : q.comp D.structureMap = a)
    (hpB : p.toRingHom.comp D.algebraMap.toRingHom =
      q.toRingHom.comp D.algebraMap.toRingHom) : p = q := by
  let e := D.homEquiv C a
  have he : e ⟨p, hpA⟩ = e ⟨q, hqA⟩ := by
    apply Subtype.ext
    show (e ⟨p, hpA⟩).1 = (e ⟨q, hqA⟩).1
    rw [D.homEquiv_apply C a ⟨p, hpA⟩,
      D.homEquiv_apply C a ⟨q, hqA⟩]
    exact IdealPair.Hom.ext_toRingHom _ _ hpB
  exact congrArg Subtype.val (e.injective he)

private theorem dividedPowerEnvelope_baseChange_of_extends
    {A : DividedPowerRing.{max u v}} [Algebra B B'] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A ((algebraMap B B').comp f)
      (J.map (algebraMap B B'))
      (map_baseIdeal_le_map f (algebraMap B B') J hJ))
    (hExt : letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
      DividedPowers.Extends D.object.dividedPowers
        (algebraMap D.object (D.object ⊗[B] B'))) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    ∃ e : (D.object ⊗[B] B') ≃+* D'.object,
      ∀ x y, e (TensorProduct.tmul B x y) =
        (baseChangeDPMorphism f (algebraMap B B') J hJ D D').toRingHom x *
          D'.algebraMap.toRingHom y := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  let ι : D.object →+* D.object ⊗[B] B' :=
    algebraMap D.object (D.object ⊗[B] B')
  let κ : B' →+* D.object ⊗[B] B' :=
    (Algebra.TensorProduct.includeRight : B' →ₐ[B] D.object ⊗[B] B').toRingHom
  obtain ⟨δ, hδ⟩ := hExt
  let C : DividedPowerRing.{max u v} :=
    { carrier := D.object ⊗[B] B'
      ideal := D.object.ideal.map ι
      dividedPowers := δ }
  let inc : DividedPowers.DPMorphism D.object.dividedPowers C.dividedPowers :=
    { toRingHom := ι
      ideal_comp := hδ.1
      dpow_comp := hδ.2 }
  let a : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers :=
    inc.comp D.structureMap
  have hικ : κ.comp (algebraMap B B') =
      ι.comp D.algebraMap.toRingHom := by
    show Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap B B') =
      Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap B D.object)
    exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
  have hκ : (J.map (algebraMap B B')).map κ ≤ C.ideal := by
    show (J.map (algebraMap B B')).map κ ≤ D.object.ideal.map ι
    rw [Ideal.map_map, hικ, ← Ideal.map_map]
    exact Ideal.map_mono D.algebraMap.ideal_comp
  let p : IdealPair.Hom (J.map (algebraMap B B')) C.ideal :=
    IdealPair.Hom.ofRingHom κ hκ
  have hp : IdealPair.Hom.comp p
      (IdealPair.Hom.ofRingHom ((algebraMap B B').comp f)
        (map_baseIdeal_le_map f (algebraMap B B') J hJ)) =
      IdealPair.Hom.ofDPMorphism a := by
    apply IdealPair.Hom.ext_toRingHom
    apply RingHom.ext
    intro x
    show κ (algebraMap B B' (f x)) = ι (D.structureMap x)
    have hx := congrArg (fun h : B →+* D.object ⊗[B] B' => h (f x)) hικ
    have hstr := congrArg (fun h : A →+* D.object => h x) D.algebraMap_comp
    change D.algebraMap.toRingHom (f x) = D.structureMap.toRingHom x at hstr
    show κ (algebraMap B B' (f x)) = ι (D.structureMap.toRingHom x)
    exact hx.trans (congrArg ι hstr)
  let q : DividedPowers.DPMorphism D'.object.dividedPowers C.dividedPowers :=
    ((D'.homEquiv C a).symm ⟨p, hp⟩).1
  have hqA : q.comp D'.structureMap = a :=
    ((D'.homEquiv C a).symm ⟨p, hp⟩).2
  have hqB : q.toRingHom.comp D'.algebraMap.toRingHom = κ :=
    homEquiv_symm_comp_algebraMap _ _ _ D' C a ⟨p, hp⟩
  let r : (D.object ⊗[B] B') →+* D'.object :=
    baseChangeTensorRingHom f J hJ D rfl D'
  let δCanon := baseChangeDPMorphism f (algebraMap B B') J hJ D D'
  have hrι : r.comp ι = δCanon.toRingHom := by
    apply RingHom.ext
    intro x
    show r (x ⊗ₜ[B] 1) = δCanon.toRingHom x
    have hx := baseChangeTensorRingHom_tmul f J hJ D rfl D' x 1
    simpa only [r, δCanon, map_one, mul_one] using hx
  have hrDP : δ.IsDPMorphism D'.object.dividedPowers r :=
    DividedPowers.IsDPMorphism.of_comp D.object.dividedPowers δ
      D'.object.dividedPowers ι r rfl hδ (by rw [hrι]; exact δCanon.isDPMorphism)
  let rDP : DividedPowers.DPMorphism C.dividedPowers D'.object.dividedPowers :=
    { toRingHom := r
      ideal_comp := hrDP.1
      dpow_comp := hrDP.2 }
  have hqδ : q.comp δCanon = inc := by
    apply envelopeDPMorphism_ext f J hJ D C a
    · calc
        (q.comp δCanon).comp D.structureMap =
            q.comp (δCanon.comp D.structureMap) := rfl
        _ = q.comp D'.structureMap := by
          rw [baseChangeDPMorphism_comp_structureMap]
        _ = a := hqA
    · rfl
    · show q.toRingHom.comp
          (δCanon.toRingHom.comp D.algebraMap.toRingHom) =
          ι.comp D.algebraMap.toRingHom
      rw [baseChangeDPMorphism_comp_algebraMap, ← RingHom.comp_assoc, hqB]
      exact hικ
  have hrκ : r.comp κ = D'.algebraMap.toRingHom := by
    apply RingHom.ext
    intro y
    show r (1 ⊗ₜ[B] y) = D'.algebraMap.toRingHom y
    have hy := baseChangeTensorRingHom_tmul f J hJ D rfl D' 1 y
    simpa only [r, map_one, one_mul] using hy
  have hqr : q.toRingHom.comp r = RingHom.id _ := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext x
      exact (congrArg q.toRingHom (RingHom.congr_fun hrι x)).trans
        (RingHom.congr_fun (congrArg DividedPowers.DPMorphism.toRingHom hqδ) x)
    · ext y
      exact (congrArg q.toRingHom (RingHom.congr_fun hrκ y)).trans (RingHom.congr_fun hqB y)
  have hrinc : rDP.comp inc = δCanon := by
    apply DividedPowers.DPMorphism.ext
    funext x
    have hx := congrArg (fun t : D.object →+* D'.object => t x) hrι
    exact hx
  have hrqDP : rDP.comp q = DividedPowers.DPMorphism.id D'.object.dividedPowers := by
    apply envelopeDPMorphism_ext ((algebraMap B B').comp f)
      (J.map (algebraMap B B'))
      (map_baseIdeal_le_map f (algebraMap B B') J hJ)
      D' D'.object D'.structureMap
    · calc
        (rDP.comp q).comp D'.structureMap =
            rDP.comp (q.comp D'.structureMap) := rfl
        _ = rDP.comp a := by rw [hqA]
        _ = (rDP.comp inc).comp D.structureMap := rfl
        _ = δCanon.comp D.structureMap := by rw [hrinc]
        _ = D'.structureMap :=
          baseChangeDPMorphism_comp_structureMap f (algebraMap B B') J hJ D D'
    · rfl
    · apply RingHom.ext
      intro y
      show r (q.toRingHom (D'.algebraMap.toRingHom y)) =
        D'.algebraMap.toRingHom y
      have hqy := congrArg (fun t : B' →+* D.object ⊗[B] B' => t y) hqB
      change q.toRingHom (D'.algebraMap.toRingHom y) = κ y at hqy
      rw [hqy]
      have hry := congrArg (fun t : B' →+* D'.object => t y) hrκ
      exact hry
  have hrq : r.comp q.toRingHom = RingHom.id D'.object := by
    have h := congrArg DividedPowers.DPMorphism.toRingHom hrqDP
    exact h
  refine ⟨RingEquiv.ofRingHom r q.toRingHom hrq hqr, ?_⟩
  intro x y
  exact baseChangeTensorRingHom_tmul f J hJ D rfl D' x y

/-- A divided power envelope commutes with base change when the base change is flat modulo the
base divided power ideal and its first Tor with that quotient vanishes. -/
@[stacks 07HD]
public theorem dividedPowerEnvelope_baseChange [Algebra B B'] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A ((algebraMap B B').comp f)
      (J.map (algebraMap B B'))
      (map_baseIdeal_le_map f (algebraMap B B') J hJ))
    (hflat : Module.Flat (B ⧸ (A.ideal.map f))
      (B' ⧸ ((A.ideal.map f).map (algebraMap B B'))))
    (hTor : IsZero (((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B B')).obj
      (ModuleCat.of B (B ⧸ (A.ideal.map f))))) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    ∃ e : (D.object ⊗[B] B') ≃+* D'.object,
      ∀ x y, e (TensorProduct.tmul B x y) =
        (baseChangeDPMorphism f (algebraMap B B') J hJ D D').toRingHom x *
          D'.algebraMap.toRingHom y := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  exact dividedPowerEnvelope_baseChange_of_extends f J hJ D D'
    (envelope_tensor_extends f J hJ D hflat hTor)

end BaseChange

end Crystalline

end
