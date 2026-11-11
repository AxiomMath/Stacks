module

public import StacksFrontier.AlgebraicGeometry.DeRham.FormsTensorWedge

/-!
# Local sections of the twisted de Rham terms `ℱ ⊗ Ω^q_{Y/S}`

Elementary identities for the local sections of the sheaves `ℱ ⊗_{𝒪_Y} Ω_{Y/S}` and
`ℱ ⊗_{𝒪_Y} Ω^q_{Y/S}` attached to a morphism of schemes `f : Y ⟶ S` and a sheaf of
`𝒪_Y`-modules `ℱ`, which the construction of twisted de Rham differentials consumes: local pure
tensors are additive in each factor, vanish on a zero factor and commute with restriction; the
relative exterior product `α ∧ ω` is additive and linear in the form and is the degree-one
generator on the unit form; the twisted wedge pairing is linear in its first argument; the
relative de Rham differential on local sections is additive and commutes with restriction.

## Main results

Everything lives in the namespace `AlgebraicGeometry.Scheme.Hom`.

* `twistedTmul_add_left`, `twistedTmul_add_right`, `twistedTmul_zero`, `twistedTmul_restrict`,
  `connectionTmul_add_left`, `connectionTmul_zero` — local pure tensors.
* `relativeExteriorProduct_add_right`, `relativeExteriorProduct_smul_right`,
  `relativeExteriorProduct_one` — the relative exterior product in its second argument.
* `twistedFormsWedgeSection_smul_left` — the twisted wedge pairing is `𝒪_Y`-linear in the value
  of the connection.
* `relativeDeRhamDifferentialSection_add`, `relativeDeRhamDifferentialSection_restrict` — the
  relative de Rham differential on local sections.
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

noncomputable section

namespace Stacks.PullbackTensorCoherence

/-- A local pure tensor in a tensor product sheaf is linear in its first factor. -/
theorem tmul_smul_left {Z : RingedSpace.{u, u}}
    {A B : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z)}
    (U : (TopologicalSpace.Opens Z.carrier)ᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf Z).obj.obj U) (a : A.val.obj U) (b : B.val.obj U) :
    letI := Stacks.PullbackGradedAlgebra.monoidalCategory Z
    Stacks.PullbackTensorCoherence.tmul Z A B U (r • a) b =
      r • Stacks.PullbackTensorCoherence.tmul Z A B U a b := by
  unfold Stacks.PullbackTensorCoherence.tmul
  rw [← TensorProduct.smul_tmul']
  exact map_smul _ _ _

end Stacks.PullbackTensorCoherence

namespace AlgebraicGeometry.Scheme.Hom



/-- A pure tensor of local sections in a sheafified tensor product is additive in the first
factor. -/
theorem toTensorSheafSection_add_tmul (X : RingedSpace.{u, u})
    (A B : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (a a' : A.val.obj U) (β : B.val.obj U) :
    toTensorSheafSection X A B U ((a + a') ⊗ₜ[X.presheaf.obj U] β) =
      toTensorSheafSection X A B U (a ⊗ₜ[X.presheaf.obj U] β) +
        toTensorSheafSection X A B U (a' ⊗ₜ[X.presheaf.obj U] β) := by
  simp only [toTensorSheafSection_eq_sheafifyUnit, TensorProduct.add_tmul]
  exact map_add _ _ _

/-- Pure tensors of local sections in `ℱ ⊗ Ω_{Y/S}` are additive in the coefficient factor. -/
theorem connectionTmul_add_left {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules)
    (U : (Y.Opens)ᵒᵖ) (s s' : M.val.obj U) (α : (relativeDifferentials f).val.obj U) :
    connectionTmul f M U (s + s') α = connectionTmul f M U s α + connectionTmul f M U s' α :=
  toTensorSheafSection_add_tmul Y.toRingedSpace M (relativeDifferentials f) U s s' α

/-- Pure tensors in `ℱ ⊗ Ω^q_{Y/S}` are additive in the coefficient factor. -/
theorem twistedTmul_add_left {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) (q : ℕ)
    (U : (Y.Opens)ᵒᵖ) (s s' : M.val.obj U) (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    twistedTmul f M q U (s + s') ω = twistedTmul f M q U s ω + twistedTmul f M q U s' ω :=
  toTensorSheafSection_add_tmul Y.toRingedSpace M (relativeDifferentialForms f (q : ℤ)) U s s' ω

/-- Pure tensors in `ℱ ⊗ Ω^q_{Y/S}` are additive in the form factor. -/
theorem twistedTmul_add_right {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) (q : ℕ)
    (U : (Y.Opens)ᵒᵖ) (s : M.val.obj U) (ω ω' : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    twistedTmul f M q U s (ω + ω') = twistedTmul f M q U s ω + twistedTmul f M q U s ω' :=
  toTensorSheafSection_tmul_add Y.toRingedSpace M (relativeDifferentialForms f (q : ℤ)) U s ω ω'

/-- Pure tensors in `ℱ ⊗ Ω^q_{Y/S}` commute with restriction. -/
theorem twistedTmul_restrict {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) (q : ℕ)
    {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V) (s : M.val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (twistedForms f M q).val.map k (twistedTmul f M q U s ω) =
      twistedTmul f M q V (M.val.map k s) ((relativeDifferentialForms f (q : ℤ)).val.map k ω) :=
  (PresheafOfModules.naturality_apply
    (sheafifyUnit Y.toRingedSpace
      ((PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf) (M.val)
        ((relativeDifferentialForms f (q : ℤ)).val)))) k
    (s ⊗ₜ[Y.presheaf.obj U] ω)).symm

/-- The relative de Rham differential on sections commutes with restriction. -/
theorem relativeDeRhamDifferentialSection_restrict {Y S : Scheme.{u}} (f : Y ⟶ S) (q : ℕ)
    {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V) (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).val.map k
        (relativeDeRhamDifferentialSection f q U ω) =
      relativeDeRhamDifferentialSection f q V ((relativeDifferentialForms f (q : ℤ)).val.map k ω) :=
  (PresheafOfModules.naturality_apply ((deRhamComplex f).d q (q + 1)).val k ω).symm

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory in
/-- The twisted wedge pairing is linear in the value of the connection. -/
theorem twistedFormsWedgeSection_smul_left {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) (q : ℕ)
    (U : (Y.Opens)ᵒᵖ) (c : Y.ringCatSheaf.obj.obj U)
    (η : (moduleConnectionTarget f M).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    twistedFormsWedgeSection f M q U (c • η) ω = c • twistedFormsWedgeSection f M q U η ω :=
  (congrArg ((twistedFormsWedge f M q).val.app U)
    (Stacks.PullbackTensorCoherence.tmul_smul_left (A := modulesOnRing M ⊗ differentialsOnRing f)
        (B := formsOnRing f q) U c η ω)).trans
    (map_smul _ _ _)

/-- A pure tensor in `ℱ ⊗ Ω_{Y/S}` with the zero differential vanishes. -/
theorem connectionTmul_zero {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules)
    (U : (Y.Opens)ᵒᵖ) (s : M.val.obj U) : connectionTmul f M U s 0 = 0 := by
  have h := connectionTmul_add_right f M U s 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm


variable {Y S : Scheme.{u}} (f : Y ⟶ S)



/-- The relative exterior product is additive in the form. -/
theorem relativeExteriorProduct_add_right (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (α : (relativeDifferentials f).val.obj U)
    (ω ω' : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    relativeExteriorProduct f q U α (ω + ω') =
      relativeExteriorProduct f q U α ω + relativeExteriorProduct f q U α ω' :=
  (congrArg (transportDifferentialForm f _ U)
      (map_add (((relativeDifferentialFormsAlgebra f).mul 1 (q : ℤ)).app U
        ((Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U α)) ω ω')).trans
    (transportDifferentialForm_add f _ U _ _)

/-- The relative exterior product vanishes on the zero form. -/
theorem relativeExteriorProduct_zero_right (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (α : (relativeDifferentials f).val.obj U) :
    relativeExteriorProduct f q U α 0 = 0 := by
  have h := relativeExteriorProduct_add_right f q U α 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

/-- The relative exterior product is linear in the form. -/
theorem relativeExteriorProduct_smul_right (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (r : Y.ringCatSheaf.obj.obj U) (α : (relativeDifferentials f).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    relativeExteriorProduct f q U α (r • ω) = r • relativeExteriorProduct f q U α ω :=
  (congrArg (transportDifferentialForm f _ U)
      (((relativeDifferentialFormsAlgebra f).mul 1 (q : ℤ)).map_smul_right U r _ ω)).trans
    (transportDifferentialForm_smul f _ U r _)

/-- The relative de Rham differential on sections is additive. -/
theorem relativeDeRhamDifferentialSection_add (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (ω ω' : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    relativeDeRhamDifferentialSection f q U (ω + ω') =
      relativeDeRhamDifferentialSection f q U ω + relativeDeRhamDifferentialSection f q U ω' :=
  map_add (((deRhamComplex f).d q (q + 1)).val.app U).hom ω ω'

/-- The relative de Rham differential on sections vanishes at zero. -/
theorem relativeDeRhamDifferentialSection_zero (q : ℕ) (U : (Y.Opens)ᵒᵖ) :
    relativeDeRhamDifferentialSection f q U 0 = 0 :=
  map_zero (((deRhamComplex f).d q (q + 1)).val.app U).hom

/-- The relative de Rham differential on sections commutes with integer multiples. -/
theorem relativeDeRhamDifferentialSection_zsmul (q : ℕ) (U : (Y.Opens)ᵒᵖ) (n : ℤ)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    relativeDeRhamDifferentialSection f q U (n • ω) = n • relativeDeRhamDifferentialSection f q U ω
        :=
  map_zsmul (((deRhamComplex f).d q (q + 1)).val.app U).hom n ω

/-- A pure tensor in `ℱ ⊗ Ω^q_{Y/S}` with the zero form vanishes. -/
theorem twistedTmul_zero (q : ℕ) (U : (Y.Opens)ᵒᵖ) (M : Y.Modules) (m : M.val.obj U) :
    twistedTmul f M q U m 0 = 0 := by
  have h := toTensorSheafSection_tmul_add Y.toRingedSpace M
    (relativeDifferentialForms f (q : ℤ)) U m 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

/-- The relative exterior product with the unit form is the degree-one generator. -/
theorem relativeExteriorProduct_one (U : (Y.Opens)ᵒᵖ) (a : (relativeDifferentials f).val.obj U) :
    relativeExteriorProduct f 0 U a ((relativeDifferentialFormsAlgebra f).one.eval U) =
      (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U a :=
  eq_of_heq ((transportDifferentialForm_heq f _ U _).trans
    ((relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.mul_one 1 U _))

end AlgebraicGeometry.Scheme.Hom

end

end
