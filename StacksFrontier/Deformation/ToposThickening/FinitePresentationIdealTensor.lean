module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationHomMono
public import StacksFrontier.Deformation.ToposThickening.FinitePresentationFlatLift
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# Finite presentation across a first order thickening, from a local injectivity of the ideal

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I = Ker(O' ⟶ i_*O)`, and let `ℱ'` be an `O'`-module.  The argument of Stacks 08VU shows
that `ℱ'` is of finite presentation as soon as `i^*ℱ'` is, once the action `I ⊗_{O'} ℱ' ⟶ ℱ'` is
injective; Stacks 08VU obtains that injectivity from flatness over a base through Stacks 08MQ.

This file isolates the input in the following local form: whenever sections `ε_j` of `I` and
`s_j` of `ℱ'` over an object `W` satisfy `∑ ε_j s_j = 0`, the tensor `∑ ε_j ⊗ s_j` of the
sections vanishes on a covering of `W`.

## Main results

* `Deformation.ToposThickening.mono_multiplicationMap_of_idealTensor`: the local form of the
  injectivity makes the action map `I ⊗_{O'} ℱ' ⟶ ℱ'` a monomorphism.
* `Deformation.ToposThickening.isFinitePresentation_iff_pullbackModules_of_idealTensor`: under
  it, `ℱ'` is of finite presentation if and only if `i^*ℱ'` is.

## Implementation notes

The sections of the ideal are written as elements of the kernel of the structure map over `W`,
an ideal of `O'(W)`, so that the tensor products are tensor products of modules over the one
ring `O'(W)`.  The square-zero ideal `I` of `Deformation.ToposThickening.FirstOrderThickening`
is identified with that kernel on sections by its inclusion, which is injective with image the
kernel (`kernelSectionEquiv`).

## References

* [Stacks Project, Tag 08VU](https://stacks.math.columbia.edu/tag/08VU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.LocalGeneration
open scoped TensorProduct
open Stacks.SheafOfModules.FlatSquareZero (ringMap multiplicationMap multiplicationPresheafMap)

universe v u v' u' w

namespace Deformation.ToposThickening

section Kernel

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The restriction of a section of the kernel of the structure map along a map of the site. -/
def kernelRestr (i : RingedToposHom X Y) {U V : Y.Cᵒᵖ} (g : U ⟶ V)
    (a : RingHom.ker (i.fSharp.hom.app U).hom) : RingHom.ker (i.fSharp.hom.app V).hom :=
  ⟨Y.O.obj.map g a, by
    rw [RingHom.mem_ker]
    have h := congrArg (fun φ => φ a) (congrArg CommRingCat.Hom.hom (i.fSharp.hom.naturality g))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
    rw [h, a.2, map_zero]⟩

/-- The underlying section of `kernelRestr i g a` is the restriction of `a` along `g`. -/
@[simp]
lemma kernelRestr_coe (i : RingedToposHom X Y) {U V : Y.Cᵒᵖ} (g : U ⟶ V)
    (a : RingHom.ker (i.fSharp.hom.app U).hom) :
    (kernelRestr i g a : Y.O.obj.obj V) = Y.O.obj.map g a :=
  rfl

/-- The inclusion of the square-zero ideal of a first order thickening, on sections over `U`,
corestricted to the kernel of the structure map over `U`. -/
noncomputable def kernelSectionMap {i : RingedToposHom X Y} (hi : FirstOrderThickening i)
    (U : Y.Cᵒᵖ) :
    ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val.obj U →ₗ[Y.O.obj.obj U]
      RingHom.ker (i.fSharp.hom.app U).hom where
  toFun a := ⟨hi.incl.val.app U a, (hi.kernel U _).2 ⟨a, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add (hi.incl.val.app U).hom a b)
  map_smul' r a := Subtype.ext (map_smul (hi.incl.val.app U).hom
    (show (ringSheaf Y.O).obj.obj U from r) a)

/-- Restricting a section of the kernel twice is restricting it along the composite. -/
lemma kernelRestr_kernelRestr (i : RingedToposHom X Y) {U V W : Y.Cᵒᵖ} (g : U ⟶ V) (g' : V ⟶ W)
    (a : RingHom.ker (i.fSharp.hom.app U).hom) :
    kernelRestr i g' (kernelRestr i g a) = kernelRestr i (g ≫ g') a :=
  Subtype.ext (by
    change Y.O.obj.map g' (Y.O.obj.map g a) = Y.O.obj.map (g ≫ g') a
    rw [Functor.map_comp, CommRingCat.comp_apply])

/-- The square-zero ideal of a first order thickening is, on sections over `U`, the kernel of
the structure map over `U`: its inclusion is injective with image that kernel. -/
noncomputable def kernelSectionEquiv {i : RingedToposHom X Y} (hi : FirstOrderThickening i)
    (U : Y.Cᵒᵖ) :
    ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val.obj U ≃ₗ[Y.O.obj.obj U]
      RingHom.ker (i.fSharp.hom.app U).hom :=
  LinearEquiv.ofBijective (kernelSectionMap hi U)
    ⟨fun a b h => hi.injective U (congrArg Subtype.val h), fun c => by
      obtain ⟨a, ha⟩ := (hi.kernel U (c : Y.O.obj.obj U)).1 c.2
      exact ⟨a, Subtype.ext ha⟩⟩

/-- The underlying section of `kernelSectionEquiv hi U a` is the image of `a` under the inclusion
of the ideal. -/
lemma kernelSectionEquiv_apply_coe {i : RingedToposHom X Y} (hi : FirstOrderThickening i)
    (U : Y.Cᵒᵖ) (a : ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val.obj U) :
    (kernelSectionEquiv hi U a : Y.O.obj.obj U) = hi.incl.val.app U a :=
  rfl

/-- The identification of the ideal with the kernel commutes with restriction. -/
lemma kernelSectionEquiv_restr {i : RingedToposHom X Y} (hi : FirstOrderThickening i)
    {U V : Y.Cᵒᵖ} (g : U ⟶ V)
    (a : ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val.obj U) :
    kernelSectionEquiv hi V
        (restr ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I) g a) =
      kernelRestr i g (kernelSectionEquiv hi U a) := by
  apply Subtype.ext
  rw [kernelSectionEquiv_apply_coe, kernelRestr_coe, kernelSectionEquiv_apply_coe]
  exact PresheafOfModules.naturality_apply hi.incl.val g a

end Kernel

section Main

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [Y.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Restriction carries a relation with coefficients in the kernel to the restricted relation. -/
lemma sum_kernelRestr_smul_restr (i : RingedToposHom X Y) (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {U V : Y.Cᵒᵖ} (g : U ⟶ V) {n : ℕ} (ε : Fin n → RingHom.ker (i.fSharp.hom.app U).hom)
    (s : Fin n → F'.val.obj U)
    (h : ∑ j, (show (ringSheaf Y.O).obj.obj U from (ε j : Y.O.obj.obj U)) • s j = 0) :
    ∑ j, (show (ringSheaf Y.O).obj.obj V from (kernelRestr i g (ε j) : Y.O.obj.obj V)) •
      restr F' g (s j) = 0 := by
  have h' := congrArg (F'.val.map g).hom h
  rw [map_sum, map_zero] at h'
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h'
  exact (F'.val.map_smul g _ (s j)).symm

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [Y.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A vanishing tensor of a kernel tuple with a tuple of sections stays zero after restriction. -/
lemma sum_kernelRestr_tmul_restr_eq_zero (i : RingedToposHom X Y)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) {U V W : Y.Cᵒᵖ} (g : U ⟶ V) (g' : V ⟶ W) {n : ℕ}
    (ε : Fin n → RingHom.ker (i.fSharp.hom.app U).hom) (s : Fin n → F'.val.obj U)
    (h : ∑ j, kernelRestr i g (ε j) ⊗ₜ[Y.O.obj.obj V] restr F' g (s j) = 0) :
    ∑ j, kernelRestr i (g ≫ g') (ε j) ⊗ₜ[Y.O.obj.obj W] restr F' (g ≫ g') (s j) = 0 := by
  let Φ : (RingHom.ker (i.fSharp.hom.app V).hom ⊗[Y.O.obj.obj V] F'.val.obj V) →+
      (RingHom.ker (i.fSharp.hom.app W).hom ⊗[Y.O.obj.obj W] F'.val.obj W) :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun a => AddMonoidHom.mk'
        (fun x => kernelRestr i g' a ⊗ₜ[Y.O.obj.obj W] restr F' g' x)
        (fun x x' => (congrArg (kernelRestr i g' a ⊗ₜ[Y.O.obj.obj W] ·)
          (show restr F' g' (x + x') = restr F' g' x + restr F' g' x' from
            map_add (F'.val.map g').hom x x')).trans
          (TensorProduct.tmul_add _ _ _)))
        (fun a a' => AddMonoidHom.ext fun x =>
          (congrArg (· ⊗ₜ[Y.O.obj.obj W] restr F' g' x) (Subtype.ext (map_add (Y.O.obj.map g').hom
            (a : Y.O.obj.obj V) a') : kernelRestr i g' (a + a') =
              kernelRestr i g' a + kernelRestr i g' a')).trans (TensorProduct.add_tmul _ _ _)))
      (fun r a x => by
        have h1 : kernelRestr i g' (r • a) = (Y.O.obj.map g' r) • kernelRestr i g' a :=
          Subtype.ext (map_mul (Y.O.obj.map g').hom _ _)
        have h2 : restr F' g' (r • x) = (Y.O.obj.map g' r) • restr F' g' x :=
          F'.val.map_smul g' (show (ringSheaf Y.O).obj.obj V from r) x
        change kernelRestr i g' (r • a) ⊗ₜ[Y.O.obj.obj W] restr F' g' x =
          kernelRestr i g' a ⊗ₜ[Y.O.obj.obj W] restr F' g' (r • x)
        rw [h1, h2]
        exact TensorProduct.smul_tmul _ _ _)
  have h' := congrArg Φ h
  rw [map_zero, map_sum] at h'
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h'
  change _ = kernelRestr i g' (kernelRestr i g (ε j)) ⊗ₜ[Y.O.obj.obj W]
    restr F' g' (restr F' g (s j))
  rw [kernelRestr_kernelRestr, restr_restr]

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [Y.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The two spellings of the scalar action of the structure sheaf on the sections of a module
agree. -/
lemma sum_kernel_smul_eq_zero_iff (i : RingedToposHom X Y) (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {U : Y.Cᵒᵖ} {n : ℕ} (ε : Fin n → RingHom.ker (i.fSharp.hom.app U).hom)
    (s : Fin n → F'.val.obj U) :
    ∑ j, (show (ringSheaf Y.O).obj.obj U from (ε j : Y.O.obj.obj U)) • s j = 0 ↔
      ∑ j, (ε j : Y.O.obj.obj U) • s j = 0 :=
  Iff.rfl

/-- The sieve of the morphisms along which a tensor of a kernel tuple with a tuple of sections
vanishes. -/
noncomputable def kernelTensorVanishingSieve (i : RingedToposHom X Y)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) {W : Y.C} {n : ℕ}
    (ε : Fin n → RingHom.ker (i.fSharp.hom.app (op W)).hom) (s : Fin n → F'.val.obj (op W)) :
    Sieve W where
  arrows W' g := ∑ j, kernelRestr i g.op (ε j) ⊗ₜ[Y.O.obj.obj (op W')] restr F' g.op (s j) = 0
  downward_closed {W' W''} g hg k := by
    rw [op_comp]
    exact sum_kernelRestr_tmul_restr_eq_zero i F' g.op k.op ε s hg

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [Y.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A composite lies in the vanishing sieve as soon as the tensor of the restricted tuples
vanishes. -/
lemma comp_mem_kernelTensorVanishingSieve (i : RingedToposHom X Y)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) {W W₁ W₂ : Y.C} {n : ℕ}
    (ε : Fin n → RingHom.ker (i.fSharp.hom.app (op W)).hom) (s : Fin n → F'.val.obj (op W))
    (a : W₁ ⟶ W) (g : W₂ ⟶ W₁)
    (h : ∑ j, kernelRestr i g.op (kernelRestr i a.op (ε j)) ⊗ₜ[Y.O.obj.obj (op W₂)]
      restr F' g.op (restr F' a.op (s j)) = 0) :
    kernelTensorVanishingSieve i F' ε s (g ≫ a) := by
  change ∑ j, kernelRestr i (g ≫ a).op (ε j) ⊗ₜ[Y.O.obj.obj (op W₂)]
    restr F' (g ≫ a).op (s j) = 0
  rw [op_comp]
  simpa only [kernelRestr_kernelRestr, restr_restr] using h

/-- **The local injectivity of the action of the square-zero ideal.**  Sections `ε_j` of the
kernel of the structure map and `s_j` of `ℱ'` over `W` with `∑ ε_j s_j = 0` have a tensor
`∑ ε_j ⊗ s_j` that vanishes on a covering of `W`. -/
def IdealTensorLocallyVanishes (i : RingedToposHom X Y) (F' : SheafOfModules.{w} (ringSheaf Y.O)) :
    Prop :=
  ∀ (W : Y.C) (n : ℕ) (ε : Fin n → RingHom.ker (i.fSharp.hom.app (op W)).hom)
    (s : Fin n → F'.val.obj (op W)),
    ∑ j, (show (ringSheaf Y.O).obj.obj (op W) from (ε j : Y.O.obj.obj (op W))) • s j = 0 →
    ∃ R : Sieve W, R ∈ Y.J W ∧ ∀ (W' : Y.C) (g : W' ⟶ W), R g →
      ∑ j, kernelRestr i g.op (ε j) ⊗ₜ[Y.O.obj.obj (op W')] restr F' g.op (s j) = 0

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify X.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The action of the square-zero ideal is a monomorphism** when it is locally injective in the
sense of `Deformation.ToposThickening.IdealTensorLocallyVanishes`. -/
theorem mono_multiplicationMap_of_idealTensor {i : RingedToposHom X Y}
    (hi : FirstOrderThickening i) (F' : SheafOfModules.{w} (ringSheaf Y.O))
    (hloc : IdealTensorLocallyVanishes i F') :
    Mono (multiplicationMap i.fSharp hi.I F' hi.incl) := by
  unfold multiplicationMap
  apply PresheafOfModules.mono_sheafificationHomEquiv_symm_of_locally_eq_zero
  intro U x hx
  obtain ⟨n, a, s, hxs⟩ := TensorProduct.exists_sum_tmul_eq x
  let ε : Fin n → RingHom.ker (i.fSharp.hom.app U).hom := fun j => kernelSectionEquiv hi U (a j)
  have hε : ∑ j, (show (ringSheaf Y.O).obj.obj U from (ε j : Y.O.obj.obj U)) • s j = 0 := by
    rw [hxs] at hx
    exact (map_sum ((multiplicationPresheafMap i.fSharp hi.I F' hi.incl).app U).hom
      (fun j => a j ⊗ₜ s j) Finset.univ).symm.trans hx
  obtain ⟨R, hR, hR'⟩ := hloc U.unop n ε s hε
  refine ⟨R, hR, fun V g hg => ?_⟩
  have h0 := congrArg (LinearMap.rTensor (F'.val.obj (op V))
    (kernelSectionEquiv hi (op V)).symm.toLinearMap) (hR' V g hg)
  rw [map_zero, map_sum] at h0
  rw [hxs]
  refine (map_sum (((PresheafOfModulesOfCommRing.Monoidal.tensorObj
    ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val F'.val).map g.op).hom)
      (fun j => a j ⊗ₜ s j) Finset.univ).trans ?_
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h0
  rw [LinearMap.rTensor_tmul]
  have hr : (kernelSectionEquiv hi (op V)).symm (kernelRestr i g.op (ε j)) =
      restr ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I) g.op (a j) := by
    rw [LinearEquiv.symm_apply_eq]
    exact (kernelSectionEquiv_restr hi g.op (a j)).symm
  rw [LinearEquiv.coe_toLinearMap, hr]
  rfl

/-- Under the local injectivity of the ideal action and finite presentation of `i^*ℱ'`, the sieve
of the sections admitting a presentation datum is covering. -/
private theorem inhabitedSieve_mem_of_pullbackModules_of_idealTensor
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {i : RingedToposHom X Y} (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) (hloc : IdealTensorLocallyVanishes i F')
    (hF : (i.toRingedToposModulesHom.pullbackModules.obj F').IsFinitePresentation) (U : Y.C) :
    Stacks.Topos.inhabitedSieve Y.J (fun q : ℕ × ℕ => presDataSheaf F' q.1 q.2) U ∈ Y.J U := by
  let : HasSheafify X.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : HasSheafify Y.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have hmono : Mono (multiplicationMap i.fSharp hi.I F' hi.incl) :=
    mono_multiplicationMap_of_idealTensor hi F' hloc
  have hM := isFinitePresentation_reduction_of_isFinitePresentation hi _ hF
  obtain ⟨σ, hσ⟩ := hM.exists_quasicoherentData
  refine Y.J.transitive (σ.coversTop U) _ fun V g hg => ?_
  obtain ⟨k, ⟨h⟩⟩ := hg
  have := hσ.isFinite_presentation k
  obtain ⟨n, m, sb, tb, hd⟩ :=
    exists_isPresentationData_of_presentation _ (σ.X k) (σ.presentation k)
  refine Y.J.superset_covering (fun W g' hg' => hg') ?_
  exact inhabitedSieve_mem_of_isPresentationData_reduction hi F' hmono _ _
    (isPresentationData_map hd h)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Finite presentation across a first order thickening** (the argument of Stacks 08VU).  Let
`i` be a first order thickening of ringed topoi and `ℱ'` an `O'`-module on which the action of the
square-zero ideal is locally injective in the sense of
`Deformation.ToposThickening.IdealTensorLocallyVanishes`.  Then `ℱ'` is of finite presentation if
and only if `i^*ℱ'` is. -/
theorem isFinitePresentation_iff_pullbackModules_of_idealTensor
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {i : RingedToposHom X Y} (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) (hloc : IdealTensorLocallyVanishes i F') :
    F'.IsFinitePresentation ↔
      (i.toRingedToposModulesHom.pullbackModules.obj F').IsFinitePresentation := by
  refine ⟨fun hF' => ?_, fun hF => ?_⟩
  · have := hF'
    exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso i).app F')
      (Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules i.toModulesHom F')
  · refine Stacks.SheafOfModules.isFinitePresentation_of_locally_isPresentationData F'
      fun U => ?_
    refine ⟨_, inhabitedSieve_mem_of_pullbackModules_of_idealTensor hi F' hloc hF U,
      fun V g hg => ?_⟩
    obtain ⟨q, ⟨p⟩⟩ := hg
    exact ⟨q.1, q.2, _, _, p.property⟩

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Finite presentation on the site descends across a first order thickening**: under the
local injectivity of the action of the square-zero ideal, if `i^*ℱ'` is of finite presentation
then `ℱ'` is of finite presentation on the site in the covering-family sense of
`SheafOfModules.IsFinitePresentationOnSite`. -/
theorem isFinitePresentationOnSite_of_pullbackModules_of_idealTensor
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {i : RingedToposHom X Y} (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) (hloc : IdealTensorLocallyVanishes i F')
    (hF : (i.toRingedToposModulesHom.pullbackModules.obj F').IsFinitePresentation) :
    F'.IsFinitePresentationOnSite := by
  refine ⟨fun U => ?_⟩
  have hU := inhabitedSieve_mem_of_pullbackModules_of_idealTensor hi F' hloc hF U
  refine ⟨Σ V : Y.C, {g : V ⟶ U //
      Stacks.Topos.inhabitedSieve Y.J (fun q : ℕ × ℕ => presDataSheaf F' q.1 q.2) U g},
    fun j => j.1, fun j => j.2.1, ?_, fun j => ?_⟩
  · refine Y.J.superset_covering (fun W g hg => ?_) hU
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨W, g, hg⟩, 𝟙 W, (Category.id_comp g).symm⟩
  · let : ∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{w} :=
      fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    obtain ⟨q, ⟨p⟩⟩ := j.2.2
    obtain ⟨P, hP⟩ := Stacks.SheafOfModules.exists_isFinite_presentation_over_of_isPresentationData
      F' _ _ p.property
    exact SheafOfModules.HasFiniteGlobalPresentation.of_presentation' P hP

end Main

end Deformation.ToposThickening

end
