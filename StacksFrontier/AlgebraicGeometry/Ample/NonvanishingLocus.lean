module

public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Ample.LocallyFiniteFreeSummand
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The nonvanishing locus of a section of an invertible module

Let `(X, 𝒪_X)` be a ringed space all of whose stalks are local rings, let `L` be an invertible
`𝒪_X`-module and let `s` be a global section of `L`. The nonvanishing locus `X_s` of `s` is the
set of points `x` at which the germ of `s` does not lie in `𝔪_x L_x`. This file proves that
`X_s` is open, which is the first assertion of Tag 01CY.

The argument runs entirely through the pairing of `L` against a tensor inverse `N`, and so never
needs to know that `L` is locally free. Near any point the section of `L ⊗ N` corresponding to
`1` is a finite sum of pure tensors `∑ sᵢ ⊗ tᵢ` over an open `U`
(`Stacks.SheafOfModules.LocallyFiniteFree.exists_local_finite_tensor_representation`), and then
`m ↦ ∑ ⟨m, tᵢ⟩ sᵢ` is an *automorphism* of `L`
(`Stacks.SheafOfModules.LocallyFiniteFree.tensorTwistAutomorphism_hom_app_apply`). Writing
`gᵢ = ⟨s, tᵢ⟩ ∈ 𝒪_X(U)` this gives, for `y ∈ U`:

* if every `gᵢ` has germ in `𝔪_y` then so does `s`, by applying the inverse automorphism; and
* if some `gᵢ` has germ a unit then the germ of `s` is not in `𝔪_y L_y`, because the pairing is
  `𝒪`-bilinear and compatible with restriction, hence carries `𝔪_y L_y` into `𝔪_y`.

So `X_s ∩ U` is the union of the basic opens `X.basicOpen gᵢ`, and `X_s` is open.

## Main definitions

* `Stacks.SheafOfModules.Invertible.nonvanishingLocus` is the set of points where the germ of a
  section is not in the maximal ideal times its stalk module.
* `Stacks.SheafOfModules.Invertible.nonvanishingOpen` packages this locus as an open subset.

## Main results

* `Stacks.SheafOfModules.Invertible.isOpen_nonvanishingLocus` is the openness assertion of
  Tag 01CY.

## Implementation notes

Nothing here uses stalkwise *linear* maps: both implications are proved by producing
representatives of germs over small enough opens and using bilinearity of the pairing on
sections. That is what keeps the proof clear of the comparison between the `RingCat`-valued and
the `CommRingCat`-valued stalk of the structure sheaf, which is the step that forces
`backward.isDefEq.respectTransparency` elsewhere in this area.

The structure sheaf of the ringed space is spelled `ringSheaf X`, the `RingCat`-valued sheaf of
rings underlying `X.presheaf`. It is `rfl`-equal to `structureSheaf X.sheaf` of Tag 01CO, but
unlike the latter it is a reducible definition, so typeclass synthesis can see through it to the
`ModuleCat` structures on the sections of `L`.

The other two assertions of Tag 01CY — that `s` trivialises `L` over `X_s`, and that there is a
section of `L^{⊗ -1}` over `X_s` pairing with `s` to `1` — are not here. The second needs the
coherent multiplication of tensor powers, which is the unproved part of Tag 01CU.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open Stacks.SheafOfModules.LocallyFiniteFree (ringSheaf pairing exists_tensor_inverse
  exists_local_finite_tensor_representation tensorTwistAutomorphism
  tensorTwistAutomorphism_hom_app_apply)

universe u

namespace Stacks.SheafOfModules.Invertible

variable (X : RingedSpace.{u}) (L : SheafOfModules.{u} (ringSheaf X))
  [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- The points where a section generates its rank-one stalk modulo the maximal ideal. -/
@[ega "0 5.5.2"]
noncomputable def nonvanishingLocus (s : L.sections) : Set X :=
  {x | letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) L.val x
    (TopCat.Presheaf.Γgerm L.val.presheaf x).hom (s.eval (op ⊤)) ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x)))}

section Pairing

variable {X L}
variable (N : SheafOfModules.{u} (ringSheaf X))
  (e : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        ((ringSheaf X).property)⟩).obj (L))).obj N ≅ SheafOfModules.unit (ringSheaf X))

omit [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- Restriction of a section of a sheaf of modules, read in the module of sections over the
smaller open rather than in the restriction of scalars presenting it. -/
private noncomputable abbrev res (M : SheafOfModules.{u} (ringSheaf X)) {U V : Opens X}
    (k : op U ⟶ op V) (m : M.val.obj (op U)) : M.val.obj (op V) := M.val.map k m

/-- Two successive restrictions of a section agree with the direct one: the category of opens
has at most one morphism between two objects. -/
private lemma res_res (M : SheafOfModules.{u} (ringSheaf X)) {U V W : Opens X}
    (k : op U ⟶ op V) (k' : op V ⟶ op W) (k'' : op U ⟶ op W) (m : M.val.obj (op U)) :
    res M k' (res M k m) = res M k'' m :=
  (M.val.map_comp_apply k k' m).symm.trans
    (M.val.congr_map_apply (Subsingleton.elim _ _) m)

/-- The germ of a restricted section is the germ of the section. -/
private lemma germ_res (M : SheafOfModules.{u} (ringSheaf X)) {U V : Opens X}
    (k : op U ⟶ op V) (y : X) (hyV : y ∈ V) (m : M.val.obj (op U)) :
    TopCat.Presheaf.germ M.val.presheaf V y hyV (res M k m) =
      TopCat.Presheaf.germ M.val.presheaf U y (k.unop.le hyV) m :=
  TopCat.Presheaf.germ_res_apply' M.val.presheaf k y hyV m

/-- Germs are additive. Stated here so that the addition is the one on the module of sections
rather than the one on the underlying abelian group. -/
private lemma germ_add (M : SheafOfModules.{u} (ringSheaf X)) {V : Opens X} (y : X)
    (hyV : y ∈ V) (m m' : M.val.obj (op V)) :
    TopCat.Presheaf.germ M.val.presheaf V y hyV (m + m') =
      TopCat.Presheaf.germ M.val.presheaf V y hyV m +
        TopCat.Presheaf.germ M.val.presheaf V y hyV m' :=
  map_add (TopCat.Presheaf.germ M.val.presheaf V y hyV).hom m m'

/-- Germs commute with finite sums of sections. -/
private lemma germ_sum (M : SheafOfModules.{u} (ringSheaf X)) {V : Opens X} (y : X)
    (hyV : y ∈ V) {ι : Type*} (t : Finset ι) (f : ι → M.val.obj (op V)) :
    TopCat.Presheaf.germ M.val.presheaf V y hyV (∑ i ∈ t, f i) =
      ∑ i ∈ t, TopCat.Presheaf.germ M.val.presheaf V y hyV (f i) :=
  map_sum (TopCat.Presheaf.germ M.val.presheaf V y hyV).hom f t

/-- The pairing of `L` against a tensor inverse is compatible with restriction. -/
private lemma pairing_res {V W : Opens X} (k : op V ⟶ op W) (m : L.val.obj (op V))
    (nV : N.val.obj (op V)) :
    X.presheaf.map k (pairing X L N e V m nV) =
      pairing X L N e W (res L k m) (res N k nV) :=
  let a := AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
    (ringSheaf X).property L
  (PresheafOfModules.naturality_apply e.hom.val k
      (((a.ι.app N).app (op V)).hom (m ⊗ₜ[X.presheaf.obj (op V)] nV))).symm.trans
    ((congrArg (e.hom.val.app (op W)).hom
        (PresheafOfModules.naturality_apply (a.ι.app N) k
          (m ⊗ₜ[X.presheaf.obj (op V)] nV))).symm.trans
      (congrArg (fun z => (e.hom.val.app (op W)).hom (((a.ι.app N).app (op W)).hom z))
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul k m nV)))

/-- The germ of a global section at `y` is the germ of its restriction to any open around `y`. -/
private lemma germ_eval_eq_Γgerm (s : L.sections) {V : Opens X} (y : X) (hyV : y ∈ V) :
    TopCat.Presheaf.germ L.val.presheaf V y hyV (s.eval (op V)) =
      (TopCat.Presheaf.Γgerm L.val.presheaf y).hom (s.eval (op ⊤)) :=
  (congrArg (fun w => TopCat.Presheaf.germ L.val.presheaf V y hyV w)
      (PresheafOfModules.sections_property s (homOfLE (le_top : V ≤ ⊤)).op)).symm.trans
    (TopCat.Presheaf.Γgerm_res_apply L.val.presheaf (i := homOfLE (le_top : V ≤ ⊤)) y hyV
      (s.eval (op ⊤)))

/-- The pairing of `L` against a tensor inverse is additive in the section of `L`. -/
private lemma pairing_add {V : Opens X} (m m' : L.val.obj (op V)) (nV : N.val.obj (op V)) :
    pairing X L N e V (m + m') nV =
      pairing X L N e V m nV + pairing X L N e V m' nV :=
  let a := AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
    (ringSheaf X).property L
  (congrArg (fun z => (e.hom.val.app (op V)).hom (((a.ι.app N).app (op V)).hom z))
      (TensorProduct.add_tmul m m' nV)).trans
    ((congrArg (e.hom.val.app (op V)).hom
        (map_add ((a.ι.app N).app (op V)).hom _ _)).trans
      (map_add (e.hom.val.app (op V)).hom _ _))

/-- The pairing of `L` against a tensor inverse is linear in the section of `L`. -/
private lemma pairing_smul {V : Opens X} (c : (ringSheaf X).obj.obj (op V))
    (m : L.val.obj (op V)) (nV : N.val.obj (op V)) :
    pairing X L N e V (c • m) nV = c * pairing X L N e V m nV :=
  let a := AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
    (ringSheaf X).property L
  (congrArg (fun z => (e.hom.val.app (op V)).hom (((a.ι.app N).app (op V)).hom z))
      (TensorProduct.smul_tmul' c m nV)).trans
    ((congrArg (e.hom.val.app (op V)).hom
        (((a.ι.app N).app (op V)).hom.map_smul c
          (m ⊗ₜ[X.presheaf.obj (op V)] nV))).trans
      ((e.hom.val.app (op V)).hom.map_smul c
        (((a.ι.app N).app (op V)).hom (m ⊗ₜ[X.presheaf.obj (op V)] nV))))

/-- The germ of the pairing of restricted sections is the germ of the pairing. -/
private lemma germ_pairing_res {V W : Opens X} (k : op V ⟶ op W) (y : X) (hyW : y ∈ W)
    (m : L.val.obj (op V)) (nV : N.val.obj (op V)) :
    X.presheaf.germ W y hyW (pairing X L N e W (res L k m) (res N k nV)) =
      X.presheaf.germ V y (k.unop.le hyW) (pairing X L N e V m nV) := by
  rw [← pairing_res, TopCat.Presheaf.germ_res_apply']

end Pairing

section Openness

variable {X L}
variable (N : SheafOfModules.{u} (ringSheaf X))
  (e : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        ((ringSheaf X).property)⟩).obj (L))).obj N ≅ SheafOfModules.unit (ringSheaf X))

/-- An element of `𝔪_y L_y` is, over a small enough open, the germ of a section whose pairing
against a fixed section of the tensor inverse has germ in `𝔪_y`.

This is the only place where membership in `𝔪_y L_y` is unpacked; it is unpacked by induction
over the submodule product, so that no stalkwise linear map is ever needed. -/
private lemma exists_res_pairing_germ_mem
    {U : Opens X} (y : X) (hyU : y ∈ U) (τ : N.val.obj (op U))
    (z : TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y)
    (hz :
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val y
      z ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) •
        (⊤ : Submodule (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y))) :
    ∃ (V : Opens X) (hyV : y ∈ V) (k : op U ⟶ op V) (ζ : L.val.obj (op V)),
      TopCat.Presheaf.germ L.val.presheaf V y hyV ζ = z ∧
        X.presheaf.germ V y hyV (pairing X L N e V ζ (res N k τ)) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  let : Module (X.presheaf.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) L.val y
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro c hc σ _
    obtain ⟨V₁, hyV₁, C, hC⟩ := X.presheaf.exists_germ_eq c
    obtain ⟨V₂, hyV₂, Z₀, hZ₀⟩ := TopCat.Presheaf.exists_germ_eq L.val.presheaf σ
    have hyV : y ∈ U ⊓ V₁ ⊓ V₂ := ⟨⟨hyU, hyV₁⟩, hyV₂⟩
    have h1 : U ⊓ V₁ ⊓ V₂ ≤ U := le_trans inf_le_left inf_le_left
    have h2 : U ⊓ V₁ ⊓ V₂ ≤ V₁ := le_trans inf_le_left inf_le_right
    have h3 : U ⊓ V₁ ⊓ V₂ ≤ V₂ := inf_le_right
    have hCres : X.presheaf.germ (U ⊓ V₁ ⊓ V₂) y hyV
        (X.presheaf.map (homOfLE h2).op C) = c :=
      (TopCat.Presheaf.germ_res_apply' X.presheaf (homOfLE h2).op y hyV C).trans hC
    have hZres : TopCat.Presheaf.germ L.val.presheaf (U ⊓ V₁ ⊓ V₂) y hyV
        (res L (homOfLE h3).op (Z₀ : L.val.obj (op V₂))) = σ :=
      (germ_res L (homOfLE h3).op y hyV (Z₀ : L.val.obj (op V₂))).trans hZ₀
    refine ⟨U ⊓ V₁ ⊓ V₂, hyV, (homOfLE h1).op,
      X.presheaf.map (homOfLE h2).op C • res L (homOfLE h3).op (Z₀ : L.val.obj (op V₂)),
      ?_, ?_⟩
    · refine (PresheafOfModules.germ_smul (R := X.presheaf) L.val y (U ⊓ V₁ ⊓ V₂) hyV
        (X.presheaf.map (homOfLE h2).op C)
        (res L (homOfLE h3).op (Z₀ : L.val.obj (op V₂)))).trans ?_
      rw [hCres, hZres]
    · rw [pairing_smul, map_mul, hCres]
      exact Ideal.mul_mem_right _ _ hc
  · rintro z₁ z₂ ⟨V₁, hyV₁, k₁, ζ₁, hζ₁, hm₁⟩ ⟨V₂, hyV₂, k₂, ζ₂, hζ₂, hm₂⟩
    have hV₁ : V₁ ⊓ V₂ ≤ V₁ := inf_le_left
    have hV₂ : V₁ ⊓ V₂ ≤ V₂ := inf_le_right
    have hyV : y ∈ V₁ ⊓ V₂ := ⟨hyV₁, hyV₂⟩
    refine ⟨V₁ ⊓ V₂, hyV, (homOfLE (le_trans hV₁ k₁.unop.le)).op,
      res L (homOfLE hV₁).op ζ₁ + res L (homOfLE hV₂).op ζ₂, ?_, ?_⟩
    · rw [germ_add, germ_res, germ_res, hζ₁, hζ₂]
    · rw [pairing_add, map_add]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← res_res N (k := k₁) (k' := (homOfLE hV₁).op), germ_pairing_res]
        exact hm₁
      · rw [← res_res N (k := k₂) (k' := (homOfLE hV₂).op), germ_pairing_res]
        exact hm₂

/-- If every pairing of a global section against the local dual sections has germ in `𝔪_x`, then
the germ of the section lies in `𝔪_x L_x`. This is the direction of Tag 01CY that uses the twist
automorphism of `L`. -/
private lemma mem_smul_of_forall_pairing_germ_mem
    {U : Opens X} {n : ℕ} (x : X) (hxU : x ∈ U)
    (sU : Fin n → L.val.obj (op U)) (tU : Fin n → N.val.obj (op U))
    (hsum :
      ((AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
        (ringSheaf X).property L).ι.app N).app
          (op U) (∑ i, sU i ⊗ₜ[X.presheaf.obj (op U)] tU i) =
        (e.inv.val.app (op U)).hom (1 : (ringSheaf X).obj.obj (op U)))
    (s : L.sections)
    (h : ∀ i, X.presheaf.germ U x hxU
        (pairing X L N e U (s.eval (op U)) (res N (𝟙 (op U)) (tU i))) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) L.val x
    (TopCat.Presheaf.Γgerm L.val.presheaf x).hom (s.eval (op ⊤)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x)) := by
  let : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) L.val x
  have hback : s.eval (op U) =
      ∑ i, pairing X L N e U (s.eval (op U)) (res N (𝟙 (op U)) (tU i)) •
        ((tensorTwistAutomorphism X L N e).inv.val.app (op U)).hom
          (res L (𝟙 (op U)) (sU i)) := by
    have h0 : ((tensorTwistAutomorphism X L N e).inv.val.app (op U)).hom
        (((tensorTwistAutomorphism X L N e).hom.val.app (op U)).hom (s.eval (op U))) =
        s.eval (op U) :=
      congrArg (fun g : L ⟶ L => (g.val.app (op U)).hom (s.eval (op U)))
        (tensorTwistAutomorphism X L N e).hom_inv_id
    conv_lhs => rw [← h0]
    rw [tensorTwistAutomorphism_hom_app_apply X L N e U n sU tU hsum (𝟙 (op U)) (s.eval (op U))]
    exact (map_sum ((tensorTwistAutomorphism X L N e).inv.val.app (op U)).hom _
        Finset.univ).trans
      (Finset.sum_congr rfl fun i _ =>
        ((tensorTwistAutomorphism X L N e).inv.val.app (op U)).hom.map_smul _ _)
  have hall : (TopCat.Presheaf.Γgerm L.val.presheaf x).hom (s.eval (op ⊤)) =
      ∑ i, X.presheaf.germ U x hxU
          (pairing X L N e U (s.eval (op U)) (res N (𝟙 (op U)) (tU i))) •
        TopCat.Presheaf.germ L.val.presheaf U x hxU
          (((tensorTwistAutomorphism X L N e).inv.val.app (op U)).hom
            (res L (𝟙 (op U)) (sU i))) :=
    (germ_eval_eq_Γgerm s x hxU).symm.trans
      ((congrArg (fun w => TopCat.Presheaf.germ L.val.presheaf U x hxU w) hback).trans
      ((germ_sum L x hxU Finset.univ _).trans
        (Finset.sum_congr rfl fun i _ =>
          PresheafOfModules.germ_smul (R := X.presheaf) L.val x U hxU _ _)))
  exact Eq.mpr (congrArg (fun w => w ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x))) hall)
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top)

/-- If some pairing of a global section against a section of the tensor inverse has germ a unit,
then the germ of the section is not in `𝔪_y L_y`. -/
private lemma notMem_smul_of_isUnit_pairing_germ
    {U : Opens X} (y : X) (hyU : y ∈ U) (τ : N.val.obj (op U)) (s : L.sections)
    (h : IsUnit (X.presheaf.germ U y hyU (pairing X L N e U (s.eval (op U)) τ))) :
    letI : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) L.val y
    (TopCat.Presheaf.Γgerm L.val.presheaf y).hom (s.eval (op ⊤)) ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) •
        (⊤ : Submodule (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y)) := by
  intro hz
  obtain ⟨V, hyV, k, ζ, hζ, hm⟩ := exists_res_pairing_germ_mem N e y hyU τ _ hz
  obtain ⟨W, hyW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq L.val.presheaf y hyV hyV ζ
    (s.eval (op V)) (hζ.trans (germ_eval_eq_Γgerm s y hyV).symm)
  have hζW : res L iU.op ζ = s.eval (op W) :=
    heq.trans (PresheafOfModules.sections_property s iV.op)
  have hmW : X.presheaf.germ W y hyW (pairing X L N e W (s.eval (op W))
      (res N (homOfLE (le_trans iU.le k.unop.le) : W ⟶ U).op τ)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
    rw [← hζW, ← res_res N (k := k) (k' := iU.op), germ_pairing_res]
    exact hm
  have hmove : X.presheaf.germ U y hyU (pairing X L N e U (s.eval (op U)) τ) =
      X.presheaf.germ W y hyW (pairing X L N e W (s.eval (op W))
        (res N (homOfLE (le_trans iU.le k.unop.le) : W ⟶ U).op τ)) := by
    rw [← germ_pairing_res N e (homOfLE (le_trans iU.le k.unop.le) : W ⟶ U).op y hyW]
    exact congrArg (X.presheaf.germ W y hyW ∘ fun w => pairing X L N e W w _)
      (PresheafOfModules.sections_property s _)
  exact IsLocalRing.notMem_maximalIdeal.mpr h (hmove ▸ hmW)

end Openness

/-- **Stacks Project, Tag 01CY**, openness. The nonvanishing locus of a section of an invertible
module is open: near any point it is the union of the basic opens of the pairings of the section
against the local dual sections of a tensor inverse. -/
-- The clause `@[stacks 01CY "openness"]` is carried by
-- `Algebra/Category/ModuleCat/Sheaf/FinitePresentationStalk.lean:469`, so this stays as
-- untagged infrastructure: the pairing argument here is still the shorter route to the fact.
@[ega "0 5.5.2"]
theorem isOpen_nonvanishingLocus
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheaf X).property L]
    (s : L.sections) : IsOpen (nonvanishingLocus X L s) := by
  obtain ⟨N, ⟨e⟩⟩ := exists_tensor_inverse X L inferInstance
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  obtain ⟨U, hxU, n, sU, tU, hsum⟩ := exists_local_finite_tensor_representation X L N e x
  obtain ⟨i, hi⟩ : ∃ i : Fin n, IsUnit (X.presheaf.germ U x hxU
      (pairing X L N e U (s.eval (op U)) (res N (𝟙 (op U)) (tU i)))) := by
    by_contra! hcon
    refine hx (mem_smul_of_forall_pairing_germ_mem N e x hxU sU tU hsum s fun i => ?_)
    by_contra hn
    exact hcon i (IsLocalRing.notMem_maximalIdeal.mp hn)
  exact Filter.mem_of_superset
    (IsOpen.mem_nhds (X.basicOpen (pairing X L N e U (s.eval (op U))
      (res N (𝟙 (op U)) (tU i)))).2 ((X.mem_basicOpen _ x hxU).mpr hi)) fun y hy =>
    notMem_smul_of_isUnit_pairing_germ N e y (X.basicOpen_le _ hy)
    (res N (𝟙 (op U)) (tU i)) s ((X.mem_basicOpen _ y (X.basicOpen_le _ hy)).mp hy)

/-- The open set on which a section of an invertible module is a basis. -/
noncomputable def nonvanishingOpen
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheaf X).property L]
    (s : L.sections) : Opens X :=
  ⟨nonvanishingLocus X L s, isOpen_nonvanishingLocus X L s⟩


end Stacks.SheafOfModules.Invertible

end
