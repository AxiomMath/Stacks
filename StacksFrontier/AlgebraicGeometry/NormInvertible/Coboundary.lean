module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Cocycle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomologous unit cocycles glue to isomorphic modules

Two unit transition cocycles on the same family of opens whose transition units differ by a
coboundary — that is, `t'ᵢⱼ = cⱼ · cᵢ⁻¹ · tᵢⱼ` for units `cᵢ` on the `i`-th chart — glue to
isomorphic sheaves of modules. The isomorphism is immediate on compatible families of local
coordinates: rescaling the `i`-th coordinate by `cᵢ` carries the compatibility condition of one
cocycle to that of the other, and the rescaling is `𝒪_X(W)`-linear because the module structure
on the `i`-th coordinate is restriction followed by multiplication.

[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY) omits the verification that the
norm construction is well defined, and this is one part of it: it makes the norm of an invertible
module independent of the chosen local generators. The chart trivializations of
`Stacks.Divisors.normTransitionCocycle` are picked with `Classical.choice`, so two choices of
them — or the constructions for two isomorphic modules — produce transition units differing
exactly by the coboundary of the norms of the ratios of the two choices.

## Main definitions

* `Stacks.SheafOfModules.UnitTransitionCocycle.IsCoboundaryTwist`: the relation "the transition
  units of `D'` are those of `D` twisted by the coboundary of the chart units `c`".
* `Stacks.SheafOfModules.UnitTransitionCocycle.coboundaryScaleHom` and
  `Stacks.SheafOfModules.UnitTransitionCocycle.coboundarySectionsEquiv`: the rescaling of local
  coordinates, as a linear map and as a linear equivalence of the modules of compatible families
  over an open.

## Main results

* `Stacks.SheafOfModules.UnitTransitionCocycle.presheafMap_trans_apply`: restriction of sections
  of the structure presheaf is transitive, in applied form.
* `Stacks.SheafOfModules.UnitTransitionCocycle.IsCoboundaryTwist.symm`: the relation is symmetric,
  with the inverse units.
* `Stacks.SheafOfModules.UnitTransitionCocycle.coboundarySectionsEquiv_sectionsMap`: the rescaling
  commutes with restriction.
* `Stacks.SheafOfModules.UnitTransitionCocycle.glueIsoOfCoboundaryTwist`: **cohomologous unit
  cocycles glue to isomorphic sheaves of modules.**
* `Stacks.SheafOfModules.UnitTransitionCocycle.chartLinearEquiv_glueIsoOfCoboundaryTwist`: the
  isomorphism rescales the `i`-th chart coordinate by `cᵢ`, which is what pins it down.

## Implementation notes

No `@[stacks]` attribute is placed. Tag 0BCY asserts the whole norm construction including the
Picard-group homomorphism, and this file is one ingredient of its well-definedness clause.

The coboundary convention is the one the compatibility condition of
`UnitTransitionCocycle.sectionsSubmodule` forces: that condition reads `tᵢⱼ · sᵢ| = sⱼ|`, so
rescaling `sᵢ ↦ cᵢ · sᵢ` requires `t'ᵢⱼ · cᵢ = cⱼ · tᵢⱼ`. Writing the twist in the other order
would describe the inverse isomorphism, and `chartLinearEquiv_glueIsoOfCoboundaryTwist` is what
fixes the orientation.

The cancellation behind `IsCoboundaryTwist.symm` is stated for an abstract commutative group
(`unitsCoboundaryCancel`) and applied, rather than proved in place: carried out directly on the
units of a ring of sections it exhausts the default heartbeat budget at `whnf`.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules.UnitTransitionCocycle

attribute [local instance] sectionsProductModule

variable {X : RingedSpace.{u, u}} {ι : Type u} {U : ι → Opens X.carrier}

/-! ### Restriction of unit-valued sections -/

/-- Restriction of a unit of the ring of sections along an inclusion of opens. -/
noncomputable def resUnits {V W : Opens X.carrier} (h : W ≤ V) :
    (X.presheaf.obj (op V))ˣ →* (X.presheaf.obj (op W))ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom

/-- The value of a restricted unit is the restriction of its value. -/
@[simp]
theorem resUnits_val {V W : Opens X.carrier} (h : W ≤ V) (a : (X.presheaf.obj (op V))ˣ) :
    (resUnits h a).val = X.presheaf.map (homOfLE h).op a.val :=
  rfl

/-- Restriction of sections is transitive, in applied form. -/
theorem presheafMap_trans_apply {V W Z : Opens X.carrier} (h : W ≤ V) (k : Z ≤ W)
    (x : X.presheaf.obj (op V)) :
    X.presheaf.map (homOfLE k).op (X.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE (k.trans h)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a unit twice is restricting it once, along the composite inclusion. -/
theorem resUnits_resUnits {V W Z : Opens X.carrier} (h : W ≤ V) (k : Z ≤ W)
    (a : (X.presheaf.obj (op V))ˣ) :
    resUnits k (resUnits h a) = resUnits (k.trans h) a :=
  Units.ext (presheafMap_trans_apply h k a.val)

/-! ### The coboundary relation -/

/-- `IsCoboundaryTwist D D' c` says that the transition units of `D'` are those of `D` twisted
by the coboundary of the chart units `c`: over an open `V` inside both the `i`-th and the `j`-th
chart, `t'ᵢⱼ = cⱼ|ᵥ · (cᵢ|ᵥ)⁻¹ · tᵢⱼ`. -/
def IsCoboundaryTwist (D D' : UnitTransitionCocycle X U)
    (c : ∀ i, (X.presheaf.obj (op (U i)))ˣ) : Prop :=
  ∀ (i j : ι) (V : Opens X.carrier) (hi : V ≤ U i) (hj : V ≤ U j),
    D'.transition i j V hi hj =
      resUnits hj (c j) * (resUnits hi (c i))⁻¹ * D.transition i j V hi hj

/-- The cancellation that makes the coboundary relation symmetric. Stated for an abstract
commutative group, because on the units of a ring of sections the same rewriting exhausts the
default heartbeat budget. -/
theorem unitsCoboundaryCancel {G : Type*} [CommGroup G] (a b t : G) :
    b⁻¹ * a * (b * a⁻¹ * t) = t := by
  rw [mul_comm b⁻¹ a, mul_assoc, mul_assoc b, inv_mul_cancel_left, mul_inv_cancel_left]

/-! ### Rescaling compatible families of local coordinates -/

section

variable {D D' : UnitTransitionCocycle X U} {c : ∀ i, (X.presheaf.obj (op (U i)))ˣ}

/-- The coboundary relation is symmetric, the inverse twist being given by the inverse units. -/
theorem IsCoboundaryTwist.symm (h : IsCoboundaryTwist D D' c) :
    IsCoboundaryTwist D' D (fun i => (c i)⁻¹) := by
  intro i j V hi hj
  rw [h i j V hi hj, map_inv, map_inv, inv_inv]
  exact (unitsCoboundaryCancel (resUnits hi (c i)) (resUnits hj (c j))
    (D.transition i j V hi hj)).symm

/-- Rescaling the `i`-th local coordinate by `cᵢ` carries a family compatible for `D` to a
family compatible for `D'`. -/
theorem coboundaryScale_mem (h : IsCoboundaryTwist D D' c) (W : Opens X.carrier)
    (s : D.sectionsSubmodule W) :
    (fun i => (resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val * s.val i) ∈
      D'.sectionsSubmodule W := by
  intro i j
  set Z : Opens X.carrier := W ⊓ U i ⊓ (W ⊓ U j) with hZdef
  have hZi : Z ≤ W ⊓ U i := inf_le_left
  have hZj : Z ≤ W ⊓ U j := inf_le_right
  have hc : ∀ (k : ι) (hk : Z ≤ W ⊓ U k),
      X.presheaf.map (homOfLE hk).op ((resUnits (inf_le_right : W ⊓ U k ≤ U k) (c k)).val) =
        (resUnits (hk.trans inf_le_right) (c k)).val := fun k hk =>
    presheafMap_trans_apply (inf_le_right : W ⊓ U k ≤ U k) hk (c k).val
  have hcompat := s.property i j
  have htw := h i j Z (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  change (D'.transition i j Z (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)).val *
      X.presheaf.map (homOfLE hZi).op
        ((resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val * s.val i) =
    X.presheaf.map (homOfLE hZj).op
      ((resUnits (inf_le_right : W ⊓ U j ≤ U j) (c j)).val * s.val j)
  rw [map_mul, map_mul, hc i hZi, hc j hZj, congrArg Units.val htw]
  set ui := resUnits (inf_le_left.trans inf_le_right : Z ≤ U i) (c i) with hui
  set uj := resUnits (inf_le_right.trans inf_le_right : Z ≤ U j) (c j) with huj
  set t := D.transition i j Z (inf_le_left.trans inf_le_right)
    (inf_le_right.trans inf_le_right) with ht
  calc (uj * ui⁻¹ * t : (X.presheaf.obj (op Z))ˣ).val *
          (ui.val * X.presheaf.map (homOfLE hZi).op (s.val i))
      = uj.val * ((ui.val * ui⁻¹.val) *
          (t.val * X.presheaf.map (homOfLE hZi).op (s.val i))) := by
        simp only [Units.val_mul]; ring
    _ = uj.val * (t.val * X.presheaf.map (homOfLE hZi).op (s.val i)) := by
        rw [Units.mul_inv]; ring
    _ = uj.val * X.presheaf.map (homOfLE hZj).op (s.val j) := by rw [hcompat]

/-- Rescaling the `i`-th local coordinate by `cᵢ`, as a linear map between the modules of
compatible families of the two cocycles over an open. -/
noncomputable def coboundaryScaleHom (h : IsCoboundaryTwist D D' c) (W : Opens X.carrier) :
    D.sectionsSubmodule W →ₗ[X.presheaf.obj (op W)] D'.sectionsSubmodule W where
  toFun s := ⟨_, coboundaryScale_mem h W s⟩
  map_add' s t := Subtype.ext (funext fun i => by
    change (resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val * (s.val i + t.val i) =
      (resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val * s.val i +
        (resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val * t.val i
    ring)
  map_smul' r s := Subtype.ext (funext fun i => by
    change (resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val *
        (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r * s.val i) =
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r *
        ((resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val * s.val i)
    ring)

/-- The `i`-th coordinate of the rescaled family is the `i`-th coordinate times `cᵢ`. -/
@[simp]
theorem coboundaryScaleHom_val (h : IsCoboundaryTwist D D' c) (W : Opens X.carrier)
    (s : D.sectionsSubmodule W) (i : ι) :
    (coboundaryScaleHom h W s).val i =
      (resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val * s.val i :=
  rfl

/-- Rescaling the `i`-th local coordinate by `cᵢ`, as a linear equivalence between the modules of
compatible families of the two cocycles over an open. -/
noncomputable def coboundarySectionsEquiv (h : IsCoboundaryTwist D D' c) (W : Opens X.carrier) :
    D.sectionsSubmodule W ≃ₗ[X.presheaf.obj (op W)] D'.sectionsSubmodule W where
  toFun s := ⟨_, coboundaryScale_mem h W s⟩
  map_add' := (coboundaryScaleHom h W).map_add'
  map_smul' := (coboundaryScaleHom h W).map_smul'
  invFun s := ⟨_, coboundaryScale_mem h.symm W s⟩
  left_inv s := Subtype.ext (funext fun i => by
    change (resUnits (inf_le_right : W ⊓ U i ≤ U i) ((c i)⁻¹)).val *
      ((resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val * s.val i) = s.val i
    rw [map_inv, ← mul_assoc, Units.inv_mul, one_mul])
  right_inv s := Subtype.ext (funext fun i => by
    change (resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val *
      ((resUnits (inf_le_right : W ⊓ U i ≤ U i) ((c i)⁻¹)).val * s.val i) = s.val i
    rw [map_inv, ← mul_assoc, Units.mul_inv, one_mul])

/-- The `i`-th coordinate of the rescaled family is the `i`-th coordinate times `cᵢ`. -/
@[simp]
theorem coboundarySectionsEquiv_val (h : IsCoboundaryTwist D D' c) (W : Opens X.carrier)
    (s : D.sectionsSubmodule W) (i : ι) :
    (coboundarySectionsEquiv h W s).val i =
      (resUnits (inf_le_right : W ⊓ U i ≤ U i) (c i)).val * s.val i :=
  rfl

/-- The rescaling commutes with restriction of compatible families. -/
theorem coboundarySectionsEquiv_sectionsMap (h : IsCoboundaryTwist D D' c)
    {W W' : Opens X.carrier} (k : W' ≤ W) (s : D.sectionsSubmodule W) :
    coboundarySectionsEquiv h W' (D.sectionsMap k s) =
      D'.sectionsMap k (coboundarySectionsEquiv h W s) := by
  refine Subtype.ext (funext fun i => ?_)
  rw [coboundarySectionsEquiv_val, sectionsMap_val, sectionsMap_val,
    coboundarySectionsEquiv_val, map_mul, resUnits_val, resUnits_val, presheafMap_trans_apply]

/-- **Cohomologous unit cocycles glue to isomorphic sheaves of modules.** -/
noncomputable def glueIsoOfCoboundaryTwist (h : IsCoboundaryTwist D D' c) : D.glue ≅ D'.glue :=
  (_root_.SheafOfModules.fullyFaithfulForget (structureSheaf X.sheaf)).preimageIso <|
    PresheafOfModules.isoMk (fun V => (coboundarySectionsEquiv h V.unop).toModuleIso)
      fun _ _ g => ModuleCat.hom_ext <| LinearMap.ext fun s =>
        coboundarySectionsEquiv_sectionsMap h g.unop.le s

/-- The gluing isomorphism rescales the `i`-th chart coordinate by `cᵢ`. Together with
`chartLinearEquiv` this pins the isomorphism down. -/
@[ega "0 5.4.7" "partial"]
theorem chartLinearEquiv_glueIsoOfCoboundaryTwist (h : IsCoboundaryTwist D D' c)
    (i : ι) {V : Opens X.carrier} (hV : V ≤ U i) (s : D.sectionsSubmodule V) :
    D'.chartLinearEquiv i hV ((glueIsoOfCoboundaryTwist h).hom.val.app (op V) s) =
      X.presheaf.map (homOfLE hV).op (c i).val * D.chartLinearEquiv i hV s := by
  change X.presheaf.map (homOfLE (le_inf le_rfl hV)).op
      ((coboundarySectionsEquiv h V s).val i) =
    X.presheaf.map (homOfLE hV).op (c i).val *
      X.presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.val i)
  rw [coboundarySectionsEquiv_val, map_mul, resUnits_val, presheafMap_trans_apply]

end

end Stacks.SheafOfModules.UnitTransitionCocycle
