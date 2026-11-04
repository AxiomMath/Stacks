module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Generators
public import StacksFrontier.Topology.Sheaves.Glueing.Sheaf
public import Mathlib.Algebra.Module.Pi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An invertible module from a cocycle of unit-valued transition functions

Let `(X, 𝒪_X)` be a ringed space and let `U : ι → Opens X` be a family of opens covering `X`.
A *unit transition cocycle* for `U` assigns to each pair `i j` and each open `V` contained in
both `U i` and `U j` a unit `u_{ij} ∈ 𝒪_X(V)^*`, compatibly with restriction, with
`u_{ji} = u_{ij}⁻¹` and with `u_{jk} u_{ij} = u_{ik}`. This file glues such a cocycle into a
sheaf of `𝒪_X`-modules, exhibits the chart trivializations, and concludes that the result is
invertible.

This is the gluing step of the norm construction of
[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY): there the transition units of a
line bundle on the source of a finite morphism are pushed through a norm on functions, the
cocycle identity survives because a norm is multiplicative, and the glued module is the norm of
the line bundle.

## Main definitions

* `Stacks.SheafOfModules.UnitTransitionCocycle`: the gluing data.
* `Stacks.SheafOfModules.UnitTransitionCocycle.sectionsSubmodule`: the sections of the glued
  module over an open, as a submodule of the product of the local coordinate rings.
* `Stacks.SheafOfModules.UnitTransitionCocycle.glue`: the glued sheaf of modules.
* `Stacks.SheafOfModules.UnitTransitionCocycle.chartLinearEquiv` and `chartOverIso`: the
  trivialization of the glued module over a chart, sectionwise and as an isomorphism on the
  localized site.
* `Stacks.SheafOfModules.UnitTransitionCocycle.chartGenerator`: the chart section with
  coordinate one, as a local generator.

## Main results

* `Stacks.SheafOfModules.UnitTransitionCocycle.smul_bijective_of_isUnit`: a compatible family
  of coordinates which is a unit in every chart generates the glued module.
* `Stacks.SheafOfModules.UnitTransitionCocycle.isInvertible_glue`: the glued module is
  invertible.

## Implementation notes

The underlying sheaf of sets is obtained from the repository's
`TopCat.Sheaf.GlueData`, so the sheaf condition is not reproved here: the module structure is
layered on top of the same carrier. Concretely, a section of the glued module over `W` is a
family `s i ∈ 𝒪_X(W ⊓ U i)` satisfying `u_{ij} · s i|_{W ⊓ U i ⊓ W ⊓ U j} = s j|_{…}`, and the
`𝒪_X(W)`-action is restriction followed by multiplication in the `i`-th coordinate, which is
`sectionsProductModule`. The identification of that carrier with
`TopCat.Sheaf.GlueData.Sections` is `sectionsEquiv`, and the sheaf condition is transported
along it.

Invertibility is concluded from the chart trivializations by
`Stacks.SheafOfModules.isInvertible_of_coversTop_iso_unit`, clause 1 of Tag 0B8M, directly.
Going instead through `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank _ 1` would
mean normalizing a free presentation on a localized site through several
restriction-of-scalars functors, and that is what makes the elaboration expensive; the
covering-of-trivializations criterion is exactly what the gluing produces, so no presentation
is built.

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, the class that
`isInvertible_of_coversTop_iso_unit` concludes. It is *not*
`AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`; the two classes have byte-identical
definitions but are distinct constants, and no bridge between them is written here.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- Unit-valued transition functions on a family of opens, with the restriction, inverse and
cocycle laws. This packages precisely the data needed to glue the local copies of the structure
sheaf into a sheaf of modules. -/
structure UnitTransitionCocycle (X : RingedSpace.{u, u}) {ι : Type u}
    (U : ι → Opens X.carrier) where
  /-- The transition unit from the `i`-th chart to the `j`-th, over an open inside both. -/
  transition (i j : ι) (V : Opens X.carrier) (hi : V ≤ U i) (hj : V ≤ U j) :
    (X.presheaf.obj (op V))ˣ
  /-- Transition units commute with restriction. -/
  restrict {i j : ι} {V W : Opens X.carrier} (hi : V ≤ U i) (hj : V ≤ U j) (h : W ≤ V) :
    Units.map (X.presheaf.map (homOfLE h).op).hom (transition i j V hi hj) =
      transition i j W (h.trans hi) (h.trans hj)
  /-- Reversing a transition inverts its unit. -/
  symm (i j : ι) (V : Opens X.carrier) (hi : V ≤ U i) (hj : V ≤ U j) :
    transition j i V hj hi = (transition i j V hi hj)⁻¹
  /-- The cocycle identity. -/
  cocycle (i j k : ι) (V : Opens X.carrier) (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    transition j k V hj hk * transition i j V hi hj = transition i k V hi hk

namespace UnitTransitionCocycle

/-- The `𝒪_X(W)`-module structure on the product of the local coordinate rings over `W`: the
action on the `i`-th coordinate is restriction to `W ⊓ U i` followed by multiplication. -/
@[instance_reducible]
noncomputable def sectionsProductModule {X : RingedSpace.{u, u}} {ι : Type u}
    (U : ι → Opens X.carrier) (W : Opens X.carrier) :
    Module (X.presheaf.obj (op W)) (∀ i, X.presheaf.obj (op (W ⊓ U i))) := by
  classical
  letI : ∀ i : ι, Module (X.presheaf.obj (op W)) (X.presheaf.obj (op (W ⊓ U i))) := fun i =>
    Module.compHom _ (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op).hom
  letI : ∀ i : ι, AddCommMonoid (X.presheaf.obj (op (W ⊓ U i))) := fun i => inferInstance
  exact Pi.module ι (fun i => X.presheaf.obj (op (W ⊓ U i))) (X.presheaf.obj (op W))

attribute [local instance] sectionsProductModule

/-- The structure sheaf is a sheaf of types. -/
theorem structureSheaf_isSheaf_as_types (X : RingedSpace.{u, u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of X))
      (X.presheaf ⋙ forget CommRingCat) :=
  (Presheaf.isSheaf_iff_isSheaf_comp _ X.presheaf (forget CommRingCat)).mp X.IsSheaf

/-- Forgetting the ring structures, a unit cocycle is a gluing datum for sheaves of sets. -/
@[ega "0 5.4.7" "partial"]
def toGlueData {X : RingedSpace.{u, u}} {ι : Type u} {U : ι → Opens X.carrier}
    (D : UnitTransitionCocycle X U) : TopCat.Sheaf.GlueData (TopCat.of X) U where
  sheaf i :=
    { obj V _ := X.presheaf.obj (op V)
      map hWV s := X.presheaf.map (homOfLE hWV).op s
      map_id := by
        intro V hV s
        change X.presheaf.map (homOfLE (le_rfl : V ≤ V)).op s = s
        rw [show (homOfLE (le_rfl : V ≤ V)).op = 𝟙 (op V) from Subsingleton.elim _ _]
        simp
      map_map := by
        intro V W Z hV hWV hZW s
        have hle : (homOfLE hWV).op ≫ (homOfLE hZW).op =
            (homOfLE (hZW.trans hWV)).op := Subsingleton.elim _ _
        have hcomp := X.presheaf.map_comp (homOfLE hWV).op (homOfLE hZW).op
        rw [hle] at hcomp
        simpa only [ConcreteCategory.comp_apply] using (congrArg (fun φ => φ s) hcomp).symm }
  isSheaf i := TopCat.Presheaf.isSheaf_toLocalPresheaf (structureSheaf_isSheaf_as_types X) (U i)
  trans i j {V} hi hj :=
    { toFun := fun x => (D.transition i j V hi hj).val * x
      invFun := fun x => ((D.transition i j V hi hj)⁻¹).val * x
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  trans_map i j {V W} hi hj h x := by
    change (D.transition i j W (h.trans hi) (h.trans hj)).val *
        X.presheaf.map (homOfLE h).op x =
      X.presheaf.map (homOfLE h).op ((D.transition i j V hi hj).val * x)
    have hval := congrArg Units.val (D.restrict (i := i) (j := j) hi hj h)
    change X.presheaf.map (homOfLE h).op (D.transition i j V hi hj).val =
      (D.transition i j W (h.trans hi) (h.trans hj)).val at hval
    rw [map_mul, hval]
  trans_trans i j k {V} hi hj hk x := by
    change (D.transition j k V hj hk).val * ((D.transition i j V hi hj).val * x) =
      (D.transition i k V hi hk).val * x
    have hc : (D.transition j k V hj hk).val * (D.transition i j V hi hj).val =
        (D.transition i k V hi hk).val := by
      simpa using congrArg Units.val (D.cocycle i j k V hi hj hk)
    rw [← mul_assoc, hc]

section

variable {X : RingedSpace.{u, u}} {ι : Type u} {U : ι → Opens X.carrier}

/-- Over an open `W`, the compatible families of local coordinates form an `𝒪_X(W)`-submodule
of the product of the local coordinate rings. -/
def sectionsSubmodule (D : UnitTransitionCocycle X U) (W : Opens X.carrier) :
    Submodule (X.presheaf.obj (op W)) (∀ i, X.presheaf.obj (op (W ⊓ U i))) := by
  classical
  refine
    { carrier := fun s => ∀ i j,
        (D.transition i j (W ⊓ U i ⊓ (W ⊓ U j))
          (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).val *
          X.presheaf.map
            (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op (s i) =
        X.presheaf.map
          (homOfLE (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op (s j)
      zero_mem' := by intro i j; simp
      add_mem' := ?_
      smul_mem' := ?_ }
  · intro s t hs ht i j
    change (D.transition i j (W ⊓ U i ⊓ (W ⊓ U j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).val *
        X.presheaf.map
          (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op (s i + t i) =
      X.presheaf.map
        (homOfLE (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op (s j + t j)
    rw [map_add, map_add, mul_add, hs i j, ht i j]
  · intro r s hs i j
    have hri : X.presheaf.map
        (homOfLE ((inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i).trans
          (inf_le_left : W ⊓ U i ≤ W))).op r =
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op
        (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r) := by
      have hle := Subsingleton.elim
        ((homOfLE (inf_le_left : W ⊓ U i ≤ W)).op ≫
          (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op)
        (homOfLE ((inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i).trans
          (inf_le_left : W ⊓ U i ≤ W))).op
      have hcomp := X.presheaf.map_comp (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op
        (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op
      rw [hle] at hcomp
      exact congrArg (fun φ => φ r) hcomp
    have hrj : X.presheaf.map
        (homOfLE ((inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j).trans
          (inf_le_left : W ⊓ U j ≤ W))).op r =
      X.presheaf.map (homOfLE (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op
        (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U j ≤ W)).op r) := by
      have hle := Subsingleton.elim
        ((homOfLE (inf_le_left : W ⊓ U j ≤ W)).op ≫
          (homOfLE (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op)
        (homOfLE ((inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j).trans
          (inf_le_left : W ⊓ U j ≤ W))).op
      have hcomp := X.presheaf.map_comp (homOfLE (inf_le_left : W ⊓ U j ≤ W)).op
        (homOfLE (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op
      rw [hle] at hcomp
      exact congrArg (fun φ => φ r) hcomp
    change (D.transition i j (W ⊓ U i ⊓ (W ⊓ U j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).val *
        X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op
          (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r * s i) =
      X.presheaf.map (homOfLE (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op
        (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U j ≤ W)).op r * s j)
    rw [map_mul, map_mul, ← hri, ← hrj]
    calc _ = X.presheaf.map
              (homOfLE ((inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i).trans
                (inf_le_left : W ⊓ U i ≤ W))).op r *
            ((D.transition i j (W ⊓ U i ⊓ (W ⊓ U j))
              (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).val *
              X.presheaf.map
                (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op (s i)) := by ring
      _ = _ := congrArg (fun z => X.presheaf.map
            (homOfLE ((inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i).trans
              (inf_le_left : W ⊓ U i ≤ W))).op r * z) (hs i j)

/-- The compatible families of local coordinates are the sections of the set-valued gluing
datum. -/
def sectionsEquiv (D : UnitTransitionCocycle X U) (W : Opens X.carrier) :
    D.toGlueData.Sections W ≃ ↥(D.sectionsSubmodule W) where
  toFun s := ⟨s.1, s.2⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv := by intro s; rfl
  right_inv := by intro s; rfl

/-- Restriction of a compatible family of local coordinates. -/
def sectionsMap (D : UnitTransitionCocycle X U) {W W' : Opens X.carrier} (h : W' ≤ W)
    (s : ↥(D.sectionsSubmodule W)) : ↥(D.sectionsSubmodule W') :=
  (D.sectionsEquiv W').symm (D.toGlueData.sectionsMap h (D.sectionsEquiv W s))

/-- The `i`-th local coordinate of the restriction of a compatible family is the restriction
of its `i`-th local coordinate. -/
theorem sectionsMap_val (D : UnitTransitionCocycle X U) {W W' : Opens X.carrier} (h : W' ≤ W)
    (s : ↥(D.sectionsSubmodule W)) (i : ι) :
    (D.sectionsMap h s).val i =
      X.presheaf.map (homOfLE (inf_le_inf_right (U i) h)).op (s.val i) := by
  show (D.toGlueData.sectionsMap h ((D.sectionsEquiv W).symm s)).1 i = _
  rw [TopCat.Sheaf.GlueData.sectionsMap_val]
  rfl

/-- Restriction on the ambient product of local coordinate rings, as a semilinear map over
restriction of functions. -/
def sectionsProdMap (_D : UnitTransitionCocycle X U) {W W' : Opens X.carrier} (h : W' ≤ W) :
    (∀ i, X.presheaf.obj (op (W ⊓ U i))) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
      (∀ i, X.presheaf.obj (op (W' ⊓ U i))) := by
  refine
    { toFun := fun s i => X.presheaf.map (homOfLE (inf_le_inf_right (U i) h)).op (s i)
      map_add' := ?_
      map_smul' := ?_ }
  · intro s t
    funext i
    simp
  · intro r s
    funext i
    change X.presheaf.map (homOfLE (inf_le_inf_right (U i) h)).op
        (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r * s i) =
      X.presheaf.map (homOfLE (inf_le_left : W' ⊓ U i ≤ W')).op
          (X.presheaf.map (homOfLE h).op r) *
        X.presheaf.map (homOfLE (inf_le_inf_right (U i) h)).op (s i)
    rw [map_mul]
    congr 1
    have hmaps : X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op ≫
        X.presheaf.map (homOfLE (inf_le_inf_right (U i) h)).op =
      X.presheaf.map (homOfLE h).op ≫
        X.presheaf.map (homOfLE (inf_le_left : W' ⊓ U i ≤ W')).op := by
      rw [← X.presheaf.map_comp, ← X.presheaf.map_comp,
        show (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op ≫
            (homOfLE (inf_le_inf_right (U i) h)).op =
          (homOfLE h).op ≫ (homOfLE (inf_le_left : W' ⊓ U i ≤ W')).op from
            Subsingleton.elim _ _]
    exact congrArg (fun φ => φ r) hmaps

/-- Restriction of compatible families, as a morphism of modules over restriction of
functions. -/
noncomputable def sectionsMapHom (D : UnitTransitionCocycle X U) {W W' : Opens X.carrier}
    (h : W' ≤ W) :
    ModuleCat.of (X.presheaf.obj (op W)) (D.sectionsSubmodule W) ⟶
      (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).obj
        (ModuleCat.of (X.presheaf.obj (op W')) (D.sectionsSubmodule W')) := by
  let M' := ModuleCat.of (X.presheaf.obj (op W')) (D.sectionsSubmodule W')
  letI : Module (X.presheaf.obj (op W)) M' :=
    Module.compHom M' (X.presheaf.map (homOfLE h).op).hom
  letI : Module (X.presheaf.obj (op W)) (D.sectionsSubmodule W') :=
    Module.compHom (D.sectionsSubmodule W') (X.presheaf.map (homOfLE h).op).hom
  exact ModuleCat.ofHom (show D.sectionsSubmodule W →ₗ[X.presheaf.obj (op W)] M' from
    { toFun := D.sectionsMap h
      map_add' := by
        intro s t
        apply Subtype.ext
        funext i
        change (D.sectionsMap h (s + t)).val i =
          (D.sectionsMap h s).val i + (D.sectionsMap h t).val i
        rw [sectionsMap_val, sectionsMap_val, sectionsMap_val]
        simp [map_add]
      map_smul' := by
        intro r s
        exact Subtype.ext (D.sectionsProdMap h |>.map_smulₛₗ r s.val) })

/-- The glued presheaf of modules. -/
noncomputable def gluedPresheafOfModules (D : UnitTransitionCocycle X U) :
    PresheafOfModules (structureSheaf X.sheaf).obj where
  obj V := ModuleCat.of (X.presheaf.obj V) (D.sectionsSubmodule V.unop)
  map f := D.sectionsMapHom f.unop.le
  map_id V := by
    apply ModuleCat.hom_ext
    ext s
    change D.sectionsMap (le_rfl : V.unop ≤ V.unop) s = s
    apply Subtype.ext
    funext i
    rw [sectionsMap_val,
      show (homOfLE (inf_le_inf_right (U i) (le_rfl : V.unop ≤ V.unop))).op =
        𝟙 (op (V.unop ⊓ U i)) from Subsingleton.elim _ _, X.presheaf.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext s
    change D.sectionsMap (g.unop.le.trans f.unop.le) s =
      D.sectionsMap g.unop.le (D.sectionsMap f.unop.le s)
    apply Subtype.ext
    funext i
    rw [sectionsMap_val, sectionsMap_val, sectionsMap_val]
    have hcomp := X.presheaf.map_comp (homOfLE (inf_le_inf_right (U i) f.unop.le)).op
      (homOfLE (inf_le_inf_right (U i) g.unop.le)).op
    rw [show (homOfLE (inf_le_inf_right (U i) f.unop.le)).op ≫
          (homOfLE (inf_le_inf_right (U i) g.unop.le)).op =
        (homOfLE (inf_le_inf_right (U i) (g.unop.le.trans f.unop.le))).op from
          Subsingleton.elim _ _] at hcomp
    simpa only [ConcreteCategory.comp_apply] using congrArg (fun φ => φ (s.val i)) hcomp

/-- The presheaf of modules glued from a unit transition cocycle is a sheaf. -/
theorem gluedPresheafOfModules_isSheaf (D : UnitTransitionCocycle X U) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of X))
      D.gluedPresheafOfModules.presheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)
    D.gluedPresheafOfModules.presheaf).mpr D.toGlueData.gluedPresheaf_isSheaf

/-- The sheaf of modules glued from a unit transition cocycle. -/
@[ega "0 5.4.7", ega "IV 21.3.6"]
noncomputable def glue (D : UnitTransitionCocycle X U) :
    _root_.SheafOfModules (structureSheaf X.sheaf) :=
  ⟨D.gluedPresheafOfModules, D.gluedPresheafOfModules_isSheaf⟩

/-- Two units with the same ratio against a third have proportional inverses. -/
theorem unit_ratio_eq {R : Type*} [CommRing R] (a b c : Rˣ) {x y : R}
    (hc : c.val * a.val = b.val) (hx : c.val * x = y) :
    x * (a⁻¹).val = y * (b⁻¹).val := by
  have hb : b = c * a := Units.ext hc.symm
  rw [hb, ← hx, mul_inv_rev, Units.val_mul]
  linear_combination (-(x * (a⁻¹).val)) * c.mul_inv

/-- A compatible family whose coordinates are units in every chart freely generates the glued
module over every open. -/
theorem smul_bijective_of_isUnit (D : UnitTransitionCocycle X U)
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (W : Opens X.carrier)
    (s : D.sectionsSubmodule W) (hs : ∀ i, IsUnit (s.val i)) :
    Function.Bijective (fun r : X.presheaf.obj (op W) => r • s) := by
  classical
  have hcov : W ≤ ⨆ i, W ⊓ U i := by
    rw [← inf_iSup_eq]
    exact le_inf le_rfl (le_top.trans hU)
  constructor
  · intro r t hrt
    exact X.sheaf.eq_of_locally_eq' (fun i => W ⊓ U i) W (fun _ => homOfLE inf_le_left) hcov
      _ _ fun i => (hs i).mul_right_cancel (congrArg (fun a : D.sectionsSubmodule W => a.val i) hrt)
  · intro t
    let a (i : ι) := (hs i).unit
    let r (i : ι) := t.val i * ((a i)⁻¹).val
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun i => W ⊓ U i) r := by
      intro i j
      let f := (X.presheaf.map
        (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op).hom
      let g := (X.presheaf.map
        (homOfLE (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op).hom
      show f (t.val i * ((a i)⁻¹).val) = g (t.val j * ((a j)⁻¹).val)
      rw [map_mul, map_mul]
      let c := D.transition i j (W ⊓ U i ⊓ (W ⊓ U j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      have hca : c.val * (Units.map f.toMonoidHom (a i)).val =
          (Units.map g.toMonoidHom (a j)).val := by
        show c.val * f (a i).val = g (a j).val
        dsimp only [a]
        rw [IsUnit.unit_spec, IsUnit.unit_spec]
        exact s.property i j
      show f (t.val i) * (Units.map f.toMonoidHom ((a i)⁻¹)).val =
        g (t.val j) * (Units.map g.toMonoidHom ((a j)⁻¹)).val
      rw [map_inv, map_inv]
      exact unit_ratio_eq (Units.map f.toMonoidHom (a i))
        (Units.map g.toMonoidHom (a j)) c hca (t.property i j)
    obtain ⟨r', hr', -⟩ := X.sheaf.existsUnique_gluing' (fun i => W ⊓ U i) W
      (fun _ => homOfLE inf_le_left) hcov r hcompat
    refine ⟨r', Subtype.ext (funext fun i => ?_)⟩
    show X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r' * s.val i = t.val i
    have he : X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r' = r i := hr' i
    rw [he]
    show (t.val i * ((a i)⁻¹).val) * s.val i = t.val i
    rw [← (hs i).unit_spec]
    simp [a, mul_assoc]

/-- Unit coordinates remain units on every smaller open, so a compatible family of unit
coordinates is a local generator of the glued module. -/
noncomputable def generatorOfUnitCoordinates (D : UnitTransitionCocycle X U)
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (W : Opens X.carrier)
    (s : D.sectionsSubmodule W) (hs : ∀ i, IsUnit (s.val i)) :
    GeneratorSections X D.glue W := by
  refine ⟨s, fun V h => D.smul_bijective_of_isUnit hU V (D.sectionsMap h s) fun i => ?_⟩
  rw [sectionsMap_val]
  exact (hs i).map _

/-- Reading off the `i`-th coordinate trivializes the glued module over any open inside the
`i`-th chart. -/
noncomputable def chartLinearEquiv (D : UnitTransitionCocycle X U) (i : ι)
    {V : Opens X.carrier} (hV : V ≤ U i) :
    D.sectionsSubmodule V ≃ₗ[X.presheaf.obj (op V)] X.presheaf.obj (op V) where
  __ := D.toGlueData.sectionsEquiv i hV
  map_add' s t := by
    change X.presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.val i + t.val i) = _
    exact map_add _ _ _
  map_smul' r s := by
    change X.presheaf.map (homOfLE (le_inf le_rfl hV)).op
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op r * s.val i) = _
    rw [map_mul]
    have hcomp := congrArg (fun q => q r)
      (X.presheaf.map_comp (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op
        (homOfLE (le_inf le_rfl hV)).op)
    rw [show (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op ≫ (homOfLE (le_inf le_rfl hV)).op =
      𝟙 (op V) from Subsingleton.elim _ _, X.presheaf.map_id] at hcomp
    change r = X.presheaf.map (homOfLE (le_inf le_rfl hV)).op
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op r) at hcomp
    rw [← hcomp]
    rfl

/-- The identification of sections of the glued sheaf over an open of the `i`-th chart with
functions on that open commutes with restriction. -/
theorem chartLinearEquiv_restrict (D : UnitTransitionCocycle X U) (i : ι)
    {V W : Opens X.carrier} (hV : V ≤ U i) (h : W ≤ V) (s : D.glue.val.obj (op V)) :
    D.chartLinearEquiv i (h.trans hV) (D.glue.val.restrictₛₗ (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (D.chartLinearEquiv i hV s) :=
  D.toGlueData.sectionsEquiv_map i hV h s

/-- The transition units out of the `i`-th chart, read as a compatible family of local
coordinates over `U i`. This is the section whose `i`-th coordinate is one. -/
def chartSection (D : UnitTransitionCocycle X U) (i : ι) : D.sectionsSubmodule (U i) := by
  refine ⟨fun j => (D.transition i j (U i ⊓ U j) inf_le_left inf_le_right).val, fun j k => ?_⟩
  set Z : Opens X.carrier := U i ⊓ U j ⊓ (U i ⊓ U k) with hZ
  have hZi : Z ≤ U i := inf_le_left.trans inf_le_left
  have hZj : Z ≤ U j := inf_le_left.trans inf_le_right
  have hZk : Z ≤ U k := inf_le_right.trans inf_le_right
  have hj : X.presheaf.map (homOfLE (inf_le_left : Z ≤ U i ⊓ U j)).op
      (D.transition i j (U i ⊓ U j) inf_le_left inf_le_right).val =
      (D.transition i j Z hZi hZj).val :=
    congrArg Units.val (D.restrict (i := i) (j := j)
      (inf_le_left : U i ⊓ U j ≤ U i) (inf_le_right : U i ⊓ U j ≤ U j)
      (inf_le_left : Z ≤ U i ⊓ U j))
  have hk : X.presheaf.map (homOfLE (inf_le_right : Z ≤ U i ⊓ U k)).op
      (D.transition i k (U i ⊓ U k) inf_le_left inf_le_right).val =
      (D.transition i k Z hZi hZk).val :=
    congrArg Units.val (D.restrict (i := i) (j := k)
      (inf_le_left : U i ⊓ U k ≤ U i) (inf_le_right : U i ⊓ U k ≤ U k)
      (inf_le_right : Z ≤ U i ⊓ U k))
  rw [hj, hk]
  simpa using congrArg Units.val (D.cocycle i j k Z hZi hZj hZk)

/-- The section with `i`-th coordinate one generates the glued module throughout the `i`-th
chart: all its coordinates are transition units. -/
noncomputable def chartGenerator (D : UnitTransitionCocycle X U)
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (i : ι) :
    GeneratorSections X D.glue (U i) :=
  D.generatorOfUnitCoordinates hU (U i) (D.chartSection i) fun _ => Units.isUnit _

/-- The sectionwise chart trivializations assemble into an isomorphism on the localized site. -/
noncomputable def chartOverIso (D : UnitTransitionCocycle X U) (i : ι) :
    D.glue.over (U i) ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over (U i)) := by
  apply (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V => (D.chartLinearEquiv i V.unop.hom.le).toModuleIso) ?_
  intro V W g
  apply ModuleCat.hom_ext
  ext s
  exact D.chartLinearEquiv_restrict i V.unop.hom.le g.unop.left.le s

/-- **A unit cocycle on a covering glues to an invertible module.** This is the gluing step of
Tag 0BCY; invertibility is clause 1 of Tag 0B8M applied to the chart trivializations. -/
theorem isInvertible_glue (D : UnitTransitionCocycle X U)
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) :
    IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property D.glue :=
  isInvertible_of_coversTop_iso_unit X.sheaf.obj (structureSheaf X.sheaf).property D.glue
    ((Opens.coversTop_iff X U).mpr (top_unique hU)) D.chartOverIso

end

end UnitTransitionCocycle

end Stacks.SheafOfModules
