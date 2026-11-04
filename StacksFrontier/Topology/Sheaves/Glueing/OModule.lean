module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import StacksFrontier.Topology.Sheaves.Glueing.AlgebraicStructure

/-!
# Glueing sheaves of `𝒪`-modules along an open covering

Let `X` be a topological space and let `𝒪` be a presheaf of rings on `X`. A *glueing datum* for
sheaves of `𝒪`-modules with respect to a family of opens `U : ι → Opens X` consists of a sheaf of
`𝒪|_{U i}`-modules `F i` on each `U i` together with comparison isomorphisms
`φ i j : (F i)|_{U i ∩ U j} ≅ (F j)|_{U i ∩ U j}` of `𝒪`-modules satisfying the cocycle condition.
This file builds from such a datum a sheaf of `𝒪`-modules on `X`.

## Main definitions

* `TopCat.Sheaf.OModuleLocalPresheaf`: a presheaf of `𝒪`-modules on an open `U` of `X`, presented
  as data indexed by the opens of `X` contained in `U`, with semilinear restriction maps.
* `TopCat.Sheaf.OModuleGlueData`: a glueing datum of sheaves of `𝒪`-modules.
* `TopCat.Sheaf.OModuleGlueData.gluedModule`: the `𝒪(W)`-module structure on the glued sections.
* `TopCat.Sheaf.OModuleGlueData.gluedPresheafOfModules`: the glued presheaf of `𝒪`-modules.
* `TopCat.Sheaf.OModuleGlueData.sectionsLinearEquiv`: the glued sections over an open `V ≤ U i`
  are the sections of `F i` over `V`, as `𝒪(V)`-modules.

## Main results

* `TopCat.Sheaf.OModuleGlueData.isSheaf_gluedPresheafOfModules`: **the glued presheaf of
  `𝒪`-modules is a sheaf.**
* `TopCat.Sheaf.OModuleGlueData.gluedPresheafOfModules_presheaf`: its underlying presheaf of
  abelian groups is the glued presheaf of abelian groups.

## Implementation notes

The comparison isomorphism `φ i j` is given over every open contained in both `U i` and `U j`,
so an overlap is never required to be a member of the covering family, and the covering
hypothesis `⨆ i, U i = ⊤` is not assumed.

`OModuleGlueData.toAddGlueData` is an ordinary definition, so the module structures it forgets are
invisible to typeclass synthesis on its sections; the instances `OModuleGlueData.moduleSheafObj`
and `OModuleGlueData.gluedModule` put them back, stated at exactly the shapes that occur in
`AddGlueData.sectionsAddSubgroup` and in `PresheafOfModules.ofPresheaf`.

Restriction maps are recorded as bundled semilinear maps, not as morphisms of `ModuleCat` into a
restriction of scalars, so that the codomain of a restriction map is literally the module of
sections over the smaller open and rewriting under it does not fail the motive check.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-! ### Restriction of scalars along inclusions of opens -/

/-- Restricting a scalar twice along inclusions of opens is restricting once. -/
theorem map_homOfLE_op_map_homOfLE_op_apply (𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}) {V W Z : Opens X}
    (hWV : W ≤ V) (hZW : Z ≤ W) (r : 𝒪.obj (op V)) :
    𝒪.map (homOfLE hZW).op (𝒪.map (homOfLE hWV).op r)
      = 𝒪.map (homOfLE (hZW.trans hWV)).op r := by
  rw [← ConcreteCategory.comp_apply, ← 𝒪.map_comp,
    show (homOfLE hWV).op ≫ (homOfLE hZW).op = (homOfLE (hZW.trans hWV)).op from
      Subsingleton.elim _ _]

/-- Restricting a scalar along the identity inclusion does nothing. -/
theorem map_homOfLE_op_refl_apply (𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}) {V : Opens X}
    (h : V ≤ V) (r : 𝒪.obj (op V)) : 𝒪.map (homOfLE h).op r = r := by
  rw [show (homOfLE h).op = 𝟙 (op V) from Subsingleton.elim _ _, 𝒪.map_id]
  rfl

/-! ### Presheaves of `𝒪`-modules on an open subset -/

/-- A presheaf of `𝒪`-modules on an open `U` of `X`, presented as data indexed by the opens of `X`
contained in `U`: an `𝒪(V)`-module of sections over each `V ≤ U`, with restriction maps semilinear
along the restriction maps of `𝒪`.

This is `TopCat.Sheaf.LocalPresheaf` with values in modules over the varying ring `𝒪(V)`, and the
local analogue of `PresheafOfModules 𝒪`. -/
structure OModuleLocalPresheaf {X : TopCat.{u}} (𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}) (U : Opens X) where
  /-- The `𝒪(V)`-module of sections over an open `V` of `X` contained in `U`. -/
  obj : (V : Opens X) → V ≤ U → ModuleCat.{u} (𝒪.obj (op V))
  /-- Restriction of sections along an inclusion `W ≤ V` of opens contained in `U`, semilinear
  along the restriction map `𝒪(V) → 𝒪(W)` of `𝒪`. -/
  map : ∀ {V W : Opens X} {hV : V ≤ U} (hWV : W ≤ V),
    obj V hV →ₛₗ[(𝒪.map (homOfLE hWV).op).hom] obj W (hWV.trans hV)
  /-- Restricting along the identity is the identity. -/
  map_id : ∀ {V : Opens X} {hV : V ≤ U} (s : obj V hV), map (hV := hV) le_rfl s = s
  /-- Restriction is compatible with composition of inclusions. -/
  map_map : ∀ {V W Z : Opens X} {hV : V ≤ U} (hWV : W ≤ V) (hZW : Z ≤ W) (s : obj V hV),
    map hZW (map hWV s) = map (hZW.trans hWV) s

namespace OModuleLocalPresheaf

variable {U : Opens X}

/-- The underlying presheaf of abelian groups of a presheaf of `𝒪`-modules on `U`. -/
def toAddLocalPresheaf (F : OModuleLocalPresheaf 𝒪 U) : AddLocalPresheaf X U where
  obj V hV := AddCommGrpCat.of (F.obj V hV)
  map hWV := AddCommGrpCat.ofHom (F.map hWV).toAddMonoidHom
  map_id := ConcreteCategory.hom_ext _ _ fun s => F.map_id s
  map_map hWV hZW := ConcreteCategory.hom_ext _ _ fun s => F.map_map hWV hZW s

/-- The sheaf condition for a presheaf of `𝒪`-modules on `U`: the sheaf condition for the
underlying presheaf of sets. -/
def IsSheaf (F : OModuleLocalPresheaf 𝒪 U) : Prop :=
  F.toAddLocalPresheaf.toLocalPresheaf.IsSheaf

end OModuleLocalPresheaf

/-! ### Glueing data of sheaves of `𝒪`-modules -/

/-- Glueing data of sheaves of `𝒪`-modules with respect to a family of opens `U : ι → Opens X`: a
sheaf of `𝒪`-modules on each `U i`, plus comparison isomorphisms of `𝒪`-modules over the overlaps
satisfying the cocycle condition.

The comparison isomorphism `φ i j` is an isomorphism of `𝒪(V)`-modules for every open `V`
contained in both `U i` and `U j`; such a `V` is not required to be a member of the family. -/
structure OModuleGlueData {X : TopCat.{u}} (𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}) {ι : Type u}
    (U : ι → Opens X) where
  /-- The sheaf of `𝒪`-modules on `U i`. -/
  sheaf : ∀ i, OModuleLocalPresheaf 𝒪 (U i)
  /-- Each `sheaf i` satisfies the sheaf condition. -/
  isSheaf : ∀ i, (sheaf i).IsSheaf
  /-- The comparison isomorphism `φ i j` of `𝒪(V)`-modules, on sections over an open `V`
  contained in both `U i` and `U j`. -/
  trans : ∀ (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j),
    (sheaf i).obj V hi ≃ₗ[𝒪.obj (op V)] (sheaf j).obj V hj
  /-- The comparison isomorphisms commute with the restriction maps. -/
  trans_map : ∀ (i j : ι) {V W : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
      (s : (sheaf i).obj V hi),
    trans i j (hWV.trans hi) (hWV.trans hj) ((sheaf i).map hWV s)
      = (sheaf j).map hWV (trans i j hi hj s)
  /-- The cocycle condition `φ j k ∘ φ i j = φ i k`. -/
  trans_trans : ∀ (i j k : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
      (s : (sheaf i).obj V hi),
    trans j k hj hk (trans i j hi hj s) = trans i k hi hk s

namespace OModuleGlueData

variable {ι : Type u} {U : ι → Opens X} (D : OModuleGlueData 𝒪 U)

/-- The underlying glueing data of sheaves of abelian groups. -/
def toAddGlueData : AddGlueData X U where
  sheaf i := (D.sheaf i).toAddLocalPresheaf
  isSheaf := D.isSheaf
  trans := fun i j {_V} hi hj => (D.trans i j hi hj).toAddEquiv.toAddCommGrpIso
  trans_map := fun i j {_V _W} hi hj hWV => ConcreteCategory.hom_ext _ _ fun s => by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact D.trans_map i j hi hj hWV s
  trans_trans := fun i j k {_V} hi hj hk => ConcreteCategory.hom_ext _ _ fun s => by
    rw [ConcreteCategory.comp_apply]
    exact D.trans_trans i j k hi hj hk s

/-! ### Recovering the module structures after forgetting them -/

/-- The sections of `D.toAddGlueData.sheaf i` over `V` are an `𝒪(V)`-module: they are the sections
of `D.sheaf i` over `V`. -/
instance moduleSheafObj (i : ι) (V : Opens X) (hV : V ≤ U i) :
    Module (𝒪.obj (op V)) ((D.toAddGlueData.sheaf i).obj V hV) :=
  inferInstanceAs (Module (𝒪.obj (op V)) ((D.sheaf i).obj V hV))

/-- The restriction maps of `D.toAddGlueData.sheaf i` are semilinear. -/
theorem sheaf_map_smul (i : ι) {V W : Opens X} {hV : V ≤ U i} (hWV : W ≤ V) (r : 𝒪.obj (op V))
    (s : (D.toAddGlueData.sheaf i).obj V hV) :
    (D.toAddGlueData.sheaf i).map hWV (r • s)
      = 𝒪.map (homOfLE hWV).op r • (D.toAddGlueData.sheaf i).map hWV s :=
  map_smulₛₗ ((D.sheaf i).map (hV := hV) hWV) r s

/-- The restriction maps of `D.toAddGlueData.sheaf i` are additive. -/
theorem sheaf_map_add (i : ι) {V W : Opens X} {hV : V ≤ U i} (hWV : W ≤ V)
    (s t : (D.toAddGlueData.sheaf i).obj V hV) :
    (D.toAddGlueData.sheaf i).map hWV (s + t)
      = (D.toAddGlueData.sheaf i).map hWV s + (D.toAddGlueData.sheaf i).map hWV t :=
  map_add ((D.sheaf i).map (hV := hV) hWV) s t

/-- The comparison isomorphisms of `D.toAddGlueData` are `𝒪(V)`-linear. -/
theorem trans_smul (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (r : 𝒪.obj (op V))
    (s : (D.toAddGlueData.sheaf i).obj V hi) :
    (D.toAddGlueData.trans i j hi hj).hom (r • s)
      = r • (D.toAddGlueData.trans i j hi hj).hom s :=
  map_smul (D.trans i j hi hj) r s

/-! ### The `𝒪(W)`-module structure on the glued sections -/

/-- The glued sections are stable under the componentwise scalar action. -/
theorem smul_mem_sectionsAddSubgroup (W : Opens X) (r : 𝒪.obj (op W))
    {s : ∀ i, (D.toAddGlueData.sheaf i).obj (W ⊓ U i) inf_le_right}
    (hs : s ∈ D.toAddGlueData.sectionsAddSubgroup W) :
    (fun i => 𝒪.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r • s i)
      ∈ D.toAddGlueData.sectionsAddSubgroup W := by
  intro i j
  rw [D.sheaf_map_smul, D.sheaf_map_smul, map_homOfLE_op_map_homOfLE_op_apply,
    map_homOfLE_op_map_homOfLE_op_apply, D.trans_smul, hs i j]

/-- **The glued sections over an open `W` form an `𝒪(W)`-module**, a scalar acting in the `i`-th
component after restriction along `𝒪(W) → 𝒪(W ⊓ U i)`. -/
noncomputable instance gluedModule (Y : (Opens X)ᵒᵖ) :
    Module (𝒪.obj Y) (D.toAddGlueData.gluedAddPresheaf.obj Y) where
  smul r s := ⟨fun i => 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r • s.1 i,
    D.smul_mem_sectionsAddSubgroup Y.unop r s.2⟩
  one_smul s := Subtype.ext (funext fun i => by
    change 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op (1 : 𝒪.obj Y) • s.1 i = s.1 i
    rw [map_one, one_smul])
  mul_smul r₁ r₂ s := Subtype.ext (funext fun i => by
    change 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op (r₁ * r₂) • s.1 i
      = 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r₁
        • (𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r₂ • s.1 i)
    rw [map_mul, mul_smul])
  smul_zero r := Subtype.ext (funext fun i => by
    change 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r
        • (0 : (D.toAddGlueData.sheaf i).obj (Y.unop ⊓ U i) inf_le_right) = 0
    rw [smul_zero])
  smul_add r s t := Subtype.ext (funext fun i => by
    change 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r • (s.1 i + t.1 i)
      = 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r • s.1 i
        + 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r • t.1 i
    rw [smul_add])
  add_smul r₁ r₂ s := Subtype.ext (funext fun i => by
    change 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op (r₁ + r₂) • s.1 i
      = 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r₁ • s.1 i
        + 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r₂ • s.1 i
    rw [map_add, add_smul])
  zero_smul s := Subtype.ext (funext fun i => by
    change 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op (0 : 𝒪.obj Y) • s.1 i = 0
    rw [map_zero, zero_smul])

/-- A scalar acts on a glued section componentwise, after restriction of scalars. -/
theorem gluedModule_smul_coe {Y : (Opens X)ᵒᵖ} (r : 𝒪.obj Y)
    (s : D.toAddGlueData.gluedAddPresheaf.obj Y) (i : ι) :
    (r • s).1 i = 𝒪.map (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op r • s.1 i :=
  rfl

/-- Restriction of glued sections is semilinear, stated for an inclusion of opens. -/
theorem gluedAddPresheaf_map_homOfLE_op_smul {W W' : Opens X} (h : W' ≤ W) (r : 𝒪.obj (op W))
    (m : D.toAddGlueData.gluedAddPresheaf.obj (op W)) :
    D.toAddGlueData.gluedAddPresheaf.map (homOfLE h).op (r • m)
      = 𝒪.map (homOfLE h).op r • D.toAddGlueData.gluedAddPresheaf.map (homOfLE h).op m := by
  refine Subtype.ext (funext fun i => ?_)
  change (D.toAddGlueData.sheaf i).map (inf_le_inf_right (U i) h)
      (𝒪.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r • m.1 i)
    = 𝒪.map (homOfLE (inf_le_left : W' ⊓ U i ≤ W')).op (𝒪.map (homOfLE h).op r)
      • (D.toAddGlueData.sheaf i).map (inf_le_inf_right (U i) h) (m.1 i)
  rw [D.sheaf_map_smul, map_homOfLE_op_map_homOfLE_op_apply,
    map_homOfLE_op_map_homOfLE_op_apply]

/-- The restriction maps of the glued presheaf of abelian groups are semilinear. -/
theorem gluedAddPresheaf_map_smul ⦃Y Z : (Opens X)ᵒᵖ⦄ (g : Y ⟶ Z) (r : 𝒪.obj Y)
    (m : D.toAddGlueData.gluedAddPresheaf.obj Y) :
    D.toAddGlueData.gluedAddPresheaf.map g (r • m)
      = 𝒪.map g r • D.toAddGlueData.gluedAddPresheaf.map g m := by
  rw [show g = (homOfLE (Quiver.Hom.unop g).le).op from Subsingleton.elim _ _]
  exact D.gluedAddPresheaf_map_homOfLE_op_smul (Quiver.Hom.unop g).le r m

/-! ### The glued sheaf of `𝒪`-modules -/

/-- **The glued presheaf of `𝒪`-modules.** Its underlying presheaf of abelian groups is
`D.toAddGlueData.gluedAddPresheaf`, and its `𝒪(W)`-module of sections over `W` is
`gluedModule`. -/
@[stacks 00AM "sheaves of O-modules"]
noncomputable def gluedPresheafOfModules : PresheafOfModules.{u} 𝒪 :=
  PresheafOfModules.ofPresheaf D.toAddGlueData.gluedAddPresheaf D.gluedAddPresheaf_map_smul

/-- The underlying presheaf of abelian groups of the glued presheaf of `𝒪`-modules is the glued
presheaf of abelian groups. -/
@[simp] theorem gluedPresheafOfModules_presheaf :
    D.gluedPresheafOfModules.presheaf = D.toAddGlueData.gluedAddPresheaf := rfl

/-- **The presheaf of `𝒪`-modules glued from a glueing datum of sheaves of `𝒪`-modules is a
sheaf.** -/
@[stacks 00AM "sheaves of O-modules"]
theorem isSheaf_gluedPresheafOfModules :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      D.gluedPresheafOfModules.presheaf :=
  D.toAddGlueData.gluedAddPresheaf_isSheaf

/-- **The comparison isomorphism `φ i : F|_{U i} ≅ F i`**, on sections over an open `V ≤ U i`, as
an isomorphism of `𝒪(V)`-modules, whose underlying bijection is
`TopCat.Sheaf.GlueData.sectionsEquiv`. -/
noncomputable def sectionsLinearEquiv (i : ι) {V : Opens X} (hV : V ≤ U i) :
    D.gluedPresheafOfModules.obj (op V) ≃ₗ[𝒪.obj (op V)]
      (D.toAddGlueData.sheaf i).obj V hV where
  toFun := D.toAddGlueData.toGlueData.sectionsEquiv i hV
  invFun := (D.toAddGlueData.toGlueData.sectionsEquiv i hV).symm
  left_inv := (D.toAddGlueData.toGlueData.sectionsEquiv i hV).left_inv
  right_inv := (D.toAddGlueData.toGlueData.sectionsEquiv i hV).right_inv
  map_add' s t := D.sheaf_map_add i (le_inf le_rfl hV) (s.1 i) (t.1 i)
  map_smul' r s := by
    change (D.toAddGlueData.sheaf i).map (le_inf le_rfl hV)
        (𝒪.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op r • s.1 i)
      = r • (D.toAddGlueData.sheaf i).map (le_inf le_rfl hV) (s.1 i)
    rw [D.sheaf_map_smul, map_homOfLE_op_map_homOfLE_op_apply, map_homOfLE_op_refl_apply]

end OModuleGlueData

end TopCat.Sheaf
