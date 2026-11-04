module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import StacksFrontier.Topology.Sheaves.Glueing.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Glueing sheaves of algebraic structures along an open covering (Stacks 00AM)

Stacks 00AL glues a family of sheaves of *sets* `F i` on the members `U i` of an open covering of a
topological space `X`, along comparison isomorphisms `φ i j` over the overlaps, into a single sheaf
of sets on `X`. Stacks 00AM upgrades that construction to the algebraic settings: if each `F i` is
a sheaf of abelian groups, resp. of `R`-modules, and each `φ i j` is an isomorphism of such, then
the glued object is a sheaf of abelian groups, resp. of `R`-modules.

The construction needs nothing new. The sections of the glued sheaf over an open `W` were built in
Stacks 00AL as the equalizer
`F(W) = eq( ∏ i, F i (W ⊓ U i)  ⇉  ∏ i j, F i (W ⊓ U i ⊓ U j) )`,
and in the algebraic settings the two parallel maps are homomorphisms, so the equalizer is a
subobject of the product — an `AddSubgroup` in `AddGlueData.sectionsAddSubgroup`, a `Submodule` in
`ModuleGlueData.sectionsSubmodule`. That subobject is the glued object, and its underlying set is
*literally* — by `AddGlueData.gluedAddPresheaf_forget`, resp.
`ModuleGlueData.gluedModulePresheaf_forget`, both of which hold by `rfl` — the set of sections
glued in Stacks 00AL. The sheaf condition therefore transfers from Stacks 00AL along the forgetful
functor, by `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`.

## Main definitions

* `TopCat.Sheaf.AddLocalPresheaf`, `TopCat.Sheaf.ModuleLocalPresheaf`: a presheaf of abelian
  groups, resp. of `R`-modules, on an open `U` of `X`, presented as data indexed by the opens of
  `X` contained in `U`, exactly as `TopCat.Sheaf.LocalPresheaf` is for presheaves of sets.
* `TopCat.Sheaf.AddGlueData`, `TopCat.Sheaf.ModuleGlueData`: glueing data of sheaves of abelian
  groups, resp. of `R`-modules.
* `TopCat.Sheaf.AddGlueData.sectionsAddSubgroup`, `TopCat.Sheaf.ModuleGlueData.sectionsSubmodule`:
  the glued sections over an open `W`, as a subobject of `∏ i, F i (W ⊓ U i)`.
* `TopCat.Sheaf.AddGlueData.sectionsHom`, `TopCat.Sheaf.ModuleGlueData.sectionsHom`: the comparison
  map `φ i` of Stacks 00AL as a homomorphism.

## Main results

* `TopCat.Sheaf.AddGlueData.gluedAddPresheaf_forget`,
  `TopCat.Sheaf.ModuleGlueData.gluedModulePresheaf_forget`: the underlying presheaf of sets of the
  glued presheaf is the presheaf glued in Stacks 00AL.
* `TopCat.Sheaf.AddGlueData.gluedAddPresheaf_isSheaf`,
  `TopCat.Sheaf.ModuleGlueData.gluedModulePresheaf_isSheaf`: the glued presheaf of abelian groups,
  resp. of `R`-modules, is a sheaf in that category.
* `TopCat.Sheaf.AddGlueData.gluedAddSheaf`, `TopCat.Sheaf.ModuleGlueData.gluedModuleSheaf`: the
  glued sheaf of abelian groups, resp. of `R`-modules.

## Implementation notes

Opens are indexed as in the Tag 00AL glueing of sheaves of sets
(`StacksFrontier/Topology/Sheaves/Glueing/Sheaf.lean`): data on an open `U` of `X` is a
family indexed by an open `V` of `X` together with a proof `V ≤ U`. See the implementation notes
there.

The instance binder one would like to write, `[∀ i V hV, AddCommGroup ((D.sheaf i).obj V hV)]`, is
useless: typeclass synthesis cannot invent the containment proof `hV`. So the algebraic structure
is carried by bundled objects of `AddCommGrpCat`, resp. `ModuleCat R`, instead, and
`AddLocalPresheaf`/`AddGlueData` and `ModuleLocalPresheaf`/`ModuleGlueData` are separate structures
mapping to `LocalPresheaf`/`GlueData` by forgetting it.

The third case of Stacks 00AM, sheaves of `O`-modules for a sheaf of rings `O` on `X`, is not
treated here: there the `F i` are `O|_{U i}`-modules with semilinear restriction maps, which is a
genuinely different development. It is carried out by
`TopCat.Sheaf.OModuleGlueData` and its `gluedPresheafOfModules`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-! ### Presheaves of abelian groups on an open subset -/

/-- A presheaf of abelian groups on an open `U` of `X`, presented as data indexed by the opens of
`X` contained in `U`. This is `TopCat.Sheaf.LocalPresheaf` with values in `AddCommGrpCat`. -/
structure AddLocalPresheaf (X : TopCat.{u}) (U : Opens X) where
  /-- The abelian group of sections over an open `V` of `X` contained in `U`. -/
  obj : (V : Opens X) → V ≤ U → AddCommGrpCat.{u}
  /-- Restriction of sections along an inclusion `W ≤ V` of opens contained in `U`. -/
  map : ∀ {V W : Opens X} {hV : V ≤ U} (hWV : W ≤ V), obj V hV ⟶ obj W (hWV.trans hV)
  /-- Restricting along the identity is the identity. -/
  map_id : ∀ {V : Opens X} {hV : V ≤ U}, map (hV := hV) le_rfl = 𝟙 (obj V hV)
  /-- Restriction is compatible with composition of inclusions. -/
  map_map : ∀ {V W Z : Opens X} {hV : V ≤ U} (hWV : W ≤ V) (hZW : Z ≤ W),
      map (hV := hV) hWV ≫ map hZW = map (hZW.trans hWV)

namespace AddLocalPresheaf

variable {U : Opens X}

/-- The underlying presheaf of sets of a presheaf of abelian groups. -/
def toLocalPresheaf (F : AddLocalPresheaf X U) : LocalPresheaf X U where
  obj V hV := ToType (F.obj V hV)
  map hWV s := F.map hWV s
  map_id s := by rw [F.map_id]; simp
  map_map hWV hZW s := by rw [← ConcreteCategory.comp_apply, F.map_map]

/-- The sections of the underlying presheaf of sets over `V` are the elements of the abelian group
of sections `F.obj V hV`. -/
@[simp] theorem toLocalPresheaf_obj (F : AddLocalPresheaf X U) (V : Opens X) (hV : V ≤ U) :
    F.toLocalPresheaf.obj V hV = ToType (F.obj V hV) := rfl

/-- Restriction in the underlying presheaf of sets is the function underlying the restriction
homomorphism of `F`. -/
@[simp] theorem toLocalPresheaf_map (F : AddLocalPresheaf X U) {V W : Opens X} {hV : V ≤ U}
    (hWV : W ≤ V) (s : ToType (F.obj V hV)) : F.toLocalPresheaf.map hWV s = F.map hWV s := rfl

end AddLocalPresheaf

/-! ### Glueing data of sheaves of abelian groups -/

/-- Glueing data of sheaves of abelian groups with respect to the covering `X = ⋃ i, U i`: a sheaf
of abelian groups on each `U i` plus comparison isomorphisms of abelian groups over the overlaps
satisfying the cocycle condition. This is `TopCat.Sheaf.GlueData` with values in
`AddCommGrpCat`. -/
structure AddGlueData (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X) where
  /-- The sheaf of abelian groups on `U i`. -/
  sheaf : ∀ i, AddLocalPresheaf X (U i)
  /-- Each `sheaf i` satisfies the sheaf condition. -/
  isSheaf : ∀ i, (sheaf i).toLocalPresheaf.IsSheaf
  /-- The comparison isomorphism `φ i j` on sections over an open contained in both `U i` and
  `U j`. -/
  trans : ∀ (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j),
      (sheaf i).obj V hi ≅ (sheaf j).obj V hj
  /-- The comparison isomorphisms commute with the restriction maps. -/
  trans_map : ∀ (i j : ι) {V W : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V),
      (sheaf i).map hWV ≫ (trans i j (hWV.trans hi) (hWV.trans hj)).hom
        = (trans i j hi hj).hom ≫ (sheaf j).map hWV
  /-- The cocycle condition `φ j k ∘ φ i j = φ i k`. -/
  trans_trans : ∀ (i j k : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k),
      (trans i j hi hj).hom ≫ (trans j k hj hk).hom = (trans i k hi hk).hom

namespace AddGlueData

variable {ι : Type u} {U : ι → Opens X} (D : AddGlueData X U)

/-- The underlying glueing data of sheaves of sets. -/
def toGlueData : GlueData X U where
  sheaf i := (D.sheaf i).toLocalPresheaf
  isSheaf := D.isSheaf
  trans := fun i j {_V} hi hj => (D.trans i j hi hj).addCommGroupIsoToAddEquiv.toEquiv
  trans_map := fun i j {_V _W} hi hj hWV s =>
    congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _))
      (D.trans_map i j hi hj hWV)) s
  trans_trans := fun i j k {_V} hi hj hk s =>
    congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _))
      (D.trans_trans i j k hi hj hk)) s

/-- The sheaf of sets on `U i` of the underlying glueing data is the presheaf of sets underlying
the sheaf of abelian groups `D.sheaf i`. -/
@[simp] theorem toGlueData_sheaf (i : ι) : D.toGlueData.sheaf i = (D.sheaf i).toLocalPresheaf := rfl

/-- The comparison bijection of the underlying glueing data of sets is the function underlying the
comparison isomorphism of abelian groups `φ i j`. -/
@[simp] theorem toGlueData_trans (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j)
    (s : ToType ((D.sheaf i).obj V hi)) :
    D.toGlueData.trans i j hi hj s = (D.trans i j hi hj).hom s := rfl

/-! ### The glued sheaf of abelian groups -/

/-- The glued sections over an open `W`, as an additive subgroup of `∏ i, F i (W ⊓ U i)`: this is
the equalizer of Stacks 00AM, whose defining equations are homomorphisms of abelian groups. Its
carrier is by construction the compatibility condition defining `GlueData.Sections`. -/
def sectionsAddSubgroup (W : Opens X) :
    AddSubgroup (∀ i, ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right)) where
  carrier := {s | ∀ i j : ι, (D.trans i j (V := W ⊓ U i ⊓ (W ⊓ U j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).hom
        ((D.sheaf i).map (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i) (s i))
      = (D.sheaf j).map (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j) (s j)}
  zero_mem' := fun i j => by simp
  add_mem' := fun hs ht i j => by simp [hs i j, ht i j]
  neg_mem' := fun hs i j => by simp [hs i j]

/-- Componentwise restriction on the ambient product `∏ i, F i (W ⊓ U i)`. -/
def sectionsProdMap {W W' : Opens X} (h : W' ≤ W) :
    (∀ i, ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right)) →+
      ∀ i, ToType ((D.sheaf i).obj (W' ⊓ U i) inf_le_right) :=
  AddMonoidHom.mk' (fun s i => (D.sheaf i).map (inf_le_inf_right (U i) h) (s i))
    fun _ _ => funext fun _ => by simp

/-- Restriction of the glued sections, as a homomorphism of abelian groups. Its underlying map is
`GlueData.sectionsMap`. -/
def sectionsMapHom {W W' : Opens X} (h : W' ≤ W) :
    AddCommGrpCat.of (D.sectionsAddSubgroup W) ⟶ AddCommGrpCat.of (D.sectionsAddSubgroup W') :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (D.toGlueData.sectionsMap h) fun s t =>
    Subtype.ext (map_add (D.sectionsProdMap h) s.1 t.1))

/-- The glued presheaf of abelian groups. -/
def gluedAddPresheaf : X.Presheaf AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (D.sectionsAddSubgroup W.unop)
  map h := D.sectionsMapHom h.unop.le
  map_id W := by
    refine ConcreteCategory.hom_ext _ _ fun s => Subtype.ext (funext fun i => ?_)
    exact (D.sheaf i).toLocalPresheaf.map_id _
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun s => Subtype.ext (funext fun i => ?_)
    exact ((D.sheaf i).toLocalPresheaf.map_map _ _ _).symm

/-- **Stacks 00AM.** The underlying presheaf of sets of the glued presheaf of abelian groups is the
presheaf of sets glued in Stacks 00AL: the additive subgroup cut out of `∏ i, F i (W ⊓ U i)` by the
equalizer equations has, as its underlying set, exactly the set of compatible families. -/
@[stacks 00AM]
theorem gluedAddPresheaf_forget :
    D.gluedAddPresheaf ⋙ CategoryTheory.forget AddCommGrpCat = D.toGlueData.gluedPresheaf := rfl

/-- **Stacks 00AM.** The presheaf of abelian groups glued from a glueing data of sheaves of abelian
groups is a sheaf of abelian groups. Since its underlying presheaf of sets is the sheaf of Stacks
00AL, this is the sheaf condition of Stacks 00AL read through the forgetful functor. -/
@[stacks 00AM, ega "0 4.1.7" "partial"]
theorem gluedAddPresheaf_isSheaf : D.gluedAddPresheaf.IsSheaf :=
  (Presheaf.isSheaf_iff_isSheaf_comp (CategoryTheory.forget AddCommGrpCat) _).2
    (D.gluedAddPresheaf_forget ▸ D.toGlueData.gluedPresheaf_isSheaf)

/-- The sheaf of abelian groups on `X` glued from a glueing data of sheaves of abelian groups. -/
@[ega "0 4.1.7" "partial"]
def gluedAddSheaf : X.Sheaf AddCommGrpCat.{u} := ⟨D.gluedAddPresheaf, D.gluedAddPresheaf_isSheaf⟩

/-- The comparison map `φ i : F|_{U i} ⟶ F i` of Stacks 00AL, on sections over an open `V ≤ U i`,
as a homomorphism of abelian groups. -/
def sectionsHom (i : ι) {V : Opens X} (hV : V ≤ U i) :
    AddCommGrpCat.of (D.sectionsAddSubgroup V) ⟶ (D.sheaf i).obj V hV :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun s => (D.sheaf i).map (le_inf le_rfl hV) (s.1 i))
    fun _ _ => by simp)

end AddGlueData

/-! ### Presheaves of modules on an open subset -/

/-- A presheaf of `R`-modules on an open `U` of `X`, presented as data indexed by the opens of `X`
contained in `U`. This is `TopCat.Sheaf.LocalPresheaf` with values in `ModuleCat R`. -/
structure ModuleLocalPresheaf (R : Type u) [Ring R] (X : TopCat.{u}) (U : Opens X) where
  /-- The `R`-module of sections over an open `V` of `X` contained in `U`. -/
  obj : (V : Opens X) → V ≤ U → ModuleCat.{u} R
  /-- Restriction of sections along an inclusion `W ≤ V` of opens contained in `U`. -/
  map : ∀ {V W : Opens X} {hV : V ≤ U} (hWV : W ≤ V), obj V hV ⟶ obj W (hWV.trans hV)
  /-- Restricting along the identity is the identity. -/
  map_id : ∀ {V : Opens X} {hV : V ≤ U}, map (hV := hV) le_rfl = 𝟙 (obj V hV)
  /-- Restriction is compatible with composition of inclusions. -/
  map_map : ∀ {V W Z : Opens X} {hV : V ≤ U} (hWV : W ≤ V) (hZW : Z ≤ W),
      map (hV := hV) hWV ≫ map hZW = map (hZW.trans hWV)

namespace ModuleLocalPresheaf

variable {R : Type u} [Ring R] {U : Opens X}

/-- The underlying presheaf of sets of a presheaf of `R`-modules. -/
def toLocalPresheaf (F : ModuleLocalPresheaf R X U) : LocalPresheaf X U where
  obj V hV := ToType (F.obj V hV)
  map hWV s := F.map hWV s
  map_id s := by rw [F.map_id]; simp
  map_map hWV hZW s := by rw [← ConcreteCategory.comp_apply, F.map_map]

/-- The sections of the underlying presheaf of sets over `V` are the elements of the `R`-module of
sections `F.obj V hV`. -/
@[simp] theorem toLocalPresheaf_obj (F : ModuleLocalPresheaf R X U) (V : Opens X) (hV : V ≤ U) :
    F.toLocalPresheaf.obj V hV = ToType (F.obj V hV) := rfl

/-- Restriction in the underlying presheaf of sets is the function underlying the `R`-linear
restriction map of `F`. -/
@[simp] theorem toLocalPresheaf_map (F : ModuleLocalPresheaf R X U) {V W : Opens X} {hV : V ≤ U}
    (hWV : W ≤ V) (s : ToType (F.obj V hV)) : F.toLocalPresheaf.map hWV s = F.map hWV s := rfl

end ModuleLocalPresheaf

/-! ### Glueing data of sheaves of modules -/

/-- Glueing data of sheaves of `R`-modules with respect to the covering `X = ⋃ i, U i`: a sheaf of
`R`-modules on each `U i` plus comparison isomorphisms of `R`-modules over the overlaps satisfying
the cocycle condition. This is `TopCat.Sheaf.GlueData` with values in `ModuleCat R`. -/
structure ModuleGlueData (R : Type u) [Ring R] (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X) where
  /-- The sheaf of `R`-modules on `U i`. -/
  sheaf : ∀ i, ModuleLocalPresheaf R X (U i)
  /-- Each `sheaf i` satisfies the sheaf condition. -/
  isSheaf : ∀ i, (sheaf i).toLocalPresheaf.IsSheaf
  /-- The comparison isomorphism `φ i j` on sections over an open contained in both `U i` and
  `U j`. -/
  trans : ∀ (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j),
      (sheaf i).obj V hi ≅ (sheaf j).obj V hj
  /-- The comparison isomorphisms commute with the restriction maps. -/
  trans_map : ∀ (i j : ι) {V W : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V),
      (sheaf i).map hWV ≫ (trans i j (hWV.trans hi) (hWV.trans hj)).hom
        = (trans i j hi hj).hom ≫ (sheaf j).map hWV
  /-- The cocycle condition `φ j k ∘ φ i j = φ i k`. -/
  trans_trans : ∀ (i j k : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k),
      (trans i j hi hj).hom ≫ (trans j k hj hk).hom = (trans i k hi hk).hom

namespace ModuleGlueData

variable {R : Type u} [Ring R] {ι : Type u} {U : ι → Opens X} (D : ModuleGlueData R X U)

/-- The underlying glueing data of sheaves of sets. -/
def toGlueData : GlueData X U where
  sheaf i := (D.sheaf i).toLocalPresheaf
  isSheaf := D.isSheaf
  trans := fun i j {_V} hi hj => (D.trans i j hi hj).toLinearEquiv.toEquiv
  trans_map := fun i j {_V _W} hi hj hWV s =>
    congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _))
      (D.trans_map i j hi hj hWV)) s
  trans_trans := fun i j k {_V} hi hj hk s =>
    congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _))
      (D.trans_trans i j k hi hj hk)) s

/-- The sheaf of sets on `U i` of the underlying glueing data is the presheaf of sets underlying
the sheaf of `R`-modules `D.sheaf i`. -/
@[simp] theorem toGlueData_sheaf (i : ι) : D.toGlueData.sheaf i = (D.sheaf i).toLocalPresheaf := rfl

/-- The comparison bijection of the underlying glueing data of sets is the function underlying the
comparison isomorphism of `R`-modules `φ i j`. -/
@[simp] theorem toGlueData_trans (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j)
    (s : ToType ((D.sheaf i).obj V hi)) :
    D.toGlueData.trans i j hi hj s = (D.trans i j hi hj).hom s := rfl

/-! ### The glued sheaf of modules -/

/-- The glued sections over an open `W`, as an `R`-submodule of `∏ i, F i (W ⊓ U i)`: this is the
equalizer of Stacks 00AM, whose defining equations are `R`-linear. Its carrier is by construction
the compatibility condition defining `GlueData.Sections`. -/
def sectionsSubmodule (W : Opens X) :
    Submodule R (∀ i, ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right)) where
  carrier := {s | ∀ i j : ι, (D.trans i j (V := W ⊓ U i ⊓ (W ⊓ U j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).hom
        ((D.sheaf i).map (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i) (s i))
      = (D.sheaf j).map (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j) (s j)}
  zero_mem' := fun i j => by simp
  add_mem' := fun hs ht i j => by simp [hs i j, ht i j]
  smul_mem' := fun r _ hs i j => by simp [hs i j]

/-- Componentwise restriction on the ambient product `∏ i, F i (W ⊓ U i)`. -/
def sectionsProdMap {W W' : Opens X} (h : W' ≤ W) :
    (∀ i, ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right)) →ₗ[R]
      ∀ i, ToType ((D.sheaf i).obj (W' ⊓ U i) inf_le_right) where
  toFun s i := (D.sheaf i).map (inf_le_inf_right (U i) h) (s i)
  map_add' _ _ := funext fun _ => by simp
  map_smul' _ _ := funext fun _ => by simp

/-- Restriction of the glued sections, as an `R`-linear map. Its underlying map is
`GlueData.sectionsMap`. -/
def sectionsMapHom {W W' : Opens X} (h : W' ≤ W) :
    ModuleCat.of R (D.sectionsSubmodule W) ⟶ ModuleCat.of R (D.sectionsSubmodule W') :=
  ModuleCat.ofHom
    { toFun := D.toGlueData.sectionsMap h
      map_add' := fun s t => Subtype.ext (map_add (D.sectionsProdMap h) s.1 t.1)
      map_smul' := fun r s => Subtype.ext (map_smul (D.sectionsProdMap h) r s.1) }

/-- The glued presheaf of `R`-modules. -/
def gluedModulePresheaf : X.Presheaf (ModuleCat.{u} R) where
  obj W := ModuleCat.of R (D.sectionsSubmodule W.unop)
  map h := D.sectionsMapHom h.unop.le
  map_id W := by
    refine ConcreteCategory.hom_ext _ _ fun s => Subtype.ext (funext fun i => ?_)
    exact (D.sheaf i).toLocalPresheaf.map_id _
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun s => Subtype.ext (funext fun i => ?_)
    exact ((D.sheaf i).toLocalPresheaf.map_map _ _ _).symm

/-- **Stacks 00AM.** The underlying presheaf of sets of the glued presheaf of `R`-modules is the
presheaf of sets glued in Stacks 00AL: the submodule cut out of `∏ i, F i (W ⊓ U i)` by the
equalizer equations has, as its underlying set, exactly the set of compatible families. -/
@[stacks 00AM]
theorem gluedModulePresheaf_forget :
    D.gluedModulePresheaf ⋙ CategoryTheory.forget (ModuleCat R) = D.toGlueData.gluedPresheaf := rfl

/-- **Stacks 00AM.** The presheaf of `R`-modules glued from a glueing data of sheaves of
`R`-modules is a sheaf of `R`-modules. Since its underlying presheaf of sets is the sheaf of Stacks
00AL, this is the sheaf condition of Stacks 00AL read through the forgetful functor. -/
@[stacks 00AM]
theorem gluedModulePresheaf_isSheaf : D.gluedModulePresheaf.IsSheaf :=
  (Presheaf.isSheaf_iff_isSheaf_comp (CategoryTheory.forget (ModuleCat R)) _).2
    (D.gluedModulePresheaf_forget ▸ D.toGlueData.gluedPresheaf_isSheaf)

/-- The sheaf of `R`-modules on `X` glued from a glueing data of sheaves of `R`-modules. -/
def gluedModuleSheaf : X.Sheaf (ModuleCat.{u} R) :=
  ⟨D.gluedModulePresheaf, D.gluedModulePresheaf_isSheaf⟩

/-- The comparison map `φ i : F|_{U i} ⟶ F i` of Stacks 00AL, on sections over an open `V ≤ U i`,
as an `R`-linear map. -/
def sectionsHom (i : ι) {V : Opens X} (hV : V ≤ U i) :
    ModuleCat.of R (D.sectionsSubmodule V) ⟶ (D.sheaf i).obj V hV :=
  ModuleCat.ofHom
    { toFun := fun s => (D.sheaf i).map (le_inf le_rfl hV) (s.1 i)
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }

end ModuleGlueData

end TopCat.Sheaf
