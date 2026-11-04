module

public import StacksFrontier.Topology.Sheaves.Glueing.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.Pi
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Glueing sheaves of `O`-modules along an open covering (Stacks 00AM, third case)

Let `X` be a topological space, let `O` be a sheaf of rings on `X`, and let `U : ι → Opens X` be
a family of opens. A *glueing datum of sheaves of `O`-modules* consists of a sheaf of
`O|_{U i}`-modules `F i` on each `U i` together with `O`-linear comparison isomorphisms
`φ i j : (F i)|_{U i ⊓ U j} ≅ (F j)|_{U i ⊓ U j}` satisfying the cocycle condition
`φ j k ∘ φ i j = φ i k`. Stacks 00AM builds from such a datum a sheaf of `O`-modules `F` on `X`
together with isomorphisms `φ i : F|_{U i} ≅ F i` compatible with the `φ i j`.

`StacksFrontier/Topology/Sheaves/Glueing/AlgebraicStructure.lean` treats the first two cases of
Stacks 00AM — sheaves of abelian groups, and sheaves of `R`-modules for a *fixed* ring `R` — and
records that the third case, sheaves of `O`-modules for a sheaf of rings `O`, is a genuinely
different development, because there the restriction maps of the `F i` are only *semilinear*,
over restriction of functions in `O`. This file is that development.

The construction still needs nothing new beyond Stacks 00AL. The sections of the glued sheaf of
sets over an open `W` were built in Stacks 00AL as the equalizer
`F(W) = eq( ∏ i, F i (W ⊓ U i)  ⇉  ∏ i j, F i (W ⊓ U i ⊓ U j) )`,
and here the two parallel maps are `O(W)`-linear once `∏ i, F i (W ⊓ U i)` is given the
`O(W)`-action obtained by restricting functions from `W` to `W ⊓ U i`. So the equalizer is an
`O(W)`-submodule of that product — `OModuleGlueData.sectionsSubmodule` — and its underlying set is
*literally* (`OModuleGlueData.sections_eq`, which holds by `rfl`) the set of sections glued in
Stacks 00AL. The sheaf condition therefore transfers from Stacks 00AL along the forgetful functor
to abelian groups, by `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`.

## Main definitions

* `Stacks.SheafOfModules.OModuleLocalPresheaf`: a presheaf of `O|_U`-modules on an open `U` of
  `X`, presented as data indexed by the opens of `X` contained in `U`, exactly as
  `TopCat.Sheaf.LocalPresheaf` is for presheaves of sets. Its restriction maps are semilinear
  over restriction of functions.
* `Stacks.SheafOfModules.OModuleLocalPresheaf.ofSheafOfModules`: a sheaf of `O`-modules on `X`,
  read as a sheaf of `O|_U`-modules on `U`.
* `Stacks.SheafOfModules.OModuleGlueData`: a glueing datum of sheaves of `O`-modules.
* `Stacks.SheafOfModules.OModuleGlueData.ofModules`: a glueing datum assembled from a family of
  sheaves of `O`-modules on `X` together with comparison isomorphisms over the overlaps.
* `Stacks.SheafOfModules.OModuleGlueData.sectionsSubmodule`: the glued sections over an open `W`,
  as an `O(W)`-submodule of `∏ i, F i (W ⊓ U i)`.
* `Stacks.SheafOfModules.OModuleGlueData.glued`: the sheaf of `O`-modules glued from the datum.
* `Stacks.SheafOfModules.OModuleGlueData.gluedModules`: the same, read in the category `S.Modules`
  of sheaves of modules on a scheme `S`.
* `Stacks.SheafOfModules.ModulesGlueData`: the same glueing datum in the shape algebraic geometry
  uses it — a scheme `S`, a family of open immersions `f i : Y i ⟶ S`, and a sheaf of modules on
  each `Y i` rather than a semilinear local presheaf.
* `Stacks.SheafOfModules.ModulesGlueData.glued`: the glued sheaf of modules on the scheme `S`.

## Main results

* `Stacks.SheafOfModules.OModuleGlueData.gluedPresheafOfModules_forget`: the underlying presheaf
  of sets of the glued presheaf of `O`-modules is the presheaf glued in Stacks 00AL.
* `Stacks.SheafOfModules.OModuleGlueData.gluedPresheafOfModules_isSheaf`: the glued presheaf of
  `O`-modules is a sheaf.
* `Stacks.SheafOfModules.OModuleGlueData.chartIso`: the comparison isomorphism
  `φ i : F|_{U i} ≅ F i`, on sections over an open `V ≤ U i`.
* `Stacks.SheafOfModules.OModuleGlueData.chartLinearEquiv_restrict`: `φ i` commutes with the
  restriction maps, i.e. it is an isomorphism of sheaves of modules on `U i`.
* `Stacks.SheafOfModules.OModuleGlueData.trans_chartLinearEquiv`: the commuting triangle
  `φ i j ∘ φ i = φ j`.
* `Stacks.SheafOfModules.ModulesGlueData.chartIso`: on a scheme,
  `D.glued.restrict (f i) ≅ D.mod i` — the glued module restricts along each chart of the cover
  to the module it was glued from. This is the form in which 00AM is consumed.
* `Stacks.SheafOfModules.ModulesGlueData.trans_chartSectionsIso`: **those comparisons are
  related to one another by the transitions of the datum.** This is what a construction of a
  morphism *out of* the glued module needs: it turns a family of morphisms given on the chart
  modules and compatible with the transitions into a family of local morphisms on the glued
  module that agree over the overlaps.

## Implementation notes

Opens are indexed as in `StacksFrontier/Topology/Sheaves/Glueing/Sheaf.lean`: data on an open `U` of
`X` is a family indexed by an open `V` of `X` together with a proof `V ≤ U`. See the
implementation notes there. In particular every overlap is a single open of `X`, so no statement
below has to be transported across an identification of opens.

The `O(W)`-action on the ambient product `∏ i, F i (W ⊓ U i)` is supplied by
`OModuleGlueData.sectionsProductModule`, which is only a *local* instance: as an instance it would
compete with `Pi.module` on every product type. Consequently a statement whose type mentions
`sectionsSubmodule` does not elaborate outside this file. The comparison isomorphism is therefore
also provided as `OModuleGlueData.chartIso`, phrased with `D.glued.val.obj (op V)` in place of
`D.sectionsSubmodule V`; the two are equal by `rfl` and the former is a bundled `ModuleCat`, so it
carries its own module structure and needs no ambient instance.

Neither the sheaf property of the glued presheaf nor the comparison isomorphisms need the family
`U` to cover `X`, so the results below are stated without that hypothesis.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 00AL](https://stacks.math.columbia.edu/tag/00AL)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}}

/-! ### Presheaves of `O`-modules on an open subset -/

/-- A presheaf of `O|_U`-modules on an open `U` of `X`, presented as data indexed by the opens of
`X` contained in `U`. This is `TopCat.Sheaf.LocalPresheaf` with values in `ModuleCat (O V)`, the
ring varying with `V`, so that the restriction maps are semilinear over restriction of
functions. -/
structure OModuleLocalPresheaf (O : TopCat.Sheaf RingCat.{u} X) (U : Opens X) where
  /-- The module of sections over an open `V` of `X` contained in `U`. -/
  obj : (V : Opens X) → V ≤ U → ModuleCat.{u} (O.obj.obj (op V))
  /-- Restriction of sections along an inclusion `W ≤ V` of opens contained in `U`, semilinear
  over restriction of functions from `V` to `W`. -/
  map : ∀ {V W : Opens X} {hV : V ≤ U} (hWV : W ≤ V),
    obj V hV →ₛₗ[(O.obj.map (homOfLE hWV).op).hom] obj W (hWV.trans hV)
  /-- Restricting along the identity is the identity. -/
  map_id : ∀ {V : Opens X} {hV : V ≤ U} (s : obj V hV), map (hV := hV) le_rfl s = s
  /-- Restriction is compatible with composition of inclusions. -/
  map_map : ∀ {V W Z : Opens X} {hV : V ≤ U} (hWV : W ≤ V) (hZW : Z ≤ W) (s : obj V hV),
    map hZW (map hWV s) = map (hZW.trans hWV) s

namespace OModuleLocalPresheaf

variable {O : TopCat.Sheaf RingCat.{u} X} {U : Opens X}

/-- The underlying presheaf of sets of a presheaf of `O`-modules. -/
def toLocalPresheaf (F : OModuleLocalPresheaf O U) : TopCat.Sheaf.LocalPresheaf X U where
  obj V hV := ToType (F.obj V hV)
  map hWV s := F.map hWV s
  map_id := F.map_id
  map_map := F.map_map

/-- The sections of the underlying presheaf of sets over `V` are the elements of the module of
sections `F.obj V hV`. -/
@[simp] theorem toLocalPresheaf_obj (F : OModuleLocalPresheaf O U) (V : Opens X) (hV : V ≤ U) :
    F.toLocalPresheaf.obj V hV = ToType (F.obj V hV) := rfl

/-- Restriction in the underlying presheaf of sets is the function underlying the semilinear
restriction map of `F`. -/
@[simp] theorem toLocalPresheaf_map (F : OModuleLocalPresheaf O U) {V W : Opens X} {hV : V ≤ U}
    (hWV : W ≤ V) (s : ToType (F.obj V hV)) : F.toLocalPresheaf.map hWV s = F.map hWV s := rfl

/-- A sheaf of `O`-modules on `X`, read as a sheaf of `O|_U`-modules on `U`. -/
noncomputable def ofSheafOfModules (N : _root_.SheafOfModules.{u} O) (U : Opens X) :
    OModuleLocalPresheaf O U where
  obj V _ := N.val.obj (op V)
  map hWV := N.val.restrictₛₗ (homOfLE hWV).op
  map_id s := by
    rw [PresheafOfModules.restrictₛₗ_apply,
      show (homOfLE (le_refl _) : _ ⟶ _).op = 𝟙 _ from Subsingleton.elim _ _, N.val.map_id]
    rfl
  map_map hWV hZW s := by
    rw [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.restrictₛₗ_apply,
      PresheafOfModules.restrictₛₗ_apply, ← PresheafOfModules.map_comp_apply,
      show (homOfLE hWV).op ≫ (homOfLE hZW).op = (homOfLE (hZW.trans hWV)).op from
        Subsingleton.elim _ _]

/-- The sections of `ofSheafOfModules N U` over `V` are the sections of `N` over `V`. -/
@[simp] theorem ofSheafOfModules_obj (N : _root_.SheafOfModules.{u} O) (U : Opens X)
    (V : Opens X) (hV : V ≤ U) : (ofSheafOfModules N U).obj V hV = N.val.obj (op V) := rfl

/-- The restriction of a sheaf of `O`-modules to an open `U` satisfies the sheaf condition on
`U`. -/
theorem isSheaf_ofSheafOfModules (N : _root_.SheafOfModules.{u} O) (U : Opens X) :
    (ofSheafOfModules N U).toLocalPresheaf.IsSheaf :=
  TopCat.Presheaf.isSheaf_toLocalPresheaf
    ((TopCat.Presheaf.isSheaf_iff_isSheaf_comp (CategoryTheory.forget AddCommGrpCat)
      N.val.presheaf).mp N.isSheaf) U

end OModuleLocalPresheaf

/-! ### Glueing data of sheaves of `O`-modules -/

/-- Glueing data of sheaves of `O`-modules with respect to the family `U`: a sheaf of
`O|_{U i}`-modules on each `U i` plus `O`-linear comparison isomorphisms over the overlaps
satisfying the cocycle condition. This is `TopCat.Sheaf.GlueData` with `O`-module structures on
the local sections and `O`-linear comparisons. -/
structure OModuleGlueData (O : TopCat.Sheaf RingCat.{u} X) {ι : Type u} (U : ι → Opens X) where
  /-- The sheaf of `O|_{U i}`-modules on `U i`. -/
  sheaf : ∀ i, OModuleLocalPresheaf O (U i)
  /-- Each `sheaf i` satisfies the sheaf condition. -/
  isSheaf : ∀ i, (sheaf i).toLocalPresheaf.IsSheaf
  /-- The comparison isomorphism `φ i j` on sections over an open contained in both `U i` and
  `U j`, linear over the functions on that open. -/
  trans : ∀ (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j),
    (sheaf i).obj V hi ≃ₗ[O.obj.obj (op V)] (sheaf j).obj V hj
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

variable {O : TopCat.Sheaf RingCat.{u} X} {ι : Type u} {U : ι → Opens X}

/-- The underlying glueing data of sheaves of sets. -/
def toGlueData (D : OModuleGlueData O U) : TopCat.Sheaf.GlueData X U where
  sheaf i := (D.sheaf i).toLocalPresheaf
  isSheaf := D.isSheaf
  trans := fun i j {_V} hi hj => (D.trans i j hi hj).toEquiv
  trans_map := fun i j {_V _W} hi hj hWV s => D.trans_map i j hi hj hWV s
  trans_trans := fun i j k {_V} hi hj hk s => D.trans_trans i j k hi hj hk s

/-- The sheaf of sets on `U i` of the underlying glueing data is the presheaf of sets underlying
the sheaf of `O`-modules `D.sheaf i`. -/
@[simp] theorem toGlueData_sheaf (D : OModuleGlueData O U) (i : ι) :
    D.toGlueData.sheaf i = (D.sheaf i).toLocalPresheaf := rfl

/-- The comparison bijection of the underlying glueing data of sets is the function underlying
the `O`-linear comparison isomorphism `φ i j`. -/
theorem toGlueData_trans (D : OModuleGlueData O U) (i j : ι) {V : Opens X} (hi : V ≤ U i)
    (hj : V ≤ U j) (s : ToType ((D.sheaf i).obj V hi)) :
    D.toGlueData.trans i j hi hj s = D.trans i j hi hj s := rfl

/-- Glueing data assembled from a family of sheaves of `O`-modules on `X`, compared over the
overlaps. The `i`-th member of the datum is `N i` read on the opens contained in `U i`; in
particular only the behaviour of `N i` inside `U i` matters. -/
noncomputable def ofModules (N : ι → _root_.SheafOfModules.{u} O)
    (trans : ∀ (i j : ι) {V : Opens X} (_hi : V ≤ U i) (_hj : V ≤ U j),
      (N i).val.obj (op V) ≃ₗ[ToType (O.obj.obj (op V))] (N j).val.obj (op V))
    (trans_map : ∀ (i j : ι) {V W : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
      (s : ToType ((N i).val.obj (op V))),
      trans i j (hWV.trans hi) (hWV.trans hj) ((N i).val.map (homOfLE hWV).op s)
        = (N j).val.map (homOfLE hWV).op (trans i j hi hj s))
    (trans_trans : ∀ (i j k : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
      (s : ToType ((N i).val.obj (op V))),
      trans j k hj hk (trans i j hi hj s) = trans i k hi hk s) :
    OModuleGlueData O U where
  sheaf i := OModuleLocalPresheaf.ofSheafOfModules (N i) (U i)
  isSheaf i := OModuleLocalPresheaf.isSheaf_ofSheafOfModules (N i) (U i)
  trans := trans
  trans_map := trans_map
  trans_trans := trans_trans

/-- The members of `ofModules N _ _ _` are the `N i`, read on the opens contained in `U i`. -/
@[simp] theorem ofModules_sheaf (N : ι → _root_.SheafOfModules.{u} O) (t tm tt) (i : ι) :
    (ofModules (U := U) N t tm tt).sheaf i
      = OModuleLocalPresheaf.ofSheafOfModules (N i) (U i) := rfl

/-! ### The glued sheaf of `O`-modules -/

private theorem res_res (F : (Opens X)ᵒᵖ ⥤ RingCat.{u}) {V W Z : Opens X} (hWV : W ≤ V)
    (hZW : Z ≤ W) (r : ToType (F.obj (op V))) :
    F.map (homOfLE hZW).op (F.map (homOfLE hWV).op r)
      = F.map (homOfLE (hZW.trans hWV)).op r := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp,
    show (homOfLE hWV).op ≫ (homOfLE hZW).op = (homOfLE (hZW.trans hWV)).op from
      Subsingleton.elim _ _]

private theorem res_self (F : (Opens X)ᵒᵖ ⥤ RingCat.{u}) {V : Opens X} (h : V ≤ V)
    (r : ToType (F.obj (op V))) : F.map (homOfLE h).op r = r := by
  rw [show (homOfLE h).op = 𝟙 (op V) from Subsingleton.elim _ _, F.map_id]
  rfl

/-- The `O(W)`-module structure on the ambient product `∏ i, F i (W ⊓ U i)`: the action on the
`i`-th coordinate is restriction of the function from `W` to `W ⊓ U i`, followed by the action of
`F i` there. This is a `local` instance only; see the implementation notes. -/
@[instance_reducible]
noncomputable def sectionsProductModule (D : OModuleGlueData O U) (W : Opens X) :
    Module (ToType (O.obj.obj (op W)))
      (∀ i, ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right)) := by
  letI : ∀ i : ι, Module (ToType (O.obj.obj (op W)))
      (ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right)) := fun i =>
    Module.compHom _ (O.obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op).hom
  exact Pi.module ι (fun i => ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right))
    (ToType (O.obj.obj (op W)))

attribute [local instance] sectionsProductModule

/-- The `O(W)`-action on the ambient product is coordinatewise, by the restricted function. -/
theorem sectionsProduct_smul_apply (D : OModuleGlueData O U) {W : Opens X}
    (r : ToType (O.obj.obj (op W)))
    (s : ∀ i, ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right)) (i : ι) :
    (r • s) i = O.obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r • s i := rfl

/-- Restricting a local section scaled by a function restricted from a larger open: the scalar
may be restricted all the way down in one step. -/
theorem map_smul_res (D : OModuleGlueData O U) {W : Opens X} (r : ToType (O.obj.obj (op W)))
    (k : ι) {Z : Opens X} (hk : Z ≤ W ⊓ U k)
    (t : ToType ((D.sheaf k).obj (W ⊓ U k) inf_le_right)) :
    (D.sheaf k).map hk (O.obj.map (homOfLE (inf_le_left : W ⊓ U k ≤ W)).op r • t)
      = O.obj.map (homOfLE (hk.trans (inf_le_left : W ⊓ U k ≤ W))).op r •
        (D.sheaf k).map hk t := by
  rw [map_smulₛₗ, res_res]

/-- The glued sections over an open `W`, as an `O(W)`-submodule of `∏ i, F i (W ⊓ U i)`: this is
the equalizer of Stacks 00AM, whose defining equations are `O(W)`-linear. Its carrier is by
construction the compatibility condition defining `TopCat.Sheaf.GlueData.Sections`. -/
def sectionsSubmodule (D : OModuleGlueData O U) (W : Opens X) :
    Submodule (ToType (O.obj.obj (op W)))
      (∀ i, ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right)) where
  carrier := {s | ∀ i j : ι, D.trans i j (V := W ⊓ U i ⊓ (W ⊓ U j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        ((D.sheaf i).map (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i) (s i))
      = (D.sheaf j).map (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j) (s j)}
  zero_mem' := fun i j => by simp
  add_mem' := fun hs ht i j => by simp [map_add, hs i j, ht i j]
  smul_mem' := fun r s hs i j => by
    change D.trans i j (V := W ⊓ U i ⊓ (W ⊓ U j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        ((D.sheaf i).map (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)
          (O.obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r • s i))
      = (D.sheaf j).map (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)
          (O.obj.map (homOfLE (inf_le_left : W ⊓ U j ≤ W)).op r • s j)
    rw [D.map_smul_res r i inf_le_left (s i), D.map_smul_res r j inf_le_right (s j),
      map_smul, hs i j]

/-- The glued sections are *literally* the sections glued in Stacks 00AL: the submodule cut out of
`∏ i, F i (W ⊓ U i)` by the equalizer equations has, as its underlying type, exactly the type of
compatible families. -/
theorem sections_eq (D : OModuleGlueData O U) (W : Opens X) :
    D.toGlueData.Sections W = ToType (ModuleCat.of (ToType (O.obj.obj (op W)))
      (D.sectionsSubmodule W)) := rfl

/-- Componentwise restriction on the ambient product, as a semilinear map over restriction of
functions. -/
def sectionsProdMap (D : OModuleGlueData O U) {W W' : Opens X} (h : W' ≤ W) :
    (∀ i, ToType ((D.sheaf i).obj (W ⊓ U i) inf_le_right)) →ₛₗ[(O.obj.map (homOfLE h).op).hom]
      (∀ i, ToType ((D.sheaf i).obj (W' ⊓ U i) inf_le_right)) where
  toFun s i := (D.sheaf i).map (inf_le_inf_right (U i) h) (s i)
  map_add' _ _ := funext fun i => map_add ((D.sheaf i).map _) _ _
  map_smul' r s := funext fun i => by
    change (D.sheaf i).map (inf_le_inf_right (U i) h)
        (O.obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r • s i)
      = O.obj.map (homOfLE (inf_le_left : W' ⊓ U i ≤ W')).op
          (O.obj.map (homOfLE h).op r) • (D.sheaf i).map (inf_le_inf_right (U i) h) (s i)
    rw [D.map_smul_res r i (inf_le_inf_right (U i) h) (s i), res_res]

/-- Restriction of the glued sections. Its underlying map is
`TopCat.Sheaf.GlueData.sectionsMap`. -/
def sectionsMap (D : OModuleGlueData O U) {W W' : Opens X} (h : W' ≤ W)
    (s : D.sectionsSubmodule W) : D.sectionsSubmodule W' :=
  D.toGlueData.sectionsMap h s

/-- The components of a restricted compatible family are the restrictions of its components. -/
@[simp] theorem sectionsMap_val (D : OModuleGlueData O U) {W W' : Opens X} (h : W' ≤ W)
    (s : D.sectionsSubmodule W) (i : ι) :
    (D.sectionsMap h s).1 i = (D.sheaf i).map (inf_le_inf_right (U i) h) (s.1 i) := rfl

/-- Restriction of the glued sections, as a semilinear map over restriction of functions. -/
def sectionsSemilinearMap (D : OModuleGlueData O U) {W W' : Opens X} (h : W' ≤ W) :
    ModuleCat.of (ToType (O.obj.obj (op W))) (D.sectionsSubmodule W)
      →ₛₗ[(O.obj.map (homOfLE h).op).hom]
      ModuleCat.of (ToType (O.obj.obj (op W'))) (D.sectionsSubmodule W') where
  toFun := D.sectionsMap h
  map_add' s t := Subtype.ext (map_add (D.sectionsProdMap h) s.1 t.1)
  map_smul' r s := Subtype.ext ((D.sectionsProdMap h).map_smulₛₗ r s.1)

/-- The glued presheaf of `O`-modules. -/
noncomputable def gluedPresheafOfModules (D : OModuleGlueData O U) :
    PresheafOfModules.{u} O.obj where
  obj W := ModuleCat.of (ToType (O.obj.obj W)) (D.sectionsSubmodule W.unop)
  map f := ModuleCat.semilinearMapAddEquiv _ _ _ (D.sectionsSemilinearMap f.unop.le)
  map_id W := by
    refine ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext (funext fun i => ?_))
    exact (D.sheaf i).toLocalPresheaf.map_id _
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext (funext fun i => ?_))
    exact ((D.sheaf i).toLocalPresheaf.map_map _ _ _).symm

/-- The underlying presheaf of sets of the glued presheaf of `O`-modules is the presheaf of sets
glued in Stacks 00AL. -/
@[stacks 00AM "sheaves of O-modules, the underlying presheaf of sets"]
theorem gluedPresheafOfModules_forget (D : OModuleGlueData O U) :
    D.gluedPresheafOfModules.presheaf ⋙ CategoryTheory.forget AddCommGrpCat
      = D.toGlueData.gluedPresheaf := rfl

/-- The presheaf of `O`-modules glued from a glueing datum of sheaves of `O`-modules is a sheaf.
Since its underlying presheaf of sets is the sheaf of Stacks 00AL, this is the sheaf condition of
Stacks 00AL read through the forgetful functor. -/
@[stacks 00AM "sheaves of O-modules, the sheaf condition"]
theorem gluedPresheafOfModules_isSheaf (D : OModuleGlueData O U) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) D.gluedPresheafOfModules.presheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (CategoryTheory.forget AddCommGrpCat)
      D.gluedPresheafOfModules.presheaf).mpr
    (D.gluedPresheafOfModules_forget ▸ D.toGlueData.gluedPresheaf_isSheaf)

/-- The sheaf of `O`-modules on `X` glued from a glueing datum of sheaves of `O`-modules. -/
@[stacks 00AM "sheaves of O-modules, the glued sheaf"]
noncomputable def glued (D : OModuleGlueData O U) : _root_.SheafOfModules.{u} O :=
  ⟨D.gluedPresheafOfModules, D.gluedPresheafOfModules_isSheaf⟩

/-- The sections of the glued sheaf over `W` are the glued sections over `W`. -/
@[simp] theorem glued_obj (D : OModuleGlueData O U) (W : Opens X) :
    D.glued.val.obj (op W) = ModuleCat.of (ToType (O.obj.obj (op W)))
      (D.sectionsSubmodule W) := rfl

/-! ### The comparison isomorphisms -/

/-- The comparison isomorphism `φ i : F|_{U i} ≅ F i` on sections over an open `V ≤ U i`, as a
linear equivalence. Over such a `V` the compatibility condition forces every component `s j` to be
`φ i j (s i)`, so a section of the glued sheaf over `V` is the same thing as a section of
`D.sheaf i` over `V`. -/
noncomputable def chartLinearEquiv (D : OModuleGlueData O U) (i : ι) {V : Opens X}
    (hV : V ≤ U i) :
    D.sectionsSubmodule V ≃ₗ[ToType (O.obj.obj (op V))] (D.sheaf i).obj V hV where
  __ := D.toGlueData.sectionsEquiv i hV
  map_add' s t := map_add ((D.sheaf i).map (le_inf le_rfl hV)) _ _
  map_smul' r s :=
    (D.map_smul_res r i (le_inf le_rfl hV) (s.1 i)).trans (by rw [res_self]; rfl)

/-- The comparison map `φ i` restricts the `i`-th component of a compatible family to `V`. -/
@[simp] theorem chartLinearEquiv_apply (D : OModuleGlueData O U) (i : ι) {V : Opens X}
    (hV : V ≤ U i) (s : D.sectionsSubmodule V) :
    D.chartLinearEquiv i hV s = (D.sheaf i).map (le_inf le_rfl hV) (s.1 i) := rfl

/-- The comparison isomorphism `φ i` commutes with the restriction maps, i.e. it is an isomorphism
of sheaves of modules on `U i`. -/
@[stacks 00AM "sheaves of O-modules, the comparison isomorphisms"]
theorem chartLinearEquiv_restrict (D : OModuleGlueData O U) (i : ι) {V W : Opens X}
    (hV : V ≤ U i) (h : W ≤ V) (s : D.sectionsSubmodule V) :
    D.chartLinearEquiv i (h.trans hV) (D.sectionsMap h s)
      = (D.sheaf i).map h (D.chartLinearEquiv i hV s) :=
  D.toGlueData.sectionsEquiv_map i hV h s

/-- The commuting triangle `φ i j ∘ φ i = φ j` over the overlaps. -/
@[stacks 00AM "sheaves of O-modules, compatibility of the comparisons"]
theorem trans_chartLinearEquiv (D : OModuleGlueData O U) (i j : ι) {V : Opens X} (hi : V ≤ U i)
    (hj : V ≤ U j) (s : D.sectionsSubmodule V) :
    D.trans i j hi hj (D.chartLinearEquiv i hi s) = D.chartLinearEquiv j hj s :=
  D.toGlueData.trans_sectionsEquiv i j hi hj s

/-- The comparison isomorphism `φ i : F|_{U i} ≅ F i` on sections over an open `V ≤ U i`, as an
isomorphism of bundled modules. This is `chartLinearEquiv` phrased so that the statement does not
mention `sectionsSubmodule`, hence elaborates without the local instance
`sectionsProductModule`. -/
noncomputable def chartIso (D : OModuleGlueData O U) (i : ι) {V : Opens X} (hV : V ≤ U i) :
    D.glued.val.obj (op V) ≅ (D.sheaf i).obj V hV :=
  (D.chartLinearEquiv i hV).toModuleIso

/-- `chartIso` reads off the `i`-th component of a compatible family, restricted to `V`. -/
theorem chartIso_hom_apply (D : OModuleGlueData O U) (i : ι) {V : Opens X} (hV : V ≤ U i)
    (s : D.sectionsSubmodule V) :
    (D.chartIso i hV).hom s = (D.sheaf i).map (le_inf le_rfl hV) (s.1 i) := rfl

/-- **Reading a section of the glued sheaf on the `i`-th chart commutes with restriction.** This
is `Stacks.SheafOfModules.OModuleGlueData.chartLinearEquiv_restrict` phrased with `chartIso`, so
that it elaborates outside this file, where the local instance
`Stacks.SheafOfModules.OModuleGlueData.sectionsProductModule` is unavailable. -/
theorem chartIso_hom_restrictₛₗ (D : OModuleGlueData O U) (i : ι) {V W : Opens X} (hV : V ≤ U i)
    (h : W ≤ V) (s : ToType (D.glued.val.obj (op V))) :
    (D.chartIso i (h.trans hV)).hom (D.glued.val.restrictₛₗ (homOfLE h).op s)
      = (D.sheaf i).map h ((D.chartIso i hV).hom s) :=
  D.chartLinearEquiv_restrict i hV h s

/-- **The commuting triangle `φ i j ∘ φ i = φ j` over the overlaps**, phrased with `chartIso` so
that it elaborates outside this file. -/
theorem trans_chartIso_hom (D : OModuleGlueData O U) (i j : ι) {V : Opens X} (hi : V ≤ U i)
    (hj : V ≤ U j) (s : ToType (D.glued.val.obj (op V))) :
    D.trans i j hi hj ((D.chartIso i hi).hom s) = (D.chartIso j hj).hom s :=
  D.trans_chartLinearEquiv i j hi hj s

end OModuleGlueData

/-! ### Glueing sheaves of modules on a scheme -/

section Scheme

open AlgebraicGeometry

variable {S : Scheme.{u}} {ι : Type u} {U : ι → S.Opens}

namespace OModuleGlueData

/-- The glued sheaf of modules, read in the category `S.Modules` of sheaves of `O_S`-modules on a
scheme `S`. The comparison isomorphisms with the members of the glueing datum are
`OModuleGlueData.chartIso`. -/
noncomputable abbrev gluedModules (D : OModuleGlueData S.ringCatSheaf U) : S.Modules := D.glued

/-- The sections of the glued module over an open `W` of the scheme are the glued sections. -/
theorem gluedModules_obj (D : OModuleGlueData S.ringCatSheaf U) (W : S.Opens) :
    Γ(D.gluedModules, W) = ToType (ModuleCat.of (ToType (S.ringCatSheaf.obj.obj (op W)))
      (D.sectionsSubmodule W)) := rfl

/-- The sections of the glued module restricted along the inclusion of a member of the cover are
the glued sections over the image open. -/
theorem restrict_gluedModules_obj (D : OModuleGlueData S.ringCatSheaf U) (i : ι)
    (V : (U i).toScheme.Opens) :
    (D.gluedModules.restrict (U i).ι).val.obj (op V)
      = (ModuleCat.restrictScalars (((U i).ι.appIso V).inv).hom).obj
          (D.glued.val.obj (op ((U i).ι ''ᵁ V))) := rfl

end OModuleGlueData

/-- The sections over an open `V` of `S` of a sheaf of modules on a scheme `Y` over `S`, as a
module over the functions on `V`. By `rfl` the underlying type is `Γ(M, f ⁻¹ᵁ V)`; passing
through the pushforward is what makes the ring of scalars `O_S(V)` rather than `O_Y(f ⁻¹ᵁ V)`,
and so makes every open of `S` carry its sections over one ring, with no transport. -/
noncomputable abbrev openSections {Y : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) (V : S.Opens) :
    ModuleCat.{u} (ToType (S.ringCatSheaf.obj.obj (op V))) :=
  ((Scheme.Modules.pushforward f).obj M).val.obj (op V)

/-- Glueing data of sheaves of modules on a scheme `S` along a family of open immersions
`f i : Y i ⟶ S`: a sheaf of modules on each `Y i`, plus comparison isomorphisms over the
overlaps satisfying the cocycle condition. This is the shape in which Stacks 00AM is used in
algebraic geometry.

The charts are open immersions from arbitrary schemes rather than the inclusions of open
subschemes of `S`, because that is the form in which charts arise: the charts of a relative
`Proj` are the projective spectra of the graded section rings, and the charts of a scheme glued
from a gluing datum are the pieces it was glued from. Taking `f i = (U i).ι` for a family of
opens `U : ι → S.Opens` recovers the open-subscheme case, since `(U i).ι.opensRange = U i`. -/
@[ega "0 3.3.1" "special case"]
structure ModulesGlueData (S : Scheme.{u}) {ι : Type u} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ S) [∀ i, IsOpenImmersion (f i)] where
  /-- The sheaf of modules on the `i`-th chart. -/
  mod : ∀ i, (Y i).Modules
  /-- The comparison isomorphism `φ i j` on sections over an open contained in the images of
  both the `i`-th and the `j`-th chart, linear over the functions on that open. -/
  trans : ∀ (i j : ι) {V : S.Opens} (_hi : V ≤ (f i).opensRange) (_hj : V ≤ (f j).opensRange),
    openSections (f i) (mod i) V ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))]
      openSections (f j) (mod j) V
  /-- The comparison isomorphisms commute with the restriction maps. -/
  trans_map : ∀ (i j : ι) {V W : S.Opens} (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (hWV : W ≤ V)
      (s : ToType (openSections (f i) (mod i) V)),
    trans i j (hWV.trans hi) (hWV.trans hj)
        (((Scheme.Modules.pushforward (f i)).obj (mod i)).val.map (homOfLE hWV).op s)
      = ((Scheme.Modules.pushforward (f j)).obj (mod j)).val.map (homOfLE hWV).op
          (trans i j hi hj s)
  /-- The cocycle condition `φ j k ∘ φ i j = φ i k`. -/
  trans_trans : ∀ (i j k : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange)
      (s : ToType (openSections (f i) (mod i) V)),
    trans j k hj hk (trans i j hi hj s) = trans i k hi hk s

namespace ModulesGlueData

variable {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ S} [∀ i, IsOpenImmersion (f i)]

/-- The underlying glueing datum of sheaves of `O_S`-modules for the family of opens
`(f i).opensRange`: the `i`-th member is the pushforward of `mod i` along `f i`, whose sections
over an open `V ≤ (f i).opensRange` are the sections of `mod i` over the preimage of `V`. -/
noncomputable def toOModuleGlueData (D : ModulesGlueData S f) :
    OModuleGlueData S.ringCatSheaf (fun i => (f i).opensRange) :=
  OModuleGlueData.ofModules (fun i => (Scheme.Modules.pushforward (f i)).obj (D.mod i))
    D.trans D.trans_map D.trans_trans

/-- The sheaf of modules on `S` glued from `D`. -/
@[stacks 00AM "sheaves of O-modules on a scheme, the glued module"]
noncomputable abbrev glued (D : ModulesGlueData S f) : S.Modules :=
  D.toOModuleGlueData.gluedModules

/-- The glued module restricts along each chart to the sheaf of modules it was glued from. -/
@[stacks 00AM "sheaves of O-modules on a scheme, the comparison isomorphisms"]
noncomputable def chartIso (D : ModulesGlueData S f) (i : ι) :
    D.glued.restrict (f i) ≅ D.mod i := by
  refine Iso.trans ?_ ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).app (D.mod i))
  refine Scheme.Modules.fullyFaithfulToPresheafOfModules.preimageIso
    (PresheafOfModules.isoMk (fun V => ?_) ?_)
  · exact (ModuleCat.restrictScalars (((f i).appIso V.unop).inv).hom).mapIso
      (D.toOModuleGlueData.chartIso i ((f i).image_le_opensRange V.unop))
  · intro V W g
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    exact D.toOModuleGlueData.chartLinearEquiv_restrict i
      ((f i).image_le_opensRange V.unop) (Scheme.Hom.image_mono _ (leOfHom g.unop)) s

/-- The sections of the glued module over an open `V ≤ (f i).opensRange` are, `O_S(V)`-linearly,
the sections of `mod i` over the preimage of `V` in the `i`-th chart. This is `chartIso` read on
sections, in the form that needs no identification of opens. -/
noncomputable def chartSectionsIso (D : ModulesGlueData S f) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) : D.glued.val.obj (op V) ≅ openSections (f i) (D.mod i) V :=
  D.toOModuleGlueData.chartIso i hV

/-- **Reading a section of the glued module on the `i`-th chart commutes with restriction.** This
is `Stacks.SheafOfModules.OModuleGlueData.chartLinearEquiv_restrict` phrased with
`chartSectionsIso`, so that it elaborates outside this file. -/
theorem chartSectionsIso_restrict (D : ModulesGlueData S f) (i : ι) {V W : S.Opens}
    (hV : V ≤ (f i).opensRange) (hWV : W ≤ V) (x : ToType (D.glued.val.obj (op V))) :
    (D.chartSectionsIso i (hWV.trans hV)).hom (D.glued.val.restrictₛₗ (homOfLE hWV).op x)
      = ((Scheme.Modules.pushforward (f i)).obj (D.mod i)).val.restrictₛₗ (homOfLE hWV).op
          ((D.chartSectionsIso i hV).hom x) :=
  D.toOModuleGlueData.chartLinearEquiv_restrict i hV hWV x

/-- **The commuting triangle `φ i j ∘ φ i = φ j` on sections over an open contained in two
charts.** Reading a section of the glued module on the `i`-th chart and comparing it with the
`j`-th chart gives the same thing as reading it on the `j`-th chart directly. This is
`Stacks.SheafOfModules.OModuleGlueData.trans_chartLinearEquiv` phrased with `chartSectionsIso`,
so that it elaborates outside this file. -/
@[stacks 00AM "sheaves of O-modules on a scheme, the comparisons related by the transitions"]
theorem trans_chartSectionsIso (D : ModulesGlueData S f) (i j : ι) {V : S.Opens}
    (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange)
    (x : ToType (D.glued.val.obj (op V))) :
    D.trans i j hi hj ((D.chartSectionsIso i hi).hom x) = (D.chartSectionsIso j hj).hom x :=
  D.toOModuleGlueData.trans_chartLinearEquiv i j hi hj x

end ModulesGlueData

end Scheme

end Stacks.SheafOfModules
