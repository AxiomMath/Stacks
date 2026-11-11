module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.Topology.Sheaves.Forget
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs
public import StacksFrontier.Topology.Sheaves.Glueing.Equivalence
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Sheaves of algebraic structures are the same thing as glueing data (Stacks 00AN)

Let `X` be a topological space and let `X = ⋃ i, U i` be an open covering. Stacks 00AN asserts
that restriction to the members of the covering is an equivalence between sheaves on `X` and
glueing data with respect to the covering, for sheaves of sets, for abelian sheaves, for sheaves
of algebraic structures and for sheaves of `𝒪`-modules. This file treats the abelian case and the
case of sheaves of algebraic structures, together, for sheaves with values in a category `C`
equipped with a functor `F : C ⥤ Type u` that is faithful, preserves limits and reflects
isomorphisms, and such that `C` has limits. A type of algebraic structure (Stacks 007M) is such a
pair, and so is the category of abelian groups with its forgetful functor.

## Main definitions

* `TopCat.Sheaf.ValuedLocalPresheaf`: a `C`-valued presheaf on an open `U` of `X`, presented as
  data indexed by the opens of `X` contained in `U`.
* `TopCat.Sheaf.ValuedGlueData`: glueing data of `C`-valued sheaves; a local presheaf is a sheaf
  when its underlying presheaf of sets (through `F`) is, as in Stacks 007M.
* `TopCat.Sheaf.ValuedGlueData.Hom`: morphisms of glueing data.
* `TopCat.Sheaf.valuedGlueDataFunctor`: the functor `Sh(X, C) ⥤ ValuedGlueData F U`.
* `TopCat.Sheaf.ValuedGlueData.glued`: the `C`-valued sheaf glued from a glueing datum, whose
  sections over `W` are the equalizer
  `∏ i, F i (W ⊓ U i) ⇉ ∏ i j, F j (W ⊓ U i ⊓ (W ⊓ U j))` of Stacks 00AM, computed in `C`.

## Main results

* `TopCat.Sheaf.valuedSheafEquivGlueData`: the equivalence for `C`-valued sheaves.
* `TopCat.Sheaf.addSheafEquivGlueData`: **Stacks 00AN** for abelian sheaves.
* `TopCat.Sheaf.algebraicStructureSheafEquivGlueData`: **Stacks 00AN** for sheaves of algebraic
  structures of a type `(C, F)` in the sense of Stacks 007M.

As in the proof of Stacks 00AN, the functor is fully faithful because morphisms of sheaves glue
(the `C`-valued analogue of Stacks 04TN, proved here through the sheaves of sets
`Hom(E, 𝒢(-))`), and essentially surjective by the glueing of Stacks 00AL and 00AM.

## Implementation notes

The sheaves of `C` on `X` are Mathlib's `X.Sheaf C`. Since `C` has limits and `F` preserves
limits and reflects isomorphisms, a `C`-valued presheaf is a sheaf exactly when its underlying
presheaf of sets is (`TopCat.Presheaf.isSheaf_iff_isSheaf_comp`), which is the definition of a
sheaf of algebraic structures in Stacks 007M.

The glued sections are a multiequalizer in `C`. Since `F` preserves it, its underlying set is in
bijection with the compatible families of Stacks 00AL (`ValuedGlueData.sectionsEquiv`); since `F`
is faithful, every equation between morphisms of `C` below is checked on underlying sets.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe w u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-! ### `C`-valued presheaves on an open subset -/

/-- A presheaf with values in `C` on an open `U` of `X`, presented as data indexed by the opens of
`X` contained in `U`. This is `TopCat.Sheaf.LocalPresheaf` with values in `C`. -/
structure ValuedLocalPresheaf (C : Type w) [Category.{u} C] (X : TopCat.{u}) (U : Opens X) where
  /-- The object of sections over an open `V` of `X` contained in `U`. -/
  obj : (V : Opens X) → V ≤ U → C
  /-- Restriction of sections along an inclusion `W ≤ V` of opens contained in `U`. -/
  map : ∀ {V W : Opens X} {hV : V ≤ U} (hWV : W ≤ V), obj V hV ⟶ obj W (hWV.trans hV)
  /-- Restricting along the identity is the identity. -/
  map_id : ∀ {V : Opens X} {hV : V ≤ U}, map (hV := hV) le_rfl = 𝟙 (obj V hV)
  /-- Restriction is compatible with composition of inclusions. -/
  map_map : ∀ {V W Z : Opens X} {hV : V ≤ U} (hWV : W ≤ V) (hZW : Z ≤ W),
      map (hV := hV) hWV ≫ map hZW = map (hZW.trans hWV)

namespace ValuedLocalPresheaf

variable {C : Type w} [Category.{u} C] (F : C ⥤ Type u) {U : Opens X}

/-- The underlying presheaf of sets of a `C`-valued presheaf on `U`, through `F`. -/
abbrev toLocalPresheaf (P : ValuedLocalPresheaf C X U) : LocalPresheaf X U where
  obj V hV := F.obj (P.obj V hV)
  map hWV s := F.map (P.map hWV) s
  map_id s := by rw [P.map_id, Functor.map_id_apply]
  map_map hWV hZW s := by rw [← Functor.map_comp_apply, P.map_map]

end ValuedLocalPresheaf

/-- The restriction of a `C`-valued presheaf on `X` to the opens contained in `U`. -/
abbrev _root_.TopCat.Presheaf.toValuedLocalPresheaf {C : Type w} [Category.{u} C]
    (P : X.Presheaf C) (U : Opens X) : ValuedLocalPresheaf C X U where
  obj V _ := P.obj (op V)
  map hWV := P.map (homOfLE hWV).op
  map_id := by
    intro V hV
    rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from Subsingleton.elim _ _, P.map_id]
  map_map := by
    intro V W Z hV hWV hZW
    rw [← P.map_comp]
    rfl

/-! ### Glueing data of `C`-valued sheaves -/

/-- Glueing data of `C`-valued sheaves with respect to a family of opens `U : ι → Opens X`: a
`C`-valued presheaf on each `U i` whose underlying presheaf of sets (through `F`) is a sheaf, plus
comparison isomorphisms in `C` over the overlaps, compatible with restriction and satisfying the
cocycle condition. -/
structure ValuedGlueData {C : Type w} [Category.{u} C] (F : C ⥤ Type u) {ι : Type u}
    (U : ι → Opens X) where
  /-- The `C`-valued sheaf on `U i`. -/
  sheaf : ∀ i, ValuedLocalPresheaf C X (U i)
  /-- The underlying presheaf of sets of each `sheaf i` is a sheaf. -/
  isSheaf : ∀ i, ((sheaf i).toLocalPresheaf F).IsSheaf
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

namespace ValuedGlueData

variable {C : Type w} [Category.{u} C] {F : C ⥤ Type u} {ι : Type u} {U : ι → Opens X}

/-! ### The category of glueing data -/

/-- A morphism of glueing data: a morphism of the local sheaves over each `U i`, commuting with
the comparison isomorphisms over the overlaps. -/
@[ext]
structure Hom (D E : ValuedGlueData F U) where
  /-- The morphism on sections over an open `V ≤ U i`. -/
  app : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i), (D.sheaf i).obj V hV ⟶ (E.sheaf i).obj V hV
  /-- Compatibility with the restriction maps. -/
  naturality : ∀ (i : ι) {V W : Opens X} (hV : V ≤ U i) (hWV : W ≤ V),
      (D.sheaf i).map hWV ≫ app i W (hWV.trans hV) = app i V hV ≫ (E.sheaf i).map hWV
  /-- Compatibility with the comparison isomorphisms. -/
  trans_app : ∀ (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j),
      (D.trans i j hi hj).hom ≫ app j V hj = app i V hi ≫ (E.trans i j hi hj).hom

/-- Glueing data of `C`-valued sheaves with respect to a fixed family of opens form a
category. -/
instance : Category.{u} (ValuedGlueData F U) where
  Hom D E := Hom D E
  id D := ⟨fun _ _ _ => 𝟙 _, by intros; simp, by intros; simp⟩
  comp f g := ⟨fun i V hV => f.app i V hV ≫ g.app i V hV, by
    intro i V W hV hWV
    rw [← Category.assoc, f.naturality, Category.assoc, g.naturality, Category.assoc], by
    intro i j V hi hj
    rw [← Category.assoc, f.trans_app, Category.assoc, g.trans_app, Category.assoc]⟩
  id_comp _ := Hom.ext (funext fun _ => funext fun _ => funext fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => funext fun _ => funext fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => funext fun _ => funext fun _ => Category.assoc _ _ _)

/-! ### The underlying glueing data of sets -/

variable (D : ValuedGlueData F U)

/-- The comparison isomorphisms commute with restriction, on underlying sets. -/
theorem trans_map_apply (i j : ι) {V W : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
    (s : F.obj ((D.sheaf i).obj V hi)) :
    F.map (D.trans i j (hWV.trans hi) (hWV.trans hj)).hom (F.map ((D.sheaf i).map hWV) s)
      = F.map ((D.sheaf j).map hWV) (F.map (D.trans i j hi hj).hom s) := by
  rw [← Functor.map_comp_apply, D.trans_map, Functor.map_comp_apply]

/-- The cocycle condition, on underlying sets. -/
theorem trans_trans_apply (i j k : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j)
    (hk : V ≤ U k) (s : F.obj ((D.sheaf i).obj V hi)) :
    F.map (D.trans j k hj hk).hom (F.map (D.trans i j hi hj).hom s)
      = F.map (D.trans i k hi hk).hom s := by
  rw [← Functor.map_comp_apply, D.trans_trans]

/-- The inverse of a comparison isomorphism undoes it, on underlying sets. -/
theorem inv_hom_apply' (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j)
    (s : F.obj ((D.sheaf i).obj V hi)) :
    F.map (D.trans i j hi hj).inv (F.map (D.trans i j hi hj).hom s) = s := by
  rw [← Functor.map_comp_apply, Iso.hom_inv_id, Functor.map_id_apply]

/-- A comparison isomorphism undoes its inverse, on underlying sets. -/
theorem hom_inv_apply' (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j)
    (s : F.obj ((D.sheaf j).obj V hj)) :
    F.map (D.trans i j hi hj).hom (F.map (D.trans i j hi hj).inv s) = s := by
  rw [← Functor.map_comp_apply, Iso.inv_hom_id, Functor.map_id_apply]

/-- The underlying glueing data of sheaves of sets, through `F`. -/
abbrev toGlueData : GlueData X U where
  sheaf i := (D.sheaf i).toLocalPresheaf F
  isSheaf := D.isSheaf
  trans i j _ hi hj :=
    { toFun := F.map (D.trans i j hi hj).hom
      invFun := F.map (D.trans i j hi hj).inv
      left_inv := fun s => D.inv_hom_apply' i j hi hj s
      right_inv := fun s => D.hom_inv_apply' i j hi hj s }
  trans_map := by
    intro i j V W hi hj hWV s
    exact D.trans_map_apply i j hi hj hWV s
  trans_trans := by
    intro i j k V hi hj hk s
    exact D.trans_trans_apply i j k hi hj hk s

/-- Restricting twice in the underlying presheaf of sets is restricting once. -/
theorem map_map_apply (i : ι) {V W Z : Opens X} {hV : V ≤ U i} (hWV : W ≤ V) (hZW : Z ≤ W)
    (s : F.obj ((D.sheaf i).obj V hV)) :
    F.map ((D.sheaf i).map hZW) (F.map ((D.sheaf i).map hWV) s)
      = F.map ((D.sheaf i).map (hZW.trans hWV)) s :=
  ((D.sheaf i).toLocalPresheaf F).map_map hWV hZW s

/-! ### The glued sections, as a multiequalizer in `C` -/

/-- The shape of the multiequalizer diagram of the glued sections: one object for each `i` and
one for each pair `(i, j)`. This is `MulticospanShape.prod ι`, as a reducible definition. -/
abbrev glueShape (ι : Type u) : MulticospanShape.{u, u} := ⟨ι, ι × ι, Prod.fst, Prod.snd⟩

/-- The multiequalizer diagram `∏ i, F i (W ⊓ U i) ⇉ ∏ i j, F j (W ⊓ U i ⊓ (W ⊓ U j))` whose
limit is the object of sections of the glued sheaf over `W`. -/
abbrev index (W : Opens X) : MulticospanIndex (glueShape ι) C where
  left i := (D.sheaf i).obj (W ⊓ U i) inf_le_right
  right p := (D.sheaf p.2).obj (W ⊓ U p.1 ⊓ (W ⊓ U p.2)) (inf_le_right.trans inf_le_right)
  fst p := (D.sheaf p.1).map (inf_le_left : W ⊓ U p.1 ⊓ (W ⊓ U p.2) ≤ W ⊓ U p.1) ≫
    (D.trans p.1 p.2 (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).hom
  snd p := (D.sheaf p.2).map (inf_le_right : W ⊓ U p.1 ⊓ (W ⊓ U p.2) ≤ W ⊓ U p.2)

variable [HasLimits C]

/-- The object of sections of the glued sheaf over an open `W`. -/
noncomputable abbrev gluedObj (W : Opens X) : C := multiequalizer (D.index W)

/-- The projection of the glued sections over `W` to the sections of `F i` over `W ⊓ U i`. -/
noncomputable abbrev proj (W : Opens X) (i : ι) :
    D.gluedObj W ⟶ (D.sheaf i).obj (W ⊓ U i) inf_le_right :=
  Multiequalizer.ι (D.index W) i

omit [HasLimits C] in
/-- A morphism of `C` is determined by the function it induces on underlying sets. -/
theorem hom_ext_of_map_apply (G : C ⥤ Type u) [G.Faithful] {A B : C} {f g : A ⟶ B}
    (h : ∀ x : G.obj A, G.map f x = G.map g x) : f = g :=
  G.map_injective (by ext x; exact h x)

/-- The underlying family of sets of an element of the glued sections is compatible. -/
theorem proj_trans_map_eq (W : Opens X) (x : F.obj (D.gluedObj W)) (i j : ι)
    {Z : Opens X} (hi : Z ≤ W ⊓ U i) (hj : Z ≤ W ⊓ U j) :
    F.map (D.trans i j (hi.trans inf_le_right) (hj.trans inf_le_right)).hom
        (F.map ((D.sheaf i).map hi) (F.map (D.proj W i) x))
      = F.map ((D.sheaf j).map hj) (F.map (D.proj W j) x) := by
  have h : F.map (D.proj W i ≫ (D.sheaf i).map (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i) ≫
        (D.trans i j (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).hom) x
      = F.map (D.proj W j ≫
        (D.sheaf j).map (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)) x :=
    congrArg (fun f => F.map f x) (Multiequalizer.condition (D.index W) (i, j))
  rw [Functor.map_comp_apply, Functor.map_comp_apply,
    Functor.map_comp_apply] at h
  have h' := congrArg (fun y => F.map ((D.sheaf j).map (le_inf hi hj)) y) h
  simp only at h'
  rwa [← D.trans_map_apply, D.map_map_apply, D.map_map_apply] at h'

/-- The underlying set of the glued sections over `W` maps to the compatible families of
Stacks 00AL. -/
noncomputable def toSections (W : Opens X) (x : F.obj (D.gluedObj W)) : D.toGlueData.Sections W :=
  ⟨fun i => F.map (D.proj W i) x, fun i j => D.proj_trans_map_eq W x i j _ _⟩

@[simp] theorem toSections_val (W : Opens X) (x : F.obj (D.gluedObj W)) (i : ι) :
    (D.toSections W x).1 i = F.map (D.proj W i) x := rfl

/-- The compatible families of Stacks 00AL are the sections of the multiequalizer diagram
underlying `D.index W`. -/
def indexSectionsEquiv (W : Opens X) :
    ((D.index W).map F).sections ≃ D.toGlueData.Sections W where
  toFun s := ⟨fun i => s.val i, fun i j =>
    (F.map_comp_apply _ _ _).symm.trans (s.property (i, j))⟩
  invFun t := ⟨fun i => t.1 i, fun p =>
    (F.map_comp_apply _ _ _).trans (t.2 p.1 p.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem toSections_eq_comp (W : Opens X) :
    D.toSections W = D.indexSectionsEquiv W ∘
      ((Multiequalizer.multifork (D.index W)).map F).toSections :=
  rfl

/-! ### The glued `C`-valued presheaf -/

variable [F.Faithful]

/-- The compatibility of the projections of the glued sections, in `C`. -/
theorem proj_map_trans (W : Opens X) (i j : ι) {Z : Opens X} (hi : Z ≤ W ⊓ U i)
    (hj : Z ≤ W ⊓ U j) :
    D.proj W i ≫ (D.sheaf i).map hi ≫
        (D.trans i j (hi.trans inf_le_right) (hj.trans inf_le_right)).hom
      = D.proj W j ≫ (D.sheaf j).map hj :=
  hom_ext_of_map_apply F fun x => by
    simp only [Functor.map_comp_apply]
    exact D.proj_trans_map_eq W x i j hi hj

/-- Restriction of the glued sections along an inclusion `W' ≤ W`. -/
noncomputable def gluedMap {W W' : Opens X} (h : W' ≤ W) : D.gluedObj W ⟶ D.gluedObj W' :=
  Multiequalizer.lift (D.index W') _
    (fun i => D.proj W i ≫ (D.sheaf i).map (inf_le_inf_right (U i) h)) fun p => by
      obtain ⟨i, j⟩ := p
      change (D.proj W i ≫ (D.sheaf i).map (inf_le_inf_right (U i) h)) ≫
          (D.sheaf i).map (inf_le_left : W' ⊓ U i ⊓ (W' ⊓ U j) ≤ W' ⊓ U i) ≫
          (D.trans i j (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).hom
        = (D.proj W j ≫ (D.sheaf j).map (inf_le_inf_right (U j) h)) ≫
          (D.sheaf j).map (inf_le_right : W' ⊓ U i ⊓ (W' ⊓ U j) ≤ W' ⊓ U j)
      rw [Category.assoc, ← Category.assoc ((D.sheaf i).map (inf_le_inf_right (U i) h)),
        (D.sheaf i).map_map, Category.assoc, (D.sheaf j).map_map]
      exact D.proj_map_trans W i j _ _

@[reassoc (attr := simp)]
theorem gluedMap_proj {W W' : Opens X} (h : W' ≤ W) (i : ι) :
    D.gluedMap h ≫ D.proj W' i = D.proj W i ≫ (D.sheaf i).map (inf_le_inf_right (U i) h) :=
  Multiequalizer.lift_ι _ _ _ _ _

theorem map_proj_gluedMap_apply {W W' : Opens X} (h : W' ≤ W) (i : ι)
    (x : F.obj (D.gluedObj W)) :
    F.map (D.proj W' i) (F.map (D.gluedMap h) x)
      = F.map ((D.sheaf i).map (inf_le_inf_right (U i) h)) (F.map (D.proj W i) x) := by
  rw [← Functor.map_comp_apply, gluedMap_proj, Functor.map_comp_apply]

/-- The glued `C`-valued presheaf. -/
noncomputable def gluedPresheaf : X.Presheaf C where
  obj W := D.gluedObj W.unop
  map h := D.gluedMap h.unop.le
  map_id W := Multiequalizer.hom_ext _ _ _ fun (i : ι) => by
    rw [gluedMap_proj, (D.sheaf i).map_id, Category.comp_id, Category.id_comp]
  map_comp f g := Multiequalizer.hom_ext _ _ _ fun (i : ι) => by
    rw [gluedMap_proj, Category.assoc, gluedMap_proj, gluedMap_proj_assoc, (D.sheaf i).map_map]

variable [PreservesLimits F]

/-- **The underlying set of the glued sections over `W` is the set of compatible families of
Stacks 00AL**, because `F` preserves the multiequalizer. -/
noncomputable def sectionsEquiv (W : Opens X) : F.obj (D.gluedObj W) ≃ D.toGlueData.Sections W :=
  Equiv.ofBijective (D.toSections W) <| by
    rw [toSections_eq_comp]
    exact (D.indexSectionsEquiv W).bijective.comp
      ((Multifork.isLimit_types_iff _).1 ⟨Multifork.isLimitMapOfPreserves _ F
        (limit.isLimit (D.index W).multicospan)⟩)

omit [F.Faithful] in
@[simp] theorem sectionsEquiv_apply_val (W : Opens X) (x : F.obj (D.gluedObj W)) (i : ι) :
    (D.sectionsEquiv W x).1 i = F.map (D.proj W i) x := rfl

/-- The underlying presheaf of sets of the glued `C`-valued presheaf is the presheaf of sets
glued in Stacks 00AL. -/
noncomputable def gluedPresheafCompIso : D.gluedPresheaf ⋙ F ≅ D.toGlueData.gluedPresheaf :=
  NatIso.ofComponents (fun W => (D.sectionsEquiv W.unop).toIso) fun {W W'} f => by
    ext x
    exact GlueData.Sections.ext fun i => D.map_proj_gluedMap_apply f.unop.le i x

variable [F.ReflectsIsomorphisms]

/-- **The glued `C`-valued presheaf is a sheaf**: its underlying presheaf of sets is the sheaf of
Stacks 00AL. -/
theorem gluedPresheaf_isSheaf : D.gluedPresheaf.IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp F _).2
    ((TopCat.Presheaf.isSheaf_iso_iff D.gluedPresheafCompIso).2
      D.toGlueData.gluedPresheaf_isSheaf)

/-- The `C`-valued sheaf on `X` glued from the glueing data `D` (Stacks 00AL and 00AM). -/
noncomputable def glued : CategoryTheory.Sheaf (Opens.grothendieckTopology X) C :=
  ⟨D.gluedPresheaf, D.gluedPresheaf_isSheaf⟩

/-- The comparison morphism `φ i : F|_{U i} ⟶ F i` on sections over an open `V ≤ U i`. -/
noncomputable def sectionsHom (i : ι) {V : Opens X} (hV : V ≤ U i) :
    D.gluedObj V ⟶ (D.sheaf i).obj V hV :=
  D.proj V i ≫ (D.sheaf i).map (le_inf le_rfl hV : V ≤ V ⊓ U i)

omit [F.Faithful] [F.ReflectsIsomorphisms] in
theorem map_sectionsHom_apply (i : ι) {V : Opens X} (hV : V ≤ U i) (x : F.obj (D.gluedObj V)) :
    F.map (D.sectionsHom i hV) x = D.toGlueData.sectionsEquiv i hV (D.sectionsEquiv V x) := by
  rw [sectionsHom, Functor.map_comp_apply]
  rfl

/-- The comparison morphisms `φ i` are isomorphisms: on underlying sets they are the bijections of
Stacks 00AL. -/
instance isIso_sectionsHom (i : ι) {V : Opens X} (hV : V ≤ U i) :
    IsIso (D.sectionsHom i hV) := by
  have : IsIso (F.map (D.sectionsHom i hV)) := by
    rw [isIso_iff_bijective]
    have : ⇑(F.map (D.sectionsHom i hV))
        = D.toGlueData.sectionsEquiv i hV ∘ D.sectionsEquiv V :=
      funext (D.map_sectionsHom_apply i hV)
    rw [this]
    exact (D.toGlueData.sectionsEquiv i hV).bijective.comp (D.sectionsEquiv V).bijective
  exact isIso_of_reflects_iso _ F

end ValuedGlueData

/-! ### The functor from sheaves to glueing data -/

section Functor

variable {C : Type w} [Category.{u} C] (F : C ⥤ Type u) [HasLimits C] [PreservesLimits F]
  [F.ReflectsIsomorphisms] {ι : Type u} (U : ι → Opens X)

/-- The functor sending a `C`-valued sheaf on `X` to its glueing data with respect to the family
`U`. The comparison isomorphisms of the resulting glueing datum are the identity. -/
noncomputable abbrev valuedGlueDataFunctor :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) C ⥤ ValuedGlueData F U where
  obj P :=
    { sheaf := fun i => TopCat.Presheaf.toValuedLocalPresheaf P.1 (U i)
      isSheaf := fun i => TopCat.Presheaf.isSheaf_toLocalPresheaf
        ((TopCat.Presheaf.isSheaf_iff_isSheaf_comp F P.1).1 P.2) (U i)
      trans := fun _ _ _ _ _ => Iso.refl _
      trans_map := by intros; simp
      trans_trans := by intros; simp }
  map ψ :=
    { app := fun _ V _ => ψ.hom.app (op V)
      naturality := by
        intro i V W hV hWV
        exact ψ.hom.naturality (homOfLE hWV).op
      trans_app := by intros; simp }
  map_id _ := ValuedGlueData.Hom.ext rfl
  map_comp _ _ := ValuedGlueData.Hom.ext rfl

variable {F U}

omit [HasLimits C] in
/-- For a `C`-valued sheaf `Q` and an object `E`, morphisms `E ⟶ Q(-)` glue uniquely along an
open covering: the presheaf of sets `Hom(E, Q(-))` is a sheaf. -/
theorem existsUnique_hom_gluing (Q : CategoryTheory.Sheaf (Opens.grothendieckTopology X) C) (E : C)
    {κ : Type u} {V : Opens X}
    (W : κ → Opens X) (hWV : ∀ k, W k ≤ V) (hcov : V ≤ ⨆ k, W k)
    (s : ∀ k, E ⟶ Q.1.obj (op (W k)))
    (hs : ∀ k l, s k ≫ Q.1.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op
      = s l ≫ Q.1.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op) :
    ∃! t : E ⟶ Q.1.obj (op V), ∀ k, t ≫ Q.1.map (homOfLE (hWV k)).op = s k :=
  TopCat.Presheaf.isSheaf_toLocalPresheaf
    ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).2 (Q.2 E)) ⊤ le_top W hWV hcov s hs

omit [HasLimits C] in
/-- Two morphisms into a `C`-valued sheaf agreeing on the members of an open covering are
equal. -/
theorem hom_ext_of_cover (Q : CategoryTheory.Sheaf (Opens.grothendieckTopology X) C) {E : C}
    {κ : Type u} {V : Opens X}
    (W : κ → Opens X) (hWV : ∀ k, W k ≤ V) (hcov : V ≤ ⨆ k, W k) {a b : E ⟶ Q.1.obj (op V)}
    (h : ∀ k, a ≫ Q.1.map (homOfLE (hWV k)).op = b ≫ Q.1.map (homOfLE (hWV k)).op) :
    a = b := by
  have hres : ∀ k l, (a ≫ Q.1.map (homOfLE (hWV k)).op) ≫
      Q.1.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op
        = (a ≫ Q.1.map (homOfLE (hWV l)).op) ≫
          Q.1.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op := by
    intro k l
    rw [Category.assoc, Category.assoc, ← Q.1.map_comp, ← Q.1.map_comp]
    rfl
  obtain ⟨_, -, huniq⟩ := existsUnique_hom_gluing Q E W hWV hcov _ hres
  exact (huniq a fun _ => rfl).trans (huniq b fun k => (h k).symm).symm

omit [HasLimits C] in
/-- Restricting twice along inclusions of opens is restricting once. -/
theorem map_homOfLE_comp (P : X.Presheaf C) {V W Z : Opens X} (hWV : W ≤ V) (hZW : Z ≤ W) :
    P.map (homOfLE hWV).op ≫ P.map (homOfLE hZW).op = P.map (homOfLE (hZW.trans hWV)).op := by
  rw [← P.map_comp]
  rfl

/-- The components of a morphism of the glueing data attached to two sheaves agree on the
overlaps, since the comparison isomorphisms are the identity. -/
theorem app_eq_app {P Q : CategoryTheory.Sheaf (Opens.grothendieckTopology X) C}
    (f : (valuedGlueDataFunctor F U).obj P ⟶ (valuedGlueDataFunctor F U).obj Q) (i j : ι)
    {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) : f.app i V hi = f.app j V hj := by
  have h := f.trans_app i j hi hj
  simp only [valuedGlueDataFunctor, Iso.refl_hom, Category.id_comp, Category.comp_id] at h
  exact h.symm

/-- The naturality of a morphism of the glueing data attached to two sheaves, in the form of the
restriction maps of the sheaves. -/
theorem app_naturality {P Q : CategoryTheory.Sheaf (Opens.grothendieckTopology X) C}
    (f : (valuedGlueDataFunctor F U).obj P ⟶ (valuedGlueDataFunctor F U).obj Q) (i : ι)
    {V W : Opens X} (hV : V ≤ U i) (hWV : W ≤ V) :
    P.1.map (homOfLE hWV).op ≫ f.app i W (hWV.trans hV)
      = f.app i V hV ≫ Q.1.map (homOfLE hWV).op :=
  f.naturality i hV hWV

/-- The glueing data functor is faithful: two morphisms of sheaves that agree on every open
contained in some `U i` are equal. -/
theorem valuedGlueDataFunctor_faithful (hU : ⨆ i, U i = ⊤) :
    (valuedGlueDataFunctor F U).Faithful where
  map_injective {P} {Q} {ψ} {ψ'} h := by
    refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
    refine hom_ext_of_cover Q (fun i => W.unop ⊓ U i) (fun _ => inf_le_left)
      (le_iSup_inf hU W.unop) fun i => ?_
    have hi := congrArg (fun m : ValuedGlueData.Hom _ _ => m.app i (W.unop ⊓ U i) inf_le_right) h
    change ψ.hom.app (op (W.unop ⊓ U i)) = ψ'.hom.app (op (W.unop ⊓ U i)) at hi
    rw [← ψ.hom.naturality, ← ψ'.hom.naturality]
    exact congrArg (P.1.map _ ≫ ·) hi

/-- The glueing data functor is full: a family of morphisms on the `U i` agreeing on the overlaps
glues to a morphism of sheaves, the `C`-valued analogue of Stacks 04TN. -/
theorem valuedGlueDataFunctor_full (hU : ⨆ i, U i = ⊤) : (valuedGlueDataFunctor F U).Full where
  map_surjective {P} {Q} f := by
    -- the morphism over `V`, glued from the `f i` over the cover `V ⊓ U i`
    have hex : ∀ V : Opens X, ∃! t : P.1.obj (op V) ⟶ Q.1.obj (op V), ∀ i,
        t ≫ Q.1.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op
          = P.1.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op ≫ f.app i (V ⊓ U i) inf_le_right :=
      fun V => existsUnique_hom_gluing Q _ (fun i => V ⊓ U i) (fun _ => inf_le_left)
        (le_iSup_inf hU V) _ fun k l => by
          rw [Category.assoc, Category.assoc,
            ← app_naturality f k inf_le_right (inf_le_left : V ⊓ U k ⊓ (V ⊓ U l) ≤ V ⊓ U k),
            ← app_naturality f l inf_le_right (inf_le_right : V ⊓ U k ⊓ (V ⊓ U l) ≤ V ⊓ U l),
            ← Category.assoc, ← Category.assoc, map_homOfLE_comp, map_homOfLE_comp,
            app_eq_app f k l]
    choose t ht _ using hex
    -- `t V` restricts to `f i` over every open `Z ≤ V` contained in `U i`
    have key : ∀ (V Z : Opens X) (hZV : Z ≤ V) (i : ι) (hZ : Z ≤ U i),
        t V ≫ Q.1.map (homOfLE hZV).op = P.1.map (homOfLE hZV).op ≫ f.app i Z hZ := by
      intro V Z hZV i hZ
      refine hom_ext_of_cover Q (fun k => Z ⊓ U k) (fun _ => inf_le_left)
        (le_iSup_inf hU Z) fun k => ?_
      have hk : Z ⊓ U k ≤ V ⊓ U k := inf_le_inf_right (U k) hZV
      rw [Category.assoc, map_homOfLE_comp,
        ← map_homOfLE_comp Q.1 (inf_le_left : V ⊓ U k ≤ V) hk, ← Category.assoc, ht V k,
        Category.assoc,
        ← app_naturality f k inf_le_right hk, ← Category.assoc, map_homOfLE_comp,
        Category.assoc, ← app_naturality f i hZ (inf_le_left : Z ⊓ U k ≤ Z), ← Category.assoc,
        map_homOfLE_comp, app_eq_app f k i]
    refine ⟨⟨{ app := fun V => t V.unop, naturality := fun {V W} g => ?_ }⟩, ?_⟩
    · rw [show g = (homOfLE g.unop.le).op from Subsingleton.elim _ _]
      refine hom_ext_of_cover Q (fun k => W.unop ⊓ U k) (fun _ => inf_le_left)
        (le_iSup_inf hU W.unop) fun k => ?_
      rw [Category.assoc, ht, ← Category.assoc, map_homOfLE_comp, Category.assoc,
        map_homOfLE_comp, key V.unop _ _ k inf_le_right]
    · refine ValuedGlueData.Hom.ext (funext fun i => funext fun V => funext fun hV => ?_)
      have h := key V V le_rfl i hV
      rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from Subsingleton.elim _ _, Q.1.map_id,
        P.1.map_id, Category.comp_id, Category.id_comp] at h
      exact h

omit [F.ReflectsIsomorphisms] in
/-- The naturality of the comparison morphisms `φ i`. -/
theorem _root_.TopCat.Sheaf.ValuedGlueData.gluedMap_sectionsHom [F.Faithful]
    (D : ValuedGlueData F U) (i : ι) {V W : Opens X}
    (hV : V ≤ U i) (hWV : W ≤ V) :
    D.gluedMap hWV ≫ D.sectionsHom i (hWV.trans hV) = D.sectionsHom i hV ≫ (D.sheaf i).map hWV :=
  ValuedGlueData.hom_ext_of_map_apply F fun x => by
    rw [Functor.map_comp_apply, D.map_sectionsHom_apply, Functor.map_comp_apply,
      D.map_sectionsHom_apply]
    refine Eq.trans ?_ (D.toGlueData.sectionsEquiv_map i hV hWV (D.sectionsEquiv V x))
    congr 1
    exact GlueData.Sections.ext fun k => D.map_proj_gluedMap_apply hWV k x

omit [F.ReflectsIsomorphisms] in
/-- The comparison morphisms `φ i` and `φ j` differ by `φ i j`. -/
theorem _root_.TopCat.Sheaf.ValuedGlueData.sectionsHom_trans [F.Faithful]
    (D : ValuedGlueData F U) (i j : ι) {V : Opens X}
    (hi : V ≤ U i) (hj : V ≤ U j) :
    D.sectionsHom j hj = D.sectionsHom i hi ≫ (D.trans i j hi hj).hom :=
  ValuedGlueData.hom_ext_of_map_apply F fun x => by
    rw [Functor.map_comp_apply, D.map_sectionsHom_apply, D.map_sectionsHom_apply]
    exact (D.toGlueData.trans_sectionsEquiv i j hi hj _).symm

theorem _root_.TopCat.Sheaf.ValuedGlueData.map_inv_sectionsHom [F.Faithful]
    (D : ValuedGlueData F U) (i : ι) {V W : Opens X} (hV : V ≤ U i) (hWV : W ≤ V) :
    (D.sheaf i).map hWV ≫ inv (D.sectionsHom i (hWV.trans hV))
      = inv (D.sectionsHom i hV) ≫ D.gluedMap hWV := by
  rw [IsIso.comp_inv_eq, Category.assoc, D.gluedMap_sectionsHom i hV hWV,
    IsIso.inv_hom_id_assoc]

theorem _root_.TopCat.Sheaf.ValuedGlueData.trans_inv_sectionsHom [F.Faithful]
    (D : ValuedGlueData F U) (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) :
    (D.trans i j hi hj).hom ≫ inv (D.sectionsHom j hj) = inv (D.sectionsHom i hi) := by
  rw [IsIso.comp_inv_eq, D.sectionsHom_trans i j hi hj, IsIso.inv_hom_id_assoc]

/-- The glueing data of the sheaf glued from `D` is isomorphic to `D`, via the comparison
isomorphisms of Stacks 00AL. -/
noncomputable def _root_.TopCat.Sheaf.ValuedGlueData.gluedIso [F.Faithful]
    (D : ValuedGlueData F U) : (valuedGlueDataFunctor F U).obj D.glued ≅ D where
  hom :=
    { app := fun i _ hV => D.sectionsHom i hV
      naturality := by
        intro i V W hV hWV
        exact D.gluedMap_sectionsHom i hV hWV
      trans_app := by
        intro i j V hi hj
        exact (Category.id_comp _).trans (D.sectionsHom_trans i j hi hj) }
  inv :=
    { app := fun i V hV => (inv (D.sectionsHom i hV) : (D.sheaf i).obj V hV ⟶ D.gluedObj V)
      naturality := by
        intro i V W hV hWV
        exact D.map_inv_sectionsHom i hV hWV
      trans_app := by
        intro i j V hi hj
        exact (D.trans_inv_sectionsHom i j hi hj).trans (Category.comp_id _).symm }
  hom_inv_id := ValuedGlueData.Hom.ext (funext fun i => funext fun _ => funext fun hV =>
    IsIso.hom_inv_id (D.sectionsHom i hV))
  inv_hom_id := ValuedGlueData.Hom.ext (funext fun i => funext fun _ => funext fun hV =>
    IsIso.inv_hom_id (D.sectionsHom i hV))

/-- The glueing data functor is essentially surjective: every glueing datum is the glueing data
of the sheaf glued from it (Stacks 00AL). -/
theorem valuedGlueDataFunctor_essSurj [F.Faithful] : (valuedGlueDataFunctor F U).EssSurj where
  mem_essImage D := ⟨D.glued, ⟨D.gluedIso⟩⟩

/-- For an open covering `X = ⋃ i, U i`, restriction to the members of the covering is an
equivalence between the category of `C`-valued sheaves on `X` and the category of glueing data of
`C`-valued sheaves with respect to the covering, whenever `C` has limits and `F : C ⥤ Type u` is
faithful, preserves limits and reflects isomorphisms. -/
noncomputable def valuedSheafEquivGlueData [F.Faithful] (hU : ⨆ i, U i = ⊤) :
    X.Sheaf C ≌ ValuedGlueData F U :=
  haveI := valuedGlueDataFunctor_faithful (F := F) hU
  haveI := valuedGlueDataFunctor_full (F := F) hU
  haveI := valuedGlueDataFunctor_essSurj (F := F) (U := U)
  haveI : (valuedGlueDataFunctor F U).IsEquivalence := {}
  (valuedGlueDataFunctor F U).asEquivalence

end Functor

/-! ### Abelian sheaves and sheaves of algebraic structures -/

variable {ι : Type u} {U : ι → Opens X}

/-- **Stacks 00AN, abelian sheaves.** For an open covering `X = ⋃ i, U i`, restriction to the
members of the covering is an equivalence between the category of abelian sheaves on `X` and the
category of glueing data of abelian sheaves with respect to the covering. -/
@[stacks 00AN "abelian sheaves"]
noncomputable def addSheafEquivGlueData (hU : ⨆ i, U i = ⊤) :
    X.Sheaf AddCommGrpCat.{u} ≌ ValuedGlueData (CategoryTheory.forget AddCommGrpCat.{u}) U :=
  valuedSheafEquivGlueData (F := CategoryTheory.forget AddCommGrpCat.{u}) hU

/-- **Stacks 00AN, sheaves of algebraic structures.** Let `(C, F)` be a type of algebraic
structure (Stacks 007M). For an open covering `X = ⋃ i, U i`, restriction to the members of the
covering is an equivalence between the category of sheaves of algebraic structures of type
`(C, F)` on `X` and the category of glueing data of such sheaves with respect to the covering. -/
@[stacks 00AN "sheaves of algebraic structures"]
noncomputable def algebraicStructureSheafEquivGlueData (S : AlgebraicStructureType.{u, w})
    (hU : ⨆ i, U i = ⊤) : X.Sheaf S.C ≌ ValuedGlueData S.F U :=
  valuedSheafEquivGlueData (F := S.F) hU

end TopCat.Sheaf
