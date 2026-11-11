module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Topology.Sheaves.Forget
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs
public import StacksFrontier.Topology.Sheaves.Glueing.Sheaf

/-!
# Glueing sheaves of algebraic structures along an open covering (Stacks 00AM)

Let `S = (C, F)` be a type of algebraic structure (Stacks 007L, formalized as
`AlgebraicStructureType`). Stacks 00AM says that the glueing of sheaves of sets of Stacks 00AL
(`TopCat.Sheaf.GlueData`) works verbatim for sheaves with values in `C`: if each `F i` is a sheaf
with values in `C` on `U i` and each `φ i j` is an isomorphism in `C`, the glued object is a sheaf
with values in `C` whose underlying sheaf of sets is the sheaf glued in Stacks 00AL.

As in the proof of Stacks 00AM, the sections over an open `W` are the equalizer of the two maps
`∏ i, F i (W ⊓ U i) ⇉ ∏ i j, F j (W ⊓ U i ⊓ (W ⊓ U j))`, taken in `C`; we take it in the form of
the multiequalizer `multiequalizer (D.multicospanIndex W)`, which is the same limit. Since the
forgetful functor `S.F` preserves limits, the underlying set of this object is the set of
compatible families of Stacks 00AL (`AlgGlueData.forgetIso`), and the sheaf condition transfers
along `S.F` by `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`.

The two other cases of Stacks 00AM, sheaves of abelian groups and sheaves of `𝒪`-modules, are
`TopCat.Sheaf.AddGlueData.gluedAddPresheaf_isSheaf` and
`TopCat.Sheaf.OModuleGlueData.isSheaf_gluedPresheafOfModules`.

## Main definitions

* `TopCat.Sheaf.AlgLocalPresheaf`: a presheaf with values in `S.C` on an open `U` of `X`,
  presented as data indexed by the opens of `X` contained in `U`.
* `TopCat.Sheaf.AlgGlueData`: glueing data of sheaves with values in `S.C`.
* `TopCat.Sheaf.AlgGlueData.gluedPresheaf`, `TopCat.Sheaf.AlgGlueData.glued`: the glued presheaf
  and sheaf with values in `S.C`.
* `TopCat.Sheaf.AlgGlueData.sectionsIso`: the comparison isomorphism `φ i` in `S.C`.

## Main results

* `TopCat.Sheaf.AlgGlueData.forgetIso`: the underlying presheaf of sets of the glued presheaf is
  the presheaf of sets glued in Stacks 00AL.
* `TopCat.Sheaf.AlgGlueData.gluedPresheaf_isSheaf`: the glued presheaf is a sheaf with values
  in `S.C`.
* `TopCat.Sheaf.AlgGlueData.sectionsIso_hom_trans`: the comparison isomorphisms are compatible with
  the `φ i j`.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe w u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (S : AlgebraicStructureType.{u, w})

/-- A presheaf with values in the category `S.C` of a type of algebraic structure on an open `U`
of `X`, presented as data indexed by the opens of `X` contained in `U`. This is
`TopCat.Sheaf.LocalPresheaf` with values in `S.C`. -/
structure AlgLocalPresheaf (X : TopCat.{u}) (U : Opens X) where
  /-- The object of sections over an open `V` of `X` contained in `U`. -/
  obj : (V : Opens X) → V ≤ U → S.C
  /-- Restriction of sections along an inclusion `W ≤ V` of opens contained in `U`. -/
  map : ∀ {V W : Opens X} {hV : V ≤ U} (hWV : W ≤ V), obj V hV ⟶ obj W (hWV.trans hV)
  /-- Restricting along the identity is the identity. -/
  map_id : ∀ {V : Opens X} {hV : V ≤ U}, map (hV := hV) le_rfl = 𝟙 (obj V hV)
  /-- Restriction is compatible with composition of inclusions. -/
  map_map : ∀ {V W Z : Opens X} {hV : V ≤ U} (hWV : W ≤ V) (hZW : Z ≤ W),
      map (hV := hV) hWV ≫ map hZW = map (hZW.trans hWV)

namespace AlgLocalPresheaf

variable {S} {U : Opens X}

attribute [reassoc] map_map

/-- The underlying presheaf of sets, obtained by applying the forgetful functor `S.F`. -/
def toLocalPresheaf (F : AlgLocalPresheaf S X U) : LocalPresheaf X U where
  obj V hV := S.F.obj (F.obj V hV)
  map hWV s := S.F.map (F.map hWV) s
  map_id s := by rw [F.map_id, Functor.map_id_apply]
  map_map hWV hZW s := by rw [← Functor.map_comp_apply, F.map_map]

end AlgLocalPresheaf

/-- Glueing data of sheaves with values in the category `S.C` of a type of algebraic structure,
with respect to the covering `X = ⋃ i, U i`: a sheaf with values in `S.C` on each `U i` plus
comparison isomorphisms in `S.C` over the overlaps satisfying the cocycle condition. A presheaf
with values in `S.C` is a sheaf iff its underlying presheaf of sets is one, and the
sheaf condition is stated on the underlying presheaf of sets. -/
structure AlgGlueData (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X) where
  /-- The sheaf with values in `S.C` on `U i`. -/
  sheaf : ∀ i, AlgLocalPresheaf S X (U i)
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

namespace AlgGlueData

variable {S} {ι : Type u} {U : ι → Opens X} (D : AlgGlueData S X U)

/-- The underlying glueing data of sheaves of sets, obtained by applying `S.F`. -/
def toGlueData : GlueData X U where
  sheaf i := (D.sheaf i).toLocalPresheaf
  isSheaf := D.isSheaf
  trans := fun i j {_V} hi hj => (S.F.mapIso (D.trans i j hi hj)).toEquiv
  trans_map := fun i j {_V _W} hi hj hWV s =>
    ((Functor.map_comp_apply S.F _ _ s).symm.trans
      (congrArg (fun f => S.F.map f s) (D.trans_map i j hi hj hWV))).trans
      (Functor.map_comp_apply S.F _ _ s)
  trans_trans := fun i j k {_V} hi hj hk s =>
    (Functor.map_comp_apply S.F _ _ s).symm.trans
      (congrArg (fun f => S.F.map f s) (D.trans_trans i j k hi hj hk))

/-! ### The glued presheaf -/

/-- The diagram whose limit is the object of glued sections over `W`: the two families of maps
`F i (W ⊓ U i) ⟶ F j (W ⊓ U i ⊓ (W ⊓ U j))`, namely restriction followed by `φ i j`, and
restriction. Its multiequalizer is the equalizer of
`∏ i, F i (W ⊓ U i) ⇉ ∏ i j, F j (W ⊓ U i ⊓ (W ⊓ U j))` of Stacks 00AM. -/
def multicospanIndex (W : Opens X) : MulticospanIndex (MulticospanShape.prod ι) S.C where
  left i := (D.sheaf i).obj (W ⊓ U i) inf_le_right
  right r := (D.sheaf r.2).obj (W ⊓ U r.1 ⊓ (W ⊓ U r.2)) (inf_le_right.trans inf_le_right)
  fst r := (D.sheaf r.1).map (inf_le_left : W ⊓ U r.1 ⊓ (W ⊓ U r.2) ≤ W ⊓ U r.1) ≫
    (D.trans r.1 r.2 (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).hom
  snd r := (D.sheaf r.2).map (inf_le_right : W ⊓ U r.1 ⊓ (W ⊓ U r.2) ≤ W ⊓ U r.2)

/-- The object of glued sections over an open `W`: the equalizer of Stacks 00AM, taken in `S.C`. -/
noncomputable def sections (W : Opens X) : S.C := multiequalizer (D.multicospanIndex W)

/-- The projection of the glued sections over `W` to `F i (W ⊓ U i)`. -/
noncomputable def sectionsι (W : Opens X) (i : ι) :
    D.sections W ⟶ (D.sheaf i).obj (W ⊓ U i) inf_le_right :=
  Multiequalizer.ι (D.multicospanIndex W) i

/-- The defining equations of the glued sections. -/
theorem sectionsι_condition (W : Opens X) (i j : ι) :
    D.sectionsι W i ≫ (D.sheaf i).map (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i) ≫
      (D.trans i j (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).hom
      = D.sectionsι W j ≫ (D.sheaf j).map (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j) :=
  Multiequalizer.condition (D.multicospanIndex W) (i, j)

/-- The defining equations of the glued sections, over an arbitrary open contained in both
`W ⊓ U i` and `W ⊓ U j`. -/
theorem sectionsι_trans {W : Opens X} (i j : ι) {Z : Opens X} (hi : Z ≤ W ⊓ U i)
    (hj : Z ≤ W ⊓ U j) :
    D.sectionsι W i ≫ (D.sheaf i).map hi ≫
      (D.trans i j (hi.trans inf_le_right) (hj.trans inf_le_right)).hom
      = D.sectionsι W j ≫ (D.sheaf j).map hj := by
  have h := D.sectionsι_condition W i j =≫ (D.sheaf j).map (le_inf hi hj)
  simp only [Category.assoc, ← D.trans_map, AlgLocalPresheaf.map_map_assoc,
    AlgLocalPresheaf.map_map] at h
  exact h

/-- Two morphisms into the glued sections are equal as soon as all their components agree. -/
theorem sections_hom_ext {W : Opens X} {T : S.C} {f g : T ⟶ D.sections W}
    (h : ∀ i, f ≫ D.sectionsι W i = g ≫ D.sectionsι W i) : f = g :=
  Multiequalizer.hom_ext _ _ _ h

/-- The family of restricted components of the glued sections over `W` satisfies the equations
defining the glued sections over `W' ≤ W`. -/
theorem sectionsι_map_condition {W W' : Opens X} (h : W' ≤ W) (i j : ι) :
    (D.sectionsι W i ≫ (D.sheaf i).map (inf_le_inf_right (U i) h)) ≫
        (D.sheaf i).map (inf_le_left : W' ⊓ U i ⊓ (W' ⊓ U j) ≤ W' ⊓ U i) ≫
          (D.trans i j (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).hom
      = (D.sectionsι W j ≫ (D.sheaf j).map (inf_le_inf_right (U j) h)) ≫
        (D.sheaf j).map (inf_le_right : W' ⊓ U i ⊓ (W' ⊓ U j) ≤ W' ⊓ U j) := by
  simp only [Category.assoc, AlgLocalPresheaf.map_map_assoc, AlgLocalPresheaf.map_map]
  exact D.sectionsι_trans i j _ _

/-- Restriction of the glued sections along an inclusion `W' ≤ W`. -/
noncomputable def sectionsMap {W W' : Opens X} (h : W' ≤ W) : D.sections W ⟶ D.sections W' :=
  Multiequalizer.lift (D.multicospanIndex W') _
    (fun i => D.sectionsι W i ≫ (D.sheaf i).map (inf_le_inf_right (U i) h)) fun r =>
      D.sectionsι_map_condition h r.1 r.2

@[reassoc (attr := simp)]
theorem sectionsMap_ι {W W' : Opens X} (h : W' ≤ W) (i : ι) :
    D.sectionsMap h ≫ D.sectionsι W' i
      = D.sectionsι W i ≫ (D.sheaf i).map (inf_le_inf_right (U i) h) :=
  Multiequalizer.lift_ι _ _ _ _ _

/-- **Stacks 00AM.** The glued presheaf with values in `S.C`: its sections over `W` are the
equalizer `D.sections W`, restricted componentwise. -/
@[stacks 00AM "sheaves of algebraic structures"]
noncomputable def gluedPresheaf : X.Presheaf S.C where
  obj W := D.sections W.unop
  map h := D.sectionsMap h.unop.le
  map_id W := D.sections_hom_ext fun i => by
    rw [sectionsMap_ι, (D.sheaf i).map_id, Category.comp_id, Category.id_comp]
  map_comp f g := D.sections_hom_ext fun i => by
    simp only [Category.assoc, sectionsMap_ι, sectionsMap_ι_assoc, AlgLocalPresheaf.map_map]

/-! ### The underlying presheaf of sets -/

/-- The sections of the diagram `D.multicospanIndex W` after forgetting to sets are the compatible
families of Stacks 00AL. -/
def multicospanSectionsEquiv (W : Opens X) :
    ((D.multicospanIndex W).multicospan ⋙ S.F).sections ≃ D.toGlueData.Sections W where
  toFun x := ⟨fun i => x.1 (WalkingMulticospan.left i), fun i j =>
    (Functor.map_comp_apply S.F _ _ _).symm.trans
      ((x.2 (WalkingMulticospan.Hom.fst (J := MulticospanShape.prod ι) (i, j))).trans
        (x.2 (WalkingMulticospan.Hom.snd (J := MulticospanShape.prod ι) (i, j))).symm)⟩
  invFun s :=
    { val := fun k => match k with
        | WalkingMulticospan.left i => s.1 i
        | WalkingMulticospan.right r => S.F.map ((D.multicospanIndex W).fst r) (s.1 r.1)
      property := by
        rintro (a | b) (a' | b') (f | f | f)
        · simp
          rfl
        · rfl
        · rcases b' with ⟨i, j⟩
          exact ((Functor.map_comp_apply S.F _ _ _).trans (s.2 i j)).symm
        · simp
          rfl }
  left_inv x := by
    ext (a | b)
    · rfl
    · exact x.2 (WalkingMulticospan.Hom.fst (J := MulticospanShape.prod ι) b)
  right_inv s := rfl

/-- The underlying set of the glued sections over `W` is the set of compatible families of
Stacks 00AL, the bijection being given by the components `D.sectionsι W i`. -/
noncomputable def sectionsEquiv (W : Opens X) :
    S.F.obj (D.sections W) ≃ D.toGlueData.Sections W :=
  (Types.isLimitEquivSections
    (isLimitOfPreserves S.F (limit.isLimit (D.multicospanIndex W).multicospan))).trans
    (D.multicospanSectionsEquiv W)

theorem sectionsEquiv_apply_val (W : Opens X) (x : S.F.obj (D.sections W)) (i : ι) :
    (D.sectionsEquiv W x).1 i = S.F.map (D.sectionsι W i) x := rfl

/-- **Stacks 00AM.** The underlying presheaf of sets of the glued presheaf with values in `S.C` is
the presheaf of sets glued in Stacks 00AL. -/
@[stacks 00AM "sheaves of algebraic structures"]
noncomputable def forgetIso : D.gluedPresheaf ⋙ S.F ≅ D.toGlueData.gluedPresheaf :=
  NatIso.ofComponents (fun W => (D.sectionsEquiv W.unop).toIso) fun {W W'} h => by
    ext x
    refine GlueData.Sections.ext fun i => ?_
    change (D.sectionsEquiv W'.unop (S.F.map (D.sectionsMap h.unop.le) x)).1 i
      = S.F.map ((D.sheaf i).map _) ((D.sectionsEquiv W.unop x).1 i)
    exact (Functor.map_comp_apply S.F _ _ _).symm.trans
      ((congrArg (fun f => S.F.map f x) (D.sectionsMap_ι h.unop.le i)).trans
        (Functor.map_comp_apply S.F _ _ _))

/-- **Stacks 00AM** (sheaves of algebraic structures). The presheaf with values in `S.C` glued
from a glueing data of sheaves with values in `S.C` is a sheaf: its underlying presheaf of sets is
the sheaf of Stacks 00AL, and `S.F` reflects the sheaf condition. -/
@[stacks 00AM "sheaves of algebraic structures"]
theorem gluedPresheaf_isSheaf : D.gluedPresheaf.IsSheaf :=
  (Presheaf.isSheaf_iff_isSheaf_comp S.F _).2
    (Presheaf.isSheaf_of_iso D.forgetIso.symm D.toGlueData.gluedPresheaf_isSheaf)

/-- The sheaf with values in `S.C` on `X` glued from a glueing data of sheaves with values in
`S.C`. -/
@[stacks 00AM "sheaves of algebraic structures"]
noncomputable def glued : X.Sheaf S.C := ⟨D.gluedPresheaf, D.gluedPresheaf_isSheaf⟩

/-! ### The comparison isomorphisms -/

/-- The comparison map `φ i : F|_{U i} ⟶ F i` on sections over an open `V ≤ U i`, in `S.C`. -/
noncomputable def sectionsHom (i : ι) {V : Opens X} (hV : V ≤ U i) :
    D.sections V ⟶ (D.sheaf i).obj V hV :=
  D.sectionsι V i ≫ (D.sheaf i).map (le_inf le_rfl hV)

/-- After forgetting to sets, `φ i` is the comparison bijection of Stacks 00AL. -/
theorem sectionsHom_apply (i : ι) {V : Opens X} (hV : V ≤ U i) (x : S.F.obj (D.sections V)) :
    S.F.map (D.sectionsHom i hV) x = D.toGlueData.sectionsEquiv i hV (D.sectionsEquiv V x) := by
  rw [sectionsHom, Functor.map_comp_apply]
  rfl

instance isIso_sectionsHom (i : ι) {V : Opens X} (hV : V ≤ U i) : IsIso (D.sectionsHom i hV) := by
  have : IsIso (S.F.map (D.sectionsHom i hV)) := by
    rw [isIso_iff_bijective]
    have h : (S.F.map (D.sectionsHom i hV) : S.F.obj (D.sections V) → _)
        = (D.sectionsEquiv V).trans (D.toGlueData.sectionsEquiv i hV) :=
      funext (D.sectionsHom_apply i hV)
    rw [h]
    exact Equiv.bijective _
  exact isIso_of_reflects_iso _ S.F

/-- **Stacks 00AM** (sheaves of algebraic structures). The comparison isomorphism
`φ i : F|_{U i} ≅ F i` on sections over an open `V ≤ U i`, as an isomorphism in `S.C`. -/
@[stacks 00AM "sheaves of algebraic structures"]
noncomputable def sectionsIso (i : ι) {V : Opens X} (hV : V ≤ U i) :
    D.sections V ≅ (D.sheaf i).obj V hV :=
  asIso (D.sectionsHom i hV)

/-- The comparison isomorphism `φ i` commutes with the restriction maps, i.e. it is an
isomorphism of sheaves on `U i`. -/
@[reassoc]
theorem sectionsMap_sectionsIso_hom (i : ι) {V W : Opens X} (hV : V ≤ U i) (hWV : W ≤ V) :
    D.sectionsMap hWV ≫ (D.sectionsIso i (hWV.trans hV)).hom
      = (D.sectionsIso i hV).hom ≫ (D.sheaf i).map hWV := by
  simp only [sectionsIso, asIso_hom, sectionsHom, sectionsMap_ι_assoc, Category.assoc,
    AlgLocalPresheaf.map_map]

/-- **Stacks 00AM** (sheaves of algebraic structures). The commuting diagram `φ i j ∘ φ i = φ j`
over the overlaps. -/
@[reassoc, stacks 00AM "sheaves of algebraic structures"]
theorem sectionsIso_hom_trans (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) :
    (D.sectionsIso i hi).hom ≫ (D.trans i j hi hj).hom = (D.sectionsIso j hj).hom := by
  simp only [sectionsIso, asIso_hom, sectionsHom, Category.assoc]
  exact D.sectionsι_trans i j (le_inf le_rfl hi) (le_inf le_rfl hj)

end AlgGlueData

end TopCat.Sheaf
