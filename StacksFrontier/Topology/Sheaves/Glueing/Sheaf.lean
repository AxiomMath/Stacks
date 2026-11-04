module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute

/-!
# Glueing sheaves of sets along an open covering

Let `X` be a topological space and let `U : ι → Opens X` be a family of opens. A *glueing datum*
for sheaves of sets consists of a sheaf of sets `F i` on each `U i` together with comparison
isomorphisms `φ i j : (F i)|_{U i ⊓ U j} ≅ (F j)|_{U i ⊓ U j}` satisfying the cocycle condition
`φ j k ∘ φ i j = φ i k` on `U i ⊓ U j ⊓ U k`. Stacks 00AL builds from such a datum a sheaf `F` on
`X` together with isomorphisms `φ i : F|_{U i} ≅ F i` compatible with the `φ i j`.

## Main definitions

* `TopCat.Sheaf.LocalPresheaf`: a presheaf on an open `U` of `X`, presented as data indexed by the
  opens of `X` contained in `U`.
* `TopCat.Sheaf.LocalPresheaf.IsSheaf`: the sheaf condition for a `LocalPresheaf`.
* `TopCat.Sheaf.GlueData`: a glueing datum for sheaves of sets with respect to `U`.
* `TopCat.Sheaf.GlueData.Sections`: the sections of the glued sheaf over an open of `X`.
* `TopCat.Sheaf.GlueData.glued`: the sheaf of sets on `X` glued from a glueing datum.
* `TopCat.Sheaf.GlueData.sectionsEquiv`: the comparison isomorphism `φ i : F|_{U i} ≅ F i`, on
  sections over an open `V ≤ U i`.

## Main results

* `TopCat.Sheaf.GlueData.gluedPresheaf_isSheaf`: the glued presheaf is a sheaf.
* `TopCat.Sheaf.GlueData.sectionsEquiv_map`: `φ i` commutes with the restriction maps, i.e. it is
  an isomorphism of sheaves on `U i`.
* `TopCat.Sheaf.GlueData.trans_sectionsEquiv`: the commuting triangle `φ i j ∘ φ i = φ j`.

## References

* [Stacks Project, Tag 00AL](https://stacks.math.columbia.edu/tag/00AL)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-! ### Presheaves and sheaves on an open subset -/

/-- A presheaf of sets on an open `U` of `X`, presented as data indexed by the opens of `X`
contained in `U`. -/
structure LocalPresheaf (X : TopCat.{u}) (U : Opens X) where
  /-- The sections over an open `V` of `X` contained in `U`. -/
  obj : (V : Opens X) → V ≤ U → Type u
  /-- Restriction of sections along an inclusion `W ≤ V` of opens contained in `U`. -/
  map : ∀ {V W : Opens X} {hV : V ≤ U} (hWV : W ≤ V), obj V hV → obj W (hWV.trans hV)
  /-- Restricting along the identity is the identity. -/
  map_id : ∀ {V : Opens X} {hV : V ≤ U} (s : obj V hV), map le_rfl s = s
  /-- Restriction is compatible with composition of inclusions. -/
  map_map : ∀ {V W Z : Opens X} {hV : V ≤ U} (hWV : W ≤ V) (hZW : Z ≤ W) (s : obj V hV),
      map hZW (map hWV s) = map (hZW.trans hWV) s

namespace LocalPresheaf

/-- The sheaf condition for a `LocalPresheaf`: over every open `V ≤ U` and every covering of `V`
by opens of `X` contained in `V`, compatible families of sections glue uniquely. -/
def IsSheaf {U : Opens X} (F : LocalPresheaf X U) : Prop :=
  ∀ ⦃ι : Type u⦄ {V : Opens X} (hV : V ≤ U) (W : ι → Opens X) (hWV : ∀ k, W k ≤ V)
      (_hcov : V ≤ ⨆ k, W k) (s : ∀ k, F.obj (W k) ((hWV k).trans hV)),
      (∀ k l, F.map (inf_le_left : W k ⊓ W l ≤ W k) (s k)
            = F.map (inf_le_right : W k ⊓ W l ≤ W l) (s l)) →
      ∃! t : F.obj V hV, ∀ k, F.map (hWV k) t = s k

/-- Two sections that agree after restriction to an open `Z` also agree after restriction to any
open contained in `Z`. -/
theorem map_eq_map_of_le {U : Opens X} (F : LocalPresheaf X U) {V₁ V₂ Z Z' : Opens X}
    {h₁ : V₁ ≤ U} {h₂ : V₂ ≤ U} {s₁ : F.obj V₁ h₁} {s₂ : F.obj V₂ h₂} {hZ₁ : Z ≤ V₁}
    {hZ₂ : Z ≤ V₂} (h : F.map hZ₁ s₁ = F.map hZ₂ s₂) (hZ' : Z' ≤ Z) :
    F.map (hZ'.trans hZ₁) s₁ = F.map (hZ'.trans hZ₂) s₂ :=
  calc F.map (hZ'.trans hZ₁) s₁ = F.map hZ' (F.map hZ₁ s₁) := (F.map_map hZ₁ hZ' s₁).symm
    _ = F.map hZ' (F.map hZ₂ s₂) := by rw [h]
    _ = F.map (hZ'.trans hZ₂) s₂ := F.map_map hZ₂ hZ' s₂

/-- A section of a sheaf on `U` is determined by its restrictions to a covering family. -/
theorem IsSheaf.eq_of_locally_eq {U : Opens X} {F : LocalPresheaf X U} (hF : F.IsSheaf)
    {ι : Type u} {V : Opens X} {hV : V ≤ U} (W : ι → Opens X) (hWV : ∀ k, W k ≤ V)
    (hcov : V ≤ ⨆ k, W k) {a b : F.obj V hV} (h : ∀ k, F.map (hWV k) a = F.map (hWV k) b) :
    a = b := by
  obtain ⟨_, -, huniq⟩ := hF hV W hWV hcov (fun k => F.map (hWV k) a)
    fun k l => by rw [F.map_map, F.map_map]
  exact (huniq a fun _ => rfl).trans (huniq b fun k => (h k).symm).symm

/-- A morphism of local presheaves on `U`: a family of maps on sections over the opens of `X`
contained in `U`, compatible with the restriction maps. -/
@[ext]
structure Hom {U : Opens X} (F G : LocalPresheaf X U) where
  /-- The map on sections over an open `V ≤ U`. -/
  app : ∀ (V : Opens X) (hV : V ≤ U), F.obj V hV → G.obj V hV
  /-- Compatibility with the restriction maps of `F` and `G`. -/
  naturality : ∀ {V W : Opens X} {hV : V ≤ U} (hWV : W ≤ V) (s : F.obj V hV),
      app W (hWV.trans hV) (F.map hWV s) = G.map hWV (app V hV s)

namespace Hom

variable {U : Opens X} {F G H : LocalPresheaf X U}

/-- The identity morphism of a local presheaf. -/
protected def id (F : LocalPresheaf X U) : Hom F F where
  app _ _ := id
  naturality _ _ := rfl

/-- Composition of morphisms of local presheaves. -/
protected def comp (f : Hom F G) (g : Hom G H) : Hom F H where
  app V hV := g.app V hV ∘ f.app V hV
  naturality hWV s := by
    simp [f.naturality hWV s, g.naturality hWV (f.app _ _ s)]

/-- The map on sections of a composite of morphisms of local presheaves is the composite of the
maps on sections. -/
@[simp] theorem comp_app (f : Hom F G) (g : Hom G H) (V : Opens X) (hV : V ≤ U) :
    (f.comp g).app V hV = g.app V hV ∘ f.app V hV := rfl

end Hom

end LocalPresheaf

/-! ### Restricting a sheaf on `X` to an open subset -/

/-- The restriction of a presheaf on `X` to the opens contained in `U`. -/
def _root_.TopCat.Presheaf.toLocalPresheaf (F : X.Presheaf (Type u)) (U : Opens X) :
    LocalPresheaf X U where
  obj V _ := F.obj (op V)
  map hWV s := F.map (homOfLE hWV).op s
  map_id s := by
    rw [show (homOfLE (le_refl _) : _ ⟶ _).op = 𝟙 _ from Subsingleton.elim _ _, F.map_id]
    rfl
  map_map hWV hZW s := by
    rw [← types_comp_apply (F.map (homOfLE hWV).op) (F.map (homOfLE hZW).op) s, ← F.map_comp,
      show (homOfLE hWV).op ≫ (homOfLE hZW).op = (homOfLE (hZW.trans hWV)).op from
        Subsingleton.elim _ _]

/-- The restriction of a sheaf on `X` to an open `U` is a sheaf on `U`. -/
@[ega "0 3.1.5" "set-valued sheaves"]
theorem _root_.TopCat.Presheaf.isSheaf_toLocalPresheaf {F : X.Presheaf (Type u)} (hF : F.IsSheaf)
    (U : Opens X) : (F.toLocalPresheaf U).IsSheaf := by
  intro ι V hV W hWV hcov s hs
  refine TopCat.Sheaf.existsUnique_gluing' ⟨F, hF⟩ W V (fun k => homOfLE (hWV k)) hcov s
    fun k l => ?_
  rw [show Opens.infLELeft (W k) (W l) = homOfLE inf_le_left from Subsingleton.elim _ _,
    show Opens.infLERight (W k) (W l) = homOfLE inf_le_right from Subsingleton.elim _ _]
  exact hs k l

/-! ### Glueing data -/

/-- Glueing data for sheaves of sets with respect to the covering `X = ⋃ i, U i`:
a sheaf on each `U i` plus comparison isomorphisms over the overlaps satisfying the cocycle
condition. -/
structure GlueData (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X) where
  /-- The sheaf of sets on `U i`. -/
  sheaf : ∀ i, LocalPresheaf X (U i)
  /-- Each `sheaf i` satisfies the sheaf condition. -/
  isSheaf : ∀ i, (sheaf i).IsSheaf
  /-- The comparison isomorphism `φ i j` on sections over an open contained in both `U i` and
  `U j`. -/
  trans : ∀ (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j),
      (sheaf i).obj V hi ≃ (sheaf j).obj V hj
  /-- The comparison isomorphisms commute with the restriction maps. -/
  trans_map : ∀ (i j : ι) {V W : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
      (s : (sheaf i).obj V hi),
      trans i j (hWV.trans hi) (hWV.trans hj) ((sheaf i).map hWV s)
        = (sheaf j).map hWV (trans i j hi hj s)
  /-- The cocycle condition `φ j k ∘ φ i j = φ i k`. -/
  trans_trans : ∀ (i j k : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
      (s : (sheaf i).obj V hi),
      trans j k hj hk (trans i j hi hj s) = trans i k hi hk s

namespace GlueData

variable {ι : Type u} {U : ι → Opens X}

/-- The comparison isomorphism of a glueing datum from `U i` to itself is the identity. -/
theorem trans_self (D : GlueData X U) (i : ι) {V : Opens X} (hi : V ≤ U i) :
    D.trans i i hi hi = Equiv.refl _ := by
  ext s
  exact (D.trans i i hi hi).injective (D.trans_trans i i i hi hi hi s)

/-! ### The glued presheaf -/

/-- The sections of the glued sheaf over an open `W`: families `s i ∈ F_i(W ⊓ U i)` matching
under the `φ i j` on the overlaps. -/
def Sections (D : GlueData X U) (W : Opens X) : Type u :=
  {s : ∀ i, (D.sheaf i).obj (W ⊓ U i) inf_le_right //
    ∀ i j : ι, D.trans i j (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        ((D.sheaf i).map (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i) (s i))
      = (D.sheaf j).map (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j) (s j)}

namespace Sections

variable {D : GlueData X U} {W : Opens X}

/-- Two sections of the glued presheaf over `W` are equal as soon as all their components
agree. -/
@[ext] theorem ext {s t : D.Sections W} (h : ∀ i, s.1 i = t.1 i) : s = t := Subtype.ext (funext h)

/-- The defining compatibility of a section of the glued presheaf, over an arbitrary open contained
in both `W ⊓ U i` and `W ⊓ U j`. -/
theorem trans_map_eq (s : D.Sections W) (i j : ι) {Z : Opens X} (hi : Z ≤ W ⊓ U i)
    (hj : Z ≤ W ⊓ U j) :
    D.trans i j (hi.trans inf_le_right) (hj.trans inf_le_right) ((D.sheaf i).map hi (s.1 i))
      = (D.sheaf j).map hj (s.1 j) := by
  have h := congrArg ((D.sheaf j).map (le_inf hi hj)) (s.2 i j)
  rwa [← D.trans_map, (D.sheaf i).map_map, (D.sheaf j).map_map] at h

end Sections

/-- Restriction of the sections of the glued presheaf along an inclusion `W' ≤ W`. -/
def sectionsMap (D : GlueData X U) {W W' : Opens X} (h : W' ≤ W) (s : D.Sections W) :
    D.Sections W' :=
  ⟨fun i => (D.sheaf i).map (inf_le_inf_right (U i) h) (s.1 i), fun i j => by
    rw [(D.sheaf i).map_map, (D.sheaf j).map_map]
    exact s.trans_map_eq i j _ _⟩

/-- The components of a restricted compatible family are the restrictions of its components. -/
theorem sectionsMap_val (D : GlueData X U) {W W' : Opens X} (h : W' ≤ W)
    (s : D.Sections W) (i : ι) :
    (D.sectionsMap h s).1 i = (D.sheaf i).map (inf_le_inf_right (U i) h) (s.1 i) :=
  rfl

/-- The glued presheaf: its sections over `W` are the compatible families `D.Sections W`,
restricted componentwise. -/
def gluedPresheaf (D : GlueData X U) : X.Presheaf (Type u) where
  obj W := D.Sections W.unop
  map h := TypeCat.ofHom (D.sectionsMap h.unop.le)
  map_id W := by ext s i; exact (D.sheaf i).map_id _
  map_comp f g := by ext s i; exact ((D.sheaf i).map_map _ _ _).symm

/-- The glued presheaf is a sheaf. -/
@[ega "0 4.1.7" "partial"]
theorem gluedPresheaf_isSheaf (D : GlueData X U) : D.gluedPresheaf.IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro ι' W sf hsf
  have hcompat : ∀ (i : ι) (k l : ι') {Z : Opens X} (hk : Z ≤ W k ⊓ U i) (hl : Z ≤ W l ⊓ U i),
      (D.sheaf i).map hk ((sf k).1 i) = (D.sheaf i).map hl ((sf l).1 i) := by
    intro i k l Z hk hl
    have h : (D.sheaf i).map (inf_le_inf_right (U i) (inf_le_left : W k ⊓ W l ≤ W k)) ((sf k).1 i)
        = (D.sheaf i).map (inf_le_inf_right (U i) (inf_le_right : W k ⊓ W l ≤ W l))
            ((sf l).1 i) :=
      congrArg (fun z : D.Sections (W k ⊓ W l) => z.1 i) (hsf k l)
    exact (D.sheaf i).map_eq_map_of_le h
      (le_inf (le_inf (hk.trans inf_le_left) (hl.trans inf_le_left)) (hk.trans inf_le_right))
  choose t ht htuniq using fun i : ι => D.isSheaf i (inf_le_right : (⨆ k, W k) ⊓ U i ≤ U i)
    (fun k => W k ⊓ U i) (fun k => inf_le_inf_right (U i) (le_iSup W k))
    (iSup_inf_eq W (U i)).le (fun k => (sf k).1 i) fun k l => hcompat i k l _ _
  have hres : ∀ (i : ι) (k : ι') {Z : Opens X} (hZ : Z ≤ W k ⊓ U i)
      (hZ' : Z ≤ (⨆ k, W k) ⊓ U i),
      (D.sheaf i).map hZ' (t i) = (D.sheaf i).map hZ ((sf k).1 i) := fun i k Z hZ _ =>
    ((D.sheaf i).map_map (inf_le_inf_right (U i) (le_iSup W k)) hZ (t i)).symm.trans
      (congrArg ((D.sheaf i).map hZ) (ht i k))
  refine ⟨⟨t, fun i j => ?_⟩, fun k => Sections.ext fun i => ht i k, fun u hu =>
    Sections.ext fun i => htuniq i (u.1 i) fun k =>
      congrArg (fun z : D.Sections (W k) => z.1 i) (hu k)⟩
  refine (D.isSheaf j).eq_of_locally_eq
    (fun k => ((⨆ k, W k) ⊓ U i) ⊓ ((⨆ k, W k) ⊓ U j) ⊓ W k) (fun _ => inf_le_left)
    (le_trans (le_inf le_rfl (inf_le_left.trans inf_le_left))
      (inf_iSup_eq (((⨆ k, W k) ⊓ U i) ⊓ ((⨆ k, W k) ⊓ U j)) W).le) fun k => ?_
  rw [← D.trans_map i j _ _ (inf_le_left :
      ((⨆ k, W k) ⊓ U i) ⊓ ((⨆ k, W k) ⊓ U j) ⊓ W k ≤ ((⨆ k, W k) ⊓ U i) ⊓ ((⨆ k, W k) ⊓ U j)),
    (D.sheaf i).map_map, (D.sheaf j).map_map,
    hres i k (le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans inf_le_right)))
      (inf_le_left.trans inf_le_left),
    hres j k (le_inf inf_le_right (inf_le_left.trans (inf_le_right.trans inf_le_right)))
      (inf_le_left.trans inf_le_right)]
  exact (sf k).trans_map_eq i j _ _

/-- The sheaf of sets on `X` glued from the glueing data `D`. -/
@[stacks 00AL, ega "0 4.1.7" "partial"]
def glued (D : GlueData X U) : X.Sheaf (Type u) := ⟨D.gluedPresheaf, D.gluedPresheaf_isSheaf⟩

/-! ### The comparison isomorphisms -/

/-- The comparison isomorphism `φ i : F|_{U i} ≅ F_i` on sections over an open `V ≤ U i`. -/
@[stacks 00AL]
def sectionsEquiv (D : GlueData X U) (i : ι) {V : Opens X} (hV : V ≤ U i) :
    D.Sections V ≃ (D.sheaf i).obj V hV where
  toFun s := (D.sheaf i).map (le_inf le_rfl hV) (s.1 i)
  invFun t := ⟨fun j => D.trans i j (inf_le_left.trans hV) inf_le_right
      ((D.sheaf i).map (inf_le_left : V ⊓ U j ≤ V) t), fun j k => by
    rw [← D.trans_map i j _ _ (inf_le_left : V ⊓ U j ⊓ (V ⊓ U k) ≤ V ⊓ U j),
      ← D.trans_map i k _ _ (inf_le_right : V ⊓ U j ⊓ (V ⊓ U k) ≤ V ⊓ U k),
      (D.sheaf i).map_map, (D.sheaf i).map_map, D.trans_trans]⟩
  left_inv s := Sections.ext fun j => by
    dsimp only
    rw [(D.sheaf i).map_map, s.trans_map_eq i j (inf_le_left.trans (le_inf le_rfl hV))
      (le_rfl : V ⊓ U j ≤ V ⊓ U j), (D.sheaf j).map_id]
  right_inv t := by
    dsimp only
    rw [D.trans_self, Equiv.refl_apply, (D.sheaf i).map_map, (D.sheaf i).map_id]

/-- The comparison map `φ i` restricts the `i`-th component of a compatible family to `V`. -/
theorem sectionsEquiv_apply (D : GlueData X U) (i : ι) {V : Opens X} (hV : V ≤ U i)
    (s : D.Sections V) :
    D.sectionsEquiv i hV s = (D.sheaf i).map (le_inf le_rfl hV) (s.1 i) :=
  rfl

/-- The comparison isomorphism `φ i` commutes with the restriction maps, i.e. it is an
isomorphism of sheaves on `U i`. -/
@[stacks 00AL]
theorem sectionsEquiv_map (D : GlueData X U) (i : ι) {V W : Opens X} (hV : V ≤ U i) (hWV : W ≤ V)
    (s : D.Sections V) :
    D.sectionsEquiv i (hWV.trans hV) (D.sectionsMap hWV s)
      = (D.sheaf i).map hWV (D.sectionsEquiv i hV s) := by
  rw [sectionsEquiv_apply, sectionsEquiv_apply, sectionsMap_val, (D.sheaf i).map_map,
    (D.sheaf i).map_map]

/-- The commuting diagram `φ i j ∘ φ i = φ j` over the overlaps. -/
@[stacks 00AL]
theorem trans_sectionsEquiv (D : GlueData X U) (i j : ι) {V : Opens X} (hi : V ≤ U i)
    (hj : V ≤ U j) (s : D.Sections V) :
    D.trans i j hi hj (D.sectionsEquiv i hi s) = D.sectionsEquiv j hj s :=
  s.trans_map_eq i j (le_inf le_rfl hi) (le_inf le_rfl hj)

end GlueData

end TopCat.Sheaf
