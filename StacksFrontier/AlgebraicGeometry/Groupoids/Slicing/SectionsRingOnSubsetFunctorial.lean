module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.FlatBaseChangeOnIntersection

/-!
# Functoriality of the sections on a subset

`AlgebraicGeometry.Scheme.sectionsRingOnSubset` assigns to a scheme `X` and a subset `E ⊆ X` the
ring of sections of the inverse image of the structure sheaf on `E`. This file makes that
assignment contravariantly functorial in the scheme: a morphism `f : X ⟶ Y` and subsets
`E ⊆ Y`, `E' ⊆ X` with `E' ⊆ f⁻¹(E)` induce a ring map
`Γ(E, 𝒪_Y|_E) ⟶ Γ(E', 𝒪_X|_{E'})`, compatibly with identities and composition. In particular an
isomorphism of schemes carrying `E'` into `E` induces an isomorphism of the two rings of
sections.

## Main definitions

* `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap` is the induced map on sections over a subset.
* `AlgebraicGeometry.Scheme.sectionsRingOnSubsetIso` is the isomorphism of rings of sections
  induced by an isomorphism of schemes.
* `AlgebraicGeometry.subsetBaseMap` is the restriction of the continuous map underlying a morphism
  of schemes to a pair of subsets.
* `AlgebraicGeometry.schemeSheafHom` is the comparison map `𝒪_Y ⟶ f_* 𝒪_X` read as a morphism of
  sheaves.
* `AlgebraicGeometry.inverseImageAdjointHom` and `AlgebraicGeometry.inverseImageSheafMap` are the
  two sides of the adjunction producing the induced map.

## Main results

* `AlgebraicGeometry.Scheme.topToSubset_comp_sectionsRingOnSubsetMap`: pulling a global function
  back along `f` and restricting it to `E'` is restricting it to `E` and then applying the induced
  map.
* `AlgebraicGeometry.Scheme.stageToSubset_comp_sectionsRingOnSubsetMap`: the same statement with
  the global functions replaced by the functions on a member of a family of opens containing the
  subset, that is on a stage of `AlgebraicGeometry.Scheme.sectionsRingDiagram`.
* `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap_id` and
  `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap_comp`: functoriality.
* `AlgebraicGeometry.Scheme.isIso_sectionsRingOnSubsetMap`: the induced map of an isomorphism of
  schemes is an isomorphism.

## Implementation notes

The subset is a `Set`, not an `Opens`. The inverse image of the structure sheaf along the
inclusion `i_E : E ↪ X` of an arbitrary subset is the sheaf pullback
`TopCat.Sheaf.pullback CommRingCat i_E`, the sheafification of a left Kan extension, and
`AlgebraicGeometry.Scheme.sectionsRingOnSubset` is its value at the total open `⊤` of `E`. There
is no formula for an element of it, so the induced map is produced by the adjunction
`TopCat.Sheaf.pullbackPushforwardAdjunction`.

Write `r : E' ⟶ E` for the restriction of `f` to the two subsets. The identities
`r ≫ i_E = i_{E'} ≫ f`, the functoriality of `Opens.map` and of `TopCat.Sheaf.pushforward` on
compositions, and `(Opens.map r).obj ⊤ = ⊤` all hold by `rfl`, so the sheaf
`(i_E)_* r_* (i_{E'})^* 𝒪_X` on `Y` is the sheaf `f_* (i_{E'})_* (i_{E'})^* 𝒪_X` with no
transport. These identities are definitional but not syntactic, so the equations between the two
readings of a sheaf are proved in term mode rather than by `rw`.

## References

* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The restriction of a morphism to a pair of subsets -/

/-- The restriction of the continuous map underlying a morphism of schemes `f : X ⟶ Y` to a
subset `E' ⊆ X` mapping into a subset `E ⊆ Y`. -/
def subsetBaseMap {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Set Y) (E' : Set X)
    (h : E' ⊆ f.base ⁻¹' E) : TopCat.of E' ⟶ TopCat.of E :=
  TopCat.ofHom ⟨fun x ↦ ⟨f.base x.1, h x.2⟩, by fun_prop⟩

/-- Restricting a composition of morphisms of schemes to subsets is composing the restrictions. -/
lemma subsetBaseMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (EZ : Set Z) (EY : Set Y)
    (EX : Set X) (h₁ : EY ⊆ g.base ⁻¹' EZ) (h₂ : EX ⊆ f.base ⁻¹' EY) :
    subsetBaseMap f EY EX h₂ ≫ subsetBaseMap g EZ EY h₁ =
      subsetBaseMap (f ≫ g) EZ EX (fun _ hx ↦ h₁ (h₂ hx)) :=
  rfl

/-- Restricting the identity to a subset and itself is the identity. -/
lemma subsetBaseMap_id {X : Scheme.{u}} (E : Set X) (h : E ⊆ (𝟙 X : X ⟶ X).base ⁻¹' E) :
    subsetBaseMap (𝟙 X) E E h = 𝟙 _ :=
  rfl

/-! ### The comparison map of sheaves -/

/-- The comparison map `𝒪_Y ⟶ f_* 𝒪_X` of a morphism of schemes, read as a morphism of sheaves of
commutative rings on `Y`. -/
def schemeSheafHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.toSheafedSpace.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.toSheafedSpace.sheaf :=
  ObjectProperty.homMk f.c

/-- The morphism `𝒪_Y ⟶ (i_E)_* r_* (i_{E'})^* 𝒪_X` adjoint to
`AlgebraicGeometry.inverseImageSheafMap`: the comparison map of `f` followed by the unit of the
inverse-image adjunction on `E'`, pushed forward along `f`. The target is the sheaf
`f_* (i_{E'})_* (i_{E'})^* 𝒪_X`, read through the definitional identity
`r ≫ i_E = i_{E'} ≫ f`. -/
def inverseImageAdjointHom {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Set Y) (E' : Set X)
    (h : E' ⊆ f.base ⁻¹' E) :
    Y.toSheafedSpace.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u}
          (Stacks.subsetInclusion (TopCat.of Y) E)).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} (subsetBaseMap f E E' h)).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u}
            (Stacks.subsetInclusion (TopCat.of X) E')).obj X.toSheafedSpace.sheaf)) :=
  schemeSheafHom f ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (Stacks.subsetInclusion (TopCat.of X) E')).unit.app X.toSheafedSpace.sheaf)

/-- The map of sheaves on `E` from the inverse image of `𝒪_Y` to the pushforward along the
restriction `r : E' ⟶ E` of the inverse image of `𝒪_X`, adjoint to
`AlgebraicGeometry.inverseImageAdjointHom`. -/
def inverseImageSheafMap {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Set Y) (E' : Set X)
    (h : E' ⊆ f.base ⁻¹' E) :
    (TopCat.Sheaf.pullback CommRingCat.{u}
        (Stacks.subsetInclusion (TopCat.of Y) E)).obj Y.toSheafedSpace.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (subsetBaseMap f E E' h)).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u}
          (Stacks.subsetInclusion (TopCat.of X) E')).obj X.toSheafedSpace.sheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (Stacks.subsetInclusion (TopCat.of Y) E)).homEquiv Y.toSheafedSpace.sheaf
        ((TopCat.Sheaf.pushforward CommRingCat.{u} (subsetBaseMap f E E' h)).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u}
            (Stacks.subsetInclusion (TopCat.of X) E')).obj X.toSheafedSpace.sheaf))).symm
    (inverseImageAdjointHom f E E' h)

/-- The defining property of `AlgebraicGeometry.inverseImageSheafMap`: composing it, pushed
forward to `Y`, with the unit of the inverse-image adjunction on `E` gives
`AlgebraicGeometry.inverseImageAdjointHom`. -/
lemma unit_comp_inverseImageSheafMap {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Set Y) (E' : Set X)
    (h : E' ⊆ f.base ⁻¹' E) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (Stacks.subsetInclusion (TopCat.of Y) E)).unit.app Y.toSheafedSpace.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u}
          (Stacks.subsetInclusion (TopCat.of Y) E)).map (inverseImageSheafMap f E E' h) =
      inverseImageAdjointHom f E E' h :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (Stacks.subsetInclusion (TopCat.of Y) E)).homEquiv Y.toSheafedSpace.sheaf
        ((TopCat.Sheaf.pushforward CommRingCat.{u} (subsetBaseMap f E E' h)).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u}
            (Stacks.subsetInclusion (TopCat.of X) E')).obj
              X.toSheafedSpace.sheaf))).apply_symm_apply (inverseImageAdjointHom f E E' h)

/-- The adjoint morphisms compose: the comparison map of `g` followed by the pushforward along
`g` of the map of sheaves for `f` is the comparison map of `f ≫ g`. -/
lemma inverseImageAdjointHom_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (EZ : Set Z)
    (EY : Set Y) (EX : Set X) (h₁ : EY ⊆ g.base ⁻¹' EZ) (h₂ : EX ⊆ f.base ⁻¹' EY) :
    inverseImageAdjointHom g EZ EY h₁ ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u}
            (Stacks.subsetInclusion (TopCat.of Z) EZ)).map
          ((TopCat.Sheaf.pushforward CommRingCat.{u} (subsetBaseMap g EZ EY h₁)).map
            (inverseImageSheafMap f EY EX h₂)) =
      inverseImageAdjointHom (f ≫ g) EZ EX (fun _ hx ↦ h₁ (h₂ hx)) :=
  congrArg (fun z ↦ schemeSheafHom g ≫ z)
    (congrArg (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
      (unit_comp_inverseImageSheafMap f EY EX h₂))

/-- The maps of sheaves compose. -/
lemma inverseImageSheafMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (EZ : Set Z)
    (EY : Set Y) (EX : Set X) (h₁ : EY ⊆ g.base ⁻¹' EZ) (h₂ : EX ⊆ f.base ⁻¹' EY) :
    inverseImageSheafMap g EZ EY h₁ ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (subsetBaseMap g EZ EY h₁)).map
          (inverseImageSheafMap f EY EX h₂) =
      inverseImageSheafMap (f ≫ g) EZ EX (fun _ hx ↦ h₁ (h₂ hx)) :=
  (Adjunction.homEquiv_naturality_right_symm
        (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (Stacks.subsetInclusion (TopCat.of Z) EZ))
        (inverseImageAdjointHom g EZ EY h₁)
        ((TopCat.Sheaf.pushforward CommRingCat.{u} (subsetBaseMap g EZ EY h₁)).map
          (inverseImageSheafMap f EY EX h₂))).symm.trans
    (congrArg
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (Stacks.subsetInclusion (TopCat.of Z) EZ)).homEquiv Z.toSheafedSpace.sheaf
            ((TopCat.Sheaf.pushforward CommRingCat.{u} (subsetBaseMap g EZ EY h₁)).obj
              ((TopCat.Sheaf.pushforward CommRingCat.{u} (subsetBaseMap f EY EX h₂)).obj
                ((TopCat.Sheaf.pullback CommRingCat.{u}
                  (Stacks.subsetInclusion (TopCat.of X) EX)).obj
                    X.toSheafedSpace.sheaf)))).symm
      (inverseImageAdjointHom_comp f g EZ EY EX h₁ h₂))

/-- The map of sheaves attached to an identity is an identity. -/
lemma inverseImageSheafMap_id {X : Scheme.{u}} (E : Set X)
    (h : E ⊆ (𝟙 X : X ⟶ X).base ⁻¹' E) :
    inverseImageSheafMap (𝟙 X) E E h = 𝟙 _ :=
  Adjunction.homEquiv_symm_unit
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (Stacks.subsetInclusion (TopCat.of X) E)) X.toSheafedSpace.sheaf

/-! ### The induced map on the sections over a subset -/

/-- The map on sections over a subset induced by a morphism of schemes `f : X ⟶ Y` and subsets
`E ⊆ Y` and `E' ⊆ X` with `E' ⊆ f⁻¹(E)`: the restriction along `f` of a section of the inverse
image of `𝒪_Y` on `E` to a section of the inverse image of `𝒪_X` on `E'`. -/
def Scheme.sectionsRingOnSubsetMap {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Set Y) (E' : Set X)
    (h : E' ⊆ f.base ⁻¹' E) : Y.sectionsRingOnSubset E ⟶ X.sectionsRingOnSubset E' :=
  (inverseImageSheafMap f E E' h).hom.app (op ⊤)

/-- The induced map does not depend on the morphism beyond its value, so a provable equality of
morphisms may be substituted even though the containment hypotheses differ. -/
lemma Scheme.sectionsRingOnSubsetMap_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f')
    (E : Set Y) (E' : Set X) (h : E' ⊆ f.base ⁻¹' E) (h' : E' ⊆ f'.base ⁻¹' E) :
    Scheme.sectionsRingOnSubsetMap f E E' h = Scheme.sectionsRingOnSubsetMap f' E E' h' := by
  subst e
  rfl

/-- The map on the sections over `E` induced by the identity of `X` is the identity. -/
@[simp]
lemma Scheme.sectionsRingOnSubsetMap_id {X : Scheme.{u}} (E : Set X)
    (h : E ⊆ (𝟙 X : X ⟶ X).base ⁻¹' E) :
    Scheme.sectionsRingOnSubsetMap (𝟙 X) E E h = 𝟙 (X.sectionsRingOnSubset E) :=
  congrArg (fun z ↦ z.hom.app (op ⊤)) (inverseImageSheafMap_id E h)

/-- The map on the sections over subsets induced by a composite `f ≫ g` is the composite of the
maps induced by `g` and by `f`. -/
@[reassoc]
lemma Scheme.sectionsRingOnSubsetMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (EZ : Set Z) (EY : Set Y) (EX : Set X) (h₁ : EY ⊆ g.base ⁻¹' EZ)
    (h₂ : EX ⊆ f.base ⁻¹' EY) :
    Scheme.sectionsRingOnSubsetMap g EZ EY h₁ ≫ Scheme.sectionsRingOnSubsetMap f EY EX h₂ =
      Scheme.sectionsRingOnSubsetMap (f ≫ g) EZ EX (fun _ hx ↦ h₁ (h₂ hx)) :=
  congrArg (fun z ↦ z.hom.app (op ⊤)) (inverseImageSheafMap_comp f g EZ EY EX h₁ h₂)

/-! ### Compatibility with the restriction maps from an open -/

/-- The restriction of a global function to a subset is the value at `⊤` of the unit of the
inverse-image adjunction. -/
lemma Scheme.topToSubset_eq_unit_app (X : Scheme.{u}) (E : Set X) :
    X.topToSubset E =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (Stacks.subsetInclusion (TopCat.of X) E)).unit.app
          X.toSheafedSpace.sheaf).hom.app (op ⊤) := by
  have hid : ∀ i : (op ((Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj ⊤) :
        (TopologicalSpace.Opens (TopCat.of E))ᵒᵖ) ⟶ op ⊤,
      ((TopCat.Sheaf.pullback CommRingCat.{u}
          (Stacks.subsetInclusion (TopCat.of X) E)).obj X.toSheafedSpace.sheaf).obj.map i
        = 𝟙 _ := by
    intro i
    rw [Subsingleton.elim i (𝟙 _)]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.topToSubset, hid]
  exact Category.comp_id _

/-- Pulling a global function of `Y` back along `f` and restricting it to `E'` is restricting it
to `E` and then applying the induced map. -/
@[reassoc]
lemma Scheme.topToSubset_comp_sectionsRingOnSubsetMap {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Set Y)
    (E' : Set X) (h : E' ⊆ f.base ⁻¹' E) :
    Y.topToSubset E ≫ Scheme.sectionsRingOnSubsetMap f E E' h =
      f.appTop ≫ X.topToSubset E' := by
  rw [Y.topToSubset_eq_unit_app E, X.topToSubset_eq_unit_app E']
  exact congrArg (fun z ↦ z.hom.app (op ⊤)) (unit_comp_inverseImageSheafMap f E E' h)

/-- A composite of a naturality square with a commuting triangle. -/
private lemma comp_assoc_of_naturality {C : Type*} [Category C] {A M N N' B D : C}
    {a : A ⟶ M} {pm : M ⟶ N} {t : N ⟶ B} {tA : M ⟶ N'} {qm : N' ⟶ B} {c : A ⟶ D}
    {b : D ⟶ N'} (hnat : pm ≫ t = tA ≫ qm) (key : a ≫ tA = c ≫ b) :
    (a ≫ pm) ≫ t = c ≫ b ≫ qm := by
  rw [Category.assoc, hnat, ← Category.assoc, key, Category.assoc]

/-- The induced map is compatible with the restrictions from a family of opens containing the
subset: restricting a function on a member `U i` of such a family to `E` and then applying the
induced map is pulling it back to `f⁻¹(U i)` and restricting that to `E'`. -/
lemma Scheme.stageToSubset_comp_sectionsRingOnSubsetMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} (U : I → Y.Opens) (E : Set Y) (hE : ∀ i, E ⊆ U i) (E' : Set X)
    (h : E' ⊆ f.base ⁻¹' E) (i : intersectionIndex U) :
    Y.stageToSubset U E hE i ≫ Scheme.sectionsRingOnSubsetMap f E E' h =
      f.appLE (U i.val) (f ⁻¹ᵁ U i.val) le_rfl ≫
        X.stageToSubset (fun j ↦ f ⁻¹ᵁ U j) E' (fun j _ hx ↦ hE j (h hx)) ⟨i.val⟩ := by
  have hnat := (inverseImageSheafMap f E E' h).hom.naturality
    (homOfLE (show (⊤ : TopologicalSpace.Opens (TopCat.of E)) ≤
        (TopologicalSpace.Opens.map (Stacks.subsetInclusion (TopCat.of Y) E)).obj (U i.val) from
      fun x _ ↦ hE i.val x.2)).op
  have key :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            (Stacks.subsetInclusion (TopCat.of Y) E)).unit.app
          Y.toSheafedSpace.sheaf).hom.app (op (U i.val)) ≫
          (inverseImageSheafMap f E E' h).hom.app
            (op ((TopologicalSpace.Opens.map
              (Stacks.subsetInclusion (TopCat.of Y) E)).obj (U i.val))) =
        f.appLE (U i.val) (f ⁻¹ᵁ U i.val) le_rfl ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
              (Stacks.subsetInclusion (TopCat.of X) E')).unit.app
            X.toSheafedSpace.sheaf).hom.app (op (f ⁻¹ᵁ U i.val)) := by
    rw [Scheme.Hom.appLE_eq_app]
    exact congrArg (fun z ↦ z.hom.app (op (U i.val))) (unit_comp_inverseImageSheafMap f E E' h)
  exact comp_assoc_of_naturality hnat key

/-! ### The isomorphism induced by an isomorphism of schemes -/

/-- If `f : X ⟶ Y` is an isomorphism and `E' = f⁻¹(E)`, then `E` is contained in the preimage of
`E'` under the inverse of `f`. -/
lemma subset_preimage_inv_base {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (E : Set Y)
    (E' : Set X) (he : E' = f.base ⁻¹' E) : E ⊆ (inv f).base ⁻¹' E' := fun y hy ↦ by
  simpa [he, ← Scheme.Hom.comp_apply] using hy

/-- If `g ≫ f` is the identity, the induced map of `f` followed by the induced map of `g` is the
identity. -/
private lemma sectionsRingOnSubsetMap_comp_eq_id {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hgf : g ≫ f = 𝟙 Y) (E : Set Y) (E' : Set X) (h : E' ⊆ f.base ⁻¹' E)
    (h' : E ⊆ g.base ⁻¹' E') :
    Scheme.sectionsRingOnSubsetMap f E E' h ≫ Scheme.sectionsRingOnSubsetMap g E' E h' =
      𝟙 (Y.sectionsRingOnSubset E) :=
  have h₀ : E ⊆ (𝟙 Y : Y ⟶ Y).base ⁻¹' E := fun _ hx ↦ hx
  (Scheme.sectionsRingOnSubsetMap_comp g f E E' E h h').trans
    ((Scheme.sectionsRingOnSubsetMap_congr hgf E E _ h₀).trans
      (Scheme.sectionsRingOnSubsetMap_id E h₀))

/-- For an isomorphism `f` the induced map on sections over `E` followed by the induced map of
`inv f` is the identity. -/
lemma Scheme.sectionsRingOnSubsetMap_comp_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (E : Set Y) (E' : Set X) (h : E' ⊆ f.base ⁻¹' E) (h' : E ⊆ (inv f).base ⁻¹' E') :
    Scheme.sectionsRingOnSubsetMap f E E' h ≫ Scheme.sectionsRingOnSubsetMap (inv f) E' E h' =
      𝟙 (Y.sectionsRingOnSubset E) :=
  sectionsRingOnSubsetMap_comp_eq_id f (inv f) (IsIso.inv_hom_id f) E E' h h'

/-- For an isomorphism `f` the induced map of `inv f` followed by the induced map of `f` is the
identity. -/
lemma Scheme.sectionsRingOnSubsetMap_inv_comp {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (E : Set Y) (E' : Set X) (h : E' ⊆ f.base ⁻¹' E) (h' : E ⊆ (inv f).base ⁻¹' E') :
    Scheme.sectionsRingOnSubsetMap (inv f) E' E h' ≫ Scheme.sectionsRingOnSubsetMap f E E' h =
      𝟙 (X.sectionsRingOnSubset E') :=
  sectionsRingOnSubsetMap_comp_eq_id (inv f) f (IsIso.hom_inv_id f) E' E h' h

/-- An isomorphism of schemes carrying `E'` into `E` and `E` into `E'` the other way induces an
isomorphism of the rings of sections over the two subsets. -/
def Scheme.sectionsRingOnSubsetIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (E : Set Y)
    (E' : Set X) (h : E' ⊆ f.base ⁻¹' E) (h' : E ⊆ (inv f).base ⁻¹' E') :
    Y.sectionsRingOnSubset E ≅ X.sectionsRingOnSubset E' where
  hom := Scheme.sectionsRingOnSubsetMap f E E' h
  inv := Scheme.sectionsRingOnSubsetMap (inv f) E' E h'
  hom_inv_id := Scheme.sectionsRingOnSubsetMap_comp_inv f E E' h h'
  inv_hom_id := Scheme.sectionsRingOnSubsetMap_inv_comp f E E' h h'

/-- The forward map of `Scheme.sectionsRingOnSubsetIso f E E' h h'` is the map on the sections
induced by `f`. -/
@[simp]
lemma Scheme.sectionsRingOnSubsetIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (E : Set Y)
    (E' : Set X) (h : E' ⊆ f.base ⁻¹' E) (h' : E ⊆ (inv f).base ⁻¹' E') :
    (Scheme.sectionsRingOnSubsetIso f E E' h h').hom =
      Scheme.sectionsRingOnSubsetMap f E E' h :=
  rfl

/-- The inverse map of `Scheme.sectionsRingOnSubsetIso f E E' h h'` is the map on the sections
induced by `inv f`. -/
@[simp]
lemma Scheme.sectionsRingOnSubsetIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (E : Set Y)
    (E' : Set X) (h : E' ⊆ f.base ⁻¹' E) (h' : E ⊆ (inv f).base ⁻¹' E') :
    (Scheme.sectionsRingOnSubsetIso f E E' h h').inv =
      Scheme.sectionsRingOnSubsetMap (inv f) E' E h' :=
  rfl

/-- The map on sections induced by an isomorphism of schemes is an isomorphism. -/
lemma Scheme.isIso_sectionsRingOnSubsetMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (E : Set Y)
    (E' : Set X) (h : E' ⊆ f.base ⁻¹' E) (h' : E ⊆ (inv f).base ⁻¹' E') :
    IsIso (Scheme.sectionsRingOnSubsetMap f E E' h) :=
  (Scheme.sectionsRingOnSubsetIso f E E' h h').isIso_hom

end AlgebraicGeometry

end

end
