module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Transporting an open of one stage across a directed system of thickenings

Let `D : Λ ⥤ (Sch/S)_fppf` be a diagram in the big fppf site over `S`, indexed by a preorder
with a least element `o`, whose transition morphisms are **thickenings** of the underlying
schemes. A thickening is a homeomorphism on underlying spaces, so it induces an order
isomorphism of the lattices of opens (`Stacks.Thickenings.IsThickening.opensCongr`); an open `V`
of the stage `D o` therefore has a canonical counterpart in every later stage.

This file assembles those counterparts into a **functor on the index**: a diagram
`transportedOpenDiagram` in the site, together with a natural transformation to `D` whose
components are the open immersions. Its transition morphisms are again thickenings, its stages
are affine as soon as `V` is, each of its squares over `D` is cartesian, and for `V` ranging
over the affine opens of `D o` the stages cover `D i` for every `i`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.transportedOpen`: the open of the stage `D i` matching an open
  of the least stage.
* `AlgebraicGeometry.FormalSpace.transportedOpenDiagram`: those opens, as a diagram in the site.
* `AlgebraicGeometry.FormalSpace.transportedOpenInclusion`: its natural open immersion into `D`.

## Main results

* `AlgebraicGeometry.FormalSpace.preimage_transportedOpen`: the transported opens are compatible
  with the transitions — the preimage of the one at `j` is the one at `i`.
* `AlgebraicGeometry.FormalSpace.isThickening_transportedOpenDiagram_map`: the transitions of the
  diagram are thickenings.
* `AlgebraicGeometry.FormalSpace.isAffine_transportedOpenDiagram_obj`: its stages are affine when
  `V` is an affine open.
* `AlgebraicGeometry.FormalSpace.isPullback_transportedOpenInclusion`: each square over `D` is
  cartesian, in the site.
* `AlgebraicGeometry.FormalSpace.iSup_transportedOpen_eq_top`: the transports of a covering
  family of opens of the least stage cover every stage.

## Implementation notes

Morphisms of a preorder, viewed as a category, are unique, so the composite of the transition
`o ⟶ i` with the transition `i ⟶ j` *is* the transition `o ⟶ j`, and the compatibility of the
transported opens with the transitions follows from
`Stacks.Thickenings.IsThickening.preimage_opensCongr` at `j` together with injectivity of taking
preimages along the thickening out of the least stage — which is
`Stacks.Thickenings.IsThickening.opensCongr_preimage`, the other half of the order isomorphism.

The transition morphisms of the diagram are `CategoryTheory.Scheme.Hom.resLE` rather than
`AlgebraicGeometry.morphismRestrict`: `Scheme.Hom.resLE_comp_resLE` and
`Scheme.Hom.resLE_id` are then the functoriality, with no `eqToHom` to transport, and
`Scheme.Hom.resLE_eq_morphismRestrict` converts to the restriction when a property of the
restriction is wanted.

The site is closed under passing to an open subscheme because an open immersion does not raise
the size of a scheme (`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion`), and the structure
morphism to `S` of the open subscheme is its inclusion followed by that of the ambient stage.

## References

* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings

namespace AlgebraicGeometry.FormalSpace

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ : Type w} [Preorder Λ] (D : Λ ⥤ BigFppfOver B S hS)
  (hD : ∀ ⦃i j : Λ⦄ (f : i ⟶ j),
    IsThickening ((BigFppfOver.toScheme B S hS).map (D.map f)))
  (o : Λ) (ho : ∀ i : Λ, o ≤ i)

/-! ### Generic facts about `Scheme.Hom.resLE` -/

/-- A restriction of the identity to one open is the identity. -/
private theorem resLE_eq_id {X : Scheme.{u}} {s : X ⟶ X} (hs : s = 𝟙 X) {U : X.Opens}
    (e : U ≤ s ⁻¹ᵁ U) : s.resLE U U e = 𝟙 U.toScheme := by
  refine (cancel_mono U.ι).mp ?_
  rw [Scheme.Hom.resLE_comp_ι, hs, Category.comp_id, Category.id_comp]

/-- Restriction depends on the morphism only through its value, the inclusion of opens being a
proposition. -/
private theorem resLE_congr_hom {X Y : Scheme.{u}} {s s' : X ⟶ Y} (hs : s = s') {U : Y.Opens}
    {V : X.Opens} (e : V ≤ s ⁻¹ᵁ U) (e' : V ≤ s' ⁻¹ᵁ U) : s.resLE U V e = s'.resLE U V e' := by
  subst hs
  rfl

/-- The restriction of a thickening to an open and its preimage is a thickening. -/
private theorem isThickening_resLE {X Y : Scheme.{u}} {s : X ⟶ Y} (hs : IsThickening s)
    {U : Y.Opens} {W : X.Opens} (h : s ⁻¹ᵁ U = W) (e : W ≤ s ⁻¹ᵁ U) :
    IsThickening (s.resLE U W e) := by
  subst h
  have key := hs.morphismRestrict U
  rwa [← Scheme.Hom.resLE_eq_morphismRestrict] at key

/-- The square cutting an open out of the target of a morphism and its preimage out of the
source is cartesian. -/
private theorem isPullback_resLE {X Y : Scheme.{u}} (s : X ⟶ Y) {U : Y.Opens} {W : X.Opens}
    (h : s ⁻¹ᵁ U = W) (e : W ≤ s ⁻¹ᵁ U) : IsPullback (s.resLE U W e) W.ι U.ι s := by
  subst h
  have key := isPullback_morphismRestrict s U
  rwa [← Scheme.Hom.resLE_eq_morphismRestrict] at key

/-! ### The transported open -/

/-- The thickening from the least stage to the stage `i`. -/
def stageBase (i : Λ) :
    (BigFppfOver.toScheme B S hS).obj (D.obj o) ⟶
      (BigFppfOver.toScheme B S hS).obj (D.obj i) :=
  (BigFppfOver.toScheme B S hS).map (D.map (homOfLE (ho i)))

include hD in
/-- The morphism from the least stage to the stage `i` is a thickening. -/
theorem isThickening_stageBase (i : Λ) : IsThickening (stageBase B S hS D o ho i) :=
  hD _

include hD in
/-- The open of the stage `D i` matching an open `V` of the least stage `D o` under the order
isomorphism of lattices of opens induced by the thickening between them. -/
def transportedOpen (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) (i : Λ) :
    ((BigFppfOver.toScheme B S hS).obj (D.obj i)).Opens :=
  (isThickening_stageBase B S hS D hD o ho i).opensCongr V

/-- The preimage of the transported open along the thickening from the least stage is `V`. -/
theorem preimage_stageBase_transportedOpen
    (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) (i : Λ) :
    stageBase B S hS D o ho i ⁻¹ᵁ transportedOpen B S hS D hD o ho V i = V :=
  (isThickening_stageBase B S hS D hD o ho i).preimage_opensCongr V

include hD in
/-- Taking preimages along the thickening out of the least stage is injective on opens: it is
the inverse of the order isomorphism `Stacks.Thickenings.IsThickening.opensCongr`. -/
theorem preimage_stageBase_injective (i : Λ) :
    Function.Injective
      (fun U : ((BigFppfOver.toScheme B S hS).obj (D.obj i)).Opens ↦
        stageBase B S hS D o ho i ⁻¹ᵁ U) := by
  intro U U' h
  rw [← (isThickening_stageBase B S hS D hD o ho i).opensCongr_preimage U,
    ← (isThickening_stageBase B S hS D hD o ho i).opensCongr_preimage U']
  exact congrArg _ h

/-- **The transported opens are compatible with the transitions**: the preimage of the one at
`j` along the transition from `i` is the one at `i`. -/
theorem preimage_transportedOpen
    (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) {i j : Λ} (f : i ⟶ j) :
    (BigFppfOver.toScheme B S hS).map (D.map f) ⁻¹ᵁ
        transportedOpen B S hS D hD o ho V j = transportedOpen B S hS D hD o ho V i := by
  refine preimage_stageBase_injective B S hS D hD o ho i ?_
  have hmap : D.map (homOfLE (ho i)) ≫ D.map f = D.map (homOfLE (ho j)) := by
    rw [← D.map_comp, show (homOfLE (ho i) : o ⟶ i) ≫ f = homOfLE (ho j) from rfl]
  have hcomp : stageBase B S hS D o ho i ≫ (BigFppfOver.toScheme B S hS).map (D.map f) =
      stageBase B S hS D o ho j := by
    simp only [stageBase, ← Functor.map_comp, hmap]
  change stageBase B S hS D o ho i ⁻¹ᵁ _ = stageBase B S hS D o ho i ⁻¹ᵁ _
  rw [preimage_stageBase_transportedOpen, ← Scheme.Hom.comp_preimage, hcomp,
    preimage_stageBase_transportedOpen]

/-- The transported open is affine when `V` is: affineness of an open is detected on its
preimage under a thickening. -/
theorem isAffineOpen_transportedOpen
    {V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens} (hV : IsAffineOpen V) (i : Λ) :
    IsAffineOpen (transportedOpen B S hS D hD o ho V i) := by
  refine (isAffineOpen_iff_isAffineOpen_preimage
    (isThickening_stageBase B S hS D hD o ho i) _).mpr ?_
  rw [preimage_stageBase_transportedOpen]
  exact hV

/-- **The transports of a covering family of opens of the least stage cover every stage.** The
order isomorphism of lattices of opens carries a supremum to a supremum, and `⊤` to `⊤`. -/
theorem iSup_transportedOpen_eq_top {ι : Type*}
    (V : ι → ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) (hV : iSup V = ⊤) (i : Λ) :
    (⨆ k, transportedOpen B S hS D hD o ho (V k) i) = ⊤ := by
  change (⨆ k, (isThickening_stageBase B S hS D hD o ho i).opensCongr (V k)) = ⊤
  rw [← (isThickening_stageBase B S hS D hD o ho i).opensCongr.map_iSup V, hV]
  exact (isThickening_stageBase B S hS D hD o ho i).opensCongr.map_top

/-! ### The transported opens as a diagram in the site -/

include hD in
/-- The site contains the transported open: an open immersion does not raise the size of a
scheme. -/
theorem contains_transportedOpen (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens)
    (i : Λ) :
    B.Contains (transportedOpen B S hS D hD o ho V i).toScheme :=
  Scheme.size_lt_of_isOpenImmersion (transportedOpen B S hS D hD o ho V i).ι
    (D.obj i).left.property

include hD in
/-- The transported open of the stage `D i`, as an object of the big fppf site over `S`: its
structure morphism is the inclusion into the stage followed by the stage's own. -/
@[implicit_reducible]
def transportedOpenObj (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) (i : Λ) :
    BigFppfOver B S hS :=
  Over.mk ((ObjectProperty.homMk (transportedOpen B S hS D hD o ho V i).ι :
    B.obj (contains_transportedOpen B S hS D hD o ho V i) ⟶ (D.obj i).left) ≫ (D.obj i).hom)

/-- The structure morphism of `transportedOpenObj` is the inclusion of the transported open
followed by the structure morphism of the stage. -/
theorem transportedOpenObj_hom (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens)
    (i : Λ) :
    (transportedOpenObj B S hS D hD o ho V i).hom =
      ObjectProperty.homMk (transportedOpen B S hS D hD o ho V i).ι ≫ (D.obj i).hom :=
  rfl

include hD in
/-- The inclusion of the transported open into its stage, as a morphism of the site. -/
def transportedOpenι (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) (i : Λ) :
    transportedOpenObj B S hS D hD o ho V i ⟶ D.obj i :=
  Over.homMk (ObjectProperty.homMk (transportedOpen B S hS D hD o ho V i).ι) rfl

/-- The underlying morphism of schemes of `transportedOpenι` is the inclusion of the open. -/
@[simp]
theorem toScheme_map_transportedOpenι
    (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) (i : Λ) :
    (BigFppfOver.toScheme B S hS).map (transportedOpenι B S hS D hD o ho V i) =
      (transportedOpen B S hS D hD o ho V i).ι :=
  rfl

include hD in
/-- The transition of the diagram of transported opens: the restriction of the transition of `D`,
which lands in the transported open of the later stage because its preimage is the transported
open of the earlier one. -/
def transportedOpenMap (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) {i j : Λ}
    (f : i ⟶ j) :
    transportedOpenObj B S hS D hD o ho V i ⟶ transportedOpenObj B S hS D hD o ho V j :=
  Over.homMk (ObjectProperty.homMk
      (((BigFppfOver.toScheme B S hS).map (D.map f)).resLE
        (transportedOpen B S hS D hD o ho V j) (transportedOpen B S hS D hD o ho V i)
        (le_of_eq (preimage_transportedOpen B S hS D hD o ho V f).symm))) (by
    refine ObjectProperty.hom_ext _ ?_
    have hw : (BigFppfOver.toScheme B S hS).map (D.map f) ≫
        B.inclusion.map (D.obj j).hom = B.inclusion.map (D.obj i).hom := by
      have h := B.inclusion.congr_map (Over.w (D.map f))
      rwa [Functor.map_comp] at h
    change ((BigFppfOver.toScheme B S hS).map (D.map f)).resLE
        (transportedOpen B S hS D hD o ho V j) (transportedOpen B S hS D hD o ho V i) _ ≫
        (transportedOpen B S hS D hD o ho V j).ι ≫ B.inclusion.map (D.obj j).hom =
      (transportedOpen B S hS D hD o ho V i).ι ≫ B.inclusion.map (D.obj i).hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hw])

/-- The underlying morphism of schemes of `transportedOpenMap` is the restriction of the
transition of `D` to the transported opens. -/
@[simp]
theorem toScheme_map_transportedOpenMap
    (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) {i j : Λ} (f : i ⟶ j) :
    (BigFppfOver.toScheme B S hS).map (transportedOpenMap B S hS D hD o ho V f) =
      ((BigFppfOver.toScheme B S hS).map (D.map f)).resLE
        (transportedOpen B S hS D hD o ho V j) (transportedOpen B S hS D hD o ho V i)
        (le_of_eq (preimage_transportedOpen B S hS D hD o ho V f).symm) :=
  rfl

include hD in
/-- **The transported opens of the stages, as a diagram in the big fppf site over `S`.** Its
functoriality is that of `AlgebraicGeometry.Scheme.Hom.resLE`. -/
def transportedOpenDiagram (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) :
    Λ ⥤ BigFppfOver B S hS where
  obj := transportedOpenObj B S hS D hD o ho V
  map f := transportedOpenMap B S hS D hD o ho V f
  map_id i := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [toScheme_map_transportedOpenMap, (BigFppfOver.toScheme B S hS).map_id]
    exact resLE_eq_id (by rw [D.map_id, (BigFppfOver.toScheme B S hS).map_id]) _
  map_comp f g := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [(BigFppfOver.toScheme B S hS).map_comp, toScheme_map_transportedOpenMap,
      toScheme_map_transportedOpenMap, toScheme_map_transportedOpenMap,
      Scheme.Hom.resLE_comp_resLE]
    exact resLE_congr_hom
      (by rw [D.map_comp, (BigFppfOver.toScheme B S hS).map_comp]) _ _

/-- The stage `i` of `transportedOpenDiagram` is `transportedOpenObj` at `i`. -/
@[simp]
theorem transportedOpenDiagram_obj (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens)
    (i : Λ) :
    (transportedOpenDiagram B S hS D hD o ho V).obj i = transportedOpenObj B S hS D hD o ho V i :=
  rfl

/-- The transition of `transportedOpenDiagram` along `f` is `transportedOpenMap` along `f`. -/
@[simp]
theorem transportedOpenDiagram_map (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens)
    {i j : Λ} (f : i ⟶ j) :
    (transportedOpenDiagram B S hS D hD o ho V).map f =
      transportedOpenMap B S hS D hD o ho V f :=
  rfl

include hD in
/-- **The open immersion of the diagram of transported opens into the diagram of stages.** -/
def transportedOpenInclusion (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) :
    transportedOpenDiagram B S hS D hD o ho V ⟶ D where
  app i := transportedOpenι B S hS D hD o ho V i
  naturality i j f := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    exact Scheme.Hom.resLE_comp_ι
      (f := (BigFppfOver.toScheme B S hS).map (D.map f))
      (U := transportedOpen B S hS D hD o ho V j)
      (V := transportedOpen B S hS D hD o ho V i)
      (e := le_of_eq (preimage_transportedOpen B S hS D hD o ho V f).symm)

/-- The component of `transportedOpenInclusion` at `i` is `transportedOpenι` at `i`. -/
@[simp]
theorem transportedOpenInclusion_app
    (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) (i : Λ) :
    (transportedOpenInclusion B S hS D hD o ho V).app i = transportedOpenι B S hS D hD o ho V i :=
  rfl

include hD in
/-- The components of the inclusion are open immersions. -/
theorem isOpenImmersion_transportedOpenι
    (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) (i : Λ) :
    IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (transportedOpenι B S hS D hD o ho V i)) := by
  change IsOpenImmersion (transportedOpen B S hS D hD o ho V i).ι
  infer_instance

include hD in
/-- **The transitions of the diagram of transported opens are thickenings**: a thickening
restricts to a thickening over any open of its target. -/
theorem isThickening_transportedOpenDiagram_map
    (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) {i j : Λ} (f : i ⟶ j) :
    IsThickening ((BigFppfOver.toScheme B S hS).map
      ((transportedOpenDiagram B S hS D hD o ho V).map f)) := by
  exact isThickening_resLE (hD f) (preimage_transportedOpen B S hS D hD o ho V f) _

include hD in
/-- The stages of the diagram of transported opens are affine when `V` is an affine open. -/
theorem isAffine_transportedOpenDiagram_obj
    {V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens} (hV : IsAffineOpen V) (i : Λ) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((transportedOpenDiagram B S hS D hD o ho V).obj i)) :=
  isAffineOpen_transportedOpen B S hS D hD o ho hV i

include hD in
/-- **Each square of the diagram of transported opens over the diagram of stages is
cartesian**, in the site: the transported open of the earlier stage is the preimage of the
transported open of the later one. -/
theorem isPullback_transportedOpenInclusion
    (V : ((BigFppfOver.toScheme B S hS).obj (D.obj o)).Opens) {i j : Λ} (f : i ⟶ j) :
    IsPullback ((transportedOpenDiagram B S hS D hD o ho V).map f)
      (transportedOpenι B S hS D hD o ho V i) (transportedOpenι B S hS D hD o ho V j)
      (D.map f) := by
  have _ : ReflectsLimit
      (cospan (transportedOpenι B S hS D hD o ho V j) (D.map f))
      (BigFppfOver.toScheme B S hS) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (isPullback_resLE _ (preimage_transportedOpen B S hS D hD o ho V f) _)

end AlgebraicGeometry.FormalSpace

end
