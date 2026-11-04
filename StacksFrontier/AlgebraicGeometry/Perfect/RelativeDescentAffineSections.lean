module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineOpen
public import StacksFrontier.Homology.RelativelyPerfect.Colimit

/-!
# The ring-level system of the affine case of Stacks 0DI7

Let `V₀` be an affine open of `X₀` contained in the preimage of an affine open `W₀ ⊆ S₀`, the
situation of `AlgebraicGeometry.RelativeDescentSituation.IsAffineOpenOverAffine`. Writing
`Rᵢ = Γ(g_i^{-1}(W₀))`, `R₀ = Γ(W₀)`, `A₀ = Γ(V₀)` and `R = Γ(g^{-1}(W₀))`, this file identifies
the part of the relative descent situation of Stacks 0DI6 lying over `V₀` with the ring-level
system that Stacks 0DHX consumes:

* `g_i^{-1}(W₀)` and `g^{-1}(W₀)` are affine opens, since the transition morphisms `Sᵢ ⟶ S₀` and
  the projections `S ⟶ Sᵢ` are affine;
* `R = colim_i Rᵢ`, because `g^{-1}(W₀) = lim_i g_i^{-1}(W₀)` is a cofiltered limit of affines;
* `Vᵢ = g_i^{-1}(W₀) ×_{W₀} V₀`, hence `Γ(Vᵢ) = Rᵢ ⊗_{R₀} A₀`, naturally in `i`;
* `R₀ ⟶ A₀` is flat of finite presentation, because `X₀ ⟶ S₀` is.

## Main definitions

* `AlgebraicGeometry.RelativeDescentSituation.stageOpFunctor` and `sectionsDiagram`: the stages
  `Xᵢ` of a relative descent situation as a diagram in `Schemeᵒᵖ` indexed by the stages at or
  beyond the fixed one, and the diagram of their rings of global sections;
  `stageOpCocone` and `sectionsCocone` are the cocones on them given by the limit `X`.
* `AlgebraicGeometry.RelativeDescentSituation.laterIndexEquivOver`: the stages at or beyond the
  fixed one, as a category, are the opposite of the slice of the index category over the fixed
  index.
* `AlgebraicGeometry.RelativeDescentSituation.basePreimageOpFunctor`, `baseRingDiagram` and
  `baseRingUnit`: the diagram `i ↦ g_i^{-1}(W₀)`, the diagram `i ↦ Rᵢ` of its rings of global
  sections, and the maps `R₀ ⟶ Rᵢ`.
* `AlgebraicGeometry.RelativeDescentSituation.baseRingCocone`: the cocone on `i ↦ Rᵢ` with vertex
  `R`.
* `AlgebraicGeometry.RelativeDescentSituation.baseRingAlgDiagram` and `baseRingAlgCocone`: the
  same system read in the category of `R₀`-algebras, which is the shape in which Stacks 0DHX
  takes it.
* `AlgebraicGeometry.RelativeDescentSituation.restrictToBasePreimage` and
  `restrictToBasePreimageLimit`: the morphisms `Vᵢ ⟶ g_i^{-1}(W₀)` and `V ⟶ g^{-1}(W₀)`.
* `AlgebraicGeometry.RelativeDescentSituation.basePreimageToStage`, `baseRingToSections` and
  `fixedRingToSections`: the morphism of diagrams `g_i^{-1}(W₀) ⟵ Vᵢ`, the induced morphism
  `Rᵢ ⟶ Γ(Vᵢ)` of diagrams of rings, and the maps `A₀ ⟶ Γ(Vᵢ)`.
* `AlgebraicGeometry.RelativeDescentSituation.tensorProductIsoSections` and
  `stageAlgebraIsoSections`: the isomorphism `Rᵢ ⊗_{R₀} A₀ ≅ Γ(Vᵢ)`, the second written in the
  vocabulary of `PseudoCoherence.stageAlgebra`, which is how Stacks 0DHX names the
  stage algebras of the system it consumes.

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.isAffineOpen_preimage_baseMap` and
  `isAffineOpen_preimage_baseProjection`: `g_i^{-1}(W₀)` and `g^{-1}(W₀)` are affine opens.
* `AlgebraicGeometry.RelativeDescentSituation.isColimitBaseRingCocone`,
  `isColimitBaseRingUnderCocone` and `isColimitBaseRingAlgCocone`: **`R = colim_i Rᵢ`**, as rings,
  as rings under `R₀` and as `R₀`-algebras.
* `AlgebraicGeometry.RelativeDescentSituation.isPullback_restrictToBasePreimage` and
  `isPullback_restrictToBasePreimageLimit`: **`Vᵢ = g_i^{-1}(W₀) ×_{W₀} V₀`** and
  **`V = g^{-1}(W₀) ×_{W₀} V₀`.**
* `AlgebraicGeometry.RelativeDescentSituation.isPushout_appTop_restrictToBasePreimage` and
  `isPushout_appTop_restrictToBasePreimageLimit`: **`Γ(Vᵢ) = Rᵢ ⊗_{R₀} A₀`** and
  **`Γ(V) = R ⊗_{R₀} A₀`** as pushouts of rings, hence as `Rᵢ`- and `R`-algebras and as
  `A₀`-algebras.
* `AlgebraicGeometry.RelativeDescentSituation.baseRingToSections_comp_sectionsCocone` and
  `fixedRingToSections_comp_sectionsCocone`: the identification over the limit is compatible with
  the cocone legs `Rᵢ ⟶ R` and `Γ(Vᵢ) ⟶ Γ(V)` from the stages, and the two share their
  `A₀`-leg.
* `AlgebraicGeometry.RelativeDescentSituation.ringHomFlat_appTop_resLE` and
  `ringHomFinitePresentation_appTop_resLE`: **`R₀ ⟶ A₀` is flat of finite presentation**;
  `moduleFlat_appTop_resLE` and `algebraFinitePresentation_appTop_resLE` are the same as
  statements about the algebra structure `A₀` carries over `R₀`.
* `AlgebraicGeometry.RelativeDescentSituation.algebraIsPushout_sections`: the same pushout square
  as `Algebra.IsPushout R₀ Rᵢ A₀ Γ(Vᵢ)`.
* `AlgebraicGeometry.RelativeDescentSituation.isFiltered_laterIndex`: the index category of all
  these diagrams is filtered.

## Implementation notes

The index category of the inverse system of a relative descent situation is `Iᵒᵖ` for a directed
preorder `I`, while the limit of the preimages of an open of the fixed stage is taken over the
slice `CategoryTheory.Over (op D.descent.base)`
(`AlgebraicGeometry.EventualLimit.isLimitPreimageCone`). The two agree: a map `op j ⟶ op i₀` in
`Iᵒᵖ` is a relation `i₀ ≤ j`, so the slice is the opposite of the stages at or beyond the fixed
one. `laterIndexEquivOver` is that identification, obtained from fullness, faithfulness and
essential surjectivity rather than by comparing objects, because the structure morphism of a
slice object and the one built from the corresponding relation agree only propositionally. Every
diagram below is indexed by `D.LaterIndex`, which is the index of
`AlgebraicGeometry.RelativeDescentSituation.homFunctor`, and the colimit statement is transported
along the equivalence.

`Γ(Vᵢ) = Rᵢ ⊗_{R₀} A₀` is stated as a pushout square of rings rather than as an isomorphism onto
a tensor product: that form is symmetric in the two factors, carries the two structure maps with
it, and is what `AlgebraicGeometry.isPushout_appTop_of_isPullback` produces from the Cartesian
square `Vᵢ = g_i^{-1}(W₀) ×_{W₀} V₀`. The literal tensor product is `tensorProductIsoSections`,
read off from `CommRingCat.isPushout_tensorProduct`, and `Algebra.IsPushout` is
`algebraIsPushout_sections`, read off from `CommRingCat.isPushout_iff_isPushout`.

The `R₀`-algebra structures appearing in those three statements are the ones the maps of the
pushout square carry, installed by `RingHom.toAlgebra`; `stageAlgebraIsoSections` needs no
transport because the algebra structure that `CommAlgCat.commAlgCatEquivUnder` puts on
`(baseRingAlgDiagram W₀).obj i` is `RingHom.toAlgebra` of that same map. No universe is
identified: the index lives in `Type v` and the rings in `Type u` throughout, exactly as in
`PseudoCoherence.stageAlgebra`, whose index and ring universes are independent.

`basePreimageOpFunctor` is written out rather than obtained by reindexing
`AlgebraicGeometry.EventualLimit.preimageDiagram` along `laterIndexToOver`, although the two are
definitionally equal and `baseRingCocone` is the reindexed limit cone of the latter: with the
explicit diagram the object at `i` is the open subscheme `g_i^{-1}(W₀)` and the morphism at
`i ≤ j` is a `Scheme.Hom.resLE`, so every comparison below is a rewrite in the ordinary way.
Those comparisons all go through the open immersions `g_i^{-1}(W₀) ⟶ Sᵢ` and `W₀ ⟶ S₀`, which are
monomorphisms, so an identity between morphisms into `g_i^{-1}(W₀)` or into `W₀` is checked after
composing with them.

## References

* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

universe v u

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{v, u} I)

attribute [local implicit_reducible] restrict

/-! ### The stages as a diagram -/

/-- The stages `Xᵢ` at or beyond the fixed stage, as a diagram in `Schemeᵒᵖ`: the transition
morphisms `Xⱼ ⟶ Xᵢ` for `i ≤ j` go the other way. -/
def stageOpFunctor : D.LaterIndex ⥤ Scheme.{u}ᵒᵖ where
  obj i := op (D.schemeAt i)
  map h := (D.transition (leOfHom h)).op
  map_id i := Quiver.Hom.unop_inj (D.transition_refl i)
  map_comp h h' := Quiver.Hom.unop_inj (D.transition_comp_transition (leOfHom h) (leOfHom h')).symm

/-- The rings of global sections `Γ(Xᵢ)` of the stages at or beyond the fixed stage, as a
diagram of commutative rings. -/
def sectionsDiagram : D.LaterIndex ⥤ CommRingCat.{u} :=
  D.stageOpFunctor ⋙ Scheme.Γ

/-- The transition morphism `Xⱼ ⟶ Xᵢ` is a morphism over `Sᵢ` up to the transition morphism
`Sⱼ ⟶ Sᵢ` of the inverse system. -/
theorem transition_comp_snd {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.transition h ≫ pullback.snd D.X₀.hom (D.baseMap i) =
      pullback.snd D.X₀.hom (D.baseMap j) ≫ D.descent.system.map (homOfLE h).op :=
  pullback.lift_snd _ _ _

/-- The projection `X ⟶ Xᵢ` from the limit is a morphism over `Sᵢ` up to the projection
`S ⟶ Sᵢ` of the inverse system. -/
theorem projection_comp_snd (i : D.LaterIndex) :
    D.projection i ≫ pullback.snd D.X₀.hom (D.baseMap i) =
      pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)) ≫
        D.descent.limitCone.π.app (op i.1) :=
  pullback.lift_snd _ _ _

/-- The projections `X ⟶ Xᵢ` exhibit the limit `X` as a cocone on the diagram of stages read in
`Schemeᵒᵖ`. -/
def stageOpCocone : Cocone D.stageOpFunctor where
  pt := op D.limitScheme
  ι :=
  { app i := (D.projection i).op
    naturality _ _ h := Quiver.Hom.unop_inj
      ((D.projection_comp_transition (leOfHom h)).trans (Category.id_comp _).symm) }

/-- The restriction maps `Γ(Xᵢ) ⟶ Γ(X)`, as a cocone on the diagram `i ↦ Γ(Xᵢ)`. -/
def sectionsCocone : Cocone D.sectionsDiagram :=
  Scheme.Γ.mapCocone D.stageOpCocone

/-- The transition morphisms of the inverse system compose to the transition morphism to the
fixed stage. -/
theorem baseMap_comp_eq {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.descent.system.map (homOfLE h).op ≫ D.baseMap i = D.baseMap j := by
  rw [← Functor.map_comp]
  exact congrArg _ (Subsingleton.elim _ _)

/-! ### The later stages as the slice over the fixed index -/

/-- The stages at or beyond the fixed stage, viewed in the opposite of the slice of the index
category over the fixed index: a stage `i` becomes the object `op i ⟶ op i₀` of the slice given
by `i₀ ≤ i`. -/
def laterIndexToOver : D.LaterIndex ⥤ (Over (op D.descent.base))ᵒᵖ where
  obj i := op (Over.mk (homOfLE i.2).op)
  map h := op (Over.homMk (homOfLE (leOfHom h)).op (Subsingleton.elim _ _))
  map_id _ := Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))
  map_comp _ _ := Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))

/-- The functor `laterIndexToOver` is faithful. -/
instance : (D.laterIndexToOver).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- The functor `laterIndexToOver` is full. -/
instance : (D.laterIndexToOver).Full where
  map_surjective f := ⟨homOfLE (leOfHom f.unop.left.unop),
    Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))⟩

/-- The functor `laterIndexToOver` is essentially surjective. -/
instance : (D.laterIndexToOver).EssSurj where
  mem_essImage b :=
    ⟨⟨b.unop.left.unop, leOfHom b.unop.hom.unop⟩,
      ⟨(Iso.op (Over.isoMk (Iso.refl _) (Subsingleton.elim _ _))).symm⟩⟩

/-- The functor `laterIndexToOver` is an equivalence of categories. -/
instance : (D.laterIndexToOver).IsEquivalence where

/-- **The stages at or beyond the fixed stage are the opposite of the slice of the index category
over the fixed index.** -/
def laterIndexEquivOver : D.LaterIndex ≌ (Over (op D.descent.base))ᵒᵖ :=
  D.laterIndexToOver.asEquivalence

/-- The stages at or beyond the fixed stage form a filtered category, being a nonempty directed
preorder. -/
theorem isFiltered_laterIndex : IsFiltered D.LaterIndex :=
  have := D.nonempty_laterIndex
  have := D.isDirected_laterIndex
  inferInstance

/-! ### The affine opens of the inverse system over an affine open of the fixed base -/

variable (W₀ : (D.descent.system.obj (op D.descent.base)).Opens)

/-- **The preimage `g_i^{-1}(W₀)` of an affine open of `S₀` in a stage `Sᵢ` is an affine open**,
the transition morphisms of the inverse system being affine. -/
theorem isAffineOpen_preimage_baseMap (hW₀ : IsAffineOpen W₀) (i : D.LaterIndex) :
    IsAffineOpen (D.baseMap i ⁻¹ᵁ W₀) :=
  have := D.isAffineHom_baseMap i
  hW₀.preimage (D.baseMap i)

/-- **The preimage `g^{-1}(W₀)` of an affine open of `S₀` in the limit `S` is an affine open**,
the projections from the limit being affine. This is Stacks 01YX. -/
theorem isAffineOpen_preimage_baseProjection (hW₀ : IsAffineOpen W₀) :
    IsAffineOpen (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀) :=
  have := D.isAffineHom_baseProjection ⟨D.descent.base, le_refl _⟩
  hW₀.preimage _

/-! ### The system of rings `Rᵢ` and its colimit -/

/-- The transition morphism `g_j^{-1}(W₀) ⟶ g_i^{-1}(W₀)` between the preimages of `W₀`, the
restriction of the transition morphism `Sⱼ ⟶ Sᵢ` of the inverse system. -/
def basePreimageTransition {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    (D.baseMap j ⁻¹ᵁ W₀ : _).toScheme ⟶ (D.baseMap i ⁻¹ᵁ W₀ : _).toScheme :=
  (D.descent.system.map (homOfLE h).op).resLE (D.baseMap i ⁻¹ᵁ W₀) (D.baseMap j ⁻¹ᵁ W₀)
    (le_of_eq (by rw [← Scheme.Hom.comp_preimage, D.baseMap_comp_eq h]))

/-- The transition morphism `g_j^{-1}(W₀) ⟶ g_i^{-1}(W₀)` is the restriction of `Sⱼ ⟶ Sᵢ`. -/
theorem basePreimageTransition_comp_ι {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.basePreimageTransition W₀ h ≫ (D.baseMap i ⁻¹ᵁ W₀).ι =
      (D.baseMap j ⁻¹ᵁ W₀).ι ≫ D.descent.system.map (homOfLE h).op :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The transition morphism of the preimages from a stage to itself is the identity. -/
theorem basePreimageTransition_refl (i : D.LaterIndex) :
    D.basePreimageTransition W₀ (le_refl i.1) = 𝟙 _ :=
  (cancel_mono (D.baseMap i ⁻¹ᵁ W₀).ι).mp <| by
    rw [D.basePreimageTransition_comp_ι W₀ (le_refl i.1),
      Subsingleton.elim (homOfLE (le_refl i.1)).op (𝟙 (op i.1)), D.descent.system.map_id,
      Category.comp_id, Category.id_comp]

/-- The transition morphisms of the preimages compose. -/
theorem basePreimageTransition_comp {i j k : D.LaterIndex} (hij : i.1 ≤ j.1) (hjk : j.1 ≤ k.1) :
    D.basePreimageTransition W₀ hjk ≫ D.basePreimageTransition W₀ hij =
      D.basePreimageTransition W₀ (hij.trans hjk) :=
  (cancel_mono (D.baseMap i ⁻¹ᵁ W₀).ι).mp <| by
    rw [Category.assoc, D.basePreimageTransition_comp_ι W₀ hij, ← Category.assoc,
      D.basePreimageTransition_comp_ι W₀ hjk, Category.assoc, ← Functor.map_comp,
      D.basePreimageTransition_comp_ι W₀ (hij.trans hjk)]
    exact congrArg (fun m => (D.baseMap k ⁻¹ᵁ W₀).ι ≫ D.descent.system.map m)
      (Subsingleton.elim _ _)

/-- A morphism of preimages of `W` lying over the morphism `t : X ⟶ Y` over `Z` lies over `W`. -/
private theorem comp_morphismRestrict_of_comp_ι {X Y Z : Scheme.{u}} {W : Z.Opens} (b : Y ⟶ Z)
    (c : X ⟶ Z) (t : X ⟶ Y) (ht : t ≫ b = c) (x : (c ⁻¹ᵁ W).toScheme ⟶ (b ⁻¹ᵁ W).toScheme)
    (hx : x ≫ (b ⁻¹ᵁ W).ι = (c ⁻¹ᵁ W).ι ≫ t) : x ≫ (b ∣_ W) = c ∣_ W :=
  (cancel_mono W.ι).mp <| by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hx, Category.assoc, ht,
      morphismRestrict_ι]

/-- The transition morphisms of the preimages of `W₀` lie over `W₀`. -/
theorem basePreimageTransition_comp_morphismRestrict {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.basePreimageTransition W₀ h ≫ (D.baseMap i ∣_ W₀) = D.baseMap j ∣_ W₀ :=
  comp_morphismRestrict_of_comp_ι _ _ _ (D.baseMap_comp_eq h) _
    (D.basePreimageTransition_comp_ι W₀ h)

/-- The preimages `g_i^{-1}(W₀)` of an open of the fixed base, as a diagram in `Schemeᵒᵖ`. -/
def basePreimageOpFunctor : D.LaterIndex ⥤ Scheme.{u}ᵒᵖ where
  obj i := op (D.baseMap i ⁻¹ᵁ W₀ : _).toScheme
  map h := (D.basePreimageTransition W₀ (leOfHom h)).op
  map_id i := Quiver.Hom.unop_inj (D.basePreimageTransition_refl W₀ i)
  map_comp h h' :=
    Quiver.Hom.unop_inj (D.basePreimageTransition_comp W₀ (leOfHom h) (leOfHom h')).symm

/-- The structure morphisms `g_i^{-1}(W₀) ⟶ W₀`, as a morphism of diagrams out of the constant
diagram `W₀`. -/
def baseUnit : (Functor.const D.LaterIndex).obj (op W₀.toScheme) ⟶ D.basePreimageOpFunctor W₀ where
  app i := (D.baseMap i ∣_ W₀).op
  naturality _ _ h := by
    apply Quiver.Hom.unop_inj
    simp only [Functor.const_obj_map]
    exact (D.basePreimageTransition_comp_morphismRestrict W₀ (leOfHom h)).symm

/-- The system of rings `Rᵢ = Γ(g_i^{-1}(W₀))`. -/
def baseRingDiagram : D.LaterIndex ⥤ CommRingCat.{u} :=
  D.basePreimageOpFunctor W₀ ⋙ Scheme.Γ

/-- The structure maps `R₀ ⟶ Rᵢ`, making `baseRingDiagram` a diagram of `R₀`-algebras. -/
def baseRingUnit :
    (Functor.const D.LaterIndex).obj Γ(W₀.toScheme, ⊤) ⟶ D.baseRingDiagram W₀ where
  app i := (D.baseMap i ∣_ W₀).appTop
  naturality _ _ h := by
    simp only [Functor.const_obj_map]
    exact congrArg Scheme.Hom.appTop
      (D.basePreimageTransition_comp_morphismRestrict W₀ (leOfHom h)).symm

/-- The projection `g^{-1}(W₀) ⟶ g_i^{-1}(W₀)` between the preimages of `W₀`, the restriction of
the projection `S ⟶ Sᵢ` from the limit. -/
def baseProjectionPreimage (i : D.LaterIndex) :
    (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme ⟶
      (D.baseMap i ⁻¹ᵁ W₀ : _).toScheme :=
  (D.descent.limitCone.π.app (op i.1)).resLE (D.baseMap i ⁻¹ᵁ W₀)
    (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀)
    (le_of_eq (by rw [← Scheme.Hom.comp_preimage, D.descent.limitCone.w (homOfLE i.2).op]))

/-- The projection `g^{-1}(W₀) ⟶ g_i^{-1}(W₀)` is the restriction of `S ⟶ Sᵢ`. -/
theorem baseProjectionPreimage_comp_ι (i : D.LaterIndex) :
    D.baseProjectionPreimage W₀ i ≫ (D.baseMap i ⁻¹ᵁ W₀).ι =
      (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀).ι ≫
        D.descent.limitCone.π.app (op i.1) :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The projections `g^{-1}(W₀) ⟶ g_i^{-1}(W₀)` lie over `W₀`. -/
theorem baseProjectionPreimage_comp_morphismRestrict (i : D.LaterIndex) :
    D.baseProjectionPreimage W₀ i ≫ (D.baseMap i ∣_ W₀) =
      D.descent.limitCone.π.app (op D.descent.base) ∣_ W₀ :=
  comp_morphismRestrict_of_comp_ι _ _ _ (D.descent.limitCone.w (homOfLE i.2).op) _
    (D.baseProjectionPreimage_comp_ι W₀ i)

/-- The cocone on `i ↦ Rᵢ` with vertex `R = Γ(g^{-1}(W₀))`. -/
def baseRingCocone : Cocone (D.baseRingDiagram W₀) :=
  (Scheme.Γ.mapCocone
    (EventualLimit.preimageCone D.descent.system D.descent.limitCone
      (op D.descent.base) W₀).op).whisker D.laterIndexToOver

/-- **`R = colim_i Rᵢ`.** The preimage of `W₀` in the limit is the limit of the preimages of `W₀`
in the stages, those are affine, and `Γ` turns a limit of affine schemes into a colimit of
rings. -/
def isColimitBaseRingCocone (hW₀ : IsAffineOpen W₀) : IsColimit (D.baseRingCocone W₀) :=
  have : Nonempty I := ⟨D.descent.base⟩
  have : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.descent.system.map g) :=
    fun g => D.descent.transition_affine g
  have : ∀ k : (Over (op D.descent.base))ᵒᵖ,
      IsAffine (((EventualLimit.preimageDiagram D.descent.system (op D.descent.base) W₀).op.obj
        k).unop) := fun k =>
    EventualLimit.isAffine_preimageDiagram_obj D.descent.system (op D.descent.base) hW₀ k.unop
  (isColimitOfPreserves Scheme.Γ
    (EventualLimit.isLimitPreimageCone D.descent.system D.descent.limitCone D.descent.isLimit
      (op D.descent.base) W₀).op).whiskerEquivalence D.laterIndexEquivOver

/-- The map `R₀ ⟶ R` structuring `R` as an `R₀`-algebra. -/
def baseRingLimitUnit : Γ(W₀.toScheme, ⊤) ⟶ (D.baseRingCocone W₀).pt :=
  (D.descent.limitCone.π.app (op D.descent.base) ∣_ W₀).appTop

/-- The structure maps `R₀ ⟶ Rᵢ ⟶ R` all agree with `R₀ ⟶ R`. -/
theorem baseRingUnit_comp_baseRingCocone_ι (i : D.LaterIndex) :
    (D.baseRingUnit W₀).app i ≫ (D.baseRingCocone W₀).ι.app i = D.baseRingLimitUnit W₀ :=
  congrArg Scheme.Hom.appTop (D.baseProjectionPreimage_comp_morphismRestrict W₀ i)

/-! ### The system of rings as a diagram of `R₀`-algebras -/

/-- The system `i ↦ Rᵢ` as a diagram of rings under `R₀`. -/
def baseRingUnder : D.LaterIndex ⥤ Under Γ(W₀.toScheme, ⊤) where
  obj i := Under.mk ((D.baseRingUnit W₀).app i)
  map h := Under.homMk ((D.baseRingDiagram W₀).map h)
    (by simpa using ((D.baseRingUnit W₀).naturality h).symm)
  map_id i := Under.UnderMorphism.ext ((D.baseRingDiagram W₀).map_id i)
  map_comp h h' := Under.UnderMorphism.ext ((D.baseRingDiagram W₀).map_comp h h')

/-- The cocone on `i ↦ Rᵢ` with vertex `R`, as rings under `R₀`. -/
def baseRingUnderCocone : Cocone (D.baseRingUnder W₀) where
  pt := Under.mk (D.baseRingLimitUnit W₀)
  ι :=
  { app i := Under.homMk ((D.baseRingCocone W₀).ι.app i)
      (D.baseRingUnit_comp_baseRingCocone_ι W₀ i)
    naturality _ _ h := Under.UnderMorphism.ext
      (((D.baseRingCocone W₀).w h).trans (Category.comp_id _).symm) }

/-- A map out of `R` is determined on `R₀` by any one stage. -/
theorem baseRingLimitUnit_comp_desc (hW₀ : IsAffineOpen W₀) (s : Cocone (D.baseRingDiagram W₀))
    (t : Γ(W₀.toScheme, ⊤) ⟶ s.pt)
    (ht : ∀ i : D.LaterIndex, (D.baseRingUnit W₀).app i ≫ s.ι.app i = t) :
    D.baseRingLimitUnit W₀ ≫ (D.isColimitBaseRingCocone W₀ hW₀).desc s = t := by
  obtain ⟨i₀⟩ := D.nonempty_laterIndex
  rw [← D.baseRingUnit_comp_baseRingCocone_ι W₀ i₀, Category.assoc,
    (D.isColimitBaseRingCocone W₀ hW₀).fac s i₀, ht i₀]

/-- **`R = colim_i Rᵢ` as rings under `R₀`**: the colimit of the underlying rings is reflected,
the index category being nonempty. -/
def isColimitBaseRingUnderCocone (hW₀ : IsAffineOpen W₀) :
    IsColimit (D.baseRingUnderCocone W₀) where
  desc s := Under.homMk
    ((D.isColimitBaseRingCocone W₀ hW₀).desc
      (((Under.forget Γ(W₀.toScheme, ⊤)).mapCocone s : Cocone (D.baseRingDiagram W₀))))
    (by
      exact D.baseRingLimitUnit_comp_desc W₀ hW₀
        ((Under.forget Γ(W₀.toScheme, ⊤)).mapCocone s : Cocone (D.baseRingDiagram W₀))
        s.pt.hom fun i => Under.w (s.ι.app i))
  fac s i := Under.UnderMorphism.ext
    ((D.isColimitBaseRingCocone W₀ hW₀).fac
      ((Under.forget Γ(W₀.toScheme, ⊤)).mapCocone s : Cocone (D.baseRingDiagram W₀)) i)
  uniq s m hm := Under.UnderMorphism.ext
    ((D.isColimitBaseRingCocone W₀ hW₀).uniq
      ((Under.forget Γ(W₀.toScheme, ⊤)).mapCocone s : Cocone (D.baseRingDiagram W₀))
      m.right fun i => congrArg Under.Hom.right (hm i))

/-- The system `i ↦ Rᵢ` as a diagram of `R₀`-algebras, the shape in which Stacks 0DHX takes
it. -/
def baseRingAlgDiagram : D.LaterIndex ⥤ CommAlgCat.{u} Γ(W₀.toScheme, ⊤) :=
  D.baseRingUnder W₀ ⋙ (commAlgCatEquivUnder Γ(W₀.toScheme, ⊤)).inverse

/-- The cocone on `i ↦ Rᵢ` with vertex `R`, as `R₀`-algebras. -/
def baseRingAlgCocone : Cocone (D.baseRingAlgDiagram W₀) :=
  (commAlgCatEquivUnder Γ(W₀.toScheme, ⊤)).inverse.mapCocone
    (D.baseRingUnderCocone W₀)

/-- **`R = colim_i Rᵢ` as `R₀`-algebras.** -/
def isColimitBaseRingAlgCocone (hW₀ : IsAffineOpen W₀) :
    IsColimit (D.baseRingAlgCocone W₀) :=
  isColimitOfPreserves _ (D.isColimitBaseRingUnderCocone W₀ hW₀)

/-! ### The stages over an affine open of the fixed stage lying over `W₀` -/

variable (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀) (hVW : V₀ ≤ D.X₀.hom ⁻¹ᵁ W₀)

/-- The preimage `g_i^{-1}(W₀)` is the fibre product `Sᵢ ×_{S₀} W₀`. -/
theorem isPullback_preimage_baseMap (i : D.LaterIndex) :
    IsPullback (D.baseMap i ⁻¹ᵁ W₀).ι (D.baseMap i ∣_ W₀) (D.baseMap i) W₀.ι :=
  (isPullback_morphismRestrict (D.baseMap i) W₀).flip

/-- The lift of a pullback `Q` of `b` and `s ≫ w` to the pullback `U` of `b` and `w` is the pullback
of `s` along `r`. -/
private theorem isPullback_lift_of_isPullback {C : Type*} [Category C] {Q U V W T S : C}
    {ι : U ⟶ T} {r : U ⟶ W} {b : T ⟶ S} {w : W ⟶ S} (H : IsPullback ι r b w) {h : Q ⟶ T}
    {k : Q ⟶ V} {s : V ⟶ W} (pb : IsPullback h k b (s ≫ w)) :
    IsPullback (H.lift h (k ≫ s) (by simpa using pb.w)) k r s :=
  .of_right (by rwa [H.lift_fst]) (H.lift_snd _ _ _) H

/-- The morphism `Vᵢ ⟶ g_i^{-1}(W₀)`, induced by `Vᵢ ⟶ Sᵢ` and `Vᵢ ⟶ V₀ ⟶ W₀`. -/
def restrictToBasePreimage (i : D.LaterIndex) :
    (D.restrict V₀ hV₀.isCompact).schemeAt i ⟶ (D.baseMap i ⁻¹ᵁ W₀ : _).toScheme :=
  (D.isPullback_preimage_baseMap W₀ i).lift
    (pullback.snd (V₀.ι ≫ D.X₀.hom) (D.baseMap i))
    ((D.restrict V₀ hV₀.isCompact).toFixedStage i ≫ D.X₀.hom.resLE W₀ V₀ hVW)
    (by rw [Category.assoc, Scheme.Hom.resLE_comp_ι]; exact pullback.condition.symm)

/-- The morphism `Vᵢ ⟶ g_i^{-1}(W₀)` composed with `g_i^{-1}(W₀) ⟶ Sᵢ` is the projection
`Vᵢ ⟶ Sᵢ`. -/
theorem restrictToBasePreimage_comp_ι (i : D.LaterIndex) :
    D.restrictToBasePreimage W₀ V₀ hV₀ hVW i ≫ (D.baseMap i ⁻¹ᵁ W₀).ι =
      pullback.snd (V₀.ι ≫ D.X₀.hom) (D.baseMap i) :=
  (D.isPullback_preimage_baseMap W₀ i).lift_fst _ _ _

/-- **`Vᵢ = g_i^{-1}(W₀) ×_{W₀} V₀`.** The square `Vᵢ ⟶ Sᵢ ⟶ S₀`, `Vᵢ ⟶ V₀ ⟶ S₀` is Cartesian
by construction, and the right-hand square `g_i^{-1}(W₀) ⟶ Sᵢ`, `W₀ ⟶ S₀` is Cartesian because
`g_i^{-1}(W₀)` is the preimage of `W₀`. -/
theorem isPullback_restrictToBasePreimage (i : D.LaterIndex) :
    IsPullback (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i)
      ((D.restrict V₀ hV₀.isCompact).toFixedStage i)
      (D.baseMap i ∣_ W₀) (D.X₀.hom.resLE W₀ V₀ hVW) :=
  isPullback_lift_of_isPullback _ <| by
    rw [Scheme.Hom.resLE_comp_ι]
    exact (IsPullback.of_hasPullback (V₀.ι ≫ D.X₀.hom) (D.baseMap i)).flip

/-- **`Γ(Vᵢ) = Rᵢ ⊗_{R₀} A₀`**, as a pushout of commutative rings: the Cartesian square
`Vᵢ = g_i^{-1}(W₀) ×_{W₀} V₀` has all three of `g_i^{-1}(W₀)`, `V₀` and `W₀` affine. -/
theorem isPushout_appTop_restrictToBasePreimage (hW₀ : IsAffineOpen W₀) (i : D.LaterIndex) :
    IsPushout (D.baseMap i ∣_ W₀).appTop (D.X₀.hom.resLE W₀ V₀ hVW).appTop
      (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).appTop
      ((D.restrict V₀ hV₀.isCompact).toFixedStage i).appTop :=
  have : IsAffine W₀.toScheme := hW₀
  have : IsAffine V₀.toScheme := hV₀
  have : IsAffine (D.baseMap i ⁻¹ᵁ W₀ : _).toScheme := D.isAffineOpen_preimage_baseMap W₀ hW₀ i
  isPushout_appTop_of_isPullback (D.isPullback_restrictToBasePreimage W₀ V₀ hV₀ hVW i)

/-! ### Naturality in the stage -/

/-- **The morphisms `Vᵢ ⟶ g_i^{-1}(W₀)` are compatible with the transition morphisms** of the
stages `Vᵢ` and of the preimages `g_i^{-1}(W₀)`: both composites `Vⱼ ⟶ g_i^{-1}(W₀)` are the
projection `Vⱼ ⟶ Sⱼ ⟶ Sᵢ` read inside `g_i^{-1}(W₀)`. -/
theorem restrictToBasePreimage_naturality {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.restrictToBasePreimage W₀ V₀ hV₀ hVW j ≫ D.basePreimageTransition W₀ h =
      (D.restrict V₀ hV₀.isCompact).transition h ≫ D.restrictToBasePreimage W₀ V₀ hV₀ hVW i :=
  (cancel_mono (D.baseMap i ⁻¹ᵁ W₀).ι).mp <| by
    rw [Category.assoc, D.basePreimageTransition_comp_ι W₀ h, ← Category.assoc,
      D.restrictToBasePreimage_comp_ι W₀ V₀ hV₀ hVW j, Category.assoc,
      D.restrictToBasePreimage_comp_ι W₀ V₀ hV₀ hVW i]
    exact ((D.restrict V₀ hV₀.isCompact).transition_comp_snd h).symm

/-- The morphisms `Vᵢ ⟶ g_i^{-1}(W₀)` as a morphism of diagrams. -/
def basePreimageToStage : D.basePreimageOpFunctor W₀ ⟶
    (D.restrict V₀ hV₀.isCompact).stageOpFunctor where
  app i := (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).op
  naturality _ _ h :=
    Quiver.Hom.unop_inj (D.restrictToBasePreimage_naturality W₀ V₀ hV₀ hVW (leOfHom h))

/-- The maps `Rᵢ ⟶ Γ(Vᵢ)` as a morphism of diagrams of rings: the transition maps of the system
`i ↦ Γ(Vᵢ)` are those of the system `i ↦ Rᵢ` base changed along `R₀ ⟶ A₀`. -/
def baseRingToSections : D.baseRingDiagram W₀ ⟶ (D.restrict V₀ hV₀.isCompact).sectionsDiagram where
  app i := (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).appTop
  naturality _ _ h :=
    congrArg Scheme.Hom.appTop (D.restrictToBasePreimage_naturality W₀ V₀ hV₀ hVW (leOfHom h))

/-- The structure morphisms `Vᵢ ⟶ V₀`, as a morphism of diagrams out of the constant diagram
`V₀`. -/
def fixedToStage : (Functor.const D.LaterIndex).obj (op V₀.toScheme) ⟶
    (D.restrict V₀ hV₀.isCompact).stageOpFunctor where
  app i := ((D.restrict V₀ hV₀.isCompact).toFixedStage i).op
  naturality _ _ h := by
    apply Quiver.Hom.unop_inj
    simp only [Functor.const_obj_map]
    exact ((D.restrict V₀ hV₀.isCompact).transition_comp_toFixedStage (leOfHom h)).symm

/-- The maps `A₀ ⟶ Γ(Vᵢ)`, making the diagram `i ↦ Γ(Vᵢ)` a diagram of `A₀`-algebras. -/
def fixedRingToSections : (Functor.const D.LaterIndex).obj Γ(V₀.toScheme, ⊤) ⟶
    (D.restrict V₀ hV₀.isCompact).sectionsDiagram where
  app i := ((D.restrict V₀ hV₀.isCompact).toFixedStage i).appTop
  naturality _ _ h := by
    simp only [Functor.const_obj_map]
    exact congrArg Scheme.Hom.appTop
      ((D.restrict V₀ hV₀.isCompact).transition_comp_toFixedStage (leOfHom h)).symm

/-! ### The limit -/

/-- The preimage `g^{-1}(W₀)` is the fibre product `S ×_{S₀} W₀`. -/
theorem isPullback_preimage_baseProjection :
    IsPullback (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀).ι
      (D.descent.limitCone.π.app (op D.descent.base) ∣_ W₀)
      (D.descent.limitCone.π.app (op D.descent.base)) W₀.ι :=
  (isPullback_morphismRestrict (D.descent.limitCone.π.app (op D.descent.base)) W₀).flip

/-- The morphism `V ⟶ g^{-1}(W₀)`, induced by `V ⟶ S` and `V ⟶ V₀ ⟶ W₀`. -/
def restrictToBasePreimageLimit :
    (D.restrict V₀ hV₀.isCompact).limitScheme ⟶
      (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme :=
  (D.isPullback_preimage_baseProjection W₀).lift
    (pullback.snd (V₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base)))
    ((D.restrict V₀ hV₀.isCompact).limitToFixedStage ≫ D.X₀.hom.resLE W₀ V₀ hVW)
    (by rw [Category.assoc, Scheme.Hom.resLE_comp_ι]; exact pullback.condition.symm)

/-- The morphism `V ⟶ g^{-1}(W₀)` composed with `g^{-1}(W₀) ⟶ S` is the projection `V ⟶ S`. -/
theorem restrictToBasePreimageLimit_comp_ι :
    D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW ≫
        (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀).ι =
      pullback.snd (V₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base)) :=
  (D.isPullback_preimage_baseProjection W₀).lift_fst _ _ _

/-- **`V = g^{-1}(W₀) ×_{W₀} V₀`**, the limit analogue of
`isPullback_restrictToBasePreimage`. -/
theorem isPullback_restrictToBasePreimageLimit :
    IsPullback (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW)
      (D.restrict V₀ hV₀.isCompact).limitToFixedStage
      (D.descent.limitCone.π.app (op D.descent.base) ∣_ W₀)
      (D.X₀.hom.resLE W₀ V₀ hVW) :=
  isPullback_lift_of_isPullback _ <| by
    rw [Scheme.Hom.resLE_comp_ι]
    exact (IsPullback.of_hasPullback (V₀.ι ≫ D.X₀.hom)
      (D.descent.limitCone.π.app (op D.descent.base))).flip

/-- **`Γ(V) = R ⊗_{R₀} A₀`**, as a pushout of commutative rings: the limit analogue of
`isPushout_appTop_restrictToBasePreimage`, the Cartesian square `V = g^{-1}(W₀) ×_{W₀} V₀` having
all three of `g^{-1}(W₀)`, `V₀` and `W₀` affine. -/
theorem isPushout_appTop_restrictToBasePreimageLimit (hW₀ : IsAffineOpen W₀) :
    IsPushout (D.descent.limitCone.π.app (op D.descent.base) ∣_ W₀).appTop
      (D.X₀.hom.resLE W₀ V₀ hVW).appTop
      (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW).appTop
      ((D.restrict V₀ hV₀.isCompact).limitToFixedStage).appTop :=
  have : IsAffine W₀.toScheme := hW₀
  have : IsAffine V₀.toScheme := hV₀
  have : IsAffine (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme :=
    D.isAffineOpen_preimage_baseProjection W₀ hW₀
  isPushout_appTop_of_isPullback (D.isPullback_restrictToBasePreimageLimit W₀ V₀ hV₀ hVW)

/-- **The morphism `V ⟶ g^{-1}(W₀)` is compatible with the projections from the limit**: going
`V ⟶ g^{-1}(W₀) ⟶ g_i^{-1}(W₀)` is going `V ⟶ Vᵢ ⟶ g_i^{-1}(W₀)`. -/
theorem restrictToBasePreimageLimit_comp_baseProjectionPreimage (i : D.LaterIndex) :
    D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW ≫ D.baseProjectionPreimage W₀ i =
      (D.restrict V₀ hV₀.isCompact).projection i ≫ D.restrictToBasePreimage W₀ V₀ hV₀ hVW i :=
  (cancel_mono (D.baseMap i ⁻¹ᵁ W₀).ι).mp <| by
    rw [Category.assoc, D.baseProjectionPreimage_comp_ι W₀ i, ← Category.assoc,
      D.restrictToBasePreimageLimit_comp_ι W₀ V₀ hV₀ hVW, Category.assoc,
      D.restrictToBasePreimage_comp_ι W₀ V₀ hV₀ hVW i]
    exact ((D.restrict V₀ hV₀.isCompact).projection_comp_snd i).symm

/-- **The identification `Γ(V) = R ⊗_{R₀} A₀` is compatible with the cocone legs from the
stages**: `Rᵢ ⟶ Γ(Vᵢ) ⟶ Γ(V)` is `Rᵢ ⟶ R ⟶ Γ(V)`. -/
theorem baseRingToSections_comp_sectionsCocone (i : D.LaterIndex) :
    (D.baseRingToSections W₀ V₀ hV₀ hVW).app i ≫
        ((D.restrict V₀ hV₀.isCompact).sectionsCocone).ι.app i =
      (D.baseRingCocone W₀).ι.app i ≫ (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW).appTop :=
  congrArg Scheme.Hom.appTop
    (D.restrictToBasePreimageLimit_comp_baseProjectionPreimage W₀ V₀ hV₀ hVW i).symm

/-- The maps `A₀ ⟶ Γ(Vᵢ) ⟶ Γ(V)` all agree with `A₀ ⟶ Γ(V)`, so the two pushout squares have the
same `A₀`-leg over the limit. -/
theorem fixedRingToSections_comp_sectionsCocone (i : D.LaterIndex) :
    (D.fixedRingToSections V₀ hV₀).app i ≫
        ((D.restrict V₀ hV₀.isCompact).sectionsCocone).ι.app i =
      ((D.restrict V₀ hV₀.isCompact).limitToFixedStage).appTop :=
  congrArg Scheme.Hom.appTop
    ((D.restrict V₀ hV₀.isCompact).projection_comp_toFixedStage i)

/-! ### `R₀ ⟶ A₀` is flat of finite presentation -/

/-- The morphism `V₀ ⟶ W₀` induced by `X₀ ⟶ S₀`, which is the ring map `R₀ ⟶ A₀` on global
sections, is flat: it is the open immersion `V₀ ⟶ π₀^{-1}(W₀)` followed by the restriction of the
flat morphism `X₀ ⟶ S₀` over `W₀`. -/
theorem flat_resLE_X₀hom : Flat (D.X₀.hom.resLE W₀ V₀ hVW) :=
  have := D.flat
  inferInstance

/-- The morphism `V₀ ⟶ W₀` induced by `X₀ ⟶ S₀` is locally of finite presentation, `X₀ ⟶ S₀`
being of finite presentation. -/
theorem locallyOfFinitePresentation_resLE_X₀hom :
    LocallyOfFinitePresentation (D.X₀.hom.resLE W₀ V₀ hVW) :=
  have := D.finitePresentation.locallyOfFinitePresentation
  inferInstance

/-- **The ring map `R₀ ⟶ A₀` is flat.** -/
theorem ringHomFlat_appTop_resLE (hW₀ : IsAffineOpen W₀) (hV₀ : IsAffineOpen V₀) :
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.Flat :=
  have : IsAffine W₀.toScheme := hW₀
  have : IsAffine V₀.toScheme := hV₀
  HasRingHomProperty.appTop (P := @Flat) _ (D.flat_resLE_X₀hom W₀ V₀ hVW)

/-- **The ring map `R₀ ⟶ A₀` is of finite presentation.** -/
theorem ringHomFinitePresentation_appTop_resLE (hW₀ : IsAffineOpen W₀) (hV₀ : IsAffineOpen V₀) :
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.FinitePresentation :=
  have : IsAffine W₀.toScheme := hW₀
  have : IsAffine V₀.toScheme := hV₀
  HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _
    (D.locallyOfFinitePresentation_resLE_X₀hom W₀ V₀ hVW)

/-- **`A₀` is a flat `R₀`-module** for the algebra structure given by `R₀ ⟶ A₀`. -/
theorem moduleFlat_appTop_resLE (hW₀ : IsAffineOpen W₀) (hV₀ : IsAffineOpen V₀) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    Module.Flat Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
  D.ringHomFlat_appTop_resLE W₀ V₀ hVW hW₀ hV₀

/-- **`A₀` is an `R₀`-algebra of finite presentation.** -/
theorem algebraFinitePresentation_appTop_resLE (hW₀ : IsAffineOpen W₀) (hV₀ : IsAffineOpen V₀) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    Algebra.FinitePresentation Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
  D.ringHomFinitePresentation_appTop_resLE W₀ V₀ hVW hW₀ hV₀

/-! ### The literal tensor product -/

/-- **`Rᵢ ⊗_{R₀} A₀ ≅ Γ(Vᵢ)`**, the pushout square
`isPushout_appTop_restrictToBasePreimage` read as an isomorphism onto a tensor product. -/
def tensorProductIsoSections (hW₀ : IsAffineOpen W₀) (i : D.LaterIndex) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤) :=
      ((D.baseMap i ∣_ W₀).appTop).hom.toAlgebra
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.of (Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤) ⊗[Γ(W₀.toScheme, ⊤)]
        Γ(V₀.toScheme, ⊤)) ≅
      Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤) :=
    ((D.baseMap i ∣_ W₀).appTop).hom.toAlgebra
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  (CommRingCat.isPushout_tensorProduct Γ(W₀.toScheme, ⊤)
      Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤) Γ(V₀.toScheme, ⊤)).isoIsPushout _ _
    (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i)

/-- **`R ⊗_{R₀} A₀ ≅ Γ(V)`**, the pushout square
`isPushout_appTop_restrictToBasePreimageLimit` read as an isomorphism onto a tensor product. -/
def tensorProductIsoSectionsLimit (hW₀ : IsAffineOpen W₀) :
    letI : Algebra Γ(W₀.toScheme, ⊤)
        Γ((D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme, ⊤) :=
      ((D.descent.limitCone.π.app (op D.descent.base) ∣_ W₀).appTop).hom.toAlgebra
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.of (Γ((D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme, ⊤) ⊗[
        Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤)) ≅
      Γ((D.restrict V₀ hV₀.isCompact).limitScheme, ⊤) :=
  let : Algebra Γ(W₀.toScheme, ⊤)
      Γ((D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme, ⊤) :=
    ((D.descent.limitCone.π.app (op D.descent.base) ∣_ W₀).appTop).hom.toAlgebra
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  (CommRingCat.isPushout_tensorProduct Γ(W₀.toScheme, ⊤)
      Γ((D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme, ⊤)
      Γ(V₀.toScheme, ⊤)).isoIsPushout _ _
    (D.isPushout_appTop_restrictToBasePreimageLimit W₀ V₀ hV₀ hVW hW₀)

/-! ### The interface of Stacks 0DHX -/

/-- **`Rᵢ ⊗_{R₀} A₀ ≅ Γ(Vᵢ)`, in the vocabulary of Stacks 0DHX.** The algebra that Tag 0DHX builds
at the stage `i` out of the system `baseRingAlgDiagram` of `R₀`-algebras and the `R₀`-algebra `A₀`
is the ring of sections of `Vᵢ`. -/
def stageAlgebraIsoSections (hW₀ : IsAffineOpen W₀) (i : D.LaterIndex) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.of
        (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀)
          Γ(V₀.toScheme, ⊤) i) ≅
      Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  D.tensorProductIsoSections W₀ V₀ hV₀ hVW hW₀ i

/-- **`Γ(Vᵢ) = Rᵢ ⊗_{R₀} A₀` as an `Algebra.IsPushout`**, for the algebra structures carried by
the maps of `isPushout_appTop_restrictToBasePreimage`; `R₀ ⟶ Γ(Vᵢ)` is taken through `Rᵢ`, and
that it may equally be taken through `A₀` is the commutativity of that square. -/
theorem algebraIsPushout_sections (hW₀ : IsAffineOpen W₀) (i : D.LaterIndex) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤) :=
      ((D.baseMap i ∣_ W₀).appTop).hom.toAlgebra
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    letI : Algebra Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤)
        Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
      ((D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).appTop).hom.toAlgebra
    letI : Algebra Γ(V₀.toScheme, ⊤) Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
      (((D.restrict V₀ hV₀.isCompact).toFixedStage i).appTop).hom.toAlgebra
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
      ((D.baseMap i ∣_ W₀).appTop ≫
        (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).appTop).hom.toAlgebra
    haveI : IsScalarTower Γ(W₀.toScheme, ⊤) Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤)
        Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤)
        Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
      IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
        (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i).w)
    Algebra.IsPushout Γ(W₀.toScheme, ⊤) Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤)
      Γ(V₀.toScheme, ⊤) Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤) :=
    ((D.baseMap i ∣_ W₀).appTop).hom.toAlgebra
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  let : Algebra Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤)
      Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
    ((D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).appTop).hom.toAlgebra
  let : Algebra Γ(V₀.toScheme, ⊤) Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
    (((D.restrict V₀ hV₀.isCompact).toFixedStage i).appTop).hom.toAlgebra
  let : Algebra Γ(W₀.toScheme, ⊤) Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
    ((D.baseMap i ∣_ W₀).appTop ≫
      (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).appTop).hom.toAlgebra
  have : IsScalarTower Γ(W₀.toScheme, ⊤) Γ((D.baseMap i ⁻¹ᵁ W₀ : _).toScheme, ⊤)
      Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤)
      Γ((D.restrict V₀ hV₀.isCompact).schemeAt i, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
      (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i).w)
  CommRingCat.isPushout_iff_isPushout.mp
    (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i)

/-- **`R ⊗_{R₀} A₀ ≅ Γ(V)`, in the vocabulary of Stacks 0DHX.** The algebra that Tag 0DHX builds
over the limit out of the cocone `baseRingAlgCocone` and the `R₀`-algebra `A₀` is the ring of
sections of `V`. -/
def limitAlgebraIsoSections (hW₀ : IsAffineOpen W₀) :
    letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.of ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤)) ≅
      Γ((D.restrict V₀ hV₀.isCompact).limitScheme, ⊤) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  D.tensorProductIsoSectionsLimit W₀ V₀ hV₀ hVW hW₀

end AlgebraicGeometry.RelativeDescentSituation

end
