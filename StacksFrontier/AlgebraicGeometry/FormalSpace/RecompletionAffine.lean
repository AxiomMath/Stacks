module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Recompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Completion of an affine formal algebraic space along a closed subset of its reduction

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an affine formal algebraic
space over `S` and let `T` be a closed subset of the points of a reduction `i : X_red ⟶ X` of
`X`. **Stacks 0GVQ** asserts that the completion

```
X_{/T} : (Sch/S)_fppf ⟶ Sets,    U ↦ {f : U ⟶ X | f(|U|) ⊆ T}
```

is again an affine formal algebraic space over `S`, and **Stacks 0GVS** names that formal
algebraic space the *completion of `X` along `T`*.

The object is already in the library: it is
`AlgebraicGeometry.FormalSpace.completionAlong`, the fppf sheafification of the subfunctor of
sections of `X` whose point-set image lies in `T`. It has a real body — no existence statement
is chosen from — so Stacks 0GVS is a naming of an existing construction and is recorded here
by `add_to_stacks`.

What this file proves is the content of Stacks 0GVQ: writing `X` as a directed colimit of
affine schemes `X_λ` along thickenings as in Definition 0AI7, the completions `(X_λ)_{/T}` of
the stages form a directed diagram whose transition morphisms are relative thickenings,
because each is a base change of a transition morphism `X_λ ⟶ X_μ` along the cartesian square
of Stacks 0GVT; Stacks 0GVM then turns a colimit presentation of `X_{/T}` by that diagram
into an affine presentation of `X_{/T}`. The hypothesis on the transition morphisms in the
form Stacks 0GVM takes it — a relative thickening of represented fppf sheaves — is proved here
from the fact that the sheafified Yoneda embedding of the site preserves fibre products.

## Main definitions

* `AlgebraicGeometry.FormalSpace.completionDiagram` is the diagram of completions of the
  stages of a cocone on a diagram of fppf sheaves, each stage being completed along the set of
  its points lying over the given set of points of the vertex, and
  `AlgebraicGeometry.FormalSpace.completionColimitDiagram` is that diagram for a colimit
  presentation.
* `AlgebraicGeometry.FormalSpace.affineStageSheaf` is the fppf sheaf represented by an object
  of the big affine fppf site over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.relative_completionDiagram_map`: every transition morphism of
  the diagram of completions is a base change of the corresponding transition morphism of the
  cocone, hence inherits every property of morphisms of the site holding relative to the
  sheafified Yoneda embedding.
* `AlgebraicGeometry.FormalSpace.preservesLimitsOfShape_sheafifiedYoneda`: the sheafified
  Yoneda embedding of the big fppf site of `S` preserves fibre products, and
  `AlgebraicGeometry.FormalSpace.relative_isThickening_sheafifiedYoneda_map`: a morphism of the
  site whose morphism of schemes is a thickening induces a relative thickening of the
  represented fppf sheaves, which is the form in which Stacks 0GVM takes its hypothesis on the
  transition morphisms.
* `AlgebraicGeometry.FormalSpace.exists_affinePresentation_completionSheafULift`: the
  completion of an affine formal algebraic space along a closed subset of its points is a
  directed colimit of affine schemes over `S` along thickenings. This is Stacks 0GVQ except
  for the set-theoretic condition of Stacks 0AIS.
* `AlgebraicGeometry.FormalSpace.isClosed_image_univ_pointsMapULift`: the point-set image of
  the whole of a reduction is closed, the instance at the whole point set of
  `AlgebraicGeometry.FormalSpace.IsReduction.isClosed_image_pointsMapULift`.
* `AlgebraicGeometry.FormalSpace.completionAlong`: **Stacks 0GVS**.

## What is assumed

Stacks 0GVQ itself is
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_completionAlong'`, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineSupplement`, which assumes nothing
beyond the tag's own hypotheses. The geometric half proved here,
`AlgebraicGeometry.FormalSpace.exists_affinePresentation_completionSheafULift`, takes two
general cited results as hypotheses, each quantified over its own data and neither mentioning
the space or the subset:

* `haiy`: **Stacks 0AIY** at the affine stages, namely that the completion of an affine scheme
  of the site along a closed subset of its points is an affine formal algebraic space. The
  library proves 0AIY as
  `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheaf`, for
  `AlgebraicGeometry.Space.completionSheaf`, the completion formed inside presheaves of
  `Type u`; what is missing is the identification of that sheaf with
  `AlgebraicGeometry.Space.completionSheafULift` of the represented fppf sheaf of
  `Type (u + 1)`.
* `hcolim`: completion commutes with directed colimits of fppf sheaves — the completion of the
  colimit is the colimit of the completions of the stages along the sets of points lying over
  the given one. This is the step the source writes as `X_{/T} = colim (X_λ)_{/T}`. It holds
  because a section of a directed colimit of sheaves comes, fppf-locally, from a stage, and
  the condition on its point-set image is then the condition at that stage.

What Stacks 0GVQ asserts beyond that geometric half is the set-theoretic condition of
Stacks 0AIS on the completion. It is needed in exactly the place and for exactly the reason that
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit` carries it (the version of
Stacks 0GVM assuming the set-theoretic condition; Stacks 0GVM itself is
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit_iff` and
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit_of_cofinal`):
the affine presentation produced for the completion is indexed by a disjoint union of the
indices of the presentations of the stages, which need not be small enough for the size cutoff
of the site. Since that is its only use, the geometric half of Stacks 0GVQ is
isolated in `exists_affinePresentation_completionSheafULift`, which assumes no instance of it.

## Implementation notes

The completion of a formal algebraic space is formed inside sheaves of `Type (u + 1)`, so the
functoriality used here is that of `AlgebraicGeometry.Space.completionSheafMapULift`; the
diagram of completions is built from it, its identity and composition laws reducing to the
corresponding laws for the morphisms of completion subfunctors, which hold on sections.

The sets along which the stages are completed are the inverse images of the given set under
the structure morphisms of the cocone. Taking inverse images rather than images is what makes
the two hypotheses of `AlgebraicGeometry.Space.isPullback_completionSheafMapULift` — that the
set on the source is contained in and contains the inverse image of the set on the target —
both available, so that the completion square is cartesian and the base-change argument runs.
It is also what makes closedness of the sets at the stages immediate from closedness of the
given set, by `AlgebraicGeometry.FormalSpace.isClosed_preimage_pointsMapULift`.

The statement of Stacks 0GVQ is given for `AlgebraicGeometry.FormalSpace.completionAlong`, the
completion along a subset of the points of a reduction, as in
`AlgebraicGeometry.FormalSpace.isPullback_completionAlongMap` (Stacks 0GVT); the intermediate
results are stated for `AlgebraicGeometry.Space.completionSheafULift`, the completion along a
set of points of the space itself, which is where the argument lives.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
* [Stacks Project, Tag 0GVQ](https://stacks.math.columbia.edu/tag/0GVQ)
* [Stacks Project, Tag 0GVS](https://stacks.math.columbia.edu/tag/0GVS)
* [Stacks Project, Tag 0GVT](https://stacks.math.columbia.edu/tag/0GVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Functoriality of the completion of a sheaf of large sets -/

/-- The morphism of completion subfunctors induced by the identity is the identity. -/
theorem completionMapULift_id (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    (T : Set (Space.pointsULift.{u + 1} B S hS X))
    (h : T ⊆ Space.pointsMapULift.{u + 1} B S hS X (𝟙 X) ⁻¹' T) :
    Space.completionMapULift B S hS (𝟙 X) T T h = 𝟙 _ := by
  ext U x
  rfl

/-- The morphism of completion subfunctors induced by a composite is the composite of the
morphisms induced by the factors. -/
theorem completionMapULift_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (T₁ : Set (Space.pointsULift.{u + 1} B S hS X))
    (T₂ : Set (Space.pointsULift.{u + 1} B S hS Y))
    (T₃ : Set (Space.pointsULift.{u + 1} B S hS Z))
    (h₁ : T₁ ⊆ Space.pointsMapULift.{u + 1} B S hS X f ⁻¹' T₂)
    (h₂ : T₂ ⊆ Space.pointsMapULift.{u + 1} B S hS Y g ⁻¹' T₃)
    (h₃ : T₁ ⊆ Space.pointsMapULift.{u + 1} B S hS X (f ≫ g) ⁻¹' T₃) :
    Space.completionMapULift B S hS (f ≫ g) T₁ T₃ h₃ =
      Space.completionMapULift B S hS f T₁ T₂ h₁ ≫
        Space.completionMapULift B S hS g T₂ T₃ h₂ := by
  ext U x
  rfl

/-- The morphisms of completions induced by two equal morphisms of sheaves agree. -/
theorem completionSheafMapULift_congr {X' X : FppfSheaf B S hS} {f g : X' ⟶ X}
    (hfg : f = g) (T' : Set (Space.pointsULift.{u + 1} B S hS X'.obj))
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (h : T' ⊆ Space.pointsMapULift.{u + 1} B S hS X'.obj f.hom ⁻¹' T) :
    Space.completionSheafMapULift B S hS f T' T h =
      Space.completionSheafMapULift B S hS g T' T (hfg ▸ h) := by
  subst hfg
  rfl

/-- The morphism of completions induced by the identity is the identity. -/
theorem completionSheafMapULift_id (X : FppfSheaf B S hS)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (h : T ⊆ Space.pointsMapULift.{u + 1} B S hS X.obj (𝟙 X.obj) ⁻¹' T) :
    Space.completionSheafMapULift B S hS (𝟙 X) T T h = 𝟙 _ :=
  (congrArg
      (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
      (completionMapULift_id B S hS X.obj T h)).trans
    (CategoryTheory.Functor.map_id _ _)

/-- The morphism of completions induced by a composite is the composite of the morphisms
induced by the factors. -/
theorem completionSheafMapULift_comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T₁ : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (T₂ : Set (Space.pointsULift.{u + 1} B S hS Y.obj))
    (T₃ : Set (Space.pointsULift.{u + 1} B S hS Z.obj))
    (h₁ : T₁ ⊆ Space.pointsMapULift.{u + 1} B S hS X.obj f.hom ⁻¹' T₂)
    (h₂ : T₂ ⊆ Space.pointsMapULift.{u + 1} B S hS Y.obj g.hom ⁻¹' T₃)
    (h₃ : T₁ ⊆ Space.pointsMapULift.{u + 1} B S hS X.obj (f ≫ g).hom ⁻¹' T₃) :
    Space.completionSheafMapULift B S hS (f ≫ g) T₁ T₃ h₃ =
      Space.completionSheafMapULift B S hS f T₁ T₂ h₁ ≫
        Space.completionSheafMapULift B S hS g T₂ T₃ h₂ :=
  (congrArg
      (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
      (completionMapULift_comp B S hS f.hom g.hom T₁ T₂ T₃ h₁ h₂ h₃)).trans
    (Functor.map_comp _ _ _)

/-! ### The diagram of completions of the stages of a cocone -/

/-- For a cocone `c` on a diagram `E` of fppf sheaves with vertex `Y` and a set `W` of points
of `Y`, the set of points of a stage lying over `W` is the inverse image under the transition
morphism of the corresponding set for a later stage. -/
theorem preimage_pointsMapULift_cocone {I : Type (u + 1)} [Preorder I]
    (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) {i j : I} (f : i ⟶ j) :
    Space.pointsMapULift.{u + 1} B S hS (E.obj i).obj (c i).hom ⁻¹' W =
      Space.pointsMapULift.{u + 1} B S hS (E.obj i).obj (E.map f).hom ⁻¹'
        (Space.pointsMapULift.{u + 1} B S hS (E.obj j).obj (c j).hom ⁻¹' W) := by
  have hhom : (E.map f).hom ≫ (c j).hom = (c i).hom :=
    congrArg (fun φ : E.obj i ⟶ Y => φ.hom) (hc f)
  rw [← Set.preimage_comp, ← Space.pointsMapULift_comp, hhom]

/-- The diagram of completions of the stages of a cocone: a stage `E i` is completed along the
set of its points lying over `W`. -/
def completionDiagram {I : Type (u + 1)} [Preorder I] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) : I ⥤ FppfSheaf B S hS where
  obj i := Space.completionSheafULift B S hS (E.obj i)
    (Space.pointsMapULift.{u + 1} B S hS (E.obj i).obj (c i).hom ⁻¹' W)
  map {_i _j} f := Space.completionSheafMapULift B S hS (E.map f) _ _
    (preimage_pointsMapULift_cocone B S hS E Y c hc W f).subset
  map_id i :=
    (completionSheafMapULift_congr B S hS (E.map_id i) _ _ _).trans
      (completionSheafMapULift_id B S hS (E.obj i) _ _)
  map_comp {_i j _k} f g :=
    (completionSheafMapULift_congr B S hS (E.map_comp f g) _ _ _).trans
      (completionSheafMapULift_comp B S hS (E.map f) (E.map g) _
        (Space.pointsMapULift.{u + 1} B S hS (E.obj j).obj (c j).hom ⁻¹' W) _
        (preimage_pointsMapULift_cocone B S hS E Y c hc W f).subset
        (preimage_pointsMapULift_cocone B S hS E Y c hc W g).subset _)

/-- Every transition morphism of the diagram of completions of the stages of a cocone is a
base change of the corresponding transition morphism of the cocone, by the cartesian square of
Stacks 0GVT, so it inherits from it every property of morphisms of the site which holds
relative to the sheafified Yoneda embedding. -/
theorem relative_completionDiagram_map {I : Type (u + 1)} [Preorder I]
    (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj))
    (P : MorphismProperty (BigFppfOver B S hS)) {i j : I} (f : i ⟶ j)
    (hf : MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) P
      (E.map f)) :
    MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) P
      ((completionDiagram B S hS E Y c hc W).map f) := by
  let _ : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) P).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (Space.isPullback_completionSheafMapULift B S hS (E.map f) _ _
      (preimage_pointsMapULift_cocone B S hS E Y c hc W f).subset
      (preimage_pointsMapULift_cocone B S hS E Y c hc W f).symm.subset) hf

/-- The diagram of completions of the stages of a directed colimit presentation of `Y`, the
stages being read in `Y` through the given isomorphism with the colimit. -/
abbrev completionColimitDiagram {I : Type (u + 1)} [Preorder I] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (e : Y ≅ colimit E)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) : I ⥤ FppfSheaf B S hS :=
  completionDiagram B S hS E Y (fun i ↦ colimit.ι E i ≫ e.inv)
    (fun {_ _} f ↦ by rw [← Category.assoc, colimit.w]) W

/-! ### Thickenings of the site as relative thickenings of represented sheaves -/

/-- The sheafified Yoneda embedding of the big fppf site of `S` preserves fibre products: the
site is subcanonical, so the embedding is, after forgetting to presheaves, the universe-lifted
Yoneda embedding, which preserves limits, and the forgetful functor to presheaves reflects
them. -/
theorem preservesLimitsOfShape_sheafifiedYoneda :
    PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := by
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let e : Sheaf.sheafifiedYoneda J ⋙ sheafToPresheaf J (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' J)
      (sheafToPresheaf J (Type (u + 1))) ≪≫
      J.uliftYonedaCompSheafToPresheaf.{u + 1}
  let _ : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda J ⋙ sheafToPresheaf J (Type (u + 1))) :=
    preservesLimitsOfShape_of_natIso e.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (Sheaf.sheafifiedYoneda J) (sheafToPresheaf J (Type (u + 1)))

/-- A morphism of the big affine fppf site over `S` whose morphism of schemes is a thickening
induces a relative thickening of the represented fppf sheaves: thickenings are stable under
base change, the sheafified Yoneda embedding is fully faithful and preserves fibre products,
and the site has fibre products. -/
theorem relative_isThickening_sheafifiedYoneda_map {a b : BigAffineFppf B S hS} (g : a ⟶ b)
    (hg : Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map g)) :
    MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map g)) := by
  let J := BigFppfOver.topology B S hS
  let _ := preservesLimitsOfShape_sheafifiedYoneda B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let ff := Sheaf.fullyFaithfulSheafifiedYoneda J
  let _ := ff.full
  let _ := ff.faithful
  exact MorphismProperty.relative_map hg

/-- The point-set image of the whole of a reduction is closed in the points of the space, the
inclusion of a reduction being bijective on points. This is the instance at the whole point
set of `AlgebraicGeometry.FormalSpace.IsReduction.isClosed_image_pointsMapULift`, which
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_completionAlong'` (Stacks 0GVQ)
uses. -/
theorem isClosed_image_univ_pointsMapULift {Z Zred : FppfSheaf B S hS} {j : Zred ⟶ Z}
    (hj : IsReduction B S hS Z Zred j) :
    @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Z.obj)
      (Space.pointsMapULift.{u + 1} B S hS Zred.obj j.hom '' Set.univ) := by
  let _ := Space.pointTopologyULift.{u + 1} B S hS Z.obj
  rw [Set.image_univ, Set.range_eq_univ.mpr hj.bijective_pointsMapULift.2]
  exact isClosed_univ

/-! ### The affine presentation of the completion -/

/-- The completion of a sheaf presented as a directed colimit is a directed colimit of affine
schemes along thickenings, as soon as the completions of the stages are affine formal
algebraic spaces, the transition morphisms of the presentation are relative thickenings, and
the completion is the colimit of the completions of the stages: the transition morphisms of
the diagram of completions are then relative thickenings as base changes, and Stacks 0GVM
applies. -/
theorem exists_affinePresentation_completionSheafULift_of_colimit {I : Type (u + 1)}
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (e : Y ≅ colimit E)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj))
    (hstage : ∀ i, IsAffineFormalAlgebraicSpace B S hS
      ((completionColimitDiagram B S hS E Y e W).obj i))
    (hEthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (E.map f))
    (ecompletion : Space.completionSheafULift B S hS Y W ≅
      colimit (completionColimitDiagram B S hS E Y e W)) :
    ∃ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K ∧ IsDirected K (· ≤ ·) ∧
      ∃ F : K ⥤ BigAffineFppf B S hS,
        (∀ ⦃p q : K⦄ (f : p ⟶ q), Stacks.Thickenings.IsThickening
          ((BigAffineFppf.toScheme B S hS).map (F.map f))) ∧
        Nonempty (Space.completionSheafULift B S hS Y W ≅ colimit (F ⋙
          BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :=
  exists_affinePresentation_of_colimit B S hS (completionColimitDiagram B S hS E Y e W)
    hstage
    (fun {_ _} f ↦ relative_completionDiagram_map B S hS E Y _ _ W _ f (hEthick f)) _
    ecompletion

/-- The fppf sheaf represented by an object of the big affine fppf site over `S`. These are the
stages of a presentation of an affine formal algebraic space as in Stacks 0AI7. -/
abbrev affineStageSheaf (V : BigAffineFppf B S hS) : FppfSheaf B S hS :=
  (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
    ((BigAffineFppf.inclusion B S hS).obj V)

/-- **The geometric half of Stacks 0GVQ.** Let `X` be an affine formal algebraic space over `S`
and let `W` be a closed subset of the points of `X`. Then the completion `X_{/W}` of `X` along
`W` is a directed colimit of affine schemes over `S` whose transition morphisms are
thickenings, that is it has an affine presentation as in Definition 0AI7.

Nothing here is assumed about `X_{/W}`; the two hypotheses `haiy` and `hcolim` are the general
cited inputs described in the module docstring, and what Stacks 0GVQ asserts beyond this
conclusion is the set-theoretic condition of Stacks 0AIS. -/
theorem exists_affinePresentation_completionSheafULift (X : FppfSheaf B S hS)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W)
    (haiy : ∀ (V : BigAffineFppf B S hS)
      (V' : Set (Space.pointsULift.{u + 1} B S hS (affineStageSheaf B S hS V).obj)),
      @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
        (affineStageSheaf B S hS V).obj) V' →
      IsAffineFormalAlgebraicSpace B S hS
        (Space.completionSheafULift B S hS (affineStageSheaf B S hS V) V'))
    (hcolim : ∀ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K → IsDirected K (· ≤ ·) →
      ∀ (F : K ⥤ FppfSheaf B S hS) (Z : FppfSheaf B S hS) (eZ : Z ≅ colimit F)
        (V : Set (Space.pointsULift.{u + 1} B S hS Z.obj)),
        Nonempty (Space.completionSheafULift B S hS Z V ≅
          colimit (completionColimitDiagram B S hS F Z eZ V))) :
    ∃ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K ∧ IsDirected K (· ≤ ·) ∧
      ∃ F : K ⥤ BigAffineFppf B S hS,
        (∀ ⦃p q : K⦄ (f : p ⟶ q), Stacks.Thickenings.IsThickening
          ((BigAffineFppf.toScheme B S hS).map (F.map f))) ∧
        Nonempty (Space.completionSheafULift B S hS X W ≅ colimit (F ⋙
          BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) := by
  obtain ⟨-, I, pre, hne, hdir, D, hthickD, ⟨e⟩⟩ := hX
  let _ : Preorder I := pre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  let E : I ⥤ FppfSheaf B S hS := D ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  exact exists_affinePresentation_completionSheafULift_of_colimit B S hS E X e W
    (fun i ↦ haiy (D.obj i) _ (isClosed_preimage_pointsMapULift _ W hW))
    (fun {_ _} f ↦ relative_isThickening_sheafifiedYoneda_map B S hS (D.map f) (hthickD f))
    (hcolim I pre hne hdir E X e W).some

add_to_stacks 0GVS "the completion of a formal algebraic space along a closed subset of its \
reduction, defined for an arbitrary morphism into the space and an arbitrary subset of the \
points of its source" AlgebraicGeometry.FormalSpace.completionAlong

end AlgebraicGeometry.FormalSpace

end
