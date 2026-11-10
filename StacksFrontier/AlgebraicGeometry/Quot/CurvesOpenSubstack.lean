module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenLocus

/-!
# Open substacks of the stack of curves (Stacks 0E0E)

Section 0E0E of the source characterizes an open substack of the stack of curves by a property
`P` of families of curves, through the condition

* (o) given a family of curves `f : X → S` there exists a largest open subscheme `S' ⊂ S` such
  that `f|_{f^{-1}(S')}` has `P`, and formation of `S'` commutes with arbitrary base change.

Given (o), the strictly full subcategory `Curves^P` of families with `P` is an open substack of
`Curves`, and it has the universal properties (1) and (2) of the source: the classifying
morphism of a family factors through `Curves^P` exactly when the family has `P`.

## Main definitions

* `AlgebraicGeometry.IsOpenCurvesLocus`: condition (o).
* `AlgebraicGeometry.curvesSubstack` and `AlgebraicGeometry.curvesSubstackInclusion`: for a
  property inherited along morphisms of families, the
  strictly full subcategory `Curves^P`, as a category fibred in groupoids over the big fppf site
  of `Spec(ℤ)`, and its inclusion into `Curves` as a 1-morphism.

## Main results

* `AlgebraicGeometry.IsOpenCurvesLocus.of_points`: (o) from an open set of points of the base
  whose inverse images describe `P` on every family mapping to the given one.
* `AlgebraicGeometry.IsOpenCurvesLocus.and`: condition (o) for a conjunction, so that
  `Curves^{Q, P} = Curves^Q ∩ Curves^P` is again an open substack.
* `AlgebraicGeometry.IsOpenCurvesLocus.prop_of_hom`: a property with (o) passes to every family
  mapping to a family with the property; in particular it is invariant under isomorphism.
* `AlgebraicGeometry.IsOpenCurvesLocus.hasOpenObjectPropertyLocus`: over every scheme-valued
  point of `Curves`, (o) cuts out an open subscheme of the base.
* `AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion`: **Stacks 0E0E**, `Curves^P ⊂
  Curves` is an open substack: strictly full, and its inclusion is representable by algebraic
  spaces and an open immersion.
* `AlgebraicGeometry.factors_curvesSubstack_iff`: **Stacks 0E0E**, part (1), the classifying
  morphism of a family factors through `Curves^P` exactly when the family has `P`.
* `AlgebraicGeometry.factors_curvesSubstack_iff_of_iso`: **Stacks 0E0E**, part (2) read as the
  special case of part (1) it is in the source.
* `AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion_and_factors_iff`: **Stacks 0E0E**,
  the whole statement.

## Implementation notes

An open substack of a category fibred in groupoids is, as in the source (Stacks 04YL, 04YM read
for a category fibred in groupoids), a strictly full subcategory whose inclusion is
representable by algebraic spaces and an open immersion in the sense of Stacks 04XB. Nothing
here uses that `Curves` is an algebraic stack: the conclusions are the predicates
`AlgebraicGeometry.Stack.IsOpenImmersion` and
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` for 1-morphisms of categories fibred
in groupoids, exactly as for Stacks 0D5B.

Condition (o) is stated in the form the open loci of this library are produced in (for example
Stacks 0DZZ, `AlgebraicGeometry.CurveFamily.exists_isOpenSubspace_smooth`): every family `G` has
an open subspace `W` of its base such that a family `F` mapping to `G` has `P` exactly when its
morphism of base schemes factors through `W`. Letting the morphism be an identity says that `G`
restricted to `W` has `P` and that `W` is the largest such open; letting it vary says that the
formation of `W` commutes with arbitrary base change, a morphism of families being a base change.

The mechanism turning (o) into an open immersion is
`AlgebraicGeometry.Stack.isOpenImmersion_and_isRepresentableByAlgebraicSpaces_of_hasOpenLocus`;
what is proved here is its input, the open subscheme of the base of a scheme-valued point. A
scheme-valued point `y` of `Curves` over `U` carries the family `y(U)`, whose base is `U`, and
every `y(T)` maps to it over the structure morphism `T → U`; so (o) at `y(U)` is the open
subscheme.

A scheme-valued point is the 2-Yoneda form of a morphism from a scheme to `Curves`, and the
family it classifies is its value at the identity of its base, so part (1) is stated for
scheme-valued points. Part (2) is, in the source, the special case of part (1) at the family a
proper scheme of dimension at most one over a field is.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Pullbacks of presheaves on the big fppf site over `Spec ℤ`, given directly: instance search
for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_CurvesOpenSubstack :
    HasPullbacks ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_CurvesOpenSubstack
    {X Y Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_CurvesOpenSubstack B hZ).has_limit _

local instance (priority := high) hasLimitsOfShape_discrete_presheaf_CurvesOpenSubstack
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- **Condition (o) of Stacks 0E0E.** Every family of curves `G` has an open subspace `W` of its
base such that a family of curves `F` mapping to `G` has the property `P` exactly when the
morphism of base schemes factors through `W`: `W` is the largest open of the base over which
`G` has `P`, and its formation commutes with arbitrary base change. -/
def IsOpenCurvesLocus (P : ObjectProperty (CurveFamily B hZ)) : Prop :=
  ∀ G : CurveFamily B hZ, ∃ W : Subfunctor (schemeSpace G.base).obj,
    Space.IsOpenSubspace B integerBase hZ W ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        P F ↔ ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
          t ≫ W.ι = (schemeSpaceMap a.baseMap).hom

variable {B hZ} {P : ObjectProperty (CurveFamily B hZ)}

/-- **Condition (o) from an open set of points.** If every family of curves `G` has an open set
`Ω` of points of its base such that a family mapping to `G` has `P` exactly when its morphism of
base schemes sends every point into `Ω`, then `P` satisfies condition (o). -/
theorem IsOpenCurvesLocus.of_points
    (h : ∀ G : CurveFamily B hZ, ∃ Ω : Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
      IsOpen Ω ∧ ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        P F ↔ Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
          (schemeSpaceMap a.baseMap).hom) ⊆ Ω) :
    IsOpenCurvesLocus B hZ P := by
  intro G
  obtain ⟨Ω, hΩ, hchar⟩ := h G
  have hW := Space.isOpenSubspace_openSubspaceOfPoints B integerBase hZ
    (schemeSpace G.base).property Ω hΩ
  refine ⟨Space.openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).obj Ω, hW,
    fun F a => ?_⟩
  rw [Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property _ hW,
    Space.range_pointsMap_ι_openSubspaceOfPoints]
  exact hchar F a

/-- **Intersections of open substacks of curves.** If two properties of families of curves
satisfy condition (o), so does their conjunction: the open of the base for the conjunction is the
intersection of the two opens. This is the step `Curves^{Q, P} = Curves^Q ∩ Curves^P` of
Stacks 0E0E. -/
theorem IsOpenCurvesLocus.and {Q : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) (hQ : IsOpenCurvesLocus B hZ Q) :
    IsOpenCurvesLocus B hZ (fun F => P F ∧ Q F) := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  obtain ⟨W₁, hW₁, h₁⟩ := hP G
  obtain ⟨W₂, hW₂, h₂⟩ := hQ G
  refine ⟨Set.range (Space.pointsMap B integerBase hZ W₁.toFunctor W₁.ι) ∩
      Set.range (Space.pointsMap B integerBase hZ W₂.toFunctor W₂.ι),
    (Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B integerBase hZ
      (schemeSpace G.base).property W₁ hW₁).inter
      (Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B integerBase hZ
        (schemeSpace G.base).property W₂ hW₂), fun F a => ?_⟩
  rw [h₁ F a, h₂ F a,
    Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property W₁ hW₁,
    Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property W₂ hW₂,
    Set.subset_inter_iff]

/-- A property satisfying condition (o) passes from a family of curves to every family mapping to
it, that is, to every base change of it. -/
theorem IsOpenCurvesLocus.prop_of_hom (hP : IsOpenCurvesLocus B hZ P) {F G : CurveFamily B hZ}
    (a : F ⟶ G) (hG : P G) : P F := by
  obtain ⟨W, -, hW⟩ := hP G
  obtain ⟨t, ht⟩ := (hW G (𝟙 G)).mp hG
  refine (hW F a).mpr ⟨(schemeSpaceMap a.baseMap).hom ≫ t, ?_⟩
  have h1 : (schemeSpaceMap (𝟙 G : G ⟶ G).baseMap).hom = 𝟙 _ := yoneda.map_id G.base
  rw [Category.assoc, ht, h1, Category.comp_id]

/-- A property satisfying condition (o) is invariant under isomorphism of families of curves:
it cuts out a strictly full subcategory. -/
theorem IsOpenCurvesLocus.isClosedUnderIsomorphisms (hP : IsOpenCurvesLocus B hZ P) :
    P.IsClosedUnderIsomorphisms :=
  ⟨fun e => hP.prop_of_hom e.inv⟩

/-- The restriction of the projection of families of curves to the strictly full subcategory cut
out by a property inherited along morphisms of families is fibred in groupoids: a lift of a
morphism of base schemes to a family with the property is a base change of it, so it has the
property. -/
theorem curvesProjectionOver_isFiberedInGroupoids_of_prop_of_hom
    (hP : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → P G → P F) :
    (P.ι ⋙ curvesProjectionOver B hZ).IsFiberedInGroupoids where
  exists_lift f x hx := by
    obtain ⟨y, φ, hφ⟩ := (curvesFiberedCategory B hZ).2.exists_lift f x.obj hx
    refine ⟨⟨y, hP φ x.property⟩, ObjectProperty.homMk φ, ?_⟩
    cases hφ
    exact Functor.IsHomLift.map _
  unique_lift φ ψ f h := by
    obtain ⟨χ, hχ, huniq⟩ := (curvesFiberedCategory B hZ).2.unique_lift φ.hom ψ.hom f h
    refine ⟨ObjectProperty.homMk χ, ⟨hχ.1, ?_⟩, ?_⟩
    · ext
      exact hχ.2
    · intro χ' hχ'
      ext
      exact huniq χ'.hom ⟨hχ'.1, congrArg (fun a => a.hom) hχ'.2⟩

variable (B hZ P)

/-- **Stacks 0E0E.** The strictly full subcategory `Curves^P` of families of curves with a
property `P` inherited along morphisms of families, as a category fibred in groupoids over the
big fppf site of `Spec(ℤ)`. When `P` satisfies condition (o) it is an open substack of `Curves`,
`AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion`. -/
def curvesSubstack (hP : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → P G → P F) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk
    (Stack.objectPropertySubcategory B integerBase hZ (curvesFiberedCategory B hZ).val P)
    (curvesProjectionOver_isFiberedInGroupoids_of_prop_of_hom hP)

/-- **Stacks 0E0E.** The inclusion `Curves^P ⟶ Curves`, as a 1-morphism of categories fibred in
groupoids over the big fppf site of `Spec(ℤ)`. -/
def curvesSubstackInclusion (hP : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → P G → P F) :
    curvesSubstack B hZ P hP ⟶ curvesFiberedCategory B hZ :=
  Bicategory.InducedBicategory.mkHom
    (Stack.objectPropertyInclusion B integerBase hZ (curvesFiberedCategory B hZ).val P)

variable {B hZ P}

/-- **The open subscheme over a scheme-valued point.** For a property satisfying condition (o),
every scheme-valued point `y` of the stack of curves over `U` cuts out an open subscheme `V` of
`U` through which an object `T` of the big fppf site of `U` maps exactly when the family `y(T)`
has the property. -/
theorem IsOpenCurvesLocus.exists_open_over (hP : IsOpenCurvesLocus B hZ P)
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ P (y.obj T) := by
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let G := y.obj T₀
  obtain ⟨W, hW, hWchar⟩ := hP G
  obtain ⟨V₀, j, hj, e, he⟩ : ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ G.base),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map j := by
    have key : ∀ (U' : BigFppfOver B integerBase hZ) (W' : Subfunctor (yoneda.obj U')),
        Space.IsOpenSubspace B integerBase hZ W' →
        ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ U'),
          IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
          ∃ e : yoneda.obj V ≅ W'.toFunctor, e.hom ≫ W'.ι = yoneda.map j := by
      intro U' W' hW'
      let h := hW'.2.rep.isPullback (𝟙 (yoneda.obj U'))
      let eMap := hW'.2.rep.fst (𝟙 (yoneda.obj U'))
      have : IsIso eMap := h.isIso_fst_of_isIso
      exact ⟨_, hW'.2.rep.snd (𝟙 (yoneda.obj U')), hW'.2.property_snd (𝟙 (yoneda.obj U')),
        asIso eMap, by simpa [eMap] using h.w⟩
    exact key G.base W hW
  have hb : ∀ T, (y.obj T).base = (Over.map U.hom).obj T := fun T => congrArg (fun F => F.obj T) hy
  have h₂ : (Over.map U.hom).obj T₀ = U := by
    cases U
    congr 1
  let β : G.base ≅ U := eqToIso ((hb T₀).trans h₂)
  let V : BigFppfOver B U.left.1 U.left.2 := Over.mk (j ≫ β.hom).left
  refine ⟨V, ?_, fun T => Iff.symm ?_⟩
  · change IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map (j ≫ β.hom))
    rw [Functor.map_comp]
    infer_instance
  let t : T ⟶ T₀ := Over.homMk T.hom (by simp [T₀])
  let a : y.obj T ⟶ G := y.map t
  have hcomm : a.baseMap ≫ β.hom =
      eqToHom (hb T) ≫ (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
    have hm := Functor.congr_hom hy t
    have hcanon : (Over.map U.hom).map t ≫ eqToHom h₂ =
        (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
      cases U
      rfl
    change (curvesProjectionOver B hZ).map (y.map t) = _ at hm
    change (curvesProjectionOver B hZ).map (y.map t) ≫ eqToHom ((hb T₀).trans h₂) = _
    rw [hm, ← hcanon, Category.assoc, Category.assoc]
    exact congrArg (fun k => eqToHom (hb T) ≫ (Over.map U.hom).map t ≫ k) (eqToHom_trans _ _)
  rw [hWchar (y.obj T) a]
  change (∃ t : yoneda.obj (y.obj T).base ⟶ W.toFunctor, t ≫ W.ι = yoneda.map a.baseMap) ↔ _
  have hgen : ∀ {U' V' A : BigFppfOver B integerBase hZ} (W' : Subfunctor (yoneda.obj U'))
      (j' : V' ⟶ U') (e' : yoneda.obj V' ≅ W'.toFunctor) (_he' : e'.hom ≫ W'.ι = yoneda.map j')
      (a' : A ⟶ U'),
      (∃ t : yoneda.obj A ⟶ W'.toFunctor, t ≫ W'.ι = yoneda.map a') ↔
        ∃ k : A ⟶ V', k ≫ j' = a' := by
    intro U' V' A W' j' e' he' a'
    have he'' : e'.inv ≫ yoneda.map j' = W'.ι := by
      rw [← he', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨yoneda.preimage (t ≫ e'.inv), yoneda.map_injective ?_⟩
      rw [Functor.map_comp, yoneda.map_preimage, Category.assoc, he'', ht]
    · rintro ⟨k, hk⟩
      exact ⟨yoneda.map k ≫ e'.hom, by rw [Category.assoc, he', ← Functor.map_comp, hk]⟩
  have hfac := hgen (U' := G.base) W j e he a.baseMap
  refine hfac.trans ?_
  have hc := congrArg (fun m => m.left) hcomm
  simp only [Over.comp_left] at hc
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨Over.homMk (eqToHom (congrArg Comma.left (hb T)).symm ≫ k.left) ?_⟩
    have hk' := congrArg (fun m => (m ≫ β.hom).left) hk
    simp only [Over.comp_left] at hk'
    change (eqToHom _ ≫ k.left) ≫ (j ≫ β.hom).left = T.hom
    rw [Over.comp_left, Category.assoc, ← Category.assoc k.left, hk', hc, Over.eqToHom_left]
    simp
  · rintro ⟨k⟩
    let l : (y.obj T).base ⟶ V₀ := Over.homMk (eqToHom (congrArg Comma.left (hb T)) ≫ k.left)
      (by apply ObjectProperty.hom_ext; exact specULiftZIsTerminal.hom_ext _ _)
    refine ⟨l, (cancel_mono β.hom).mp (Over.OverMorphism.ext ?_)⟩
    simp only [Over.comp_left]
    rw [hc, Over.eqToHom_left]
    change (eqToHom _ ≫ k.left) ≫ (j ≫ β.hom).left = _
    rw [Category.assoc, show k.left ≫ (j ≫ β.hom).left = T.hom from Over.w k]
    rfl

/-- **The open locus of the inclusion of `Curves^P`.** For a property satisfying condition (o),
every scheme-valued point of the stack of curves cuts out an open subscheme of its base along
which the families it carries have the property. -/
theorem IsOpenCurvesLocus.hasOpenObjectPropertyLocus (hP : IsOpenCurvesLocus B hZ P) :
    Stack.HasOpenObjectPropertyLocus B integerBase hZ (curvesFiberedCategory B hZ).val P :=
  hP.exists_open_over

/-- **Stacks 0E0E.** For a property `P` of families of curves satisfying condition (o), the
strictly full subcategory `Curves^P` is an open substack of `Curves`: `P` is invariant under
isomorphism, and the inclusion `Curves^P ⟶ Curves` is representable by algebraic spaces and an
open immersion. -/
theorem isOpenImmersion_curvesSubstackInclusion (hP : IsOpenCurvesLocus B hZ P) :
    P.IsClosedUnderIsomorphisms ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ P hP.prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (curvesSubstackInclusion B hZ P hP.prop_of_hom) := by
  have h := Stack.isOpenImmersion_and_isRepresentableByAlgebraicSpaces_of_hasOpenLocus
    B integerBase hZ (curvesSubstackInclusion B hZ P hP.prop_of_hom)
    (Stack.full_objectPropertyInclusion B integerBase hZ (curvesFiberedCategory B hZ).val P)
    (Stack.faithful_objectPropertyInclusion B integerBase hZ (curvesFiberedCategory B hZ).val P)
    (Stack.hasOpenLocus_objectPropertyInclusion B integerBase hZ (curvesFiberedCategory B hZ).val P
      hP.isClosedUnderIsomorphisms hP.hasOpenObjectPropertyLocus)
  exact ⟨hP.isClosedUnderIsomorphisms, h.2, h.1⟩

/-- **Stacks 0E0E, part (1).** For a property `P` satisfying condition (o), the classifying
morphism of a family of curves factors through `Curves^P` exactly when the family has `P`: a
scheme-valued point `y` of `Curves` over `U` lifts to `Curves^P` exactly when the family `y(U)`
it classifies has `P`. -/
theorem factors_curvesSubstack_iff (hP : IsOpenCurvesLocus B hZ P)
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ P.FullSubcategory, z ⋙ P.ι = y) ↔
      P (y.obj (Over.mk (𝟙 U.left))) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact (z.obj _).property
  · intro h
    exact ⟨P.lift y fun T => hP.prop_of_hom (y.map (Over.homMk T.hom (by simp))) h, rfl⟩

/-- **Stacks 0E0E, part (2).** The special case of part (1) at a given family of curves `X`
over `U` — for instance the family of a proper scheme of dimension at most one over a field
`k`, with `U = Spec k`: a scheme-valued point classifying `X` lifts to `Curves^P` exactly when
`X` has `P`. -/
theorem factors_curvesSubstack_iff_of_iso (hP : IsOpenCurvesLocus B hZ P)
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) (X : CurveFamily B hZ)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ X) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ P.FullSubcategory, z ⋙ P.ι = y) ↔ P X :=
  (factors_curvesSubstack_iff hP U y hy).trans
    ⟨hP.prop_of_hom e.inv, hP.prop_of_hom e.hom⟩

/-- **Stacks 0E0E.** For a property `P` of families of curves satisfying condition (o):
`Curves^P ⊂ Curves` is an open substack — `P` is invariant under isomorphism, and the inclusion
is representable by algebraic spaces and an open immersion — and the classifying morphism of a
family factors through `Curves^P` exactly when the family has `P`. -/
@[stacks 0E0E "the open substack Curves^P cut out by a property P with condition (o), and its \
universal property (1); part (2) is the special case of (1) at the family of a proper scheme of \
dimension at most one over a field"]
theorem isOpenImmersion_curvesSubstackInclusion_and_factors_iff
    (hP : IsOpenCurvesLocus B hZ P) :
    (P.IsClosedUnderIsomorphisms ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ P hP.prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (curvesSubstackInclusion B hZ P hP.prop_of_hom)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ P.FullSubcategory, z ⋙ P.ι = y) ↔
        P (y.obj (Over.mk (𝟙 U.left)))) :=
  ⟨isOpenImmersion_curvesSubstackInclusion hP, factors_curvesSubstack_iff hP⟩

end AlgebraicGeometry

end
