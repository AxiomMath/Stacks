module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliaryGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialitySourceTargetCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSmoothBaseChange07U4
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.NormalizationMorphism

/-!
# The normalized groupoid of a smooth groupoid in algebraic spaces

Let `(U, R, s, t, c)` be a smooth groupoid in algebraic spaces over `B` whose object space `U`
satisfies the equivalent conditions of Stacks 0BB1. The proof of Stacks 0GMJ builds from it the
*normalized groupoid* `(U^ν, R^ν, s^ν, t^ν, c^ν)`:

* `U^ν` is the normalization of `U` (Stacks 07U4, `AlgebraicGeometry.Space.normalizationData`);
* `R^ν = U^ν ×_{ν, U, s} R`, with `s^ν` the first projection;
* `t^ν : R^ν ⟶ U^ν` is the morphism of normalizations induced by `t`, the unique lift of
  `R^ν ⟶ R ⟶ U` through `ν : U^ν ⟶ U` given by the universal property of the normalization
  (Stacks 0BB4, part (4)) — that `R^ν` is normal and that this composite preserves codimension
  zero is exactly where normalization commuting with smooth base change (Stacks 07U4, part (4))
  enters;
* `c^ν((x, r₁), (y, r₂)) = (y, c(r₁, r₂))`.

The groupoid axioms are reduced, by the uniqueness half of the same universal property, to the
corresponding axioms of `(U, R, s, t, c)`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Normalized.groupoid`: the normalized groupoid
  `(U^ν, R^ν, s^ν, t^ν, c^ν)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Normalized.hom`: the morphism of groupoids
  `(U^ν, R^ν) ⟶ (U, R)`.
* `AlgebraicGeometry.Stack.normalizationGroupoid`: the normalized groupoid as an
  `AlgebraicGeometry.Stack.NormalizationGroupoid`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Normalized.isSmooth_tgt`: `t^ν` is smooth, being
  the composite of the involution `i^ν` with `s^ν`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Normalized.isSmooth`: the normalized groupoid is
  smooth.

## References

* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0GMJ](https://stacks.math.columbia.edu/tag/0GMJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces.Normalized

open Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G)
  (hfin : HasLocallyFiniteIrreducibleComponents C S hS G.objects.obj)

/-! ### Points of fibre products of presheaves -/

section Points

variable {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- A point of a fibre product of presheaves over a test object, from its two projections. -/
noncomputable def ptMk (T : (BigFppfOver C S hS)ᵒᵖ) (x : X.obj T) (y : Y.obj T)
    (h : f.app T x = g.app T y) : (pullback f g).obj T :=
  (pullbackObjIso f g T).inv ((Types.pullbackIsoPullback (f.app T) (g.app T)).inv ⟨(x, y), h⟩)

/-- The first projection of `ptMk f g T x y h` is `x`. -/
@[simp]
theorem ptMk_fst (T : (BigFppfOver C S hS)ᵒᵖ) (x : X.obj T) (y : Y.obj T)
    (h : f.app T x = g.app T y) : (pullback.fst f g).app T (ptMk f g T x y h) = x := by
  show ((pullbackObjIso f g T).inv ≫ (pullback.fst f g).app T) _ = x
  rw [pullbackObjIso_inv_comp_fst]
  exact Types.pullbackIsoPullback_inv_fst_apply (f.app T) (g.app T) ⟨(x, y), h⟩

/-- The second projection of `ptMk f g T x y h` is `y`. -/
@[simp]
theorem ptMk_snd (T : (BigFppfOver C S hS)ᵒᵖ) (x : X.obj T) (y : Y.obj T)
    (h : f.app T x = g.app T y) : (pullback.snd f g).app T (ptMk f g T x y h) = y := by
  show ((pullbackObjIso f g T).inv ≫ (pullback.snd f g).app T) _ = y
  rw [pullbackObjIso_inv_comp_snd]
  exact Types.pullbackIsoPullback_inv_snd_apply (f.app T) (g.app T) ⟨(x, y), h⟩

/-- A point of a fibre product of presheaves is determined by its two projections. -/
theorem pt_ext (T : (BigFppfOver C S hS)ᵒᵖ) {a b : (pullback f g).obj T}
    (h₁ : (pullback.fst f g).app T a = (pullback.fst f g).app T b)
    (h₂ : (pullback.snd f g).app T a = (pullback.snd f g).app T b) : a = b := by
  have hfst : ∀ c : (pullback f g).obj T,
      ((Types.pullbackIsoPullback (f.app T) (g.app T)).hom ((pullbackObjIso f g T).hom c)).1.1 =
        (pullback.fst f g).app T c := fun c => by
    rw [Types.pullbackIsoPullback_hom_fst]
    exact congrArg (fun k => k c) (pullbackObjIso_hom_comp_fst f g T)
  have hsnd : ∀ c : (pullback f g).obj T,
      ((Types.pullbackIsoPullback (f.app T) (g.app T)).hom ((pullbackObjIso f g T).hom c)).1.2 =
        (pullback.snd f g).app T c := fun c => by
    rw [Types.pullbackIsoPullback_hom_snd]
    exact congrArg (fun k => k c) (pullbackObjIso_hom_comp_snd f g T)
  exact (pullbackObjIso f g T ≪≫ Types.pullbackIsoPullback _ _).toEquiv.injective <|
    Subtype.ext <| Prod.ext ((hfst a).trans (h₁.trans (hfst b).symm))
      ((hsnd a).trans (h₂.trans (hsnd b).symm))

/-- A lift into a fibre product of presheaves, evaluated at a point. -/
theorem lift_app {W : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ X) (b : W ⟶ Y)
    (w : a ≫ f = b ≫ g) (T : (BigFppfOver C S hS)ᵒᵖ) (z : W.obj T) :
    (pullback.lift a b w).app T z =
      ptMk f g T (a.app T z) (b.app T z) (congrArg (fun k => k.app T z) w) :=
  pt_ext f g T ((congrArg (fun k => k.app T z) (pullback.lift_fst a b w)).trans
      (ptMk_fst _ _ _ _ _ _).symm)
    ((congrArg (fun k => k.app T z) (pullback.lift_snd a b w)).trans (ptMk_snd _ _ _ _ _ _).symm)

end Points

/-! ### The spaces and the source -/

/-- The normalization `U^ν ⟶ U` of the object space. -/
noncomputable abbrev data : NormalizationData C S hS G.objects.obj :=
  normalizationData C S hS G.objects.property hfin

/-- The arrow space `R^ν = U^ν ×_{ν, U, s} R`, as a presheaf. -/
noncomputable abbrev arrowsObj : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u :=
  pullback (data G hfin).hom G.source.hom

/-- The source `s^ν : R^ν ⟶ U^ν`, the first projection. -/
noncomputable abbrev src : arrowsObj G hfin ⟶ (data G hfin).space :=
  pullback.fst (data G hfin).hom G.source.hom

/-- The projection `R^ν ⟶ R`. -/
noncomputable abbrev proj : arrowsObj G hfin ⟶ G.arrows.obj :=
  pullback.snd (data G hfin).hom G.source.hom

/-- `ν ∘ s^ν = s ∘ pr` as morphisms `R^ν ⟶ U`. -/
theorem src_comp : src G hfin ≫ (data G hfin).hom = proj G hfin ≫ G.source.hom :=
  pullback.condition

/-- `R^ν` is an algebraic space. -/
theorem isAlgebraicSpace_arrowsObj :
    _root_.AlgebraicGeometry.IsAlgebraicSpace C S hS (arrowsObj G hfin) :=
  isAlgebraicSpace_pullback C S hS _ _ (data G hfin).isAlgebraicSpace G.arrows.property
    G.objects.property

include hG in
/-- The source `s^ν : R^ν ⟶ U^ν` is smooth, being a base change of `s`. -/
theorem isSmooth_src : Space.IsSmooth C S hS (src G hfin) :=
  isSmooth_of_isPullback (IsPullback.of_hasPullback (data G hfin).hom G.source.hom)
    (isAlgebraicSpace_arrowsObj G hfin) G.arrows.property (data G hfin).isAlgebraicSpace
    G.objects.property hG.1

include hG in
/-- `R^ν` is normal, being smooth over the normal space `U^ν`. -/
theorem isNormal_arrowsObj : Space.IsNormal C S hS (arrowsObj G hfin) :=
  isNormal_of_isSmooth (isAlgebraicSpace_arrowsObj G hfin) (data G hfin).isAlgebraicSpace _
    (isSmooth_src G hG hfin) ((data G hfin).isNormal G.objects.property)

/-! ### Rigidity of morphisms into `U^ν` -/

omit hfin in
/-- Two morphisms from a normal algebraic space to `U^ν` which agree after `ν` are equal, as soon
as their common composite with `ν` preserves codimension zero. -/
theorem hom_ext (hfin : HasLocallyFiniteIrreducibleComponents C S hS G.objects.obj)
    {Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (hZ : _root_.AlgebraicGeometry.IsAlgebraicSpace C S hS Z)
    (hZn : Space.IsNormal C S hS Z) {f g : Z ⟶ (data G hfin).space}
    (h : f ≫ (data G hfin).hom = g ≫ (data G hfin).hom)
    (hgen : ∀ z : Space.points C S hS Z, localRingDimension C S hS z = 0 →
      localRingDimension C S hS (pointsMap C S hS Z (f ≫ (data G hfin).hom) z) = 0) :
    f = g :=
  ((data G hfin).existsUnique_lift_hom G.objects.property hZ hZn _ hgen).unique rfl h.symm

/-- Codimension zero is preserved by a flat morphism to `U^ν` followed by `ν`. -/
theorem codimZero_of_isFlat {Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hZ : _root_.AlgebraicGeometry.IsAlgebraicSpace C S hS Z) (f : Z ⟶ (data G hfin).space)
    (hf : Space.IsFlat C S hS f)
    (z : Space.points C S hS Z) (hz : localRingDimension C S hS z = 0) :
    localRingDimension C S hS (pointsMap C S hS Z (f ≫ (data G hfin).hom) z) = 0 := by
  rw [pointsMap_comp_apply]
  exact ((data G hfin).bijOn_codimensionZeroPoints_hom G.objects.property).1
    (localRingDimension_eq_zero_of_isFlat C S hS hZ (data G hfin).isAlgebraicSpace f hf z hz)

/-- Two morphisms from a normal algebraic space to `U^ν` which agree after `ν` are equal when
the second one is smooth. -/
private theorem eq_of_comp_eq_of_isSmooth {Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hZ : _root_.AlgebraicGeometry.IsAlgebraicSpace C S hS Z) (hZn : Space.IsNormal C S hS Z)
    {f g : Z ⟶ (data G hfin).space} (h : f ≫ (data G hfin).hom = g ≫ (data G hfin).hom)
    (hg : Space.IsSmooth C S hS g) : f = g :=
  hom_ext G hfin hZ hZn h (by
    rw [h]
    exact codimZero_of_isFlat G hfin hZ g (isFlat_of_isSmooth C S hS _ hg))

/-! ### The target -/

include hG in
/-- The composite `R^ν ⟶ R ⟶ U` along the target preserves codimension zero. -/
theorem codimZero_proj_target (z : Space.points C S hS (arrowsObj G hfin))
    (hz : localRingDimension C S hS z = 0) :
    localRingDimension C S hS
      (pointsMap C S hS _ (proj G hfin ≫ G.target.hom) z) = 0 := by
  rw [pointsMap_comp_apply]
  exact localRingDimension_eq_zero_of_isFlat C S hS G.arrows.property G.objects.property _
    (isFlat_of_isSmooth C S hS _ hG.2) _
    ((data G hfin).localRingDimension_pullback_snd_eq_zero G.objects.property G.arrows.property
      G.source.hom (isFlat_of_isSmooth C S hS _ hG.1) z hz)

/-- **The target `t^ν : R^ν ⟶ U^ν`**: the morphism of normalizations induced by `t`, that is the
unique lift of `R^ν ⟶ R ⟶ U` through `ν` (Stacks 0BB4, part (4)). -/
noncomputable def tgt : arrowsObj G hfin ⟶ (data G hfin).space :=
  ((data G hfin).existsUnique_lift_hom G.objects.property (isAlgebraicSpace_arrowsObj G hfin)
    (isNormal_arrowsObj G hG hfin) _ (codimZero_proj_target G hG hfin)).exists.choose

/-- `ν ∘ t^ν = t ∘ pr` as morphisms `R^ν ⟶ U`. -/
theorem tgt_comp : tgt G hG hfin ≫ (data G hfin).hom = proj G hfin ≫ G.target.hom :=
  ((data G hfin).existsUnique_lift_hom G.objects.property (isAlgebraicSpace_arrowsObj G hfin)
    (isNormal_arrowsObj G hG hfin) _ (codimZero_proj_target G hG hfin)).exists.choose_spec

/-! ### The inverse, and smoothness of the target -/

/-- The inverse `i^ν : R^ν ⟶ R^ν`, `(x, r) ↦ (t^ν(x, r), r⁻¹)`. -/
noncomputable def inv : arrowsObj G hfin ⟶ arrowsObj G hfin :=
  pullback.lift (tgt G hG hfin) (proj G hfin ≫ groupoidInverse G) (by
    rw [tgt_comp, Category.assoc, groupoidInverse_source])

/-- `s^ν ∘ i^ν = t^ν`. -/
@[reassoc (attr := simp)]
theorem inv_src : inv G hG hfin ≫ src G hfin = tgt G hG hfin := pullback.lift_fst _ _ _

/-- The projection of `i^ν(x, r)` to `R` is `r⁻¹`. -/
@[reassoc (attr := simp)]
theorem inv_proj : inv G hG hfin ≫ proj G hfin = proj G hfin ≫ groupoidInverse G :=
  pullback.lift_snd _ _ _

/-- `t^ν ∘ i^ν = s^ν`. -/
@[reassoc]
theorem inv_tgt : inv G hG hfin ≫ tgt G hG hfin = src G hfin := by
  have h : (inv G hG hfin ≫ tgt G hG hfin) ≫ (data G hfin).hom =
      src G hfin ≫ (data G hfin).hom := by
    rw [Category.assoc, tgt_comp, inv_proj_assoc, groupoidInverse_target, src_comp]
  exact eq_of_comp_eq_of_isSmooth G hfin (isAlgebraicSpace_arrowsObj G hfin)
    (isNormal_arrowsObj G hG hfin) h (isSmooth_src G hG hfin)

/-- `i^ν` is an involution. -/
@[reassoc (attr := simp)]
theorem inv_inv : inv G hG hfin ≫ inv G hG hfin = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, inv_src, inv_tgt, Category.id_comp]
  · rw [Category.assoc, inv_proj, inv_proj_assoc, groupoidInverse_groupoidInverse,
      Category.comp_id, Category.id_comp]

/-- `i^ν` is an isomorphism, being its own inverse. -/
instance isIso_inv : IsIso (inv G hG hfin) := ⟨inv G hG hfin, inv_inv G hG hfin, inv_inv G hG hfin⟩

/-- `t^ν = s^ν ∘ i^ν`. -/
theorem tgt_eq : tgt G hG hfin = inv G hG hfin ≫ src G hfin :=
  (inv_src G hG hfin).symm

/-- The target `t^ν : R^ν ⟶ U^ν` is smooth. -/
theorem isSmooth_tgt : Space.IsSmooth C S hS (tgt G hG hfin) := by
  rw [tgt_eq]
  exact isSmooth_comp C S hS (isAlgebraicSpace_arrowsObj G hfin) (isAlgebraicSpace_arrowsObj G hfin)
    (data G hfin).isAlgebraicSpace _ _
    (isSmooth_of_isIso C S hS (isAlgebraicSpace_arrowsObj G hfin)
      (isAlgebraicSpace_arrowsObj G hfin) _)
    (isSmooth_src G hG hfin)

/-! ### The identity -/

/-- The identity `e^ν : U^ν ⟶ R^ν`, `x ↦ (x, e(ν x))`. -/
noncomputable def ident : (data G hfin).space ⟶ arrowsObj G hfin :=
  pullback.lift (𝟙 _) ((data G hfin).hom ≫ (identityArrow G).hom) (by
    rw [Category.id_comp, Category.assoc, identityArrow_hom_comp_source, Category.comp_id])

/-- `s^ν ∘ e^ν = id`. -/
@[reassoc (attr := simp)]
theorem ident_src : ident G hfin ≫ src G hfin = 𝟙 _ := pullback.lift_fst _ _ _

/-- The projection of `e^ν(x)` to `R` is `e(ν x)`. -/
@[reassoc (attr := simp)]
theorem ident_proj : ident G hfin ≫ proj G hfin = (data G hfin).hom ≫ (identityArrow G).hom :=
  pullback.lift_snd _ _ _

/-- `t^ν ∘ e^ν = id`. -/
@[reassoc (attr := simp)]
theorem ident_tgt : ident G hfin ≫ tgt G hG hfin = 𝟙 _ :=
  have h : (ident G hfin ≫ tgt G hG hfin) ≫ (data G hfin).hom = (data G hfin).hom := by
    rw [Category.assoc, tgt_comp, ident_proj_assoc, identityArrow_hom_comp_target,
      Category.comp_id]
  hom_ext G hfin (data G hfin).isAlgebraicSpace ((data G hfin).isNormal G.objects.property)
    (by rw [h, Category.id_comp])
    (by
      rw [h]
      exact fun z hz => ((data G hfin).bijOn_codimensionZeroPoints_hom G.objects.property).1 hz)

/-! ### Composition in `R` -/

omit hfin in
/-- The composite in the evaluated groupoid is the composition morphism at the point of the
fibre product. -/
theorem compose_eq (T : (BigFppfOver C S hS)ᵒᵖ) (a b : G.arrows.obj.obj T)
    (h : G.source.hom.app T a = G.target.hom.app T b) :
    G.toGroupoidInFunctors.compose T a b h =
      G.comp.hom.app T (ptMk G.source.hom G.target.hom T a b h) := by
  show G.comp.hom.app T ((composableToPullback G.source.hom G.target.hom).app T ⟨(a, b), h⟩) = _
  congr 1
  apply pt_ext _ _ T
  · rw [pullbackFst_app_composableToPullback, ptMk_fst]
  · rw [pullbackSnd_app_composableToPullback, ptMk_snd]

omit hfin in
/-- A point of `R ×_{s, U, t} R` is the point built from its two projections. -/
theorem ptMk_eta (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (pullback G.source.hom G.target.hom).obj T) :
    ptMk G.source.hom G.target.hom T ((pullback.fst G.source.hom G.target.hom).app T p)
      ((pullback.snd G.source.hom G.target.hom).app T p)
      (congrArg (fun k => k.app T p) (pullback.condition (f := G.source.hom) (g := G.target.hom))) =
      p :=
  pt_ext _ _ T (ptMk_fst _ _ _ _ _ _) (ptMk_snd _ _ _ _ _ _)

omit hfin in
/-- `t ∘ c = t ∘ pr₀` as morphisms `R ×_{s, U, t} R ⟶ U`. -/
theorem comp_hom_target :
    G.comp.hom ≫ G.target.hom = pullback.fst G.source.hom G.target.hom ≫ G.target.hom := by
  ext T p
  show G.target.hom.app T (G.comp.hom.app T p) =
    G.target.hom.app T ((pullback.fst G.source.hom G.target.hom).app T p)
  rw [← ptMk_eta G T p, ← compose_eq, ptMk_fst]
  exact (G.toGroupoidInFunctors.pointwiseData T).target_comp _ _ _

/-! ### The composition of the normalized groupoid -/

/-- The composition `c^ν((x, r₁), (y, r₂)) = (y, c(r₁, r₂))` of the normalized groupoid. -/
noncomputable def comp : pullback (src G hfin) (tgt G hG hfin) ⟶ arrowsObj G hfin :=
  pullback.lift (pullback.snd _ _ ≫ src G hfin)
    (groupoidCompose G (pullback.fst _ _ ≫ proj G hfin) (pullback.snd _ _ ≫ proj G hfin) (by
      rw [Category.assoc, Category.assoc, ← src_comp, ← tgt_comp, ← Category.assoc,
        pullback.condition, Category.assoc])) (by
    rw [groupoidCompose_source, Category.assoc, Category.assoc, src_comp])

/-- The projections to `R` of a composable pair in `R^ν ×_{s^ν, U^ν, t^ν} R^ν` are composable
in `R`. -/
theorem composable_w : (pullback.fst (src G hfin) (tgt G hG hfin) ≫ proj G hfin) ≫ G.source.hom =
    (pullback.snd (src G hfin) (tgt G hG hfin) ≫ proj G hfin) ≫ G.target.hom := by
  rw [Category.assoc, Category.assoc, ← src_comp, ← tgt_comp, ← Category.assoc,
    pullback.condition, Category.assoc]

/-- `s^ν ∘ c^ν = s^ν ∘ pr₁`. -/
@[reassoc (attr := simp)]
theorem comp_src : comp G hG hfin ≫ src G hfin = pullback.snd _ _ ≫ src G hfin :=
  pullback.lift_fst _ _ _

/-- The projection of `c^ν((x, r₁), (y, r₂))` to `R` is `c(r₁, r₂)`. -/
@[reassoc (attr := simp)]
theorem comp_proj : comp G hG hfin ≫ proj G hfin =
    groupoidCompose G _ _ (composable_w G hG hfin) :=
  pullback.lift_snd _ _ _

/-- `R^ν ×_{s^ν, U^ν, t^ν} R^ν` is an algebraic space. -/
theorem isAlgebraicSpace_composable :
    _root_.AlgebraicGeometry.IsAlgebraicSpace C S hS (pullback (src G hfin) (tgt G hG hfin)) :=
  isAlgebraicSpace_pullback C S hS _ _ (isAlgebraicSpace_arrowsObj G hfin)
    (isAlgebraicSpace_arrowsObj G hfin) (data G hfin).isAlgebraicSpace

/-- The first projection `R^ν ×_{s^ν, U^ν, t^ν} R^ν ⟶ R^ν` is smooth. -/
theorem isSmooth_composable_fst :
    Space.IsSmooth C S hS (pullback.fst (src G hfin) (tgt G hG hfin)) :=
  isSmooth_of_isPullback (IsPullback.of_hasPullback (src G hfin) (tgt G hG hfin))
    (isAlgebraicSpace_composable G hG hfin) (isAlgebraicSpace_arrowsObj G hfin)
    (isAlgebraicSpace_arrowsObj G hfin) (data G hfin).isAlgebraicSpace (isSmooth_tgt G hG hfin)

/-- `t^ν ∘ c^ν = t^ν ∘ pr₀`. -/
@[reassoc]
theorem comp_tgt : comp G hG hfin ≫ tgt G hG hfin = pullback.fst _ _ ≫ tgt G hG hfin := by
  have h : (comp G hG hfin ≫ tgt G hG hfin) ≫ (data G hfin).hom =
      (pullback.fst _ _ ≫ tgt G hG hfin) ≫ (data G hfin).hom := by
    rw [Category.assoc, tgt_comp, comp_proj_assoc, groupoidCompose_target, Category.assoc,
      Category.assoc, tgt_comp]
  exact eq_of_comp_eq_of_isSmooth G hfin (isAlgebraicSpace_composable G hG hfin)
    (isNormal_of_isSmooth (isAlgebraicSpace_composable G hG hfin)
      (isAlgebraicSpace_arrowsObj G hfin) _ (isSmooth_composable_fst G hG hfin)
      (isNormal_arrowsObj G hG hfin)) h
    (isSmooth_comp C S hS (isAlgebraicSpace_composable G hG hfin)
      (isAlgebraicSpace_arrowsObj G hfin) (data G hfin).isAlgebraicSpace _ _
      (isSmooth_composable_fst G hG hfin) (isSmooth_tgt G hG hfin))

/-! ### The pointwise groupoid -/

section Pointwise

variable (T : (BigFppfOver C S hS)ᵒᵖ)

/-- `ν(t^ν a) = t(pr a)` for a point `a` of `R^ν`. -/
theorem tgt_app_comp (a : (arrowsObj G hfin).obj T) :
    (data G hfin).hom.app T ((tgt G hG hfin).app T a) =
      G.target.hom.app T ((proj G hfin).app T a) :=
  natTrans_app_congr (tgt_comp G hG hfin) T a

/-- `ν(s^ν a) = s(pr a)` for a point `a` of `R^ν`. -/
theorem src_app_comp (a : (arrowsObj G hfin).obj T) :
    (data G hfin).hom.app T ((src G hfin).app T a) =
      G.source.hom.app T ((proj G hfin).app T a) :=
  natTrans_app_congr (src_comp G hfin) T a

/-- The projection to `R` of the point `(x, r)` of `R^ν` is `r`. -/
@[simp]
theorem proj_ptMk (x : (data G hfin).space.obj T) (r : G.arrows.obj.obj T)
    (h : (data G hfin).hom.app T x = G.source.hom.app T r) :
    (proj G hfin).app T (ptMk (data G hfin).hom G.source.hom T x r h) = r :=
  ptMk_snd _ _ _ _ _ _

/-- The source of the point `(x, r)` of `R^ν` is `x`. -/
@[simp]
theorem src_ptMk (x : (data G hfin).space.obj T) (r : G.arrows.obj.obj T)
    (h : (data G hfin).hom.app T x = G.source.hom.app T r) :
    (src G hfin).app T (ptMk (data G hfin).hom G.source.hom T x r h) = x :=
  ptMk_fst _ _ _ _ _ _

/-- The point `(x, r)` of `R^ν` depends only on `x` and `r`. -/
theorem ptMk_congr {x : (data G hfin).space.obj T} {r r' : G.arrows.obj.obj T} (hr : r = r')
    (h : (data G hfin).hom.app T x = G.source.hom.app T r)
    (h' : (data G hfin).hom.app T x = G.source.hom.app T r') :
    ptMk (data G hfin).hom G.source.hom T x r h =
      ptMk (data G hfin).hom G.source.hom T x r' h' := by
  subst hr; rfl

omit hfin in
/-- The composite of two arrows in the evaluated groupoid depends only on the arrows. -/
theorem compose_congr {a a' b b' : G.arrows.obj.obj T} (ha : a = a') (hb : b = b')
    (h : G.source.hom.app T a = G.target.hom.app T b)
    (h' : G.source.hom.app T a' = G.target.hom.app T b') :
    G.toGroupoidInFunctors.compose T a b h = G.toGroupoidInFunctors.compose T a' b' h' := by
  subst ha hb; rfl

/-- `s^ν(c^ν p) = s^ν(pr₁ p)` for a composable pair `p`. -/
theorem comp_app_src (p : (pullback (src G hfin) (tgt G hG hfin)).obj T) :
    (src G hfin).app T ((comp G hG hfin).app T p) =
      (src G hfin).app T ((pullback.snd (src G hfin) (tgt G hG hfin)).app T p) :=
  natTrans_app_congr (comp_src G hG hfin) T p

/-- The projection to `R` of `c^ν p` is the composite in `R` of the projections of the two
components of the composable pair `p`. -/
theorem comp_app_proj (p : (pullback (src G hfin) (tgt G hG hfin)).obj T) :
    (proj G hfin).app T ((comp G hG hfin).app T p) =
      G.toGroupoidInFunctors.compose T
        ((proj G hfin).app T ((pullback.fst (src G hfin) (tgt G hG hfin)).app T p))
        ((proj G hfin).app T ((pullback.snd (src G hfin) (tgt G hG hfin)).app T p))
        (congrArg (fun k => k.app T p) (composable_w G hG hfin)) :=
  (natTrans_app_congr (comp_proj G hG hfin) T p).trans (groupoidCompose_eval G _ _ _ T p)

/-- The action of the evaluated groupoid of `(U, R)` on the fibres of `ν`: an arrow
`r : u ⟶ u'` carries `x` over `u` to `t^ν(x, r)` over `u'`. -/
noncomputable def action : G.toGroupoidInFunctors.Evaluation T ⥤ Type u where
  obj u := { x : (data G hfin).space.obj T // (data G hfin).hom.app T x = u }
  map {u u'} r := ↾ fun x => ⟨(tgt G hG hfin).app T
      (ptMk _ _ T x.1 (G.toGroupoidInFunctors.evaluationArrowEquiv T u u' r).1
        (x.2.trans (G.toGroupoidInFunctors.evaluationArrowEquiv T u u' r).2.1.symm)),
    (tgt_app_comp G hG hfin T _).trans ((congrArg (G.target.hom.app T)
      (proj_ptMk G hfin T _ _ _)).trans (G.toGroupoidInFunctors.evaluationArrowEquiv T u u' r).2.2)⟩
  map_id u := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    subst hx
    change (tgt G hG hfin).app T (ptMk _ _ T x _ _) = x
    have h1 : ptMk (data G hfin).hom G.source.hom T x
        (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ (𝟙 _)).1
        (rfl.trans (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ (𝟙 _)).2.1.symm) =
        (ident G hfin).app T x :=
      pt_ext _ _ T ((ptMk_fst _ _ _ _ _ _).trans (natTrans_app_congr (ident_src G hfin) T x).symm)
        ((ptMk_snd _ _ _ _ _ _).trans
          ((Deformation.GroupoidInFunctors.evaluationArrowEquiv_id _ _ _).trans
            ((identityArrow_hom_app G T _).symm.trans
              (natTrans_app_congr (ident_proj G hfin) T x).symm)))
    exact (congrArg ((tgt G hG hfin).app T) h1).trans
      (natTrans_app_congr (ident_tgt G hG hfin) T x)
  map_comp {u u' u''} r r' := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, hx⟩
    rw [types_comp_apply]
    apply Subtype.ext
    change (tgt G hG hfin).app T (ptMk _ _ T x _ _) =
      (tgt G hG hfin).app T (ptMk _ _ T ((tgt G hG hfin).app T (ptMk _ _ T x _ _)) _ _)
    let ρ := (G.toGroupoidInFunctors.evaluationArrowEquiv T u u' r).1
    let ρ' := (G.toGroupoidInFunctors.evaluationArrowEquiv T u' u'' r').1
    let b := ptMk (data G hfin).hom G.source.hom T x ρ
      (hx.trans (G.toGroupoidInFunctors.evaluationArrowEquiv T u u' r).2.1.symm)
    let a := ptMk (data G hfin).hom G.source.hom T ((tgt G hG hfin).app T b) ρ'
      ((tgt_app_comp G hG hfin T _).trans ((congrArg (G.target.hom.app T)
        (proj_ptMk G hfin T _ _ _)).trans
          ((G.toGroupoidInFunctors.evaluationArrowEquiv T u u' r).2.2.trans
            (G.toGroupoidInFunctors.evaluationArrowEquiv T u' u'' r').2.1.symm)))
    let p := ptMk (src G hfin) (tgt G hG hfin) T a b (ptMk_fst _ _ _ _ _ _)
    have hsrc : (src G hfin).app T ((comp G hG hfin).app T p) = x :=
      (comp_app_src G hG hfin T p).trans
        ((congrArg ((src G hfin).app T) (ptMk_snd _ _ _ _ _ _)).trans (src_ptMk G hfin T _ _ _))
    have hproj : (proj G hfin).app T ((comp G hG hfin).app T p) =
        G.toGroupoidInFunctors.compose T ρ' ρ
          ((G.toGroupoidInFunctors.evaluationArrowEquiv T u' u'' r').2.1.trans
            (G.toGroupoidInFunctors.evaluationArrowEquiv T u u' r).2.2.symm) := by
      refine (comp_app_proj G hG hfin T p).trans ?_
      refine compose_congr G T ?_ ?_ _ _
      · exact (congrArg ((proj G hfin).app T) (ptMk_fst _ _ _ _ _ _)).trans
          (proj_ptMk G hfin T _ _ _)
      · exact (congrArg ((proj G hfin).app T) (ptMk_snd _ _ _ _ _ _)).trans
          (proj_ptMk G hfin T _ _ _)
    have hpt : ptMk (data G hfin).hom G.source.hom T x
        (G.toGroupoidInFunctors.evaluationArrowEquiv T u u'' (r ≫ r')).1
        (hx.trans (G.toGroupoidInFunctors.evaluationArrowEquiv T u u'' (r ≫ r')).2.1.symm) =
        (comp G hG hfin).app T p :=
      pt_ext _ _ T ((ptMk_fst _ _ _ _ _ _).trans hsrc.symm) ((ptMk_snd _ _ _ _ _ _).trans
        ((Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp _ _ r r').trans hproj.symm))
    exact (congrArg ((tgt G hG hfin).app T) hpt).trans
      ((natTrans_app_congr (comp_tgt G hG hfin) T p).trans
        (congrArg ((tgt G hG hfin).app T) (ptMk_fst _ _ _ _ _ _)))

/-- A point of `U^ν` as an object of the groupoid of elements of the action. -/
noncomputable def index (x : (data G hfin).space.obj T) : (action G hG hfin T).Elements :=
  (action G hG hfin T).elementsMk ((data G hfin).hom.app T x) ⟨x, rfl⟩

/-- The arrows `x ⟶ x'` of the groupoid of elements are the points of `R^ν` from `x` to `x'`. -/
noncomputable def arrowEquiv (x x' : (data G hfin).space.obj T) :
    (index G hG hfin T x ⟶ index G hG hfin T x') ≃
      { a : (arrowsObj G hfin).obj T //
        (src G hfin).app T a = x ∧ (tgt G hG hfin).app T a = x' } where
  toFun φ := ⟨ptMk _ _ T x (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ φ.1).1
      ((G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ φ.1).2.1.symm),
    ptMk_fst _ _ _ _ _ _, congrArg Subtype.val φ.2⟩
  invFun a := ⟨(G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).symm
      ⟨(proj G hfin).app T a.1,
        (src_app_comp G hfin T a.1).symm.trans (congrArg _ a.2.1),
        (tgt_app_comp G hG hfin T a.1).symm.trans (congrArg _ a.2.2)⟩, by
    apply Subtype.ext
    change (tgt G hG hfin).app T (ptMk _ _ T x _ _) = x'
    exact (congrArg ((tgt G hG hfin).app T) (pt_ext _ _ T
      ((ptMk_fst _ _ _ _ _ _).trans a.2.1.symm)
      ((ptMk_snd _ _ _ _ _ _).trans (congrArg Subtype.val (Equiv.apply_symm_apply _ _))))).trans
        a.2.2⟩
  left_inv φ := by
    apply Functor.Elements.hom_ext
    change (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).symm _ = φ.1
    apply (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (ptMk_snd _ _ _ _ _ _)
  right_inv a := Subtype.ext <| pt_ext _ _ T ((ptMk_fst _ _ _ _ _ _).trans a.2.1.symm)
    ((ptMk_snd _ _ _ _ _ _).trans (congrArg Subtype.val (Equiv.apply_symm_apply _ _)))

/-- **The evaluation of the normalized groupoid at a test object is a groupoid**: it is the
groupoid of elements of the action of the evaluated groupoid of `(U, R)` on the fibres of `ν`. -/
noncomputable def pointwise :
    Deformation.PointwiseGroupoid ((src G hfin).app T) ((tgt G hG hfin).app T)
      (fun p => (composableToPullback (src G hfin) (tgt G hG hfin) ≫ comp G hG hfin).app T p) :=
  Deformation.PointwiseGroupoid.ofIndexing (index G hG hfin T) _ _ _ (arrowEquiv G hG hfin T)
    (fun x y z g f => by
      change ptMk _ _ T x _ _ = (comp G hG hfin).app T
        ((composableToPullback (src G hfin) (tgt G hG hfin)).app T _)
      apply pt_ext _ _ T
      · refine (ptMk_fst _ _ _ _ _ _).trans ?_
        refine Eq.symm ((comp_app_src G hG hfin T _).trans ?_)
        rw [pullbackSnd_app_composableToPullback]
        exact ptMk_fst _ _ _ _ _ _
      · refine (ptMk_snd _ _ _ _ _ _).trans ?_
        refine Eq.trans ?_ (comp_app_proj G hG hfin T _).symm
        refine (Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp _ _ g.1 f.1).trans ?_
        refine compose_congr G T ?_ ?_ _ _
        · rw [pullbackFst_app_composableToPullback]
          exact (ptMk_snd _ _ _ _ _ _).symm
        · rw [pullbackSnd_app_composableToPullback]
          exact (ptMk_snd _ _ _ _ _ _).symm)

end Pointwise

/-! ### The normalized groupoid -/

/-- The object space `U^ν`, as an algebraic space. -/
noncomputable abbrev objectsSp : AlgebraicSpaces C S hS :=
  ⟨(data G hfin).space, (data G hfin).isAlgebraicSpace⟩

/-- The arrow space `R^ν`, as an algebraic space. -/
noncomputable abbrev arrowsSp : AlgebraicSpaces C S hS :=
  ⟨arrowsObj G hfin, isAlgebraicSpace_arrowsObj G hfin⟩

/-- **The normalized groupoid `(U^ν, R^ν, s^ν, t^ν, c^ν)`** of a smooth groupoid in algebraic
spaces whose object space satisfies the conditions of Stacks 0BB1, as in the proof of
Stacks 0GMJ. -/
noncomputable def groupoid : GroupoidInAlgebraicSpaces C S hS B where
  objects := objectsSp G hfin
  arrows := arrowsSp G hfin
  objectsToBase := ObjectProperty.homMk ((data G hfin).hom ≫ G.objectsToBase.hom)
  arrowsToBase := ObjectProperty.homMk (proj G hfin ≫ G.arrowsToBase.hom)
  source := ObjectProperty.homMk (src G hfin)
  target := ObjectProperty.homMk (tgt G hG hfin)
  source_over := by
    apply ObjectProperty.hom_ext
    change src G hfin ≫ (data G hfin).hom ≫ G.objectsToBase.hom = proj G hfin ≫ G.arrowsToBase.hom
    rw [← Category.assoc, src_comp, Category.assoc,
      ← congrArg (fun k => k.hom) G.source_over]
    rfl
  target_over := by
    apply ObjectProperty.hom_ext
    change tgt G hG hfin ≫ (data G hfin).hom ≫ G.objectsToBase.hom =
      proj G hfin ≫ G.arrowsToBase.hom
    rw [← Category.assoc, tgt_comp, Category.assoc,
      ← congrArg (fun k => k.hom) G.target_over]
    rfl
  comp := ObjectProperty.homMk (comp G hG hfin)
  comp_over := by
    apply ObjectProperty.hom_ext
    change comp G hG hfin ≫ proj G hfin ≫ G.arrowsToBase.hom =
      pullback.fst (src G hfin) (tgt G hG hfin) ≫ proj G hfin ≫ G.arrowsToBase.hom
    rw [← congrArg (fun k => k.hom) G.target_over]
    change comp G hG hfin ≫ proj G hfin ≫ G.target.hom ≫ G.objectsToBase.hom =
      pullback.fst (src G hfin) (tgt G hG hfin) ≫ proj G hfin ≫ G.target.hom ≫
        G.objectsToBase.hom
    rw [comp_proj_assoc, ← Category.assoc, groupoidCompose_target]
    simp only [Category.assoc]
  pointwiseGroupoid T := ⟨pointwise G hG hfin T⟩

/-- **The morphism of groupoids `(U^ν, R^ν) ⟶ (U, R)`**, given by `ν` on objects and by the
projection `R^ν ⟶ R` on arrows. -/
noncomputable def hom : GroupoidInAlgebraicSpaces.Hom (groupoid G hG hfin) G where
  toGroupoidHom :=
    { mapObjects := (data G hfin).hom
      mapArrows := proj G hfin
      map_source := fun T a => (src_app_comp G hfin T a).symm
      map_target := fun T a => (tgt_app_comp G hG hfin T a).symm
      map_id := mapIdentityOfMapComp (G := (groupoid G hG hfin).toGroupoidInFunctors)
          (H := G.toGroupoidInFunctors) (data G hfin).hom (proj G hfin)
          (fun T a => (src_app_comp G hfin T a).symm)
          (fun T a => (tgt_app_comp G hG hfin T a).symm)
          (fun T a b h => by
            change _ = (proj G hfin).app T ((comp G hG hfin).app T
              ((composableToPullback (src G hfin) (tgt G hG hfin)).app T ⟨(a, b), h⟩))
            refine Eq.trans ?_ (comp_app_proj G hG hfin T _).symm
            refine compose_congr G T ?_ ?_ _ _
            · rw [pullbackFst_app_composableToPullback]; rfl
            · rw [pullbackSnd_app_composableToPullback]; rfl)
      map_comp := fun T a b h => by
        change _ = (proj G hfin).app T ((comp G hG hfin).app T
          ((composableToPullback (src G hfin) (tgt G hG hfin)).app T ⟨(a, b), h⟩))
        refine Eq.trans ?_ (comp_app_proj G hG hfin T _).symm
        refine compose_congr G T ?_ ?_ _ _
        · rw [pullbackFst_app_composableToPullback]; rfl
        · rw [pullbackSnd_app_composableToPullback]; rfl }
  mapObjects_over := rfl
  mapArrows_over := rfl

/-- The normalized groupoid is smooth. -/
theorem isSmooth : GroupoidInAlgebraicSpaces.IsSmooth C S hS (groupoid G hG hfin) :=
  ⟨isSmooth_src G hG hfin, isSmooth_tgt G hG hfin⟩

/-- The source square of the morphism of groupoids is cartesian: `R^ν = U^ν ×_{ν, U, s} R`. -/
theorem isPullback_source :
    IsPullback (hom G hG hfin).toGroupoidHom.mapArrows (groupoid G hG hfin).source.hom
      G.source.hom (hom G hG hfin).toGroupoidHom.mapObjects := by
  show IsPullback (proj G hfin) (src G hfin) G.source.hom (data G hfin).hom
  exact (IsPullback.of_hasPullback (data G hfin).hom G.source.hom).flip

end AlgebraicGeometry.GroupoidInAlgebraicSpaces.Normalized

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The normalized groupoid of a smooth groupoid `(U, R, s, t, c)` in algebraic spaces whose
object space satisfies the equivalent conditions of Stacks 0BB1, as an
`AlgebraicGeometry.Stack.NormalizationGroupoid`: `U^ν` is the normalization of `U`,
`R^ν = U^ν ×_{ν, U, s} R`, and the normalized groupoid is smooth. -/
noncomputable def normalizationGroupoid {G : GroupoidInAlgebraicSpaces C S hS B}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G)
    (hfin : Space.HasLocallyFiniteIrreducibleComponents C S hS G.objects.obj) :
    NormalizationGroupoid C S hS G where
  groupoid := GroupoidInAlgebraicSpaces.Normalized.groupoid G hG hfin
  hom := GroupoidInAlgebraicSpaces.Normalized.hom G hG hfin
  data := GroupoidInAlgebraicSpaces.Normalized.data G hfin
  objects_eq := rfl
  mapObjects_eq := (Category.id_comp (GroupoidInAlgebraicSpaces.Normalized.data G hfin).hom).symm
  isPullback_source := GroupoidInAlgebraicSpaces.Normalized.isPullback_source G hG hfin
  smooth := GroupoidInAlgebraicSpaces.Normalized.isSmooth G hG hfin

end AlgebraicGeometry.Stack

end
