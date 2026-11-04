module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubsetReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EquivalenceRelationFromCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.Equalizer
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre

/-!
# The equalizer of two elements of Artin's contraction functor

In the situation of Stacks 0GH8, recorded by
`AlgebraicGeometry.Artin.ContractionSituation`, let `V` be a scheme over `S` and let
`(Z₁, u'₁, x̂₁)` and `(Z₂, u'₂, x̂₂)` be two elements of `F(V)`, that is two values of
`AlgebraicGeometry.Artin.ContractionSituation.Triple`. Choose for each a witness of its
compatibility condition, consisting of `V'ᵢ ⟶ V`, `x̂'ᵢ` and `x'ᵢ`. **Stacks 0GHD** builds
from these data the fibre product `V' = V'₁ ×_V V'₂`, the equalizer `E' ⟶ V'` of the two
morphisms `V' ⟶ V'ᵢ ⟶ X'`, the closed set `Z = Z₁ ∩ Z₂` and the equalizer `E_W ⟶ V_{/Z}` of
the two morphisms `V_{/Z} ⟶ V_{/Zᵢ} ⟶ W`, and asserts five properties of them.

This file provides the constructions, assertions (1), (2) and (5), and the sentence of the
remark that `E' ⟶ V` is separated and locally of finite type.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionEqualizer`: the data the remark starts from, namely
  two triples over `V` together with a chosen compatibility witness for each.
* `AlgebraicGeometry.Artin.ContractionEqualizer.fibProd`: the fibre product `V' = V'₁ ×_V V'₂`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.eqz`: the equalizer `E'` of the two morphisms
  `V' ⟶ X'`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.toBase`: the morphism `E' ⟶ V`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.Z`: the closed set `Z = Z₁ ∩ Z₂`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.EW`: the equalizer `E_W ⟶ V_{/Z}` of the two
  morphisms `V_{/Z} ⟶ W`.

## Main results

* `AlgebraicGeometry.Artin.ContractionEqualizer.isSeparated_toBase` and
  `AlgebraicGeometry.Artin.ContractionEqualizer.isLocallyOfFiniteType_toBase`:
  **Stacks 0GHD**, the sentence "observe that `E' → V` is separated and locally of finite
  type".
* `AlgebraicGeometry.Artin.ContractionEqualizer.range_pointsMap_toBase_inter_union_subset`:
  **Stacks 0GHD**, assertion (1): the image of `E' ⟶ V` meets `Z₁ ∪ Z₂` only inside
  `Z = Z₁ ∩ Z₂`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.mono_pullbackSnd_offCenter` and
  `AlgebraicGeometry.Artin.ContractionEqualizer.exists_isLimit_fork_offCenter`:
  **Stacks 0GHD**, assertion (2): `E' ×_V (V ∖ Z) ⟶ V ∖ Z` is a monomorphism and is the
  equalizer of the restrictions of `u'₁` and `u'₂` to `V ∖ (Z₁ ∪ Z₂)`.
* `AlgebraicGeometry.Artin.ContractionSituation.Triple.eq_iff_of_Z_eq`: two triples over one
  object with the same first component are equal exactly when their second and third
  components are, stated through the restriction morphisms along the identity so that neither
  side's type depends on the first component.
* `AlgebraicGeometry.Artin.ContractionEqualizer.mapTriple_eq_iff_factorsOffCenter_and_factorsEW`:
  **Stacks 0GHD**, assertion (5): for `φ : A ⟶ V` the two triples restrict to the same element
  of `F(A)` if and only if `A ∖ φ⁻¹(Z) ⟶ V ∖ Z` factors through `E' ×_V (V ∖ Z)` and
  `A_{/φ⁻¹(Z)} ⟶ V_{/Z}` factors through `E_W`. Its geometric step, that the first condition
  forces `φ⁻¹(Z₁ ∪ Z₂) ⊆ φ⁻¹(Z)`, is
  `AlgebraicGeometry.Artin.ContractionEqualizer.union_subset_preZ_of_factorsOffCenter`.

## What is assumed

Nothing. In particular none of `V'`, `E'` or `E_W` is carried as a hypothesis:

* `V'` is the presheaf fibre product, an algebraic space over `S` by Stacks 02X2;
* `E'` is Mathlib's `CategoryTheory.Limits.equalizer` in the presheaf category, which has all
  limits, and it is an algebraic space over `S` by
  `AlgebraicGeometry.Space.isAlgebraicSpace_equalizer` — an equalizer is a base change of the
  diagonal, so this is Stacks 04T9 and needs no new construction;
* `E_W` is the equalizer in the category of fppf sheaves of `Type (u + 1)`, which likewise
  has all limits.

## Implementation notes

The two morphisms `V_{/Z} ⟶ V_{/Zᵢ} ⟶ W` whose equalizer is `E_W` are built with
`AlgebraicGeometry.Space.completionSheafRestrict` along the identity of `V`, which is defined
for any source set contained in the inverse image of the target set; for the identity that
inverse image is the target set itself, so `Z ⊆ Zᵢ` is exactly the hypothesis it wants and no
transport along an equality of sets of points is needed.

`V ∖ Z` and `V ∖ (Z₁ ∪ Z₂)` are the open subspaces
`AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by the complements, as everywhere in
this development, and the morphisms between them are `CategoryTheory.Subfunctor.homOfLe`
applied to `AlgebraicGeometry.Space.openSubspaceOfPoints_mono`, so that
`CategoryTheory.Subfunctor.homOfLe_ι` is available for them.

Assertion (2) names `E' ×_V (V ∖ Z)`, whose structure morphism to `V ∖ Z` is
`pullback.snd (toBase) ((V ∖ Z).ι)`. That this morphism *is* the equalizer of the two
restricted morphisms is recorded as the existence of a morphism to `V ∖ (Z₁ ∪ Z₂)` which
composes to it and is a limiting fork, rather than as an isomorphism with a chosen equalizer:
the two sides live over different open subspaces of `V` and the content of the assertion is
precisely that the comparison exists and is limiting. Its construction uses assertion (1):
a point of `E' ×_V (V ∖ Z)` cannot lie over `Z₁ ∪ Z₂`, because its image lies outside
`Z = Z₁ ∩ Z₂` and assertion (1) confines the image of `E'` inside `Z₁ ∪ Z₂` to `Z`.

Everything here is proved for an arbitrary object `V` of the big fppf site over `S`. The remark
takes `V` to be a locally Noetherian scheme over `S`, but local Noetherianness is used nowhere, so
the remark's statement is the special case `V := V.obj` for a locally Noetherian object of that
site, which is how `AlgebraicGeometry.Artin.contractionFunctor` presents `F`.

## The other assertions

The factorization and the cartesian square of assertion (3), and the separatedness of `E_W ⟶ V`,
are proved in `StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerCompletion`. The closing
sentence of assertion (3) — that `E'_{/Z} ⟶ E_W` is a formal modification, as the base change of
`g` along `E_W ⟶ W` — and assertion (4) both require `E_W` to be a *locally Noetherian formal
algebraic space*, which is also the other half of the remark's "observe" sentence. All three are
proved in `StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerSituation` (by Stacks 0AIP, 0AQ8
and 0GDN).

Assertion (5) speaks only of a morphism `A_{/φ⁻¹(Z)} ⟶ V_{/Z}` factoring through `E_W`, and `E_W`
is constructed here as the equalizer in the category of fppf sheaves, where formal algebraic spaces
over `S` live, so its proof does not need `E_W` to be a formal algebraic space.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 04T9](https://stacks.math.columbia.edu/tag/04T9)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A field-valued point of a presheaf on the big fppf site of `S` lies in a set `T` of
points exactly when its own section has point-set image in `T`.

One direction tests the point-set image at the tautological field-valued point of the site
object; the other uses that every field-valued point of the spectrum of a field is carried to
the point itself by that point's section, which is
`AlgebraicGeometry.Space.FieldValuedPoint.pointsMap_class_eq_class`. -/
theorem hasImageIn_iff_class_mem (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (points B S hS X)) (p : FieldValuedPoint B S hS X) :
    HasImageIn B S hS X T p.siteObject p.value ↔ p.class B S hS X ∈ T := by
  refine ⟨fun h => ?_, fun h r => ?_⟩
  · have hr : (FieldValuedPoint.map B S hS (yoneda.obj p.siteObject)
        (yonedaEquiv.symm p.value) (FieldValuedPoint.tautological B S hS p)).class
          B S hS X ∈ T := h _
    rwa [FieldValuedPoint.map_tautological] at hr
  · have hval : (⟨r.carrier, r.contained, r.toBase, X.map r.value.op p.value⟩ :
        FieldValuedPoint B S hS X) =
        FieldValuedPoint.map B S hS (yoneda.obj p.siteObject)
          (yonedaEquiv.symm p.value) r := rfl
    rwa [hval, ← pointsMap_class, FieldValuedPoint.pointsMap_class_eq_class]

/-- A point of `G` whose section is the image of a section of `F` lies in the image on points
of `f : F ⟶ G`. -/
theorem class_mem_range_pointsMap_of_app_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (p : FieldValuedPoint B S hS G) (x : F.obj (Opposite.op p.siteObject))
    (hx : f.app (Opposite.op p.siteObject) x = p.value) :
    p.class B S hS G ∈ Set.range (pointsMap B S hS F f) := by
  refine ⟨(⟨p.carrier, p.contained, p.toBase, x⟩ :
    FieldValuedPoint B S hS F).class B S hS F, ?_⟩
  rw [pointsMap_class]
  congr 1
  obtain ⟨K, hK, tb, v⟩ := p
  exact congrArg (fun y => (⟨K, hK, tb, y⟩ : FieldValuedPoint B S hS G)) hx

/-! ### Composing the subset-form restriction morphisms with an inclusion

The restriction morphisms of `AlgebraicGeometry.Space.openSubspaceOfPointsRestrict` and
`AlgebraicGeometry.Space.completionSheafRestrict` take a *subset* of the inverse image as
hypothesis rather than the inverse image itself, so enlarging or shrinking the set of points
is composition with a restriction along the identity and no transport along an equality of
sets of points is needed. The four lemmas below are that composition in the two orders. -/

section RestrictComp

variable {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A subset of a set of points is contained in its inverse image under the identity. -/
theorem subset_preimage_pointsMap_id {W' W : Set (points B S hS F)} (h : W' ⊆ W) :
    W' ⊆ pointsMap B S hS F (𝟙 F) ⁻¹' W := by
  simpa only [pointsMap_id, Set.preimage_id] using h

/-- A point in the inverse image of a set of points under the identity is in that set. -/
theorem mem_of_mem_preimage_pointsMap_id {W : Set (points B S hS F)}
    {x : points B S hS F} (h : x ∈ pointsMap B S hS F (𝟙 F) ⁻¹' W) : x ∈ W := by
  simpa only [pointsMap_id, Set.preimage_id] using h

/-- Transitivity of the inverse-image containments, with the identity on the left. -/
theorem subset_preimage_trans_id_left {W'' W' : Set (points B S hS F')}
    {W : Set (points B S hS F)} {f : F' ⟶ F}
    (h₁ : W'' ⊆ pointsMap B S hS F' (𝟙 F') ⁻¹' W')
    (h₂ : W' ⊆ pointsMap B S hS F' f ⁻¹' W) : W'' ⊆ pointsMap B S hS F' f ⁻¹' W :=
  fun _ hx => h₂ (mem_of_mem_preimage_pointsMap_id B S hS (h₁ hx))

/-- Transitivity of the inverse-image containments, with the identity on the right. -/
theorem subset_preimage_trans_id_right {W' : Set (points B S hS F')}
    {W'' W : Set (points B S hS F)} {f : F' ⟶ F}
    (h₁ : W' ⊆ pointsMap B S hS F' f ⁻¹' W'')
    (h₂ : W'' ⊆ pointsMap B S hS F (𝟙 F) ⁻¹' W) : W' ⊆ pointsMap B S hS F' f ⁻¹' W :=
  fun _ hx => mem_of_mem_preimage_pointsMap_id B S hS (W := W) (h₂ (h₁ hx))

/-- Restricting along `𝟙 F'` and then along `f` is restricting along `f`, for open subspaces. -/
@[reassoc]
theorem openSubspaceOfPointsRestrict_id_comp (f : F' ⟶ F) (W'' W' : Set (points B S hS F'))
    (W : Set (points B S hS F)) (h₁ : W'' ⊆ pointsMap B S hS F' (𝟙 F') ⁻¹' W')
    (h₂ : W' ⊆ pointsMap B S hS F' f ⁻¹' W) :
    openSubspaceOfPointsRestrict B S hS (𝟙 F') W'' W' h₁ ≫
        openSubspaceOfPointsRestrict B S hS f W' W h₂ =
      openSubspaceOfPointsRestrict B S hS f W'' W
        (subset_preimage_trans_id_left B S hS h₁ h₂) :=
  ((openSubspaceOfPointsRestrict_comp B S hS (𝟙 F') f W'' W' W h₁ h₂
    (by simpa only [Category.id_comp] using
      subset_preimage_trans_id_left B S hS h₁ h₂)).symm).trans
      (openSubspaceOfPointsRestrict_congr B S hS (Category.id_comp f) W'' W _ _)

/-- Restricting along `f` and then along `𝟙 F` is restricting along `f`, for open subspaces. -/
@[reassoc]
theorem openSubspaceOfPointsRestrict_comp_id (f : F' ⟶ F) (W' : Set (points B S hS F'))
    (W'' W : Set (points B S hS F)) (h₁ : W' ⊆ pointsMap B S hS F' f ⁻¹' W'')
    (h₂ : W'' ⊆ pointsMap B S hS F (𝟙 F) ⁻¹' W) :
    openSubspaceOfPointsRestrict B S hS f W' W'' h₁ ≫
        openSubspaceOfPointsRestrict B S hS (𝟙 F) W'' W h₂ =
      openSubspaceOfPointsRestrict B S hS f W' W
        (subset_preimage_trans_id_right B S hS h₁ h₂) :=
  ((openSubspaceOfPointsRestrict_comp B S hS f (𝟙 F) W' W'' W h₁ h₂
    (by simpa only [Category.comp_id] using
      subset_preimage_trans_id_right B S hS h₁ h₂)).symm).trans
      (openSubspaceOfPointsRestrict_congr B S hS (Category.comp_id f) W' W _ _)

/-- Restricting along `𝟙 F'` and then along `f` is restricting along `f`, for completions. -/
@[reassoc]
theorem completionSheafRestrict_id_comp (f : F' ⟶ F) (T'' T' : Set (points B S hS F'))
    (T : Set (points B S hS F)) (h₁ : T'' ⊆ pointsMap B S hS F' (𝟙 F') ⁻¹' T')
    (h₂ : T' ⊆ pointsMap B S hS F' f ⁻¹' T) :
    completionSheafRestrict B S hS (𝟙 F') T'' T' h₁ ≫
        completionSheafRestrict B S hS f T' T h₂ =
      completionSheafRestrict B S hS f T'' T
        (subset_preimage_trans_id_left B S hS h₁ h₂) :=
  ((completionSheafRestrict_comp B S hS (𝟙 F') f T'' T' T h₁ h₂
    (by simpa only [Category.id_comp] using
      subset_preimage_trans_id_left B S hS h₁ h₂)).symm).trans
      (completionSheafRestrict_congr B S hS (Category.id_comp f) T'' T _ _)

/-- Restricting along `f` and then along `𝟙 F` is restricting along `f`, for completions. -/
@[reassoc]
theorem completionSheafRestrict_comp_id (f : F' ⟶ F) (T' : Set (points B S hS F'))
    (T'' T : Set (points B S hS F)) (h₁ : T' ⊆ pointsMap B S hS F' f ⁻¹' T'')
    (h₂ : T'' ⊆ pointsMap B S hS F (𝟙 F) ⁻¹' T) :
    completionSheafRestrict B S hS f T' T'' h₁ ≫
        completionSheafRestrict B S hS (𝟙 F) T'' T h₂ =
      completionSheafRestrict B S hS f T' T
        (subset_preimage_trans_id_right B S hS h₁ h₂) :=
  ((completionSheafRestrict_comp B S hS f (𝟙 F) T' T'' T h₁ h₂
    (by simpa only [Category.comp_id] using
      subset_preimage_trans_id_right B S hS h₁ h₂)).symm).trans
      (completionSheafRestrict_congr B S hS (Category.comp_id f) T' T _ _)

/-- The inclusion of one open subspace cut out by a set of points into another is the
restriction morphism along the identity. -/
theorem homOfLe_openSubspaceOfPoints (W' W : Set (points B S hS F)) (hW : W' ⊆ W)
    (h : W' ⊆ pointsMap B S hS F (𝟙 F) ⁻¹' W) :
    Subfunctor.homOfLe (openSubspaceOfPoints_mono B S hS hW) =
      openSubspaceOfPointsRestrict B S hS (𝟙 F) W' W h := rfl

/-- Restricting along `f` and then including a smaller open subspace into a larger one is
restricting along `f` into the larger one. -/
private theorem openSubspaceOfPointsRestrict_comp_homOfLe (f : F' ⟶ F)
    (W'' : Set (points B S hS F')) (W' W : Set (points B S hS F)) (hW : W' ⊆ W)
    (h : W'' ⊆ pointsMap B S hS F' f ⁻¹' W')
    (h' : W'' ⊆ pointsMap B S hS F' f ⁻¹' W) :
    openSubspaceOfPointsRestrict B S hS f W'' W' h ≫
        Subfunctor.homOfLe (openSubspaceOfPoints_mono B S hS hW) =
      openSubspaceOfPointsRestrict B S hS f W'' W h' := by
  rw [homOfLe_openSubspaceOfPoints B S hS W' W hW (subset_preimage_pointsMap_id B S hS hW),
    openSubspaceOfPointsRestrict_comp_id]

end RestrictComp

/-- The two names this library has for the morphism `X_{/T} ⟶ X` into the universe lift of an
fppf sheaf `X` of `Type u` agree: both restrict along the unit of the sheafification to the
inclusion of the completion subfunctor. -/
theorem completionToULift_eq_completionSheafToAmbient {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hXus : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    (T : Set (points B S hS X)) :
    FormalSpace.completionToULift B S hS X hX T = completionSheafToAmbient B S hS X hXus T := by
  refine (BigFppfOver.topology B S hS).sheafify_hom_ext _ _ hXus ?_
  rw [toSheafify_comp_completionSheafToAmbient]
  exact FormalSpace.toSheafify_comp_completionToULift B S hS X hX T

end Space

namespace Artin

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ContractionSituation

variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}

/-- The compatibility of `x'` with `x̂'` in a compatibility witness, read as an equation of
morphisms into the universe lift of `X'` rather than into its sheafification. -/
theorem CompatibilityWitness.completionToULift_comp_whiskerRight
    (w : CompatibilityWitness c V Z u xhat) :
    FormalSpace.completionToULift B S hS w.V' w.isAlgebraicSpace_V'.isSheaf
          (Space.pointsMap B S hS w.V' w.p ⁻¹' Z) ≫
        Functor.whiskerRight w.x' uliftFunctor.{u + 1} =
      w.xhat'.hom ≫ FormalSpace.completionToULift B S hS c.X'
        c.isAlgebraicSpace_X'.isSheaf c.T' := by
  have hw := congrArg (fun φ : Space.completionSheaf B S hS w.V'
      (Space.pointsMap B S hS w.V' w.p ⁻¹' Z) ⟶ Space.sheafifiedULift B S hS c.X' => φ.hom)
    w.completion_x'
  rw [← cancel_mono (Space.sheafifiedULiftIso B S hS c.X' c.isAlgebraicSpace_X'.isSheaf).hom]
  simp only [FormalSpace.completionToULift, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Space.sheafifiedULiftMap_hom_eq B S hS w.isAlgebraicSpace_V'.isSheaf
    c.isAlgebraicSpace_X'.isSheaf w.x']
  exact hw

/-- **A field-valued point of `V'` whose image in `V` lies in `Z` is carried into `T'` by
`x'`.** This is one of the two compatibilities Stacks 0GHD invokes for its assertion (1).

The point's own section lies in the completion subfunctor of `V'` along the inverse image of
`Z`, so it gives a morphism from the spectrum of the field into the completion `V'_{/Z}`;
composing with `x̂' : V'_{/Z} ⟶ X'_{/T'}` exhibits the image section as a scheme-valued point
of the completion `X'_{/T'}`, whose point-set image lies in `T'` by
`AlgebraicGeometry.Space.range_pointsMap_subset_of_whiskerRight_eq`. -/
theorem CompatibilityWitness.class_map_witnessMap_mem_closedSubset
    (w : CompatibilityWitness c V Z u xhat)
    (q : Space.FieldValuedPoint B S hS w.V')
    (hq : Space.pointsMap B S hS w.V' w.p (q.class B S hS w.V') ∈ Z) :
    (Space.FieldValuedPoint.map B S hS w.V' w.x' q).class B S hS c.X' ∈ c.T' := by
  have hV'us := FormalSpace.isSheaf_comp_uliftFunctor B S hS w.isAlgebraicSpace_V'
  have hX'us := FormalSpace.isSheaf_comp_uliftFunctor B S hS c.isAlgebraicSpace_X'
  have hA : Space.HasImageIn B S hS w.V' (Space.pointsMap B S hS w.V' w.p ⁻¹' Z)
      q.siteObject q.value :=
    (Space.hasImageIn_iff_class_mem B S hS w.V' _ q).2 hq
  -- the section `q.value` as a section of the completion subfunctor, and the morphism
  -- `Spec(k) ⟶ X'_{/T'}` it induces
  set z₁ : (Space.completionSubfunctor B S hS w.V'
      (Space.pointsMap B S hS w.V' w.p ⁻¹' Z)).toFunctor.obj (Opposite.op q.siteObject) :=
    ⟨ULift.up q.value, hA⟩ with hz₁
  set g : uliftYoneda.{u + 1}.obj q.siteObject ⟶
      (Space.completionSheaf B S hS c.X' c.T').obj :=
    uliftYonedaEquiv.symm z₁ ≫
      FormalSpace.toCompletionSheaf B S hS w.V'
        (Space.pointsMap B S hS w.V' w.p ⁻¹' Z) ≫ w.xhat'.hom with hg
  -- the induced morphism `Spec(k) ⟶ X'` and the compatibility it satisfies
  have hgs : Functor.whiskerRight (yonedaEquiv.symm q.value ≫ w.x') uliftFunctor.{u + 1} =
      g ≫ Space.completionSheafToAmbient B S hS c.X' hX'us c.T' := by
    rw [hg, Category.assoc, Category.assoc,
      ← Space.completionToULift_eq_completionSheafToAmbient B S hS
        c.isAlgebraicSpace_X'.isSheaf hX'us c.T',
      ← CompatibilityWitness.completionToULift_comp_whiskerRight w,
      show FormalSpace.toCompletionSheaf B S hS w.V'
            (Space.pointsMap B S hS w.V' w.p ⁻¹' Z) ≫
          (FormalSpace.completionToULift B S hS w.V' w.isAlgebraicSpace_V'.isSheaf
            (Space.pointsMap B S hS w.V' w.p ⁻¹' Z) ≫
              Functor.whiskerRight w.x' uliftFunctor.{u + 1}) =
          (Space.completionSubfunctor B S hS w.V'
            (Space.pointsMap B S hS w.V' w.p ⁻¹' Z)).ι ≫
              Functor.whiskerRight w.x' uliftFunctor.{u + 1} from by
        rw [← Category.assoc, FormalSpace.toSheafify_comp_completionToULift]]
    rw [Functor.whiskerRight_comp, ← Category.assoc]
    refine congrArg (· ≫ Functor.whiskerRight w.x' uliftFunctor.{u + 1}) ?_
    rw [uliftYonedaEquiv_symm_comp]
    rfl
  have hsub := Space.range_pointsMap_subset_of_whiskerRight_eq B S hS c.T' hX'us g hgs
  refine hsub ⟨(Space.FieldValuedPoint.tautological B S hS q).class B S hS _, ?_⟩
  rw [show (yonedaEquiv.symm q.value ≫ w.x' :
        yoneda.obj q.siteObject ⟶ c.X') =
      yonedaEquiv.symm (Space.FieldValuedPoint.map B S hS w.V' w.x' q).value from
    yonedaEquiv_symm_naturality_right _ w.x' q.value]
  exact Space.FieldValuedPoint.pointsMap_eq_class B S hS
    (Space.FieldValuedPoint.map B S hS w.V' w.x' q) _

/-- The first component of a transported triple, by construction of
`AlgebraicGeometry.Artin.ContractionSituation.mapTriple`. -/
theorem mapTriple_Z {c : ContractionSituation B S hS} {V₂ V₁ : BigFppfOver B S hS}
    (φ : V₂ ⟶ V₁) (t : Triple c V₁) :
    (mapTriple c φ t).Z =
      Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Z := rfl

/-- **Two triples over the same object with the same first component are equal exactly when
their second and third components are.** The comparison morphisms are the restrictions along
the identity, which for equal sets of points are identities; stating the criterion with them
rather than with `HEq` keeps both sides in types that do not depend on the first component. -/
theorem Triple.eq_iff_of_Z_eq {c : ContractionSituation B S hS} {A : BigFppfOver B S hS}
    {t t' : Triple c A} (hZ : t.Z = t'.Z) :
    t = t' ↔
      (Space.openSubspaceOfPointsRestrict B S hS (𝟙 (yoneda.obj A)) t.Zᶜ t'.Zᶜ
          (by
            simpa only [Space.pointsMap_id, Set.preimage_id] using
              Set.compl_subset_compl.2 hZ.symm.subset) ≫ t'.u =
        t.u) ∧
      (Space.completionSheafRestrict B S hS (𝟙 (yoneda.obj A)) t.Z t'.Z
          (by simpa only [Space.pointsMap_id, Set.preimage_id] using hZ.subset) ≫ t'.xhat =
        t.xhat) := by
  refine ⟨fun h => ?_, ?_⟩
  · subst h
    refine ⟨Category.id_comp t.u, ?_⟩
    rw [Space.completionSheafRestrict_id, Category.id_comp]
  · obtain ⟨Z₁, hc₁, u₁, x₁, a₁, w₁⟩ := t
    obtain ⟨Z₂, hc₂, u₂, x₂, a₂, w₂⟩ := t'
    dsimp only at hZ ⊢
    subst hZ
    rintro ⟨hu, hx⟩
    rw [Space.completionSheafRestrict_id, Category.id_comp] at hx
    exact Triple.mk_congr rfl (heq_of_eq hu.symm) (heq_of_eq hx.symm)

/-- **A field-valued point of `V'` whose image in `V` lies outside `Z` is carried outside
`T'` by `x'`.** This is the second of the two compatibilities Stacks 0GHD invokes for its
assertion (1).

The image point lies in the open subspace `V ∖ Z`, over which `p : V' ⟶ V` is an isomorphism
with `j` as the identification; so the point of `V'` comes from `V ∖ Z` along `j`, and `x'`
restricted along `j` is `u' : V ∖ Z ⟶ U'`, whose point set is the complement of `T'`. -/
theorem CompatibilityWitness.class_map_witnessMap_mem_compl_closedSubset
    (w : CompatibilityWitness c V Z u xhat)
    (q : Space.FieldValuedPoint B S hS w.V')
    (hq : Space.pointsMap B S hS w.V' w.p (q.class B S hS w.V') ∉ Z) :
    (Space.FieldValuedPoint.map B S hS w.V' w.x' q).class B S hS c.X' ∈ c.T'ᶜ := by
  -- the image section lies in the open subspace `V ∖ Z`
  have hopen : (Space.FieldValuedPoint.map B S hS w.V' w.p q).value ∈
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).obj
        (Opposite.op q.siteObject) := by
    rintro y ⟨z, rfl⟩
    exact Set.mem_of_eq_of_mem
      (Space.FieldValuedPoint.pointsMap_eq_class B S hS
        (Space.FieldValuedPoint.map B S hS w.V' w.p q) z) hq
  -- hence the point of `V'` comes from `V ∖ Z` along `j`
  have hpb := w.isPullback_j.map
    ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj (Opposite.op q.siteObject))
  simp only [evaluation_obj_map] at hpb
  obtain ⟨o, -, ho⟩ := Types.exists_of_isPullback hpb
    ⟨(Space.FieldValuedPoint.map B S hS w.V' w.p q).value, hopen⟩ q.value rfl
  -- and `x'` on it is `u'` followed by the inclusion of `U'`
  have hx : (Space.FieldValuedPoint.map B S hS w.V' w.x' q).value =
      c.U'.ι.app (Opposite.op q.siteObject) (u.app (Opposite.op q.siteObject) o) := by
    have hc := congrArg (fun f : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor
      ⟶ c.X' => f.app (Opposite.op q.siteObject) o) w.restrict_x'
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hc
    rw [show (Space.FieldValuedPoint.map B S hS w.V' w.x' q).value =
      w.x'.app (Opposite.op q.siteObject) q.value from rfl, ← ho]
    exact hc
  rw [← c.range_pointsMap_ι_U']
  exact Space.class_mem_range_pointsMap_of_app_eq B S hS c.U'.ι
    (Space.FieldValuedPoint.map B S hS w.V' w.x' q)
    (u.app (Opposite.op q.siteObject) o) hx.symm

end ContractionSituation

open ContractionSituation in
/-- The data Stacks 0GHD starts from: two elements `(Zᵢ, u'ᵢ, x̂ᵢ)` of `F(V)` together with a
choice, for each, of the witness `V'ᵢ ⟶ V`, `x̂'ᵢ`, `x'ᵢ` of its compatibility condition.

The remark's `V'`, `E'`, `Z` and `E_W` are all *constructed* from these data; see
`AlgebraicGeometry.Artin.ContractionEqualizer.fibProd`,
`AlgebraicGeometry.Artin.ContractionEqualizer.eqz`,
`AlgebraicGeometry.Artin.ContractionEqualizer.Z` and
`AlgebraicGeometry.Artin.ContractionEqualizer.EW`. -/
structure ContractionEqualizer (c : ContractionSituation B S hS) (V : BigFppfOver B S hS)
    where
  /-- The first element `(Z₁, u'₁, x̂₁)` of `F(V)`. -/
  t₁ : Triple c V
  /-- The second element `(Z₂, u'₂, x̂₂)` of `F(V)`. -/
  t₂ : Triple c V
  /-- The chosen witness `V'₁ ⟶ V`, `x̂'₁`, `x'₁` of the compatibility of `u'₁` and `x̂₁`. -/
  w₁ : CompatibilityWitness c V t₁.Z t₁.u t₁.xhat
  /-- The chosen witness `V'₂ ⟶ V`, `x̂'₂`, `x'₂` of the compatibility of `u'₂` and `x̂₂`. -/
  w₂ : CompatibilityWitness c V t₂.Z t₂.u t₂.xhat

namespace ContractionEqualizer

variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V)

/-! ### The fibre product `V' = V'₁ ×_V V'₂` -/

/-- The fibre product `V' = V'₁ ×_V V'₂` of the two chosen compatibility witnesses. -/
abbrev fibProd : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := pullback d.w₁.p d.w₂.p

/-- `V'` is an algebraic space over `S`, by Stacks 02X2. -/
theorem isAlgebraicSpace_fibProd : IsAlgebraicSpace B S hS d.fibProd :=
  isAlgebraicSpace_pullback B S hS d.w₁.p d.w₂.p d.w₁.isAlgebraicSpace_V'
    d.w₂.isAlgebraicSpace_V' (isAlgebraicSpace_yoneda B S hS V)

/-- The first of the two morphisms `V' ⟶ V'₁ ⟶ X'` whose equalizer is `E'`. -/
def x₁ : d.fibProd ⟶ c.X' := pullback.fst d.w₁.p d.w₂.p ≫ d.w₁.x'

/-- The second of the two morphisms `V' ⟶ V'₂ ⟶ X'` whose equalizer is `E'`. -/
def x₂ : d.fibProd ⟶ c.X' := pullback.snd d.w₁.p d.w₂.p ≫ d.w₂.x'

/-! ### The equalizer `E' ⟶ V'` -/

/-- The equalizer `E' ⟶ V'` of the two morphisms `V' ⟶ V'ᵢ ⟶ X'`. -/
abbrev eqz : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := equalizer d.x₁ d.x₂

/-- `E'` is an algebraic space over `S`: an equalizer is a base change of the diagonal of
`X'`, so this is Stacks 04T9. -/
theorem isAlgebraicSpace_eqz : IsAlgebraicSpace B S hS d.eqz :=
  Space.isAlgebraicSpace_equalizer B S hS d.isAlgebraicSpace_fibProd c.isAlgebraicSpace_X' _ _

/-- The structure morphism `E' ⟶ V` of the remark, the composite of `E' ⟶ V'`, the first
projection `V' ⟶ V'₁` and `V'₁ ⟶ V`. -/
def toBase : d.eqz ⟶ yoneda.obj V :=
  equalizer.ι d.x₁ d.x₂ ≫ pullback.fst d.w₁.p d.w₂.p ≫ d.w₁.p

/-- The morphism `E' ⟶ V'₁`, the equalizer inclusion followed by the first projection. -/
def toFst : d.eqz ⟶ d.w₁.V' := equalizer.ι d.x₁ d.x₂ ≫ pullback.fst d.w₁.p d.w₂.p

/-- The morphism `E' ⟶ V'₂`, the equalizer inclusion followed by the second projection. -/
def toSnd : d.eqz ⟶ d.w₂.V' := equalizer.ι d.x₁ d.x₂ ≫ pullback.snd d.w₁.p d.w₂.p

/-- The composite `E' ⟶ V'₁ ⟶ V` is the structure morphism `E' ⟶ V`. -/
@[simp]
theorem toFst_comp_p : d.toFst ≫ d.w₁.p = d.toBase := by
  rw [toFst, toBase, Category.assoc]

/-- The composite `E' ⟶ V'₂ ⟶ V` is the structure morphism `E' ⟶ V`. -/
@[simp]
theorem toSnd_comp_p : d.toSnd ≫ d.w₂.p = d.toBase := by
  rw [toSnd, toBase, Category.assoc, pullback.condition]

/-- The two morphisms `E' ⟶ V'ᵢ ⟶ X'` agree, `E'` being their equalizer. -/
theorem toFst_comp_witnessMap_eq : d.toFst ≫ d.w₁.x' = d.toSnd ≫ d.w₂.x' := by
  rw [toFst, toSnd, Category.assoc, Category.assoc]
  exact equalizer.condition d.x₁ d.x₂

/-! ### The closed set `Z = Z₁ ∩ Z₂` -/

/-- The closed set `Z = Z₁ ∩ Z₂` of the remark. -/
def Z : Set (Space.points B S hS (yoneda.obj V)) := d.t₁.Z ∩ d.t₂.Z

/-- `Z = Z₁ ∩ Z₂` is closed. -/
theorem isClosed_Z : IsClosed d.Z := d.t₁.isClosed_Z.inter d.t₂.isClosed_Z

/-- `Z = Z₁ ∩ Z₂` is contained in `Z₁`. -/
theorem Z_subset_t₁ : d.Z ⊆ d.t₁.Z := Set.inter_subset_left

/-- `Z = Z₁ ∩ Z₂` is contained in `Z₂`. -/
theorem Z_subset_t₂ : d.Z ⊆ d.t₂.Z := Set.inter_subset_right

/-! ### The equalizer `E_W ⟶ V_{/Z}` -/

/-- The first of the two morphisms `V_{/Z} ⟶ V_{/Z₁} ⟶ W` whose equalizer is `E_W`. -/
def xhat₁ : Space.completionSheaf B S hS (yoneda.obj V) d.Z ⟶ c.W :=
  Space.completionSheafRestrict B S hS (𝟙 _) d.Z d.t₁.Z
    (by simpa only [Space.pointsMap_id, Set.preimage_id] using d.Z_subset_t₁) ≫ d.t₁.xhat

/-- The second of the two morphisms `V_{/Z} ⟶ V_{/Z₂} ⟶ W` whose equalizer is `E_W`. -/
def xhat₂ : Space.completionSheaf B S hS (yoneda.obj V) d.Z ⟶ c.W :=
  Space.completionSheafRestrict B S hS (𝟙 _) d.Z d.t₂.Z
    (by simpa only [Space.pointsMap_id, Set.preimage_id] using d.Z_subset_t₂) ≫ d.t₂.xhat

/-- The equalizer `E_W ⟶ V_{/Z}` of the two morphisms `V_{/Z} ⟶ V_{/Zᵢ} ⟶ W`, taken in the
category of fppf sheaves of `Type (u + 1)` on the big fppf site of `S`. -/
abbrev EW : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  equalizer d.xhat₁ d.xhat₂

/-! ### Assertion (1): the image of `E' ⟶ V` -/

/-- **Stacks 0GHD**, assertion (1): the image of `E' ⟶ V` meets `Z₁ ∪ Z₂` only inside
`Z = Z₁ ∩ Z₂`.

A field-valued point of `E'` lying over `Z₁` is carried by `x'₁` into `T'`, and if it did not
lie over `Z₂` it would be carried by `x'₂` outside `T'`; but the two images agree, `E'` being
the equalizer. The argument is symmetric in the two indices. -/
@[stacks 0GHD "assertion (1), in full: that Im(E' → V) ∩ (Z₁ ∪ Z₂) is contained in \
Z = Z₁ ∩ Z₂, for the fibre product V' = V'₁ ×_V V'₂ and the equalizer E' ⟶ V' that this file \
constructs from two elements of F(V) and a chosen compatibility witness for each. Proved with \
no hypothesis on V beyond its being an object of the big fppf site over S, so the tag's own \
hypothesis that V be a locally Noetherian scheme over S is the special case V := V.obj for a \
locally Noetherian object V of that site"]
theorem range_pointsMap_toBase_inter_union_subset :
    Set.range (Space.pointsMap B S hS d.eqz d.toBase) ∩ (d.t₁.Z ∪ d.t₂.Z) ⊆ d.Z := by
  rintro y ⟨⟨z, rfl⟩, hy⟩
  induction z using Quot.ind with | _ q => ?_
  have hm : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : d.eqz ⟶ Y) (g : Y ⟶ yoneda.obj V),
      f ≫ g = d.toBase → Space.pointsMap B S hS Y g
        ((Space.FieldValuedPoint.map B S hS d.eqz f q).class B S hS Y) =
      Space.pointsMap B S hS d.eqz d.toBase (q.class B S hS d.eqz) := fun f g h => by
    rw [Space.pointsMap_class, ← Space.FieldValuedPoint.map_comp, h,
      ← Space.pointsMap_class B S hS d.eqz d.toBase q]
  have heq : (Space.FieldValuedPoint.map B S hS d.w₁.V' d.w₁.x'
        (Space.FieldValuedPoint.map B S hS d.eqz d.toFst q)).class B S hS c.X' =
      (Space.FieldValuedPoint.map B S hS d.w₂.V' d.w₂.x'
        (Space.FieldValuedPoint.map B S hS d.eqz d.toSnd q)).class B S hS c.X' := by
    rw [← Space.FieldValuedPoint.map_comp, ← Space.FieldValuedPoint.map_comp,
      d.toFst_comp_witnessMap_eq]
  have hm₁ := hm d.toFst d.w₁.p d.toFst_comp_p
  have hm₂ := hm d.toSnd d.w₂.p d.toSnd_comp_p
  rcases hy with h₁ | h₂
  · exact ⟨h₁, by_contra fun h => d.w₂.class_map_witnessMap_mem_compl_closedSubset _
      (by rwa [hm₂]) (heq ▸ d.w₁.class_map_witnessMap_mem_closedSubset _ (by rwa [hm₁]))⟩
  · exact ⟨by_contra fun h => d.w₁.class_map_witnessMap_mem_compl_closedSubset _
      (by rwa [hm₁]) (heq ▸ d.w₂.class_map_witnessMap_mem_closedSubset _ (by rwa [hm₂])), h₂⟩

/-! ### Assertion (2): the equalizer away from `Z` -/

section OffCenter

/-- The open subspace `V ∖ Z` of `V`. -/
abbrev offCenter : Subfunctor (yoneda.obj V) :=
  Space.openSubspaceOfPoints B S hS (yoneda.obj V) d.Zᶜ

/-- The open subspace `V ∖ (Z₁ ∪ Z₂)` of `V`. -/
abbrev offBoth : Subfunctor (yoneda.obj V) :=
  Space.openSubspaceOfPoints B S hS (yoneda.obj V) (d.t₁.Z ∪ d.t₂.Z)ᶜ

/-- `V ∖ (Z₁ ∪ Z₂)` is contained in `V ∖ Z`. -/
theorem offBoth_le_offCenter : d.offBoth ≤ d.offCenter :=
  Space.openSubspaceOfPoints_mono B S hS
    (Set.compl_subset_compl.2 fun _ h => Or.inl h.1)

/-- `V ∖ (Z₁ ∪ Z₂)` is contained in `V ∖ Z₁`. -/
theorem offBoth_le_fst : d.offBoth ≤ Space.openSubspaceOfPoints B S hS (yoneda.obj V) d.t₁.Zᶜ :=
  Space.openSubspaceOfPoints_mono B S hS
    (Set.compl_subset_compl.2 fun _ h => Or.inl h)

/-- `V ∖ (Z₁ ∪ Z₂)` is contained in `V ∖ Z₂`. -/
theorem offBoth_le_snd : d.offBoth ≤ Space.openSubspaceOfPoints B S hS (yoneda.obj V) d.t₂.Zᶜ :=
  Space.openSubspaceOfPoints_mono B S hS
    (Set.compl_subset_compl.2 fun _ h => Or.inr h)

/-- The restriction of `u'₁` to `V ∖ (Z₁ ∪ Z₂)`, followed by the inclusion `U' ⟶ X'`. -/
def restrictedMap₁ : d.offBoth.toFunctor ⟶ c.X' :=
  Subfunctor.homOfLe d.offBoth_le_fst ≫ d.t₁.u ≫ c.U'.ι

/-- The restriction of `u'₂` to `V ∖ (Z₁ ∪ Z₂)`, followed by the inclusion `U' ⟶ X'`. -/
def restrictedMap₂ : d.offBoth.toFunctor ⟶ c.X' :=
  Subfunctor.homOfLe d.offBoth_le_snd ≫ d.t₂.u ≫ c.U'.ι

/-- The image of `E' ×_V (V ∖ Z) ⟶ V` avoids `Z₁ ∪ Z₂`: it lands in the image of `E' ⟶ V`
and in `V ∖ Z`, and by assertion (1) those two meet `Z₁ ∪ Z₂` only inside `Z`. -/
theorem range_le_offBoth :
    Subfunctor.range (pullback.fst d.toBase d.offCenter.ι ≫ d.toBase) ≤ d.offBoth := by
  rintro ⟨U⟩ y ⟨s, rfl⟩
  rw [Space.mem_openSubspaceOfPoints_iff]
  rintro w ⟨z, rfl⟩
  have hcond : d.toBase.app (Opposite.op U)
        ((pullback.fst d.toBase d.offCenter.ι).app (Opposite.op U) s) =
      ((pullback.snd d.toBase d.offCenter.ι).app (Opposite.op U) s).val :=
    congrArg (fun η => η.app (Opposite.op U) s)
      (pullback.condition (f := d.toBase) (g := d.offCenter.ι))
  have hrange : Space.pointsMap B S hS (yoneda.obj U)
      (yonedaEquiv.symm
        ((pullback.fst d.toBase d.offCenter.ι ≫ d.toBase).app (Opposite.op U) s)) z ∈
      Set.range (Space.pointsMap B S hS d.eqz d.toBase) := by
    rw [show (pullback.fst d.toBase d.offCenter.ι ≫ d.toBase).app (Opposite.op U) s =
        d.toBase.app (Opposite.op U)
          ((pullback.fst d.toBase d.offCenter.ι).app (Opposite.op U) s) from rfl,
      ← yonedaEquiv_symm_naturality_right, Space.pointsMap_comp]
    exact ⟨_, rfl⟩
  have hoff : Space.pointsMap B S hS (yoneda.obj U)
      (yonedaEquiv.symm
        ((pullback.fst d.toBase d.offCenter.ι ≫ d.toBase).app (Opposite.op U) s)) z ∈
      d.Zᶜ := by
    rw [show (pullback.fst d.toBase d.offCenter.ι ≫ d.toBase).app (Opposite.op U) s =
      ((pullback.snd d.toBase d.offCenter.ι).app (Opposite.op U) s).val from hcond]
    exact ((pullback.snd d.toBase d.offCenter.ι).app (Opposite.op U) s).property ⟨z, rfl⟩
  exact fun hmem => hoff (d.range_pointsMap_toBase_inter_union_subset ⟨hrange, hmem⟩)

/-- The comparison morphism `E' ×_V (V ∖ Z) ⟶ V ∖ (Z₁ ∪ Z₂)`. -/
def offCenterFactor : pullback d.toBase d.offCenter.ι ⟶ d.offBoth.toFunctor :=
  Subfunctor.lift _ d.range_le_offBoth

/-- The composite `E' ×_V (V ∖ Z) ⟶ V ∖ (Z₁ ∪ Z₂) ⟶ V` is the projection to `E'` followed
by `E' ⟶ V`. -/
@[simp]
theorem offCenterFactor_comp_ι :
    d.offCenterFactor ≫ d.offBoth.ι = pullback.fst d.toBase d.offCenter.ι ≫ d.toBase :=
  Subfunctor.lift_ι _ _

/-- The composite `E' ×_V (V ∖ Z) ⟶ V ∖ (Z₁ ∪ Z₂) ⟶ V ∖ Z` is the second projection. -/
theorem offCenterFactor_comp :
    d.offCenterFactor ≫ Subfunctor.homOfLe d.offBoth_le_offCenter =
      pullback.snd d.toBase d.offCenter.ι := by
  rw [← cancel_mono d.offCenter.ι, Category.assoc, Subfunctor.homOfLe_ι,
    offCenterFactor_comp_ι, pullback.condition]

/-- In a cartesian square whose top edge is an identity, a cone factors through the left
edge: this is the universal property of
`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.isPullback_j`, which
identifies `V ∖ Z` with `(V ∖ Z) ×_V V'`. -/
private theorem comp_eq_of_isPullback_id {C : Type*} [Category C] {O W X A : C}
    {j : O ⟶ W} {ι : O ⟶ X} {p : W ⟶ X} (h : IsPullback (𝟙 O) j ι p)
    (a : A ⟶ O) (b : A ⟶ W) (hc : a ≫ ι = b ≫ p) : a ≫ j = b := by
  have h₁ := h.lift_fst a b hc
  rw [Category.comp_id] at h₁
  rw [← h₁]
  exact h.lift_snd a b hc

/-- The composite `E' ×_V (V ∖ Z) ⟶ V ∖ (Z₁ ∪ Z₂) ⟶ V ∖ Zᵢ ⟶ V'ᵢ` is the projection to `E'`
followed by any `E' ⟶ V'ᵢ` over `V`. -/
private theorem offCenterFactor_comp_homOfLe_comp {Zi : Set (Space.points B S hS (yoneda.obj V))}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : P ⟶ yoneda.obj V}
    {j : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Ziᶜ).toFunctor ⟶ P}
    (h : IsPullback (𝟙 _) j (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Ziᶜ).ι p)
    (le : d.offBoth ≤ Space.openSubspaceOfPoints B S hS (yoneda.obj V) Ziᶜ)
    (e : d.eqz ⟶ P) (he : e ≫ p = d.toBase) :
    d.offCenterFactor ≫ Subfunctor.homOfLe le ≫ j = pullback.fst d.toBase d.offCenter.ι ≫ e := by
  rw [← Category.assoc]
  refine comp_eq_of_isPullback_id h _ _ ?_
  rw [Category.assoc, Subfunctor.homOfLe_ι, offCenterFactor_comp_ι, Category.assoc, he]

/-- The composite `E' ×_V (V ∖ Z) ⟶ V ∖ (Z₁ ∪ Z₂) ⟶ V ∖ Z₁ ⟶ V'₁` is the projection to `E'`
followed by `E' ⟶ V'₁`. -/
theorem offCenterFactor_comp_j₁ :
    d.offCenterFactor ≫ Subfunctor.homOfLe d.offBoth_le_fst ≫ d.w₁.j =
      pullback.fst d.toBase d.offCenter.ι ≫ d.toFst :=
  d.offCenterFactor_comp_homOfLe_comp d.w₁.isPullback_j _ _ d.toFst_comp_p

/-- The composite `E' ×_V (V ∖ Z) ⟶ V ∖ (Z₁ ∪ Z₂) ⟶ V ∖ Z₂ ⟶ V'₂` is the projection to `E'`
followed by `E' ⟶ V'₂`. -/
theorem offCenterFactor_comp_j₂ :
    d.offCenterFactor ≫ Subfunctor.homOfLe d.offBoth_le_snd ≫ d.w₂.j =
      pullback.fst d.toBase d.offCenter.ι ≫ d.toSnd :=
  d.offCenterFactor_comp_homOfLe_comp d.w₂.isPullback_j _ _ d.toSnd_comp_p

/-- The morphism `E' ×_V (V ∖ Z) ⟶ V ∖ (Z₁ ∪ Z₂)` equalizes the restrictions of `u'₁` and
`u'₂` to `V ∖ (Z₁ ∪ Z₂)`. -/
theorem offCenterFactor_equalizes :
    d.offCenterFactor ≫ d.restrictedMap₁ = d.offCenterFactor ≫ d.restrictedMap₂ := by
  have h₁ := congrArg (· ≫ d.w₁.x') d.offCenterFactor_comp_j₁
  have h₂ := congrArg (· ≫ d.w₂.x') d.offCenterFactor_comp_j₂
  simp only [Category.assoc, d.w₁.restrict_x', d.w₂.restrict_x'] at h₁ h₂
  rw [restrictedMap₁, restrictedMap₂, ← Category.assoc, ← Category.assoc]
  simp only [Category.assoc] at h₁ h₂ ⊢
  rw [h₁, h₂, d.toFst_comp_witnessMap_eq]

/-- **Stacks 0GHD**, first half of assertion (2): the morphism
`E' ×_V (V ∖ Z) ⟶ V ∖ Z` is a monomorphism. -/
@[stacks 0GHD "assertion (2), the monomorphism half in full: that the morphism \
E' ×_V (V ∖ Z) → V ∖ Z is a monomorphism. The other half of the assertion, that this \
morphism is the equalizer of the restrictions of u'₁ and u'₂ to V ∖ (Z₁ ∪ Z₂), is \
`AlgebraicGeometry.Artin.ContractionEqualizer.exists_isLimit_fork_offCenter`. Proved with no \
hypothesis on V beyond its being an object of the big fppf site over S, so the tag's own \
hypothesis that V be a locally Noetherian scheme over S is a special case"]
theorem mono_pullbackSnd_offCenter : Mono (pullback.snd d.toBase d.offCenter.ι) := by
  refine ⟨fun {A} left right hlr => ?_⟩
  have hfac : left ≫ d.offCenterFactor = right ≫ d.offCenterFactor := by
    refine (cancel_mono (Subfunctor.homOfLe d.offBoth_le_offCenter)).1 ?_
    simpa only [Category.assoc, d.offCenterFactor_comp] using hlr
  have key : ∀ {Zi : Set (Space.points B S hS (yoneda.obj V))}
      {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : P ⟶ yoneda.obj V}
      {j : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Ziᶜ).toFunctor ⟶ P}
      (h : IsPullback (𝟙 _) j (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Ziᶜ).ι p)
      (le : d.offBoth ≤ Space.openSubspaceOfPoints B S hS (yoneda.obj V) Ziᶜ)
      (e : d.eqz ⟶ P) (he : e ≫ p = d.toBase),
      left ≫ pullback.fst d.toBase d.offCenter.ι ≫ e =
        right ≫ pullback.fst d.toBase d.offCenter.ι ≫ e := fun {_ _ _ j} h le e he => by
    simpa only [Category.assoc, d.offCenterFactor_comp_homOfLe_comp h le e he] using
      congrArg (· ≫ Subfunctor.homOfLe le ≫ j) hfac
  refine pullback.hom_ext ?_ hlr
  refine (cancel_mono (equalizer.ι d.x₁ d.x₂)).1 ?_
  refine (IsPullback.of_hasPullback d.w₁.p d.w₂.p).hom_ext ?_ ?_
  · simpa only [Category.assoc, toFst] using key d.w₁.isPullback_j d.offBoth_le_fst d.toFst
      d.toFst_comp_p
  · simpa only [Category.assoc, toSnd] using key d.w₂.isPullback_j d.offBoth_le_snd d.toSnd
      d.toSnd_comp_p

/-- The morphism `E' ×_V (V ∖ Z) ⟶ V ∖ (Z₁ ∪ Z₂)` is a monomorphism. -/
theorem mono_offCenterFactor : Mono d.offCenterFactor :=
  have := d.mono_pullbackSnd_offCenter
  mono_of_mono_fac d.offCenterFactor_comp

/-- A morphism to `V ∖ (Z₁ ∪ Z₂)` equalizing the restrictions of `u'₁` and `u'₂` factors
through `E' ×_V (V ∖ Z) ⟶ V ∖ (Z₁ ∪ Z₂)`. -/
theorem exists_lift_offCenterFactor
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : A ⟶ d.offBoth.toFunctor)
    (hm : m ≫ d.restrictedMap₁ = m ≫ d.restrictedMap₂) :
    ∃ l : A ⟶ pullback d.toBase d.offCenter.ι, l ≫ d.offCenterFactor = m := by
  have hb₁ : Subfunctor.homOfLe d.offBoth_le_fst ≫ d.w₁.j ≫ d.w₁.p = d.offBoth.ι := by
    rw [← d.w₁.isPullback_j.w, Category.id_comp, Subfunctor.homOfLe_ι]
  have hb₂ : Subfunctor.homOfLe d.offBoth_le_snd ≫ d.w₂.j ≫ d.w₂.p = d.offBoth.ι := by
    rw [← d.w₂.isPullback_j.w, Category.id_comp, Subfunctor.homOfLe_ι]
  set n : A ⟶ d.fibProd := pullback.lift (m ≫ Subfunctor.homOfLe d.offBoth_le_fst ≫ d.w₁.j)
    (m ≫ Subfunctor.homOfLe d.offBoth_le_snd ≫ d.w₂.j)
    (by simp only [Category.assoc, hb₁, hb₂]) with hn
  have hnx : n ≫ d.x₁ = n ≫ d.x₂ := by
    rw [x₁, x₂, hn, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    simp only [Category.assoc, d.w₁.restrict_x', d.w₂.restrict_x']
    simpa only [restrictedMap₁, restrictedMap₂, Category.assoc] using hm
  have hbase : equalizer.lift n hnx ≫ d.toBase =
      (m ≫ Subfunctor.homOfLe d.offBoth_le_offCenter) ≫ d.offCenter.ι := by
    rw [Category.assoc, Subfunctor.homOfLe_ι, toBase, ← Category.assoc,
      equalizer.lift_ι, hn, pullback.lift_fst_assoc]
    simp only [Category.assoc]
    rw [hb₁]
  refine ⟨pullback.lift (equalizer.lift n hnx)
    (m ≫ Subfunctor.homOfLe d.offBoth_le_offCenter) hbase, ?_⟩
  refine (cancel_mono (Subfunctor.homOfLe d.offBoth_le_offCenter)).1 ?_
  rw [Category.assoc, d.offCenterFactor_comp, pullback.lift_snd]

/-- **Stacks 0GHD**, second half of assertion (2): the morphism
`E' ×_V (V ∖ Z) ⟶ V ∖ Z` *is* the equalizer of the restrictions of `u'₁` and `u'₂` to
`V ∖ (Z₁ ∪ Z₂)`, in the sense that it factors through `V ∖ (Z₁ ∪ Z₂)` by a morphism which is
a limiting fork for those two restrictions. -/
@[stacks 0GHD "assertion (2), the equalizer half in full: that the morphism \
E' ×_V (V ∖ Z) → V ∖ Z factors through the open subspace V ∖ (Z₁ ∪ Z₂) by a morphism which is \
a limiting fork for the restrictions of u'₁ and u'₂ to V ∖ (Z₁ ∪ Z₂), that being what it is \
for the morphism to be equal to their equalizer. The other half of the assertion, that the \
morphism is a monomorphism, is \
`AlgebraicGeometry.Artin.ContractionEqualizer.mono_pullbackSnd_offCenter`. Proved with no \
hypothesis on V beyond its being an object of the big fppf site over S, so the tag's own \
hypothesis that V be a locally Noetherian scheme over S is a special case"]
theorem exists_isLimit_fork_offCenter :
    ∃ e : pullback d.toBase d.offCenter.ι ⟶ d.offBoth.toFunctor,
      e ≫ Subfunctor.homOfLe d.offBoth_le_offCenter =
          pullback.snd d.toBase d.offCenter.ι ∧
        ∃ he : e ≫ d.restrictedMap₁ = e ≫ d.restrictedMap₂,
          Nonempty (IsLimit (Fork.ofι e he)) := by
  refine ⟨d.offCenterFactor, d.offCenterFactor_comp, d.offCenterFactor_equalizes, ⟨?_⟩⟩
  have := d.mono_offCenterFactor
  refine Fork.IsLimit.mk' _ fun fork => ?_
  refine ⟨Classical.choose (d.exists_lift_offCenterFactor fork.ι fork.condition),
    Classical.choose_spec (d.exists_lift_offCenterFactor fork.ι fork.condition),
    fun {m} hm => (cancel_mono d.offCenterFactor).1 (hm.trans
      (Classical.choose_spec
        (d.exists_lift_offCenterFactor fork.ι fork.condition)).symm)⟩

end OffCenter

/-! ### `E' ⟶ V` is separated and locally of finite type -/

section Observe

private theorem isSeparated_of_isPullback
    {P F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {top : P ⟶ F} {left : P ⟶ G} {right : F ⟶ H} {bottom : G ⟶ H}
    (sq : IsPullback top left right bottom)
    (hbottom : Space.IsSeparated B S hS bottom) :
    Space.IsSeparated B S hS top :=
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))).diagonal.of_isPullback sq.flip hbottom

private theorem isLocallyOfFiniteType_of_isPullback
    {P F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {top : P ⟶ F} {left : P ⟶ G} {right : F ⟶ H} {bottom : G ⟶ H}
    (hP : IsAlgebraicSpace B S hS P) (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H)
    (sq : IsPullback top left right bottom)
    (hbottom : Space.IsLocallyOfFiniteType B S hS bottom) :
    Space.IsLocallyOfFiniteType B S hS top := by
  have hsq : IsPullback (ObjectProperty.homMk top : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk left : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
      (ObjectProperty.homMk right : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨H, hH⟩)
      (ObjectProperty.homMk bottom : (⟨G, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨H, hH⟩) :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F => IsAlgebraicSpace B S hS F)) sq
  exact (Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hsq.flip
    hbottom

/-- The first projection `V' ⟶ V'₁` is separated, being a base change of `V'₂ ⟶ V`, which is
proper and hence separated. -/
theorem isSeparated_pullbackFst : Space.IsSeparated B S hS (pullback.fst d.w₁.p d.w₂.p) :=
  isSeparated_of_isPullback (IsPullback.of_hasPullback d.w₁.p d.w₂.p) d.w₂.isProper_p.1

/-- The first projection `V' ⟶ V'₁` is locally of finite type, being a base change of
`V'₂ ⟶ V`, which is proper and hence locally of finite type. -/
theorem isLocallyOfFiniteType_pullbackFst :
    Space.IsLocallyOfFiniteType B S hS (pullback.fst d.w₁.p d.w₂.p) :=
  isLocallyOfFiniteType_of_isPullback d.isAlgebraicSpace_fibProd d.w₁.isAlgebraicSpace_V'
    d.w₂.isAlgebraicSpace_V' (isAlgebraicSpace_yoneda B S hS V)
    (IsPullback.of_hasPullback d.w₁.p d.w₂.p) d.w₂.isProper_p.2.1.1

/-- **Stacks 0GHD**, first half of the sentence "observe that `E' → V` is separated and
locally of finite type": the morphism `E' ⟶ V` is separated.

It is the composite of the equalizer inclusion `E' ⟶ V'`, which is a monomorphism, of the
projection `V' ⟶ V'₁`, which is a base change of the proper morphism `V'₂ ⟶ V`, and of the
proper morphism `V'₁ ⟶ V`. -/
@[stacks 0GHD "the sentence `Observe that E' → V is separated and locally of finite type', \
the separatedness half in full: that the morphism E' ⟶ V is separated. The local-finite-type \
half is `AlgebraicGeometry.Artin.ContractionEqualizer.isLocallyOfFiniteType_toBase`. The \
remainder of that sentence, that E_W is a locally Noetherian formal algebraic space separated \
over V, is not claimed here; its separatedness half is \
`AlgebraicGeometry.Artin.ContractionEqualizer.isSeparatedMorphism_EW`. Proved with no \
hypothesis on V \
beyond its being an object of the big fppf site over S, so the tag's own hypothesis that V be \
a locally Noetherian scheme over S is a special case"]
theorem isSeparated_toBase : Space.IsSeparated B S hS d.toBase :=
  Space.isSeparated_comp B S hS _ _ (Space.isSeparated_equalizer_ι B S hS d.x₁ d.x₂)
    (Space.isSeparated_comp B S hS _ _ d.isSeparated_pullbackFst d.w₁.isProper_p.1)

/-- **Stacks 0GHD**, second half of the sentence "observe that `E' → V` is separated and
locally of finite type": the morphism `E' ⟶ V` is locally of finite type.

It is the composite of the equalizer inclusion `E' ⟶ V'`, which is a base change of the
diagonal of `X'` and so locally of finite type by Stacks 02X4, of the projection
`V' ⟶ V'₁`, which is a base change of the proper morphism `V'₂ ⟶ V`, and of the proper
morphism `V'₁ ⟶ V`. -/
@[stacks 0GHD "the sentence `Observe that E' → V is separated and locally of finite type', \
the local-finite-type half in full: that the morphism E' ⟶ V is locally of finite type. The \
separatedness half is `AlgebraicGeometry.Artin.ContractionEqualizer.isSeparated_toBase`. The \
remainder of that sentence, that E_W is a locally Noetherian formal algebraic space separated \
over V, is not claimed here; its separatedness half is \
`AlgebraicGeometry.Artin.ContractionEqualizer.isSeparatedMorphism_EW`. Proved with no \
hypothesis on V \
beyond its being an object of the big fppf site over S, so the tag's own hypothesis that V be \
a locally Noetherian scheme over S is a special case"]
theorem isLocallyOfFiniteType_toBase :
    Space.IsLocallyOfFiniteType B S hS d.toBase :=
  Space.isLocallyOfFiniteType_comp B S hS d.isAlgebraicSpace_eqz d.isAlgebraicSpace_fibProd
    (isAlgebraicSpace_yoneda B S hS V) _ _
    (Space.isLocallyOfFiniteType_equalizer_ι B S hS d.isAlgebraicSpace_fibProd
      c.isAlgebraicSpace_X' d.x₁ d.x₂)
    (Space.isLocallyOfFiniteType_comp B S hS d.isAlgebraicSpace_fibProd
      d.w₁.isAlgebraicSpace_V' (isAlgebraicSpace_yoneda B S hS V) _ _
      d.isLocallyOfFiniteType_pullbackFst d.w₁.isProper_p.2.1.1)

end Observe

/-! ### Assertion (5): when two triples restrict to the same element -/

section Criterion

open ContractionSituation

variable {A : BigFppfOver B S hS} (φ : A ⟶ V)

/-- The inverse image `φ⁻¹(Z)` of `Z = Z₁ ∩ Z₂`, which is the first component of the
restriction along `φ` of either triple once the two restrictions agree. -/
abbrev preZ : Set (Space.points B S hS (yoneda.obj A)) :=
  Space.pointsMap B S hS (yoneda.obj A) (yoneda.map φ) ⁻¹' d.Z

/-- The inverse image `φ⁻¹(Z₁)`, the first component of the restriction of the first
triple. -/
abbrev preZ₁ : Set (Space.points B S hS (yoneda.obj A)) :=
  Space.pointsMap B S hS (yoneda.obj A) (yoneda.map φ) ⁻¹' d.t₁.Z

/-- The inverse image `φ⁻¹(Z₂)`, the first component of the restriction of the second
triple. -/
abbrev preZ₂ : Set (Space.points B S hS (yoneda.obj A)) :=
  Space.pointsMap B S hS (yoneda.obj A) (yoneda.map φ) ⁻¹' d.t₂.Z

/-- `φ⁻¹(Z)` is contained in `φ⁻¹(Z₁)`. -/
theorem preZ_subset_preZ₁ : d.preZ φ ⊆ d.preZ₁ φ := fun _ hx => hx.1

/-- `φ⁻¹(Z)` is contained in `φ⁻¹(Z₂)`. -/
theorem preZ_subset_preZ₂ : d.preZ φ ⊆ d.preZ₂ φ := fun _ hx => hx.2

/-- The comparison morphism `A ∖ φ⁻¹(Z) ⟶ V ∖ (Z₁ ∪ Z₂)`, available once `φ⁻¹(Z₁ ∪ Z₂)` is
known to be contained in `φ⁻¹(Z)`. -/
def offBothOfPre (hU : d.preZ₁ φ ∪ d.preZ₂ φ ⊆ d.preZ φ) :
    (Space.openSubspaceOfPoints B S hS (yoneda.obj A) (d.preZ φ)ᶜ).toFunctor ⟶
      d.offBoth.toFunctor :=
  Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) (d.preZ φ)ᶜ (d.t₁.Z ∪ d.t₂.Z)ᶜ
    (by
      intro x hx hmem
      exact hx (hU hmem))

/-- The composite `A ∖ φ⁻¹(Z) ⟶ V ∖ (Z₁ ∪ Z₂) ⟶ V` is the inclusion `A ∖ φ⁻¹(Z) ⟶ A`
followed by `φ`. -/
theorem offBothOfPre_comp_ι (hU : d.preZ₁ φ ∪ d.preZ₂ φ ⊆ d.preZ φ) :
    d.offBothOfPre φ hU ≫ d.offBoth.ι =
      (Space.openSubspaceOfPoints B S hS (yoneda.obj A) (d.preZ φ)ᶜ).ι ≫ yoneda.map φ := rfl

/-- The composite `A ∖ φ⁻¹(Z) ⟶ V ∖ (Z₁ ∪ Z₂) ⟶ V ∖ Z₁` is the restriction of `φ`. -/
theorem offBothOfPre_comp_homOfLe_fst (hU : d.preZ₁ φ ∪ d.preZ₂ φ ⊆ d.preZ φ) :
    d.offBothOfPre φ hU ≫ Subfunctor.homOfLe d.offBoth_le_fst =
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) (d.preZ φ)ᶜ d.t₁.Zᶜ
        (by intro x hx hmem; exact hx (hU (Or.inl hmem))) := by
  exact Space.openSubspaceOfPointsRestrict_comp_homOfLe B S hS _ _ _ _
    (Set.compl_subset_compl.2 fun _ h => Or.inl h) _ _

/-- The composite `A ∖ φ⁻¹(Z) ⟶ V ∖ (Z₁ ∪ Z₂) ⟶ V ∖ Z₂` is the restriction of `φ`. -/
theorem offBothOfPre_comp_homOfLe_snd (hU : d.preZ₁ φ ∪ d.preZ₂ φ ⊆ d.preZ φ) :
    d.offBothOfPre φ hU ≫ Subfunctor.homOfLe d.offBoth_le_snd =
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) (d.preZ φ)ᶜ d.t₂.Zᶜ
        (by intro x hx hmem; exact hx (hU (Or.inr hmem))) := by
  exact Space.openSubspaceOfPointsRestrict_comp_homOfLe B S hS _ _ _ _
    (Set.compl_subset_compl.2 fun _ h => Or.inr h) _ _

/-- The composite `A ∖ φ⁻¹(Z) ⟶ V ∖ (Z₁ ∪ Z₂) ⟶ V ∖ Z` is the restriction of `φ`. -/
theorem offBothOfPre_comp_homOfLe_offCenter (hU : d.preZ₁ φ ∪ d.preZ₂ φ ⊆ d.preZ φ) :
    d.offBothOfPre φ hU ≫ Subfunctor.homOfLe d.offBoth_le_offCenter =
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) (d.preZ φ)ᶜ d.Zᶜ
        (by intro x hx hmem; exact hx hmem) := by
  exact Space.openSubspaceOfPointsRestrict_comp_homOfLe B S hS _ _ _ _
    (Set.compl_subset_compl.2 fun _ h => Or.inl h.1) _ _

/-- **Assertion (5)(b), first condition**: the morphism `A ∖ φ⁻¹(Z) ⟶ V ∖ Z` factors through
`E' ×_V (V ∖ Z)`. -/
def FactorsOffCenter : Prop :=
  ∃ k : (Space.openSubspaceOfPoints B S hS (yoneda.obj A) (d.preZ φ)ᶜ).toFunctor ⟶
      pullback d.toBase d.offCenter.ι,
    k ≫ pullback.snd d.toBase d.offCenter.ι =
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) (d.preZ φ)ᶜ d.Zᶜ
        Set.Subset.rfl

/-- **Assertion (5)(b), second condition**: the morphism `A_{/φ⁻¹(Z)} ⟶ V_{/Z}` factors
through `E_W`. -/
def FactorsEW : Prop :=
  ∃ l : Space.completionSheaf B S hS (yoneda.obj A) (d.preZ φ) ⟶ d.EW,
    l ≫ equalizer.ι d.xhat₁ d.xhat₂ =
      Space.completionSheafRestrict B S hS (yoneda.map φ) (d.preZ φ) d.Z Set.Subset.rfl

/-- A factorization of `A ∖ φ⁻¹(Z) ⟶ V ∖ Z` through `E' ×_V (V ∖ Z)` confines
`φ⁻¹(Z₁ ∪ Z₂)` to `φ⁻¹(Z)`: the composite lands in `V ∖ (Z₁ ∪ Z₂)` by assertion (1), whose
point set is the complement of `Z₁ ∪ Z₂` by Stacks 03BZ. -/
theorem union_subset_preZ_of_factorsOffCenter (hfac : d.FactorsOffCenter φ) :
    d.preZ₁ φ ∪ d.preZ₂ φ ⊆ d.preZ φ := by
  obtain ⟨k, hk⟩ := hfac
  have hmι : (k ≫ d.offCenterFactor) ≫ d.offBoth.ι =
      (Space.openSubspaceOfPoints B S hS (yoneda.obj A) (d.preZ φ)ᶜ).ι ≫ yoneda.map φ := by
    rw [Category.assoc, d.offCenterFactor_comp_ι, pullback.condition, ← Category.assoc, hk]
    exact Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _
  intro x hx
  by_contra hnot
  obtain ⟨y, hy⟩ : x ∈ Set.range (Space.pointsMap B S hS
      (Space.openSubspaceOfPoints B S hS (yoneda.obj A) (d.preZ φ)ᶜ).toFunctor
      (Space.openSubspaceOfPoints B S hS (yoneda.obj A) (d.preZ φ)ᶜ).ι) := by
    rw [Space.range_pointsMap_ι_openSubspaceOfPoints]
    exact hnot
  have hmem : Space.pointsMap B S hS (yoneda.obj A) (yoneda.map φ) x ∈
      Set.range (Space.pointsMap B S hS d.offBoth.toFunctor d.offBoth.ι) := by
    refine ⟨Space.pointsMap B S hS _ (k ≫ d.offCenterFactor) y, ?_⟩
    have h1 : Space.pointsMap B S hS _ ((k ≫ d.offCenterFactor) ≫ d.offBoth.ι) y =
        Space.pointsMap B S hS d.offBoth.toFunctor d.offBoth.ι
          (Space.pointsMap B S hS _ (k ≫ d.offCenterFactor) y) := by
      rw [Space.pointsMap_comp]
      rfl
    rw [← h1, hmι, Space.pointsMap_comp]
    exact congrArg _ hy
  rw [Space.range_pointsMap_ι_openSubspaceOfPoints] at hmem
  exact hmem hx

/-- If `φ⁻¹(Z₁ ∪ Z₂) ⊆ φ⁻¹(Z)`, then `φ⁻¹(Z₁) ⊆ φ⁻¹(Z)`. -/
theorem preZ₁_subset_preZ (hU : d.preZ₁ φ ∪ d.preZ₂ φ ⊆ d.preZ φ) : d.preZ₁ φ ⊆ d.preZ φ :=
  fun _ hx => hU (Or.inl hx)

/-- If `φ⁻¹(Z₁ ∪ Z₂) ⊆ φ⁻¹(Z)`, then `φ⁻¹(Z₂) ⊆ φ⁻¹(Z)`. -/
theorem preZ₂_subset_preZ (hU : d.preZ₁ φ ∪ d.preZ₂ φ ⊆ d.preZ φ) : d.preZ₂ φ ⊆ d.preZ φ :=
  fun _ hx => hU (Or.inr hx)

/-- The restriction of the first triple's third component to a set `T ⊆ φ⁻¹(Z)` factors
through the composite `A_{/φ⁻¹(Z)} ⟶ V_{/Z} ⟶ W` defining `E_W`. -/
theorem completionSheafRestrict_comp_xhat₁ (T : Set (Space.points B S hS (yoneda.obj A)))
    (hT : T ⊆ d.preZ φ) (h : T ⊆ Space.pointsMap B S hS (yoneda.obj A) (yoneda.map φ) ⁻¹' d.t₁.Z) :
    Space.completionSheafRestrict B S hS (yoneda.map φ) T d.t₁.Z h ≫ d.t₁.xhat =
      Space.completionSheafRestrict B S hS (𝟙 _) T (d.preZ φ)
          (Space.subset_preimage_pointsMap_id B S hS hT) ≫
        Space.completionSheafRestrict B S hS (yoneda.map φ) (d.preZ φ) d.Z Set.Subset.rfl ≫
          d.xhat₁ := by
  rw [xhat₁, Space.completionSheafRestrict_comp_id_assoc,
    Space.completionSheafRestrict_id_comp_assoc]

/-- The counterpart of `completionSheafRestrict_comp_xhat₁` for the second triple. -/
theorem completionSheafRestrict_comp_xhat₂ (T : Set (Space.points B S hS (yoneda.obj A)))
    (hT : T ⊆ d.preZ φ) (h : T ⊆ Space.pointsMap B S hS (yoneda.obj A) (yoneda.map φ) ⁻¹' d.t₂.Z) :
    Space.completionSheafRestrict B S hS (yoneda.map φ) T d.t₂.Z h ≫ d.t₂.xhat =
      Space.completionSheafRestrict B S hS (𝟙 _) T (d.preZ φ)
          (Space.subset_preimage_pointsMap_id B S hS hT) ≫
        Space.completionSheafRestrict B S hS (yoneda.map φ) (d.preZ φ) d.Z Set.Subset.rfl ≫
          d.xhat₂ := by
  rw [xhat₂, Space.completionSheafRestrict_comp_id_assoc,
    Space.completionSheafRestrict_id_comp_assoc]

/-- **Stacks 0GHD**, assertion (5), the implication (a) ⇒ (b): if the two triples restrict to
the same element of `F(A)` along `φ : A ⟶ V`, then `A ∖ φ⁻¹(Z) ⟶ V ∖ Z` factors through
`E' ×_V (V ∖ Z)` and `A_{/φ⁻¹(Z)} ⟶ V_{/Z}` factors through `E_W`. -/
theorem factorsOffCenter_and_factorsEW_of_mapTriple_eq
    (h : mapTriple c φ d.t₁ = mapTriple c φ d.t₂) : d.FactorsOffCenter φ ∧ d.FactorsEW φ := by
  have hZ : (mapTriple c φ d.t₁).Z = (mapTriple c φ d.t₂).Z := congrArg Triple.Z h
  have hZ' : d.preZ₁ φ = d.preZ₂ φ := hZ
  have hU : d.preZ₁ φ ∪ d.preZ₂ φ ⊆ d.preZ φ := by
    rintro x (hx | hx)
    · exact ⟨hx, hZ'.subset hx⟩
    · exact ⟨hZ'.symm.subset hx, hx⟩
  obtain ⟨hu, hx⟩ := (Triple.eq_iff_of_Z_eq hZ).1 h
  refine ⟨?_, ?_⟩
  · -- the open-subspace side: the comparison morphism equalizes the two restrictions, so it
    -- lifts to `E' ×_V (V ∖ Z)` by assertion (2)
    have h₀ : (d.preZ φ)ᶜ ⊆ Space.pointsMap B S hS (yoneda.obj A) (𝟙 _) ⁻¹' (d.preZ₁ φ)ᶜ :=
      Space.subset_preimage_pointsMap_id B S hS
        (Set.compl_subset_compl.2 (d.preZ₁_subset_preZ φ hU))
    have e₁ : d.offBothOfPre φ hU ≫ d.restrictedMap₁ =
        Space.openSubspaceOfPointsRestrict B S hS (𝟙 _) (d.preZ φ)ᶜ (d.preZ₁ φ)ᶜ h₀ ≫
          (mapTriple c φ d.t₁).u ≫ c.U'.ι := rfl
    have e₂ : d.offBothOfPre φ hU ≫ d.restrictedMap₂ =
        Space.openSubspaceOfPointsRestrict B S hS (𝟙 _) (d.preZ φ)ᶜ (d.preZ₁ φ)ᶜ h₀ ≫
          (mapTriple c φ d.t₁).u ≫ c.U'.ι := by
      rw [← hu]
      rfl
    obtain ⟨k, hk⟩ := d.exists_lift_offCenterFactor (d.offBothOfPre φ hU) (e₁.trans e₂.symm)
    refine ⟨k, ?_⟩
    rw [← d.offCenterFactor_comp, ← Category.assoc, hk, offBothOfPre_comp_homOfLe_offCenter]
  · -- the completion side: the restriction equalizes `x̂₁` and `x̂₂`
    refine ⟨equalizer.lift (Space.completionSheafRestrict B S hS (yoneda.map φ) (d.preZ φ) d.Z
      Set.Subset.rfl) ?_, equalizer.lift_ι _ _⟩
    have hx' : Space.completionSheafRestrict B S hS (𝟙 _) (d.preZ₁ φ) (d.preZ₂ φ)
          (Space.subset_preimage_pointsMap_id B S hS hZ'.subset) ≫
          Space.completionSheafRestrict B S hS (yoneda.map φ) (d.preZ₂ φ) d.t₂.Z
            Set.Subset.rfl ≫ d.t₂.xhat =
        Space.completionSheafRestrict B S hS (yoneda.map φ) (d.preZ₁ φ) d.t₁.Z
          Set.Subset.rfl ≫ d.t₁.xhat := hx
    have key₁ := d.completionSheafRestrict_comp_xhat₁ φ (d.preZ φ) subset_rfl
      (d.preZ_subset_preZ₁ φ)
    have key₂ := d.completionSheafRestrict_comp_xhat₂ φ (d.preZ φ) subset_rfl
      (d.preZ_subset_preZ₂ φ)
    rw [Space.completionSheafRestrict_id, Category.id_comp] at key₁ key₂
    rw [← key₁, ← key₂, ← Space.completionSheafRestrict_id_comp_assoc B S hS (yoneda.map φ)
      (d.preZ φ) (d.preZ₁ φ) d.t₁.Z
      (Space.subset_preimage_pointsMap_id B S hS (d.preZ_subset_preZ₁ φ)) Set.Subset.rfl,
      ← hx', Space.completionSheafRestrict_id_comp_assoc,
      Space.completionSheafRestrict_id_comp_assoc]

/-- **Stacks 0GHD**, assertion (5), the implication (b) ⇒ (a): if `A ∖ φ⁻¹(Z) ⟶ V ∖ Z`
factors through `E' ×_V (V ∖ Z)` and `A_{/φ⁻¹(Z)} ⟶ V_{/Z}` factors through `E_W`, then the
two triples restrict to the same element of `F(A)` along `φ : A ⟶ V`. -/
theorem mapTriple_eq_of_factorsOffCenter_of_factorsEW (hoff : d.FactorsOffCenter φ)
    (hEW : d.FactorsEW φ) : mapTriple c φ d.t₁ = mapTriple c φ d.t₂ := by
  have hU := d.union_subset_preZ_of_factorsOffCenter φ hoff
  have hZ' : d.preZ₁ φ = d.preZ₂ φ :=
    ((d.preZ₁_subset_preZ φ hU).trans (d.preZ_subset_preZ₂ φ)).antisymm
      ((d.preZ₂_subset_preZ φ hU).trans (d.preZ_subset_preZ₁ φ))
  have hZ : (mapTriple c φ d.t₁).Z = (mapTriple c φ d.t₂).Z := hZ'
  obtain ⟨k, hk⟩ := hoff
  obtain ⟨l, hl⟩ := hEW
  refine (Triple.eq_iff_of_Z_eq hZ).2 ⟨?_, ?_⟩
  · -- the open-subspace side, through the comparison morphism and assertion (2)
    have ho : k ≫ d.offCenterFactor = d.offBothOfPre φ hU := by
      refine (cancel_mono (Subfunctor.homOfLe d.offBoth_le_offCenter)).1 ?_
      rw [Category.assoc, d.offCenterFactor_comp, hk, offBothOfPre_comp_homOfLe_offCenter]
    have heq : d.offBothOfPre φ hU ≫ d.restrictedMap₁ =
        d.offBothOfPre φ hU ≫ d.restrictedMap₂ := by
      rw [← ho, Category.assoc, Category.assoc, d.offCenterFactor_equalizes]
    exact (cancel_mono c.U'.ι).1 (congrArg (Space.openSubspaceOfPointsRestrict B S hS
      (𝟙 (yoneda.obj A)) (d.preZ₁ φ)ᶜ (d.preZ φ)ᶜ
      (Space.subset_preimage_pointsMap_id B S hS
        (Set.compl_subset_compl.2 (d.preZ_subset_preZ₁ φ))) ≫ ·) heq.symm)
  · -- the completion side, through the factorization through `E_W`
    have hc : Space.completionSheafRestrict B S hS (𝟙 _) (d.preZ₁ φ) (d.preZ₂ φ)
          (Space.subset_preimage_pointsMap_id B S hS hZ'.subset) ≫
          Space.completionSheafRestrict B S hS (yoneda.map φ) (d.preZ₂ φ) d.t₂.Z
            Set.Subset.rfl ≫ d.t₂.xhat =
        Space.completionSheafRestrict B S hS (yoneda.map φ) (d.preZ₁ φ) d.t₁.Z
          Set.Subset.rfl ≫ d.t₁.xhat := by
      rw [Space.completionSheafRestrict_id_comp_assoc,
        d.completionSheafRestrict_comp_xhat₁ φ _ (d.preZ₁_subset_preZ φ hU),
        d.completionSheafRestrict_comp_xhat₂ φ _ (d.preZ₁_subset_preZ φ hU), ← hl]
      simp only [Category.assoc]
      rw [equalizer.condition]
    exact hc

/-- **Stacks 0GHD**, assertion (5): given a morphism `φ : A ⟶ V`, the two triples
`(Z₁, u'₁, x̂₁)` and `(Z₂, u'₂, x̂₂)` restrict to the same element of `F(A)` if and only if
`A ∖ φ⁻¹(Z) ⟶ V ∖ Z` factors through `E' ×_V (V ∖ Z)` and `A_{/φ⁻¹(Z)} ⟶ V_{/Z}` factors
through `E_W`.

The restriction of a triple along `φ` is
`AlgebraicGeometry.Artin.ContractionSituation.mapTriple`, which is the value on `φ` of Artin's
functor `F` (`AlgebraicGeometry.Artin.contractionFunctor`) when `A` and `V` are locally
Noetherian. The two conditions of (b) are
`AlgebraicGeometry.Artin.ContractionEqualizer.FactorsOffCenter` and
`AlgebraicGeometry.Artin.ContractionEqualizer.FactorsEW`; `E_W` is the equalizer of the two
morphisms `V_{/Z} ⟶ W` in the category of fppf sheaves, which is where formal algebraic spaces
over `S` live, so factoring through it is factoring through the remark's `E_W`. -/
@[stacks 0GHD "assertion (5), in full: for a morphism φ : A ⟶ V, the two triples restrict to \
the same element of F(A) if and only if A ∖ φ⁻¹(Z) → V ∖ Z factors through E' ×_V (V ∖ Z) and \
A_{/φ⁻¹(Z)} → V_{/Z} factors through E_W. Proved for an arbitrary morphism φ of the big fppf \
site over S, local Noetherianness of A and V being used nowhere, so the tag's own statement, \
for a morphism of locally Noetherian schemes, is a special case"]
theorem mapTriple_eq_iff_factorsOffCenter_and_factorsEW :
    mapTriple c φ d.t₁ = mapTriple c φ d.t₂ ↔ d.FactorsOffCenter φ ∧ d.FactorsEW φ :=
  ⟨d.factorsOffCenter_and_factorsEW_of_mapTriple_eq φ,
    fun h => d.mapTriple_eq_of_factorsOffCenter_of_factorsEW φ h.1 h.2⟩

end Criterion

end ContractionEqualizer

end Artin

end AlgebraicGeometry

end
