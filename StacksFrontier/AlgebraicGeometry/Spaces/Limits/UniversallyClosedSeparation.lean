module

public import Mathlib.Topology.Maps.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Limits.ClosedSubsetFibreSeparation
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfRepresentablePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Separating a closed subset from a point after an étale neighbourhood

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over a scheme `S`, let
`g : Z ⟶ Y` be a morphism of algebraic spaces, let `z ∈ |Z|` and let `T ⊆ |X ×_Y Z|` be a
closed subset whose image in `|Z|` misses `z`. Tag 0CM8 produces an affine étale neighbourhood
`(V, v) → (Z, z)`, a factorization `V ⟶ Z' ⟶ Y` of `V ⟶ Y` with `Z'` affine and `Z' ⟶ Y`
locally of finite presentation, and a closed subset `T' ⊆ |X ×_Y Z'|` which misses the image
of `v` and which receives the inverse image of `T` in `|X ×_Y V|`.

This file proves that statement, the descent of its clauses (2) and (3) along an étale cover
of `X`, and the refinement for `Z` a scheme, where `V` may be taken to be an affine open
neighbourhood of `z`, under hypotheses which supply a Zariski-local factorization of `Z ⟶ Y`
at `z` through an affine scheme locally of finite presentation over `Y`.

## Main results

* `exists_isClosed_separation_of_isPullback`: for a cartesian square of presheaves whose base
  morphism is open and surjective on points, a closed subset separating a point over the cover
  produces one separating the same point over the base, namely the closure of the image; the
  inputs are the commutation of closure with preimages along an open map (Tag 02YB) and the
  surjectivity of the comparison map on the points of a cartesian square (Tag 03H4).
* `exists_isClosed_separation_of_etale_cover`: the same statement for the configuration of
  fibre products in which Tag 0CM8 uses it, with the four comparison morphisms and their
  projections produced explicitly.
* `exists_separation_of_affine_lfp_chart`: Tag 0CM8 with the chart data of its proof taken as
  hypotheses.
* `exists_affine_etale_isLocallyOfFinitePresentation_separation`: Tag 0CM8, with `V` and `Z'`
  affine.
* `exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization`: the
  refinement for `Z` a scheme, given a Zariski-local factorization of `Z ⟶ Y` at `z` through an
  affine scheme locally of finite presentation over `Y`.
* `exists_affineOpen_isLocallyOfFinitePresentation_separation_of_lfp_morphism`: the
  refinement for `Z` a scheme and `g` locally of finite presentation.
* `exists_affineOpen_isLocallyOfFinitePresentation_separation`: the refinement for `Z` and `Y`
  schemes.
* `exists_affine_isLocallyOfFinitePresentation_factorization_of_separation`: the factorization
  hypothesis is implied by the refinement, so the two are equivalent.

## Implementation notes

The separating subset over `X` is the closure of the image of the inverse image of `T`, an
explicit construction and not a choice from an existence statement. The subset `T` itself is
not required to be closed: closedness of the output comes from taking a closure, and only the
subset over the cover has to be closed.

Openness and surjectivity on points of the comparison morphism `|W ×_Y Z'| → |X ×_Y Z'|` are
derived rather than assumed: that morphism is a base change of `c`, the property of having
étale represented base changes is stable under base change by
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`, such a morphism is open on
points by clause (3) of Tag 03BX, and surjectivity on points is stable under base change by
Tag 03MH.

The topologies on point sets are `AlgebraicGeometry.Space.pointTopology`, which is not an
instance. The first results pass them explicitly with `@`; the section
`FinitePresentationSeparation` makes `pointTopology` a local instance.

## References

* [Stacks Project, Tag 02YB](https://stacks.math.columbia.edu/tag/02YB)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 05BD](https://stacks.math.columbia.edu/tag/05BD)
* [Stacks Project, Tag 0CM8](https://stacks.math.columbia.edu/tag/0CM8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Descent of a separating closed subset along the base morphism of a cartesian square of
presheaves

```
P --α₁--> Q
|         |
γ         κ
↓         ↓
P' -α₂--> Q'
```

whose base morphism `κ` is open and surjective on points, along morphisms `π : Q ⟶ R` and
`π' : Q' ⟶ R` with `κ ≫ π' = π`. If a closed `T₀ ⊆ |Q|` receives the image of the inverse
image of `T ⊆ |P'|` and its image in `|R|` misses `r`, then the closure of the image of `T`
in `|Q'|` is closed, receives `T`, and its image in `|R|` still misses `r`. -/
theorem exists_isClosed_separation_of_isPullback
    {P P' Q Q' R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {γ : P ⟶ P'} {α₁ : P ⟶ Q} {α₂ : P' ⟶ Q'} {κ : Q ⟶ Q'}
    (sq : IsPullback γ α₁ α₂ κ) {π : Q ⟶ R} {π' : Q' ⟶ R} (hπ : κ ≫ π' = π)
    (hopen : @IsOpenMap _ _ (pointTopology B S hS Q) (pointTopology B S hS Q')
      (pointsMap B S hS Q κ))
    (hsurj : Function.Surjective (pointsMap B S hS Q κ))
    (T : Set (points B S hS P')) {T₀ : Set (points B S hS Q)}
    (hT₀ : @IsClosed _ (pointTopology B S hS Q) T₀)
    (hsub : pointsMap B S hS P α₁ '' (pointsMap B S hS P γ ⁻¹' T) ⊆ T₀)
    {r : points B S hS R} (hr : r ∉ pointsMap B S hS Q π '' T₀) :
    ∃ T' : Set (points B S hS Q'),
      @IsClosed _ (pointTopology B S hS Q') T' ∧
        T ⊆ pointsMap B S hS P' α₂ ⁻¹' T' ∧
          r ∉ pointsMap B S hS Q' π' '' T' := by
  let _ : TopologicalSpace (points B S hS Q) := pointTopology B S hS Q
  let _ : TopologicalSpace (points B S hS Q') := pointTopology B S hS Q'
  refine ⟨closure (pointsMap B S hS P' α₂ '' T), isClosed_closure,
    fun x hx ↦ subset_closure ⟨x, hx, rfl⟩, ?_⟩
  have hkey : pointsMap B S hS Q κ ⁻¹' closure (pointsMap B S hS P' α₂ '' T) ⊆ T₀ := by
    rw [hopen.preimage_closure_eq_closure_preimage (continuous_pointsMap B S hS κ),
      preimage_image_pointsMap_of_isPullback B S hS sq T]
    exact hT₀.closure_subset_iff.mpr hsub
  rintro ⟨y, hy, hyr⟩
  obtain ⟨x, hx⟩ := hsurj y
  exact hr ⟨x, hkey (by rwa [Set.mem_preimage, hx]), by
    rw [← hπ, pointsMap_comp_apply, hx, hyr]⟩

variable {X Y Z' V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Comparing `W ×_Y Z'` with `X ×_Y Z'` for a morphism `c : W ⟶ X`: the induced morphism is a
base change of `c` along the projection to `X`. -/
private theorem exists_comparison_fst (f : X ⟶ Y) (b : Z' ⟶ Y) (c : W ⟶ X) :
    ∃ κ : pullback (c ≫ f) b ⟶ pullback f b,
      κ ≫ pullback.fst f b = pullback.fst (c ≫ f) b ≫ c ∧
        κ ≫ pullback.snd f b = pullback.snd (c ≫ f) b ∧
          IsPullback κ (pullback.fst (c ≫ f) b) (pullback.fst f b) c :=
  ⟨_, (IsPullback.of_hasPullback f b).flip.lift_snd _ _ _,
    (IsPullback.of_hasPullback f b).flip.lift_fst _ _ _,
    IsPullback.of_right' (IsPullback.of_hasPullback (c ≫ f) b).flip
      (IsPullback.of_hasPullback f b).flip⟩

/-- Comparing `X ×_Y V` with `X ×_Y Z'` for a morphism `a : V ⟶ Z'`: the induced morphism is a
base change of `a` along the projection to `Z'`. -/
private theorem exists_comparison_snd (f : X ⟶ Y) (b : Z' ⟶ Y) (a : V ⟶ Z') :
    ∃ α : pullback f (a ≫ b) ⟶ pullback f b,
      α ≫ pullback.fst f b = pullback.fst f (a ≫ b) ∧
        α ≫ pullback.snd f b = pullback.snd f (a ≫ b) ≫ a ∧
          IsPullback α (pullback.snd f (a ≫ b)) (pullback.snd f b) a :=
  ⟨_, (IsPullback.of_hasPullback f b).lift_fst _ _ _,
    (IsPullback.of_hasPullback f b).lift_snd _ _ _,
    IsPullback.of_right' (IsPullback.of_hasPullback f (a ≫ b))
      (IsPullback.of_hasPullback f b)⟩

/-- An algebraic space over `S` receives a morphism from a representable presheaf which has
étale represented base changes and is surjective on points. -/
theorem exists_etale_atlas_surjective_on_points (hX : IsAlgebraicSpace B S hS X) :
    ∃ (U : BigFppfOver B S hS) (c : yoneda.obj U ⟶ X),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c ∧
        Function.Surjective (pointsMap B S hS (yoneda.obj U) c) := by
  obtain ⟨U, c, hcSurj, hcEt⟩ := hX.exists_atlas
  exact ⟨U, c, hcEt,
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U c).mp hcSurj⟩

/-- **Stacks 0CM8**, the étale-descent step of the proof. Let `f : X ⟶ Y`, `b : Z' ⟶ Y` and
`a : V ⟶ Z'` be morphisms of presheaves on the big fppf site of `S`, and let `c : W ⟶ X` be a
morphism whose represented base changes are étale and which is surjective on points. There
are comparison morphisms `γ`, `α₁`, `α₂`, `κ` filling the square

```
W ×_Y V --α₁--> W ×_Y Z'
   |               |
   γ               κ
   ↓               ↓
X ×_Y V --α₂--> X ×_Y Z'
```

along which clauses (2) and (3) of Tag 0CM8 descend: given a closed subset `T₀` of
`|W ×_Y Z'|` receiving the inverse image of `T ⊆ |X ×_Y V|` and whose image in `|Z'|` misses
`r`, there is a closed `T' ⊆ |X ×_Y Z'|` receiving `T` and whose image in `|Z'|` misses `r`.
Clause (1), that `b` is locally of finite presentation, is a property of `b` alone and is
untouched by the descent. -/
@[stacks 0CM8 "etale-descent step of the proof: clauses (2) and (3) descend along a cover \
of X whose represented base changes are etale and which is surjective on points; the \
reduction to the case of affine schemes and the appeal to Tag 05BD are not included"]
theorem exists_isClosed_separation_of_etale_cover
    (f : X ⟶ Y) (b : Z' ⟶ Y) (a : V ⟶ Z') (c : W ⟶ X)
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hcsurj : Function.Surjective (pointsMap B S hS W c)) :
    ∃ (γ : pullback (c ≫ f) (a ≫ b) ⟶ pullback f (a ≫ b))
      (α₁ : pullback (c ≫ f) (a ≫ b) ⟶ pullback (c ≫ f) b)
      (α₂ : pullback f (a ≫ b) ⟶ pullback f b)
      (κ : pullback (c ≫ f) b ⟶ pullback f b),
      γ ≫ pullback.fst f (a ≫ b) = pullback.fst (c ≫ f) (a ≫ b) ≫ c ∧
        γ ≫ pullback.snd f (a ≫ b) = pullback.snd (c ≫ f) (a ≫ b) ∧
        α₁ ≫ pullback.fst (c ≫ f) b = pullback.fst (c ≫ f) (a ≫ b) ∧
        α₁ ≫ pullback.snd (c ≫ f) b = pullback.snd (c ≫ f) (a ≫ b) ≫ a ∧
        α₂ ≫ pullback.fst f b = pullback.fst f (a ≫ b) ∧
        α₂ ≫ pullback.snd f b = pullback.snd f (a ≫ b) ≫ a ∧
        κ ≫ pullback.fst f b = pullback.fst (c ≫ f) b ≫ c ∧
        κ ≫ pullback.snd f b = pullback.snd (c ≫ f) b ∧
        ∀ (T : Set (points B S hS (pullback f (a ≫ b))))
          (T₀ : Set (points B S hS (pullback (c ≫ f) b))),
          @IsClosed _ (pointTopology B S hS (pullback (c ≫ f) b)) T₀ →
          pointsMap B S hS _ α₁ '' (pointsMap B S hS _ γ ⁻¹' T) ⊆ T₀ →
          ∀ r : points B S hS Z',
            r ∉ pointsMap B S hS _ (pullback.snd (c ≫ f) b) '' T₀ →
            ∃ T' : Set (points B S hS (pullback f b)),
              @IsClosed _ (pointTopology B S hS (pullback f b)) T' ∧
                T ⊆ pointsMap B S hS _ α₂ ⁻¹' T' ∧
                  r ∉ pointsMap B S hS _ (pullback.snd f b) '' T' := by
  obtain ⟨κ, hκ₁, hκ₂, sqκ⟩ := exists_comparison_fst B S hS f b c
  obtain ⟨γ, hγ₁, hγ₂, sqγ⟩ := exists_comparison_fst B S hS f (a ≫ b) c
  obtain ⟨α₁, hα₁₁, hα₁₂, -⟩ := exists_comparison_snd B S hS (c ≫ f) b a
  obtain ⟨α₂, hα₂₁, hα₂₂, -⟩ := exists_comparison_snd B S hS f b a
  have hcomm : α₁ ≫ κ = γ ≫ α₂ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hκ₁, Category.assoc, hα₂₁, ← Category.assoc, hα₁₁, hγ₁]
    · rw [Category.assoc, hκ₂, hα₁₂, Category.assoc, hα₂₂, ← Category.assoc, hγ₂]
  have sq : IsPullback γ α₁ α₂ κ := by
    refine (IsPullback.of_right ?_ hcomm sqκ.flip).flip
    rw [hα₁₁, hα₂₁]
    exact sqγ.flip
  have hstable : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hκet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf κ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sqκ.flip hc
  exact ⟨γ, α₁, α₂, κ, hγ₁, hγ₂, hα₁₁, hα₁₂, hα₂₁, hα₂₂, hκ₁, hκ₂,
    fun T T₀ hT₀ hsub r hr ↦
      exists_isClosed_separation_of_isPullback B S hS sq hκ₂
        (isOpenMap_pointsMap_of_presheafEtale B S hS κ hκet)
        (surjective_pointsMap_of_isPullback B S hS sqκ.flip hcsurj) T hT₀ hsub hr⟩

section FinitePresentationSeparation

attribute [local instance] pointTopology

/-- The comparison between the points of a fibre product of represented presheaves and the
fibre product of the underlying schemes is natural in morphisms of the site: a morphism of
fibre products taken in the site induces, on points, the morphism of fibre products of schemes
it induces there. -/
private theorem pullbackPointsHomeomorph_naturality
    {U₁ U₂ U₃ U₁' U₂' U₃' : BigFppfOver B S hS}
    (φ : U₁ ⟶ U₃) (ψ : U₂ ⟶ U₃) (φ' : U₁' ⟶ U₃') (ψ' : U₂' ⟶ U₃')
    (m : (pullback φ ψ : BigFppfOver B S hS) ⟶ (pullback φ' ψ' : BigFppfOver B S hS))
    (x : points B S hS (pullback (yoneda.map φ) (yoneda.map ψ))) :
    pullbackPointsHomeomorph B S hS φ' ψ'
        (pointsMap B S hS _ ((PreservesPullback.iso yoneda φ ψ).inv ≫ yoneda.map m ≫
          (PreservesPullback.iso yoneda φ' ψ').hom) x) =
      (PreservesPullback.iso (BigFppfOver.toScheme B S hS) φ' ψ').hom
        ((BigFppfOver.toScheme B S hS).map m
          ((PreservesPullback.iso (BigFppfOver.toScheme B S hS) φ ψ).inv
            (pullbackPointsHomeomorph B S hS φ ψ x))) := by
  have hinv : ∀ y : ↥((BigFppfOver.toScheme B S hS).obj (pullback φ ψ)),
      (PreservesPullback.iso (BigFppfOver.toScheme B S hS) φ ψ).inv
        ((PreservesPullback.iso (BigFppfOver.toScheme B S hS) φ ψ).hom y) = y := by
    intro y
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [pullbackPointsHomeomorph_apply, pullbackPointsHomeomorph_apply, ← pointsMap_comp_apply,
    Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id, pointsMap_comp_apply,
    pointsToScheme_pointsMap_yoneda, hinv]

/-- A morphism of fibre products in the target of a functor `F` which is induced by a morphism
`m` of fibre products in the source agrees with `m` under the comparison isomorphisms
`PreservesPullback.iso`. -/
private theorem eq_preservesPullback_iso_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {U₁ U₂ U₃ U₁' U₂' U₃' : C}
    (φ : U₁ ⟶ U₃) (ψ : U₂ ⟶ U₃) (φ' : U₁' ⟶ U₃') (ψ' : U₂' ⟶ U₃')
    (n₁ : U₁ ⟶ U₁') (n₂ : U₂ ⟶ U₂') [HasPullback φ ψ] [HasPullback φ' ψ']
    [HasPullback (F.map φ) (F.map ψ)] [HasPullback (F.map φ') (F.map ψ')]
    [PreservesLimit (cospan φ ψ) F] [PreservesLimit (cospan φ' ψ') F]
    (m : pullback φ ψ ⟶ pullback φ' ψ')
    (hm₁ : m ≫ pullback.fst φ' ψ' = pullback.fst φ ψ ≫ n₁)
    (hm₂ : m ≫ pullback.snd φ' ψ' = pullback.snd φ ψ ≫ n₂)
    (M : pullback (F.map φ) (F.map ψ) ⟶ pullback (F.map φ') (F.map ψ'))
    (hM₁ : M ≫ pullback.fst (F.map φ') (F.map ψ') = pullback.fst (F.map φ) (F.map ψ) ≫ F.map n₁)
    (hM₂ : M ≫ pullback.snd (F.map φ') (F.map ψ') = pullback.snd (F.map φ) (F.map ψ) ≫ F.map n₂) :
    M = (PreservesPullback.iso F φ ψ).inv ≫ F.map m ≫ (PreservesPullback.iso F φ' ψ').hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [hM₁, Category.assoc, Category.assoc, PreservesPullback.iso_hom_fst,
      ← CategoryTheory.Functor.map_comp, hm₁, CategoryTheory.Functor.map_comp,
      ← Category.assoc, PreservesPullback.iso_inv_fst]
  · rw [hM₂, Category.assoc, Category.assoc, PreservesPullback.iso_hom_snd,
      ← CategoryTheory.Functor.map_comp, hm₂, CategoryTheory.Functor.map_comp,
      ← Category.assoc, PreservesPullback.iso_inv_snd]

/-- A morphism `M` of fibre products of represented presheaves and a morphism `N` of the
corresponding fibre products of schemes agree under the comparison
`pullbackPointsHomeomorph` as soon as both are induced, on the two projections, by one morphism
`m` of the site. -/
private theorem pullbackPointsHomeomorph_comparison
    {U₁ U₂ U₃ U₁' U₂' U₃' : BigFppfOver B S hS}
    (φ : U₁ ⟶ U₃) (ψ : U₂ ⟶ U₃) (φ' : U₁' ⟶ U₃') (ψ' : U₂' ⟶ U₃')
    (n₁ : U₁ ⟶ U₁') (n₂ : U₂ ⟶ U₂')
    (m : (pullback φ ψ : BigFppfOver B S hS) ⟶ (pullback φ' ψ' : BigFppfOver B S hS))
    (hm₁ : m ≫ pullback.fst φ' ψ' = pullback.fst φ ψ ≫ n₁)
    (hm₂ : m ≫ pullback.snd φ' ψ' = pullback.snd φ ψ ≫ n₂)
    (M : pullback (yoneda.map φ) (yoneda.map ψ) ⟶ pullback (yoneda.map φ') (yoneda.map ψ'))
    (hM₁ : M ≫ pullback.fst (yoneda.map φ') (yoneda.map ψ') =
      pullback.fst (yoneda.map φ) (yoneda.map ψ) ≫ yoneda.map n₁)
    (hM₂ : M ≫ pullback.snd (yoneda.map φ') (yoneda.map ψ') =
      pullback.snd (yoneda.map φ) (yoneda.map ψ) ≫ yoneda.map n₂)
    (N : (pullback ((BigFppfOver.toScheme B S hS).map φ)
        ((BigFppfOver.toScheme B S hS).map ψ) : Scheme.{u}) ⟶
      pullback ((BigFppfOver.toScheme B S hS).map φ') ((BigFppfOver.toScheme B S hS).map ψ'))
    (hN₁ : N ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map φ')
        ((BigFppfOver.toScheme B S hS).map ψ') =
      pullback.fst ((BigFppfOver.toScheme B S hS).map φ) ((BigFppfOver.toScheme B S hS).map ψ) ≫
        (BigFppfOver.toScheme B S hS).map n₁)
    (hN₂ : N ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map φ')
        ((BigFppfOver.toScheme B S hS).map ψ') =
      pullback.snd ((BigFppfOver.toScheme B S hS).map φ) ((BigFppfOver.toScheme B S hS).map ψ) ≫
        (BigFppfOver.toScheme B S hS).map n₂)
    (x : points B S hS (pullback (yoneda.map φ) (yoneda.map ψ))) :
    pullbackPointsHomeomorph B S hS φ' ψ' (pointsMap B S hS _ M x) =
      N (pullbackPointsHomeomorph B S hS φ ψ x) := by
  have hMeq := eq_preservesPullback_iso_comp yoneda φ ψ φ' ψ' n₁ n₂ m hm₁ hm₂ M hM₁ hM₂
  have hNeq := eq_preservesPullback_iso_comp (BigFppfOver.toScheme B S hS) φ ψ φ' ψ' n₁ n₂ m
    hm₁ hm₂ N hN₁ hN₂
  rw [hMeq, hNeq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact pullbackPointsHomeomorph_naturality B S hS φ ψ φ' ψ' m x

/-- The inclusion of an open of a representing scheme, as a morphism of the site, is an open
immersion, and every point of `|Z₀|` lying in the open comes from a point of the open. -/
private theorem exists_point_openSiteObject {Z₀ : BigFppfOver B S hS}
    (VO : ((BigFppfOver.toScheme B S hS).obj Z₀).Opens) (z : points B S hS (yoneda.obj Z₀))
    (hzVO : pointsToScheme B S hS Z₀ z ∈ VO) :
    ∃ v : points B S hS (yoneda.obj (openSiteObject B S hS Z₀ VO)),
      pointsMap B S hS _ (yoneda.map (openSiteObjectHom B S hS Z₀ VO)) v = z ∧
      AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS Z₀ VO)) := by
  obtain ⟨v, hv⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS
    (openSiteObjectHom B S hS Z₀ VO) z (by rw [map_openSiteObjectHom]; exact ⟨⟨_, hzVO⟩, rfl⟩)
  refine ⟨v, hv, ?_⟩
  rw [map_openSiteObjectHom]
  exact (inferInstance : AlgebraicGeometry.IsOpenImmersion VO.ι)

/-- **Stacks 05BD on the point spaces of representable presheaves.** Let `w : W ⟶ U` and
`α₀ : V₀ ⟶ U` be morphisms of the big fppf site of `S` with affine source and target, let
`v₀` be a point of `V₀`, and let `C` be a closed subset of `|W ×_U V₀|` whose image in `|V₀|`
misses `v₀`. Then `C` can be separated from `v₀` after shrinking `V₀` to an affine open
neighbourhood `Vs` of `v₀` and factoring `Vs ⟶ U` through an affine `Z'` which is locally of
finite presentation over `U`: there is a closed subset `C'` of `|W ×_U Z'|` whose image in
`|Z'|` misses the image of `v₀` and which receives `C` along the two comparison morphisms.
Moreover `jV : Vs ⟶ V₀` is an étale open immersion. -/
private theorem exists_separation_representable_isOpenImmersion
    {U W V₀ : BigFppfOver B S hS}
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hV₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (w : W ⟶ U) (α₀ : V₀ ⟶ U) (v₀ : points B S hS (yoneda.obj V₀))
    (C : Set (points B S hS (pullback (yoneda.map w) (yoneda.map α₀))))
    (hC : IsClosed C)
    (hv₀ : v₀ ∉ pointsMap B S hS _ (pullback.snd (yoneda.map w) (yoneda.map α₀)) '' C) :
    ∃ (Vs Z' : BigFppfOver B S hS) (jV : Vs ⟶ V₀) (β : Z' ⟶ U) (α' : Vs ⟶ Z')
      (v : points B S hS (yoneda.obj Vs))
      (C' : Set (points B S hS (pullback (yoneda.map w) (yoneda.map β)))),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Vs) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map jV) ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jV) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map β) ∧
      pointsMap B S hS _ (yoneda.map jV) v = v₀ ∧
      jV ≫ α₀ = α' ≫ β ∧
      IsClosed C' ∧
      pointsMap B S hS _ (yoneda.map α') v ∉
        pointsMap B S hS _ (pullback.snd (yoneda.map w) (yoneda.map β)) '' C' ∧
      ∀ (μ : pullback (yoneda.map w) (yoneda.map (α' ≫ β)) ⟶
          pullback (yoneda.map w) (yoneda.map α₀))
        (μZ : pullback (yoneda.map w) (yoneda.map (α' ≫ β)) ⟶
          pullback (yoneda.map w) (yoneda.map β)),
        μ ≫ pullback.fst (yoneda.map w) (yoneda.map α₀) =
          pullback.fst (yoneda.map w) (yoneda.map (α' ≫ β)) →
        μ ≫ pullback.snd (yoneda.map w) (yoneda.map α₀) =
          pullback.snd (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map jV →
        μZ ≫ pullback.fst (yoneda.map w) (yoneda.map β) =
          pullback.fst (yoneda.map w) (yoneda.map (α' ≫ β)) →
        μZ ≫ pullback.snd (yoneda.map w) (yoneda.map β) =
          pullback.snd (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map α' →
        ∀ x, pointsMap B S hS _ μ x ∈ C → pointsMap B S hS _ μZ x ∈ C' := by
  classical
  have hV₀aff' := hV₀aff
  have hEclosed : IsClosed (pullbackPointsHomeomorph B S hS w α₀ '' C) :=
    (isClosed_points_pullback_iff B S hS w α₀ C).mp hC
  have hEt : pointsToScheme B S hS V₀ v₀ ∉
      pullback.snd ((BigFppfOver.toScheme B S hS).map w)
        ((BigFppfOver.toScheme B S hS).map α₀) '' (pullbackPointsHomeomorph B S hS w α₀ '' C) :=
    (notMem_image_pointsMap_pullback_snd_iff B S hS w α₀ C v₀).mp hv₀
  obtain ⟨V', htV', Zs, hZsaff, bs, hbs, as, habs, E', hE'closed, pc, qc,
    hpc₁, hpc₂, hqc₁, hqc₂, hq5, hq6⟩ :=
    exists_affine_locallyFinitePresentation_separation_isClosed
      ((BigFppfOver.toScheme B S hS).map w) ((BigFppfOver.toScheme B S hS).map α₀)
      (pointsToScheme B S hS V₀ v₀) _ hEclosed hEt
  set Vs : BigFppfOver B S hS := openSiteObject B S hS V₀ V'.1 with hVsdef
  set jV : Vs ⟶ V₀ := openSiteObjectHom B S hS V₀ V'.1 with hjVdef
  have hjV : (BigFppfOver.toScheme B S hS).map jV = V'.1.ι :=
    map_openSiteObjectHom B S hS V₀ V'.1
  have hVsaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Vs) := V'.2
  have hZsaff' : IsAffine Zs := hZsaff
  have hbs' : LocallyOfFinitePresentation bs := hbs
  have hZssize : Zs.size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact bs U.left.property
  set Z' : BigFppfOver B S hS :=
    Over.mk (B.inclusion.preimage (X := B.obj hZssize) (Y := U.left) bs ≫ U.hom) with hZ'def
  set β : Z' ⟶ U :=
    Over.homMk (B.inclusion.preimage (X := B.obj hZssize) (Y := U.left) bs) rfl with hβdef
  have hβ : (BigFppfOver.toScheme B S hS).map β = bs := B.inclusion.map_preimage _
  have hasval : B.inclusion.map (B.inclusion.preimage
      (show B.inclusion.obj Vs.left ⟶ B.inclusion.obj Z'.left from as)) = as :=
    B.inclusion.map_preimage _
  have hcompose : B.inclusion.preimage
        (show B.inclusion.obj Vs.left ⟶ B.inclusion.obj Z'.left from as) ≫
      B.inclusion.preimage (X := B.obj hZssize) (Y := U.left) bs = jV.left ≫ α₀.left := by
    refine B.inclusion.map_injective ?_
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hasval,
      B.inclusion.map_preimage]
    change as ≫ bs =
      (BigFppfOver.toScheme B S hS).map jV ≫ (BigFppfOver.toScheme B S hS).map α₀
    rw [hjV]
    exact habs.symm
  set α' : Vs ⟶ Z' :=
    Over.homMk (B.inclusion.preimage
      (show B.inclusion.obj Vs.left ⟶ B.inclusion.obj Z'.left from as)) (by
      change _ ≫ B.inclusion.preimage (X := B.obj hZssize) (Y := U.left) bs ≫ U.hom = Vs.hom
      rw [← Category.assoc, hcompose, Category.assoc, Over.w, Over.w]) with hα'def
  have hα' : (BigFppfOver.toScheme B S hS).map α' = as := hasval
  have hjVα₀ : jV ≫ α₀ = α' ≫ β := Over.OverMorphism.ext hcompose.symm
  obtain ⟨v, hv, -⟩ := exists_point_openSiteObject B S hS V'.1 v₀ htV'
  have hAB : (BigFppfOver.toScheme B S hS).map (α' ≫ β) =
      V'.1.ι ≫ (BigFppfOver.toScheme B S hS).map α₀ := by
    rw [CategoryTheory.Functor.map_comp, hα', hβ]
    exact habs.symm
  set qcHom : (pullback ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map β) : Scheme.{u}) ⟶
      pullback ((BigFppfOver.toScheme B S hS).map w) bs :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _)
      (by rw [← hβ]; exact pullback.condition) with hqcHomdef
  set qcInv : (pullback ((BigFppfOver.toScheme B S hS).map w) bs : Scheme.{u}) ⟶
      pullback ((BigFppfOver.toScheme B S hS).map w) ((BigFppfOver.toScheme B S hS).map β) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _)
      (by rw [hβ]; exact pullback.condition) with hqcInvdef
  have hqcInvHom : qcInv ≫ qcHom = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [hqcHomdef, hqcInvdef, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        Category.id_comp]
  set χ := pullback.lift (f := (BigFppfOver.toScheme B S hS).map w)
      (g := V'.1.ι ≫ (BigFppfOver.toScheme B S hS).map α₀)
      (pullback.fst ((BigFppfOver.toScheme B S hS).map w)
        ((BigFppfOver.toScheme B S hS).map (α' ≫ β)))
      (pullback.snd ((BigFppfOver.toScheme B S hS).map w)
        ((BigFppfOver.toScheme B S hS).map (α' ≫ β)))
      (by rw [← hAB]; exact pullback.condition) with hχdef
  have hχfst : χ ≫ pullback.fst _ _ = pullback.fst ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map (α' ≫ β)) := pullback.lift_fst _ _ _
  have hχsnd : χ ≫ pullback.snd _ _ = pullback.snd ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map (α' ≫ β)) := pullback.lift_snd _ _ _
  have hmVcond : pullback.fst w (α' ≫ β) ≫ w = (pullback.snd w (α' ≫ β) ≫ jV) ≫ α₀ := by
    rw [Category.assoc, hjVα₀]
    exact pullback.condition
  have hmZcond : pullback.fst w (α' ≫ β) ≫ w = (pullback.snd w (α' ≫ β) ≫ α') ≫ β := by
    rw [Category.assoc]
    exact pullback.condition
  have hcompV : ∀ (μ : pullback (yoneda.map w) (yoneda.map (α' ≫ β)) ⟶
        pullback (yoneda.map w) (yoneda.map α₀)),
      μ ≫ pullback.fst (yoneda.map w) (yoneda.map α₀) =
        pullback.fst (yoneda.map w) (yoneda.map (α' ≫ β)) →
      μ ≫ pullback.snd (yoneda.map w) (yoneda.map α₀) =
        pullback.snd (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map jV →
      ∀ x, pullbackPointsHomeomorph B S hS w α₀ (pointsMap B S hS _ μ x) =
        (χ ≫ pc) (pullbackPointsHomeomorph B S hS w (α' ≫ β) x) := by
    intro μ h1 h2 x
    refine pullbackPointsHomeomorph_comparison B S hS w (α' ≫ β) w α₀ (𝟙 W) jV
      (pullback.lift _ _ hmVcond) (by rw [pullback.lift_fst, Category.comp_id])
      (pullback.lift_snd _ _ _) μ ?_ h2 (χ ≫ pc) ?_ ?_ x
    · rw [h1, CategoryTheory.Functor.map_id, Category.comp_id]
    · rw [Category.assoc, hpc₁, hχfst, CategoryTheory.Functor.map_id, Category.comp_id]
    · rw [Category.assoc, hpc₂, ← Category.assoc, hχsnd, hjV]
      rfl
  have hcompZ : ∀ (μZ : pullback (yoneda.map w) (yoneda.map (α' ≫ β)) ⟶
        pullback (yoneda.map w) (yoneda.map β)),
      μZ ≫ pullback.fst (yoneda.map w) (yoneda.map β) =
        pullback.fst (yoneda.map w) (yoneda.map (α' ≫ β)) →
      μZ ≫ pullback.snd (yoneda.map w) (yoneda.map β) =
        pullback.snd (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map α' →
      ∀ x, pullbackPointsHomeomorph B S hS w β (pointsMap B S hS _ μZ x) =
        (χ ≫ qc ≫ qcInv) (pullbackPointsHomeomorph B S hS w (α' ≫ β) x) := by
    intro μZ h3 h4 x
    refine pullbackPointsHomeomorph_comparison B S hS w (α' ≫ β) w β (𝟙 W) α'
      (pullback.lift _ _ hmZcond) (by rw [pullback.lift_fst, Category.comp_id])
      (pullback.lift_snd _ _ _) μZ ?_ h4 (χ ≫ qc ≫ qcInv) ?_ ?_ x
    · rw [h3, CategoryTheory.Functor.map_id, Category.comp_id]
    · rw [Category.assoc, Category.assoc, hqcInvdef, pullback.lift_fst, hqc₁, hχfst,
        CategoryTheory.Functor.map_id, Category.comp_id]
    · rw [Category.assoc, Category.assoc, hqcInvdef, pullback.lift_snd, hqc₂, ← Category.assoc,
        hχsnd, hα']
      rfl
  have hvpt : V'.1.ι (pointsToScheme B S hS Vs v) = pointsToScheme B S hS V₀ v₀ := by
    have hnat := pointsToScheme_pointsMap_yoneda B S hS jV v
    rw [hv, hjV] at hnat
    exact hnat.symm
  refine ⟨Vs, Z', jV, β, α', v,
    (fun y => qcHom (pullbackPointsHomeomorph B S hS w β y)) ⁻¹' E',
    hVsaff, hZsaff', by rw [hjV]; exact (inferInstance : AlgebraicGeometry.Etale V'.1.ι),
    by rw [hjV]; exact (inferInstance : AlgebraicGeometry.IsOpenImmersion V'.1.ι),
    by rwa [hβ], hv, hjVα₀, ?_, ?_, ?_⟩
  · exact hE'closed.preimage (by fun_prop)
  · rintro ⟨y, hy, hyv⟩
    refine hq5 ⟨qcHom (pullbackPointsHomeomorph B S hS w β y), hy, ?_⟩
    have h1 : pullback.snd ((BigFppfOver.toScheme B S hS).map w) bs
        (qcHom (pullbackPointsHomeomorph B S hS w β y)) =
        pullback.snd ((BigFppfOver.toScheme B S hS).map w)
          ((BigFppfOver.toScheme B S hS).map β) (pullbackPointsHomeomorph B S hS w β y) := by
      rw [← Scheme.Hom.comp_apply, hqcHomdef, pullback.lift_snd]
    rw [h1, ← pointsToScheme_pointsMap_pullback_snd, hyv, pointsToScheme_pointsMap_yoneda, hα']
    congr 1
    exact Subtype.ext hvpt
  · intro μ μZ h1 h2 h3 h4 x hx
    change qcHom (pullbackPointsHomeomorph B S hS w β (pointsMap B S hS _ μZ x)) ∈ E'
    rw [hcompZ μZ h3 h4 x]
    have hid : qcHom ((χ ≫ qc ≫ qcInv) (pullbackPointsHomeomorph B S hS w (α' ≫ β) x)) =
        (χ ≫ qc) (pullbackPointsHomeomorph B S hS w (α' ≫ β) x) := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hqcInvHom, Category.comp_id]
    rw [hid]
    refine hq6 ?_
    change pc (χ (pullbackPointsHomeomorph B S hS w (α' ≫ β) x)) ∈
      pullbackPointsHomeomorph B S hS w α₀ '' C
    rw [← Scheme.Hom.comp_apply, ← hcompV μ h1 h2 x]
    exact ⟨_, hx, rfl⟩

/-- **Stacks 05BD on the point spaces of representable presheaves**, without recording that
the shrinking `jV` is an open immersion: the form of
`exists_separation_representable_isOpenImmersion` with that conjunct forgotten. -/
private theorem exists_separation_representable
    {U W V₀ : BigFppfOver B S hS}
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hV₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (w : W ⟶ U) (α₀ : V₀ ⟶ U) (v₀ : points B S hS (yoneda.obj V₀))
    (C : Set (points B S hS (pullback (yoneda.map w) (yoneda.map α₀))))
    (hC : IsClosed C)
    (hv₀ : v₀ ∉ pointsMap B S hS _ (pullback.snd (yoneda.map w) (yoneda.map α₀)) '' C) :
    ∃ (Vs Z' : BigFppfOver B S hS) (jV : Vs ⟶ V₀) (β : Z' ⟶ U) (α' : Vs ⟶ Z')
      (v : points B S hS (yoneda.obj Vs))
      (C' : Set (points B S hS (pullback (yoneda.map w) (yoneda.map β)))),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Vs) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map jV) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map β) ∧
      pointsMap B S hS _ (yoneda.map jV) v = v₀ ∧
      jV ≫ α₀ = α' ≫ β ∧
      IsClosed C' ∧
      pointsMap B S hS _ (yoneda.map α') v ∉
        pointsMap B S hS _ (pullback.snd (yoneda.map w) (yoneda.map β)) '' C' ∧
      ∀ (μ : pullback (yoneda.map w) (yoneda.map (α' ≫ β)) ⟶
          pullback (yoneda.map w) (yoneda.map α₀))
        (μZ : pullback (yoneda.map w) (yoneda.map (α' ≫ β)) ⟶
          pullback (yoneda.map w) (yoneda.map β)),
        μ ≫ pullback.fst (yoneda.map w) (yoneda.map α₀) =
          pullback.fst (yoneda.map w) (yoneda.map (α' ≫ β)) →
        μ ≫ pullback.snd (yoneda.map w) (yoneda.map α₀) =
          pullback.snd (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map jV →
        μZ ≫ pullback.fst (yoneda.map w) (yoneda.map β) =
          pullback.fst (yoneda.map w) (yoneda.map (α' ≫ β)) →
        μZ ≫ pullback.snd (yoneda.map w) (yoneda.map β) =
          pullback.snd (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map α' →
        ∀ x, pointsMap B S hS _ μ x ∈ C → pointsMap B S hS _ μZ x ∈ C' := by
  obtain ⟨Vs, Z', jV, β, α', v, C', h1, h2, h3, -, h5⟩ :=
    exists_separation_representable_isOpenImmersion B S hS hUaff hWaff hV₀aff w α₀ v₀ C hC hv₀
  exact ⟨Vs, Z', jV, β, α', v, C', h1, h2, h3, h5⟩

/-- **Stacks 0CM8, the argument of the source with its two choices of chart made into
hypotheses.** Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over `S`, let
`g : Z ⟶ Y` be a morphism of algebraic spaces, let `z` be a point of `|Z|`, and let `T` be a
closed subset of `|X ×_Y Z|` whose image in `|Z|` misses `z`. Suppose given an affine `U` and
an `ι : U ⟶ Y` which is locally of finite presentation, together with an affine `V₀`, a point
`v₀` of `|V₀|` above `z`, and a factorization `p₀ ≫ g = α₀ ≫ ι` of `V₀ ⟶ Y` through `U`.
Then the conclusion of Tag 0CM8 holds with `V` an affine *open* of `V₀` and `p = jV ≫ p₀`: all
three clauses of the source, namely that `b` is locally of finite presentation, that the image
of `T'` in `|Z'|` misses the image of `v`, and that `T'` receives the inverse image of `T`, hold
for that `V`.

The source's own proof is the case where `ι` is an affine étale chart of `Y` through the image
of `z` and `p₀` comes from an affine étale chart of `Z ×_Y U` through a point over `z`; that
is `AlgebraicGeometry.Space.exists_affine_etale_isLocallyOfFinitePresentation_separation`
below, where `p = jV ≫ p₀` is étale because `jV` is an open immersion. Isolating the chart
data is what makes the refinement of the source available: when `p₀` is itself an open
immersion — which is what happens when `Z` is a scheme and the factorization through `U` can
be arranged Zariski-locally at `z` — the composite `p` is an open immersion too, so `V` is an
affine open neighbourhood of `z`.

Étaleness of `ι` is not used: the chart enters the argument only through `Z' ⟶ U ⟶ Y` having
to be locally of finite presentation, and `Z' ⟶ U` is. Asking only that `ι` be locally of
finite presentation is what makes the hypothesis sharp, because the conclusion hands back a
factorization of exactly that kind, as
`AlgebraicGeometry.Space.exists_affine_isLocallyOfFinitePresentation_factorization_of_separation`
records. -/
theorem exists_separation_of_affine_lfp_chart
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : IsQuasiCompact B S hS f)
    (z : points B S hS Z) (T : Set (points B S hS (pullback f g))) (hT : IsClosed T)
    (hz : z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T)
    {U V₀ : BigFppfOver B S hS} (ι : yoneda.obj U ⟶ Y)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hιlfp : IsLocallyOfFinitePresentation B S hS ι)
    (hV₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (p₀ : yoneda.obj V₀ ⟶ Z) (α₀ : V₀ ⟶ U) (hfac₀ : p₀ ≫ g = yoneda.map α₀ ≫ ι)
    (v₀ : points B S hS (yoneda.obj V₀))
    (hp₀v : pointsMap B S hS (yoneda.obj V₀) p₀ v₀ = z) :
    ∃ (V Z' : BigFppfOver B S hS) (jV : V ⟶ V₀)
      (v : points B S hS (yoneda.obj V)) (a : yoneda.obj V ⟶ yoneda.obj Z')
      (b : yoneda.obj Z' ⟶ Y) (T' : Set (points B S hS (pullback f b)))
      (r : pullback f ((yoneda.map jV ≫ p₀) ≫ g) ⟶ pullback f g)
      (q : pullback f ((yoneda.map jV ≫ p₀) ≫ g) ⟶ pullback f b),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map jV) ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jV) ∧
      pointsMap B S hS (yoneda.obj V) (yoneda.map jV) v = v₀ ∧
      pointsMap B S hS (yoneda.obj V) (yoneda.map jV ≫ p₀) v = z ∧
      (yoneda.map jV ≫ p₀) ≫ g = a ≫ b ∧
      IsLocallyOfFinitePresentation B S hS b ∧
      IsClosed T' ∧
      pointsMap B S hS (yoneda.obj V) a v ∉
        pointsMap B S hS (pullback f b) (pullback.snd f b) '' T' ∧
      r ≫ pullback.fst f g = pullback.fst f ((yoneda.map jV ≫ p₀) ≫ g) ∧
      r ≫ pullback.snd f g =
        pullback.snd f ((yoneda.map jV ≫ p₀) ≫ g) ≫ (yoneda.map jV ≫ p₀) ∧
      IsPullback r (pullback.snd f ((yoneda.map jV ≫ p₀) ≫ g)) (pullback.snd f g)
        (yoneda.map jV ≫ p₀) ∧
      q ≫ pullback.fst f b = pullback.fst f ((yoneda.map jV ≫ p₀) ≫ g) ∧
      q ≫ pullback.snd f b = pullback.snd f ((yoneda.map jV ≫ p₀) ≫ g) ≫ a ∧
      pointsMap B S hS (pullback f ((yoneda.map jV ≫ p₀) ≫ g)) q ''
        (pointsMap B S hS (pullback f ((yoneda.map jV ≫ p₀) ≫ g)) r ⁻¹' T) ⊆ T' := by
  classical
  have hyU := isAlgebraicSpace_yoneda B S hS U
  have hUcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  have hqcU : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    ⟨U, 𝟙 _, hUcompact, presheaf_surjective_id B S hS U, isEtale_id B S hS _⟩
  have hXU : IsAlgebraicSpace B S hS (pullback f ι) :=
    isAlgebraicSpace_pullback B S hS f ι hX hyU hY
  have hXUqc : IsQuasiCompactSpace B S hS (pullback f ι) :=
    IsQuasiCompactSpace.of_iso B S hS (hf (yoneda.obj U) hyU hqcU ι) (pullbackSymmetry ι f)
  obtain ⟨W, c, hWaff, hcsurj, hcet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hXU).mp hXUqc
  obtain ⟨w, hw⟩ : ∃ w : W ⟶ U, yoneda.map w = c ≫ pullback.snd f ι :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  set cX : yoneda.obj W ⟶ X := c ≫ pullback.fst f ι with hcXdef
  have hcXfac : cX ≫ f = yoneda.map w ≫ ι := by
    rw [hcXdef, hw, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨r₀, hr₀₁, hr₀₂, -⟩ := exists_comparison_snd B S hS f g p₀
  have hδcond : (pullback.fst (yoneda.map w) (yoneda.map α₀) ≫ cX) ≫ f =
      pullback.snd (yoneda.map w) (yoneda.map α₀) ≫ (p₀ ≫ g) := by
    rw [Category.assoc, hcXfac, hfac₀, ← Category.assoc, ← Category.assoc, pullback.condition]
  obtain ⟨δ₀, hδ₁, hδ₂⟩ := pullback.lift' _ _ hδcond
  set C₀ : Set (points B S hS (pullback (yoneda.map w) (yoneda.map α₀))) :=
    pointsMap B S hS _ δ₀ ⁻¹' (pointsMap B S hS _ r₀ ⁻¹' T) with hC₀def
  have hC₀ : IsClosed C₀ :=
    (hT.preimage (continuous_pointsMap B S hS r₀)).preimage (continuous_pointsMap B S hS δ₀)
  have hnot : v₀ ∉ pointsMap B S hS _ (pullback.snd (yoneda.map w) (yoneda.map α₀)) '' C₀ := by
    rintro ⟨x, hx, hxv⟩
    refine hz ⟨pointsMap B S hS _ r₀ (pointsMap B S hS _ δ₀ x), hx, ?_⟩
    have h1 : pointsMap B S hS _ (pullback.snd f g)
          (pointsMap B S hS _ r₀ (pointsMap B S hS _ δ₀ x))
        = pointsMap B S hS _ ((δ₀ ≫ r₀) ≫ pullback.snd f g) x := by
      simp only [pointsMap_comp_apply]
    have h2 : (δ₀ ≫ r₀) ≫ pullback.snd f g
        = pullback.snd (yoneda.map w) (yoneda.map α₀) ≫ p₀ := by
      rw [Category.assoc, hr₀₂, ← Category.assoc, hδ₂]
    rw [h1, h2, pointsMap_comp_apply, hxv, hp₀v]
  obtain ⟨Vs, Z', jV, β, α', v, C', hVsaff, hZ'aff, hjVetale, hjVopen, hβlfp, hv, hjVα₀,
    hC'closed, hnotC', hkey⟩ :=
    exists_separation_representable_isOpenImmersion B S hS hUaff hWaff hV₀aff w α₀ v₀ C₀ hC₀ hnot
  have hpg : (yoneda.map jV ≫ p₀) ≫ g = yoneda.map α' ≫ yoneda.map β ≫ ι := by
    rw [Category.assoc, hfac₀, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hjVα₀,
      CategoryTheory.Functor.map_comp, Category.assoc]
  have hpv : pointsMap B S hS _ (yoneda.map jV ≫ p₀) v = z := by
    rw [pointsMap_comp_apply, hv, hp₀v]
  have hblfp : IsLocallyOfFinitePresentation B S hS (yoneda.map β ≫ ι) :=
    isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS Z') hyU hY
      (yoneda.map β) ι (isLocallyOfFinitePresentation_yoneda_map B S hS β hβlfp) hιlfp
  have hcsurjpts : Function.Surjective (pointsMap B S hS (yoneda.obj W) c) :=
    (surjective_iff_surjective_pointsMap B S hS _ hXU W c).mp hcsurj
  obtain ⟨γ, a₁, a₂, κ, hγ₁, hγ₂, ha₁₁, ha₁₂, ha₂₁, ha₂₂, hκ₁, hκ₂, hdesc⟩ :=
    exists_isClosed_separation_of_etale_cover B S hS (pullback.snd f ι) (yoneda.map β)
      (yoneda.map α') c (presheaf_etale_of_isEtale B S hS hcet) hcsurjpts
  have hρcond : pullback.fst (c ≫ pullback.snd f ι) (yoneda.map β) ≫ yoneda.map w =
      pullback.snd (c ≫ pullback.snd f ι) (yoneda.map β) ≫ yoneda.map β := by
    rw [hw]
    exact pullback.condition
  obtain ⟨ρ, hρfst, hρsnd⟩ := pullback.lift' _ _ hρcond
  have hρPcond : pullback.fst (c ≫ pullback.snd f ι)
        (yoneda.map α' ≫ yoneda.map β) ≫ yoneda.map w =
      pullback.snd (c ≫ pullback.snd f ι) (yoneda.map α' ≫ yoneda.map β) ≫
        yoneda.map (α' ≫ β) := by
    rw [hw, CategoryTheory.Functor.map_comp]
    exact pullback.condition
  obtain ⟨ρP, hρPfst, hρPsnd⟩ := pullback.lift' _ _ hρPcond
  have hμcond : pullback.fst (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map w =
      (pullback.snd (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map jV) ≫ yoneda.map α₀ := by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hjVα₀]
    exact pullback.condition
  obtain ⟨μ, hμfst, hμsnd⟩ := pullback.lift' _ _ hμcond
  have hμZcond : pullback.fst (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map w =
      (pullback.snd (yoneda.map w) (yoneda.map (α' ≫ β)) ≫ yoneda.map α') ≫ yoneda.map β := by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
    exact pullback.condition
  obtain ⟨μZ, hμZfst, hμZsnd⟩ := pullback.lift' _ _ hμZcond
  have hpg' : yoneda.map jV ≫ p₀ ≫ g = yoneda.map α' ≫ yoneda.map β ≫ ι :=
    (Category.assoc _ _ _).symm.trans hpg
  have hηcond : (pullback.fst (pullback.snd f ι) (yoneda.map α' ≫ yoneda.map β) ≫
        pullback.fst f ι) ≫ f =
      (pullback.snd (pullback.snd f ι) (yoneda.map α' ≫ yoneda.map β) ≫
        (yoneda.map jV ≫ p₀)) ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
    simp only [Category.assoc, hpg']
  obtain ⟨η, hηfst, hηsnd⟩ := pullback.lift' _ _ hηcond
  have hν₁cond : pullback.fst f ((yoneda.map jV ≫ p₀) ≫ g) ≫ f =
      (pullback.snd f ((yoneda.map jV ≫ p₀) ≫ g) ≫ yoneda.map (α' ≫ β)) ≫ ι := by
    rw [pullback.condition]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, hpg']
  obtain ⟨ν₁, hν₁fst, hν₁snd⟩ := pullback.lift' _ _ hν₁cond
  have hνcond : ν₁ ≫ pullback.snd f ι =
      pullback.snd f ((yoneda.map jV ≫ p₀) ≫ g) ≫ (yoneda.map α' ≫ yoneda.map β) := by
    rw [hν₁snd, CategoryTheory.Functor.map_comp]
  obtain ⟨ν, hνfst, hνsnd⟩ := pullback.lift' _ _ hνcond
  obtain ⟨r, hr₁, hr₂, sqr⟩ := exists_comparison_snd B S hS f g (yoneda.map jV ≫ p₀)
  have hqqcond : pullback.fst f ((yoneda.map jV ≫ p₀) ≫ g) ≫ f =
      (pullback.snd f ((yoneda.map jV ≫ p₀) ≫ g) ≫ yoneda.map α') ≫ (yoneda.map β ≫ ι) := by
    rw [pullback.condition]
    simp only [Category.assoc, hpg']
  obtain ⟨qq, hqqfst, hqqsnd⟩ := pullback.lift' _ _ hqqcond
  set eZ := pullbackLeftPullbackSndIso f ι (yoneda.map β) with heZdef
  have hνη : ν ≫ η = r := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc ν η, hηfst, ← Category.assoc ν, hνfst, hν₁fst, hr₁]
    · rw [Category.assoc ν η, hηsnd, ← Category.assoc ν, hνsnd, hr₂]
  have hνq : ν ≫ a₂ ≫ eZ.hom = qq := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc ν (a₂ ≫ eZ.hom), Category.assoc a₂ eZ.hom, heZdef,
        pullbackLeftPullbackSndIso_hom_fst, ← Category.assoc a₂, ha₂₁,
        ← Category.assoc ν, hνfst, hν₁fst, hqqfst]
    · rw [Category.assoc ν (a₂ ≫ eZ.hom), Category.assoc a₂ eZ.hom, heZdef,
        pullbackLeftPullbackSndIso_hom_snd, ha₂₂, ← Category.assoc ν, hνsnd, hqqsnd]
  have hT₀closed : IsClosed (pointsMap B S hS _ ρ ⁻¹' C') :=
    hC'closed.preimage (continuous_pointsMap B S hS ρ)
  have hchain : ρP ≫ μ ≫ δ₀ ≫ r₀ = γ ≫ η := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, hcXdef, hr₀₁, hδ₁, reassoc_of% hμfst, reassoc_of% hρPfst,
        hηfst, reassoc_of% hγ₁]
    · simp only [Category.assoc, hr₀₂, reassoc_of% hδ₂, reassoc_of% hμsnd,
        reassoc_of% hρPsnd, hηsnd, reassoc_of% hγ₂]
  have hchainZ : ρP ≫ μZ = a₁ ≫ ρ := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, hμZfst, hρPfst, hρfst, ha₁₁]
    · simp only [Category.assoc, hμZsnd, reassoc_of% hρPsnd, hρsnd, ha₁₂]
  have hsub : pointsMap B S hS _ a₁ ''
      (pointsMap B S hS _ γ ⁻¹' (pointsMap B S hS _ η ⁻¹' T)) ⊆
      pointsMap B S hS _ ρ ⁻¹' C' := by
    rintro _ ⟨y, hy, rfl⟩
    change pointsMap B S hS _ ρ (pointsMap B S hS _ a₁ y) ∈ C'
    have h1 : pointsMap B S hS _ ρ (pointsMap B S hS _ a₁ y) =
        pointsMap B S hS _ μZ (pointsMap B S hS _ ρP y) := by
      simp only [← pointsMap_comp_apply, hchainZ]
    rw [h1]
    refine hkey μ μZ hμfst hμsnd hμZfst hμZsnd _ ?_
    change pointsMap B S hS _ r₀ (pointsMap B S hS _ δ₀ (pointsMap B S hS _ μ
      (pointsMap B S hS _ ρP y))) ∈ T
    have h2 : pointsMap B S hS _ r₀ (pointsMap B S hS _ δ₀ (pointsMap B S hS _ μ
          (pointsMap B S hS _ ρP y))) = pointsMap B S hS _ η (pointsMap B S hS _ γ y) := by
      simp only [← pointsMap_comp_apply, Category.assoc]
      rw [hchain]
    rwa [h2]
  have hr' : pointsMap B S hS _ (yoneda.map α') v ∉
      pointsMap B S hS _ (pullback.snd (c ≫ pullback.snd f ι) (yoneda.map β)) ''
        (pointsMap B S hS _ ρ ⁻¹' C') := by
    rintro ⟨y, hy, hyv⟩
    refine hnotC' ⟨pointsMap B S hS _ ρ y, hy, ?_⟩
    rw [← pointsMap_comp_apply, hρsnd, hyv]
  obtain ⟨TU, hTUclosed, hTUsub, hTUnot⟩ :=
    hdesc (pointsMap B S hS _ η ⁻¹' T) (pointsMap B S hS _ ρ ⁻¹' C') hT₀closed hsub
      (pointsMap B S hS _ (yoneda.map α') v) hr'
  refine ⟨Vs, Z', jV, v, yoneda.map α', yoneda.map β ≫ ι,
    pointsMap B S hS _ eZ.hom '' TU, r, qq, hVsaff, hZ'aff, hjVetale, hjVopen, hv, hpv, hpg,
    hblfp,
    isClosedMap_pointsMap_of_isIso B S hS eZ.hom _ hTUclosed, ?_, hr₁, hr₂, sqr, hqqfst,
    hqqsnd, ?_⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, hyv⟩
    refine hTUnot ⟨y, hy, ?_⟩
    rw [← hyv, ← pointsMap_comp_apply, heZdef, pullbackLeftPullbackSndIso_hom_snd]
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨pointsMap B S hS _ a₂ (pointsMap B S hS _ ν x), ?_, ?_⟩
    · refine hTUsub ?_
      change pointsMap B S hS _ η (pointsMap B S hS _ ν x) ∈ T
      rwa [← pointsMap_comp_apply, hνη]
    · simp only [← pointsMap_comp_apply, Category.assoc]
      rw [hνq]

/-- **Stacks 0CM8.** Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over `S`,
let `g : Z ⟶ Y` be a morphism of algebraic spaces, let `z` be a point of `|Z|`, and let `T` be
a closed subset of `|X ×_Y Z|` whose image in `|Z|` misses `z`. Then there are an affine étale
neighbourhood `(V, v)` of `z`, an affine `Z'` and a factorization `V ⟶ Z' ⟶ Y` of `V ⟶ Y`
whose second leg `b` is locally of finite presentation, and a closed subset `T'` of
`|X ×_Y Z'|` whose image in `|Z'|` misses the image of `v` and which receives the inverse image
of `T` along the two comparison morphisms `r` and `q` of the three fibre products. -/
@[stacks 0CM8 "the separation statement, with V and Z' affine; the refinement for Z a \
scheme, where V may be taken to be an affine open neighbourhood of z, is not included"]
theorem exists_affine_etale_isLocallyOfFinitePresentation_separation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsQuasiCompact B S hS f)
    (z : points B S hS Z) (T : Set (points B S hS (pullback f g))) (hT : IsClosed T)
    (hz : z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T) :
    ∃ (V Z' : BigFppfOver B S hS) (p : yoneda.obj V ⟶ Z)
      (v : points B S hS (yoneda.obj V)) (a : yoneda.obj V ⟶ yoneda.obj Z')
      (b : yoneda.obj Z' ⟶ Y) (T' : Set (points B S hS (pullback f b)))
      (r : pullback f (p ≫ g) ⟶ pullback f g) (q : pullback f (p ≫ g) ⟶ pullback f b),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
      IsEtale B S hS p ∧
      pointsMap B S hS (yoneda.obj V) p v = z ∧
      p ≫ g = a ≫ b ∧
      IsLocallyOfFinitePresentation B S hS b ∧
      IsClosed T' ∧
      pointsMap B S hS (yoneda.obj V) a v ∉
        pointsMap B S hS (pullback f b) (pullback.snd f b) '' T' ∧
      r ≫ pullback.fst f g = pullback.fst f (p ≫ g) ∧
      r ≫ pullback.snd f g = pullback.snd f (p ≫ g) ≫ p ∧
      IsPullback r (pullback.snd f (p ≫ g)) (pullback.snd f g) p ∧
      q ≫ pullback.fst f b = pullback.fst f (p ≫ g) ∧
      q ≫ pullback.snd f b = pullback.snd f (p ≫ g) ≫ a ∧
      pointsMap B S hS (pullback f (p ≫ g)) q ''
        (pointsMap B S hS (pullback f (p ≫ g)) r ⁻¹' T) ⊆ T' := by
  classical
  obtain ⟨U, ι, u, hUaff, hιet, hιu⟩ :=
    exists_affine_etale_chart_of_point B S hS Y hY (pointsMap B S hS Z g z)
  have hyU := isAlgebraicSpace_yoneda B S hS U
  have hbcEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hmulEt := isMultiplicative_presheaf_etale B S hS
  obtain ⟨ζ, hζ₁, hζ₂⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback g ι) z u hιu.symm
  have hZU : IsAlgebraicSpace B S hS (pullback g ι) :=
    isAlgebraicSpace_pullback B S hS g ι hZ hyU hY
  obtain ⟨V₀, κ, v₀, hV₀aff, hκet, hκv⟩ := exists_affine_etale_chart_of_point B S hS _ hZU ζ
  set p₀ : yoneda.obj V₀ ⟶ Z := κ ≫ pullback.fst g ι with hp₀def
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : V₀ ⟶ U, yoneda.map α₀ = κ ≫ pullback.snd g ι :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hfac₀ : p₀ ≫ g = yoneda.map α₀ ≫ ι := by
    rw [hα₀, hp₀def, Category.assoc, Category.assoc, pullback.condition]
  have hp₀v : pointsMap B S hS _ p₀ v₀ = z := by
    rw [hp₀def, pointsMap_comp, Function.comp_apply, hκv, hζ₁]
  have hfstEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst g ι) :=
    hbcEt.of_isPullback (IsPullback.of_hasPullback g ι).flip hιet
  have hp₀et : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p₀ :=
    MorphismProperty.comp_mem _ κ (pullback.fst g ι) hκet hfstEt
  obtain ⟨V, Z', jV, v, a, b, T', r, q, hVaff, hZ'aff, hjVetale, -, -, hpv, hpg, hblfp,
    hT'closed, hT'not, hr₁, hr₂, sqr, hqqfst, hqqsnd, hsub⟩ :=
    exists_separation_of_affine_lfp_chart B S hS hX hY f g hf z T hT hz ι hUaff
      (isLocallyOfFinitePresentation_of_isEtale B S hS
        (isEtale_of_presheaf_etale B S hS hιet))
      hV₀aff p₀ α₀ hfac₀ v₀ hp₀v
  have hpet : IsEtale B S hS (yoneda.map jV ≫ p₀) :=
    isEtale_of_presheaf_etale B S hS (MorphismProperty.comp_mem _ (yoneda.map jV) p₀
      ((presheaf_yoneda_map_etale_iff B S hS jV).2 hjVetale) hp₀et)
  exact ⟨V, Z', yoneda.map jV ≫ p₀, v, a, b, T', r, q, hVaff, hZ'aff, hpet, hpv, hpg, hblfp,
    hT'closed, hT'not, hr₁, hr₂, sqr, hqqfst, hqqsnd, hsub⟩

/-! ### The refinement of the source for `Z` a scheme

The source adds that when `Z` is a scheme the étale neighbourhood `V` may be taken to be an
affine *open* neighbourhood of `z`. The statements below carry that refinement.

The first is the refinement for `Z` a scheme and `Y` a *general* algebraic space, with the one
input the argument needs isolated as a hypothesis: an affine open neighbourhood of `z` in `Z`
together with a factorization of its morphism to `Y` through an affine scheme which is locally
of finite presentation over `Y`. That hypothesis is sharp, and not an artifact:
`exists_affine_isLocallyOfFinitePresentation_factorization_of_separation` derives it back from
the refinement's own conclusion, so for a fixed `Z ⟶ Y` and `z` the refinement and the
factorization are equivalent. The three statements after it discharge that input. The first
discharges it for `Y` an arbitrary algebraic space and `g : Z ⟶ Y` locally of finite
presentation: an affine open neighbourhood of `z` is then itself an affine scheme locally of
finite presentation over `Y`, and the factorization is the identity. The second is the same
refinement with the factorization packaged the way the source produces it when `Y` is a scheme
— through an affine `U` étale over `Y` — and the third discharges the input outright when `Y`
is a scheme, from the affine opens of `Y`.

The equivalence also says what kind of argument cannot prove the refinement for a general `Y`
and a general `g`. The factorization is forced already by `T = ∅`, where clauses (2) and (3)
are vacuous, so descending those two clauses cannot be what is missing: the étale-descent step
`AlgebraicGeometry.Space.exists_isClosed_separation_of_etale_cover` descends them along a
cover of `X`, whereas the content of the refinement is the Zariski topology of `Z` near `z`,
which an étale cover of `Z` does not see.

Nor is the gap an artifact of asking `Z'` to be affine, as the source does. Were `Z'` allowed
to be an arbitrary object of the site, shrinking the affine open neighbourhood `V` into the
preimage of an affine open of `Z'` around the image of `z` would return the factorization
through an affine scheme, an affine open of `Z'` being locally of finite presentation over `Y`
as soon as `Z'` is. Only allowing `Z'` to be a non-representable algebraic space would avoid
the factorization, and then the scheme case of Tag 05BD the argument runs on, over the affine
`U`, is no longer available.

For `Y` a general algebraic space the input is *not* available from the source's proof. That
proof chooses an affine étale neighbourhood `(V, v) → (Z, z)` whose morphism to `Y` factors
through an affine étale chart `U` of `Y`, and such a `V` is an affine open of `Z ×_Y U`, not of
`Z`. A Zariski neighbourhood of `z` factoring through `U` amounts to a *section* of the étale
morphism `Z ×_Y U → Z` near `z`, and that is strictly more than a point above `z` with the same
residue field as `z`. Such a point is always available, with no decency hypothesis: every
field-valued point of an arbitrary algebraic space lifts along some affine étale chart, by
`AlgebraicGeometry.Space.exists_affine_etale_chart_of_fieldValuedPoint`. So decency, and Tag
0BBP, are not what is missing. What a section near `z` asks is that the *local ring* be
unchanged, which for an étale morphism is the Henselian property of `𝒪_{Z, z}` and not a
property of residue fields: `ℤ_(5) ⟶ (ℤ[t]/(t² - t + 5))_{(5, t)}` is flat, unramified and
essentially of finite presentation and has `𝔽₅` on both sides, and is not an isomorphism. Once
the local rings do agree the section exists, by
`AlgebraicGeometry.exists_isOpenImmersion_of_etale_of_isIso_stalkMap`. Weakening `U ⟶ Y` from
étale to locally of finite presentation — which is all the argument uses — is the room needed
to state the sharp hypothesis.

A *finite* étale cover does not supply it either, so the symmetric-power construction that
makes the elementary refinement of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ElementaryEtaleSeparation.lean` work for an
arbitrary `Y` does not apply here. That construction turns a degree-`n` finite étale subcover
of `V ×_Y U ⟶ V` into a morphism from `V` to a symmetric power of the chart `U`, which is
again étale over `Y`; but an étale covering of an affine scheme need not be refinable by
Zariski coverings together with finite étale coverings. Take `V = Spec ℤ_(5)`, which is local,
and `P ⊂ Spec(ℤ_(5)[t]/(t² - t + 5))` the complement of the point with `t ≡ 1 mod 5`. The
ambient scheme is finite étale of degree two over `V`, since the discriminant `-19` is a unit,
and it is connected, being the spectrum of a domain; `P ⟶ V` is étale and surjective; and a
finite étale `Q ⟶ V` with a morphism to `P` over `V` would be proper and étale over that
connected scheme, hence onto a nonempty open and closed part of it, hence onto all of it,
which `P` is not.

What does supply the input for a general `Y` is approximation relative to `Y`, not a section,
and these are the declarations it runs through. Take an affine open `V ∋ z` and an affine étale
chart `W ⟶ Y` through the image of `z`, by
`AlgebraicGeometry.Space.exists_affine_etale_chart_of_point`, and an affine `P` étale and
surjective over `V` carrying a morphism to `W` over `Y`, cut out of `V ×_Y W`. Then `P ⟶ W` is
a limit of affine schemes locally of finite presentation over `W`, by
`Stacks.AlgebraicGeometry.Tag05JXGeneral.exists_directedOrder_affine_limit_presentation`; the
étale equivalence relation `P ×_V P` is of finite presentation over `P` and so is defined over
a stage, and its morphism to `W ×_Y W` descends to a stage by
`AlgebraicGeometry.Space.exists_stage_map_of_relativelyLimitPreserving`, whose hypothesis is met
because `W ×_Y W ⟶ W` is étale and therefore locally of finite presentation. The quotient of
such a stage by that relation is an algebraic space, by
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase_unconditional` (Tag 0265),
it is locally of finite presentation over `Y` because its chart is, and `V` is the limit of
those quotients — an `AlgebraicGeometry.Space.LimitSituation` (Tag 084R). Tag 07SQ makes one
quotient a *scheme* which is affine, and
`exists_affine_isLocallyOfFinitePresentation_factorization_of_limitPresentation` below turns an
affine stage of such a system into exactly the factorization the statements of this section
consume. Chevalley's theorem is no shortcut past Tag 07SQ here: the quotient map
of a stage is étale and not finite.

Tag 07SQ is the one step of that route this development does not have. What it proves is a
*separated* stage,
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isAffineSpace`
(Tag 084T); the strengthening to an affine stage consumes Tag 07SI, the identification
`Γ(X, 𝒪_X) = colim_i Γ(X_i, 𝒪_{X_i})` carried by
`AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit`, which is stated and nowhere proved,
and the assertion that some stage is affine occurs in this library only as a hypothesis. For
the system the approximation above produces that identification is however the affine case of
Tag 07SI: there `V` and `P` are affine, so `P ×_V P` is affine and every stage has an affine
chart and an affine relation, the sections of each stage are the equalizer of two rings, and
filtered colimits commute with equalizers. What is then still owed of Tag 07SQ for that system
is that the square of Tag 084U is cartesian —
`AlgebraicGeometry.Space.commSq_chart_specOfGlobalFunctions` proves only that it commutes — and
the descent of the resulting isomorphism to a stage,
`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isIso_mapAt` (bounded Tag 084S) with
`AlgebraicGeometry.Space.isLocalAtTarget_isAffineHom_fpqc` (Tag 041Z).
-/

/-- **Stacks 0CM8, the refinement for `Z` a scheme and `Y` a general algebraic space**, given a
Zariski-local factorization of `Z ⟶ Y` at `z` through an affine scheme locally of finite
presentation over `Y`. Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over
`S` with `Z` represented by an object `Z₀` of the site, let `z` be a point of `|Z₀|`, and let
`T` be a closed subset of `|X ×_Y Z₀|` whose image in `|Z₀|` misses `z`. Suppose given an
affine `U` with an `ι : U ⟶ Y` locally of finite presentation, an affine `V₀` with an open
immersion `pV₀ : V₀ ⟶ Z₀` whose image contains `z` — witnessed by a point `v₀` of `|V₀|` above
`z` — and a factorization `pV₀ ≫ g = α₀ ≫ ι` of `V₀ ⟶ Y` through `U`. Then the conclusion of
Tag 0CM8 holds with the étale neighbourhood `p` an *open immersion* out of an affine `V`
sending `v` to `z`: that is, `V` is an affine open neighbourhood of `z`, and clauses (1), (2)
and (3) — `b` locally of finite presentation, the image of `T'` in `|Z'|` missing the image of
`v`, and `T'` receiving the inverse image of `T` — all hold, as does étaleness of `p`.

The hypothesis is the weakest one that can appear here, by
`AlgebraicGeometry.Space.exists_affine_isLocallyOfFinitePresentation_factorization_of_separation`:
the conclusion returns an affine `Z'` with `b : Z' ⟶ Y` locally of finite presentation and a
factorization of the affine open neighbourhood `V` through it. -/
theorem exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z₀ : BigFppfOver B S hS}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (g : yoneda.obj Z₀ ⟶ Y)
    (hf : IsQuasiCompact B S hS f)
    (z : points B S hS (yoneda.obj Z₀))
    (T : Set (points B S hS (pullback f g))) (hT : IsClosed T)
    (hz : z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T)
    {U V₀ : BigFppfOver B S hS} (ι : yoneda.obj U ⟶ Y)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hιlfp : IsLocallyOfFinitePresentation B S hS ι)
    (hV₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (pV₀ : V₀ ⟶ Z₀)
    (hpV₀open : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV₀))
    (v₀ : points B S hS (yoneda.obj V₀))
    (hv₀ : pointsMap B S hS (yoneda.obj V₀) (yoneda.map pV₀) v₀ = z)
    (α₀ : V₀ ⟶ U) (hfac : yoneda.map pV₀ ≫ g = yoneda.map α₀ ≫ ι) :
    ∃ (V Z' : BigFppfOver B S hS) (p : yoneda.obj V ⟶ yoneda.obj Z₀) (pV : V ⟶ Z₀)
      (v : points B S hS (yoneda.obj V)) (a : yoneda.obj V ⟶ yoneda.obj Z')
      (b : yoneda.obj Z' ⟶ Y) (T' : Set (points B S hS (pullback f b)))
      (r : pullback f (p ≫ g) ⟶ pullback f g) (q : pullback f (p ≫ g) ⟶ pullback f b),
      p = yoneda.map pV ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
      (BigFppfOver.toScheme B S hS).map pV (pointsToScheme B S hS V v) =
        pointsToScheme B S hS Z₀ z ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
      IsEtale B S hS p ∧
      pointsMap B S hS (yoneda.obj V) p v = z ∧
      p ≫ g = a ≫ b ∧
      IsLocallyOfFinitePresentation B S hS b ∧
      IsClosed T' ∧
      pointsMap B S hS (yoneda.obj V) a v ∉
        pointsMap B S hS (pullback f b) (pullback.snd f b) '' T' ∧
      r ≫ pullback.fst f g = pullback.fst f (p ≫ g) ∧
      r ≫ pullback.snd f g = pullback.snd f (p ≫ g) ≫ p ∧
      IsPullback r (pullback.snd f (p ≫ g)) (pullback.snd f g) p ∧
      q ≫ pullback.fst f b = pullback.fst f (p ≫ g) ∧
      q ≫ pullback.snd f b = pullback.snd f (p ≫ g) ≫ a ∧
      pointsMap B S hS (pullback f (p ≫ g)) q ''
        (pointsMap B S hS (pullback f (p ≫ g)) r ⁻¹' T) ⊆ T' := by
  classical
  have hmulEt := isMultiplicative_presheaf_etale B S hS
  have hpV₀et : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map pV₀) :=
    (presheaf_yoneda_map_etale_iff B S hS pV₀).2 inferInstance
  obtain ⟨V, Z', jV, v, a, b, T', r, q, hVaff, hZ'aff, hjVetale, hjVopen, -, hpv, hpg, hblfp,
    hT'closed, hT'not, hr₁, hr₂, sqr, hqqfst, hqqsnd, hsub⟩ :=
    exists_separation_of_affine_lfp_chart B S hS hX hY f g hf z T hT hz ι hUaff hιlfp
      hV₀aff (yoneda.map pV₀) α₀ hfac v₀ hv₀
  refine ⟨V, Z', yoneda.map jV ≫ yoneda.map pV₀, jV ≫ pV₀, v, a, b, T', r, q,
    (CategoryTheory.Functor.map_comp yoneda jV pV₀).symm, ?_, ?_, hVaff, hZ'aff, ?_, hpv, hpg,
    hblfp, hT'closed, hT'not, hr₁, hr₂, sqr, hqqfst, hqqsnd, hsub⟩
  · rw [CategoryTheory.Functor.map_comp]
    infer_instance
  · have h1 := pointsToScheme_pointsMap_yoneda B S hS (jV ≫ pV₀) v
    rw [CategoryTheory.Functor.map_comp] at h1
    rw [← h1, hpv]
  · exact isEtale_of_presheaf_etale B S hS (MorphismProperty.comp_mem _ (yoneda.map jV)
      (yoneda.map pV₀) ((presheaf_yoneda_map_etale_iff B S hS jV).2 hjVetale) hpV₀et)

/-- **Stacks 0CM8, the refinement for `Z` a scheme and `Y` an arbitrary algebraic space**, for a
morphism `g : Z ⟶ Y` which is locally of finite presentation. Let `f : X ⟶ Y` be a
quasi-compact morphism of algebraic spaces over `S` with `Z` represented by an object `Z₀` of
the site, let `g : yoneda.obj Z₀ ⟶ Y` be locally of finite presentation, let `z` be a point of
`|Z₀|`, and let `T` be a closed subset of `|X ×_Y Z₀|` whose image in `|Z₀|` misses `z`. Then
the conclusion of Tag 0CM8 holds with the étale neighbourhood `p` an *open immersion* out of an
affine `V` sending `v` to `z`: that is, `V` is an affine open neighbourhood of `z`, `Z'` is
affine, and clauses (1), (2) and (3) — `b` locally of finite presentation, the image of `T'` in
`|Z'|` missing the image of `v`, and `T'` receiving the inverse image of `T` — all hold, as
does étaleness of `p`.

Nothing is assumed of `Y` beyond being an algebraic space over `S`. -/
@[stacks 0CM8 "the refinement for Z a scheme with Y an arbitrary algebraic space over S, for \
g : Z -> Y locally of finite presentation: the etale neighbourhood p : V -> Z is an open \
immersion onto an affine open neighbourhood of z, Z' is affine, and clauses (1), (2) and (3) \
hold -- b locally of finite presentation, the image of T' in |Z'| missing a(v), and T' \
receiving the inverse image of T. An affine open neighbourhood of z is then itself an affine \
scheme locally of finite presentation over Y, which is the factorization the refinement \
amounts to"]
theorem exists_affineOpen_isLocallyOfFinitePresentation_separation_of_lfp_morphism
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z₀ : BigFppfOver B S hS}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (g : yoneda.obj Z₀ ⟶ Y)
    (hf : IsQuasiCompact B S hS f) (hg : IsLocallyOfFinitePresentation B S hS g)
    (z : points B S hS (yoneda.obj Z₀))
    (T : Set (points B S hS (pullback f g))) (hT : IsClosed T)
    (hz : z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T) :
    ∃ (V Z' : BigFppfOver B S hS) (p : yoneda.obj V ⟶ yoneda.obj Z₀) (pV : V ⟶ Z₀)
      (v : points B S hS (yoneda.obj V)) (a : yoneda.obj V ⟶ yoneda.obj Z')
      (b : yoneda.obj Z' ⟶ Y) (T' : Set (points B S hS (pullback f b)))
      (r : pullback f (p ≫ g) ⟶ pullback f g) (q : pullback f (p ≫ g) ⟶ pullback f b),
      p = yoneda.map pV ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
      (BigFppfOver.toScheme B S hS).map pV (pointsToScheme B S hS V v) =
        pointsToScheme B S hS Z₀ z ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
      IsEtale B S hS p ∧
      pointsMap B S hS (yoneda.obj V) p v = z ∧
      p ≫ g = a ≫ b ∧
      IsLocallyOfFinitePresentation B S hS b ∧
      IsClosed T' ∧
      pointsMap B S hS (yoneda.obj V) a v ∉
        pointsMap B S hS (pullback f b) (pullback.snd f b) '' T' ∧
      r ≫ pullback.fst f g = pullback.fst f (p ≫ g) ∧
      r ≫ pullback.snd f g = pullback.snd f (p ≫ g) ≫ p ∧
      IsPullback r (pullback.snd f (p ≫ g)) (pullback.snd f g) p ∧
      q ≫ pullback.fst f b = pullback.fst f (p ≫ g) ∧
      q ≫ pullback.snd f b = pullback.snd f (p ≫ g) ≫ a ∧
      pointsMap B S hS (pullback f (p ≫ g)) q ''
        (pointsMap B S hS (pullback f (p ≫ g)) r ⁻¹' T) ⊆ T' := by
  classical
  obtain ⟨VO, hVO, hzVO, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := pointsToScheme B S hS Z₀ z) trivial
  obtain ⟨v₀, hv₀, hjZopen⟩ := exists_point_openSiteObject B S hS VO z hzVO
  set jZ : openSiteObject B S hS Z₀ VO ⟶ Z₀ := openSiteObjectHom B S hS Z₀ VO with hjZdef
  have hVaff : IsAffine
      ((BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS Z₀ VO)) := hVO
  have hjZet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map jZ) :=
    (presheaf_yoneda_map_etale_iff B S hS jZ).2 inferInstance
  have hιlfp : IsLocallyOfFinitePresentation B S hS (yoneda.map jZ ≫ g) :=
    isLocallyOfFinitePresentation_comp B S hS
      (isAlgebraicSpace_yoneda B S hS (openSiteObject B S hS Z₀ VO))
      (isAlgebraicSpace_yoneda B S hS Z₀) hY (yoneda.map jZ) g
      (isLocallyOfFinitePresentation_of_isEtale B S hS
        (isEtale_of_presheaf_etale B S hS hjZet)) hg
  exact exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization B S hS hX hY
    f g hf z T hT hz (yoneda.map jZ ≫ g) hVaff hιlfp hVaff jZ hjZopen v₀ hv₀ (𝟙 _)
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp])

/-- **Stacks 0CM8, the refinement for `Z` a scheme**, given a Zariski-local factorization of
`Z ⟶ Y` through an affine étale chart at `z`. Let `f : X ⟶ Y` be a quasi-compact morphism of
algebraic spaces over `S` with `Y` and `Z` represented by objects `Y₀` and `Z₀` of the site,
let `z` be a point of `|Z₀|`, and let `T` be a closed subset of `|X ×_Y Z₀|` whose image in
`|Z₀|` misses `z`. Suppose given an affine `U` with an étale `ι : U ⟶ Y`, an affine open `VO`
of `Z₀` containing `z`, and a factorization of `VO ⟶ Y` through `U`. Then the conclusion of
Tag 0CM8 holds with the étale neighbourhood `p` an *open immersion* out of an affine `V`
sending `v` to `z`: that is, `V` is an affine open neighbourhood of `z`, and clauses (1), (2)
and (3) — `b` locally of finite presentation, the image of `T'` in `|Z'|` missing the image of
`v`, and `T'` receiving the inverse image of `T` — all still hold, as does étaleness of `p`.

This is the case of `exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization`
where `V₀` is the affine open `VO` and `ι` is étale. -/
theorem exists_affineOpen_isLocallyOfFinitePresentation_separation_of_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ Z₀ : BigFppfOver B S hS}
    (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ yoneda.obj Y₀) (g : yoneda.obj Z₀ ⟶ yoneda.obj Y₀)
    (hf : IsQuasiCompact B S hS f)
    (z : points B S hS (yoneda.obj Z₀))
    (T : Set (points B S hS (pullback f g))) (hT : IsClosed T)
    (hz : z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T)
    {U : BigFppfOver B S hS} (ι : yoneda.obj U ⟶ yoneda.obj Y₀)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hιet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ι)
    (VO : ((BigFppfOver.toScheme B S hS).obj Z₀).Opens)
    (hVOaff : IsAffine VO.toScheme) (hzVO : pointsToScheme B S hS Z₀ z ∈ VO)
    (α₀ : openSiteObject B S hS Z₀ VO ⟶ U)
    (hfac : yoneda.map (openSiteObjectHom B S hS Z₀ VO) ≫ g = yoneda.map α₀ ≫ ι) :
    ∃ (V Z' : BigFppfOver B S hS) (p : yoneda.obj V ⟶ yoneda.obj Z₀) (pV : V ⟶ Z₀)
      (v : points B S hS (yoneda.obj V)) (a : yoneda.obj V ⟶ yoneda.obj Z')
      (b : yoneda.obj Z' ⟶ yoneda.obj Y₀) (T' : Set (points B S hS (pullback f b)))
      (r : pullback f (p ≫ g) ⟶ pullback f g) (q : pullback f (p ≫ g) ⟶ pullback f b),
      p = yoneda.map pV ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
      (BigFppfOver.toScheme B S hS).map pV (pointsToScheme B S hS V v) =
        pointsToScheme B S hS Z₀ z ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
      IsEtale B S hS p ∧
      pointsMap B S hS (yoneda.obj V) p v = z ∧
      p ≫ g = a ≫ b ∧
      IsLocallyOfFinitePresentation B S hS b ∧
      IsClosed T' ∧
      pointsMap B S hS (yoneda.obj V) a v ∉
        pointsMap B S hS (pullback f b) (pullback.snd f b) '' T' ∧
      r ≫ pullback.fst f g = pullback.fst f (p ≫ g) ∧
      r ≫ pullback.snd f g = pullback.snd f (p ≫ g) ≫ p ∧
      IsPullback r (pullback.snd f (p ≫ g)) (pullback.snd f g) p ∧
      q ≫ pullback.fst f b = pullback.fst f (p ≫ g) ∧
      q ≫ pullback.snd f b = pullback.snd f (p ≫ g) ≫ a ∧
      pointsMap B S hS (pullback f (p ≫ g)) q ''
        (pointsMap B S hS (pullback f (p ≫ g)) r ⁻¹' T) ⊆ T' := by
  classical
  obtain ⟨v₀, hv₀, hjZopen⟩ := exists_point_openSiteObject B S hS VO z hzVO
  have hV₀aff : IsAffine
      ((BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS Z₀ VO)) := hVOaff
  exact exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization B S hS hX
    (isAlgebraicSpace_yoneda B S hS Y₀) f g hf z T hT hz ι hUaff
    (isLocallyOfFinitePresentation_of_isEtale B S hS
      (isEtale_of_presheaf_etale B S hS hιet))
    hV₀aff (openSiteObjectHom B S hS Z₀ VO) hjZopen v₀ hv₀ α₀ hfac

/-- **Stacks 0CM8, the refinement for `Z` a scheme**, with no hypothesis on `g`, in the
situation the source's own proof reduces to, where `Y` is represented by an object of the site
as well. Let `f : X ⟶ Y` be a quasi-compact morphism with `X` an algebraic space over `S` and
`Y` and `Z` represented by objects `Y₀` and `Z₀` of the site, let `z` be a point of `|Z₀|`, and
let `T` be a closed subset of `|X ×_Y Z₀|` whose image in `|Z₀|` misses `z`. Then the
conclusion of Tag 0CM8 holds with `V` an affine *open* neighbourhood of `z`: the morphism
`p : V ⟶ Z₀` is an open immersion sending `v` to `z`, `V` and `Z'` are affine, and clauses
(1), (2) and (3) of the source hold unchanged.

For `Y` an arbitrary algebraic space the refinement holds whenever `g` is locally of finite
presentation, by
`exists_affineOpen_isLocallyOfFinitePresentation_separation_of_lfp_morphism`, and in general
from a Zariski-local factorization, by
`exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization`,
which asks for the input in its sharpest form — an affine open neighbourhood of `z` whose
morphism to `Y` factors through an affine scheme *locally of finite presentation* over `Y`.
That input cannot be dispensed with: it is part of the refinement's own conclusion, by
`AlgebraicGeometry.Space.exists_affine_isLocallyOfFinitePresentation_factorization_of_separation`.
What `Y` being a scheme supplies is a Zariski-local factorization: for a general algebraic
space the affine opens of `Y` are replaced by affine étale charts, and pulling a chart back
along `Z₀ ⟶ Y` gives an étale morphism to `Z₀`, of which one needs a *section* near `z`. A
point above `z` with the same residue field as `z` is not enough for that and is in any case
always available, by
`AlgebraicGeometry.Space.exists_affine_etale_chart_of_fieldValuedPoint`, for an arbitrary
algebraic space and with no decency hypothesis; an étale morphism with trivial residue
extension at a point has a section near it exactly when the map of local rings there is an
isomorphism, by `AlgebraicGeometry.exists_isOpenImmersion_of_etale_of_isIso_stalkMap`, and that
is the Henselian property of `𝒪_{Z₀, z}` rather than anything about `Y`. What does supply the
factorization for an arbitrary `Y` and an arbitrary `g`, and which step of it this development
is missing, is recorded in the note opening this section. -/
@[stacks 0CM8 "the refinement for Z a scheme with no hypothesis on g, for Y represented by an \
object of the site as well -- the situation the source's own proof reduces to before it \
produces the affine open neighbourhood: the etale neighbourhood p : V -> Z is an open \
immersion onto an affine open neighbourhood of z, Z' is affine, and clauses (1), (2) and (3) \
hold -- b locally of finite presentation, the image of T' in |Z'| missing a(v), and T' \
receiving the inverse image of T. The affine opens of Y supply \
the factorization of an affine open neighbourhood of z through an affine scheme locally of \
finite presentation over Y that the refinement amounts to"]
theorem exists_affineOpen_isLocallyOfFinitePresentation_separation
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ Z₀ : BigFppfOver B S hS}
    (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ yoneda.obj Y₀) (g : yoneda.obj Z₀ ⟶ yoneda.obj Y₀)
    (hf : IsQuasiCompact B S hS f)
    (z : points B S hS (yoneda.obj Z₀))
    (T : Set (points B S hS (pullback f g))) (hT : IsClosed T)
    (hz : z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T) :
    ∃ (V Z' : BigFppfOver B S hS) (p : yoneda.obj V ⟶ yoneda.obj Z₀) (pV : V ⟶ Z₀)
      (v : points B S hS (yoneda.obj V)) (a : yoneda.obj V ⟶ yoneda.obj Z')
      (b : yoneda.obj Z' ⟶ yoneda.obj Y₀) (T' : Set (points B S hS (pullback f b)))
      (r : pullback f (p ≫ g) ⟶ pullback f g) (q : pullback f (p ≫ g) ⟶ pullback f b),
      p = yoneda.map pV ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
      (BigFppfOver.toScheme B S hS).map pV (pointsToScheme B S hS V v) =
        pointsToScheme B S hS Z₀ z ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
      IsEtale B S hS p ∧
      pointsMap B S hS (yoneda.obj V) p v = z ∧
      p ≫ g = a ≫ b ∧
      IsLocallyOfFinitePresentation B S hS b ∧
      IsClosed T' ∧
      pointsMap B S hS (yoneda.obj V) a v ∉
        pointsMap B S hS (pullback f b) (pullback.snd f b) '' T' ∧
      r ≫ pullback.fst f g = pullback.fst f (p ≫ g) ∧
      r ≫ pullback.snd f g = pullback.snd f (p ≫ g) ≫ p ∧
      IsPullback r (pullback.snd f (p ≫ g)) (pullback.snd f g) p ∧
      q ≫ pullback.fst f b = pullback.fst f (p ≫ g) ∧
      q ≫ pullback.snd f b = pullback.snd f (p ≫ g) ≫ a ∧
      pointsMap B S hS (pullback f (p ≫ g)) q ''
        (pointsMap B S hS (pullback f (p ≫ g)) r ⁻¹' T) ⊆ T' := by
  classical
  obtain ⟨g', hg'⟩ : ∃ g' : Z₀ ⟶ Y₀, yoneda.map g' = g :=
    ⟨yoneda.preimage g, yoneda.map_preimage _⟩
  obtain ⟨UO, hUOaff, hyUO, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := (BigFppfOver.toScheme B S hS).map g' (pointsToScheme B S hS Z₀ z)) trivial
  obtain ⟨VO, hVO, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset
    (U := (BigFppfOver.toScheme B S hS).map g' ⁻¹ᵁ UO) (x := pointsToScheme B S hS Z₀ z) hyUO
  set uH : openSiteObject B S hS Y₀ UO ⟶ Y₀ := openSiteObjectHom B S hS Y₀ UO with huHdef
  have huH : (BigFppfOver.toScheme B S hS).map uH = UO.ι :=
    map_openSiteObjectHom B S hS Y₀ UO
  set jZ : openSiteObject B S hS Z₀ VO ⟶ Z₀ := openSiteObjectHom B S hS Z₀ VO with hjZdef
  have hjZ : (BigFppfOver.toScheme B S hS).map jZ = VO.ι :=
    map_openSiteObjectHom B S hS Z₀ VO
  set aL := B.inclusion.preimage
    (show B.inclusion.obj (openSiteObject B S hS Z₀ VO).left ⟶
      B.inclusion.obj (openSiteObject B S hS Y₀ UO).left from
      ((BigFppfOver.toScheme B S hS).map g').resLE UO VO hle) with haLdef
  have haL : B.inclusion.map aL =
      ((BigFppfOver.toScheme B S hS).map g').resLE UO VO hle :=
    B.inclusion.map_preimage _
  have hkey : aL ≫ uH.left = jZ.left ≫ g'.left := by
    refine B.inclusion.map_injective ?_
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, haL]
    change ((BigFppfOver.toScheme B S hS).map g').resLE UO VO hle ≫
        (BigFppfOver.toScheme B S hS).map uH =
      (BigFppfOver.toScheme B S hS).map jZ ≫ (BigFppfOver.toScheme B S hS).map g'
    rw [huH, hjZ]
    exact Scheme.Hom.resLE_comp_ι _ _
  set α₀ : openSiteObject B S hS Z₀ VO ⟶ openSiteObject B S hS Y₀ UO :=
    Over.homMk aL (by
      rw [← Over.w uH, ← Category.assoc, hkey, Category.assoc, Over.w g', Over.w jZ])
    with hα₀def
  have hfac : yoneda.map jZ ≫ g = yoneda.map α₀ ≫ yoneda.map uH := by
    rw [← hg', ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg yoneda.map (Over.OverMorphism.ext hkey.symm)
  exact exists_affineOpen_isLocallyOfFinitePresentation_separation_of_chart B S hS hX f g hf z
    T hT hz (yoneda.map uH)
    (show IsAffine ((BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS Y₀ UO)) from
      hUOaff)
    ((presheaf_yoneda_map_etale_iff B S hS uH).2
      (by rw [huH]; exact (inferInstance : AlgebraicGeometry.Etale UO.ι)))
    VO hVO hzV α₀ hfac

/-- The factorization hypothesis of
`exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization`
is necessary, hence equivalent to the refinement of Tag 0CM8 it proves. Let `g : Z₀ ⟶ Y` be a
morphism from a representable presheaf to an algebraic space over `S`, and let `z` be a point
of `|Z₀|`. Suppose that the refinement holds for every quasi-compact `f : X ⟶ Y` and every
closed `T ⊆ |X ×_Y Z₀|` whose image in `|Z₀|` misses `z`, in the weak form keeping only the
data a factorization consists of. Then there are an affine `U`, an `ι : U ⟶ Y` locally of
finite presentation, an affine `V` with an open immersion `pV : V ⟶ Z₀` sending a point `v` to
`z` and a morphism `α₀ : V ⟶ U` with `pV ≫ g = α₀ ≫ ι`.

The hypothesis is needed only for `f` the identity of `Y` and `T` empty, where clauses (2) and
(3) of the source are vacuous. -/
theorem exists_affine_isLocallyOfFinitePresentation_factorization_of_separation
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z₀ : BigFppfOver B S hS}
    (hY : IsAlgebraicSpace B S hS Y) (g : yoneda.obj Z₀ ⟶ Y)
    (z : points B S hS (yoneda.obj Z₀))
    (hrefine : ∀ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS X →
      ∀ f : X ⟶ Y, IsQuasiCompact B S hS f →
      ∀ T : Set (points B S hS (pullback f g)), IsClosed T →
      z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T →
      ∃ (V Z' : BigFppfOver B S hS) (pV : V ⟶ Z₀) (v : points B S hS (yoneda.obj V))
        (a : yoneda.obj V ⟶ yoneda.obj Z') (b : yoneda.obj Z' ⟶ Y),
        AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
        pointsMap B S hS (yoneda.obj V) (yoneda.map pV) v = z ∧
        IsLocallyOfFinitePresentation B S hS b ∧
        yoneda.map pV ≫ g = a ≫ b) :
    ∃ (U V : BigFppfOver B S hS) (ι : yoneda.obj U ⟶ Y) (pV : V ⟶ Z₀)
      (v : points B S hS (yoneda.obj V)) (α₀ : V ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsLocallyOfFinitePresentation B S hS ι ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
      pointsMap B S hS (yoneda.obj V) (yoneda.map pV) v = z ∧
      yoneda.map pV ≫ g = yoneda.map α₀ ≫ ι := by
  obtain ⟨V, Z', pV, v, a, b, hpVopen, hVaff, hZ'aff, hv, hblfp, hfac⟩ :=
    hrefine Y hY (𝟙 Y)
      (fun W _ hWqc k => IsQuasiCompactSpace.of_iso B S hS hWqc
        (IsPullback.of_id_fst (f := k)).isoPullback)
      ∅ isClosed_empty (by simp)
  exact ⟨Z', V, b, pV, v, yoneda.preimage a, hZ'aff, hblfp, hVaff, hpVopen, hv,
    by rwa [yoneda.map_preimage]⟩

/-- The factorization hypothesis of
`exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization`, from a
presentation of an affine open neighbourhood of `z` as a limit over `Y` of algebraic spaces
locally of finite presentation over `Y`, one stage of which is represented by an affine object of
the site: that stage is the affine scheme the factorization goes through. -/
theorem exists_affine_isLocallyOfFinitePresentation_factorization_of_limitPresentation
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z₀ V₀ : BigFppfOver B S hS}
    (hY : IsAlgebraicSpace B S hS Y) (g : yoneda.obj Z₀ ⟶ Y) (pV₀ : V₀ ⟶ Z₀)
    {I : Type u} [Preorder I] {Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (cV : Cone Dsys)
    (eV : yoneda.obj V₀ ≅ cV.pt) (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y)
    (hDalg : ∀ i : Iᵒᵖ, IsAlgebraicSpace B S hS (Dsys.obj i))
    (hDlfp : ∀ i : Iᵒᵖ, IsLocallyOfFinitePresentation B S hS (t.app i))
    (hcompat : ∀ i : Iᵒᵖ, eV.hom ≫ cV.π.app i ≫ t.app i = yoneda.map pV₀ ≫ g)
    (hstage : ∃ (i : Iᵒᵖ) (U : BigFppfOver B S hS) (_ : yoneda.obj U ≅ Dsys.obj i),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ (U : BigFppfOver B S hS) (ι : yoneda.obj U ⟶ Y) (α : V₀ ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsLocallyOfFinitePresentation B S hS ι ∧
      yoneda.map pV₀ ≫ g = yoneda.map α ≫ ι := by
  obtain ⟨i, U, e, hUaff⟩ := hstage
  refine ⟨U, e.hom ≫ t.app i, yoneda.preimage (eV.hom ≫ cV.π.app i ≫ e.inv), hUaff, ?_, ?_⟩
  · exact isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS U)
      (hDalg i) hY e.hom (t.app i)
      (isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_of_isIso B S hS e.hom))
      (hDlfp i)
  · rw [yoneda.map_preimage]
    simp [hcompat i]

end FinitePresentationSeparation

end AlgebraicGeometry.Space

end
