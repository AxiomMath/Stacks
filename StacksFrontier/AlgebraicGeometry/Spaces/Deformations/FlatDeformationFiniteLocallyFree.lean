module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatDeformationMorphismClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableIff
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.DeformationChartReduction

/-!
# Finite local freeness is invariant under a flat deformation of algebraic spaces

In a flat deformation diagram of algebraic spaces
(`AlgebraicGeometry.Space.FlatDeformationDiagram`) the morphism `f` is finite locally free exactly
when its ambient deformation `f'` is, and then of the same rank. This is part (21) of Stacks 0CGX,
for finite local freeness in the sense of Stacks 03ZV: affine, with `f_*𝒪_X` a finite locally free
`𝒪_Y`-module (of rank `d`). It is first proved for finite local freeness in the sense of Section
03HA — representable, with every represented base change a finite locally free morphism of schemes
(of rank `d`) — and then carried across Stacks 03ZU,
`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree` and its rank form.

The argument is the source's. If `f` is finite locally free then it is finite, flat and locally
of finite presentation (Stacks 0416), so `f'` is finite and flat by the corresponding parts of
Stacks 0CGX and locally of finite presentation by Stacks 05WT, hence finite locally free by
Stacks 0416 again. Conversely `f` is a base change of `f'` (Stacks 03ZY).

For the rank, let `V' ⟶ Y'` be a morphism from a scheme and `ψ' : U' ⟶ V'` the base change of
`f'`. The inclusion `Y ⊂ Y'` pulls back to a surjective closed immersion `V ⟶ V'` of schemes, and
the base change of `ψ'` along it is a base change of `f` over `V`, of rank `d`; so `ψ'` has rank
`d` by
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback_of_isClosedImmersion_of_surjective`.

## Main results

* `presheaf_isFiniteLocallyFree_iff_of_flatDeformationDiagram`
* `presheaf_isFiniteLocallyFreeOfRank_iff_of_flatDeformationDiagram`
* `isFiniteLocallyFree_iff_and_isFiniteLocallyFreeOfRank_iff_of_flatDeformationDiagram`:
  **Stacks 0CGX**, part (21).

## References

* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZY](https://stacks.math.columbia.edu/tag/03ZY)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Finite local freeness in the sense of Section 03HA — representable, with every represented
base change a finite locally free morphism of schemes — is invariant under a flat deformation of
algebraic spaces. -/
theorem presheaf_isFiniteLocallyFree_iff_of_flatDeformationDiagram
    (D : FlatDeformationDiagram B S hS) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf D.f.hom ↔
      (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf D.f'.hom := by
  refine ⟨fun h ↦ ?_, isFiniteLocallyFree_presheaf_of_isPullback B S hS D.isPullback_f⟩
  obtain ⟨h₁, h₂, -⟩ := (isFiniteLocallyFree_presheaf_iff B S hS D.X.2 D.Y.2 D.f.hom).mp h
  exact (isFiniteLocallyFree_presheaf_iff B S hS D.X'.2 D.Y'.2 D.f'.hom).mpr
    ⟨(isFinite_iff_of_flatDeformationDiagram B S hS D).mp h₁,
      (isFlat_iff_of_flatDeformationDiagram B S hS D).mp h₂, D.isLocallyOfFinitePresentation_f'⟩

/-- The rank half of the transfer: if `f'` is finite locally free in the sense of Section 03HA
and every represented base change of `f` has rank `d`, then every represented base change of
`f'` has rank `d`. -/
private theorem presheaf_isFiniteLocallyFreeOfRank_f'_of_flatDeformationDiagram
    (D : FlatDeformationDiagram B S hS) (d : ℕ)
    (hf' : (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf D.f'.hom)
    (hf : (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
        (BigFppfOver.toScheme B S hS)).presheaf D.f.hom) :
    (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
        (BigFppfOver.toScheme B S hS)).presheaf D.f'.hom := by
  refine ⟨hf'.rep, fun a b g fst snd sq' => ?_⟩
  have := D.iY_mono
  obtain ⟨a₀, j, p, hpY, hthick⟩ :=
    exists_thickening_chart_pullback B S hS D.iY D.iY_thickening a g
  let b₀ := hf.rep.pullback p
  let snd₀ : b₀ ⟶ a₀ := hf.rep.snd p
  let fst₀ : yoneda.obj b₀ ⟶ D.X.1 := hf.rep.fst p
  have h0 : IsPullback fst₀ (yoneda.map snd₀) D.f.hom p := hf.rep.isPullback p
  have hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map snd₀) d := hf.property p fst₀ snd₀ h0
  have hw : (fst₀ ≫ D.iX.hom) ≫ D.f'.hom = (yoneda.map snd₀ ≫ yoneda.map j) ≫ g := by
    rw [Category.assoc, ← D.f_comp_iY, ← Category.assoc, h0.w, Category.assoc, hpY.w,
      Category.assoc]
  let k' : yoneda.obj b₀ ⟶ yoneda.obj b := sq'.lift (fst₀ ≫ D.iX.hom)
    (yoneda.map snd₀ ≫ yoneda.map j) hw
  have hbig : IsPullback (k' ≫ fst) (yoneda.map snd₀) D.f'.hom (yoneda.map j ≫ g) := by
    rw [sq'.lift_fst, ← hpY.w]
    exact h0.paste_horiz D.isPullback_f
  have hleft : IsPullback k' (yoneda.map snd₀) (yoneda.map snd) (yoneda.map j) :=
    hbig.of_right (sq'.lift_snd _ _ _) sq'
  let k : b₀ ⟶ b := yoneda.preimage k'
  have hk : yoneda.map k = k' := yoneda.map_preimage _
  have hsite : IsPullback k snd₀ snd j :=
    IsPullback.of_map_of_faithful yoneda (by rwa [hk])
  have hflf : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map snd) :=
    hf'.property g fst snd sq'
  obtain ⟨hfin, hflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp hflf
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) :=
    hthick.1
  have : Surjective ((BigFppfOver.toScheme B S hS).map j) := ⟨hthick.2⟩
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback_of_isClosedImmersion_of_surjective
    (hsite.map (BigFppfOver.toScheme B S hS)) hrank

/-- Finite local freeness of rank `d` in the sense of Section 03HA — representable, with every
represented base change a finite locally free morphism of schemes of rank `d` — is invariant
under a flat deformation of algebraic spaces. -/
theorem presheaf_isFiniteLocallyFreeOfRank_iff_of_flatDeformationDiagram
    (D : FlatDeformationDiagram B S hS) (d : ℕ) :
    (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
        (BigFppfOver.toScheme B S hS)).presheaf D.f.hom ↔
      (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
        (BigFppfOver.toScheme B S hS)).presheaf D.f'.hom := by
  have hforget : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {h : F ⟶ G},
      (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
        (BigFppfOver.toScheme B S hS)).presheaf h →
      (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf h := fun h =>
    ⟨h.rep, fun _ _ g fst snd sq => by
      have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
          ((BigFppfOver.toScheme B S hS).map snd) d := h.property g fst snd sq
      exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d⟩
  refine ⟨fun hf ↦ presheaf_isFiniteLocallyFreeOfRank_f'_of_flatDeformationDiagram B S hS D d
      ((presheaf_isFiniteLocallyFree_iff_of_flatDeformationDiagram B S hS D).mp (hforget hf)) hf,
    fun hf' ↦ ?_⟩
  have : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback D.isPullback_f hf'

/-- **Stacks 0CGX, part (21).** Being finite locally free, and being finite locally free of a
given rank `d`, in the sense of Stacks 03ZV — affine, with `f_*𝒪_X` a finite locally free
`𝒪_Y`-module (of rank `d`) — are each invariant under a flat deformation of algebraic spaces. -/
@[stacks 0CGX "part (21): finite locally free, and finite locally free of rank d"]
theorem isFiniteLocallyFree_iff_and_isFiniteLocallyFreeOfRank_iff_of_flatDeformationDiagram
    (D : FlatDeformationDiagram B S hS) :
    (IsFiniteLocallyFree B S hS D.f ↔ IsFiniteLocallyFree B S hS D.f') ∧
      ∀ d : ℕ,
        IsFiniteLocallyFreeOfRank B S hS D.f d ↔ IsFiniteLocallyFreeOfRank B S hS D.f' d := by
  refine ⟨?_, fun d => ?_⟩
  · rw [← isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS D.f,
      ← isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS D.f']
    exact presheaf_isFiniteLocallyFree_iff_of_flatDeformationDiagram B S hS D
  · rw [← presheaf_iff_isFiniteLocallyFreeOfRank B S hS D.f d,
      ← presheaf_iff_isFiniteLocallyFreeOfRank B S hS D.f' d]
    exact presheaf_isFiniteLocallyFreeOfRank_iff_of_flatDeformationDiagram B S hS D d

end AlgebraicGeometry.Space

end
