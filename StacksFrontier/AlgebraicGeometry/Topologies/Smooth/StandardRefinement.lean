module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver

/-!
# Standard smooth refinements of smooth coverings

Every smooth covering of an affine scheme admits a finite refinement by affine schemes whose
maps to the target are standard smooth, and the refining schemes may be chosen as affine open
subschemes of members of the original covering. So the standard smooth coverings of an affine
scheme are cofinal among its smooth coverings.

## Main results

* `AlgebraicGeometry.exists_finite_affine_standardSmooth_refinement` — a finite standard smooth
  refinement of a smooth covering of an affine scheme.

## Implementation notes

Smooth coverings are `AlgebraicGeometry.Scheme.Cover` for the precoverage of smooth morphisms.
The refining family is an `AlgebraicGeometry.Scheme.AffineCover`, so its members are affine by
construction; the refinement itself is a morphism of the underlying pre-zero-hypercovers, and
requiring each of its components to be an open immersion says that every refining member is an
open affine subscheme of the selected member of the original covering.

## References

* [Stacks Project, Tag 0222](https://stacks.math.columbia.edu/tag/0222)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A smooth morphism onto an affine scheme is standard smooth on an affine open neighbourhood
of any given point of its source. -/
private lemma local_standardSmooth {X T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ T) [Smooth f] (x : X) :
    ∃ (W : X.Opens) (hW : IsAffineOpen W), x ∈ W ∧
      IsStandardSmooth (hW.fromSpec ≫ f) := by
  have hsm : InfinitesimalLifting.SmoothAt f x := by
    rw [InfinitesimalLifting.smoothAt_iff_exists_affine]
    obtain ⟨V, hV, hfxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := T) (x := f.base x) (U := ⊤) (by simp)
    obtain ⟨U, hU, hxU, hUV⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hfxV
    exact ⟨U, V, hU, hV, hxU, hUV,
      HasRingHomProperty.appLE (@Smooth) f ‹Smooth f› ⟨V, hV⟩ ⟨U, hU⟩ hUV⟩
  obtain ⟨W, hW, hxW, hWT, hstd⟩ :=
    (InfinitesimalLifting.smoothAt_iff_exists_affine_isStandardSmooth f x ⊤
      (isAffineOpen_top T) (by simp)).mp hsm
  refine ⟨W, hW, hxW, ?_⟩
  have : IsAffine W.toScheme := hW
  have : IsAffine (⊤ : T.Opens).toScheme := isAffineOpen_top T
  let e : Arrow.mk (f.resLE ⊤ W hWT) ≅ Arrow.mk (hW.fromSpec ≫ f) :=
    Arrow.isoMk hW.isoSpec T.topIso (by
      dsimp; rw [← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
      exact (Scheme.Hom.resLE_comp_ι f hWT).symm)
  exact (isStandardSmooth_iff_of_arrow_iso
    (f.resLE ⊤ W hWT) (hW.fromSpec ≫ f) e).mp hstd

/-- A smooth covering of an affine scheme has a finite refinement by affine schemes which are
standard smooth over the target; each member of the refinement is an open subscheme of a member of
the original covering. -/
@[stacks 0222]
public theorem exists_finite_affine_standardSmooth_refinement {T : Scheme.{u}} [IsAffine T]
    (U : T.Cover.{v} (Scheme.precoverage (@Smooth.{u}))) :
    ∃ (V : T.AffineCover.{u} (@Smooth.{u}))
        (refinement : V.cover.toPreZeroHypercover.Hom U.toPreZeroHypercover),
      Finite V.I₀ ∧
        (∀ j, IsStandardSmooth (V.f j)) ∧
          ∀ j, IsOpenImmersion (refinement.h₀ j) := by
  have hcov : ∀ t : T, ∃ i y, U.f i y = t :=
    (Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀ |>.1
  let i (t : T) : U.I₀ := (hcov t).choose
  let y (t : T) : U.X (i t) := (hcov t).choose_spec.choose
  have hy (t : T) : U.f (i t) (y t) = t := (hcov t).choose_spec.choose_spec
  have hsm (t : T) : Smooth (U.f (i t)) := U.map_prop (i t)
  let data (t : T) := local_standardSmooth (U.f (i t)) (y t)
  let W (t : T) : (U.X (i t)).Opens := (data t).choose
  let hW (t : T) : IsAffineOpen (W t) := (data t).choose_spec.choose
  let hxW (t : T) : y t ∈ W t := (data t).choose_spec.choose_spec.1
  let hstd (t : T) : IsStandardSmooth ((hW t).fromSpec ≫ U.f (i t)) :=
    (data t).choose_spec.choose_spec.2
  let g (t : T) : Spec Γ(U.X (i t), W t) ⟶ T := (hW t).fromSpec ≫ U.f (i t)
  have hopen (t : T) : IsOpen (Set.range (g t)) := by
    have hh := (Scheme.Hom.isOpenMap (U.f (i t))) _
      (IsOpenImmersion.isOpen_range (hW t).fromSpec)
    convert hh using 1; ext z
    simp only [Set.mem_range, Set.mem_image, g, Scheme.Hom.comp_apply]; aesop
  have hmem (t : T) : t ∈ Set.range (g t) := by
    use (hW t).isoSpec.hom ⟨y t, hxW t⟩
    change U.f (i t) ((hW t).fromSpec ((hW t).isoSpec.hom ⟨y t, hxW t⟩)) = t
    have hh : (hW t).fromSpec ((hW t).isoSpec.hom ⟨y t, hxW t⟩) = y t := by
      change ((hW t).isoSpec.hom ≫ (hW t).fromSpec) ⟨y t, hxW t⟩ = y t
      rw [IsAffineOpen.isoSpec_hom_fromSpec]; rfl
    simpa only [hh] using hy t
  let hc := CompactSpace.elim_nhds_subcover
    (fun t : T => Set.range (g t)) (fun t => (hopen t).mem_nhds (hmem t))
  let s := hc.choose
  have hs : ∀ t : T, ∃ q : s, t ∈ Set.range (g q.1) := by
    intro t
    have ht : t ∈ (⊤ : Set T) := trivial
    rw [← Classical.choose_spec hc, Set.mem_iUnion] at ht
    rcases ht with ⟨q, _, ⟨hq, rfl⟩, hqt⟩
    exact ⟨⟨q, hq⟩, hqt⟩
  let V : T.AffineCover.{u} (@Smooth.{u}) :=
    { I₀ := s
      X q := Γ(U.X (i q.1), W q.1)
      f q := g q.1
      idx t := (hs t).choose
      covers t := (hs t).choose_spec
      map_prop q := by
        dsimp [g]
        infer_instance }
  refine ⟨V, { s₀ q := i q.1
               h₀ q := (hW q.1).fromSpec
               w₀ q := rfl }, ?_, ?_, ?_⟩
  · dsimp [V]; infer_instance
  · exact fun q => hstd q.1
  · intro q; change IsOpenImmersion ((hW q.1).fromSpec); infer_instance

end AlgebraicGeometry
