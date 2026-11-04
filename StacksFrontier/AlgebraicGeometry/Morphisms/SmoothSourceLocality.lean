module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.AffineCriteria
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme

/-!
# Smoothness is local on the source for the smooth topology

Smoothness of morphisms of schemes is local on the source for the smooth precoverage
(**Stacks 036U**): a morphism is smooth exactly when its composites with the members of a smooth
covering of its source are smooth.

## Main results

* `AlgebraicGeometry.exists_finite_affine_refinement_of_universallyOpen`: a covering of an
  affine scheme by universally open morphisms with a given property is refined, by open
  immersions, by a finite covering by affine schemes.
* `AlgebraicGeometry.Smooth.isLocalAtSource_smoothPrecoverage`: **Stacks 036U**.

## References

* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 036U](https://stacks.math.columbia.edu/tag/036U)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A covering of an affine scheme by morphisms with a property `Q` whose morphisms are
universally open and which is preserved by precomposition with open immersions has a finite
refinement by affine schemes; each member of the refinement is an affine open subscheme of a
member of the original covering. -/
theorem exists_finite_affine_refinement_of_universallyOpen (Q : MorphismProperty Scheme.{u})
    [Q.RespectsLeft (@IsOpenImmersion.{u})]
    (hQ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Q f → UniversallyOpen f)
    {T : Scheme.{u}} [IsAffine T] (U : T.Cover.{v} (Scheme.precoverage Q)) :
    ∃ (V : T.AffineCover.{u} Q)
        (refinement : V.cover.toPreZeroHypercover.Hom U.toPreZeroHypercover),
      Finite V.I₀ ∧ ∀ j, IsOpenImmersion (refinement.h₀ j) := by
  classical
  have hcov : ∀ t : T, ∃ i y, U.f i y = t :=
    (Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀ |>.1
  choose i y hy using hcov
  let data (t : T) := exists_isAffineOpen_mem_and_subset
    (X := U.X (i t)) (x := y t) (U := ⊤) (by simp)
  let W (t : T) : (U.X (i t)).Opens := (data t).choose
  have hW (t : T) : IsAffineOpen (W t) := (data t).choose_spec.1
  have hxW (t : T) : y t ∈ W t := (data t).choose_spec.2.1
  let g (t : T) : Spec Γ(U.X (i t), W t) ⟶ T := (hW t).fromSpec ≫ U.f (i t)
  have hopen (t : T) : IsOpen (Set.range (g t)) := by
    have : UniversallyOpen (U.f (i t)) := hQ _ (U.map_prop (i t))
    convert (Scheme.Hom.isOpenMap (U.f (i t))) _
      (IsOpenImmersion.isOpen_range (hW t).fromSpec) using 1
    ext z
    simp only [Set.mem_range, Set.mem_image, g, Scheme.Hom.comp_apply]
    aesop
  have hmem (t : T) : t ∈ Set.range (g t) := by
    refine ⟨(hW t).isoSpec.hom ⟨y t, hxW t⟩, ?_⟩
    have hh : ((hW t).isoSpec.hom ≫ (hW t).fromSpec) ⟨y t, hxW t⟩ = y t := by
      rw [IsAffineOpen.isoSpec_hom_fromSpec]
      rfl
    have hh' : (hW t).fromSpec ((hW t).isoSpec.hom ⟨y t, hxW t⟩) = y t := hh
    simpa only [g, Scheme.Hom.comp_apply, hh'] using hy t
  obtain ⟨s, hsU⟩ := CompactSpace.elim_nhds_subcover
    (fun t : T => Set.range (g t)) (fun t => (hopen t).mem_nhds (hmem t))
  have hs : ∀ t : T, ∃ q : s, t ∈ Set.range (g q.1) := by
    intro t
    have ht : t ∈ (⊤ : Set T) := trivial
    rw [← hsU, Set.mem_iUnion] at ht
    rcases ht with ⟨q, _, ⟨hq, rfl⟩, hqt⟩
    exact ⟨⟨q, hq⟩, hqt⟩
  let V : T.AffineCover.{u} Q :=
    { I₀ := s
      X q := Γ(U.X (i q.1), W q.1)
      f q := g q.1
      idx t := (hs t).choose
      covers t := (hs t).choose_spec
      map_prop q := by
        dsimp only [g]
        exact MorphismProperty.RespectsLeft.precomp (P := Q) (Q := @IsOpenImmersion.{u})
          ((hW q.1).fromSpec) inferInstance _ (U.map_prop (i q.1)) }
  refine ⟨V,
    { s₀ q := i q.1
      h₀ q := (hW q.1).fromSpec
      w₀ q := rfl }, ?_, ?_⟩
  · dsimp only [V]
    infer_instance
  · exact fun q => (inferInstance : IsOpenImmersion ((hW q.1).fromSpec))

/-- **Stacks 036U.** Smoothness of morphisms of schemes is local on the source for the smooth
topology: a morphism is smooth exactly when its composites with the members of a smooth covering
of its source are smooth.

The affine descent hypothesis of the smooth case of Stacks 036H is the smooth case of
Stacks 02KM, which holds without any affineness assumption. -/
@[stacks 036U, sga "4 IV 8.5.5" "special case"]
instance Smooth.isLocalAtSource_smoothPrecoverage :
    MorphismProperty.IsLocalAtSource (@Smooth : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
  letI : MorphismProperty.RespectsLeft (@Smooth.{u}) (@Smooth.{u}) :=
    { precomp := fun i hi f hf => by
        have : Smooth i := hi
        have : Smooth f := hf
        exact inferInstance }
  letI : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  letI : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth.{u}) (Q := RingHom.Smooth)
  isLocalAtSource_smooth_of_affine_descent (@Smooth.{u}) fun g f hg hg' hcomp =>
    have : Surjective g := hg
    have : Smooth g := hg'
    have : Smooth (g ≫ f) := hcomp
    Stacks.Smooth.smooth_of_comp_surjective_smooth g f

end AlgebraicGeometry

end
