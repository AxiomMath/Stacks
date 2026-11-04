module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver

/-!
# Étale descent on the source

A property of morphisms of schemes is local on the source for the étale precoverage as soon as
it is Zariski local on the source and on the target, is preserved by precomposition with étale
morphisms, and descends along surjective étale morphisms of affine schemes.

This is the étale case of Tag 036H. It is the étale twin of
`AlgebraicGeometry.isLocalAtSource_syntomic_of_affine_descent`, and like it is obtained from the
general reduction `AlgebraicGeometry.isLocalAtSource_of_affineCriterion` by refining an étale
covering of an affine scheme to a finite covering by affine schemes.

For the étale topology the refinement needs no structure theory: an étale morphism is open, so
finitely many affine opens of the members of the covering already cover a quasi-compact target,
and an affine open subscheme of a member maps to the target by an étale morphism, being the
composition of an open immersion with an étale morphism. This is why the standard étale
structure of Tag 0218 does not appear.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.exists_finite_affine_etale_refinement`: an étale covering of an affine
  scheme is refined, by open immersions, by a finite covering by affine schemes.
* `AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent`: **Stacks 036H**, étale case.
* `AlgebraicGeometry.Smooth.respectsLeft_etale`: precomposition with an étale morphism
  preserves smoothness.
* `AlgebraicGeometry.smooth_isEtaleLocalOnSourceAndTarget_of_affine_descent`: smoothness is
  étale local on the source and target as soon as it descends along a surjective étale
  morphism of affine schemes.

## Implementation notes

Étale coverings are `AlgebraicGeometry.Scheme.Cover` for `AlgebraicGeometry.Scheme.precoverage`
of `AlgebraicGeometry.Etale`, which is `AlgebraicGeometry.Scheme.etalePrecoverage`. The refining
family is an `AlgebraicGeometry.Scheme.AffineCover`, so its members are affine by construction,
and each component of the refinement morphism is an open immersion, which says that every
refining member is an affine open subscheme of the selected member of the original covering.

Openness of the range of an étale morphism is inherited from smoothness, since an étale
morphism is smooth and a smooth morphism is open.

For smoothness the criterion gives the reduction of Tag 04R3 to a statement about affine
schemes. Mathlib's Zariski locality instances for `AlgebraicGeometry.Smooth` are supplied by
name rather than by synthesis, because the ring-homomorphism property they are indexed by is
not an output parameter and so cannot be inferred from `AlgebraicGeometry.Smooth` alone.

## References

* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- An étale covering of an affine scheme has a finite refinement by affine schemes; each
member of the refinement is an affine open subscheme of a member of the original covering. -/
theorem exists_finite_affine_etale_refinement {T : Scheme.{u}} [IsAffine T]
    (U : T.Cover.{v} (Scheme.precoverage (@Etale.{u}))) :
    ∃ (V : T.AffineCover.{u} (@Etale.{u}))
        (refinement : V.cover.toPreZeroHypercover.Hom U.toPreZeroHypercover),
      Finite V.I₀ ∧ ∀ j, IsOpenImmersion (refinement.h₀ j) := by
  classical
  choose i y hy using
    ((Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀).1
  choose W hW hxW _ using fun t =>
    exists_isAffineOpen_mem_and_subset (X := U.X (i t)) (x := y t) (U := ⊤) (by simp)
  let g (t : T) : Spec Γ(U.X (i t), W t) ⟶ T := (hW t).fromSpec ≫ U.f (i t)
  have : ∀ t, Etale (U.f (i t)) := fun t => U.map_prop (i t)
  have hopen (t : T) : IsOpen (Set.range (g t)) := by
    convert (U.f (i t)).isOpenMap _ (IsOpenImmersion.isOpen_range (hW t).fromSpec) using 1
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
  let V : T.AffineCover.{u} (@Etale.{u}) :=
    { I₀ := s
      X q := Γ(U.X (i q.1), W q.1)
      f q := g q.1
      idx t := (hs t).choose
      covers t := (hs t).choose_spec
      map_prop q := by
        dsimp only [g]
        infer_instance }
  refine ⟨V, { s₀ q := i q.1
               h₀ q := (hW q.1).fromSpec
               w₀ q := rfl }, ?_, ?_⟩
  · exact inferInstanceAs (Finite s)
  · exact fun q => (inferInstance : IsOpenImmersion ((hW q.1).fromSpec))

/-- **Stacks Project, Tag 036H, étale case.** A property of morphisms of schemes which is
Zariski local on the source and on the target, which is preserved by precomposition with étale
morphisms, and which descends along surjective étale morphisms of affine schemes, is étale
local on the source. -/
@[stacks 036H "étale case"]
theorem isLocalAtSource_etale_of_affine_descent (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Etale.{u})] [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Etale g → P (g ≫ f) → P f) :
    P.IsLocalAtSource Scheme.etalePrecoverage := by
  have := precoverage_isStableUnderBaseChange (@Etale.{u})
  have h : P.IsLocalAtSource (Scheme.precoverage (@Etale.{u})) := by
    refine isLocalAtSource_of_affineCriterion (P := P) (Q := @Etale.{u})
      (K := Scheme.precoverage (@Etale.{u})) (fun U i ↦ ?_) (fun {X Y} _ _ f U hU ↦ ?_)
    · exact ((Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀).2 i
    · let U' : X.Cover (Scheme.precoverage (@Etale.{u})) :=
        { __ := U.toPreZeroHypercover, mem₀ := U.mem₀ }
      obtain ⟨V, r, hfinite, hopen⟩ := exists_finite_affine_etale_refinement U'
      have : Finite V.I₀ := hfinite
      exact affine_descent_of_refinement P f U' V r hopen hU hAffine
        (sigmaDesc_of_hasRingHomProperty (Q := @Etale.{u}) V.f V.map_prop)
  exact h

/-- Precomposition with an étale morphism preserves smoothness: an étale morphism is smooth,
and smooth morphisms compose. -/
theorem Smooth.respectsLeft_etale :
    MorphismProperty.RespectsLeft (@Smooth : MorphismProperty Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) where
  precomp i hi f hf := by
    have : Etale i := hi
    have : Smooth f := hf
    infer_instance

/-- Being a smooth morphism of schemes is étale local on the source and target, given that
smoothness descends along a surjective étale morphism of affine schemes.

This is the reduction of Tag 04R3 for smoothness to a single statement about affine schemes.
Neither Tag 04R2 nor locality of smoothness on the target is used: étale postcomposition
preserves smoothness outright, by `AlgebraicGeometry.Smooth.respectsRight_etale`, and étale
base change is Mathlib's `AlgebraicGeometry.smooth_isStableUnderBaseChange`. -/
theorem smooth_isEtaleLocalOnSourceAndTarget_of_affine_descent
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Etale g → Smooth (g ≫ f) → Smooth f) :
    IsEtaleLocalOnSourceAndTarget (@Smooth : MorphismProperty Scheme.{u}) :=
  let := Smooth.respectsLeft_etale.{u}
  let : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  let : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth.{u}) (Q := RingHom.Smooth)
  let := isLocalAtSource_etale_of_affine_descent
    (@Smooth : MorphismProperty Scheme.{u}) hAffine
  smooth_isEtaleLocalOnSourceAndTarget

end AlgebraicGeometry

end
