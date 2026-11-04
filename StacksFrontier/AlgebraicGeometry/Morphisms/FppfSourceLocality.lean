module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Source locality for the fppf topology of schemes

**Stacks 036H** reduces source locality of a property `P` of morphisms of schemes, for each of
the five topologies, to a statement about affine schemes: if `P` is Zariski local on the source
and on the target, is preserved by precomposition with the morphisms appearing in the coverings,
and descends along a surjective such morphism of affine schemes, then `P` is local on the source
for that topology. This module proves the **fppf** case, the remaining one of the four that
`AlgebraicGeometry.Scheme.fppfPrecoverage` makes available, and instantiates it at local finite
type to give **Stacks 036O**.

An fppf covering is a jointly surjective family of flat morphisms locally of finite presentation,
so the reduction needs the fppf analogue of
`AlgebraicGeometry.exists_finite_affine_etale_refinement`: an fppf covering of an affine scheme
has a finite refinement by affine opens of its members. The only non-formal input is that a flat
morphism locally of finite presentation is universally open (**Stacks 01UA**, Mathlib's
`AlgebraicGeometry.Scheme.Hom.isOpenMap`), which replaces the openness of a smooth morphism used
in the étale case; quasi-compactness of the affine base then selects finitely many members.

## Main results

* `AlgebraicGeometry.exists_finite_affine_fppf_refinement`: an fppf covering of an affine scheme
  has a finite refinement by affine schemes, each member an affine open subscheme of a member of
  the original covering.
* `AlgebraicGeometry.isLocalAtSource_fppf_of_affine_descent`: **Stacks 036H**, fppf case.
* `AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSource_fppfPrecoverage`: **Stacks 036O**, being
  locally of finite type is fppf local on the source.

## Implementation notes

Neither of the two results carries a `@[stacks]` attribute; both are statements of the Descent
chapter (Chapter 35).
For `AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSource_fppfPrecoverage` the statement is
complete: Stacks 036O is the single assertion that local finite type is fppf local on the
source, and that is exactly this declaration's statement.

The instantiation at local finite type is the étale and smooth siblings' body verbatim — its only
non-formal input is **Stacks 0367**, the descent of finite type along a faithfully flat ring map
of finite presentation, through
`RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation`. Those two siblings
(`AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSource_etalePrecoverage` and
`AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSource_smoothPrecoverage`) already use the
faithfully-flat-of-finite-presentation input while concluding only the weaker étale and smooth
statements, so the fppf case needs no new ring theory at all; what it needed was the covering
combinatorics above. Both siblings' implementation notes explain that they withhold `@[stacks
036O]` because they prove something strictly weaker than it, and those notes remain correct.

The two Zariski locality instances and the
`CategoryTheory.MorphismProperty.RespectsLeft` instance are supplied by name rather than by
synthesis, for the reasons the étale and smooth siblings give: the ring-homomorphism property
indexing `AlgebraicGeometry.HasRingHomProperty` is not an output parameter, and `RespectsLeft`
at `@AlgebraicGeometry.Flat ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation` does not
synthesize.

Two of the four imports are reachable transitively through
`StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource`, so they are retained
as documentation rather than for necessity:
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality` is where the étale refinement that
`AlgebraicGeometry.exists_finite_affine_fppf_refinement` mirrors lives, and
`StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme` is where the topology-free reduction
`AlgebraicGeometry.isLocalAtSource_of_affineCriterion` and the finite descent step
`AlgebraicGeometry.affine_descent_of_refinement` live.

## References

* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 036O](https://stacks.math.columbia.edu/tag/036O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- An fppf covering of an affine scheme has a finite refinement by affine schemes; each
member of the refinement is an affine open subscheme of a member of the original covering.

The range of each member of the refinement is open because a flat morphism locally of finite
presentation is universally open (Stacks 01UA) and an affine open has open range, and the affine
base is quasi-compact, so finitely many of those ranges already cover it. -/
theorem exists_finite_affine_fppf_refinement {T : Scheme.{u}} [IsAffine T]
    (U : T.Cover.{v} Scheme.fppfPrecoverage) :
    ∃ (V : T.AffineCover.{u} (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}))
        (refinement : V.cover.toPreZeroHypercover.Hom U.toPreZeroHypercover),
      Finite V.I₀ ∧ ∀ j, IsOpenImmersion (refinement.h₀ j) := by
  classical
  have hdata := (Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀
  have hflat (j) : Flat (U.f j) := (hdata.2 j).1
  have hlfp (j) : LocallyOfFinitePresentation (U.f j) := (hdata.2 j).2
  have hcov : ∀ t : T, ∃ i y, U.f i y = t := by
    intro t
    obtain ⟨i, y, hy⟩ := hdata.1 t
    exact ⟨i, y, hy⟩
  let i (t : T) : U.I₀ := (hcov t).choose
  let y (t : T) : U.X (i t) := (hcov t).choose_spec.choose
  have hy (t : T) : U.f (i t) (y t) = t := (hcov t).choose_spec.choose_spec
  have data (t : T) := exists_isAffineOpen_mem_and_subset
    (X := U.X (i t)) (x := y t) (U := ⊤) (by simp)
  let W (t : T) : (U.X (i t)).Opens := (data t).choose
  have hW (t : T) : IsAffineOpen (W t) := (data t).choose_spec.1
  have hxW (t : T) : y t ∈ W t := (data t).choose_spec.2.1
  let g (t : T) : Spec Γ(U.X (i t), W t) ⟶ T := (hW t).fromSpec ≫ U.f (i t)
  have hopen (t : T) : IsOpen (Set.range (g t)) := by
    convert (U.f (i t)).isOpenMap _ (IsOpenImmersion.isOpen_range (hW t).fromSpec) using 1
    ext z
    simp only [Set.mem_range, Set.mem_image, g, Scheme.Hom.comp_apply]
    aesop
  have hmemrange (t : T) : t ∈ Set.range (g t) := by
    refine ⟨(hW t).isoSpec.hom ⟨y t, hxW t⟩, ?_⟩
    have hh : ((hW t).isoSpec.hom ≫ (hW t).fromSpec) ⟨y t, hxW t⟩ = y t := by
      rw [IsAffineOpen.isoSpec_hom_fromSpec]; rfl
    have hh' : (hW t).fromSpec ((hW t).isoSpec.hom ⟨y t, hxW t⟩) = y t := hh
    simpa only [g, Scheme.Hom.comp_apply, hh'] using hy t
  obtain ⟨s, hs₀⟩ := CompactSpace.elim_nhds_subcover
    (fun t : T => Set.range (g t)) fun t => (hopen t).mem_nhds (hmemrange t)
  have hs : ∀ t : T, ∃ q : s, t ∈ Set.range (g q.1) := by
    intro t
    have ht : t ∈ (⊤ : Set T) := trivial
    rw [← hs₀, Set.mem_iUnion] at ht
    rcases ht with ⟨q, _, ⟨hq, rfl⟩, hqt⟩
    exact ⟨⟨q, hq⟩, hqt⟩
  let V : T.AffineCover.{u} (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) :=
    { I₀ := s
      X q := Γ(U.X (i q.1), W q.1)
      f q := g q.1
      idx t := (hs t).choose
      covers t := (hs t).choose_spec
      map_prop q := by
        dsimp only [g]
        exact ⟨inferInstance, inferInstance⟩ }
  exact ⟨V, { s₀ q := i q.1
              h₀ q := (hW q.1).fromSpec
              w₀ q := rfl },
    inferInstanceAs (Finite s), fun q => inferInstanceAs (IsOpenImmersion (hW q.1).fromSpec)⟩

/-- **Stacks Project, Tag 036H, fppf case.** A property of morphisms of schemes which is
Zariski local on the source and on the target, which is preserved by precomposition with flat
morphisms locally of finite presentation, and which descends along a surjective flat morphism of
finite presentation of affine schemes, is fppf local on the source.

Deliberately untagged; see the implementation notes. -/
theorem isLocalAtSource_fppf_of_affine_descent (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u})]
    [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Flat g → LocallyOfFinitePresentation g →
        P (g ≫ f) → P f) :
    P.IsLocalAtSource Scheme.fppfPrecoverage := by
  refine isLocalAtSource_of_affineCriterion (P := P)
    (Q := @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u})
    (K := Scheme.fppfPrecoverage.{u})
    (fun U i ↦ ?_) (fun {X Y} _ _ f U hU ↦ ?_)
  · exact ((Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀).2 i
  · obtain ⟨V, r, hfinite, hopen⟩ :=
      exists_finite_affine_fppf_refinement
        (T := X) { __ := U.toPreZeroHypercover, mem₀ := U.mem₀ }
    have : Finite V.I₀ := hfinite
    exact affine_descent_of_refinement P f
      { __ := U.toPreZeroHypercover, mem₀ := U.mem₀ } V r hopen hU
      (fun g f₀ hg hQ hcomp ↦ hAffine g f₀ hg hQ.1 hQ.2 hcomp)
      ⟨sigmaDesc_of_hasRingHomProperty (Q := @Flat.{u}) V.f fun j ↦ (V.map_prop j).1,
        sigmaDesc_of_hasRingHomProperty (Q := @LocallyOfFinitePresentation.{u}) V.f
          fun j ↦ (V.map_prop j).2⟩

/-- **Stacks Project, Tag 036O.** Being locally of finite type is local on the source for the
fppf topology of schemes.

This is the fppf case of Stacks 036H applied to local finite type. Its only non-formal input is
Stacks 0367, the descent of finite type along a faithfully flat ring map of finite presentation —
the same input the étale and smooth siblings already use.

Deliberately untagged; see the implementation notes. -/
@[ega "IV 11.3.16" "local finite type of g", sga "3 V 9.1" "partial"]
instance LocallyOfFiniteType.isLocalAtSource_fppfPrecoverage :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  letI : MorphismProperty.RespectsLeft
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) :=
    { precomp := fun i hi f hf => by
        have : LocallyOfFinitePresentation i := hi.2
        have : LocallyOfFiniteType f := hf
        exact inferInstance }
  letI : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  letI : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  isLocalAtSource_fppf_of_affine_descent (@LocallyOfFiniteType.{u})
    fun {_X' _X _Y} _ _ _ g f hg hgflat hglfp hcomp => by
      have : Surjective g := hg
      have : Flat g := hgflat
      have : LocallyOfFinitePresentation g := hglfp
      rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
      refine RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation
        (f := f.appTop.hom) (g := g.appTop.hom) ?_ ?_
        (Scheme.Hom.finitePresentation_appTop g)
      · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
          HasRingHomProperty.appTop (@LocallyOfFiniteType.{u}) (g ≫ f) hcomp
      · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
          ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry

end
