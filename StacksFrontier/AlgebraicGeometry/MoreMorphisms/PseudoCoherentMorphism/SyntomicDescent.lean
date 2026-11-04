module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.SyntomicLocalAtSource
public import StacksFrontier.RingTheory.PseudoCoherentMap.SyntomicDescent

/-!
# Pseudo-coherence is local on the source for the syntomic topology

Pseudo-coherence of morphisms of schemes is local on the source for the syntomic topology, which
is Tag 0698. The reduction of that statement to a single statement about affine schemes is
`AlgebraicGeometry.pseudoCoherent_isLocalAtSource_of_affine_descent`; what is added here is the
affine statement it leaves open, namely that pseudo-coherence descends along a surjective
syntomic morphism of affine schemes.

On global sections a surjective syntomic morphism of affine schemes is a syntomic and faithfully
flat ring map, by `AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`
and by the affine-local description of syntomicity through
`AlgebraicGeometry.HasRingHomProperty`, so the affine statement is exactly
`Algebra.PseudoCoherent.of_syntomic_faithfullyFlat`.

## Main results

* `AlgebraicGeometry.pseudoCoherent_of_comp_surjective_syntomic_of_isAffine`: the affine case,
  the mathematical content of Tag 0698.
* `AlgebraicGeometry.PseudoCoherent.isLocalAtSource_syntomicPrecoverage`: **Tag 0698**.

## Implementation notes

The three algebra structures on the rings of global sections are supplied by `let` from the
induced maps on sections rather than by synthesis, since nothing makes `Γ(X', ⊤)` an algebra over
`Γ(Y, ⊤)` on its own; with those choices the scalar towers hold by `rfl` and the hypothesis on
the composite is the pseudo-coherence of `g.appTop ≫ f.appTop` transported across
`AlgebraicGeometry.Scheme.Hom.comp_appTop`.

## References

* [The Stacks Project, Lemma 37.60.13 (0698)](https://stacks.math.columbia.edu/tag/0698)
* [The Stacks Project, Lemma 35.26.4 (036H)](https://stacks.math.columbia.edu/tag/036H)
* [The Stacks Project, Definition 37.60.2 (067Z)](https://stacks.math.columbia.edu/tag/067Z)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 0698, the affine case.** If `g : X' ⟶ X` is a surjective syntomic morphism of
affine schemes and `g ≫ f : X' ⟶ Y` is pseudo-coherent, then `f : X ⟶ Y` is pseudo-coherent.

On global sections `g` is a syntomic and faithfully flat ring map, so this is
`Algebra.PseudoCoherent.of_syntomic_faithfullyFlat`. -/
theorem pseudoCoherent_of_comp_surjective_syntomic_of_isAffine {X' X Y : Scheme.{u}}
    [IsAffine X'] [IsAffine X] [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    (hgsurj : Surjective g) (hg : Syntomic g) (hcomp : PseudoCoherent (g ≫ f)) :
    PseudoCoherent f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @PseudoCoherent)]
  algebraize [f.appTop.hom, g.appTop.hom, g.appTop.hom.comp f.appTop.hom]
  have : Module.FaithfullyFlat Γ(X, ⊤) Γ(X', ⊤) :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨flat hg, hgsurj⟩
  have : Algebra.Syntomic Γ(X, ⊤) Γ(X', ⊤) :=
    HasRingHomProperty.appTop (P := @Syntomic) g hg
  have hcomp' : RingHom.PseudoCoherent (g.appTop.hom.comp f.appTop.hom) := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      HasRingHomProperty.appTop (P := @PseudoCoherent) (g ≫ f) hcomp
  exact hcomp'.of_syntomic_faithfullyFlat

/-- **Stacks 0698.** Pseudo-coherence of morphisms of schemes is local on the source for the
syntomic topology.

This is `AlgebraicGeometry.pseudoCoherent_isLocalAtSource_of_affine_descent`, the reduction of
the source's statement to the case of a surjective syntomic morphism of affine schemes, with
that case discharged by
`AlgebraicGeometry.pseudoCoherent_of_comp_surjective_syntomic_of_isAffine`. -/
@[stacks 0698]
instance PseudoCoherent.isLocalAtSource_syntomicPrecoverage :
    MorphismProperty.IsLocalAtSource (@PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Syntomic.{u})) :=
  pseudoCoherent_isLocalAtSource_of_affine_descent fun g f hgsurj hg hcomp =>
    pseudoCoherent_of_comp_surjective_syntomic_of_isAffine g f hgsurj hg hcomp

end AlgebraicGeometry

end
