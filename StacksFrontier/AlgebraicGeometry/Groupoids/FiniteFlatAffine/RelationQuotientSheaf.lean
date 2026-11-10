module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.FppfLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fppf quotient sheaf of a finite locally free equivalence relation is representable

Let `j : R ⟶ U ×_S U` be an internal equivalence relation of schemes over `S` whose relation
scheme and whose base are affine and whose source and target maps are finite locally free, and
let `U` be small enough to be an object of a big fppf site over `S`. The quotient sheaf `U/R`
for the fppf topology is then representable, by the spectrum of the ring of invariant functions
on `U`.

## Main results

* `Stacks.Groupoids.isRepresentable_quotientSheaf_of_isFiniteLocallyFree`: the quotient sheaf
  of such a relation is representable.

## Implementation notes

The quotient scheme and the surjective finite locally free projection onto it come from
`AlgebraicGeometry.Space.exists_quotient_of_isFiniteLocallyFree_relation`, which is the
affine quotient of a finite flat groupoid read for an equivalence relation. That projection
realises the quotient sheaf by the representability criterion
`Stacks.Groupoids.isIso_quotientSheafToPoints`: it induces a locally surjective map of functors
of points because it is flat, locally of finite presentation and surjective, and the comparison
`R ⟶ U ×_{U/R} U` is an isomorphism because the relation *is* the kernel pair of the
projection.

The size bound on `U` is what places the quotient scheme in the site: the quotient is a
subscheme of the spectrum of the global functions of `U`, so it is no larger than `U`. Without
it the functor of points of the quotient is a sheaf and is isomorphic to the quotient sheaf,
but is not represented by an object of the site.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

/-- **The fppf quotient sheaf of a finite locally free equivalence relation on an affine scheme
is representable.** The relation scheme and the base are assumed affine, the source and target
maps finite locally free, and the base small enough to lie in the chosen big fppf site; the
representing object is the spectrum of the ring of invariant functions. -/
@[sga "3 V 4.1" "(iv), special case", sga "3 VIA 5.4.1" "special case"]
theorem isRepresentable_quotientSheaf_of_isFiniteLocallyFree
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {R U : Over S}
    (j : PreRelation R U) [IsAffine U.left] [IsAffine R.left]
    [Stacks.Morphisms.IsFiniteLocallyFree j.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree j.target.left]
    [IsEquivalenceRelation j.target j.source] (hU : U.left.size < B.cutoff) :
    (quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) j).obj.IsRepresentable := by
  classical
  obtain ⟨A, _, g, π, hsize, hflf, hsurj, hpb⟩ :=
    Space.exists_quotient_of_isFiniteLocallyFree_relation S j.target j.source
  have _ := hflf
  have _ := hsurj
  have _ : Flat π.left := Stacks.Morphisms.IsFiniteLocallyFree.flat π.left
  have _ : LocallyOfFinitePresentation π.left :=
    Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left
  have hcontains : B.Contains (Spec (CommRingCat.of A)) := lt_of_le_of_lt hsize hU
  have hf : j.target ≫ π = j.source ≫ π := hpb.w
  have hM := isSheaf_points B S hS (Over.mk g)
  -- The relation is the kernel pair of the projection, so the comparison map is an isomorphism.
  have hk : IsIso (pullback.lift j.target j.source hf) := by
    have he : (hpb.isoIsPullback U U (IsPullback.of_hasPullback π π)).hom =
        pullback.lift j.target j.source hf := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst]
        exact hpb.isoIsPullback_hom_fst U U (IsPullback.of_hasPullback π π)
      · rw [pullback.lift_snd]
        exact hpb.isoIsPullback_hom_snd U U (IsPullback.of_hasPullback π π)
    rw [← he]
    infer_instance
  have _ := hk
  have _ : IsIso (pullback.lift j.target j.source hf).left := by
    change IsIso ((Over.forget S).map (pullback.lift j.target j.source hf))
    infer_instance
  have hiso : IsIso (quotientSheafToPoints (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) j π hf hM) :=
    isIso_quotientSheafToPoints _ _ j π hf hM
      (isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective B S hS π)
      (isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective B S hS
        (pullback.lift j.target j.source hf))
  have _ := hiso
  -- The quotient scheme lies in the site, so its functor of points is representable.
  have hrep : (points (Over.post (X := B.obj hS) B.inclusion)
      (Over.mk g)).IsRepresentable := by
    refine isRepresentable_of_natIso
      (yoneda.obj (Over.mk (⟨g⟩ : B.obj hcontains ⟶ B.obj hS))) ?_
    exact (Space.pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion)
      (Over.mk (⟨g⟩ : B.obj hcontains ⟶ B.obj hS))).symm
  have _ := hrep
  exact isRepresentable_of_natIso (points (Over.post (X := B.obj hS) B.inclusion) (Over.mk g))
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
      (asIso (quotientSheafToPoints (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j π hf hM))).symm

end Stacks.Groupoids

end
