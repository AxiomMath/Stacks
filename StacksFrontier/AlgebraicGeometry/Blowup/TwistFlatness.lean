module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOneLocal
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk

/-!
# Invertible sheaves of modules are flat, and the twists on the affine blowup

An invertible sheaf of modules on a ringed space is flat. Flatness is a condition on stalks
(Tag 05NE), and the stalk of an invertible sheaf of modules is an invertible module over the
stalk of the structure sheaf, hence finitely generated projective, hence flat.

Applied to the affine blowup `Stacks.Blowup.blowUpSpec I = Proj (reesGrading I)`, whose twists
`𝒪(q)` are invertible because the Rees algebra is generated in degree one, this says that every
twist on the affine blowup is a flat `𝒪`-module. A flat module placed in a single degree is a
K-flat complex by Tag 06YQ, so the single complex `𝒪(q)[0]` is K-flat as well; that is the form
in which the twists enter a derived pullback along the structure morphism of the blowup.

## Main results

* `Stacks.SheafOfModules.isFlat_of_isInvertible`: an invertible sheaf of modules on a ringed
  space is flat.
* `Stacks.Blowup.isFlat_twistingSheaf_reesGrading`: every twist `𝒪(q)` on the affine blowup is
  a flat sheaf of modules.
* `Stacks.Blowup.kFlat_single_twistingSheaf_reesGrading` and
  `Stacks.Blowup.kFlat_singleFunctor_twistingSheaf_reesGrading`: the complex `𝒪(q)[0]` is
  K-flat, at the two spellings of the single complex.

## Implementation notes

The `𝒪_{X,x}`-module structure on a module stalk of Tag 01CB exists in two copies: the one built
by hand in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorStalkRingedSpace.lean`, which the
invertibility of the stalks is stated over, and Mathlib's, which the stalk criterion for flatness
is stated over. They are equal, both being pinned down by `germ (r • m) = germ r • germ m`; that
equality is `Stacks.SheafOfModules.stalkModule_eq` and it is the only step of
`isFlat_of_isInvertible` beyond the two inputs.

## References

* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

/-- **An invertible sheaf of modules on a ringed space is flat.** By Tag 05NE flatness is the
stalkwise condition, and by Tag 0B8K the stalk `L_x` of an invertible `L` is an invertible
`𝒪_{X,x}`-module, hence finitely generated projective and therefore flat. -/
theorem isFlat_of_isInvertible {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hL : IsInvertible X.presheaf (structureSheafRing X).property L) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) L := by
  refine (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat
    (X := X.carrier) (O := X.sheaf) L).2 fun x => ?_
  have := hL
  have hflat : @Module.Flat _ _ _ _ (TensorStalkRingedSpace.stalkModule X L.val x) :=
    have := module_invertible_grpStalk X L x
    inferInstance
  rw [stalkModule_eq X L.val x] at hflat
  exact hflat

end Stacks.SheafOfModules

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **Every twist on the affine blowup is a flat sheaf of modules.** The twists `𝒪(q)` on
`Proj` of the Rees algebra are invertible, and an invertible sheaf of modules is flat. -/
theorem isFlat_twistingSheaf_reesGrading (q : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (Stacks.Blowup.blowUpSpec I).toRingedSpace.sheaf)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (Stacks.Blowup.reesGrading I) q) :=
  Stacks.SheafOfModules.isFlat_of_isInvertible
    (X := (Stacks.Blowup.blowUpSpec I).toRingedSpace) _ (isInvertible_blowUpTwist I q)

/-- **The complex `𝒪(q)[0]` on the affine blowup is K-flat.** Its only nonzero term is flat,
and a flat module placed in a single degree is K-flat by Tag 06YQ. -/
theorem kFlat_single_twistingSheaf_reesGrading (q : ℤ) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex
      (Stacks.Blowup.blowUpSpec I).toRingedSpace
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
          (Stacks.Blowup.reesGrading I) q)) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ _
    (isFlat_twistingSheaf_reesGrading I q) 0

/-- `kFlat_single_twistingSheaf_reesGrading` at the `CochainComplex.singleFunctor` spelling of
the single complex. -/
theorem kFlat_singleFunctor_twistingSheaf_reesGrading (q : ℤ) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex
      (Stacks.Blowup.blowUpSpec I).toRingedSpace
      ((CochainComplex.singleFunctor _ 0).obj
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
          (Stacks.Blowup.reesGrading I) q)) :=
  kFlat_single_twistingSheaf_reesGrading I q

end Stacks.Blowup

end
