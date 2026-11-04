module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineDenseSubsite
import all StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineDenseSubsite

/-!
# Every covering of an affine object of the big étale site is refined by a finite affine one

A covering family of an object `T` of a big étale site whose underlying scheme is affine admits
a refinement which is **finite**, consists of **affine** objects, and is still a covering of the
site.  Each member of the refinement also factors through a member of the original family, and
is étale over `T`.

This is the standard-refinement step of Stacks 021E.  It is the input a descent argument needs
when it has to replace an arbitrary étale covering by one along which the affine machinery of
effective descent applies — for instance Stacks 03RV, where a finite locally constant sheaf is
trivialized on *some* étale covering and the descent has to be carried out along a covering by
finitely many affines.

## Main results

* `AlgebraicGeometry.BigEtaleSite.IsCovering.etale_map` — each member of a chosen covering family
  is étale.
* `AlgebraicGeometry.BigEtaleSite.exists_finite_affine_refinement` — **the finite affine
  standard refinement.**

## Implementation notes

The construction is already carried out in
`StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineDenseSubsite`, where it is `private`
(named `finite_standard_refinement`) because it was only needed to prove that affine objects form
a dense subsite.  It is reached here through `import all`, which is this library's idiom for
consuming a private rather than forking its fully qualified name.

The refinement produced there is not stated to be étale over `T`.  That conjunct is supplied here
from the covering family itself, by `AlgebraicGeometry.BigEtaleSite.IsCovering.etale_map`, so the
statement below is the form a consumer needs and no second construction is required.

## References

* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.BigEtaleSite

/-- **Each member of a chosen covering family of a big étale site is étale.**  This is the
`Etale` half of the defining condition `AlgebraicGeometry.IsEtaleCovering`, extracted from the
membership in `AlgebraicGeometry.Scheme.etalePrecoverage`. -/
theorem IsCovering.etale_map {B : AlgebraicGeometry.BigEtaleSite.{u}} {T : B.Scheme}
    {F : PreZeroHypercover T} (hF : B.IsCovering ⟨T, F⟩) (i : F.I₀) :
    Etale (B.inclusion.map (F.f i)) :=
  (show Scheme.Cover Scheme.etalePrecoverage (B.inclusion.obj T) from
    { I₀ := F.I₀
      X i := B.inclusion.obj (F.X i)
      f i := B.inclusion.map (F.f i)
      mem₀ := hF.1 }).map_prop i

/-- **A covering of an affine object of the big étale site is refined by a finite affine
covering.**  Given a covering family `E` of an object `T` whose underlying scheme is affine,
there is a covering family `F` of `T` with finitely many members, all of them affine, each
factoring through a member of `E`, and each étale over `T`.

This is the public form of the standard-refinement step of Stacks 021E. -/
theorem exists_finite_affine_refinement (B : AlgebraicGeometry.BigEtaleSite.{u}) (T : B.Scheme)
    [IsAffine (B.inclusion.obj T)]
    (E : PreZeroHypercover T) (hE : B.IsCovering ⟨T, E⟩) :
    ∃ F : PreZeroHypercover T,
      B.IsCovering ⟨T, F⟩ ∧ Finite F.I₀ ∧
        (∀ i, IsAffine (B.inclusion.obj (F.X i))) ∧
        (∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j, g ≫ E.f j = F.f i) ∧
        ∀ i, Etale (B.inclusion.map (F.f i)) := by
  obtain ⟨F, hF, hfin, haff, hrefine⟩ :=
    AlgebraicGeometry.finite_standard_refinement B T E hE
  exact ⟨F, hF, hfin, haff, hrefine, fun i ↦ IsCovering.etale_map hF i⟩

end AlgebraicGeometry.BigEtaleSite

end
