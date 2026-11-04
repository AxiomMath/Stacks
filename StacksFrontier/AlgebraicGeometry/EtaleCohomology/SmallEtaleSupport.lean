module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints

/-!
# The support of an abelian sheaf on Mathlib's small étale site

The support of an abelian sheaf `F` on the small étale site of a scheme `X` is the set of points
`x ∈ X` over which some geometric point has nonzero stalk. This is the definition of
[Stacks, Tag 04FS], on Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`
and with the stalk `Stacks.EtaleCohomology.smallEtaleStalkAb` at the site point
`AlgebraicGeometry.Scheme.pointSmallEtale` of a geometric point. The library's other two supports,
`AlgebraicGeometry.supportSheaf` and `AlgebraicGeometry.SmallEtale.supportSheaf`, are stated on the
size-bounded small étale site of a big étale site.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleSupport` — the support of an abelian sheaf on Mathlib's small
  étale site.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSupport_subset_iff` — the support is contained in a set `E`
  exactly when the stalk vanishes at every geometric point not lying over `E`.

## References

* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- The support of an abelian sheaf on Mathlib's small étale site of `X`: the points of `X` over
which some geometric point has nonzero stalk. -/
def smallEtaleSupport {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Set X :=
  {x | ∃ s : GeometricPoint X, s.LiesOver x ∧ ¬ IsZero ((smallEtaleStalkAb s.hom).obj F)}

/-- The support of `F` is contained in `E` exactly when the stalk of `F` vanishes at every
geometric point whose image does not lie in `E`. -/
theorem smallEtaleSupport_subset_iff {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (E : Set X) :
    smallEtaleSupport F ⊆ E ↔
      ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) ∉ E →
        IsZero ((smallEtaleStalkAb s.hom).obj F) := by
  have hpt : ∀ s : GeometricPoint X,
      s.hom default = s.hom (IsLocalRing.closedPoint s.residueField) := fun s =>
    congrArg s.hom (Subsingleton.elim _ _)
  constructor
  · intro h s hs
    by_contra hn
    exact hs (hpt s ▸ h ⟨s, rfl, hn⟩)
  · rintro h x ⟨s, rfl, hn⟩
    by_contra hx
    exact hn (h s (hpt s ▸ hx))

end Stacks.EtaleCohomology

end
