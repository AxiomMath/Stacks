module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionExists
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# K-flat resolutions of complexes of modules on a ringed space

A ringed space is a ringed site: the site is the poset of its open sets with the open-cover
topology, and the structure sheaf is unchanged. So the K-flat resolutions built on a ringed site
in `StacksDraft.Ch21.Sec17.ExistsKFlatResolution` are available for complexes of
`𝒪_X`-modules on a ringed space, with no transport of the statement in between.

## Main definitions

* `AlgebraicGeometry.RingedSpace.ringedSite`: a ringed space, read as a ringed site.

## Main results

* `AlgebraicGeometry.RingedSpace.ringSheaf_ringedSite`: the sheaf of rings that the modules of
  a ringed space live over is the one of the associated ringed site.
* `AlgebraicGeometry.RingedSpace.exists_isKFlat_quasiIso`: every complex of `𝒪_X`-modules
  receives a quasi-isomorphism from a K-flat complex.

## Implementation notes

No comparison functor is needed and no isomorphism of categories is invoked.
`structureSheafRing X` and
`AlgebraicGeometry.RingedSite.ringSheaf (ringedSite X)` are the same term — both are
`X.sheaf` composed with `forget₂ CommRingCat RingCat` and sheafified — the instance argument
recording that this composition is again a sheaf being a proposition, so the two spellings are
equal by `rfl` and the categories of modules are literally the same category. In particular
`Stacks.SheafOfModules.IsKFlat X.sheaf` is a predicate on
`CochainComplex (SheafOfModules (structureSheafRing X)) ℤ` on the nose.

`ringedSite` is an abbreviation rather than a definition, so that instance search sees through
its structure projections: the standing hypotheses below are stated at `X.sheaf` and the
ringed-site statement consumes them at `(ringedSite X).O`, which is the same sheaf but only
after a projection is reduced.

The instance arguments are those of the ringed-site statement, read at the site of open sets:
sheafification of abelian groups, and additivity of the tensor product of `𝒪_X`-modules in each
variable together with the countable direct sums forming the total complexes. They are the
standing hypotheses of the whole K-flatness development and are not discharged here.

As on a ringed site, the conclusion is K-flatness together with the quasi-isomorphism and not
the termwise flatness and termwise surjectivity that [Stacks, Tag 06YF] also asserts, so no tag
is placed.

## References

* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

universe u

/-- A ringed space, read as a ringed site: the underlying category is the poset of open sets,
the topology is the open-cover topology, and the structure sheaf is unchanged. -/
public abbrev ringedSite (X : RingedSpace.{u, u}) :
    AlgebraicGeometry.RingedSite.{u, u, u} where
  C := Opens X.carrier
  J := Opens.grothendieckTopology X.carrier
  O := X.sheaf

/-- The sheaf of rings that the modules of a ringed space live over is the structure sheaf of
the associated ringed site with commutativity forgotten. -/
public theorem ringSheaf_ringedSite (X : RingedSpace.{u, u}) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O) =
      structureSheafRing X :=
  rfl

variable (X : RingedSpace.{u, u})
  [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)]

/-- Every cochain complex of `𝒪_X`-modules on a ringed space receives a quasi-isomorphism from
a K-flat complex: a ringed space is a ringed site, and the resolution is the one built there. -/
public theorem exists_isKFlat_quasiIso
    (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
      (s : K ⟶ G), Stacks.SheafOfModules.IsKFlat X.sheaf K ∧ QuasiIso s :=
  Stacks.SheafOfModules.exists_isKFlat_quasiIso (ringedSite X) G

end AlgebraicGeometry.RingedSpace

end
