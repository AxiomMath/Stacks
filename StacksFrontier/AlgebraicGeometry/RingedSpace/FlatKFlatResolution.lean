module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTermsSurjective
import StacksCore.Tactic.StacksAttribute

/-!
# K-flat resolutions with flat terms on a ringed space

A ringed space is a ringed site, so the resolution of [Stacks, Tag 06YS] built on a ringed site
in `StacksDraft.Ch21.Sec17.FlatKFlatResolution` is available for complexes of `𝒪_X`-modules on
a ringed space, with no transport of the statement in between. That specialisation is
[Stacks, Tag 06YF].

## Main results

* `AlgebraicGeometry.RingedSpace.exists_isKFlat_isFlat_quasiIso_epi`: [Stacks, Tag 06YF]. Every
  complex of `𝒪_X`-modules receives a termwise surjective quasi-isomorphism from a K-flat
  complex of flat `𝒪_X`-modules.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution` no comparison functor is
needed: `structureSheafRing X` and
`AlgebraicGeometry.RingedSite.ringSheaf (ringedSite X)` are the same term, and the structure
sheaf of `ringedSite X` is `X.sheaf` on the nose, so both the K-flatness predicate of
[Stacks, Tag 06Y9] and the flatness predicate of [Stacks, Tag 03ER] apply to the complexes
produced on the site with no translation.

The instance arguments are those of the ringed-site statement, read at the site of open sets;
they are the standing hypotheses of the whole K-flatness development and are not discharged
here.

## References

* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

universe u

variable (X : RingedSpace.{u, u})
  [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)]

/-- **Stacks 06YF.** Every cochain complex `G` of `𝒪_X`-modules on a ringed space receives a
termwise surjective quasi-isomorphism from a K-flat complex whose terms are flat `𝒪_X`-modules.

A ringed space is a ringed site, and this is the resolution built there
([Stacks, Tag 06YS]). -/
@[stacks 06YF]
public theorem exists_isKFlat_isFlat_quasiIso_epi
    (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
      (s : K ⟶ G),
      Stacks.SheafOfModules.IsKFlat X.sheaf K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i)) ∧
      QuasiIso s ∧ ∀ i : ℤ, Epi (s.f i) :=
  Stacks.SheafOfModules.exists_isKFlat_isFlat_quasiIso_epi (ringedSite X) G

end AlgebraicGeometry.RingedSpace

end
