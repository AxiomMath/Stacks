module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatSliceExtension
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.SequentialColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionByExtensionsByZero

/-!
# Every complex of modules on a ringed site has a K-flat resolution

Let `(C, 𝒪)` be a ringed site. Every cochain complex `G` of `𝒪`-modules receives a
quasi-isomorphism from a K-flat complex: the colimit of a ladder of bounded above complexes,
termwise direct sums of extensions by zero of the structure sheaves of the slice sites,
resolving the upper truncations of `G`.

## Main results

* `Stacks.SheafOfModules.isFlat_of_iso`: flatness of a sheaf of modules is invariant under
  isomorphism.
* `Stacks.SheafOfModules.isFlat_of_isSumOfExtensionByZeroStructureSheaves`: a direct sum of
  extensions by zero of the structure sheaves of slice sites is flat.
* `Stacks.SheafOfModules.isKFlat_resolutionByDirectSumsExtensionsByZero_system`: every rung of a
  resolution by direct sums of extensions by zero is K-flat.
* `Stacks.SheafOfModules.exists_isKFlat_quasiIso`: every cochain complex of modules receives a
  quasi-isomorphism from a K-flat complex.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YE](https://stacks.math.columbia.edu/tag/06YE)
* [Stacks Project, Tag 03EV](https://stacks.math.columbia.edu/tag/03EV)
* [Stacks Project, Tag 05NG](https://stacks.math.columbia.edu/tag/05NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})

/-- Flatness of a sheaf of modules is invariant under isomorphism. -/
public theorem isFlat_of_iso {R : Sheaf X.J CommRingCat.{u}}
    {F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)} (e : F ≅ G)
    (h : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) F) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) G :=
  (exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.mapIso e) h

/-- A direct sum of extensions by zero of the structure sheaves of slice sites is flat. -/
public theorem isFlat_of_isSumOfExtensionByZeroStructureSheaves
    {M : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hM : IsSumOfExtensionByZeroStructureSheaves X M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) M := by
  obtain ⟨ι, U, ⟨e⟩⟩ := hM
  have hsum : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      (∐ fun i : ι =>
        (_root_.SheafOfModules.pullback.{u} (F := Over.forget (U i))
            (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over (U i)))).obj
          (_root_.SheafOfModules.unit
            (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over (U i)))) :=
    FlatColimits.isFlat_coproduct (O := X.O) _
      (fun i => Stacks.Sites.OverModules.sheafExtensionUnit_isFlat X.J X.O (U i))
  exact isFlat_of_iso X e hsum

section Resolution

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]

/-- Every rung of a resolution by direct sums of extensions by zero of the structure sheaves of
slice sites is K-flat. -/
public theorem isKFlat_resolutionByDirectSumsExtensionsByZero_system
    {G : CochainComplex
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ}
    (L : ResolutionByDirectSumsExtensionsByZero X G) (n : ℕ) :
    IsKFlat.{u, u, u} X.O (L.system.obj n) :=
  kFlat_of_boundedAbove_of_flat X.O (L.system.obj n) (L.boundedAbove n)
    (fun i => isFlat_of_isSumOfExtensionByZeroStructureSheaves X (L.term_isSum n i))

/-- Every cochain complex of modules on a ringed site receives a quasi-isomorphism from a K-flat
complex. -/
public theorem exists_isKFlat_quasiIso
    (G : CochainComplex
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) :
    ∃ (K : CochainComplex
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) (s : K ⟶ G),
      IsKFlat.{u, u, u} X.O K ∧ QuasiIso s := by
  obtain ⟨L⟩ := exists_resolutionByDirectSumsExtensionsByZero X G
  exact ⟨colimit L.system, L.colimitComparison,
    kFlat_colimit X.O L.system (isKFlat_resolutionByDirectSumsExtensionsByZero_system X L),
    L.colimit_quasiIso⟩

end Resolution

end Stacks.SheafOfModules

end
