module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ConeHomologyLadder
public import StacksFrontier.Algebra.Homology.Embedding.MapExtend07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BasisAnnihilation07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Resolution07Q9

/-!
# [Stacks, Tag 07Q9] reduced to sections over a basis of opens

The conclusion of [Stacks, Tag 07Q9] is a statement about the cohomology *sheaves* on `X_Zar` of
the cone of the comparison map `Ru_{X/S, *}ℱ ⟶ f_*Ru_{X'/S, *}ℱ'`.  This file reduces it to a
statement about complexes of abelian groups: the sections over the opens of a basis of `X` of
the map `u_{X/S, *}J ⟶ u_{X/S, *}f_{cris, *}J'` of complexes of sheaves, for injective
resolutions `J` of `ℱ` and `J'` of `ℱ'` and any map `ψ : J ⟶ f_{cris, *}J'` lifting the unit
`ℱ ⟶ f_{cris, *}ℱ'`.

The three ingredients are all in the library: the comparison map is `Ru_{X/S, *}` of the derived
unit followed by an isomorphism (`...SmallSite.moduleComparison07Q9_eq`); on injective
resolutions that is the class of the map of complexes `u_{X/S, *}ψ`
(`...SmallSite.moduleCrisUnitArrowIsoExtend`); and the cohomology sheaves of the cone of a map of
complexes are killed by `q` as soon as the cohomology of its sections over the members of a basis
is (`...SmallSite.annihilation07Q9_of_isBasis_mappingCone`).

## Main result

* `annihilation07Q9_moduleComparison07Q9_of_isBasis` — the reduction.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  TopologicalSpace Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- **Sections over an open commute with extending a complex by zero**, as an isomorphism of
arrows in `D(Ab)` between the two orders of applying them to a map of complexes of sheaves. -/
def sectionsExtendArrowIso [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}] (W : S'.X.Opens)
    {K L : CochainComplex (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ L) :
    Arrow.mk (DerivedCategory.Q.map ((((sheafSections (opensTopology S')
        AddCommGrpCat.{u + 1}).obj (op W)).mapHomologicalComplex _).map
          (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))) ≅
      Arrow.mk (DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((((sheafSections (opensTopology S') AddCommGrpCat.{u + 1}).obj
          (op W)).mapHomologicalComplex _).map φ) ComplexShape.embeddingUpNat)) :=
  Arrow.isoMk (DerivedCategory.Q.mapIso (HomologicalComplex.mapExtendIso _ _ K))
    (DerivedCategory.Q.mapIso (HomologicalComplex.mapExtendIso _ _ L)) (by
      simp only [Arrow.mk_hom, Functor.mapIso_hom, ← Functor.map_comp]
      exact congrArg _ (HomologicalComplex.mapExtendIso_hom_naturality _ _ φ).symm)

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

/-- **[Stacks, Tag 07Q9] reduced to sections over a basis.**  If for some injective resolutions
`J` of `ℱ` and `J'` of `f_cris^*ℱ` and the lift `ψ : J ⟶ f_{cris, *}J'` of the unit
(`crisResolutionMap`), the sections over every member of a basis `ℬ` of the opens of `X` of
`u_{X/S, *}ψ` have mapping cone with cohomology killed by `q`, then the cone of the comparison
map of [Stacks, Tag 07Q9] has cohomology sheaves killed by `q`. -/
theorem annihilation07Q9_moduleComparison07Q9_of_isBasis (F : ModuleSheaf S') (q : ℕ)
    {ℬ : Set S'.X.Opens} (hℬ : Opens.IsBasis ℬ)
    (hloc : ∀ W ∈ ℬ, ChainConeAnnihilation q (sectionsChainMap S' W
      (crisResolutionMap S S' fS fX hf F (injectiveResolution _) (injectiveResolution _)))) :
    Annihilation07Q9 S' q (moduleComparison07Q9 S S' fS fX hf F) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  rw [moduleComparison07Q9_eq]
  refine Stacks.Triangulated.coneHomologyAnnihilation_comp_isIso _ q _
    ((derivedZariskiSquare S S' fS fX hf (crisZariskiSquare S S' fS fX hf)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)))) ?_
  set J := injectiveResolution ((toAbelianSheaf S').obj F)
  set J' := injectiveResolution ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))
  refine annihilation07Q9_of_isBasis_mappingCone S' q _ _
    (moduleCrisUnitArrowIsoExtend S S' fS fX hf F J J' (crisResolutionMap S S' fS fX hf F J J')
      (ι_f_zero_comp_crisResolutionMap_f_zero S S' fS fX hf F J J')) hℬ fun W hW j => ?_
  refine (Stacks.ConeLadder.coneHomologyKilled_Q_map_iff (q : ℤ) _).1
    (Stacks.ConeLadder.ConeHomologyKilled.of_arrowIso (sectionsExtendArrowIso S' W _)
      ((Stacks.ConeLadder.coneHomologyKilled_Q_map_iff (q : ℤ) _).2 (hloc W hW))) j

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
