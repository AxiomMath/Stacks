module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingComplexUniqueness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeBiduality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Picard.ZariskiSiteFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalShiftOfInvertible

/-!
# Two dualizing complexes on a locally Noetherian scheme are locally shifts of each other

Let `X` be a locally Noetherian scheme and `K`, `K'` dualizing complexes on `X`
([Stacks, Tag 0A87]). Then every point of `X` has an open neighbourhood `V` on which `K'|_V` is
isomorphic to a shift `K|_V[n]`.

By the proof of [Stacks, Tag 0ATP] the object `R𝓗om(K', K)` of `D(𝒪_X)` is invertible, and by
biduality ([Stacks, Tag 0A89]) `K' ≅ R𝓗om(R𝓗om(K', K), K)`. An invertible object on the locally
ringed site of opens of `X` is locally `𝒪` placed in one degree (clause (3) of
[Stacks, Tag 0FPY]), so on a neighbourhood `V` of the point
`K'|_V ≅ R𝓗om(𝒪_V[-n], K|_V) ≅ K|_V[n]`.

## Main results

* `Stacks.Duality.exists_mem_restrictDer_iso_shift_of_isDualizingComplex`: the statement on the
  slice site of opens over `V`.
* `Stacks.Duality.exists_mem_derivedPullback_iso_shift_of_isDualizingComplex`: the statement
  for the derived pullback along the open immersion `V ⟶ X`.

## Implementation notes

The derived categories are those at `CategoryTheory.HasDerivedCategory.standard`, named
explicitly: the dualizing complexes of [Stacks, Tag 0A87] and the derived internal Hom of the
inputs above are used there.

## References

* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Duality

variable {T : Scheme.{u}} [IsLocallyNoetherian T]

/-- **Two dualizing complexes on a locally Noetherian scheme are, near every point, shifts of
each other**, on the slice site of opens: for dualizing complexes `K`, `K'` on `T` and a point
`x`, there are an open `V ∋ x` and an integer `n` with `K'|_V ≅ K|_V[n]`, restriction being
`RingedSite.InvertibleDerived.restrictDer` to the slice site over `V`. -/
theorem exists_mem_restrictDer_iso_shift_of_isDualizingComplex
    (K K' : @DerivedCategory T.Modules _ _ (HasDerivedCategory.standard _))
    (hK : @IsDualizingComplex T _ (HasDerivedCategory.standard _) K)
    (hK' : @IsDualizingComplex T _ (HasDerivedCategory.standard _) K') (x : T) :
    ∃ V : T.Opens, x ∈ V ∧ ∃ n : ℤ,
      Nonempty ((RingedSite.InvertibleDerived.restrictDer
          (Stacks.SheafOfModules.ringedSite T.sheaf) V).obj K' ≅
        ((RingedSite.InvertibleDerived.restrictDer
          (Stacks.SheafOfModules.ringedSite T.sheaf) V).obj K)⟦n⟧) := by
  let := HasDerivedCategory.standard T.Modules
  let Y := Stacks.SheafOfModules.ringedSite T.sheaf
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  let := HasDerivedCategory.standard (RingedSite.Modules Y)
  have hY : RingedSite.IsLocallyRinged Y :=
    Stacks.Picard.ZariskiSite.schemeRingedSite_isLocallyRinged T
  have hinv := isInvertible_derivedSheafHom_of_isDualizingComplex K' K hK' hK
  let DT := RingedSite.derivedTensorMonoidal Y
  let DM := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
  let Tn := Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct.{u, u + 1}
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y)
  let μ : ∀ A B, @MonoidalCategoryStruct.tensorObj _ _ DM.toMonoidalCategoryStruct A B ≅
      @MonoidalCategoryStruct.tensorObj _ _ DT.toMonoidalCategoryStruct A B := fun A B =>
    ((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso Y.O Tn).app A).app B
  let ε : @MonoidalCategoryStruct.tensorUnit _ _ DM.toMonoidalCategoryStruct ≅
      @MonoidalCategoryStruct.tensorUnit _ _ DT.toMonoidalCategoryStruct :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.O
  have hR : RingedSite.InvertibleDerived.IsInvertibleObject Y
      (((RingedSite.derivedSheafHomBifunctor Y).obj (op K')).obj K) :=
    @isInvertible_of_tensorComparison_of_braided _ _ DT _ _ DM
      (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric Y.O).toBraidedCategory
      (𝟭 _) (fun A B => (μ A B).symm) ε.symm _ hinv
  have hbid := isIso_derivedBiduality_of_isDualizingComplex K K' hK
    (isCoherent_homology_of_isDualizingComplex hK')
  obtain ⟨S, hS, hSf⟩ :=
    RingedSite.InvertibleDerived.exists_covering_restrictDer_iso_shift_of_biduality Y hY K K' hR
      (asIso (RingedSite.derivedBiduality Y K K')) ⊤
  obtain ⟨W, f, hf, hxW⟩ := hS x (Set.mem_univ x)
  obtain ⟨V, g, f', hf', -⟩ := hf
  exact ⟨V, leOfHom g hxW, hSf f' hf'⟩

/-- **Two dualizing complexes on a locally Noetherian scheme are, near every point, shifts of
each other**: every point `x` has an open neighbourhood `V` and an integer `n` with
`L(V ⟶ X)^* K' ≅ (L(V ⟶ X)^* K)[n]`, for every morphism equal to the inclusion of `V`. -/
theorem exists_mem_derivedPullback_iso_shift_of_isDualizingComplex
    (K K' : @DerivedCategory T.Modules _ _ (HasDerivedCategory.standard _))
    (hK : @IsDualizingComplex T _ (HasDerivedCategory.standard _) K)
    (hK' : @IsDualizingComplex T _ (HasDerivedCategory.standard _) K') (x : T) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    ∃ V : T.Opens, x ∈ V ∧ ∃ n : ℤ, ∀ j : V.toScheme ⟶ T, j = V.ι →
      letI := HasDerivedCategory.standard
        (SheafOfModules.{u} (structureSheafRing V.toScheme.toRingedSpace))
      Nonempty ((derivedPullback j.toLRSHom.toShHom).obj K' ≅
        ((derivedPullback j.toLRSHom.toShHom).obj K)⟦n⟧) := by
  let := HasDerivedCategory.standard T.Modules
  obtain ⟨V, hxV, n, ⟨e⟩⟩ := exists_mem_restrictDer_iso_shift_of_isDualizingComplex K K' hK hK' x
  refine ⟨V, hxV, n, ?_⟩
  rintro _ rfl
  let := HasDerivedCategory.standard V.toScheme.Modules
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing V.toScheme.toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.SheafOfModules.ringedSite T.sheaf).O).over V))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (T.ringCatSheaf.over V))
  let E := ((Scheme.Modules.overEquiv V).functor).mapDerivedCategory
  let ι : ∀ L : DerivedCategory T.Modules, (derivedPullback V.ι.toLRSHom.toShHom).obj L ≅
      E.obj ((RingedSite.InvertibleDerived.restrictDer
        (Stacks.SheafOfModules.ringedSite T.sheaf) V).obj L) := fun L =>
    (Scheme.Modules.derivedPullbackIsoMapDerivedCategoryRestrict V.ι).app L ≪≫
      ((Stacks.SheafOfModules.derivedOverFunctorEquiv V).app L).symm
  exact ⟨ι K' ≪≫ E.mapIso e ≪≫ (E.commShiftIso n).app _ ≪≫ (shiftFunctor _ n).mapIso (ι K).symm⟩

end Stacks.Duality
