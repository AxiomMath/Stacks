module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryFullyFaithfulOfResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightResolvingSubcategoryPlus
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleSpacesEtaleDerivedComparison

/-!
# `Φ_X` is fully faithful on the unbounded derived category

Let `X` be an algebraic space over a scheme `S`, and let
`Φ_X = AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor` be the comparison
`D(𝒪_X) ⥤ D(𝒪_{X, spaces-étale})`. It is the derived functor of the exact transport `ι` of
Stacks 03G1 from modules on the small étale site of `X` with sections in `Type u` to modules on
the spaces-étale site with sections in `Type (u + 1)`. This file proves that `Φ_X` is fully
faithful on the whole unbounded derived category. It also describes its essential image: an
object lies in it as soon as its cohomology sheaves have `u`-small sections, and when those
sheaves are quasi-coherent the preimage can be taken with quasi-coherent cohomology.

The input is the sheaf-site Löwenheim–Skolem statement (Stacks 0GYY for the spaces-étale
topology, `AlgebraicGeometry.Space.spacesEtaleSmallQuasiIsoSubcomplex`). Every complex on the
spaces-étale site whose cohomology sheaves have `u`-small sections receives a quasi-isomorphism
from a complex with `u`-small terms. By
`AlgebraicGeometry.Space.toSpacesEtaleModules_full_faithful_essImage` such a complex is
termwise, and hence as a complex, in the image of `ι`. The calculus of fractions argument of
`CategoryTheory.Functor.mapDerivedCategory_full_of_resolutions` then applies.

## Main results

* `AlgebraicGeometry.Space.hasResolutionsOfEssImageHomology_toSpacesEtaleRingedToposModules`:
  the resolution property of `ι`.
* `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor_full` and
  `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor_faithful`: `Φ_X` is full and
  faithful.
* `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor_map_bijective`: the bijectivity
  clause of `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`.
* `AlgebraicGeometry.Space.exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso` and
  `AlgebraicGeometry.Space.exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso_of_quasicoherent`:
  the essential image.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `ι`, read over the spaces-étale ringed topos, is full. -/
theorem toSpacesEtaleRingedToposModules_full (X : AlgebraicSpaces B S hS) :
    (toSpacesEtaleRingedToposModules B S hS X).Full :=
  (toSpacesEtaleModules_full_faithful_essImage B S hS X).1

/-- `ι`, read over the spaces-étale ringed topos, is faithful. -/
theorem toSpacesEtaleRingedToposModules_faithful (X : AlgebraicSpaces B S hS) :
    (toSpacesEtaleRingedToposModules B S hS X).Faithful :=
  (toSpacesEtaleModules_full_faithful_essImage B S hS X).2.1

private instance (X : AlgebraicSpaces B S hS) :
    HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2) := HasDerivedCategory.standard _

private instance (X : AlgebraicSpaces B S hS) :
    HasDerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O)) :=
  HasDerivedCategory.standard _

private instance (X : AlgebraicSpaces B S hS) :
    PreservesFiniteLimits (toSpacesEtaleModules B S hS X) :=
  preservesFiniteLimits_toSpacesEtaleModules B S hS X

private instance (X : AlgebraicSpaces B S hS) :
    PreservesFiniteColimits (toSpacesEtaleModules B S hS X) :=
  preservesFiniteColimits_toSpacesEtaleModules B S hS X

private instance (X : AlgebraicSpaces B S hS) :
    (toSpacesEtaleRingedToposModules B S hS X).Full :=
  toSpacesEtaleRingedToposModules_full B S hS X

private instance (X : AlgebraicSpaces B S hS) :
    (toSpacesEtaleRingedToposModules B S hS X).Faithful :=
  toSpacesEtaleRingedToposModules_faithful B S hS X

/-- **The resolution property of `ι`**: a complex of modules on the spaces-étale site of `X`
whose cohomology sheaves lie in the essential image of `ι` receives a quasi-isomorphism from the
image under `ι` of a complex on the small étale site. This is the Löwenheim–Skolem statement
`AlgebraicGeometry.Space.spacesEtaleSmallQuasiIsoSubcomplex` together with the description of the
essential image of `ι` by `u`-small sections. -/
theorem hasResolutionsOfEssImageHomology_toSpacesEtaleRingedToposModules
    (X : AlgebraicSpaces B S hS) :
    haveI := preservesFiniteLimits_toSpacesEtaleModules B S hS X
    haveI := preservesFiniteColimits_toSpacesEtaleModules B S hS X
    (toSpacesEtaleRingedToposModules B S hS X).HasResolutionsOfEssImageHomology := by
  intro M hM
  obtain ⟨M', i, hi, hM'⟩ := spacesEtaleSmallQuasiIsoSubcomplex B S hS X M
    (fun n ↦ ((toSpacesEtaleModules_full_faithful_essImage B S hS X).2.2 _).1 (hM n))
  obtain ⟨N, ⟨e⟩⟩ := CochainComplex.exists_iso_mapHomologicalComplex_of_forall_essImage
    (toSpacesEtaleRingedToposModules B S hS X) M' (fun n ↦
      ((toSpacesEtaleModules_full_faithful_essImage B S hS X).2.2 _).2 (hM' n))
  exact ⟨N, e.hom ≫ i, inferInstance⟩

/-- **`Φ_X` is full** on the unbounded derived category. -/
theorem smallEtaleSpacesEtaleDerivedFunctor_full (X : AlgebraicSpaces B S hS) :
    (smallEtaleSpacesEtaleDerivedFunctor B S hS X).Full := by
  exact Functor.mapDerivedCategory_full_of_resolutions
    (hasResolutionsOfEssImageHomology_toSpacesEtaleRingedToposModules B S hS X)

/-- **`Φ_X` is faithful** on the unbounded derived category. -/
theorem smallEtaleSpacesEtaleDerivedFunctor_faithful (X : AlgebraicSpaces B S hS) :
    (smallEtaleSpacesEtaleDerivedFunctor B S hS X).Faithful := by
  exact Functor.mapDerivedCategory_faithful_of_resolutions
    (hasResolutionsOfEssImageHomology_toSpacesEtaleRingedToposModules B S hS X)

/-- **`Φ_X` is bijective on morphisms** between complexes with quasi-coherent cohomology: the
first clause of `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`. It holds for
all complexes (`AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor_full` and
`AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor_faithful`); the quasi-coherence
hypotheses are not used. -/
theorem smallEtaleSpacesEtaleDerivedFunctor_map_bijective (X : AlgebraicSpaces B S hS)
    (K E : derivedModules B S hS X) (_ : IsSmallEtaleQuasicoherentComplex B S hS X K)
    (_ : IsSmallEtaleQuasicoherentComplex B S hS X E) :
    Function.Bijective (fun g : K ⟶ E => (smallEtaleSpacesEtaleDerivedFunctor B S hS X).map g) :=
  have := smallEtaleSpacesEtaleDerivedFunctor_full B S hS X
  have := smallEtaleSpacesEtaleDerivedFunctor_faithful B S hS X
  ⟨(smallEtaleSpacesEtaleDerivedFunctor B S hS X).map_injective,
    (smallEtaleSpacesEtaleDerivedFunctor B S hS X).map_surjective⟩

/-- **The essential image of `Φ_X`** contains every complex on the spaces-étale site of `X`
whose cohomology sheaves have `u`-small sections. -/
theorem exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso (X : AlgebraicSpaces B S hS)
    (L : spacesEtaleDerivedModules B S hS X)
    (hL : ∀ (n : ℤ) (V : (SpacesEtale B S hS X)ᵒᵖ),
      Small.{u} (((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _)
        n).obj L).val.obj V)) :
    ∃ K : derivedModules B S hS X,
      Nonempty ((smallEtaleSpacesEtaleDerivedFunctor B S hS X).obj K ≅ L) := by
  obtain ⟨N, ⟨e⟩⟩ := Functor.exists_mapDerivedCategory_obj_iso_of_resolutions
    (hasResolutionsOfEssImageHomology_toSpacesEtaleRingedToposModules B S hS X) L
    (fun n ↦ ((toSpacesEtaleModules_full_faithful_essImage B S hS X).2.2 _).2 (hL n))
  exact ⟨DerivedCategory.Q.obj N, ⟨e⟩⟩

/-- **The essential image of `Φ_X` on quasi-coherent complexes**: a complex on the spaces-étale
site of `X` with quasi-coherent cohomology sheaves having `u`-small sections is `Φ_X(K)` for a
complex `K` on the small étale site with quasi-coherent cohomology sheaves. -/
theorem exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso_of_quasicoherent
    (X : AlgebraicSpaces B S hS) (L : spacesEtaleDerivedModules B S hS X)
    (hQ : IsSpacesEtaleQuasicoherentComplex B S hS X L)
    (hL : ∀ (n : ℤ) (V : (SpacesEtale B S hS X)ᵒᵖ),
      Small.{u} (((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _)
        n).obj L).val.obj V)) :
    ∃ K : derivedModules B S hS X, IsSmallEtaleQuasicoherentComplex B S hS X K ∧
      Nonempty ((smallEtaleSpacesEtaleDerivedFunctor B S hS X).obj K ≅ L) := by
  obtain ⟨K, ⟨e⟩⟩ := exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso B S hS X L hL
  refine ⟨K, ?_, ⟨e⟩⟩
  intro n
  have h := hQ n
  have e' := ((toSpacesEtaleRingedToposModules B S hS X).mapDerivedCategoryHomologyIso n).app K
  have : ((toSpacesEtaleModules B S hS X).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj
        K)).IsQuasicoherentOnSite :=
    (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      (((DerivedCategory.homologyFunctor _ n).mapIso e).symm ≪≫ e') h
  exact isQuasicoherentOnSite_of_toSpacesEtaleModules B S hS X _

end AlgebraicGeometry.Space

end
