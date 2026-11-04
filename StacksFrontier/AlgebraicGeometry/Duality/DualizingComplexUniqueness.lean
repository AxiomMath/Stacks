module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSlice
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIsIso
import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of dualizing complexes on a locally Noetherian scheme

**[Stacks, Tag 0ATP].** Let `X` be a locally Noetherian scheme. If `K` and `K'` are dualizing
complexes on `X` ([Stacks, Tag 0A87]), then `K'` is isomorphic to `K ⊗^𝐋_{𝒪_X} L` for some
invertible object `L` of `D(𝒪_X)`.

The proof is the source's: `L = R𝓗om_{𝒪_X}(K, K')` is invertible and the evaluation
`L ⊗^𝐋 K ⟶ K'` is an isomorphism, because both hold affine locally. Three inputs make that
sentence a proof.

* *The affine case on the slice site.* Over an affine open `V` the restrictions of `K` and `K'`
  are the complexes associated to dualizing complexes over `Γ(X, V)`, and there the two
  conclusions are the affine case [Stacks, Tag 0A7F]:
  `Stacks.Duality.isIso_derivedSheafHomCounit_restrictD_of_isDualizingComplex`.
* *Restriction commutes with the derived internal hom through the canonical map*, so that the
  restriction of `L` and of the evaluation morphism are the internal hom and the evaluation
  morphism of the restrictions:
  `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTransposeIso` and
  `Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_derivedSheafHomCounit_iff`.
* *Both conclusions are local*: `Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor`
  for the morphism and
  `Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction` for the
  object.

## Main results

* `Stacks.Duality.exists_isInvertible_tensor_iso_of_isDualizingComplex`: **[Stacks, Tag 0ATP]**.
* `Stacks.Duality.isIso_derivedSheafHomCounit_of_isDualizingComplex` and
  `Stacks.Duality.isInvertible_derivedSheafHom_of_isDualizingComplex`: the two halves, for
  `L = R𝓗om_{𝒪_X}(K, K')` itself.

## Implementation notes

The monoidal structure on `D(𝒪_X)` is that of [Stacks, Tag 0FPT],
`AlgebraicGeometry.Scheme.Modules.derivedMonoidal`, at the model `HasDerivedCategory.standard`,
the model the derived internal hom and the tensor–internal-hom bijection of [Stacks, Tag 08J8] are
stated at. This file does not import
`StacksFrontier/AlgebraicGeometry/Duality/GlobalDualizingUniqueness.lean`: with the pullback
comparisons in scope, instance search no longer finds the abelian structure on the modules of a
ringed space, which that file's ringed-space statements rely on.

## References

* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.Duality

attribute [local instance 10000] HasDerivedCategory.standard

section Scheme

variable {X : Scheme.{u}}

/-- Sheafification on the site of opens of a scheme, supplied directly. -/
local instance hasSheafifyOpensScheme' (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

/-- Sheafification on a slice of the site of opens of a scheme, supplied directly. -/
local instance hasSheafifyOverOpens' (X : Scheme.{u}) (U : X.Opens) :
    HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} := inferInstance

/-- The affine opens of a scheme cover the top of its ringed site. -/
private theorem coversTop_affineOpens (X : Scheme.{u}) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).J.CoversTop
      (fun V : X.affineOpens => (V : X.Opens)) :=
  (Opens.coversTop_iff _ _).2 (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X))

/-- **The evaluation morphism `R𝓗om(K, K') ⊗^𝐋 K ⟶ K'` of [Stacks, Tag 08J8] is an
isomorphism** for dualizing complexes `K`, `K'` on a locally Noetherian scheme: over each affine
open it restricts to the evaluation morphism of the restrictions
(`Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_derivedSheafHomCounit_iff`), which is an
isomorphism by the affine case
(`Stacks.Duality.isIso_derivedSheafHomCounit_restrictD_of_isDualizingComplex`), and being an
isomorphism is local (`Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor`). -/
theorem isIso_derivedSheafHomCounit_of_isDualizingComplex [IsLocallyNoetherian X]
    (K K' : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (hK' : IsDualizingComplex K') :
    IsIso (RingedSite.derivedSheafHomCounit (Stacks.SheafOfModules.ringedSite X.sheaf) K K') := by
  refine Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor
    (coversTop_affineOpens X) _ fun V => ?_
  exact (Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_derivedSheafHomCounit_iff
    (Stacks.SheafOfModules.ringedSite X.sheaf) (V : X.Opens) K K').2
      (isIso_derivedSheafHomCounit_restrictD_of_isDualizingComplex (V : X.Opens) V.2 K K' hK
        hK').1

/-- **`R𝓗om(K, K')` is an invertible object of `D(𝒪_X)`** for dualizing complexes `K`, `K'` on a
locally Noetherian scheme, at the re-seated monoidal structure of the ringed site of `X`: over each
affine open its restriction is `R𝓗om(K|_V, K'|_V)`
(`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTransposeIso`), which is
invertible by the affine case
(`Stacks.Duality.isIso_derivedSheafHomCounit_restrictD_of_isDualizingComplex`), and invertibility
is local (`Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction`). -/
theorem isInvertible_derivedSheafHom_of_isDualizingComplex [IsLocallyNoetherian X]
    (K K' : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (hK' : IsDualizingComplex K') :
    letI := RingedSite.derivedTensorMonoidal (Stacks.SheafOfModules.ringedSite X.sheaf)
    MonoidalCategory.IsInvertible
      (((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
        (op K)).obj K') := by
  refine Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction
    (Stacks.SheafOfModules.ringedSite X.sheaf) (coversTop_affineOpens X) _ fun V => ?_
  exact @MonoidalCategory.isInvertible_of_iso _ _
    (RingedSite.derivedTensorMonoidal
      ((Stacks.SheafOfModules.ringedSite X.sheaf).over (V : X.Opens))) _ _
    (Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTransposeIso
      (Stacks.SheafOfModules.ringedSite X.sheaf) (V : X.Opens) K K').symm
    (isIso_derivedSheafHomCounit_restrictD_of_isDualizingComplex (V : X.Opens) V.2 K K' hK
      hK').2

/-- **[Stacks, Tag 0ATP].** Let `X` be a locally Noetherian scheme and let `K`, `K'` be dualizing
complexes on `X` ([Stacks, Tag 0A87]). Then `K'` is isomorphic to `K ⊗^𝐋_{𝒪_X} L` for some
invertible object `L` of `D(𝒪_X)` ([Stacks, Tag 0FFN]), the monoidal structure being that of
[Stacks, Tag 0FPT].

The proof is the source's, with `L = R𝓗om_{𝒪_X}(K, K')`: `L` is invertible
(`Stacks.Duality.isInvertible_derivedSheafHom_of_isDualizingComplex`) and the evaluation
`L ⊗^𝐋 K ⟶ K'` is an isomorphism
(`Stacks.Duality.isIso_derivedSheafHomCounit_of_isDualizingComplex`), both because they hold
affine locally. -/
@[stacks 0ATP]
theorem exists_isInvertible_tensor_iso_of_isDualizingComplex [IsLocallyNoetherian X]
    (K K' : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (hK' : IsDualizingComplex K') :
    letI := Scheme.Modules.derivedMonoidal X
    ∃ L : DerivedCategory X.Modules,
      MonoidalCategory.IsInvertible L ∧ Nonempty (K' ≅ K ⊗ L) := by
  have hev := isIso_derivedSheafHomCounit_of_isDualizingComplex K K' hK hK'
  have hinv := isInvertible_derivedSheafHom_of_isDualizingComplex K K' hK hK'
  let := Scheme.Modules.derivedMonoidal X
  let e := Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.sheaf
    (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct.{u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (Stacks.SheafOfModules.ringedSite X.sheaf)))
  refine ⟨((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
      (op K)).obj K', ?_, ⟨?_⟩⟩
  · exact @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _
      (RingedSite.derivedTensorMonoidal (Stacks.SheafOfModules.ringedSite X.sheaf)) _ _
      (Scheme.Modules.derivedMonoidal X) (Scheme.Modules.derivedSymmetric X).toBraidedCategory
      (𝟭 _)
      (fun A B => ((e.app A).app B).symm)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf).symm _ hinv
  · exact (((e.app K).app _) ≪≫
      @BraidedCategory.braiding _ _
        (RingedSite.derivedTensorMonoidal (Stacks.SheafOfModules.ringedSite X.sheaf))
        (RingedSite.derivedTensorSymmetric
          (Stacks.SheafOfModules.ringedSite X.sheaf)).toBraidedCategory K _ ≪≫
      @asIso _ _ _ _ (RingedSite.derivedSheafHomCounit (Stacks.SheafOfModules.ringedSite X.sheaf)
        K K') hev).symm

end Scheme

end Stacks.Duality

end
