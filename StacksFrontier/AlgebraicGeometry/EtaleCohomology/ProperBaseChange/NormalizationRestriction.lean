module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteSurjectiveCoverRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpen

/-!
# Restriction along an étale morphism through the normalization of the target in its source

Let `h : V ⟶ X` be an étale morphism from an affine scheme to a reduced separated scheme locally of
finite type over a field `k`. The normalization `Ȳ` of `X` in `V` factors `h` as an open immersion
`t : V ⟶ Ȳ` through every generic point of `Ȳ`, followed by a finite morphism `ν : Ȳ ⟶ X`. Since
`ν` is finite, restriction to a scalar extension on the cohomology of `h_* N = ν_* t_* N` is
restriction on the cohomology of `t_* N` on `Ȳ`. This is the step of the dévissage of Stacks 03SC
(7) which replaces a finite étale cover of a dense open of a curve by an open of another curve.

## Main results

* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_directImage_comp_iff` — for
  `h = t ≫ ν` with `ν` finite, surjectivity on `h_* N` is surjectivity on `t_* N`.
* `AlgebraicGeometry.exists_isOpenImmersion_isFinite_factorization_of_etale` — the factorization
  through the normalization of `X` in `V`.
* `AlgebraicGeometry.topologicalKrullDim_le_of_locallyQuasiFinite` — a locally quasi-finite
  morphism does not raise the Krull dimension, its fibres being discrete.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

/-- **Restriction on a direct image through a finite morphism.** For `h = t ≫ ν` with `ν` finite,
restriction to `X_{k'}` is surjective on the cohomology of `h_* N` exactly when restriction to
`Ȳ_{k'}` is surjective on the cohomology of `t_* N`. -/
theorem surjective_etaleCohomologyRestrictionMap_directImage_comp_iff (k k' : Type u) [Field k]
    [Field k'] [Algebra k k'] {X Y V : Scheme.{u}} (π : X ⟶ Spec (.of k)) (t : V ⟶ Y)
    (ν : Y ⟶ X) [IsFinite ν] (h : V ⟶ X) (hh : h = t ≫ ν)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (scalarExtension k k' (ν ≫ π)).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (N : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' π)
        ((etaleAbelianDirectImage.{u, 0} h).obj N) q) ↔
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
        (scalarExtensionFst k k' (ν ≫ π)) ((etaleAbelianDirectImage.{u, 0} t).obj N) q) := by
  let e := (etaleAbelianDirectImageCompIso'.{u, 0} t ν h hh).app N
  rw [← etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite.{u, w} ν _ _ _
    (isPullback_scalarExtension_closed k k' π ν)]
  exact ⟨surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, w} _ e.symm q,
    surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, w} _ e q⟩

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

/-- **The normalization of the target in the source of an étale morphism.** For `h : V ⟶ X` étale
with `V` affine and `X` reduced, separated and locally of finite type over a field `k`, there is a
factorization `h = t ≫ ν` with `t` an open immersion whose image contains every generic point of
the middle scheme `Ȳ`, which is reduced, and `ν` finite. -/
public theorem exists_isOpenImmersion_isFinite_factorization_of_etale (k : Type u) [Field k]
    {X V : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [IsReduced X] [IsNoetherian X] (h : V ⟶ X) [Etale h] [IsAffine V] :
    ∃ (Y : Scheme.{u}) (t : V ⟶ Y) (ν : Y ⟶ X), IsOpenImmersion t ∧ IsFinite ν ∧
      t ≫ ν = h ∧ genericPoints Y ⊆ Set.range t.base := by
  have : IsReduced V := AlgebraicGeometry.isReduced_of_smooth h
  have : IsSeparated h := IsSeparated.of_comp h π
  have : QuasiCompact h := quasiCompact_of_compactSpace h
  obtain ⟨ht, -, -⟩ := isOpenImmersion_toNormalization_and_isIntegralHom_fromNormalization h
  have hfin := isFinite_fromNormalization_of_locallyOfFiniteType_over_field k π (h ≫ π) h rfl
  refine ⟨h.normalization, h.toNormalization, h.fromNormalization, ht, hfin,
    h.toNormalization_fromNormalization, fun η hη => ?_⟩
  have : IsNoetherian h.normalization := by
    have : LocallyOfFiniteType h.fromNormalization := inferInstance
    have : IsLocallyNoetherian h.normalization :=
      LocallyOfFiniteType.isLocallyNoetherian h.fromNormalization
    have : CompactSpace h.normalization :=
      QuasiCompact.compactSpace_of_compactSpace h.fromNormalization
    exact ⟨⟩
  exact TopologicalSpace.NoetherianSpace.mem_of_mem_genericPoints_of_dense
    h.toNormalization.isOpenEmbedding.isOpen_range h.toNormalization.denseRange hη

/-- **A locally quasi-finite morphism does not raise the dimension.** Its fibres are discrete, so
it is injective on specializations. -/
public theorem topologicalKrullDim_le_of_locallyQuasiFinite {Y X : Scheme.{u}} (ν : Y ⟶ X)
    [LocallyQuasiFinite ν] : topologicalKrullDim Y ≤ topologicalKrullDim X :=
  Topology.topologicalKrullDim_le_of_continuous_of_specializes_injective ν.base
    ν.base.hom.continuous
    fun _ _ h he => ν.eq_of_specializes h he

end AlgebraicGeometry

end
