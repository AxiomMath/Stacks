module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineConstantUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantModuleSheafSections

/-!
# The constant sheaf of modules on an integral normal scheme is a direct image from a dense open

Let `X` be an integral normal scheme, `h : U ⟶ X` an open immersion with `U` nonempty, `Λ` a ring
and `M` a `Λ`-module. Then `M_X ≅ h_* M_U` as sheaves of `Λ`-modules on `X_ét`, the module form
of [Stacks, Tag 09Z5] (2) (its abelian form is
`Stacks.EtaleCohomology.Purity.isIso_constantSheafDirectImageMap_opensι`). On sections over an
étale `V ⟶ X`, read as locally constant maps
(`AlgebraicGeometry.smallEtaleConstantSheafIsoLocallyConstantMapsModule`),
the comparison is restriction along the open immersion `V ×_X U ⟶ V`, whose image is dense; as
every point of `V` has an irreducible open neighbourhood, restriction of locally constant maps to
a dense open is bijective.

## Main definitions

* `Stacks.EtaleCohomology.locallyConstantMapsModuleDirectImageMap`: pullback of locally constant
  maps along the projections `V ×_X Y ⟶ V`.
* `Stacks.EtaleCohomology.constantModuleSheafOpenDirectImageIso`: `M_X ≅ h_* M_U`.

## Main results

* `Stacks.EtaleCohomology.isIso_locallyConstantMapsModuleDirectImageMap_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 09Z5](https://stacks.math.columbia.edu/tag/09Z5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (h : Y ⟶ X) (M : ModuleCat.{u + 1} Λ)

/-- Pullback of locally constant `M`-valued maps along the projections `V ×_X Y ⟶ V`, as a
morphism of sheaves of `Λ`-modules on `X_ét` from the locally constant maps on `X` to the direct
image of the locally constant maps on `Y`. -/
def locallyConstantMapsModuleDirectImageMap :
    smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} Λ X M ⟶
      (etaleModuleDirectImage.{u, 0} Λ h).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} Λ Y M) :=
  ⟨Functor.whiskerRight (NatTrans.op (smallEtaleBaseChangeProjection h))
    (locallyConstantMapsModule.{u, u + 1} Λ M)⟩

/-- **Restriction of locally constant maps along a dense open immersion into an integral normal
scheme is bijective on étale sections.** -/
theorem isIso_locallyConstantMapsModuleDirectImageMap_of_isOpenImmersion [IsIntegral X]
    [IsNormal X] [IsOpenImmersion h] [Nonempty Y] :
    IsIso (locallyConstantMapsModuleDirectImageMap Λ h M) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  rintro ⟨V⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  have hV : Etale V.hom := V.prop
  have hVo : IsOpenMap V.hom.base := by
    have h' := Etale.iff_flat_and_formallyUnramified.mp hV
    have : Flat V.hom := h'.1
    have : LocallyOfFinitePresentation V.hom := h'.2.2
    have : UniversallyOpen V.hom := universallyOpen_of_flat_of_locallyOfFinitePresentation V.hom
    exact V.hom.isOpenMap
  have hdense : DenseRange (pullback.fst V.hom h).base := by
    show Dense (Set.range (pullback.fst V.hom h).base)
    rw [Scheme.Pullback.range_fst]
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact (h.isOpenEmbedding.isOpen_range.dense ⟨_, y, rfl⟩).preimage hVo
  exact Purity.bijective_locallyConstant_comap_of_denseRange (M := M)
    (pullback.fst V.hom h).base.hom (pullback.fst V.hom h).isOpenEmbedding hdense
    (Purity.exists_isPreirreducible_open_of_etale (X := X) V.hom)

/-- **[Stacks, Tag 09Z5] (2) for sheaves of modules.** On an integral normal scheme `X` the
constant sheaf `M_X` is the direct image of the constant sheaf `M_U` along an open immersion
`h : U ⟶ X` with `U` nonempty. -/
def constantModuleSheafOpenDirectImageIso [IsIntegral X] [IsNormal X] [IsOpenImmersion h]
    [Nonempty Y] :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ≅
      (etaleModuleDirectImage.{u, 0} Λ h).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  haveI := isIso_locallyConstantMapsModuleDirectImageMap_of_isOpenImmersion Λ h M
  smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, 0} Λ X M ≪≫
    asIso (locallyConstantMapsModuleDirectImageMap Λ h M) ≪≫
    (etaleModuleDirectImage.{u, 0} Λ h).mapIso
      (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, 0} Λ Y M).symm

end Stacks.EtaleCohomology

end
