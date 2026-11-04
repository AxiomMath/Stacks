module

public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.FlatPushforwardOfKInjectives
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Sections with support on a closed subset of a pushforward from a disjoint open subset

Let `Z` be a closed subset of a ringed space `X` and let `j : (U, 𝒪_X|_U) ⟶ (X, 𝒪_X)` be the
inclusion of an open subset `U` disjoint from `Z`. Then the sheaf `H_Z(j_* 𝒢)` of sections of a
pushforward supported on `Z` vanishes: a section of `j_* 𝒢` over an open `W` supported on
`Z ∩ W` already vanishes on `W ∖ Z`, and `j⁻¹(W) = j⁻¹(W ∖ Z)` because `U ∩ Z = ∅`, so the
restriction map of `j_* 𝒢` from `W` to `W ∖ Z` is an isomorphism and the section is zero.

Since `j` is flat, `j_*` preserves K-injectivity, so a K-injective resolution of a complex of
`𝒪_U`-modules is carried to a complex computing both `Rj_*` and `R H_Z ∘ Rj_*`. The degreewise
vanishing therefore propagates to the unbounded derived category: `R H_Z(Rj_* K) = 0` for every
`K` in `D(𝒪_U)`.

## Main results

* `AlgebraicGeometry.isFlat_ofRestrict`: the inclusion of an open subset of a ringed space is
  flat.
* `Stacks.SheafOfModules.SupportedSections.isZero_supportedSectionsSheaf_modulePushforward`: the
  subsheaf of sections of `j_* 𝒢` supported on `Z` is zero.
* `Stacks.SheafOfModules.SupportedSections.isZero_supportedSectionsOnClosed_modulePushforward`:
  the same statement for `H_Z` as a sheaf of `𝒪_X|_Z`-modules on `Z`.
* `Stacks.SheafOfModules.SupportedSections.isZero_derivedSupportedSections_derivedPushforward`:
  `R H_Z(Rj_* K) = 0` for every object `K` of the unbounded derived category of
  `𝒪_U`-modules.

## Implementation notes

`H_Z` is the sheaf-valued functor `Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of sections supported on `Z`,
namely `Stacks.SheafOfModules.SupportedSections.supportedSectionsOnClosedFunctor`; it is not
the global functor `Γ_Z` of sections supported on `Z` with values in modules over the ring of
global functions. Its value on `𝒪_X`-modules is pinned down, up to the natural isomorphism
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso`, by the condition that its
pushforward to `X` is the subsheaf `supportedSectionsSheaf` of sections supported on `Z`; the
vanishing is therefore first proved for that subsheaf and then transported, pushforward along
the inclusion of a closed subset being faithful.

Both derived functors are arbitrary models: `Rj_*` and `R H_Z` enter as functors on the
unbounded derived categories together with a unit exhibiting them as right derived functors,
rather than as a fixed construction. No choice of resolution is made in the statement, and the
conclusion holds for every model, which is what makes it independent of the construction. The
two units are inverted at a K-injective complex by
`Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective`: for `Rj_*` at a K-injective
resolution `ℐ^•` of `K`, and for `R H_Z` at `j_* ℐ^•`, which is K-injective by Tag 0D5Z because
`j` is flat. Flatness of `j` holds because every germ map of the inclusion of an open subset is
an isomorphism of rings.

## References

* [Stacks Project, Tag 0G73](https://stacks.math.columbia.edu/tag/0G73)
* [Stacks Project, Tag 0G6N](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 0D5Z](https://stacks.math.columbia.edu/tag/0D5Z)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- The inclusion of an open subset of a ringed space is flat: its germ maps are the
isomorphisms `𝒪_{X, x} ⟶ (𝒪_X|_U)_x`, and a bijective ring homomorphism is flat. -/
theorem isFlat_ofRestrict (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    AlgebraicGeometry.IsFlat (X.ofRestrict U.isOpenEmbedding) := by
  intro x
  have : IsIso ((X.ofRestrict U.isOpenEmbedding).hom.stalkMap x) :=
    AlgebraicGeometry.PresheafedSpace.ofRestrict_stalkMap_isIso _ _ x
  exact RingHom.Flat.of_bijective
    ((ConcreteCategory.isIso_iff_bijective (C := CommRingCat) _).mp inferInstance)

end AlgebraicGeometry

namespace Stacks.SheafOfModules.SupportedSections

attribute [local instance] HasDerivedCategory.standard

/-- Let `j : (U, 𝒪_X|_U) ⟶ (X, 𝒪_X)` be the inclusion of an open subset disjoint from a closed
subset `Z`. A section of `j_* 𝒢` over an open `W` whose support lies in `Z ∩ W` is zero: it
vanishes on `W ∖ Z`, and restriction from `W` to `W ∖ Z` is injective on `j_* 𝒢` because the
two open sets have the same preimage in `U`. -/
theorem modulePushforward_section_eq_zero_of_suppSection_subset (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) (U : Opens X.carrier)
    (hUZ : (U : Set X.carrier) ∩ Z = ∅)
    (G : _root_.SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)))
    (W : Opens X.carrier)
    (s : ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj G).val.obj (op W))
    (hs : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
        ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj G)).suppSection W s ⊆
      Z ∩ (W : Set X.carrier)) :
    s = 0 := by
  set W' : Opens X.carrier := ⟨(W : Set X.carrier) \ Z, W.2.sdiff hZ⟩ with hW'
  set i : W' ⟶ W := homOfLE fun _ hx => hx.1 with hi
  have hzero : ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj G).val.presheaf.map
      i.op s = 0 :=
    TopCat.Presheaf.restrict_eq_zero_of_germ_eq_zero
      ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj G).isSheaf i s
      fun x hx => by
        by_contra hne
        exact hx.2 (hs ⟨hx.1, hne⟩).1
  have hpre : (opensMap (X.ofRestrict U.isOpenEmbedding)).obj W =
      (opensMap (X.ofRestrict U.isOpenEmbedding)).obj W' := by
    ext x
    refine ⟨fun hxW => ⟨hxW, fun hxZ => ?_⟩, fun hx => hx.1⟩
    have hmem : (X.ofRestrict U.isOpenEmbedding).hom.base x ∈ (U : Set X.carrier) ∩ Z :=
      ⟨x.2, hxZ⟩
    rw [hUZ] at hmem
    exact hmem
  have hiso : IsIso ((opensMap (X.ofRestrict U.isOpenEmbedding)).map i) :=
    ⟨eqToHom hpre, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hinj : Function.Injective
      (G.val.presheaf.map ((opensMap (X.ofRestrict U.isOpenEmbedding)).map i).op) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
  exact hinj ((hzero : G.val.presheaf.map
    ((opensMap (X.ofRestrict U.isOpenEmbedding)).map i).op s = 0).trans (map_zero _).symm)

/-- For the inclusion `j` of an open subset disjoint from the closed subset `Z`, the subsheaf of
sections of `j_* 𝒢` supported on `Z` is the zero sheaf of modules. -/
theorem isZero_supportedSectionsSheaf_modulePushforward (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) (U : Opens X.carrier)
    (hUZ : (U : Set X.carrier) ∩ Z = ∅)
    (G : _root_.SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :
    IsZero ((supportedSectionsSheaf Z
      ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj G)).1) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext s
  refine Subtype.ext ?_
  exact modulePushforward_section_eq_zero_of_suppSection_subset X Z hZ U hUZ G (unop W) s.1
    ((mem_supportedSectionsSheafι_range_iff Z _ W s.1).mp ⟨s, rfl⟩)

/-- For the inclusion `j` of an open subset disjoint from the closed subset `Z`, the sheaf
`H_Z(j_* 𝒢)` of `𝒪_X|_Z`-modules on `Z` is zero. -/
theorem isZero_supportedSectionsOnClosed_modulePushforward (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) (U : Opens X.carrier)
    (hUZ : (U : Set X.carrier) ∩ Z = ∅)
    (G : _root_.SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :
    IsZero ((supportedSectionsOnClosedFunctor X Z hZ).obj
      ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj G)) := by
  have hv : IsZero ((modulePushforward (RingedSpace.inverseImageProjection X
      (ClosedImmersionSheaves.closedSubsetInclusion Z))).obj
        ((supportedSectionsOnClosedFunctor X Z hZ).obj
          ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj G))) :=
    (((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).app
      ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj G)).isZero_iff).mpr
        (isZero_supportedSectionsSheaf_modulePushforward X Z hZ U hUZ G)
  have := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).faithful
  refine (IsZero.iff_id_eq_zero _).2 (Functor.map_injective
    (modulePushforward (RingedSpace.inverseImageProjection X
      (ClosedImmersionSheaves.closedSubsetInclusion Z))) ?_)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hv.eq_of_src _ _

/-- `H_Z` is additive, being right adjoint to the additive pushforward along the inclusion of
the closed subset `Z`. -/
instance supportedSectionsOnClosedFunctor_additive (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    (supportedSectionsOnClosedFunctor X Z hZ).Additive :=
  (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ).right_adjoint_additive

/-- **Stacks 0G73.** Let `Z` be a closed subset of a ringed space `X` and let
`j : (U, 𝒪_X|_U) ⟶ (X, 𝒪_X)` be the inclusion of an open subset with `U ∩ Z = ∅`. Then
`R H_Z(Rj_* K) = 0` for every `K` in `D(𝒪_U)`. -/
@[stacks 0G73]
theorem isZero_derivedSupportedSections_derivedPushforward
    (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) (U : Opens X.carrier)
    (hUZ : (U : Set X.carrier) ∩ Z = ∅)
    (Rj : DerivedCategory
        (_root_.SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (αj : (modulePushforward (X.ofRestrict U.isOpenEmbedding)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)))
      (ComplexShape.up ℤ))]
    (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing (RingedSpace.inverseImage X
        (ClosedImmersionSheaves.closedSubsetInclusion Z)))))
    (αH : (supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    [RH.IsRightDerivedFunctor αH (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (K : DerivedCategory
      (_root_.SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)))) :
    IsZero (RH.obj (Rj.obj K)) := by
  obtain ⟨K₀, e₀⟩ := HomotopyCategory.quotient_obj_surjective (DerivedCategory.Qh.objPreimage K)
  obtain ⟨I, q, hI, hq⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck K₀
  have hjI : CochainComplex.IsKInjective
      (((modulePushforward (X.ofRestrict U.isOpenEmbedding)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    isKInjective_modulePushforward_of_isFlat _ (isFlat_ofRestrict X U) I hI
  have hqiso : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) :=
    Localization.inverts DerivedCategory.Qh _ _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq)
  have hαj := Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective _ Rj αj I
  have hαH := Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective _ RH αH
    (((modulePushforward (X.ofRestrict U.isOpenEmbedding)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)
  have hzero : IsZero (((supportedSectionsOnClosedFunctor X Z hZ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((modulePushforward (X.ofRestrict U.isOpenEmbedding)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) := by
    refine (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun n => ?_)
    exact (isZero_supportedSectionsOnClosed_modulePushforward X Z hZ U hUZ (I.X n)).eq_of_src _ _
  let eK : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₀) ≅ K :=
    DerivedCategory.Qh.mapIso (eqToIso e₀) ≪≫ DerivedCategory.Qh.objObjPreimageIso K
  let eRj : Rj.obj K ≅ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePushforward (X.ofRestrict U.isOpenEmbedding)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :=
    (Rj.mapIso eK).symm ≪≫ Rj.mapIso (asIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q))) ≪≫
      (asIso (αj.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm
  refine IsZero.of_iso (Functor.map_isZero DerivedCategory.Qh
    (Functor.map_isZero (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) hzero)) ?_
  exact RH.mapIso eRj ≪≫ (asIso (αH.app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((modulePushforward (X.ofRestrict U.isOpenEmbedding)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)))).symm

end Stacks.SheafOfModules.SupportedSections

end
