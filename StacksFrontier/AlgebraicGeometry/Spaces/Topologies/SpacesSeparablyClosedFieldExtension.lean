module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableSeparablyClosedInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleProperBaseChangeChow
public import StacksFrontier.CategoryTheory.Adjunction.MateEquivBijective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale cohomology of an algebraic space after extending a separably closed ground field

Let `K/k` be an extension of separably closed fields and let `p : X ⟶ Spec k` be a proper
morphism of algebraic spaces. Then for every torsion abelian sheaf `F` on `X_étale` and every
`q ≥ 0` the restriction map `H^q(X, F) ⟶ H^q(X_K, F|_{X_K})` is bijective (Stacks 0DG5).

## Main results

* `hasTorsionCohomology_shift`: having torsion cohomology sheaves is stable under shifts.
* `spacesEtaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt`: bijectivity of the
  restriction map is bijectivity of the inverse image on `Ext` out of the constant sheaf `ℤ`.
* `spacesEtaleCohomologyRestrictionMap_bijective_of_isSepClosed`: the statement above.

## Implementation notes

In the derived category, `H^q(X, F) = Hom(ℤ_X, F[q]) = Hom(p⁻¹ ℤ_k, F[q]) = Hom(ℤ_k, R p_* F[q])`
by the derived adjunction `p⁻¹ ⊣ R p_*`, and likewise over `K`. The derived base change map is the
mate of the comparison of the two composite inverse images around the cartesian square
(`AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleDerivedBaseChange_eq_mateEquiv`), so under these
identifications restriction to `X_K` becomes the map induced by `g⁻¹` for `g : Spec K ⟶ Spec k`
followed by the base change map at `F[q]` (`Stacks.Adjunction.map_bijective_of_mateEquiv`). The
base change map is invertible at `F[q]` by Stacks 0DG3, `F[q]` being bounded below with torsion
cohomology sheaves; and `g⁻¹` is an equivalence on derived categories, being one on abelian
sheaves (`AlgebraicGeometry.BigEtaleSpaceSite.isEquivalence_abelianInverseImage_of_isSepClosed`),
which is the source's "the spectrum of a separably closed field has no higher cohomology".

Stacks 0DG3 at the cartesian square `X_K = X ×_{Spec k} Spec K` is the reduction
`isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_representable` with its two scheme inputs
proved: proper base change for sheaves of sets on schemes (Stacks 0A3U,
`AlgebraicGeometry.isIso_smallEtaleSetBaseChange_of_isProper_forall`) and the proper base change
theorem for schemes (Stacks 095T,
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`).

The base change map `spacesEtaleDerivedBaseChange` and the derived adjunctions
`smallEtaleDerivedAdjunction` are defined for the standard model of the derived category,
`HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0DG5](https://stacks.math.columbia.edu/tag/0DG5)
* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 0DG2](https://stacks.math.columbia.edu/tag/0DG2)
* [Stacks Project, Tag 0DDG](https://stacks.math.columbia.edu/tag/0DDG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Space
open Stacks.Homology.DerivedSquare (derivedTwoSquare)

universe u w

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard smallEtaleAbelianInverseImage_additive

/-- Having torsion cohomology sheaves is stable under shifts: the cohomology sheaves of `E⟦n⟧` are
those of `E`, reindexed. -/
theorem hasTorsionCohomology_shift {Y : T.Spaces}
    {E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})}
    (hE : HasTorsionCohomology T E) (n : ℤ) : HasTorsionCohomology T (E⟦n⟧) :=
  fun i ↦ ObjectProperty.prop_of_iso _
    (((DerivedCategory.homologyFunctor _ 0).shiftIso n i (n + i) rfl).app E).symm (hE (n + i))

/-- Bijectivity of the restriction map on étale cohomology of algebraic spaces is bijectivity of
the map the inverse image induces on the `Ext` group out of the constant sheaf `ℤ`. -/
theorem spacesEtaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt {X Y : T.Spaces}
    (f : Y ⟶ X)
    [HasExt.{w} (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})]
    [HasExt.{w} (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})]
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) (q : ℕ) :
    Function.Bijective (spacesEtaleCohomologyRestrictionMap.{u, w} T f F q) ↔
      Stacks.EtaleCohomology.IsBijectiveOnExt
        (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f))
        ((constantSheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))) F q :=
  (Function.Bijective.of_comp_iff'
    (Stacks.EtaleCohomology.ext_precomp_iso_bijective
      ((smallEtaleAbelianInverseImageConstantIso T f).app (AddCommGrpCat.of (ULift ℤ))) q) _).trans
    (Stacks.EtaleCohomology.mapExt_bijective_iff_mapDerivedCategory _ _ _ _)

section SeparablyClosed

variable (k K : Type u) [Field k] [IsSepClosed k] [Field K] [IsSepClosed K] [Algebra k K]
  (hk : T.fppfSite.Contains (Spec (.of k))) (hK : T.fppfSite.Contains (Spec (.of K)))
  (s : Spec (.of k) ⟶ S)

/-- The morphism `h_{Spec K} ⟶ h_{Spec k}` of represented algebraic spaces induced by an
extension of fields `K/k`, with `Spec k` over `S` by `s` and `Spec K` over `S` through it. -/
abbrev fieldExtensionSpaceHom :
    yonedaSpace T.fppfSite S T.fppf_mem (BigFppfOver.mk T.fppfSite S T.fppf_mem hK
        (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ s)) ⟶
      yonedaSpace T.fppfSite S T.fppf_mem (BigFppfOver.mk T.fppfSite S T.fppf_mem hk s) :=
  yonedaSpaceHom (BigFppfOver.homMk T.fppfSite S T.fppf_mem hk s
    (T := BigFppfOver.mk T.fppfSite S T.fppf_mem hK
      (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ s))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl)

/-- **Étale cohomology of a proper algebraic space does not change under an extension of
separably closed ground fields**. Let `K/k` be an extension of separably closed fields and
`p : X ⟶ Spec k` a proper morphism of algebraic spaces; write `X_K = X ×_{Spec k} Spec K` with
projection `g' : X_K ⟶ X`. Then for every torsion abelian sheaf `F` on `X_étale` and every
`q ≥ 0` the restriction map `H^q_étale(X, F) ⟶ H^q_étale(X_K, F|_{X_K})` is bijective.

The base change map `g⁻¹ R p_* E ⟶ R p_{K,*} (g')⁻¹ E` is invertible at every bounded below `E`
with torsion cohomology sheaves by Stacks 0DG3
(`isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_representable`, with Stacks 0A3U and
Stacks 095T for schemes supplied). -/
@[stacks 0DG5, sga "4 XII 5.4" "more general", sga "4 XVI 1.6" "Abelian clause"]
theorem spacesEtaleCohomologyRestrictionMap_bijective_of_isSepClosed {X : T.Spaces}
    (p : X ⟶ yonedaSpace T.fppfSite S T.fppf_mem (BigFppfOver.mk T.fppfSite S T.fppf_mem hk s))
    (hp : Space.IsProper T.fppfSite S T.fppf_mem p.hom)
    [HasExt.{w} (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})]
    [HasExt.{w} (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
      (pullback p (fieldExtensionSpaceHom T k K hk hK s))) Ab.{u + 1})]
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) F) (q : ℕ) :
    Function.Bijective (spacesEtaleCohomologyRestrictionMap.{u, w} T
      (pullback.fst p (fieldExtensionSpaceHom T k K hk hK s)) F q) := by
  let g := fieldExtensionSpaceHom T k K hk hK s
  let g' := pullback.fst p g
  let f' := pullback.snd p g
  have sq : IsPullback g' f' p g := IsPullback.of_hasPullback p g
  let Zk := (constantSheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
    (yonedaSpace T.fppfSite S T.fppf_mem (BigFppfOver.mk T.fppfSite S T.fppf_mem hk s)))
      Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))
  refine (spacesEtaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, w} T g' F q).mpr ?_
  refine (Stacks.EtaleCohomology.isBijectiveOnExt_congr_obj _
    ((smallEtaleAbelianInverseImageConstantIso T p).app (AddCommGrpCat.of (ULift ℤ)))
    (Iso.refl F) q).mp ?_
  refine (Stacks.EtaleCohomology.map_bijective_iff_of_objIso _
    (((CategoryTheory.Sites.abelianInverseImage
      (smallEtaleMorphism T p)).mapDerivedCategorySingleFunctor 0).app Zk) (Iso.refl _)).mp ?_
  let α := derivedTwoSquare (spacesEtaleAbelianInverseImageSquare T p g g' f' sq)
  have hβ : IsIso ((spacesEtaleDerivedBaseChange T p g g' f' sq).app
      (((DerivedCategory.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)) :=
    isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_representable T
      isIso_smallEtaleSetBaseChange_of_isProper_forall
      (fun f _ ↦ Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f) p hp
      g g' f' sq _ (-(q : ℤ))
      (DerivedCategory.TStructure.t.isGE_shift ((DerivedCategory.singleFunctor
        (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) 0).obj F)
        0 (q : ℤ) (-(q : ℤ)) (by omega))
      (hasTorsionCohomology_shift T (hasTorsionCohomology_singleFunctor_obj T F hF) (q : ℤ))
  rw [spacesEtaleDerivedBaseChange_eq_mateEquiv] at hβ
  have : (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)).IsEquivalence :=
    isEquivalence_abelianInverseImage_of_isSepClosed T k K hk hK s
  have : (CategoryTheory.Sites.abelianInverseImage
      (smallEtaleMorphism T g)).mapDerivedCategory.IsEquivalence :=
    Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory _
  exact Stacks.Adjunction.map_bijective_of_mateEquiv
    (smallEtaleDerivedAdjunction T p) (smallEtaleDerivedAdjunction T f') α
    ((DerivedCategory.singleFunctor _ 0).obj Zk)
    (((DerivedCategory.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)
    ((Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _)

end SeparablyClosed

end AlgebraicGeometry.BigEtaleSpaceSite

end
