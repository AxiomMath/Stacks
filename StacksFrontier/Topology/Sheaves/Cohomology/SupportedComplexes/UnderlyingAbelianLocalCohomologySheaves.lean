module

public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianLocalCohomologySheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheaves
import StacksCore.Tactic.StacksAttribute

/-!
# Local cohomology sheaves and the underlying abelian sheaf

Let `Z` be a closed subset of a ringed space `X` and let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the
inclusion. Sections supported on `Z` are available in two flavours: the functor
`H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of Stacks 0G6N and the functor `H_Z : Ab(X) ⥤ Ab(Z)` of
Stacks 01AY. This file identifies the two: forgetting the module structure takes the first to
the second,

`H_Z(ℱ)_ab ≅ H_Z(ℱ_ab)`,

naturally in the `𝒪_X`-module `ℱ`. Passing to right derived functors, this gives the
degree-zero case of Stacks 0G74 part (2), the comparison `ℋ ⁿ_Z(ℱ)_ab ≅ ℋ ⁿ_Z(ℱ_ab)` of local
cohomology *sheaves*.

## Main results

* `supportedSectionsSheafForgetIso`: the comparison on `X`, before realization on `Z`. The
  underlying abelian sheaf of the subsheaf of sections of `ℱ` supported on `Z` is the subsheaf
  of sections of `ℱ_ab` supported on `Z`.
* `supportedSectionsOnClosedForgetIso` (Stacks 0G6N, abelian compatibility):
  `H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` followed by forgetting the module structure is
  `ℱ ↦ H_Z(ℱ_ab)`, as functors `Mod(𝒪_X) ⥤ Ab(Z)`.
* `localCohomologySheafFunctorZeroForgetIso` (Stacks 0G74, part (2) in degree zero):
  `ℋ ⁰_Z(ℱ)_ab ≅ ℋ ⁰_Z(ℱ_ab)`, naturally in `ℱ`.

## Implementation notes

The comparison on `X` is sectionwise the identity. Both subsheaves are cut out of the same
abelian sheaf of sections by the same condition: the module-level subsheaf by containment of
the support of a section in `Z ∩ U`, the abelian one by vanishing of every germ outside `Z`,
and these two conditions agree by
`AlgebraicGeometry.SheafOfModules.mem_supportedSections_moduleSheaf_iff`. So the components are
the identity on the ambient sections, restricted to coinciding subgroups, and every naturality
square commutes by `rfl`.

The comparison on `Z` is obtained from the one on `X` by reflecting along pushforward. Neither
realization on `Z` is an equality — both are a choice of preimage under a fully faithful
pushforward, specified only up to the natural isomorphisms
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` (module level, in
`Stacks.SheafOfModules.SupportedSections`) and
`ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_comp_pushforward_iso` (abelian
level) — so the
comparison cannot be written down directly. Instead the two composites with `i_*` are
identified, using that pushforward of modules along `i` followed by forgetting the module
structure is *definitionally* abelian pushforward along `i` (`modulePushforward` is
`SheafOfModules.pushforward`, which leaves the underlying presheaf of abelian groups alone), and
then `CategoryTheory.Functor.fullyFaithfulCancelRight` removes the `i_*`, which is fully
faithful because `i` is a closed embedding (Stacks 00AG).

Only the degree-zero case of Stacks 0G74 part (2) is proved here, and in that degree the
statement carries no derived-functor content: `ℋ ⁰_Z` is `H_Z` on both sides, by
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorZeroIso` and
`ClosedImmersionSheaves.localCohomologySheafFunctorZeroIso`, both of which hold because `H_Z`
is a right adjoint and hence left exact. The higher degrees are **not** proved here, and are
not a formal consequence of what is: forgetting the module structure does not preserve
injectives, so an injective resolution of `ℱ` by `𝒪_X`-modules is not an injective resolution
of `ℱ_ab`. The source's argument for the higher degrees is that the underlying abelian sheaf of
an injective `𝒪_X`-module is flasque, hence acyclic for `H_Z`, so that such a resolution is
nonetheless an `H_Z`-acyclic resolution of `ℱ_ab`. That argument is carried out, at the level of
the unbounded derived categories rather than degree by degree, in
`UnderlyingAbelianLocalCohomologyInvertible.lean`, whose
`isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor` is the full statement of
Stacks 0G74 part (2). The higher degrees are not deduced from it here,
which would need the comparison of `Functor.rightDerived` with the total derived functor on the
unbounded derived category.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Remark 17.5.4 (Tag 01AY)](https://stacks.math.columbia.edu/tag/01AY)
* [Stacks Project, Tag 00AG](https://stacks.math.columbia.edu/tag/00AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier)

/-! ### The comparison before realization on the closed subset -/

/-- The comparison of `supportedSectionsSheafForgetIso` over a single open set. Both groups are
the subgroup of sections of `ℱ` over `U` supported on `Z ∩ U`, described once through the
support of a section of a sheaf of modules and once through vanishing of germs of an abelian
sheaf; the map is the identity on the underlying sections. -/
def supportedSectionsForgetAppIso (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) :
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj
        ((supportedSectionsFunctor X Z).obj F)).obj.obj U ≅
      ((ClosedImmersionSheaves.supportedSectionsFunctor Z).obj
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj F)).obj.obj U where
  hom := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun s => ⟨s.1, (AlgebraicGeometry.SheafOfModules.mem_supportedSections_moduleSheaf_iff
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F) Z (unop U) s.1).2 s.2⟩)
    (fun _ _ => rfl))
  inv := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun s => ⟨s.1, (AlgebraicGeometry.SheafOfModules.mem_supportedSections_moduleSheaf_iff
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F) Z (unop U) s.1).1 s.2⟩)
    (fun _ _ => rfl))
  hom_inv_id := by ext s; rfl
  inv_hom_id := by ext s; rfl

/-- **Forgetting the module structure commutes with taking sections supported on `Z`.** The
underlying abelian sheaf of the subsheaf of `𝒪_X`-module sections supported on `Z` is the
subsheaf of the underlying abelian sheaf consisting of its sections supported on `Z`, naturally
in the `𝒪_X`-module. No closedness assumption on `Z` is needed. -/
def supportedSectionsSheafForgetIso :
    supportedSectionsFunctor X Z ⋙ _root_.SheafOfModules.toSheaf (structureSheafRing X) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        ClosedImmersionSheaves.supportedSectionsFunctor Z :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk
      (P := CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
        (A := AddCommGrpCat.{u}))
      (NatIso.ofComponents (supportedSectionsForgetAppIso X Z F)
        (by intro U V i; ext s; rfl)))
    (by
      intro F G f
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      ext s
      rfl)

/-! ### The comparison on the closed subset -/

/-- **Stacks 0G6N, abelian compatibility.** Let `Z` be a closed subset of a ringed space `X`.
Taking the sections of an `𝒪_X`-module supported on `Z`, realized as a sheaf of `𝒪_X|_Z`-modules
on `Z`, and then forgetting the module structure, is the same as forgetting the module structure
first and then taking the sections of the resulting abelian sheaf supported on `Z`, realized as
an abelian sheaf on `Z`. The identification is natural in the `𝒪_X`-module. -/
@[stacks 0G6N "abelian compatibility"]
def supportedSectionsOnClosedForgetIso (hZ : IsClosed Z) :
    supportedSectionsOnClosedFunctor X Z hZ ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z)) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        ClosedImmersionSheaves.supportedSectionsOnClosedFunctor Z hZ := by
  have hc : (supportedSectionsOnClosedFunctor X Z hZ ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z))) ⋙
        closedInclusionPushforward (TopCat.of Z) X.carrier
          (ClosedImmersionSheaves.closedSubsetInclusion Z) ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        ClosedImmersionSheaves.supportedSectionsOnClosedFunctor Z hZ) ⋙
        closedInclusionPushforward (TopCat.of Z) X.carrier
          (ClosedImmersionSheaves.closedSubsetInclusion Z) :=
    Functor.isoWhiskerRight
        (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ)
        (_root_.SheafOfModules.toSheaf (structureSheafRing X)) ≪≫
      supportedSectionsSheafForgetIso X Z ≪≫
      Functor.isoWhiskerLeft (_root_.SheafOfModules.toSheaf (structureSheafRing X))
        (ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_comp_pushforward_iso Z hZ).symm
  have hfull : (closedInclusionPushforward (TopCat.of Z) X.carrier
      (ClosedImmersionSheaves.closedSubsetInclusion Z)).Full :=
    closedInclusion_pushforward_full _ _ _ hZ.isClosedEmbedding_subtypeVal
  have hfaithful : (closedInclusionPushforward (TopCat.of Z) X.carrier
      (ClosedImmersionSheaves.closedSubsetInclusion Z)).Faithful :=
    closedInclusion_pushforward_faithful _ _ _ hZ.isClosedEmbedding_subtypeVal
  exact @Functor.fullyFaithfulCancelRight _ _ _ _ _ _ _ _
    (closedInclusionPushforward (TopCat.of Z) X.carrier
      (ClosedImmersionSheaves.closedSubsetInclusion Z)) hfull hfaithful hc

/-! ### The local cohomology sheaves in degree zero -/

/-- **Stacks 0G74, part (2), in degree zero.** Let `Z` be a closed subset of a ringed space `X`
and let `ℱ` be a sheaf of `𝒪_X`-modules with underlying abelian sheaf `ℱ_ab`. The degree-zero
local cohomology sheaf `ℋ ⁰_Z(ℱ)`, an `𝒪_X|_Z`-module on `Z`, has underlying abelian sheaf the
degree-zero local cohomology sheaf `ℋ ⁰_Z(ℱ_ab)` of `ℱ_ab`, naturally in `ℱ`.

In degree zero both sides are the supported-sections functor itself, `H_Z` being left exact, so
this is `supportedSectionsOnClosedForgetIso` read through the two degree-zero
identifications. -/
@[stacks 0G74
  "part (2) in degree 0 only; the comparison in higher degrees is not proved here, see \
  isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor for the derived form"]
def localCohomologySheafFunctorZeroForgetIso (hZ : IsClosed Z) :
    localCohomologySheafFunctor X Z hZ 0 ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z)) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        ClosedImmersionSheaves.localCohomologySheafFunctor Z hZ 0 :=
  Functor.isoWhiskerRight (localCohomologySheafFunctorZeroIso X Z hZ)
      (_root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z))) ≪≫
    supportedSectionsOnClosedForgetIso X Z hZ ≪≫
    Functor.isoWhiskerLeft (_root_.SheafOfModules.toSheaf (structureSheafRing X))
      (ClosedImmersionSheaves.localCohomologySheafFunctorZeroIso Z hZ).symm

end Stacks.Cohomology.SupportedComplexes

end
