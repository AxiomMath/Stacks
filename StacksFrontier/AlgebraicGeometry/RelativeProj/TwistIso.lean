module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.TwistBaseChange.General

/-!
# The twist comparison along the inclusion of projective spectra is invertible

Let `A` be a sheaf of graded algebras on a scheme `S`, and let `U ⊆ V` be affine opens of `S`.
Restriction `Γ(V, A) → Γ(U, A)` induces a morphism of projective spectra defined on an open
domain of `Proj Γ(U, A)`, which is everything, and
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` is the resulting everywhere-defined
morphism `Proj Γ(U, A) → Proj Γ(V, A)`. This file shows that the comparison map from the pullback
along it of the `n`-th twisting sheaf of `Proj Γ(V, A)` to the `n`-th twisting sheaf of
`Proj Γ(U, A)` is an isomorphism, for every `n : ℤ`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProj.projInclusionTopSection`: the identification of
  `Proj Γ(U, A)` with the open domain, which is everything.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProj.projInclusionTopSection_ι`: the identification is a
  section of the inclusion of the open domain.
* `Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap_eq_comp`: the everywhere-defined
  morphism is the identification followed by the morphism on the open domain.
* `Stacks.AlgebraicGeometry.RelativeProj.isIso_projInclusionTwistComposite`: the comparison map
  on the `n`-th twist, written out as a composite of six factors, is an isomorphism.

## Implementation notes

The comparison map is the image under pullback of the twist map on the open domain, conjugated by
components of `AlgebraicGeometry.Scheme.Modules.pullbackComp`, `pullbackCongr` and `pullbackId`.
The reassociation `projInclusionMap_eq_comp` enters as an explicit `pullbackCongr` component
rather than through definitional unfolding, which keeps the kernel check fast.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeProj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- The identification of `Proj Γ(U, A)` with the open domain of the morphism induced by
restriction, which is everything by
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionDomain_eq_top`. -/
public def projInclusionTopSection (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    AlgebraicGeometry.Proj (A.grading U) ⟶
      (mapDomain (A.grading V) (A.grading U) (A.res h)).toScheme :=
  (Scheme.topIso _).inv ≫
    (Scheme.isoOfEq _ (projInclusionDomain_eq_top A U V h hU hV).symm).hom

/-- The identification is a section of the inclusion of the open domain. -/
public theorem projInclusionTopSection_ι (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    projInclusionTopSection A U V h hU hV ≫
        (mapDomain (A.grading V) (A.grading U) (A.res h)).ι =
      𝟙 (AlgebraicGeometry.Proj (A.grading U)) := by
  rw [projInclusionTopSection, Category.assoc]
  exact topIso_inv_isoOfEq_hom_ι (A.grading V) (A.grading U) (A.res h)
    (projInclusionDomain_eq_top A U V h hU hV)

/-- The everywhere-defined morphism of projective spectra is the identification followed by the
morphism induced by restriction on the open domain. -/
public theorem projInclusionMap_eq_comp (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    projInclusionTopSection A U V h hU hV ≫
        (projMapData (A.grading V) (A.grading U) (A.res h)).hom =
      projInclusionMap A U V h hU hV :=
  Category.assoc _ _ _

/-- For an inclusion `U ⊆ V` of affine opens of the base and every `n : ℤ`, the comparison map
from the pullback along `projInclusionMap` of the `n`-th twisting sheaf of `Proj Γ(V, A)` to the
`n`-th twisting sheaf of `Proj Γ(U, A)`, written out as a composite, is an isomorphism. -/
public theorem isIso_projInclusionTwistComposite (U V : S.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ) :
    IsIso (((Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).inv.app
          (twistingSheaf (A.grading V) n) ≫
        (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
            (projMapData (A.grading V) (A.grading U) (A.res h)).hom).inv.app
          (twistingSheaf (A.grading V) n) ≫
        (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
          ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n) ≫
        (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
            (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).hom.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullbackCongr (projInclusionTopSection_ι A U V h hU hV)).hom.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullbackId
          (AlgebraicGeometry.Proj (A.grading U))).hom.app (twistingSheaf (A.grading U) n) :
      (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
          (twistingSheaf (A.grading V) n) ⟶ twistingSheaf (A.grading U) n)) := by
  have _hD : IsIso ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n) :=
    TwistBaseChange.isIso_projMapData_twistMap_res_of_le_opens A.toGradedAlgebra
      (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h n
  exact IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _)
    (IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _)
      (IsIso.comp_isIso' (Functor.map_isIso _ _)
        (IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _)
          (IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _)
            (NatIso.isIso_app_of_isIso _ _)))))

end Stacks.AlgebraicGeometry.RelativeProj

end
