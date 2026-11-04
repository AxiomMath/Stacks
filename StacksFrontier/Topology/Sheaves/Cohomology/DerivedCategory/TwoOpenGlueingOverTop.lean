module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DerivedRestrictionDictionaryCoherence

/-!
# The compatibility clause of the two-open glueing problem over the ambient open

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it, as in
Situation 0D67.  This file proves the coherence of the dictionary along a chain `W ≤ U ≤ O`, and
with it the compatibility clause of the transport of [Stacks, Tag 08DG] into that situation over
the ambient open `⊤`.

## Main results

* `Stacks.DerivedGlueing.assemble_dictionary`: the right-hand side of the coherence, read through
  `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrictIncl`, is the same as read
  through the dictionary over the middle open.
* `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrict_hom_app_trans_incl`: the
  coherence of the dictionary for `W ≤ U ≤ O`.
* `Stacks.DerivedGlueing.twoOpenGlueingOver_top`: the compatibility clause of the two-open
  glueing problem of Situation 0D67 over the ambient open.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlueingComplexes Stacks.Cohomology.DerivedOpenImmersion

namespace Stacks.DerivedGlueing

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The two readings of the right-hand side of the coherence agree.** -/
theorem assemble_dictionary (S : LocallyGiven X) (W U O : Opens X.carrier) (hWU : W ≤ U)
    (hUO : U ≤ O) (K : OpenDerivedCategory X O) :
    (S.restrictionComp W U O hWU hUO).hom.app K ≫
        (S.restrictionIsoDerivedRestrictIncl hWU).hom.app ((S.restriction U O hUO).obj K) ≫
        (derivedRestrict (restrictIncl (X := X) hWU)).map
          ((S.restrictionIsoDerivedRestrict O U hUO).hom.app K) ≫
        (restrictInclDerivedIso (X := X) hWU).inv.app
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K) =
      (S.restrictionComp W U O hWU hUO).hom.app K ≫
        (S.restrictionIsoDerivedRestrict U W hWU).hom.app ((S.restriction U O hUO).obj K) ≫
        (derivedRestrict (X.ofRestrict W.isOpenEmbedding)).map
          ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory.map
              ((S.restrictionIsoJStar O U hUO).hom.app K) ≫
            (derivedJShriekCounit U).app
              ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) :=
  assemble_pure (S.restrictionIsoDerivedRestrict U W hWU)
    (restrictInclDerivedIso (X := X) hWU) (derivedRestrictJShriekIso U)
    (restrictionIsoDerivedRestrictIncl_eq S hWU)
    (N := (jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
    ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory.map
        ((S.restrictionIsoJStar O U hUO).hom.app K) ≫
      (derivedJShriekCounit U).app
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K))
    ((S.restrictionComp W U O hWU hUO).hom.app K)
    ((S.restrictionIsoDerivedRestrict O U hUO).hom.app K)
    (dictionary_at_one_open S O U hUO K)

/-- **The coherence of the dictionary for `W ≤ U ≤ O`.** -/
theorem LocallyGiven.restrictionIsoDerivedRestrict_hom_app_trans_incl (S : LocallyGiven X)
    (W U O : Opens X.carrier) (hWU : W ≤ U) (hUO : U ≤ O) (K : OpenDerivedCategory X O) :
    (S.restrictionIsoDerivedRestrict O W (hWU.trans hUO)).hom.app K =
      (S.restrictionComp W U O hWU hUO).hom.app K ≫
        (S.restrictionIsoDerivedRestrictIncl hWU).hom.app ((S.restriction U O hUO).obj K) ≫
        (derivedRestrict (restrictIncl (X := X) hWU)).map
          ((S.restrictionIsoDerivedRestrict O U hUO).hom.app K) ≫
        (restrictInclDerivedIso (X := X) hWU).inv.app
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K) :=
  (S.restrictionIsoDerivedRestrict_hom_app_trans W U O hWU hUO K).trans
    (assemble_dictionary S W U O hWU hUO K).symm

/-- The coherence of the dictionary along `U ⊓ V ≤ U ≤ ⊤`. -/
theorem coherence_at_top_left (S : LocallyGiven X)
    (U V : Opens X.carrier) (K : OpenDerivedCategory X ⊤) :
    (S.restrictionIsoDerivedRestrict ⊤ (U ⊓ V) le_top).hom.app K =
      (S.restrictionComp (U ⊓ V) U ⊤ inf_le_left le_top).hom.app K ≫
        (S.restrictionIsoDerivedRestrictIncl (inf_le_left : U ⊓ V ≤ U)).hom.app
          ((S.restriction U ⊤ le_top).obj K) ≫
        (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).map
          ((S.restrictionIsoDerivedRestrict ⊤ U le_top).hom.app K) ≫
        (restrictInclDerivedIso (X := X) (inf_le_left : U ⊓ V ≤ U)).inv.app
          ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj K) :=
  S.restrictionIsoDerivedRestrict_hom_app_trans_incl (U ⊓ V) U ⊤ inf_le_left le_top K

/-- The coherence of the dictionary along `U ⊓ V ≤ V ≤ ⊤`. -/
theorem coherence_at_top_right (S : LocallyGiven X)
    (U V : Opens X.carrier) (K : OpenDerivedCategory X ⊤) :
    (S.restrictionIsoDerivedRestrict ⊤ (U ⊓ V) le_top).hom.app K =
      (S.restrictionComp (U ⊓ V) V ⊤ inf_le_right le_top).hom.app K ≫
        (S.restrictionIsoDerivedRestrictIncl (inf_le_right : U ⊓ V ≤ V)).hom.app
          ((S.restriction V ⊤ le_top).obj K) ≫
        (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map
          ((S.restrictionIsoDerivedRestrict ⊤ V le_top).hom.app K) ≫
        (restrictInclDerivedIso (X := X) (inf_le_right : U ⊓ V ≤ V)).inv.app
          ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj K) :=
  S.restrictionIsoDerivedRestrict_hom_app_trans_incl (U ⊓ V) V ⊤ inf_le_right le_top K

/-- **The compatibility clause of the two-open glueing problem of Situation 0D67 over the
ambient open.** -/
theorem twoOpenGlueingOver_top (S : LocallyGiven X) (U V : Opens X.carrier) :
    TwoOpenGlueingOver S U V ⊤ le_top le_top :=
  twoOpenGlueingOver_top_of_coherence S U V (coherence_at_top_left S U V)
    (coherence_at_top_right S U V)

end Stacks.DerivedGlueing

end
