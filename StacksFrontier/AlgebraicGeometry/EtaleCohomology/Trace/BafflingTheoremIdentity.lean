module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BafflingTheorem
public import StacksFrontier.Homology.Ext.MapExactFunctorIsoId
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The baffling theorem: the Frobenius pullback on cohomology is the identity

For a scheme `X` of characteristic `p` the absolute Frobenius `F_X` induces, by pullback, the
identity on the étale cohomology `H^j(X, ℤ/nℤ)` of the constant sheaf, in every degree `j`.

The map is the canonical pullback map on étale cohomology, `etaleCohomologyRestrictionMap`,
followed by the canonical identification of the inverse image of the constant sheaf with the
constant sheaf. Both ingredients are the canonical ones attached to an arbitrary morphism of
schemes; nothing about the Frobenius enters their construction.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso_hom_app` — on constant sheaves the
  canonical inverse-image comparison agrees with the comparison coming from an identification of
  base change with the identity functor of the small étale site.
* `Stacks.EtaleCohomology.absoluteFrobenius_etaleCohomologyRestrictionMap_eq_id` — the baffling
  theorem: the induced map on `H^j(X, ℤ/nℤ)` is the identity.

## References

* [Stacks Project, Tag 03SN](https://stacks.math.columbia.edu/tag/03SN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u v w

namespace Stacks.EtaleCohomology

/-- On a constant sheaf the canonical comparison between the inverse image of the constant sheaf
and the constant sheaf is the component of the comparison between inverse image and the identity
functor obtained from an identification of base change with the identity of the small étale site.
-/
public theorem etaleAbelianInverseImageConstantIso_hom_app {X : Scheme.{u}} (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    (A : AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImageConstantIso.{u, v} g).hom.app A =
      (etaleSheafPullbackComparison.{u, v} X g e).hom.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) := by
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  let G := smallEtaleBaseChange g
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let hGT := hT.isTerminalObj G
  let : G.IsContinuous X.smallEtaleTopology X.smallEtaleTopology :=
    Functor.isContinuous_of_iso e _ _
  let pushIso : G.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      X.smallEtaleTopology X.smallEtaleTopology ≅ 𝟭 _ :=
    Functor.sheafPushforwardContinuousIso e.symm _ _ _ ≪≫
      Functor.sheafPushforwardContinuousId _ _
  let adjId := (Adjunction.id).ofNatIsoRight pushIso.symm
  let cA := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A
  let adjE := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    AddCommGrpCat.{max (u + 1) v} X.smallEtaleTopology X.smallEtaleTopology
  let adjT := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} hT).comp adjE
  let adjGT := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} hGT
  change (Adjunction.leftAdjointUniq adjT adjGT).hom.app A =
    (Adjunction.leftAdjointUniq adjE adjId).hom.app cA
  apply (adjT.homEquiv A cA).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app adjT adjGT A, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  change adjGT.unit.app A =
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} hT).homEquiv
      A ((G.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        X.smallEtaleTopology X.smallEtaleTopology).obj cA)
      ((adjE.homEquiv cA cA) ((Adjunction.leftAdjointUniq adjE adjId).hom.app cA))
  have hcmp : adjE.homEquiv cA cA ((Adjunction.leftAdjointUniq adjE adjId).hom.app cA) =
      adjId.unit.app cA := by
    simpa only [Functor.id_obj] using
      (Adjunction.homEquiv_leftAdjointUniq_hom_app adjE adjId cA)
  rw [hcmp]
  let P0 := (Functor.const X.Etaleᵒᵖ).obj A
  have hunit :
      (toSheafify X.smallEtaleTopology P0).app (Opposite.op (G.obj T)) =
        (toSheafify X.smallEtaleTopology P0).app (Opposite.op T) ≫
          (sheafify X.smallEtaleTopology P0).map (e.inv.app T).op := by
    simpa [P0] using (toSheafify X.smallEtaleTopology P0).naturality (e.inv.app T).op
  rw [Adjunction.homEquiv_unit]
  exact hunit

section AbsoluteFrobenius

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- **The Baffling Theorem**: on a scheme `X` of characteristic `p` the absolute Frobenius induces
the identity on `H^j(X, ℤ/nℤ)`. The canonical pullback map on étale cohomology, followed by the
canonical identification of the inverse image of the constant sheaf `ℤ/nℤ` with `ℤ/nℤ`, sends
every class to itself, in every degree `j`. -/
@[stacks 03SN "the induced map on H^j(X, Z/nZ) is the identity",
  sga "5 XV 2.Proposition2" "special case"]
public theorem absoluteFrobenius_etaleCohomologyRestrictionMap_eq_id
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (n j : ℕ)
    (x : Sheaf.H.{w}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n)))) j) :
    Sheaf.H.map
        ((etaleAbelianInverseImageConstantIso.{u, v} (absoluteFrobenius X p hX)).hom.app
          (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n)))) j
        (etaleCohomologyRestrictionMap.{u, v, w} (absoluteFrobenius X p hX)
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n)))) j x) = x := by
  let : IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology _
  let : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    CategoryTheory.IsGrothendieckAbelian.enoughInjectives
  let β := etaleSheafPullbackComparison.{u, v} X (absoluteFrobenius X p hX)
    (absoluteFrobeniusEtaleSiteIso X p hX)
  rw [etaleCohomologyRestrictionMap_apply, Sheaf.H.map_apply,
    Ext.comp_assoc_of_third_deg_zero,
    etaleAbelianInverseImageConstantIso_hom_app.{u, v} (absoluteFrobenius X p hX)
      (absoluteFrobeniusEtaleSiteIso X p hX)]
  have hinv : ((etaleAbelianInverseImageConstantIso.{u, v} (absoluteFrobenius X p hX)).app
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))).inv = β.inv.app _ := by
    have h : ((etaleAbelianInverseImageConstantIso.{u, v} (absoluteFrobenius X p hX)).app
          (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))).hom =
        (β.app ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ)))).hom :=
      etaleAbelianInverseImageConstantIso_hom_app.{u, v} (absoluteFrobenius X p hX)
        (absoluteFrobeniusEtaleSiteIso X p hX) _
    exact congrArg Iso.inv (Iso.ext h)
  rw [hinv]
  exact Stacks.Homology.ext_mapExactFunctor_of_isoId
    (etaleAbelianInverseImage.{u, v} (absoluteFrobenius X p hX)) β _ j _ x

end AbsoluteFrobenius

end Stacks.EtaleCohomology

end
