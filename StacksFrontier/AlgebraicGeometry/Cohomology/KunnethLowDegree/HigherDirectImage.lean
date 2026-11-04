module

public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.DirectImage
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# The first higher direct image along a projection of a product over a field

For `fX : X ⟶ Spec k` quasi-compact and quasi-separated and `fY : Y ⟶ Spec k`, flat base change
([Stacks, Tag 02KH]) identifies `R¹π₂_* 𝒪` on `Y`, `π₂ : X ×_k Y ⟶ Y`, with the inverse image
of `R¹fX_* 𝒪_X`, a quasi-coherent module on `Spec k`.

## Main definitions

* `Stacks.KunnethLowDegree.rightDerivedSndUnitIso`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.KunnethLowDegree

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k))
  (fY : Y ⟶ Spec (.of k))

/-- **`R¹π₂_* 𝒪 ≅ fY^* R¹fX_* 𝒪_X`** by flat base change. -/
def rightDerivedSndUnitIso [QuasiCompact fX] [QuasiSeparated fX] :
    ((Scheme.Modules.pushforward (pullback.snd fX fY)).rightDerived 1).obj
        (SheafOfModules.unit (pullback fX fY).ringCatSheaf) ≅
      (Scheme.Modules.pullback fY).obj
        (((Scheme.Modules.pushforward fX).rightDerived 1).obj
          (SheafOfModules.unit X.ringCatSheaf)) :=
  haveI := flat_of_spec_field fY
  ((Scheme.Modules.pushforward (pullback.snd fX fY)).rightDerived 1).mapIso
      ((Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso (pullback.fst fX fY)).symm ≪≫
        (Stacks.ProjectiveBundleQuotients.pullbackIso (pullback.fst fX fY)).app _) ≪≫
    (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.derivedPlusIsoNat _ _ 1).symm ≪≫
    (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso
      (IsPullback.of_hasPullback fX fY) (SheafOfModules.unit X.ringCatSheaf) 1).symm ≪≫
    ((Stacks.ProjectiveBundleQuotients.pullbackIso fY).app _).symm ≪≫
    (Scheme.Modules.pullback fY).mapIso
      (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.derivedPlusIsoNat
        (Scheme.Modules.pushforward fX) (SheafOfModules.unit X.ringCatSheaf) 1)

end Stacks.KunnethLowDegree

end
