module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# Cohomology classes of a filtered colimit come from a stage

Let `Z` be a quasi-compact and quasi-separated scheme and `F = colim Fᵢ` a filtered colimit of
abelian sheaves on the small étale site of `Z`. Every class in `H^q(Z, F)` is the image of a
class in some `H^q(Z, Fᵢ)`. This is the elementwise consequence of [Stacks, Tag 03Q5], read on
`CategoryTheory.Sheaf.H` (`Ext` out of the constant sheaf `ℤ`) rather than on the right derived
functors of global sections, through
`CategoryTheory.Sheaf.rightDerivedΓIsoFunctorH`-style identification
`Stacks.Cohomology.rightDerivedΓIsoFunctorH`.

It is the first reduction of the proof of [Stacks, Tag 09ZE]: a class of `F|_Z` comes from a
"small" sheaf mapping to `F`.

## Main results

* `Stacks.EtaleCohomology.exists_comp_mk₀_eq_of_isColimit` — the class comes from a stage.

## References

* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 09ZE](https://stacks.math.columbia.edu/tag/09ZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology


/-- **A class in the cohomology of a filtered colimit comes from a stage.** For `Z`
quasi-compact and quasi-separated and a filtered colimit cocone `c` of abelian sheaves on
`Z_ét`, every `ξ ∈ H^q(Z, c.pt)` is the image of some class of `H^q(Z, D i)` under
`D i ⟶ c.pt`. -/
theorem exists_comp_mk₀_eq_of_isColimit (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z] [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (c : Cocone D)
    (hc : IsColimit c) (q : ℕ) (ξ : Sheaf.H.{u + 1} c.pt q) :
    ∃ (i : I) (x : Sheaf.H.{u + 1} (D.obj i) q), x.comp (Ext.mk₀ (c.ι.app i)) (add_zero q) = ξ := by
  have : EnoughInjectives (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    smallEtaleAbSheaf_enoughInjectives Z
  have : (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hpost := isIso_colimit_post_rightDerived_Γ_smallEtale.{0, u} Z q D
  have : PreservesColimit D
      ((Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q) :=
    preservesColimit_of_isIso_post _ D
  let H : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.functorH.{u + 1, u + 1, u, u + 1} Z.smallEtaleTopology q
  let e : (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q ≅
      H :=
    Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u, u + 1}
      Z.smallEtaleTopology q
  have : PreservesColimit D (H) :=
    preservesColimit_of_natIso D e
  have hc' := isColimitOfPreserves (H) hc
  obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep _ hc' ξ
  exact ⟨i, x, hx⟩

end Stacks.EtaleCohomology
