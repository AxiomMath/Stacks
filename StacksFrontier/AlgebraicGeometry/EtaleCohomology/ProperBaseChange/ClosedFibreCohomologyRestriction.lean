module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.EffaceableRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# Restriction of étale cohomology to the closed fibre over a henselian local ring

Let `A` be a henselian local ring, `f : X ⟶ Spec A` proper, `i : X₀ ⟶ X` the inclusion of the
closed fibre and `ℓ` a natural number. The first paragraph of the proof of the proper base change
theorem ([Stacks, Tag 095T]) shows that restriction
`H^q(X, F) ⟶ H^q(X₀, F|_{X₀})` is bijective for every abelian sheaf `F` killed by `ℓ`, as soon as
the restriction to `X₀` of every injective sheaf of `ℤ/ℓℤ`-modules on `X` has vanishing higher
cohomology. For `X = ℙ¹_A` that is [Stacks, Tag 0A5H].

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_toSheaf_of_injective` — [Stacks, Tag 03FD]: the
  underlying abelian sheaf of an injective sheaf of `ℤ/ℓℤ`-modules on the small étale site has
  vanishing positive-degree cohomology.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_closedFibre_zero` — restriction
  to the closed fibre is bijective in degree zero ([Stacks, Tag 0A3S]).
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_closedFibre_of_injective` —
  restriction to the closed fibre is bijective in every degree on sheaves killed by `ℓ`, granted
  the vanishing on the closed fibre for injective sheaves of `ℤ/ℓℤ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

universe u

namespace Stacks.EtaleCohomology

section Torsion

variable {X : Scheme.{u}} {ℓ : ℕ}

/-- The underlying abelian sheaf of a sheaf of `ℤ/ℓℤ`-modules is killed by `ℓ`. -/
private theorem zsmul_id_toSheaf_eq_zero
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) :
    (ℓ : ℤ) • 𝟙 ((SheafOfModules.toSheaf _).obj J) = 0 := by
  rw [zsmul_id_eq_zero_iff]
  intro V x
  rw [natCast_zsmul]
  exact nsmul_toSheaf_eq_zero.{u + 1, u + 1} X.smallEtaleTopology ℓ J V x

/-- An abelian sheaf killed by `ℓ` embeds into the underlying abelian sheaf of an injective sheaf
of `ℤ/ℓℤ`-modules. -/
private theorem exists_injective_mono_toSheaf_of_zsmul_id_eq_zero
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : (ℓ : ℤ) • 𝟙 G = 0) :
    ∃ (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ))
      (φ : G ⟶ (SheafOfModules.toSheaf _).obj J), Injective J ∧ Mono φ := by
  let : Abelian (SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u + 1, u, u + 1, 0} _
  have : EnoughInjectives (SheafOfModules.{u + 1}
      (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u + 1, u} _
  have hG' : ∀ (V : X.Etaleᵒᵖ) (x : ToType (G.obj.obj V)), ℓ • x = 0 := fun V x ↦ by
    rw [← natCast_zsmul]
    exact (zsmul_id_eq_zero_iff G (ℓ : ℤ)).1 hG V x
  let M := torsionSheafToModules.{u + 1, u + 1} X.smallEtaleTopology ℓ G hG'
  exact ⟨Injective.under M, (torsionSheafToModulesIso.{u + 1, u + 1} X.smallEtaleTopology ℓ
    G hG').inv ≫ (SheafOfModules.toSheaf _).map (Injective.ι M), inferInstance, mono_comp _ _⟩

end Torsion

section Injective

variable {X : Scheme.{u}} {ℓ : ℕ}
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **[Stacks, Tag 03FD] on the small étale site, in the form of sheaf cohomology.** The underlying
abelian sheaf of an injective sheaf of `ℤ/ℓℤ`-modules has vanishing cohomology in positive
degrees. -/
theorem subsingleton_H_toSheaf_of_injective
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) [Injective J]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((SheafOfModules.toSheaf _).obj J) q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    smallEtaleAbSheaf_enoughInjectives X
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0, u, u + 1}]
  let e := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (isTerminalEtaleMkId X)
  let E : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived (p + 1) ≅
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Scheme.Etale.mk (𝟙 X)))).rightDerived (p + 1) :=
    { hom := NatTrans.rightDerived e.hom (p + 1)
      inv := NatTrans.rightDerived e.inv (p + 1)
      hom_inv_id := by
        rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by
        rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id] }
  exact
    (Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_rightDerived_sections_toSheaf_succ.{0}
      X.smallEtaleTopology _ J (Scheme.Etale.mk (𝟙 X)) p).of_iso (E.app _)

end Injective

section ClosedFibre

variable (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsProper f]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (closedFibre A f).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Restriction to the closed fibre is bijective in degree zero** ([Stacks, Tag 0A3S] at abelian
coefficients). -/
theorem bijective_etaleCohomologyRestrictionMap_closedFibre_zero
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion A f) F 0) := by
  have := isIso_globalSectionsComparison_closedFibre_of_isProper.{u, 0} A f
  rw [etaleCohomologyRestrictionMap_zero_bijective_iff_unit _ terminalIsTerminal]
  have := (isIso_Γ_map_iff_isIso_app_terminal _).1
    (isIso_Γ_map_etaleAbelianUnit_of_isIso (closedFibreInclusion A f)
      (globalSectionsSmallEtaleInverseImageComparison.{u, 0} (closedFibreInclusion A f)).val F)
  exact ConcreteCategory.bijective_of_isIso _

/-- **Restriction to the closed fibre is bijective in every degree on sheaves killed by `ℓ`**,
granted that the restriction to the closed fibre of every injective sheaf of `ℤ/ℓℤ`-modules on
`X` has vanishing positive-degree cohomology (`hinj`; for `X = ℙ¹_A` this is
[Stacks, Tag 0A5H]). This is the first paragraph of the proof of [Stacks, Tag 095T]. -/
theorem bijective_etaleCohomologyRestrictionMap_closedFibre_of_injective (ℓ : ℕ)
    (hinj : ∀ (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)),
      Injective J → ∀ q : ℕ, 0 < q →
        Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
          (closedFibreInclusion A f)).obj ((SheafOfModules.toSheaf _).obj J)) q))
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (ℓ : ℤ) • 𝟙 F = 0) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion A f) F q) := by
  refine bijective_etaleCohomologyRestrictionMap_of_effaceable.{u, 0, u + 1}
    (closedFibreInclusion A f) (fun G ↦ (ℓ : ℤ) • 𝟙 G = 0) ?_ ?_ ?_ ?_ q F hF
  · intro G G' φ hG'
    rw [← cancel_epi (cokernel.π φ), Preadditive.comp_zsmul, Category.comp_id, comp_zero,
      ← Category.id_comp (cokernel.π φ), ← Preadditive.zsmul_comp, hG', zero_comp]
  · exact fun G _ ↦ bijective_etaleCohomologyRestrictionMap_closedFibre_zero A f G
  · intro G hG q hq ξ
    obtain ⟨J, φ, hJ, hφ⟩ := exists_injective_mono_toSheaf_of_zsmul_id_eq_zero G hG
    exact ⟨_, φ, hφ, zsmul_id_toSheaf_eq_zero J,
      @Subsingleton.elim _ (subsingleton_H_toSheaf_of_injective J q hq) _ _⟩
  · intro G hG q hq ξ
    obtain ⟨J, φ, hJ, hφ⟩ := exists_injective_mono_toSheaf_of_zsmul_id_eq_zero G hG
    exact ⟨_, φ, hφ, zsmul_id_toSheaf_eq_zero J, @Subsingleton.elim _ (hinj J hJ q hq) _ _⟩

end ClosedFibre

end Stacks.EtaleCohomology

end
