module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.OpenPairSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomologyOverAnObject

/-!
# Sections over an open, and the excision sequence of an open subscheme

Let `X` be a scheme and `V` an open subscheme. The functor `Γ_{V,∅}` of sections over `V`
(`AlgebraicGeometry.Scheme.opensSupport` for the pair `∅ ≤ V`) has as right derived functors the
étale cohomology of the *scheme* `V` with coefficients in the restriction `𝓕|_V`:

`R^iΓ_{V,∅}(𝓕) ≅ H^i(V, 𝓕|_V)`,

by `Stacks.EtaleCohomology.rightDerivedSectionsOverObjectIso` (restriction to an object of the
small étale site is exact and preserves injectives). Together with the excision sequence
`Γ_{X,U} ⟶ Γ_{X,∅} ⟶ Γ_{U,∅}` (short exact on injective sheaves,
`AlgebraicGeometry.Scheme.shortExact_opensSupport_of_injective`) this gives the window

`H^i(X, 𝓕) ⟶ H^i(U, 𝓕|_U) ⟶ H^{i+1}_{X∖U}(X, 𝓕)`

of the long exact sequence of cohomology with supports, which is how the proof of Theorem 1.1 of
Travaux de Gabber, Exposé XVIII-A, passes from a bound on `H^*_{X∖U}(X, -)` to a bound on
`H^*(U, -)` when `X` has no higher cohomology.

## Main definitions

* `AlgebraicGeometry.Scheme.opensSupportBotToEvaluation`: `Γ_{V,∅}` is the functor of sections
  over `V`.

## Main results

* `Scheme.subsingleton_sheafH_etaleRestriction_iff_isZero_rightDerived_opensSupport_bot`:
  `H^i(V, 𝓕|_V) = 0` exactly when `R^iΓ_{V,∅}(𝓕) = 0`.
* `AlgebraicGeometry.Scheme.isZero_rightDerived_opensSupport_bot_top_of_subsingleton`:
  `H^i(X, 𝓕) = 0` gives `R^iΓ_{X,∅}(𝓕) = 0`.
* `AlgebraicGeometry.Scheme.isZero_rightDerived_opensSupport_bot_of_isZero`: the window of the
  excision sequence, `R^iΓ_{X,∅}(𝓕) = 0` and `R^{i+1}Γ_{X,U}(𝓕) = 0` give `R^iΓ_{U,∅}(𝓕) = 0`.
* `AlgebraicGeometry.Scheme.subsingleton_sheafH_etaleRestriction_of_subsingleton_of_isZero`:
  the same window read on cohomology.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  proof of Theorem 1.1, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- **`Γ_{V,∅}` is the functor of sections over `V`**: the inclusion of the sections vanishing on
the empty open subscheme, which are all sections. -/
def opensSupportBotToEvaluation (V : X.Opens) :
    opensSupport (bot_le : (⊥ : X.Opens) ≤ V) ⟶
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op ((opensToEtale X).obj V)) where
  app _ := AddCommGrpCat.ofHom (AddSubgroup.subtype _)
  naturality _ _ _ := rfl

/-- The inclusion `opensSupportBotToEvaluation V` of `Γ_{V,∅}` into the sections over `V` is an
isomorphism. -/
instance isIso_opensSupportBotToEvaluation (V : X.Opens) :
    IsIso (opensSupportBotToEvaluation V) := by
  have : ∀ G, IsIso ((opensSupportBotToEvaluation V).app G) := fun G => by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨Subtype.val_injective, fun s => ?_⟩
    have := subsingleton_etaleSections_bot G
    exact ⟨⟨s, AddMonoidHom.mem_ker.2 (Subsingleton.elim _ _)⟩, rfl⟩
  exact NatIso.isIso_of_isIso_app _

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  Stacks.EtaleCohomology.etaleContainsIdentities
  Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- **`Γ_{V,∅}` computes the étale cohomology of the open subscheme `V`**: the `i`-th right
derived functor of `Γ_{V,∅}` vanishes at `𝓕` exactly when `H^i(V, 𝓕|_V) = 0`. The derived
functors of sections over the object `V ⟶ X` of the small étale site are the cohomology of the
scheme `V` (`Stacks.EtaleCohomology.rightDerivedSectionsOverObjectIso`). -/
theorem subsingleton_sheafH_etaleRestriction_iff_isZero_rightDerived_opensSupport_bot
    (V : X.Opens) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} ((Stacks.EtaleCohomology.etaleRestriction.{u, 0} V.ι).obj F) i) ↔
      IsZero (((opensSupport (bot_le : (⊥ : X.Opens) ≤ V)).rightDerived i).obj F) := by
  let e₀ : opensSupport (bot_le : (⊥ : X.Opens) ≤ V) ≅
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op ((opensToEtale X).obj V)) :=
    asIso (opensSupportBotToEvaluation V)
  let e := (Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso e₀ i).app F ≪≫
    (Stacks.EtaleCohomology.rightDerivedSectionsOverObjectIso.{0} ((opensToEtale X).obj V) i).app F
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}]
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- **`Γ_{X,∅}` computes the étale cohomology of `X`**, the converse direction of
`AlgebraicGeometry.Scheme.subsingleton_sheafH_of_isZero_rightDerived_opensSupport_bot`: if
`H^i(X, 𝓕) = 0` then the `i`-th right derived functor of `Γ_{X,∅}` vanishes at `𝓕`. -/
theorem isZero_rightDerived_opensSupport_bot_top_of_subsingleton
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} F i)) :
    IsZero (((opensSupport (bot_le : (⊥ : X.Opens) ≤ ⊤)).rightDerived i).obj F) := by
  let e : opensSupport (bot_le : (⊥ : X.Opens) ≤ ⊤) ≅ Sheaf.Γ X.smallEtaleTopology
      AddCommGrpCat.{u + 1} :=
    asIso opensSupportBotToSections ≪≫
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (isTerminal_opensToEtale_top X)).symm
  exact ((Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
    _ _ _).1 h).of_iso ((Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso e i).app F)

/-- **The window `H^i(X) ⟶ H^i(U) ⟶ H^{i+1}_{X∖U}(X)` of the excision sequence.** For an open
`U ⊆ X`, if `R^iΓ_{X,∅}(𝓕) = 0` and `R^{i+1}Γ_{X,U}(𝓕) = 0` then `R^iΓ_{U,∅}(𝓕) = 0`: the
sequence `Γ_{X,U} ⟶ Γ_{X,∅} ⟶ Γ_{U,∅}` is short exact on injective sheaves, so its right derived
functors form a long exact sequence. -/
theorem isZero_rightDerived_opensSupport_bot_of_isZero {U : X.Opens}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ)
    (h₁ : IsZero (((opensSupport (bot_le : (⊥ : X.Opens) ≤ ⊤)).rightDerived i).obj F))
    (h₂ : IsZero (((opensSupport (le_top : U ≤ ⊤)).rightDerived (i + 1)).obj F)) :
    IsZero (((opensSupport (bot_le : (⊥ : X.Opens) ≤ U)).rightDerived i).obj F) := by
  have hE := exact_rightDerived_composableArrows₅
    (opensSupportRestrict (le_top : U ≤ ⊤) ((bot_le : (⊥ : X.Opens) ≤ U).trans le_top) le_rfl
      bot_le)
    (opensSupportRestrict ((bot_le : (⊥ : X.Opens) ≤ U).trans le_top) bot_le le_top le_rfl)
    (opensSupportRestrict_comp_eq_zero (bot_le : (⊥ : X.Opens) ≤ U) le_top)
    (fun I hI => by
      have := hI
      exact shortExact_opensSupport_of_injective (bot_le : (⊥ : X.Opens) ≤ U) le_top I)
    (injectiveResolution F) i
  exact (hE.exact 1).isZero_of_both_isZero h₁ h₂

/-- **The window of the excision sequence, on cohomology.** For an open `U ⊆ X` and `i ≥ 0`, if
`H^i(X, 𝓕) = 0` and `H^{i+1}_{X∖U}(X, 𝓕) = 0` then `H^i(U, 𝓕|_U) = 0`. -/
theorem subsingleton_sheafH_etaleRestriction_of_subsingleton_of_isZero (U : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ)
    (h₁ : Subsingleton (Sheaf.H.{u + 1} F i))
    (h₂ : IsZero (((opensSupport (le_top : U ≤ ⊤)).rightDerived (i + 1)).obj F)) :
    Subsingleton (Sheaf.H.{u + 1} ((Stacks.EtaleCohomology.etaleRestriction.{u, 0} U.ι).obj F) i) :=
  (subsingleton_sheafH_etaleRestriction_iff_isZero_rightDerived_opensSupport_bot U F i).2
    (isZero_rightDerived_opensSupport_bot_of_isZero F i
      (isZero_rightDerived_opensSupport_bot_top_of_subsingleton F i h₁) h₂)

end AlgebraicGeometry.Scheme

end
