module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperGeometricFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFilteredColimit
import StacksCore.Tactic.StacksAttribute

/-!
# Étale cohomology of a proper scheme after extending a separably closed field (Tag 0DDG)

Let `K/k` be an extension of separably closed fields, `X` a proper scheme over `k` and `F` a
torsion abelian sheaf on `X_étale`. Then restriction `H^q(X, F) ⟶ H^q(X_K, F|_{X_K})` is
bijective for every `q ≥ 0`. Unlike Tag 0A5E, no bound on the dimension of `X` is imposed.

The source deduces this from the proper base change theorem (Tag 095T) by looking at stalks. Here
the proper base change theorem enters only through a vanishing statement, so that no comparison
of maps is needed:

* **Degree zero.** Restriction is bijective on `H⁰` for every abelian sheaf
  (`etaleCohomologyRestrictionMap_zero_bijective_of_isSepClosed`, Tag 0A3I).
* **Injective `ℤ/ℓℤ`-modules restrict to acyclic sheaves.** For an injective sheaf `J` of
  `ℤ/ℓℤ`-modules on `X` (`ℓ > 0`), the geometric point `Spec K ⟶ Spec k` has geometric fibre
  `X_K`, so by Tag 0DDF (1), a consequence of Tag 095T,
  `Hⁿ(X_K, J|_{X_K}) ≅ (Rⁿ f_* J)_{Spec K}`, and `Rⁿ f_* J = 0` for `n > 0` (Tag 03FD).
* **Sheaves killed by a prime.** Such a sheaf embeds in the underlying sheaf of an injective
  sheaf of `ℤ/ℓℤ`-modules, which is acyclic on `X` (Tag 03FD) and on `X_K` (previous step), so
  dimension shifting (`bijective_etaleCohomologyRestrictionMap_of_effaceable`) gives bijectivity
  in every degree.
* **Sheaves killed by an integer** by dévissage along `0 → F[ℓ] → F → F/F[ℓ] → 0`
  (`etaleCohomologyRestrictionMap_bijective_of_nsmul_id_eq_zero`), and **torsion sheaves** as the
  filtered colimit of their `n!`-torsion subsheaves (`Stacks.Torsion.isIso_torsionFiltrationDesc`),
  since cohomology and restriction commute with filtered colimits on the quasi-compact
  quasi-separated schemes `X` and `X_K` (Tag 03Q5).

Finally bijectivity of the restriction map does not depend on the universe in which `Ext` is
computed (`etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt`).

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_scalarExtension_toSheaf_of_injective`
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_zsmul`
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_isProper`:
  **Tag 0DDG.**

## References

* [Stacks Project, Tag 0DDG](https://stacks.math.columbia.edu/tag/0DDG)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] hasExt_sheaf_smallEtale_succ

/-- Abelian sheaves on a small étale site, at the coefficients `AddCommGrpCat.{u + 1}`, form a
Grothendieck abelian category; this pins the coefficient universe of
`isGrothendieckAbelian_sheaf_smallEtale`. -/
local instance (priority := 2000) isGrothendieckAbelian_sheaf_smallEtale_succ (Z : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  isGrothendieckAbelian_sheaf_smallEtale.{u, 0} Z

/-- The stalk functor of a point of the small étale site is additive, being left exact. -/
local instance additive_sheafFiber_smallEtale_scalarExtension {Z : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{u + 1} Z.smallEtaleTopology) :
    (Φ.sheafFiber (A := AddCommGrpCat.{u + 1})).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosed k] [IsSepClosed K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

omit [IsSepClosed k] in
/-- **Injective `ℤ/ℓℤ`-modules stay acyclic after extending a separably closed field.** Let
`f : X ⟶ Spec k` be proper, `k ⊆ K` separably closed fields, `ℓ > 0` and `J` an injective sheaf
of `ℤ/ℓℤ`-modules on `X_étale`. Then `H^q(X_K, J|_{X_K}) = 0` for every `q > 0`: by Tag 0DDF (1)
at the geometric point `Spec K ⟶ Spec k`, whose geometric fibre is `X_K`, this group is the stalk
of `R^q f_* J`, and `J` has no higher direct images (Tag 03FD). -/
theorem subsingleton_H_scalarExtension_toSheaf_of_injective {ℓ : ℕ} (hℓ : 0 < ℓ)
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) [Injective J]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (scalarExtensionFst k K f)).obj ((SheafOfModules.toSheaf _).obj J)) q) := by
  set G := (SheafOfModules.toSheaf _).obj J
  have hG : ℓ • 𝟙 G = 0 := nsmul_id_toSheaf_eq_zero.{u, u + 1} ℓ J
  have hT := torsionSheafProperty_of_nsmul_id_eq_zero G ℓ hℓ hG
  have hR : IsZero (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj G) :=
    IsZero.of_iso
      (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective.{u, 0} f ℓ J
        q (by exact_mod_cast hq))
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
        (etaleAbelianDirectImage.{u, 0} f) (etaleAbelianDerivedDirectImage.{u, 0} f)
        (etaleAbelianDerivedDirectImageUnit.{u, 0} f)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective G q).symm
  let e := etaleAbelianSheafFiberRightDerivedDirectImageIsoOfIsProper f
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) G hT q
  have hS := (((pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).ulift.{u + 1}).sheafFiber
    (A := AddCommGrpCat.{u + 1})).map_isZero hR
  exact AddCommGrpCat.isZero_iff_subsingleton.1 (hS.of_iso e.symm)

/-- **Restriction to `X_K` is bijective on sheaves killed by `ℓ > 0`**, in every degree, for `X`
proper over the separably closed field `k` and `K/k` separably closed. Dimension shifting along
embeddings into underlying sheaves of injective `ℤ/ℓℤ`-modules, which are acyclic on `X`
(Tag 03FD) and on `X_K` (`subsingleton_H_scalarExtension_toSheaf_of_injective`); degree zero is
Tag 0A3I. -/
theorem bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_zsmul {ℓ : ℕ}
    (hℓ : 0 < ℓ) (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (ℓ : ℤ) • 𝟙 F = 0) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k K f) F q) := by
  let : Abelian (SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u + 1, u, u + 1, 0} _
  have : EnoughInjectives (SheafOfModules.{u + 1}
      (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u + 1, u} _
  -- an abelian sheaf killed by `ℓ` embeds in the underlying sheaf of an injective `ℤ/ℓℤ`-module
  have hemb : ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, (ℓ : ℤ) • 𝟙 G = 0 →
      ∃ (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ))
        (φ : G ⟶ (SheafOfModules.toSheaf _).obj J), Injective J ∧ Mono φ ∧
          (ℓ : ℤ) • 𝟙 ((SheafOfModules.toSheaf _).obj J) = 0 := by
    intro G hG
    have hG' : ∀ (V : X.Etaleᵒᵖ) (x : ToType (G.obj.obj V)), ℓ • x = 0 := fun V x ↦ by
      rw [← natCast_zsmul]
      exact (zsmul_id_eq_zero_iff G (ℓ : ℤ)).1 hG V x
    let M := torsionSheafToModules.{u + 1, u + 1} X.smallEtaleTopology ℓ G hG'
    exact ⟨Injective.under M, (torsionSheafToModulesIso.{u + 1, u + 1} X.smallEtaleTopology ℓ
      G hG').inv ≫ (SheafOfModules.toSheaf _).map (Injective.ι M), inferInstance, mono_comp _ _,
      by rw [natCast_zsmul]; exact nsmul_id_toSheaf_eq_zero.{u, u + 1} ℓ _⟩
  refine bijective_etaleCohomologyRestrictionMap_of_effaceable.{u, 0, u + 1}
    (scalarExtensionFst k K f) (fun G ↦ (ℓ : ℤ) • 𝟙 G = 0) ?_ ?_ ?_ ?_ q F hF
  · -- quotients of sheaves killed by `ℓ` are killed by `ℓ`
    intro G G' φ hG'
    rw [← cancel_epi (cokernel.π φ), Preadditive.comp_zsmul, Category.comp_id, comp_zero,
      ← Category.id_comp (cokernel.π φ), ← Preadditive.zsmul_comp, hG', zero_comp]
  · exact fun G _ ↦ etaleCohomologyRestrictionMap_zero_bijective_of_isSepClosed k K f G
  · -- effacement on `X`, by [Stacks, Tag 03FD]
    intro G hG q hq ξ
    obtain ⟨J, φ, hJ, hφ, hJ'⟩ := hemb G hG
    exact ⟨_, φ, hφ, hJ', (subsingleton_H_toSheaf_of_injective J q hq).elim _ _⟩
  · -- effacement on `X_K`, by proper base change
    intro G hG q hq ξ
    obtain ⟨J, φ, hJ, hφ, hJ'⟩ := hemb G hG
    exact ⟨_, φ, hφ, hJ',
      (subsingleton_H_scalarExtension_toSheaf_of_injective k K f hℓ J q hq).elim _ _⟩

/-- **Restriction to `X_K` is bijective on torsion sheaves**, with `Ext` in the universe `u + 1`:
a torsion sheaf is the filtered colimit of its `n!`-torsion subsheaves, restriction commutes with
filtered colimits on the quasi-compact quasi-separated schemes `X` and `X_K` (Tag 03Q5), and a
sheaf killed by `n!` is handled by dévissage to sheaves killed by a prime. -/
theorem bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_torsion
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k K f) F q) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace (scalarExtension k K f) := QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  have : QuasiSeparatedSpace (scalarExtension k K f) := quasiSeparatedSpace_of_quasiSeparated
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  let := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  have : IsIso (Stacks.Torsion.torsionFiltrationDesc X.smallEtaleTopology F) :=
    Stacks.Torsion.isIso_torsionFiltrationDesc _ F hF
  have hc : IsColimit (Cocone.mk F (Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F)) :=
    IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext (asIso (Stacks.Torsion.torsionFiltrationDesc X.smallEtaleTopology F))
        (fun j ↦ Stacks.Torsion.ι_torsionFiltrationDesc _ F j))
  refine bijective_etaleCohomologyRestrictionMap_of_isColimit hc _ q (fun n ↦ ?_)
  exact etaleCohomologyRestrictionMap_bijective_of_nsmul_id_eq_zero (scalarExtensionFst k K f)
    (fun p hp G hG r ↦ bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_zsmul
      k K f hp.pos r G (by rw [natCast_zsmul]; exact hG))
    (Nat.factorial n.down) (Nat.factorial_ne_zero _) _
    (nsmul_id_kernel_eq_zero F _) q

/-- **Stacks Project, Tag 0DDG.** Let `K/k` be an extension of separably closed fields, `X` a
proper scheme over `k` (`f : X ⟶ Spec k` proper) and `F` a torsion abelian sheaf on `X_étale`.
Then the restriction map `H^q_étale(X, F) ⟶ H^q_étale(X_K, F|_{X_K})` along the projection
`X_K = X ×_{Spec k} Spec K ⟶ X` is bijective for every `q ≥ 0`, with `Ext` computed in any
universe `w`. -/
@[stacks 0DDG]
theorem bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_isProper
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (scalarExtension k K f).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k K f) F q) :=
  (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, 0, w} _ F q).2
    ((etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, 0, u + 1} _ F q).1
      (bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_torsion k K f F hF q))

end Stacks.EtaleCohomology

end
