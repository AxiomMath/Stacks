module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence

/-!
# Restriction is bijective in all degrees once higher classes are effaceable

Let `i : Y ⟶ X` be a morphism of schemes and let `P` be a class of abelian sheaves on the small
étale site of `X` stable under quotients. Suppose

* restriction `H⁰(X, F) ⟶ H⁰(Y, i⁻¹F)` is bijective for every `F` in `P`;
* every class in `H^q(X, F)`, `q > 0`, `F` in `P`, dies in `H^q(X, F')` for some monomorphism
  `F ⟶ F'` with `F'` in `P`;
* every class in `H^q(Y, i⁻¹F)`, `q > 0`, `F` in `P`, dies in `H^q(Y, i⁻¹F')` for some
  monomorphism `F ⟶ F'` with `F'` in `P`.

Then restriction `H^q(X, F) ⟶ H^q(Y, i⁻¹F)` is bijective for every `q` and every `F` in `P`.

This is the induction of the proof of [Stacks, Tag 09ZI] (Gabber's affine analog of proper base
change), where `P` is the class of torsion sheaves, `i` is the inclusion of `Spec (A ⧸ I)` into
`Spec A` for a henselian pair `(A, I)`, the degree-zero input is [Stacks, Tag 09ZH], and the two
effaceability inputs are [Stacks, Tag 09ZE] applied with `Z = X` and with `Z = Spec (A ⧸ I)`.
The argument is formal: it compares the two long exact cohomology sequences of
`0 ⟶ F ⟶ F' ⟶ F'/F ⟶ 0`, using that restriction is a morphism of long exact sequences
(`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence`).

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_effaceable`

## References

* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Bijectivity of restriction in every degree from effaceability.** If `P` is stable under
quotients, restriction is bijective in degree zero on `P`, and positive-degree classes over `X`
and over `Y` of sheaves in `P` are effaced by monomorphisms into sheaves in `P`, then restriction
`H^q(X, F) ⟶ H^q(Y, i⁻¹F)` is bijective for every `q` and every `F` in `P`. -/
theorem bijective_etaleCohomologyRestrictionMap_of_effaceable
    (P : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (hquot : ∀ {F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (φ : F ⟶ F'),
      P F' → P (cokernel φ))
    (h0 : ∀ F, P F → Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i F 0))
    (heffX : ∀ F, P F → ∀ (q : ℕ), 0 < q → ∀ ξ : Sheaf.H.{w} F q,
      ∃ (F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (φ : F ⟶ F'),
        Mono φ ∧ P F' ∧ ξ.comp (Ext.mk₀ φ) (add_zero q) = 0)
    (heffY : ∀ F, P F → ∀ (q : ℕ), 0 < q →
      ∀ ξ : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} i).obj F) q,
      ∃ (F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (φ : F ⟶ F'),
        Mono φ ∧ P F' ∧
          ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map φ)) (add_zero q) = 0)
    (q : ℕ) : ∀ F, P F → Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i F q) := by
  induction q with
  | zero => exact h0
  | succ p ih =>
    intro F hF
    -- the short exact sequence attached to a monomorphism `F ⟶ F'`
    have hses : ∀ {F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (φ : F ⟶ F'),
        Mono φ → (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
      fun φ _ => ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel φ)) inferInstance inferInstance
    refine ⟨fun ξ₁ ξ₂ h => ?_, fun η => ?_⟩
    · -- injectivity: reduce to a class `ξ` with zero restriction
      suffices hinj : ∀ ξ : Sheaf.H.{w} F (p + 1),
          etaleCohomologyRestrictionMap.{u, v, w} i F (p + 1) ξ = 0 → ξ = 0 by
        exact sub_eq_zero.mp (hinj _ (by rw [map_sub, h, sub_self]))
      intro ξ hξ
      obtain ⟨F', φ, hφ, hF', hkill⟩ := heffX F hF (p + 1) (Nat.succ_pos p) ξ
      have hS := hses φ hφ
      set S := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
      obtain ⟨η, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS ξ hkill rfl
      have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)
      have hη : (etaleCohomologyRestrictionMap.{u, v, w} i (cokernel φ) p η).comp
          hS'.extClass rfl = 0 :=
        (etaleCohomologyRestrictionMap_comp_extClass i hS p (p + 1) rfl η).symm.trans hξ
      obtain ⟨ζ, hζ⟩ := Ext.covariant_sequence_exact₃ _ hS' _ rfl hη
      obtain ⟨ζ₀, rfl⟩ := (ih F' hF').2 ζ
      have hrest : etaleCohomologyRestrictionMap.{u, v, w} i (cokernel φ) p
          (η - ζ₀.comp (Ext.mk₀ S.g) (add_zero p)) = 0 := by
        rw [map_sub, etaleCohomologyRestrictionMap_comp_mk₀]
        exact sub_eq_zero.mpr hζ.symm
      have hzero := (ih (cokernel φ) (hquot φ hF')).1
        (hrest.trans (map_zero (etaleCohomologyRestrictionMap.{u, v, w} i (cokernel φ) p)).symm)
      rw [sub_eq_zero.mp hzero, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
        Ext.comp_zero]
    · -- surjectivity
      obtain ⟨F', φ, hφ, hF', hkill⟩ := heffY F hF (p + 1) (Nat.succ_pos p) η
      have hS := hses φ hφ
      have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)
      obtain ⟨θ, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS' η hkill rfl
      obtain ⟨θ₀, rfl⟩ := (ih (cokernel φ) (hquot φ hF')).2 θ
      exact ⟨θ₀.comp hS.extClass rfl, etaleCohomologyRestrictionMap_comp_extClass i hS p _ rfl θ₀⟩

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- **Effacement transported along a pushout.** If a class `ζ` of `i⁻¹G` dies along the inverse
image of a monomorphism `ι : G ⟶ G'`, then for any `φ : G ⟶ F` the image of `ζ` in the
cohomology of `i⁻¹F` dies along the inverse image of the pushout `F ⟶ G' ⊔_G F`, which is again a
monomorphism. This is the first reduction of the proof of [Stacks, Tag 09ZE]. -/
theorem effaces_pushout_inr {G F G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (φ : G ⟶ F) (ι : G ⟶ G') [Mono ι] (q : ℕ)
    (ζ : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} i).obj G) q)
    (hζ : ζ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map ι)) (add_zero q) = 0) :
    Mono (pushout.inr ι φ) ∧
      (ζ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map φ)) (add_zero q)).comp
        (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map (pushout.inr ι φ))) (add_zero q) = 0 := by
  refine ⟨inferInstance, ?_⟩
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp,
    ← pushout.condition, Functor.map_comp, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, hζ, Ext.zero_comp]

omit [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- **An effaced class of an injective sheaf is zero.** If `I` is injective, a class of `i⁻¹I` that
dies along the inverse image of a monomorphism `I ⟶ F'` is zero: the monomorphism has a
retraction. -/
theorem eq_zero_of_effaced_of_injective {I F' : Sheaf X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}} [Injective I] (ι : I ⟶ F') [Mono ι] (q : ℕ)
    (ξ : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} i).obj I) q)
    (hξ : ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map ι)) (add_zero q) = 0) :
    ξ = 0 := by
  calc ξ = ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map
        (ι ≫ Injective.factorThru (𝟙 I) ι))) (add_zero q) := by
          rw [Injective.comp_factorThru (𝟙 I) ι, CategoryTheory.Functor.map_id, Ext.comp_mk₀_id]
    _ = 0 := by
      rw [Functor.map_comp, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero, hξ,
        Ext.zero_comp]

end Stacks.EtaleCohomology
