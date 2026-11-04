module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyQcqsRestriction
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CohomologyVanishingTransport

/-!
# Cohomology classes dying after a field extension die over a finitely generated subalgebra

Let `k'/k` be a field extension, `X` a quasi-compact quasi-separated scheme over `k` and `G` an
abelian sheaf on `X_étale`. The base change `X_{k'}` is the limit of the base changes `X_A` to the
finitely generated `k`-subalgebras `A ⊆ k'`, with affine transition morphisms
(`AlgebraicGeometry.FieldExtensionDescent.baseChangeLimitCone`). By Stacks 09YQ for
quasi-compact quasi-separated levels, a class of `H^q(X, G)` which vanishes on `X_{k'}` already
vanishes on some `X_A`: this is the injectivity half of Stacks 03Q6 for the system of finitely
generated subalgebras of `k'`.

## Main results

* `Stacks.EtaleCohomology.LimitExt.exists_fg_restriction_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open AlgebraicGeometry.FieldExtensionDescent

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- Restriction along an isomorphism followed by a morphism kills what restriction along the
morphism kills. -/
theorem restriction_eq_zero_of_comp_isIso {X Y Z : Scheme.{u}} (e : Z ⟶ Y) [IsIso e]
    (f : Y ⟶ X) (ef : Z ⟶ X) (hef : ef = e ≫ f)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (ξ : Sheaf.H.{u + 1} G q) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} ef G q ξ = 0 ↔
      etaleCohomologyRestrictionMap.{u, 0, u + 1} f G q ξ = 0 := by
  rw [← restriction_restriction_eq_zero_iff f e ef hef]
  exact ⟨fun h => (bijective_etaleCohomologyRestrictionMap_of_isIso e _ q).1
    (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

/-- **Classes dying after a field extension die over a finitely generated subalgebra**
(the injectivity half of Stacks 03Q6 for the system of finitely generated subalgebras of `k'`).
Let `k'/k` be a field extension, `X` a quasi-compact quasi-separated scheme over `k`, `G` an
abelian sheaf on `X_étale` and `c ∈ H^q(X, G)`. If `c` restricts to zero on `X_{k'}`, then it
restricts to zero on `X ×_k Spec A` for some finitely generated `k`-subalgebra `A ⊆ k'`. -/
theorem exists_fg_restriction_eq_zero (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (π : X ⟶ Spec (.of k))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (c : Sheaf.H.{u + 1} G q)
    (hc : etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π) G q c = 0) :
    ∃ A : Subalgebra k k', A.FG ∧ etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k A)))) G q c = 0 := by
  let D := baseChangeDiagram k k' π
  let L := baseChangeLimitCone k k' π
  let i₀ : FGSubalgebra k k' := ⟨⊥, Subalgebra.fg_bot⟩
  -- the projection of a stage to `X`, and its compatibility with the system
  let p : ∀ i : (FGSubalgebra k k')ᵒᵖ, D.obj i ⟶ X := fun i => pullback.snd _ π
  have hpD : ∀ {i j : (FGSubalgebra k k')ᵒᵖ} (g : i ⟶ j), D.map g ≫ p j = p i := fun g =>
    Over.w ((Over.pullback π).map ((specDiagram k k').map g))
  have hpL : ∀ i, L.cone.π.app i ≫ p i = pullback.snd (Spec.map (CommRingCat.ofHom
      (algebraMap k k'))) π := fun i =>
    Over.w (((Over.pullback π).mapCone (specLimitCone k k').cone).π.app i)
  -- the class pulled back to the least stage
  let ξ := etaleCohomologyRestrictionMap.{u, 0, u + 1} (p (op i₀)) G q c
  have hξ : etaleCohomologyRestrictionMap.{u, 0, u + 1} (L.cone.π.app (op i₀)) _ q ξ = 0 :=
    (restriction_restriction_eq_zero_iff _ _ _ (hpL (op i₀)).symm G q c).2
      ((restriction_eq_zero_of_comp_isIso (pullbackSymmetry _ _).hom (scalarExtensionFst k k' π)
        _ (pullbackSymmetry_hom_comp_fst _ _).symm G q c).2 hc)
  obtain ⟨i, h, hi⟩ := exists_le_restriction_eq_zero_of_qcqs D L.cone L.isLimit i₀ _ q ξ hξ
  exact ⟨i.1, i.2, (restriction_eq_zero_of_comp_isIso (pullbackSymmetry _ _).hom (p (op i)) _
    (pullbackSymmetry_hom_comp_snd _ _).symm G q c).2
      ((restriction_restriction_eq_zero_iff _ _ _ (hpD (homOfLE h).op).symm G q c).1 hi)⟩

end Stacks.EtaleCohomology.LimitExt
