module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldSections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldSeparableSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite locally free morphisms and rational points over an algebraically closed field

## Main results

* `Stacks.Morphisms.surjective_of_isFiniteLocallyFreeOfRank`: a finite locally free morphism of
  positive rank is surjective.
* `Stacks.Morphisms.card_sections_of_etale_of_isAlgClosed`: an étale morphism to the spectrum of
  an algebraically closed field which is finite locally free of rank `d` has exactly `d`
  sections.
* `AlgebraicGeometry.exists_comp_eq_of_surjective_of_isAlgClosed`: a surjective morphism of
  schemes locally of finite type over an algebraically closed field `K` is surjective on
  `K`-rational points.
* `AlgebraicGeometry.cardinalMk_sections_le_of_isAlgClosed`: such a scheme has at most as many
  `K`-rational points as points.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Morphisms

/-- A finite locally free morphism of positive rank is surjective. -/
theorem surjective_of_isFiniteLocallyFreeOfRank {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ)
    (hr : r ≠ 0) [IsFiniteLocallyFreeOfRank f r] : Surjective f := by
  obtain ⟨hfin, hflat, hlfp⟩ := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    f).mp (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f r)
  have h := (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f r).mp ‹_›
  exact (Scheme.Hom.one_le_finrank_iff_surjective f).mp fun s => by
    simpa [h s] using Nat.one_le_iff_ne_zero.mpr hr

/-- **Sections over an algebraically closed field.** An étale morphism `f : Z ⟶ Spec K` which is
finite locally free of rank `d`, with `K` algebraically closed, has exactly `d` sections. -/
theorem card_sections_of_etale_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank f d) (hetale : Etale f) :
    Nat.card {σ : Spec (CommRingCat.of K) ⟶ Z // σ ≫ f = 𝟙 _} = d := by
  obtain ⟨hfinite, hle⟩ := finite_and_card_sections_le_of_isFiniteLocallyFreeOfRank f d hf
  refine le_antisymm hle ?_
  obtain ⟨K', _, _, _, _, σ, hσ, hσf⟩ :=
    exists_finiteSeparable_hom_of_etale_isFiniteLocallyFreeOfRank f d hf hetale
  let φ : CommRingCat.of K ⟶ CommRingCat.of K' := CommRingCat.ofHom (algebraMap K K')
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let τ : Fin d → {σ : Spec (CommRingCat.of K) ⟶ Z // σ ≫ f = 𝟙 _} := fun k =>
    ⟨Spec.map (inv φ) ≫ σ k, by
      rw [Category.assoc, hσf, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]⟩
  have hτ : Function.Injective τ := fun k l hkl =>
    hσ ((cancel_epi (Spec.map (inv φ))).mp (congrArg Subtype.val hkl))
  simpa using Nat.card_le_card_of_injective τ hτ

end Stacks.Morphisms

namespace AlgebraicGeometry

/-- **Rational points along a surjection.** Over an algebraically closed field `K`, a surjective
morphism `g : X ⟶ Y` of schemes locally of finite type over `K` is surjective on `K`-rational
points. -/
@[ega "IV 1.3.7" "special case"]
theorem exists_comp_eq_of_surjective_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of K)) (q : Y ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    [LocallyOfFiniteType q] (g : X ⟶ Y) (hg : g ≫ q = p) [Surjective g]
    (y : Spec (.of K) ⟶ Y) (hy : y ≫ q = 𝟙 _) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ ∧ x ≫ g = y := by
  have hpt : IsClosed ({y (IsLocalRing.closedPoint K)} : Set Y) :=
    ((pointEquivClosedPoint q) ⟨y, hy⟩).2
  obtain ⟨x₀, hx₀⟩ := g.surjective (y (IsLocalRing.closedPoint K))
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, hz, hzc'⟩ := nonempty_inter_closedPoints (Z := g ⁻¹' {y (IsLocalRing.closedPoint K)})
    ⟨x₀, hx₀⟩ (hpt.preimage g.continuous).isLocallyClosed
  have hzc : IsClosed ({z} : Set X) := hzc'
  refine ⟨pointOfClosedPoint p z hzc, pointOfClosedPoint_comp p z hzc, ?_⟩
  refine ext_of_apply_closedPoint_eq q ?_ hy ?_
  · rw [Category.assoc, hg, pointOfClosedPoint_comp]
  · change g (pointOfClosedPoint p z hzc (IsLocalRing.closedPoint K)) = _
    rw [pointOfClosedPoint_apply p z hzc (IsLocalRing.closedPoint K : Spec (.of K))]
    exact hz

/-- Over an algebraically closed field `K`, a `K`-rational point of a scheme locally of finite
type over `K` is determined by its image point, so there are at most as many rational points as
points. -/
theorem cardinalMk_sections_le_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    Cardinal.mk {σ : Spec (.of K) ⟶ X // σ ≫ f = 𝟙 _} ≤ Cardinal.mk X :=
  Cardinal.mk_le_of_injective (f := fun σ => ((pointEquivClosedPoint f σ : closedPoints X) : X))
    (Subtype.val_injective.comp (pointEquivClosedPoint f).injective)

end AlgebraicGeometry

end
