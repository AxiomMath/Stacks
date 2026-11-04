module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCompletionStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.CategoryTheory.Limits.UniqueLiftingAlongPullback
public import StacksFrontier.CategoryTheory.Limits.UniversalColimitPullback
public import StacksFrontier.CategoryTheory.Sites.FilteredUniversalColimit
public import StacksFrontier.RingTheory.Etale.Lifting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Unique lifting along universal homeomorphisms in the big fppf site

Let `S` be a scheme of a big fppf site. The topological invariance of the étale site
(Stacks 0BTY) says that along a universal homeomorphism `W ⟶ Z` of schemes, morphisms into a
scheme étale over `Z` lift uniquely from their base changes to `W`. This file reads that
statement in the big fppf category over `S` and in the sheaves on it.

## Main results

* `AlgebraicGeometry.FormalSpace.uniqueLiftingAlong_bigFppfOver`: unique lifting along a
  universal homeomorphism of objects of the site, into an object étale over the target.
* `AlgebraicGeometry.FormalSpace.uniqueLiftingAlong_sheafifiedYoneda`: the same for the sheaves
  represented by those objects.

The unique lifting is transported from `Stacks.Etale.existsUnique_hom_of_pullback_hom` along the
functors from the site to schemes and to sheaves.

## References

* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### Unique lifting along universal homeomorphisms -/

/-- **Stacks 0BTY, as unique lifting.** Along a universal homeomorphism of schemes `w`, morphisms
into a scheme étale over the target lift uniquely from base changes. -/
@[sga "3 VIIB 1.6.D" "partial, special case"]
theorem uniqueLiftingAlong_of_universalHomeomorphism {W Z X Y : Scheme.{u}} (w : W ⟶ Z)
    [UniversalHomeomorphism w] (p : X ⟶ Z) (q : Y ⟶ Z) [Etale q] :
    UniqueLiftingAlong w p q :=
  UniqueLiftingAlong.of_pullback fun φ hφ ↦ Stacks.Etale.existsUnique_hom_of_pullback_hom w p q φ hφ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of schemes between the underlying schemes of two objects of the big fppf site
over a third, compatible with the two structure morphisms to it, is a morphism of the site. -/
theorem exists_map_toScheme_eq {X Y Z : BigFppfOver B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (ψ : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hψ : ψ ≫ (BigFppfOver.toScheme B S hS).map q = (BigFppfOver.toScheme B S hS).map p) :
    ∃ m : X ⟶ Y, (BigFppfOver.toScheme B S hS).map m = ψ := by
  refine ⟨Over.homMk (ObjectProperty.homMk ψ) ?_, rfl⟩
  apply B.inclusion.map_injective
  have hq := congrArg B.inclusion.map (Over.w q)
  have hp := congrArg B.inclusion.map (Over.w p)
  rw [Functor.map_comp] at hq hp
  rw [Functor.map_comp, ← hq, ← hp, ← Category.assoc]
  exact congrArg (· ≫ B.inclusion.map Z.hom) hψ

/-- An isomorphism of underlying schemes over a third object of the site is an isomorphism of
objects of the site. -/
theorem exists_iso_toScheme_eq {X Y Z : BigFppfOver B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (μ : (BigFppfOver.toScheme B S hS).obj X ≅ (BigFppfOver.toScheme B S hS).obj Y)
    (hμ : μ.hom ≫ (BigFppfOver.toScheme B S hS).map q = (BigFppfOver.toScheme B S hS).map p) :
    ∃ m : X ≅ Y, m.hom ≫ q = p := by
  have hμ' : μ.inv ≫ (BigFppfOver.toScheme B S hS).map p =
      (BigFppfOver.toScheme B S hS).map q := by rw [← hμ, Iso.inv_hom_id_assoc]
  obtain ⟨a, ha⟩ := exists_map_toScheme_eq B S hS p q μ.hom hμ
  obtain ⟨b, hb⟩ := exists_map_toScheme_eq B S hS q p μ.inv hμ'
  refine ⟨⟨a, b, ?_, ?_⟩, ?_⟩ <;> apply (BigFppfOver.toScheme B S hS).map_injective
  · rw [Functor.map_comp, ha, hb, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  · rw [Functor.map_comp, ha, hb, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  · rw [Functor.map_comp, ha, hμ]

/-- **Stacks 0BTY in the big fppf site.** Let `w : W ⟶ Z` be a morphism of the site whose
underlying morphism of schemes is a universal homeomorphism, and let `q : Y ⟶ Z` be étale. Then
morphisms from any `p : X ⟶ Z` to `q` lift uniquely along `w`. -/
theorem uniqueLiftingAlong_bigFppfOver {W Z X Y : BigFppfOver B S hS} (w : W ⟶ Z)
    (p : X ⟶ Z) (q : Y ⟶ Z) (hw : UniversalHomeomorphism ((BigFppfOver.toScheme B S hS).map w))
    (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    UniqueLiftingAlong w p q := by
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  refine UniqueLiftingAlong.of_map (BigFppfOver.toScheme B S hS)
    (fun ψ hψ ↦ exists_map_toScheme_eq B S hS p q ψ hψ)
    (fun _ _ a p' b q' hX hY ↦ ⟨hX.map _, hY.map _⟩) ?_
  exact uniqueLiftingAlong_of_universalHomeomorphism _ _ _

/-- **Stacks 0BTY in the sheaves on the big fppf site.** Let `w : W ⟶ Z` be a morphism of the
site whose underlying morphism of schemes is a universal homeomorphism, and let `q : Y ⟶ Z` be
étale. Then, for the sheafified Yoneda embedding `h`, morphisms from `h p` to `h q` lift
uniquely along `h w`. -/
theorem uniqueLiftingAlong_sheafifiedYoneda {W Z X Y : BigFppfOver B S hS} (w : W ⟶ Z)
    (p : X ⟶ Z) (q : Y ⟶ Z) (hw : UniversalHomeomorphism ((BigFppfOver.toScheme B S hS).map w))
    (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    UniqueLiftingAlong ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map w)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  exact (uniqueLiftingAlong_bigFppfOver B S hS w p q hw hq).map _


end AlgebraicGeometry.FormalSpace

end
