module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteSupportRestriction

/-!
# Restriction of cohomology along a jointly surjective étale family

Two closure properties of the class of abelian étale sheaves on which restriction of cohomology
is surjective, used in the dévissage of Stacks 03SC (7) for a sheaf which is constant on the
members of a finite étale cover of a dense open.

* Restriction is surjective on a finite biproduct as soon as it is on each summand.
* For a finite family of morphisms `g a : T a ⟶ X` whose images cover `X`, the map from an abelian
  sheaf `G` to `⨁ₐ (g a)_* (g a)^{-1} G` assembled from the units is a monomorphism: its kernel
  dies after inverse image along every `g a`, because there each unit is split by the counit,
  and the `g a` jointly reflect isomorphisms
  (`Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianInverseImage_family`).

## Main results

* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_biproduct`
* `Stacks.EtaleCohomology.mono_biproductLift_unit_of_iUnion_range_eq_univ`

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

/-- Abelian sheaves on a small étale site have finite biproducts. -/
instance hasFiniteBiproducts_sheaf_smallEtale (X : Scheme.{u}) :
    HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **Restriction is surjective on a finite biproduct when it is on every summand.** -/
theorem surjective_etaleCohomologyRestrictionMap_biproduct {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {ι : Type} [Finite ι] (A : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : ∀ a, Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} i (A a) q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} i (⨁ A) q) := by
  have := Fintype.ofFinite ι
  intro y
  choose x hx using fun a => h a
    (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map (biproduct.π A a))) (add_zero q))
  refine ⟨∑ a, (x a).comp (Ext.mk₀ (biproduct.ι A a)) (add_zero q), ?_⟩
  rw [map_sum]
  simp_rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, 0, w}, hx,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp]
  rw [← Ext.comp_sum, ← Ext.mk₀_sum, ← Functor.map_sum]
  simp only [biproduct.total, CategoryTheory.Functor.map_id, Ext.comp_mk₀_id]

/-- **A jointly surjective finite family detects sections.** For a finite family of morphisms
`g a : T a ⟶ X` whose images cover `X`, the morphism `G ⟶ ⨁ₐ (g a)_* (g a)^{-1} G` whose components
are the units of the inverse-image/direct-image adjunctions is a monomorphism. -/
theorem mono_biproductLift_unit_of_iUnion_range_eq_univ {X : Scheme.{u}} {ι : Type} [Finite ι]
    {T : ι → Scheme.{u}} (g : ∀ a, T a ⟶ X) (hg : ⋃ a, Set.range (g a).base = Set.univ)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Mono (biproduct.lift fun a =>
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} (g a)).unit.app G) := by
  set φ := biproduct.lift fun a =>
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (g a)).unit.app G
  have hK (a : ι) : IsZero ((etaleAbelianInverseImage.{u, 0} (g a)).obj (kernel φ)) := by
    let L := etaleAbelianInverseImage.{u, 0} (g a)
    let ua := (etaleAbelianInverseImageDirectImageAdj.{u, 0} (g a)).unit.app G
    have e : kernel.ι φ ≫ ua = 0 := by
      rw [show ua = φ ≫ biproduct.π _ a by simp only [φ, ua, biproduct.lift_π],
        kernel.condition_assoc, zero_comp]
    have : IsSplitMono (L.map ua) :=
      ⟨⟨⟨(etaleAbelianInverseImageDirectImageAdj.{u, 0} (g a)).counit.app (L.obj G),
        (etaleAbelianInverseImageDirectImageAdj.{u, 0} (g a)).left_triangle_components G⟩⟩⟩
    exact IsZero.of_mono_eq_zero _ <| by
      rw [← cancel_mono (L.map ua), ← L.map_comp, e, L.map_zero, zero_comp]
  have hiso : IsIso (0 : kernel φ ⟶ kernel φ) :=
    isIso_of_isIso_etaleAbelianInverseImage_family.{u, 0} (ι := ULift.{u} ι)
      (fun a => g a.down)
      ((Equiv.ulift.surjective.iUnion_comp fun a => Set.range (g a).base).trans hg) _ fun a =>
      ⟨⟨0, (hK a.down).eq_of_src _ _, (hK a.down).eq_of_src _ _⟩⟩
  exact Preadditive.mono_of_kernel_zero ((IsZero.of_mono_zero _ (kernel φ)).eq_of_src _ _)

end Stacks.EtaleCohomology

end
