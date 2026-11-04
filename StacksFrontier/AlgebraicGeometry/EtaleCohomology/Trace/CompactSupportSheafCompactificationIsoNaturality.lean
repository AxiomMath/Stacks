module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportSheafFiniteness

/-!
# Changing the compactification of `Hⁱ_c(X_k̄, G)` is natural and Frobenius-equivariant

For a sheaf `G` of `Λ`-modules killed by a positive integer, the isomorphism
`Hⁱ_c(X_k̄, G)` through `j₁` `≅` through `j₂` of
`Stacks.EtaleCohomology.compactSupportSheafCohomologyCompactificationIso` ([Stacks, Tag 0ATU]) is
natural in `G` and commutes with the canonical geometric Frobenius `π_X^*`. This moves the
inclusion `H⁰_loc ⊆ H¹_c` of Weil II 1.8 ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)),
built on the levels with a compactification of a curve `W ⊇ V`, to a given compactification of
`V`.

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.

## Main results

* `Stacks.EtaleCohomology.compactSupportSheafCohomologyCompactificationIso_hom_naturality`
* `Stacks.EtaleCohomology.compactSupportSheafCohomologyCompactificationIso_hom_frobenius`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (j₁ j₂ : CompactificationOf (Over.mk f))

/-- Two squares pasted along an inverse; stated on variables. -/
private theorem paste_inv_hom {C : Type*} [Category* C] {a b d a' b' d' : C}
    (x : a ⟶ a') (y : b ⟶ b') (z : d ⟶ d') (e : b ≅ a) (e' : b' ≅ a') (g : b ⟶ d) (g' : b' ⟶ d')
    (h₁ : y ≫ e'.hom = e.hom ≫ x) (h₂ : y ≫ g' = g ≫ z) :
    x ≫ (e'.inv ≫ g') = (e.inv ≫ g) ≫ z := by
  have h₁' : x ≫ e'.inv = e.inv ≫ y := by
    rw [Iso.comp_inv_eq, Category.assoc, h₁, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h₁', h₂, Category.assoc]

/-- Every term of the single complex of a sheaf killed by `m > 0` is killed by some `m > 0`. -/
private theorem exists_nsmul_id_sheafSingleComplex_X {G : EtaleModules.{u, 0} Λ X} (m : ℕ)
    (hm : 0 < m) (h : m • 𝟙 G = 0) :
    ∀ n, ∃ m : ℕ, 0 < m ∧ m • 𝟙 (((sheafSingleComplex Λ).obj G).obj.X n) = 0 :=
  fun n => ⟨m, hm, nsmul_id_sheafSingleComplex_X G m h n⟩

/-- **Changing the compactification of `Hⁱ_c(X_k̄, -)` is natural in the sheaf.** -/
public theorem compactSupportSheafCohomologyCompactificationIso_hom_naturality
    {G G' : EtaleModules.{u, 0} Λ X} (g : G ⟶ G') (m : ℕ) (hm : 0 < m) (h : m • 𝟙 G = 0)
    (m' : ℕ) (hm' : 0 < m') (h' : m' • 𝟙 G' = 0) (i : ℤ) :
    (compactSupportSheafCohomology Λ f j₁ kbar i).map g ≫
        (compactSupportSheafCohomologyCompactificationIso Λ f kbar j₁ j₂ G' m' hm' h' i).hom =
      (compactSupportSheafCohomologyCompactificationIso Λ f kbar j₁ j₂ G m hm h i).hom ≫
        (compactSupportSheafCohomology Λ f j₂ kbar i).map g := by
  have hK := exists_nsmul_id_sheafSingleComplex_X Λ m hm h
  have hK' := exists_nsmul_id_sheafSingleComplex_X Λ m' hm' h'
  have hL := compactSupportFrobeniusCohomologyHomIso_hom_naturality Λ f
    (IsCofiltered.minToLeft j₁ j₂) kbar ((sheafSingleComplex Λ).map g) hK hK'
  have hR := compactSupportFrobeniusCohomologyHomIso_hom_naturality Λ f
    (IsCofiltered.minToRight j₁ j₂) kbar ((sheafSingleComplex Λ).map g) hK hK'
  dsimp only [compactSupportSheafCohomologyCompactificationIso, Functor.mapIso_hom, Iso.trans_hom,
    Iso.symm_hom, Functor.comp_map, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    canonicalCompactSupportFrobeniusNatTrans_app]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg _ (paste_inv_hom _ _ _ _ _ _ _ hL hR)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Changing the compactification of `Hⁱ_c(X_k̄, -)` commutes with `π_X^*`.** -/
public theorem compactSupportSheafCohomologyCompactificationIso_hom_frobenius
    (G : EtaleModules.{u, 0} Λ X) (m : ℕ) (hm : 0 < m) (h : m • 𝟙 G = 0) (i : ℤ) :
    (compactSupportSheafFrobenius Λ f j₁ kbar p q hcard i).app G ≫
        (compactSupportSheafCohomologyCompactificationIso Λ f kbar j₁ j₂ G m hm h i).hom =
      (compactSupportSheafCohomologyCompactificationIso Λ f kbar j₁ j₂ G m hm h i).hom ≫
        (compactSupportSheafFrobenius Λ f j₂ kbar p q hcard i).app G := by
  have hK := exists_nsmul_id_sheafSingleComplex_X Λ m hm h
  have hL := compactSupportFrobeniusCohomologyHomIso_hom_frobenius Λ f
    (IsCofiltered.minToLeft j₁ j₂) kbar p q hcard _ hK
  have hR := compactSupportFrobeniusCohomologyHomIso_hom_frobenius Λ f
    (IsCofiltered.minToRight j₁ j₂) kbar p q hcard _ hK
  show (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j₁ kbar p q hcard).app
          ((sheafSingleComplex Λ).obj G)) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((compactSupportFrobeniusCohomologyHomIso Λ f (IsCofiltered.minToLeft j₁ j₂) kbar _
            hK).inv ≫
          (compactSupportFrobeniusCohomologyHomIso Λ f (IsCofiltered.minToRight j₁ j₂) kbar _
            hK).hom) =
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((compactSupportFrobeniusCohomologyHomIso Λ f (IsCofiltered.minToLeft j₁ j₂) kbar _
            hK).inv ≫
          (compactSupportFrobeniusCohomologyHomIso Λ f (IsCofiltered.minToRight j₁ j₂) kbar _
            hK).hom) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j₂ kbar p q hcard).app
          ((sheafSingleComplex Λ).obj G))
  rw [← CategoryTheory.Functor.map_comp]
  exact (congrArg _ (paste_inv_hom _ _ _ _ _ _ _ hL hR)).trans
    (CategoryTheory.Functor.map_comp _ _ _)

end Stacks.EtaleCohomology
