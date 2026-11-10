module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# Extension by zero from a finite disjoint union of opens

Let `X` be a scheme, let `W_1, …, W_n` be pairwise disjoint opens of `X` with union `W`, and let
`ℱ` be a sheaf of `Λ`-modules on `X_étale`. Then
```
j_! (ℱ|_W) ≅ j_{1!} (ℱ|_{W_1}) ⊕ ⋯ ⊕ j_{n!} (ℱ|_{W_n}),
```
where `j : W ⟶ X` and `j_a : W_a ⟶ X` are the inclusions. This is the decomposition used in the
proof of Stacks 0GJI, where a dense open of a curve is shrunk to a disjoint union of irreducible
opens.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleBiproductToExtensionByZeroISup` — the canonical map from the
  direct sum to `j_!(ℱ|_W)`, whose `a`-th component is the comparison
  `Stacks.EtaleCohomology.etaleModuleCoverComparison` of `j_a` with `j`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroISupIso` — the resulting isomorphism.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleBiproductToExtensionByZeroISup` — the canonical map
  is an isomorphism.

## Implementation notes

Isomorphy is checked after inverse image along a family of morphisms whose images cover `X`
(`Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleInverseImage_family`): the inclusions of the
`W_b`, and the spectra of the residue fields at the points outside `W`. At a point outside `W`
both sides pull back to zero, since every extension by zero involved comes from an open missing
the point. Along `W_b ⟶ X` the summands with `a ≠ b` pull back to zero for the same reason, and
the `b`-th component pulls back to an isomorphism, because its composite with the counit of
`j_! ⊣ j^{-1}` is the counit of `j_{b!} ⊣ j_b^{-1}` and both counits become isomorphisms after
inverse image along `W_b ⟶ X`.

## References

* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] Abelian.hasFiniteBiproducts

section Biproduct

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {J : Type*} {f : J → C} [HasBiproduct f]

private theorem biproduct_total' [Fintype J] : ∑ j, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
  IsBilimit.total (biproduct.isBilimit f)

/-- An additive functor kills a finite biproduct all of whose summands it kills. -/
private theorem isZero_map_biproduct [Finite J] (h : ∀ a, IsZero (F.obj (f a))) :
    IsZero (F.obj (⨁ f)) := by
  have := Fintype.ofFinite J
  rw [IsZero.iff_id_eq_zero, ← F.map_id, ← biproduct_total', F.map_sum]
  exact Finset.sum_eq_zero fun a _ => by rw [F.map_comp, (h a).eq_zero_of_src (F.map _),
    comp_zero]

/-- If an additive functor kills every summand of a finite biproduct but the `b`-th one, then it
carries a map out of the biproduct to an isomorphism as soon as it does so for its `b`-th
component. -/
private theorem isIso_map_biproduct_desc [Finite J] {Y : C} (c : ∀ a, f a ⟶ Y) (b : J)
    (h : ∀ a, a ≠ b → IsZero (F.obj (f a))) (hb : IsIso (F.map (c b))) :
    IsIso (F.map (biproduct.desc c)) := by
  classical
  have := Fintype.ofFinite J
  have hι : IsIso (F.map (biproduct.ι f b)) := by
    refine ⟨F.map (biproduct.π f b), ?_, ?_⟩
    · rw [← F.map_comp, biproduct.ι_π_self, F.map_id]
    · rw [← F.map_comp, ← F.map_id]
      have htot := biproduct_total' (f := f)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at htot
      rw [← htot, F.map_add, F.map_sum, left_eq_add]
      exact Finset.sum_eq_zero fun a ha => by
        rw [F.map_comp, (h a (Finset.ne_of_mem_erase ha)).eq_zero_of_src (F.map _), comp_zero]
  have hcomp : F.map (biproduct.ι f b) ≫ F.map (biproduct.desc c) = F.map (c b) := by
    rw [← F.map_comp, biproduct.ι_desc]
  rw [← hcomp] at hb
  exact IsIso.of_isIso_comp_left (F.map (biproduct.ι f b)) (F.map (biproduct.desc c))

end Biproduct

variable (Λ : Type r) [Ring Λ] {X : Scheme.{u}} {ι : Type u} [Finite ι] (W : ι → X.Opens)

/-- The canonical map `⨁_a j_{a!}(ℱ|_{W_a}) ⟶ j_!(ℱ|_W)`, for opens `W_a` of `X` with union `W`:
its `a`-th component is the comparison of the extensions by zero along `W_a ⟶ X` and `W ⟶ X`. -/
def etaleModuleBiproductToExtensionByZeroISup (F : EtaleModules.{u, r} Λ X) :
    (⨁ fun a => (etaleModuleExtensionByZero.{u, r} Λ (W a).ι).obj
        ((etaleModuleRestriction.{u, r} Λ (W a).ι).obj F)) ⟶
      (etaleModuleExtensionByZero.{u, r} Λ (⨆ a, W a).ι).obj
        ((etaleModuleRestriction.{u, r} Λ (⨆ a, W a).ι).obj F) :=
  biproduct.desc fun a => (etaleModuleCoverComparison.{u, r} Λ (W a).ι (⨆ a, W a).ι
    (X.homOfLE (le_iSup W a)) (X.homOfLE_ι _)).app F

/-- **Extension by zero from a finite disjoint union of opens is the direct sum of the extensions
by zero from the pieces**: the canonical map `⨁_a j_{a!}(ℱ|_{W_a}) ⟶ j_!(ℱ|_W)` is an
isomorphism when the opens `W_a` are pairwise disjoint. -/
theorem isIso_etaleModuleBiproductToExtensionByZeroISup
    (hW : Pairwise fun a b => Disjoint (W a) (W b)) (F : EtaleModules.{u, r} Λ X) :
    IsIso (etaleModuleBiproductToExtensionByZeroISup Λ W F) := by
  classical
  have := Fintype.ofFinite ι
  let T : ι ⊕ {x : X // x ∉ ⨆ a, W a} → Scheme.{u} :=
    Sum.elim (fun a => (W a).toScheme) (fun x => Spec (X.residueField x.1))
  let g : ∀ s, T s ⟶ X := fun s => match s with
    | .inl a => (W a).ι
    | .inr x => X.fromSpecResidueField x.1
  refine isIso_of_isIso_etaleModuleInverseImage_family Λ g ?_ _ fun s => ?_
  · refine Set.eq_univ_of_forall fun y => ?_
    by_cases hy : y ∈ ⨆ a, W a
    · obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact Set.mem_iUnion.2 ⟨.inl a, ⟨⟨y, ha⟩, rfl⟩⟩
    · refine Set.mem_iUnion.2 ⟨.inr ⟨y, hy⟩, ?_⟩
      change y ∈ Set.range (X.fromSpecResidueField y)
      rw [range_fromSpecResidueField]
      rfl
  · rcases s with b | ⟨x, hx⟩
    · refine isIso_map_biproduct_desc _ _ b (fun a hab => ?_) ?_
      · refine isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ (W b).ι (W a).ι ?_ _
        rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
        have h : Disjoint (W b) (W a) := hW (Ne.symm hab)
        exact Set.disjoint_left.2 fun x hxb hxa => by
          simpa using h.le_bot (show x ∈ W b ⊓ W a from ⟨hxb, hxa⟩)
      · have h1 := isIso_etaleModuleInverseImage_map_counit_of_factors Λ (W b).ι (W b).ι (𝟙 _)
          (Category.id_comp _) F
        have h2 := isIso_etaleModuleInverseImage_map_counit_of_factors Λ (W b).ι (⨆ a, W a).ι
          (X.homOfLE (le_iSup W b)) (X.homOfLE_ι _) F
        have hc := etaleModuleCoverComparison_comp_counit Λ (W b).ι (⨆ a, W a).ι
          (X.homOfLE (le_iSup W b)) (X.homOfLE_ι _) F
        have h3 : IsIso ((etaleModuleInverseImage.{u, r} Λ (W b).ι).map
            ((etaleModuleCoverComparison.{u, r} Λ (W b).ι (⨆ a, W a).ι
              (X.homOfLE (le_iSup W b)) (X.homOfLE_ι _)).app F) ≫
            (etaleModuleInverseImage.{u, r} Λ (W b).ι).map
              ((etaleModuleExtensionByZeroAdj.{u, r} Λ (⨆ a, W a).ι).counit.app F)) := by
          rw [← Functor.map_comp, hc]
          exact h1
        exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 h3
    · have hdisj : ∀ (U : X.Opens), U ≤ ⨆ a, W a →
          Disjoint (Set.range (X.fromSpecResidueField x).base) (Set.range U.ι.base) := by
        intro U hU
        rw [range_fromSpecResidueField, Scheme.Opens.range_ι, Set.disjoint_singleton_left]
        exact fun h => hx (hU h)
      refine isIso_of_source_target_iso_zero _ (IsZero.isoZero ?_) (IsZero.isoZero ?_)
      · exact isZero_map_biproduct _ fun a =>
          isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ _ (W a).ι
            (hdisj _ (le_iSup W a)) _
      · exact isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ _ _
          (hdisj _ le_rfl) _

/-- **`j_!` over a finite disjoint union of opens is the direct sum.** For pairwise disjoint opens
`W_a` of `X` with union `W`, `j_!(ℱ|_W) ≅ ⨁_a j_{a!}(ℱ|_{W_a})`, the inverse of the canonical
map `Stacks.EtaleCohomology.etaleModuleBiproductToExtensionByZeroISup`. -/
def etaleModuleExtensionByZeroISupIso (hW : Pairwise fun a b => Disjoint (W a) (W b))
    (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleExtensionByZero.{u, r} Λ (⨆ a, W a).ι).obj
        ((etaleModuleRestriction.{u, r} Λ (⨆ a, W a).ι).obj F) ≅
      ⨁ fun a => (etaleModuleExtensionByZero.{u, r} Λ (W a).ι).obj
        ((etaleModuleRestriction.{u, r} Λ (W a).ι).obj F) :=
  have := isIso_etaleModuleBiproductToExtensionByZeroISup Λ W hW F
  (asIso (etaleModuleBiproductToExtensionByZeroISup Λ W F)).symm

end Stacks.EtaleCohomology

end
