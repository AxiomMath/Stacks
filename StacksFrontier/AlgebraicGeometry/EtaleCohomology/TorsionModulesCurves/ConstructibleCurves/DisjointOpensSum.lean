module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# Extension by zero from a finite disjoint union of opens

Let `j : V ⟶ X` be an open immersion whose image is the disjoint union of the images of finitely
many open immersions `jₐ : Uₐ ⟶ X`. Then for every sheaf `𝒦` of `Λ`-modules on `V_étale` the sheaf
`ℋ = j_! 𝒦` is the direct sum of the extensions by zero of its restrictions to the `Uₐ`:

`⨁ₐ jₐ! jₐ⁻¹ ℋ ≅ ℋ`.

This is the identity `j_!𝒢 = j_{1!}(𝒢|_{U_1}) ⊕ … ⊕ j_{n!}(𝒢|_{U_n})` in the proof of
[Stacks, Tag 0GJI].

## Main results

* `Stacks.EtaleCohomology.isIso_biproductDesc_counit_etaleModuleExtensionByZero` — the sum of the
  counits `jₐ! jₐ⁻¹ ℋ ⟶ ℋ` is an isomorphism.

## Implementation notes

The isomorphism is checked after inverse image along the jointly surjective family formed by the
`jₐ` and the points `Spec κ(x) ⟶ X` of the complement of the image of `j`
(`Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleInverseImage_family`). On `U_b` every summand
with `a ≠ b` restricts to zero and the counit of `j_b` restricts to an isomorphism; at a point
outside the image of `j` both sides restrict to zero.

## References

* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] Abelian.hasFiniteBiproducts

variable (Λ : Type r) [Ring Λ]

/-- In a finite biproduct whose other summands vanish, the inclusion of one summand is an
isomorphism. -/
theorem isIso_biproduct_ι_of_isZero_of_ne {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] {ι : Type} [Finite ι] (f : ι → C) (b : ι)
    (h : ∀ a, a ≠ b → IsZero (f a)) :
    IsIso (biproduct.ι f b) := by
  classical
  refine ⟨⟨biproduct.π f b, biproduct.ι_π_self f b, ?_⟩⟩
  refine biproduct.hom_ext _ _ fun a => ?_
  by_cases hab : a = b
  · subst hab
    simp
  · exact (h a hab).eq_of_tgt _ _

/-- The inverse image of a finite direct sum of sheaves of modules all of whose inverse images
vanish is zero: maps out of it correspond, by adjunction, to maps out of the direct sum into a
direct image, which are determined by their (vanishing) components. -/
theorem isZero_etaleModuleInverseImage_biproduct {T X : Scheme.{u}} (g : T ⟶ X)
    {ι : Type} [Finite ι] (D : ι → EtaleModules.{u, r} Λ X)
    (hD : ∀ a, IsZero ((etaleModuleInverseImage.{u, r} Λ g).obj (D a))) :
    IsZero ((etaleModuleInverseImage.{u, r} Λ g).obj (⨁ D)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((etaleModuleInverseImageAdj.{u, r} Λ g).homEquiv _ _).injective
  refine biproduct.hom_ext' _ _ fun a => ?_
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  exact congrArg _ ((hD a).eq_of_src _ _)

/-- **Extension by zero from a finite disjoint union of opens.** Let `j : V ⟶ X` be an open
immersion and `jₐ : Uₐ ⟶ X` finitely many open immersions with pairwise disjoint images whose
union is the image of `j`. For every sheaf `𝒦` of `Λ`-modules on `V_étale`, the sum of the
counits `jₐ! jₐ⁻¹ (j_! 𝒦) ⟶ j_! 𝒦` is an isomorphism `⨁ₐ jₐ! jₐ⁻¹ (j_! 𝒦) ≅ j_! 𝒦`. -/
theorem isIso_biproductDesc_counit_etaleModuleExtensionByZero {X V : Scheme.{u}}
    {ι : Type} [Finite ι] {U : ι → Scheme.{u}} (j : ∀ a, U a ⟶ X)
    [∀ a, IsOpenImmersion (j a)] (jV : V ⟶ X) [IsOpenImmersion jV]
    (hdisj : Pairwise fun a b => Disjoint (Set.range (j a).base) (Set.range (j b).base))
    (hcov : ⋃ a, Set.range (j a).base = Set.range jV.base) (K : EtaleModules.{u, r} Λ V) :
    IsIso (biproduct.desc fun a => (etaleModuleExtensionByZeroAdj.{u, r} Λ (j a)).counit.app
      ((etaleModuleExtensionByZero.{u, r} Λ jV).obj K)) := by
  classical
  set H := (etaleModuleExtensionByZero.{u, r} Λ jV).obj K
  set D := fun a => (etaleModuleExtensionByZero.{u, r} Λ (j a)).obj
    ((etaleModuleRestriction.{u, r} Λ (j a)).obj H)
  set φ : ⨁ D ⟶ H := biproduct.desc fun a =>
    (etaleModuleExtensionByZeroAdj.{u, r} Λ (j a)).counit.app H
  let Z := {x : X // x ∉ Set.range jV.base}
  let T : ULift.{u} ι ⊕ Z → Scheme.{u}
    | .inl a => U a.down
    | .inr x => Spec (X.residueField x.1)
  let g : ∀ c, T c ⟶ X
    | .inl a => j a.down
    | .inr x => X.fromSpecResidueField x.1
  refine isIso_of_isIso_etaleModuleInverseImage_family.{u, r} Λ g ?_ φ ?_
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    by_cases hx : x ∈ Set.range jV.base
    · rw [← hcov] at hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
      exact ⟨.inl ⟨a⟩, ha⟩
    · refine ⟨.inr ⟨x, hx⟩, ?_⟩
      change x ∈ Set.range (X.fromSpecResidueField x).base
      rw [Scheme.range_fromSpecResidueField]
      rfl
  rintro (⟨⟨b⟩⟩ | ⟨x, hx⟩)
  · change IsIso ((etaleModuleInverseImage.{u, r} Λ (j b)).map φ)
    refine (NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, r} Λ (j b)) φ).mpr ?_
    set R := etaleModuleRestriction.{u, r} Λ (j b)
    have hzero : ∀ a, a ≠ b → IsZero (R.obj (D a)) := fun a hab =>
      (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint.{u, r} Λ (j b) (j a)
        (hdisj (Ne.symm hab)) _).of_iso
          ((etaleModuleInverseImageRestrictionIso.{u, r} Λ (j b)).app (D a)).symm
    have hι : IsIso (R.map (biproduct.ι D b)) := by
      have := Functor.preservesFiniteBiproductsOfAdditive R
      have h1 := isIso_biproduct_ι_of_isZero_of_ne (fun a => R.obj (D a)) b hzero
      have h2 : R.map (biproduct.ι D b) =
          biproduct.ι (fun a => R.obj (D a)) b ≫ (R.mapBiproduct D).inv := by
        rw [Iso.eq_comp_inv]
        refine biproduct.hom_ext _ _ fun a => ?_
        simp only [Functor.mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← R.map_comp,
          biproduct.ι_π]
        by_cases hab : b = a
        · subst hab
          simp
        · simp [hab]
      rw [h2]
      infer_instance
    have hcomp : R.map (biproduct.ι D b) ≫ R.map φ =
        R.map ((etaleModuleExtensionByZeroAdj.{u, r} Λ (j b)).counit.app H) := by
      rw [← R.map_comp, biproduct.ι_desc]
    have hcounit := isIso_etaleModuleRestriction_map_counit.{u, r} Λ (j b) H
    rw [← hcomp] at hcounit
    exact IsIso.of_isIso_comp_left (R.map (biproduct.ι D b)) _
  · change IsIso ((etaleModuleInverseImage.{u, r} Λ (X.fromSpecResidueField x)).map φ)
    have hrange : Set.range (X.fromSpecResidueField x).base = {x} :=
      Scheme.range_fromSpecResidueField x
    have hV : Disjoint (Set.range (X.fromSpecResidueField x).base) (Set.range jV.base) := by
      rw [hrange, Set.disjoint_singleton_left]
      exact hx
    have hsrc : IsZero ((etaleModuleInverseImage.{u, r} Λ (X.fromSpecResidueField x)).obj
        (⨁ D)) := by
      refine isZero_etaleModuleInverseImage_biproduct Λ _ D fun a => ?_
      refine isZero_etaleModuleInverseImage_extensionByZero_of_disjoint.{u, r} Λ _ (j a) ?_ _
      rw [hrange, Set.disjoint_singleton_left]
      intro hxa
      exact hx (hcov ▸ Set.mem_iUnion.2 ⟨a, hxa⟩)
    have htgt := isZero_etaleModuleInverseImage_extensionByZero_of_disjoint.{u, r} Λ _ jV hV K
    exact ⟨⟨hsrc.from_ _, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩⟩

end Stacks.EtaleCohomology

end
