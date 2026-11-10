module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.KeelMoriTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliFiniteTypeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.EtaleMorphismModuliSquare

/-!
# The moduli space of a stack with finite inertia is locally of finite type (Stacks 0DUX)

Let `p : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space, where the
inertia `I_𝒳 ⟶ 𝒳` is finite, `Y` is locally Noetherian and `p` is locally of finite type. For
the moduli space `f : 𝒳 ⟶ M` of the Keel–Mori theorem (Stacks 0DUT), `p` factors as `f`
followed by a unique morphism `M ⟶ Y`, and this morphism is locally of finite type.

The statement is made for every categorical moduli space `f : 𝒳 ⟶ M`. This covers the moduli
space of Stacks 0DUT, which is a uniform categorical moduli space, and loses nothing: a
categorical moduli space is unique up to unique isomorphism
(`AlgebraicGeometry.Stack.exists_iso_of_isCategoricalModuliSpace`).

The proof follows the source. The morphism `M ⟶ Y` comes from the universal property of `f`.
Stacks 0DUE gives a jointly surjective family of separated étale stabilizer preserving
1-morphisms `gᵢ : 𝒳ᵢ ⟶ 𝒳` from well-nigh affine stacks; by Stacks 0DUV the Keel–Mori moduli
spaces `Mᵢ` of the `𝒳ᵢ` map étale to a Keel–Mori moduli space of `𝒳`, hence to `M`. This
reduces the claim, étale locally on `M`, to the well-nigh affine case, which is the Artin–Tate
argument of the source
(`AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_wellNighAffine_etale_moduli_squares`).

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_isCategoricalModuliSpace_of_isFinite_inertia`:
  **Stacks 0DUX**.

## References

* [Stacks Project, Tag 0DUX](https://stacks.math.columbia.edu/tag/0DUX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DUX.** Let `p : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic
space such that the inertia `I_𝒳 ⟶ 𝒳` is finite, `Y` is locally Noetherian and `p` is locally
of finite type, and let `f : 𝒳 ⟶ M` be a categorical moduli space (for instance the moduli
space of Stacks 0DUT). Then `p` factors as `f` followed by a unique morphism `M ⟶ Y`, up to a
2-isomorphism, and that morphism `M ⟶ Y` is locally of finite type. -/
@[stacks 0DUX]
theorem isLocallyOfFiniteType_of_isCategoricalModuliSpace_of_isFinite_inertia
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (Y : AlgebraicSpaces B S hS)
    (hY : Space.HasEtaleLocalProperty B S hS Y.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (p : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hp : AlgebraicStacks.IsLocallyOfFiniteType B S hS p)
    (M : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : IsCategoricalModuliSpace B S hS M f.hom) :
    (∃! q : M ⟶ Y, Nonempty (f.hom ≫ (associatedMap B S hS q.hom).1 ≅ p.hom)) ∧
      ∀ q : M ⟶ Y, Nonempty (f.hom ≫ (associatedMap B S hS q.hom).1 ≅ p.hom) →
        Space.IsLocallyOfFiniteType B S hS q.hom := by
  refine ⟨hf Y p.hom, fun q hq => ?_⟩
  obtain ⟨ι, 𝒳ᵢ, g, hcov, hwna, hstab, hrep⟩ := exists_isWellNighAffine_etale_cover B S hS 𝒳 hI
  obtain ⟨M₀, f₀, hu₀, -, -, hUH₀⟩ :=
    exists_isUniformCategoricalModuliSpace_of_isFinite_inertia B S hS 𝒳 hI
  have hc₀ := isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS hu₀
  obtain ⟨e, he⟩ := exists_iso_of_isCategoricalModuliSpace B S hS hc₀ hf
  have hq₀ : Nonempty (f₀.hom ≫ (associatedMap B S hS (e.hom ≫ q).hom).1 ≅ p.hom) := by
    obtain ⟨η⟩ := hq
    refine ⟨?_⟩
    change f₀.hom ≫ (associatedMap B S hS (e.hom.hom ≫ q.hom)).1 ≅ p.hom
    rw [associatedMap_comp]
    exact (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso (eqToIso he) _ ≪≫ η
  have h₀ : Space.IsLocallyOfFiniteType B S hS (e.hom ≫ q).hom := by
    refine isLocallyOfFiniteType_of_wellNighAffine_etale_moduli_squares B S hS hY p hp f₀ hc₀
      hUH₀ (e.hom ≫ q) hq₀ 𝒳ᵢ hwna g (fun i => (hrep i).1) (fun i => (hrep i).2.2) hcov
      (fun i => ?_)
    obtain ⟨M₁, M', f₁, f', g', hcomm, hg', -, -, ⟨hu₁, -⟩, ⟨hu', -⟩⟩ :=
      exists_isTwoFibreProduct_keelMoriModuliSpace_of_isEtale_of_isSeparated B S hS (g i) hI
        (hrep i).2.2 (hrep i).2.1 (hstab i).2
    exact ⟨M₁, M', f₁, f', g', hcomm, hg', hu₁, hu'⟩
  have h := Space.isLocallyOfFiniteType_iso_hom_comp B S hS M.property M₀.property Y.property
    ((ObjectProperty.ι _).mapIso e.symm) (e.hom ≫ q).hom h₀
  convert h using 1
  change q.hom = e.inv.hom ≫ e.hom.hom ≫ q.hom
  rw [← Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
  rfl

end AlgebraicGeometry.Stack

end
