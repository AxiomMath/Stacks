module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.GeometricPointConservativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerGeneratorSheaf

/-!
# Inverse image to a closed subscheme of a morphism invertible on the stalks over it

A morphism `φ` of sheaves of `Λ`-modules on `U_étale` whose underlying morphism of abelian sheaves
is invertible on the stalks at the geometric points of `U` lying over `i(Z)`, for `i : Z ⟶ U`,
has invertible inverse image `i⁻¹ φ`
(`Stacks.EtaleCohomology.Purity.isIso_etaleModuleInverseImage_map_of_isIsoStalksOver`): the stalk
of `i⁻¹ φ` at a geometric point `z` of `Z` is the stalk of `φ` at `i ∘ z`, and stalks detect
isomorphisms ([Stacks, Tag 03PU]).

This turns the stalkwise form of cohomological purity over the divisor into the statement that
the purity maps become isomorphisms after `i⁻¹`, in the tower form of purity
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.Purity.isIso_etaleModuleInverseImage_map_of_isIsoStalksOver`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.Purity

variable (Λ : Type) [CommRing Λ] {Z U : Scheme.{u}} (i : Z ⟶ U)

/-- **`i⁻¹ φ` is an isomorphism when `φ` is invertible on the stalks over `i(Z)`.** -/
theorem isIso_etaleModuleInverseImage_map_of_isIsoStalksOver {F G : EtaleModules.{u, 0} Λ U}
    (φ : F ⟶ G) (h : IsIsoStalksOver (Set.range i.base) ((etaleModuleForgetAb.{u, 0} Λ U).map φ)) :
    IsIso ((etaleModuleInverseImage.{u, 0} Λ i).map φ) := by
  rw [← isIso_iff_of_reflects_iso _ (etaleModuleForgetAb.{u, 0} Λ Z),
    isIso_iff_forall_isIso_smallEtaleStalkAb]
  intro z
  have e₁ : etaleAbelianInverseImage.{u, 0} i ≅ smallEtalePullbackAb i :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange i)
        AddCommGrpCat.{u + 1} U.smallEtaleTopology Z.smallEtaleTopology).leftAdjointUniq
      ((smallEtaleBaseChange i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        U.smallEtaleTopology Z.smallEtaleTopology)
  have hz : Set.range (z.hom ≫ i).base ⊆ Set.range i.base := by
    rintro _ ⟨p, rfl⟩
    exact ⟨z.hom.base p, rfl⟩
  have h₀ := h (z.hom ≫ i) hz
  have h₁ : IsIso ((smallEtaleStalkAb z.hom).map
      ((smallEtalePullbackAb i).map ((etaleModuleForgetAb.{u, 0} Λ U).map φ))) :=
    (NatIso.isIso_map_iff (smallEtalePullbackStalkAbIso i z.hom) _).2 h₀
  have h₂ : IsIso ((smallEtaleStalkAb z.hom).map
      ((etaleAbelianInverseImage.{u, 0} i).map ((etaleModuleForgetAb.{u, 0} Λ U).map φ))) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight e₁ (smallEtaleStalkAb z.hom)) _).2 h₁
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (etaleModuleForgetInverseImageIso.{u, 0} Λ i) (smallEtaleStalkAb z.hom)) φ).1 h₂

end Stacks.EtaleCohomology.Purity

end
