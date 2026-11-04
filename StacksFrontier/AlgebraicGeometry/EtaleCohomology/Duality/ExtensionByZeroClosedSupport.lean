module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeLocality

/-!
# Extension by zero of a sheaf supported on a closed subset

Let `n : U ⟶ Y` be an open immersion and `P` a sheaf of `Λ`-modules on `U` which vanishes on
`U ∩ O` for an open `O ⊆ Y` with `U ∪ O = Y`; that is, `P` is supported on a subset of `U` which
is closed in `Y`. Then the inclusion `ε : n_! P ⟶ n_* P` is an isomorphism: it is one over `U`,
and over `O` both sides vanish (`(n_! P)|_O = (U ∩ O ⟶ O)_!(P|_{U ∩ O})` and
`(n_* P)|_O = (U ∩ O ⟶ O)_*(P|_{U ∩ O})`). Consequently a morphism `A ⟶ n_! P` is determined by its
restriction to `U`, and every morphism `A|_U ⟶ (n_! P)|_U` is such a restriction: restriction to
`U` is bijective on `Hom(A, n_! P)`.

## Main results

* `Stacks.EtaleCohomology.isZero_of_isZero_etaleModuleRestriction`: vanishing is étale local.
* `Stacks.EtaleCohomology.isIso_extensionByZeroToDirectImage_of_isZero`
* `Stacks.EtaleCohomology.bijective_etaleModuleRestriction_map_extensionByZero`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ZeroObject

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ]

/-- **Vanishing of a sheaf of modules is étale local.** -/
theorem isZero_of_isZero_etaleModuleRestriction {X : Scheme.{u}} {ι : Type*}
    {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ X) [∀ i, Etale (j i)]
    (hsurj : ∀ x : X, ∃ i, x ∈ Set.range (j i)) (F : EtaleModules.{u, 0} Λ X)
    (h : ∀ i, IsZero ((etaleModuleRestriction.{u, 0} Λ (j i)).obj F)) : IsZero F := by
  have hφ : IsIso (0 : F ⟶ 0) :=
    isIso_of_isIso_etaleRestrictionAt (0 : F ⟶ 0) j
      (coversTop_smallEtaleObj_of_jointlySurjective j hsurj) fun i =>
        have hB := Functor.map_isZero (etaleModuleRestriction.{u, 0} Λ (j i))
          (isZero_zero (EtaleModules.{u, 0} Λ X))
        ⟨⟨hB.to_ _, (h i).eq_of_src _ _, hB.eq_of_src _ _⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

section Support

variable {Y U O O' : Scheme.{u}} (n : U ⟶ Y) [IsOpenImmersion n] (m : O ⟶ Y) [IsOpenImmersion m]
  (c : O' ⟶ U) [IsOpenImmersion c] (c' : O' ⟶ O) (sq : IsPullback c' c m n)

include sq in
/-- The direct image `n_* P` vanishes on `O` when `P` vanishes on `U ∩ O`. -/
theorem isZero_restriction_directImage_of_isZero (P : EtaleModules.{u, 0} Λ U)
    (hP : IsZero ((etaleModuleRestriction.{u, 0} Λ c).obj P)) :
    IsZero ((etaleModuleRestriction.{u, 0} Λ m).obj ((etaleModuleDirectImage.{u, 0} Λ n).obj P)) :=
  (Functor.map_isZero (etaleModuleDirectImage.{u, 0} Λ c') hP).of_iso
    ((etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{u + 1} Λ) sq).app P).symm

include sq in
/-- The extension by zero `n_! P` vanishes on `O` when `P` vanishes on `U ∩ O`. -/
theorem isZero_restriction_extensionByZero_of_isZero (P : EtaleModules.{u, 0} Λ U)
    (hP : IsZero ((etaleModuleRestriction.{u, 0} Λ c).obj P)) :
    IsZero ((etaleModuleRestriction.{u, 0} Λ m).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ n).obj P)) := by
  have : Etale c' := MorphismProperty.of_isPullback (P := @Etale) sq.flip inferInstance
  have h₁ : IsZero ((etaleModuleInverseImage.{u, 0} Λ c).obj P) :=
    hP.of_iso ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ c).app P)
  have h₂ : IsZero ((etaleModuleInverseImage.{u, 0} Λ m).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ n).obj P)) :=
    (Functor.map_isZero (etaleModuleExtensionByZero.{u, 0} Λ c') h₁).of_iso
      ((etaleModuleInverseImageExtensionByZeroIso Λ sq.flip).app P).symm
  exact h₂.of_iso ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ m).app _).symm

include sq in
/-- **Extension by zero of a sheaf supported on a closed subset is direct image**: if `U ∪ O = Y`
and `P` vanishes on `U ∩ O`, then `ε : n_! P ⟶ n_* P` is an isomorphism. -/
theorem isIso_extensionByZeroToDirectImage_of_isZero
    (hcov : ∀ y : Y, y ∈ Set.range n.base ∨ y ∈ Set.range m.base) (P : EtaleModules.{u, 0} Λ U)
    (hP : IsZero ((etaleModuleRestriction.{u, 0} Λ c).obj P)) :
    IsIso ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ n).app P) := by
  let S : Bool → Scheme.{u} := fun b => match b with
    | true => U
    | false => O
  let j : ∀ b, S b ⟶ Y := fun b => match b with
    | true => n
    | false => m
  have : ∀ b, Etale (j b) := fun b => by cases b <;> (dsimp [j]; infer_instance)
  refine isIso_of_isIso_etaleRestrictionAt _ j
    (coversTop_smallEtaleObj_of_jointlySurjective j fun y => ?_) fun b => ?_
  · exact (hcov y).elim (fun h => ⟨true, h⟩) fun h => ⟨false, h⟩
  · cases b
    · have hA := isZero_restriction_extensionByZero_of_isZero Λ n m c c' sq P hP
      have hB := isZero_restriction_directImage_of_isZero Λ n m c c' sq P hP
      exact ⟨⟨hB.to_ _, hA.eq_of_src _ _, hB.eq_of_src _ _⟩⟩
    · exact isIso_etaleModuleRestriction_map_extensionByZeroToDirectImage Λ n P

/-- **Restriction to `U` is bijective on maps into `n_! P`** when `ε : n_! P ⟶ n_* P` is an
isomorphism. -/
theorem bijective_etaleModuleRestriction_map_extensionByZero (A : EtaleModules.{u, 0} Λ Y)
    (P : EtaleModules.{u, 0} Λ U)
    [IsIso ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ n).app P)] :
    Function.Bijective (fun z : A ⟶ (etaleModuleExtensionByZero.{u, 0} Λ n).obj P =>
      (etaleModuleRestriction.{u, 0} Λ n).map z) := by
  let ε := (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ n).app P
  let adj := etaleModuleRestrictionDirectImageAdj.{u, 0} Λ n
  have key : ∀ z : A ⟶ (etaleModuleExtensionByZero.{u, 0} Λ n).obj P,
      (etaleModuleRestriction.{u, 0} Λ n).map z =
        (adj.homEquiv _ _).symm (z ≫ ε) ≫ inv (adj.counit.app P) ≫
          inv ((etaleModuleRestriction.{u, 0} Λ n).map ε) := by
    intro z
    rw [Adjunction.homEquiv_counit, Category.assoc, IsIso.hom_inv_id_assoc, Functor.map_comp,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have h₁ : Function.Bijective fun w : (etaleModuleRestriction.{u, 0} Λ n).obj A ⟶ P =>
      w ≫ inv (adj.counit.app P) ≫ inv ((etaleModuleRestriction.{u, 0} Λ n).map ε) :=
    ⟨fun a b h => by simpa using congrArg (· ≫ (etaleModuleRestriction.{u, 0} Λ n).map ε ≫
        adj.counit.app P) h,
      fun w => ⟨w ≫ (etaleModuleRestriction.{u, 0} Λ n).map ε ≫ adj.counit.app P, by simp⟩⟩
  have h₂ : Function.Bijective fun z : A ⟶ (etaleModuleExtensionByZero.{u, 0} Λ n).obj P =>
      z ≫ ε :=
    ⟨fun a b h => by simpa using congrArg (· ≫ inv ε) h, fun w => ⟨w ≫ inv ε, by simp⟩⟩
  convert h₁.comp ((adj.homEquiv _ _).symm.bijective.comp h₂) using 1
  exact funext key

end Support

end Stacks.EtaleCohomology

end
