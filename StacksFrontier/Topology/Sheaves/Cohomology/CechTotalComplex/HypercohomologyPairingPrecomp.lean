module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupAdditivity
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupBoundaryTensor
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Pairings precomposed with morphisms of complexes

A pairing `γ : K^a ⊗ L^b ⟶ M^{a+b}` of complexes of coefficient presheaves, precomposed in the
first or in the second variable with a morphism of complexes, is again a pairing. On
hypercohomology the cup product of the precomposed pairing is the cup product of the given one
after the induced map: this is the naturality of the cup product
(`Stacks.Cech.Hypercohomology.cup_natural`) at an identity.

## Main definitions

* `Stacks.Cech.LinearCupProduct.ComplexPairing.precompLeft`,
  `Stacks.Cech.LinearCupProduct.ComplexPairing.precompRight`.

## Main results

* `Stacks.Cech.Hypercohomology.cup_precompLeft`, `Stacks.Cech.Hypercohomology.cup_precompRight`.
* `LinearMap.isPerfPair_of_linearEquiv`: perfectness is invariant under linear equivalences of
  the two factors.

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)

universe u

namespace LinearMap

/-- **Perfectness is invariant under linear equivalences of the two factors**: if
`P'(e₁ a, e₂ b) = P(a, b)` for linear equivalences `e₁`, `e₂` and `P'` is perfect, so is `P`. -/
theorem isPerfPair_of_linearEquiv {k M N M' N' : Type*} [Field k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup M'] [Module k M'] [AddCommGroup N']
    [Module k N'] (P : M →ₗ[k] N →ₗ[k] k) (P' : M' →ₗ[k] N' →ₗ[k] k) (e₁ : M ≃ₗ[k] M')
    (e₂ : N ≃ₗ[k] N') (h : ∀ a b, P' (e₁ a) (e₂ b) = P a b) (hP' : P'.IsPerfPair) :
    P.IsPerfPair := by
  have hP : P = (P'.compl₁₂ e₁.toLinearMap e₂.toLinearMap) :=
    LinearMap.ext₂ fun a b => (h a b).symm
  subst hP
  have := hP'
  infer_instance

/-- **Perfectness is invariant under additive bijections of the two factors, up to a unit**: if
`P'(e₁ a, e₂ b) = u · P(a, b)` for additive equivalences `e₁`, `e₂`, a unit `u` and `P'` is
perfect, so is `P`. The additive equivalences are then automatically linear, since `P'` is
nondegenerate. -/
theorem isPerfPair_of_addEquiv {k M N M' N' : Type*} [Field k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup M'] [Module k M'] [AddCommGroup N']
    [Module k N'] (P : M →ₗ[k] N →ₗ[k] k) (P' : M' →ₗ[k] N' →ₗ[k] k) (e₁ : M ≃+ M')
    (e₂ : N ≃+ N') (u : kˣ) (h : ∀ a b, P' (e₁ a) (e₂ b) = (u : k) * P a b)
    (hP' : P'.IsPerfPair) : P.IsPerfPair := by
  have h₁ : ∀ (c : k) (a : M), e₁ (c • a) = c • e₁ a := by
    intro c a
    refine hP'.bijective_left.1 (LinearMap.ext fun b' => ?_)
    obtain ⟨b, rfl⟩ := e₂.surjective b'
    simp only [h, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have h₂ : ∀ (c : k) (b : N), e₂ (c • b) = c • e₂ b := by
    intro c b
    refine hP'.bijective_right.1 (LinearMap.ext fun a' => ?_)
    obtain ⟨a, rfl⟩ := e₁.surjective a'
    simp only [LinearMap.flip_apply, h, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  refine isPerfPair_of_linearEquiv P P' (e₁.toLinearEquiv h₁)
    ((e₂.toLinearEquiv h₂).trans (LinearEquiv.smulOfUnit u⁻¹)) (fun a b => ?_) hP'
  show P' (e₁ a) ((u⁻¹ : kˣ) • e₂ b) = P a b
  rw [Units.smul_def, map_smul, smul_eq_mul, h, ← mul_assoc, Units.inv_mul, one_mul]

end LinearMap

namespace Stacks.Cech.LinearCupProduct

section Precomp

variable {C : Type*} [Category* C] {R : Type u} [CommRing R]
  {K K' L L' M : CochainComplex (PresheafModules.{u} C R) ℤ}

/-- **A pairing of complexes precomposed in its first variable** with a morphism of complexes. -/
noncomputable def ComplexPairing.precompLeft (D : ComplexPairing R K L M) (f : K' ⟶ K) :
    ComplexPairing R K' L M where
  μ a b n h := ((tensorPresheafModules.{u} R).map (f.f a)).app (L.X b) ≫ D.μ a b n h
  μ_d a b n h := by
    rw [Category.assoc, D.μ_d a b n h]
    simp only [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul]
    congr 1
    · rw [← Category.assoc, ← Category.assoc, ← NatTrans.comp_app, ← NatTrans.comp_app,
        ← Functor.map_comp, ← Functor.map_comp, f.comm]
    · rw [← Category.assoc, ← Category.assoc, NatTrans.naturality]

/-- The components of `D.precompLeft f` are those of `D` precomposed with the tensor product of
`f` with the identity. -/
theorem ComplexPairing.precompLeft_μ (D : ComplexPairing R K L M) (f : K' ⟶ K) (a b n : ℤ)
    (h : a + b = n) : (D.precompLeft f).μ a b n h =
      ((tensorPresheafModules.{u} R).map (f.f a)).app (L.X b) ≫ D.μ a b n h :=
  rfl

/-- **A pairing of complexes precomposed in its second variable** with a morphism of complexes. -/
noncomputable def ComplexPairing.precompRight (D : ComplexPairing R K L M) (g : L' ⟶ L) :
    ComplexPairing R K L' M where
  μ a b n h := ((tensorPresheafModules.{u} R).obj (K.X a)).map (g.f b) ≫ D.μ a b n h
  μ_d a b n h := by
    rw [Category.assoc, D.μ_d a b n h]
    simp only [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul]
    congr 1
    · rw [← Category.assoc, ← Category.assoc, NatTrans.naturality]
    · rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, g.comm]

/-- The components of `D.precompRight g` are those of `D` precomposed with the tensor product of
the identity with `g`. -/
theorem ComplexPairing.precompRight_μ (D : ComplexPairing R K L M) (g : L' ⟶ L) (a b n : ℤ)
    (h : a + b = n) : (D.precompRight g).μ a b n h =
      ((tensorPresheafModules.{u} R).obj (K.X a)).map (g.f b) ≫ D.μ a b n h :=
  rfl

end Precomp

end Stacks.Cech.LinearCupProduct

namespace Stacks.Cech.Hypercohomology

open Stacks.Cech.LinearCupProduct (ComplexPairing tensorPresheafModules)

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  {K K' L L' M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}

variable {O}

/-- A pairing of bounded below complexes precomposed in its first variable. -/
noncomputable abbrev Pairing.precompLeft (D : Pairing O K L M) (f : K' ⟶ K) : Pairing O K' L M :=
  ComplexPairing.precompLeft D ((Stacks.Cech.Refinement.sectionsComplex O).map f.hom)

/-- A pairing of bounded below complexes precomposed in its second variable. -/
noncomputable abbrev Pairing.precompRight (D : Pairing O K L M) (g : L' ⟶ L) : Pairing O K L' M :=
  ComplexPairing.precompRight D ((Stacks.Cech.Refinement.sectionsComplex O).map g.hom)

variable (O)

/-- The morphism `f`, together with the identities of `L` and `M`, is a morphism of pairings
from `D.precompLeft f` to `D`. -/
theorem pairingHom_precompLeft (D : Pairing O K L M) (f : K' ⟶ K) :
    PairingHom O f (𝟙 L) (𝟙 M) (D.precompLeft f) D := fun a b n h => by
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.comp_id,
    ObjectProperty.FullSubcategory.id_hom, Category.id_comp]
  rfl

/-- The morphism `g`, together with the identities of `K` and `M`, is a morphism of pairings
from `D.precompRight g` to `D`. -/
theorem pairingHom_precompRight (D : Pairing O K L M) (g : L' ⟶ L) :
    PairingHom O (𝟙 K) g (𝟙 M) (D.precompRight g) D := fun a b n h => by
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.comp_id,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.id_comp]
  rfl

/-- **The cup product of a pairing precomposed in its first variable** is the cup product after
the induced map. -/
theorem cup_precompLeft (hK : CechComputes O K) (hK' : CechComputes O K') (hL : CechComputes O L)
    (D : Pairing O K L M) (f : K' ⟶ K) (p q t : ℤ) (ht : p + q = t)
    (a : hypercohomology O K' p) (b : hypercohomology O L q) :
    cup O hK' hL (D.precompLeft f) p q t ht a b =
      cup O hK hL D p q t ht (hypercohomologyMap O f p a) b := by
  have := cup_natural O hK' hL hK hL f (𝟙 L) (𝟙 M) (D.precompLeft f) D
    (pairingHom_precompLeft O D f) p q t ht a b
  rwa [hypercohomologyMap_id, hypercohomologyMap_id] at this

/-- **The cup product of a pairing precomposed in its second variable** is the cup product after
the induced map. -/
theorem cup_precompRight (hK : CechComputes O K) (hL : CechComputes O L) (hL' : CechComputes O L')
    (D : Pairing O K L M) (g : L' ⟶ L) (p q t : ℤ) (ht : p + q = t)
    (a : hypercohomology O K p) (b : hypercohomology O L' q) :
    cup O hK hL' (D.precompRight g) p q t ht a b =
      cup O hK hL D p q t ht a (hypercohomologyMap O g q b) := by
  have := cup_natural O hK hL' hK hL (𝟙 K) g (𝟙 M) (D.precompRight g) D
    (pairingHom_precompRight O D g) p q t ht a b
  rwa [hypercohomologyMap_id, hypercohomologyMap_id] at this

/-- **The cup product of a pairing followed by a morphism of complexes** is the image of the cup
product. -/
theorem cup_comp (hK : CechComputes O K) (hL : CechComputes O L) {M' : CochainComplex.Plus
      (SheafOfModules.{u} (ringSheaf O))} (D : Pairing O K L M) (φ : M ⟶ M') (p q t : ℤ)
    (ht : p + q = t) (a : hypercohomology O K p) (b : hypercohomology O L q) :
    cup O hK hL (ComplexPairing.comp D ((Stacks.Cech.Refinement.sectionsComplex O).map φ.hom))
        p q t ht a b = hypercohomologyMap O φ t (cup O hK hL D p q t ht a b) := by
  have := cup_natural O hK hL hK hL (𝟙 K) (𝟙 L) φ D
    (ComplexPairing.comp D ((Stacks.Cech.Refinement.sectionsComplex O).map φ.hom))
    (fun a b n h => by
      simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f,
        ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.id_comp]
      rfl) p q t ht a b
  rw [hypercohomologyMap_id, hypercohomologyMap_id] at this
  exact this.symm

end Stacks.Cech.Hypercohomology

end
