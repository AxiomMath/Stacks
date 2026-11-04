module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.GradedNaturality

/-!
# A linear substitution in the homogeneous coordinates, and the morphism it moves

A change of basis of a module `V` with two bases indexed by `Fin (n + 1)` is a linear
substitution in the variables of `k[T₀, …, Tₙ]`: the composite
`k[T] ≅ Sym_k V ≅ k[T]` of the two coordinate isomorphisms of
`SymPow.gradedMvPolynomialHom`. That composite is a *graded* ring automorphism, so
`AlgebraicGeometry.Proj.map` of it is an automorphism of `Proj k[T₀, …, Tₙ]` — the linear
automorphism of projective space attached to the invertible matrix of the change of basis.

The point of this file is the identity that automorphism satisfies. If `s₀, …, sₙ` are global
sections of `𝒪_X` spanning the unit ideal and `s'₀, …, s'ₙ` is the family obtained from them by
the substitution, then the morphism `X ⟶ Proj k[T]` of `s'` is the morphism of `s` followed by
that automorphism. This is **the content that makes a condition on the morphism of a linear
system basis-independent**: see "What this is for" below.

## Main definitions

* `AlgebraicGeometry.basisChangeGradedHom`: **the graded ring automorphism of `k[T₀, …, Tₙ]`
  attached to a change of basis of `V`** — the linear substitution `Tᵢ ↦ ∑ⱼ aᵢⱼ Tⱼ` whose matrix
  is the change-of-basis matrix.

## Main results

* `AlgebraicGeometry.basisChangeGradedHom_X` and `…_C`: the substitution on the variables and on
  the constants.
* `AlgebraicGeometry.isIso_map_basisChangeGradedHom`: `Proj` of the substitution is an
  **automorphism of `Proj k[T₀, …, Tₙ]`**, inverse to the substitution of the two bases taken in
  the other order.
* `AlgebraicGeometry.map_basisChangeGradedHom_eq`: that automorphism is the conjugate, by the
  coordinate isomorphism `𝐏(V) ≅ Proj k[T]`, of the change-of-basis automorphism of `𝐏(V)`
  already built as `AlgebraicGeometry.basisChangeProjectiveSpaceIso`.
* `AlgebraicGeometry.fromOfGlobalSections_substitution`: **the identity.** The morphism
  `X ⟶ Proj k[T₀, …, Tₙ]` of the substituted family of sections is the morphism of the original
  family followed by the automorphism of projective space.

## What this is for

Hypothesis (3) of [Stacks, Tag 0FD6] is that the morphism `φ_{ℒ,ψ} : X → 𝐏(V)` of a linear
system is an immersion, and `𝐏(V)` and `φ_{ℒ,ψ}` are basis free. The repository can only state
the hypothesis at a chosen basis `b` of `V`
(`Stacks.Bertini.FamilyDivisors.IsImmersive`), and the basis enters twice. Through the
coordinate isomorphism of `𝐏(V)`, which is immaterial and was already shown immaterial
(`AlgebraicGeometry.isImmersion_toProjectiveSpaceOfModule_congr_basis`); and through the
*family* `sᵢ = ψ(vᵢ)`, where changing the basis replaces the family by an invertible linear
substitution of itself. The second occurrence is the one with content, and
`fromOfGlobalSections_substitution` is that content, for the morphism built directly out of a
ring homomorphism — equivalently, for a linear system on `𝒪_X` with a chosen trivialization,
which is the chart of the general construction.

The passage from the identity in this shape to the same identity for the *glued* morphism of
[Stacks, Tag 01ND] for a general invertible module is
`Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map`. Two steps separate them: the
glued morphism has to be read in the polynomial model over `k` rather than in the integral model
`ℙⁿ_ℤ` that `AlgebraicGeometry.projectiveSpaceOver` is a base change of
(`Stacks.ProjectiveSpaceChartRatio.ι_toPolynomialModel`), and the comparison of the two families
then has to be made over the *refined* cover by the intersections `X_{sᵢ} ⊓ X_{s'ⱼ}`, since a
substitution does not preserve the nonvanishing loci. That local comparison is
`Stacks.ProjectiveSpaceChartRatio.exists_unit_resOfLE_chartRatio_eq`, so the identity for the
glued morphism is unconditional
(`Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map_basisChangeGradedHom`); the
consequence for hypothesis (3) is `Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis`.

## Implementation notes

The substitution is built from the two coordinate isomorphisms rather than from a matrix,
because `SymPow.gradedMvPolynomialHom` and `SymPow.gradedMvPolynomialInv` are already
homomorphisms of *graded* rings: that a linear substitution carries homogeneous polynomials of
degree `d` to homogeneous polynomials of degree `d` is then not a separate proof. Nothing is
lost in generality: every invertible matrix over `k` is the change-of-basis matrix of two bases
of `k^{n+1}`.

`AlgebraicGeometry.Proj.map` is contravariant, so the substitution whose matrix expresses the
second basis in the first is `SymPow.gradedMvPolynomialHom b` after
`SymPow.gradedMvPolynomialInv b'`.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k V : Type u} [CommRing k] [AddCommGroup V] [Module k V] {n : ℕ}
  (b b' : Module.Basis (Fin (n + 1)) k V)

/-! ### The substitution -/

/-- **The graded ring automorphism of `k[T₀, …, Tₙ]` attached to a change of basis of `V`.**
Read through the coordinate isomorphisms of the two bases, the identity of `Sym_k V` is the
linear substitution `Tᵢ ↦ ∑ⱼ aᵢⱼ Tⱼ` whose matrix `a` expresses the second basis in the first
(`AlgebraicGeometry.basisChangeGradedHom_X`). -/
def basisChangeGradedHom :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k :=
  (SymPow.gradedMvPolynomialHom b).comp (SymPow.gradedMvPolynomialInv b')

/-- The substitution sends a polynomial `x` to the image under the coordinate isomorphism of `b`
of the element of `Sym_k V` whose coordinates in `b'` are `x`. -/
@[simp]
theorem basisChangeGradedHom_apply (x : MvPolynomial (Fin (n + 1)) k) :
    basisChangeGradedHom b b' x =
      SymmetricAlgebra.equivMvPolynomial b
        ((SymmetricAlgebra.equivMvPolynomial b').symm x) :=
  rfl

/-- **The substitution on the variables**: `Tᵢ` goes to the linear form whose coefficients are
the coordinates of the `i`-th vector of the second basis in the first. -/
theorem basisChangeGradedHom_X (i : Fin (n + 1)) :
    basisChangeGradedHom b b' (MvPolynomial.X i) =
      ∑ j, b.repr (b' i) j • MvPolynomial.X (R := k) j := by
  have h : SymmetricAlgebra.ι k V (b' i) =
      ∑ j, b.repr (b' i) j • SymmetricAlgebra.ι k V (b j) := by
    conv_lhs => rw [← b.sum_repr (b' i)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  rw [basisChangeGradedHom_apply, SymmetricAlgebra.equivMvPolynomial_symm_X, h, map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_smul, SymmetricAlgebra.equivMvPolynomial_ι_apply]

/-- The substitution fixes the constants: both coordinate isomorphisms are `k`-algebra maps. -/
theorem basisChangeGradedHom_C (a : k) :
    basisChangeGradedHom b b' (MvPolynomial.C a) = MvPolynomial.C a := by
  have h : (SymmetricAlgebra.equivMvPolynomial b').symm (MvPolynomial.C a) =
      algebraMap k (SymmetricAlgebra k V) a :=
    (SymmetricAlgebra.equivMvPolynomial b').symm_apply_eq.2
      (by rw [AlgEquiv.commutes, MvPolynomial.algebraMap_eq])
  rw [basisChangeGradedHom_apply, h, AlgEquiv.commutes, MvPolynomial.algebraMap_eq]

/-- The substitutions of two bases in the two orders are inverse to each other. -/
theorem basisChangeGradedHom_comp :
    (basisChangeGradedHom b b').comp (basisChangeGradedHom b' b) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) :=
  GradedRingHom.ext fun x => by
    rw [GradedRingHom.coe_comp, Function.comp_apply, basisChangeGradedHom_apply,
      basisChangeGradedHom_apply, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply]
    rfl

/-- The substitution satisfies Mathlib's hypothesis for `AlgebraicGeometry.Proj.map`. -/
theorem irrelevant_le_map_basisChangeGradedHom :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).map (basisChangeGradedHom b b') :=
  HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_gradedMvPolynomialInv b')
    (irrelevant_le_map_gradedMvPolynomialHom b)

/-- **`Proj` of the substitution is an automorphism of `Proj k[T₀, …, Tₙ]`**: the linear
automorphism of projective `n`-space attached to the invertible matrix of the change of
basis. -/
theorem isIso_map_basisChangeGradedHom :
    IsIso (Proj.map (basisChangeGradedHom b b')
      (irrelevant_le_map_basisChangeGradedHom b b')) :=
  Proj.isIso_map (irrelevant_le_map_basisChangeGradedHom b b')
    (irrelevant_le_map_basisChangeGradedHom b' b) (basisChangeGradedHom_comp b' b)
    (basisChangeGradedHom_comp b b')

/-- The inverse of `AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial` is `Proj` of
the coordinate isomorphism taken in the other direction. -/
theorem projectiveSpaceOfModuleIsoProjMvPolynomial_inv :
    (projectiveSpaceOfModuleIsoProjMvPolynomial b).inv =
      Proj.map (SymPow.gradedMvPolynomialHom b) (irrelevant_le_map_gradedMvPolynomialHom b) := by
  refine ((projectiveSpaceOfModuleIsoProjMvPolynomial b).hom_comp_eq_id).1 ?_ |>.symm
  rw [projectiveSpaceOfModuleIsoProjMvPolynomial_hom,
    ← Proj.map_comp (SymPow.gradedMvPolynomialHom b) (SymPow.gradedMvPolynomialInv b)
      (irrelevant_le_map_gradedMvPolynomialHom b) (irrelevant_le_map_gradedMvPolynomialInv b)]
  exact (Proj.map_congr (SymPow.gradedMvPolynomialInv_comp_hom b) _ (by simp)).trans Proj.map_id

/-- **The automorphism of `Proj k[T₀, …, Tₙ]` given by the substitution is the change-of-basis
automorphism of `𝐏(V)` read in coordinates.** The automorphism
`AlgebraicGeometry.basisChangeProjectiveSpaceIso` of `𝐏(V)` was free; this identifies it with
`Proj` of a graded automorphism of the polynomial ring, which is what makes it computable on the
morphism of a linear system. -/
theorem map_basisChangeGradedHom_eq :
    Proj.map (basisChangeGradedHom b b') (irrelevant_le_map_basisChangeGradedHom b b') =
      (projectiveSpaceOfModuleIsoProjMvPolynomial b).inv ≫
        (projectiveSpaceOfModuleIsoProjMvPolynomial b').hom := by
  rw [projectiveSpaceOfModuleIsoProjMvPolynomial_inv,
    projectiveSpaceOfModuleIsoProjMvPolynomial_hom,
    ← Proj.map_comp (SymPow.gradedMvPolynomialInv b') (SymPow.gradedMvPolynomialHom b)
      (irrelevant_le_map_gradedMvPolynomialInv b') (irrelevant_le_map_gradedMvPolynomialHom b)]
  rfl

/-! ### The identity -/

variable {X : Scheme.{u}}

/-- Substituting in the variables and then evaluating is evaluating at the substituted family. -/
theorem eval₂Hom_comp_basisChangeGradedHom (κ : k →+* Γ(X, ⊤))
    (s s' : Fin (n + 1) → Γ(X, ⊤)) (hss' : ∀ i, s' i = ∑ j, κ (b.repr (b' i) j) * s j) :
    (MvPolynomial.eval₂Hom κ s).comp (basisChangeGradedHom b b').toRingHom =
      MvPolynomial.eval₂Hom κ s' := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, GradedRingHom.coe_toRingHom, basisChangeGradedHom_C,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
  · rw [RingHom.comp_apply, GradedRingHom.coe_toRingHom, basisChangeGradedHom_X, map_sum,
      MvPolynomial.eval₂Hom_X', hss']
    exact Finset.sum_congr rfl fun j _ => by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X']

/-- **The identity.** Let `s₀, …, sₙ` be global sections of `𝒪_X` whose images of the irrelevant
ideal generate the unit ideal, and let `s'₀, …, s'ₙ` be obtained from them by the linear
substitution of a change of basis. Then the morphism `X ⟶ Proj k[T₀, …, Tₙ]` attached to `s'` is
the morphism attached to `s` followed by the linear automorphism of projective space the
substitution defines.

This is the geometric content that is missing for hypothesis (3) of [Stacks, Tag 0FD6] to be
stated on the intrinsic morphism `φ_{ℒ,ψ}`; see "What this is for" in the module docstring. -/
theorem fromOfGlobalSections_substitution (κ : k →+* Γ(X, ⊤))
    (s s' : Fin (n + 1) → Γ(X, ⊤)) (hss' : ∀ i, s' i = ∑ j, κ (b.repr (b' i) j) * s j)
    (hs : (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).toIdeal.map
      (MvPolynomial.eval₂Hom κ s) = ⊤)
    (hs' : (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).toIdeal.map
      (MvPolynomial.eval₂Hom κ s') = ⊤) :
    Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (MvPolynomial.eval₂Hom κ s') hs' =
      Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
          (MvPolynomial.eval₂Hom κ s) hs ≫
        Proj.map (basisChangeGradedHom b b') (irrelevant_le_map_basisChangeGradedHom b b') := by
  have he := eval₂Hom_comp_basisChangeGradedHom b b' κ s s' hss'
  have h2 : (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).toIdeal.map
        ((MvPolynomial.eval₂Hom κ s).comp (basisChangeGradedHom b b').toRingHom) = ⊤ := by
    rw [he]; exact hs'
  rw [Proj.fromOfGlobalSections_comp_map _ (irrelevant_le_map_basisChangeGradedHom b b')
    (MvPolynomial.eval₂Hom κ s) hs h2]
  exact Proj.fromOfGlobalSections_congr he.symm hs' h2

end AlgebraicGeometry

end
