module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformPunctual
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PunctualEtaleModule
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation

/-!
# A sheaf whose Fourier transform has no `H⁰` has no punctual subsheaf

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. Let `A` be a sheaf on `𝔸¹_k` with finite geometric stalks and `H⁰(Φ(A[0])) = 0`.
Then every punctual subsheaf `P ⊆ A` is zero.

The statements are made in the standard model `HasDerivedCategory.standard` of the derived
category, in which the Fourier transform is defined.

## Main results

* `Stacks.EtaleCohomology.fourierTransform_map_eq_zero_of_isPunctual`: for `P` punctual and
  `H⁰(Φ(A[0])) = 0`, every morphism `Φ(P[0]) ⟶ Φ(A[0])` is zero.
* `Stacks.EtaleCohomology.isZero_of_mono_of_isZero_homology_zero_fourierTransform`: a sheaf `A`
  with finite geometric stalks and `H⁰(Φ(A[0])) = 0` has no nonzero punctual subsheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- For `P` a punctual sheaf and `A` a sheaf with `H⁰(Φ(A[0])) = 0`, every morphism
`Φ(P[0]) ⟶ Φ(A[0])` is zero. -/
theorem fourierTransform_map_eq_zero_of_isPunctual (j : CompactificationOf (Over.mk 𝔸f))
    {P A : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (hP : IsPunctualEtaleModule Λ P)
    (hA : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A))))
    (f : (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj P) ⟶
      (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A)) :
    f = 0 := by
  obtain ⟨U, jU, _, _, h₃⟩ := hP
  have : ((fourierTransform k Λ ψ B p₀ j).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj P)).IsLE 0 :=
    (DerivedCategory.Plus.isLE_iff _ 0).2 fun i hi =>
      isZero_homology_fourierTransform_of_isZero_inverseImage k Λ ψ B p₀ j P jU h₃ i (by omega)
  have : ((fourierTransform k Λ ψ B p₀ j).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj A)).IsGE 1 :=
    (DerivedCategory.Plus.isGE_iff _ 1).2 fun i hi => by
      rcases lt_or_eq_of_le (show i ≤ 0 by omega) with h | rfl
      · exact isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j A i h
      · exact hA
  exact DerivedCategory.Plus.TStructure.t.zero f 0 1

/-- Let `ψ` be an additive character of `k` with `∑ ψ = 0`, with `#k` invertible in `Λ`. A sheaf
`A` with finite geometric stalks and `H⁰(Φ(A[0])) = 0` has no nonzero punctual subsheaf. -/
theorem isZero_of_mono_of_isZero_homology_zero_fourierTransform (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    {P A : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (ι : P ⟶ A) [Mono ι]
    (hP : IsPunctualEtaleModule Λ P)
    (hAf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj A)))
    (hA : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A)))) :
    IsZero P := by
  rw [IsZero.iff_id_eq_zero]
  exact eq_zero_of_fourierTransform_map_comp_mono_eq_zero k Λ ψ B p₀ hψ hq j jQ ι (𝟙 P) hAf
    (fourierTransform_map_eq_zero_of_isPunctual k Λ ψ B p₀ j hP hA _)

end Stacks.EtaleCohomology

end
