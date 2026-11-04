module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormGroupProduct
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorFamily

/-!
# The norm along a group action as a tensor product of translates

Let `π : P ⟶ Q` be a finite morphism of schemes with a norm on functions, and let
`a : G → (P ⟶ P)` be a family of endomorphisms of `P` indexed by a finite type `G`. This file
defines the property that for every invertible `𝒪_P`-module `ℒ` there is an isomorphism

  `π^*(Norm_π ℒ) ≅ ⨂_{σ ∈ G} (a σ)^*ℒ`,

the tensor product being `Stacks.SheafOfModules.schemeTensorList`, and shows that it implies the
identification `π^*(Norm_π ℒ) = ∑_{σ ∈ G} (a σ)^*ℒ` in `Pic(P)` of
`Stacks.Divisors.HasNormGroupProductPullback`.

## Main definitions

* `Stacks.Divisors.HasNormGroupProductTensor`: `π^*(Norm_π ℒ) ≅ ⨂_{σ ∈ G} (a σ)^*ℒ` for every
  invertible `ℒ` on `P`.

## Main results

* `Stacks.Divisors.hasNormGroupProductPullback_of_hasNormGroupProductTensor`: the isomorphism
  implies the identification of Picard classes.
* `pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum_of_tensor`, in
  `Stacks.SheafOfModules`: on the fibre power `Yⁿ`, `π^*(Norm_π ℒ_{i₀}) = (n-1)! • ∑ᵢ [ℒᵢ]` for a
  family `ℒᵢ` whose class is `prᵢ^*[ℒ]`, under `HasNormGroupProductTensor`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Nat RingedSpaceModuleAdjunction
open Stacks.SheafOfModules
open Stacks.Norm (MorphismNorm MorphismNormMap)

universe u

namespace Stacks.Divisors

/-- For a finite `π : P ⟶ Q` with a norm `N` on functions and a family `a : G → (P ⟶ P)` of
endomorphisms of the source indexed by a finite type, every invertible `𝒪_P`-module `ℒ` satisfies

  `π^*(Norm_π ℒ) ≅ ⨂_{σ ∈ G} (a σ)^*ℒ`,

the tensor product being taken over `Finset.univ.toList`. -/
def HasNormGroupProductTensor {P Q : Scheme.{u}} (π : P ⟶ Q) [IsFinite π] {d : ℕ}
    (N : MorphismNorm π d) {G : Type*} [Fintype G] (a : G → (P ⟶ P)) : Prop :=
  ∀ (L : SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (_ : IsInvertible P.presheaf P.ringCatIsSheaf L),
    Nonempty ((modulePullback π.toLRSHom.toShHom).obj (normInvertible π N.toMorphismNormMap L) ≅
      schemeTensorList P (fun σ : G => (modulePullback (a σ).toLRSHom.toShHom).obj L)
        Finset.univ.toList)

/-- `HasNormGroupProductTensor π N a` implies `HasNormGroupProductPullback π N a`: taking classes
in `Pic(P)` turns `π^*(Norm_π ℒ) ≅ ⨂_{σ ∈ G} (a σ)^*ℒ` into
`π^*(Norm_π ℒ) = ∑_{σ ∈ G} (a σ)^*ℒ`. -/
theorem hasNormGroupProductPullback_of_hasNormGroupProductTensor {P Q : Scheme.{u}} (π : P ⟶ Q)
    [IsFinite π] {d : ℕ} (N : MorphismNorm π d) {G : Type*} [Fintype G] (a : G → (P ⟶ P))
    (h : HasNormGroupProductTensor π N a) :
    HasNormGroupProductPullback π N a := by
  intro L hL
  have hpb : ∀ σ : G, IsInvertible P.presheaf P.ringCatIsSheaf
      ((modulePullback (a σ).toLRSHom.toShHom).obj L) :=
    fun σ ↦ Stacks.RingedSpace.modulePullback_isInvertible _ L
  have hnorm := isInvertible_normInvertible π N.toMorphismNormMap L
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL)
  have hnormpb : IsInvertible P.presheaf P.ringCatIsSheaf
      ((modulePullback π.toLRSHom.toShHom).obj (normInvertible π N.toMorphismNormMap L)) :=
    Stacks.RingedSpace.modulePullback_isInvertible _ _
  rw [pullbackPicardClass_eq_picardClass π _ hnorm hnormpb,
    (picardClass_eq_iff P.presheaf P.ringCatIsSheaf _ _ hnormpb
      (isInvertible_schemeTensorList P _ hpb Finset.univ.toList)).2 (h L hL),
    picardClass_schemeTensorList_toList P _ hpb Finset.univ]
  exact Finset.sum_congr rfl fun σ _ ↦ (pullbackPicardClass_eq_picardClass (a σ) L hL (hpb σ)).symm

end Stacks.Divisors

namespace Stacks.SheafOfModules

open Stacks.Scheme

/-- On the `n`-fold fibre power `Yⁿ` with its permutation action, for a finite `π : Yⁿ ⟶ Q` with a
norm on functions satisfying `Stacks.Divisors.HasNormGroupProductTensor`, and for a family `ℒᵢ`
whose class is `prᵢ^*[ℒ]`,

  `π^*(Norm_π ℒ_{i₀}) = (n-1)! • ∑ᵢ [ℒᵢ]`   in   `Pic(Yⁿ)`. -/
theorem pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum_of_tensor
    {S : Scheme.{u}} (Y : Over S) {n : ℕ} {Q : Scheme.{u}}
    (π : (∏ᶜ fun _ : Fin n => Y).left ⟶ Q) [IsFinite π] {d : ℕ} (N : MorphismNorm π d)
    (i₀ : Fin n)
    (M : SheafOfModules.{u} (structureSheafRing Y.left.toRingedSpace))
    (hM : IsInvertible Y.left.presheaf Y.left.ringCatIsSheaf M)
    (L : Fin n → SheafOfModules.{u}
      (structureSheafRing (∏ᶜ fun _ : Fin n => Y).left.toRingedSpace))
    (hL : ∀ i, IsInvertible (∏ᶜ fun _ : Fin n => Y).left.presheaf
      (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i))
    (hpull : ∀ i, pullbackPicardClass (Pi.π (fun _ : Fin n => Y) i).left M hM =
      picardClass (∏ᶜ fun _ : Fin n => Y).left.presheaf
        (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i) (hL i))
    (hhint : Stacks.Divisors.HasNormGroupProductTensor π N
      fun σ : Equiv.Perm (Fin n) => (fibrePowerPerm Y n σ).left) :
    pullbackPicardClass π (Stacks.Divisors.normInvertible π N.toMorphismNormMap (L i₀))
        (Stacks.Divisors.isInvertible_normInvertible π N.toMorphismNormMap (L i₀)
          (Stacks.Divisors.hasTrivializingTargetCover_of_isFinite_of_isInvertible π (L i₀)
            (hL i₀))) =
      (n - 1)! • ∑ i, picardClass (∏ᶜ fun _ : Fin n => Y).left.presheaf
        (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i) (hL i) :=
  pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum Y π N i₀ M hM L hL hpull
    (Stacks.Divisors.hasNormGroupProductPullback_of_hasNormGroupProductTensor π N _ hhint)

end Stacks.SheafOfModules

end
