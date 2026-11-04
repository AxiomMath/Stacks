module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.FibrePowerPermutation
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PicardData

/-!
# The norm along a group action as the sum of translates

Let `π : P ⟶ Q` be a finite morphism of schemes with a norm `N` on functions of degree `d`
(`Stacks.Norm.MorphismNorm`), and let `a : G → (P ⟶ P)` be a family of endomorphisms of `P` indexed
by a finite type `G`. This file defines the property

  `π^*(Norm_π ℒ) = ∑_{σ ∈ G} (a σ)^*ℒ`   in   `Pic(P)`,   for every invertible `𝒪_P`-module `ℒ`,

where `Norm_π ℒ` is the norm `Stacks.Divisors.normInvertible` of an invertible module, and derives
from it the formula `π^*(Norm_π ℒ_{i₀}) = (n-1)! • ∑ᵢ [ℒᵢ]` of Stacks 0FH9 on the `n`-fold fibre
power with its permutation action.

## Main definitions

* `Stacks.Divisors.HasNormGroupProductPullback`: `π^*(Norm_π ℒ) = ∑_{σ ∈ G} (a σ)^*ℒ` in `Pic(P)`
  for every invertible `ℒ` on `P`.

## Main results

* `Stacks.SheafOfModules.sum_pullbackPicardClass_eq_card_nsmul_of_comp_eq`: if `a σ ≫ π = π` for
  every `σ`, then `∑_{σ ∈ G} (a σ)^*(π^*𝒩) = #G • π^*𝒩` in `Pic(P)`.
* `Stacks.Divisors.pullbackPicardClass_normInvertible_modulePullback_eq_card_nsmul`: under
  `HasNormGroupProductPullback` and `a σ ≫ π = π` for every `σ`,
  `π^*(Norm_π(π^*𝒩)) = #G • π^*𝒩` in `Pic(P)`.
* `Stacks.SheafOfModules.pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum`:
  on the fibre power `Yⁿ`, `π^*(Norm_π ℒ_{i₀}) = (n-1)! • ∑ᵢ [ℒᵢ]` for a family `ℒᵢ` whose class
  is `prᵢ^*[ℒ]`.
* `pullbackPicardClass_normInvertible_fibrePowerPullback_eq_factorial_nsmul_sum`, in the same
  namespace: the same formula for the family `ℒᵢ = prᵢ^*ℒ`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0BCX](https://stacks.math.columbia.edu/tag/0BCX)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Nat RingedSpaceModuleAdjunction
open Stacks.SheafOfModules
open Stacks.Norm (MorphismNorm MorphismNormMap)

universe u

namespace Stacks.SheafOfModules

/-! ### Sums of translates for an action over the target -/

/-- If each `a σ` is a morphism over `π`, that is `a σ ≫ π = π`, then the translates of a module
pulled back from the target all have the same class:

  `∑_{σ ∈ G} (a σ)^*(π^*𝒩) = #G • π^*𝒩`   in   `Pic(P)`. -/
theorem sum_pullbackPicardClass_eq_card_nsmul_of_comp_eq {P Q : Scheme.{u}} (π : P ⟶ Q)
    {G : Type*} [Fintype G] (a : G → (P ⟶ P)) (hinv : ∀ σ, a σ ≫ π = π)
    (N : SheafOfModules.{u} (structureSheafRing Q.toRingedSpace))
    (hN : IsInvertible Q.presheaf Q.ringCatIsSheaf N)
    (h : IsInvertible P.presheaf P.ringCatIsSheaf
      ((modulePullback π.toLRSHom.toShHom).obj N)) :
    ∑ σ : G, pullbackPicardClass (a σ) ((modulePullback π.toLRSHom.toShHom).obj N) h =
      Fintype.card G • pullbackPicardClass π N hN := by
  simp only [← pullbackPicardClass_comp _ π N hN h, hinv, Finset.sum_const, Finset.card_univ]

end Stacks.SheafOfModules

namespace Stacks.Divisors

/-! ### The norm as a sum of translates -/

/-- For a finite `π : P ⟶ Q` with a norm `N` on functions and a family `a : G → (P ⟶ P)` of
endomorphisms of the source indexed by a finite type, the pullback along `π` of the norm of every
invertible `𝒪_P`-module `ℒ` is the sum of its translates,

  `π^*(Norm_π ℒ) = ∑_{σ ∈ G} (a σ)^*ℒ`   in   `Pic(P)`,

where `Norm_π ℒ` is `Stacks.Divisors.normInvertible`. -/
def HasNormGroupProductPullback {P Q : Scheme.{u}} (π : P ⟶ Q) [IsFinite π] {d : ℕ}
    (N : MorphismNorm π d) {G : Type*} [Fintype G] (a : G → (P ⟶ P)) : Prop :=
  ∀ (L : SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (hL : IsInvertible P.presheaf P.ringCatIsSheaf L),
    pullbackPicardClass π (normInvertible π N.toMorphismNormMap L)
        (isInvertible_normInvertible π N.toMorphismNormMap L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL)) =
      ∑ σ : G, pullbackPicardClass (a σ) L hL

/-- If each `a σ` is a morphism over `π` and `HasNormGroupProductPullback π N a` holds, then for
every invertible `𝒪_Q`-module `𝒩`,

  `π^*(Norm_π(π^*𝒩)) = #G • π^*𝒩`   in   `Pic(P)`. -/
theorem pullbackPicardClass_normInvertible_modulePullback_eq_card_nsmul {P Q : Scheme.{u}}
    (π : P ⟶ Q) [IsFinite π] {d : ℕ} (N : MorphismNorm π d) {G : Type*} [Fintype G]
    (a : G → (P ⟶ P)) (hinv : ∀ σ, a σ ≫ π = π)
    (hhint : HasNormGroupProductPullback π N a)
    (M : SheafOfModules.{u} (structureSheafRing Q.toRingedSpace))
    (hM : IsInvertible Q.presheaf Q.ringCatIsSheaf M)
    (h : IsInvertible P.presheaf P.ringCatIsSheaf
      ((modulePullback π.toLRSHom.toShHom).obj M)) :
    pullbackPicardClass π
        (normInvertible π N.toMorphismNormMap ((modulePullback π.toLRSHom.toShHom).obj M))
        (isInvertible_normInvertible π N.toMorphismNormMap _
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π _ h)) =
      Fintype.card G • pullbackPicardClass π M hM :=
  (hhint _ h).trans (sum_pullbackPicardClass_eq_card_nsmul_of_comp_eq π a hinv M hM h)

end Stacks.Divisors

namespace Stacks.SheafOfModules

open Stacks.Scheme

/-! ### The formula on the fibre power -/

/-- On the `n`-fold fibre power `Yⁿ` with its permutation action, for a finite `π : Yⁿ ⟶ Q` with a
norm on functions satisfying `Stacks.Divisors.HasNormGroupProductPullback`, and for a family `ℒᵢ`
whose class is `prᵢ^*[ℒ]`,

  `π^*(Norm_π ℒ_{i₀}) = (n-1)! • ∑ᵢ [ℒᵢ]`   in   `Pic(Yⁿ)`,

which is `π^*𝒩 = (ℒ₁ ⊗ ⋯ ⊗ ℒₙ)^{⊗(n-1)!}` written additively. -/
theorem pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum {S : Scheme.{u}}
    (Y : Over S) {n : ℕ} {Q : Scheme.{u}}
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
    (hhint : Stacks.Divisors.HasNormGroupProductPullback π N
      fun σ : Equiv.Perm (Fin n) => (fibrePowerPerm Y n σ).left) :
    pullbackPicardClass π (Stacks.Divisors.normInvertible π N.toMorphismNormMap (L i₀))
        (Stacks.Divisors.isInvertible_normInvertible π N.toMorphismNormMap (L i₀)
          (Stacks.Divisors.hasTrivializingTargetCover_of_isFinite_of_isInvertible π (L i₀)
            (hL i₀))) =
      (n - 1)! • ∑ i, picardClass (∏ᶜ fun _ : Fin n => Y).left.presheaf
        (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i) (hL i) :=
  pullbackPicardClass_fibrePower_eq_factorial_nsmul_sum Y π i₀ M hM L hL hpull _ _
    (hhint (L i₀) (hL i₀))

/-- On the `n`-fold fibre power `Yⁿ` with its permutation action, for a finite `π : Yⁿ ⟶ Q` with a
norm on functions satisfying `Stacks.Divisors.HasNormGroupProductPullback`, and for an invertible
`ℒ` on `Y`,

  `π^*(Norm_π(pr_{i₀}^*ℒ)) = (n-1)! • ∑ᵢ [prᵢ^*ℒ]`   in   `Pic(Yⁿ)`. -/
theorem pullbackPicardClass_normInvertible_fibrePowerPullback_eq_factorial_nsmul_sum
    {S : Scheme.{u}} (Y : Over S) {n : ℕ} {Q : Scheme.{u}}
    (π : (∏ᶜ fun _ : Fin n => Y).left ⟶ Q) [IsFinite π] {d : ℕ} (N : MorphismNorm π d)
    (i₀ : Fin n)
    (M : SheafOfModules.{u} (structureSheafRing Y.left.toRingedSpace))
    (hM : IsInvertible Y.left.presheaf Y.left.ringCatIsSheaf M)
    (hpb : ∀ i : Fin n, IsInvertible (∏ᶜ fun _ : Fin n => Y).left.presheaf
      (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf
      ((modulePullback (Pi.π (fun _ : Fin n => Y) i).left.toLRSHom.toShHom).obj M))
    (hhint : Stacks.Divisors.HasNormGroupProductPullback π N
      fun σ : Equiv.Perm (Fin n) => (fibrePowerPerm Y n σ).left) :
    pullbackPicardClass π (Stacks.Divisors.normInvertible π N.toMorphismNormMap
          ((modulePullback (Pi.π (fun _ : Fin n => Y) i₀).left.toLRSHom.toShHom).obj M))
        (Stacks.Divisors.isInvertible_normInvertible π N.toMorphismNormMap _
          (Stacks.Divisors.hasTrivializingTargetCover_of_isFinite_of_isInvertible π _
            (hpb i₀))) =
      (n - 1)! • ∑ i, pullbackPicardClass (Pi.π (fun _ : Fin n => Y) i).left M hM :=
  pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum Y π N i₀ M hM
    (fun i ↦ (modulePullback (Pi.π (fun _ : Fin n ↦ Y) i).left.toLRSHom.toShHom).obj M) hpb
    (fun i ↦ pullbackPicardClass_eq_picardClass (Pi.π (fun _ : Fin n ↦ Y) i).left M hM (hpb i))
    hhint

end Stacks.SheafOfModules

end
