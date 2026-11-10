module

public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness

/-!
# An epimorphism of finite locally free sheaves of the same rank is an isomorphism

Let `X` be a scheme and `φ : ℳ ⟶ 𝒩` an epimorphism of finite locally free `𝒪_X`-modules of the
same rank `r`. Then `φ` is an isomorphism: on the stalk at a point `x` it is a surjective
`𝒪_{X,x}`-linear map between free modules of rank `r`, and a surjective endomorphism of a finite
module over a commutative ring is injective (Vasconcelos).

## Main results

* `AlgebraicGeometry.SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfRank`.
-/

@[expose] public section

open CategoryTheory Stacks.SheafOfModules.FlatShortExact

namespace AlgebraicGeometry.SheafOfModules

universe u

variable {X : Scheme.{u}}

/-- **An epimorphism between finite locally free sheaves of modules of the same rank is an
isomorphism.** -/
theorem isIso_of_epi_of_isFiniteLocallyFreeOfRank {M N : X.Modules} (φ : M ⟶ N) [Epi φ]
    (r : ℕ) [IsFiniteLocallyFreeOfRank.{u, u, u} M r]
    [IsFiniteLocallyFreeOfRank.{u, u, u} N r] : IsIso φ := by
  refine (isIso_iff_bijective_stalkMap (O := X.ringCatSheaf)
    (M := (M : SheafOfModules.{u} X.ringCatSheaf)) (N := N) φ).2 fun x => ?_
  have hs := (epi_iff_surjective_stalkMap (O := X.ringCatSheaf) φ).1 ‹Epi φ› x
  refine ⟨?_, hs⟩
  let := stalkModule (X := X.toRingedSpace) M x
  let := stalkModule (X := X.toRingedSpace) N x
  let g := stalkLinearMap (X := X.toRingedSpace) φ x
  change Function.Injective g
  change Function.Surjective g at hs
  obtain ⟨eM⟩ := nonempty_stalkLinearEquiv_fin M r x
  obtain ⟨eN⟩ := nonempty_stalkLinearEquiv_fin N r x
  have hinj := OrzechProperty.injective_of_surjective_endomorphism
    (eN.toLinearMap ∘ₗ g ∘ₗ eM.symm.toLinearMap)
    (eN.surjective.comp (hs.comp eM.symm.surjective))
  intro a b hab
  exact eM.injective (hinj (by simpa using congrArg eN hab))

end AlgebraicGeometry.SheafOfModules
