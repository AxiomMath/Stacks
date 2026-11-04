module

public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentQuasicoherent

/-!
# The sheaf of relative differentials is quasi-coherent

Let `f : X ⟶ S` be an arbitrary morphism of schemes. This file proves that the sheaf of
relative differentials `Ω_{X/S}` is a quasi-coherent sheaf of `𝒪_X`-modules, together with two
consequences for its pullback `a^*Ω_{X/S}` along a morphism `a : T ⟶ X`.

## Main results

* `Stacks.Smooth.isQuasicoherent_cotangentSheaf`: `Ω_{X/S}` is quasi-coherent.
* `Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf'`: `a^*Ω_{X/S}` is quasi-coherent for an
  arbitrary `a : T ⟶ X`.
* `Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'`: for `T` affine and
  `g : Γ(T, ⊤)`, the restriction map on sections of `a^*Ω_{X/S}` exhibits the sections over
  `T.basicOpen g` as the localization of the global sections away from `g`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Smooth

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X)

/-- For an arbitrary morphism of schemes `f : X ⟶ S`, the sheaf of relative differentials
`Ω_{X/S}` is a quasi-coherent sheaf of `𝒪_X`-modules. -/
theorem isQuasicoherent_cotangentSheaf : (cotangentSheaf f).IsQuasicoherent := by
  have key : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      ((cotangentSheaf f).restrict W.ι).IsQuasicoherent := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (Opens.mem_top (f.base x))
    obtain ⟨W, hW, hxW, hWV⟩ :=
      exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) (x := x) hxV
    exact ⟨W, hxW, isQuasicoherent_restrict_cotangentSheaf f hV hW hWV⟩
  choose W hxW hqc using key
  exact Stacks.Modules.isQuasicoherent_of_restrict _ W
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩) hqc

/-- For morphisms of schemes `f : X ⟶ S` and `a : T ⟶ X`, the pullback `a^*Ω_{X/S}` is
quasi-coherent. -/
theorem isQuasicoherent_pullbackCotangentSheaf' :
    (pullbackCotangentSheaf f a).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback a _ (isQuasicoherent_cotangentSheaf f)

/-- For a morphism of schemes `a : T ⟶ X` with `T` affine and a global section `g` of `T`, the
restriction map

`Γ(a^*Ω_{X/S}, ⊤) → Γ(a^*Ω_{X/S}, T.basicOpen g)`

exhibits its target as the localization of its source away from `g`. -/
theorem isLocalizedModule_restrictₗ_pullbackCotangentSheaf' [IsAffine T] (g : Γ(T, ⊤)) :
    letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : T.basicOpen g ≤ ⊤)
    IsLocalizedModule.Away g (restrictₗ (pullbackCotangentSheaf f a)
      (le_top : T.basicOpen g ≤ ⊤)) :=
  have := isQuasicoherent_pullbackCotangentSheaf' f a
  isLocalizedModule_restrictₗ _ (isAffineOpen_top T) g rfl le_top

end Stacks.Smooth

end
