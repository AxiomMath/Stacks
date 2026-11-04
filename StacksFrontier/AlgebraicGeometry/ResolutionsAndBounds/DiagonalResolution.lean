module

public import StacksFrontier.AlgebraicGeometry.Perfect.DiagonalResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorResolution

/-!
# The diagonal of a scheme with the resolution property is resolved by external tensor products

Let `R` be a Noetherian ring and let `X` be a separated scheme of finite type over `R` having the
resolution property. Write `Δ : X ⟶ X ×_R X` for the diagonal and `𝒪_Δ = Δ_*𝒪_X`. Then there is
an exact sequence

`… → ℰ₂ ⊠ 𝒢₂ → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ → 0`

of `𝒪_{X ×_R X}`-modules in which every `ℰᵢ` and every `𝒢ᵢ` is a finite locally free
`𝒪_X`-module and `ℰ ⊠ 𝒢 = pr₁^*ℰ ⊗ pr₂^*𝒢` is the external tensor product.

`X` being separated over `R`, the diagonal is a closed immersion, so `𝒪_Δ` is a coherent
`𝒪_{X ×_R X}`-module. A coherent module on `X ×_R X` is a quotient of an external tensor product
of finite locally free modules; the kernel of such a quotient map is again coherent, because
`X ×_R X` is Noetherian and both the kernel's ambient module and its quotient are coherent, so
the same statement applies to it and the construction can be repeated indefinitely.

## Main results

* `AlgebraicGeometry.nonempty_externalTensorCover`: a coherent module on `X ×_R X` admits a
  surjection from an external tensor product of finite locally free modules on `X`.
* `AlgebraicGeometry.exists_diagonalResolution`: **the structure sheaf of the diagonal admits a
  resolution by external tensor products of finite locally free modules**, which is
  [Stacks, Tag 0FZ2].

## References

* [Stacks Project, Tag 0FZ2](https://stacks.math.columbia.edu/tag/0FZ2)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] [QuasiCompact f] [HasResolutionProperty X]

/-- **A coherent module on `X ×_R X` is covered by an external tensor product of finite locally
free modules.** This is [Stacks, Tag 0FZ0] for the two factors of `X ×_R X`, packaged as the
covering datum from which a resolution of the diagonal is assembled. -/
theorem nonempty_externalTensorCover (M : (pullback f f).Modules) (hM : M.IsCoherent) :
    Nonempty (ExternalTensorCover f M) := by
  have := hM
  obtain ⟨E, G, hE, hG, q, hq⟩ := exists_externalTensorProduct_epi R f f M
  exact ⟨⟨E, G, hE, hG, q, hq⟩⟩

/-- **Stacks Project, Tag 0FZ2.** Let `R` be a Noetherian ring and let `X` be a separated scheme
of finite type over `R` having the resolution property. The structure sheaf `𝒪_Δ = Δ_*𝒪_X` of the
diagonal `Δ : X ⟶ X ×_R X` admits a resolution

`… → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ → 0`

by external tensor products of finite locally free `𝒪_X`-modules. -/
@[stacks 0FZ2]
theorem exists_diagonalResolution [IsSeparated f] :
    ∃ (C : ChainComplex (pullback f f).Modules ℕ) (E G : ℕ → X.Modules)
      (_ : ∀ i, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E i))
      (_ : ∀ i, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (G i))
      (_ : C.X 0 ≅
        (Scheme.Modules.pushforward (pullback.diagonal f)).obj (SheafOfModules.unit _))
      (_ : ∀ i, C.X (i + 1) ≅ externalTensorProduct f f (E i) (G i)),
      C.Acyclic := by
  obtain ⟨r⟩ := nonempty_diagonalResolution_of_externalTensorCovers f
    fun M hM => (nonempty_externalTensorCover R f M hM).some
  exact ⟨r.complex, r.left, r.right, r.left_finiteLocallyFree, r.right_finiteLocallyFree,
    r.zeroIso, r.termIso, r.acyclic⟩

end AlgebraicGeometry

end
