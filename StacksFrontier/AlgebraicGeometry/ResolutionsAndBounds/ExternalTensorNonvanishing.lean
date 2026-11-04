module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorResolution

/-!
# A nonzero coherent module on a product is hit by an external tensor product

Let `R` be a Noetherian ring and let `X` and `Y` be schemes of finite type over `R` with the
resolution property. [Stacks, Tag 0FZ0] produces, for every coherent `𝒪_{X ×_R Y}`-module `F`, a
surjection `ℰ ⊠ 𝒢 → F` with `ℰ` and `𝒢` finite locally free. This file records the consequence
that the proofs of [Stacks, Tag 0G0D] and [Stacks, Tag 0G0E] use: such a surjection onto a
*nonzero* `F` is itself a nonzero morphism, so the group `Hom(ℰ ⊠ 𝒢, F)` is nonzero, and
conversely a coherent module receiving only the zero morphism from every external tensor product
of finite locally free modules vanishes.

In the source this is the sentence "if `H^i(K)` is nonzero, then we can choose `ℰ` and `𝒢` such
that there is a surjection `ℰ^∨ ⊠ 𝒢^∨ → H^i(K)` by Lemma 57.9.1; in this case the left hand side
of the equalities is nonzero".

## Main results

* `AlgebraicGeometry.exists_externalTensorProduct_hom_ne_zero`: a nonzero coherent module on
  `X ×_R Y` admits a nonzero — indeed surjective — morphism from an external tensor product of
  a finite locally free `𝒪_X`-module and a finite locally free `𝒪_Y`-module.
* `AlgebraicGeometry.isZero_of_forall_externalTensorProduct_hom_eq_zero`: the contrapositive, in
  the form a vanishing argument consumes.

## References

* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
  [HasResolutionProperty X] [HasResolutionProperty Y]

/-- **A nonzero coherent module on `X ×_R Y` receives a nonzero morphism from an external tensor
product of finite locally free modules.** The surjection of [Stacks, Tag 0FZ0] is the morphism:
were it zero, its target would be zero because it is an epimorphism. -/
theorem exists_externalTensorProduct_hom_ne_zero
    (F : (pullback f g).Modules) [F.IsCoherent] (hF : ¬ IsZero F) :
    ∃ (E : X.Modules) (G : Y.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G)
      (q : externalTensorProduct f g E G ⟶ F), Epi q ∧ q ≠ 0 := by
  obtain ⟨E, G, hE, hG, q, hq⟩ := exists_externalTensorProduct_epi R f g F
  exact ⟨E, G, hE, hG, q, hq, fun h => hF (IsZero.of_epi_eq_zero q h)⟩

/-- **A coherent module on `X ×_R Y` receiving only the zero morphism from every external tensor
product of finite locally free modules is zero.** This is the contrapositive of
`AlgebraicGeometry.exists_externalTensorProduct_hom_ne_zero`, and it is the form in which a
vanishing argument uses [Stacks, Tag 0FZ0]. -/
theorem isZero_of_forall_externalTensorProduct_hom_eq_zero
    (F : (pullback f g).Modules) [F.IsCoherent]
    (hF : ∀ (E : X.Modules) (G : Y.Modules),
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E →
        SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G →
          ∀ q : externalTensorProduct f g E G ⟶ F, q = 0) :
    IsZero F := by
  by_contra h
  obtain ⟨E, G, hE, hG, q, -, hq⟩ := exists_externalTensorProduct_hom_ne_zero R f g F h
  exact hq (hF E G hE hG q)

end AlgebraicGeometry

end

end
