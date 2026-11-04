module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceLimitProjectionCompatibility

/-!
# The derived Grothendieck existence theorem for algebraic spaces: the restrictions of `K`

In Situation [Stacks, Tag 0DIK] the derived existence theorem [Stacks, Tag 0DIQ] produces a
pseudo-coherent `K` in `D(𝒪_X)` with `Kₙ = K ⊗^L_{𝒪_X} 𝒪_{Xₙ}` for all `n`, compatibly with the
maps `φₙ`. Here `K ⊗^L_{𝒪_X} 𝒪_{Xₙ}` is read as the derived pullback `Ljₙ^* K` along
`jₙ : Xₙ ⟶ X` (the source identifies `Kₙ` with its pushforward to `X`), and compatibility with
the `φₙ` means that the isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ` satisfy

`ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`,

with `Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*` the composition isomorphism of derived pullbacks (Stacks 0D6D) along
`iₙ ≫ jₙ₊₁ = jₙ`, and `φₙ : Liₙ^* Kₙ₊₁ ⟶ Kₙ` the comparison maps of the situation.

This file states that property and reads it off the maps `τₙ : Ljₙ^* K ⟶ Kₙ` of
[Stacks, Tag 0DIL]: when every `τₙ` is invertible, the `τₙ` themselves are such isomorphisms.

## Main definitions

* `DerivedExistenceSystem.IsPseudoCoherentOnLimit`: pseudo-coherence, in the sense of Stacks 08FT,
  of an object of `D(𝒪_X)`.
* `DerivedExistenceSystem.IsCompatibleRestriction`: a family of maps `Ljₙ^* K ⟶ Kₙ` satisfies
  `ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ` for every `n`.

## Main results

* `DerivedExistenceSystem.isCompatibleRestriction_coheratorLimitPullbackMap`: the maps `τₙ` are
  compatible with the `φₙ`, given that the composition isomorphism of derived pullbacks is
  conjugate to the composition isomorphism of the tower.
* `DerivedExistenceSystem.exists_iso_isCompatibleRestriction_of_isIso`: if moreover every `τₙ` is
  invertible, then `Kₙ = K ⊗^L 𝒪_{Xₙ}` compatibly with the `φₙ`.
* `DerivedExistenceSystem.exists_isPseudoCoherent_of_isIso`: if moreover `K` is pseudo-coherent,
  the conclusion of Stacks 0DIQ holds.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- **Pseudo-coherence on `X`**, in the sense of Stacks 08FT, of an object of `D(𝒪_X)`: the
counterpart on `X` of `AlgebraicGeometry.Space.IsPseudoCoherentOn` on the `Xₙ`, at the same
ringed site (the small étale ringed topos of `X` read as a ringed site) and the same model of the
derived category. -/
abbrev IsPseudoCoherentOnLimit (K : D.limitDerivedCategory) : Prop :=
  letI : HasDerivedCategory.{u + 1} (D.toposModules D.X.left) := HasDerivedCategory.standard _
  RingedSite.IsPseudoCoherent.{u + 1, u, u, u, u + 1}
    (RingedTopos.toRingedSite
      (smallEtaleRingedTopos D.B (limitBase D.system) D.containsLimitBase D.X.left)) K

/-- **Compatibility with the `φₙ`** of a family of maps `ψₙ : Ljₙ^* K ⟶ Kₙ`:
`ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ` for every `n`, with the composition isomorphism
of derived pullbacks along `iₙ ≫ jₙ₊₁ = jₙ` (Stacks 0D6D). -/
def IsCompatibleRestriction {K : D.limitDerivedCategory}
    (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ⟶ D.K n) : Prop :=
  ∀ n : ℕ, ψ n = (D.stageDerivedPullbackCompIso n).inv.app K ≫
    (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
      (ψ (n + 1)) ≫ D.φ n

section Coherator

variable (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).FullSubcategory)
  (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)

/-- **The `τₙ` are compatible with the `φₙ`**, given that the composition isomorphism
`Ljₙ₊₁^* ⋙ Liₙ^* ≅ Ljₙ^*` of derived pullbacks is conjugate to the composition isomorphism
`Riₙ,* ⋙ Rjₙ₊₁,* ≅ Rjₙ,*` of the tower. -/
theorem isCompatibleRestriction_coheratorLimitPullbackMap
    (he : ∀ n : ℕ, conjugateEquiv (D.stageAdjunction n)
      ((D.stageAdjunction (n + 1)).comp (D.transitionAdjunction n))
        (D.stageDerivedPullbackCompIso n).hom = (D.stagePushforwardCompIso n).inv) :
    D.IsCompatibleRestriction (D.coheratorLimitPullbackMap DQ adj) := fun n =>
  D.coheratorLimitPullbackMap_eq DQ adj n _ (he n)

/-- **`Kₙ = K ⊗^L 𝒪_{Xₙ}` compatibly with the `φₙ`, from the invertibility of the `τₙ`.** If
every `τₙ : Ljₙ^* K ⟶ Kₙ` is an isomorphism, the `τₙ` are isomorphisms `Ljₙ^* K ≅ Kₙ`
compatible with the `φₙ`. -/
theorem exists_iso_isCompatibleRestriction_of_isIso
    (he : ∀ n : ℕ, conjugateEquiv (D.stageAdjunction n)
      ((D.stageAdjunction (n + 1)).comp (D.transitionAdjunction n))
        (D.stageDerivedPullbackCompIso n).hom = (D.stagePushforwardCompIso n).inv)
    (hτ : ∀ n : ℕ, IsIso (D.coheratorLimitPullbackMap DQ adj n)) :
    ∃ ψ : ∀ n : ℕ,
        (D.stageDerivedPullback n).obj
          ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
            (D.coheratorLimit DQ)) ≅ D.K n,
      (∀ n : ℕ, (ψ n).hom = D.coheratorLimitPullbackMap DQ adj n) ∧
        D.IsCompatibleRestriction fun n => (ψ n).hom :=
  ⟨fun n => asIso (D.coheratorLimitPullbackMap DQ adj n), fun _ => rfl,
    D.isCompatibleRestriction_coheratorLimitPullbackMap DQ adj he⟩

/-- **The conclusion of Stacks 0DIQ, from its three inputs.** If `K = DQ_X(R lim Kₙ)` is
pseudo-coherent, every `τₙ` is invertible, and the composition isomorphisms of derived pullbacks
are conjugate to those of the tower, then there is a pseudo-coherent `K` in `D(𝒪_X)` with
`Kₙ = K ⊗^L 𝒪_{Xₙ}` for all `n` compatibly with the `φₙ`. -/
theorem exists_isPseudoCoherent_of_isIso
    (hK : D.IsPseudoCoherentOnLimit
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        (D.coheratorLimit DQ)))
    (he : ∀ n : ℕ, conjugateEquiv (D.stageAdjunction n)
      ((D.stageAdjunction (n + 1)).comp (D.transitionAdjunction n))
        (D.stageDerivedPullbackCompIso n).hom = (D.stagePushforwardCompIso n).inv)
    (hτ : ∀ n : ℕ, IsIso (D.coheratorLimitPullbackMap DQ adj n)) :
    ∃ (K : D.limitDerivedCategory) (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n),
      D.IsPseudoCoherentOnLimit K ∧ D.IsCompatibleRestriction fun n => (ψ n).hom := by
  obtain ⟨ψ, -, hψ⟩ := D.exists_iso_isCompatibleRestriction_of_isIso DQ adj he hτ
  exact ⟨_, ψ, hK, hψ⟩

end Coherator

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
