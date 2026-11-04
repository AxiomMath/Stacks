module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExistence

/-!
# Situation 0DIK with the derived pullback constructed

Let `(Aₙ)` be an inverse system of rings with surjective transition maps whose kernels are
locally nilpotent, let `A = lim Aₙ`, let `X` be an algebraic space proper, flat and of finite
presentation over `A`, and let `Xₙ = X ×_{Spec A} Spec Aₙ`. Situation 0DIK of the Stacks
project is a system `(Kₙ, φₙ)` of pseudo-coherent objects `Kₙ` of `D(𝒪_{Xₙ})` together with
maps `φₙ` whose adjoints `Liₙ^* Kₙ₊₁ ⟶ Kₙ` are isomorphisms, where `iₙ : Xₙ ⟶ Xₙ₊₁` is the
closed immersion of consecutive infinitesimal base changes.

Here the derived pullback `Liₙ^*` is the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` ([Stacks, Tag 06YY]) along the morphism
of small étale ringed topoi induced by `iₙ`; no derived functor is part of the data.

## Main definitions

* `AlgebraicGeometry.Space.transitionDerivedPullback`: the derived pullback `Liₙ^*` along the
  transition morphism `Xₙ ⟶ Xₙ₊₁`, a functor `D(𝒪_{Xₙ₊₁}) ⥤ D(𝒪_{Xₙ})`.
* `AlgebraicGeometry.Space.transitionLeftDerivedPullback`: the same functor packaged as a
  `AlgebraicGeometry.Space.DerivedPullbackAt`, computed by the K-flat complexes with flat terms.
* `AlgebraicGeometry.Space.DerivedExistenceSystem`: the rings, the algebraic space and the
  compatible system of pseudo-coherent derived objects, compared through `Liₙ^*`.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.toDerivedExistenceSituation`: the
  `AlgebraicGeometry.Space.DerivedExistenceSituation` with `transitionLeftDerivedPullback` as its
  derived pullback.

## Main results

* `AlgebraicGeometry.Space.transitionLeftDerivedPullback_functor`: the functor of the packaged
  datum is `transitionDerivedPullback`, by definition.

## Implementation notes

The derived categories are those of `derivedCategoryAt`, at the standard model
`CategoryTheory.HasDerivedCategory.standard`, which is also the model of
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`.

The index `n : ℕ` stands for the level `n + 1` of the source, as in the base encoding, and the
comparison `φₙ` is stated in its adjoint form `Liₙ^* Kₙ₊₁ ⟶ Kₙ` together with its invertibility,
which is exactly the condition the source places on `φₙ : Kₙ₊₁ ⟶ Riₙ,* Kₙ`.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)
open Stacks.Cohomology.DerivedPushforward (LeftDerivedPullback)

universe u

namespace AlgebraicGeometry.Space

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (B : BigFppfSite.{u})
    (hS : B.Contains (limitBase F)) (hSn : ∀ n : ℕ, B.Contains (baseAt F n))
    (X : Over (schemeSpace (limitBaseObject F B hS)))

/-- The derived pullback `Liₙ^* : D(𝒪_{Xₙ₊₁}) ⥤ D(𝒪_{Xₙ})` along the transition morphism
`iₙ : Xₙ ⟶ Xₙ₊₁` between consecutive infinitesimal base changes: the derived pullback along the
morphism of small étale ringed topoi induced by `iₙ`. -/
abbrev transitionDerivedPullback (n : ℕ) :
    derivedCategoryAt F B hS hSn X (n + 1) ⥤ derivedCategoryAt F B hS hSn X n :=
  smallEtaleDerivedModulePullback B (limitBase F) hS (transitionSpace F B hS hSn X n)

/-- The derived pullback along the transition morphism `Xₙ ⟶ Xₙ₊₁`, packaged as a total left
derived pullback computed by the resolving class of K-flat complexes with flat terms. -/
def transitionLeftDerivedPullback (n : ℕ) : DerivedPullbackAt F B hS hSn X n :=
  LeftDerivedPullback.ofResolving
    (smallEtaleRingedToposHom B (limitBase F) hS (transitionSpace F B hS hSn X n))
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
    (fun M => by
      obtain ⟨N, hN, t, ht⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat M
      exact ⟨N, hN, t, ht⟩)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
      (smallEtaleRingedToposHom B (limitBase F) hS (transitionSpace F B hS hSn X n)))

/-- The functor of the packaged derived pullback is `transitionDerivedPullback`. -/
lemma transitionLeftDerivedPullback_functor (n : ℕ) :
    (transitionLeftDerivedPullback F B hS hSn X n).functor =
      transitionDerivedPullback F B hS hSn X n :=
  rfl

/-- The standing data of Grothendieck's existence theorem for algebraic spaces in its derived
form: an inverse system of rings `(Aₙ)` with surjective transitions whose kernels are locally
nilpotent, an algebraic space `X` proper, flat and of finite presentation over `A = lim Aₙ`, and
pseudo-coherent objects `Kₙ` of `D(𝒪_{Xₙ})` on the infinitesimal base changes
`Xₙ = X ×_{Spec A} Spec Aₙ`, with maps `Liₙ^* Kₙ₊₁ ⟶ Kₙ` that are isomorphisms, `Liₙ^*` being
the derived pullback along `Xₙ ⟶ Xₙ₊₁` constructed in `transitionDerivedPullback`. -/
@[stacks 0DIK "the situation as stated, with the derived pullback along each Xₙ → Xₙ₊₁ \
constructed by Stacks 06YY rather than given; nothing is granted or assumed beyond the source's \
data and a big fppf site containing Spec A and every Spec Aₙ"]
structure DerivedExistenceSystem where
  /-- The inverse system of rings `(Aₙ)`. -/
  system : ℕᵒᵖ ⥤ CommRingCat.{u}
  /-- Its consecutive transition maps are surjective. -/
  transition_surjective (n : ℕ) :
    Function.Surjective (system.map (homOfLE (Nat.le_succ n)).op).hom
  /-- The kernels of those transition maps are locally nilpotent. -/
  transition_locallyNilpotent (n : ℕ) :
    (RingHom.ker (system.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent
  /-- The big fppf site in which the algebraic spaces are taken. -/
  B : BigFppfSite.{u}
  /-- The inverse-limit base `Spec A` belongs to the site. -/
  containsLimitBase : B.Contains (limitBase system)
  /-- Every affine base `Spec Aₙ` belongs to the site. -/
  containsBaseAt (n : ℕ) : B.Contains (baseAt system n)
  /-- The algebraic space `X` over `Spec A`. -/
  X : Over (schemeSpace (limitBaseObject system B containsLimitBase))
  /-- `X` is proper over `Spec A`. -/
  proper : IsProper B (limitBase system) containsLimitBase X.hom.hom
  /-- `X` is flat over `Spec A`. -/
  flat : IsFlat B (limitBase system) containsLimitBase X.hom.hom
  /-- `X` is of finite presentation over `Spec A`. -/
  finitePresentation :
    IsFinitePresentation B (limitBase system) containsLimitBase X.hom.hom
  /-- The object `Kₙ` of `D(𝒪_{Xₙ})`. -/
  K (n : ℕ) : derivedCategoryAt system B containsLimitBase containsBaseAt X n
  /-- Each `Kₙ` is pseudo-coherent. -/
  pseudoCoherent (n : ℕ) :
    IsPseudoCoherentOn system B containsLimitBase containsBaseAt X n (K n)
  /-- The comparison map `Liₙ^* Kₙ₊₁ ⟶ Kₙ`, the adjoint of the map `Kₙ₊₁ ⟶ Riₙ,* Kₙ`. -/
  φ (n : ℕ) :
    (transitionDerivedPullback system B containsLimitBase containsBaseAt X n).obj (K (n + 1)) ⟶
      K n
  /-- The comparison map is an isomorphism `Kₙ₊₁ ⊗^L 𝒪_{Xₙ} ≅ Kₙ`. -/
  φ_isIso (n : ℕ) : IsIso (φ n)

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- The `AlgebraicGeometry.Space.DerivedExistenceSituation` underlying a
`DerivedExistenceSystem`: its derived pullback datum is `transitionLeftDerivedPullback`, whose
functor is the one `φ` is stated against. -/
def toDerivedExistenceSituation : DerivedExistenceSituation.{u} where
  system := D.system
  transition_surjective := D.transition_surjective
  transition_locallyNilpotent := D.transition_locallyNilpotent
  B := D.B
  containsLimitBase := D.containsLimitBase
  containsBaseAt := D.containsBaseAt
  X := D.X
  proper := D.proper
  flat := D.flat
  finitePresentation := D.finitePresentation
  K := D.K
  pseudoCoherent := D.pseudoCoherent
  derivedPullback := transitionLeftDerivedPullback D.system D.B D.containsLimitBase
    D.containsBaseAt D.X
  φ := D.φ
  φ_isIso := D.φ_isIso

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
