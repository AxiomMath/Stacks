module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapGlobalAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapSystemAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapTransportAux
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison map of a proper morphism which is an isomorphism outside a closed subset

Let `Y` be a Noetherian scheme and let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent sheaves of ideals. Let
`f : X ⟶ Y` be a proper morphism which is an isomorphism over `V = Y ∖ V(𝒦)`, and set
`ℐ = f^{-1}𝒥 𝒪_X`. Let `(𝒢_n)` be an object of `Coh(Y, 𝒥)`, let `𝓕` be a coherent `𝒪_X`-module
and let `β : (f^*𝒢_n) ⟶ 𝓕^` be an isomorphism in `Coh(X, ℐ)`. Then there is a map

`α : (𝒢_n) ⟶ (f_*𝓕)^`

in `Coh(Y, 𝒥)` whose levelwise kernels and cokernels are annihilated by one power of `𝒦`.

The map is the unique one compatible with the maps

`γ_n : 𝒢_n ⟶ f_*f^*𝒢_n ⟶ f_*(𝓕/ℐ ⁿ⁺¹𝓕)`

of `Stacks.Coherent.directImageComparison`: the comparison
`Stacks.Coherent.pushforwardCompletionComparison` from `(f_*𝓕)^` to `(f_*(𝓕/ℐ ⁿ⁺¹𝓕))` is an
isomorphism on inverse limits by the theorem on formal functions, and a morphism of coherent
adic systems is determined by, and may be constructed from, a morphism of the inverse limits.

## Main results

* `Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_comparisonMap` — **Stacks 088B.**

## Implementation notes

The hypothesis "`f` is an isomorphism over `V = Y ∖ V(𝒦)`" is `IsIso (f ∣_ K.support.compl)`,
that is, invertibility of the restriction `f^{-1}(V) ⟶ V` of `f` over the open complement of the
closed set cut out by `𝒦`. Noetherianity of `X` is not an extra hypothesis: it follows from
properness of `f` over the Noetherian `Y`, and so does coherence of `f_*𝓕`, by
[Stacks, Tag 02O5]; both are introduced in the statement by `letI` so that the type of `β` and
the type of `α` can be written down.

The construction of `α` is `Stacks.Coherent.systemMapOfComparisonIso`, and the annihilation of
its levelwise kernels and cokernels is
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_isNoetherian`, which uses `α` only
through the identity `α ≫ c = γ` that `systemMapOfComparisonIso_comp` supplies.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

open Stacks.Algebraization

/-- **Stacks 088B.** Let `Y` be a Noetherian scheme and let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent
sheaves of ideals. Let `f : X ⟶ Y` be a proper morphism which is an isomorphism over
`V = Y ∖ V(𝒦)`, and set `ℐ = f^{-1}𝒥 𝒪_X`. Let `(𝒢_n)` be an object of `Coh(Y, 𝒥)`, let `𝓕` be
a coherent `𝒪_X`-module, and let `β : (f^*𝒢_n) ⟶ 𝓕^` be an isomorphism in `Coh(X, ℐ)`. Then
there exists a map

`α : (𝒢_n) ⟶ (f_*𝓕)^`

in `Coh(Y, 𝒥)` whose kernel and cokernel are annihilated by a power of `𝒦`. -/
@[stacks 088B]
public theorem exists_isKernelCokernelAnnihilatedByPower_comparisonMap
    {X Y : Scheme.{u}} [IsNoetherian Y] (J K : Y.IdealSheafData)
    (f : X ⟶ Y) [IsProper f] (hf : IsIso (f ∣_ K.support.compl))
    (G : CoherentAdicSystems J) (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    ∀ _β : (coherentAdicPullback f J).obj G ≅
        (completionFunctor X (J.comap f)).obj ⟨F, inferInstance⟩,
      ∃ α : G ⟶ (completionFunctor Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩,
        IsKernelCokernelAnnihilatedByPower K α.hom := by
  intro β
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  let : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  have : IsIso (limMap (pushforwardCompletionComparison f J F)) :=
    isIso_limMap_pushforwardCompletionComparison f J F
  exact ⟨systemMapOfComparisonIso (pushforwardCompletionComparison f J F)
      (directImageComparison f J G ⟨F, inferInstance⟩ β),
    isKernelCokernelAnnihilatedByPower_of_isNoetherian J K f hf G F β _
      (systemMapOfComparisonIso_comp _ _)⟩

end Stacks.Coherent

end
