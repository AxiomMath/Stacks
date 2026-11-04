module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMap

/-!
# The kernel–cokernel bound of Stacks 088B from the maps `γ_n` alone

In Stacks 088B the isomorphism `β : (f^*𝒢_n) ≅ 𝓕^` enters the kernel–cokernel bound only through
the maps

`γ_n : 𝒢_n ⟶ f_*f^*𝒢_n ⟶ f_*(𝓕/ℐ ⁿ⁺¹𝓕)`,

and `β_n` is recovered from `γ_n` as its adjoint.  This file records the bound in that form: for
a morphism of inverse systems `γ : (𝒢_n) ⟶ (f_*(𝓕/ℐ ⁿ⁺¹𝓕))` whose levelwise adjoints
`f^*𝒢_n ⟶ 𝓕/ℐ ⁿ⁺¹𝓕` are isomorphisms, any `α : (𝒢_n) ⟶ (f_*𝓕)^` with `α ≫ c = γ` has its
levelwise kernels and cokernels annihilated by one power of `𝒦`.  This is the form in which the
bound is transported from algebraic spaces to schemes along étale charts (Stacks 08BD), where
`γ` is available on the chart but `β` is not.

## Main results

* `Stacks.Coherent.C1573.adjointSystemIso`: the isomorphism `(f^*𝒢_n) ≅ 𝓕^` of coherent adic
  systems assembled from levelwise invertible adjoints of `γ`.
* `Stacks.Coherent.C1573.directImageComparison_adjointSystemIso`: its maps `γ_n` are `γ`.
* `Stacks.Coherent.C1573.isKernelCokernelAnnihilatedByPower_of_isIso_adjoint`: the
  kernel–cokernel bound for `α` with `α ≫ c = γ`, when the levelwise adjoints of `γ` are
  isomorphisms.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
-/

namespace Stacks.Coherent.C1573
end Stacks.Coherent.C1573

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

open Stacks.Algebraization

open _root_.Stacks.Coherent.C1573
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
  (J : Y.IdealSheafData) (G : CoherentAdicSystems J)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (γ : G.obj ⟶ ((completionFunctor X (J.comap f)).obj F).obj ⋙ Scheme.Modules.pushforward f)

/-- The levelwise adjoints `f^*𝒢_n ⟶ 𝓕/ℐ ⁿ⁺¹𝓕` of a morphism of inverse systems
`γ : (𝒢_n) ⟶ (f_*(𝓕/ℐ ⁿ⁺¹𝓕))`, as a morphism of inverse systems. -/
def C1573.adjointSystemHom :
    G.obj ⋙ Scheme.Modules.pullback f ⟶ ((completionFunctor X (J.comap f)).obj F).obj where
  app n := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (γ.app n)
  naturality i j a := by
    change (Scheme.Modules.pullback f).map (G.obj.map a) ≫ _ = _ ≫ _
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
      γ.naturality]
    rfl

/-- **The isomorphism `(f^*𝒢_n) ≅ 𝓕^` assembled from levelwise invertible adjoints of `γ`**, as
an isomorphism of coherent adic systems along `ℐ = f⁻¹𝒥 𝒪_X`. -/
def C1573.adjointSystemIso
    (hγ : ∀ n, IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
      (γ.app n))) :
    (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun n => @asIso _ _ _ _ ((adjointSystemHom f J G F γ).app n) (hγ n))
    (fun a => (adjointSystemHom f J G F γ).naturality a))

/-- The components of `adjointSystemIso` are the levelwise adjoints of `γ`. -/
theorem C1573.adjointSystemIso_hom_app
    (hγ : ∀ n, IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
      (γ.app n))) (n : ℕᵒᵖ) :
    (adjointSystemIso f J G F γ hγ).hom.hom.app n =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (γ.app n) :=
  rfl

/-- The maps `γ_n` of the isomorphism `adjointSystemIso` are the given `γ`. -/
theorem C1573.directImageComparison_adjointSystemIso
    (hγ : ∀ n, IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
      (γ.app n))) :
    directImageComparison f J G F (adjointSystemIso f J G F γ hγ) = γ := by
  ext n : 2
  rw [directImageComparison_app, adjointSystemIso_hom_app]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **The kernel–cokernel bound of Stacks 088B from the maps `γ_n`.**  Let `Y` be a Noetherian
scheme, `𝒥, 𝒦 ⊆ 𝒪_Y` quasi-coherent sheaves of ideals, `f : X ⟶ Y` proper and an isomorphism over
`Y ∖ V(𝒦)`, `(𝒢_n)` a coherent `𝒥`-adic system and `𝓕` a coherent `𝒪_X`-module.  Let
`γ : (𝒢_n) ⟶ (f_*(𝓕/ℐ ⁿ⁺¹𝓕))` be a morphism of inverse systems whose levelwise adjoints
`f^*𝒢_n ⟶ 𝓕/ℐ ⁿ⁺¹𝓕` are isomorphisms.  Then the levelwise kernels and cokernels of every
`α : (𝒢_n) ⟶ (f_*𝓕)^` with `α ≫ c = γ` are annihilated by one power of `𝒦`. -/
theorem C1573.isKernelCokernelAnnihilatedByPower_of_isIso_adjoint
    {X Y : Scheme.{u}} [IsNoetherian Y] (J K : Y.IdealSheafData)
    (f : X ⟶ Y) [IsProper f] (hf : IsIso (f ∣_ K.support.compl))
    (G : CoherentAdicSystems J) (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    ∀ (γ : G.obj ⟶ ((completionFunctor X (J.comap f)).obj ⟨F, inferInstance⟩).obj ⋙
        Scheme.Modules.pushforward f),
      (∀ n, IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
        (γ.app n))) →
      ∀ (α : G ⟶ (completionFunctor Y J).obj
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩),
      α.hom ≫ pushforwardCompletionComparison f J F = γ →
        IsKernelCokernelAnnihilatedByPower K α.hom := by
  intro γ hγ α hα
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  let : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  exact isKernelCokernelAnnihilatedByPower_of_isNoetherian J K f hf G F
    (adjointSystemIso f J G ⟨F, inferInstance⟩ γ hγ) α
    (hα.trans (directImageComparison_adjointSystemIso f J G ⟨F, inferInstance⟩ γ hγ).symm)

end Stacks.Coherent

end
