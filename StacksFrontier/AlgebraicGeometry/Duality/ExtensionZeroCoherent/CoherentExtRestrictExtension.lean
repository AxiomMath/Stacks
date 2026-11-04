module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerImageContainment
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension

/-!
# Extending a coherent epimorphism onto `𝓕|_U` across the open immersion

Let `X` be a Noetherian scheme, `U ⊆ X` open, `𝓕` a coherent `𝒪_X`-module and `φ : 𝓗 ⟶ 𝓕|_U` an
epimorphism from a coherent `𝒪_U`-module. Then `φ` extends: there are a **coherent**
`𝒪_X`-module `𝓔`, a morphism `ψ : 𝓔 ⟶ 𝓕` and an isomorphism `𝓔|_U ≅ 𝓗` carrying `φ` to `ψ|_U`,
and `ψ|_U` is again an epimorphism.

This is the second of the four inputs of the surjectivity half of the induction on `i` in the
core case of [Stacks, Tag 0G2H]: the chase effaces the given class on `U`
(`Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_restrict_of_pos`) and must then carry
the effacing epimorphism back to `X`, where it is no longer surjective — only its restriction to
`U` is. How far down the ideal-power filtration of `𝓕` one has to go for it to be surjective
onto is
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_idealPowerMultiple_le_imageSubmodule`, whose
hypothesis is exactly the surjectivity on `U` recorded here.

## What has to be supplied

[Stacks, Tag 01PI], `AlgebraicGeometry.exists_finitePresentation_extension_of_hom`, extends a
morphism from a **finitely presented** `𝒪_U`-module to a quasi-coherent `𝒪_X`-module along a
quasi-compact open immersion of a quasi-compact quasi-separated scheme. On a Noetherian scheme
every one of those hypotheses is automatic and finite presentation is coherence
([Stacks, Tag 01XZ]), in the two directions
`Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent'` and
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation`. That the
extended morphism is still an epimorphism on `U` is the only thing [Stacks, Tag 01PI] does not
say, and it is immediate from the comparison isomorphism its conclusion carries.

## Main results

* `Stacks.ExtEffacement.exists_isCoherent_extension_epi_restrict`: **an epimorphism onto `𝓕|_U`
  from a coherent `𝒪_U`-module extends to a morphism of coherent `𝒪_X`-modules whose
  restriction to `U` is again an epimorphism.**
* `Stacks.ExtEffacement.exists_isCoherent_extension_idealPowerMultiple_le_imageSubmodule`: the
  same, together with the member `𝓘^m 𝓕` of the ideal-power filtration that the extension does
  surject onto — **the whole geometric input of the surjectivity chase of [Stacks, Tag 0G2H] in
  one statement.**

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01PI](https://stacks.math.columbia.edu/tag/01PI)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.ExtEffacement

variable {X : Scheme.{u}}

/-- **An epimorphism onto `𝓕|_U` from a coherent `𝒪_U`-module extends across the open
immersion.** Let `X` be a Noetherian scheme, `U ⊆ X` open, `𝓕` a coherent `𝒪_X`-module and
`φ : 𝓗 ⟶ 𝓕|_U` an epimorphism from a coherent `𝒪_U`-module. Then there are a coherent
`𝒪_X`-module `𝓔`, a morphism `ψ : 𝓔 ⟶ 𝓕` and an isomorphism `e : 𝓔|_U ≅ 𝓗` with
`e.hom ≫ φ = ψ|_U`; in particular `ψ|_U` is an epimorphism.

This is [Stacks, Tag 01PI] on a Noetherian scheme, where its quasi-compactness and
quasi-separatedness hypotheses are automatic and finite presentation is coherence. It is the
step of the surjectivity chase of [Stacks, Tag 0G2H] at which the effacement produced on `U`
returns to `X`. -/
public theorem exists_isCoherent_extension_epi_restrict [IsNoetherian X] (U : X.Opens)
    (F : X.Modules) [F.IsCoherent] (H : U.toScheme.Modules) [H.IsCoherent]
    (φ : H ⟶ (Scheme.Modules.restrictFunctor U.ι).obj F) (hφ : Epi φ) :
    ∃ (E : X.Modules) (_ : E.IsCoherent) (ψ : E ⟶ F)
      (e : (Scheme.Modules.restrictFunctor U.ι).obj E ≅ H),
      e.hom ≫ φ = (Scheme.Modules.restrictFunctor U.ι).map ψ ∧
        Epi ((Scheme.Modules.restrictFunctor U.ι).map ψ) := by
  have := hφ
  have : QuasiSeparatedSpace X := NoetherianSpace.to_quasiSeparatedSpace
  have hU : IsCompact U.1 := NoetherianSpace.isCompact _
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have : H.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' H
  obtain ⟨E, hE, ψ, e, he⟩ := exists_finitePresentation_extension_of_hom F U hU H φ
  refine ⟨E, Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation E hE,
    ψ, e, he, ?_⟩
  rw [← he]
  exact epi_comp _ _

/-- **The geometric input of the surjectivity chase of [Stacks, Tag 0G2H] in one statement.**
Let `X` be a Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals, `U = X ∖ V(𝓘)`, `𝓕` a
coherent `𝒪_X`-module and `φ : 𝓗 ⟶ 𝓕|_U` an epimorphism from a coherent `𝒪_U`-module. Then
there are a coherent `𝒪_X`-module `𝓔`, a morphism `ψ : 𝓔 ⟶ 𝓕` restricting to `φ` across an
isomorphism `𝓔|_U ≅ 𝓗`, and an exponent `m` with `𝓘^m 𝓕 ⊆ Im ψ`.

This is [Stacks, Tag 01PI] followed by the containment
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_idealPowerMultiple_le_imageSubmodule`, which
is [Stacks, Tag 01Y9] read on submodules of `𝓕`: the effacement produced on `U` is carried back
to `X`, where it is surjective only after `𝓕` is replaced by a deep enough member of its
ideal-power filtration. -/
public theorem exists_isCoherent_extension_idealPowerMultiple_le_imageSubmodule
    [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens) (hU : U = I.support.compl)
    (F : X.Modules) [F.IsCoherent] (H : U.toScheme.Modules) [H.IsCoherent]
    (φ : H ⟶ (Scheme.Modules.restrictFunctor U.ι).obj F) (hφ : Epi φ) :
    ∃ (E : X.Modules) (_ : E.IsCoherent) (ψ : E ⟶ F)
      (e : (Scheme.Modules.restrictFunctor U.ι).obj E ≅ H) (m : ℕ),
      e.hom ≫ φ = (Scheme.Modules.restrictFunctor U.ι).map ψ ∧
        Stacks.Algebraization.idealPowerMultiple I m F ≤
          _root_.AlgebraicGeometry.imageSubmodule ψ := by
  obtain ⟨E, hE, ψ, e, he, hepi⟩ := exists_isCoherent_extension_epi_restrict U F H φ hφ
  have := hE
  have : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  obtain ⟨m, hm⟩ :=
    Stacks.AlgebraicGeometry.IdealPowerColimit.exists_idealPowerMultiple_le_imageSubmodule
      I U hU ψ hepi
  exact ⟨E, hE, ψ, e, m, he, hm⟩

end Stacks.ExtEffacement

end
