module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Quasi-coherence reflected along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes and let `ℱ` be a sheaf of `𝒪_Z`-modules whose
direct image `i_*ℱ` is an `𝒪_X`-module of finite presentation. Then `ℱ` is quasi-coherent.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isFinitePresentation_pushforward`: the
  implication of Stacks 01QY that is needed to read off quasi-coherence of `ℱ` from finite
  presentation of `i_*ℱ`.

## Implementation notes

The direct image along a closed immersion is fully faithful (Stacks 08KS,
`Stacks.ClosedImmersion.fullyFaithfulPushforward`), so the counit of the adjunction
`i^* ⊣ i_*` is an isomorphism at `ℱ`. A module of finite presentation is quasi-coherent
(Stacks 01BO), pullback preserves quasi-coherence (Stacks 01BG,
`AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent`), and quasi-coherence is closed
under isomorphisms; composing these gives quasi-coherence of `ℱ`.

## References

* [The Stacks Project, Lemma 29.4.1 (01QY)](https://stacks.math.columbia.edu/tag/01QY)
* [The Stacks Project, Lemma 17.11.4 (08KS)](https://stacks.math.columbia.edu/tag/08KS)
* [The Stacks Project, Lemma 17.11.1 (01BO)](https://stacks.math.columbia.edu/tag/01BO)
* [The Stacks Project, Lemma 17.10.2 (01BG)](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Quasi-coherence is reflected by the direct image along a closed immersion**, in the form
needed for Stacks 01QY: if `i : Z ⟶ X` is a closed immersion and `i_*ℱ` is an `𝒪_X`-module of
finite presentation, then `ℱ` is quasi-coherent.

Finite presentation of `i_*ℱ` gives its quasi-coherence (Stacks 01BO), hence that of `i^*i_*ℱ`
(Stacks 01BG); the direct image along a closed immersion is fully faithful (Stacks 08KS), so the
counit `i^*i_*ℱ ⟶ ℱ` is an isomorphism and quasi-coherence transports along it. -/
public theorem isQuasicoherent_of_isFinitePresentation_pushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Z.Modules)
    (hF : ((pushforward i).obj F).IsFinitePresentation) : F.IsQuasicoherent := by
  have := hF
  have := Stacks.ClosedImmersion.full_pushforward i
  have := Stacks.ClosedImmersion.faithful_pushforward i
  have hqc : ((pushforward i).obj F).IsQuasicoherent :=
    (_root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((pushforward i).obj F)).choose.isQuasicoherent
  have hpull : ((pullback i).obj ((pushforward i).obj F)).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ i.toLRSHom.toShHom _ hqc
  have hiso : IsIso ((pullbackPushforwardAdjunction i).counit.app F) := inferInstance
  have e : (pullback i).obj ((pushforward i).obj F) ≅ F :=
    @asIso _ _ _ _ _ hiso
  exact (inferInstance :
      (_root_.SheafOfModules.isQuasicoherent Z.ringCatSheaf).IsClosedUnderIsomorphisms).of_iso
    e hpull

end AlgebraicGeometry.Scheme.Modules

end
