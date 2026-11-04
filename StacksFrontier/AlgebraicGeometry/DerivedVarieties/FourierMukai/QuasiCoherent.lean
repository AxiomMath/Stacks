module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# A Fourier-Mukai functor preserves quasi-coherence of cohomology

Let `S` be a scheme, let `X` and `Y` be schemes over `S` with `X ⟶ S` quasi-compact and
quasi-separated, and let `K` be a complex on `X ×_S Y` with quasi-coherent cohomology sheaves.
Then the Fourier-Mukai functor

`Φ_K : D(𝒪_X) ⟶ D(𝒪_Y)`,  `M ⟼ R pr_{2,*}(L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K)`

of [Stacks, Tag 0FYQ] carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. This is [Stacks, Tag 0FYR].

The proof is the source's: the three factors of `Φ_K` preserve quasi-coherence of cohomology one
after the other. Derived pullback does so for an arbitrary morphism of schemes, which is
[Stacks, Tag 08DW] part (1); the derived tensor product does so with no hypothesis, which is
[Stacks, Tag 08DX] part (1); and the derived direct image does so for a quasi-compact and
quasi-separated morphism, which is [Stacks, Tag 08D5] part (1). The hypothesis on `X ⟶ S` enters
only in the third step, through `pr₂ : X ×_S Y ⟶ Y`, which is quasi-compact and quasi-separated
because `X ⟶ S` is and both properties are stable under base change.

## Main definitions

* `AlgebraicGeometry.quasiCoherentFourierMukai` — the restriction
  `Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, which is the "Fourier-Mukai functor on `D_QCoh`" of
  [Stacks, Tag 0FYQ].

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_fourierMukai` — **[Stacks, Tag 0FYR]**: every
  cohomology sheaf of `Φ_K(M)` is quasi-coherent, for `M` and `K` with quasi-coherent cohomology
  sheaves and `X ⟶ S` quasi-compact and quasi-separated.

## Implementation notes

*The model of the derived categories.* `AlgebraicGeometry.fourierMukai` is pinned to
`CategoryTheory.HasDerivedCategory.standard`, which the priority of the local instance selects
here in preference to the locally small model arriving with the imports. The three inputs are
read at that model: [Stacks, Tag 08D5] and [Stacks, Tag 08DX] are stated there, and
[Stacks, Tag 08DW] part (1) is available at an arbitrary model as
`Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel`.

*No shift.* The normalisation is the one of [Stacks, Tag 0FYQ] Definition 57.8.1: pullback along
`pr₁`, tensor over `𝒪_{X ×_S Y}`, pushforward along `pr₂`, and no shift.

## References

* [Stacks Project, Tag 0FYR](https://stacks.math.columbia.edu/tag/0FYR)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- The priority selects the standard model of the derived categories, which
-- `AlgebraicGeometry.fourierMukai` and the quasi-coherence of the derived tensor product and of
-- the derived direct image are stated at, over the locally small model arriving with the imports.
attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **[Stacks, Tag 0FYR].** Let `S` be a scheme, let `X` and `Y` be schemes over `S` with
`f : X ⟶ S` quasi-compact and quasi-separated, and let `K` be a complex on `X ×_S Y` all of whose
cohomology sheaves are quasi-coherent. Then the Fourier-Mukai functor `Φ_K` carries
`D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`: every cohomology sheaf of `Φ_K(M)` is quasi-coherent whenever
every cohomology sheaf of `M` is.

The three factors of `Φ_K` are applied in turn: `L pr_1^*` by [Stacks, Tag 08DW] part (1),
`- ⊗^𝐋 K` by [Stacks, Tag 08DX] part (1), and `R pr_{2,*}` by [Stacks, Tag 08D5] part (1), whose
hypothesis holds because `pr₂` is quasi-compact and quasi-separated by base change from `f`. -/
@[stacks 0FYR]
theorem isQuasicoherent_homology_fourierMukai [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      K).IsQuasicoherent)
    (M : DerivedCategory X.Modules)
    (hM : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj M).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((fourierMukai f g K).obj M)).IsQuasicoherent := by
  have hpull : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      ((fourierMukaiPullback f g).obj M)).IsQuasicoherent := fun j =>
    Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
      (Limits.pullback.fst f g) M hM j
  have htens : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      ((fourierMukaiTensor f g K).obj
        ((fourierMukaiPullback f g).obj M))).IsQuasicoherent := fun j =>
    TorFormula.isQuasicoherent_homology_derivedTensor (Limits.pullback f g)
      ((fourierMukaiPullback f g).obj M) K hpull hK j
  exact isQuasicoherent_derivedPushforward_affineLocal (Limits.pullback.snd f g)
    ⟨(fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M), htens⟩ i

/-- **The Fourier-Mukai functor on the quasi-coherent derived categories**, which is the
restriction `Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` named in [Stacks, Tag 0FYQ]. It exists under the
hypotheses of [Stacks, Tag 0FYR]. -/
def quasiCoherentFourierMukai [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      K).IsQuasicoherent) :
    QuasicoherentDerivedCategory X ⥤ QuasicoherentDerivedCategory Y :=
  fourierMukaiOn f g K _ _ fun M =>
    isQuasicoherent_homology_fourierMukai f g K hK M.obj M.property

end AlgebraicGeometry

end
