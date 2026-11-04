module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.FlatDimensionTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.GenericFreeMapSpreading
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatAtPointOpenBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.SectionsUniversalInjectivityBaseChange

/-!
# Flatness in dimensions `≥ d` at a dévissage stage with fibres of dimension `> d`

Let `(Z, Y, i, π, 𝒢, α)` be a stage of a complete dévissage of `ℱ/X/S` over `s`, with `Y`
smooth over `S` with geometrically irreducible fibres of dimension `d₁ > d`, and suppose `π_* 𝒢`
is flat over `S` in dimensions `≥ d + 1` over an open `V ∋ s`. Then there is an open `W ∋ s`
such that, for every `T` over `W`, the points of `Y_T` where `(π_* 𝒢)_T` is flat over `T` are the
points where `Coker(α)_T` is.

## Main results

* `AlgebraicGeometry.DevissageStage.exists_basicOpen_of_lt`: there is an open `W ∋ s` such that
  for every scheme `T` over `W` the functors `F_d` of `π_* 𝒢` and of `Coker(α)` agree at `T`, and
  `Coker(α)` is flat over `S` in dimensions `≥ d + 1` over `V ∩ W`.

## References

* [Stacks Project, Tag 05UF](https://stacks.math.columbia.edu/tag/05UF)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace DevissageStage

variable {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {F : X.Modules}
  [F.IsQuasicoherent] [F.IsFiniteType] {s : S}

attribute [local instance] OneStepDevissage.quasi_coherent_G OneStepDevissage.finite_type_G
  OneStepDevissage.closed_immersion OneStepDevissage.finite OneStepDevissage.smooth

/-- If `π_* 𝒢` is flat over `S` in dimensions `≥ d + 1` over an open `V ∋ s` and the fibres of the
smooth scheme of the stage have dimension `> d`, then there is an open `W ∋ s` such that, for every
scheme `T` over `S` lying over `W`, `(π_* 𝒢)_T` is flat over `T` in dimensions `≥ d` exactly when
`Coker(α)_T` is, and `Coker(α)` is flat over `S` in dimensions `≥ d + 1` over `V ∩ W`. -/
theorem exists_basicOpen_of_lt (stage : DevissageStage f F s) (n : ℕ)
    (hf : FinitePresentation f) [F.IsFinitePresentation] {V : S.Opens} (hs : s ∈ V)
    (h : IsFlatOverInDimensionsGEOn stage.oneStep.g
      ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G) (n + 1) V)
    (hlt : (n : WithBot ℕ∞) < topologicalKrullDim (stage.oneStep.g.fiber s)) :
    ∃ W : S.Opens, s ∈ W ∧
      (∀ T : Over S, (∀ t, T.hom t ∈ W) →
        (BaseChangeFlatInDimensionsGE stage.oneStep.g
          ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G) n T ↔
          BaseChangeFlatInDimensionsGE stage.oneStep.g stage.coker n T)) ∧
      IsFlatOverInDimensionsGEOn stage.oneStep.g stage.coker (n + 1) (V ⊓ W : S.Opens) := by
  have : IsAffine stage.oneStep.Y := stage.oneStep.affine_Y
  have : IsAffine S := stage.oneStep.affine_S
  obtain ⟨a, hsa, hα⟩ := stage.exists_universallyInjective_away hf
    (stage.isFlatOverAt_genericPoint_of_lt n hf hs h hlt)
  have hpt : ∀ (T : Over S), (∀ t, T.hom t ∈ S.basicOpen a) →
      ∀ x : ↑(pullback stage.oneStep.g T.hom),
        IsFlatOverAt (pullback.snd stage.oneStep.g T.hom).toLRSHom.toShHom
            ((Scheme.Modules.pullback (pullback.fst stage.oneStep.g T.hom)).obj
              ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G)) x ↔
          IsFlatOverAt (pullback.snd stage.oneStep.g T.hom).toLRSHom.toShHom
            ((Scheme.Modules.pullback (pullback.fst stage.oneStep.g T.hom)).obj stage.coker) x :=
    fun T hT x ↦ isFlatOverAt_pullback_iff_cokernel_of_away stage.oneStep.g T.hom
      (E := Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank))) stage.alpha a hα
      hT x (isFlatOverAt_pullback_free stage.oneStep.g T.hom _ x)
  refine ⟨S.basicOpen a, hsa, fun T hT ↦
    ⟨fun hh x hx hnf ↦ hh x hx fun hfl ↦ hnf ((hpt T hT x).mp hfl),
      fun hh x hx hnf ↦ hh x hx fun hfl ↦ hnf ((hpt T hT x).mpr hfl)⟩, fun y hy hnf ↦ ?_⟩
  obtain ⟨x, rfl⟩ : y ∈ Set.range (pullback.fst stage.oneStep.g (S.basicOpen a).ι) := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hy.2
  refine h _ hy.1 fun hflM ↦ hnf ?_
  have : stage.coker.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
      (M := Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank))) stage.alpha
  rw [← isFlatOverAt_pullback_fst_iff_of_opens] at hflM ⊢
  exact (hpt (Over.mk (S.basicOpen a).ι) (fun t ↦ t.2) x).mp hflM

end DevissageStage

end AlgebraicGeometry
