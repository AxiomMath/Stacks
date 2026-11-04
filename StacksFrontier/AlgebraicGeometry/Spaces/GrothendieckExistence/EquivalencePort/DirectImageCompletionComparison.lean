module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffineSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AdicQuotientCommute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CompletionQuotientCommute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionAlgebraization

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The comparison `(f_*𝓕)/𝓙ⁿ⁺¹ ⟶ f_*(𝓕/𝓘ⁿ⁺¹𝓕)` of the proof of Stacks 08BD

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces, `𝓙 ⊆ 𝒪_Y` a sheaf of ideals and
`𝓘 = f⁻¹𝓙 · 𝒪_X` the inverse-image ideal (`AlgebraicGeometry.Space.pullbackIdealSubsheaf`). The
direct image `f_*` of a module annihilated by `𝓘^k` is annihilated by `𝓙^k`, so the direct image of
the projection `𝓕 ⟶ 𝓕/𝓘ⁿ⁺¹𝓕` factors through `(f_*𝓕)/𝓙ⁿ⁺¹(f_*𝓕)`. These factorizations form a
morphism of inverse systems `(f_*𝓕)^∧ ⟶ (f_*(𝓕/𝓘ⁿ⁺¹𝓕))_n`
(`AlgebraicGeometry.Space.C1573.directImageCompletionComparison`), the map `c` through which the
source's `α` of Stacks 08BD factors the maps `γ_n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
  (J : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)

/-- The inverse-image ideal `f⁻¹𝓙 · 𝒪_X` (`AlgebraicGeometry.Space.pullbackIdealSubsheaf`), with
its type spelled through the small étale ringed site, as the ideals of `Coh(X, 𝓘)` are. -/
abbrev C1573.inverseImageIdeal :
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule :=
  pullbackIdealSubsheaf B S hS f hf J

/-- **The direct image along small-chart base change of a module annihilated by `(f⁻¹𝓙)^k` is
annihilated by `𝓙^k`**: over a chart `Q` of `Y` an element `r` of `𝓙(Q)^k` acts on the sections
of `f_*N` through its pullback, which lies in `(f⁻¹𝓙)(Q ×_Y X)^k`. -/
theorem C1573.isPowAnnihilated_smallBaseChangeModulePushforward_inverseImageIdeal (k : ℕ)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : IsPowAnnihilated B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) k N) :
    IsPowAnnihilated B S hS Y.1 Y.2 J k ((smallBaseChangeModulePushforward B S hS f hf).obj N) := by
  intro Q r hr x
  have hmap : ∀ a ∈ chartSectionsIdeal B S hS Y J Q,
      chartIdealPullbackHom B S hS f hf Q a ∈
        chartSectionsIdeal B S hS X (inverseImageIdeal B S hS f hf J)
          ((smallBaseChange B S hS f hf).obj Q) := fun a ha =>
    chartIdealPullbackHom_mem_pullbackIdealSubsheaf B S hS f hf J Q ha
  have hle : (chartSectionsIdeal B S hS Y J Q).map (chartIdealPullbackHom B S hS f hf Q) ≤
      chartSectionsIdeal B S hS X (inverseImageIdeal B S hS f hf J)
        ((smallBaseChange B S hS f hf).obj Q) :=
    Ideal.map_le_iff_le_comap.2 hmap
  have hr' : chartIdealPullbackHom B S hS f hf Q r ∈
      chartSectionsIdeal B S hS X (inverseImageIdeal B S hS f hf J)
        ((smallBaseChange B S hS f hf).obj Q) ^ k := by
    have h1 := Ideal.mem_map_of_mem (chartIdealPullbackHom B S hS f hf Q) hr
    exact Ideal.pow_right_mono hle k ((Ideal.map_pow _ _ _).le h1)
  exact hN _ _ hr' x

/-- **The direct image of Stacks 03LU of a module annihilated by `(f⁻¹𝓙)^k` is annihilated by
`𝓙^k`.** -/
theorem C1573.isPowAnnihilated_modulePushforward_inverseImageIdeal (k : ℕ)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : IsPowAnnihilated B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) k N) :
    IsPowAnnihilated B S hS Y.1 Y.2 J k ((modulePushforward B S hS f).obj N) :=
  isPowAnnihilated_of_iso B S hS Y.1 Y.2 J ((modulePushforwardChartIso B S hS f hf).app N).symm k
    (isPowAnnihilated_smallBaseChangeModulePushforward_inverseImageIdeal B S hS f hf J k N hN)

variable (F : Modules.{u, u} B S hS X.1 X.2)

/-- The comparison `(f_*𝓕)/𝓙ᵏ ⟶ f_*(𝓕/𝓘ᵏ𝓕)`. -/
def C1573.directImageQuotientComparison (k : ℕ) :
    smallEtaleAdicQuotient B S hS Y.1 Y.2 J k ((modulePushforward B S hS f).obj F) ⟶
      (modulePushforward B S hS f).obj
        (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) k F) :=
  smallEtaleAdicQuotientLift B S hS Y.1 Y.2 J k
    ((modulePushforward B S hS f).map
      (smallEtaleAdicQuotientProjection B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) k F))
    (isPowAnnihilated_modulePushforward_inverseImageIdeal B S hS f hf J k _
      (isPowAnnihilated_smallEtaleAdicQuotient B S hS X.1 X.2 _ k F))

/-- The projection `f_*𝓕 ⟶ (f_*𝓕)/𝓙ᵏ` followed by the comparison `(f_*𝓕)/𝓙ᵏ ⟶ f_*(𝓕/𝓘ᵏ𝓕)` is the
direct image of the projection `𝓕 ⟶ 𝓕/𝓘ᵏ𝓕`. -/
@[reassoc (attr := simp)]
theorem C1573.projection_directImageQuotientComparison (k : ℕ) :
    smallEtaleAdicQuotientProjection B S hS Y.1 Y.2 J k ((modulePushforward B S hS f).obj F) ≫
        directImageQuotientComparison B S hS f hf J F k =
      (modulePushforward B S hS f).map
        (smallEtaleAdicQuotientProjection B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) k F) :=
  smallEtaleAdicQuotientProjection_lift B S hS Y.1 Y.2 J k _ _

/-- The comparisons `(f_*𝓕)/𝓙ᵏ ⟶ f_*(𝓕/𝓘ᵏ𝓕)` commute with the transition maps
`(f_*𝓕)/𝓙ᵏ⁺¹ ⟶ (f_*𝓕)/𝓙ᵏ` and `f_*(𝓕/𝓘ᵏ⁺¹𝓕) ⟶ f_*(𝓕/𝓘ᵏ𝓕)`. -/
theorem C1573.directImageQuotientComparison_transition (k : ℕ) :
    smallEtaleAdicQuotientTransition B S hS Y.1 Y.2 J k ((modulePushforward B S hS f).obj F) ≫
        directImageQuotientComparison B S hS f hf J F k =
      directImageQuotientComparison B S hS f hf J F (k + 1) ≫
        (modulePushforward B S hS f).map
          (smallEtaleAdicQuotientTransition B S hS X.1 X.2
            (inverseImageIdeal B S hS f hf J) k F) := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS Y.1 Y.2 J (k + 1) _)).1 ?_
  rw [reassoc_of% (smallEtaleAdicQuotientProjection_comp_transition B S hS Y.1 Y.2 J k
      ((modulePushforward B S hS f).obj F)),
    projection_directImageQuotientComparison, projection_directImageQuotientComparison_assoc,
    ← Functor.map_comp, smallEtaleAdicQuotientProjection_comp_transition]

/-- **The comparison `(f_*𝓕)^∧ ⟶ (f_*(𝓕/𝓘ⁿ⁺¹𝓕))_n`** of inverse systems. -/
def C1573.directImageCompletionComparison :
    adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F) ⟶
      adicQuotientSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F ⋙
        modulePushforward B S hS f :=
  NatTrans.ofOpSequence (fun n => directImageQuotientComparison B S hS f hf J F (n + 1)) fun n => by
    change (adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F)).map
        (homOfLE (Nat.le_add_right n 1)).op ≫
          directImageQuotientComparison B S hS f hf J F (n + 1) =
      directImageQuotientComparison B S hS f hf J F (n + 1 + 1) ≫
        (modulePushforward B S hS f).map
          ((adicQuotientSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F).map
            (homOfLE (Nat.le_add_right n 1)).op)
    rw [adicQuotientSystem_map_succ, adicQuotientSystem_map_succ]
    exact directImageQuotientComparison_transition B S hS f hf J F (n + 1)

/-- The component of `directImageCompletionComparison` at `n` is the comparison
`(f_*𝓕)/𝓙ⁿ⁺¹ ⟶ f_*(𝓕/𝓘ⁿ⁺¹𝓕)`. -/
theorem C1573.directImageCompletionComparison_app (n : ℕ) :
    (directImageCompletionComparison B S hS f hf J F).app (op n) =
      directImageQuotientComparison B S hS f hf J F (n + 1) :=
  rfl

end AlgebraicGeometry.Space

end
