module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatInDimensionsGEOn
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme

/-!
# Flatness in dimensions at least `n` along a one-step dévissage

Let `(Z, Y, i, π, G)` be a one-step dévissage of `F/X/S` over a point of `S` (Stacks 05H4): `F` is
the direct image of `G` along a closed immersion `i : Z ⟶ X` of finite presentation, and
`π : Z ⟶ Y` is finite over a smooth `g : Y ⟶ S`. If `X` is of finite presentation over `S` and `F`
is of finite presentation, then for every scheme `T` over `S` the base change `F_T` is flat over
`T` in dimensions `≥ n` exactly when the base change of `π_* G` to `Y_T` is, and the same holds
over every subset of `T`. This is the first paragraph of the proof of Stacks 05UF: the closed
immersion and the finite morphism stay so after base change, and direct image along a finite
morphism does not change flatness in dimensions `≥ n`.

## Main results

* `AlgebraicGeometry.isFlatOverInDimensionsGEOn_pullback_pushforward_iff`: across one cartesian
  square, the base change of a direct image along a finite morphism is the direct image of the base
  change (Stacks 02KG), so the condition transfers.
* `AlgebraicGeometry.OneStepDevissage.isFinitePresentation_G` and
  `AlgebraicGeometry.OneStepDevissage.isFinitePresentation_pushforward`: the modules `G` and
  `π_* G` of a one-step dévissage are of finite presentation when `F` is and `X` is of finite
  presentation over `S`.
* `AlgebraicGeometry.OneStepDevissage.isFlatOverInDimensionsGEOn_iff`: over the base itself.
* `AlgebraicGeometry.OneStepDevissage.isFlatOverInDimensionsGEOn_baseChange_iff`: after an
  arbitrary base change.
* `AlgebraicGeometry.DevissageStage.isFlatOverAt_genericPoint_of_lt`: in the case `d₁ > d`,
  `π_* G` is flat over `S` at the generic point of the fibre over `s`.

## References

* [Stacks Project, Tag 05UF](https://stacks.math.columbia.edu/tag/05UF)
* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 05B4](https://stacks.math.columbia.edu/tag/05B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Base change of a direct image along a finite morphism.** Let `π : Z ⟶ X` be finite and let
`G` be a module of finite presentation on `Z` with direct image of finite presentation, over a
morphism `f : X ⟶ S` locally of finite presentation such that `π ≫ f` is too. For a cartesian
square `X' ⟶ X` over `S' ⟶ S` and the cartesian square `Z' = Z ×_X X'`, the base change of `π_* G`
to `X'` is flat over `S'` in dimensions `≥ n` over `W` exactly when the base change of `G` to `Z'`
is.

The base change of `π_* G` is the direct image of the base change of `G` (Stacks 02KG), and direct
image along the finite `Z' ⟶ X'` does not change the condition. -/
theorem isFlatOverInDimensionsGEOn_pullback_pushforward_iff
    {Z X S X' Z' S' : Scheme.{u}} (π : Z ⟶ X) [IsFinite π] (f : X ⟶ S) {a : X' ⟶ X}
    {f' : X' ⟶ S'} {h : S' ⟶ S} (hX : IsPullback a f' f h) {b : Z' ⟶ Z} {π' : Z' ⟶ X'}
    (hZ : IsPullback b π' π a) [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation (π ≫ f)] (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFinitePresentation] [((Scheme.Modules.pushforward π).obj G).IsFinitePresentation]
    (n : ℕ) (W : Set S') :
    IsFlatOverInDimensionsGEOn f'
        ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pushforward π).obj G)) n W ↔
      IsFlatOverInDimensionsGEOn (π' ≫ f') ((Scheme.Modules.pullback b).obj G) n W := by
  have : IsFinite π' := MorphismProperty.of_isPullback hZ inferInstance
  have : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback hX inferInstance
  have : LocallyOfFinitePresentation (π' ≫ f') :=
    MorphismProperty.of_isPullback (hZ.paste_vert hX) inferInstance
  have : ((Scheme.Modules.pullback b).obj G).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_of_isFinitePresentation _
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hZ.w).app G) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hZ G
  let e : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pushforward π).obj G) ≅
      (Scheme.Modules.pushforward π').obj ((Scheme.Modules.pullback b).obj G) :=
    asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hZ.w).app G)
  have : ((Scheme.Modules.pushforward π').obj
      ((Scheme.Modules.pullback b).obj G)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation X'.ringCatSheaf).prop_of_iso e inferInstance
  rw [IsFlatOverInDimensionsGEOn.iff_of_moduleIso e]
  exact (isFlatOverInDimensionsGEOn_pushforward_iff π' f' _ n W).symm

namespace OneStepDevissage

variable {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {F : X.Modules}
  [F.IsQuasicoherent] [F.IsFiniteType] {s : S} (D : OneStepDevissage f F s)

attribute [local instance] OneStepDevissage.quasi_coherent_G OneStepDevissage.finite_type_G
  OneStepDevissage.closed_immersion OneStepDevissage.finite OneStepDevissage.smooth

/-- The composite `Z ⟶ Y ⟶ S` of a one-step dévissage is locally of finite presentation when `X`
is, being `Z ⟶ X ⟶ S`. -/
private theorem locallyOfFinitePresentation_π_comp_g [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (D.π ≫ D.g) := by
  rw [← D.over_base]
  have : LocallyOfFinitePresentation D.i := D.finite_presentation.1
  infer_instance

/-- The direct image of the module on the closed subscheme along the closed immersion of a
one-step dévissage is of finite presentation when `F` is, as it is isomorphic to `F`. -/
private theorem isFinitePresentation_pushforward_i [F.IsFinitePresentation] :
    ((Scheme.Modules.pushforward D.i).obj D.G).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso D.module_iso inferInstance

/-- The finite morphism of a one-step dévissage is locally of finite presentation when `X` is
locally of finite presentation over `S`: the composite `Z ⟶ Y ⟶ S` is, being `Z ⟶ X ⟶ S`, and
`Y ⟶ S` is locally of finite type. -/
theorem locallyOfFinitePresentation_π [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation D.π := by
  have := D.locallyOfFinitePresentation_π_comp_g
  exact locallyOfFinitePresentation_of_comp D.π D.g

/-- The finite morphism of a one-step dévissage is of finite presentation when `X` is locally of
finite presentation over `S`. -/
theorem finitePresentation_π [LocallyOfFinitePresentation f] : FinitePresentation D.π :=
  have := D.locallyOfFinitePresentation_π
  FinitePresentation.mk inferInstance inferInstance inferInstance

/-- The module on the closed subscheme of a one-step dévissage is of finite presentation when `F`
is: its direct image along the closed immersion of finite presentation is `F` (Stacks 05B4). -/
theorem isFinitePresentation_G [F.IsFinitePresentation] : D.G.IsFinitePresentation :=
  (isFinitePresentation_iff_pushforward_isFinitePresentation D.i D.finite_presentation D.G).mpr
    D.isFinitePresentation_pushforward_i

/-- The direct image of the module on the closed subscheme along the finite morphism of a one-step
dévissage is of finite presentation when `F` is and `X` is locally of finite presentation over `S`
(Stacks 05B4). -/
theorem isFinitePresentation_pushforward [LocallyOfFinitePresentation f]
    [F.IsFinitePresentation] :
    ((Scheme.Modules.pushforward D.π).obj D.G).IsFinitePresentation :=
  have := D.isFinitePresentation_G
  (isFinitePresentation_iff_pushforward_isFinitePresentation D.π D.finitePresentation_π D.G).mp
    inferInstance

/-- **Stacks Project, Tag 05UF**, the comparison of the first paragraph of its proof, over the base
itself: `F` is flat over `S` in dimensions `≥ n` over `W` exactly when `π_* G` is. -/
theorem isFlatOverInDimensionsGEOn_iff [LocallyOfFinitePresentation f] [F.IsFinitePresentation]
    (n : ℕ) (W : Set S) :
    IsFlatOverInDimensionsGEOn f F n W ↔
      IsFlatOverInDimensionsGEOn D.g ((Scheme.Modules.pushforward D.π).obj D.G) n W := by
  have := D.isFinitePresentation_G
  have := D.isFinitePresentation_pushforward
  have : LocallyOfFinitePresentation D.i := D.finite_presentation.1
  have := D.isFinitePresentation_pushforward_i
  have := D.locallyOfFinitePresentation_π_comp_g
  rw [IsFlatOverInDimensionsGEOn.iff_of_moduleIso D.module_iso,
    ← isFlatOverInDimensionsGEOn_pushforward_iff D.i f, D.over_base,
    isFlatOverInDimensionsGEOn_pushforward_iff D.π D.g]

/-- **Stacks Project, Tag 05UF**, the comparison of the first paragraph of its proof: for every
scheme `T` over `S`, the base change `F_T` is flat over `T` in dimensions `≥ n` over `W` exactly
when the base change of `π_* G` to `Y_T` is. -/
theorem isFlatOverInDimensionsGEOn_baseChange_iff [LocallyOfFinitePresentation f]
    [F.IsFinitePresentation] (T : Over S) (n : ℕ) (W : Set T.left) :
    IsFlatOverInDimensionsGEOn (pullback.snd f T.hom)
        ((Scheme.Modules.pullback (pullback.fst f T.hom)).obj F) n W ↔
      IsFlatOverInDimensionsGEOn (pullback.snd D.g T.hom)
        ((Scheme.Modules.pullback (pullback.fst D.g T.hom)).obj
          ((Scheme.Modules.pushforward D.π).obj D.G)) n W := by
  have := D.isFinitePresentation_G
  have := D.isFinitePresentation_pushforward
  have : LocallyOfFinitePresentation D.i := D.finite_presentation.1
  have := D.isFinitePresentation_pushforward_i
  have : LocallyOfFinitePresentation (D.i ≫ f) := inferInstance
  have := D.locallyOfFinitePresentation_π_comp_g
  have hX := IsPullback.of_hasPullback f T.hom
  have hZ := IsPullback.of_hasPullback D.i (pullback.fst f T.hom)
  have hY := IsPullback.of_hasPullback D.g T.hom
  let π' : pullback D.i (pullback.fst f T.hom) ⟶ pullback D.g T.hom :=
    pullback.lift (pullback.fst _ _ ≫ D.π) (pullback.snd _ _ ≫ pullback.snd f T.hom) (by
      rw [Category.assoc, ← D.over_base, ← Category.assoc, pullback.condition,
        Category.assoc, pullback.condition, Category.assoc])
  have hπ'snd : π' ≫ pullback.snd D.g T.hom =
      pullback.snd D.i (pullback.fst f T.hom) ≫ pullback.snd f T.hom :=
    pullback.lift_snd _ _ _
  have hZY : IsPullback (pullback.fst D.i (pullback.fst f T.hom)) π' D.π
      (pullback.fst D.g T.hom) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm hY
    rw [hπ'snd, ← D.over_base]
    exact hZ.paste_vert hX
  rw [IsFlatOverInDimensionsGEOn.iff_of_moduleIso
      ((Scheme.Modules.pullback (pullback.fst f T.hom)).mapIso D.module_iso),
    isFlatOverInDimensionsGEOn_pullback_pushforward_iff D.i f hX hZ,
    isFlatOverInDimensionsGEOn_pullback_pushforward_iff D.π D.g hY hZY, hπ'snd]

end OneStepDevissage

namespace DevissageStage

variable {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {F : X.Modules}
  [F.IsQuasicoherent] [F.IsFiniteType] {s : S}

attribute [local instance] OneStepDevissage.quasi_coherent_G OneStepDevissage.finite_type_G
  OneStepDevissage.closed_immersion OneStepDevissage.finite OneStepDevissage.smooth

/-- **Flatness at the generic point of the fibre, in the case `d₁ > d` of Stacks 05UF.** If
`π_* G` is flat over `S` in dimensions `≥ n + 1` at the points over an open containing `s`, and
the fibre of the smooth scheme of the stage over `s` has dimension `> n`, then `π_* G` is flat
over `S` at the generic point of that fibre: otherwise the non-flat locus of the fibre, being
closed, would be the whole irreducible fibre, of dimension `≥ n + 1`. -/
theorem isFlatOverAt_genericPoint_of_lt (stage : DevissageStage f F s) (n : ℕ)
    (hf : FinitePresentation f) [F.IsFinitePresentation] {V : S.Opens} (hs : s ∈ V)
    (h : IsFlatOverInDimensionsGEOn stage.oneStep.g
      ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G) (n + 1) V)
    (hlt : (n : WithBot ℕ∞) < topologicalKrullDim (stage.oneStep.g.fiber s)) :
    IsFlatOverAt stage.oneStep.g.toLRSHom.toShHom
      ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G)
      (stage.oneStep.g.fiberι s stage.genericPoint) := by
  have : LocallyOfFinitePresentation f := hf.1
  have := stage.oneStep.isFinitePresentation_pushforward
  have : ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _
  set g := stage.oneStep.g
  set M := (Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G
  by_contra hnf
  set N : Set (g.fiber s) := {y | ¬ IsFlatOverAt g.toLRSHom.toShHom M (g.fiberι s y)} with hN
  have hdimN : topologicalKrullDim ↥N < ((n + 1 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff_isFlatOverInDimensionsGEOn g M (n + 1)
      s).2 (h.mono (Set.singleton_subset_iff.mpr hs))
  have hNsub : closure ({stage.genericPoint} : Set (g.fiber s)) ⊆ N :=
    closure_minimal (Set.singleton_subset_iff.mpr hnf)
      (isOpen_isFlatOverAt_fiber_of_locallyOfFiniteType g M s).isClosed_compl
  have hNuniv : N = Set.univ := by
    rw [show closure ({stage.genericPoint} : Set (g.fiber s)) = Set.univ from
      stage.genericPoint_spec] at hNsub
    exact Set.eq_univ_of_univ_subset hNsub
  have hdim : topologicalKrullDim ↥N = topologicalKrullDim (g.fiber s) :=
    IsHomeomorph.topologicalKrullDim_eq _
      ((Homeomorph.setCongr hNuniv).trans (Homeomorph.Set.univ (g.fiber s))).isHomeomorph
  rw [hdim] at hdimN
  generalize topologicalKrullDim (g.fiber s) = a at hdimN hlt
  induction a using WithBot.recBotCoe with
  | bot => exact not_lt_bot hlt
  | coe e =>
    have h1 : e < ((n + 1 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.mp hdimN
    have h2 : (n : ℕ∞) < e := WithBot.coe_lt_coe.mp hlt
    have h3 := Order.add_one_le_of_lt h2
    push_cast at h1
    exact absurd h1 (not_lt.mpr h3)

end DevissageStage

end AlgebraicGeometry

end
