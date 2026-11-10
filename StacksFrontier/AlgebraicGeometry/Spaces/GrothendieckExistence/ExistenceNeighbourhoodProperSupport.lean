module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ProperSupportNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability

/-!
# The support of `H⁰(K)` near the closed fibre is proper over `A`

In Situation [Stacks, Tag 0CX4] let `K` be as in [Stacks, Tag 0CX5] and `W ⊂ X` as in
[Stacks, Tag 0CX9]. [Stacks, Tag 0CXA] says that, after possibly shrinking `W`, the support of
`F = H⁰(K)|_W` is proper over `A`.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.range_closedImmersion_zero`: the points of
  `X₀ ⊂ |X|` are the points of the first infinitesimal stage.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.IsExistenceNeighbourhood.mono`: the three
  conclusions of Stacks 0CX9 persist on a smaller open subspace still containing `X₀`; this is
  what "possibly shrinking `W`" leaves intact.
* `FlatSheafExistenceSituation.exists_isExistenceNeighbourhood_hasProperSupport`:
  **Stacks 0CXA**, for every object `K` with maps `πₙ : K ⟶ Fₙ` and every open subspace `W`
  with the three conclusions of Stacks 0CX9.

## Implementation notes

The source's proof uses of `K` and `W` only that `F = H⁰(K)|_W` is of finite presentation and
that `F ⊗ 𝒪_{X₁} = F₁`; so the statement is proved for every `K` and `W` with the conclusions of
Stacks 0CX9, the `K` of Stacks 0CX5 and the `W` of Stacks 0CX9 being one instance. The level
used is the first one, index `0`, whose points are exactly `X₀`.

The shrunk open is again a neighbourhood with the three conclusions of Stacks 0CX9, so the
statement says that the support is proper over `A` for a `W` as in Stacks 0CX9, which is how the
source continues to use it (Stacks 0CXB).

Stacks 0CWI enters through
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.exists_isOpenSubspace_hasProperSupport`.

## References

* [Stacks Project, Tag 0CXA](https://stacks.math.columbia.edu/tag/0CXA)
* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
* [Stacks Project, Tag 0CWI](https://stacks.math.columbia.edu/tag/0CWI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- **The points of `X₀ ⊂ |X|` are the points of the first infinitesimal stage `X₁ ⊂ X`.** A point
of `X` lies over the image of `Spec A₁` exactly when it comes from the fibre product
`X₁ = Spec A₁ ×_{Spec A} X`. -/
theorem range_closedImmersion_zero :
    Set.range (pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion 0).hom) =
      D.pointsOverFirstStage := by
  have sq := IsPullback.of_hasPullback
    (baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt 0).hom D.X.hom.hom
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨pointsMap D.B D.S D.containsLimitBase _ (D.stageToBase 0).hom y, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply]
    exact congrArg (fun m => pointsMap D.B D.S D.containsLimitBase _ m y) pullback.condition
  · rintro ⟨t, ht⟩
    obtain ⟨w, -, hw⟩ := exists_points_of_isPullback D.B D.S D.containsLimitBase sq t x ht
    exact ⟨w, hw⟩

/-- **The conclusions of Stacks 0CX9 persist on a smaller open subspace containing `X₀`.**
Restriction to `W' ⊆ W` is the inverse image along `W' ⟶ W` of the restriction to `W`, which
carries zero modules to zero modules (it is a left adjoint), modules of finite presentation to
modules of finite presentation, and isomorphisms to isomorphisms. -/
theorem IsExistenceNeighbourhood.mono
    {K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    {π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)} {W W' : Subfunctor D.X.left.1}
    {hW : IsOpenSubspace D.B D.S D.containsLimitBase W}
    (hN : D.IsExistenceNeighbourhood K π W hW)
    (hW' : IsOpenSubspace D.B D.S D.containsLimitBase W') (hle : W' ≤ W)
    (h₀ : D.pointsOverFirstStage ⊆
      Set.range (pointsMap D.B D.S D.containsLimitBase W'.toFunctor W'.ι)) :
    D.IsExistenceNeighbourhood K π W' hW' := by
  let r : openSubspaceSpace D.B D.S D.containsLimitBase W' hW' ⟶
      openSubspaceSpace D.B D.S D.containsLimitBase W hW :=
    ObjectProperty.homMk (Subfunctor.homOfLe hle)
  have hk : r ≫ openSubspaceHom D.B D.S D.containsLimitBase W hW =
      openSubspaceHom D.B D.S D.containsLimitBase W' hW' :=
    ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι hle)
  have := (modulePullbackAdjunction D.B D.S D.containsLimitBase r).isLeftAdjoint
  refine ⟨h₀, fun i hi => ?_, ?_, fun n => ?_⟩
  · exact (Functor.map_isZero (modulePullback D.B D.S D.containsLimitBase r)
      (hN.isZero_homology i hi)).of_iso
      ((modulePullbackTriangle D.B D.S D.containsLimitBase hk).app _)
  · exact SheafOfModules.IsFinitePresentationOnSite.of_iso
      ((modulePullbackTriangle D.B D.S D.containsLimitBase hk).app _).symm
      (isFinitePresentationOnSite_modulePullback D.B D.S D.containsLimitBase r _
        hN.isFinitePresentation)
  · have hlen : D.stagePreimage W' n ≤ D.stagePreimage W n := fun U x hx => hle _ hx
    let rn : openSubspaceSpace D.B D.S D.containsLimitBase (D.stagePreimage W' n)
          (D.isOpenSubspace_stagePreimage hW' n) ⟶
        openSubspaceSpace D.B D.S D.containsLimitBase (D.stagePreimage W n)
          (D.isOpenSubspace_stagePreimage hW n) :=
      ObjectProperty.homMk (Subfunctor.homOfLe hlen)
    have hkn : rn ≫ openSubspaceHom D.B D.S D.containsLimitBase (D.stagePreimage W n)
          (D.isOpenSubspace_stagePreimage hW n) =
        openSubspaceHom D.B D.S D.containsLimitBase (D.stagePreimage W' n)
          (D.isOpenSubspace_stagePreimage hW' n) :=
      ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι hlen)
    have := hN.isIso_stageComparison n
    refine (NatIso.isIso_map_iff (modulePullbackTriangle D.B D.S D.containsLimitBase hkn) _).2 ?_
    rw [Functor.comp_map]
    infer_instance

/-- **Stacks 0CXA.** In Situation 0CX4 let `K` be an object of `D(𝒪_X)` with maps
`πₙ : K ⟶ Fₙ`, and let `W ⊆ X` be an open subspace with the conclusions of Stacks 0CX9
(`D.IsExistenceNeighbourhood K π W hW`). Then, after shrinking `W` to an open subspace `W'` which
still has the conclusions of Stacks 0CX9, the support of `F = H⁰(K)|_{W'}` is proper over `A`.

This covers the source's statement as written: its `K` is that of Stacks 0CX5,
`K = DQ_X(R lim Fₙ)`, here `(spaceQuasicoherentProp _ _ _ _).ι.obj (DQ.obj L)` with the maps
`D.derivedLimitProjection adj p` for a coherator `adj : ι ⊣ DQ` and a triangle `p` presenting
`L = R lim_{D(𝒪_X)} Fₙ`, and its `W` is any open subspace with the conclusions of Stacks 0CX9
for that `K`, which is what `D.IsExistenceNeighbourhood K π W hW` says; the statement below is
the special case of the one for every `K` and every such `W`.

The source's proof, at the first level: `F` restricted to `X₁` is `F₁` by part (3) of
Stacks 0CX9, since `W` contains `X₀ = |X₁|`; so the support of `F` meets `X₁` in the support of
`F₁`, proper over `A₁`, and
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.exists_isOpenSubspace_hasProperSupport`
(the henselian pair `(A, Ker(A → A₁))` and Stacks 0CWI) shrinks `W`. -/
@[stacks 0CXA "the full statement: for every K with maps to the Fₙ (in particular the K of 0CX5 \
with its canonical maps) and every W with the three conclusions of 0CX9, a smaller open W', \
still with those conclusions, on which the support of H⁰(K)|_W' is proper over A; nothing is \
granted or assumed"]
theorem exists_isExistenceNeighbourhood_hasProperSupport
    {K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    {π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)} {W : Subfunctor D.X.left.1}
    {hW : IsOpenSubspace D.B D.S D.containsLimitBase W}
    (hN : D.IsExistenceNeighbourhood K π W hW) :
    ∃ (W' : Subfunctor D.X.left.1) (hW' : IsOpenSubspace D.B D.S D.containsLimitBase W')
      (_ : W' ≤ W), D.IsExistenceNeighbourhood K π W' hW' ∧
      ∃ hlft : IsLocallyOfFiniteType D.B D.S D.containsLimitBase (W'.ι ≫ D.X.hom.hom),
        HasProperSupport D.B D.S D.containsLimitBase hW'.1
          (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2
          (W'.ι ≫ D.X.hom.hom) hlft
          ((SheafOfModules.toSheaf _).obj
            ((modulePullback D.B D.S D.containsLimitBase
              (openSubspaceHom D.B D.S D.containsLimitBase W' hW')).obj
                ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj K))) := by
  let H₀ := (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj K
  let FW := (modulePullback D.B D.S D.containsLimitBase
    (openSubspaceHom D.B D.S D.containsLimitBase W hW)).obj H₀
  have : FW.IsFinitePresentationOnSite := hN.isFinitePresentation
  have hqc : FW.IsQuasicoherentOnSite := inferInstance
  have hft : SheafOfModules.IsFiniteTypeOnSite FW := inferInstance
  -- `X₁ ⟶ X` factors through `W`
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points D.B D.S D.containsLimitBase
    D.X.left.2 (D.stage 0).2 W hW (D.closedImmersion 0).hom).2
      (D.range_closedImmersion_zero ▸ hN.subset_range)
  let k : D.stage 0 ⟶ (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces D.B D.S D.containsLimitBase) :=
    ObjectProperty.homMk g
  have hkX : k ≫ openSubspaceHom D.B D.S D.containsLimitBase W hW = D.closedImmersion 0 :=
    ObjectProperty.hom_ext _ hg
  -- the comparison `i₁^* H⁰(K) ⟶ F₁` is an isomorphism, `W₁ ⟶ X₁` having a section
  have hle₀ : Subfunctor.range (𝟙 (D.stage 0).1) ≤ D.stagePreimage W 0 := by
    rintro U _ ⟨x, rfl⟩
    change (D.closedImmersion 0).hom.app U x ∈ W.obj U
    rw [← hg]
    exact (g.app U x).2
  let s : D.stage 0 ⟶ openSubspaceSpace D.B D.S D.containsLimitBase (D.stagePreimage W 0)
      (D.isOpenSubspace_stagePreimage hW 0) :=
    ObjectProperty.homMk (Subfunctor.lift (𝟙 _) hle₀)
  have hs : s ≫ openSubspaceHom D.B D.S D.containsLimitBase (D.stagePreimage W 0)
      (D.isOpenSubspace_stagePreimage hW 0) = 𝟙 _ :=
    ObjectProperty.hom_ext _ (Subfunctor.lift_ι (𝟙 _) hle₀)
  have hφ : IsIso (D.stageComparison K π 0) := by
    have := hN.isIso_stageComparison 0
    refine (NatIso.isIso_map_iff ((modulePushforwardCoherence D.B D.S
      D.containsLimitBase).modulePullbackIdIso (D.stage 0)).symm
        (D.stageComparison K π 0)).2 ?_
    refine (NatIso.isIso_map_iff (modulePullbackTriangle D.B D.S D.containsLimitBase hs)
      (D.stageComparison K π 0)).2 ?_
    rw [Functor.comp_map]
    infer_instance
  let eF : (modulePullback D.B D.S D.containsLimitBase k).obj FW ≅ D.F 0 :=
    ((modulePullbackTriangle D.B D.S D.containsLimitBase hkX).app H₀).symm ≪≫
      asIso (D.stageComparison K π 0)
  obtain ⟨W', hW', hle, hrange, hlft, hprop⟩ :=
    D.exists_isOpenSubspace_hasProperSupport 0 W hW k hg FW hqc hft eF
  refine ⟨W', hW', hle, IsExistenceNeighbourhood.mono D hN hW' hle
    (D.range_closedImmersion_zero ▸ hrange), hlft, ?_⟩
  -- the restriction of `F` to `W'` is the inverse image of `FW` along `W' ⟶ W`
  let r : (⟨W'.toFunctor, hW'.1⟩ : AlgebraicSpaces D.B D.S D.containsLimitBase) ⟶
      ⟨W.toFunctor, hW.1⟩ := ObjectProperty.homMk (Subfunctor.homOfLe hle)
  have hr : r ≫ openSubspaceHom D.B D.S D.containsLimitBase W hW =
      openSubspaceHom D.B D.S D.containsLimitBase W' hW' :=
    ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι hle)
  have hset := supportOfSheaf_eq_of_iso D.B D.S D.containsLimitBase
    (⟨W'.toFunctor, hW'.1⟩ : AlgebraicSpaces D.B D.S D.containsLimitBase)
    ((modulePullbackTriangle D.B D.S D.containsLimitBase hr).app H₀).symm
  obtain ⟨hcl, hp⟩ := hprop
  have key : ∀ (T T' : Set (points D.B D.S D.containsLimitBase W'.toFunctor)) (_ : T = T')
      (hT : IsClosed T) (hT' : IsClosed T'),
      IsProperOver D.B D.S D.containsLimitBase hW'.1
          (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2
          (W'.ι ≫ D.X.hom.hom) hlft T hT →
        IsProperOver D.B D.S D.containsLimitBase hW'.1
          (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2
          (W'.ι ≫ D.X.hom.hom) hlft T' hT' := by
    rintro T _ rfl _ _ h
    exact h
  exact ⟨hset ▸ hcl, key _ _ hset hcl _ hp⟩

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
