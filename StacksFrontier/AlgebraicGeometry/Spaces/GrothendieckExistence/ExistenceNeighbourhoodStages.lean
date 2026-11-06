module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhoodProperSupport
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointCompIsoHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedCoheratorGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
/-!
# The identifications `H⁰(K)|_{Xₙ} ≅ Fₙ` of an existence neighbourhood

In Situation [Stacks, Tag 0CX4] let `K` be an object of `D(𝒪_X)` with maps `πₙ : K ⟶ Fₙ` and let
`W ⊆ X` be an open subspace with the three conclusions of [Stacks, Tag 0CX9]
(`AlgebraicGeometry.Space.FlatSheafExistenceSituation.IsExistenceNeighbourhood`). Part (3) of those
conclusions says that the comparisons `iₙ^* H⁰(K) ⟶ Fₙ` induced by the `πₙ` are isomorphisms on
`W ×_X Xₙ`. The proof of [Stacks, Tag 0CXB] uses them on all of `Xₙ` and compatibly with the
isomorphisms `φₙ`; this file proves both.

## Main definitions

* `ModulePullbackCompatible`: compatibility of two identifications along a factorization
  `t ≫ i' = i` with an isomorphism `φ : t^* F'' ≅ F'`.

## Main results

* `modulePullback_map_homEquiv_symm_comp_of_comp_eq`: adjoints of maps `H ⟶ i'_* F''` and
  `H ⟶ i_* F'` compatible with the map induced by `φ` are compatible with `φ`.
* `FlatSheafExistenceSituation.range_closedImmersion_subset_pointsOverFirstStage`: every `Xₙ` lies
  over the closed fibre `X₀`.
* `FlatSheafExistenceSituation.IsExistenceNeighbourhood.isIso_stageComparison_stage`: on an
  existence neighbourhood the comparisons `iₙ^* H⁰(K) ⟶ Fₙ` are isomorphisms.
* `FlatSheafExistenceSituation.stageComparison_compatible`: for compatible `πₙ` they are compatible
  with the `φₙ`.
* `FlatSheafExistenceSituation.derivedLimitProjection_comp_map`: the maps `K ⟶ Fₙ` of a derived
  limit `K = DQ_X(R lim Fₙ)` are compatible.

## References

* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
* [Stacks Project, Tag 0CX4](https://stacks.math.columbia.edu/tag/0CX4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **Compatibility of identifications along a factorization `t ≫ i' = i`.** Maps
`b' : i'^* H ⟶ F''` and `b : i^* H ⟶ F'` are compatible with `φ : t^* F'' ≅ F'` when `φ ∘ t^* b'`
is `b` under the comparison `t^* i'^* H ≅ (t ≫ i')^* H = i^* H`. -/
structure ModulePullbackCompatible {X X' X'' : AlgebraicSpaces B S hS}
    (t : X' ⟶ X'') (i' : X'' ⟶ X) (i : X' ⟶ X) (h : t ≫ i' = i)
    (H : Modules.{u, u} B S hS X.1 X.2) {F'' : Modules.{u, u} B S hS X''.1 X''.2}
    {F' : Modules.{u, u} B S hS X'.1 X'.2} (φ : (modulePullback B S hS t).obj F'' ≅ F')
    (b' : (modulePullback B S hS i').obj H ⟶ F'') (b : (modulePullback B S hS i).obj H ⟶ F') :
    Prop where
  /-- The compatibility equation. -/
  eq : (modulePullback B S hS t).map b' ≫ φ.hom =
    (modulePullbackCompIso B S hS t i').hom.app H ≫
      eqToHom (congrArg (fun g => (modulePullback B S hS g).obj H) h) ≫ b

/-- **Compatibility of adjoints in pullback form.** Let `t ≫ i' = i`, let `φ : t^* F'' ≅ F'`, and
let `d'' : H ⟶ i'_* F''` and `d' : H ⟶ i_* F'` be compatible with the map `i'_* F'' ⟶ i_* F'`
induced by `φ`, that is `i'_*` of the adjoint `τ` of `φ` followed by `i'_* t_* = (t ≫ i')_* = i_*`
(`e`). Then the adjoints `i'^* H ⟶ F''` and `i^* H ⟶ F'` are compatible with `φ`, through the
comparison `t^* i'^* ≅ (t ≫ i')^* = i^*`. -/
theorem modulePullback_map_homEquiv_symm_comp_of_comp_eq {X X' X'' : AlgebraicSpaces B S hS}
    (t : X' ⟶ X'') (i' : X'' ⟶ X) (i : X' ⟶ X) (h : t ≫ i' = i)
    (H : Modules.{u, u} B S hS X.1 X.2) {F'' : Modules.{u, u} B S hS X''.1 X''.2}
    {F' : Modules.{u, u} B S hS X'.1 X'.2} (φ : (modulePullback B S hS t).obj F'' ≅ F')
    (d'' : H ⟶ (modulePushforward B S hS i').obj F'') (d' : H ⟶ (modulePushforward B S hS i).obj F')
    (τ : F'' ⟶ (modulePushforward B S hS t).obj F')
    (hτ : τ = (modulePullbackAdjunction B S hS t).unit.app F'' ≫
      (modulePushforward B S hS t).map φ.hom)
    (e : (modulePushforward B S hS i').obj ((modulePushforward B S hS t).obj F') ≅
      (modulePushforward B S hS i).obj F')
    (h' : (modulePushforward B S hS (t ≫ i')).obj F' = (modulePushforward B S hS i).obj F')
    (he : e = (modulePushforwardCompIso B S hS t i').app F' ≪≫ eqToIso h')
    (hd : d'' ≫ (modulePushforward B S hS i').map τ ≫ e.hom = d') :
    ModulePullbackCompatible t i' i h H φ
      (((modulePullbackAdjunction B S hS i').homEquiv _ _).symm d'')
      (((modulePullbackAdjunction B S hS i).homEquiv _ _).symm d') := by
  refine ⟨?_⟩
  subst h hτ he
  simp only [eqToIso_refl, Iso.trans_refl, Iso.app_hom, eqToHom_refl, Category.id_comp] at hd ⊢
  rw [← Iso.app_hom, ← Iso.inv_comp_eq, Iso.app_inv]
  apply ((modulePullbackAdjunction B S hS (t ≫ i')).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, ← hd]
  have key := Adjunction.homEquiv_leftAdjointCompIso_inv_app
    (modulePullbackAdjunction B S hS i') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS (t ≫ i')) (modulePushforwardCompIso B S hS t i')
    (((modulePullbackAdjunction B S hS i').homEquiv _ _).symm d'') φ.hom
  rw [← modulePullbackCompIso_eq_leftAdjointCompIso] at key
  rw [key, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- The map `H⁰(K) ⟶ iₙ,* Fₙ` induced by `πₙ : K ⟶ iₙ,* Fₙ`, of which
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageComparison` is the adjoint. -/
abbrev stageHomologyMap (K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)) (n : ℕ) :
    (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj K ⟶ D.pushforwardModule n :=
  (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).map (π n) ≫
    ((@DerivedCategory.singleFunctorCompHomologyFunctorIso _ _
      (modulesAbelianSmallEtale D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2)
      (spaceHasDerivedCategory D.B D.S D.containsLimitBase D.X.left) 0).app
        (D.pushforwardModule n)).hom

/-- If the maps `πₙ` are compatible with the transition maps of the system, so are the induced
maps `H⁰(K) ⟶ iₙ,* Fₙ`. -/
theorem stageHomologyMap_comp_pushforwardTransition
    (K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n))
    (hπ : ∀ n : ℕ, π (n + 1) ≫ D.derivedSystem.map (homOfLE (Nat.le_succ n)).op = π n)
    (n : ℕ) :
    D.stageHomologyMap K π (n + 1) ≫ D.pushforwardTransition n = D.stageHomologyMap K π n := by
  have hmap : D.derivedSystem.map (homOfLE (Nat.le_succ n)).op =
      (spaceDerivedSingle D.B D.S D.containsLimitBase D.X.left 0).map
        (D.pushforwardTransition n) := by
    rw [Functor.comp_map, pushforwardSystem_map_succ]
    rfl
  let ε := @DerivedCategory.singleFunctorCompHomologyFunctorIso _ _
    (modulesAbelianSmallEtale D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2)
    (spaceHasDerivedCategory D.B D.S D.containsLimitBase D.X.left) 0
  have e1 : (ε.app (D.pushforwardModule (n + 1))).hom ≫ D.pushforwardTransition n =
      (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).map
        (D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) ≫
          (ε.app (D.pushforwardModule n)).hom := by
    rw [hmap]
    exact (ε.hom.naturality (D.pushforwardTransition n)).symm
  calc D.stageHomologyMap K π (n + 1) ≫ D.pushforwardTransition n
      = (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).map (π (n + 1)) ≫
          ((ε.app (D.pushforwardModule (n + 1))).hom ≫ D.pushforwardTransition n) :=
        Category.assoc _ _ _
    _ = (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).map (π (n + 1)) ≫
          (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).map
            (D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) ≫
          (ε.app (D.pushforwardModule n)).hom :=
        congrArg (fun f => (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).map
          (π (n + 1)) ≫ f) e1
    _ = (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).map
            (π (n + 1) ≫ D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) ≫
          (ε.app (D.pushforwardModule n)).hom := by
        rw [Functor.map_comp]
        exact (Category.assoc _ _ _).symm
    _ = D.stageHomologyMap K π n := by rw [hπ n]

/-- The adjoint `transitionAdjoint n` of `φₙ` is the unit of `tₙ^* ⊣ tₙ,*` at `Fₙ₊₁` followed by
`tₙ,*` of `φₙ`. -/
theorem transitionAdjoint_eq (n : ℕ) :
    D.transitionAdjoint n =
      (modulePullbackAdjunction D.B D.S D.containsLimitBase (D.transition n)).unit.app
          (D.F (n + 1)) ≫
        (modulePushforward D.B D.S D.containsLimitBase (D.transition n)).map (D.φ n).hom := rfl

/-- The isomorphism `pushforwardCompIso n` is the comparison `iₙ₊₁,* tₙ,* Fₙ ≅ (tₙ ≫ iₙ₊₁)_* Fₙ`
followed by the identification `(tₙ ≫ iₙ₊₁)_* Fₙ = iₙ,* Fₙ`. -/
theorem pushforwardCompIso_eq (n : ℕ) (h : (modulePushforward D.B D.S D.containsLimitBase
      (D.transition n ≫ D.closedImmersion (n + 1))).obj (D.F n) = D.pushforwardModule n) :
    D.pushforwardCompIso n = (modulePushforwardCompIso D.B D.S D.containsLimitBase (D.transition n)
      (D.closedImmersion (n + 1))).app (D.F n) ≪≫ eqToIso h := by
  unfold pushforwardCompIso
  rfl

/-- The transition map `iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ` is `iₙ₊₁,*` of the adjoint `transitionAdjoint n`
of `φₙ`, followed by `pushforwardCompIso n`. -/
theorem pushforwardTransition_eq_comp (n : ℕ) :
    D.pushforwardTransition n =
      (modulePushforward D.B D.S D.containsLimitBase (D.closedImmersion (n + 1))).map
        (D.transitionAdjoint n) ≫ (D.pushforwardCompIso n).hom := rfl

/-- **The identifications of an existence neighbourhood are compatible with the `φₙ`.** If the
maps `πₙ : K ⟶ iₙ,* Fₙ` are compatible with the transition maps of the system, the maps
`iₙ^* H⁰(K) ⟶ Fₙ` they induce are compatible with the isomorphisms `φₙ`. -/
theorem stageComparison_compatible
    (K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n))
    (hπ : ∀ n : ℕ, π (n + 1) ≫ D.derivedSystem.map (homOfLE (Nat.le_succ n)).op = π n)
    (n : ℕ) :
    ModulePullbackCompatible (D.transition n) (D.closedImmersion (n + 1)) (D.closedImmersion n)
      (D.transition_closedImmersion n)
      ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj K) (D.φ n)
      (D.stageComparison K π (n + 1)) (D.stageComparison K π n) := by
  have hh : (modulePushforward D.B D.S D.containsLimitBase
      (D.transition n ≫ D.closedImmersion (n + 1))).obj (D.F n) = D.pushforwardModule n := by
    rw [D.transition_closedImmersion]
  exact modulePullback_map_homEquiv_symm_comp_of_comp_eq (D.transition n)
    (D.closedImmersion (n + 1)) (D.closedImmersion n) (D.transition_closedImmersion n) _ (D.φ n)
    (D.stageHomologyMap K π (n + 1)) (D.stageHomologyMap K π n) (D.transitionAdjoint n)
    (D.transitionAdjoint_eq n) (D.pushforwardCompIso n) hh (D.pushforwardCompIso_eq n hh)
    ((congrArg (fun f => D.stageHomologyMap K π (n + 1) ≫ f)
      (D.pushforwardTransition_eq_comp n)).symm.trans
      (D.stageHomologyMap_comp_pushforwardTransition K π hπ n))


/-! ### Every stage lies over the closed fibre -/

/-- The transition `Spec Aₙ ⟶ Spec Aₙ₊₁` of affine bases is surjective on points: its kernel is
locally nilpotent, so it lies in every prime. -/
theorem surjective_pointsMap_baseSpaceTransition (n : ℕ) :
    Function.Surjective (pointsMap D.B D.S D.containsLimitBase
      (schemeSpace (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).1
      (baseSpaceTransition D.system D.B D.containsLimitBase D.containsBaseAt n).hom) := by
  have hsurj : Function.Surjective ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).map
      (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)) := by
    intro t
    let p : PrimeSpectrum (D.system.obj (op (n + 1))) := t
    have hmem : p ∈
        Set.range (PrimeSpectrum.comap (D.system.map (homOfLE (Nat.le_succ n)).op).hom) := by
      rw [range_comap_of_surjective _ _ (D.transition_surjective n)]
      intro x hx
      obtain ⟨m, hm⟩ := D.transition_locallyNilpotent n x hx
      exact p.2.mem_of_pow_mem m (hm ▸ p.asIdeal.zero_mem)
    exact hmem
  intro t
  obtain ⟨σ, hσ⟩ := hsurj (schemePointsHomeomorph D.B D.S D.containsLimitBase _ t)
  refine ⟨(schemePointsHomeomorph D.B D.S D.containsLimitBase _).symm σ, ?_⟩
  show pointsMap D.B D.S D.containsLimitBase _
    (yoneda.map (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n))
    ((schemePointsHomeomorph D.B D.S D.containsLimitBase _).symm σ) = t
  rw [schemePointsHomeomorph_symm_naturality, hσ]
  exact Homeomorph.symm_apply_apply _ _

/-- Every point of `Xₙ₊₁` comes from `Xₙ`. -/
theorem range_closedImmersion_succ_subset (n : ℕ) :
    Set.range (pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion (n + 1)).hom) ⊆
      Set.range (pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion n).hom) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨t', ht'⟩ := D.surjective_pointsMap_baseSpaceTransition n
    (pointsMap D.B D.S D.containsLimitBase _ (D.stageToBase (n + 1)).hom x)
  obtain ⟨w, -, hw⟩ := exists_point_of_isPullback D.B D.S D.containsLimitBase
    (isPullback_transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n) t' x ht'
  refine ⟨w, ?_⟩
  rw [← hw, ← Function.comp_apply (f := pointsMap D.B D.S D.containsLimitBase _
    (D.closedImmersion (n + 1)).hom), ← pointsMap_comp, ← D.transition_closedImmersion n]
  rfl

/-- **Every stage `Xₙ` lies over the closed fibre**: its points are among the points `X₀` of `X`
over `Spec A₁ ⊆ Spec A`. -/
theorem range_closedImmersion_subset_pointsOverFirstStage (n : ℕ) :
    Set.range (pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion n).hom) ⊆
      D.pointsOverFirstStage := by
  induction n with
  | zero => exact D.range_closedImmersion_zero.le
  | succ n ih => exact (D.range_closedImmersion_succ_subset n).trans ih

/-! ### The identifications on the stages -/

/-- **The comparison `iₙ^* H⁰(K) ⟶ Fₙ` is an isomorphism** as soon as `Xₙ ⟶ X` factors through
an open subspace on which it is an isomorphism after restriction. -/
theorem isIso_stageComparison_of_range_subset
    {K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    {π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)} {W : Subfunctor D.X.left.1}
    {hW : IsOpenSubspace D.B D.S D.containsLimitBase W}
    (hN : D.IsExistenceNeighbourhood K π W hW) (n : ℕ)
    (hn : Set.range (pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion n).hom) ⊆
      Set.range (pointsMap D.B D.S D.containsLimitBase W.toFunctor W.ι)) :
    IsIso (D.stageComparison K π n) := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points D.B D.S D.containsLimitBase
    D.X.left.2 (D.stage n).2 W hW (D.closedImmersion n).hom).2 hn
  have hle : Subfunctor.range (𝟙 (D.stage n).1) ≤ D.stagePreimage W n := by
    rintro U _ ⟨x, rfl⟩
    show (D.closedImmersion n).hom.app U x ∈ W.obj U
    rw [← hg]
    exact (g.app U x).2
  let s : D.stage n ⟶ openSubspaceSpace D.B D.S D.containsLimitBase (D.stagePreimage W n)
      (D.isOpenSubspace_stagePreimage hW n) :=
    ObjectProperty.homMk (Subfunctor.lift (𝟙 _) hle)
  have hs : s ≫ openSubspaceHom D.B D.S D.containsLimitBase (D.stagePreimage W n)
      (D.isOpenSubspace_stagePreimage hW n) = 𝟙 _ :=
    ObjectProperty.hom_ext _ (Subfunctor.lift_ι (𝟙 _) hle)
  have := hN.isIso_stageComparison n
  refine (NatIso.isIso_map_iff ((modulePushforwardCoherence D.B D.S
    D.containsLimitBase).modulePullbackIdIso (D.stage n)).symm (D.stageComparison K π n)).2 ?_
  refine (NatIso.isIso_map_iff (modulePullbackTriangle D.B D.S D.containsLimitBase hs)
    (D.stageComparison K π n)).2 ?_
  rw [Functor.comp_map]
  infer_instance

/-- **On an existence neighbourhood the comparisons `iₙ^* H⁰(K) ⟶ Fₙ` are isomorphisms on all of
`Xₙ`**, every `Xₙ` lying over the closed fibre, which the neighbourhood contains. -/
theorem IsExistenceNeighbourhood.isIso_stageComparison_stage
    {K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    {π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)} {W : Subfunctor D.X.left.1}
    {hW : IsOpenSubspace D.B D.S D.containsLimitBase W}
    (hN : D.IsExistenceNeighbourhood K π W hW) (n : ℕ) :
    IsIso (D.stageComparison K π n) :=
  D.isIso_stageComparison_of_range_subset hN n
    ((D.range_closedImmersion_subset_pointsOverFirstStage n).trans hN.subset_range)

end FlatSheafExistenceSituation

section DerivedLimit

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- **The maps to the levels of a derived limit are compatible.** For a distinguished triangle
`L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` presenting `L` as the derived limit of the system, with second map
`(xₙ) ↦ (xₙ - tₙ(xₙ₊₁))`, the projections `L ⟶ Fₙ` commute with the transition maps. -/
theorem derivedLimitProjection_comp_map
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    {L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)
    {δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧}
    (hT : Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
        D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang _)
    (n : ℕ) :
    D.derivedLimitProjection adj p (n + 1) ≫ D.derivedSystem.map (homOfLE (Nat.le_succ n)).op =
      D.derivedLimitProjection adj p n := by
  let := spaceHasDerivedCategory D.B D.S D.containsLimitBase D.X.left
  have h1 := congrArg (· ≫ Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n)
    (comp_distTriang_mor_zero₁₂ _ hT)
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₁,
    Triangle.mk_mor₂, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, zero_comp,
    sub_eq_zero] at h1
  simp only [derivedLimitProjection, Category.assoc]
  rw [h1]

end FlatSheafExistenceSituation

end DerivedLimit

end AlgebraicGeometry.Space

end
