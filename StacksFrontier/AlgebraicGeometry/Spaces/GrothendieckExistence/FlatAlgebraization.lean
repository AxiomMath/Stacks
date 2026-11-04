module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhoodStages
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.RelativePseudoCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFlatteningExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionDirectImageSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Monomorphism

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedCoheratorGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
/-!
# Grothendieck's existence theorem for algebraic spaces: the algebraization

In Situation [Stacks, Tag 0CX4], let `K` be an object of `D(𝒪_X)` with compatible maps
`πₙ : K ⟶ Fₙ` and let `W ⊆ X` be an open subspace containing the closed fibre on which `H⁰(K)` is
a finitely presented module restricting to the `Fₙ`. Then there is a finitely presented
`𝒪_X`-module, flat over `A`, with support proper over `A`, restricting to the `Fₙ` compatibly with
the `φₙ`: the conclusion of [Stacks, Tag 0CXB]. A finitely presented `𝒪_X`-module with support
proper over `A` restricting to the `Fₙ` is flat over `A`.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `FlatSheafExistenceSituation.isFlatOver_of_hasProperSupport`: an `𝒪_X`-module of finite
  presentation with support proper over `A` restricting to the `Fₙ` is flat over `A`.
* `ModulePullbackCompatible.of_isIso_map`: compatibility with the `φₙ` is preserved by a map of
  modules invertible on the `Xₙ`.
* `FlatSheafExistenceSituation.exists_algebraization_of_isExistenceNeighbourhood`: the conclusion
  of Stacks 0CXB from an existence neighbourhood.

## References

* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
* [Stacks Project, Tag 0CXA](https://stacks.math.columbia.edu/tag/0CXA)
* [Stacks Project, Tag 0CVI](https://stacks.math.columbia.edu/tag/0CVI)
* [Stacks Project, Tag 0CX1](https://stacks.math.columbia.edu/tag/0CX1)
* [Stacks Project, Tag 0CX2](https://stacks.math.columbia.edu/tag/0CX2)
* [Stacks Project, Tag 0CTJ](https://stacks.math.columbia.edu/tag/0CTJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt baseProjection)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} in
/-- **Compatibility is preserved by changing the module along a map that is invertible on the
two subspaces.** If `b'` and `b` are compatible with `φ` and `u : H ⟶ G` becomes invertible after
restriction to `X''` and to `X'`, then `b' ∘ (i'^* u)⁻¹` and `b ∘ (i^* u)⁻¹` are compatible with
`φ`. -/
theorem ModulePullbackCompatible.of_isIso_map {X X' X'' : AlgebraicSpaces B S hS}
    {t : X' ⟶ X''} {i' : X'' ⟶ X} {i : X' ⟶ X} {h : t ≫ i' = i}
    {H G : Modules.{u, u} B S hS X.1 X.2} {F'' : Modules.{u, u} B S hS X''.1 X''.2}
    {F' : Modules.{u, u} B S hS X'.1 X'.2} {φ : (modulePullback B S hS t).obj F'' ≅ F'}
    {b' : (modulePullback B S hS i').obj H ⟶ F''} {b : (modulePullback B S hS i).obj H ⟶ F'}
    (hc : ModulePullbackCompatible t i' i h H φ b' b) (u : H ⟶ G)
    [IsIso ((modulePullback B S hS i').map u)] [IsIso ((modulePullback B S hS i).map u)] :
    ModulePullbackCompatible t i' i h G φ (inv ((modulePullback B S hS i').map u) ≫ b')
      (inv ((modulePullback B S hS i).map u) ≫ b) := by
  subst h
  refine ⟨?_⟩
  have hn := (modulePullbackCompIso B S hS t i').hom.naturality u
  rw [Functor.comp_map] at hn
  have e := hc.eq
  simp only [eqToHom_refl, Category.id_comp] at e ⊢
  rw [Functor.map_comp, Functor.map_inv, Category.assoc, e, IsIso.inv_comp_eq,
    ← Category.assoc ((modulePullback B S hS t).map ((modulePullback B S hS i').map u)), hn,
    Category.assoc, IsIso.hom_inv_id_assoc]

/-- Flatness over the base of a quasi-coherent module is detected after pullback along an
isomorphism. -/
private theorem isFlatOver_modulePullback_iff_of_iso {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y Z : AlgebraicSpaces B S hS}
    (e : X ≅ Y) (g : Y ⟶ Z) (G : Modules.{u, u} B S hS Y.1 Y.2) [G.IsQuasicoherentOnSite] :
    IsFlatOver B S hS Y.2 g.hom G ↔
      IsFlatOver B S hS X.2 (e.hom ≫ g).hom ((modulePullback B S hS e.hom).obj G) :=
  isFlatOver_modulePullback_iff_of_isSurjective_of_isFlat _ _ _ e.hom g G
    (isSurjective_of_isIso _ _ _ e.hom.hom)
    (isFlat_of_isEtale _ _ _ (isEtale_of_isIso _ _ _ e.hom.hom))

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- The algebraic space `Spec A` of the situation. -/
abbrev baseSpace : AlgebraicSpaces D.B D.S D.containsLimitBase :=
  schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)

/-- The flatness situation of Stacks 0CWX of a quasi-coherent `𝒪_X`-module over `Spec A`. -/
def moduleFlatnessSituation (G : Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2)
    (hG : G.IsQuasicoherentOnSite) : FlatnessSituation.{u} D.B D.S D.containsLimitBase where
  X := D.X.left
  Y := D.baseSpace
  f := D.X.hom
  F := G
  quasicoherent := hG

/-- The identity test scheme `Spec A` over `Spec A`. -/
abbrev baseTestScheme : SchemesOver D.baseSpace :=
  CostructuredArrow.mk (Y := limitBaseObject D.system D.B D.containsLimitBase)
    (𝟙 ((schemeSpaceFunctor D.B D.S D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase)))

/-- A module of finite presentation with support proper over `A` is pure relative to `Spec A`
(Stacks 0CVI). -/
theorem isPureAbove_of_hasProperSupport
    (G : Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2)
    (hG : G.IsFinitePresentationOnSite)
    (hprop : HasProperSupport D.B D.S D.containsLimitBase D.X.left.2 D.baseSpace.2 D.X.hom.hom
      D.isLocallyOfFiniteType_structureMorphism ((SheafOfModules.toSheaf _).obj G))
    (y : points D.B D.S D.containsLimitBase D.baseSpace.1) :
    IsPureAbove (((D.moduleFlatnessSituation G inferInstance).toFlatDimensionSituation
      D.finitePresentation hG).fpPrePureSituation D.finitePresentation y) := by
  refine IsPureAbove.of_isUniversallyPureAbove
    (isUniversallyPureAbove_of_isProper_supportSubspace _ ?_)
  let P := ((D.moduleFlatnessSituation G inferInstance).toFlatDimensionSituation
      D.finitePresentation hG).fpPrePureSituation D.finitePresentation y
  exact isProper_comp_of_hasProperSupport_of_range_subset _ _ _ D.X.left.2 D.baseSpace.2
    D.X.hom.hom D.isLocallyOfFiniteType_structureMorphism hprop P.supportSubspace.2.1 _
    P.supportSubspace.2.2
    (supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport _ _ _ D.X.left G inferInstance
      inferInstance).ge

/-- The test scheme `Spec Aₙ ⟶ Spec A` over `Spec A`, written as the point of `Spec A` over
`Spec Aₙ` that the structure morphism is. -/
abbrev stageTestScheme (n : ℕ) : SchemesOver D.baseSpace :=
  CostructuredArrow.mk (Y := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
    ((schemeSpaceFunctor D.B D.S D.containsLimitBase).map
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) ≫
      D.baseTestScheme.hom)

/-- **The base change of a module restricting to the `Fₙ` is flat over `Spec Aₙ`.** If
`G|_{Xₙ} ≅ Fₙ`, the base change of `G` to `Spec Aₙ` is flat over `Spec Aₙ`. -/
theorem isFlatAfterBaseChange_stageTestScheme (n : ℕ)
    (G : Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2)
    (hG : G.IsQuasicoherentOnSite)
    (α : (modulePullback D.B D.S D.containsLimitBase (D.closedImmersion n)).obj G ≅ D.F n) :
    (D.moduleFlatnessSituation G hG).IsFlatAfterBaseChange (D.stageTestScheme n) := by
  have hb : IsPullback (baseChangeProjection D.X.hom (D.stageTestScheme n))
      (baseChangeInclusion D.X.hom (D.stageTestScheme n)) D.X.hom (D.stageTestScheme n).hom :=
    AlgebraicSpaces.isPullback_fiberProduct _ _ _ _ _
  have hT : (D.stageTestScheme n).hom =
      baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt n :=
    Category.comp_id _
  have hs : IsPullback (D.closedImmersion n) (D.stageToBase n) D.X.hom
      (D.stageTestScheme n).hom := by
    rw [hT]
    exact (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip
  let e := IsPullback.isoIsPullback _ _ hb hs
  have he₁ : e.hom ≫ D.closedImmersion n = baseChangeProjection D.X.hom (D.stageTestScheme n) :=
    IsPullback.isoIsPullback_hom_fst _ _ hb hs
  have he₂ : e.hom ≫ D.stageToBase n = baseChangeInclusion D.X.hom (D.stageTestScheme n) :=
    IsPullback.isoIsPullback_hom_snd _ _ hb hs
  have hF : IsFlatOver D.B D.S D.containsLimitBase (D.stage n).2 (D.stageToBase n).hom
      ((modulePullback D.B D.S D.containsLimitBase (D.closedImmersion n)).obj G) :=
    IsFlatOver.of_iso _ _ _ _ α.symm (D.flat n)
  have : ((modulePullback D.B D.S D.containsLimitBase (D.closedImmersion n)).obj
      G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite _ _ _ _ G hG
  have h := (isFlatOver_modulePullback_iff_of_iso e (D.stageToBase n) _).1 hF
  rw [he₂] at h
  exact IsFlatOver.of_iso _ _ _ _
    ((modulePullbackTriangle D.B D.S D.containsLimitBase he₁).app G).symm h

/-- **A module restricting to the `Fₙ` with support proper over `A` is flat over `A`.** If `G` is
an `𝒪_X`-module of finite presentation whose support is proper over `A` and `G|_{Xₙ} ≅ Fₙ` for
every `n`, then `G` is flat over `A`. -/
theorem isFlatOver_of_hasProperSupport
    (G : Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2)
    (hG : G.IsFinitePresentationOnSite)
    (hprop : HasProperSupport D.B D.S D.containsLimitBase D.X.left.2 D.baseSpace.2 D.X.hom.hom
      D.isLocallyOfFiniteType_structureMorphism ((SheafOfModules.toSheaf _).obj G))
    (α : ∀ n : ℕ,
      (modulePullback D.B D.S D.containsLimitBase (D.closedImmersion n)).obj G ≅ D.F n) :
    IsFlatOver D.B D.S D.containsLimitBase D.X.left.2 D.X.hom.hom G := by
  have := hG
  have hqc : G.IsQuasicoherentOnSite := inferInstance
  let D₀ := D.moduleFlatnessSituation G hqc
  let D₁ := D₀.toFlatDimensionSituation D.finitePresentation hG
  have hpure := D.isPureAbove_of_hasProperSupport G hG hprop
  have hqf : IsLocallyQuasiFinite D.B D.S D.containsLimitBase D.baseTestScheme.hom.hom :=
    isLocallyQuasiFinite_of_isEtale' _ _ _
      (@isEtale_of_isIso _ _ _ _ _ _ (inferInstanceAs (IsIso (𝟙 _))))
  obtain ⟨Zs, z, jj, hzfp, hzm, hsq⟩ :=
    D₁.exists_isPullback_flatDimensionSubfunctor D.finitePresentation hG hpure 0
      D.baseTestScheme hqf
  have hfac : ∀ n : ℕ, ∃ k : baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n ⟶ Zs,
      k ≫ z = baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n := by
    intro n
    have hdim : D₁.IsFlatInDimensionsGEAfterBaseChange (D.stageTestScheme n) 0 :=
      (D₁.isFlatInDimensionsGEAfterBaseChange_zero_iff _).2
        (D.isFlatAfterBaseChange_stageTestScheme n G hqc (α n))
    let t := baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n
    have hle : Subfunctor.range (yoneda.map t ≫ D.baseTestScheme.hom.hom) ≤
        D₁.flatDimensionSubfunctor 0 := by
      rintro ⟨U⟩ _ ⟨x, rfl⟩
      have h := D₁.pointSchemeOver_app_eq D.baseTestScheme (x ≫ t)
      have h' : D₁.IsFlatInDimensionsGEAfterBaseChange
          (CostructuredArrow.mk ((schemeSpaceFunctor D.B D.S D.containsLimitBase).map (x ≫ t) ≫
            D.baseTestScheme.hom)) 0 :=
        D₁.isFlatInDimensionsGEAfterBaseChange_of_hom
          (CostructuredArrow.homMk x (by
            simp only [stageTestScheme, t, CostructuredArrow.mk_hom_eq_self, Functor.map_comp]
            exact (Category.assoc _ _ _).symm)) 0 hdim
      rwa [← h] at h'
    have ha : Subfunctor.lift _ hle ≫ (D₁.flatDimensionSubfunctor 0).ι =
        yoneda.map t ≫ D.baseTestScheme.hom.hom :=
      Subfunctor.lift_ι _ _
    refine ⟨yoneda.preimage (hsq.lift _ (yoneda.map t) ha), yoneda.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage]
    exact hsq.lift_snd _ _ ha
  have hF' : ∀ n : ℕ, Function.Surjective (D.system.map (homOfLE (Nat.le_succ n)).op).hom ∧
      RingHom.ker (D.system.map (homOfLE (Nat.le_succ n)).op).hom ≤
        nilradical (D.system.obj (op (n + 1))) := fun n ↦
    ⟨D.transition_surjective n, fun x hx ↦ mem_nilradical.2 (D.transition_locallyNilpotent n x hx)⟩
  have : Mono ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).map z) := hzm
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).map z) :=
    hzfp.1
  have hiso : IsIso ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).map z) :=
    isIso_of_forall_spec_factors_of_isLimit D.system (limit.cone D.system) (limit.isLimit _) hF'
      ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).map z) fun n ↦ by
        obtain ⟨k, hk⟩ := hfac n
        refine ⟨(BigFppfOver.toScheme D.B D.S D.containsLimitBase).map k,
          ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).map_comp k z).symm.trans ?_⟩
        rw [hk]
        rfl
  let f := (BigFppfOver.toScheme D.B D.S D.containsLimitBase).map z
  have hw : (ObjectProperty.homMk (inv f) : D.baseTestScheme.left.left ⟶ Zs.left) ≫ Zs.hom =
      D.baseTestScheme.left.hom := by
    rw [← Over.w z]
    apply ObjectProperty.hom_ext
    exact IsIso.inv_hom_id_assoc f _
  let s0 : D.baseTestScheme.left ⟶ Zs := Over.homMk (ObjectProperty.homMk (inv f)) hw
  have hs0 : s0 ≫ z = 𝟙 _ :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ (IsIso.inv_hom_id f))
  let a0 := yoneda.map s0 ≫ jj
  have ha0 : a0 ≫ (D₁.flatDimensionSubfunctor 0).ι = D.baseTestScheme.hom.hom := by
    simp only [a0, Category.assoc, hsq.w]
    refine (Functor.map_comp_assoc _ _ _ _).symm.trans ?_
    rw [hs0, CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  have hmem := (a0.app (op D.baseTestScheme.left) (𝟙 _)).2
  have hval : (a0.app (op D.baseTestScheme.left) (𝟙 _)).1 =
      D.baseTestScheme.hom.hom.app (op D.baseTestScheme.left) (𝟙 _) :=
    congrFun (congrArg (fun φ ↦ φ.app (op D.baseTestScheme.left)) ha0) (𝟙 _)
  rw [hval] at hmem
  have hpt := D₁.pointSchemeOver_app_eq D.baseTestScheme (𝟙 D.baseTestScheme.left)
  have hmem' := (congrArg (fun T ↦ D₁.IsFlatInDimensionsGEAfterBaseChange T 0) hpt).mp hmem
  have hflat1 := (D₁.isFlatInDimensionsGEAfterBaseChange_zero_iff _).1 hmem'
  let T1 : SchemesOver D.baseSpace := CostructuredArrow.mk
    ((schemeSpaceFunctor D.B D.S D.containsLimitBase).map (𝟙 D.baseTestScheme.left) ≫
      D.baseTestScheme.hom)
  have hT1 : T1.hom = 𝟙 _ := by
    simp only [T1, CostructuredArrow.mk_hom_eq_self, CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  have hb1 : IsPullback (baseChangeProjection D.X.hom T1) (baseChangeInclusion D.X.hom T1)
      D.X.hom T1.hom :=
    AlgebraicSpaces.isPullback_fiberProduct _ _ _ _ _
  have : IsIso T1.hom := by rw [hT1]; exact IsIso.id _
  have : IsIso (baseChangeProjection D.X.hom T1) := hb1.isIso_fst_of_isIso
  have hw1 : baseChangeProjection D.X.hom T1 ≫ D.X.hom = baseChangeInclusion D.X.hom T1 := by
    rw [hb1.w, hT1]
    exact Category.comp_id _
  refine (isFlatOver_modulePullback_iff_of_iso (asIso (baseChangeProjection D.X.hom T1))
    D.X.hom G).2 ?_
  change IsFlatOver D.B D.S D.containsLimitBase _
    (baseChangeProjection D.X.hom T1 ≫ D.X.hom).hom _
  rwa [hw1]

/-- **The conclusion of the proof of Stacks 0CXB, from an existence neighbourhood.** In
Situation 0CX4, let `K` be an object of `D(𝒪_X)` with maps `πₙ : K ⟶ Fₙ` compatible with the
transition maps, and let `W ⊆ X` be an open subspace with the three conclusions of Stacks 0CX9.
Then there is a finitely presented `𝒪_X`-module `G`, flat over `A`, with support proper over `A`,
with isomorphisms `G|_{Xₙ} ≅ Fₙ` compatible with the `φₙ`. -/
theorem exists_algebraization_of_isExistenceNeighbourhood
    {K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    {π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)}
    (hπ : ∀ n : ℕ, π (n + 1) ≫ D.derivedSystem.map (homOfLE (Nat.le_succ n)).op = π n)
    {W : Subfunctor D.X.left.1} {hW : IsOpenSubspace D.B D.S D.containsLimitBase W}
    (hN : D.IsExistenceNeighbourhood K π W hW) :
    ∃ (G : Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2)
      (_ : G.IsFinitePresentationOnSite),
      IsFlatOver D.B D.S D.containsLimitBase D.X.left.2 D.X.hom.hom G ∧
      HasProperSupport D.B D.S D.containsLimitBase D.X.left.2 D.baseSpace.2 D.X.hom.hom
        D.isLocallyOfFiniteType_structureMorphism ((SheafOfModules.toSheaf _).obj G) ∧
      ∃ α : ∀ n : ℕ,
          (modulePullback D.B D.S D.containsLimitBase (D.closedImmersion n)).obj G ≅ D.F n,
        ∀ n : ℕ, ModulePullbackCompatible (D.transition n) (D.closedImmersion (n + 1))
          (D.closedImmersion n) (D.transition_closedImmersion n) G (D.φ n) (α (n + 1)).hom
          (α n).hom := by
  obtain ⟨W', hW', -, hN', hlft, hprop⟩ := D.exists_isExistenceNeighbourhood_hasProperSupport hN
  let j := openSubspaceHom D.B D.S D.containsLimitBase W' hW'
  have hj : IsOpenImmersion D.B D.S D.containsLimitBase j.hom := hW'.2
  let H₀ := (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj K
  let Q := (modulePullback D.B D.S D.containsLimitBase j).obj H₀
  have hQfp : Q.IsFinitePresentationOnSite := hN'.isFinitePresentation
  have hjg : IsLocallyOfFiniteType D.B D.S D.containsLimitBase (j ≫ D.X.hom).hom := hlft
  have hQprop : HasProperSupport D.B D.S D.containsLimitBase
      (openSubspaceSpace D.B D.S D.containsLimitBase W' hW').2 D.baseSpace.2 (j ≫ D.X.hom).hom hjg
      ((SheafOfModules.toSheaf _).obj Q) := hprop
  have hcl : IsClosed (pointsMap D.B D.S D.containsLimitBase
      (openSubspaceSpace D.B D.S D.containsLimitBase W' hW').1 j.hom ''
        supportOfSheaf D.B D.S D.containsLimitBase
          (openSubspaceSpace D.B D.S D.containsLimitBase W' hW').1
          ((SheafOfModules.toSheaf _).obj Q)) :=
    isClosed_image_of_isProperOver _ _ _ (openSubspaceSpace D.B D.S D.containsLimitBase W' hW').2
      D.X.left.2 D.baseSpace.2 j.hom (j ≫ D.X.hom).hom D.X.hom.hom rfl hjg
      D.isLocallyOfFiniteType_structureMorphism D.separated _ hQprop.1 hQprop.2
  let G := (modulePushforward D.B D.S D.containsLimitBase j).obj Q
  have hGfp : G.IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_modulePushforward_of_isOpenImmersion _ _ _ j hj Q hQfp hcl
  have hGprop := hasProperSupport_modulePushforward_of_isOpenImmersion _ _ _ j hj D.X.hom
    D.isLocallyOfFiniteType_structureMorphism hjg D.separated Q hQprop
  let η := (modulePullbackAdjunction D.B D.S D.containsLimitBase j).unit.app H₀
  have hjη : IsIso ((modulePullback D.B D.S D.containsLimitBase j).map η) := by
    have := isIso_modulePullbackAdjunction_counit_of_isOpenImmersion _ _ _ j hj Q
    have h := (modulePullbackAdjunction D.B D.S D.containsLimitBase j).left_triangle_components H₀
    have h' : IsIso ((modulePullback D.B D.S D.containsLimitBase j).map η ≫
        (modulePullbackAdjunction D.B D.S D.containsLimitBase j).counit.app Q) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((modulePullbackAdjunction D.B D.S D.containsLimitBase j).counit.app Q)
  have hstage : ∀ n : ℕ,
      IsIso ((modulePullback D.B D.S D.containsLimitBase (D.closedImmersion n)).map η) := by
    intro n
    obtain ⟨g₀, hg₀⟩ := (factorsThrough_openSubspace_iff_points D.B D.S D.containsLimitBase
      D.X.left.2 (D.stage n).2 W' hW' (D.closedImmersion n).hom).2
        ((D.range_closedImmersion_subset_pointsOverFirstStage n).trans hN'.subset_range)
    let k : D.stage n ⟶ openSubspaceSpace D.B D.S D.containsLimitBase W' hW' :=
      ObjectProperty.homMk g₀
    have hk : k ≫ j = D.closedImmersion n := ObjectProperty.hom_ext _ hg₀
    refine (NatIso.isIso_map_iff (modulePullbackTriangle D.B D.S D.containsLimitBase hk) η).2 ?_
    rw [Functor.comp_map]
    infer_instance
  let α : ∀ n : ℕ,
      (modulePullback D.B D.S D.containsLimitBase (D.closedImmersion n)).obj G ≅ D.F n :=
    fun n ↦ (@asIso _ _ _ _ _ (hstage n)).symm ≪≫
      @asIso _ _ _ _ (D.stageComparison K π n) (hN.isIso_stageComparison_stage D n)
  refine ⟨G, hGfp, D.isFlatOver_of_hasProperSupport G hGfp hGprop α, hGprop, α, fun n ↦ ?_⟩
  have := hstage n
  have := hstage (n + 1)
  exact (D.stageComparison_compatible K π hπ n).of_isIso_map η

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
