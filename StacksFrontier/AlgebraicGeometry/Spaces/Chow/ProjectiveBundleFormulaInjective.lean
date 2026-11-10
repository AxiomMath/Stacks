module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineBundleSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatProperTopPowerOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOfRankModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem

/-!
# The injectivity half of the projective bundle formula

Let `X` be a good algebraic space over the base, `ℰ` a finite locally free `𝒪_X`-module of rank
`n + 1` and `π : P = 𝐏(ℰ) → X` its projective bundle; all names below are in the namespace
`AlgebraicGeometry.Space`. The injectivity half of Stacks 0ERV follows from the top power
`π_*(c₁(𝒪_P(1))^n ∩ π^*α) = α` of Stacks 0ERU on cycles (`injective_bundleFormulaMap_of_top`). By
`properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_self_of_forall` that identity
reduces to the class of `π_{T,*}(c₁(ℒ_T)^n ∩ π_T^*[T])` over each integral closed subspace
`T ⊆ X`, and by
`properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_top_of_isOpenImmersion` that
class is `[T]` as soon as the top power holds in the Chow group on a nonempty open `U ⊆ T`. Over
`U` the bundle `π^{-1}(T) ×_T U` is `𝐏(g^*ℰ)` for `g : U → T → X`
(`projectiveBundlePullbackIso`), with the twist (`projectiveBundleTwistFiberProductIso`); when
`g^*ℰ` is free the top power for `𝐏(g^*ℰ)` is the free case (`projectiveBundleFormula_freeTower`).

## Main results

* `AlgebraicGeometry.Space.chowClassCanonical_closedBaseChangeTopPowerCycle_of_isPullback`: for a
  proper flat datum `(π, ℒ)`, the class over an integral closed subspace `T` from the top power in
  the Chow group of a nonempty open `U ⊆ T` and a cartesian square over `U → T → X`.
* `AlgebraicGeometry.Space.chowClassCanonical_closedBaseChangeTopPowerCycle_projectiveBundle`: the
  same for a projective bundle, from the projective bundle formula for `𝐏(g^*ℰ)`.
* `AlgebraicGeometry.Space.injective_bundleFormulaMap_projectiveBundle_of_forall`: the injectivity
  half of Stacks 0ERV, from the projective bundle formula for the free modules, its invariance
  under isomorphisms of modules, and the freeness of a finite locally free module on a nonempty
  open.

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The class over an integral closed subspace, from a nonempty open -/

section Datum

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The top power only depends on the isomorphism class of the invertible module.** -/
theorem BundleTopPowerIdentity.of_moduleIso
    (L' : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL' : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L')
    (e : L ≅ L') (h : BundleTopPowerIdentity D sX hX sP hP π hπB n hflat hrel hp L hL) :
    BundleTopPowerIdentity D sX hX sP hP π hπB n hflat hrel hp L' hL' := by
  intro k α
  rw [← chowGroupCanonicalProperPushforward_chowClassCanonical.{u + 1} D sP hP sX hX hπB hp,
    ← chowClassCanonical_firstChernCapPowCycleMap_congr_iso D sP hP L L' hL hL' e,
    chowGroupCanonicalProperPushforward_chowClassCanonical]
  exact h k α

/-- **The class of the top power over an integral closed subspace `T ⊆ X`, from a nonempty
open.** Let `j : U → T` be an open immersion with `U` nonempty and `θ : P_U → P`, `π_U : P_U → U`
a cartesian square over `U → T → X`. If the top power of Stacks 0ERU holds in the Chow groups for
`(π_U, ℒ')` with `θ^*ℒ ≅ ℒ'`, then `π_{T,*}(c₁(ℒ_T)^n ∩ π_T^*[T]) = [T]` in `CH_k(T)`. -/
theorem chowClassCanonical_closedBaseChangeTopPowerCycle_of_isPullback
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)
    (hT : deltaDimension D sX T = k)
    {U PU : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sU : U ⟶ D.space) (hU : D.IsGood sU) (sPU : PU ⟶ D.space) (hPU : D.IsGood sPU)
    (j : U ⟶ T.subspace.toFunctor) (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (hjB : j ≫ T.subspace.ι ≫ sX = sU) (u₀ : points D.site D.base D.base_mem U)
    (πU : PU ⟶ U) (hπUB : πU ≫ sU = sPU) (θ : PU ⟶ P)
    (hθ : IsPullback θ πU π (j ≫ T.subspace.ι))
    (hflatU : IsFlat D.site D.base D.base_mem πU)
    (hrelU : HasRelativeDimension n D.site D.base D.base_mem πU)
    (hpU : IsProper D.site D.base D.base_mem πU)
    (L' : Modules.{u, u} D.site D.base D.base_mem PU hPU.1)
    (hL' : IsInvertibleModule (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L')
    (e : (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk θ : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P, hP.1⟩)).obj L ≅ L')
    (htop : BundleTopPowerIdentity D sU hU sPU hPU πU hπUB n hflatU hrelU hpU L' hL') :
    chowClassCanonical.{u + 1} D (T.subspace.ι ≫ sX)
        (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace) k
        (closedBaseChangeTopPowerCycle D sX hX sP hP π hπB n hflat hrel hp L hL T.subspace
          T.isClosedSubspace k
          (integralCycle D (T.subspace.ι ≫ sX) k
            (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
              T.isIntegralSpace)
            ((IntegralClosedSubspace.deltaDimension_top_eq D sX hX T).trans hT))) =
      chowClassCanonical.{u + 1} D (T.subspace.ι ≫ sX)
        (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace) k
        (integralCycle D (T.subspace.ι ≫ sX) k
          (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
            T.isIntegralSpace)
          ((IntegralClosedSubspace.deltaDimension_top_eq D sX hX T).trans hT)) := by
  have hc := isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π T.subspace
    T.isClosedSubspace
  have w : (πU ≫ j) ≫ T.subspace.ι = θ ≫ π := (Category.assoc _ _ _).trans hθ.w.symm
  let j' : PU ⟶ (T.subspace.preimage π).toFunctor :=
    (Subfunctor.isPullback_preimage π T.subspace).lift (πU ≫ j) θ w
  have hj'ι : j' ≫ (T.subspace.preimage π).ι = θ :=
    (Subfunctor.isPullback_preimage π T.subspace).lift_snd _ _ w
  have hj'π : j' ≫ T.subspace.fromPreimage π = πU ≫ j :=
    (Subfunctor.isPullback_preimage π T.subspace).lift_fst _ _ w
  have sq : IsPullback j' πU (T.subspace.fromPreimage π) j :=
    IsPullback.of_right (by rw [hj'ι]; exact hθ) hj'π
      (Subfunctor.isPullback_preimage π T.subspace).flip
  have hj'B : j' ≫ (T.subspace.preimage π).ι ≫ sP = sPU := by
    calc j' ≫ (T.subspace.preimage π).ι ≫ sP = (θ ≫ π) ≫ sX := by
          rw [← Category.assoc, hj'ι, Category.assoc, hπB]
      _ = sPU := by rw [hθ.w, Category.assoc, Category.assoc, hjB, hπUB]
  have hLT := modulePullbackInvertible
    (closedSubspaceHom D.site D.base D.base_mem hP.1 (T.subspace.preimage π) hc) L hL
  have hw : (ObjectProperty.homMk j' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨(T.subspace.preimage π).toFunctor, hc.1⟩) ≫
        closedSubspaceHom D.site D.base D.base_mem hP.1 (T.subspace.preimage π) hc =
      ObjectProperty.homMk θ := ObjectProperty.hom_ext _ hj'ι
  have e₁ := (modulePullbackCompIsoOfEq D.site D.base D.base_mem
        (ObjectProperty.homMk j' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨(T.subspace.preimage π).toFunctor, hc.1⟩)
        (closedSubspaceHom D.site D.base D.base_mem hP.1 (T.subspace.preimage π) hc) hw).app L
  have htop' := BundleTopPowerIdentity.of_moduleIso D sU hU sPU hPU πU hπUB n hflatU hrelU hpU L'
    hL' _ (modulePullbackInvertible _ _ hLT) (e.symm ≪≫ e₁.symm) htop
  have key := properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_top_of_isOpenImmersion
    D (T.subspace.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace)
    ((T.subspace.preimage π).ι ≫ sP) (isGood_ι_of_isClosedSubspace D sP hP _ hc) sU hU sPU hPU
    (T.subspace.fromPreimage π) (fromPreimage_comp_structureMorphism D sP sX π hπB T.subspace) n
    (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB T.subspace
      T.isClosedSubspace n hflat hrel).1
    (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB T.subspace
      T.isClosedSubspace n hflat hrel).2
    (isProper_fromPreimage_of_isClosedSubspace D sX hX sP hP π hp T.subspace T.isClosedSubspace)
    (closedSubspaceModuleRestrict D sP hP L ⟨T.subspace.preimage π, hc⟩) hLT hj hjB hj'B hπUB sq
    T.isIntegralSpace u₀ k ((IntegralClosedSubspace.deltaDimension_top_eq D sX hX T).trans hT)
    (fun γ => htop' k γ)
  exact congrArg _ key

end Datum

/-! ### The class over an integral closed subspace, for a projective bundle -/

section ProjectiveBundle

variable (D : BaseSpaceDimensionSituation.{u})
    {X : AlgebraicSpaces D.site D.base D.base_mem} (sX : X.1 ⟶ D.space) (hX : D.IsGood sX)
    (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (n + 1))

/-- **The base change of a projective bundle along `g : U → X` is cartesian over `𝐏(g^*ℰ)`**:
the square formed by `θ = Θ ≫ g' : 𝐏(g^*ℰ) → P`, the projections and `g`, for the
identification `Θ : 𝐏(g^*ℰ) ≅ P ×_X U`. -/
theorem isPullback_projectiveBundlePullbackIso_hom_comp_fst {U : AlgebraicSpaces D.site D.base
    D.base_mem}
    (g : U ⟶ X) :
    IsPullback ((projectiveBundlePullbackIso (hE :=
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
        hr.isFiniteLocallyFreeOnSite).hom ≫
        projectiveBundleFiberProductFst (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
            X.2 hr)) g E hr.isFiniteLocallyFreeOnSite).hom
      (@projectiveBundleProj D.site D.base D.base_mem U ((modulePullback D.site D.base D.base_mem
          g).obj E)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2
          (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem g E (n + 1) hr))
        (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem g E (n + 1)
          hr).isFiniteLocallyFreeOnSite).hom
      (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom
      g.hom := by
  have h1 := IsPullback.of_horiz_isIso
    (fst := (projectiveBundlePullbackIso (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
        X.2 hr)) g E hr.isFiniteLocallyFreeOnSite).hom)
    (g := 𝟙 U)
    ⟨(projectiveBundlePullbackIso_hom_comp_proj (hE :=
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
        hr.isFiniteLocallyFreeOnSite).trans
      (Category.comp_id _).symm⟩
  have h2 := AlgebraicSpaces.isPullback_fiberProduct D.site D.base D.base_mem
    (@projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite) g
  have h3 := AlgebraicSpaces.isPullback_hom D.site D.base D.base_mem (h1.paste_horiz h2)
  rw [Category.id_comp] at h3
  exact h3

/-- **The class of the top power over an integral closed subspace `T ⊆ X` for a projective
bundle**, from the projective bundle formula for `𝐏(g^*ℰ)`, `g : U → T → X` a nonempty open of
`T`. -/
theorem chowClassCanonical_closedBaseChangeTopPowerCycle_projectiveBundle
    (T : IntegralClosedSubspace D.site D.base D.base_mem X.1) (k : ℤ)
    (hT : deltaDimension D sX T = k) {U : AlgebraicSpaces D.site D.base D.base_mem}
    (j : U ⟶ ⟨T.subspace.toFunctor, T.isClosedSubspace.1⟩)
    (hj : IsOpenImmersion D.site D.base D.base_mem j.hom) (u₀ : points D.site D.base D.base_mem U.1)
    (hU : D.IsGood ((j ≫ closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace
        T.isClosedSubspace : U ⟶ X).hom ≫ sX))
    (hQ : ProjectiveBundleFormulaHolds D ((j ≫ closedSubspaceHom D.site D.base D.base_mem X.2
        T.subspace T.isClosedSubspace : U ⟶ X).hom ≫ sX) hU ((modulePullback D.site D.base
        D.base_mem
        (j ≫ closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace T.isClosedSubspace : U ⟶
            X)).obj E) n (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
        (j ≫ closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace T.isClosedSubspace : U ⟶ X)
        E (n + 1) hr)) :
    chowClassCanonical.{u + 1} D (T.subspace.ι ≫ sX)
        (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace) k
        (closedBaseChangeTopPowerCycle D sX hX _ (isGood_projectiveBundleProj_comp_of_rank D sX hX
            E n hr)
          (@projectiveBundleProj D.site D.base D.base_mem X E
              (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
              hr.isFiniteLocallyFreeOnSite).hom rfl n
          (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
              (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
            hr.isFiniteLocallyFreeOnSite)
          (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
              (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
            hr.isFiniteLocallyFreeOnSite)
          (@isProper_projectiveBundleProj D.site D.base D.base_mem X E
              (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
              hr.isFiniteLocallyFreeOnSite)
          (@projectiveBundleTwist D.site D.base D.base_mem X E
              (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
              hr.isFiniteLocallyFreeOnSite).obj
          (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
              (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
            hr.isFiniteLocallyFreeOnSite)
          T.subspace T.isClosedSubspace k
          (integralCycle D (T.subspace.ι ≫ sX) k
            (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
              T.isIntegralSpace)
            ((IntegralClosedSubspace.deltaDimension_top_eq D sX hX T).trans hT))) =
      chowClassCanonical.{u + 1} D (T.subspace.ι ≫ sX)
        (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace) k
        (integralCycle D (T.subspace.ι ≫ sX) k
          (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
            T.isIntegralSpace)
          ((IntegralClosedSubspace.deltaDimension_top_eq D sX hX T).trans hT)) := by
  have hθ := isPullback_projectiveBundlePullbackIso_hom_comp_fst D E n hr (j ≫ closedSubspaceHom
      D.site D.base D.base_mem X.2 T.subspace T.isClosedSubspace : U ⟶ X)
  have e := ((modulePullbackCompIsoOfEq D.site D.base D.base_mem
      (projectiveBundlePullbackIso (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2
          hr)) (j ≫ closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace T.isClosedSubspace :
          U ⟶ X) E hr.isFiniteLocallyFreeOnSite).hom
      (projectiveBundleFiberProductFst (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
          X.2 hr)) (j ≫ closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace
          T.isClosedSubspace : U ⟶ X) E hr.isFiniteLocallyFreeOnSite)
      rfl).app _).symm ≪≫
    projectiveBundleTwistFiberProductIso (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
        X.2 hr)) (j ≫ closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace T.isClosedSubspace
        : U ⟶ X) E hr.isFiniteLocallyFreeOnSite
  exact chowClassCanonical_closedBaseChangeTopPowerCycle_of_isPullback D sX hX _
    (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr) _ rfl n _ _ _ _ _ T k hT _ hU _
    (isGood_projectiveBundleProj_comp_of_rank D _ hU ((modulePullback D.site D.base D.base_mem
        (j ≫ closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace T.isClosedSubspace : U ⟶
            X)).obj E) n (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
        (j ≫ closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace T.isClosedSubspace : U ⟶ X)
        E (n + 1) hr)) j.hom hj
    (Category.assoc _ _ _).symm u₀ _ rfl _ hθ _ _ _ _ _ e hQ.1

/-- **The injectivity half of Stacks 0ERV**, from three inputs on good algebraic spaces over the
base: a finite locally free module of rank `n + 1` is isomorphic to the free module `F_n` on a
nonempty open subspace of any good space with a point; the projective bundle formula is invariant
under isomorphisms of modules; and it holds for `F_n`. -/
theorem injective_bundleFormulaMap_projectiveBundle_of_forall
    (hfreeOpen : ∀ (Y : AlgebraicSpaces D.site D.base D.base_mem) (sY : Y.1 ⟶ D.space),
      D.IsGood sY → points D.site D.base D.base_mem Y.1 →
      ∀ F : Modules.{u, u} D.site D.base D.base_mem Y.1 Y.2,
        RingedSite.IsFiniteLocallyFreeOfRank
          (smallEtaleRingedSite D.site D.base D.base_mem Y.1 Y.2) F (n + 1) →
        ∃ (U : AlgebraicSpaces D.site D.base D.base_mem) (j : U ⟶ Y),
          IsOpenImmersion D.site D.base D.base_mem j.hom ∧
            Nonempty (points D.site D.base D.base_mem U.1) ∧
            Nonempty ((modulePullback D.site D.base D.base_mem j).obj F ≅ freeTower U n))
    (hmod : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU) (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2)
      (hF : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F (n + 1))
      (hF' : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F' (n + 1)),
      (F ≅ F') → ProjectiveBundleFormulaHolds D sU hU F n hF →
        ProjectiveBundleFormulaHolds D sU hU F' n hF')
    (hfreeHolds : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU),
      ProjectiveBundleFormulaHolds D sU hU (freeTower U n) n (isFiniteLocallyFreeOfRank_freeTower U
          n))
    (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) :
    Function.Injective (bundleFormulaMap D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom rfl n
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite) N d hd) := by
  refine injective_bundleFormulaMap_of_top D sX hX _ _ _ rfl n _ _ _ _
    (@isProper_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite)
    (fun k α => ?_) N d hd
  refine properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_self_of_forall D sX hX
    _ _ _ rfl n _ _
    (@isProper_projectiveBundleProj D.site D.base D.base_mem X E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite)
    _ _ k (fun T hT => ?_) α
  obtain ⟨U, j, hj, ⟨u₀⟩, ⟨eU⟩⟩ := hfreeOpen ⟨T.subspace.toFunctor, T.isClosedSubspace.1⟩
    (T.subspace.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace)
    T.isIntegralSpace.2.2.toNonempty.some
    ((modulePullback D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace T.isClosedSubspace)).obj E)
    (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem _ E (n + 1) hr)
  have hU : D.IsGood ((j ≫ closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace
      T.isClosedSubspace : U ⟶ X).hom ≫ sX) :=
    (Category.assoc j.hom T.subspace.ι sX).symm ▸ isGood_comp_of_isOpenImmersion D
      (T.subspace.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace)
      U.2 hj
  exact chowClassCanonical_closedBaseChangeTopPowerCycle_projectiveBundle D sX hX E n hr T k hT j
    hj u₀ hU (hmod U _ hU (freeTower U n) _ (isFiniteLocallyFreeOfRank_freeTower U n) _
      (eU.symm ≪≫ (modulePullbackCompIsoOfEq D.site D.base D.base_mem j
        (closedSubspaceHom D.site D.base D.base_mem X.2 T.subspace T.isClosedSubspace)
        rfl).app E)
      (hfreeHolds U _ hU))

/-- **The injectivity half of Stacks 0ERV**, from the freeness of a finite locally free module
on a nonempty open subspace, the invariance of the projective bundle formula under isomorphisms of
modules, and the two geometric inputs of the free case: `𝐏(𝒪_U) → U` is an isomorphism and
`i^*𝒪_{𝐏(F_m ⊕ 𝒪)}(1) ≅ 𝒪_{𝐏(F_m)}(1)` along the hyperplane at infinity. -/
theorem injective_bundleFormulaMap_projectiveBundle_of_freeTower
    (hfreeOpen : ∀ (Y : AlgebraicSpaces D.site D.base D.base_mem) (sY : Y.1 ⟶ D.space),
      D.IsGood sY → points D.site D.base D.base_mem Y.1 →
      ∀ F : Modules.{u, u} D.site D.base D.base_mem Y.1 Y.2,
        RingedSite.IsFiniteLocallyFreeOfRank
          (smallEtaleRingedSite D.site D.base D.base_mem Y.1 Y.2) F (n + 1) →
        ∃ (U : AlgebraicSpaces D.site D.base D.base_mem) (j : U ⟶ Y),
          IsOpenImmersion D.site D.base D.base_mem j.hom ∧
            Nonempty (points D.site D.base D.base_mem U.1) ∧
            Nonempty ((modulePullback D.site D.base D.base_mem j).obj F ≅ freeTower U n))
    (hmod : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU) (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2)
      (hF : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F (n + 1))
      (hF' : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F' (n + 1)),
      (F ≅ F') → ProjectiveBundleFormulaHolds D sU hU F n hF →
        ProjectiveBundleFormulaHolds D sU hU F' n hF')
    (hbase : ∀ U : AlgebraicSpaces D.site D.base D.base_mem,
      IsIso (@projectiveBundleProj D.site D.base D.base_mem U (freeTower U 0)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2
            (isFiniteLocallyFreeOfRank_freeTower U 0))
        (isFiniteLocallyFreeOfRank_freeTower U 0).isFiniteLocallyFreeOnSite).hom)
    (htw : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (m : ℕ),
      Nonempty ((modulePullback D.site D.base D.base_mem
        (projectiveCompletionInfinityImmersion (freeTower U m)
          (isFiniteLocallyFreeOfRank_freeTower U m))).obj
        (projectiveCompletionTwist (freeTower U m) (isFiniteLocallyFreeOfRank_freeTower U m)).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem U (freeTower U m)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2
            (isFiniteLocallyFreeOfRank_freeTower U m))
        (isFiniteLocallyFreeOfRank_freeTower U m).isFiniteLocallyFreeOnSite).obj))
    (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) :
    Function.Injective (bundleFormulaMap D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom rfl n
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite) N d hd) :=
  injective_bundleFormulaMap_projectiveBundle_of_forall D sX hX E n hr hfreeOpen hmod
    (fun U sU hU => projectiveBundleFormula_freeTower D sU hU (hbase U) (htw U) n) N d hd

end ProjectiveBundle

/-! ### The base change of a projective bundle -/

section FiberProduct

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : AlgebraicSpaces D.site D.base D.base_mem} (sX : X.1 ⟶ D.space) (hX : D.IsGood sX)
    (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (n + 1))
    (g : X' ⟶ X) (hX' : D.IsGood (g.hom ≫ sX))

include hX hX' in
/-- The base change `P ×_X X'` of a projective bundle is good over the base. -/
theorem isGood_projectiveBundleFiberProductProj_comp :
    D.IsGood ((projectiveBundleFiberProductProj (hE :=
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
        hr.isFiniteLocallyFreeOnSite).hom ≫ g.hom ≫ sX) :=
  @isGood_projectiveBundleBaseChangeProj_comp D X.1 X'.1 sX hX E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite
      g.hom hX'

include hX hX' in
/-- The projection `P ×_X X' → X'` is flat. -/
theorem isFlat_projectiveBundleFiberProductProj :
    IsFlat D.site D.base D.base_mem (projectiveBundleFiberProductProj (hE :=
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
        hr.isFiniteLocallyFreeOnSite).hom :=
  @isFlat_projectiveBundleBaseChangeProj D X.1 X'.1 sX hX E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite
      g.hom hX' n hr

include hX hX' in
/-- The projection `P ×_X X' → X'` has relative dimension `n`. -/
theorem hasRelativeDimension_projectiveBundleFiberProductProj :
    HasRelativeDimension n D.site D.base D.base_mem
      (projectiveBundleFiberProductProj (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
          X.2 hr)) g E hr.isFiniteLocallyFreeOnSite).hom :=
  @hasRelativeDimension_projectiveBundleBaseChangeProj D X.1 X'.1 sX hX E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite
      g.hom hX' n hr

include hX hX' in
/-- The projection `P ×_X X' → X'` is proper. -/
theorem isProper_projectiveBundleFiberProductProj :
    IsProper D.site D.base D.base_mem (projectiveBundleFiberProductProj (hE :=
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
        hr.isFiniteLocallyFreeOnSite).hom :=
  @isProper_projectiveBundleBaseChangeProj D X.1 X'.1 sX hX E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite
      g.hom hX'

/-- The identification `Θ⁻¹ : P ×_X X' ≅ 𝐏(g^*ℰ)` lies over `X'`. -/
theorem projectiveBundlePullbackIso_inv_comp_proj :
    (projectiveBundlePullbackIso (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2
        hr)) g E hr.isFiniteLocallyFreeOnSite).inv.hom ≫
        (@projectiveBundleProj D.site D.base D.base_mem X' ((modulePullback D.site D.base
            D.base_mem g).obj E)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X'.2
              (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem g E (n + 1) hr))
              (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem g E (n + 1)
              hr).isFiniteLocallyFreeOnSite).hom =
      (projectiveBundleFiberProductProj (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
          X.2 hr)) g E hr.isFiniteLocallyFreeOnSite).hom :=
  congrArg (fun f => f.hom) ((Iso.inv_comp_eq _).2
    (projectiveBundlePullbackIso_hom_comp_proj (hE :=
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
        hr.isFiniteLocallyFreeOnSite).symm)

/-- `(Θ⁻¹)^*𝒪_{𝐏(g^*ℰ)}(1) ≅ g'^*𝒪_P(1)` on `P ×_X X'`. -/
def projectiveBundleFiberProductTwistIso :
    (modulePullback D.site D.base D.base_mem (projectiveBundlePullbackIso (hE :=
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
        hr.isFiniteLocallyFreeOnSite).inv).obj
        (@projectiveBundleTwist D.site D.base D.base_mem X' ((modulePullback D.site D.base
            D.base_mem g).obj E)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X'.2
              (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem g E (n + 1) hr))
              (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem g E (n + 1)
              hr).isFiniteLocallyFreeOnSite).obj ≅
      (modulePullback D.site D.base D.base_mem
        (projectiveBundleFiberProductFst (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
            X.2 hr)) g E hr.isFiniteLocallyFreeOnSite)).obj
        (@projectiveBundleTwist D.site D.base D.base_mem X E
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
            hr.isFiniteLocallyFreeOnSite).obj :=
  (modulePullback D.site D.base D.base_mem (projectiveBundlePullbackIso (hE :=
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
      hr.isFiniteLocallyFreeOnSite).inv).mapIso
      (projectiveBundleTwistFiberProductIso (hE :=
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
          hr.isFiniteLocallyFreeOnSite).symm ≪≫
    (modulePullbackCompIsoOfEq D.site D.base D.base_mem
      (projectiveBundlePullbackIso (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2
          hr)) g E hr.isFiniteLocallyFreeOnSite).inv
      (projectiveBundlePullbackIso (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2
          hr)) g E hr.isFiniteLocallyFreeOnSite).hom
      (projectiveBundlePullbackIso (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2
          hr)) g E hr.isFiniteLocallyFreeOnSite).inv_hom_id).app _ ≪≫
    (modulePullbackIdIso D.site D.base D.base_mem _).app _

/-- The underlying morphism of `Θ⁻¹ : P ×_X X' ≅ 𝐏(g^*ℰ)` is an isomorphism. -/
private theorem isIso_projectiveBundlePullbackIso_inv_hom :
    IsIso (projectiveBundlePullbackIso (hE :=
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) g E
      hr.isFiniteLocallyFreeOnSite).inv.hom :=
  inferInstance

include hX' in
/-- **The top power of Stacks 0ERU for the base change `P ×_X X' → X'` of a projective bundle**,
with `g'^*𝒪_P(1)`, from the one for `𝐏(g^*ℰ)`. -/
theorem bundleTopPowerIdentity_projectiveBundleFiberProduct
    (hQ : ProjectiveBundleFormulaHolds D (g.hom ≫ sX) hX'
      ((modulePullback D.site D.base D.base_mem g).obj E) n
          (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem g E (n + 1) hr)) :
    BundleTopPowerIdentity D (g.hom ≫ sX) hX' _
      (isGood_projectiveBundleFiberProductProj_comp D sX hX E n hr g hX')
      (projectiveBundleFiberProductProj (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
          X.2 hr)) g E hr.isFiniteLocallyFreeOnSite).hom rfl n
      (isFlat_projectiveBundleFiberProductProj D sX hX E n hr g hX')
      (hasRelativeDimension_projectiveBundleFiberProductProj D sX hX E n hr g hX')
      (isProper_projectiveBundleFiberProductProj D sX hX E n hr g hX')
      ((modulePullback D.site D.base D.base_mem
        (projectiveBundleFiberProductFst (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
            X.2 hr)) g E hr.isFiniteLocallyFreeOnSite)).obj
        (@projectiveBundleTwist D.site D.base D.base_mem X E
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
            hr.isFiniteLocallyFreeOnSite).obj)
      (modulePullbackInvertible _ _
        (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
            hr.isFiniteLocallyFreeOnSite)) := by
  have := isIso_projectiveBundlePullbackIso_inv_hom D E n hr g
  exact BundleTopPowerIdentity.of_iso D (g.hom ≫ sX) hX' _ _ _ _ _ rfl _ rfl n _ _ _ _ _ _ _ _ _ _
    (projectiveBundlePullbackIso (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2
        hr)) g E hr.isFiniteLocallyFreeOnSite).inv.hom
    (by rw [← Category.assoc, projectiveBundlePullbackIso_inv_comp_proj D E n hr g])
    (projectiveBundlePullbackIso_inv_comp_proj D E n hr g)
    (projectiveBundleFiberProductTwistIso D E n hr g) hQ.1

include hX' in
/-- **The surjectivity half of Stacks 0ERV for the base change `P ×_X X' → X'` of a projective
bundle**, with `g'^*𝒪_P(1)`, from the one for `𝐏(g^*ℰ)`. -/
theorem bundleFormulaSurjective_projectiveBundleFiberProduct
    (hQ : ProjectiveBundleFormulaHolds D (g.hom ≫ sX) hX'
      ((modulePullback D.site D.base D.base_mem g).obj E) n
          (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem g E (n + 1) hr)) :
    BundleFormulaSurjective D (g.hom ≫ sX) hX' _
      (isGood_projectiveBundleFiberProductProj_comp D sX hX E n hr g hX')
      (projectiveBundleFiberProductProj (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
          X.2 hr)) g E hr.isFiniteLocallyFreeOnSite).hom rfl n
      (isFlat_projectiveBundleFiberProductProj D sX hX E n hr g hX')
      (hasRelativeDimension_projectiveBundleFiberProductProj D sX hX E n hr g hX')
      ((modulePullback D.site D.base D.base_mem
        (projectiveBundleFiberProductFst (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank
            X.2 hr)) g E hr.isFiniteLocallyFreeOnSite)).obj
        (@projectiveBundleTwist D.site D.base D.base_mem X E
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
            hr.isFiniteLocallyFreeOnSite).obj)
      (modulePullbackInvertible _ _
        (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
            hr.isFiniteLocallyFreeOnSite)) := by
  have := isIso_projectiveBundlePullbackIso_inv_hom D E n hr g
  exact BundleFormulaSurjective.of_iso D (g.hom ≫ sX) hX' _ _ _ _ _ rfl _ rfl n _ _ _ _ _ _ _ _
    (projectiveBundlePullbackIso (hE := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2
        hr)) g E hr.isFiniteLocallyFreeOnSite).inv.hom
    (by rw [← Category.assoc, projectiveBundlePullbackIso_inv_comp_proj D E n hr g])
    (projectiveBundlePullbackIso_inv_comp_proj D E n hr g)
    (projectiveBundleFiberProductTwistIso D E n hr g) hQ.2

end FiberProduct

end AlgebraicGeometry.Space

end
