module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageRings
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageWitness
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# Functions on the stages of a descended witness

In the proof of Stacks 0GI5 ("algebra, more rings") a witness `V' ⟶ V` over the limit
`V = lim V_k` is descended to a proper `q : Y ⟶ V_j` with `V' = V ×_{V_j} Y`, and its base
changes `Y_k = V_k ×_{V_j} Y` form a system with limit `V'`, so that `Γ(V', 𝒪) = colim Γ(Y_k, 𝒪)`
(Limits, Lemma 01Z0). This file proves the half of this used in the proof: **a function on `Y`
vanishing on `V'` vanishes on some `Y_k`**. An affine étale atlas `N ⟶ Y` base changes to atlases
`N_k = V_k ×_{V_j} N` of the `Y_k` and `V ×_{V_j} N` of `V'`, and the affine schemes `N_k` have
limit `V ×_{V_j} N`, so the vanishing happens on some `N_k`, hence on `Y_k`.

It also records the torsion statement of
`AlgebraicGeometry.Artin.StageRings.exists_pow_smul_ker_coker` for a stage witness.

## Main results

* `AlgebraicGeometry.Artin.StageRings.eq_zero_of_evalAt_eq_zero`: a global function vanishing
  along a surjective étale chart vanishes.
* `AlgebraicGeometry.Artin.ContractionSituation.StageModel.exists_restrict_eq_zero`: the vanishing
  at a later stage.
* `AlgebraicGeometry.Artin.ContractionSituation.StageWitness.exists_pow_smul_ker_coker`: the
  kernel and the cokernel of `Γ(V_j) ⟶ Γ(Y)` are killed by a power of an ideal cutting out `Z_j`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.StageRings

open Space Stacks.Cohomology.SiteModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `evalAt` along a composite: pull back first. -/
theorem evalAt_comp_globalSectionsRingHomSite {T : BigFppfOver B S hS}
    {X X' : AlgebraicSpaces B S hS} (h : schemeSpace T ⟶ X') (k : X' ⟶ X)
    (e : ↥(GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O))) :
    evalAt (h ≫ k) e = evalAt h (globalSectionsRingHomSite B S hS k e) := by
  change globalSectionEval _ _ (globalSectionsRingHomSite B S hS (h ≫ k) e) = _
  rw [globalSectionsRingHomSite_comp]
  rfl

/-- `evalAt` of a function whose pullback along `a` vanishes is zero along any morphism factoring
through `a`. -/
theorem evalAt_homMk_eq_zero_of_factors {T : BigFppfOver B S hS} {X X' : AlgebraicSpaces B S hS}
    {a : X'.1 ⟶ X.1} {e : ↥(GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O))}
    (he : globalSectionsRingHomSite B S hS (ObjectProperty.homMk a : X' ⟶ X) e = 0)
    {f : yoneda.obj T ⟶ X.1} (φ : yoneda.obj T ⟶ X'.1) (hφ : φ ≫ a = f) :
    evalAt (ObjectProperty.homMk f : schemeSpace T ⟶ X) e = 0 := by
  rw [show (ObjectProperty.homMk f : schemeSpace T ⟶ X) =
      (ObjectProperty.homMk φ : schemeSpace T ⟶ X') ≫ ObjectProperty.homMk a from
    ObjectProperty.hom_ext _ hφ.symm, evalAt_comp_globalSectionsRingHomSite, he, map_zero]

/-- Along an étale morphism `p` from an object of the site, `evalAt` is the value on the chart
`p`. -/
theorem evalAt_chartFromEtaleHom {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (p : yoneda.obj U ⟶ X.1)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) (e : ↥(GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O))) :
    evalAt (ObjectProperty.homMk p : schemeSpace U ⟶ X) e =
      globalSectionEval _ (op (chartFromEtaleHom B S hS X U p hetale)) e := by
  let d : ChartDiagram B S hS (schemeSpace U).1 X.1
      (ObjectProperty.homMk p : schemeSpace U ⟶ X).hom :=
    ⟨idEtaleChart B S hS U, chartFromEtaleHom B S hS X U p hetale, 𝟙 U, by
      change 𝟙 _ ≫ p = yoneda.map (𝟙 U) ≫ p
      rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]⟩
  refine (globalSectionsRingHomSite_val_chartDiagram B S hS _ e d).trans ?_
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝟙 U)).op).hom
      (e.1 (op (chartFromEtaleHom B S hS X U p hetale))) =
    e.1 (op (chartFromEtaleHom B S hS X U p hetale))
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **A global function vanishing along a surjective étale chart vanishes.** -/
theorem eq_zero_of_evalAt_eq_zero {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (p : yoneda.obj U ⟶ X.1)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (e : ↥(GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O)))
    (he : evalAt (ObjectProperty.homMk p : schemeSpace U ⟶ X) e = 0) : e = 0 := by
  let hrep : yoneda.relativelyRepresentable p := hetale.1
  have hpb := hrep.isPullback' p
  let D : AtlasKernelPairData B S hS X := ⟨U, hrep.pullback p, p, hrep.fst' p, hrep.snd p, hsurj,
    hetale, hpb, hetale.2 p (yoneda.map (hrep.snd p)) (hrep.fst' p) hpb.flip,
    hetale.2 p (hrep.fst p) (hrep.snd p) (hrep.isPullback p)⟩
  have h1 : globalSectionEval _ (op (chartFromEtaleHom B S hS X U p hetale)) e = 0 :=
    (evalAt_chartFromEtaleHom p hetale e).symm.trans he
  refine globalFunctionsChartRestriction_injective B S hS X D ?_
  change globalSectionEval _ (op (chartFromEtaleHom B S hS X U p hetale)) e =
    globalSectionEval _ (op (chartFromEtaleHom B S hS X U p hetale)) 0
  rw [h1, map_zero]

/-- A global function whose pullback to `F` vanishes along a surjective étale chart of `F` has
vanishing pullback. -/
theorem globalSectionsRingHomSite_eq_zero_of_evalAt_comp_eq_zero
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {hG : IsAlgebraicSpace B S hS G} {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ F)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (k : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
    (s : ↥(GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS G hG).O)))
    (hs : evalAt ((ObjectProperty.homMk p : schemeSpace U ⟶ ⟨F, hF⟩) ≫ k) s = 0) :
    globalSectionsRingHomSite B S hS k s = 0 :=
  eq_zero_of_evalAt_eq_zero (X := ⟨F, hF⟩) p hsurj hetale _
    ((evalAt_comp_globalSectionsRingHomSite _ k s).symm.trans hs)

/-- The two legs of the pullback of `g` along `n` agree after composing to `V_j`, when `n` is the
image of `f ≫ q`. -/
private theorem yoneda_map_pullback_fst_comp_eq {Vj Vk U : BigFppfOver B S hS} (g : Vk ⟶ Vj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : Y ⟶ yoneda.obj Vj) (f : yoneda.obj U ⟶ Y)
    (n : U ⟶ Vj) (hn : yoneda.map n = f ≫ q) :
    yoneda.map (pullback.fst g n) ≫ yoneda.map g = (yoneda.map (pullback.snd g n) ≫ f) ≫ q := by
  rw [Category.assoc, ← hn, ← Functor.map_comp, ← Functor.map_comp, pullback.condition]

/-- **The base change of an atlas detects vanishing on the base change.** For `q : Y ⟶ V_j`, an
atlas `N ⟶ Y` and `g : V_k ⟶ V_j`, the base change `V_k ×_{V_j} N ⟶ V_k ×_{V_j} Y` is a
surjective étale chart, so a function on `Y` vanishing along `V_k ×_{V_j} N ⟶ N ⟶ Y` vanishes on
`V_k ×_{V_j} Y`. -/
theorem globalSectionsRingHomSite_pullback_snd_eq_zero {Vj Vk : BigFppfOver B S hS}
    (g : Vk ⟶ Vj) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    (q : Y ⟶ yoneda.obj Vj) (hYk : IsAlgebraicSpace B S hS (pullback (yoneda.map g) q))
    (At : AtlasKernelPairData B S hS ⟨Y, hY⟩) (n : At.U ⟶ Vj) (hn : yoneda.map n = At.f ≫ q)
    (s : ↥(GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS Y hY).O)))
    (hz : evalAt (ObjectProperty.homMk (yoneda.map (pullback.snd g n) ≫ At.f) :
      schemeSpace (pullback g n) ⟶ ⟨Y, hY⟩) s = 0) :
    globalSectionsRingHomSite B S hS (ObjectProperty.homMk (pullback.snd (yoneda.map g) q) :
      (⟨pullback (yoneda.map g) q, hYk⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) s = 0 := by
  let χ : yoneda.obj (pullback g n) ⟶ pullback (yoneda.map g) q :=
    pullback.lift (yoneda.map (pullback.fst g n)) (yoneda.map (pullback.snd g n) ≫ At.f)
      (yoneda_map_pullback_fst_comp_eq g q At.f n hn)
  have hsq : IsPullback χ (yoneda.map (pullback.snd g n)) (pullback.snd (yoneda.map g) q) At.f :=
    IsPullback.of_right (h₁₂ := pullback.fst (yoneda.map g) q) (h₂₂ := q) (v₁₃ := yoneda.map g)
      (by
        rw [pullback.lift_fst, ← hn]
        exact (IsPullback.of_hasPullback g n).map yoneda)
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have e3 : (ObjectProperty.homMk χ : schemeSpace (pullback g n) ⟶
        (⟨pullback (yoneda.map g) q, hYk⟩ : AlgebraicSpaces B S hS)) ≫
        (ObjectProperty.homMk (pullback.snd (yoneda.map g) q) :
          (⟨pullback (yoneda.map g) q, hYk⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) =
      (ObjectProperty.homMk (yoneda.map (pullback.snd g n) ≫ At.f) :
        schemeSpace (pullback g n) ⟶ ⟨Y, hY⟩) :=
    ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)
  refine globalSectionsRingHomSite_eq_zero_of_evalAt_comp_eq_zero χ
    (presheaf_of_isPullback B S hS hsq.flip At.surjective)
    (presheaf_of_isPullback B S hS hsq.flip At.etale) _ s ?_
  rwa [e3]

end AlgebraicGeometry.Artin.StageRings

namespace AlgebraicGeometry.Artin.ContractionSituation

open Space Stacks.Cohomology.SiteModules StageRings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {c : ContractionSituation B S hS} {I : Type u} [Category.{u} I]
  {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {ξ : Triple c κ.pt.obj}
  {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat}

/-- A function on a model `Y` of `V'` over `V_j` which vanishes on `V'` vanishes along
`V_k ×_{V_j} N ⟶ N ⟶ Y` for some `k ⟶ j`, for an affine atlas `N ⟶ Y`. -/
theorem StageModel.exists_evalAt_pullback_snd_eq_zero [IsCofiltered I]
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i))) {j : I}
    (M : StageModel c κ ξ w j)
    (s : ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS M.Y M.isAlgebraicSpace_Y).O)))
    (hs : globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk M.a : (⟨w.V', w.isAlgebraicSpace_V'⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨M.Y, M.isAlgebraicSpace_Y⟩) s = 0)
    (At : AtlasKernelPairData B S hS ⟨M.Y, M.isAlgebraicSpace_Y⟩)
    (hAt : IsAffine ((BigFppfOver.toScheme B S hS).obj At.U)) (n : At.U ⟶ (D.obj j).obj)
    (hn : yoneda.map n = At.f ≫ M.q) :
    ∃ (k : I) (g : k ⟶ j), evalAt (ObjectProperty.homMk
      (yoneda.map (pullback.snd ((D ⋙ ObjectProperty.ι _).map g) n) ≫ At.f) :
        schemeSpace _ ⟶ (⟨M.Y, M.isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS)) s = 0 := by
  let E := D ⋙ ObjectProperty.ι _
  let F := overBaseChangeDiagram E j n ⋙ BigFppfOver.toScheme B S hS
  let cF := (BigFppfOver.toScheme B S hS).mapCone
    (overBaseChangeCone E ((ObjectProperty.ι _).mapCone κ) j n)
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hcF : IsLimit cF := isLimitMapOverBaseChangeCone E ((ObjectProperty.ι _).mapCone κ) j n
    (BigFppfOver.toScheme B S hS) hκ
  have : ∀ h : Over j, IsAffine (F.obj h) := fun h => by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj h.left)) := hD h.left
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj j)) := hD j
    exact isAffine_pullback _ _
  -- the value on the stage `j` of the atlas
  let i₀ : Over j := Over.mk (𝟙 j)
  let h₀ : schemeSpace (pullback (E.map i₀.hom) n) ⟶
      (⟨M.Y, M.isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS) :=
    ObjectProperty.homMk (yoneda.map (pullback.snd (E.map i₀.hom) n) ≫ At.f)
  have hval : ∀ {T : BigFppfOver B S hS} (ψ : T ⟶ pullback (E.map i₀.hom) n),
      ((BigFppfOver.toScheme B S hS).map ψ).appTop (evalAt h₀ s) =
        evalAt (ObjectProperty.homMk (yoneda.map (ψ ≫ pullback.snd (E.map i₀.hom) n) ≫ At.f) :
          schemeSpace T ⟶ (⟨M.Y, M.isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS)) s := by
    intro T ψ
    have e2 : schemeSpaceMap ψ ≫ h₀ = (ObjectProperty.homMk
        (yoneda.map (ψ ≫ pullback.snd (E.map i₀.hom) n) ≫ At.f) :
          schemeSpace T ⟶ (⟨M.Y, M.isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS)) :=
      ObjectProperty.hom_ext _ (by
        change yoneda.map ψ ≫ yoneda.map (pullback.snd (E.map i₀.hom) n) ≫ At.f =
          yoneda.map (ψ ≫ pullback.snd (E.map i₀.hom) n) ≫ At.f
        rw [Functor.map_comp, Category.assoc])
    rw [← e2]
    exact (evalAt_comp ψ h₀ s).symm
  have ht₀ : (cF.π.app i₀).appTop (evalAt h₀ s) = 0 := by
    refine (hval _).trans ?_
    refine evalAt_homMk_eq_zero_of_factors hs (M.isPullback_a.lift
      (yoneda.map (pullback.fst ((κ.π.app j).hom) n))
      (yoneda.map (pullback.snd ((κ.π.app j).hom) n) ≫ At.f) ?_) ?_
    · exact yoneda_map_pullback_fst_comp_eq _ M.q At.f n hn
    · rw [IsPullback.lift_snd]
      change _ = yoneda.map (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ At.f
      rw [pullback.lift_snd]
      rfl
  obtain ⟨k', f', hk'⟩ :=
    exists_appTop_map_eq_zero_of_isAffine_of_isLimit F cF hcF i₀ (evalAt h₀ s) ht₀
  refine ⟨k'.left, k'.hom, ?_⟩
  let ψ : pullback (E.map k'.hom) n ⟶ pullback (E.map i₀.hom) n :=
    pullback.lift (pullback.fst _ _ ≫ E.map f'.left) (pullback.snd _ _)
      (by rw [Category.assoc, ← E.map_comp, Over.w f', pullback.condition])
  have h3 := hval ψ
  rw [pullback.lift_snd] at h3
  rw [← h3]
  exact hk'

/-- **A function on a model `Y` of `V'` over `V_j` which vanishes on `V'` vanishes on
`Y_k = V_k ×_{V_j} Y` for some `k ⟶ j`** (injectivity in `Γ(V', 𝒪) = colim Γ(Y_k, 𝒪)`,
Limits, Lemma 01Z0). -/
theorem StageModel.exists_restrict_eq_zero [IsCofiltered I]
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i))) {j : I}
    (M : StageModel c κ ξ w j)
    (s : ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS M.Y M.isAlgebraicSpace_Y).O)))
    (hs : globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk M.a : (⟨w.V', w.isAlgebraicSpace_V'⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨M.Y, M.isAlgebraicSpace_Y⟩) s = 0) :
    ∃ (k : I) (g : k ⟶ j), globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (M.baseChangeHom g) :
        (⟨(M.baseChange g).Y, (M.baseChange g).isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨M.Y, M.isAlgebraicSpace_Y⟩) s = 0 := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj) := hD j
  obtain ⟨At, hAt⟩ := exists_atlasKernelPairData_isAffine
    (X := (⟨M.Y, M.isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS))
    (isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS (D.obj j).obj (hD j)
      M.isAlgebraicSpace_Y (isAlgebraicSpace_yoneda B S hS _) M.q M.isProper_q.2.2)
  let n : At.U ⟶ (D.obj j).obj := yoneda.preimage (At.f ≫ M.q)
  have hn : yoneda.map n = At.f ≫ M.q := Functor.map_preimage _ _
  obtain ⟨k, g, hz⟩ := M.exists_evalAt_pullback_snd_eq_zero hκ hD s hs At hAt n hn
  refine ⟨k, g, ?_⟩
  exact globalSectionsRingHomSite_pullback_snd_eq_zero ((D ⋙ ObjectProperty.ι _).map g) M.q
    (M.baseChange g).isAlgebraicSpace_Y At n hn s hz

/-- **The kernel and the cokernel of `Γ(V_j) ⟶ Γ(Y)` are killed by a power of an ideal `I_j`
cutting out `Z_j`**, for a stage witness `q : Y ⟶ V_j` (proper, an isomorphism over
`V_j ∖ Z_j`); `AlgebraicGeometry.Artin.StageRings.exists_pow_smul_ker_coker`. -/
theorem StageWitness.exists_pow_smul_ker_coker
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i))) {j : I}
    (W : StageWitness c κ ξ w j)
    {Ij : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj, ⊤)}
    (hZI : ∀ x, x ∈ W.Z ↔ Space.pointsToScheme B S hS (D.obj j).obj x ∈
      ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj).zeroLocus
        (Ij : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj, ⊤))) :
    ∃ N : ℕ, (∀ a, pullbackRingHom B (D.obj j).obj
        (ObjectProperty.homMk W.q : (⟨W.Y, W.isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace (D.obj j).obj) a = 0 → ∀ x ∈ Ij ^ N, x * a = 0) ∧
      ∀ (s : ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B S hS W.Y W.isAlgebraicSpace_Y).O))), ∀ x ∈ Ij ^ N,
        pullbackRingHom B (D.obj j).obj
          (ObjectProperty.homMk W.q : (⟨W.Y, W.isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS) ⟶
            schemeSpace (D.obj j).obj) x * s ∈
          (pullbackRingHom B (D.obj j).obj (ObjectProperty.homMk W.q :
            (⟨W.Y, W.isAlgebraicSpace_Y⟩ : AlgebraicSpaces B S hS) ⟶
              schemeSpace (D.obj j).obj)).range := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj) := hD j
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj) := (D.obj j).property
  exact StageRings.exists_pow_smul_ker_coker (D.obj j).obj hZI W.isIso_q W.isProper_q

end AlgebraicGeometry.Artin.ContractionSituation

end
