module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectGlueAlongSystem

/-!
# The square step of the descent of perfect objects along Situation 09RH

In Situation 09RH let `j ↦ W_j` be a directed system over a quasi-compact quasi-separated
algebraic space `W`, presented as the base change of the situation along `W ⟶ X₀`
(`AlgebraicGeometry.Space.DescentSituation.BaseChangeData`), with vertex `W_∞`.  Say that perfect
objects descend along a family of morphisms `p_j : X ⟶ Y_j` if every perfect object of `D(𝒪_X)`
is the derived pullback of a perfect object of some `D(𝒪_{Y_j})`
(`AlgebraicGeometry.Space.PerfectObjectsDescend`).  This file proves the step of the induction of
Stacks 08GP for the essential surjectivity half of Stacks 09RJ: for an elementary distinguished
square `(U ⊆ W, V ⟶ W)` with quasi-compact quasi-separated intersection, if perfect objects
descend along the systems of the open subspaces `U ×_W W_j` and of the étale algebraic spaces
`V ×_W W_j`, then they descend along `j ↦ W_j`.

The proof is the source's.  A perfect object `E` of `D(𝒪_{W_∞})` restricts to perfect objects
over `U_∞` and `V_∞`, which descend to perfect objects `A` over some `U_i` and `Bo` over some
`V_i`, the two stages being made equal by directedness.  Over `P_∞ = U_∞ ×_{W_∞} V_∞` the
restrictions of `A` and `Bo` are identified through `E`.  The system of intersections read beyond
the stage `i` is presented as a base change of Situation 09RH with its chosen index moved to `i`,
over the quasi-compact quasi-separated `P_i`, so Stacks 09RI for perfect objects
(`AlgebraicGeometry.Space.DescentSituation.BaseChangeData.isColim_of_isPerfect`) applies to the
restrictions to `P_i`, and the identification descends to an isomorphism at a later stage `m`
(`CategoryTheory.PullbackData.LimitSystem.IsColim.exists_iso`).  The objects are glued at `W_m`
by `AlgebraicGeometry.Space.exists_isPerfect_iso_of_factorHom_eq_limitComparisonIso`.

## Main definitions

* `AlgebraicGeometry.Space.PerfectObjectsDescend`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.BaseChangeData.perfectObjectsDescend_of_eds`.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Perfect objects descend along a family of morphisms `p_j : X ⟶ Y_j`**: every perfect
object of `D(𝒪_X)` is the derived pullback along some `p_j` of a perfect object of
`D(𝒪_{Y_j})`. -/
def PerfectObjectsDescend {J : Type w} {X : AlgebraicSpaces B S hS}
    {Y : J → AlgebraicSpaces B S hS} (p : ∀ j, X ⟶ Y j) : Prop :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  ∀ E : @DerivedCategory (Modules.{u, u} B S hS X.1 X.2) _ _ (HasDerivedCategory.standard _),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E →
      ∃ (j : J) (A : @DerivedCategory (Modules.{u, u} B S hS (Y j).1 (Y j).2)
        _ _ (HasDerivedCategory.standard _)),
        letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (Y j).1 (Y j).2)
        (smallEtaleRingedSite B S hS (Y j).1 (Y j).2).IsPerfect A ∧
          Nonempty ((smallEtaleDerivedModulePullback B S hS (p j)).obj A ≅ E)

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I}
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {y : W ⟶ D.stage D.base}
  {Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W D.Stages}

namespace BaseChangeData

include hsq in
/-- **The square step of the descent of perfect objects along Situation 09RH.**  For a presented
system `j ↦ W_j` over `W` and an elementary distinguished square of `W` whose intersection is
quasi-compact and quasi-separated, if perfect objects descend along the systems of the open
subspaces and of the étale algebraic spaces of the base changes of the square, then they descend
along `j ↦ W_j`. -/
theorem perfectObjectsDescend_of_eds (β : D.BaseChangeData y Sys)
    (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (hPqc : IsQuasiCompactSpace B S hS (Space.edsInter B S hS hsq).1)
    (hPqs : IsAbsolutelyQuasiSeparated B S hS hZ (Space.edsInter B S hS hsq).1)
    (hU : PerfectObjectsDescend (edsOpenSystem hsq Sys).proj)
    (hV : PerfectObjectsDescend (edsEtaleSystem hsq Sys).proj) :
    PerfectObjectsDescend Sys.proj := by
  intro E hE
  have hP := (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
  obtain ⟨iU, A₀, hA₀, ⟨αU₀⟩⟩ := hU _ (isPerfect_smallEtaleDerivedModulePullback
    (edsOpenHom B S hS (edsPreimage hsq Sys.limitToBase)) E hE)
  obtain ⟨iV, B₀, hB₀, ⟨αV₀⟩⟩ := hV _ (isPerfect_smallEtaleDerivedModulePullback
    (edsEtaleHom B S hS (edsPreimage hsq Sys.limitToBase)) E hE)
  obtain ⟨i, hiU, hiV⟩ := (isDirectedStages (D := D)).directed iU iV
  -- the two descended objects at the common stage `i`
  let A := (smallEtaleDerivedModulePullback B S hS ((edsOpenSystem hsq Sys).transition hiU)).obj A₀
  let Bo :=
    (smallEtaleDerivedModulePullback B S hS ((edsEtaleSystem hsq Sys).transition hiV)).obj B₀
  have hA := isPerfect_smallEtaleDerivedModulePullback ((edsOpenSystem hsq Sys).transition hiU)
    A₀ hA₀
  have hBo := isPerfect_smallEtaleDerivedModulePullback ((edsEtaleSystem hsq Sys).transition hiV)
    B₀ hB₀
  let αU := ((DerivedPullbackComposition.canonical B S hS).iso ((edsOpenSystem hsq Sys).proj i)
    ((edsOpenSystem hsq Sys).transition hiU) ((edsOpenSystem hsq Sys).proj iU)
    ((edsOpenSystem hsq Sys).proj_transition hiU)).app A₀ ≪≫ αU₀
  let αV := ((DerivedPullbackComposition.canonical B S hS).iso ((edsEtaleSystem hsq Sys).proj i)
    ((edsEtaleSystem hsq Sys).transition hiV) ((edsEtaleSystem hsq Sys).proj iV)
    ((edsEtaleSystem hsq Sys).proj_transition hiV)).app B₀ ≪≫ αV₀
  -- the intersections beyond `i`, presented over `P_i`
  have βP := β.edsInter hsq rfl
  have hPiqc := βP.isQuasiCompactSpace_stage hPqc hPqs i
  have hPiqs := βP.isAbsolutelyQuasiSeparated_stage hPqc hPqs i
  have hX := isPerfect_smallEtaleDerivedModulePullback
    (edsFst B S hS (edsPreimage hsq (Sys.toBase i))) A hA
  have hY := isPerfect_smallEtaleDerivedModulePullback
    (edsSnd B S hS (edsPreimage hsq (Sys.toBase i))) Bo hBo
  have colim := (βP.rebase i).isColim_of_isPerfect hconv hPiqc hPiqs
  have hXY := colim _ _ hX hY
  have hYX := colim _ _ hY hX
  have hXX := colim _ _ hX hX
  have hYY := colim _ _ hY hY
  obtain ⟨m, c, hc⟩ := hXY.exists_iso hP hYX hXX hYY
    ((DerivedPullbackComposition.canonical B S hS).limitComparisonIso
      (edsFst B S hS (edsPreimage hsq Sys.limitToBase)) ((edsOpenSystem hsq Sys).proj i)
      ((edsInterSystem hsq Sys).proj i) (edsFst B S hS (edsPreimage hsq (Sys.toBase i)))
      (edsFst_comp_edsPreimageOpenMap hsq _ _ _ (Sys.proj_toBase i))
      (edsSnd B S hS (edsPreimage hsq Sys.limitToBase)) ((edsEtaleSystem hsq Sys).proj i)
      (edsSnd B S hS (edsPreimage hsq (Sys.toBase i)))
      (edsSnd_comp_edsPreimageEtaleMap hsq _ _ _ (Sys.proj_toBase i))
      (edsOpenHom B S hS (edsPreimage hsq Sys.limitToBase))
      (edsEtaleHom B S hS (edsPreimage hsq Sys.limitToBase))
      (isPullback_edsInter B S hS (edsPreimage hsq Sys.limitToBase)).flip.w A Bo E αU αV)
  have hc' := ((DerivedPullbackComposition.canonical B S hS).factorHom_toPullbackData
    ((edsInterSystem hsq Sys).proj_transition (D.le_stageOfLE i m)) _ _ c.hom).symm.trans hc
  obtain ⟨F, hF, hFE⟩ := exists_isPerfect_iso_of_factorHom_eq_limitComparisonIso
    (hi := edsPreimage hsq (Sys.toBase i)) (hm := edsPreimage hsq (Sys.toBase (D.stageOfLE i m)))
    (hl := edsPreimage hsq Sys.limitToBase) (Sys.proj (D.stageOfLE i m))
    ((edsOpenSystem hsq Sys).proj (D.stageOfLE i m))
    ((edsEtaleSystem hsq Sys).proj (D.stageOfLE i m))
    ((edsInterSystem hsq Sys).proj (D.stageOfLE i m))
    (edsPreimageOpenMap_comp hsq _ _ _ (Sys.proj_toBase _))
    (edsPreimageEtaleMap_comp hsq _ _ _ (Sys.proj_toBase _))
    (edsFst_comp_edsPreimageOpenMap hsq _ _ _ (Sys.proj_toBase _))
    (edsSnd_comp_edsPreimageEtaleMap hsq _ _ _ (Sys.proj_toBase _))
    ((edsOpenSystem hsq Sys).transition (D.le_stageOfLE i m))
    ((edsEtaleSystem hsq Sys).transition (D.le_stageOfLE i m))
    ((edsInterSystem hsq Sys).transition (D.le_stageOfLE i m))
    (edsFst_comp_edsPreimageOpenMap hsq _ _ _ (Sys.transition_toBase _))
    (edsSnd_comp_edsPreimageEtaleMap hsq _ _ _ (Sys.transition_toBase _))
    ((edsOpenSystem hsq Sys).proj i) ((edsEtaleSystem hsq Sys).proj i)
    ((edsInterSystem hsq Sys).proj i)
    ((edsOpenSystem hsq Sys).proj_transition _) ((edsEtaleSystem hsq Sys).proj_transition _)
    ((edsInterSystem hsq Sys).proj_transition _)
    (edsFst_comp_edsPreimageOpenMap hsq _ _ _ (Sys.proj_toBase i))
    (edsSnd_comp_edsPreimageEtaleMap hsq _ _ _ (Sys.proj_toBase i)) E A Bo hA hBo αU αV c hc'
  exact ⟨D.stageOfLE i m, F, hF, hFE⟩

end BaseChangeData

end DescentSituation

end AlgebraicGeometry.Space

end
