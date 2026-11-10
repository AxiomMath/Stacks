module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitExactDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationCokernelOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesRightExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyFinitePresentationConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyLimitSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertySituationBaseChange

/-!
# The direction of Stacks 0GV2 from the limit to a stage

Let `X = lim X_i` be the limit of a cofiltered system of quasi-compact and quasi-separated
algebraic spaces over `S` with affine transition morphisms, and assume `X` has the resolution
property.  This file carries out the proof of the source that some `X_i` has it:

1. choose on a stage `X_{i₀}` the situation of Stacks 0GUY with `π₀ : Y₀ ⟶ X_{i₀}` finite and
   `π₀,_*𝒪_{Y₀}` of finite presentation (Stacks 0874), and base change it to `X` and to the
   later stages (`ResolutionPropertyDescentSituation.exists_baseChange_arrowIso`);
2. on `X`, the resolution property gives `ℰ ⟶ π_*ℐ` onto, with `ℰ` finite locally free
   (Stacks 0GV1, easy direction), that is, an exact sequence `ℰ ⟶ π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)`;
3. descend `ℰ` to a finite locally free module on a stage (Stacks 0D2X) and the exact sequence to
   a later stage (Stacks 07V7, through
   `Stacks.ModuleColimit.PullbackSystem.exists_stage_exact_of_pbL_of_iso`), which is the source's
   comparison of the two quotients `Coker(ℰ_i ⟶ π_{i,*}𝒪_{Y_i})` and `π_{i,*}(𝒪_{Y_i}/ℐ_i)`;
4. at that stage `ℰ_i ⟶ π_{i,*}ℐ_i` is onto, and the converse of Stacks 0GV1 concludes.

## Main results

* `AlgebraicGeometry.Space.exists_stage_hasResolutionProperty_of_inputs`: the assembly of steps
  1–4, with the clauses of Stacks 07V7, Stacks 0D2X(1), the existence part of Stacks 0GUY with `π`
  of finite presentation as its inputs; the converse of Stacks 0GV1 (with `π_*𝒪_Y` of finite
  presentation) is proved, without Noetherian hypotheses, in
  `StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyFinitePresentationConverse`.  These
  inputs are not yet proved here; the theorem carries no `stacks` attribute.

## References

* [Stacks Project, Tag 0GV2](https://stacks.math.columbia.edu/tag/0GV2)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 0D2X](https://stacks.math.columbia.edu/tag/0D2X)
* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-- **The pullback system of modules of the limit situation**: the categories of modules on the
stages and on the limit, the inverse images along the transition morphisms and the projections,
the comparisons of iterated inverse images, and finite presentation as the property of objects.
The three clauses of Stacks 07V7 are statements about it. -/
noncomputable abbrev limitModulePullbackSystem :
    Stacks.ModuleColimit.PullbackSystem.{u, u, u + 1, u + 1} I where
  C j := Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD j).1
    (stageAlgebraicSpace B S hS D hD j).2
  L := Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
    (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2
  pb e := modulePullback B S hS (stageTransition B S hS D hD e)
  pbL j := modulePullback B S hS (limitProjection B S hS D hSize hHomSize hD hAffine j)
  comp e :=
    modulePullbackTriangle B S hS (limitProjection_comp B S hS D hSize hHomSize hD hAffine e)
  P _ M := M.IsFinitePresentationOnSite
  PL M := M.IsFinitePresentationOnSite

/-- The abelian structure on modules, pinned at the universes in use. -/
noncomputable local instance (priority := high) abelianModules_limitHard
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian.{u} _

/-- Inverse images preserve cokernels. -/
theorem modulePullback_preservesColimitsOfShape {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    PreservesColimitsOfShape WalkingParallelPair (modulePullback B S hS f) := by
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS f) :=
    (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  infer_instance

/-- Inverse images keep finite local freeness. -/
theorem isFiniteLocallyFreeOnSite_modulePullback' {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (E : Modules.{u, u} B S hS Y.1 Y.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS f).obj E) :=
  isFiniteLocallyFreeOnSite_modulePullback B S hS f E
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite E hE) hE

attribute [local irreducible] modulePullback modulePullbackTriangle in
open ResolutionPropertyDescentSituation in
/-- **The direction of Stacks 0GV2 from the limit to a stage, from its inputs.**  If the limit has
the resolution property then so does some stage, granted the faithfulness and fullness clauses of
Stacks 07V7 (`hF`, `hFu`), Stacks 0D2X(1) (`h0D2X`), and the existence of the situation of
Stacks 0GUY with `π_*𝒪_Y` of finite presentation (`hsit`); the converse of Stacks 0GV1 for such a
situation is `hasResolutionProperty_of_epi_idealDirectImage_of_isFinitePresentationOnSite`.  See
the module documentation. -/
theorem exists_stage_hasResolutionProperty_of_inputs
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hF : (limitModulePullbackSystem B S hS D hSize hHomSize hD hAffine).Faithfulness)
    (hFu : (limitModulePullbackSystem B S hS D hSize hHomSize hD hAffine).Fullness)
    (h0D2X : ∀ F : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
        (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2,
      SheafOfModules.IsFiniteLocallyFreeOnSite F →
        ∃ (i : I) (G : Modules.{u, u} B S hS (D.obj i) (hD i)),
          SheafOfModules.IsFiniteLocallyFreeOnSite G ∧
            Nonempty ((modulePullback B S hS
              (limitProjection B S hS D hSize hHomSize hD hAffine i)).obj G ≅ F))
    (hsit : ∀ (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
        (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1),
      ∃ sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs,
        (pushforwardStructureModule B S hS (πHom B S hS hZ sit)).IsFinitePresentationOnSite)
    (hres : HasResolutionProperty.{u, u} B S hS
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2) :
    ∃ i, HasResolutionProperty.{u, u} B S hS (D.obj i) (hD i) := by
  classical
  let A := limitModulePullbackSystem B S hS D hSize hHomSize hD hAffine
  let Xs := stageAlgebraicSpace B S hS D hD
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  obtain ⟨sit₀, hfp₀⟩ := hsit (Xs i₀) (hqc i₀) (hqs i₀)
  let c₀ := quotientDirectImageMap hZ sit₀
  have hN₀ := isFinitePresentationOnSite_quotientDirectImage hZ sit₀ hfp₀
  -- the situation on the limit
  let p := limitProjection B S hS D hSize hHomSize hD hAffine i₀
  have hp : IsAffineHom B S hS p.hom := isAffineHom_limitπ B S hS D hSize hHomSize hAffine i₀
  have hqcL := isQuasiCompactSpace_limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine hqc
  have hqsL := isAbsolutelyQuasiSeparated_limitAlgebraicSpace B S hS hZ D hSize hHomSize hD
    hAffine i₀ (hqs i₀)
  obtain ⟨sitL, -, ⟨αL⟩⟩ := exists_baseChange_arrowIso hZ sit₀ p hp hqcL hqsL hfp₀
  obtain ⟨E, hE, e, he⟩ :=
    exists_isFiniteLocallyFreeOnSite_epi_idealDirectImage_of_hasResolutionProperty B S hS hZ
      sitL hres
  obtain ⟨g, w, hex⟩ := exists_exact_of_epi_idealDirectImage hZ sitL _ αL e
  -- descend `ℰ`
  obtain ⟨j, Ej, hEj, ⟨ε⟩⟩ := h0D2X E hE
  let 𝒜₀ := (modulePushforward B S hS (πHom B S hS hZ sit₀)).obj (unitModule hZ sit₀)
  let 𝒩₀ := (modulePushforward B S hS (πHom B S hS hZ sit₀)).obj (cokernel (idealIncl hZ sit₀))
  have hpb : ∀ {j k : I} (e : j ⟶ k) (N : A.C k), A.P k N → A.P j ((A.pb e).obj N) :=
    fun e N hN => isFinitePresentationOnSite_modulePullback B S hS _ N hN
  have hcoker : ∀ j {M N : A.C j} (f : M ⟶ N), A.P j M → A.P j N → A.P j (cokernel f) :=
    fun j M N f hM hN => Stacks.SheafOfModules.isFinitePresentationOnSite_cokernel_of_isColimit
      (cokernel.condition f) (cokernelIsCokernel f) hM hN
  have hEjP : A.P j Ej := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hEj
  have hepi : Epi ((A.pbL i₀).map c₀) := epi_modulePullback_map B S hS p c₀
    (epi_quotientDirectImageMap hZ sit₀)
  have : ∀ {j k : I} (e : j ⟶ k), (A.pb e).PreservesZeroMorphisms :=
    fun e => modulePullback_preservesZeroMorphisms_of_adjunction B S hS _
  have : ∀ {j k : I} (e : j ⟶ k), PreservesColimitsOfShape WalkingParallelPair (A.pb e) :=
    fun e => modulePullback_preservesColimitsOfShape B S hS _
  have : ∀ j, (A.pbL j).PreservesZeroMorphisms :=
    fun j => modulePullback_preservesZeroMorphisms_of_adjunction B S hS _
  have : ∀ j, PreservesColimitsOfShape WalkingParallelPair (A.pbL j) :=
    fun j => modulePullback_preservesColimitsOfShape B S hS _
  obtain ⟨k, a, b, j₀, e₀, j₁, e₁, j₂, e₂, j₃, e₃, j₄, e₄, φ, w', hexl⟩ :=
    A.exists_stage_exact_of_pbL_of_iso hF hFu hpb hcoker (M := 𝒜₀) (N := 𝒩₀) hfp₀ hN₀ c₀
      hEjP ε g w hex hepi
  let t := e₄ ≫ e₃ ≫ e₂ ≫ e₁ ≫ e₀ ≫ b
  let αc := arrowIsoOfNatIso (modulePullbackStageTransitionChainIso B S hS D hD b e₀ e₁ e₂ e₃ e₄) c₀
  obtain ⟨sitl, hfpl, ⟨αl⟩⟩ := exists_baseChange_arrowIso hZ sit₀ (stageTransition B S hS D hD t)
    (hAffine t) (hqc j₄) (hqs j₄) hfp₀
  obtain ⟨el, hel⟩ := exists_epi_idealDirectImage_of_exact hZ sitl _ (αc ≪≫ αl) φ w' hexl
  have hFLF : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((A.pb e₀ ⋙ A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄).obj ((A.pb a).obj Ej)) := by
    have h := fun {x y : I} (e : x ⟶ y) (G : A.C y)
        (hG : SheafOfModules.IsFiniteLocallyFreeOnSite G) =>
      isFiniteLocallyFreeOnSite_modulePullback' B S hS (stageTransition B S hS D hD e) G hG
    exact h e₄ _ (h e₃ _ (h e₂ _ (h e₁ _ (h e₀ _ (h a _ hEj)))))
  exact ⟨j₄, hasResolutionProperty_of_epi_idealDirectImage_of_isFinitePresentationOnSite B S hS hZ
    (Xs j₄) (hqc j₄) (hqs j₄) sitl hfpl _ hFLF el hel⟩

end AlgebraicGeometry.Space

end
