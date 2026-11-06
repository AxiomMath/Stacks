module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartWSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedQuotientFiniteTypeOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Stacks 0A0X from the approximations it is proved with

**Stacks 0A0X.** Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `ℤ` with `Y`
quasi-compact and quasi-separated. Then there is a directed set `I` and an inverse system
`(f_i : X_i ⟶ Y_i)` over `I` of morphisms of algebraic spaces with affine transition morphisms,
each `f_i` proper and of finite presentation and each `Y_i` of finite presentation over `ℤ`,
such that `(X ⟶ Y) = lim (X_i ⟶ Y_i)`.

The proof here is the second route of the source, through the scheme-theoretic images of
Stacks 0CP9, with one model only. Stacks 07SU writes `Y = lim_j Y_j` with `Y_j` of finite
presentation over `ℤ`, hence Noetherian (Stacks 06G4, 04ZK), so `(Y_j)` is a system as in
Situation 0CP6. Stacks 0A0W gives a closed immersion `X ⟶ X'` with `X' ⟶ Y` proper and of finite
presentation; Stacks 07SK descends `X' ⟶ Y` to `W₀ ⟶ Y_{j₀}` of finite presentation, and
Stacks 08K1 makes its base change `W ⟶ Y_{j₁}` proper. Then `X ⟶ W ⟶ Y_{j₁}` is a diagram as in
Stacks 0CP8, and Stacks 0CP9 writes `X = lim_{j ≥ j₁} X_j` with `X_j` the scheme-theoretic image
of `X ⟶ Y_j ×_{Y_{j₁}} W`. The morphism `f_j : X_j ⟶ Y_j` is the closed immersion into
`Y_j ×_{Y_{j₁}} W` followed by the base change of `W ⟶ Y_{j₁}`, so it is proper, and it is of
finite presentation because `Y_j` is Noetherian (Stacks 06G4); the transition morphisms of the
image system are affine. Since every `f_j` factors through the same model, the morphisms of
image systems of Stacks 0CPA and the properness statement of Stacks 0CPE are not needed, and
neither is the fullness half of Stacks 07SK.

Stacks 07SK, 08K1 and 0CP9 are available in this development only for systems indexed by a set
below the cofinality of the site's cutoff, which the system of Stacks 07SU need not be. The
source states them under the standing convention of Section 70.2 (tag 07SD); as in
`AlgebraicGeometry.Space.ampleSpreadsFromResidueFieldsToOpens_of_approximation`
the convention is an abstract property `Conv` of inverse systems, and each of the three
results is an explicit hypothesis in the form of the library's statement with the bound on the
index replaced by `Conv`. Stacks 07SU is
`AlgebraicGeometry.Space.hasNoetherianApproximation_of_hasWSystems`, whose one input is the
W-systems `hW`; that the convention may be imposed on the approximation it produces is the
hypothesis `hconv`. Stacks 0A0W is the hypothesis `h0A0W`, in its registered form.
Nothing here is registered.

## Main results

* `AlgebraicGeometry.Space.exists_descentSituation_arrow_of_approximations`: the conclusion of
  Stacks 0A0X, as a morphism of two `AlgebraicGeometry.Space.DescentSituation`s, together with any
  two properties `Conv'` of the two systems which the hypotheses `hTail` and `hImage` grant.
* `AlgebraicGeometry.Space.exists_isLimit_isProper_isFinitePresentation_arrow_of_approximations`:
  the statement of Stacks 0A0X from the inputs above.
* `AlgebraicGeometry.Space.exists_descentSituation_arrow_conv_of_approximations`: the same over an
  affine target, with the convention for both systems, in the shape `h0A0X` of
  `AlgebraicGeometry.Space.ampleSpreadsFromResidueFieldsToOpens_of_approximation` consumes.

## References

* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Tails of a directed set -/

section Tail

variable {I : Type u} [Preorder I]

/-- The inclusion of the tail `{j // i₁ ≤ j}` of a preorder. -/
def tailInclusion (i₁ : I) : {j : I // i₁ ≤ j} ⥤ I :=
  Monotone.functor (f := Subtype.val) fun _ _ h => h

/-- The tail `{j // i₁ ≤ j}` of a preorder, as stages over `i₁` in the opposite category. -/
def tailOver (i₁ : I) : {j : I // i₁ ≤ j}ᵒᵖ ⥤ Over (op i₁) where
  obj j := Over.mk (homOfLE j.unop.2).op
  map g := Over.homMk (homOfLE (leOfHom g.unop)).op
    (Quiver.Hom.unop_inj (C := I) (Subsingleton.elim _ _))
  map_id _ := by ext; exact Subsingleton.elim _ _
  map_comp _ _ := by ext; exact Subsingleton.elim _ _

/-- A tail of a directed preorder is directed. -/
theorem isDirected_tail [IsDirected I (· ≤ ·)] (i₁ : I) :
    IsDirected {j : I // i₁ ≤ j} (· ≤ ·) :=
  ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩

variable [IsDirected I (· ≤ ·)]

/-- The inclusion of a tail of a directed preorder is final. -/
theorem final_tailInclusion (i₁ : I) : (tailInclusion i₁).Final := by
  have := isDirected_tail i₁
  have : Nonempty {j : I // i₁ ≤ j} := ⟨⟨i₁, le_rfl⟩⟩
  refine Functor.final_of_exists_of_isFiltered _ (fun d => ?_) (fun {d c} s s' => ?_)
  · obtain ⟨c, hdc, hic⟩ := directed_of (· ≤ ·) d i₁
    exact ⟨⟨c, hic⟩, ⟨homOfLE hdc⟩⟩
  · exact ⟨c, 𝟙 _, Subsingleton.elim _ _⟩

/-- The tail of a directed preorder is initial among the stages over its first index. -/
theorem initial_tailOver (i₁ : I) : (tailOver i₁).Initial := by
  have := isDirected_tail i₁
  have : Nonempty {j : I // i₁ ≤ j} := ⟨⟨i₁, le_rfl⟩⟩
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d => ?_) (fun {d c} s s' => ?_)
  · exact ⟨op ⟨d.left.unop, leOfHom d.hom.unop⟩, ⟨Over.homMk (𝟙 _)
      (Quiver.Hom.unop_inj (C := I) (Subsingleton.elim _ _))⟩⟩
  · refine ⟨c, 𝟙 _, ?_⟩
    ext
    exact Subsingleton.elim _ _

end Tail

/-! ### Finite presentation over `ℤ` -/

section Integers

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The presheaf represented by the identity of the base is the terminal presheaf. -/
def yonedaOverIdIsoTerminalOverIntegers :
    yoneda.obj (Over.mk (𝟙 (B.obj hZ))) ≅ ⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :=
  ((Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal

variable {B hZ}

/-- **A quasi-separated space of finite type over `ℤ` is of finite presentation over `ℤ`,
quasi-compact and locally Noetherian** (Stacks 06G4 and 04ZK over the Noetherian base `Spec ℤ`),
with finite type read through `AlgebraicGeometry.Space.viewOverIntegers` as in
`AlgebraicGeometry.Space.NoetherianApproximation`. -/
theorem isFinitePresentation_terminal_of_isFiniteType_viewOverIntegers {F :
  ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)}
    (hF : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ F)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ F)
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))) :
    IsFinitePresentation B (⊤_ Scheme.{u}) hZ (terminal.from F) ∧
      IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ F ∧
      HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ F
        (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  -- the isomorphism to the terminal presheaf has any such property of schemes
  have hiso (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] :
      (Q.inverseImage (BigFppfOver.toScheme B _ hZ)).presheaf
        (yonedaOverIdIsoTerminalOverIntegers B hZ).hom :=
    have := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := Q)
    presheaf_of_isIso B _ hZ (MorphismProperty.RespectsIso.inverseImage _ _)
      (fun U => by simpa using Q.id_mem _) _
  -- the terminal presheaf is represented by the terminal scheme, which is locally Noetherian
  have hN₀ : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
    have : IsNoetherianRing (ULift.{u} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
    exact LocallyOfFiniteType.isLocallyNoetherian
      (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  have hN : HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ (⊤_
    ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    ⟨Over.mk (𝟙 (B.obj hZ)), (yonedaOverIdIsoTerminalOverIntegers B hZ).hom,
      hiso (@Surjective.{u}), hiso (@Etale.{u}),
      hN₀⟩
  have hqc₀ : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (⊤_
    ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) :=
    isQuasiCompactSpace_of_iso B _ hZ (yonedaOverIdIsoTerminalOverIntegers B hZ)
      (isQuasiCompactSpace_yoneda_of_isAffine B _ hZ (Over.mk (𝟙 (B.obj hZ)))
        (IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv))
  let e := viewOverIntegersOfTerminalIso F
  have hft : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from F) :=
    ⟨(isLocallyOfFiniteType_terminal_iff_of_iso B _ hZ e).mp h.1, by
      rw [show terminal.from F = e.inv ≫ terminal.from _ from terminal.hom_ext _ _]
      exact (isQuasiCompact_isIso_comp_iff B _ hZ e.inv _).2 h.2⟩
  have hfp := isFinitePresentation_of_isFiniteType B _ hZ hF (isAlgebraicSpace_terminal B _ hZ) _
    hN hft (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B _ hZ hZ hF hqs _)
  exact ⟨hfp, isQuasiCompactSpace_of_isFinitePresentation B _ hZ _
      (isAlgebraicSpace_terminal B _ hZ) hqc₀ hfp,
    isLocallyNoetherian_of_isLocallyOfFiniteType B _ hZ hF (isAlgebraicSpace_terminal B _ hZ) _
      hft.1 hN⟩

end Integers

/-! ### Tails of Noetherian limit systems and of their image systems -/

section TailSituations

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [Nonempty I] [IsDirected I (· ≤ ·)]

/-- The tail `j ≥ i₁` of a Noetherian limit system, as a descent situation. -/
def NoetherianLimitSystem.tailDescentSituation (N : NoetherianLimitSystem B _ hZ hZ I) (i₁ : I) :
    haveI := isDirected_tail i₁
    DescentSituation B (⊤_ Scheme.{u}) hZ hZ {j : I // i₁ ≤ j} :=
  haveI := isDirected_tail i₁
  haveI := final_tailInclusion i₁
  { system := (tailInclusion i₁).op ⋙ N.system
    algebraicSpace := fun j => N.system_isAlgebraicSpace j.1
    transition_affine := fun _ => N.transition_affine _
    quasiCompact := fun j => (N.noetherian j.1).1
    quasiSeparated := fun j => (N.noetherian j.1).2.1
    limitCone := N.limitCone.whisker (tailInclusion i₁).op
    isLimit := (Functor.Initial.isLimitWhiskerEquiv (tailInclusion i₁).op _).symm N.isLimit
    limitAlgebraicSpace := N.limit_isAlgebraicSpace
    base := ⟨i₁, le_rfl⟩ }

namespace GoodDiagram

variable {N : NoetherianLimitSystem B _ hZ hZ I}
  {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {f : X ⟶ N.limitCone.pt}
  (G : GoodDiagram B _ hZ hZ N f)

/-- The members of the system of scheme-theoretic images of a good diagram with quasi-separated
model are quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_imageSystem_obj
    (hW : IsAbsolutelyQuasiSeparated B _ hZ hZ G.model) (j : Over (op G.index)) :
    IsAbsolutelyQuasiSeparated B _ hZ hZ ((imageSystem G).obj j) :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ (imageSystem_isAlgebraicSpace G j)
    (isAbsolutelyQuasiSeparated_pullback B _ hZ hZ (N.system.map j.hom) G.modelMap
      (N.system_isAlgebraicSpace j.left.unop) G.model_isAlgebraicSpace
      (N.system_isAlgebraicSpace G.index) (N.noetherian j.left.unop).2.1 hW)
    (isQuasiSeparated_of_isClosedImmersion B _ hZ (isClosedSubspace_stageImage G j).2)

/-- The tail `j ≥ G.index` of the system of scheme-theoretic images of a good diagram, as a
descent situation, when the model is quasi-separated and `X` is the limit of the images. -/
def tailDescentSituation (hX : IsAlgebraicSpace B _ hZ X)
    (hW : IsAbsolutelyQuasiSeparated B _ hZ hZ G.model) (hG : IsLimit (imageCone G)) :
    haveI := isDirected_tail G.index
    DescentSituation B (⊤_ Scheme.{u}) hZ hZ {j : I // G.index ≤ j} :=
  haveI := isDirected_tail G.index
  haveI := initial_tailOver G.index
  { system := tailOver G.index ⋙ imageSystem G
    algebraicSpace := fun _ => imageSystem_isAlgebraicSpace G _
    transition_affine := fun _ => imageSystem_map_isAffineHom G _
    quasiCompact := fun _ => imageSystem_isQuasiCompactSpace G _
    quasiSeparated := fun _ => isAbsolutelyQuasiSeparated_imageSystem_obj G hW _
    limitCone := (imageCone G).whisker (tailOver G.index)
    isLimit := (Functor.Initial.isLimitWhiskerEquiv (tailOver G.index) _).symm hG
    limitAlgebraicSpace := hX
    base := ⟨G.index, le_rfl⟩ }

/-- The morphism from the tail of the image system of a good diagram to the tail of its
Noetherian limit system: the closed immersion into the base-changed model, then the projection. -/
def tailDescentHom (hX : IsAlgebraicSpace B _ hZ X)
    (hW : IsAbsolutelyQuasiSeparated B _ hZ hZ G.model) (hG : IsLimit (imageCone G)) :
    (G.tailDescentSituation hX hW hG).system ⟶ (N.tailDescentSituation G.index).system where
  app j := (stageImage G ((tailOver G.index).obj j)).ι ≫ pullback.fst _ _
  naturality j j' g := by
    change imageTransition G ((tailOver G.index).map g) ≫
        (stageImage G ((tailOver G.index).obj j')).ι ≫ pullback.fst _ _ =
      ((stageImage G ((tailOver G.index).obj j)).ι ≫ pullback.fst _ _) ≫
        N.system.map ((tailInclusion G.index).op.map g)
    rw [imageTransition_ι_assoc, stageTargetMap_fst, Category.assoc]
    rfl

/-- The tail morphism of a good diagram is compatible with `f` on the limits. -/
theorem tailDescentSituation_π_app_comp_tailDescentHom_app (hX : IsAlgebraicSpace B _ hZ X)
    (hW : IsAbsolutelyQuasiSeparated B _ hZ hZ G.model) (hG : IsLimit (imageCone G))
    (i : {j : I // G.index ≤ j}) :
    (G.tailDescentSituation hX hW hG).limitCone.π.app (op i) ≫
        (G.tailDescentHom hX hW hG).app (op i) =
      f ≫ (N.tailDescentSituation G.index).limitCone.π.app (op i) :=
  (imageCone_π_ι_assoc G ((tailOver G.index).obj (op i)) (pullback.fst _ _)).trans
    (stageMap_fst G ((tailOver G.index).obj (op i)))

/-- The tail morphism of a good diagram with proper model is proper at every stage. -/
theorem isProper_tailDescentHom_app (hX : IsAlgebraicSpace B _ hZ X)
    (hW : IsAbsolutelyQuasiSeparated B _ hZ hZ G.model) (hG : IsLimit (imageCone G))
    (hp : IsProper B _ hZ G.modelMap) (i : {j : I // G.index ≤ j}) :
    IsProper B _ hZ ((G.tailDescentHom hX hW hG).app (op i)) :=
  isProper_comp B _ hZ (imageSystem_isAlgebraicSpace G _) (isAlgebraicSpace_stageTarget G _)
    (N.system_isAlgebraicSpace i.1) _ _
    (isProper_of_isClosedImmersion B _ hZ (imageSystem_isAlgebraicSpace G _)
      (isAlgebraicSpace_stageTarget G _) _ (isClosedSubspace_stageImage G _).2)
    (isProper_pullback_fst B _ hZ G.model_isAlgebraicSpace (N.system_isAlgebraicSpace G.index)
      (N.system_isAlgebraicSpace i.1) _ _ hp)

/-- The tail morphism of a good diagram with proper model is of finite presentation at every
stage. -/
theorem isFinitePresentation_tailDescentHom_app (hX : IsAlgebraicSpace B _ hZ X)
    (hW : IsAbsolutelyQuasiSeparated B _ hZ hZ G.model) (hG : IsLimit (imageCone G))
    (hp : IsProper B _ hZ G.modelMap) (i : {j : I // G.index ≤ j}) :
    IsFinitePresentation B _ hZ ((G.tailDescentHom hX hW hG).app (op i)) :=
  isFinitePresentation_of_isFiniteType B _ hZ (imageSystem_isAlgebraicSpace G _)
    (N.system_isAlgebraicSpace i.1) _ (N.noetherian i.1).2.2
    (G.isProper_tailDescentHom_app hX hW hG hp i).2.1
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B _ hZ hZ
      (imageSystem_isAlgebraicSpace G _) (isAbsolutelyQuasiSeparated_imageSystem_obj G hW _) _)

/-- The good diagram `X ⟶ W ⟶ B_i` of a closed immersion `ι : X ⟶ X'`, with `X' ⟶ B` the base
change of a model `w : W₀ ⟶ B_j` and `W` its base change to a later stage `i`. -/
def ofIsPullback {X' W₀ : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {ι : X ⟶ X'}
    (hι : IsClosedImmersion B _ hZ ι) {p : X' ⟶ N.limitCone.pt} (hιp : ι ≫ p = f) {j i : I}
    (hji : j ≤ i) {w : W₀ ⟶ N.system.obj (op j)} {q : X' ⟶ W₀}
    (hsq : IsPullback q p w (N.limitCone.π.app (op j)))
    (hW : IsAlgebraicSpace B _ hZ (pullback (N.system.map (homOfLE hji).op) w))
    (hft : IsFiniteType B _ hZ (pullback.fst (N.system.map (homOfLE hji).op) w)) :
    GoodDiagram B _ hZ hZ N f where
  index := i
  model := pullback (N.system.map (homOfLE hji).op) w
  model_isAlgebraicSpace := hW
  modelMap := pullback.fst _ _
  toModel := ι ≫ pullback.lift _ _
    (by rw [Category.assoc, N.limitCone.w, hsq.w] :
      (p ≫ N.limitCone.π.app (op i)) ≫ N.system.map (homOfLE hji).op = q ≫ w)
  commutes := by rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hιp]
  isFiniteType := hft
  isClosedImmersion := by
    have hout : IsPullback (pullback.lift (p ≫ N.limitCone.π.app (op i)) q
        (by rw [Category.assoc, N.limitCone.w, hsq.w]) ≫
          pullback.snd (N.system.map (homOfLE hji).op) w) p w
        (N.limitCone.π.app (op i) ≫ N.system.map (homOfLE hji).op) := by
      rwa [pullback.lift_snd, N.limitCone.w]
    have hleft := IsPullback.of_right hout (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback _ w).flip
    convert isClosedImmersion_comp B _ hZ _ _ hι
      (isClosedImmersion_of_isIso B _ hZ hleft.flip.isoPullback.hom) using 1
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst, hιp]
    · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd]

end GoodDiagram

end TailSituations

/-! ### The assembly -/

section Assembly

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The base change of `w` along `a` is proper if and only if its comparison map to the base
change of the identity is. -/
theorem isProper_pullback_map_id_iff {A S W : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B _ hZ A) (hS : IsAlgebraicSpace B _ hZ S)
    (hW : IsAlgebraicSpace B _ hZ W) (a : A ⟶ S) (w : W ⟶ S) :
    IsProper B _ hZ (pullback.map a w a (𝟙 S) (𝟙 _) w (𝟙 _) (by simp) (by simp)) ↔
      IsProper B _ hZ (pullback.fst a w) := by
  have hAW := isAlgebraicSpace_pullback B _ hZ a w hA hW hS
  have hAS := isAlgebraicSpace_pullback B _ hZ a (𝟙 S) hA hS hS
  have hm : pullback.map a w a (𝟙 S) (𝟙 _) w (𝟙 _) (by simp) (by simp) ≫ pullback.fst a (𝟙 S) =
      pullback.fst a w := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← hm]
    exact isProper_comp B _ hZ hAW hAS hA _ _ h
      (isProper_of_isClosedImmersion B _ hZ hAS hA _ (isClosedImmersion_of_isIso B _ hZ _))
  · rw [(IsIso.eq_comp_inv _).2 hm]
    exact isProper_comp B _ hZ hAW hA hAS _ _ h
      (isProper_of_isClosedImmersion B _ hZ hA hAS _ (isClosedImmersion_of_isIso B _ hZ _))

/-- A model `W₀ ⟶ T` of `p : X' ⟶ Y`, given as an isomorphism of `p` with the base change of
`W₀` along `πL : L ⟶ T` for `Y ≅ L`, makes `p` the base change of `W₀ ⟶ T`. -/
theorem isPullback_of_iso_overPullback {X' Y L T : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    {p : X' ⟶ Y} {eL : Y ≅ L} {πL : L ⟶ T} {π : Y ⟶ T} (hπ : eL.hom ≫ πL = π) {W₀ : Over T}
    (e₀ : Over.mk (p ≫ eL.hom) ≅ (Over.pullback πL).obj W₀) :
    IsPullback (e₀.hom.left ≫ pullback.fst W₀.hom πL) p W₀.hom π := by
  refine IsPullback.of_iso (IsPullback.of_hasPullback W₀.hom πL)
    ((Over.forget _).mapIso e₀).symm (Iso.refl _) eL.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · have h := Over.w e₀.inv
    simp only [Over.mk_hom, Over.pullback_obj_hom] at h
    rw [← h]
    simp
  · simp
  · simp [← hπ]

/-- The base change of a model `W₀ ⟶ T` of a proper morphism `p : X' ⟶ Y` along
`πL : L ⟶ T`, for `Y ≅ L`, is proper. -/
theorem isProper_pullback_fst_of_iso_overPullback
    {X' Y L T : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {p : X' ⟶ Y} (eL : Y ≅ L)
    {πL : L ⟶ T} {W₀ : Over T} (e₀ : Over.mk (p ≫ eL.hom) ≅ (Over.pullback πL).obj W₀)
    (hp : IsProper B _ hZ p) : IsProper B _ hZ (pullback.fst πL W₀.hom) := by
  refine isProper_of_arrowIso B _ hZ p _
    ((Over.forget _).mapIso e₀ ≪≫ pullbackSymmetry _ _).hom eL.hom ?_ hp
  have h := Over.w e₀.hom
  simp only [Over.mk_hom, Over.pullback_obj_hom] at h
  simp only [Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]
  rw [pullbackSymmetry_hom_comp_fst, h]

/-- **Stacks 0A0X, as a morphism of descent situations, from Stacks 07SU under a convention.**
This is `AlgebraicGeometry.Space.exists_descentSituation_arrow_of_approximations` with its two
inputs about Stacks 07SU, the W-systems `hW` and the choice `hconv` of an approximation satisfying
`Conv`, replaced by the one input `h07SU` they are used for: every quasi-compact quasi-separated
algebraic space over `ℤ` has a Noetherian approximation whose system satisfies `Conv`. The other
inputs are those of `AlgebraicGeometry.Space.exists_descentSituation_arrow_of_approximations`. -/
theorem exists_descentSituation_arrow_of_convNoetherianApproximation
    (Conv : ∀ {J : Type u} [Category.{u} J], (J ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      → Prop)
    (Conv' : ∀ {J : Type u} [Category.{u} J], (J ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      → Prop)
    (h07SU : ∀ Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B _ hZ Y →
      IsQuasiCompactSpace B _ hZ Y → IsAbsolutelyQuasiSeparated B _ hZ hZ Y →
      ∃ A : NoetherianApproximation B _ hZ hZ Y, letI := A.preorder; Conv A.diagram)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h07SK : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), Conv D →
      (∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) →
      (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      (∀ j, IsQuasiCompactSpace B _ hZ (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj j)) →
      ∀ Y : Over (limit D), IsAlgebraicSpace B _ hZ Y.left → IsFinitePresentation B _ hZ Y.hom →
        ∃ (j : J) (Yⱼ : Over (D.obj j)), IsAlgebraicSpace B _ hZ Yⱼ.left ∧
          IsFinitePresentation B _ hZ Yⱼ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D j)).obj Yⱼ))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), Conv D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    (h0CP9 : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : NoetherianLimitSystem B _ hZ hZ I), Conv D.system →
      ∀ {X : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} {f : X ⟶ D.limitCone.pt} (G :
        GoodDiagram B _ hZ hZ D f),
        IsAlgebraicSpace B _ hZ X → Nonempty (IsLimit (GoodDiagram.imageCone G)))
    (hTail : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (i₁ : I),
      Conv D → Conv' ((tailInclusion i₁).op ⋙ D))
    (hImage : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : NoetherianLimitSystem B _ hZ hZ I) {X : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)}
        {f : X ⟶ D.limitCone.pt}
      (G : GoodDiagram B _ hZ hZ D f), Conv D.system →
        Conv' (tailOver G.index ⋙ GoodDiagram.imageSystem G))
    {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (hX : IsAlgebraicSpace B _ hZ X) (hY :
      IsAlgebraicSpace B _ hZ Y)
    (f : X ⟶ Y) (hf : IsProper B _ hZ f) (hYqc : IsQuasiCompactSpace B _ hZ Y)
    (hYqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (eX : DX.limitCone.pt ≅ X) (eY : DY.limitCone.pt ≅ Y),
      (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
        eX.hom ≫ f ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
      (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
      (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
      Conv' DX.system ∧ Conv' DY.system := by
  -- Stacks 07SU, with the convention.
  obtain ⟨A, hA⟩ := h07SU Y hY hYqc hYqs
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  set D := A.diagram
  have hDZ := fun j => isFinitePresentation_terminal_of_isFiniteType_viewOverIntegers
    (A.isAlgebraicSpace j) (A.isAbsolutelyQuasiSeparated j) (A.isFiniteTypeOverIntegers j)
  have hDqc : ∀ j, IsQuasiCompactSpace B _ hZ (D.obj j) := fun j => (hDZ j).2.1
  let eL : Y ≅ limit D := A.isLimit.conePointUniqueUpToIso (limit.isLimit D)
  have hlim : IsAlgebraicSpace B _ hZ (limit D) := isAlgebraicSpace_of_iso B _ hZ eL hY
  -- Stacks 0A0W: a closed immersion into a proper space of finite presentation over `Y`.
  obtain ⟨K, _, _, ⟨k⟩, DK, t, π, hDK, ht, -, hπ, hπt, -⟩ := h0A0W hX hY f hf hYqc hYqs
  set p := t.app (op k)
  have hιp : π.app (op k) ≫ p = f := by
    have h := NatTrans.congr_app hπt (op k)
    rwa [NatTrans.comp_app, Functor.const_map_app] at h
  -- Stacks 07SK: a model of `X' ⟶ Y` at a stage.
  obtain ⟨⟨j₀⟩, W₀, hW₀, hW₀fp, ⟨e₀⟩⟩ := h07SK D hA A.isAlgebraicSpace
    A.isAffineHom_map hDqc A.isAbsolutelyQuasiSeparated (Over.mk (p ≫ eL.hom))
    (hDK _) (isFinitePresentation_of_arrowIso B _ hZ p (p ≫ eL.hom) (𝟙 _) eL.hom
      (by simp) (ht _).2)
  -- Stacks 08K1: the model is proper at a later stage.
  obtain ⟨i₁, hi₁, hprop⟩ := h08K1 D hA (fun i => A.isAlgebraicSpace _)
    A.isAffineHom_map hlim j₀ W₀.hom (𝟙 _) W₀.hom (Category.comp_id _) hW₀
    (A.isAlgebraicSpace _) (hDqc _) (A.isAbsolutelyQuasiSeparated _)
    (isQuasiCompactSpace_of_isFinitePresentation B _ hZ W₀.hom (A.isAlgebraicSpace _) (hDqc _)
      hW₀fp)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ hW₀
      (A.isAbsolutelyQuasiSeparated _) hW₀fp.2.2) (hDqc _) (A.isAbsolutelyQuasiSeparated _)
    ((isProper_pullback_map_id_iff hZ hlim (A.isAlgebraicSpace _) hW₀ _ _).2
      (isProper_pullback_fst_of_iso_overPullback hZ eL e₀ (ht _).1))
    (isFiniteType_of_isFinitePresentation B _ hZ hW₀fp).1
  set e : op i₁ ⟶ op j₀ := (homOfLE hi₁).op
  have hWalg : IsAlgebraicSpace B _ hZ (pullback (D.map e) W₀.hom) :=
    isAlgebraicSpace_pullback B _ hZ _ _ (A.isAlgebraicSpace _) hW₀ (A.isAlgebraicSpace _)
  have hmodel : IsProper B _ hZ (pullback.fst (D.map e) W₀.hom) :=
    (isProper_pullback_map_id_iff hZ (A.isAlgebraicSpace _) (A.isAlgebraicSpace _) hW₀ _ _).1
      hprop
  have hWqs : IsAbsolutelyQuasiSeparated B _ hZ hZ (pullback (D.map e) W₀.hom) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ hWalg
      (A.isAbsolutelyQuasiSeparated _) (isQuasiSeparated_of_isSeparated B _ hZ hmodel.1)
  let N : NoetherianLimitSystem B _ hZ hZ A.I :=
    { system := D
      system_isAlgebraicSpace := fun i => A.isAlgebraicSpace _
      noetherian := fun i => ⟨hDqc _, A.isAbsolutelyQuasiSeparated _, (hDZ _).2.2⟩
      transition_affine := A.isAffineHom_map
      limitCone := Cone.mk Y A.π
      isLimit := A.isLimit
      limit_isAlgebraicSpace := hY }
  -- The good diagram `X ⟶ W ⟶ Y_{i₁}` of Stacks 0CP8.
  let G : GoodDiagram B _ hZ hZ N f := GoodDiagram.ofIsPullback (hπ _) hιp hi₁
    (isPullback_of_iso_overPullback hZ
      (A.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit D) _) e₀) hWalg hmodel.2.1
  -- Stacks 0CP9.
  obtain ⟨hGlim⟩ := h0CP9 N hA G hX
  have := isDirected_tail i₁
  refine ⟨{j : A.I // i₁ ≤ j}, inferInstance, inferInstance, G.tailDescentSituation hX hWqs hGlim,
    N.tailDescentSituation i₁, G.tailDescentHom hX hWqs hGlim, Iso.refl _, Iso.refl _,
    G.tailDescentSituation_π_app_comp_tailDescentHom_app hX hWqs hGlim,
    fun i => ⟨G.isProper_tailDescentHom_app hX hWqs hGlim hmodel i,
      G.isFinitePresentation_tailDescentHom_app hX hWqs hGlim hmodel i⟩,
    fun i => (hDZ (op i.1)).1, hImage N G hA, hTail D i₁ hA⟩

/-- **Stacks 0A0X, as a morphism of descent situations, from the approximations it is proved
with.** Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `ℤ` with `Y`
quasi-compact and quasi-separated. Then `f` is the limit of a morphism `φ` of directed inverse
systems of quasi-compact quasi-separated algebraic spaces with affine transition morphisms, each
`φ_i` proper and of finite presentation and each stage of the target of finite presentation over
`ℤ`; moreover the two systems have the properties `Conv'` granted by `hTail` and `hImage`.

The inputs are the results the proof cites which this development has only for systems indexed
by a set below the cofinality of the site's cutoff, each with that bound replaced by the
standing convention of Section 70.2 (tag 07SD), read as an abstract property `Conv`:

* `hW`: the W-systems of the proof of Stacks 07SU, so that
  `AlgebraicGeometry.Space.hasNoetherianApproximation_of_hasWSystems` is Stacks 07SU, and
  `hconv`: the approximation may be chosen satisfying `Conv`;
* `h0A0W`: Stacks 0A0W, in its registered form;
* `h07SK`: Stacks 07SK, essential surjectivity
  (`AlgebraicGeometry.Space.exists_model_of_finitePresentation` with `Conv` for the bound);
* `h08K1`: Stacks 08K1;
* `h0CP9`: Stacks 0CP9 (`AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone` with `Conv` for
  the bound).

The systems produced are a tail of the approximation of `Y` and the system of scheme-theoretic
images over that tail; `hTail` and `hImage` say what is known of `Conv'` for such systems. -/
theorem exists_descentSituation_arrow_of_approximations
    (Conv : ∀ {J : Type u} [Category.{u} J], (J ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      → Prop)
    (Conv' : ∀ {J : Type u} [Category.{u} J], (J ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      → Prop)
    (hW : ElementaryChart.HasWSystems B hZ)
    (hconv : ∀ Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B _ hZ Y →
      IsQuasiCompactSpace B _ hZ Y →
      IsAbsolutelyQuasiSeparated B _ hZ hZ Y → HasNoetherianApproximation B _ hZ hZ Y →
      ∃ A : NoetherianApproximation B _ hZ hZ Y, letI := A.preorder; Conv A.diagram)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h07SK : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), Conv D →
      (∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) →
      (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      (∀ j, IsQuasiCompactSpace B _ hZ (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj j)) →
      ∀ Y : Over (limit D), IsAlgebraicSpace B _ hZ Y.left → IsFinitePresentation B _ hZ Y.hom →
        ∃ (j : J) (Yⱼ : Over (D.obj j)), IsAlgebraicSpace B _ hZ Yⱼ.left ∧
          IsFinitePresentation B _ hZ Yⱼ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D j)).obj Yⱼ))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), Conv D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    (h0CP9 : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : NoetherianLimitSystem B _ hZ hZ I), Conv D.system →
      ∀ {X : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} {f : X ⟶ D.limitCone.pt} (G :
        GoodDiagram B _ hZ hZ D f),
        IsAlgebraicSpace B _ hZ X → Nonempty (IsLimit (GoodDiagram.imageCone G)))
    (hTail : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (i₁ : I),
      Conv D → Conv' ((tailInclusion i₁).op ⋙ D))
    (hImage : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : NoetherianLimitSystem B _ hZ hZ I) {X : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)}
        {f : X ⟶ D.limitCone.pt}
      (G : GoodDiagram B _ hZ hZ D f), Conv D.system →
        Conv' (tailOver G.index ⋙ GoodDiagram.imageSystem G))
    {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (hX : IsAlgebraicSpace B _ hZ X) (hY :
      IsAlgebraicSpace B _ hZ Y)
    (f : X ⟶ Y) (hf : IsProper B _ hZ f) (hYqc : IsQuasiCompactSpace B _ hZ Y)
    (hYqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (eX : DX.limitCone.pt ≅ X) (eY : DY.limitCone.pt ≅ Y),
      (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
        eX.hom ≫ f ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
      (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
      (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
      Conv' DX.system ∧ Conv' DY.system :=
  exists_descentSituation_arrow_of_convNoetherianApproximation hZ Conv Conv'
    (fun Y hY hYqc hYqs => hconv Y hY hYqc hYqs
      (hasNoetherianApproximation_of_hasWSystems hW Y hY hYqc hYqs))
    h0A0W h07SK h08K1 h0CP9 hTail hImage hX hY f hf hYqc hYqs

/-- **Stacks 0A0X, from the approximations it is proved with.** Let `f : X ⟶ Y` be a proper
morphism of algebraic spaces over `ℤ` with `Y` quasi-compact and quasi-separated. Then there is a
directed set `I` and an inverse system `(f_i : X_i ⟶ Y_i)` of morphisms of algebraic spaces over
`I` — the morphism `φ` between the two systems of `DX` and `DY` — whose transition morphisms
`X_i ⟶ X_{i'}` and `Y_i ⟶ Y_{i'}` are affine, with `f_i` proper and of finite presentation and
`Y_i` of finite presentation over `ℤ`, such that `(X ⟶ Y) = lim (X_i ⟶ Y_i)`: `X` and `Y` are
the limits of the two systems (`eX`, `eY`) and `f` is the limit of the `f_i`.

The hypotheses beyond the source's are the inputs of
`AlgebraicGeometry.Space.exists_descentSituation_arrow_of_approximations`: Stacks 07SU (`hW`, and
`hconv` for the convention on its approximation), Stacks 0A0W (`h0A0W`), and Stacks 07SK, 08K1
and 0CP9 under the convention of Section 70.2 read as `Conv` (`h07SK`, `h08K1`, `h0CP9`). There
is no bound on the index set. -/
theorem exists_isLimit_isProper_isFinitePresentation_arrow_of_approximations
    (Conv : ∀ {J : Type u} [Category.{u} J], (J ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      → Prop)
    (hW : ElementaryChart.HasWSystems B hZ)
    (hconv : ∀ Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B _ hZ Y →
      IsQuasiCompactSpace B _ hZ Y →
      IsAbsolutelyQuasiSeparated B _ hZ hZ Y → HasNoetherianApproximation B _ hZ hZ Y →
      ∃ A : NoetherianApproximation B _ hZ hZ Y, letI := A.preorder; Conv A.diagram)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h07SK : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), Conv D →
      (∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) →
      (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      (∀ j, IsQuasiCompactSpace B _ hZ (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj j)) →
      ∀ Y : Over (limit D), IsAlgebraicSpace B _ hZ Y.left → IsFinitePresentation B _ hZ Y.hom →
        ∃ (j : J) (Yⱼ : Over (D.obj j)), IsAlgebraicSpace B _ hZ Yⱼ.left ∧
          IsFinitePresentation B _ hZ Yⱼ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D j)).obj Yⱼ))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), Conv D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    (h0CP9 : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : NoetherianLimitSystem B _ hZ hZ I), Conv D.system →
      ∀ {X : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} {f : X ⟶ D.limitCone.pt} (G :
        GoodDiagram B _ hZ hZ D f),
        IsAlgebraicSpace B _ hZ X → Nonempty (IsLimit (GoodDiagram.imageCone G)))
    {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (hX : IsAlgebraicSpace B _ hZ X) (hY :
      IsAlgebraicSpace B _ hZ Y)
    (f : X ⟶ Y) (hf : IsProper B _ hZ f) (hYqc : IsQuasiCompactSpace B _ hZ Y)
    (hYqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (eX : DX.limitCone.pt ≅ X) (eY : DY.limitCone.pt ≅ Y),
      (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
        eX.hom ≫ f ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
      (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
      (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) := by
  obtain ⟨I, _, _, DX, DY, φ, eX, eY, h₁, h₂, h₃, -, -⟩ :=
    exists_descentSituation_arrow_of_approximations hZ Conv (fun _ => True) hW hconv h0A0W h07SK
      h08K1 h0CP9 (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial) hX hY f hf hYqc hYqs
  exact ⟨I, inferInstance, inferInstance, DX, DY, φ, eX, eY, h₁, h₂, h₃⟩

/-- **Stacks 0A0X over an affine target, in the shape the assembly of Stacks 0D3D consumes.** For
an affine object `U` of the site of `Spec ℤ` and a proper morphism `f' : X' ⟶ h_U`, `f'` is the
  limit
of a morphism `φ` of descent situations with `φ_i` proper and of finite presentation and the stages
of the target of finite presentation over `ℤ`, and both systems satisfy the convention `Conv`. This
is exactly the hypothesis `h0A0X` of
`AlgebraicGeometry.Space.ampleSpreadsFromResidueFieldsToOpens_of_approximation`.

The inputs are those of
`AlgebraicGeometry.Space.exists_isLimit_isProper_isFinitePresentation_arrow_of_approximations`,
and two consequences of the convention for the systems the proof produces: that it passes to a
tail of a system (`hTail`) and to the system of scheme-theoretic images of Stacks 0CP9 over a tail
(`hImage`). -/
theorem exists_descentSituation_arrow_conv_of_approximations
    (Conv : ∀ {J : Type u} [Category.{u} J], (J ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      → Prop)
    (hW : ElementaryChart.HasWSystems B hZ)
    (hconv : ∀ Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B _ hZ Y →
      IsQuasiCompactSpace B _ hZ Y →
      IsAbsolutelyQuasiSeparated B _ hZ hZ Y → HasNoetherianApproximation B _ hZ hZ Y →
      ∃ A : NoetherianApproximation B _ hZ hZ Y, letI := A.preorder; Conv A.diagram)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h07SK : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), Conv D →
      (∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) →
      (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      (∀ j, IsQuasiCompactSpace B _ hZ (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj j)) →
      ∀ Y : Over (limit D), IsAlgebraicSpace B _ hZ Y.left → IsFinitePresentation B _ hZ Y.hom →
        ∃ (j : J) (Yⱼ : Over (D.obj j)), IsAlgebraicSpace B _ hZ Yⱼ.left ∧
          IsFinitePresentation B _ hZ Yⱼ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D j)).obj Yⱼ))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), Conv D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    (h0CP9 : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : NoetherianLimitSystem B _ hZ hZ I), Conv D.system →
      ∀ {X : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} {f : X ⟶ D.limitCone.pt} (G :
        GoodDiagram B _ hZ hZ D f),
        IsAlgebraicSpace B _ hZ X → Nonempty (IsLimit (GoodDiagram.imageCone G)))
    (hTail : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (i₁ : I),
      Conv D → Conv ((tailInclusion i₁).op ⋙ D))
    (hImage : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : NoetherianLimitSystem B _ hZ hZ I) {X : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)}
        {f : X ⟶ D.limitCone.pt}
      (G : GoodDiagram B _ hZ hZ D f), Conv D.system →
        Conv (tailOver G.index ⋙ GoodDiagram.imageSystem G)) :
    ∀ (U : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj U) →
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (f' : X' ⟶ representedAlgebraicSpace B _ hZ U), IsProper B _ hZ f'.hom →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
        (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
        (eX : DX.limitCone.pt ≅ X'.1) (eY : DY.limitCone.pt ≅ yoneda.obj U),
        (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
          eX.hom ≫ f'.hom ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
        (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
        (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
        Conv DX.system ∧ Conv DY.system := fun U hU X' f' hf' =>
  exists_descentSituation_arrow_of_approximations hZ Conv Conv hW hconv h0A0W h07SK h08K1
    h0CP9 hTail hImage X'.2 (isAlgebraicSpace_yoneda B _ hZ U) f'.hom hf'
    (isQuasiCompactSpace_yoneda_of_isAffine B _ hZ U hU)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B _ hZ (yoneda.obj U) hZ
      ⟨U, inferInstance, ⟨Functor.RepresentableBy.yoneda U⟩⟩)

end Assembly

end AlgebraicGeometry.Space

end
