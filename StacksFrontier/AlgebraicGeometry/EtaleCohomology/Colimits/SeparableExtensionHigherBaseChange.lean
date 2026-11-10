module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackPresentationIsoLeg
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimitTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystemPresentation
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting
public import Mathlib.RingTheory.Etale.Field

/-!
# Higher direct images commute with base change to a separable algebraic extension

Let `K/k` be a separable algebraic field extension, `X` a scheme over `k` and `j : T ⟶ X` a
quasi-compact quasi-separated morphism. Base change to `K` gives a cartesian square
`X_K ⟵ T_K` over `X ⟵ T`, and the base change map
`(X_K ⟶ X)⁻¹ R^q j_* F ⟶ R^q j_{K,*} (T_K ⟶ T)⁻¹ F` is an isomorphism for every abelian sheaf
`F` on `T_étale` and every `q`.

`X_K` is the limit of the base changes `X_A` to the finitely generated `k`-subalgebras `A ⊆ K`
(`AlgebraicGeometry.FieldExtensionDescent.baseChangeLimitCone`), each of which is a finite
separable extension field of `k`, so that every `X_A ⟶ X` and every transition morphism is
étale. By [Stacks, Tag 0EYM] the sheaf `R^q j_{K,*}` of the inverse image of `F` is the colimit of
the inverse images of the `R^q j_{A,*}` of the inverse images of `F`; the transition maps of this
system are base change maps of étale squares, hence isomorphisms, so the leg at `A = k` is an
isomorphism (`Stacks.EtaleCohomology.LimitHigherDirectImage.isIso_leg_of_isIso_map`). Pasting with
the étale square at `A = k` gives the claim ([Stacks, Tag 0EZS]).

## Main results

* `Stacks.EtaleCohomology.SeparableBaseChange.isIso_higherBaseChangeMapAb`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.FieldExtensionDescent

universe u

namespace Stacks.EtaleCohomology.SeparableBaseChange

-- Hom types must resolve `Quiver Scheme` as the stage diagrams of `FieldExtensionDescent` do,
-- through the category structure, or the kernel has to unfold the two paths against each other.
attribute [-instance] CategoryTheory.catToReflQuiver

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]

/-- A finitely generated subalgebra of a separable algebraic extension is étale over `k`. -/
theorem etale_fgSubalgebra (i : FGSubalgebra k K) :
    Algebra.Etale k (i : Subalgebra k K) := by
  have hfield : IsField (i : Subalgebra k K) :=
    Subalgebra.isField_of_algebraic _
  let : Field (i : Subalgebra k K) := hfield.toField
  have : Algebra.IsSeparable k (i : Subalgebra k K) :=
    Algebra.IsSeparable.of_algHom k K (Subalgebra.val (i : Subalgebra k K))
  have : Algebra.FormallyEtale k (i : Subalgebra k K) := Algebra.FormallyEtale.of_isSeparable k _
  have : Algebra.FinitePresentation k (i : Subalgebra k K) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- The structure morphism `Spec A ⟶ Spec k` of a stage is étale. -/
instance etale_specDiagram_hom (i : (FGSubalgebra k K)ᵒᵖ) :
    Etale ((specDiagram k K).obj i).hom := by
  have := etale_fgSubalgebra k K i.unop
  change Etale (Spec.map (CommRingCat.ofHom (algebraMap k (i.unop : Subalgebra k K))))
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.2 inferInstance

section Square

variable {k} {X T S' : Scheme.{u}} (πX : X ⟶ Spec (.of k)) (j : T ⟶ X)

/-- The base change `T ×_k S' ⟶ X ×_k S'` of `j` along `S' ⟶ Spec k`. -/
abbrev baseChangeMap (s : S' ⟶ Spec (.of k)) : pullback s (j ≫ πX) ⟶ pullback s πX :=
  pullback.map s (j ≫ πX) s πX (𝟙 _) j (𝟙 _) (by simp) (by simp)

/-- **The base change of `j` along `S' ⟶ Spec k` is a base change along `X ×_k S' ⟶ X`.** -/
theorem isPullback_baseChangeMap (s : S' ⟶ Spec (.of k)) :
    IsPullback (baseChangeMap πX j s) (pullback.snd s (j ≫ πX)) (pullback.snd s πX) j := by
  refine IsPullback.of_right (h₁₂ := pullback.fst s πX) (v₁₃ := s) (h₂₂ := πX) ?_
    (by simp) (IsPullback.of_hasPullback s πX)
  simpa using IsPullback.of_hasPullback s (j ≫ πX)

/-- The base change of `j` along `S' ⟶ Spec k`, followed by the projection to `X`, is the
projection to `T` followed by `j`. -/
theorem baseChangeMap_snd {S' : Scheme.{u}} (s : S' ⟶ Spec (.of k)) :
    baseChangeMap πX j s ≫ pullback.snd s πX = pullback.snd s (j ≫ πX) ≫ j :=
  pullback.lift_snd _ _ _

end Square

/-- Invertibility of a base change map does not depend on how its upper horizontal morphism is
named. -/
theorem isIso_higherBaseChangeMapAb_app_congr_h {X' Y S T : Scheme.{u}} (f' : X' ⟶ S)
    (g : T ⟶ S) {h h' : Y ⟶ X'} (e : Y ⟶ T) (hh : h = h') (w : h ≫ f' = e ≫ g)
    (w' : h' ≫ f' = e ≫ g) (q : ℕ) (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f' g h e w q).app G) ↔
      IsIso ((higherBaseChangeMapAb f' g h' e w' q).app G) := by
  subst hh
  rfl

section System

variable {X T : Scheme.{u}} (πX : X ⟶ Spec (.of k)) (j : T ⟶ X)

local notation "𝔇" => FieldExtensionDescent.baseChangeDiagram k K

/-- The projection `X_A ⟶ X` of a stage. -/
def stageSnd {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) (i : (FGSubalgebra k K)ᵒᵖ) :
    (𝔇 π).obj i ⟶ Y :=
  pullback.snd ((specDiagram k K).obj i).hom π

/-- The projection `X_A ⟶ Spec A` of a stage. -/
def stageFst {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) (i : (FGSubalgebra k K)ᵒᵖ) :
    (𝔇 π).obj i ⟶ ((specDiagram k K).obj i).left :=
  pullback.fst ((specDiagram k K).obj i).hom π

omit [Algebra.IsSeparable k K] in
/-- The stage `X_A` is the fibre product of `Spec A ⟶ Spec k` and `Y ⟶ Spec k`. -/
theorem isPullback_stage {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) (i : (FGSubalgebra k K)ᵒᵖ) :
    IsPullback (stageFst k K π i) (stageSnd k K π i) ((specDiagram k K).obj i).hom π :=
  IsPullback.of_hasPullback _ _

omit [Algebra.IsSeparable k K] in
/-- The transition morphisms of the stages commute with the projections to `Y`. -/
@[reassoc]
theorem map_stageSnd {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) {i i' : (FGSubalgebra k K)ᵒᵖ}
    (a : i ⟶ i') : (𝔇 π).map a ≫ stageSnd k K π i' = stageSnd k K π i :=
  Over.w ((Over.pullback π).map ((specDiagram k K).map a))

omit [Algebra.IsSeparable k K] in
/-- The transition morphisms of the stages commute with the projections to the `Spec A`. -/
@[reassoc]
theorem map_stageFst {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) {i i' : (FGSubalgebra k K)ᵒᵖ}
    (a : i ⟶ i') : (𝔇 π).map a ≫ stageFst k K π i' =
      stageFst k K π i ≫ ((specDiagram k K).map a).left := by
  simp only [FieldExtensionDescent.baseChangeDiagram, Functor.comp_map, Over.forget_map,
    Over.pullback_map_left, stageFst]
  exact pullback.lift_fst _ _ _

/-- The morphism of inverse systems `T_A ⟶ X_A` induced by `j`. -/
def stageMap : 𝔇 (j ≫ πX) ⟶ 𝔇 πX where
  app i := (isPullback_stage k K πX i).lift (stageFst k K (j ≫ πX) i)
    (stageSnd k K (j ≫ πX) i ≫ j) (by simpa using (isPullback_stage k K (j ≫ πX) i).w)
  naturality i i' a := by
    refine (isPullback_stage k K πX i').hom_ext ?_ ?_
    · simp only [Category.assoc, IsPullback.lift_fst, map_stageFst, IsPullback.lift_fst_assoc]
    · simp only [Category.assoc, IsPullback.lift_snd, map_stageSnd, map_stageSnd_assoc]

omit [Algebra.IsSeparable k K] in
/-- The morphism `T_A ⟶ X_A` commutes with the projections to `Spec A`. -/
theorem stageMap_fst (i : (FGSubalgebra k K)ᵒᵖ) :
    (stageMap k K πX j).app i ≫ stageFst k K πX i = stageFst k K (j ≫ πX) i :=
  IsPullback.lift_fst _ _ _ _

omit [Algebra.IsSeparable k K] in
/-- The morphism `T_A ⟶ X_A` followed by `X_A ⟶ X` is `T_A ⟶ T` followed by `j`. -/
theorem stageMap_snd (i : (FGSubalgebra k K)ᵒᵖ) :
    (stageMap k K πX j).app i ≫ stageSnd k K πX i = stageSnd k K (j ≫ πX) i ≫ j :=
  IsPullback.lift_snd _ _ _ _

omit [Algebra.IsSeparable k K] in
/-- **A stage of `j` is a base change of `j`.** -/
theorem isPullback_stageMap (i : (FGSubalgebra k K)ᵒᵖ) :
    IsPullback ((stageMap k K πX j).app i) (stageSnd k K (j ≫ πX) i) (stageSnd k K πX i) j := by
  refine IsPullback.of_right (h₁₂ := stageFst k K πX i) (v₁₃ := ((specDiagram k K).obj i).hom)
    (h₂₂ := πX) ?_ (stageMap_snd k K πX j i) (isPullback_stage k K πX i)
  rw [stageMap_fst]
  exact isPullback_stage k K (j ≫ πX) i

omit [Algebra.IsSeparable k K] in
/-- For a transition `A ⊆ A'`, the square formed by `T_{A'} ⟶ X_{A'}`, `T_A ⟶ X_A` and the
transition morphisms is cartesian. -/
theorem isPullback_stageMap_transition {i i' : (FGSubalgebra k K)ᵒᵖ} (a : i ⟶ i') :
    IsPullback ((stageMap k K πX j).app i) ((𝔇 (j ≫ πX)).map a) ((𝔇 πX).map a)
      ((stageMap k K πX j).app i') := by
  refine IsPullback.of_bot (v₂₁ := stageSnd k K (j ≫ πX) i') (v₂₂ := stageSnd k K πX i')
    (h₃₁ := j) ?_ ((stageMap k K πX j).naturality a).symm (isPullback_stageMap k K πX j i')
  rw [map_stageSnd, map_stageSnd]
  exact isPullback_stageMap k K πX j i

/-- Each stage `X_A ⟶ X` is étale. -/
instance etale_stageSnd {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) (i : (FGSubalgebra k K)ᵒᵖ) :
    Etale (stageSnd k K π i) :=
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale) π :=
    ⟨fun sq H => MorphismProperty.of_isPullback (P := @Etale) sq H⟩
  MorphismProperty.pullback_snd _ _ (etale_specDiagram_hom k K i)

/-- Each transition morphism `X_{A'} ⟶ X_A` of the stages is étale. -/
instance etale_baseChangeDiagram_map {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k))
    {i i' : (FGSubalgebra k K)ᵒᵖ} (a : i ⟶ i') : Etale ((𝔇 π).map a) := by
  have : Etale ((𝔇 π).map a ≫ stageSnd k K π i') := by
    rw [map_stageSnd]
    infer_instance
  exact Etale.of_comp _ (stageSnd k K π i')

end System

section Generic

/-- The transition maps of the system of inverse images of one sheaf are invertible. -/
theorem isIso_ofCocone_map {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {S : Scheme.{u}}
    (ι : ∀ i, D.obj i ⟶ S) (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    IsIso ((EtaleSheafSystem.ofCocone ι hι G).map a) :=
  ((smallEtalePullbackAbComp' (D.map a) (ι j) (ι i) (hι a).symm).app G).isIso_hom

/-- A transition map of [Stacks, Tag 0EYM] at an étale cartesian transition square, for a system
whose own transition map is invertible, is invertible. -/
theorem isIso_transitionMap_of_etale {I : Type u} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
    (γ : DX ⟶ DS) (F : EtaleSheafSystem DX Ab.{u + 1}) (q : ℕ) {i i' : Iᵒᵖ} (a : i ⟶ i')
    (sq : IsPullback (γ.app i) (DX.map a) (DS.map a) (γ.app i')) [Etale (DS.map a)]
    [IsIso (F.map a)] : IsIso (LimitHigherDirectImage.transitionMap γ q F a) := by
  have := SmoothBaseChange.isIso_higherBaseChangeMapAb_of_etale
    SmoothBaseChange.etaleLocalHigherBaseChange (DS.map a) (γ.app i) (DX.map a) (γ.app i') sq
    (F.obj i') q
  dsimp only [LimitHigherDirectImage.transitionMap]
  infer_instance

/-- **Base change along the limit of an inverse system of étale squares.** Let `γ_i : T_i ⟶ X_i`
be an inverse system of quasi-compact quasi-separated morphisms with affine transition morphisms
over a directed set with a least element `i₀`, with limit `γ : T_∞ ⟶ X_∞`, and let `j : T ⟶ X`
receive cartesian squares from the `γ_i` along étale morphisms `X_i ⟶ X`, compatibly with the
transitions, which are étale with cartesian squares. Then the base change map of the limit square
is an isomorphism in every degree. -/
theorem isIso_higherBaseChangeMapAb_of_etale_system {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] {DT DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DT ⟶ DS)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
    [∀ i, QuasiSeparated (γ.app i)] {cT : Cone DT} (hcT : IsLimit cT) {cS : Cone DS}
    (hcS : IsLimit cS) {X T : Scheme.{u}} (j : T ⟶ X) (ιS : ∀ i, DS.obj i ⟶ X)
    (ιT : ∀ i, DT.obj i ⟶ T) (hιT : ∀ {i i' : Iᵒᵖ} (a : i ⟶ i'), DT.map a ≫ ιT i' = ιT i)
    (fS : cS.pt ⟶ X) (hfS : ∀ i, CategoryStruct.comp (X := cS.pt) (cS.π.app i) (ιS i) = fS)
    (eT : cT.pt ⟶ T) (heT : ∀ i, CategoryStruct.comp (X := cT.pt) (cT.π.app i) (ιT i) = eT)
    (sqi : ∀ i, IsPullback (γ.app i) (ιT i) (ιS i) j)
    (sqa : ∀ {i i' : Iᵒᵖ} (a : i ⟶ i'), IsPullback (γ.app i) (DT.map a) (DS.map a) (γ.app i'))
    [∀ {i i' : Iᵒᵖ} (a : i ⟶ i'), Etale (DS.map a)] [∀ i, Etale (ιS i)] (i₀ : I)
    (hi₀ : ∀ i : I, i₀ ≤ i)
    (w : LimitHigherDirectImage.limitMorphism γ cT cS hcS ≫ fS = eT ≫ j)
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) :
    IsIso ((higherBaseChangeMapAb fS j (LimitHigherDirectImage.limitMorphism γ cT cS hcS) eT w
      q).app G) := by
  let F := EtaleSheafSystem.ofCocone ιT hιT G
  let 𝓕 := (smallEtalePullbackAb eT).obj G
  let legs := EtaleSheafSystem.ofCoconeLeg ιT hιT cT eT heT G
  obtain ⟨-, hcone, hcolim⟩ := LimitHigherDirectImage.higherDirectImageColimit γ hcT hcS q F 𝓕
    legs (EtaleSheafSystem.isPullbackCocone_ofCocone ιT hιT cT eT heT G)
    (EtaleSheafSystem.isPullbackColimitPresentation_ofCocone ιT hιT cT eT heT G)
  have hleg := LimitHigherDirectImage.isIso_leg_of_isIso_map cS
    (LimitHigherDirectImage.higherDirectImageSystem γ q F)
    (LimitHigherDirectImage.projectionMap γ cT cS hcS q 𝓕 F legs)
    (fun a => (Category.assoc _ _ _).trans (hcone a)) hcolim
    (fun a => have := isIso_ofCocone_map ιT hιT G a
      isIso_transitionMap_of_etale γ F q a (sqa a))
    i₀ hi₀
  have hb₂ : IsIso ((higherBaseChangeMapAb (cS.π.app (Opposite.op i₀)) (γ.app (Opposite.op i₀))
      (LimitHigherDirectImage.limitMorphism γ cT cS hcS) (cT.π.app (Opposite.op i₀))
      (LimitHigherDirectImage.limitMorphism_comp_π γ cT cS hcS (Opposite.op i₀)) q).app
        (F.obj (Opposite.op i₀))) := by
    have : IsIso (legs (Opposite.op i₀)) :=
      ((smallEtalePullbackAbComp' (cT.π.app (Opposite.op i₀)) (ιT (Opposite.op i₀)) eT
        (heT (Opposite.op i₀)).symm).app G).isIso_hom
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (((smallEtalePushforwardAb
      (LimitHigherDirectImage.limitMorphism γ cT cS hcS)).rightDerived q).map
        (legs (Opposite.op i₀))) _ hleg
  have hF : F.obj (Opposite.op i₀) = (smallEtalePullbackAb (ιT (Opposite.op i₀))).obj G := rfl
  rw [hF] at hb₂
  have hb₁ := SmoothBaseChange.isIso_higherBaseChangeMapAb_of_etale
    SmoothBaseChange.etaleLocalHigherBaseChange (ιS (Opposite.op i₀)) (γ.app (Opposite.op i₀))
    (ιT (Opposite.op i₀)) j (sqi (Opposite.op i₀)) G q
  have hrect := isIso_higherBaseChangeMapAb_app_of_paste (X₂ := cT.pt) (S₂ := cS.pt)
    j (γ.app (Opposite.op i₀))
    (LimitHigherDirectImage.limitMorphism γ cT cS hcS) (ιS (Opposite.op i₀))
    (cS.π.app (Opposite.op i₀)) (ιT (Opposite.op i₀)) (cT.π.app (Opposite.op i₀))
    (sqi (Opposite.op i₀)).w
    (LimitHigherDirectImage.limitMorphism_comp_π γ cT cS hcS (Opposite.op i₀)) q G hb₁ hb₂
  exact (isIso_higherBaseChangeMapAb_app_congr j _ (hfS _) (heT _) _ w q G).1 hrect

end Generic

section Main

variable {X T : Scheme.{u}} (πX : X ⟶ Spec (.of k)) (j : T ⟶ X)

local notation "𝔇" => FieldExtensionDescent.baseChangeDiagram k K
local notation "𝔏" => FieldExtensionDescent.baseChangeLimitCone k K

omit [Algebra.IsSeparable k K] in
/-- The projections of the limit `X_K` to the stages lie over `X`. -/
theorem cone_π_stageSnd {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) (i : (FGSubalgebra k K)ᵒᵖ) :
    (𝔏 π).cone.π.app i ≫ stageSnd k K π i =
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) π :
        (𝔏 π).cone.pt ⟶ Y) :=
  Over.w (((Over.pullback π).mapCone (specLimitCone k K).cone).π.app i)

omit [Algebra.IsSeparable k K] in
/-- The limit of the stages of `j` is the base change of `j` to `K`. -/
theorem limitMorphism_stageMap :
    LimitHigherDirectImage.limitMorphism (stageMap k K πX j) (𝔏 (j ≫ πX)).cone (𝔏 πX).cone
        (𝔏 πX).isLimit =
      baseChangeMap πX j (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  refine (𝔏 πX).isLimit.hom_ext fun i => ?_
  rw [LimitHigherDirectImage.limitMorphism_comp_π]
  have e : ∀ {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)), (𝔏 π).cone.π.app i ≫ stageFst k K π i =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) π ≫
        ((specLimitCone k K).cone.π.app i).left := fun π => by
    change ((Over.pullback π).map ((specLimitCone k K).cone.π.app i)).left ≫
      pullback.fst ((specDiagram k K).obj i).hom π = _
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  refine (isPullback_stage k K πX i).hom_ext ?_ ?_
  · have eX := e πX
    have eT := e (j ≫ πX)
    have e1 : baseChangeMap πX j (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) πX =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) (j ≫ πX) := by simp
    refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
    refine ((congrArg _ (stageMap_fst k K πX j i)).trans ?_).trans (congrArg _ eX).symm
    refine eT.trans ?_
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e1)).symm
  · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
    refine ((congrArg _ (stageMap_snd k K πX j i)).trans ?_).trans
      (congrArg _ (cone_π_stageSnd k K πX i)).symm
    refine ((Category.assoc _ _ _).symm.trans ?_).trans (baseChangeMap_snd πX j _).symm
    exact congrArg (· ≫ j) (cone_π_stageSnd k K (j ≫ πX) i)

variable [QuasiCompact j] [QuasiSeparated j]

/-- Each stage `T_A ⟶ X_A` of a quasi-compact `j` is quasi-compact. -/
instance (i : (FGSubalgebra k K)ᵒᵖ) : QuasiCompact ((stageMap k K πX j).app i) :=
  MorphismProperty.of_isPullback (isPullback_stageMap k K πX j i).flip inferInstance

/-- Each stage `T_A ⟶ X_A` of a quasi-separated `j` is quasi-separated. -/
instance (i : (FGSubalgebra k K)ᵒᵖ) : QuasiSeparated ((stageMap k K πX j).app i) :=
  MorphismProperty.of_isPullback (isPullback_stageMap k K πX j i).flip inferInstance

omit [Algebra.IsSeparable k K] in
/-- The projections of the limit `X_K` to the stages lie over `X`, with the source of the
composite spelled as the apex of the cone. -/
theorem cone_π_stageSnd' {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) (i : (FGSubalgebra k K)ᵒᵖ) :
    CategoryStruct.comp (X := (𝔏 π).cone.pt) ((𝔏 π).cone.π.app i) (stageSnd k K π i) =
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) π :
        (𝔏 π).cone.pt ⟶ Y) :=
  cone_π_stageSnd k K π i

/-- **Higher direct images commute with base change to a separable algebraic extension.** For a
separable algebraic extension `K/k`, a scheme `X` over `k` and a quasi-compact quasi-separated
`j : T ⟶ X`, the base change map `(X_K ⟶ X)⁻¹ R^q j_* G ⟶ R^q j_{K,*} (T_K ⟶ T)⁻¹ G` is an
isomorphism for every abelian sheaf `G` on `T_étale` and every `q`. -/
theorem isIso_higherBaseChangeMapAb (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) :
    IsIso ((higherBaseChangeMapAb (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) πX)
      j (baseChangeMap πX j (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) (j ≫ πX))
      (isPullback_baseChangeMap πX j _).w q).app G) := by
  have hw : LimitHigherDirectImage.limitMorphism (stageMap k K πX j) (𝔏 (j ≫ πX)).cone
      (𝔏 πX).cone (𝔏 πX).isLimit ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) πX =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) (j ≫ πX) ≫ j := by
    rw [limitMorphism_stageMap]
    exact (isPullback_baseChangeMap πX j _).w
  exact (isIso_higherBaseChangeMapAb_app_congr_h _ j _ (limitMorphism_stageMap k K πX j) _ _ q
    G).1 (isIso_higherBaseChangeMapAb_of_etale_system (stageMap k K πX j) (𝔏 (j ≫ πX)).isLimit
      (𝔏 πX).isLimit j (stageSnd k K πX) (stageSnd k K (j ≫ πX))
      (fun a => map_stageSnd k K (j ≫ πX) a) _ (cone_π_stageSnd' k K πX) _
      (cone_π_stageSnd' k K (j ≫ πX)) (isPullback_stageMap k K πX j)
      (fun a => isPullback_stageMap_transition k K πX j a) ⟨⊥, Subalgebra.fg_bot⟩
      (fun i => Subtype.coe_le_coe.mp bot_le) hw G q)

end Main

end Stacks.EtaleCohomology.SeparableBaseChange
