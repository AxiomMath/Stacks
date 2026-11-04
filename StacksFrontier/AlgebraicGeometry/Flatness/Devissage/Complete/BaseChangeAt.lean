module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.BaseChangeAt

/-!
# Base change of a complete dévissage at a point

Under a pointed base change with affine new base inducing an isomorphism of residue fields,
the stagewise base change of a complete dévissage at a point is again a complete dévissage at
the point above it.

## Main definitions

* `AlgebraicGeometry.PointedStageIsBaseChange`: the distinguished points of a stage project to
  those of the stage it is a base change of.
* `AlgebraicGeometry.PointedChainIsBaseChange`: the same at every stage of a chain.
* `AlgebraicGeometry.CompleteDevissageAt.IsBaseChange`: a complete dévissage at a point is the
  stagewise base change of another, distinguished points included.

## Main results

* `AlgebraicGeometry.exists_completeDevissageAt_baseChange`: any given stagewise base change of
  a complete dévissage at a point carries compatible distinguished points.
* `AlgebraicGeometry.CompleteDevissageAt.exists_isBaseChange`: Stacks 05HK, combining the
  construction of Stacks 05HJ with the previous result, empty dévissage included.

## Implementation notes

The relation `AlgebraicGeometry.StageIsBaseChange` pins down the base-changed stage, so the
pointed dévissage produced here is carried by those very stages and not by some unrelated
dévissage of the base-changed module. The distinguished points are the unique points of the
base-changed schemes lying over the original ones and over the new base point; their
uniqueness is what the residue-field isomorphism buys, and it is Stacks 05H8 that produces
them. Stacks 05H8 is stated for the canonical fibre product, so the stage at hand is carried
there by `AlgebraicGeometry.OneStepDevissage.ofSourceIso` and its distinguished data carried
back by `AlgebraicGeometry.mem_fiberSupport_iff_of_sourceIso` and its companions.

## References

* [Stacks Project, Tag 05HK](https://stacks.math.columbia.edu/tag/05HK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section Stage

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {F : X.Modules} {F' : X'.Modules}
  {s : S} {s' : S'} {h : S' ⟶ S}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
  [LocallyOfFiniteType f'] [F'.IsQuasicoherent] [F'.IsFiniteType]

/-- The distinguished points of a stage and of a stage it is a base change of project to one
another. -/
structure PointedStageIsBaseChange {x : X} {x' : X'} {D : DevissageStage f F s}
    {D' : DevissageStage f' F' s'} (h : S' ⟶ S) (pX : X' ⟶ X)
    (pointed : PointedDevissageStage f F s x D)
    (pointed' : PointedDevissageStage f' F' s' x' D')
    (hstage : StageIsBaseChange h pX D D') where
  x_eq : pX x' = x
  y_eq : hstage.pY pointed'.y = pointed.y
  /-- The distinguished point of the closed subscheme of the stage. -/
  z : D.oneStep.Z
  /-- The distinguished point of the closed subscheme of the base-changed stage. -/
  z' : D'.oneStep.Z
  z_eq : hstage.pZ z' = z
  /-- `z` is the distinguished point of the closed subscheme of the pointed stage. -/
  z_is_pointed : HEq pointed.atPoint.z z
  /-- `z'` is the distinguished point of the closed subscheme of the pointed base-changed stage. -/
  z'_is_pointed : HEq pointed'.atPoint.z z'

/-- The geometric data of a one-step dévissage at a point, read off any one-step dévissage
heterogeneously equal to the underlying one. -/
private lemma oneStepDevissageAt_geometry {x : X} (E : OneStepDevissageAt f F x) {t : S}
    (ht : f x = t) (C : OneStepDevissage f F t) (hC : HEq E.toOneStepDevissage C) (z : C.Z)
    (hz : HEq E.z z) (y : C.Y) (hy : HEq E.y y) :
    C.i z = x ∧ C.π z = y ∧ C.π ⁻¹' {y} = {z} ∧
      ∃ hgy : C.g y = t,
        letI : Algebra (S.residueField t) (C.Y.residueField y) :=
          ((S.residueFieldCongr hgy).inv ≫ C.g.residueFieldMap y).hom.toAlgebra
        PurelyTranscendental (S.residueField t) (C.Y.residueField y) := by
  subst ht
  obtain rfl := eq_of_heq hC
  obtain rfl := eq_of_heq hz
  obtain rfl := eq_of_heq hy
  exact ⟨E.i_z, E.π_z, E.fiber_eq_singleton, E.g_y, E.residueField_purelyTranscendental⟩

/-- The distinguished point of the smooth scheme of a pointed stage lies over the base point
of the dévissage. -/
private lemma pointedStage_g_y {x : X} {D : DevissageStage f F s}
    (P : PointedDevissageStage f F s x D) (hx : f x = s) : D.oneStep.g P.y = s := by
  cases hx
  cases D with
  | mk step rank alpha genericPoint genericPoint_spec genericFiber_isIso =>
    cases P with
    | mk atPoint sameOneStep y sameY =>
      cases sameOneStep
      cases sameY
      exact atPoint.g_y

/-- A stage which is a base change of a pointed stage is pointed, at the unique point above
the distinguished point, as soon as the base change is along a cartesian square with affine
new base inducing an isomorphism of residue fields. -/
private def pointedStageIsBaseChange (hs : h s' = s) [IsAffine S']
    (hres : IsIso (h.residueFieldMap s')) {x : X} {x' : X'}
    {D : DevissageStage f F s} {D' : DevissageStage f' F' s'} (pX : X' ⟶ X)
    (hX : IsPullback pX f' f h) (P : PointedDevissageStage f F s x D)
    (hstage : StageIsBaseChange h pX D D') (hx : pX x' = x) (hxbase : f x = s)
    (hxbase' : f' x' = s') (eF : (Scheme.Modules.pullback pX).obj F ≅ F') :
    Σ P' : PointedDevissageStage f' F' s' x' D',
      PointedStageIsBaseChange h pX P P' hstage := by
  subst hxbase hxbase'
  cases D with
  | mk Dstep rank alpha η hη hα =>
    cases P with
    | mk atPoint sameOneStep y sameY =>
      cases sameOneStep
      cases sameY
      let j : X' ≅ Limits.pullback f h := hX.isoPullback
      let xc : (Limits.pullback f h : Scheme.{u}) := j.hom x'
      have hjf : j.hom ≫ Limits.pullback.fst f h = pX := hX.isoPullback_hom_fst
      have hjg : j.hom ≫ Limits.pullback.snd f h = f' := hX.isoPullback_hom_snd
      have hji : j.inv ≫ f' = Limits.pullback.snd f h := hX.isoPullback_inv_snd
      have hxc : Limits.pullback.fst f h xc = x := by
        change (j.hom ≫ Limits.pullback.fst f h) x' = x
        rwa [hjf]
      have hxcb : Limits.pullback.snd f h xc = f' x' := by
        change (j.hom ≫ Limits.pullback.snd f h) x' = f' x'
        rw [hjg]
      let B₀ := OneStepDevissage.baseChange f F (f x) (f' x') h hs atPoint.toOneStepDevissage
      have := B₀.locallyOfFiniteType
      have := B₀.quasicoherent
      have := B₀.finiteType
      let eFbc : (Scheme.Modules.pullback j.inv).obj F' ≅
          (Scheme.Modules.pullback (Limits.pullback.fst f h)).obj F :=
        (Scheme.Modules.pullback j.inv).mapIso eF.symm ≪≫
          (Scheme.Modules.pullbackComp j.inv pX).app F ≪≫
          (Scheme.Modules.pullbackCongr hX.isoPullback_inv_fst).app F
      let eFl : (Scheme.Modules.pullback j.hom).obj
          ((Scheme.Modules.pullback (Limits.pullback.fst f h)).obj F) ≅ F' :=
        (Scheme.Modules.pullbackComp j.hom (Limits.pullback.fst f h)).app F ≪≫
          (Scheme.Modules.pullbackCongr hjf).app F ≪≫ eF
      let C := OneStepDevissage.ofSourceIso j.symm hji eFbc D'.oneStep
      have hsq : IsPullback hstage.pZ C.i atPoint.toOneStepDevissage.i
          (Limits.pullback.fst f h) := by
        rw [OneStepDevissage.ofSourceIso_i]
        exact hstage.x_square.of_iso (Iso.refl _) (Iso.refl _) j (Iso.refl _) (by simp) (by simp)
          (by simp) (by simp [hjf])
      let B : OneStepDevissage.BaseChangeData f F (f x) (f' x') h hs
          atPoint.toOneStepDevissage :=
        { locallyOfFiniteType := inferInstance
          quasicoherent := inferInstance
          finiteType := inferInstance
          devissage := C
          pY := hstage.pY
          pZ := hstage.pZ
          y_square := hstage.y_square
          x_square := hsq
          z_square := hstage.z_square
          module_eq := hstage.G_eq }
      choose z' hz hiz using Scheme.exists_preimage_of_isPullback hstage.x_square
        atPoint.z x' (by rw [atPoint.i_z, hx])
      choose y' hy hgy using Scheme.exists_preimage_of_isPullback hstage.y_square
        atPoint.y (f' x') (by rw [atPoint.g_y, hs])
      have hzs : (D'.oneStep.π ≫ D'.oneStep.g) z' = f' x' := by
        rw [← D'.oneStep.over_base, Scheme.Hom.comp_apply, hiz]
      choose E hEC hEz hEy using OneStepDevissageAt.exists_baseChange f F x atPoint
        (f' x') h hs B xc hxc hxcb z' hz hzs y' hy hgy
      have hgeo := oneStepDevissageAt_geometry E hxcb C hEC z' hEz y' hEy
      choose hgy₂ hpt using hgeo.2.2.2
      let E' := E.ofSourceIso j hjg eFl rfl
      exact ⟨⟨{ toOneStepDevissage := D'.oneStep
                mem_fiber_support := E'.mem_fiber_support
                dimension := E'.dimension
                z := z'
                y := y'
                i_z := hiz
                π_z := hgeo.2.1
                g_y := hgy₂
                fiber_eq_singleton := hgeo.2.2.1
                residueField_purelyTranscendental := hpt },
            HEq.rfl, y', HEq.rfl⟩,
        ⟨hx, hy, atPoint.z, z', hz, HEq.rfl, HEq.rfl⟩⟩

end Stage

/-- The distinguished points in every stage of two corresponding pointed dévissage chains
project to one another. -/
inductive PointedChainIsBaseChange {S S' : Scheme.{u}} {s : S} {s' : S'} (h : S' ⟶ S) :
    {X : Scheme.{u}} → {f : X ⟶ S} → {F : X.Modules} → {hl : LocallyOfFiniteType f} →
      {hq : F.IsQuasicoherent} → {ht : F.IsFiniteType} →
      {X' : Scheme.{u}} → {f' : X' ⟶ S'} → {F' : X'.Modules} →
      {hl' : LocallyOfFiniteType f'} → {hq' : F'.IsQuasicoherent} →
      {ht' : F'.IsFiniteType} → (pX : X' ⟶ X) → {x : X} → {x' : X'} →
      {chain : DevissageChain s X f F hl hq ht} →
      {chain' : DevissageChain s' X' f' F' hl' hq' ht'} →
      PointedDevissageChain s X f F hl hq ht x chain →
      PointedDevissageChain s' X' f' F' hl' hq' ht' x' chain' → Prop where
  /-- The final stages correspond. -/
  | last {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {X' : Scheme.{u}} {f' : X' ⟶ S'}
      {F' : X'.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
      [ht : F.IsFiniteType] [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent]
      [ht' : F'.IsFiniteType] {pX : X' ⟶ X} {x : X} {x' : X'}
      {D : @DevissageStage X S f F s hl hq ht}
      {D' : @DevissageStage X' S' f' F' s' hl' hq' ht'}
      {hz : IsZero D.coker} {hz' : IsZero D'.coker}
      {P : @PointedDevissageStage X S f F s x hl hq ht D}
      {P' : @PointedDevissageStage X' S' f' F' s' x' hl' hq' ht' D'}
      (hstage : @StageIsBaseChange X S X' S' f f' F F' s s' hl hq ht hl' hq' ht' h pX D D')
      (hpoint : PointedStageIsBaseChange h pX P P' hstage) :
      PointedChainIsBaseChange h pX (.last x D hz P) (.last x' D' hz' P')
  /-- A nonfinal stage corresponds, and so does the dévissage of its cokernel. -/
  | more {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {X' : Scheme.{u}} {f' : X' ⟶ S'}
      {F' : X'.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
      [ht : F.IsFiniteType] [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent]
      [ht' : F'.IsFiniteType] {pX : X' ⟶ X} {x : X} {x' : X'}
      {D : @DevissageStage X S f F s hl hq ht}
      {D' : @DevissageStage X' S' f' F' s' hl' hq' ht'}
      {hqC : D.coker.IsQuasicoherent} {htC : D.coker.IsFiniteType}
      {hlY : LocallyOfFiniteType D.oneStep.g} {hqC' : D'.coker.IsQuasicoherent}
      {htC' : D'.coker.IsFiniteType} {hlY' : LocallyOfFiniteType D'.oneStep.g}
      {tail : DevissageChain s D.oneStep.Y D.oneStep.g D.coker hlY hqC htC}
      {tail' : DevissageChain s' D'.oneStep.Y D'.oneStep.g D'.coker hlY' hqC' htC'}
      {P : @PointedDevissageStage X S f F s x hl hq ht D}
      {P' : @PointedDevissageStage X' S' f' F' s' x' hl' hq' ht' D'}
      {Pt : PointedDevissageChain s D.oneStep.Y D.oneStep.g D.coker hlY hqC htC P.y tail}
      {Pt' : PointedDevissageChain s' D'.oneStep.Y D'.oneStep.g D'.coker hlY' hqC' htC'
        P'.y tail'}
      (hstage : @StageIsBaseChange X S X' S' f f' F F' s s' hl hq ht hl' hq' ht' h pX D D')
      (hpoint : PointedStageIsBaseChange h pX P P' hstage)
      (htail : PointedChainIsBaseChange h hstage.pY Pt Pt') :
      PointedChainIsBaseChange h pX (.more x D hqC htC hlY tail P Pt)
        (.more x' D' hqC' htC' hlY' tail' P' Pt')

section Chain

variable {S S' : Scheme.{u}} {s : S} {s' : S'} {h : S' ⟶ S}

/-- Compatible distinguished points can be chosen in a stagewise base change of a pointed
dévissage chain. -/
private theorem exists_pointedChainIsBaseChange (hs : h s' = s) [IsAffine S']
    (hres : IsIso (h.residueFieldMap s')) {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} {x : X}
    {chain : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x chain) :
    ∀ {X' : Scheme.{u}} {f' : X' ⟶ S'} {F' : X'.Modules} {hl' : LocallyOfFiniteType f'}
      {hq' : F'.IsQuasicoherent} {ht' : F'.IsFiniteType}
      {chain' : DevissageChain s' X' f' F' hl' hq' ht'} (pX : X' ⟶ X) (x' : X'),
      IsPullback pX f' f h → ((Scheme.Modules.pullback pX).obj F ≅ F') →
      ChainIsBaseChange h pX chain chain' → pX x' = x → f x = s → f' x' = s' →
      ∃ P' : PointedDevissageChain s' X' f' F' hl' hq' ht' x' chain',
        PointedChainIsBaseChange h pX P P' := by
  induction P with
  | last x D hz Pstage =>
    intro X' f' F' hl' hq' ht' chain' pX x' hX eF hbc hx hxbase hxbase'
    cases hbc with
    | last hstage hz0 hz1 =>
      obtain ⟨P', hP'⟩ :=
        pointedStageIsBaseChange hs hres pX hX Pstage hstage hx hxbase hxbase' eF
      exact ⟨.last x' _ hz1 P', .last hstage hP'⟩
  | more x D hqC htC hlY tail Pstage Pt ih =>
    intro X' f' F' hl' hq' ht' chain' pX x' hX eF hbc hx hxbase hxbase'
    cases hbc with
    | more hstage htail =>
      obtain ⟨P', hP'⟩ :=
        pointedStageIsBaseChange hs hres pX hX Pstage hstage hx hxbase hxbase' eF
      obtain ⟨Pt', htail'⟩ := ih hstage.pY P'.y hstage.y_square
        (cokernelIsoOfStageIsBaseChange hstage) htail hP'.y_eq
        (pointedStage_g_y Pstage hxbase) (pointedStage_g_y P' hxbase')
      exact ⟨.more x' _ _ _ _ _ P' Pt', .more hstage hP' htail'⟩

/-- Any stagewise base change of a complete dévissage at a point, along a cartesian square with
affine new base inducing an isomorphism of residue fields, is again a complete dévissage at the
point above it, with the distinguished points projecting to the original ones. Here the
base-changed chain is given; `AlgebraicGeometry.CompleteDevissageAt.exists_isBaseChange`
constructs it. -/
theorem exists_completeDevissageAt_baseChange {X X' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {F : X.Modules} {F' : X'.Modules} {x : X} {x' : X'} [IsAffine S']
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] [LocallyOfFiniteType f']
    [F'.IsQuasicoherent] [F'.IsFiniteType] (hs : h (f' x') = f x)
    (hres : IsIso (h.residueFieldMap (f' x'))) (D : NonemptyCompleteDevissageAt f F x) (pX : X' ⟶ X)
    (hX : IsPullback pX f' f h) (eF : (Scheme.Modules.pullback pX).obj F ≅ F')
    (hx : pX x' = x) (D' : NonemptyCompleteDevissage f' F' (f' x'))
    (hbc : ChainIsBaseChange h pX D.toNonemptyCompleteDevissage.chain D'.chain) :
    ∃ DAt' : NonemptyCompleteDevissageAt f' F' x',
      DAt'.toNonemptyCompleteDevissage = D' ∧
        PointedChainIsBaseChange h pX D.pointed DAt'.pointed := by
  obtain ⟨P', hP'⟩ :=
    exists_pointedChainIsBaseChange hs hres D.pointed pX x' hX eF hbc hx rfl rfl
  exact ⟨⟨D', P'⟩, rfl, hP'⟩

end Chain

section Full

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {F : X.Modules} {F' : X'.Modules}
  {x : X} {x' : X'}

/-- The base change of a locally finite type morphism along a cartesian square is locally of
finite type. -/
theorem CompleteDevissageAt.locallyOfFiniteType_of_isPullback {h : S' ⟶ S} {pX : X' ⟶ X}
    [LocallyOfFiniteType f] (hX : IsPullback pX f' f h) : LocallyOfFiniteType f' :=
  MorphismProperty.of_isPullback hX (P := @LocallyOfFiniteType) inferInstance

/-- A module isomorphic to the pullback of a quasi-coherent module is quasi-coherent. -/
theorem CompleteDevissageAt.isQuasicoherent_of_iso_pullback {pX : X' ⟶ X} [F.IsQuasicoherent]
    (eF : (Scheme.Modules.pullback pX).obj F ≅ F') : F'.IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_of_iso eF
    (Stacks.Modules.isQuasicoherent_pullback pX F inferInstance)

/-- A module isomorphic to the pullback of a module of finite type is of finite type. -/
theorem CompleteDevissageAt.isFiniteType_of_iso_pullback {pX : X' ⟶ X} [F.IsFiniteType]
    (eF : (Scheme.Modules.pullback pX).obj F ≅ F') : F'.IsFiniteType :=
  SheafOfModules.isFiniteType_of_iso eF
    (SheafOfModules.pullback_isFiniteType pX.toLRSHom.toShHom F)

/-- The relation between a complete dévissage of `F/X/S` at `x` and one of `F'/X'/S'` at `x'`
saying that the second is the stagewise base change of the first along `h`, with distinguished
points projecting to the original ones: both are empty, or both are nonempty with chains
related by `AlgebraicGeometry.ChainIsBaseChange` and distinguished points related by
`AlgebraicGeometry.PointedChainIsBaseChange`. -/
def CompleteDevissageAt.IsBaseChange [LocallyOfFiniteType f] [F.IsQuasicoherent]
    [F.IsFiniteType] [LocallyOfFiniteType f'] [F'.IsQuasicoherent] [F'.IsFiniteType]
    (h : S' ⟶ S) (pX : X' ⟶ X) :
    CompleteDevissageAt f F x → CompleteDevissageAt f' F' x' → Prop
  | .empty _, .empty _ => True
  | .nonempty D, .nonempty D' =>
      ChainIsBaseChange h pX D.toNonemptyCompleteDevissage.chain
          D'.toNonemptyCompleteDevissage.chain ∧
        PointedChainIsBaseChange h pX D.pointed D'.pointed
  | _, _ => False

/-- **Stacks 05HK.** Let `(S', s') → (S, s)` be a morphism of pointed schemes inducing an
isomorphism of residue fields, with `S'` affine, let `X'` be the base change of `X` and `F'`
the pullback of `F`, and let `x' ∈ X'` lie over `x ∈ X` and `s'` (so `s = f x`, `s' = f' x'`).
Then every complete dévissage of `F/X/S` at `x` base-changes, stage by stage as in Stacks 05HJ,
to a complete dévissage of `F'/X'/S'` at `x'` whose distinguished points lie over the original
ones. The finiteness properties of `f'` and `F'` are derived from the base change, not
assumed. -/
@[stacks 05HK]
theorem CompleteDevissageAt.exists_isBaseChange {h : S' ⟶ S} [IsAffine S']
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (hres : IsIso (h.residueFieldMap (f' x'))) (pX : X' ⟶ X) (hX : IsPullback pX f' f h)
    (eF : (Scheme.Modules.pullback pX).obj F ≅ F') (hx : pX x' = x)
    (D : CompleteDevissageAt f F x) :
    haveI := locallyOfFiniteType_of_isPullback hX
    haveI := isQuasicoherent_of_iso_pullback eF
    haveI := isFiniteType_of_iso_pullback eF
    ∃ D' : CompleteDevissageAt f' F' x', D.IsBaseChange h pX D' := by
  have := locallyOfFiniteType_of_isPullback hX
  have := isQuasicoherent_of_iso_pullback eF
  have := isFiniteType_of_iso_pullback eF
  have hs : h (f' x') = f x := by
    rw [← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hX.w]
  cases D with
  | empty hz =>
    exact ⟨.empty (IsZero.of_iso ((Scheme.Modules.pullback pX).map_isZero hz) eF.symm),
      trivial⟩
  | nonempty D =>
    obtain ⟨D', hbc⟩ :=
      exists_completeDevissage_baseChange hs D.toNonemptyCompleteDevissage pX hX eF
    obtain ⟨DAt', rfl, hP⟩ :=
      exists_completeDevissageAt_baseChange hs hres D pX hX eF hx D' hbc
    exact ⟨.nonempty DAt', hbc, hP⟩

end Full

end AlgebraicGeometry

end
