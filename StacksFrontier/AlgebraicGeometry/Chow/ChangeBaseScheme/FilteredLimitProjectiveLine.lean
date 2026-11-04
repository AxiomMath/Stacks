module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChowPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The family of projective lines in a filtered limit of base schemes

In the situation of Stacks 0FVQ the quasi-compact scheme `X` of finite type over the base `S` may
be replaced by the family `X ×_S 𝐏¹_S` of projective lines over it, which is again quasi-compact
and of finite type over `S` because `𝐏¹_S` is proper over `S`. The base changes of the resulting
system are `X_i ×_{S_i} 𝐏¹_{S_i}` and `X' ×_{S'} 𝐏¹_{S'}`, so the surjectivity clause of Stacks
0FVQ for cycle groups applies to cycles on a family of projective lines.

## Main definitions

* `Stacks.Chow.FilteredBaseChangeSystem.projectiveLineSystem` — the system with `X` replaced by
  the family `X ×_S 𝐏¹_S`.
* `Stacks.Chow.FilteredBaseChangeSystem.projectiveLineStageCyclePullback` — the homomorphism
  `Z_k(X_i ×_{S_i} 𝐏¹_{S_i}) ⟶ Z_k(X' ×_{S'} 𝐏¹_{S'})` of cycle groups.
* `Stacks.Chow.FilteredBaseChangeSystem.plStageProjection` — the projection
  `(X ×_S 𝐏¹_S) ×_S S' ⟶ (X ×_S 𝐏¹_S) ×_S S_i` of the projective-line system.

## Main results

* `Stacks.Chow.FilteredBaseChangeSystem.map_comp_isoPullback` — the identifications of the
  families `X_i ×_{S_i} 𝐏¹_{S_i}` and `X' ×_{S'} 𝐏¹_{S'}` with the base changes of `X ×_S 𝐏¹_S`
  carry the morphism of families to the projection of the projective-line system.
* `Stacks.Chow.baseChangeCyclePullbackOfIsPullback_properPushforward` — base change along a
  cartesian square commutes with the pushforward along an isomorphism of two such squares.
* `Stacks.Chow.FilteredBaseChangeSystem.exists_projectiveLineStageCyclePullback_eq` —
  **Stacks 0FVQ, surjectivity for the projective-line family**: every `k`-cycle on
  `X' ×_{S'} 𝐏¹_{S'}` is the image of a `k`-cycle on `X_i ×_{S_i} 𝐏¹_{S_i}` for some finite
  stage `i`.

## Implementation notes

The base changes of the new system are the chosen fibre products `(X ×_S 𝐏¹_S) ×_S S_i`, whereas
the families `X_i ×_{S_i} 𝐏¹_{S_i}` are presented by the cartesian square
`Stacks.Chow.isPullback_projectiveLineProductBaseChange`. The two are identified by
`CategoryTheory.IsPullback.isoPullback`, and the surjectivity statement is carried across those
identifications by `Stacks.Chow.baseChangeCyclePullbackOfIsPullback_properPushforward`, which is
stated for abstract cartesian squares and abstract isomorphisms.

The morphisms of the new system are repeated below with the structure morphism of `X ×_S 𝐏¹_S`
written out, rather than used through the field `Stacks.Chow.FilteredBaseChangeSystem.X`. The two
spellings are definitionally equal but not syntactically, and a rewrite between them fails to be
type-correct.

## References

* [Stacks Project, Tag 0FVQ](https://stacks.math.columbia.edu/tag/0FVQ)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace Stacks.Chow

/-! ### Base change along a cartesian square and isomorphisms -/

/-- Pushing a cycle forward along an isomorphism and back along its inverse recovers it. -/
private theorem properPushforwardHom_inv_hom (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : A ≅ B)
    (he : e.hom ≫ sB = sA) (hinv : e.inv ≫ sA = sB) (k : ℤ) (c : CycleGroup C sA k) :
    properPushforwardHom C sB sA e.inv hinv k (properPushforwardHom C sA sB e.hom he k c) = c := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  have hx : e.inv.base (e.hom.base x) = x :=
    congrArg (fun m : A ⟶ A ↦ m.base x) e.hom_inv_id
  have h1 := properPushforward_apply_of_isIso C sB sA e.inv hinv k
    (properPushforwardHom C sA sB e.hom he k c) (e.hom.base x)
  rw [hx] at h1
  rw [properPushforwardHom_apply, h1, properPushforwardHom_apply,
    properPushforward_apply_of_isIso C sA sB e.hom he k c x]

/-- **Base change along a cartesian square commutes with an isomorphism of squares.** Let two
cartesian squares realize `Y₁` and `Y₂` as the base changes of `X₁` and `X₂` along `g`, and let
`a : X₁ ⟶ X₂` and `b : Y₁ ⟶ Y₂` be isomorphisms over the two bases forming a commuting square
with the two projections. Then the two base-change homomorphisms agree after pushing forward
along `a` and `b`. -/
theorem baseChangeCyclePullbackOfIsPullback_properPushforward
    (B : FlatBaseChangeSituation.{u}) (hc : B.c = 0) {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (f₁ : X₁ ⟶ B.base.S) [LocallyOfFiniteType f₁] {p₁ : Y₁ ⟶ X₁} {q₁ : Y₁ ⟶ B.baseChange.S}
    [LocallyOfFiniteType q₁] (sq₁ : IsPullback p₁ q₁ f₁ B.g)
    (f₂ : X₂ ⟶ B.base.S) [LocallyOfFiniteType f₂] {p₂ : Y₂ ⟶ X₂} {q₂ : Y₂ ⟶ B.baseChange.S}
    [LocallyOfFiniteType q₂] (sq₂ : IsPullback p₂ q₂ f₂ B.g)
    (a : X₁ ⟶ X₂) [IsIso a] (ha : a ≫ f₂ = f₁) (b : Y₁ ⟶ Y₂) [IsIso b] (hb : b ≫ q₂ = q₁)
    (hab : p₁ ≫ a = b ≫ p₂) (k : ℤ) (z : CycleGroup B.base f₁ k) :
    properPushforwardHom B.baseChange q₁ q₂ b hb k
        (baseChangeCyclePullbackOfIsPullback B hc f₁ sq₁ k z) =
      baseChangeCyclePullbackOfIsPullback B hc f₂ sq₂ k
        (properPushforwardHom B.base f₁ f₂ a ha k z) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y₂ => ?_)
  have hy : b.base ((inv b).base y₂) = y₂ :=
    congrArg (fun m : Y₂ ⟶ Y₂ ↦ m.base y₂) (IsIso.inv_hom_id b)
  set y₁ := (inv b).base y₂ with hy₁
  have hpt : a.base (p₁.base y₁) = p₂.base y₂ := by
    have h := congrArg (fun m : Y₁ ⟶ X₂ ↦ m.base y₁) hab
    simp only [Scheme.Hom.comp_apply] at h
    rw [h, hy]
  have hw := flatPullbackWeight_eq_of_isIso B.baseChange q₁ q₂ a b hb p₁ p₂ hab k y₁
  rw [hy] at hw
  have hl := properPushforward_apply_of_isIso B.baseChange q₁ q₂ b hb k
    (baseChangeCyclePullbackOfIsPullback B hc f₁ sq₁ k z) y₁
  rw [hy] at hl
  rw [properPushforwardHom_apply, hl,
    baseChangeCyclePullbackOfIsPullback_apply' B hc f₁ sq₁ k z y₁,
    baseChangeCyclePullbackOfIsPullback_apply' B hc f₂ sq₂ k _ y₂, ← hpt,
    properPushforwardHom_apply, properPushforward_apply_of_isIso B.base f₁ f₂ a ha k z, hw]

namespace FilteredBaseChangeSystem

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (s : FilteredBaseChangeSystem.{w, v, u} I)

/-! ### The projective-line family as a new system -/

/-- The family of projective lines over `X` is quasi-compact: `X` is, and the projection
`X ×_S 𝐏¹_S ⟶ X` is proper. -/
instance compactSpace_projectiveLineProduct_X :
    CompactSpace (projectiveLineProduct s.X.hom) :=
  QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
      s.limitBaseChange.base.S))

/-- The family of projective lines over `X` is locally of finite type over `S`. -/
instance locallyOfFiniteType_projectiveLineProduct_X :
    LocallyOfFiniteType (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
      s.limitBaseChange.base.S) ≫ s.X.hom) :=
  inferInstance

/-- The structure morphism of the family of projective lines over `X` is quasi-compact. -/
instance quasiCompact_projectiveLineProduct_X :
    QuasiCompact (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
      s.limitBaseChange.base.S) ≫ s.X.hom) :=
  inferInstance

/-- **The filtered base-change system of the projective-line family.** The system of Stacks 0FVQ
with the scheme `X` replaced by the family `X ×_S 𝐏¹_S`; the inverse system of bases and the flat
base change to the limit base are unchanged. -/
def projectiveLineSystem : FilteredBaseChangeSystem.{w, v, u} I :=
  { s with
    X := Over.mk (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
      s.limitBaseChange.base.S) ≫ s.X.hom)
    compactSpaceX := s.compactSpace_projectiveLineProduct_X
    locallyOfFiniteTypeX := s.locallyOfFiniteType_projectiveLineProduct_X
    quasiCompactX := s.quasiCompact_projectiveLineProduct_X }

/-- The scheme of the projective-line system is the family `X ×_S 𝐏¹_S`. -/
@[simp] theorem projectiveLineSystem_X_left :
    s.projectiveLineSystem.X.left = projectiveLineProduct s.X.hom := rfl

/-- The structure morphism of the projective-line system is that of the family `X ×_S 𝐏¹_S`. -/
@[simp] theorem projectiveLineSystem_X_hom :
    s.projectiveLineSystem.X.hom =
      pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
        s.limitBaseChange.base.S) ≫ s.X.hom := rfl

/-- The projective-line system has the same flat base change to the limit base. -/
@[simp] theorem projectiveLineSystem_limitBaseChange :
    s.projectiveLineSystem.limitBaseChange = s.limitBaseChange := rfl

/-- The projective-line system has the same structure morphisms of the stages. -/
@[simp] theorem projectiveLineSystem_stageToBase (i : I) :
    s.projectiveLineSystem.stageToBase i = s.stageToBase i := rfl

/-- The projective-line system has the same Chow situation at each stage. -/
@[simp] theorem projectiveLineSystem_stageSituation (i : I) :
    s.projectiveLineSystem.stageSituation i = s.stageSituation i := rfl

/-- The projective-line system has the same projections from the limit base to the stages. -/
@[simp] theorem projectiveLineSystem_limitProjection (i : I) :
    s.projectiveLineSystem.limitProjection i = s.limitProjection i := rfl

/-! ### The base changes of the projective-line family -/

/-- The projection `(X ×_S 𝐏¹_S) ×_S S' ⟶ (X ×_S 𝐏¹_S) ×_S S_i` of the projective-line system,
with the structure morphism of the family written out. -/
def plStageProjection (i : I) :
    pullback (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
        s.limitBaseChange.base.S) ≫ s.X.hom) s.limitBaseChange.g ⟶
      pullback (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
        s.limitBaseChange.base.S) ≫ s.X.hom) (s.stageToBase i) :=
  s.projectiveLineSystem.stageProjection i

/-- The projection of the projective-line system is the identity on the first factor. -/
private theorem plStageProjection_comp_fst (i : I) :
    s.plStageProjection i ≫ pullback.fst (pullback.fst s.X.hom
        (relativeProjectiveLine s.limitBaseChange.base.S ↘ s.limitBaseChange.base.S) ≫ s.X.hom)
        (s.stageToBase i) =
      pullback.fst (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
        s.limitBaseChange.base.S) ≫ s.X.hom) s.limitBaseChange.g :=
  s.projectiveLineSystem.stageProjection_comp_fst i

/-- The projection of the projective-line system is the projection of bases on the second
factor. -/
private theorem plStageProjection_comp_snd (i : I) :
    s.plStageProjection i ≫ pullback.snd (pullback.fst s.X.hom
        (relativeProjectiveLine s.limitBaseChange.base.S ↘ s.limitBaseChange.base.S) ≫ s.X.hom)
        (s.stageToBase i) =
      pullback.snd (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
        s.limitBaseChange.base.S) ≫ s.X.hom) s.limitBaseChange.g ≫ s.limitProjection i :=
  s.projectiveLineSystem.stageProjection_comp_snd i

/-- The base change of the projective-line family to the limit base is the base change of its
base change to a finite stage along the projection of bases. -/
private theorem isPullback_plStageProjection (i : I) :
    IsPullback (s.plStageProjection i)
      (pullback.snd (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
        s.limitBaseChange.base.S) ≫ s.X.hom) s.limitBaseChange.g)
      (pullback.snd (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
        s.limitBaseChange.base.S) ≫ s.X.hom) (s.stageToBase i))
      (s.limitProjection i) :=
  s.projectiveLineSystem.isPullback_stageProjection i

/-- The morphism `X' ×_{S'} 𝐏¹_{S'} ⟶ X_i ×_{S_i} 𝐏¹_{S_i}` of families is compatible with the
two comparison morphisms to `X ×_S 𝐏¹_S`. -/
private theorem map_comp_baseChange (i : I) :
    projectiveLineProductMap (pullback.snd s.X.hom (s.stageToBase i)) (s.limitProjection i)
          (s.isPullback_stageProjection i).w ≫
        projectiveLineProductBaseChange s.X.hom (s.stageToBase i) =
      projectiveLineProductBaseChange s.X.hom s.limitBaseChange.g := by
  apply pullback.hom_ext
  · rw [Category.assoc, projectiveLineProductBaseChange_comp_fst,
      projectiveLineProductMap_comp_fst_assoc, s.stageProjection_comp_fst i,
      projectiveLineProductBaseChange_comp_fst]
  · rw [Category.assoc, projectiveLineProductBaseChange_comp_snd,
      projectiveLineProductMap_comp_snd_assoc, ← projectiveLineBaseChange_comp,
      s.limitProjection_comp_stageToBase i, projectiveLineProductBaseChange_comp_snd]

/-- The identifications of `X_i ×_{S_i} 𝐏¹_{S_i}` and `X' ×_{S'} 𝐏¹_{S'}` with the base changes
of `X ×_S 𝐏¹_S` form a commuting square with the morphism of families and the projection of the
projective-line system. -/
theorem map_comp_isoPullback (i : I) :
    projectiveLineProductMap (pullback.snd s.X.hom (s.stageToBase i)) (s.limitProjection i)
          (s.isPullback_stageProjection i).w ≫
        (isPullback_projectiveLineProductBaseChange s.X.hom (s.stageToBase i)).isoPullback.hom =
      (isPullback_projectiveLineProductBaseChange s.X.hom s.limitBaseChange.g).isoPullback.hom ≫
        s.plStageProjection i := by
  apply pullback.hom_ext
  · rw [Category.assoc,
      (isPullback_projectiveLineProductBaseChange s.X.hom (s.stageToBase i)).isoPullback_hom_fst,
      s.map_comp_baseChange i, Category.assoc, s.plStageProjection_comp_fst i,
      (isPullback_projectiveLineProductBaseChange s.X.hom s.limitBaseChange.g).isoPullback_hom_fst]
  · rw [Category.assoc,
      (isPullback_projectiveLineProductBaseChange s.X.hom (s.stageToBase i)).isoPullback_hom_snd,
      Category.assoc, s.plStageProjection_comp_snd i,
      ← Category.assoc _ _ (s.limitProjection i),
      (isPullback_projectiveLineProductBaseChange s.X.hom s.limitBaseChange.g).isoPullback_hom_snd]
    exact (isPullback_projectiveLineProductMap (pullback.snd s.X.hom (s.stageToBase i))
      (s.limitProjection i) (s.isPullback_stageProjection i)).w

/-! ### Stacks 0FVQ for the projective-line family -/

/-- The homomorphism `Z_k(X_i ×_{S_i} 𝐏¹_{S_i}) ⟶ Z_k(X' ×_{S'} 𝐏¹_{S'})` of cycle groups
induced by the projection from the limit base to the stage `i`, taken along the cartesian square
`Stacks.Chow.isPullback_projectiveLineProductMap`. -/
def projectiveLineStageCyclePullback (i : I) (k : ℤ) :
    CycleGroup (s.stageSituation i)
        (pullback.fst (pullback.snd s.X.hom (s.stageToBase i))
          (relativeProjectiveLine (s.diagram.obj i) ↘ s.diagram.obj i) ≫
            pullback.snd s.X.hom (s.stageToBase i)) k →+
      CycleGroup s.limitBaseChange.baseChange
        (pullback.fst (pullback.snd s.X.hom s.limitBaseChange.g)
          (relativeProjectiveLine s.limitBaseChange.baseChange.S ↘
            s.limitBaseChange.baseChange.S) ≫ pullback.snd s.X.hom s.limitBaseChange.g) k :=
  baseChangeCyclePullbackOfIsPullback (s.stageToLimitBaseChange i) rfl
    (pullback.fst (pullback.snd s.X.hom (s.stageToBase i))
      (relativeProjectiveLine (s.diagram.obj i) ↘ s.diagram.obj i) ≫
        pullback.snd s.X.hom (s.stageToBase i))
    (isPullback_projectiveLineProductMap (pullback.snd s.X.hom (s.stageToBase i))
      (s.limitProjection i) (s.isPullback_stageProjection i)) k

/-- The homomorphism on the cycle groups of the families of projective lines, written out. -/
theorem projectiveLineStageCyclePullback_def (i : I) (k : ℤ) :
    s.projectiveLineStageCyclePullback i k =
      baseChangeCyclePullbackOfIsPullback (s.stageToLimitBaseChange i) rfl
        (pullback.fst (pullback.snd s.X.hom (s.stageToBase i))
          (relativeProjectiveLine (s.diagram.obj i) ↘ s.diagram.obj i) ≫
            pullback.snd s.X.hom (s.stageToBase i))
        (isPullback_projectiveLineProductMap (pullback.snd s.X.hom (s.stageToBase i))
          (s.limitProjection i) (s.isPullback_stageProjection i)) k :=
  rfl

/-- **Stacks Project, Tag 0FVQ, surjectivity for the projective-line family.** Every `k`-cycle on
`X' ×_{S'} 𝐏¹_{S'}` is the image of a `k`-cycle on `X_i ×_{S_i} 𝐏¹_{S_i}` for some finite stage
`i`. -/
@[stacks 0FVQ "cycle groups, surjectivity for the projective line family"]
theorem exists_projectiveLineStageCyclePullback_eq (k : ℤ)
    (z : CycleGroup s.limitBaseChange.baseChange
      (pullback.fst (pullback.snd s.X.hom s.limitBaseChange.g)
        (relativeProjectiveLine s.limitBaseChange.baseChange.S ↘
          s.limitBaseChange.baseChange.S) ≫ pullback.snd s.X.hom s.limitBaseChange.g) k) :
    ∃ (i : I) (c : CycleGroup (s.stageSituation i)
      (pullback.fst (pullback.snd s.X.hom (s.stageToBase i))
        (relativeProjectiveLine (s.diagram.obj i) ↘ s.diagram.obj i) ≫
          pullback.snd s.X.hom (s.stageToBase i)) k),
      s.projectiveLineStageCyclePullback i k c = z := by
  have hvs := (isPullback_projectiveLineProductBaseChange s.X.hom
    s.limitBaseChange.g).isoPullback_hom_snd
  have hvi := (Iso.inv_comp_eq _).2 hvs.symm
  obtain ⟨i, w, hw⟩ := s.projectiveLineSystem.exists_stageCyclePullback_eq k
    (properPushforwardHom s.limitBaseChange.baseChange _ _
      (isPullback_projectiveLineProductBaseChange s.X.hom s.limitBaseChange.g).isoPullback.hom
      hvs k z)
  have hus := (isPullback_projectiveLineProductBaseChange s.X.hom
    (s.stageToBase i)).isoPullback_hom_snd
  have hui := (Iso.inv_comp_eq _).2 hus.symm
  have hab : s.plStageProjection i ≫ (isPullback_projectiveLineProductBaseChange s.X.hom
        (s.stageToBase i)).isoPullback.inv =
      (isPullback_projectiveLineProductBaseChange s.X.hom
          s.limitBaseChange.g).isoPullback.inv ≫
        projectiveLineProductMap (pullback.snd s.X.hom (s.stageToBase i)) (s.limitProjection i)
          (s.isPullback_stageProjection i).w := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← s.map_comp_isoPullback i, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  refine ⟨i, properPushforwardHom (s.stageSituation i) _ _
    (isPullback_projectiveLineProductBaseChange s.X.hom (s.stageToBase i)).isoPullback.inv hui k
    w, ?_⟩
  have key := baseChangeCyclePullbackOfIsPullback_properPushforward
    (s.stageToLimitBaseChange i) rfl _ (s.isPullback_plStageProjection i) _
    (isPullback_projectiveLineProductMap (pullback.snd s.X.hom (s.stageToBase i))
      (s.limitProjection i) (s.isPullback_stageProjection i))
    (isPullback_projectiveLineProductBaseChange s.X.hom (s.stageToBase i)).isoPullback.inv hui
    (isPullback_projectiveLineProductBaseChange s.X.hom s.limitBaseChange.g).isoPullback.inv hvi
    hab k w
  have hw2 : baseChangeCyclePullbackOfIsPullback (s.stageToLimitBaseChange i) rfl
      (pullback.snd (pullback.fst s.X.hom (relativeProjectiveLine s.limitBaseChange.base.S ↘
        s.limitBaseChange.base.S) ≫ s.X.hom) (s.stageToBase i))
      (s.isPullback_plStageProjection i) k w =
      properPushforwardHom s.limitBaseChange.baseChange _ _
        (isPullback_projectiveLineProductBaseChange s.X.hom s.limitBaseChange.g).isoPullback.hom
        hvs k z := hw
  rw [hw2] at key
  exact key.symm.trans (properPushforwardHom_inv_hom s.limitBaseChange.baseChange _ _
    (isPullback_projectiveLineProductBaseChange s.X.hom s.limitBaseChange.g).isoPullback hvs hvi
    k z)

end FilteredBaseChangeSystem

end Stacks.Chow

end
