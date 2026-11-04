module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.CommonTargetPairs
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliaryGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliarySpaces

/-!
# The groupoid of pairs of arrows with a common target

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`.  The pairs of arrows with a
common target form an equivalence relation `R ×_{t, U, t} R` on `R`, and so a groupoid in
algebraic spaces `(R, R ×_{t, U, t} R, pr₁, pr₀, pr₀₂)` over `B`: an arrow `(r₀, r₁)` goes from
`r₁` to `r₀`, and `(r₀, r₁) ∘ (r₁, r₂) = (r₀, r₂)`.  This is the groupoid that the proof of
Stacks 0GPP attaches to `(U, R, s, t, c)`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.targetPairsGroupoid`: the groupoid
  `(R, R ×_{t, U, t} R, pr₁, pr₀, pr₀₂)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- The first projection `pr₀ : R ×_{t, U, t} R ⟶ R`. -/
abbrev targetPairsFst : AlgebraicSpaces.fiberProduct C S hS G.target G.target ⟶ G.arrows :=
  ObjectProperty.homMk (pullback.fst G.target.hom G.target.hom)

/-- The second projection `pr₁ : R ×_{t, U, t} R ⟶ R`. -/
abbrev targetPairsSnd : AlgebraicSpaces.fiberProduct C S hS G.target G.target ⟶ G.arrows :=
  ObjectProperty.homMk (pullback.snd G.target.hom G.target.hom)

/-- The two arrows of a pair with a common target have the same target. -/
theorem targetPairsFst_comp_target :
    targetPairsFst G ≫ G.target = targetPairsSnd G ≫ G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target).w

/-- The composition `pr₀₂` of the groupoid of pairs with a common target, sending a composable
pair `((r₀, r₁), (r₁, r₂))` to `(r₀, r₂)`. -/
def targetPairsComp :
    AlgebraicSpaces.fiberProduct C S hS (targetPairsSnd G) (targetPairsFst G) ⟶
      AlgebraicSpaces.fiberProduct C S hS G.target G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target).lift
    ((ObjectProperty.homMk (pullback.fst (targetPairsSnd G).hom (targetPairsFst G).hom) :
        AlgebraicSpaces.fiberProduct C S hS (targetPairsSnd G) (targetPairsFst G) ⟶ _) ≫
      targetPairsFst G)
    ((ObjectProperty.homMk (pullback.snd (targetPairsSnd G).hom (targetPairsFst G).hom) :
        AlgebraicSpaces.fiberProduct C S hS (targetPairsSnd G) (targetPairsFst G) ⟶ _) ≫
      targetPairsSnd G) (by
    have h := (AlgebraicSpaces.isPullback_fiberProduct C S hS (targetPairsSnd G)
      (targetPairsFst G)).w
    rw [Category.assoc, targetPairsFst_comp_target, ← Category.assoc, h, Category.assoc,
      targetPairsFst_comp_target, Category.assoc])

/-- The first component of `pr₀₂((r₀, r₁), (r₁, r₂))` is `r₀`. -/
@[simp]
theorem targetPairsComp_fst :
    targetPairsComp G ≫ targetPairsFst G =
      (ObjectProperty.homMk (pullback.fst (targetPairsSnd G).hom (targetPairsFst G).hom) :
        AlgebraicSpaces.fiberProduct C S hS (targetPairsSnd G) (targetPairsFst G) ⟶ _) ≫
      targetPairsFst G :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target).lift_fst _ _ _

/-- The second component of `pr₀₂((r₀, r₁), (r₁, r₂))` is `r₂`. -/
@[simp]
theorem targetPairsComp_snd :
    targetPairsComp G ≫ targetPairsSnd G =
      (ObjectProperty.homMk (pullback.snd (targetPairsSnd G).hom (targetPairsFst G).hom) :
        AlgebraicSpaces.fiberProduct C S hS (targetPairsSnd G) (targetPairsFst G) ⟶ _) ≫
      targetPairsSnd G :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target).lift_snd _ _ _

section Pointwise

variable (T : (BigFppfOver C S hS)ᵒᵖ)

/-- The pair `(y, x)` of arrows with a common target, at a test object. -/
def targetPairsMk (y x : G.arrows.obj.obj T)
    (h : G.target.hom.app T y = G.target.hom.app T x) :
    (AlgebraicSpaces.fiberProduct C S hS G.target G.target).obj.obj T :=
  fibreProductMk G.target G.target T y x h

/-- A pair of arrows with a common target, read at a test object: its two components have the
same target. -/
theorem targetPairs_target_app
    (a : (AlgebraicSpaces.fiberProduct C S hS G.target G.target).obj.obj T) :
    G.target.hom.app T ((targetPairsFst G).hom.app T a) =
      G.target.hom.app T ((targetPairsSnd G).hom.app T a) :=
  natTrans_app_congr (congrArg (fun k => k.hom) (targetPairsFst_comp_target G)) T a

/-- The first component of the composite of a composable pair of pairs with a common target is
the first component of the first pair. -/
theorem targetPairsComp_app_fst
    (p : (Deformation.composableArrows _ _ (targetPairsSnd G).hom (targetPairsFst G).hom).obj T) :
    (targetPairsFst G).hom.app T ((composableToPullback (targetPairsSnd G).hom
        (targetPairsFst G).hom ≫ (targetPairsComp G).hom).app T p) =
      (targetPairsFst G).hom.app T p.1.1 :=
  (natTrans_app_congr (congrArg (fun k => k.hom) (targetPairsComp_fst G)) T _).trans
    (congrArg ((targetPairsFst G).hom.app T) (pullbackFst_app_composableToPullback _ _ T p))

/-- The second component of the composite of a composable pair of pairs with a common target is
the second component of the second pair. -/
theorem targetPairsComp_app_snd
    (p : (Deformation.composableArrows _ _ (targetPairsSnd G).hom (targetPairsFst G).hom).obj T) :
    (targetPairsSnd G).hom.app T ((composableToPullback (targetPairsSnd G).hom
        (targetPairsFst G).hom ≫ (targetPairsComp G).hom).app T p) =
      (targetPairsSnd G).hom.app T p.1.2 :=
  (natTrans_app_congr (congrArg (fun k => k.hom) (targetPairsComp_snd G)) T _).trans
    (congrArg ((targetPairsSnd G).hom.app T) (pullbackSnd_app_composableToPullback _ _ T p))

/-- The groupoid structure on the points of `R` over a test object in which there is exactly one
arrow from `x` to `y` when `x` and `y` have the same target, and none otherwise: the groupoid
induced from the discrete groupoid on the points of `U` along the target. -/
abbrev targetPairsIndex (x : G.arrows.obj.obj T) : Discrete (G.objects.obj.obj T) :=
  Discrete.mk (G.target.hom.app T x)

/-- The arrows from `x` to `y` of the indexing groupoid are the pairs `(y, x)` with a common
target. -/
def targetPairsArrowEquiv (x y : G.arrows.obj.obj T) :
    (targetPairsIndex G T x ⟶ targetPairsIndex G T y) ≃
      { a : (AlgebraicSpaces.fiberProduct C S hS G.target G.target).obj.obj T //
        (targetPairsSnd G).hom.app T a = x ∧ (targetPairsFst G).hom.app T a = y } where
  toFun h := ⟨targetPairsMk G T y x (Discrete.eq_of_hom h).symm,
    fibreProductMk_snd _ _ _ _ _ _, fibreProductMk_fst _ _ _ _ _ _⟩
  invFun a := Discrete.eqToHom (by
    obtain ⟨a, rfl, rfl⟩ := a
    exact (targetPairs_target_app G T a).symm)
  left_inv _ := Subsingleton.elim _ _
  right_inv a := Subtype.ext (fibreProduct_ext G.target G.target T
    ((fibreProductMk_fst _ _ _ _ _ _).trans a.2.2.symm)
    ((fibreProductMk_snd _ _ _ _ _ _).trans a.2.1.symm))

/-- The groupoid of pairs with a common target, at a test object. -/
def targetPairsPointwise :
    Deformation.PointwiseGroupoid ((targetPairsSnd G).hom.app T) ((targetPairsFst G).hom.app T)
      (fun p => (composableToPullback (targetPairsSnd G).hom (targetPairsFst G).hom ≫
        (targetPairsComp G).hom).app T p) :=
  letI : Groupoid (Discrete (G.objects.obj.obj T)) := Groupoid.ofIsGroupoid
  Deformation.PointwiseGroupoid.ofIndexing (targetPairsIndex G T)
    ((targetPairsSnd G).hom.app T) ((targetPairsFst G).hom.app T)
    (fun p => (composableToPullback (targetPairsSnd G).hom (targetPairsFst G).hom ≫
      (targetPairsComp G).hom).app T p)
    (targetPairsArrowEquiv G T)
    (fun x y z g f => by
      refine fibreProduct_ext G.target G.target T ?_ ?_
      · refine (fibreProductMk_fst _ _ _ _ _ _).trans (Eq.symm ?_)
        refine (targetPairsComp_app_fst G T _).trans ?_
        exact fibreProductMk_fst G.target G.target T z y _
      · refine (fibreProductMk_snd _ _ _ _ _ _).trans (Eq.symm ?_)
        refine (targetPairsComp_app_snd G T _).trans ?_
        exact fibreProductMk_snd G.target G.target T y x _)

end Pointwise

/-- **The groupoid of pairs of arrows with a common target**: the groupoid in algebraic spaces
`(R, R ×_{t, U, t} R, pr₁, pr₀, pr₀₂)` over `B` attached to a groupoid `(U, R, s, t, c)` over
`B`, in which an arrow `(r₀, r₁)` goes from `r₁` to `r₀`. -/
abbrev targetPairsGroupoid : GroupoidInAlgebraicSpaces C S hS B where
  objects := G.arrows
  arrows := AlgebraicSpaces.fiberProduct C S hS G.target G.target
  objectsToBase := G.arrowsToBase
  arrowsToBase := targetPairsFst G ≫ G.arrowsToBase
  source := targetPairsSnd G
  target := targetPairsFst G
  source_over := by
    rw [← G.target_over, ← Category.assoc, ← targetPairsFst_comp_target, Category.assoc]
  target_over := rfl
  comp := targetPairsComp G
  comp_over := by rw [← Category.assoc, targetPairsComp_fst, Category.assoc]
  pointwiseGroupoid T := ⟨targetPairsPointwise G T⟩

/-- The objects of the groupoid of pairs with a common target are the arrows `R`. -/
@[simp] theorem targetPairsGroupoid_objects : (targetPairsGroupoid G).objects = G.arrows := rfl

/-- The arrows of the groupoid of pairs with a common target are `R ×_{t, U, t} R`. -/
@[simp] theorem targetPairsGroupoid_arrows :
    (targetPairsGroupoid G).arrows = AlgebraicSpaces.fiberProduct C S hS G.target G.target := rfl

/-- The source map of the groupoid of pairs with a common target is `pr₁`. -/
@[simp] theorem targetPairsGroupoid_source :
    (targetPairsGroupoid G).source = targetPairsSnd G := rfl

/-- The target map of the groupoid of pairs with a common target is `pr₀`. -/
@[simp] theorem targetPairsGroupoid_target :
    (targetPairsGroupoid G).target = targetPairsFst G := rfl

/-- The composition of the groupoid of pairs with a common target is `pr₀₂`. -/
@[simp] theorem targetPairsGroupoid_comp : (targetPairsGroupoid G).comp = targetPairsComp G := rfl

/-! ### The morphism to the given groupoid -/

/-- The map `R ×_{t, U, t} R ⟶ R`, `(r₀, r₁) ↦ r₀⁻¹ ∘ r₁`: the second arrow of the composable
pair `(r₀, r₀⁻¹ ∘ r₁)` that **Stacks 0450** attaches to a pair with a common target. -/
def targetPairsArrowsMap : AlgebraicSpaces.fiberProduct C S hS G.target G.target ⟶ G.arrows :=
  (commonTargetPairsIso G).hom ≫
    ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom)

/-- `r₀⁻¹ ∘ r₁` has the target of `r₀⁻¹`, which is the source of `r₀`. -/
theorem targetPairsArrowsMap_comp_target :
    targetPairsArrowsMap G ≫ G.target = targetPairsFst G ≫ G.source := by
  rw [targetPairsArrowsMap, Category.assoc,
    ← (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).w, ← Category.assoc,
    commonTargetPairsIso_hom_fst]

/-- `r₀⁻¹ ∘ r₁` has the source of `r₁`. -/
theorem targetPairsArrowsMap_comp_source :
    targetPairsArrowsMap G ≫ G.source = targetPairsSnd G ≫ G.source := by
  rw [targetPairsArrowsMap, Category.assoc, ← comp_source_eq_snd_source, ← Category.assoc,
    commonTargetPairsIso_hom_comp]

/-- `r₀⁻¹ ∘ r₁` has the target of `r₀⁻¹`, which is the source of `r₀`, on presheaves. -/
theorem targetPairsArrowsMap_hom_comp_target :
    (targetPairsArrowsMap G).hom ≫ G.target.hom = (targetPairsFst G).hom ≫ G.source.hom :=
  congrArg (fun k => k.hom) (targetPairsArrowsMap_comp_target G)

/-- `r₀⁻¹ ∘ r₁` has the source of `r₁`, on presheaves. -/
theorem targetPairsArrowsMap_hom_comp_source :
    (targetPairsArrowsMap G).hom ≫ G.source.hom = (targetPairsSnd G).hom ≫ G.source.hom :=
  congrArg (fun k => k.hom) (targetPairsArrowsMap_comp_source G)

/-- The pair `(r₀, r₀⁻¹ ∘ r₁)` attached to a pair with a common target, on presheaves: it is
the lift of the first projection and of `r₀⁻¹ ∘ r₁`. -/
theorem commonTargetPairsIso_hom_hom :
    (commonTargetPairsIso G).hom.hom =
      pullback.lift (targetPairsFst G).hom (targetPairsArrowsMap G).hom
        (congrArg (fun k => k.hom) (targetPairsArrowsMap_comp_target G)).symm := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact congrArg (fun k => k.hom) (commonTargetPairsIso_hom_fst G)
  · rw [pullback.lift_snd]
    rfl

/-- `r₀ ∘ (r₀⁻¹ ∘ r₁) = r₁`, as an identity of generalized arrows. -/
theorem groupoidCompose_targetPairsArrowsMap :
    groupoidCompose G (targetPairsFst G).hom (targetPairsArrowsMap G).hom
        (congrArg (fun k => k.hom) (targetPairsArrowsMap_comp_target G)).symm =
      (targetPairsSnd G).hom := by
  rw [groupoidCompose_eq_comp, ← commonTargetPairsIso_hom_hom]
  exact congrArg (fun k => k.hom) (commonTargetPairsIso_hom_comp G)

/-- **Left cancellation of generalized arrows**: two generalized arrows which become equal after
composing with a common arrow on the left are equal. -/
theorem groupoidCompose_left_cancel {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a x y : T ⟶ G.arrows.obj) (wx : a ≫ G.source.hom = x ≫ G.target.hom)
    (wy : a ≫ G.source.hom = y ≫ G.target.hom)
    (h : groupoidCompose G a x wx = groupoidCompose G a y wy) : x = y := by
  have wi : (a ≫ groupoidInverse G) ≫ G.source.hom = a ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]
  have key : ∀ (z : T ⟶ G.arrows.obj) (wz : a ≫ G.source.hom = z ≫ G.target.hom),
      groupoidCompose G (a ≫ groupoidInverse G) (groupoidCompose G a z wz)
        (by rwa [groupoidCompose_target]) = z := by
    intro z wz
    have wL : groupoidCompose G (a ≫ groupoidInverse G) a wi ≫ G.source.hom =
        z ≫ G.target.hom := by
      rwa [groupoidCompose_source]
    rw [← groupoidCompose_assoc G (a ≫ groupoidInverse G) a z wi wz wL]
    have hz : identityAfterTarget G z = groupoidCompose G (a ≫ groupoidInverse G) a wi := by
      rw [groupoidCompose_inverseRight, identityAfterTarget, identityAfterSource,
        ← Category.assoc, ← wz, Category.assoc]
    rw [← groupoidCompose_congr G (identityAfterTarget_composable G z) wL hz rfl,
      groupoidCompose_leftIdentity]
  rw [← key x wx, ← key y wy]
  exact groupoidCompose_congr G _ _ rfl h

/-- `r₀` and `r₀⁻¹ ∘ r₁` are composable, after precomposition with any generalized pair `q`. -/
private theorem targetPairsArrowsMap_pre_composable {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (q : T ⟶ (AlgebraicSpaces.fiberProduct C S hS G.target G.target).obj) :
    (q ≫ (targetPairsFst G).hom) ≫ G.source.hom =
      (q ≫ (targetPairsArrowsMap G).hom) ≫ G.target.hom := by
  rw [Category.assoc, Category.assoc, targetPairsArrowsMap_hom_comp_target]

/-- `r₀ ∘ (r₀⁻¹ ∘ r₁) = r₁` after precomposition with any generalized pair `q`. -/
private theorem groupoidCompose_pre_targetPairsArrowsMap {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (q : T ⟶ (AlgebraicSpaces.fiberProduct C S hS G.target G.target).obj) :
    groupoidCompose G (q ≫ (targetPairsFst G).hom) (q ≫ (targetPairsArrowsMap G).hom)
        (targetPairsArrowsMap_pre_composable G q) = q ≫ (targetPairsSnd G).hom := by
  rw [← groupoidCompose_targetPairsArrowsMap G, groupoidCompose_pre]

/-- `r₀⁻¹ ∘ r₁` is characterized by `r₀ ∘ (r₀⁻¹ ∘ r₁) = r₁`: a generalized arrow `ρ` composable
after `r₀` with composite `r₁` is `r₀⁻¹ ∘ r₁`. -/
theorem eq_targetPairsArrowsMap {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (p : T ⟶ (AlgebraicSpaces.fiberProduct C S hS G.target G.target).obj)
    (ρ : T ⟶ G.arrows.obj) (w : p ≫ (targetPairsFst G).hom ≫ G.source.hom = ρ ≫ G.target.hom)
    (h : groupoidCompose G (p ≫ (targetPairsFst G).hom) ρ (by rw [Category.assoc]; exact w) =
      p ≫ (targetPairsSnd G).hom) :
    ρ = p ≫ (targetPairsArrowsMap G).hom := by
  exact groupoidCompose_left_cancel G (p ≫ (targetPairsFst G).hom) _ _
    (by rwa [Category.assoc]) (targetPairsArrowsMap_pre_composable G p)
    (h.trans (groupoidCompose_pre_targetPairsArrowsMap G p).symm)

/-- The first pair of a composable pair of pairs with a common target. -/
abbrev targetPairsComposableFst :
    AlgebraicSpaces.fiberProduct C S hS (targetPairsSnd G) (targetPairsFst G) ⟶
      AlgebraicSpaces.fiberProduct C S hS G.target G.target :=
  ObjectProperty.homMk (pullback.fst (targetPairsSnd G).hom (targetPairsFst G).hom)

/-- The second pair of a composable pair of pairs with a common target. -/
abbrev targetPairsComposableSnd :
    AlgebraicSpaces.fiberProduct C S hS (targetPairsSnd G) (targetPairsFst G) ⟶
      AlgebraicSpaces.fiberProduct C S hS G.target G.target :=
  ObjectProperty.homMk (pullback.snd (targetPairsSnd G).hom (targetPairsFst G).hom)

/-- In a composable pair `((r₀, r₁), (r₁', r₂))` of pairs with a common target, `r₁ = r₁'`. -/
theorem targetPairsComposable_condition :
    (targetPairsComposableFst G).hom ≫ (targetPairsSnd G).hom =
      (targetPairsComposableSnd G).hom ≫ (targetPairsFst G).hom :=
  pullback.condition

/-- For a composable pair `((r₀, r₁), (r₁, r₂))` of pairs with a common target, the arrows
`r₀⁻¹ ∘ r₁` and `r₁⁻¹ ∘ r₂` are composable. -/
theorem targetPairsComposable_arrowsMap_composable :
    ((targetPairsComposableFst G).hom ≫ (targetPairsArrowsMap G).hom) ≫ G.source.hom =
      ((targetPairsComposableSnd G).hom ≫ (targetPairsArrowsMap G).hom) ≫ G.target.hom := by
  rw [Category.assoc, Category.assoc, targetPairsArrowsMap_hom_comp_source,
    targetPairsArrowsMap_hom_comp_target, ← Category.assoc, ← Category.assoc,
    targetPairsComposable_condition]

/-- The composite `(r₀⁻¹ ∘ r₁) ∘ (r₁⁻¹ ∘ r₂)` is `r₀⁻¹ ∘ r₂`, on the composable pairs of pairs
with a common target. -/
theorem groupoidCompose_targetPairsArrowsMap_comp :
    groupoidCompose G ((targetPairsComposableFst G).hom ≫ (targetPairsArrowsMap G).hom)
        ((targetPairsComposableSnd G).hom ≫ (targetPairsArrowsMap G).hom)
        (targetPairsComposable_arrowsMap_composable G) =
      (targetPairsComp G).hom ≫ (targetPairsArrowsMap G).hom := by
  have hf₀ : (targetPairsComp G).hom ≫ (targetPairsFst G).hom =
      (targetPairsComposableFst G).hom ≫ (targetPairsFst G).hom :=
    congrArg (fun k => k.hom) (targetPairsComp_fst G)
  have hf₁ : (targetPairsComp G).hom ≫ (targetPairsSnd G).hom =
      (targetPairsComposableSnd G).hom ≫ (targetPairsSnd G).hom :=
    congrArg (fun k => k.hom) (targetPairsComp_snd G)
  have ht := targetPairsArrowsMap_hom_comp_target G
  have hc := targetPairsComposable_condition G
  refine eq_targetPairsArrowsMap G (targetPairsComp G).hom _ ?_ ?_
  · rw [groupoidCompose_target, ← Category.assoc, hf₀, Category.assoc, Category.assoc, ht]
  · have w₁ := targetPairsArrowsMap_pre_composable G (targetPairsComposableFst G).hom
    have w₂ : ((targetPairsComposableFst G).hom ≫ (targetPairsSnd G).hom) ≫ G.source.hom =
        ((targetPairsComposableSnd G).hom ≫ (targetPairsArrowsMap G).hom) ≫ G.target.hom := by
      rw [Category.assoc, Category.assoc, ht, ← Category.assoc, ← Category.assoc, hc]
    have h₁ : groupoidCompose G ((targetPairsComposableFst G).hom ≫ (targetPairsFst G).hom)
        ((targetPairsComposableFst G).hom ≫ (targetPairsArrowsMap G).hom) w₁ =
        (targetPairsComposableFst G).hom ≫ (targetPairsSnd G).hom :=
      groupoidCompose_pre_targetPairsArrowsMap G _
    have h₂ : groupoidCompose G ((targetPairsComposableFst G).hom ≫ (targetPairsSnd G).hom)
        ((targetPairsComposableSnd G).hom ≫ (targetPairsArrowsMap G).hom) w₂ =
        (targetPairsComposableSnd G).hom ≫ (targetPairsSnd G).hom := by
      rw [groupoidCompose_congr G w₂ (targetPairsArrowsMap_pre_composable G _) hc rfl]
      exact groupoidCompose_pre_targetPairsArrowsMap G _
    have wL : groupoidCompose G ((targetPairsComposableFst G).hom ≫ (targetPairsFst G).hom)
        ((targetPairsComposableFst G).hom ≫ (targetPairsArrowsMap G).hom) w₁ ≫ G.source.hom =
        ((targetPairsComposableSnd G).hom ≫ (targetPairsArrowsMap G).hom) ≫ G.target.hom := by
      rwa [h₁]
    rw [hf₁, ← h₂, groupoidCompose_congr G _ (by rwa [groupoidCompose_target]) hf₀ rfl,
      ← groupoidCompose_assoc G _ _ _ w₁ _ wL]
    exact groupoidCompose_congr G _ _ h₁ rfl

/-- The map `(r₀, r₁) ↦ r₀⁻¹ ∘ r₁` is a morphism over the base. -/
theorem targetPairsArrowsMap_comp_arrowsToBase :
    targetPairsArrowsMap G ≫ G.arrowsToBase = targetPairsFst G ≫ G.arrowsToBase :=
  calc targetPairsArrowsMap G ≫ G.arrowsToBase
      = (targetPairsArrowsMap G ≫ G.target) ≫ G.objectsToBase := by
        rw [Category.assoc, G.target_over]
    _ = targetPairsFst G ≫ G.arrowsToBase := by
        rw [targetPairsArrowsMap_comp_target, Category.assoc, G.source_over]

/-- The map `(r₀, r₁) ↦ r₀⁻¹ ∘ r₁` respects composition, at a test object. -/
theorem targetPairsArrowsMap_map_comp (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (targetPairsGroupoid G).arrows.obj.obj T)
    (h : (targetPairsGroupoid G).source.hom.app T a =
      (targetPairsGroupoid G).target.hom.app T b)
    (h' : G.source.hom.app T ((targetPairsArrowsMap G).hom.app T a) =
      G.target.hom.app T ((targetPairsArrowsMap G).hom.app T b)) :
    G.toGroupoidInFunctors.compose T ((targetPairsArrowsMap G).hom.app T a)
        ((targetPairsArrowsMap G).hom.app T b) h' =
      (targetPairsArrowsMap G).hom.app T
        ((targetPairsGroupoid G).toGroupoidInFunctors.compose T a b h) := by
  let z := (composableToPullback (targetPairsSnd G).hom (targetPairsFst G).hom).app T ⟨(a, b), h⟩
  have h₁ : (targetPairsComposableFst G).hom.app T z = a :=
    pullbackFst_app_composableToPullback _ _ T _
  have h₂ : (targetPairsComposableSnd G).hom.app T z = b :=
    pullbackSnd_app_composableToPullback _ _ T _
  have key := natTrans_app_congr (groupoidCompose_targetPairsArrowsMap_comp G) T z
  have hev := groupoidCompose_eval G _ _ (targetPairsComposable_arrowsMap_composable G) T z
  refine Eq.trans ?_ (hev.symm.trans key)
  exact Deformation.GroupoidInFunctors.compose_congr G.toGroupoidInFunctors T _ _
    (congrArg ((targetPairsArrowsMap G).hom.app T) h₁).symm
    (congrArg ((targetPairsArrowsMap G).hom.app T) h₂).symm

/-- **The morphism `f : (R, R ×_{t, U, t} R, pr₁, pr₀, pr₀₂) ⟶ (U, R, s, t, c)` of the proof of
Stacks 0GPP**: the source `s : R ⟶ U` on objects and `(r₀, r₁) ↦ r₀⁻¹ ∘ r₁` on arrows. -/
def targetPairsHom : Hom (targetPairsGroupoid G) G :=
  Hom.mk' G.source.hom (targetPairsArrowsMap G).hom
    (fun T a => natTrans_app_congr (targetPairsArrowsMap_hom_comp_source G) T a)
    (fun T a => natTrans_app_congr (targetPairsArrowsMap_hom_comp_target G) T a)
    (fun T a b h => targetPairsArrowsMap_map_comp G T a b h _)
    (congrArg (fun k => k.hom) G.source_over)
    (congrArg (fun k => k.hom) (targetPairsArrowsMap_comp_arrowsToBase G))

/-- On objects, `targetPairsHom` is the source `s : R ⟶ U`. -/
@[simp]
theorem targetPairsHom_objectsMap : (targetPairsHom G).objectsMap = G.source :=
  ObjectProperty.hom_ext _ rfl

/-- On arrows, `targetPairsHom` is `(r₀, r₁) ↦ r₀⁻¹ ∘ r₁`. -/
@[simp]
theorem targetPairsHom_arrowsMap : (targetPairsHom G).arrowsMap = targetPairsArrowsMap G :=
  ObjectProperty.hom_ext _ rfl

/-- **The cartesian square of the proof of Stacks 0GPP**:

```
R ×_{t, U, t} R --(r₀, r₁) ↦ r₀⁻¹ ∘ r₁--> R
      | pr₀                                | t
      v                                    v
      R ----------------- s -------------> U
```

It is the defining square of `R ×_{s, U, t} R` read through the comparison of **Stacks 0450**
with the pairs with a common target. -/
theorem isPullback_targetPairsArrowsMap :
    IsPullback (targetPairsArrowsMap G) (targetPairsFst G) G.target G.source := by
  refine IsPullback.flip ?_
  refine (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).of_iso
    (commonTargetPairsIso G).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp,
      commonTargetPairsIso_hom_fst]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp]
    rfl
  · simp
  · simp

/-- The square of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_targetPairsArrowsMap`,
stated for the morphism `AlgebraicGeometry.GroupoidInAlgebraicSpaces.targetPairsHom`. -/
theorem isPullback_targetPairsHom :
    IsPullback (targetPairsHom G).arrowsMap (targetPairsGroupoid G).target G.target
      (targetPairsHom G).objectsMap := by
  rw [targetPairsHom_arrowsMap, targetPairsHom_objectsMap, targetPairsGroupoid_target]
  exact isPullback_targetPairsArrowsMap G

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
