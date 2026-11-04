module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystemOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LimitDescriptionIsomorphism

/-!
# Stacks 0CPF with no bound on the index type

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces with
affine transition morphisms (Situation 0CP6), and let `X₁ = X₂ ×_{X₄} X₃` be a cartesian square
of algebraic spaces over `B`, quasi-separated over `B`. Choosing diagrams as in Stacks 0CP8 for
the four spaces gives limit descriptions `X_j = lim_i X^j_i` (Stacks 0CP9), and the four
morphisms of the square descend to morphisms of these inverse systems (Stacks 0CPA). Stacks 0CPF
asserts that at every late stage the descended square commutes, that the comparison morphism
`X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` is a closed immersion, and that it is an isomorphism when `a` is flat
and of finite presentation. Here no bound is put on the size of the index type.

## Main definitions

* `AlgebraicGeometry.Space.GoodDiagram.cartesianDiagramOfAlgebraicLimit`: the diagram of
  Stacks 0CP8 for `X₁` whose model is the fibre product `X²_k ×_{X⁴_k} X³_k` of the stages.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_forall_app_eq_of_algebraicLimit`:
  two morphisms of image systems inducing the same morphism agree at every late stage.
* `AlgebraicGeometry.Space.GoodDiagram.exists_isClosedImmersion_lift_of_algebraicLimit`: the
  descended square eventually commutes and its comparison morphisms are closed immersions.
* `AlgebraicGeometry.Space.GoodDiagram.isIso_lift_of_isFlat_of_algebraicLimit`: at a stage
  where `a_i` is flat and `X₃ = X₄ ×_{X⁴_i} X³_i`, a closed comparison morphism is an
  isomorphism.
* `AlgebraicGeometry.Space.GoodDiagram.exists_isClosedImmersion_lift_and_isIso_of_algebraicLimit`:
  **Stacks 0CPF**.

## Implementation notes

The argument is the one of
`AlgebraicGeometry.Space.GoodDiagram.exists_isClosedImmersion_lift_and_isIso`, which carries the
bound `#I < B.cutoff.ord.cof`: the closed immersion is obtained for the cartesian diagram and
transported to the given diagram of `X₁` along the eventual isomorphism of limit descriptions of
Stacks 0CPB, and the isomorphism follows from Stacks 0CPC for `a` and Stacks 089E. Its bounded
ingredients are replaced by their forms with no bound on the index type: Stacks 0CPA and 0CPB
(`AlgebraicGeometry.Space.GoodDiagram.eventually_eq_systemMorphism_of_algebraicLimit`,
`AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_systemMorphism_inv_of_algebraicLimit`),
Stacks 0CPC
(`AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isFlat_isPullback_of_algebraicLimit`),
the quasi-separatedness of the members of an image system, and the quasi-compactness of its
stage maps. As in the bounded form, only `a` needs to be flat and of finite presentation; the
source assumes this of `a` and `b`.

## References

* [Stacks Project, Tag 0CPF](https://stacks.math.columbia.edu/tag/0CPF)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
* [Stacks Project, Tag 0CPB](https://stacks.math.columbia.edu/tag/0CPB)
* [Stacks Project, Tag 0CPC](https://stacks.math.columbia.edu/tag/0CPC)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}

namespace SystemMorphism

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
    {pY : Y ⟶ D.limitCone.pt} {GX : GoodDiagram B S hS hZ D pX}
    {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y} {i₀ i₁ : I} {hiX : GX.index ≤ i₀}
    {hiY : GY.index ≤ i₀} {hiX' : GX.index ≤ i₁} {hiY' : GY.index ≤ i₁}

/-- **Stacks 0CPA, eventual uniqueness, stagewise**, for an index set of any size. Two morphisms
of image systems inducing the same morphism, defined on tails above possibly different stages,
have the same component at every sufficiently late stage. -/
theorem exists_forall_app_eq_of_algebraicLimit (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX) (F : SystemMorphism GX GY f i₀ hiX hiY)
    (F' : SystemMorphism GX GY f i₁ hiX' hiY') :
    ∃ (i₃ : I) (h₀ : i₀ ≤ i₃) (h₁ : i₁ ≤ i₃), ∀ (i : I) (h : i₃ ≤ i),
      F.app i (h₀.trans h) = F'.app i (h₁.trans h) := by
  obtain ⟨m, hm₀, hm₁⟩ := exists_ge_ge i₀ i₁
  obtain ⟨i₃, hm, hi₃⟩ := eventually_eq_systemMorphism_of_algebraicLimit hX hXqs
    (F.restrict hm₀) (F'.restrict hm₁)
  exact ⟨i₃, hm₀.trans hm, hm₁.trans hm, fun i h =>
    hi₃ (Over.mk (homOfLE (hm.trans h)).op) h⟩

end SystemMorphism

/-! ### The cartesian diagram -/

section Cartesian

variable {X₁ X₂ X₃ X₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX₁ : X₁ ⟶ D.limitCone.pt}
    {pX₂ : X₂ ⟶ D.limitCone.pt} {pX₃ : X₃ ⟶ D.limitCone.pt} {pX₄ : X₄ ⟶ D.limitCone.pt}
    {G₂ : GoodDiagram B S hS hZ D pX₂} {G₃ : GoodDiagram B S hS hZ D pX₃}
    {G₄ : GoodDiagram B S hS hZ D pX₄} {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄}
    {b : X₂ ⟶ X₄} {i₅ i₆ : I} {h₃₅ : G₃.index ≤ i₅} {h₄₅ : G₄.index ≤ i₅}
    {h₂₆ : G₂.index ≤ i₆} {h₄₆ : G₄.index ≤ i₆}

/-- If `X₁ = X₂ ×_{X₄} X₃` is cartesian over `B`, then `p` lies over `B` as `X₃` does. -/
private theorem comp_eq_of_isPullback (hcart : IsPullback p q a b) (ha : a ≫ pX₄ = pX₃)
    (hb : b ≫ pX₄ = pX₂) (hq : q ≫ pX₂ = pX₁) : p ≫ pX₃ = pX₁ := by
  rw [← ha, ← Category.assoc, hcart.w, Category.assoc, hb, hq]

/-- The model `X²_k ×_{X⁴_k} X³_k ⟶ B_k` of the cartesian diagram is of finite type, for an index
set of any size. -/
theorem isFiniteType_cartesianModelMap_of_algebraicLimit (alg₄ : IsAlgebraicSpace B S hS X₄)
    (qs₄ : IsQuasiSeparated B S hS pX₄)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I)
    (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    IsFiniteType B S hS (cartesianModelMap Fa Fb k h₅ h₆) := by
  have alg₂ := imageSystem_isAlgebraicSpace G₂ (Over.mk (homOfLE (h₂₆.trans h₆)).op)
  have alg₃ := imageSystem_isAlgebraicSpace G₃ (Over.mk (homOfLE (h₃₅.trans h₅)).op)
  have alg₄k := imageSystem_isAlgebraicSpace G₄ (Over.mk (homOfLE (h₄₅.trans h₅)).op)
  have algB := D.system_isAlgebraicSpace k
  have algT := isAlgebraicSpace_pullback B S hS (Fb.app k h₆) (Fa.app k h₅) alg₂ alg₃ alg₄k
  have lft (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pY' : Y' ⟶ D.limitCone.pt)
      (G' : GoodDiagram B S hS hZ D pY') (i : I) (h : G'.index ≤ i) :
      IsLocallyOfFiniteType B S hS
        ((stageImage G' (Over.mk (homOfLE h).op)).ι ≫ pullback.fst _ _) :=
    isLocallyOfFiniteType_comp B S hS (imageSystem_isAlgebraicSpace G' _)
      (isAlgebraicSpace_stageTarget G' _) (D.system_isAlgebraicSpace i) _ _
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS _
        (isClosedSubspace_stageImage G' _).2)
      (isLocallyOfFiniteType_stageTarget_fst G' _)
  have lftA : IsLocallyOfFiniteType B S hS (Fa.app k h₅) := by
    refine isLocallyOfFiniteType_of_comp B S hS alg₃ alg₄k algB _
      ((stageImage G₄ (Over.mk (homOfLE (h₄₅.trans h₅)).op)).ι ≫ pullback.fst _ _) ?_
    rw [Fa.app_over_base]
    exact lft _ _ G₃ k _
  constructor
  · exact isLocallyOfFiniteType_comp B S hS algT alg₂ algB _ _
      (isLocallyOfFiniteType_pullback_fst' B S hS alg₃ alg₄k alg₂ _ _ lftA) (lft _ _ G₂ k _)
  · have qcT : IsQuasiCompactSpace B S hS (pullback (Fb.app k h₆) (Fa.app k h₅)) :=
      isQuasiCompactSpace_pullback B S hS hZ _ _ alg₂ alg₄k
        (imageSystem_isQuasiCompactSpace G₂ _) (imageSystem_isQuasiCompactSpace G₃ _)
        (imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit G₄ alg₄
          qs₄ _)
    exact isQuasiCompact_of_isQuasiCompactSpace B S hS hZ algB (D.noetherian k).2.1 qcT _

/-- **The good diagram of a cartesian square with model the fibre product of the stages**, for an
index set of any size. For a cartesian square `X₁ = X₂ ×_{X₄} X₃` over `B` and a stage `k` at
which the morphisms `a_k` and `b_k` of image systems are defined, the diagram
`X₁ ⟶ X²_k ×_{X⁴_k} X³_k ⟶ B_k`. -/
noncomputable abbrev cartesianDiagramOfAlgebraicLimit (alg₄ : IsAlgebraicSpace B S hS X₄)
    (qs₄ : IsQuasiSeparated B S hS pX₄) (hcart : IsPullback p q a b) (ha : a ≫ pX₄ = pX₃)
    (hb : b ≫ pX₄ = pX₂) (hq : q ≫ pX₂ = pX₁)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I)
    (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) : GoodDiagram B S hS hZ D pX₁ where
  index := k
  model := cartesianModel Fa Fb k h₅ h₆
  model_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS _ _
    (imageSystem_isAlgebraicSpace G₂ _) (imageSystem_isAlgebraicSpace G₃ _)
    (imageSystem_isAlgebraicSpace G₄ _)
  modelMap := cartesianModelMap Fa Fb k h₅ h₆
  toModel := pullback.lift (q ≫ stageπ G₂ k (h₂₆.trans h₆)) (p ≫ stageπ G₃ k (h₃₅.trans h₅))
    (by rw [Category.assoc, Category.assoc, Fb.stageπ_app, Fa.stageπ_app, ← Category.assoc,
      ← Category.assoc, hcart.w])
  commutes := by
    rw [pullback.lift_fst_assoc, Category.assoc, stageπ_ι_fst, ← Category.assoc, hq]
  isFiniteType := isFiniteType_cartesianModelMap_of_algebraicLimit alg₄ qs₄ Fa Fb k h₅ h₆
  isClosedImmersion := by
    have hp : p ≫ pX₃ = pX₁ := by rw [← ha, ← Category.assoc, hcart.w, Category.assoc, hb, hq]
    refine isClosedImmersion_of_comp_mono B S hS _ (cartesianComparison Fa Fb k h₅ h₆) ?_
    convert isClosedImmersion_lift_toStageBaseChange hcart ha hb Fa Fb k h₅ h₆ using 1
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, cartesianComparison_fst_fst, pullback.lift_fst,
        toStageBaseChange_fst, hq]
    · simp only [Category.assoc, cartesianComparison_fst_snd, pullback.lift_snd_assoc,
        pullback.lift_fst, toStageBaseChange_snd]
    · simp only [Category.assoc, cartesianComparison_snd_fst, pullback.lift_fst,
        pullback.lift_snd_assoc, toStageBaseChange_fst, hp]
    · simp only [Category.assoc, cartesianComparison_snd_snd, pullback.lift_snd_assoc,
        pullback.lift_snd, toStageBaseChange_snd]

/-- **The cartesian square of the image systems of the cartesian good diagram**, for an index set
of any size. The two
projections of `X²_k ×_{X⁴_k} X³_k` induce morphisms `q'` and `p'` from the image system of the
cartesian good diagram to those of `G₂` and `G₃`, inducing `q` and `p`; at every stage
`i ≥ k` they satisfy `b_i ∘ q'_i = a_i ∘ p'_i`, and `(q'_i, p'_i)` is a closed immersion into
`X²_i ×_{X⁴_i} X³_i`. -/
theorem exists_isClosedImmersion_cartesianDiagram_of_algebraicLimit
    (alg₄ : IsAlgebraicSpace B S hS X₄) (qs₄ : IsQuasiSeparated B S hS pX₄)
    (hcart : IsPullback p q a b) (ha : a ≫ pX₄ = pX₃) (hb : b ≫ pX₄ = pX₂)
    (hq : q ≫ pX₂ = pX₁)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I)
    (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    ∃ (Q : SystemMorphism
        (cartesianDiagramOfAlgebraicLimit alg₄ qs₄ hcart ha hb hq Fa Fb k h₅ h₆) G₂ q k le_rfl
        (h₂₆.trans h₆))
      (P : SystemMorphism
        (cartesianDiagramOfAlgebraicLimit alg₄ qs₄ hcart ha hb hq Fa Fb k h₅ h₆) G₃ p k le_rfl
        (h₃₅.trans h₅))
      (comm : ∀ (i : I) (h : k ≤ i),
        Q.app i h ≫ Fb.app i (h₆.trans h) = P.app i h ≫ Fa.app i (h₅.trans h)),
      ∀ (i : I) (h : k ≤ i), IsClosedImmersion B S hS (pullback.lift _ _ (comm i h)) := by
  have hp := comp_eq_of_isPullback hcart ha hb hq
  set G := cartesianDiagramOfAlgebraicLimit alg₄ qs₄ hcart ha hb hq Fa Fb k h₅ h₆ with hG
  -- the inclusion of the base stage of `G` into `X²_k ×_{X⁴_k} X³_k`
  let ι₀ : stageAt G k le_rfl ⟶ cartesianModel Fa Fb k h₅ h₆ :=
    (stageImage G (Over.mk (homOfLE (le_refl k)).op)).ι ≫ pullback.snd _ _
  have ι₀_base : ι₀ ≫ cartesianModelMap Fa Fb k h₅ h₆ =
      (stageImage G (Over.mk (homOfLE (le_refl k)).op)).ι ≫ pullback.fst _ _ := by
    have hc := pullback.condition
      (f := D.system.map (Over.mk (homOfLE (le_refl k)).op).hom) (g := G.modelMap)
    have hid : D.system.map (Over.mk (homOfLE (le_refl k)).op).hom = 𝟙 _ :=
      (congrArg D.system.map (Subsingleton.elim _ (𝟙 (op k)))).trans (D.system.map_id _)
    exact (Category.assoc _ _ _).trans
      ((congrArg ((stageImage G (Over.mk (homOfLE (le_refl k)).op)).ι ≫ ·) hc.symm).trans
        ((congrArg (fun t => (stageImage G (Over.mk (homOfLE (le_refl k)).op)).ι ≫
          pullback.fst _ _ ≫ t) hid).trans (congrArg _ (Category.comp_id _))))
  have ι₀_lim : stageπ G k le_rfl ≫ ι₀ = G.toModel := stageπ_ι_snd G k le_rfl
  obtain ⟨Q, hQ⟩ := exists_systemMorphism_of_stage_hom (i₀ := k) G G₂ q hq le_rfl
    (h₂₆.trans h₆) (ι₀ ≫ pullback.fst _ _)
    (by rw [Category.assoc]; exact ι₀_base)
    (by rw [reassoc_of% ι₀_lim]; exact pullback.lift_fst _ _ _)
  obtain ⟨P, hP⟩ := exists_systemMorphism_of_stage_hom (i₀ := k) G G₃ p hp le_rfl
    (h₃₅.trans h₅) (ι₀ ≫ pullback.snd _ _)
    (by rw [Category.assoc, ← cartesian_fst_ι_fst]; exact ι₀_base)
    (by rw [reassoc_of% ι₀_lim]; exact pullback.lift_snd _ _ _)
  have comm : ∀ (i : I) (h : k ≤ i),
      Q.app i h ≫ Fb.app i (h₆.trans h) = P.app i h ≫ Fa.app i (h₅.trans h) := by
    intro i h
    refine stage_hom_ext G₄ (h₄₅.trans h₅) h ?_ ?_
    · rw [Category.assoc, Category.assoc, SystemMorphism.app_over_base,
        SystemMorphism.app_over_base, SystemMorphism.app_over_base,
        SystemMorphism.app_over_base]
    · rw [Category.assoc, Category.assoc, ← Fb.stageTransition_app h₆ h,
        ← Fa.stageTransition_app h₅ h, reassoc_of% hQ i h, reassoc_of% hP i h,
        Category.assoc, Category.assoc, pullback.condition]
  refine ⟨Q, P, comm, fun i h => ?_⟩
  -- the comparison of `X²_i ×_{X⁴_i} X³_i` with the base change of the model
  let κ : pullback (Fb.app i (h₆.trans h)) (Fa.app i (h₅.trans h)) ⟶
      pullback (D.system.map (Over.mk (homOfLE (le_refl k |>.trans h)).op).hom) G.modelMap :=
    pullback.lift
      (pullback.fst _ _ ≫ (stageImage G₂ (Over.mk (homOfLE ((h₂₆.trans h₆).trans h)).op)).ι ≫
        pullback.fst _ _)
      (pullback.lift (pullback.fst _ _ ≫ stageTransition G₂ (h₂₆.trans h₆) h)
        (pullback.snd _ _ ≫ stageTransition G₃ (h₃₅.trans h₅) h) (by
          rw [Category.assoc, Category.assoc, SystemMorphism.stageTransition_app,
            SystemMorphism.stageTransition_app, pullback.condition_assoc]))
      (by
        show _ = _ ≫ cartesianModelMap Fa Fb k h₅ h₆
        simp only [Category.assoc, pullback.lift_fst_assoc]
        rw [stageTransition_ι_fst]
        rfl)
  have hκ : Mono κ := ⟨fun u v huv => by
    have e₁ := congrArg (· ≫ pullback.fst _ _) huv
    have e₂ := congrArg (· ≫ pullback.snd _ _ ≫ pullback.fst _ _) huv
    have e₃ := congrArg (· ≫ pullback.snd _ _ ≫ pullback.snd _ _) huv
    simp only [κ, Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc,
      pullback.lift_snd] at e₁ e₂ e₃
    refine pullback.hom_ext (stage_hom_ext G₂ (h₂₆.trans h₆) h ?_ ?_)
      (stage_hom_ext G₃ (h₃₅.trans h₅) h ?_ ?_)
    · simpa only [Category.assoc] using e₁
    · simpa only [Category.assoc] using e₂
    · simp only [Category.assoc]
      rw [← cartesian_fst_ι_fst]
      simpa only [Category.assoc] using e₁
    · simpa only [Category.assoc] using e₃⟩
  refine isClosedImmersion_of_comp_mono B S hS _ κ ?_
  convert (isClosedSubspace_stageImage G (Over.mk (homOfLE (le_refl k |>.trans h)).op)).2
    using 1
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
  · simp only [κ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact SystemMorphism.app_over_base Q i h
  · simp only [κ, Category.assoc, pullback.lift_snd, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [hQ i h]
    exact stageTransition_ι_snd_assoc _ _ _ _
  · simp only [κ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [hP i h]
    exact stageTransition_ι_snd_assoc _ _ _ _

end Cartesian

/-! ### Stacks 0CPF -/

section Main

variable {X₁ X₂ X₃ X₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX₁ : X₁ ⟶ D.limitCone.pt}
    {pX₂ : X₂ ⟶ D.limitCone.pt} {pX₃ : X₃ ⟶ D.limitCone.pt} {pX₄ : X₄ ⟶ D.limitCone.pt}
    {G₁ : GoodDiagram B S hS hZ D pX₁} {G₂ : GoodDiagram B S hS hZ D pX₂}
    {G₃ : GoodDiagram B S hS hZ D pX₃} {G₄ : GoodDiagram B S hS hZ D pX₄} {p : X₁ ⟶ X₃}
    {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄} {i₅ i₆ i₇ i₈ : I}
    {h₃₅ : G₃.index ≤ i₅} {h₄₅ : G₄.index ≤ i₅} {h₂₆ : G₂.index ≤ i₆} {h₄₆ : G₄.index ≤ i₆}
    {h₁₇ : G₁.index ≤ i₇} {h₃₇ : G₃.index ≤ i₇} {h₁₈ : G₁.index ≤ i₈} {h₂₈ : G₂.index ≤ i₈}

/-- **Stacks 0CPF, the closed immersion**, for an index set of any size. In Situation 0CP6, let
`X₁ = X₂ ×_{X₄} X₃` be a cartesian square of algebraic spaces over `B`, with `X₁` and `X₄`
quasi-separated over `B`, let `G₁, …, G₄` be diagrams as in Stacks 0CP8 for the four spaces,
and let `a_i`, `b_i`, `p_i`, `q_i` be morphisms of the image systems inducing `a`, `b`, `p`, `q`,
as in Stacks 0CPA. Then at every sufficiently late stage `a_i ∘ p_i = b_i ∘ q_i`, and
`(q_i, p_i) : X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` is a closed immersion. -/
theorem exists_isClosedImmersion_lift_of_algebraicLimit (alg₁ : IsAlgebraicSpace B S hS X₁)
    (alg₄ : IsAlgebraicSpace B S hS X₄) (qs₁ : IsQuasiSeparated B S hS pX₁)
    (qs₄ : IsQuasiSeparated B S hS pX₄) (cart : IsPullback p q a b) (overA : a ≫ pX₄ = pX₃)
    (overB : b ≫ pX₄ = pX₂) (overQ : q ≫ pX₂ = pX₁)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆)
    (Fp : SystemMorphism G₁ G₃ p i₇ h₁₇ h₃₇) (Fq : SystemMorphism G₁ G₂ q i₈ h₁₈ h₂₈) :
    ∃ (i₉ : I) (h₅ : i₅ ≤ i₉) (h₆ : i₆ ≤ i₉) (h₇ : i₇ ≤ i₉) (h₈ : i₈ ≤ i₉)
      (comm : ∀ (i : I) (hi : i₉ ≤ i),
        Fq.app i (h₈.trans hi) ≫ Fb.app i (h₆.trans hi) =
          Fp.app i (h₇.trans hi) ≫ Fa.app i (h₅.trans hi)),
      ∀ (i : I) (hi : i₉ ≤ i), IsClosedImmersion B S hS (pullback.lift _ _ (comm i hi)) := by
  have overP := comp_eq_of_isPullback cart overA overB overQ
  obtain ⟨k, h₅k, h₆k⟩ := exists_ge_ge i₅ i₆
  set G := cartesianDiagramOfAlgebraicLimit alg₄ qs₄ cart overA overB overQ Fa Fb k h₅k h₆k
  obtain ⟨Q, P, comm', closed'⟩ := exists_isClosedImmersion_cartesianDiagram_of_algebraicLimit
    alg₄ qs₄ cart overA overB overQ Fa Fb k h₅k h₆k
  obtain ⟨m, hmG, hmG', E, E', n, hmn, inv⟩ :=
    SystemMorphism.exists_systemMorphism_inv_of_algebraicLimit alg₁ qs₁ G₁ G
  -- `E'` followed by `q_i` and `p_i` is eventually `Q` and `P`
  obtain ⟨m₁, hm₁, hm₁', hQ⟩ := SystemMorphism.exists_forall_app_eq_of_algebraicLimit alg₁ qs₁
    ((E'.restrict (exists_ge_ge m i₈).choose_spec.1).comp
      (Fq.restrict (exists_ge_ge m i₈).choose_spec.2) (Category.id_comp q)) Q
  obtain ⟨m₂, hm₂, hm₂', hP⟩ := SystemMorphism.exists_forall_app_eq_of_algebraicLimit alg₁ qs₁
    ((E'.restrict (exists_ge_ge m i₇).choose_spec.1).comp
      (Fp.restrict (exists_ge_ge m i₇).choose_spec.2) (Category.id_comp p)) P
  -- `a_i ∘ p_i = b_i ∘ q_i` eventually
  classical
  obtain ⟨c, hc⟩ := Finset.exists_le ({i₅, i₆, i₇, i₈} : Finset I)
  obtain ⟨m₃, _, _, hcomm⟩ := SystemMorphism.exists_forall_app_eq_of_algebraicLimit alg₁ qs₁
    ((Fq.restrict (hc i₈ (by simp))).comp (Fb.restrict (hc i₆ (by simp))) cart.w.symm)
    ((Fp.restrict (hc i₇ (by simp))).comp (Fa.restrict (hc i₅ (by simp))) rfl)
  obtain ⟨i₉, hi₉⟩ := Finset.exists_le ({i₅, i₆, i₇, i₈, k, n, m₁, m₂, m₃} : Finset I)
  have comm : ∀ (i : I) (hi : i₉ ≤ i),
      Fq.app i ((hi₉ i₈ (by simp)).trans hi) ≫ Fb.app i ((hi₉ i₆ (by simp)).trans hi) =
        Fp.app i ((hi₉ i₇ (by simp)).trans hi) ≫ Fa.app i ((hi₉ i₅ (by simp)).trans hi) :=
    fun i hi => hcomm i ((hi₉ m₃ (by simp)).trans hi)
  refine ⟨i₉, hi₉ i₅ (by simp), hi₉ i₆ (by simp), hi₉ i₇ (by simp), hi₉ i₈ (by simp), comm,
    fun i hi => ?_⟩
  have hk : k ≤ i := (hi₉ k (by simp)).trans hi
  have hn : n ≤ i := (hi₉ n (by simp)).trans hi
  have hQi : E'.app i (hmn.trans hn) ≫ Fq.app i ((hi₉ i₈ (by simp)).trans hi) = Q.app i hk :=
    hQ i ((hi₉ m₁ (by simp)).trans hi)
  have hPi : E'.app i (hmn.trans hn) ≫ Fp.app i ((hi₉ i₇ (by simp)).trans hi) = P.app i hk :=
    hP i ((hi₉ m₂ (by simp)).trans hi)
  obtain ⟨inv₁, inv₂⟩ := inv i hn
  have hiso : IsIso (E.app i (hmn.trans hn)) := ⟨⟨_, inv₁, inv₂⟩⟩
  have key : pullback.lift _ _ (comm i hi) =
      E.app i (hmn.trans hn) ≫ pullback.lift (Q.app i hk) (P.app i hk) (comm' i hk) := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← hQi, ← Category.assoc,
        inv₁, Category.id_comp]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← hPi, ← Category.assoc,
        inv₁, Category.id_comp]
  rw [key]
  exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _) (closed' i hk)

/-- **The isomorphism at a stage where `X³` is the base change of `X³_i`**, for an index set of
any size. If at a stage `i` the
component `a_i` is flat, the square `X³ = X⁴ ×_{X⁴_i} X³_i` is cartesian, and the morphism
`(q_i, p_i) : X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` is a closed immersion, then that morphism is an
isomorphism: `X¹ = X² ×_{X²_i} (X²_i ×_{X⁴_i} X³_i)` is the base change of `X² ⟶ X²_i`, whose
scheme-theoretic image is all of `X²_i`, along a flat morphism, so its scheme-theoretic image is
all of `X²_i ×_{X⁴_i} X³_i` (Stacks 089E), and it lies in the closed subspace `X¹_i`. -/
theorem isIso_lift_of_isFlat_of_algebraicLimit (alg₂ : IsAlgebraicSpace B S hS X₂)
    (cart : IsPullback p q a b)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆)
    (Fp : SystemMorphism G₁ G₃ p i₇ h₁₇ h₃₇) (Fq : SystemMorphism G₁ G₂ q i₈ h₁₈ h₂₈)
    (i : I) (h₅ : i₅ ≤ i) (h₆ : i₆ ≤ i) (h₇ : i₇ ≤ i) (h₈ : i₈ ≤ i)
    (comm : Fq.app i h₈ ≫ Fb.app i h₆ = Fp.app i h₇ ≫ Fa.app i h₅)
    (flat : IsFlat B S hS (Fa.app i h₅))
    (base : IsPullback (stageπ G₃ i (h₃₅.trans h₅)) a (Fa.app i h₅)
      (stageπ G₄ i (h₄₅.trans h₅)))
    (closed : IsClosedImmersion B S hS (pullback.lift _ _ comm)) :
    IsIso (pullback.lift _ _ comm) := by
  set φ := pullback.lift _ _ comm
  have alg₂i := imageSystem_isAlgebraicSpace G₂ (Over.mk (homOfLE (h₂₆.trans h₆)).op)
  have alg₃i := imageSystem_isAlgebraicSpace G₃ (Over.mk (homOfLE (h₃₅.trans h₅)).op)
  have alg₄i := imageSystem_isAlgebraicSpace G₄ (Over.mk (homOfLE (h₄₅.trans h₅)).op)
  have algT := isAlgebraicSpace_pullback B S hS (Fb.app i h₆) (Fa.app i h₅) alg₂i alg₃i alg₄i
  -- the composite `X¹ ⟶ X²_i ×_{X⁴_i} X³_i`
  let χ : X₁ ⟶ pullback (Fb.app i h₆) (Fa.app i h₅) := stageπ G₁ i (h₁₈.trans h₈) ≫ φ
  have χ_fst : χ ≫ pullback.fst _ _ = q ≫ stageπ G₂ i (h₂₆.trans h₆) := by
    rw [Category.assoc, pullback.lift_fst, Fq.stageπ_app]
  have χ_snd : χ ≫ pullback.snd _ _ = p ≫ stageπ G₃ i (h₃₅.trans h₅) := by
    rw [Category.assoc, pullback.lift_snd, Fp.stageπ_app i h₇]
  -- `X¹` is the base change of `X² ⟶ X²_i` along `X²_i ×_{X⁴_i} X³_i ⟶ X²_i`
  have sq : IsPullback χ q (pullback.fst _ _) (stageπ G₂ i (h₂₆.trans h₆)) := by
    have s := cart.paste_horiz base
    rw [← χ_snd, ← Fb.stageπ_app i h₆] at s
    exact IsPullback.of_right s χ_fst (IsPullback.of_hasPullback (Fb.app i h₆) (Fa.app i h₅)).flip
  have flatFst : IsFlat B S hS (pullback.fst (Fb.app i h₆) (Fa.app i h₅)) :=
    isFlat_of_isPullback_of_isAlgebraicSpace B S hS
      (IsPullback.of_hasPullback (Fb.app i h₆) (Fa.app i h₅)) alg₃i alg₄i flat
  have qcπ : IsQuasiCompact B S hS (stageπ G₂ i (h₂₆.trans h₆)) :=
    isQuasiCompact_of_comp_mono B S hS _ _
      (by rw [toSchemeTheoreticImage_ι]; exact isQuasiCompact_stageMap_of_algebraicLimit G₂ _)
  have himage : schemeTheoreticImageSubfunctor B S hS χ = ⊤ := by
    have e := sq.flip.isoPullback
    have he : sq.flip.isoPullback.hom ≫ pullback.snd _ _ = χ := sq.flip.isoPullback_hom_snd
    rw [← he, schemeTheoreticImageSubfunctor_comp_of_epi,
      schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact' B S hS _ _
        algT alg₂i alg₂ flatFst qcπ]
    have htop : schemeTheoreticImageSubfunctor B S hS (stageπ G₂ i (h₂₆.trans h₆)) = ⊤ :=
      schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS _
        (isAlgebraicSpace_stageTarget G₂ _)
    rw [htop]
    rfl
  have hmono : Mono φ := mono_of_isClosedImmersion B S hS _ closed
  have hrange : Subfunctor.range φ = ⊤ := by
    refine top_le_iff.1 (himage ▸ schemeTheoreticImageSubfunctor_le B S hS χ
      (isClosedSubspace_range_of_isClosedImmersion B S hS φ
        (imageSystem_isAlgebraicSpace G₁ _) closed) ?_)
    exact Subfunctor.range_comp_le _ _
  have hepi : Epi φ := (Subfunctor.epi_iff_range_eq_top φ).2 hrange
  exact isIso_of_mono_of_epi φ

/-- **Stacks 0CPF**, for an index set of any size. In Situation 0CP6, let
```
X₁ --p--> X₃
|q        |a
X₂ --b--> X₄
```
be a cartesian diagram of algebraic spaces over `B`, quasi-separated over `B`. For each
`j = 1, 2, 3, 4` let `G_j` be a diagram `X_j ⟶ W_j ⟶ B_{i_j}` as in Stacks 0CP8, with limit
description `X_j = lim_{i ≥ i_j} X^j_i` (Stacks 0CP9), and let `(a_i)_{i ≥ i₅}`, `(b_i)_{i ≥ i₆}`,
`(p_i)_{i ≥ i₇}`, `(q_i)_{i ≥ i₈}` be morphisms of these inverse systems inducing `a`, `b`, `p`,
`q`, as in Stacks 0CPA. Then there is an `i₉ ≥ i₅, i₆, i₇, i₈` such that for `i ≥ i₉` we have
`a_i ∘ p_i = b_i ∘ q_i` and `(q_i, p_i) : X¹_i ⟶ X²_i ×_{b_i, X⁴_i, a_i} X³_i` is a closed
immersion. If `a` is flat and of finite presentation (the source asks this of `a` and of `b`),
there is an `i₁₀ ≥ i₉` such that for `i ≥ i₁₀` this morphism is an isomorphism. -/
theorem exists_isClosedImmersion_lift_and_isIso_of_algebraicLimit
    (alg₁ : IsAlgebraicSpace B S hS X₁) (alg₂ : IsAlgebraicSpace B S hS X₂)
    (alg₃ : IsAlgebraicSpace B S hS X₃) (alg₄ : IsAlgebraicSpace B S hS X₄)
    (qs₁ : IsQuasiSeparated B S hS pX₁) (qs₃ : IsQuasiSeparated B S hS pX₃)
    (qs₄ : IsQuasiSeparated B S hS pX₄)
    (cart : IsPullback p q a b) (overA : a ≫ pX₄ = pX₃) (overB : b ≫ pX₄ = pX₂)
    (overQ : q ≫ pX₂ = pX₁)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆)
    (Fp : SystemMorphism G₁ G₃ p i₇ h₁₇ h₃₇) (Fq : SystemMorphism G₁ G₂ q i₈ h₁₈ h₂₈) :
    ∃ (i₉ : I) (le₅ : i₅ ≤ i₉) (le₆ : i₆ ≤ i₉) (le₇ : i₇ ≤ i₉) (le₈ : i₈ ≤ i₉)
      (comm : ∀ (i : I) (le : i₉ ≤ i),
        Fp.app i (le₇.trans le) ≫ Fa.app i (le₅.trans le) =
          Fq.app i (le₈.trans le) ≫ Fb.app i (le₆.trans le)),
      (∀ (i : I) (le : i₉ ≤ i),
        IsClosedImmersion B S hS (pullback.lift _ _ (comm i le).symm)) ∧
      (IsFlat B S hS a → IsFinitePresentation B S hS a →
        ∃ i₁₀ : I, ∃ le₁₀ : i₉ ≤ i₁₀, ∀ (i : I) (le : i₁₀ ≤ i),
          IsIso (pullback.lift _ _ (comm i (le₁₀.trans le)).symm)) := by
  obtain ⟨i₉, le₅, le₆, le₇, le₈, comm, closed⟩ :=
    exists_isClosedImmersion_lift_of_algebraicLimit alg₁ alg₄ qs₁ qs₄ cart overA overB overQ
      Fa Fb Fp Fq
  refine ⟨i₉, le₅, le₆, le₇, le₈, fun i hi => (comm i hi).symm, closed, fun flat fp => ?_⟩
  obtain ⟨i₃, -, hi₃⟩ :=
    SystemMorphism.exists_isFlat_isPullback_of_algebraicLimit alg₃ alg₄ qs₃ qs₄ Fa flat fp
  obtain ⟨i₁₀, h₉, h₃⟩ := exists_ge_ge i₉ i₃
  refine ⟨i₁₀, h₉, fun i hi => ?_⟩
  obtain ⟨flatᵢ, baseᵢ, -⟩ := hi₃ (Over.mk (homOfLE (le₅.trans (h₉.trans hi))).op) (h₃.trans hi)
  exact isIso_lift_of_isFlat_of_algebraicLimit alg₂ cart Fa Fb Fp Fq i _ _ _ _
    (comm i (h₉.trans hi)) flatᵢ baseᵢ (closed i (h₉.trans hi))

end Main

end GoodDiagram

end AlgebraicGeometry.Space

end
