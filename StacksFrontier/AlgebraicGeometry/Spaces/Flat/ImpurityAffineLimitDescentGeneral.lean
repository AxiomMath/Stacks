module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ImpurityAffineLimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# Impurities descend along an arbitrary directed limit of affine test schemes

**Stacks 0CV9** in the generality of the source. In the situation of Stacks 0CV6, let
`(g : T ⟶ Y, t' ⤳ t, ξ)` be an impurity of `ℱ` above `y`, and let `T = lim_{i} Tᵢ` be a
directed limit of affine schemes over the target. Then for some stage `i` the triple
`(Tᵢ ⟶ Y, t'ᵢ ⤳ tᵢ, ξᵢ)` is again an impurity of `ℱ` above `y`.

## Main definitions

* `AlgebraicGeometry.Space.ImpurityDiagram.push`: the impurity diagram pushed along a morphism
  `T ⟶ T'` of test schemes over the target.
* `AlgebraicGeometry.Space.AffineLimitSystem`: the hypothesis of Stacks 0CV9, a presentation of
  the test scheme as a directed limit of affine schemes over the target, with no condition on
  the size of the system.
* `AlgebraicGeometry.Space.AffineLimitSystem.stageDiagram`: the impurity diagram at a stage.
* `AlgebraicGeometry.Space.AffineLimitSystem.shrunkPresentation`: a bounded presentation of the
  same test scheme, by closed subschemes of the stages over a small directed set of indices.

## Main results

* `AlgebraicGeometry.Space.AffineLimitSystem.exists_isImpurity_stageDiagram`: **Stacks 0CV9**.
* `AlgebraicGeometry.Space.ImpurityDiagram.isRelativeWeakAssassinPoint_push`: the
  relative-assassin half survives every push (part (1) of Stacks 0CV2).
* `AlgebraicGeometry.Space.ImpurityDiagram.isImpurity_push_of_isClosedImmersion`: an impurity
  moves up along a closed immersion of test schemes.

## Implementation notes

The bounded form `AlgebraicGeometry.Space.AffineLimitPresentation.exists_isImpurity_stageDiagram`
asks the system for the cardinality clause `AlgebraicGeometry.Space.SiteLimitBound`, which keeps
the limits formed in its proof inside the size-bounded site; the source has no such clause. It
is removed here by changing the system, not the argument.

Write `R = Γ(T)` and `Sᵢ ⊆ R` for the image of `Γ(Tᵢ)`. The images grow along the system, and
the closed subschemes `Zᵢ = Spec Sᵢ ⟶ Tᵢ` receive compatible morphisms `T ⟶ Zᵢ`. Since
`#R ≤ size(T) ^ size(T)` (`AlgebraicGeometry.Scheme.mk_Γ_top_le_size_power`), every `Zᵢ` lies in
the site with size bounded by one cardinal below the cutoff. Choosing, for every element of
`⋃ Sᵢ`, one stage containing it, and closing the chosen indices under binary minima, gives a
directed set of fewer indices than the cutoff (`AffineLimitSystem.ShrunkIndex`); on it the
transition morphisms of the `Zᵢ` are the spectra of the inclusions `Sⱼ ⊆ Sᵢ`, so they do not
depend on a choice of morphism of the original index category. The system of the `Zᵢ` over this
directed set still has limit `T` (`AffineLimitSystem.isLimitShrunkCone`): a compatible family
of morphisms `U ⟶ Zᵢ` is a compatible family of ring maps `Sᵢ ⟶ Γ(U)`, which glues on the
directed union `⋃ Sᵢ` and so gives morphisms `U ⟶ Tⱼ` for every original index `j`, to which the
original limit property applies. This system satisfies the third package of the cardinality
clause, so the bounded form gives a stage `Zᵢ` carrying an impurity; the impurity moves up to
`Tᵢ` because `Zᵢ ⟶ Tᵢ` is a closed immersion, which is closed and injective on points.

## References

* [Stacks Project, Tag 0CV9](https://stacks.math.columbia.edu/tag/0CV9)
* [Stacks Project, Tag 0CV6](https://stacks.math.columbia.edu/tag/0CV6)
* [Stacks Project, Tag 0CV8](https://stacks.math.columbia.edu/tag/0CV8)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_ImpurityAffineLimitDescentGeneral
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace ImpurityDiagram

variable {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P)
  {T' : BigFppfOver B S hS} (p : D.T ⟶ T') (g' : yoneda.obj T' ⟶ P.Y)
  (hp : yoneda.map p ≫ g' = D.g)

/-- The morphism `X_T ⟶ X_{T'}` induced by a morphism `p : T ⟶ T'` over the target. -/
noncomputable def pushMap : D.baseChange ⟶ pullback g' P.f :=
  pullback.lift (D.toT ≫ yoneda.map p) D.toX
    (by rw [Category.assoc, hp]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem pushMap_fst : D.pushMap p g' hp ≫ pullback.fst g' P.f = D.toT ≫ yoneda.map p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pushMap_snd : D.pushMap p g' hp ≫ pullback.snd g' P.f = D.toX :=
  pullback.lift_snd _ _ _

/-- **The impurity diagram pushed along a morphism over the target.** For a morphism
`p : T ⟶ T'` of test schemes over `Y`, the triple `(T' ⟶ Y, p(t') ⤳ p(t), ξ')` whose points are
the images of `t'`, `t` and `ξ` under `p` and under the induced morphism `X_T ⟶ X_{T'}`. -/
noncomputable def push : ImpurityDiagram P where
  T := T'
  g := g'
  t' := pointsMap B S hS (yoneda.obj D.T) (yoneda.map p) D.t'
  t := pointsMap B S hS (yoneda.obj D.T) (yoneda.map p) D.t
  specializes := by
    have hcont : Continuous ((BigFppfOver.toScheme B S hS).map p).base :=
      ((BigFppfOver.toScheme B S hS).map p).base.hom.continuous_toFun
    have h := D.specializes.map hcont
    rwa [← pointsToScheme_pointsMap_yoneda, ← pointsToScheme_pointsMap_yoneda] at h
  mapsToChosenPoint := by
    rw [← pointsMap_comp_apply, hp]
    exact D.mapsToChosenPoint
  xi := pointsMap B S hS D.baseChange (D.pushMap p g' hp) D.xi
  xi_liesOver := by
    rw [← pointsMap_comp_apply, pushMap_fst, pointsMap_comp_apply, D.pointsMap_toT_xi]

/-- `X_T` is the base change of `X_{T'}` along `p : T ⟶ T'`. -/
theorem isPullback_pushMap :
    IsPullback D.toT (D.pushMap p g' hp) (yoneda.map p) (pullback.fst g' P.f) :=
  isPullback_of_comp_fst_snd (IsPullback.of_hasPullback D.g P.f) hp _
    (D.pushMap_fst p g' hp) (D.pushMap_snd p g' hp)

/-- The morphism `X_T ⟶ X_{T'}`, as a morphism of algebraic spaces. -/
noncomputable abbrev pushMapSpace : D.baseChangeSpace ⟶ P.baseChangeSpace T' g' :=
  ObjectProperty.homMk (D.pushMap p g' hp)

/-- The morphism `p : T ⟶ T'`, as a morphism of algebraic spaces. -/
noncomputable abbrev pushProjSpace :
    (schemeSpace D.T : AlgebraicSpaces B S hS) ⟶ schemeSpace T' :=
  ObjectProperty.homMk (yoneda.map p)

/-- The square exhibiting `X_T ⟶ T` as the base change of `X_{T'} ⟶ T'`, in the orientation
that part (1) of Stacks 0CV2 consumes. -/
theorem isPullback_pushMapSpace :
    IsPullback (D.pushMapSpace p g' hp).hom (P.baseChangeToBase D.T D.g).hom
      (P.baseChangeToBase T' g').hom (D.pushProjSpace p).hom :=
  (D.isPullback_pushMap p g' hp).flip

/-- The restriction `ℱ_T` is the pullback of the restriction `ℱ_{T'}` along `X_T ⟶ X_{T'}`. -/
noncomputable def pushModuleIso :
    (modulePullback B S hS (D.pushMapSpace p g' hp)).obj (P.baseChangeModule T' g') ≅
      P.baseChangeModule D.T D.g :=
  (modulePullbackCompIso B S hS (D.pushMapSpace p g' hp)
      (P.baseChangeToSource T' g')).app P.F ≪≫
    eqToIso (congrArg
      (fun m : D.baseChangeSpace ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) ↦
        (modulePullback B S hS m).obj P.F)
      (ObjectProperty.hom_ext _ (D.pushMap_snd p g' hp) :
        D.pushMapSpace p g' hp ≫ P.baseChangeToSource T' g' = P.baseChangeToSource D.T D.g))

/-- **The relative-assassin half survives every push.** If `ξ` lies in the relative weak
assassin of `ℱ_T`, its image `ξ'` lies in that of `ℱ_{T'}`; this is part (1) of Stacks 0CV2 for
the cartesian square exhibiting `X_T ⟶ T` as the base change of `X_{T'} ⟶ T'`. -/
theorem isRelativeWeakAssassinPoint_push (hD : D.IsRelativeWeakAssassinPoint D.xi) :
    (D.push p g' hp).IsRelativeWeakAssassinPoint (D.push p g' hp).xi := by
  rw [ImpurityDiagram.isRelativeWeakAssassinPoint_iff] at hD ⊢
  refine isRelativeWeaklyAssociatedPoint_of_baseChange B S hS
    (D.isPullback_pushMapSpace p g' hp) (P.baseChangeModule T' g') ?_
  exact (isRelativeWeaklyAssociatedPoint_congr (P.baseChangeToBase D.T D.g)
    (D.pushModuleIso p g' hp) D.xi).2 hD

/-- **Impurities move up along a closed immersion of test schemes.** Let `ι : T₁ ⟶ T₂` be a
morphism of test schemes over the target whose underlying morphism of schemes is a closed
immersion, and let `p₁ : T ⟶ T₁` be a morphism over the target. If the push of the diagram
along `p₁` is an impurity, so is its push along `p₂ = p₁ ≫ ι`, provided `ξ` lies in the
relative weak assassin of `ℱ_T`.

The relative-assassin half is `ImpurityDiagram.isRelativeWeakAssassinPoint_push`. For the
closure half, `X_{T₁} ⟶ X_{T₂}` is a closed immersion, so the closure of the image of `ξ₁` is
contained in the image of the closure of `ξ₁`; and `T₁ ⟶ T₂` is injective on points, so a
specialization of `ξ₂` over `p₂(t)` comes from a specialization of `ξ₁` over `p₁(t)`. -/
theorem isImpurity_push_of_isClosedImmersion {T₁ T₂ : BigFppfOver B S hS}
    (p₁ : D.T ⟶ T₁) (g₁ : yoneda.obj T₁ ⟶ P.Y) (hp₁ : yoneda.map p₁ ≫ g₁ = D.g)
    (ι : T₁ ⟶ T₂) (p₂ : D.T ⟶ T₂) (hι : p₁ ≫ ι = p₂) (g₂ : yoneda.obj T₂ ⟶ P.Y)
    (hg : yoneda.map ι ≫ g₂ = g₁) (hp₂ : yoneda.map p₂ ≫ g₂ = D.g)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hD : D.IsRelativeWeakAssassinPoint D.xi) (h₁ : (D.push p₁ g₁ hp₁).IsImpurity) :
    (D.push p₂ g₂ hp₂).IsImpurity := by
  subst hι
  refine ⟨D.isRelativeWeakAssassinPoint_push _ g₂ hp₂ hD, ?_⟩
  rintro ⟨θ, hθ, hθt⟩
  have hw : (pullback.fst g₁ P.f ≫ yoneda.map ι) ≫ g₂ = pullback.snd g₁ P.f ≫ P.f := by
    rw [Category.assoc, hg]; exact pullback.condition
  let φ : pullback g₁ P.f ⟶ pullback g₂ P.f :=
    pullback.lift (pullback.fst g₁ P.f ≫ yoneda.map ι) (pullback.snd g₁ P.f) hw
  have hφfst : φ ≫ pullback.fst g₂ P.f = pullback.fst g₁ P.f ≫ yoneda.map ι :=
    pullback.lift_fst _ _ _
  have hsq : IsPullback (pullback.fst g₁ P.f) φ (yoneda.map ι) (pullback.fst g₂ P.f) :=
    isPullback_of_comp_fst_snd (IsPullback.of_hasPullback g₁ P.f) hg φ hφfst
      (pullback.lift_snd _ _ _)
  have hιY : IsClosedImmersion B S hS (yoneda.map ι) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) ι).2 hci
  have hφ : IsClosedImmersion B S hS φ :=
    (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback hsq hιY
  have hφmap : D.pushMap p₁ g₁ hp₁ ≫ φ = D.pushMap (p₁ ≫ ι) g₂ hp₂ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hφfst, pushMap_fst_assoc, pushMap_fst, Functor.map_comp]
    · rw [Category.assoc, pullback.lift_snd, pushMap_snd, pushMap_snd]
  have hξ : pointsMap B S hS _ φ (D.push p₁ g₁ hp₁).xi = (D.push (p₁ ≫ ι) g₂ hp₂).xi := by
    change pointsMap B S hS _ φ (pointsMap B S hS _ (D.pushMap p₁ g₁ hp₁) D.xi) =
      pointsMap B S hS _ (D.pushMap (p₁ ≫ ι) g₂ hp₂) D.xi
    rw [← pointsMap_comp_apply, hφmap]
  have hclosedMap : IsClosedMap (pointsMap B S hS _ φ) :=
    isClosedMap_pointsMap_of_presheafIsClosedMap B S hS φ
      (MorphismProperty.relative_monotone (fun _ _ g hg ↦
        (show _root_.AlgebraicGeometry.IsClosedImmersion _ from hg).isClosedEmbedding.isClosedMap)
        _ hφ)
  have hsub : closure {(D.push (p₁ ≫ ι) g₂ hp₂).xi} ⊆
      pointsMap B S hS _ φ '' closure {(D.push p₁ g₁ hp₁).xi} := by
    refine closure_minimal ?_ (hclosedMap _ isClosed_closure)
    rw [Set.singleton_subset_iff, ← hξ]
    exact Set.mem_image_of_mem _ (subset_closure rfl)
  obtain ⟨θ₁, hθ₁, rfl⟩ := hsub hθ
  refine h₁.2 ⟨θ₁, hθ₁, ?_⟩
  refine pointsMap_injective_of_isClosedImmersion B S hS (yoneda.map ι) hιY ?_
  change pointsMap B S hS _ (yoneda.map ι) (pointsMap B S hS _ (pullback.fst g₁ P.f) θ₁) =
    pointsMap B S hS _ (yoneda.map ι) (pointsMap B S hS _ (yoneda.map p₁) D.t)
  rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, ← hφfst, pointsMap_comp_apply, ←
    Functor.map_comp]
  exact hθt

end ImpurityDiagram

/-! ### The hypothesis of Stacks 0CV9 -/

/-- **The hypothesis of Stacks 0CV9.** A presentation of the test scheme `T` of an impurity
diagram as a directed limit `T = lim_{i} Tᵢ` of affine schemes over the target: a cofiltered
index category, a diagram `stage` of affine objects of the site with compatible morphisms
`base i : Tᵢ ⟶ Y` to the target, and compatible projections `proj i : T ⟶ Tᵢ` over the target
which exhibit `yoneda T` as the limit of the `yoneda Tᵢ`. No condition is put on the size of the
index category or of the stages. -/
structure AffineLimitSystem {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P) where
  /-- The index category of the system. -/
  J : Type u
  /-- Its category structure. -/
  [category : Category.{u} J]
  /-- It is cofiltered, which is the source's "directed". -/
  [cofiltered : IsCofiltered J]
  /-- The system of test schemes. -/
  stage : J ⥤ BigFppfOver B S hS
  /-- Every stage is an affine scheme. -/
  isAffine : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (stage.obj i))
  /-- The projection from the test scheme of the diagram to a stage. -/
  proj : ∀ i, D.T ⟶ stage.obj i
  /-- The projections are compatible with the transition morphisms. -/
  proj_comp : ∀ {i j : J} (a : i ⟶ j), proj i ≫ stage.map a = proj j
  /-- The structure morphism of a stage to the target of the situation. -/
  base : ∀ i, yoneda.obj (stage.obj i) ⟶ P.Y
  /-- The system is a system over the target. -/
  base_comp : ∀ {i j : J} (a : i ⟶ j), yoneda.map (stage.map a) ≫ base j = base i
  /-- The projections are morphisms over the target. -/
  proj_base : ∀ i, yoneda.map (proj i) ≫ base i = D.g
  /-- The test scheme is the limit: the presheaf it represents has the universal property of
  the limit of the presheaves represented by the stages. -/
  isLimit : ∀ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (m : ∀ i, W ⟶ yoneda.obj (stage.obj i)),
    (∀ {i j : J} (a : i ⟶ j), m i ≫ yoneda.map (stage.map a) = m j) →
    ∃! h : W ⟶ yoneda.obj D.T, ∀ i, h ≫ yoneda.map (proj i) = m i

attribute [instance] AffineLimitSystem.category AffineLimitSystem.cofiltered

namespace AffineLimitSystem

variable {P : PrePureSituation.{u, u} B S hS} {D : ImpurityDiagram P} (A : AffineLimitSystem D)

/-- **The impurity diagram at a stage.** The triple `(Tᵢ ⟶ Y, t'ᵢ ⤳ tᵢ, ξᵢ)` obtained by
pushing the three points of the given diagram along the limit projections. -/
noncomputable def stageDiagram (i : A.J) : ImpurityDiagram P :=
  D.push (A.proj i) (A.base i) (A.proj_base i)

end AffineLimitSystem

/-! ### Size bounds -/

/-- The ring of global sections of a scheme has cardinality at most `size X ^ size X`: a global
section is determined by its restrictions to the affine opens. -/
theorem _root_.AlgebraicGeometry.Scheme.mk_Γ_top_le_size_power (X : Scheme.{u}) :
    #Γ(X, ⊤) ≤ X.size ^ X.size := by
  let r : Γ(X, ⊤) → ∀ U : X.affineOpens, Γ(X, U.1) :=
    fun s U ↦ X.presheaf.map (homOfLE le_top).op s
  have hr : Function.Injective r := fun s t hst ↦
    TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun U : X.affineOpens ↦ U.1) ⊤
      (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top X).ge s t
      fun U ↦ congrFun hst U
  calc #Γ(X, ⊤) ≤ #(∀ U : X.affineOpens, Γ(X, U.1)) := mk_le_of_injective hr
    _ = Cardinal.prod fun U : X.affineOpens ↦ #Γ(X, U.1) := mk_pi _
    _ ≤ Cardinal.prod fun _ : X.affineOpens ↦ X.size := prod_le_prod _ _ X.mk_sections_le_size
    _ = X.size ^ #X.affineOpens := prod_const' _ _
    _ ≤ X.size ^ X.size :=
      power_le_power_left (aleph0_pos.trans_le X.aleph0_le_size).ne' X.mk_affineOpens_le_size

/-! ### Closing a set of indices under binary minima -/

section MinClosure

variable {J : Type u} [Category.{u} J] [IsCofiltered J]

/-- One step of the closure: adjoin a chosen common lower bound of every pair. -/
def cofilteredMinStep (s : Set J) : Set J :=
  s ∪ Set.image2 (fun a b ↦ IsCofiltered.min a b) s s

/-- The closure of a set of objects under the chosen binary minima. -/
def cofilteredMinClosure (s : Set J) : Set J :=
  ⋃ n : ℕ, cofilteredMinStep^[n] s

theorem iterate_cofilteredMinStep_mono (s : Set J) : Monotone fun n : ℕ ↦ cofilteredMinStep^[n] s :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [Function.iterate_succ_apply']
    exact Set.subset_union_left

theorem subset_cofilteredMinClosure (s : Set J) : s ⊆ cofilteredMinClosure s :=
  Set.subset_iUnion (fun n : ℕ ↦ cofilteredMinStep^[n] s) 0

theorem min_mem_cofilteredMinClosure {s : Set J} {a b : J} (ha : a ∈ cofilteredMinClosure s)
    (hb : b ∈ cofilteredMinClosure s) : IsCofiltered.min a b ∈ cofilteredMinClosure s := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 ha
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hb
  refine Set.mem_iUnion.2 ⟨max m n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact Or.inr ⟨a, iterate_cofilteredMinStep_mono s (le_max_left m n) hm, b,
    iterate_cofilteredMinStep_mono s (le_max_right m n) hn, rfl⟩

theorem mk_cofilteredMinClosure_le {s : Set J} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hs : #s ≤ κ) :
    #(cofilteredMinClosure s) ≤ κ := by
  have hstep : ∀ t : Set J, #t ≤ κ → #(cofilteredMinStep t) ≤ κ := fun t ht ↦
    (mk_union_le _ _).trans <| (add_le_add ht (mk_image2_le.trans (mul_le_mul' ht ht))).trans <|
      by rw [mul_eq_self hκ, add_eq_self hκ]
  have hiter : ∀ n : ℕ, #(cofilteredMinStep^[n] s) ≤ κ := fun n ↦ by
    induction n with
    | zero => exact hs
    | succ n ih => rw [Function.iterate_succ_apply']; exact hstep _ ih
  have h := mk_iUnion_le_lift (fun n : ℕ ↦ cofilteredMinStep^[n] s)
  simp only [lift_uzero, mk_nat, lift_aleph0] at h
  refine h.trans ?_
  calc ℵ₀ * ⨆ n : ℕ, #(cofilteredMinStep^[n] s) ≤ κ * κ := mul_le_mul' hκ (ciSup_le' hiter)
    _ = κ := mul_eq_self hκ

end MinClosure

namespace AffineLimitSystem

variable {P : PrePureSituation.{u, u} B S hS} {D : ImpurityDiagram P} (A : AffineLimitSystem D)

instance : Nonempty A.J := IsCofiltered.nonempty

/-! ### The images of the rings of the stages in the ring of the test scheme -/

/-- The scheme underlying a stage. -/
noncomputable abbrev stageScheme (i : A.J) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj (A.stage.obj i)

instance (i : A.J) : IsAffine (A.stageScheme i) := A.isAffine i

/-- The projection `T ⟶ Tᵢ`, on underlying schemes. -/
noncomputable abbrev projScheme (i : A.J) :
    (BigFppfOver.toScheme B S hS).obj D.T ⟶ A.stageScheme i :=
  (BigFppfOver.toScheme B S hS).map (A.proj i)

/-- The ring map `Γ(Tᵢ) ⟶ Γ(T)` induced by a projection. -/
noncomputable abbrev sectionsMap (i : A.J) :
    Γ(A.stageScheme i, ⊤) ⟶ Γ((BigFppfOver.toScheme B S hS).obj D.T, ⊤) :=
  (A.projScheme i).appTop

theorem projScheme_comp {i j : A.J} (a : i ⟶ j) :
    A.projScheme i ≫ (BigFppfOver.toScheme B S hS).map (A.stage.map a) = A.projScheme j := by
  rw [← Functor.map_comp, A.proj_comp a]

theorem sectionsMap_comp {i j : A.J} (a : i ⟶ j) :
    ((BigFppfOver.toScheme B S hS).map (A.stage.map a)).appTop ≫ A.sectionsMap i =
      A.sectionsMap j := by
  rw [← Scheme.Hom.comp_appTop, A.projScheme_comp a]

/-- **The image of `Γ(Tᵢ)` in `Γ(T)`**, as a subring (a `ℤ`-subalgebra). -/
noncomputable def stageImage (i : A.J) :
    Subalgebra ℤ Γ((BigFppfOver.toScheme B S hS).obj D.T, ⊤) :=
  (A.sectionsMap i).hom.toIntAlgHom.range

theorem sectionsMap_mem_stageImage (i : A.J) (x : Γ(A.stageScheme i, ⊤)) :
    A.sectionsMap i x ∈ A.stageImage i :=
  ⟨x, rfl⟩

/-- The images grow along the system. -/
theorem stageImage_le {i j : A.J} (a : i ⟶ j) : A.stageImage j ≤ A.stageImage i := by
  rintro _ ⟨y, rfl⟩
  refine ⟨((BigFppfOver.toScheme B S hS).map (A.stage.map a)).appTop y, ?_⟩
  change A.sectionsMap i (((BigFppfOver.toScheme B S hS).map (A.stage.map a)).appTop y) =
    A.sectionsMap j y
  rw [← A.sectionsMap_comp a]
  rfl

/-- The surjection of `Γ(Tᵢ)` onto its image. -/
noncomputable def stageImageRestrict (i : A.J) :
    Γ(A.stageScheme i, ⊤) →+* A.stageImage i :=
  (A.sectionsMap i).hom.toIntAlgHom.rangeRestrict.toRingHom

@[simp] theorem coe_stageImageRestrict (i : A.J) (x : Γ(A.stageScheme i, ⊤)) :
    (A.stageImageRestrict i x : Γ((BigFppfOver.toScheme B S hS).obj D.T, ⊤)) =
      A.sectionsMap i x := rfl

theorem stageImageRestrict_surjective (i : A.J) :
    Function.Surjective (A.stageImageRestrict i) :=
  AlgHom.rangeRestrict_surjective _

/-- **The closed subscheme `Zᵢ = Spec (image of Γ(Tᵢ) in Γ(T)) ⟶ Tᵢ`.** -/
noncomputable def imageToStage (i : A.J) :
    Spec (.of (A.stageImage i)) ⟶ A.stageScheme i :=
  Spec.map (CommRingCat.ofHom (A.stageImageRestrict i)) ≫ (A.stageScheme i).isoSpec.inv

instance (i : A.J) : _root_.AlgebraicGeometry.IsClosedImmersion (A.imageToStage i) := by
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (A.stageImageRestrict i))
    (A.stageImageRestrict_surjective i)
  unfold imageToStage
  infer_instance

/-- The morphism `T ⟶ Zᵢ`: the canonical `T ⟶ Spec Γ(T)` followed by the spectrum of the
inclusion of the image of `Γ(Tᵢ)`. -/
noncomputable def toImage (i : A.J) :
    (BigFppfOver.toScheme B S hS).obj D.T ⟶ Spec (.of (A.stageImage i)) :=
  ((BigFppfOver.toScheme B S hS).obj D.T).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (A.stageImage i).val.toRingHom)

/-- The projection `T ⟶ Tᵢ` factors through `Zᵢ`. -/
theorem toImage_comp_imageToStage (i : A.J) :
    A.toImage i ≫ A.imageToStage i = A.projScheme i := by
  have h : CommRingCat.ofHom (A.stageImageRestrict i) ≫
      CommRingCat.ofHom (A.stageImage i).val.toRingHom = A.sectionsMap i := by
    ext x; rfl
  have hiso : (A.stageScheme i).toSpecΓ ≫ (A.stageScheme i).isoSpec.inv = 𝟙 _ :=
    (A.stageScheme i).isoSpec.hom_inv_id
  rw [toImage, imageToStage, Category.assoc, ← Spec.map_comp_assoc, h,
    ← Scheme.toSpecΓ_naturality_assoc, hiso, Category.comp_id]

/-- The inclusion of images along a transition, as a morphism `Zᵢ ⟶ Zⱼ`. -/
noncomputable def imageMap {i j : A.J} (h : A.stageImage j ≤ A.stageImage i) :
    Spec (.of (A.stageImage i)) ⟶ Spec (.of (A.stageImage j)) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

/-- The closed subschemes `Zᵢ ⟶ Tᵢ` are compatible with the transition morphisms. -/
theorem imageMap_comp_imageToStage {i j : A.J} (a : i ⟶ j) :
    A.imageMap (A.stageImage_le a) ≫ A.imageToStage j =
      A.imageToStage i ≫ (BigFppfOver.toScheme B S hS).map (A.stage.map a) := by
  rw [imageMap, imageToStage, imageToStage, Category.assoc, ← Scheme.isoSpec_inv_naturality,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext x
  change A.sectionsMap j x =
    A.sectionsMap i (((BigFppfOver.toScheme B S hS).map (A.stage.map a)).appTop x)
  rw [← A.sectionsMap_comp a]
  rfl

theorem toImage_comp_imageMap {i j : A.J} (h : A.stageImage j ≤ A.stageImage i) :
    A.toImage i ≫ A.imageMap h = A.toImage j := by
  rw [toImage, toImage, imageMap, Category.assoc, ← Spec.map_comp]
  rfl

theorem imageMap_id (i : A.J) (h : A.stageImage i ≤ A.stageImage i) :
    A.imageMap h = 𝟙 _ := by
  rw [imageMap, ← Spec.map_id]
  rfl

theorem imageMap_comp {i j k : A.J} (h : A.stageImage j ≤ A.stageImage i)
    (h' : A.stageImage k ≤ A.stageImage j) :
    A.imageMap h ≫ A.imageMap h' = A.imageMap (h'.trans h) := by
  rw [imageMap, imageMap, imageMap, ← Spec.map_comp]
  rfl

/-! ### The stages `Zᵢ` as objects of the site -/

/-- The uniform bound `size(T) ^ size(T)`, below the cutoff, on the ring `Γ(T)`. -/
theorem power_size_lt_cutoff :
    ((BigFppfOver.toScheme B S hS).obj D.T).size ^ ((BigFppfOver.toScheme B S hS).obj D.T).size <
      B.cutoff :=
  Cardinal.power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    D.T.left.property D.T.left.property

theorem aleph0_le_power_size :
    ℵ₀ ≤ ((BigFppfOver.toScheme B S hS).obj D.T).size ^
      ((BigFppfOver.toScheme B S hS).obj D.T).size :=
  ((BigFppfOver.toScheme B S hS).obj D.T).aleph0_le_size.trans
    (self_le_power _ (one_le_aleph0.trans ((BigFppfOver.toScheme B S hS).obj D.T).aleph0_le_size))

/-- Every `Zᵢ` has size at most `size(T) ^ size(T)`. -/
theorem size_Spec_stageImage_le (i : A.J) :
    (Spec (.of (A.stageImage i))).size ≤
      ((BigFppfOver.toScheme B S hS).obj D.T).size ^
        ((BigFppfOver.toScheme B S hS).obj D.T).size := by
  rw [Scheme.size_Spec]
  exact max_le aleph0_le_power_size
    ((mk_subtype_le _).trans ((BigFppfOver.toScheme B S hS).obj D.T).mk_Γ_top_le_size_power)

theorem contains_stageImage (i : A.J) : B.Contains (Spec (.of (A.stageImage i))) :=
  (A.size_Spec_stageImage_le i).trans_lt power_size_lt_cutoff

/-- **The stage `Zᵢ`**, an object of the site over `S` through `Zᵢ ⟶ Tᵢ ⟶ S`. -/
noncomputable abbrev imageObj (i : A.J) : BigFppfOver B S hS :=
  siteObject B S hS (A.contains_stageImage i)
    (A.imageToStage i ≫ B.inclusion.map (A.stage.obj i).hom)

/-- The closed immersion `Zᵢ ⟶ Tᵢ`, as a morphism of the site. -/
noncomputable def imageToStageHom (i : A.J) : A.imageObj i ⟶ A.stage.obj i :=
  Over.homMk (ObjectProperty.homMk (A.imageToStage i)) (ObjectProperty.hom_ext _ rfl)

/-- The transition morphism `Zᵢ ⟶ Zⱼ`, as a morphism of the site. -/
noncomputable def imageHom {i j : A.J} (a : i ⟶ j) : A.imageObj i ⟶ A.imageObj j :=
  Over.homMk (ObjectProperty.homMk (A.imageMap (A.stageImage_le a)))
    (ObjectProperty.hom_ext _ (by
      change A.imageMap (A.stageImage_le a) ≫ A.imageToStage j ≫
          B.inclusion.map (A.stage.obj j).hom =
        A.imageToStage i ≫ B.inclusion.map (A.stage.obj i).hom
      rw [← Category.assoc, A.imageMap_comp_imageToStage a, Category.assoc,
        BigFppfOver.toScheme_map_comp_hom]))

/-- The morphism `T ⟶ Zᵢ`, as a morphism of the site. -/
noncomputable def toImageHom (i : A.J) : D.T ⟶ A.imageObj i :=
  Over.homMk (ObjectProperty.homMk (A.toImage i))
    (ObjectProperty.hom_ext _ (by
      change A.toImage i ≫ A.imageToStage i ≫ B.inclusion.map (A.stage.obj i).hom =
        B.inclusion.map D.T.hom
      rw [← Category.assoc, A.toImage_comp_imageToStage,
        BigFppfOver.toScheme_map_comp_hom]))

@[simp] theorem toScheme_map_imageToStageHom (i : A.J) :
    (BigFppfOver.toScheme B S hS).map (A.imageToStageHom i) = A.imageToStage i := rfl

@[simp] theorem toScheme_map_imageHom {i j : A.J} (a : i ⟶ j) :
    (BigFppfOver.toScheme B S hS).map (A.imageHom a) = A.imageMap (A.stageImage_le a) := rfl

@[simp] theorem toScheme_map_toImageHom (i : A.J) :
    (BigFppfOver.toScheme B S hS).map (A.toImageHom i) = A.toImage i := rfl

theorem toImageHom_comp_imageToStageHom (i : A.J) :
    A.toImageHom i ≫ A.imageToStageHom i = A.proj i :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, toScheme_map_toImageHom, toScheme_map_imageToStageHom]
    exact A.toImage_comp_imageToStage i)

theorem imageHom_comp_imageToStageHom {i j : A.J} (a : i ⟶ j) :
    A.imageHom a ≫ A.imageToStageHom j = A.imageToStageHom i ≫ A.stage.map a :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, Functor.map_comp, toScheme_map_imageHom, toScheme_map_imageToStageHom,
      toScheme_map_imageToStageHom]
    exact A.imageMap_comp_imageToStage a)

/-! ### A small index category -/

/-- The indices chosen to cover `Γ(T)`: for every section in the image of some stage, one such
stage, together with one further index. -/
noncomputable def coverSeed : Set A.J :=
  insert (Classical.arbitrary A.J)
    (Set.range fun r : {r : Γ((BigFppfOver.toScheme B S hS).obj D.T, ⊤) //
      ∃ j, r ∈ A.stageImage j} ↦ r.2.choose)

/-- The chosen indices, closed under binary minima. -/
noncomputable abbrev shrunkSet : Set A.J := cofilteredMinClosure A.coverSeed

/-- **The small index category**: the chosen indices, with `i ≤ j` when there is a morphism
`i ⟶ j`. It is a preorder, so its morphism types are subsingletons. -/
structure ShrunkIndex : Type u where
  /-- The index. -/
  val : A.J
  /-- It is one of the chosen indices. -/
  mem : val ∈ A.shrunkSet

instance : Preorder A.ShrunkIndex where
  le i j := Nonempty (i.1 ⟶ j.1)
  le_refl i := ⟨𝟙 _⟩
  le_trans _ _ _ h h' := ⟨h.some ≫ h'.some⟩

instance : IsCodirectedOrder A.ShrunkIndex where
  directed i j := ⟨⟨IsCofiltered.min i.1 j.1, min_mem_cofilteredMinClosure i.2 j.2⟩,
    ⟨IsCofiltered.minToLeft _ _⟩, ⟨IsCofiltered.minToRight _ _⟩⟩

instance : Nonempty A.ShrunkIndex :=
  ⟨⟨Classical.arbitrary A.J, subset_cofilteredMinClosure _ (Set.mem_insert _ _)⟩⟩

theorem mk_shrunkIndex_le :
    #A.ShrunkIndex ≤ ((BigFppfOver.toScheme B S hS).obj D.T).size ^
      ((BigFppfOver.toScheme B S hS).obj D.T).size := by
  refine (mk_le_of_injective (f := fun i : A.ShrunkIndex ↦ (⟨i.1, i.2⟩ : A.shrunkSet))
    fun i j h ↦ by cases i; cases j; cases h; rfl).trans ?_
  refine mk_cofilteredMinClosure_le aleph0_le_power_size ?_
  refine mk_insert_le.trans ?_
  calc _ ≤ #Γ((BigFppfOver.toScheme B S hS).obj D.T, ⊤) + 1 :=
        add_le_add (mk_range_le.trans (mk_subtype_le _)) le_rfl
    _ ≤ _ + _ := add_le_add ((BigFppfOver.toScheme B S hS).obj D.T).mk_Γ_top_le_size_power
        (one_le_aleph0.trans aleph0_le_power_size)
    _ = _ := add_eq_self aleph0_le_power_size

/-- Every section in the image of a stage lies in the image of a chosen stage. -/
theorem exists_mem_stageImage_shrunk {j : A.J} {x : Γ((BigFppfOver.toScheme B S hS).obj D.T, ⊤)}
    (hx : x ∈ A.stageImage j) : ∃ i : A.ShrunkIndex, x ∈ A.stageImage i.1 :=
  ⟨⟨_, subset_cofilteredMinClosure _ (Set.mem_insert_of_mem _ ⟨⟨x, j, hx⟩, rfl⟩)⟩,
    (⟨x, j, hx⟩ : {r // ∃ j, r ∈ A.stageImage j}).2.choose_spec⟩

theorem stageImage_le_iSup (j : A.J) : A.stageImage j ≤ ⨆ i : A.ShrunkIndex, A.stageImage i.1 :=
  fun _ hx ↦ let ⟨i, hi⟩ := A.exists_mem_stageImage_shrunk hx; le_iSup (fun i : A.ShrunkIndex ↦
    A.stageImage i.1) i hi

theorem directed_stageImage : Directed (· ≤ ·) fun i : A.ShrunkIndex ↦ A.stageImage i.1 :=
  fun i j ↦ let ⟨c, hci, hcj⟩ := directed_of (· ≥ ·) i j
    ⟨c, A.stageImage_le hci.some, A.stageImage_le hcj.some⟩

/-! ### The system of the `Zᵢ` over the small index category -/

/-- **The system `i ↦ Zᵢ`** over the small index category. -/
noncomputable abbrev shrunkStage : A.ShrunkIndex ⥤ BigFppfOver B S hS where
  obj i := A.imageObj i.1
  map f := A.imageHom f.le.some
  map_id i := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [CategoryTheory.Functor.map_id, toScheme_map_imageHom]
    exact A.imageMap_id _ _)
  map_comp f g := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, toScheme_map_imageHom, toScheme_map_imageHom, toScheme_map_imageHom]
    exact (A.imageMap_comp _ _).symm)

@[simp] theorem shrunkStage_obj (i : A.ShrunkIndex) : A.shrunkStage.obj i = A.imageObj i.1 :=
  rfl

@[simp] theorem shrunkStage_map {i j : A.ShrunkIndex} (f : i ⟶ j) :
    A.shrunkStage.map f = A.imageHom f.le.some :=
  rfl

/-- The cone on the system `Zᵢ` with vertex `T`. -/
noncomputable abbrev shrunkCone : Cone A.shrunkStage where
  pt := D.T
  π :=
    { app := fun i ↦ A.toImageHom i.1
      naturality := fun i j f ↦ (Category.id_comp _).trans <|
        (BigFppfOver.toScheme B S hS).map_injective (by
          rw [Functor.map_comp, toScheme_map_toImageHom, toScheme_map_toImageHom, shrunkStage_map,
            toScheme_map_imageHom]
          exact (A.toImage_comp_imageMap _).symm) }

/-- The cone on the given system with vertex `T`. -/
noncomputable abbrev cone : Cone A.stage where
  pt := D.T
  π :=
    { app := A.proj
      naturality := fun _ _ a ↦ (Category.id_comp _).trans (A.proj_comp a).symm }

/-- The limit hypothesis, read in the site. -/
noncomputable def isLimitCone : IsLimit A.cone :=
  isLimitOfReflects yoneda (IsLimit.ofExistsUnique fun s ↦
    A.isLimit s.pt (fun i ↦ s.π.app i) (fun a ↦ s.w a))

/-! ### The limit property of the system `Zᵢ` -/

/-- A morphism `g : U ⟶ Spec R` is the composite of `U ⟶ Spec Γ(U)` with the spectrum of the
ring map `R ⟶ Γ(U)` it induces. -/
theorem _root_.AlgebraicGeometry.Scheme.toSpecΓ_comp_Spec_map_ΓSpecIso_inv_appTop
    {U : Scheme.{u}} {R : CommRingCat.{u}} (g : U ⟶ Spec R) :
    U.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop) = g := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- On global sections, a morphism `n : U ⟶ T` followed by `T ⟶ Zᵢ` is the restriction of
`n` on global sections to the image of `Γ(Tᵢ)`. -/
theorem ΓSpecIso_inv_comp_appTop_toImage {U : Scheme.{u}}
    (n : U ⟶ (BigFppfOver.toScheme B S hS).obj D.T) (i : A.J) :
    (Scheme.ΓSpecIso (.of (A.stageImage i))).inv ≫ (n ≫ A.toImage i).appTop =
      CommRingCat.ofHom (A.stageImage i).val.toRingHom ≫ n.appTop := by
  simp only [toImage, Scheme.Hom.comp_appTop, Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]

section Lift

variable (s : Cone A.shrunkStage)

/-- The ring map `Γ(Zᵢ) ⟶ Γ(U)` of a leg of a cone on the system `Zᵢ`. -/
noncomputable def coneRingHom (i : A.ShrunkIndex) :
    A.stageImage i.1 →ₐ[ℤ] Γ((BigFppfOver.toScheme B S hS).obj s.pt, ⊤) :=
  ((Scheme.ΓSpecIso (.of (A.stageImage i.1))).inv ≫
    ((BigFppfOver.toScheme B S hS).map (s.π.app i)).appTop).hom.toIntAlgHom

theorem coneRingHom_eq_comp {k i : A.ShrunkIndex} (f : k ⟶ i) :
    A.coneRingHom s i =
      (A.coneRingHom s k).comp (Subalgebra.inclusion (A.stageImage_le f.le.some)) := by
  have h1 : (BigFppfOver.toScheme B S hS).map (s.π.app k) ≫ A.imageMap (A.stageImage_le f.le.some) =
      (BigFppfOver.toScheme B S hS).map (s.π.app i) := by
    rw [← s.w f, Functor.map_comp]; rfl
  have h2 : (Scheme.ΓSpecIso (.of (A.stageImage i.1))).inv ≫
        ((BigFppfOver.toScheme B S hS).map (s.π.app i)).appTop =
      CommRingCat.ofHom (Subalgebra.inclusion (A.stageImage_le f.le.some)).toRingHom ≫
        (Scheme.ΓSpecIso (.of (A.stageImage k.1))).inv ≫
          ((BigFppfOver.toScheme B S hS).map (s.π.app k)).appTop := by
    rw [← h1, Scheme.Hom.comp_appTop, imageMap, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  ext x
  exact congrArg (fun g ↦ g.hom x) h2

theorem coneRingHom_compat (i j : A.ShrunkIndex) (h : A.stageImage i.1 ≤ A.stageImage j.1) :
    A.coneRingHom s i = (A.coneRingHom s j).comp (Subalgebra.inclusion h) := by
  obtain ⟨c, hci, hcj⟩ := directed_of (· ≥ ·) i j
  rw [A.coneRingHom_eq_comp s (homOfLE hci), A.coneRingHom_eq_comp s (homOfLE hcj),
    AlgHom.comp_assoc]
  rfl

/-- The ring map from the image of `Γ(Tⱼ)` to `Γ(U)` glued from the legs of the cone, for any
index `j` of the given system. -/
noncomputable def liftRingHom (j : A.J) :
    A.stageImage j →ₐ[ℤ] Γ((BigFppfOver.toScheme B S hS).obj s.pt, ⊤) :=
  Subalgebra.iSupLift (fun i : A.ShrunkIndex ↦ A.stageImage i.1) A.directed_stageImage
    (A.coneRingHom s) (A.coneRingHom_compat s) (A.stageImage j) (A.stageImage_le_iSup j)

theorem liftRingHom_mk (j : A.J) {x : Γ((BigFppfOver.toScheme B S hS).obj D.T, ⊤)}
    (hxj : x ∈ A.stageImage j) (i : A.ShrunkIndex) (hxi : x ∈ A.stageImage i.1) :
    A.liftRingHom s j ⟨x, hxj⟩ = A.coneRingHom s i ⟨x, hxi⟩ :=
  Subalgebra.iSupLift_mk (K := fun i : A.ShrunkIndex ↦ A.stageImage i.1) (i := i) ⟨x, hxi⟩ hxj

theorem liftRingHom_comp_inclusion {j k : A.J} (h : A.stageImage k ≤ A.stageImage j) :
    (A.liftRingHom s j).comp (Subalgebra.inclusion h) = A.liftRingHom s k := by
  ext x
  obtain ⟨i, hi⟩ := A.exists_mem_stageImage_shrunk x.2
  exact (A.liftRingHom_mk s j (h x.2) i hi).trans (A.liftRingHom_mk s k x.2 i hi).symm

theorem liftRingHom_shrunk (i : A.ShrunkIndex) :
    CommRingCat.ofHom (A.liftRingHom s i.1).toRingHom =
      (Scheme.ΓSpecIso (.of (A.stageImage i.1))).inv ≫
        ((BigFppfOver.toScheme B S hS).map (s.π.app i)).appTop := by
  ext x
  exact A.liftRingHom_mk s i.1 x.2 i x.2

/-- The morphism `U ⟶ Tⱼ` induced by the cone, for any index `j` of the given system. -/
noncomputable def liftScheme (j : A.J) :
    (BigFppfOver.toScheme B S hS).obj s.pt ⟶ A.stageScheme j :=
  ((BigFppfOver.toScheme B S hS).obj s.pt).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (A.liftRingHom s j).toRingHom) ≫ A.imageToStage j

theorem liftScheme_comp {j k : A.J} (a : j ⟶ k) :
    A.liftScheme s j ≫ (BigFppfOver.toScheme B S hS).map (A.stage.map a) = A.liftScheme s k := by
  rw [liftScheme, liftScheme, Category.assoc, Category.assoc, ← A.imageMap_comp_imageToStage a,
    imageMap, ← Spec.map_comp_assoc, ← A.liftRingHom_comp_inclusion s (A.stageImage_le a)]
  rfl

theorem liftScheme_shrunk (i : A.ShrunkIndex) :
    A.liftScheme s i.1 = (BigFppfOver.toScheme B S hS).map (s.π.app i) ≫ A.imageToStage i.1 := by
  rw [liftScheme, A.liftRingHom_shrunk s i, ← Category.assoc,
    Scheme.toSpecΓ_comp_Spec_map_ΓSpecIso_inv_appTop]

theorem liftScheme_comp_hom (j : A.J) :
    A.liftScheme s j ≫ B.inclusion.map (A.stage.obj j).hom = B.inclusion.map s.pt.hom := by
  let i₀ : A.ShrunkIndex := Classical.arbitrary _
  let k := IsCofiltered.min j i₀.1
  rw [← A.liftScheme_comp s (IsCofiltered.minToLeft j i₀.1), Category.assoc,
    BigFppfOver.toScheme_map_comp_hom,
    ← BigFppfOver.toScheme_map_comp_hom (A.stage.map (IsCofiltered.minToRight j i₀.1)),
    ← Category.assoc, A.liftScheme_comp s, A.liftScheme_shrunk s i₀, Category.assoc]
  exact BigFppfOver.toScheme_map_comp_hom (s.π.app i₀)

/-- The cone on the given system induced by a cone on the system `Zᵢ`. -/
noncomputable abbrev liftCone : Cone A.stage where
  pt := s.pt
  π :=
    { app := fun j ↦ Over.homMk (ObjectProperty.homMk (A.liftScheme s j))
        (ObjectProperty.hom_ext _ (A.liftScheme_comp_hom s j))
      naturality := fun j k a ↦ (Category.id_comp _).trans <|
        (BigFppfOver.toScheme B S hS).map_injective (by
          rw [Functor.map_comp]
          exact (A.liftScheme_comp s a).symm) }

/-- Any morphism `n : U ⟶ T` compatible with the cone is determined on the images of the rings of
the stages. -/
theorem appTop_apply_of_comp_eq (n : s.pt ⟶ D.T)
    (hn : ∀ i, n ≫ A.shrunkCone.π.app i = s.π.app i) (i : A.ShrunkIndex)
    (x : A.stageImage i.1) :
    ((BigFppfOver.toScheme B S hS).map n).appTop x = A.coneRingHom s i x := by
  have h := A.ΓSpecIso_inv_comp_appTop_toImage ((BigFppfOver.toScheme B S hS).map n) i.1
  have h' : (BigFppfOver.toScheme B S hS).map n ≫ A.toImage i.1 =
      (BigFppfOver.toScheme B S hS).map (s.π.app i) := by
    rw [← hn i, Functor.map_comp]; rfl
  rw [h'] at h
  exact (congrArg (fun g ↦ g.hom x) h).symm

end Lift

/-- **The system `Zᵢ` over the small index category still has limit `T`.** -/
noncomputable def isLimitShrunkCone : IsLimit A.shrunkCone :=
  IsLimit.ofExistsUnique fun s ↦ by
    have hfac : ∀ i, A.isLimitCone.lift (A.liftCone s) ≫ A.shrunkCone.π.app i = s.π.app i := by
      intro i
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [← cancel_mono (A.imageToStage i.1), Functor.map_comp]
      change _ ≫ A.toImage i.1 ≫ A.imageToStage i.1 = _
      rw [A.toImage_comp_imageToStage, ← A.liftScheme_shrunk s i, ← Functor.map_comp,
        A.isLimitCone.fac (A.liftCone s) i.1]
      rfl
    refine ⟨A.isLimitCone.lift (A.liftCone s), hfac, fun m hm ↦ ?_⟩
    refine A.isLimitCone.hom_ext fun j ↦ (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    refine ext_of_isAffine ?_
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    ext y
    obtain ⟨i, hi⟩ := A.exists_mem_stageImage_shrunk (A.sectionsMap_mem_stageImage j y)
    exact (A.appTop_apply_of_comp_eq s m hm i ⟨_, hi⟩).trans
      (A.appTop_apply_of_comp_eq s _ hfac i ⟨_, hi⟩).symm

/-- **The bounded presentation.** The system `Zᵢ` over the small index category is a limit
presentation of `T` carrying the third package of `AlgebraicGeometry.Space.SiteLimitBound`:
fewer indices than the cutoff, subsingleton morphism types, and all stages of size at most
`size(T) ^ size(T)`. -/
noncomputable def shrunkPresentation : AffineLimitPresentation D where
  J := A.ShrunkIndex
  stage := A.shrunkStage
  bound := Or.inr (Or.inr ⟨A.mk_shrunkIndex_le.trans_lt power_size_lt_cutoff, 1,
    one_lt_aleph0.trans B.aleph0_lt_cutoff, fun _ _ ↦ le_one_iff_subsingleton.2 inferInstance,
    _, power_size_lt_cutoff, fun i ↦ A.size_Spec_stageImage_le i.1⟩)
  isAffine := fun i ↦ inferInstanceAs (IsAffine (Spec _))
  proj := fun i ↦ A.toImageHom i.1
  proj_comp := fun f ↦ A.shrunkCone.w f
  base := fun i ↦ yoneda.map (A.imageToStageHom i.1) ≫ A.base i.1
  base_comp := fun {i j} f ↦ by
    rw [← Category.assoc, ← Functor.map_comp]
    change yoneda.map (A.imageHom f.le.some ≫ A.imageToStageHom j.1) ≫ _ = _
    rw [A.imageHom_comp_imageToStageHom, Functor.map_comp, Category.assoc, A.base_comp]
  proj_base := fun i ↦ by
    rw [← Category.assoc, ← Functor.map_comp, A.toImageHom_comp_imageToStageHom, A.proj_base]
  isLimit := fun W m hm ↦ (isLimitOfPreserves yoneda A.isLimitShrunkCone).existsUnique
    { pt := W
      π :=
        { app := m
          naturality := fun _ _ f ↦ (Category.id_comp _).trans (hm f).symm } }

/-- **Stacks 0CV9.** In Situation 0CV6, let `(g : T ⟶ Y, t' ⤳ t, ξ)` be an impurity of `ℱ`
above `y` and let `T = lim_{i} Tᵢ` be a directed limit of affine schemes over `Y`. Then for
some stage `i` the triple `(Tᵢ ⟶ Y, t'ᵢ ⤳ tᵢ, ξᵢ)` is an impurity of `ℱ` above `y`, where the
three points are the images of `t'`, `t` and `ξ` under the canonical projections.

No condition is put on the size of the system. The proof replaces it by a bounded one with the
same limit, the closed subschemes `Zᵢ = Spec (image of Γ(Tᵢ) in Γ(T))` over a small directed set
of indices (`AffineLimitSystem.shrunkPresentation`), applies the bounded form
`AlgebraicGeometry.Space.AffineLimitPresentation.exists_isImpurity_stageDiagram`, and moves the
impurity found at some `Zᵢ` up to `Tᵢ` along the closed immersion `Zᵢ ⟶ Tᵢ`
(`ImpurityDiagram.isImpurity_push_of_isClosedImmersion`). -/
@[stacks 0CV9 "for an arbitrary directed limit of affine schemes over the target; the source's \
`g : T → S` is read as `g : T → Y`, as Definition 0CV8 requires"]
theorem exists_isImpurity_stageDiagram {P : PrePureSituation.{u, u} B S hS}
    {D : ImpurityDiagram P} (A : AffineLimitSystem D) (hD : D.IsImpurity) :
    ∃ i : A.J, (A.stageDiagram i).IsImpurity := by
  obtain ⟨i, hi⟩ := A.shrunkPresentation.exists_isImpurity_stageDiagram hD
  exact ⟨i.1, D.isImpurity_push_of_isClosedImmersion (A.toImageHom i.1) _
    (A.shrunkPresentation.proj_base i)
    (A.imageToStageHom i.1) (A.proj i.1) (A.toImageHom_comp_imageToStageHom i.1) (A.base i.1)
    rfl (A.proj_base i.1)
    (inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion (A.imageToStage i.1))) hD.1 hi⟩

end AffineLimitSystem

/-- A limit presentation carrying the cardinality clause `AlgebraicGeometry.Space.SiteLimitBound`
is in particular a system of the shape of Stacks 0CV9. -/
def AffineLimitPresentation.toAffineLimitSystem {P : PrePureSituation.{u, u} B S hS}
    {D : ImpurityDiagram P} (A : AffineLimitPresentation D) : AffineLimitSystem D where
  J := A.J
  stage := A.stage
  isAffine := A.isAffine
  proj := A.proj
  proj_comp := A.proj_comp
  base := A.base
  base_comp := A.base_comp
  proj_base := A.proj_base
  isLimit := A.isLimit

/-- The impurity diagram at a stage of a limit presentation is the push of the given diagram
along the projection to that stage. -/
theorem AffineLimitPresentation.stageDiagram_eq_push {P : PrePureSituation.{u, u} B S hS}
    {D : ImpurityDiagram P} (A : AffineLimitPresentation D) (i : A.J) :
    A.stageDiagram i = D.push (A.proj i) (A.base i) (A.proj_base i) := rfl

/-- The impurity diagram at a stage is the same whether the presentation is read with or without
its cardinality clause. -/
theorem AffineLimitPresentation.stageDiagram_toAffineLimitSystem
    {P : PrePureSituation.{u, u} B S hS} {D : ImpurityDiagram P} (A : AffineLimitPresentation D)
    (i : A.J) : A.toAffineLimitSystem.stageDiagram i = A.stageDiagram i := rfl

end AlgebraicGeometry.Space

end
