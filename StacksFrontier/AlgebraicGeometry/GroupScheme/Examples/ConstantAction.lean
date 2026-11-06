module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Action
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductUniversal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Actions of constant group schemes

Let `G` be an abstract group and `S` a scheme. An action of `G` on a scheme `U` over `S` by
automorphisms over `S`, that is a homomorphism `a : G →* Aut_S(U)`, is the same thing as an action
of the constant group scheme `G_S` of **Stacks 03YW** on `U` in the sense of **Stacks 022Z**. This
file constructs the action of `G_S` from `a` and shows that `a` is recovered from it on the
summands of `G_S ×_S U`, which is the disjoint union of one copy of `U` for each `g ∈ G`.

## Main definitions

* `AlgebraicGeometry.constantGroupSchemePoint`: the `S`-point of `G_S` indexed by `g ∈ G`, the
  inclusion of the `g`-th summand `S ⟶ G_S`.
* `AlgebraicGeometry.constantGroupSchemeModObj`: the action of `G_S` on `U` induced by `a`.

## Main results

* `AlgebraicGeometry.isColimit_constantGroupSchemeCofan`: `G_S` is the disjoint union of copies
  of `S` indexed by `G`, the summands being the points `constantGroupSchemePoint`.
* `AlgebraicGeometry.isColimit_constantGroupSchemeTensorCofan`: `G_S ×_S U` is the disjoint union
  of copies of `U` indexed by `G`.
* `AlgebraicGeometry.constantGroupSchemeLeg_smul` and
  `AlgebraicGeometry.constantGroupSchemePoint_smul`: the action of `G_S` restricted to the `g`-th
  summand, or to the constant `T`-point `g`, is `a g` — the abstract action is recovered.
* `AlgebraicGeometry.constantGroupSchemeModObj_unique`: it is the only action of `G_S` on `U`
  with this property.
* `AlgebraicGeometry.isFreeAction_constantGroupSchemeModObj`: if `a` is free on nonempty points,
  the action of `G_S` is free in the sense of **Stacks 07S1**.
* `AlgebraicGeometry.exists_smul_eq_constantGroupSchemeModObj`: if `a` is transitive on the
  points of `U`, so is the action of `G_S`, read on the points of `G_S ×_S U`.

## Implementation notes

The group law of `G_S` is the base change of that of `G_{Spec ℤ}`, of which the library only
records the behaviour on summands (`AlgebraicGeometry.IsConstantGroupSchemeStructure`); that is all
the construction uses. Disjoint unions are universal in the category of schemes
(`AlgebraicGeometry.isUniversalColimit_sigmaCofan`), which is what makes the base changes of the
decomposition of `G_{Spec ℤ}` again disjoint unions.

## References

* [Stacks Project, Tag 03YW](https://stacks.math.columbia.edu/tag/03YW)
* [Stacks Project, Tag 022Z](https://stacks.math.columbia.edu/tag/022Z)
* [Stacks Project, Tag 07S1](https://stacks.math.columbia.edu/tag/07S1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Functor.LaxMonoidal
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u v

namespace AlgebraicGeometry

variable (G : Type v) [Small.{u} G] [Group G] (S : Scheme.{u})

/-- The underlying scheme over `S` of the constant group scheme `G_S`: the base change of
`G_{Spec ℤ}` to `S`. It is `(constantGroupScheme G S).X`, with the same group structure. -/
@[sga "3 VIII 1.0.3" "partial"]
abbrev constantGroupSchemeObj : Over S :=
  (Over.pullback (terminal.from S)).obj (constantSchemeOverIntegersObj G)

/-- `AlgebraicGeometry.constantGroupSchemeObj` is the underlying object of the constant group
scheme of **Stacks 03YW**. -/
theorem constantGroupSchemeObj_eq : constantGroupSchemeObj G S = (constantGroupScheme G S).X :=
  rfl

/-- The `S`-point of the constant group scheme `G_S` indexed by `g ∈ G`: the inclusion of the
summand of `G_S` indexed by `g`. -/
def constantGroupSchemePoint (g : G) : 𝟙_ (Over S) ⟶ constantGroupSchemeObj G S :=
  ε (Over.pullback (terminal.from S)) ≫
    (Over.pullback (terminal.from S)).map (constantComponent G g)

/-- The summands of `G_{Spec ℤ}` multiply as the group `G` does. -/
private theorem lift_constantComponent_mul (g h : G) :
    lift (constantComponent G g) (constantComponent G h) ≫ μ[constantSchemeOverIntegersObj G] =
      constantComponent G (g * h) :=
  (constantGroupSchemeStructure G).2 g h

/-- The summand of `G_{Spec ℤ}` indexed by `1` is its unit. -/
private theorem constantComponent_one :
    constantComponent G 1 = η[constantSchemeOverIntegersObj G] := by
  have h : constantComponent G 1 * constantComponent G 1 = constantComponent G 1 := by
    rw [Hom.mul_def, lift_constantComponent_mul, one_mul]
  rw [mul_eq_left.mp h, Hom.one_def]
  exact (congrArg (· ≫ η[constantSchemeOverIntegersObj G])
    (toUnit_unique (toUnit (𝟙_ (Over (⊤_ Scheme.{u})))) (𝟙 _))).trans (Category.id_comp _)

/-- The image of a product of global points under a monoidal functor. -/
private theorem lift_ε_map_μ {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {M : C} [MonObj M] (c d e : 𝟙_ C ⟶ M) (h : lift c d ≫ μ[M] = e) :
    lift (ε F ≫ F.map c) (ε F ≫ F.map d) ≫ (Functor.LaxMonoidal.μ F M M ≫ F.map μ[M]) =
      ε F ≫ F.map e := by
  rw [← comp_lift_assoc, Functor.Monoidal.lift_μ_assoc, ← F.map_comp, h]

/-- The `S`-points of `G_S` indexed by `g` and `h` multiply to the one indexed by `g * h`. -/
@[reassoc]
theorem lift_constantGroupSchemePoint_mul (g h : G) :
    lift (constantGroupSchemePoint G S g) (constantGroupSchemePoint G S h) ≫
      μ[constantGroupSchemeObj G S] = constantGroupSchemePoint G S (g * h) :=
  lift_ε_map_μ (Over.pullback (terminal.from S)) _ _ _ (lift_constantComponent_mul G g h)

/-- The unit of `G_S` is its `S`-point indexed by `1`. -/
theorem constantGroupSchemePoint_one :
    η[constantGroupSchemeObj G S] = constantGroupSchemePoint G S 1 := by
  simp only [constantGroupSchemePoint, constantComponent_one]
  rfl

/-! ### `G_S` and `G_S ×_S U` as disjoint unions -/

/-- `G_S` as a cofan over the constant family `S`, with the points `constantGroupSchemePoint` as
legs. -/
abbrev constantGroupSchemeCofan : Cofan (fun _ : G ↦ 𝟙_ (Over S)) :=
  Cofan.mk (constantGroupSchemeObj G S) (constantGroupSchemePoint G S)

omit [Group G] in
/-- On underlying schemes, the `g`-th point of `G_S` followed by the projection to `G_{Spec ℤ}` is
the `g`-th summand. -/
theorem constantGroupSchemePoint_left_fst (g : G) :
    (constantGroupSchemePoint G S g).left ≫
        pullback.fst (constantSchemeOverIntegersObj G).hom (terminal.from S) =
      terminal.from S ≫ Sigma.ι (fun _ : G ↦ ⊤_ Scheme.{u}) g := by
  have hmap : ((Over.pullback (terminal.from S)).map (constantComponent G g)).left ≫
      pullback.fst (constantSchemeOverIntegersObj G).hom (terminal.from S) =
      pullback.fst _ _ ≫ (constantComponent G g).left :=
    pullback.lift_fst _ _ _
  rw [constantGroupSchemePoint, Over.comp_left, Category.assoc, hmap, ← Category.assoc]
  exact congrArg (· ≫ (constantComponent G g).left)
    (IsTerminal.hom_ext terminalIsTerminal _ _)

omit [Group G] in
/-- On underlying schemes, the `g`-th point of `G_S` is a section of the structure morphism. -/
theorem constantGroupSchemePoint_left_snd (g : G) :
    (constantGroupSchemePoint G S g).left ≫
        pullback.snd (constantSchemeOverIntegersObj G).hom (terminal.from S) = 𝟙 S :=
  Over.w (constantGroupSchemePoint G S g)

/-- **`G_S` is the disjoint union of copies of `S` indexed by `G`**, the summands being the points
`AlgebraicGeometry.constantGroupSchemePoint`: base change along `S ⟶ Spec ℤ` of the decomposition
of `G_{Spec ℤ}`, disjoint unions of schemes being universal. -/
def isColimit_constantGroupSchemeCofan : IsColimit (constantGroupSchemeCofan G S) := by
  refine isColimitCofanOfIsColimitLeft _ (Classical.choice ?_)
  refine isUniversalColimit_sigmaCofan (fun _ : G ↦ ⊤_ Scheme.{u})
    (Cofan.mk (constantGroupSchemeObj G S).left
      (fun g ↦ (constantGroupSchemePoint G S g).left))
    (Discrete.natTrans fun _ ↦ terminal.from S)
    (pullback.fst (constantSchemeOverIntegersObj G).hom (terminal.from S)) ?_
    (.of_discrete _) fun ⟨g⟩ ↦ ?_
  · ext ⟨g⟩
    exact (constantGroupSchemePoint_left_fst G S g).symm
  · refine IsPullback.of_right ?_ (constantGroupSchemePoint_left_fst G S g)
      (IsPullback.of_hasPullback (constantSchemeOverIntegersObj G).hom (terminal.from S)).flip
    have h₁ : Sigma.ι (fun _ : G ↦ ⊤_ Scheme.{u}) g ≫ (constantSchemeOverIntegersObj G).hom =
        𝟙 _ := terminal.hom_ext _ _
    change IsPullback ((constantGroupSchemePoint G S g).left ≫ _) (terminal.from S)
      (terminal.from S) (Sigma.ι (fun _ : G ↦ ⊤_ Scheme.{u}) g ≫ _)
    rw [constantGroupSchemePoint_left_snd, h₁]
    exact IsPullback.id_horiz _

variable {G S}

/-- The `g`-th summand `U ⟶ G_S ×_S U`, `u ↦ (g, u)`. -/
def constantGroupSchemeLeg (U : Over S) (g : G) : U ⟶ constantGroupSchemeObj G S ⊗ U :=
  lift (toUnit U ≫ constantGroupSchemePoint G S g) (𝟙 U)

omit [Group G] in
/-- The first component of the `g`-th summand `U ⟶ G_S ×_S U` is the constant map to the
point `g`. -/
@[reassoc (attr := simp)]
theorem constantGroupSchemeLeg_fst (U : Over S) (g : G) :
    constantGroupSchemeLeg U g ≫ fst _ _ = toUnit U ≫ constantGroupSchemePoint G S g :=
  lift_fst _ _

omit [Group G] in
/-- The second component of the `g`-th summand `U ⟶ G_S ×_S U` is the identity of `U`. -/
@[reassoc (attr := simp)]
theorem constantGroupSchemeLeg_snd (U : Over S) (g : G) :
    constantGroupSchemeLeg U g ≫ snd _ _ = 𝟙 U :=
  lift_snd _ _

omit [Group G] in
/-- The `g`-th summand of `G_S ×_S U` is the base change of the `g`-th summand of `G_S`. -/
theorem isPullback_constantGroupSchemeLeg (U : Over S) (g : G) :
    IsPullback (constantGroupSchemeLeg U g) (toUnit U) (fst (constantGroupSchemeObj G S) U)
      (constantGroupSchemePoint G S g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.fst ≫ snd _ _) ?_ ?_ ?_⟩⟩
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · calc (s.fst ≫ snd _ _) ≫ constantGroupSchemeLeg U g ≫ fst _ _
          = ((s.fst ≫ snd _ _) ≫ toUnit U) ≫ constantGroupSchemePoint G S g := by simp
        _ = s.snd ≫ constantGroupSchemePoint G S g := by
          rw [toUnit_unique ((s.fst ≫ snd _ _) ≫ toUnit U) s.snd]
        _ = s.fst ≫ fst _ _ := s.condition.symm
    · simp [constantGroupSchemeLeg]
  · intro s
    exact toUnit_unique ((s.fst ≫ snd _ _) ≫ toUnit U) s.snd
  · intro s m hm _
    rw [← hm, Category.assoc, constantGroupSchemeLeg_snd, Category.comp_id]

/-- `G_S ×_S U` as a cofan over the constant family `U`, with the summands as legs. -/
abbrev constantGroupSchemeTensorCofan (U : Over S) : Cofan (fun _ : G ↦ U) :=
  Cofan.mk (constantGroupSchemeObj G S ⊗ U) (constantGroupSchemeLeg U)

/-- **`G_S ×_S U` is the disjoint union of copies of `U` indexed by `G`**, the summands being
`AlgebraicGeometry.constantGroupSchemeLeg`. -/
def isColimit_constantGroupSchemeTensorCofan (U : Over S) :
    IsColimit (constantGroupSchemeTensorCofan (G := G) U) :=
  Classical.choice <| isUniversalColimit_of_isColimit_cofanOver
    (isColimit_constantGroupSchemeCofan G S) (constantGroupSchemeTensorCofan U)
    (Discrete.natTrans fun _ ↦ toUnit U) (fst _ _)
    (by ext ⟨g⟩; simp) (.of_discrete _) fun ⟨g⟩ ↦ isPullback_constantGroupSchemeLeg U g

omit [Group G] in
/-- Two morphisms out of `G_S ×_S U` agree as soon as they agree on every summand. -/
theorem constantGroupSchemeTensor_hom_ext {U Y : Over S}
    {φ ψ : constantGroupSchemeObj G S ⊗ U ⟶ Y}
    (h : ∀ g : G, constantGroupSchemeLeg U g ≫ φ = constantGroupSchemeLeg U g ≫ ψ) : φ = ψ :=
  Cofan.IsColimit.hom_ext (isColimit_constantGroupSchemeTensorCofan U) _ _ h

/-! ### The action -/

/-- The action map `G_S ×_S U ⟶ U` of an abstract action: `a g` on the `g`-th summand. -/
def constantGroupSchemeSMul {U : Over S} (a : G →* Aut U) :
    constantGroupSchemeObj G S ⊗ U ⟶ U :=
  Cofan.IsColimit.desc (isColimit_constantGroupSchemeTensorCofan U) fun g ↦ (a g).asIso.hom

/-- On the `g`-th summand of `G_S ×_S U`, the action map `constantGroupSchemeSMul a` is the
automorphism `a g` of `U`. -/
@[reassoc (attr := simp)]
theorem constantGroupSchemeLeg_smulMap {U : Over S} (a : G →* Aut U) (g : G) :
    constantGroupSchemeLeg U g ≫ constantGroupSchemeSMul a = (a g).asIso.hom :=
  Cofan.IsColimit.fac (isColimit_constantGroupSchemeTensorCofan U) (fun g ↦ (a g).asIso.hom) g

/-- Precomposing the `g`-th summand with `x` is the pair of the constant point `g` and `x`. -/
private theorem comp_constantGroupSchemeLeg {H : Type v} [Small.{u} H] {T V : Over S}
    (x : T ⟶ V) (g : H) :
    x ≫ constantGroupSchemeLeg V g = lift (toUnit T ≫ constantGroupSchemePoint H S g) x := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, constantGroupSchemeLeg_fst, ← Category.assoc,
      toUnit_unique (x ≫ toUnit V) (toUnit T), lift_fst]
  · simp

private theorem leftUnitor_inv_whiskerRight_point (U : Over S) :
    (λ_ U).inv ≫ constantGroupSchemePoint G S 1 ▷ U = constantGroupSchemeLeg U 1 := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [constantGroupSchemeLeg]

private theorem leg_leg_associator_inv_mul (U : Over S) (g h : G) :
    constantGroupSchemeLeg U h ≫ constantGroupSchemeLeg (constantGroupSchemeObj G S ⊗ U) g ≫
        (α_ _ _ _).inv ≫ μ[constantGroupSchemeObj G S] ▷ U =
      constantGroupSchemeLeg U (g * h) := by
  have e := comp_constantGroupSchemeLeg (constantGroupSchemeLeg U h) g
  rw [reassoc_of% e, constantGroupSchemeLeg, lift_lift_associator_inv_assoc,
    lift_whiskerRight, ← comp_lift_assoc, lift_constantGroupSchemePoint_mul]
  rfl

private theorem leg_leg_whiskerLeft {U : Over S} (a : G →* Aut U) (g h : G) :
    constantGroupSchemeLeg U h ≫ constantGroupSchemeLeg (constantGroupSchemeObj G S ⊗ U) g ≫
        constantGroupSchemeObj G S ◁ constantGroupSchemeSMul a =
      (a h).asIso.hom ≫ constantGroupSchemeLeg U g := by
  have hu : constantGroupSchemeLeg U h ≫ toUnit (constantGroupSchemeObj G S ⊗ U) = toUnit U :=
    toUnit_unique _ _
  have hu' : (a h).asIso.hom ≫ toUnit U = toUnit U := toUnit_unique _ _
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, whiskerLeft_fst, constantGroupSchemeLeg_fst,
      ← Category.assoc, hu, Category.assoc, constantGroupSchemeLeg_fst, ← Category.assoc, hu']
  · rw [Category.assoc, Category.assoc, whiskerLeft_snd, constantGroupSchemeLeg_snd_assoc,
      constantGroupSchemeLeg_smulMap, Category.assoc, constantGroupSchemeLeg_snd,
      Category.comp_id]

/-- **The action of the constant group scheme `G_S` on `U` induced by an abstract action
`a : G →* Aut_S(U)`** (**Stacks 022Z**, **Stacks 03YW**): the action map `G_S ×_S U ⟶ U` is
`a g` on the summand of `G_S ×_S U` indexed by `g`. -/
@[instance_reducible]
def constantGroupSchemeModObj (U : Over S) (a : G →* Aut U) :
    ModObj (constantGroupSchemeObj G S) U where
  smul := constantGroupSchemeSMul a
  one_smul := by
    change η[constantGroupSchemeObj G S] ▷ U ≫ constantGroupSchemeSMul a = (λ_ U).hom
    rw [← cancel_epi (λ_ U).inv, constantGroupSchemePoint_one, ← Category.assoc,
      leftUnitor_inv_whiskerRight_point, constantGroupSchemeLeg_smulMap, map_one,
      Iso.inv_hom_id]
    rfl
  mul_smul := by
    change μ[constantGroupSchemeObj G S] ▷ U ≫ constantGroupSchemeSMul a =
      (α_ _ _ U).hom ≫ constantGroupSchemeObj G S ◁ constantGroupSchemeSMul a ≫
        constantGroupSchemeSMul a
    rw [← cancel_epi (α_ _ _ U).inv, Iso.inv_hom_id_assoc]
    refine constantGroupSchemeTensor_hom_ext fun g ↦ constantGroupSchemeTensor_hom_ext fun h ↦ ?_
    rw [reassoc_of% (leg_leg_associator_inv_mul U g h), constantGroupSchemeLeg_smulMap,
      reassoc_of% (leg_leg_whiskerLeft a g h), constantGroupSchemeLeg_smulMap, map_mul]
    rfl

/-- **The abstract action is recovered from the action of `G_S` on the summands of
`G_S ×_S U`:** on the summand indexed by `g` the action map of `G_S` is `a g`. -/
theorem constantGroupSchemeLeg_smul (U : Over S) (a : G →* Aut U) (g : G) :
    let := constantGroupSchemeModObj U a
    constantGroupSchemeLeg U g ≫ γ[constantGroupSchemeObj G S, U] = (a g).asIso.hom :=
  constantGroupSchemeLeg_smulMap a g

/-- **The abstract action is recovered on `T`-points:** the constant `T`-point of `G_S` with value
`g` acts on the `T`-points of `U` by composition with `a g`. -/
theorem constantGroupSchemePoint_smul (U : Over S) (a : G →* Aut U) (g : G) {T : Over S}
    (x : T ⟶ U) :
    let := constantGroupSchemeModObj U a
    (toUnit T ≫ constantGroupSchemePoint G S g) • x = x ≫ (a g).asIso.hom := by
  intro inst
  rw [Hom.smul_def, ← comp_constantGroupSchemeLeg x g, Category.assoc]
  exact congrArg (x ≫ ·) (constantGroupSchemeLeg_smul U a g)

/-- **Uniqueness:** an action of `G_S` on `U` which is `a g` on the summand of `G_S ×_S U` indexed
by `g`, for every `g`, is the action `AlgebraicGeometry.constantGroupSchemeModObj` of `a`. -/
theorem constantGroupSchemeModObj_unique (U : Over S) (a : G →* Aut U)
    (m : ModObj (constantGroupSchemeObj G S) U)
    (hm : ∀ g : G, constantGroupSchemeLeg U g ≫ m.smul = (a g).asIso.hom) :
    m = constantGroupSchemeModObj U a := by
  have : m.smul = (constantGroupSchemeModObj U a).smul :=
    constantGroupSchemeTensor_hom_ext fun g ↦ (hm g).trans (constantGroupSchemeLeg_smulMap a g).symm
  cases m
  simp only at this
  subst this
  rfl

/-! ### Freeness and transitivity -/

omit [Group G] in
/-- A `T`-point of `G_S` is, on the pieces of a decomposition of `T` indexed by `G`, constant:
two morphisms out of `T` agree as soon as they agree on each piece `T ×_{G_S} S` of `T` over the
summand of `G_S` indexed by `g`. -/
theorem hom_ext_of_constantGroupSchemePoint {T Y : Over S} (m : T ⟶ constantGroupSchemeObj G S)
    {φ ψ : T ⟶ Y}
    (h : ∀ g : G, pullback.fst m (constantGroupSchemePoint G S g) ≫ φ =
      pullback.fst m (constantGroupSchemePoint G S g) ≫ ψ) : φ = ψ := by
  obtain ⟨hc⟩ := isUniversalColimit_of_isColimit_cofanOver
    (isColimit_constantGroupSchemeCofan G S)
    (Cofan.mk T fun g ↦ pullback.fst m (constantGroupSchemePoint G S g))
    (Discrete.natTrans fun g ↦ pullback.snd m (constantGroupSchemePoint G S g.as)) m
    (by
      ext ⟨g⟩
      exact congrArg Over.Hom.left
        (pullback.condition (f := m) (g := constantGroupSchemePoint G S g)).symm) (.of_discrete _)
    fun ⟨g⟩ ↦ IsPullback.of_hasPullback m (constantGroupSchemePoint G S g)
  exact Cofan.IsColimit.hom_ext hc _ _ h

omit [Group G] in
private theorem pullback_fst_comp_point {T : Over S} (m : T ⟶ constantGroupSchemeObj G S)
    (g : G) :
    pullback.fst m (constantGroupSchemePoint G S g) ≫ m =
      toUnit _ ≫ constantGroupSchemePoint G S g := by
  rw [pullback.condition, toUnit_unique (pullback.snd _ _) (toUnit _)]

/-- **Freeness.** If the abstract action `a` is free on nonempty points — no `T`-point of `U`
with `T` nonempty is fixed by two distinct elements of `G` — then the action of `G_S` on `U` is
free in the sense of **Stacks 07S1**: for every `T`, the group `G_S(T)` acts freely on `U(T)`. -/
theorem isFreeAction_constantGroupSchemeModObj (U : Over S) (a : G →* Aut U)
    (ha : ∀ T : Over S, Nonempty T.left → ∀ (x : T ⟶ U) (g g' : G),
      x ≫ (a g).asIso.hom = x ≫ (a g').asIso.hom → g = g') :
    let := constantGroupSchemeModObj U a
    IsFreeAction (constantGroupSchemeObj G S) U := by
  intro inst T
  refine { toIsLeftCancelSMul := inferInstance, right_cancel' := fun m n x hmn ↦ ?_ }
  refine hom_ext_of_constantGroupSchemePoint m fun g ↦ ?_
  set p := pullback.fst m (constantGroupSchemePoint G S g)
  refine hom_ext_of_constantGroupSchemePoint (p ≫ n) fun h ↦ ?_
  set q := pullback.fst (p ≫ n) (constantGroupSchemePoint G S h)
  have hm : q ≫ p ≫ m = toUnit _ ≫ constantGroupSchemePoint G S g := by
    rw [pullback_fst_comp_point, ← Category.assoc, toUnit_unique (q ≫ toUnit _) (toUnit _)]
  have hn : q ≫ p ≫ n = toUnit _ ≫ constantGroupSchemePoint G S h :=
    pullback_fst_comp_point (p ≫ n) h
  rcases isEmpty_or_nonempty (pullback (p ≫ n) (constantGroupSchemePoint G S h)).left with
    hE | hE
  · exact Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext _ _)
  · have hx := congrArg ((q ≫ p) ≫ ·) hmn
    simp only [ModObj.comp_smul, Category.assoc, hm, hn, constantGroupSchemePoint_smul] at hx
    obtain rfl := ha _ hE (q ≫ p ≫ x) g h (by simpa only [Category.assoc] using hx)
    rw [hm, hn]

/-- **Transitivity.** If the abstract action `a` is transitive on the points of `U`, so is the
action of `G_S`: for any two points `u, v` of `U` there is a point of `G_S ×_S U` lying over `u`
under the projection and over `v` under the action map. -/
theorem exists_smul_eq_constantGroupSchemeModObj (U : Over S) (a : G →* Aut U)
    (ha : ∀ u v : U.left, ∃ g : G, (a g).asIso.hom.left u = v) (u v : U.left) :
    let := constantGroupSchemeModObj U a
    ∃ z : (constantGroupSchemeObj G S ⊗ U).left,
      (snd (constantGroupSchemeObj G S) U).left z = u ∧
        (γ[constantGroupSchemeObj G S, U]).left z = v := by
  intro inst
  obtain ⟨g, hg⟩ := ha u v
  refine ⟨(constantGroupSchemeLeg U g).left u, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, constantGroupSchemeLeg_snd]
    rfl
  · rwa [← Scheme.Hom.comp_apply, ← Over.comp_left, constantGroupSchemeLeg_smul]

end AlgebraicGeometry

end
