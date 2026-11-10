module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections

/-!
# `Rj_*` is fully faithful: the counit of `j^* ⊣ Rj_*` is invertible

Let `j : X ⟶ Y` be an open immersion of schemes. Restriction of sheaves of modules along `j` is
left adjoint to direct image, and the counit of that underived adjunction is an isomorphism:
`j^* j_* = id`, Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`. This
file descends that statement to the derived adjunction `j^* ⊣ Rj_*`,
`Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction`, at an arbitrary model of
the two derived categories: `j^* Rj_* = id`, i.e. `Rj_*` is fully faithful.

The descent is abstract and costs nothing beyond the universal property of a right derived
functor. For an adjunction `adj : F ⊣ G` of additive functors between abelian categories with `F`
exact, Mathlib's `CategoryTheory.Adjunction.derivedε` is *by construction* the natural
transformation `RG ⋙ LF ⟶ 𝟭` obtained by descending

  `(F ⋙ L₁) ⋙ G' ⟶ L₂`,  `α.app (G X) ≫ L₂.map (adj.counit.app X)`

along the localization `L₂`, using that `RG ⋙ LF` is the right derived functor of the left-hand
side. If `α` and `adj.counit` are invertible then that comparison is an isomorphism, so the
identity functor is *also* a right derived functor of the same functor, and
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc` turns the uniqueness of
right derived functors into invertibility of the descent. No K-injective resolution has to be
written down and no complex is transported: only the structure actually needed, which is the
comparison `α`.

The two remaining steps are bookkeeping. The counit of
`Stacks.SmallDerivedCategory.derivedAdjunction` is `CategoryTheory.Adjunction.derivedε` of the
adjunction read on homotopy categories; and the counit of that homotopy-category adjunction is
invertible whenever `adj.counit` is, because `Stacks.SmallDerivedCategory.homotopyAdjunction` is
`CategoryTheory.Adjunction.localization` and `CategoryTheory.Adjunction.localization_counit_app`
expresses its counit on the image of a cochain complex as the degreewise counit conjugated by two
isomorphisms.

## Main results

* `CategoryTheory.Adjunction.isIso_derivedε` — the abstract statement: the counit of
  `CategoryTheory.Adjunction.derived` is invertible as soon as the comparison for the left derived
  functor and the underived counit are.
* `Stacks.SmallDerivedCategory.isIso_homotopyAdjunction_counit` — the counit of an adjunction read
  on homotopy categories of cochain complexes is invertible if the underived one is.
* `Stacks.SmallDerivedCategory.isIso_derivedAdjunction_counit` — the counit of
  `Stacks.SmallDerivedCategory.derivedAdjunction` is invertible if the underived counit is.
* `Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit` and
  `Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit_app` —
  **`Rj_*` is fully faithful along an open immersion of schemes**, at an arbitrary model of the two
  derived categories.

## Implementation notes

No `HasDerivedCategory.standard` appears in any statement: every derived category is an instance
argument, inherited from `Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction`,
which is stated at a free model. This is what makes the result usable at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the only model at which the
compact-generation statements of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] have content.

No `@[stacks]` attribute is attached. The statement is an input to [Stacks, Tag 09IR] and to
[Stacks, Tag 0GEK] rather than the content of a tag of its own.

## References

* [The Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [The Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe w u

namespace CategoryTheory.Adjunction

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  {G' : D₁ ⥤ D₂} {F' : D₂ ⥤ D₁}
  (α : L₁ ⋙ G' ⟶ G ⋙ L₂) (β : F ⋙ L₁ ⟶ L₂ ⋙ F')
  [(F' ⋙ G').IsRightDerivedFunctor
    (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂]

/-- The comparison `(F ⋙ L₁) ⋙ G' ⟶ L₂ ⋙ 𝟭 D₂` whose descent along `L₂` is
`CategoryTheory.Adjunction.derivedε`: the underived counit, read through the comparison `α` for
the left derived functor. -/
private def derivedεSrc : (F ⋙ L₁) ⋙ G' ⟶ L₂ ⋙ 𝟭 D₂ :=
  (Functor.associator _ _ _).hom ≫ whiskerLeft F α ≫ (Functor.associator _ _ _).inv ≫
    whiskerRight adj.counit _ ≫ L₂.leftUnitor.hom ≫ L₂.rightUnitor.inv

private lemma derivedε_eq_rightDerivedDesc :
    adj.derivedε W₂ α β = (F' ⋙ G').rightDerivedDesc
      (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂ (𝟭 D₂) (derivedεSrc adj α) :=
  rfl

private lemma derivedεSrc_app (X : C₂) :
    (derivedεSrc adj α).app X = α.app (F.obj X) ≫ L₂.map (adj.counit.app X) := by
  simp [derivedεSrc]

/-- **The counit of a derived adjunction is invertible when the underived one is.** Let
`adj : G ⊣ F` be an adjunction, let `G'` be a left derived functor of `G` with comparison `α` and
`F'` a right derived functor of `F` with comparison `β`, and suppose `F' ⋙ G'` is again a right
derived functor, so that `CategoryTheory.Adjunction.derived` produces an adjunction `G' ⊣ F'`.
If `α` is an isomorphism — which is the case when `G` is exact, so that no derivation is involved
on the left — and the counit of `adj` is an isomorphism, then so is the counit of the derived
adjunction; equivalently, `F'` is fully faithful.

The derived counit is by construction the descent of `α` followed by the underived counit, so
under these hypotheses it descends an isomorphism; the identity functor is then a second right
derived functor of the same functor, and uniqueness of right derived functors does the rest. -/
lemma isIso_derivedε [IsIso α] [IsIso adj.counit] : IsIso (adj.derivedε W₂ α β) := by
  have happ : ∀ X : C₂, IsIso ((derivedεSrc adj α).app X) := fun X => by
    have : IsIso (α.app (F.obj X)) := NatIso.isIso_app_of_isIso α _
    have : IsIso (adj.counit.app X) := NatIso.isIso_app_of_isIso adj.counit X
    rw [derivedεSrc_app]
    infer_instance
  have : IsIso (derivedεSrc adj α) := NatIso.isIso_of_isIso_app _
  rw [derivedε_eq_rightDerivedDesc,
    ← Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc]
  exact Functor.isRightDerivedFunctor_of_inverts W₂ (𝟭 D₂) (asIso (derivedεSrc adj α)).symm

end CategoryTheory.Adjunction

namespace Stacks.SmallDerivedCategory

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] {C₂ : Type*} [Category* C₂] [Abelian C₂]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} [F.Additive] [G.Additive]

/-- The counit of the degreewise adjunction is the degreewise counit, hence invertible when
`adj.counit` is. -/
private lemma isIso_mapHomologicalComplex_counit (adj : F ⊣ G) [IsIso adj.counit]
    {ι : Type*} (c : ComplexShape ι) :
    IsIso (adj.mapHomologicalComplex c).counit :=
  (NatIso.mapHomologicalComplex (asIso adj.counit) c).isIso_hom

/-- **The counit of an adjunction read on homotopy categories is invertible when the underived
one is.** `Stacks.SmallDerivedCategory.homotopyAdjunction` is the localization of the degreewise
adjunction along the quotient functors, so by
`CategoryTheory.Adjunction.localization_counit_app` its counit on the image of a cochain complex
is the degreewise counit conjugated by the two comparison isomorphisms; the degreewise counit is
invertible because `adj.counit` is, degree by degree. -/
lemma isIso_homotopyAdjunction_counit (adj : F ⊣ G) [IsIso adj.counit] :
    IsIso (homotopyAdjunction adj).counit := by
  have := isIso_mapHomologicalComplex_counit adj (ComplexShape.up ℤ)
  have happ : ∀ Z : HomotopyCategory C₂ (ComplexShape.up ℤ),
      IsIso ((homotopyAdjunction adj).counit.app Z) := fun Z => by
    change IsIso ((homotopyAdjunction adj).counit.app
      ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj Z.as))
    simp only [homotopyAdjunction, Adjunction.localization_counit_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

section

variable [HasDerivedCategory C₁] [HasDerivedCategory C₂] (adj : F ⊣ G)
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {LF : DerivedCategory C₁ ⥤ DerivedCategory C₂} (e : LF ≅ F.mapDerivedCategory)
  {RG : DerivedCategory C₂ ⥤ DerivedCategory C₁}
  (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)
  (hC₂ : ∀ K : CochainComplex C₂ ℤ, ∃ (I : CochainComplex C₂ ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  [RG.IsRightDerivedFunctor β (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ))]

include hC₂ in
/-- **The counit of `Stacks.SmallDerivedCategory.derivedAdjunction` is invertible when the
underived counit is**, i.e. `RG` is fully faithful as soon as `G` is. The comparison for the left
derived functor is the isomorphism `e`, no derivation being involved on the left, so this is
`CategoryTheory.Adjunction.isIso_derivedε` for the adjunction read on homotopy categories. -/
theorem isIso_derivedAdjunction_counit [IsIso adj.counit] :
    IsIso (derivedAdjunction adj e β hC₂).counit := by
  have := isRightDerivedFunctor_comp_leftDerived (LF := LF) β hC₂
  have : IsIso (homotopyAdjunction adj).counit := isIso_homotopyAdjunction_counit adj
  have hcounit : (derivedAdjunction adj e β hC₂).counit =
      (homotopyAdjunction adj).derivedε
        (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ)) (leftDerivedFactorsQh e).hom β := by
    dsimp only [derivedAdjunction]
    rw [Adjunction.derived_counit]
  rw [hcounit]
  exact Adjunction.isIso_derivedε _ _ _ _

end

end Stacks.SmallDerivedCategory

namespace Stacks.Duality.OpenImmersion

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- **`Rj_*` is fully faithful along an open immersion of schemes**: the counit of the derived
adjunction `j^* ⊣ Rj_*`,
`Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction`, is an isomorphism, at an
arbitrary model of the two derived categories.

Restriction along an open immersion is exact and its underived counit `j^* j_* = id` is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`, so this is
`Stacks.SmallDerivedCategory.isIso_derivedAdjunction_counit`. -/
instance isIso_derivedRestrictPushforwardAdjunction_counit :
    IsIso (derivedRestrictPushforwardAdjunction j).counit :=
  Stacks.SmallDerivedCategory.isIso_derivedAdjunction_counit
    (Scheme.Modules.restrictAdjunction j) (Iso.refl _) _
    (AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X)

/-- **`j^* Rj_* = id` at every object**: the pointwise form of
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit`, which is the
shape in which [Stacks, Tag 09IR] and [Stacks, Tag 0GEK] consume it. -/
instance isIso_derivedRestrictPushforwardAdjunction_counit_app
    (Z : DerivedCategory X.Modules) :
    IsIso ((derivedRestrictPushforwardAdjunction j).counit.app Z) :=
  NatIso.isIso_app_of_isIso _ Z

end Stacks.Duality.OpenImmersion

end
