module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeDivisibility
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EffectiveFunctor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertCycleOfClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeComposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cycles of sections and graphs

Let `p : P ⟶ T` be locally of finite presentation and let `σ : T ⟶ P` be a section of `p` which is
a closed immersion. The closed subscheme `σ(T) ⊆ P` is isomorphic to `T` over `T`, hence flat, of
finite presentation and quasi-finite over `T`, so it is a member of `Hilb(P/T, 0)` and its cycle
`[σ(T)/P/T]_0` is a relative `0`-cycle: over a point `t` of `T` it is the point of the fibre lying
over `σ t`, with coefficient one. Base change of families of cycles carries this cycle to the
cycle of the base-changed section.

For `f : X ⟶ S` separated and locally of finite type over a locally Noetherian base this gives
the *diagonal cycle* of `X/S`, an element of `z^eff(X ×_S X / X, 0)`; its image under the map of
the functor `S' ↦ z^eff(X'/S', 0)` attached to a morphism `e : S' ⟶ X` over `S` is the cycle of
the graph of `e`. These are the cycles `[x]` of a point `x` of a fibre that Stacks Remark 0H5Y
writes down.

## Main definitions

* `Stacks.Chow.HilbertCycleDatum.ofSection` — the member `σ(T)` of `Hilb(P/T, 0)`.
* `Stacks.Chow.diagonalRelativeCycle` — the diagonal cycle of `X/S`, as an element of the value at
  `X` of `Stacks.Chow.effectiveRelativeCyclesFunctor`.
* `Stacks.Chow.graphSection` — the graph `S' ⟶ X ×_S S'` of a morphism `e : S' ⟶ X` over `S`.

## Main results

* `Stacks.Chow.baseChangeFamilyOfIsPullback_familyAssociatedToClosedSubscheme_section` — base
  change of the cycle of a section is the cycle of the base-changed section.
* `Stacks.Chow.effectiveRelativeCyclesFunctor_map_diagonalRelativeCycle_apply` — the pullback of
  the diagonal cycle along `e` is, over a point `t`, the point of the fibre lying on the graph of
  `e` with coefficient one.
* `Stacks.Chow.effectiveRelativeCyclesMap_add` — the maps of the functor are additive.

## References

* [Stacks Project, Remark 0H5Y](https://stacks.math.columbia.edu/tag/0H5Y)
* [Stacks Project, Section 0H6V](https://stacks.math.columbia.edu/tag/0H6V)
* [Stacks Project, Example 0H4S](https://stacks.math.columbia.edu/tag/0H4S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow

/-- A morphism locally of finite type and locally quasi-finite has relative dimension at most
zero. -/
theorem relativeDimensionLE_zero_of_locallyQuasiFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] : RelativeDimensionLE f 0 := fun x =>
  le_of_eq ((quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x).mp
    ((forall_quasiFiniteAt_iff f).mpr ⟨inferInstance, inferInstance⟩ x))

/-! ### The cycle of a section -/

namespace HilbertCycleDatum

variable {P T : Scheme.{u}} (p : P ⟶ T) (σ : T ⟶ P) [IsClosedImmersion σ] (hσ : σ ≫ p = 𝟙 T)

include hσ in
omit [IsClosedImmersion σ] in
/-- If `σ` is a section of `p`, then `σ ≫ p` is flat. -/
theorem flat_section : Flat (σ ≫ p) := by rw [hσ]; infer_instance

include hσ in
omit [IsClosedImmersion σ] in
/-- If `σ` is a section of `p`, then `σ ≫ p` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_section : LocallyOfFinitePresentation (σ ≫ p) := by
  rw [hσ]; infer_instance

include hσ in
omit [IsClosedImmersion σ] in
/-- If `σ` is a section of `p`, then `σ ≫ p` is quasi-compact. -/
theorem quasiCompact_section : QuasiCompact (σ ≫ p) := by rw [hσ]; infer_instance

include hσ in
omit [IsClosedImmersion σ] in
/-- If `σ` is a section of `p`, then `σ ≫ p` is locally quasi-finite. -/
theorem locallyQuasiFinite_section : LocallyQuasiFinite (σ ≫ p) := by rw [hσ]; infer_instance

/-- **The member `σ(T)` of `Hilb(P/T, 0)` attached to a section `σ` of `p` which is a closed
immersion.** -/
def ofSection : HilbertCycleDatum p 0 :=
  haveI := flat_section p σ hσ
  haveI := locallyOfFinitePresentation_section p σ hσ
  haveI := quasiCompact_section p σ hσ
  haveI := locallyQuasiFinite_section p σ hσ
  ofClosedImmersion p 0 σ (relativeDimensionLE_zero_of_locallyQuasiFinite _)

/-- The ideal sheaf of the member `σ(T)` of `Hilb(P/T, 0)` is the kernel of `σ`. -/
theorem ofSection_ideal : (ofSection p σ hσ).ideal = σ.ker := rfl

/-- The cycle family of the member `σ(T)` of `Hilb(P/T, 0)` is the family `[σ(T)/P/T]_0` of
`0`-cycles attached to the closed subscheme `σ(T)`. -/
theorem cycleFamily_ofSection [LocallyOfFinitePresentation p] :
    (ofSection p σ hσ).cycleFamily p = familyAssociatedToClosedSubscheme p σ 0 := by
  have := flat_section p σ hσ
  have := locallyOfFinitePresentation_section p σ hσ
  have := quasiCompact_section p σ hσ
  have := locallyQuasiFinite_section p σ hσ
  exact cycleFamily_ofClosedImmersion p 0 σ _

end HilbertCycleDatum

/-- The cycle `[σ(T)/P/T]_0` of a section is a relative `0`-cycle. -/
theorem isRelativeCycle_familyAssociatedToClosedSubscheme_section {P T : Scheme.{u}} (p : P ⟶ T)
    [LocallyOfFinitePresentation p] [IsLocallyNoetherian T] (σ : T ⟶ P) [IsClosedImmersion σ]
    (hσ : σ ≫ p = 𝟙 T) : IsRelativeCycle p 0 (familyAssociatedToClosedSubscheme p σ 0) := by
  rw [← HilbertCycleDatum.cycleFamily_ofSection p σ hσ]
  exact isRelativeCycle_cycleFamily _ _

/-- The cycle `[σ(T)/P/T]_0` of a section is effective. -/
theorem isEffectiveFamily_familyAssociatedToClosedSubscheme_section {P T : Scheme.{u}}
    (p : P ⟶ T) [LocallyOfFiniteType p] (σ : T ⟶ P) [IsClosedImmersion σ] (hσ : σ ≫ p = 𝟙 T) :
    IsEffectiveFamily p 0 (familyAssociatedToClosedSubscheme p σ 0) := by
  rw [isEffectiveFamily_iff]
  intro t x
  rw [familyAssociatedToClosedSubscheme_apply_of_section p σ hσ t x]
  split_ifs <;> norm_num

/-- A section of a morphism, base changed: in a cartesian square `a ≫ f = p ≫ g`, sections
`σ` of `f` and `σ'` of `p` with `σ' ≫ a = g ≫ σ` form a cartesian square. -/
theorem isPullback_section {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {a : P ⟶ X}
    {p : P ⟶ T} (sq : IsPullback a p f g) {σ : S ⟶ X} (hσ : σ ≫ f = 𝟙 S) {σ' : T ⟶ P}
    (hσ' : σ' ≫ p = 𝟙 T) (hσa : σ' ≫ a = g ≫ σ) : IsPullback σ' g a σ := by
  refine IsPullback.of_right ?_ hσa sq.flip
  rw [hσ', hσ]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **Base change of the cycle of a section.** In a cartesian square `a ≫ f = p ≫ g`, the base
change of the cycle `[σ(S)/X/S]_0` of a section `σ` of `f` is the cycle of the section `σ'` of `p`
induced by `σ`. -/
theorem baseChangeFamilyOfIsPullback_familyAssociatedToClosedSubscheme_section
    {X S T P : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] {g : T ⟶ S} {a : P ⟶ X}
    {p : P ⟶ T} [LocallyOfFinitePresentation p] (sq : IsPullback a p f g) (σ : S ⟶ X)
    [IsClosedImmersion σ] (hσ : σ ≫ f = 𝟙 S) (σ' : T ⟶ P) [IsClosedImmersion σ']
    (hσ' : σ' ≫ p = 𝟙 T) (hσa : σ' ≫ a = g ≫ σ) :
    baseChangeFamilyOfIsPullback f sq 0 (familyAssociatedToClosedSubscheme f σ 0) =
      familyAssociatedToClosedSubscheme p σ' 0 := by
  rw [← HilbertCycleDatum.cycleFamily_ofSection f σ hσ,
    ← HilbertCycleDatum.cycleFamily_ofIsPullback,
    HilbertCycleDatum.cycleFamily_eq_familyAssociatedToClosedSubscheme]
  have hker : ((HilbertCycleDatum.ofSection f σ hσ).ofIsPullback sq).ideal = σ'.ker := by
    rw [HilbertCycleDatum.ofIsPullback_ideal, HilbertCycleDatum.ofSection_ideal]
    have hpb := isPullback_section sq hσ hσ' hσa
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion σ a, ← hpb.isoPullback_hom_fst,
      Scheme.Hom.ker_comp_of_isIso]
  rw [hker]
  exact familyAssociatedToClosedSubscheme_eq_of_iso p _ σ'
    (HilbertCycleDatum.kerSubschemeIso σ').symm (HilbertCycleDatum.kerSubschemeIso_inv_comp σ') 0

/-! ### The diagonal cycle and the cycles of graphs -/

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The graph `S' ⟶ X ×_S S'` of a morphism `e : S' ⟶ X` over `S`, a section of the second
projection. -/
abbrev graphSection {O : Over S} (e : O ⟶ Over.mk f) : O.left ⟶ pullback f O.hom :=
  pullback.lift e.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w e)

/-- The graph of `e` is a section of the second projection `X ×_S S' ⟶ S'`. -/
theorem graphSection_snd {O : Over S} (e : O ⟶ Over.mk f) :
    graphSection f e ≫ pullback.snd f O.hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The graph of a morphism to a separated scheme is a closed immersion. -/
@[ega "I 5.3.11" "separated target", ega "I 5.4.3", ega "IV 20.4.1" "partial"]
instance isClosedImmersion_graphSection [IsSeparated f] {O : Over S} (e : O ⟶ Over.mk f) :
    IsClosedImmersion (graphSection f e) := by
  have : IsClosedImmersion (graphSection f e ≫ pullback.snd f O.hom) := by
    rw [graphSection_snd]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd f O.hom)

/-- The graph of `e`, followed by the top edge of the square relating `X ×_S S'` to `X ×_S X`,
is `e` followed by the diagonal. -/
theorem graphSection_comp_overBaseChange {O : Over S} (e : O ⟶ Over.mk f) :
    graphSection f e ≫ overBaseChangeMap f e = e.left ≫ graphSection f (𝟙 (Over.mk f)) := by
  apply pullback.hom_ext
  · simp only [overBaseChangeMap, graphSection, Category.assoc, pullback.lift_fst]
    rw [Over.id_left, Category.comp_id]
  · simp only [overBaseChangeMap, graphSection, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.id_comp, Category.comp_id, Over.id_left]

variable [LocallyOfFiniteType f] [IsSeparated f]

/-- **The pullback of the diagonal cycle along a morphism is the cycle of its graph.** For
`e : S' ⟶ X` over `S`, the base change of the diagonal cycle `[Δ(X)/X ×_S X/X]_0` along `e` is the
cycle `[Γ_e/X ×_S S'/S']_0` of the graph of `e`. -/
theorem baseChangeFamilyOfIsPullback_diagonal [IsLocallyNoetherian S] {O : Over S}
    (e : O ⟶ Over.mk f) :
    baseChangeFamilyOfIsPullback (pullback.snd f (Over.mk f).hom) (isPullback_overBaseChange f e) 0
        (familyAssociatedToClosedSubscheme (pullback.snd f (Over.mk f).hom)
          (graphSection f (𝟙 (Over.mk f))) 0) =
      familyAssociatedToClosedSubscheme (pullback.snd f O.hom) (graphSection f e) 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : LocallyOfFiniteType (pullback.snd f O.hom) := inferInstance
  have : LocallyOfFinitePresentation (pullback.snd f (Over.mk f).hom) := inferInstance
  exact baseChangeFamilyOfIsPullback_familyAssociatedToClosedSubscheme_section _
    (isPullback_overBaseChange f e) _ (graphSection_snd f _) _ (graphSection_snd f e)
    (graphSection_comp_overBaseChange f e)

end Diagonal

/-! ### The diagonal cycle as an element of the functor -/

section Functor

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S]

/-- The maps of the functor `S' ↦ z^eff(X'/S', r)` are additive. -/
theorem effectiveRelativeCyclesMap_add (r : ℕ) {T₁ T₂ : LocallyOfFiniteTypeOver S}
    (h : T₂ ⟶ T₁) (α β : ↥(effectiveRelativeCycles (pullback.snd f T₁.obj.hom) r)) :
    effectiveRelativeCyclesMap f r h (α + β) =
      effectiveRelativeCyclesMap f r h α + effectiveRelativeCyclesMap f r h β :=
  Subtype.ext (Subtype.ext (baseChangeFamilyOfIsPullback_add _ _ r _ _))

/-- `X`, as a scheme locally of finite type over `S`. -/
abbrev objOf : LocallyOfFiniteTypeOver S := ⟨Over.mk f, inferInstanceAs (LocallyOfFiniteType f)⟩

variable [IsSeparated f]

/-- **The diagonal cycle** of a separated morphism `f : X ⟶ S` locally of finite type: the cycle
`[Δ(X)/X ×_S X/X]_0` of the diagonal, an element of `z^eff(X ×_S X / X, 0)`, the value at `X` of
the functor `S' ↦ z^eff(X'/S', 0)`. Over a point `x` of `X` it is the point `x` of the fibre
`X_{f x} ⊗ κ(x)` with coefficient one. -/
def diagonalRelativeCycle : (effectiveRelativeCyclesFunctor f 0).obj (op (objOf f)) :=
  haveI : IsLocallyNoetherian (Over.mk f).left := LocallyOfFiniteType.isLocallyNoetherian f
  ⟨⟨familyAssociatedToClosedSubscheme (pullback.snd f (Over.mk f).hom)
      (graphSection f (𝟙 (Over.mk f))) 0,
    isRelativeCycle_familyAssociatedToClosedSubscheme_section (pullback.snd f (Over.mk f).hom)
      (graphSection f (𝟙 (Over.mk f))) (graphSection_snd f _)⟩,
    isEffectiveFamily_familyAssociatedToClosedSubscheme_section (pullback.snd f (Over.mk f).hom)
      (graphSection f (𝟙 (Over.mk f))) (graphSection_snd f _)⟩

/-- **The pullback of the diagonal cycle along `e : S' ⟶ X` is the cycle of the graph of `e`**:
over a point `t` of `S'` it is the point of the fibre lying on the graph, with coefficient one. -/
theorem effectiveRelativeCyclesFunctor_map_diagonalRelativeCycle_apply
    {T : LocallyOfFiniteTypeOver S} (e : T ⟶ objOf f) (t : T.obj.left)
    (x : (pullback.snd f T.obj.hom).fiber t) :
    (((effectiveRelativeCyclesFunctor f 0).map e.op (diagonalRelativeCycle f)).1.1 t :
        AlgebraicCycle _ ℤ) x =
      open Classical in
      if (pullback.snd f T.obj.hom).fiberι t x = graphSection f e.hom t then 1 else 0 := by
  have h := baseChangeFamilyOfIsPullback_diagonal f e.hom
  have h2 := congrArg (fun γ : FamilyOfCycles (pullback.snd f T.obj.hom) 0 =>
    (γ t : AlgebraicCycle _ ℤ) x) h
  refine h2.trans ?_
  exact familyAssociatedToClosedSubscheme_apply_of_section (pullback.snd f T.obj.hom)
    (graphSection f e.hom) (graphSection_snd f _) t x

end Functor

end Stacks.Chow

end
