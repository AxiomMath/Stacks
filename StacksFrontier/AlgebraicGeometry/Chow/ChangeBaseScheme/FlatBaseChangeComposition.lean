module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChowPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of flat base changes for Chow homology

Let `(S, δ)`, `(S', δ')` and `(S'', δ'')` be bases for Chow homology, and let `g : S' ⟶ S` and
`g' : S'' ⟶ S'` be flat morphisms which are base changes of Chow situations with dimension
shifts `c` and `c'`. This file proves Stacks 0FVP: the composite `g ∘ g'` is again a flat base
change of Chow situations, with dimension shift `c + c'`, and the pullback homomorphisms on
cycle groups and on Chow groups compose accordingly.

## Main definitions

* `Stacks.Chow.FlatBaseChangeSituation.second` — the second of two composable flat base changes.
* `Stacks.Chow.FlatBaseChangeSituation.comp` — the composite flat base change.

## Main results

* `Stacks.Chow.composed_dimensionFunction_eq_add` — **Stacks 0FVP, part (1)**, the dimension
  functions differ by `c + c'` on the generic points of the fibres of the composite.

## Implementation notes

A generic point `s''` of an irreducible component of the fibre of `g ∘ g'` over `s` is a generic
point of the corresponding fibre of `g'`, because a strict generalization inside the latter
fibre already lies inside the former. Its image `s'` is a generic point of a component of the
fibre of `g` over `s`, and this is where flatness of `g'` enters: a strict generalization of `s'`
inside that fibre lifts to a strict generalization of `s''` inside the fibre of `g ∘ g'`.

## References

* [Stacks Project, Tag 0FVP](https://stacks.math.columbia.edu/tag/0FVP)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The fibre of a morphism of schemes over a point is a sober space. -/
private theorem quasiSober_fiber {X Y : Scheme.{u}} (h : X ⟶ Y) (y : Y) :
    QuasiSober (h ⁻¹' {y} : Set X) :=
  (h.fiberHomeo y).symm.isOpenEmbedding.quasiSober

/-- A point of the fibre specializing to a generic point of an irreducible component of the fibre
is equal to it. -/
private theorem eq_of_specializes_of_mem_genericPoints_fiber {X Z : Scheme.{u}} (h : X ⟶ Z)
    (s : Z) (s'' : genericPoints (h ⁻¹' {s} : Set X)) (w : X) (hw : h w = s)
    (hsp : w ⤳ s''.1.1) : w = s''.1.1 := by
  have := quasiSober_fiber h s
  exact congrArg Subtype.val ((TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq
    s''.1).1 s''.2 (⟨w, hw⟩ : (h ⁻¹' {s} : Set X)) ((subtype_specializes_iff _ s''.1).2 hsp))

/-- A generic point of an irreducible component of a fibre of a composite `g ∘ g'` is a generic
point of an irreducible component of the corresponding fibre of `g'`: a strict generalization
inside the fibre of `g'` has the same image under `g'`, hence the same image under `g ∘ g'`, so
it lies inside the fibre of the composite, where no strict generalization exists. -/
@[ega "0 2.1.8" "partial, special case"]
private theorem mem_genericPoints_fiber_second {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (g' : X ⟶ Y)
    (s : Z) (s'' : genericPoints ((g' ≫ g) ⁻¹' {s} : Set X)) :
    (⟨s''.1.1, rfl⟩ : (g' ⁻¹' {g' s''.1.1} : Set X)) ∈
      genericPoints (g' ⁻¹' {g' s''.1.1} : Set X) := by
  have := quasiSober_fiber g' (g' s''.1.1)
  refine (TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq _).2 fun z hz ↦ ?_
  have hzsp : (z : X) ⤳ s''.1.1 := (subtype_specializes_iff z ⟨s''.1.1, rfl⟩).1 hz
  have hzMem : (g' ≫ g) (z : X) = s := by
    rw [Scheme.Hom.comp_apply, show g' (z : X) = g' s''.1.1 from z.2,
      ← Scheme.Hom.comp_apply g' g s''.1.1]
    exact s''.1.2
  exact Subtype.ext (eq_of_specializes_of_mem_genericPoints_fiber (g' ≫ g) s s'' z hzMem hzsp)

/-! ### Base change on cycle groups along an arbitrary cartesian square -/

/-- The base-change homomorphism `Z_k(X) ⟶ Z_{k+c}(Y)` on cycle groups attached to a flat base
change of Chow situations with dimension shift `c`, written for an arbitrary cartesian square
realizing `Y` as the base change of `X` rather than for the chosen fibre product. -/
def baseChangeCyclePullbackSquare (B : FlatBaseChangeSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S}
    [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ) :
    CycleGroup B.base f k →+ CycleGroup B.baseChange q (k + B.c) :=
  (properPushforwardHom B.baseChange (pullback.snd f B.g) q sq.isoPullback.inv
      (isoPullback_inv_comp_snd B f sq) (k + B.c)).comp
    (baseChangeCyclePullback B f k)

/-- The base change of a cycle along a cartesian square is the base change along the chosen
fibre product, reindexed by the comparison isomorphism. -/
theorem baseChangeCyclePullbackSquare_apply_isoPullback (B : FlatBaseChangeSituation.{u})
    {X Y : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ)
    (z : CycleGroup B.base f k) (y : Y) :
    (baseChangeCyclePullbackSquare B f sq k z).1 y =
      (baseChangeCyclePullback B f k z).1 (sq.isoPullback.hom.base y) := by
  have hy : sq.isoPullback.inv.base (sq.isoPullback.hom.base y) = y :=
    congrArg (fun m : Y ⟶ Y ↦ m.base y) sq.isoPullback.hom_inv_id
  have hmain := properPushforward_apply_of_isIso B.baseChange (pullback.snd f B.g) q
    sq.isoPullback.inv (isoPullback_inv_comp_snd B f sq) (k + B.c)
    (baseChangeCyclePullback B f k z) (sq.isoPullback.hom.base y)
  rwa [hy] at hmain

/-- The coefficient of the base change of a cycle along a cartesian square: the coefficient of
the cycle at the image point, times the multiplicity of the point in the inverse image of the
reduced closure of that image. -/
theorem baseChangeCyclePullbackSquare_apply (B : FlatBaseChangeSituation.{u})
    {X Y : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ)
    (z : CycleGroup B.base f k) (y : Y) :
    (baseChangeCyclePullbackSquare B f sq k z).1 y =
      z.1 (p.base y) * flatPullbackWeight B.baseChange q p (k + B.c) y := by
  have hpt : (pullback.fst f B.g).base (sq.isoPullback.hom.base y) = p.base y := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m : Y ⟶ X ↦ m.base y) sq.isoPullback_hom_fst
  have hw := flatPullbackWeight_eq_of_isIso B.baseChange q (pullback.snd f B.g)
    (𝟙 X) sq.isoPullback.hom sq.isoPullback_hom_snd p (pullback.fst f B.g)
    ((Category.comp_id p).trans sq.isoPullback_hom_fst.symm) (k + B.c) y
  rw [baseChangeCyclePullbackSquare_apply_isoPullback B f sq k z y,
    baseChangeCyclePullback_apply B f k z (sq.isoPullback.hom.base y), hpt, hw]

/-- The pullback of a closed immersion `ι` along `p` is isomorphic to its pullback along the
first projection of the chosen fibre product, compatibly with the second projections. -/
private theorem exists_iso_pullback_snd_comp_isoPullback (B : FlatBaseChangeSituation.{u})
    {X Y W : Scheme.{u}} (f : X ⟶ B.base.S) {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S}
    (sq : IsPullback p q f B.g) (ι : W ⟶ X) [IsClosedImmersion ι] :
    ∃ e : (pullback ι p : Scheme.{u}) ≅ (pullback ι (pullback.fst f B.g) : Scheme.{u}),
      e.hom ≫ pullback.snd ι (pullback.fst f B.g) = pullback.snd ι p ≫ sq.isoPullback.hom :=
  ⟨asIso (pullback.map ι p ι (pullback.fst f B.g) (𝟙 W) sq.isoPullback.hom (𝟙 X)
      ((Category.comp_id ι).trans (Category.id_comp ι).symm)
      ((Category.comp_id p).trans sq.isoPullback_hom_fst.symm)), pullback.lift_snd _ _ _⟩

/-- **Stacks Project, Tag 0FVI, part (1), along an arbitrary cartesian square.** The base change
of the fundamental cycle of a closed subscheme `W ⊆ X` of delta-dimension at most `k` is the
fundamental cycle of the base change of `W`. -/
theorem baseChangeCyclePullbackSquare_cycleAssociatedToClosedSubscheme
    (B : FlatBaseChangeSituation.{u}) {X Y W : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q]
    (sq : IsPullback p q f B.g) (ι : W ⟶ X) [IsClosedImmersion ι] (k : ℤ)
    (hW : schemeDeltaDimension B.base (ι ≫ f) ≤ (k : EInt)) :
    baseChangeCyclePullbackSquare B f sq k (cycleAssociatedToClosedSubscheme B.base f ι k) =
      cycleAssociatedToClosedSubscheme B.baseChange q (pullback.snd ι p) (k + B.c) := by
  obtain ⟨e, hcomp⟩ := exists_iso_pullback_snd_comp_isoPullback B f sq ι
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [baseChangeCyclePullbackSquare_apply_isoPullback B f sq k _ y,
    baseChangeCyclePullback_cycleAssociatedToClosedSubscheme B f ι k hW]
  change closedSubschemeCycleCoeff B.baseChange (pullback.snd f B.g)
      (pullback.snd ι (pullback.fst f B.g)) (k + B.c) (sq.isoPullback.hom.base y) =
    closedSubschemeCycleCoeff B.baseChange q (pullback.snd ι p) (k + B.c) y
  rw [closedSubschemeCycleCoeff_of_isIso_ambient B.baseChange q (pullback.snd f B.g)
    sq.isoPullback.hom sq.isoPullback_hom_snd (pullback.snd ι p) (k + B.c) y]
  exact (closedSubschemeCycleCoeff_eq_of_iso B.baseChange (pullback.snd f B.g)
    (pullback.snd ι p ≫ sq.isoPullback.hom) (pullback.snd ι (pullback.fst f B.g))
    e hcomp (k + B.c) (sq.isoPullback.hom.base y)).symm

variable (B : FlatBaseChangeSituation.{u}) (C : ChowSituation.{u}) (g' : C.S ⟶ B.baseChange.S)
  [Flat g'] (c' : ℤ)
  (hg' : ∀ (s' : B.baseChange.S) (s'' : genericPoints (g' ⁻¹' {s'} : Set C.S)),
    C.dimensionFunction s''.1.1 = B.baseChange.dimensionFunction s' + c')

/-- The second of two composable flat base changes of Chow situations: the base is the base
change of the first. -/
@[reducible] def FlatBaseChangeSituation.second : FlatBaseChangeSituation.{u} where
  base := B.baseChange
  baseChange := C
  g := g'
  c := c'
  dimensionFunction_eq_add := hg'

/-- The base of `FlatBaseChangeSituation.second` is the base change of `B`. -/
@[simp]
theorem FlatBaseChangeSituation.second_base :
    (FlatBaseChangeSituation.second B C g' c' hg').base = B.baseChange :=
  rfl

/-- The base change of `FlatBaseChangeSituation.second` is `C`. -/
@[simp]
theorem FlatBaseChangeSituation.second_baseChange :
    (FlatBaseChangeSituation.second B C g' c' hg').baseChange = C :=
  rfl

/-- The flat morphism of `FlatBaseChangeSituation.second` is `g'`. -/
@[simp]
theorem FlatBaseChangeSituation.second_g :
    (FlatBaseChangeSituation.second B C g' c' hg').g = g' :=
  rfl

/-- The dimension shift of `FlatBaseChangeSituation.second` is `c'`. -/
@[simp]
theorem FlatBaseChangeSituation.second_c :
    (FlatBaseChangeSituation.second B C g' c' hg').c = c' :=
  rfl

/-! ### The dimension shift of a composite -/

include hg' in
/-- **Stacks Project, Tag 0FVP, part (1).** For composable flat base changes of Chow situations
with dimension shifts `B.c` and `c'`, every generic point `s''` of the fibre of `g' ≫ B.g` over
`s` satisfies `δ''(s'') = δ(s) + (B.c + c')`. -/
@[stacks 0FVP "part (1): the composite dimension shift is the sum of the two shifts"]
theorem composed_dimensionFunction_eq_add (s : B.base.S)
    (s'' : genericPoints ((g' ≫ B.g) ⁻¹' {s} : Set C.S)) :
    C.dimensionFunction s''.1.1 = B.base.dimensionFunction s + (B.c + c') := by
  have := quasiSober_fiber B.g s
  have hmem : B.g (g' s''.1.1) = s := by
    rw [← Scheme.Hom.comp_apply g' B.g s''.1.1]
    exact s''.1.2
  have hB : (⟨g' s''.1.1, hmem⟩ : (B.g ⁻¹' {s} : Set B.baseChange.S)) ∈
      genericPoints (B.g ⁻¹' {s} : Set B.baseChange.S) := by
    refine (TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq _).2 fun z hz ↦ ?_
    obtain ⟨w', hw'sp, hw'eq⟩ :=
      Flat.generalizingMap g' ((subtype_specializes_iff z ⟨g' s''.1.1, hmem⟩).1 hz)
    have hw'mem : (g' ≫ B.g) w' = s := by
      rw [Scheme.Hom.comp_apply, hw'eq]
      exact z.2
    have hww := eq_of_specializes_of_mem_genericPoints_fiber (g' ≫ B.g) s s'' w' hw'mem hw'sp
    exact Subtype.ext (by rw [← hw'eq, hww])
  rw [hg' (g' s''.1.1) ⟨⟨s''.1.1, rfl⟩, mem_genericPoints_fiber_second B.g g' s s''⟩,
    B.dimensionFunction_eq_add s ⟨⟨g' s''.1.1, hmem⟩, hB⟩, add_assoc]

/-- The composite of two composable flat base changes of Chow situations, with dimension shift
the sum of the two shifts. -/
@[reducible] def FlatBaseChangeSituation.comp : FlatBaseChangeSituation.{u} where
  base := B.base
  baseChange := C
  g := g' ≫ B.g
  c := B.c + c'
  dimensionFunction_eq_add := composed_dimensionFunction_eq_add B C g' c' hg'

/-- The base of `FlatBaseChangeSituation.comp` is the base of `B`. -/
@[simp]
theorem FlatBaseChangeSituation.comp_base :
    (FlatBaseChangeSituation.comp B C g' c' hg').base = B.base :=
  rfl

/-- The base change of `FlatBaseChangeSituation.comp` is `C`. -/
@[simp]
theorem FlatBaseChangeSituation.comp_baseChange :
    (FlatBaseChangeSituation.comp B C g' c' hg').baseChange = C :=
  rfl

/-- The flat morphism of `FlatBaseChangeSituation.comp` is the composite `g' ≫ B.g`. -/
@[simp]
theorem FlatBaseChangeSituation.comp_g :
    (FlatBaseChangeSituation.comp B C g' c' hg').g = g' ≫ B.g :=
  rfl

/-- The dimension shift of `FlatBaseChangeSituation.comp` is the sum `B.c + c'`. -/
@[simp]
theorem FlatBaseChangeSituation.comp_c :
    (FlatBaseChangeSituation.comp B C g' c' hg').c = B.c + c' :=
  rfl

/-! ### Iterated base change of a closed subscheme -/

private theorem schemeDeltaDimension_congr_morphism (D : ChowSituation.{u}) {X : Scheme.{u}}
    (f g : X ⟶ D.S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f = g) :
    schemeDeltaDimension D f = schemeDeltaDimension D g := by
  cases h
  rfl

/-- **Stacks Project, Tag 0FVI, part (1), dimension bound, along an arbitrary cartesian
square.** -/
theorem schemeDeltaDimension_baseChangeSquare_le (B : FlatBaseChangeSituation.{u})
    {X Y W : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g)
    (ι : W ⟶ X) [IsClosedImmersion ι] {k : ℤ}
    (hW : schemeDeltaDimension B.base (ι ≫ f) ≤ (k : EInt)) :
    schemeDeltaDimension B.baseChange (pullback.snd ι p ≫ q) ≤ ((k + B.c : ℤ) : EInt) := by
  obtain ⟨e, hcomp⟩ := exists_iso_pullback_snd_comp_isoPullback B f sq ι
  have he : e.hom ≫ (pullback.snd ι (pullback.fst f B.g) ≫ pullback.snd f B.g) =
      pullback.snd ι p ≫ q := by
    rw [← Category.assoc, hcomp, Category.assoc, sq.isoPullback_hom_snd]
  rw [← schemeDeltaDimension_congr_morphism B.baseChange _ _ he,
    schemeDeltaDimension_comp_iso B.baseChange e]
  exact schemeDeltaDimension_baseChange_closedSubscheme_le B f ι hW

/-- Base changing a closed subscheme twice is base changing it once along the composite. -/
theorem cycleAssociatedToClosedSubscheme_iterated_pullback (D : ChowSituation.{u})
    {X Y₁ Y₂ W : Scheme.{u}} (sY₂ : Y₂ ⟶ D.S) [LocallyOfFiniteType sY₂]
    (ι : W ⟶ X) [IsClosedImmersion ι] (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ Y₁) (k : ℤ) :
    cycleAssociatedToClosedSubscheme D sY₂ (pullback.snd (pullback.snd ι p₁) p₂) k =
      cycleAssociatedToClosedSubscheme D sY₂ (pullback.snd ι (p₂ ≫ p₁)) k :=
  cycleAssociatedToClosedSubscheme_eq_of_iso D sY₂ _ _ (pullbackLeftPullbackSndIso ι p₁ p₂)
    (pullbackLeftPullbackSndIso_hom_snd ι p₁ p₂) k

/-! ### Groups of equal delta-dimension -/

/-- Cycle groups of equal delta-dimension are the same group. -/
def cycleGroupCongrDegree (D : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ D.S)
    [LocallyOfFiniteType f] {j k : ℤ} (h : j = k) : CycleGroup D f j ≃+ CycleGroup D f k where
  toFun z := ⟨z.1, h ▸ z.2⟩
  invFun z := ⟨z.1, h ▸ z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- `cycleGroupCongrDegree` does not change the underlying cycle. -/
@[simp]
theorem cycleGroupCongrDegree_apply_coe (D : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ D.S)
    [LocallyOfFiniteType f] {j k : ℤ} (h : j = k) (z : CycleGroup D f j) :
    (cycleGroupCongrDegree D f h z).1 = z.1 :=
  rfl

/-- Chow groups of equal delta-dimension are the same group. -/
def chowGroupCongrDegree (D : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ D.S)
    [LocallyOfFiniteType f] {j k : ℤ} (h : j = k) : chowGroup D f j ≃+ chowGroup D f k := by
  subst h
  exact AddEquiv.refl _

/-- `chowGroupCongrDegree` sends the class of a cycle `z` to the class of
`cycleGroupCongrDegree D f h z`. -/
@[simp]
theorem chowGroupCongrDegree_mk (D : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ D.S)
    [LocallyOfFiniteType f] {j k : ℤ} (h : j = k) (z : CycleGroup D f j) :
    chowGroupCongrDegree D f h (QuotientAddGroup.mk' (rationalEquivalences D f j) z) =
      QuotientAddGroup.mk' (rationalEquivalences D f k) (cycleGroupCongrDegree D f h z) := by
  subst h
  rfl

/-! ### Base change on Chow groups along an arbitrary cartesian square -/

/-- The base-change homomorphism `CH_k(X) ⟶ CH_{k+c}(Y)` on Chow groups attached to a flat base
change of Chow situations with dimension shift `c`, written for an arbitrary cartesian square
realizing `Y` as the base change of `X`. -/
def baseChangeChowPullbackSquare (B : FlatBaseChangeSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S}
    [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ) :
    chowGroup B.base f k →+ chowGroup B.baseChange q (k + B.c) :=
  (chowPushforwardOfIso B.baseChange (pullback.snd f B.g) q sq.isoPullback.inv
      (isoPullback_inv_comp_snd B f sq) (k + B.c)).comp
    (baseChangeChowPullback B f k)

/-- The base-change homomorphism on Chow groups along a cartesian square sends the class of a
cycle to the class of the base change of that cycle. -/
theorem baseChangeChowPullbackSquare_mk (B : FlatBaseChangeSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S}
    [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ) (z : CycleGroup B.base f k) :
    baseChangeChowPullbackSquare B f sq k
        (QuotientAddGroup.mk' (rationalEquivalences B.base f k) z) =
      QuotientAddGroup.mk' (rationalEquivalences B.baseChange q (k + B.c))
        (baseChangeCyclePullbackSquare B f sq k z) := by
  change chowPushforwardOfIso B.baseChange (pullback.snd f B.g) q sq.isoPullback.inv
      (isoPullback_inv_comp_snd B f sq) (k + B.c)
    (baseChangeChowPullback B f k
      (QuotientAddGroup.mk' (rationalEquivalences B.base f k) z)) = _
  rw [baseChangeChowPullback_mk B f k z, chowPushforwardOfIso_mk]
  rfl

/-! ### Composition on cycle groups -/

variable {X Y Y'' : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f]
  {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g)
  {p' : Y'' ⟶ Y} {q' : Y'' ⟶ C.S} [LocallyOfFiniteType q'] (sq' : IsPullback p' q' q g')

include hg' in
/-- On the fundamental cycle of a closed subscheme, base changing twice and base changing once
along the composite give the same cycle: each step is Stacks 0FVI part (1), and base changing a
closed subscheme twice is base changing it once along the composite. -/
private theorem comp_cycleAssociatedToClosedSubscheme_coeff {W : Scheme.{u}} (ι : W ⟶ X)
    [IsClosedImmersion ι] (k : ℤ) (hW : schemeDeltaDimension B.base (ι ≫ f) ≤ (k : EInt))
    (y : Y'') :
    (baseChangeCyclePullbackSquare (FlatBaseChangeSituation.second B C g' c' hg') q sq' (k + B.c)
        (baseChangeCyclePullbackSquare B f sq k
          (cycleAssociatedToClosedSubscheme B.base f ι k))).1 y =
      (baseChangeCyclePullbackSquare (FlatBaseChangeSituation.comp B C g' c' hg') f
        (sq'.paste_horiz sq) k (cycleAssociatedToClosedSubscheme B.base f ι k)).1 y := by
  rw [baseChangeCyclePullbackSquare_cycleAssociatedToClosedSubscheme B f sq ι k hW,
    baseChangeCyclePullbackSquare_cycleAssociatedToClosedSubscheme
      (FlatBaseChangeSituation.second B C g' c' hg') q sq' (pullback.snd ι p) (k + B.c)
      (schemeDeltaDimension_baseChangeSquare_le B f sq ι hW),
    baseChangeCyclePullbackSquare_cycleAssociatedToClosedSubscheme
      (FlatBaseChangeSituation.comp B C g' c' hg') f (sq'.paste_horiz sq) ι k hW,
    cycleAssociatedToClosedSubscheme_iterated_pullback C q' ι p p' (k + B.c + c'),
    add_assoc]

include hg' in
/-- **Stacks Project, Tag 0FVP, part (2).** The pullbacks on cycle groups of two composable flat
base changes compose to the pullback of the composite, read coefficientwise.

Both composites send a cycle `z` to a multiple of the coefficient of `z` at the image point `x`
of the given point, the factor depending only on the point. If `x` does not have relative
dimension `k` then every `k`-cycle vanishes there and both sides are zero. Otherwise the
fundamental cycle of the reduced closure of `x` is a `k`-cycle with coefficient one at `x`, so
the two factors agree by
`Stacks.Chow.comp_cycleAssociatedToClosedSubscheme_coeff`. -/
@[stacks 0FVP "part (2): pullback on cycle groups respects composition, coefficientwise"]
theorem baseChangeCyclePullbackSquare_comp_apply (k : ℤ) (z : CycleGroup B.base f k) (y : Y'') :
    (baseChangeCyclePullbackSquare (FlatBaseChangeSituation.second B C g' c' hg') q sq' (k + B.c)
        (baseChangeCyclePullbackSquare B f sq k z)).1 y =
      (baseChangeCyclePullbackSquare (FlatBaseChangeSituation.comp B C g' c' hg') f
        (sq'.paste_horiz sq) k z).1 y := by
  classical
  have hpt : (p' ≫ p).base y = p.base (p'.base y) := Scheme.Hom.comp_apply p' p y
  rw [baseChangeCyclePullbackSquare_apply
      (FlatBaseChangeSituation.second B C g' c' hg') q sq' (k + B.c) _ y,
    baseChangeCyclePullbackSquare_apply B f sq k z (p'.base y),
    baseChangeCyclePullbackSquare_apply
      (FlatBaseChangeSituation.comp B C g' c' hg') f (sq'.paste_horiz sq) k z y,
    hpt]
  by_cases hdim :
      relativeDimension B.base.dimensionFunction f (p.base (p'.base y)) = k
  · have hWdim : schemeDeltaDimension B.base
        ((integralComponentAt (p.base (p'.base y))).subschemeι ≫ f) = (k : EInt) :=
      schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq B.base f _ hdim
    have hone : (cycleAssociatedToClosedSubscheme B.base f
        (integralComponentAt (p.base (p'.base y))).subschemeι k).1
          (p.base (p'.base y)) = 1 :=
      cycleAssociatedToClosedSubscheme_integralComponentAt_self B.base f
        (p.base (p'.base y)) hWdim
    have hgen := comp_cycleAssociatedToClosedSubscheme_coeff B C g' c' hg' f sq sq'
      (integralComponentAt (p.base (p'.base y))).subschemeι k (le_of_eq hWdim) y
    rw [baseChangeCyclePullbackSquare_apply
        (FlatBaseChangeSituation.second B C g' c' hg') q sq' (k + B.c) _ y,
      baseChangeCyclePullbackSquare_apply B f sq k _ (p'.base y),
      baseChangeCyclePullbackSquare_apply
        (FlatBaseChangeSituation.comp B C g' c' hg') f (sq'.paste_horiz sq) k _ y,
      hpt, hone, one_mul, one_mul] at hgen
    rw [mul_assoc, hgen]
  · have hz : z.1 (p.base (p'.base y)) = 0 := by
      by_contra hne
      exact hdim ((mem_cyclesOfDimension_iff_forall_point B.base f k z.1).1 z.2 _ hne)
    rw [hz, zero_mul, zero_mul, zero_mul]

include hg' in
/-- **Stacks Project, Tag 0FVP, part (2).** The pullbacks on cycle groups of two composable flat
base changes compose to the pullback of the composite. -/
@[stacks 0FVP "part (2): pullback on cycle groups respects composition"]
theorem baseChangeCyclePullbackSquare_comp (k : ℤ) :
    (baseChangeCyclePullbackSquare (FlatBaseChangeSituation.second B C g' c' hg') q sq'
          (k + B.c)).comp (baseChangeCyclePullbackSquare B f sq k) =
      ((cycleGroupCongrDegree C q'
          (show k + (B.c + c') = k + B.c + c' from (add_assoc k B.c c').symm)).toAddMonoidHom).comp
        (baseChangeCyclePullbackSquare (FlatBaseChangeSituation.comp B C g' c' hg') f
          (sq'.paste_horiz sq) k) :=
  AddMonoidHom.ext fun z ↦ Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦
    baseChangeCyclePullbackSquare_comp_apply B C g' c' hg' f sq sq' k z y)

include hg' in
/-- **Stacks Project, Tag 0FVP, part (3).** The pullbacks on Chow groups of two composable flat
base changes compose to the pullback of the composite: both are induced by the corresponding
pullbacks on cycle groups, which compose by
`Stacks.Chow.baseChangeCyclePullbackSquare_comp`. -/
@[stacks 0FVP "part (3): pullback on Chow groups respects composition"]
theorem baseChangeChowPullbackSquare_comp (k : ℤ) :
    (baseChangeChowPullbackSquare (FlatBaseChangeSituation.second B C g' c' hg') q sq'
          (k + B.c)).comp (baseChangeChowPullbackSquare B f sq k) =
      ((chowGroupCongrDegree C q'
          (show k + (B.c + c') = k + B.c + c' from (add_assoc k B.c c').symm)).toAddMonoidHom).comp
        (baseChangeChowPullbackSquare (FlatBaseChangeSituation.comp B C g' c' hg') f
          (sq'.paste_horiz sq) k) := by
  refine AddMonoidHom.ext fun α ↦ ?_
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences B.base f k) α
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, baseChangeChowPullbackSquare_mk,
    baseChangeChowPullbackSquare_mk, baseChangeChowPullbackSquare_mk,
    AddEquiv.coe_toAddMonoidHom, chowGroupCongrDegree_mk]
  exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C q' (k + B.c + c')))
    (DFunLike.congr_fun (baseChangeCyclePullbackSquare_comp B C g' c' hg' f sq sq' k) z)

end Stacks.Chow

end
