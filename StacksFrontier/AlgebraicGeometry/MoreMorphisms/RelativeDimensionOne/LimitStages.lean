module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.EmptyFibreAtStage
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.Constructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyConnectedFibres
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChangeGeneric
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ

/-!
# Conditions which hold at the limit of a system of schemes hold at a stage

Let `S = lim Sᵢ` be a cofiltered limit of schemes with affine transition morphisms. This file
collects the bookkeeping used to pass a whole diagram of schemes of finite presentation over `S`
to one stage `Sᵢ`: the comparison of the base change to `S` through two stages, the stability of
a property of a base change under further base change, and two *fibrewise* conditions which
descend from `S` to a stage although they are not limit-preserved properties of a single
morphism — geometric connectedness of the fibres and a bound on the dimension of the fibres.

## Main results

* `AlgebraicGeometry.LimitStages.prop_limit_map_iff`: a property respecting isomorphisms holds for
  the base change of a morphism to the limit exactly when it holds for the base change to the
  limit of its base change to a later stage.
* `AlgebraicGeometry.LimitStages.prop_overPullback_map_comp`: a property stable under base change
  which holds at a stage holds at every later stage.
* `AlgebraicGeometry.LimitStages.exists_model_below`: a scheme of finite presentation over the
  limit is the base change of one over a stage below any prescribed stage.
* `AlgebraicGeometry.LimitStages.exists_forall_fst_notMem_range`: a subset of a scheme over a
  stage which is the image of a quasi-compact scheme and is avoided by the base change to the
  limit is avoided by the base change to every sufficiently late stage.
* `AlgebraicGeometry.LimitStages.exists_geometricallyConnected_stage`: geometrically connected
  fibres descend from the limit to a stage, for a morphism of finite presentation with affine
  target.
* `AlgebraicGeometry.LimitStages.exists_topologicalKrullDim_fiber_le_stage`: a bound on the
  dimension of all fibres descends from the limit to a stage, for a morphism locally of finite
  type with quasi-compact source.

## Implementation notes

"At every sufficiently late stage" is spelled out as an existential stage `j ⟶ i` together with a
universal quantification over all further stages `k ⟶ j`, so that finitely many such statements
about the same stage `i` combine through `CategoryTheory.IsCofiltered.cospan`.

The two fibrewise descents are the argument of [Stacks, Tag 05F3]: the bad locus is the image of
a quasi-compact scheme — by [Stacks, Tag 055I] for geometric connectedness, by
[Stacks, Tag 02FZ] for the dimension of fibres — and it is missed by the image of the limit by
the compatibility of the condition with base change ([Stacks, Tag 055E] and
[Stacks, Tag 02FY]), so its fibre product with the limit is empty, hence so is its fibre product
with a stage.

## References

* [Stacks Project, Tag 05F3](https://stacks.math.columbia.edu/tag/05F3)
* [Stacks Project, Tag 055I](https://stacks.math.columbia.edu/tag/055I)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.LimitStages

section Functors

variable {S T T' : Scheme.{u}}

/-- A property respecting isomorphisms holds for the left part of a morphism of over objects
conjugated by isomorphisms exactly when it holds for the morphism. -/
theorem prop_left_conj_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {A A' B B' : Over S} (eA : A' ≅ A) (f : A ⟶ B) (eB : B ≅ B') :
    P (eA.hom ≫ f ≫ eB.hom).left ↔ P f.left := by
  have : IsIso eA.hom.left := (Over.forget S).map_isIso eA.hom
  have : IsIso eB.hom.left := (Over.forget S).map_isIso eB.hom
  rw [Over.comp_left, Over.comp_left, MorphismProperty.cancel_left_of_respectsIso P,
    MorphismProperty.cancel_right_of_respectsIso P]

/-- A property respecting isomorphisms transfers along a commutative square of over objects whose
horizontal sides are isomorphisms. -/
theorem prop_left_iff_of_comm (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {A A' B B' : Over S} (α : A ≅ A') (β : B ≅ B') (m : A' ⟶ B') (n : A ⟶ B)
    (h : α.hom ≫ m = n ≫ β.hom) : P n.left ↔ P m.left := by
  have hn : n = α.hom ≫ m ≫ β.inv := by
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hn]
  exact prop_left_conj_iff P α m β.symm

/-- A property stable under base change which holds for a morphism over `S` holds for its base
change along any `g`. -/
theorem prop_overPullback_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (g : T ⟶ S) {A B : Over S} (f : A ⟶ B) (h : P f.left) :
    P ((Over.pullback g).map f).left :=
  MorphismProperty.of_isPullback (overPullback_isPullback g _ _ _) h

/-- A property stable under base change which holds for the base change of a morphism along
`g` holds for its base change along every `g' ≫ g`. -/
theorem prop_overPullback_map_comp (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.RespectsIso] (g : T ⟶ S) (g' : T' ⟶ T) {A B : Over S}
    (f : A ⟶ B) (h : P ((Over.pullback g).map f).left) :
    P ((Over.pullback (g' ≫ g)).map f).left :=
  (prop_left_iff_of_comm P (overPullbackCompIso g g' _ rfl A) (overPullbackCompIso g g' _ rfl B)
    _ _ (overPullbackCompIso_naturality g g' _ rfl f)).mp (prop_overPullback_map P g' _ h)

/-- **Base change preserves pullback squares of over objects.** -/
theorem isPullback_overPullback_map (g : T ⟶ S) {P Y W X : Over S} (a : P ⟶ Y) (b : P ⟶ W)
    (f : Y ⟶ X) (w : W ⟶ X) (h : IsPullback a.left b.left f.left w.left) :
    IsPullback ((Over.pullback g).map a).left ((Over.pullback g).map b).left
      ((Over.pullback g).map f).left ((Over.pullback g).map w).left := by
  have hout : IsPullback (pullback.fst P.hom g ≫ a.left) ((Over.pullback g).map b).left f.left
      (pullback.fst W.hom g ≫ w.left) :=
    (overPullback_isPullback g P W b).paste_horiz h
  have hout' : IsPullback (((Over.pullback g).map a).left ≫ pullback.fst Y.hom g)
      ((Over.pullback g).map b).left f.left
      (((Over.pullback g).map w).left ≫ pullback.fst X.hom g) := by
    rwa [overPullback_map_left_fst, overPullback_map_left_fst]
  have hcomm : a ≫ f = b ≫ w := Over.OverMorphism.ext h.w
  refine IsPullback.of_right hout' ?_ (overPullback_isPullback g Y X f)
  rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, ← Functor.map_comp, hcomm]

end Functors

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The canonical comparison of the base change to the limit through a later stage with the base
change to the limit through an earlier one. -/
noncomputable abbrev limitIso {i j : I} (g : j ⟶ i) (A : Over (D.obj i)) :
    (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj A) ≅
      (Over.pullback (c.π.app i)).obj A :=
  overPullbackCompIso (D.map g) (c.π.app j) (c.π.app i) (c.w g) A

/-- A property respecting isomorphisms holds for the base change of a morphism to the limit
exactly when it holds for the base change to the limit of its base change to a later stage. -/
theorem prop_limit_map_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {i j : I}
    (g : j ⟶ i) {A B : Over (D.obj i)} (f : A ⟶ B) :
    P ((Over.pullback (c.π.app j)).map ((Over.pullback (D.map g)).map f)).left ↔
      P ((Over.pullback (c.π.app i)).map f).left :=
  prop_left_iff_of_comm P (limitIso D c g A) (limitIso D c g B) _ _
    (overPullbackCompIso_naturality _ _ _ _ f)

/-- A scheme of finite presentation over the limit is the base change of one over a stage lying
below any prescribed stage. -/
theorem exists_model_below [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (i₀ : I) (A : Over c.pt)
    (hA : FinitePresentation A.hom) :
    ∃ (j : I) (_ : j ⟶ i₀) (A₀ : Over (D.obj j)), FinitePresentation A₀.hom ∧
      Nonempty (A ≅ (Over.pullback (c.π.app j)).obj A₀) := by
  obtain ⟨i, A₁, h₁, ⟨e⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc A hA
  obtain ⟨j, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i i₀
  exact ⟨j, b, (Over.pullback (D.map a)).obj A₁,
    Stacks.GenericFlatness.finitePresentation_pullback _ A₁ h₁,
    ⟨e ≪≫ (limitIso D c a A₁).symm⟩⟩

/-- The structure morphism of the base change of an over object is the second projection, and the
first projection satisfies the pullback condition pointwise. -/
theorem hom_fst_apply {S T : Scheme.{u}} (A : Over S) (h : T ⟶ S)
    (a : ((Over.pullback h).obj A).left) :
    A.hom (pullback.fst A.hom h a) = h (pullback.snd A.hom h a) := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

/-- Two morphisms into a base change of an over object agree as soon as they agree after the
first projection. -/
theorem over_pullback_hom_ext {S T : Scheme.{u}} (h : T ⟶ S) {A : Over S} {Z : Over T}
    (φ ψ : Z ⟶ (Over.pullback h).obj A)
    (hfst : φ.left ≫ pullback.fst A.hom h = ψ.left ≫ pullback.fst A.hom h) : φ = ψ :=
  GlueingNearPoint.overPullback_hom_ext_fst h (m := φ) (n := ψ) hfst

/-- The comparison of base changes through three stages, `J ⟶ j ⟶ k`. -/
theorem limitIso_trans {k j J : I} (e : j ⟶ k) (v : J ⟶ j) (h : J ⟶ k) (hh : v ≫ e = h)
    (A : Over (D.obj k)) :
    (limitIso D c h A).hom =
      (Over.pullback (c.π.app J)).map
          (overPullbackCompIso (D.map e) (D.map v) (D.map h) (by rw [← hh, D.map_comp]) A).inv ≫
        (limitIso D c v ((Over.pullback (D.map e)).obj A)).hom ≫ (limitIso D c e A).hom := by
  have hD : D.map v ≫ D.map e = D.map h := by rw [← hh, D.map_comp]
  apply GlueingNearPoint.overPullback_hom_ext_fst
  have h₁ := overPullbackCompIso_fst (D.map e) (D.map v) (D.map h) hD A
  have h₂ : (overPullbackCompIso (D.map e) (D.map v) (D.map h) hD A).inv.left ≫
        pullback.fst ((Over.pullback (D.map e)).obj A).hom (D.map v) ≫
          pullback.fst A.hom (D.map e) = pullback.fst A.hom (D.map h) := by
    rw [← h₁, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left,
      Category.id_comp]
  have h₃ := overPullbackCompIso_fst (D.map e) (c.π.app j) (c.π.app k) (c.w e) A
  have h₄ := overPullbackCompIso_fst (D.map v) (c.π.app J) (c.π.app j) (c.w v)
    ((Over.pullback (D.map e)).obj A)
  have h₅ := overPullbackCompIso_fst (D.map h) (c.π.app J) (c.π.app k) (c.w h) A
  have h₆ := overPullback_map_left_fst (c.π.app J)
    (overPullbackCompIso (D.map e) (D.map v) (D.map h) hD A).inv
  simp only [Over.comp_left, Category.assoc]
  rw [h₃, reassoc_of% h₄, reassoc_of% h₆, h₂]
  exact h₅

/-- The transport of a morphism between base changes to a stage `j` to a later stage `J`, along
`v : J ⟶ j`, written between the base changes along the composite `h = v ≫ e`. -/
noncomputable abbrev transportHom {k j J : I} (e : j ⟶ k) (v : J ⟶ j) (h : J ⟶ k)
    (hh : v ≫ e = h) {A B : Over (D.obj k)}
    (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B) :
    (Over.pullback (D.map h)).obj A ⟶ (Over.pullback (D.map h)).obj B :=
  (overPullbackCompIso (D.map e) (D.map v) (D.map h) (by rw [← hh, D.map_comp]) A).inv ≫
    (Over.pullback (D.map v)).map G ≫
      (overPullbackCompIso (D.map e) (D.map v) (D.map h) (by rw [← hh, D.map_comp]) B).hom

/-- A property respecting isomorphisms holds for a transported morphism exactly when it holds
for the base change of the morphism. -/
theorem prop_transportHom_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {k j J : I}
    (e : j ⟶ k) (v : J ⟶ j) (h : J ⟶ k) (hh : v ≫ e = h) {A B : Over (D.obj k)}
    (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B) :
    P (transportHom D e v h hh G).left ↔ P ((Over.pullback (D.map v)).map G).left := by
  exact prop_left_conj_iff P (overPullbackCompIso _ _ _ _ A).symm _
    (overPullbackCompIso _ _ _ _ B)

/-- **Compatibility with the limit is preserved by transport to a later stage.** -/
theorem limitIso_transportHom {k j J : I} (e : j ⟶ k) (v : J ⟶ j) (h : J ⟶ k)
    (hh : v ≫ e = h) {A B : Over (D.obj k)}
    (m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B)
    (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B)
    (hG : (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫
      (limitIso D c e B).hom) :
    (limitIso D c h A).hom ≫ m = (Over.pullback (c.π.app J)).map (transportHom D e v h hh G) ≫
      (limitIso D c h B).hom := by
  rw [limitIso_trans D c e v h hh A, limitIso_trans D c e v h hh B]
  simp only [Category.assoc, hG, transportHom, Functor.map_comp]
  rw [← Category.assoc ((limitIso D c v _).hom), overPullbackCompIso_naturality]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Stacks Project, Tag 01ZM part (2), in canonical form.** A morphism between the base changes
to the limit of two schemes of finite presentation over a stage is, after passing to a later
stage, the base change of a morphism, the base changes being compared by the canonical
isomorphisms `AlgebraicGeometry.LimitStages.limitIso`. -/
theorem exists_hom_limitIso [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (k : I) (A B : Over (D.obj k))
    (hA : FinitePresentation A.hom) (hB : FinitePresentation B.hom)
    (m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B) :
    ∃ (j : I) (e : j ⟶ k) (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B),
      (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫ (limitIso D c e B).hom := by
  have : EssentiallySmall.{u} I := essentiallySmallSelf.{u} I
  obtain ⟨j, e, G, α, β, hα, hβ, hcomp⟩ :=
    exists_morphism_after_baseChange D c hc k A B hA hB m
  have hα' := iso_eq_overPullbackCompIso (D.map e) (c.π.app j) (c.π.app k) (c.w e) A α hα
  have hβ' := iso_eq_overPullbackCompIso (D.map e) (c.π.app j) (c.π.app k) (c.w e) B β hβ
  subst hα' hβ'
  exact ⟨j, e, G, hcomp⟩

/-- Two conditions each holding at all sufficiently late stages hold together at all sufficiently
late stages. -/
theorem eventually_and [IsCofiltered I] {i : I} {Q₁ Q₂ : ∀ k : I, (k ⟶ i) → Prop}
    (h₁ : ∃ (j : I) (g : j ⟶ i), ∀ (k : I) (g' : k ⟶ j), Q₁ k (g' ≫ g))
    (h₂ : ∃ (j : I) (g : j ⟶ i), ∀ (k : I) (g' : k ⟶ j), Q₂ k (g' ≫ g)) :
    ∃ (j : I) (g : j ⟶ i), ∀ (k : I) (g' : k ⟶ j), Q₁ k (g' ≫ g) ∧ Q₂ k (g' ≫ g) := by
  obtain ⟨j₁, g₁, H₁⟩ := h₁
  obtain ⟨j₂, g₂, H₂⟩ := h₂
  obtain ⟨j, a, b, hab⟩ := IsCofiltered.cospan g₁ g₂
  refine ⟨j, a ≫ g₁, fun k g' => ⟨?_, ?_⟩⟩
  · simpa only [Category.assoc] using H₁ k (g' ≫ a)
  · rw [hab]
    simpa only [Category.assoc] using H₂ k (g' ≫ b)

/-- A property stable under base change which holds at one stage holds at all later stages. -/
theorem eventually_of_exists (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.RespectsIso] {i : I} {A B : Over (D.obj i)} (f : A ⟶ B)
    (h : ∃ (j : I) (g : j ⟶ i), P ((Over.pullback (D.map g)).map f).left) :
    ∃ (j : I) (g : j ⟶ i), ∀ (k : I) (g' : k ⟶ j),
      P ((Over.pullback (D.map (g' ≫ g))).map f).left := by
  obtain ⟨j, g, hg⟩ := h
  refine ⟨j, g, fun k g' => ?_⟩
  have := prop_overPullback_map_comp P (D.map g) (D.map g') f hg
  rwa [← D.map_comp] at this

variable [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]

/-- **A bad locus missed at the limit is missed at a stage.** Let `E` be the image of a
quasi-compact scheme in a scheme `A` over a stage. If no point of the base change of `A` to the
limit lies over `E`, then no point of the base change of `A` to any sufficiently late stage lies
over `E`. -/
theorem exists_forall_fst_notMem_range (hc : IsLimit c) (i : I) (A : Over (D.obj i))
    {Z : Scheme.{u}} [CompactSpace Z] (z : Z ⟶ A.left)
    (hlim : ∀ a : ((Over.pullback (c.π.app i)).obj A).left,
      pullback.fst A.hom (c.π.app i) a ∉ Set.range z) :
    ∃ (j : I) (g : j ⟶ i), ∀ (k : I) (g' : k ⟶ j)
      (a : ((Over.pullback (D.map (g' ≫ g))).obj A).left),
        pullback.fst A.hom (D.map (g' ≫ g)) a ∉ Set.range z := by
  have hempty : IsEmpty (pullback (c.π.app i) (z ≫ A.hom) : Scheme.{u}) := by
    refine ⟨fun p => ?_⟩
    have hp₀ : (pullback.snd (c.π.app i) (z ≫ A.hom) ≫ z ≫ A.hom) p =
        (pullback.fst (c.π.app i) (z ≫ A.hom) ≫ c.π.app i) p := by
      rw [pullback.condition]
    have hp : A.hom (z (pullback.snd (c.π.app i) (z ≫ A.hom) p)) =
        c.π.app i (pullback.fst (c.π.app i) (z ≫ A.hom) p) := by
      simpa only [Scheme.Hom.comp_apply] using hp₀
    obtain ⟨a, ha, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hp
    exact hlim a ⟨_, ha.symm⟩
  have : EssentiallySmall.{u} I := essentiallySmallSelf.{u} I
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  obtain ⟨j, g, hg⟩ :=
    exists_isEmpty_pullback_map_of_isEmpty_pullback_π_app D c hc i (z ≫ A.hom) hempty
  refine ⟨j, g, fun k g' a ⟨ζ, hζ⟩ => ?_⟩
  have h₁ : (z ≫ A.hom) ζ = D.map g (D.map g' (pullback.snd A.hom (D.map (g' ≫ g)) a)) := by
    rw [Scheme.Hom.comp_apply, hζ, hom_fst_apply]
    conv_rhs => rw [← Scheme.Hom.comp_apply, ← D.map_comp]
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.map g) (g := z ≫ A.hom)
    _ ζ h₁.symm
  exact hg.false p

/-- **Geometric connectedness of the fibres descends to a stage.** Let `f` be a morphism of
finite presentation of schemes over a stage, with affine target. If the base change of `f` to
the limit has geometrically connected fibres, so does its base change to every sufficiently late
stage. -/
@[sga "3 VIB 10.9" "special case"]
theorem exists_geometricallyConnected_stage (hc : IsLimit c) (i : I) {A B : Over (D.obj i)}
    (f : A ⟶ B) (hf : FinitePresentation f.left) [IsAffine B.left]
    (h : GeometricallyConnected ((Over.pullback (c.π.app i)).map f).left) :
    ∃ (j : I) (g : j ⟶ i), ∀ (k : I) (g' : k ⟶ j),
      GeometricallyConnected ((Over.pullback (D.map (g' ≫ g))).map f).left := by
  classical
  let E : Set B.left := {y | numGeometricConnectedComponents f.left y = 1}ᶜ
  have hE : Topology.IsConstructible E :=
    Topology.isConstructible_compl.mpr
      (isLocallyConstructible_numGeometricConnectedComponents f.left hf 1).isConstructible
  obtain ⟨Z, -, _, z, hz⟩ := exists_affine_scheme_with_range hE
  have hcount {T : Scheme.{u}} (h' : T ⟶ D.obj i) (y : ((Over.pullback h').obj B).left) :
      numGeometricConnectedComponents ((Over.pullback h').map f).left y =
        numGeometricConnectedComponents f.left (pullback.fst B.hom h' y) :=
    congrFun (numGeometricConnectedComponents_eq_of_isPullback f.left _ _ _
      (overPullback_isPullback h' A B f)) y
  obtain ⟨j, g, hg⟩ := exists_forall_fst_notMem_range D c hc i B z (fun b hb => by
    rw [hz] at hb
    apply hb
    rw [Set.mem_ofPred_eq, ← hcount,
      ← geometricallyConnected_iff_numGeometricConnectedComponents_eq_one]
    exact (GeometricallyConnected.iff_geometricallyConnected_fiber _).mp h b)
  refine ⟨j, g, fun k g' => (GeometricallyConnected.iff_geometricallyConnected_fiber _).mpr
    fun y => ?_⟩
  have hy := hg k g' y
  rw [hz] at hy
  rw [geometricallyConnected_iff_numGeometricConnectedComponents_eq_one, hcount]
  simpa [E] using hy

/-- **A bound on the dimension of the fibres descends to a stage.** Let `f` be a morphism locally
of finite type of schemes over a stage, with quasi-compact source. If every fibre of the base
change of `f` to the limit has dimension at most `d`, then so does every fibre of its base change
to every sufficiently late stage. -/
theorem exists_topologicalKrullDim_fiber_le_stage (hc : IsLimit c) (i : I)
    {A B : Over (D.obj i)} (f : A ⟶ B) [LocallyOfFiniteType f.left] [CompactSpace A.left]
    (d : ℕ)
    (h : ∀ s, topologicalKrullDim (((Over.pullback (c.π.app i)).map f).left.fiber s) ≤
      (d : WithBot ℕ∞)) :
    ∃ (j : I) (g : j ⟶ i), ∀ (k : I) (g' : k ⟶ j)
      (s : ((Over.pullback (D.map (g' ≫ g))).obj B).left),
      topologicalKrullDim (((Over.pullback (D.map (g' ≫ g))).map f).left.fiber s) ≤
        (d : WithBot ℕ∞) := by
  classical
  let E : Set A.left := {x | topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) ≤
    (d : WithBot ℕ∞)}ᶜ
  have hEc : IsClosed E := (isOpen_setOf_fiberDimensionAt_le f.left d).isClosed_compl
  let J := Scheme.IdealSheafData.vanishingIdeal (⟨E, hEc⟩ : Closeds A.left)
  have hrange : Set.range J.subschemeι = E := by
    rw [J.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : CompactSpace J.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  have hdimAt {T : Scheme.{u}} (h' : T ⟶ D.obj i) (x : ((Over.pullback h').obj A).left) :=
    topologicalKrullDimAt_fiber_eq_of_isPullback (overPullback_isPullback h' A B f) x
  obtain ⟨j, g, hg⟩ := exists_forall_fst_notMem_range D c hc i A J.subschemeι (fun a ha => by
    rw [hrange] at ha
    refine ha ?_
    change topologicalKrullDimAt (f.left.fiber (f.left (pullback.fst A.hom (c.π.app i) a)))
      (f.left.asFiber (pullback.fst A.hom (c.π.app i) a)) ≤ (d : WithBot ℕ∞)
    rw [← hdimAt]
    exact (topologicalKrullDim_fiber_le_iff _ _ _).mp (h _) a rfl)
  refine ⟨j, g, fun k g' s => (topologicalKrullDim_fiber_le_iff _ _ _).mpr fun x _ => ?_⟩
  have hx := hg k g' x
  rw [hrange] at hx
  rw [hdimAt]
  simpa [E] using hx

end AlgebraicGeometry.LimitStages

end
