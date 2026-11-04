module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# The relative diagonal through equalizer loci

Let `p : X ⟶ Y` be a morphism of presheaves of types on a category `C`, with values in a universe
`max w v` for an arbitrary `w`. Two sections `x, y` of `X` over `a` which have the same image in
`Y` define a morphism `uliftYoneda a ⟶ X ×_Y X`, and the base change of the relative diagonal
`X ⟶ X ×_Y X` along it is the *equalizer locus* of `x` and `y`: the subfunctor of
`uliftYoneda a` of morphisms `t : c ⟶ a` with `x|_t = y|_t`.

This file proves that the relative diagonal has a property `P` of morphisms of `C` relative to
`uliftYoneda` (in the sense of `CategoryTheory.MorphismProperty.relative`) as soon as every
equalizer locus is represented by a monomorphism of `C` with property `P`. This is the shape of
the statement "the diagonal of `p` is representable by closed immersions" which the source
proves by exhibiting the equalizer locus of two families as a closed subscheme.

## Main results

* `CategoryTheory.MorphismProperty.relative_pullbackDiagonal_of_equalizerLoci`, and its form
  `CategoryTheory.MorphismProperty.presheaf_pullbackDiagonal_of_equalizerLoci` through `yoneda`.
* `CategoryTheory.MorphismProperty.relative_of_injective_of_imageLoci`: the same criterion for a
  monomorphism of presheaves, through the loci where a section lies in its image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- A point of the fibre product `X ×_Y X` is the image of `z` under the relative diagonal exactly
when both of its projections are `z`. -/
private theorem diagonal_app_eq_iff {X Y : Cᵒᵖ ⥤ Type (max w v)} (p : X ⟶ Y) (c : Cᵒᵖ)
    (z : X.obj c) (u : (pullback p p).obj c) :
    (pullback.diagonal p).app c z = u ↔
      (pullback.fst p p).app c u = z ∧ (pullback.snd p p).app c u = z := by
  have h₁ : (pullback.fst p p).app c ((pullback.diagonal p).app c z) = z := by
    rw [← NatTrans.comp_app_apply, pullback.diagonal_fst]
    rfl
  have h₂ : (pullback.snd p p).app c ((pullback.diagonal p).app c z) = z := by
    rw [← NatTrans.comp_app_apply, pullback.diagonal_snd]
    rfl
  refine ⟨fun h => h ▸ ⟨h₁, h₂⟩, fun h => ?_⟩
  refine ((Types.isPullback_iff _ _ _ _).1
    ((IsPullback.of_hasPullback p p).map ((evaluation Cᵒᵖ (Type (max w v))).obj c))).2.1
    _ _ ⟨h₁.trans h.1.symm, h₂.trans h.2.symm⟩

private theorem app_up_eq_map_uliftYonedaEquiv {F : Cᵒᵖ ⥤ Type (max w v)} {a c : C}
    (g : uliftYoneda.{w}.obj a ⟶ F) (t : c ⟶ a) :
    g.app (Opposite.op c) (ULift.up t) = F.map t.op (uliftYonedaEquiv g) := by
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_apply]
  simp only [uliftYoneda]
  show g.app (Opposite.op c) (ULift.up t) = g.app (Opposite.op c) (ULift.up (𝟙 c ≫ t))
  rw [Category.id_comp]

/-- **The relative diagonal through equalizer loci.** Let `p : X ⟶ Y` be a morphism of presheaves
of types and `P` a property of morphisms of `C` which respects isomorphisms. Suppose that for any
two sections `x, y` of `X` over `a` with the same image in `Y` there is a monomorphism `s : b ⟶ a`
with property `P` through which a morphism `t : c ⟶ a` factors exactly when `x` and `y` agree after
restriction along `t`. Then the relative diagonal `X ⟶ X ×_Y X` has property `P` relative to
`uliftYoneda`. -/
theorem relative_pullbackDiagonal_of_equalizerLoci (P : MorphismProperty C) [P.RespectsIso]
    {X Y : Cᵒᵖ ⥤ Type (max w v)} (p : X ⟶ Y)
    (h : ∀ (a : C) (x y : X.obj (Opposite.op a)),
      p.app (Opposite.op a) x = p.app (Opposite.op a) y →
      ∃ (b : C) (s : b ⟶ a), Mono s ∧ P s ∧ ∀ (c : C) (t : c ⟶ a),
        X.map t.op x = X.map t.op y ↔ ∃ r : c ⟶ b, r ≫ s = t) :
    P.relative uliftYoneda.{w} (pullback.diagonal p) := by
  apply MorphismProperty.relative.of_exists
  intro a g
  let x : X.obj (Opposite.op a) := uliftYonedaEquiv (g ≫ pullback.fst p p)
  let y : X.obj (Opposite.op a) := uliftYonedaEquiv (g ≫ pullback.snd p p)
  have hxy : p.app (Opposite.op a) x = p.app (Opposite.op a) y := by
    simp only [x, y, ← uliftYonedaEquiv_comp, Category.assoc, pullback.condition]
  obtain ⟨b, s, hmono, hs, hloc⟩ := h a x y hxy
  have hb : X.map s.op x = X.map s.op y := (hloc b s).2 ⟨𝟙 b, Category.id_comp s⟩
  -- the value of `g` at a morphism `t : c ⟶ a`, through its two projections
  have hg₁ : ∀ (c : C) (t : c ⟶ a),
      (pullback.fst p p).app (Opposite.op c) (g.app (Opposite.op c) (ULift.up t)) =
        X.map t.op x := fun _ t => app_up_eq_map_uliftYonedaEquiv (g ≫ pullback.fst p p) t
  have hg₂ : ∀ (c : C) (t : c ⟶ a),
      (pullback.snd p p).app (Opposite.op c) (g.app (Opposite.op c) (ULift.up t)) =
        X.map t.op y := fun _ t => app_up_eq_map_uliftYonedaEquiv (g ≫ pullback.snd p p) t
  refine ⟨b, uliftYonedaEquiv.symm (X.map s.op x), s, ?_, hs⟩
  refine IsPullback.of_forall_isPullback_app fun ⟨c⟩ => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    rintro ⟨r⟩
    show (pullback.diagonal p).app (Opposite.op c) (X.map r.op (X.map s.op x)) =
      g.app (Opposite.op c) (ULift.up (r ≫ s))
    rw [diagonal_app_eq_iff, hg₁, hg₂]
    simp [hb]
  · rintro ⟨r⟩ ⟨r'⟩ ⟨-, hrr'⟩
    exact congrArg ULift.up (hmono.right_cancellation r r' (congrArg ULift.down hrr'))
  · rintro z ⟨t⟩ hz
    rw [diagonal_app_eq_iff, hg₁, hg₂] at hz
    obtain ⟨r, hr⟩ := (hloc c t).1 (hz.1.trans hz.2.symm)
    refine ⟨ULift.up r, ?_, congrArg ULift.up hr⟩
    change X.map r.op (X.map s.op x) = z
    rw [← Functor.map_comp_apply, ← op_comp, hr, hz.1]

/-- **The relative diagonal through equalizer loci, read through `yoneda`.** This is
`CategoryTheory.MorphismProperty.relative_pullbackDiagonal_of_equalizerLoci` for presheaves with
values in the universe of the morphisms of `C`, where the representable presheaves are those of
`yoneda`: if every equalizer locus of two sections with the same image is represented by a
monomorphism with property `P`, then the relative diagonal has property `P` relative to
`yoneda`. -/
theorem presheaf_pullbackDiagonal_of_equalizerLoci (P : MorphismProperty C) [P.RespectsIso]
    {X Y : Cᵒᵖ ⥤ Type v} (p : X ⟶ Y)
    (h : ∀ (a : C) (x y : X.obj (Opposite.op a)),
      p.app (Opposite.op a) x = p.app (Opposite.op a) y →
      ∃ (b : C) (s : b ⟶ a), Mono s ∧ P s ∧ ∀ (c : C) (t : c ⟶ a),
        X.map t.op x = X.map t.op y ↔ ∃ r : c ⟶ b, r ≫ s = t) :
    P.presheaf (pullback.diagonal p) := by
  apply MorphismProperty.relative.of_exists
  intro a g
  let x : X.obj (Opposite.op a) := yonedaEquiv (g ≫ pullback.fst p p)
  let y : X.obj (Opposite.op a) := yonedaEquiv (g ≫ pullback.snd p p)
  have hxy : p.app (Opposite.op a) x = p.app (Opposite.op a) y := by
    simp only [x, y, ← yonedaEquiv_comp, Category.assoc, pullback.condition]
  obtain ⟨b, s, hmono, hs, hloc⟩ := h a x y hxy
  have hb : X.map s.op x = X.map s.op y := (hloc b s).2 ⟨𝟙 b, Category.id_comp s⟩
  have hg₁ : ∀ (c : C) (t : c ⟶ a),
      (pullback.fst p p).app (Opposite.op c) (g.app (Opposite.op c) t) = X.map t.op x :=
    fun _ t => (map_yonedaEquiv (g ≫ pullback.fst p p) t).symm
  have hg₂ : ∀ (c : C) (t : c ⟶ a),
      (pullback.snd p p).app (Opposite.op c) (g.app (Opposite.op c) t) = X.map t.op y :=
    fun _ t => (map_yonedaEquiv (g ≫ pullback.snd p p) t).symm
  refine ⟨b, yonedaEquiv.symm (X.map s.op x), s, ?_, hs⟩
  refine IsPullback.of_forall_isPullback_app fun ⟨c⟩ => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro r
    show (pullback.diagonal p).app (Opposite.op c) (X.map r.op (X.map s.op x)) =
      g.app (Opposite.op c) (r ≫ s)
    rw [diagonal_app_eq_iff, hg₁, hg₂]
    simp [hb]
  · rintro r r' ⟨-, hrr'⟩
    exact hmono.right_cancellation r r' hrr'
  · rintro z t hz
    rw [diagonal_app_eq_iff, hg₁, hg₂] at hz
    obtain ⟨r, hr⟩ := (hloc c t).1 (hz.1.trans hz.2.symm)
    refine ⟨r, ?_, hr⟩
    change X.map r.op (X.map s.op x) = z
    rw [← Functor.map_comp_apply, ← op_comp, hr, hz.1]

/-- **A monomorphism of presheaves through image loci.** Let `ι : X ⟶ Y` be a morphism of
presheaves of types which is injective at every object, and `P` a property of morphisms of `C`
which respects isomorphisms. Suppose that for every section `y` of `Y` over `a` there is a
monomorphism `s : b ⟶ a` with property `P` through which a morphism `t : c ⟶ a` factors exactly
when the restriction of `y` along `t` lies in the image of `ι`. Then `ι` has property `P` relative
to `uliftYoneda`. -/
theorem relative_of_injective_of_imageLoci (P : MorphismProperty C) [P.RespectsIso]
    {X Y : Cᵒᵖ ⥤ Type (max w v)} (ι : X ⟶ Y)
    (hinj : ∀ c : Cᵒᵖ, Function.Injective (ι.app c))
    (h : ∀ (a : C) (y : Y.obj (Opposite.op a)), ∃ (b : C) (s : b ⟶ a), Mono s ∧ P s ∧
      ∀ (c : C) (t : c ⟶ a),
        (∃ x : X.obj (Opposite.op c), ι.app (Opposite.op c) x = Y.map t.op y) ↔
          ∃ r : c ⟶ b, r ≫ s = t) :
    P.relative uliftYoneda.{w} ι := by
  apply MorphismProperty.relative.of_exists
  intro a g
  let y : Y.obj (Opposite.op a) := uliftYonedaEquiv g
  obtain ⟨b, s, hmono, hs, hloc⟩ := h a y
  obtain ⟨x₀, hx₀⟩ := (hloc b s).2 ⟨𝟙 b, Category.id_comp s⟩
  have hg : ∀ (c : C) (t : c ⟶ a), g.app (Opposite.op c) (ULift.up t) = Y.map t.op y :=
    fun _ t => app_up_eq_map_uliftYonedaEquiv g t
  have hι : ∀ (c : C) (r : c ⟶ b),
      ι.app (Opposite.op c) (X.map r.op x₀) = Y.map (r ≫ s).op y := by
    intro c r
    rw [NatTrans.naturality_apply, hx₀, op_comp, Functor.map_comp_apply]
  refine ⟨b, uliftYonedaEquiv.symm x₀, s, ?_, hs⟩
  refine IsPullback.of_forall_isPullback_app fun ⟨c⟩ => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact ConcreteCategory.hom_ext _ _ fun ⟨r⟩ => (hι c r).trans (hg c (r ≫ s)).symm
  · rintro ⟨r⟩ ⟨r'⟩ ⟨-, hrr'⟩
    exact congrArg ULift.up (hmono.right_cancellation r r' (congrArg ULift.down hrr'))
  · rintro x ⟨t⟩ hx
    have hx' : ι.app (Opposite.op c) x = Y.map t.op y := hx.trans (hg c t)
    obtain ⟨r, hr⟩ := (hloc c t).1 ⟨x, hx'⟩
    refine ⟨ULift.up r, ?_, congrArg ULift.up hr⟩
    show X.map r.op x₀ = x
    apply hinj
    rw [hι, hr, hx']

end CategoryTheory.MorphismProperty

end
