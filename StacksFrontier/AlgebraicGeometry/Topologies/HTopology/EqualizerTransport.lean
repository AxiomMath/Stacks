module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.Coherent.RegularSheaves

/-!
# Transporting the equalizer condition along a comparison of squares

The sheaf condition for a one-element family `{f : V ⟶ U}` is the bijectivity of
`CategoryTheory.regularTopology.mapToEqualizer F f p₁ p₂ _`, the canonical map from the sections
over `U` to the equalizer of the two restriction maps `F(V) ⟶ F(W)` attached to a pair
`p₁, p₂ : W ⟶ V` with `p₁ ≫ f = p₂ ≫ f`.

Given a second datum `f' : V' ⟶ U'`, `p₁', p₂' : W' ⟶ V'` and comparison morphisms `u : U' ⟶ U`,
`v : V' ⟶ V`, `q : W' ⟶ W` making the three evident squares commute, if `F` sends `u`, `v` and `q`
to bijections then the equalizer map of the first datum is bijective as soon as that of the second
is. This file also shows that in a cartesian square of types with two singleton corners on one
side, the opposite map is a bijection.

## Main results

* `CategoryTheory.regularTopology.mapsTo_equalizer`: a comparison morphism `v : V' ⟶ V`
  compatible with `p₁, p₂` and `p₁', p₂'` sends the equalizer of `F(p₁), F(p₂)` into the
  equalizer of `F(p₁'), F(p₂')`.
* `CategoryTheory.regularTopology.bijective_restrict_mapsTo_equalizer`: that induced map on
  equalizers is bijective as soon as `F.map v.op` is bijective and `F.map q.op` is injective.
* `CategoryTheory.regularTopology.bijective_mapToEqualizer_of_bijective`: the transport of the
  bijectivity of the equalizer map along a comparison of squares.
* `CategoryTheory.IsPullback.bijective_fst_of_subsingleton`: in a cartesian square of types whose
  bottom row is a map between singletons, the top map is bijective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

namespace regularTopology

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)

/-- Restriction along a commuting square of morphisms gives a commuting square of maps. -/
private theorem map_op_comp_apply_eq {X Y Z T : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ T) (d : T ⟶ Z)
    (h : a ≫ b = c ≫ d) (x : F.obj (op Z)) :
    F.map a.op (F.map b.op x) = F.map c.op (F.map d.op x) := by
  rw [← Functor.map_comp_apply, ← op_comp, h, op_comp, Functor.map_comp_apply]

/-- A comparison morphism `v : V' ⟶ V` which is compatible, through `q : W' ⟶ W`, with two pairs
`p₁, p₂ : W ⟶ V` and `p₁', p₂' : W' ⟶ V'`, sends the equalizer of `F.map p₁.op` and `F.map p₂.op`
into the equalizer of `F.map p₁'.op` and `F.map p₂'.op`. -/
public theorem mapsTo_equalizer {V W V' W' : C} (p₁ p₂ : W ⟶ V) (p₁' p₂' : W' ⟶ V')
    (v : V' ⟶ V) (q : W' ⟶ W) (h₁ : p₁' ≫ v = q ≫ p₁) (h₂ : p₂' ≫ v = q ≫ p₂) :
    Set.MapsTo (F.map v.op) {x : F.obj (op V) | F.map p₁.op x = F.map p₂.op x}
      {x : F.obj (op V') | F.map p₁'.op x = F.map p₂'.op x} := by
  intro x (hx : F.map p₁.op x = F.map p₂.op x)
  show F.map p₁'.op (F.map v.op x) = F.map p₂'.op (F.map v.op x)
  rw [map_op_comp_apply_eq F _ _ _ _ h₁, map_op_comp_apply_eq F _ _ _ _ h₂, hx]

/-- The map on equalizers induced by a comparison morphism `v : V' ⟶ V` compatible with
`p₁, p₂ : W ⟶ V` and `p₁', p₂' : W' ⟶ V'` through `q : W' ⟶ W` is bijective, provided `F.map v.op`
is bijective and `F.map q.op` is injective. -/
public theorem bijective_restrict_mapsTo_equalizer {V W V' W' : C} (p₁ p₂ : W ⟶ V)
    (p₁' p₂' : W' ⟶ V') (v : V' ⟶ V) (q : W' ⟶ W) (h₁ : p₁' ≫ v = q ≫ p₁)
    (h₂ : p₂' ≫ v = q ≫ p₂) (hv : Function.Bijective (F.map v.op))
    (hq : Function.Injective (F.map q.op)) :
    Function.Bijective ((mapsTo_equalizer F p₁ p₂ p₁' p₂' v q h₁ h₂).restrict _ _ _) := by
  refine ⟨fun x y hxy ↦ Subtype.ext (hv.1 (Subtype.ext_iff.1 hxy)), fun ⟨y, hy⟩ ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hv.2 y
  exact ⟨⟨x, hq (by
    rw [← map_op_comp_apply_eq F _ _ _ _ h₁, ← map_op_comp_apply_eq F _ _ _ _ h₂]; exact hy)⟩, rfl⟩

/-- Let `f : V ⟶ U` and `p₁, p₂ : W ⟶ V` satisfy `p₁ ≫ f = p₂ ≫ f`, and let `f' : V' ⟶ U'` and
`p₁', p₂' : W' ⟶ V'` be a second such datum. Suppose given comparison morphisms `u : U' ⟶ U`,
`v : V' ⟶ V` and `q : W' ⟶ W` making the squares `f' ≫ u = v ≫ f`, `p₁' ≫ v = q ≫ p₁` and
`p₂' ≫ v = q ≫ p₂` commute, and suppose `F` sends all three of `u`, `v` and `q` to bijections.
Then the canonical map from `F(U)` to the equalizer of `F.map p₁.op` and `F.map p₂.op` is
bijective as soon as the corresponding map for the primed datum is. -/
public theorem bijective_mapToEqualizer_of_bijective {U V W U' V' W' : C}
    (f : V ⟶ U) (p₁ p₂ : W ⟶ V) (hp : p₁ ≫ f = p₂ ≫ f)
    (f' : V' ⟶ U') (p₁' p₂' : W' ⟶ V') (hp' : p₁' ≫ f' = p₂' ≫ f')
    (u : U' ⟶ U) (v : V' ⟶ V) (q : W' ⟶ W)
    (hf : f' ≫ u = v ≫ f) (h₁ : p₁' ≫ v = q ≫ p₁) (h₂ : p₂' ≫ v = q ≫ p₂)
    (hu : Function.Bijective (F.map u.op)) (hv : Function.Bijective (F.map v.op))
    (hq : Function.Bijective (F.map q.op))
    (h : Function.Bijective (mapToEqualizer F f' p₁' p₂' hp')) :
    Function.Bijective (mapToEqualizer F f p₁ p₂ hp) := by
  have hres := bijective_restrict_mapsTo_equalizer F p₁ p₂ p₁' p₂' v q h₁ h₂ hv hq.1
  refine (hres.of_comp_iff' _).1 ?_
  have hsq : (mapsTo_equalizer F p₁ p₂ p₁' p₂' v q h₁ h₂).restrict _ _ _ ∘
      mapToEqualizer F f p₁ p₂ hp = mapToEqualizer F f' p₁' p₂' hp' ∘ F.map u.op := by
    funext t
    refine Subtype.ext ?_
    show F.map v.op (F.map f.op t) = F.map f'.op (F.map u.op t)
    exact map_op_comp_apply_eq F _ _ _ _ hf.symm t
  rw [hsq]
  exact h.comp hu

end regularTopology

namespace IsPullback

/-- In a cartesian square of types
```
A --α--> B
|β       |γ
v        v
D --δ--> E
```
whose bottom row `δ : D ⟶ E` is a map between singletons, the top map `α : A ⟶ B` is bijective. -/
public theorem bijective_fst_of_subsingleton {A B D E : Type w} {α : A ⟶ B} {β : A ⟶ D}
    {γ : B ⟶ E} {δ : D ⟶ E} (h : IsPullback α β γ δ) [Subsingleton D] [Subsingleton E]
    [Nonempty D] : Function.Bijective α :=
  ⟨fun _ _ hxy ↦ Types.ext_of_isPullback h hxy (Subsingleton.elim _ _), fun b ↦
    (Types.exists_of_isPullback h b (Classical.arbitrary D) (Subsingleton.elim _ _)).imp
      fun _ ↦ And.left⟩

end IsPullback

end CategoryTheory

end
