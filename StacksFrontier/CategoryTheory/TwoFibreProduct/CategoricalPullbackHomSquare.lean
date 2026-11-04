module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackSquareDiagonal
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Full faithfulness of a comparison functor, read as a cartesian square of Hom-sets

Fix a 2-commutative square of categories

```
C' --a--> C
|         |
u         p
↓         ↓
D' --b--> D
```

that is, functors `a`, `u`, `p`, `b` together with a natural isomorphism `α : a ⋙ p ≅ u ⋙ b`, and
let `A : C' ⥤ C ×_D D'` be its comparison functor
`CategoryTheory.Limits.CategoricalPullback.squareComparison`. A morphism
`A x ⟶ A y` is, by the definition of the Hom-sets of a categorical pullback, exactly a pair of
morphisms `g : a x ⟶ a y` and `k : u x ⟶ u y` with `p g ≫ α_y = α_x ≫ b k`. So **`A` is fully
faithful precisely when, for every pair of objects `x, y` of `C'`, the square of Hom-sets**

```
(x ⟶ y)   --a--> (a x ⟶ a y)
   |                  |  g ↦ p g ≫ α_y
   u                  |
   ↓                  ↓
(u x ⟶ u y) --k ↦ α_x ≫ b k--> (p (a x) ⟶ b (u y))
```

**is cartesian.** That is the form in which full faithfulness of such a comparison functor is
proved in practice: one exhibits the four Hom-sets as concrete objects — matrices over a ring of
sections, say — and the square of Hom-sets as a cartesian square of those.

This complements
`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff`, which
characterises full faithfulness of `A` through the diagonal of the square (Stacks 0CMW) and needs
two of the corners to be groupoids. **No groupoid hypothesis appears here**, and nothing is
assumed of the four categories beyond their being categories.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.faithful_squareComparison_of_jointly_injective` and
  `CategoryTheory.Limits.CategoricalPullback.full_squareComparison_of_exists`: the comparison
  functor is faithful, respectively full, as soon as `a` and `u` are jointly injective on each
  Hom-set, respectively as soon as every compatible pair of morphisms comes from a morphism of
  `C'`. These carry no universe restriction.
* `CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback`:
  **the comparison functor is fully faithful if and only if the square of Hom-sets above is
  cartesian for every pair of objects.**

## Implementation notes

The two "unpackaged" criteria are stated first and carry no universe restriction, because the
joint injectivity and the existence statement each mention only two of the four Hom-sets at a
time. The cartesian-square form, by contrast, is a square in a *single* category of types, so the
four Hom-sets must lie in one universe; it is therefore stated in a section in which all four
categories have morphisms in the same universe `v`. A consumer whose four categories do not
satisfy that can still use the two unpackaged criteria.

The square is stated on morphisms of types, `CategoryTheory.asHom` (`↾`) being applied to each of
the four maps, since that is where a cartesian square lives; the elementary characterisation
`CategoryTheory.Limits.Types.isPullback_iff` is what both directions go through. Note that
`Θ → X` and `Θ ⟶ X` are not interchangeable in this development, so the four maps are written as
honest functions and turned into morphisms once — the same convention as
`CategoryTheory.Limits.Types.isPullback_pi`.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CategoricalPullback

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section General

variable {C' : Type u₁} {C : Type u₂} {D' : Type u₃} {D : Type u₄}
  [Category.{v₁} C'] [Category.{v₂} C] [Category.{v₃} D'] [Category.{v₄} D]
  (a : C' ⥤ C) (u : C' ⥤ D') (p : C ⥤ D) (b : D' ⥤ D) (α : a ⋙ p ≅ u ⋙ b)

/-- **The comparison functor of a 2-commutative square is faithful as soon as the two functors
out of its initial corner are jointly injective on Hom-sets.** A morphism of the categorical
pullback is a pair of morphisms, so two morphisms of `C'` with the same image agree as soon as
their images under `a` and under `u` agree. -/
theorem faithful_squareComparison_of_jointly_injective
    (h : ∀ (x y : C') (f g : x ⟶ y), a.map f = a.map g → u.map f = u.map g → f = g) :
    (squareComparison a u p b α).Faithful where
  map_injective {x y} {f g} hfg :=
    h x y f g (congrArg Hom.fst hfg) (congrArg Hom.snd hfg)

/-- **The comparison functor of a 2-commutative square is full as soon as every compatible pair
of morphisms comes from a morphism of the initial corner.** A morphism `A x ⟶ A y` is exactly a
pair `(g, k)` satisfying the displayed compatibility, so fullness is the statement that each such
pair is `(a f, u f)` for some `f : x ⟶ y`. -/
theorem full_squareComparison_of_exists
    (h : ∀ (x y : C') (g : a.obj x ⟶ a.obj y) (k : u.obj x ⟶ u.obj y),
      p.map g ≫ α.hom.app y = α.hom.app x ≫ b.map k →
      ∃ f : x ⟶ y, a.map f = g ∧ u.map f = k) :
    (squareComparison a u p b α).Full where
  map_surjective {x y} φ := by
    obtain ⟨f, hf₁, hf₂⟩ := h x y φ.fst φ.snd φ.w
    exact ⟨f, hom_ext hf₁ hf₂⟩

/-- The two functors out of the initial corner are jointly injective on Hom-sets as soon as the
comparison functor is faithful. This is the converse of
`CategoryTheory.Limits.CategoricalPullback.faithful_squareComparison_of_jointly_injective`. -/
theorem jointly_injective_of_faithful_squareComparison
    [(squareComparison a u p b α).Faithful] (x y : C') (f g : x ⟶ y)
    (h₁ : a.map f = a.map g) (h₂ : u.map f = u.map g) : f = g :=
  (squareComparison a u p b α).map_injective (hom_ext h₁ h₂)

/-- Every compatible pair of morphisms comes from a morphism of the initial corner as soon as the
comparison functor is full. This is the converse of
`CategoryTheory.Limits.CategoricalPullback.full_squareComparison_of_exists`. -/
theorem exists_of_full_squareComparison [(squareComparison a u p b α).Full] (x y : C')
    (g : a.obj x ⟶ a.obj y) (k : u.obj x ⟶ u.obj y)
    (w : p.map g ≫ α.hom.app y = α.hom.app x ≫ b.map k) :
    ∃ f : x ⟶ y, a.map f = g ∧ u.map f = k :=
  let φ : (squareComparison a u p b α).obj x ⟶ (squareComparison a u p b α).obj y :=
    { fst := g, snd := k, w := w }
  ⟨(squareComparison a u p b α).preimage φ,
    congrArg Hom.fst ((squareComparison a u p b α).map_preimage φ),
    congrArg Hom.snd ((squareComparison a u p b α).map_preimage φ)⟩

end General

section Types

variable {C' : Type u₁} {C : Type u₂} {D' : Type u₃} {D : Type u₄}
  [Category.{v} C'] [Category.{v} C] [Category.{v} D'] [Category.{v} D]
  (a : C' ⥤ C) (u : C' ⥤ D') (p : C ⥤ D) (b : D' ⥤ D) (α : a ⋙ p ≅ u ⋙ b)

/-- The square of Hom-sets attached to a 2-commutative square at a pair of objects of its initial
corner commutes: that is the naturality of the filler `α`. -/
theorem squareComparison_homSquare_w (x y : C') :
    (↾fun f : x ⟶ y => a.map f) ≫ (↾fun g : a.obj x ⟶ a.obj y => p.map g ≫ α.hom.app y) =
      (↾fun f : x ⟶ y => u.map f) ≫ (↾fun k : u.obj x ⟶ u.obj y => α.hom.app x ≫ b.map k) := by
  ext f
  exact α.hom.naturality f

/-- **The comparison functor of a 2-commutative square is faithful as soon as the square of
Hom-sets is cartesian at every pair of objects.** -/
theorem faithful_squareComparison_of_isPullback
    (h : ∀ x y : C', IsPullback (↾fun f : x ⟶ y => a.map f) (↾fun f : x ⟶ y => u.map f)
      (↾fun g : a.obj x ⟶ a.obj y => p.map g ≫ α.hom.app y)
      (↾fun k : u.obj x ⟶ u.obj y => α.hom.app x ≫ b.map k)) :
    (squareComparison a u p b α).Faithful :=
  faithful_squareComparison_of_jointly_injective a u p b α fun x y _ _ h₁ h₂ =>
    Types.ext_of_isPullback (h x y) h₁ h₂

/-- **The comparison functor of a 2-commutative square is full as soon as the square of Hom-sets
is cartesian at every pair of objects.** -/
theorem full_squareComparison_of_isPullback
    (h : ∀ x y : C', IsPullback (↾fun f : x ⟶ y => a.map f) (↾fun f : x ⟶ y => u.map f)
      (↾fun g : a.obj x ⟶ a.obj y => p.map g ≫ α.hom.app y)
      (↾fun k : u.obj x ⟶ u.obj y => α.hom.app x ≫ b.map k)) :
    (squareComparison a u p b α).Full :=
  full_squareComparison_of_exists a u p b α fun x y g k w =>
    Types.exists_of_isPullback (h x y) g k w

/-- The square of Hom-sets is cartesian at every pair of objects as soon as the comparison
functor is fully faithful. -/
theorem isPullback_squareComparison_homSquare [(squareComparison a u p b α).Full]
    [(squareComparison a u p b α).Faithful] (x y : C') :
    IsPullback (↾fun f : x ⟶ y => a.map f) (↾fun f : x ⟶ y => u.map f)
      (↾fun g : a.obj x ⟶ a.obj y => p.map g ≫ α.hom.app y)
      (↾fun k : u.obj x ⟶ u.obj y => α.hom.app x ≫ b.map k) := by
  rw [Types.isPullback_iff]
  refine ⟨squareComparison_homSquare_w a u p b α x y, ?_, ?_⟩
  · intro f g ⟨h₁, h₂⟩
    exact jointly_injective_of_faithful_squareComparison a u p b α x y f g h₁ h₂
  · intro g k w
    exact exists_of_full_squareComparison a u p b α x y g k w

/-- Conjugating two morphisms with the same image under a functor by isomorphisms keeps their
images equal. -/
private theorem map_conj_eq {X : Type*} {Y : Type*} [Category X] [Category Y] (F : X ⥤ Y)
    {x y x' y' : X} (ex : x ≅ x') (ey : y ≅ y') {f₁ f₂ : x' ⟶ y'} (h : F.map f₁ = F.map f₂) :
    F.map (ex.hom ≫ f₁ ≫ ey.inv) = F.map (ex.hom ≫ f₂ ≫ ey.inv) := by
  simp [h]

/-- A morphism whose image is a conjugate of `g` conjugates back to a morphism with image `g`. -/
private theorem map_conj_inv_eq {X : Type*} {Y : Type*} [Category X] [Category Y] (F : X ⥤ Y)
    {x y x' y' : X} (ex : x ≅ x') (ey : y ≅ y') {f : x ⟶ y} {g : F.obj x' ⟶ F.obj y'}
    (hf : F.map f = F.map ex.hom ≫ g ≫ F.map ey.inv) :
    F.map (ex.inv ≫ f ≫ ey.hom) = g := by
  simp [hf, ← F.map_comp]

/-- **Cartesianness of the square of Hom-sets depends only on the isomorphism classes of the two
objects.**  Conjugating a morphism by two isomorphisms is a bijection of Hom-sets, and it commutes
with the four maps of the square up to the naturality of the filler `α`.

This is what lets a criterion proved at *particular* objects — free sheaves of modules, say — be
applied at every object isomorphic to one of them, for instance to pass the cartesian Hom-square
of [Stacks, Tag 0EXD] from a free module to a module that is merely trivialised. -/
theorem isPullback_squareComparison_homSquare_of_iso {x y x' y' : C'} (ex : x ≅ x') (ey : y ≅ y')
    (h : IsPullback (↾fun f : x ⟶ y => a.map f) (↾fun f : x ⟶ y => u.map f)
      (↾fun g : a.obj x ⟶ a.obj y => p.map g ≫ α.hom.app y)
      (↾fun k : u.obj x ⟶ u.obj y => α.hom.app x ≫ b.map k)) :
    IsPullback (↾fun f : x' ⟶ y' => a.map f) (↾fun f : x' ⟶ y' => u.map f)
      (↾fun g : a.obj x' ⟶ a.obj y' => p.map g ≫ α.hom.app y')
      (↾fun k : u.obj x' ⟶ u.obj y' => α.hom.app x' ≫ b.map k) := by
  have hαx : p.map (a.map ex.hom) ≫ α.hom.app x' = α.hom.app x ≫ b.map (u.map ex.hom) :=
    α.hom.naturality ex.hom
  have hαy : p.map (a.map ey.inv) ≫ α.hom.app y = α.hom.app y' ≫ b.map (u.map ey.inv) :=
    α.hom.naturality ey.inv
  refine (Types.isPullback_iff _ _ _ _).mpr
    ⟨squareComparison_homSquare_w a u p b α x' y', ?_, ?_⟩
  · -- Joint injectivity: conjugate into the Hom-set at `(x, y)`, then cancel the isomorphisms.
    intro f₁ f₂ ⟨h₁, h₂⟩
    have key : ex.hom ≫ f₁ ≫ ey.inv = ex.hom ≫ f₂ ≫ ey.inv :=
      Types.ext_of_isPullback h (map_conj_eq a ex ey h₁) (map_conj_eq u ex ey h₂)
    simpa using congrArg (· ≫ ey.hom) ((cancel_epi ex.hom).mp key)
  · -- Existence: conjugate the compatible pair back, solve there, conjugate the solution across.
    intro g k hgk
    have hgk' : p.map g ≫ α.hom.app y' = α.hom.app x' ≫ b.map k := hgk
    have hcompat : p.map (a.map ex.hom ≫ g ≫ a.map ey.inv) ≫ α.hom.app y =
        α.hom.app x ≫ b.map (u.map ex.hom ≫ k ≫ u.map ey.inv) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hαy, reassoc_of% hgk', reassoc_of% hαx]
    obtain ⟨f, hf₁, hf₂⟩ := Types.exists_of_isPullback h
      (a.map ex.hom ≫ g ≫ a.map ey.inv) (u.map ex.hom ≫ k ≫ u.map ey.inv) hcompat
    exact ⟨ex.inv ≫ f ≫ ey.hom, map_conj_inv_eq a ex ey hf₁, map_conj_inv_eq u ex ey hf₂⟩

/-- **The comparison functor of a 2-commutative square is fully faithful if and only if the
square of its Hom-sets is cartesian at every pair of objects of the initial corner.**

Unlike `CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff`, which
characterises the same property through the diagonal of the square, this carries no groupoid
hypothesis on any corner. -/
theorem fullyFaithful_squareComparison_iff_isPullback :
    ((squareComparison a u p b α).Full ∧ (squareComparison a u p b α).Faithful) ↔
      ∀ x y : C', IsPullback (↾fun f : x ⟶ y => a.map f) (↾fun f : x ⟶ y => u.map f)
        (↾fun g : a.obj x ⟶ a.obj y => p.map g ≫ α.hom.app y)
        (↾fun k : u.obj x ⟶ u.obj y => α.hom.app x ≫ b.map k) := by
  constructor
  · intro ⟨_, _⟩ x y
    exact isPullback_squareComparison_homSquare a u p b α x y
  · intro h
    exact ⟨full_squareComparison_of_isPullback a u p b α h,
      faithful_squareComparison_of_isPullback a u p b α h⟩

end Types

end CategoryTheory.Limits.CategoricalPullback

end
