module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Sites.Grothendieck

/-! # Local equality of morphisms in a category over a site

Let `p : 𝒳 ⥤ 𝒮` be a category over a site `(𝒮, J)`. Following the first stage of the
construction of the stackification of a fibred category, we say that two morphisms
`a b : x ⟶ y` of `𝒳` are *locally equal* if they lie over the same morphism of `𝒮` and
if there is a covering sieve `R` of `p.obj x` such that `a` and `b` agree after
restricting `x` along any morphism of `𝒳` lying over a member of `R`.

The source phrases the condition using a covering family `{f i : U i ⟶ U}` and the chosen
restrictions `(f i)^* x ⟶ x`. The formulation used here quantifies over *all* morphisms
`φ : w ⟶ x` of `𝒳` whose image lies in a covering sieve. For a fibred category the two
agree: any such `φ` factors through a strongly cartesian morphism lying over `p.map φ`
(see `CategoryTheory.Functor.LocallyEqual.of_isStronglyCartesian`), so testing against all
morphisms is no stronger than testing against the chosen restrictions. The advantage is
that stability under pre- and postcomposition — the congruence property, which is what
makes the quotient category exist — needs no fibredness hypothesis at all.

## Main definitions

* `CategoryTheory.Functor.LocallyEqual`: the relation itself.
* `CategoryTheory.Functor.locallyEqualRel`: the same relation packaged as a `HomRel`.

## Main results

* `CategoryTheory.Functor.congruence_locallyEqualRel`: local equality is a congruence,
  so morphisms may be quotiented by it. No fibredness is required.
* `CategoryTheory.Functor.LocallyEqual.of_isStronglyCartesian`: for a fibred category it
  suffices to test local equality against one chosen strongly cartesian restriction for
  each member of a covering sieve.

## References

This is the relation `∼` of the first stage of the proof of Stacks 02ZN.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Two morphisms `a b : x ⟶ y` of `𝒳` are *locally equal* with respect to a topology `J`
on the base `𝒮` if they lie over the same morphism of `𝒮` and if there is a covering sieve
`R` of `p.obj x` such that `φ ≫ a = φ ≫ b` for every morphism `φ` into `x` lying over a
member of `R`. -/
def LocallyEqual (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) {x y : 𝒳} (a b : x ⟶ y) : Prop :=
  p.map a = p.map b ∧
    ∃ R ∈ J (p.obj x), ∀ ⦃w : 𝒳⦄ (φ : w ⟶ x), R.arrows (p.map φ) → φ ≫ a = φ ≫ b

variable {p : 𝒳 ⥤ 𝒮} {J : GrothendieckTopology 𝒮}

/-- Locally equal morphisms lie over the same morphism of the base. -/
theorem LocallyEqual.base_eq {x y : 𝒳} {a b : x ⟶ y} (h : p.LocallyEqual J a b) :
    p.map a = p.map b :=
  h.1

/-- Equal morphisms are locally equal. -/
theorem locallyEqual_of_eq {x y : 𝒳} {a b : x ⟶ y} (h : a = b) : p.LocallyEqual J a b :=
  ⟨by rw [h], ⊤, J.top_mem _, fun _ _ _ ↦ by rw [h]⟩

/-- Local equality is reflexive. -/
@[refl]
theorem LocallyEqual.refl {x y : 𝒳} (a : x ⟶ y) : p.LocallyEqual J a a :=
  locallyEqual_of_eq rfl

/-- Local equality is symmetric, the same covering sieve witnessing both directions. -/
theorem LocallyEqual.symm {x y : 𝒳} {a b : x ⟶ y} (h : p.LocallyEqual J a b) :
    p.LocallyEqual J b a := by
  obtain ⟨hbase, R, hR, hagree⟩ := h
  exact ⟨hbase.symm, R, hR, fun _ φ hφ ↦ (hagree φ hφ).symm⟩

/-- Local equality is transitive, witnessed by the intersection of the two covering sieves. -/
theorem LocallyEqual.trans {x y : 𝒳} {a b c : x ⟶ y} (hab : p.LocallyEqual J a b)
    (hbc : p.LocallyEqual J b c) : p.LocallyEqual J a c := by
  obtain ⟨hbase₁, R, hR, hagree₁⟩ := hab
  obtain ⟨hbase₂, S, hS, hagree₂⟩ := hbc
  refine ⟨hbase₁.trans hbase₂, R ⊓ S, J.intersection_covering hR hS, fun _ φ hφ ↦ ?_⟩
  exact (hagree₁ φ hφ.1).trans (hagree₂ φ hφ.2)

/-- Local equality is an equivalence relation on each set of morphisms `x ⟶ y`. -/
theorem equivalence_locallyEqual (x y : 𝒳) :
    _root_.Equivalence (fun a b : x ⟶ y ↦ p.LocallyEqual J a b) where
  refl := LocallyEqual.refl
  symm := LocallyEqual.symm
  trans := LocallyEqual.trans

/-- Local equality of morphisms, packaged as a `HomRel` on `𝒳` so that the quotient
category by it can be formed. -/
def locallyEqualRel (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : HomRel 𝒳 :=
  fun _ _ a b ↦ p.LocallyEqual J a b

/-- The `HomRel` `locallyEqualRel` relates `a` and `b` exactly when they are locally equal. -/
theorem locallyEqualRel_iff {x y : 𝒳} (a b : x ⟶ y) :
    p.locallyEqualRel J a b ↔ p.LocallyEqual J a b :=
  Iff.rfl

/-- Local equality is stable under precomposition. If `g` and `g'` are locally equal, then
so are `f ≫ g` and `f ≫ g'`: pull the witnessing covering sieve back along `p.map f`. -/
instance isStableUnderPrecomp_locallyEqualRel :
    HomRel.IsStableUnderPrecomp (p.locallyEqualRel J) where
  comp_left := by
    intro x y z f g g' h
    obtain ⟨hbase, R, hR, hagree⟩ := h
    refine ⟨by simp [hbase], R.pullback (p.map f), J.pullback_stable _ hR, fun w φ hφ ↦ ?_⟩
    have hmem : R.arrows (p.map (φ ≫ f)) := by rw [p.map_comp]; exact hφ
    simpa only [assoc] using hagree (φ ≫ f) hmem

/-- Local equality is stable under postcomposition: the same covering sieve works. -/
instance isStableUnderPostcomp_locallyEqualRel :
    HomRel.IsStableUnderPostcomp (p.locallyEqualRel J) where
  comp_right := by
    intro x y z f f' g h
    obtain ⟨hbase, R, hR, hagree⟩ := h
    refine ⟨by simp [hbase], R, hR, fun w φ hφ ↦ ?_⟩
    rw [← assoc, ← assoc, hagree φ hφ]

/-- **Local equality is a congruence.** Hence the quotient of `𝒳` by local equality of
morphisms is a category, and `CategoryTheory.Quotient.functor_map_eq_iff` applies to it:
the quotient makes no identifications beyond local equality.

Note that no fibredness hypothesis on `p` is needed. -/
instance congruence_locallyEqualRel : Congruence (p.locallyEqualRel J) where
  equivalence := equivalence_locallyEqual _ _

/-- **The relation is non-degenerate.** For the trivial topology, in which only the maximal
sieve is covering, local equality is equality. So the first stage of the construction of the
stackification does nothing when the topology is trivial, as it must not. -/
theorem locallyEqual_bot_iff {x y : 𝒳} (a b : x ⟶ y) :
    p.LocallyEqual ⊥ a b ↔ a = b := by
  refine ⟨fun h ↦ ?_, locallyEqual_of_eq⟩
  obtain ⟨-, R, hR, hagree⟩ := h
  rw [GrothendieckTopology.bot_covering] at hR
  subst hR
  simpa using hagree (𝟙 x) trivial

/-- The characterisation of local equality closest to the source: for a fibred category it
suffices to exhibit, for each member `f` of a covering sieve, *one* strongly cartesian
morphism over `f` along which `a` and `b` agree. Every other morphism into `x` over a
member of the sieve then factors through it. -/
theorem LocallyEqual.of_isStronglyCartesian [p.IsFibered] {x y : 𝒳} {a b : x ⟶ y}
    (hbase : p.map a = p.map b) {R : Sieve (p.obj x)} (hR : R ∈ J (p.obj x))
    (h : ∀ ⦃V : 𝒮⦄ (f : V ⟶ p.obj x), R.arrows f → ∀ {w : 𝒳} (φ : w ⟶ x),
      p.IsStronglyCartesian f φ → φ ≫ a = φ ≫ b) :
    p.LocallyEqual J a b := by
  refine ⟨hbase, R, hR, fun w φ hφ ↦ ?_⟩
  -- The chosen strongly cartesian morphism over `p.map φ`.
  set ψ := IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (p.map φ) with hψdef
  have hcart : p.IsStronglyCartesian (p.map φ) ψ := inferInstance
  have hfac : IsStronglyCartesian.map p (p.map φ) ψ (id_comp (p.map φ)).symm φ ≫ ψ = φ :=
    IsStronglyCartesian.fac ..
  rw [← hfac, assoc, assoc, h (p.map φ) hφ ψ hcart]

end CategoryTheory.Functor
