module

public import StacksFrontier.CategoryTheory.FiberedCategory.Slice
public import StacksFrontier.CategoryTheory.FiberedCategory.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.OverIsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverStack
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Stacks and localization

Let `(𝒞, J)` be a site, let `U` be an object of `𝒞` and write `j = j_U` for the localization
functor `CategoryTheory.Over.forget U : 𝒞/U ⥤ 𝒞`. Stacks 04WV relates categories over `𝒞/U` and
categories over `𝒞` equipped with a morphism to `𝒞/U`:

* **Construction A** sends `p : 𝒮 ⥤ 𝒞/U` to `j_! p = p ⋙ j : 𝒮 ⥤ 𝒞`, together with the functor
  `p` itself as a morphism to `𝒞/U` over `𝒞`;
* **Construction B** sends a pair `(q : 𝒯 ⥤ 𝒞, p : 𝒯 ⥤ 𝒞/U)` with `p ⋙ j = q` to `p`.

This file shows that `Functor.IsHomLift`, `Functor.IsStronglyCartesian` and `Functor.IsFibered`
for `p` and for `p ⋙ j` say the same thing, and that Constructions A and B are mutually inverse
functors between the 2-category `CategoryTheory.CatFibered (𝒞/U)` of fibred categories over `𝒞/U`
(Stacks 02XP) and the 2-category of pairs `(𝒯, p)` with `𝒯` a fibred category over `𝒞` and
`p : 𝒯 ⟶ 𝒞/U` a 1-morphism over `𝒞`. When `h_U` is a sheaf, Construction A takes stacks over
`(𝒞/U, J.over U)` to stacks over `(𝒞, J)`, and is bijective on 1-morphisms and on 2-morphisms of
stacks.

## Main definitions

* `CategoryTheory.Over.constructionA` and `CategoryTheory.Over.constructionB`: the two
  constructions on objects, for fibred categories.
* `CategoryTheory.Over.CatFiberedPair`, `CategoryTheory.Over.CatFiberedPairHom` and
  `CategoryTheory.Over.CatFiberedPairHom₂`: the objects, 1-morphisms and 2-morphisms of the
  2-category of pairs `(𝒯, p)`.
* `CategoryTheory.Over.constructionObjEquiv`, `CategoryTheory.Over.constructionHomEquiv` and
  `CategoryTheory.Over.constructionHom₂Equiv`: Constructions A and B are mutually inverse on
  objects, on 1-morphisms and on 2-morphisms.
* `CategoryTheory.Over.stackConstructionA`, `CategoryTheory.Over.stackConstructionHomEquiv` and
  `CategoryTheory.Over.stackConstructionHom₂Equiv`: Construction A for stacks, and its
  bijectivity on 1-morphisms and on 2-morphisms.

## Main results

* `CategoryTheory.Functor.isHomLift_comp_forget` and
  `CategoryTheory.Functor.isHomLift_of_comp_forget`: `Functor.IsHomLift` transfers in both
  directions across `j`.
* `CategoryTheory.Functor.isStronglyCartesian_comp_forget_iff`: a morphism of `𝒮` is strongly
  cartesian for `p` if and only if it is strongly cartesian for `p ⋙ j`.
* `CategoryTheory.Functor.preservesStronglyCartesian_comp_forget_iff`: a functor over `𝒞/U`
  preserves strongly cartesian morphisms for the structure functors to `𝒞/U` if and only if it
  preserves them for their composites with `j`.
* `CategoryTheory.Functor.isFibered_comp_forget_iff`: `p` is a fibred category over `𝒞/U` if and
  only if `p ⋙ j` is a fibred category over `𝒞`.
* `CategoryTheory.Functor.isHomLift_id_comp_forget_iff`: a morphism of `𝒮` lies over an identity
  of `𝒞/U` if and only if it lies over the corresponding identity of `𝒞`.
* `CategoryTheory.Over.map_app_eq_eqToHom`: the image under the structure morphism to `𝒞/U` of
  every component of a 2-morphism of pairs is an `eqToHom`.
* `CategoryTheory.Functor.isInheritedTopology_forget`: `J.over U` is the topology on `𝒞/U`
  inherited from `(𝒞, J)` along `j` (Stacks 06NV).
* `CategoryTheory.Functor.isStack_comp_forget`: if `h_U` is a sheaf and `p : 𝒮 ⥤ 𝒞/U` is a stack
  over `(𝒞/U, J.over U)`, then `p ⋙ j : 𝒮 ⥤ 𝒞` is a stack over `(𝒞, J)`.

## Implementation notes

A 1-morphism of pairs commutes with the structure morphisms to `𝒞/U` on the nose, and a 2-morphism
of pairs is any 2-morphism of fibred categories over `𝒞` between the underlying 1-morphisms; by
`CategoryTheory.Over.map_app_eq_eqToHom` no triangle condition has to be imposed on it.

Since `𝒞/U` has to be an object of the 2-category of fibred categories (or of stacks) over `𝒞`,
the 2-categorical statements are stated for fibre categories in the universes of `𝒞/U` itself,
`Type (max u₁ v₁)` with morphisms in `v₁`. The transfer lemmas are universe-polymorphic.

The converse of `CategoryTheory.Functor.isStack_comp_forget`, Construction B for stacks, is
`CategoryTheory.Over.isStack_of_comp_forget`, and the bijection on objects of stacks is
`CategoryTheory.Over.stackConstructionObjEquiv`; both need `[HasPullbacks 𝒞]`.
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {U : 𝒞} {𝒳 : Type u₂} [Category.{v₂} 𝒳]

section IsHomLift

variable (p : 𝒳 ⥤ Over U)

/-- If a morphism `φ : a ⟶ b` of `𝒮` lies over `j g` for the composite `p ⋙ j`, where
`g : A ⟶ p b`, then `A = p a`. -/
lemma over_eq_of_isHomLift_comp_forget {a b : 𝒳} {A : Over U} (g : A ⟶ p.obj b) (φ : a ⟶ b)
    (h : (p ⋙ Over.forget U).IsHomLift ((Over.forget U).map g) φ) : A = p.obj a := by
  have := h
  have hA : A.left = (p.obj a).left :=
    (IsHomLift.domain_eq (p ⋙ Over.forget U) ((Over.forget U).map g) φ).symm
  have hf : (Over.forget U).map g
      = eqToHom hA ≫ (p ⋙ Over.forget U).map φ ≫ 𝟙 _ :=
    IsHomLift.fac (p ⋙ Over.forget U) ((Over.forget U).map g) φ
  simp only [Over.forget_obj, Over.forget_map, Functor.comp_obj, Functor.comp_map,
    Category.comp_id] at hf
  have hA' : A.left = (p.obj a).left := hA
  rcases A with ⟨AL, AR, Ah⟩
  subst hA'
  simp only [eqToHom_refl, Category.id_comp] at hf
  have hAw : g.left ≫ (p.obj b).hom = Ah := Over.w g
  have hAh : Ah = (p.obj a).hom := by rw [← hAw, hf, Over.w (p.map φ)]
  subst hAh
  obtain rfl : AR = (p.obj a).right := Subsingleton.elim _ _
  rfl

/-- `Functor.IsHomLift` for `p` gives `Functor.IsHomLift` for `p ⋙ j`. -/
lemma isHomLift_comp_forget {a b : 𝒳} {A B : Over U} (g : A ⟶ B) (φ : a ⟶ b)
    (h : p.IsHomLift g φ) :
    (p ⋙ Over.forget U).IsHomLift ((Over.forget U).map g) φ := by
  cases h
  exact ⟨_⟩

/-- `Functor.IsHomLift` for `p ⋙ j` gives `Functor.IsHomLift` for `p`. -/
lemma isHomLift_of_comp_forget {a b : 𝒳} {A : Over U} (g : A ⟶ p.obj b) (φ : a ⟶ b)
    (h : (p ⋙ Over.forget U).IsHomLift ((Over.forget U).map g) φ) : p.IsHomLift g φ := by
  obtain rfl : A = p.obj a := over_eq_of_isHomLift_comp_forget p g φ h
  obtain rfl : p.map φ = g :=
    (Over.forget U).map_injective (@IsHomLift.eq_of_isHomLift _ _ _ _
      (p ⋙ Over.forget U) a b ((Over.forget U).map g) φ h).symm
  exact CategoryTheory.IsHomLift.map p φ

/-- `Functor.IsHomLift` for `p` and for `p ⋙ j` are equivalent. -/
private lemma isHomLift_comp_forget_iff {a b : 𝒳} {A : Over U} (g : A ⟶ p.obj b) (φ : a ⟶ b) :
    p.IsHomLift g φ ↔ (p ⋙ Over.forget U).IsHomLift ((Over.forget U).map g) φ :=
  ⟨isHomLift_comp_forget p g φ, isHomLift_of_comp_forget p g φ⟩

/-- A morphism of `𝒮` lies over the identity of an object `A` of `𝒞/U` for `p` if and only if it
lies over the identity of the underlying object of `𝒞` for `p ⋙ j`. -/
lemma isHomLift_id_comp_forget_iff {x y : 𝒳} {A : Over U} (hy : p.obj y = A) (ψ : x ⟶ y) :
    p.IsHomLift (𝟙 A) ψ ↔ (p ⋙ Over.forget U).IsHomLift (𝟙 A.left) ψ := by
  subst hy
  simpa using isHomLift_comp_forget_iff p (𝟙 (p.obj y)) ψ

end IsHomLift

section IsStronglyCartesian

variable (p : 𝒳 ⥤ Over U)

/-- Strong cartesianness for `p` gives strong cartesianness for `p ⋙ j`. -/
lemma isStronglyCartesian_comp_forget {a b : 𝒳} {A : Over U} (g : A ⟶ p.obj b) (φ : a ⟶ b)
    (hp : p.IsStronglyCartesian g φ) :
    (p ⋙ Over.forget U).IsStronglyCartesian ((Over.forget U).map g) φ := by
  have := hp
  have hlift : (p ⋙ Over.forget U).IsHomLift ((Over.forget U).map g) φ :=
    isHomLift_comp_forget p g φ hp.toIsHomLift
  obtain rfl : A = p.obj a := (IsHomLift.domain_eq p g φ).symm
  refine @IsStronglyCartesian.mk _ _ _ _ _ _ _ _ _ _ _ hlift ?_
  intro a' g' φ' hφ'
  have heq : g' ≫ (Over.forget U).map g = (p ⋙ Over.forget U).map φ' := by
    have := hφ'
    exact IsHomLift.eq_of_isHomLift (p ⋙ Over.forget U) _ φ'
  have hw : g' ≫ (p.obj a).hom = (p.obj a').hom := by
    rw [← Over.w g, ← Category.assoc]
    simp only [Over.forget_map] at heq
    rw [heq]
    exact Over.w (p.map φ')
  have hg'' : p.IsHomLift ((Over.homMk g' hw : p.obj a' ⟶ p.obj a) ≫ g) φ' := by
    refine isHomLift_of_comp_forget p _ φ' ?_
    simpa using hφ'
  obtain ⟨χ, ⟨hχ_lift, hχ_comp⟩, hχ_uniq⟩ :=
    IsStronglyCartesian.universal_property (p := p) (f := g) (φ := φ)
      (g := (Over.homMk g' hw : p.obj a' ⟶ p.obj a))
      (f' := (Over.homMk g' hw : p.obj a' ⟶ p.obj a) ≫ g) rfl φ'
  refine ⟨χ, ⟨?_, hχ_comp⟩, ?_⟩
  · simpa using (isHomLift_comp_forget_iff p (Over.homMk g' hw) χ).1 hχ_lift
  · rintro χ₁ ⟨hχ₁_lift, hχ₁_comp⟩
    exact hχ_uniq χ₁ ⟨(isHomLift_comp_forget_iff p (Over.homMk g' hw) χ₁).2
      (by simpa using hχ₁_lift), hχ₁_comp⟩

/-- Strong cartesianness for `p ⋙ j` gives strong cartesianness for `p`. -/
lemma isStronglyCartesian_of_comp_forget {a b : 𝒳} {A : Over U} (g : A ⟶ p.obj b) (φ : a ⟶ b)
    (hp : (p ⋙ Over.forget U).IsStronglyCartesian ((Over.forget U).map g) φ) :
    p.IsStronglyCartesian g φ := by
  have hlift : p.IsHomLift g φ := isHomLift_of_comp_forget p g φ hp.toIsHomLift
  refine @IsStronglyCartesian.mk _ _ _ _ _ _ _ _ _ _ _ hlift ?_
  intro a' g' φ' hφ'
  obtain rfl : A = p.obj a := over_eq_of_isHomLift_comp_forget p g φ hp.toIsHomLift
  have hcomp : (p ⋙ Over.forget U).IsHomLift ((Over.forget U).map (g' ≫ g)) φ' :=
    isHomLift_comp_forget p (g' ≫ g) φ' hφ'
  obtain ⟨χ, ⟨hχ_lift, hχ_comp⟩, hχ_uniq⟩ :=
    IsStronglyCartesian.universal_property
      (p := p ⋙ Over.forget U) (f := (Over.forget U).map g) (φ := φ)
      (g := (Over.forget U).map g') (f' := (Over.forget U).map (g' ≫ g)) (by simp) φ'
  refine ⟨χ, ⟨isHomLift_of_comp_forget p g' χ hχ_lift, hχ_comp⟩, ?_⟩
  rintro χ₁ ⟨hχ₁_lift, hχ₁_comp⟩
  exact hχ_uniq χ₁ ⟨isHomLift_comp_forget p g' χ₁ hχ₁_lift, hχ₁_comp⟩

/-- A morphism of `𝒮` is strongly cartesian for `p : 𝒮 ⥤ 𝒞/U` if and only if it is strongly
cartesian for `p ⋙ j : 𝒮 ⥤ 𝒞`. -/
lemma isStronglyCartesian_comp_forget_iff {a b : 𝒳} (φ : a ⟶ b) :
    p.IsStronglyCartesian (p.map φ) φ ↔
      (p ⋙ Over.forget U).IsStronglyCartesian ((p ⋙ Over.forget U).map φ) φ :=
  ⟨fun h ↦ isStronglyCartesian_comp_forget p (p.map φ) φ h,
    fun h ↦ isStronglyCartesian_of_comp_forget p (p.map φ) φ h⟩

end IsStronglyCartesian

section IsFibered

variable (p : 𝒳 ⥤ Over U)

/-- If `p : 𝒮 ⥤ 𝒞/U` is a fibred category over `𝒞/U`, then `j_! p = p ⋙ j : 𝒮 ⥤ 𝒞` is a fibred
category over `𝒞`. -/
lemma isFibered_comp_forget [p.IsFibered] : (p ⋙ Over.forget U).IsFibered :=
  IsFibered.comp_functor p (Over.forget U)

/-- If `p ⋙ j : 𝒮 ⥤ 𝒞` is a fibred category over `𝒞`, then `p : 𝒮 ⥤ 𝒞/U` is a fibred category
over `𝒞/U`. -/
lemma isFibered_of_comp_forget (h : (p ⋙ Over.forget U).IsFibered) : p.IsFibered :=
  have := h
  IsFibered.of_comp_over U p (p ⋙ Over.forget U) rfl

/-- A functor `p : 𝒮 ⥤ 𝒞/U` is a fibred category over `𝒞/U` if and only if `j_! p = p ⋙ j` is a
fibred category over `𝒞`. -/
lemma isFibered_comp_forget_iff : (p ⋙ Over.forget U).IsFibered ↔ p.IsFibered :=
  ⟨isFibered_of_comp_forget p, fun h ↦ have := h; isFibered_comp_forget p⟩

end IsFibered

section IsStack

/-- `J.over U` is the topology on `𝒞/U` inherited from `(𝒞, J)` along `j_U : 𝒞/U ⥤ 𝒞`
(Stacks 06NV, in the characterised form `CategoryTheory.Functor.IsInheritedTopology`): a family of
morphisms of `𝒞/U` generates a `J.over U`-covering sieve exactly when its image family in `𝒞`
generates a `J`-covering sieve. -/
lemma isInheritedTopology_forget (U : 𝒞) (J : GrothendieckTopology 𝒞) :
    IsInheritedTopology.{w} (Over.forget U) J (J.over U) := by
  intro Y I Y' g _
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Iff.rfl

/-- **Construction A for stacks.** Let `U` be an object of `𝒞` whose representable presheaf `h_U`
is a sheaf, and let `p : 𝒮 ⥤ 𝒞/U` be a stack over the site `(𝒞/U, J.over U)`. Then
`j_! p = p ⋙ j_U : 𝒮 ⥤ 𝒞` is a stack over `(𝒞, J)`. -/
@[stacks 04WV]
theorem isStack_comp_forget (p : 𝒳 ⥤ Over U) {J : GrothendieckTopology 𝒞}
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) (hp : p.IsStack (J.over U)) :
    (p ⋙ Over.forget U).IsStack J :=
  (isStack_comp_of_isInheritedTopology ((Over.isStack_forget_iff_isSheaf J).2 hU)
    (isInheritedTopology_forget U J) hp).1

end IsStack

section Preserves

/-- A morphism of `𝒮` lying over `f` for a composite `G ⋙ q` has its `G`-image lying over `f`
for `q`. -/
lemma isHomLift_map_comp {𝒴 : Type u₃} [Category.{v₃} 𝒴] (G : 𝒳 ⥤ 𝒴) (q : 𝒴 ⥤ 𝒞) {a b : 𝒳}
    (φ : a ⟶ b) {R S : 𝒞} (f : R ⟶ S) (h : (G ⋙ q).IsHomLift f φ) : q.IsHomLift f (G.map φ) := by
  cases h
  exact ⟨_⟩

/-- A functor `G : 𝒮 ⥤ 𝒮'` over `𝒞/U`, with the structure functor of `𝒮` written as `G ⋙ p'`,
preserves strongly cartesian morphisms for the structure functors `G ⋙ p', p'` to `𝒞/U` if and
only if it preserves them for their composites `G ⋙ p' ⋙ j, p' ⋙ j` to `𝒞`. -/
lemma preservesStronglyCartesian_comp_forget_iff {𝒴 : Type u₃} [Category.{v₃} 𝒴]
    (p' : 𝒴 ⥤ Over U) (G : 𝒳 ⥤ 𝒴) :
    (∀ ⦃A B : Over U⦄ ⦃a b : 𝒳⦄ (g : A ⟶ B) (φ : a ⟶ b),
        (G ⋙ p').IsStronglyCartesian g φ → p'.IsStronglyCartesian g (G.map φ)) ↔
      (∀ ⦃R S : 𝒞⦄ ⦃a b : 𝒳⦄ (f : R ⟶ S) (φ : a ⟶ b),
        (G ⋙ p' ⋙ Over.forget U).IsStronglyCartesian f φ →
          (p' ⋙ Over.forget U).IsStronglyCartesian f (G.map φ)) := by
  refine ⟨fun h R S a b f φ hsc ↦ ?_, fun h A B a b g φ hsc ↦ ?_⟩
  · have := hsc
    subst_hom_lift (G ⋙ p' ⋙ Over.forget U) f φ
    exact isStronglyCartesian_comp_forget p' (p'.map (G.map φ)) (G.map φ)
      (h ((G ⋙ p').map φ) φ
        (isStronglyCartesian_of_comp_forget (G ⋙ p') ((G ⋙ p').map φ) φ hsc))
  · have := hsc
    subst_hom_lift (G ⋙ p') g φ
    exact isStronglyCartesian_of_comp_forget p' (p'.map (G.map φ)) (G.map φ)
      (h ((G ⋙ p' ⋙ Over.forget U).map φ) φ
        (isStronglyCartesian_comp_forget (G ⋙ p') ((G ⋙ p').map φ) φ hsc))

/-- The version of `CategoryTheory.Functor.preservesStronglyCartesian_comp_forget_iff` that takes
the equality `G ⋙ p' = p` expressing that `G` is a functor over `𝒞/U` as a hypothesis. -/
lemma preservesStronglyCartesian_comp_forget_iff' {𝒴 : Type u₃} [Category.{v₃} 𝒴]
    (p : 𝒳 ⥤ Over U) (p' : 𝒴 ⥤ Over U) (G : 𝒳 ⥤ 𝒴) (hw : G ⋙ p' = p) :
    (∀ ⦃A B : Over U⦄ ⦃a b : 𝒳⦄ (g : A ⟶ B) (φ : a ⟶ b),
        p.IsStronglyCartesian g φ → p'.IsStronglyCartesian g (G.map φ)) ↔
      (∀ ⦃R S : 𝒞⦄ ⦃a b : 𝒳⦄ (f : R ⟶ S) (φ : a ⟶ b),
        (p ⋙ Over.forget U).IsStronglyCartesian f φ →
          (p' ⋙ Over.forget U).IsStronglyCartesian f (G.map φ)) := by
  subst hw
  exact preservesStronglyCartesian_comp_forget_iff p' G

/-- A functor `G` with `G ⋙ p' = p` is a 1-morphism of fibred categories over `𝒞/U` from `p` to
`p'` if and only if it is a 1-morphism of fibred categories over `𝒞` from `p ⋙ j_U` to
`p' ⋙ j_U`. -/
lemma isFibredOneMorphism_comp_forget_iff {𝒴 : Type u₃} [Category.{v₃} 𝒴]
    (p : 𝒳 ⥤ Over U) (p' : 𝒴 ⥤ Over U) (G : 𝒳 ⥤ 𝒴) (hw : G ⋙ p' = p) :
    IsFibredOneMorphism p p' G ↔
      IsFibredOneMorphism (p ⋙ Over.forget U) (p' ⋙ Over.forget U) G := by
  constructor
  · intro h
    refine ⟨congrArg (fun H : 𝒳 ⥤ Over U ↦ H ⋙ Over.forget U) hw, ?_⟩
    intro R T f a b φ hsc
    exact (preservesStronglyCartesian_comp_forget_iff' p p' G hw).1
      (by intro A B a b g ψ hg; exact h.map_isStronglyCartesian g ψ hg) f φ hsc
  · intro h
    refine ⟨hw, ?_⟩
    intro A B g a b φ hsc
    exact (preservesStronglyCartesian_comp_forget_iff' p p' G hw).2
      (by intro R T a b f ψ hf; exact h.map_isStronglyCartesian f ψ hf) g φ hsc

end Preserves

end Functor

/-- Two 1-morphisms of stacks over `𝒞` with the same underlying based functor are equal. -/
lemma BasedStack.Hom.ext_hom {𝒞 : Type u₁} [Category.{v₁} 𝒞] {J : GrothendieckTopology 𝒞}
    {𝒳 𝒴 : BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J} {f g : BasedStack.Hom 𝒳 𝒴}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  subst h
  rfl

/-! ### Constructions A and B as mutually inverse functors of 2-categories

The 2-category of pairs `(𝒯, p)`, with `𝒯` a fibred category over `𝒞` and `p : 𝒯 ⟶ 𝒞/U` a
1-morphism of fibred categories over `𝒞`, is not given a `CategoryTheory.Bicategory` instance: its
objects, 1-morphisms and 2-morphisms are `CategoryTheory.Over.CatFiberedPair`,
`CategoryTheory.Over.CatFiberedPairHom` and `CategoryTheory.Over.CatFiberedPairHom₂`, and
Constructions A and B are bijections on all three levels, compatible with identities and with
composition of 1-morphisms and of 2-morphisms.
-/

namespace Over

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] (U : 𝒞)

/-- The localization `j_U : 𝒞/U ⥤ 𝒞` as an object of the 2-category of fibred categories over `𝒞`
(Stacks 02XP). -/
def catFibered : CatFibered.{v₁, v₁, u₁, max u₁ v₁} 𝒞 :=
  ⟨{ obj := Over U, category := inferInstance, p := Over.forget U }, Over.isFibered_forget⟩

/-- An object of the right-hand 2-category of Stacks 04WV, at the level of fibred categories: a
pair `(𝒯, p)` consisting of a fibred category `𝒯` over `𝒞` and a 1-morphism `p : 𝒯 ⟶ 𝒞/U` of
fibred categories over `𝒞`. -/
abbrev CatFiberedPair := Σ 𝒯 : CatFibered.{v₁, v₁, u₁, max u₁ v₁} 𝒞, (𝒯 ⟶ catFibered U)

/-- A 1-morphism of the right-hand 2-category of Stacks 04WV: a 1-morphism of fibred categories
over `𝒞` commuting strictly with the two structure morphisms to `𝒞/U`. -/
abbrev CatFiberedPairHom (X Y : CatFiberedPair U) := { f : X.1 ⟶ Y.1 // f ≫ Y.2 = X.2 }

/-- A 2-morphism of the right-hand 2-category of Stacks 04WV: a 2-morphism of fibred categories
over `𝒞` between the underlying 1-morphisms. -/
abbrev CatFiberedPairHom₂ {X Y : CatFiberedPair U} (f g : CatFiberedPairHom U X Y) :=
  f.val ⟶ g.val

/-- The identity 1-morphism of the right-hand 2-category of Stacks 04WV. -/
def CatFiberedPairHom.id (X : CatFiberedPair U) : CatFiberedPairHom U X X :=
  ⟨𝟙 X.1, Category.id_comp _⟩

/-- Composition of 1-morphisms in the right-hand 2-category of Stacks 04WV, computed in the
2-category of fibred categories over `𝒞`. -/
def CatFiberedPairHom.comp {X Y Z : CatFiberedPair U} (f : CatFiberedPairHom U X Y)
    (g : CatFiberedPairHom U Y Z) : CatFiberedPairHom U X Z :=
  ⟨f.val ≫ g.val, by rw [Category.assoc, g.2, f.2]⟩

/-- **Construction A** on objects. A fibred category `p : 𝒮 ⥤ 𝒞/U` over `𝒞/U` is sent to
`j_! p = p ⋙ j_U : 𝒮 ⥤ 𝒞`, which is a fibred category over `𝒞`, together with `p` itself as a
1-morphism `j_! 𝒮 ⟶ 𝒞/U` of fibred categories over `𝒞`. -/
def constructionA (𝒮 : CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U)) : CatFiberedPair U :=
  ⟨⟨{ obj := 𝒮.val.obj, category := 𝒮.val.category, p := 𝒮.val.p ⋙ Over.forget U },
      Functor.isFibered_comp_forget 𝒮.val.p⟩,
    ⟨{ toFunctor := 𝒮.val.p, w := rfl }, by
      intro R S a b f φ h
      have := Functor.isHomLift_map_comp 𝒮.val.p (Over.forget U) φ f h.toIsHomLift
      exact Over.isStronglyCartesian_forget f (𝒮.val.p.map φ)⟩⟩

/-- If `G ⋙ j_U = q` and `q` is a fibred category over `𝒞`, then `G` is a fibred category over
`𝒞/U`. -/
lemma isFibered_of_pair_aux {X₀ : Type (max u₁ v₁)} [Category.{v₁} X₀] (G : X₀ ⥤ Over U)
    (q : X₀ ⥤ 𝒞) (hw : G ⋙ Over.forget U = q) (hq : q.IsFibered) : G.IsFibered := by
  subst hw
  exact Functor.isFibered_of_comp_forget G hq

/-- **Construction B** on objects. A pair `(𝒯, p)` is sent to `p : 𝒯 ⥤ 𝒞/U`, which is a fibred
category over `𝒞/U`. -/
def constructionB (X : CatFiberedPair U) :
    CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) :=
  ⟨{ obj := X.1.val.obj, category := X.1.val.category,
      p := (X.2.hom.toFunctor : X.1.val.obj ⥤ Over U) },
    isFibered_of_pair_aux U (X.2.hom.toFunctor : X.1.val.obj ⥤ Over U) X.1.val.p X.2.hom.w X.1.2⟩

/-- Construction A applied to Construction B of a pair `(𝒯, p)` gives back `(𝒯, p)`, for a pair
whose data is given explicitly. -/
lemma constructionA_constructionB_aux {X₀ : Type (max u₁ v₁)} [instX : Category.{v₁} X₀]
    (G : X₀ ⥤ Over U) (q : X₀ ⥤ 𝒞) (hw : G ⋙ Over.forget U = q) (hq : q.IsFibered)
    (hpres : ∀ ⦃R S : 𝒞⦄ ⦃a b : X₀⦄ (f : R ⟶ S) (φ : a ⟶ b),
      q.IsStronglyCartesian f φ → (Over.forget U).IsStronglyCartesian f (G.map φ)) :
    constructionA U (constructionB U ⟨⟨⟨X₀, instX, q⟩, hq⟩, ⟨⟨G, hw⟩, hpres⟩⟩) =
      ⟨⟨⟨X₀, instX, q⟩, hq⟩, ⟨⟨G, hw⟩, hpres⟩⟩ := by
  subst hw
  rfl

/-- **Constructions A and B are mutually inverse on objects**: they are inverse bijections between
fibred categories over `𝒞/U` and pairs `(𝒯, p)`. -/
def constructionObjEquiv :
    CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) ≃ CatFiberedPair U where
  toFun := constructionA U
  invFun := constructionB U
  left_inv _ := rfl
  right_inv X :=
    constructionA_constructionB_aux U (X.2.hom.toFunctor : X.1.val.obj ⥤ Over U) X.1.val.p
      X.2.hom.w X.1.2 X.2.preservesStronglyCartesian

/-- **Constructions A and B are mutually inverse on 1-morphisms**, and both are the identity on the
underlying functor: a 1-morphism `𝒮 ⟶ 𝒮'` of fibred categories over `𝒞/U` is the same thing as a
1-morphism `A 𝒮 ⟶ A 𝒮'` of pairs. -/
def constructionHomEquiv (𝒮 𝒮' : CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U)) :
    (𝒮 ⟶ 𝒮') ≃ CatFiberedPairHom U (constructionA U 𝒮) (constructionA U 𝒮') where
  toFun f :=
    ⟨⟨{ toFunctor := f.hom.toFunctor,
          w := congrArg (fun H : 𝒮.val.obj ⥤ Over U ↦ H ⋙ Over.forget U) f.hom.w },
        (Functor.preservesStronglyCartesian_comp_forget_iff' 𝒮.val.p 𝒮'.val.p f.hom.toFunctor
          f.hom.w).1 f.preservesStronglyCartesian⟩,
      CatFibered.Hom.ext' (BasedCategory.BasedFunctor.ext' f.hom.w)⟩
  invFun f :=
    ⟨{ toFunctor := f.val.hom.toFunctor,
        w := congrArg (fun h ↦ (CatFibered.Hom.hom h).toFunctor) f.2 },
      (Functor.preservesStronglyCartesian_comp_forget_iff' 𝒮.val.p 𝒮'.val.p f.val.hom.toFunctor
        (congrArg (fun h ↦ (CatFibered.Hom.hom h).toFunctor) f.2)).2
          f.val.preservesStronglyCartesian⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Construction A preserves the identity 1-morphism. -/
@[simp]
lemma constructionHomEquiv_id (𝒮 : CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U)) :
    constructionHomEquiv U 𝒮 𝒮 (𝟙 𝒮) = CatFiberedPairHom.id U (constructionA U 𝒮) :=
  rfl

/-- Construction A preserves composition of 1-morphisms. -/
@[simp]
lemma constructionHomEquiv_comp
    {𝒮 𝒮' 𝒮'' : CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U)} (f : 𝒮 ⟶ 𝒮') (g : 𝒮' ⟶ 𝒮'') :
    constructionHomEquiv U 𝒮 𝒮'' (f ≫ g) =
      CatFiberedPairHom.comp U (constructionHomEquiv U 𝒮 𝒮' f)
        (constructionHomEquiv U 𝒮' 𝒮'' g) :=
  rfl

/-- **Constructions A and B are mutually inverse on 2-morphisms**, and both are the identity on the
underlying morphism of functors. -/
def constructionHom₂Equiv {𝒮 𝒮' : CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U)}
    (f g : 𝒮 ⟶ 𝒮') :
    (f ⟶ g) ≃ CatFiberedPairHom₂ U (constructionHomEquiv U 𝒮 𝒮' f)
      (constructionHomEquiv U 𝒮 𝒮' g) where
  toFun η :=
    ⟨{ toNatTrans := η.hom.toNatTrans,
        isHomLift' := fun a ↦
          (Functor.isHomLift_id_comp_forget_iff 𝒮'.val.p (BasedFunctor.w_obj g.hom a) _).1
            (η.hom.isHomLift' a) }⟩
  invFun η :=
    ⟨{ toNatTrans := η.hom.toNatTrans,
        isHomLift' := fun a ↦
          (Functor.isHomLift_id_comp_forget_iff 𝒮'.val.p (BasedFunctor.w_obj g.hom a) _).2
            (η.hom.isHomLift' a) }⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Construction A preserves identity 2-morphisms. -/
@[simp]
lemma constructionHom₂Equiv_id {𝒮 𝒮' : CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U)}
    (f : 𝒮 ⟶ 𝒮') : constructionHom₂Equiv U f f (𝟙 f) = 𝟙 _ :=
  rfl

/-- Construction A preserves vertical composition of 2-morphisms. -/
@[simp]
lemma constructionHom₂Equiv_comp {𝒮 𝒮' : CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U)}
    {f g h : 𝒮 ⟶ 𝒮'} (η : f ⟶ g) (θ : g ⟶ h) :
    (constructionHom₂Equiv U f h (η ≫ θ)).hom =
      (constructionHom₂Equiv U f g η).hom ≫ (constructionHom₂Equiv U g h θ).hom :=
  rfl

/-- Construction A preserves left whiskering. -/
@[simp]
lemma constructionHom₂Equiv_whiskerLeft
    {𝒮 𝒮' 𝒮'' : CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U)} (f : 𝒮 ⟶ 𝒮')
    {g h : 𝒮' ⟶ 𝒮''} (η : g ⟶ h) :
    constructionHom₂Equiv U (f ≫ g) (f ≫ h) (CatFibered.whiskerLeft f η) =
      CatFibered.whiskerLeft (constructionHomEquiv U 𝒮 𝒮' f).val
        (constructionHom₂Equiv U g h η) :=
  rfl

/-- Construction A preserves right whiskering. -/
@[simp]
lemma constructionHom₂Equiv_whiskerRight
    {𝒮 𝒮' 𝒮'' : CatFibered.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U)} {f g : 𝒮 ⟶ 𝒮'} (η : f ⟶ g)
    (h : 𝒮' ⟶ 𝒮'') :
    constructionHom₂Equiv U (f ≫ h) (g ≫ h) (CatFibered.whiskerRight η h) =
      CatFibered.whiskerRight (constructionHom₂Equiv U f g η)
        (constructionHomEquiv U 𝒮' 𝒮'' h).val :=
  rfl

/-- A morphism of `𝒞/U` lying over an identity of `𝒞` is the comparison `eqToHom` between its
source and target. -/
lemma eq_eqToHom_of_isHomLift_id {A B : Over U} (φ : A ⟶ B) {V : 𝒞}
    (h : (Over.forget U).IsHomLift (𝟙 V) φ) (hAB : A = B) : φ = eqToHom hAB := by
  refine Over.hom_ext_of_isHomLift (𝟙 V) h ?_
  subst hAB
  have hV : A.left = V := IsHomLift.domain_eq (Over.forget U) (𝟙 V) φ
  subst hV
  simpa using IsHomLift.id (p := Over.forget U) (a := A) rfl

/-- **The triangle condition on a 2-morphism of the right-hand 2-category of Stacks 04WV is
automatic.** For a 2-morphism `η` of fibred categories over `𝒞` between two 1-morphisms
`f, g : X ⟶ Y` that lie over `𝒞/U`, the image under the structure morphism `p_Y : 𝒴 ⟶ 𝒞/U` of
every component of `η` is the comparison `eqToHom`, i.e. `p_Y ∘ η` is an identity 2-morphism. -/
lemma map_app_eq_eqToHom {X Y : CatFiberedPair U} (f g : CatFiberedPairHom U X Y)
    (η : CatFiberedPairHom₂ U f g) (x : X.1.val.obj)
    (hx : Y.2.hom.toFunctor.obj (f.val.hom.obj x) = Y.2.hom.toFunctor.obj (g.val.hom.obj x)) :
    Y.2.hom.toFunctor.map (η.hom.toNatTrans.app x) = eqToHom hx := by
  have hY : Y.2.hom.toFunctor ⋙ Over.forget U = Y.1.val.p := Y.2.hom.w
  have hlift : (Y.2.hom.toFunctor ⋙ Over.forget U).IsHomLift (𝟙 (X.1.val.p.obj x))
      (η.hom.toNatTrans.app x) := by
    rw [hY]
    exact η.hom.isHomLift' x
  exact eq_eqToHom_of_isHomLift_id U _ (V := X.1.val.p.obj x)
    (Functor.isHomLift_map_comp Y.2.hom.toFunctor (Over.forget U) (η.hom.toNatTrans.app x)
      (𝟙 (X.1.val.p.obj x)) hlift) hx

/-! ### Construction A as a functor of 2-categories of stacks

Construction A takes a stack over `(𝒞/U, J.over U)` to a stack over `(𝒞, J)` together with a
1-morphism to `𝒞/U`, and it is a bijection on 1-morphisms and on 2-morphisms. -/

section Stacks

variable (J : GrothendieckTopology 𝒞) (hU : Presheaf.IsSheaf J (yoneda.obj U))

/-- `𝒞/U` as an object of the 2-category of stacks over `(𝒞, J)` (Stacks 02ZG), when `h_U` is a
sheaf. -/
def basedStack : BasedStack.{v₁, v₁, u₁, max u₁ v₁} 𝒞 J :=
  ⟨{ obj := Over U, category := inferInstance, p := Over.forget U },
    (Over.isStack_forget_iff_isSheaf J).2 hU⟩

/-- An object of the right-hand 2-category of Stacks 04WV: a pair `(𝒯, p)` consisting of a stack
`𝒯` over `(𝒞, J)` and a 1-morphism `p : 𝒯 ⟶ 𝒞/U` of stacks over `𝒞`. -/
abbrev StackPair := Σ 𝒯 : BasedStack.{v₁, v₁, u₁, max u₁ v₁} 𝒞 J, (𝒯 ⟶ basedStack U J hU)

/-- A 1-morphism of the right-hand 2-category of Stacks 04WV: a 1-morphism of stacks over `𝒞`
commuting strictly with the two structure morphisms to `𝒞/U`. -/
abbrev StackPairHom (X Y : StackPair U J hU) := { f : X.1 ⟶ Y.1 // f ≫ Y.2 = X.2 }

/-- A 2-morphism of the right-hand 2-category of Stacks 04WV: a 2-morphism of stacks over `𝒞`
between the underlying 1-morphisms. -/
abbrev StackPairHom₂ {X Y : StackPair U J hU} (f g : StackPairHom U J hU X Y) := f.val ⟶ g.val

/-- The identity 1-morphism of the right-hand 2-category of Stacks 04WV. -/
def StackPairHom.id (X : StackPair U J hU) : StackPairHom U J hU X X :=
  ⟨𝟙 X.1, Category.id_comp _⟩

/-- Composition of 1-morphisms in the right-hand 2-category of Stacks 04WV. -/
def StackPairHom.comp {X Y Z : StackPair U J hU} (f : StackPairHom U J hU X Y)
    (g : StackPairHom U J hU Y Z) : StackPairHom U J hU X Z :=
  ⟨f.val ≫ g.val, by rw [Category.assoc, g.2, f.2]⟩

/-- **Construction A of Stacks 04WV**, on objects: a stack `p : 𝒮 ⥤ 𝒞/U` over `𝒞/U` is sent to
`j_! p = p ⋙ j_U`, which is a stack over `𝒞`, together with `p` itself as a 1-morphism
`j_! 𝒮 ⟶ 𝒞/U` of stacks over `𝒞`. -/
def stackConstructionA (𝒮 : BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U)) :
    StackPair U J hU :=
  ⟨⟨{ obj := 𝒮.toBasedCategory.obj, category := 𝒮.toBasedCategory.category,
        p := 𝒮.toBasedCategory.p ⋙ Over.forget U },
      Functor.isStack_comp_forget 𝒮.toBasedCategory.p hU 𝒮.isStack⟩,
    ⟨{ toFunctor := 𝒮.toBasedCategory.p, w := rfl },
      { comp_eq := rfl
        map_isStronglyCartesian := by
          intro R T f a b φ h
          have := Functor.isHomLift_map_comp 𝒮.toBasedCategory.p (Over.forget U) φ f h.toIsHomLift
          exact Over.isStronglyCartesian_forget f (𝒮.toBasedCategory.p.map φ) }⟩⟩

/-- **Construction A is bijective on 1-morphisms**, and is the identity on the underlying
functor. -/
@[stacks 04WV]
def stackConstructionHomEquiv
    (𝒮 𝒮' : BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U)) :
    (𝒮 ⟶ 𝒮') ≃
      StackPairHom U J hU (stackConstructionA U J hU 𝒮) (stackConstructionA U J hU 𝒮') where
  toFun f :=
    ⟨⟨{ toFunctor := f.hom.toFunctor,
          w := congrArg (fun H : 𝒮.toBasedCategory.obj ⥤ Over U ↦ H ⋙ Over.forget U) f.hom.w },
        (Functor.isFibredOneMorphism_comp_forget_iff 𝒮.toBasedCategory.p 𝒮'.toBasedCategory.p
          f.hom.toFunctor f.hom.w).1 f.isFibredOneMorphism⟩,
      BasedStack.Hom.ext_hom (BasedCategory.BasedFunctor.ext' f.hom.w)⟩
  invFun f :=
    ⟨{ toFunctor := f.val.hom.toFunctor,
        w := congrArg (fun h ↦ (BasedStack.Hom.hom h).toFunctor) f.2 },
      (Functor.isFibredOneMorphism_comp_forget_iff 𝒮.toBasedCategory.p 𝒮'.toBasedCategory.p
        f.val.hom.toFunctor (congrArg (fun h ↦ (BasedStack.Hom.hom h).toFunctor) f.2)).2
          f.val.isFibredOneMorphism⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Construction A preserves the identity 1-morphism. -/
@[simp]
lemma stackConstructionHomEquiv_id
    (𝒮 : BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U)) :
    stackConstructionHomEquiv U J hU 𝒮 𝒮 (𝟙 𝒮) =
      StackPairHom.id U J hU (stackConstructionA U J hU 𝒮) :=
  rfl

/-- Construction A preserves composition of 1-morphisms. -/
@[simp]
lemma stackConstructionHomEquiv_comp
    {𝒮 𝒮' 𝒮'' : BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U)} (f : 𝒮 ⟶ 𝒮')
    (g : 𝒮' ⟶ 𝒮'') :
    stackConstructionHomEquiv U J hU 𝒮 𝒮'' (f ≫ g) =
      StackPairHom.comp U J hU (stackConstructionHomEquiv U J hU 𝒮 𝒮' f)
        (stackConstructionHomEquiv U J hU 𝒮' 𝒮'' g) :=
  rfl

/-- **Construction A is bijective on 2-morphisms**, and is the identity on the underlying morphism
of functors. -/
@[stacks 04WV]
def stackConstructionHom₂Equiv
    {𝒮 𝒮' : BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U)} (f g : 𝒮 ⟶ 𝒮') :
    (f ⟶ g) ≃ StackPairHom₂ U J hU (stackConstructionHomEquiv U J hU 𝒮 𝒮' f)
      (stackConstructionHomEquiv U J hU 𝒮 𝒮' g) where
  toFun η :=
    { toNatTrans := η.toNatTrans,
      isHomLift' := fun a ↦
        (Functor.isHomLift_id_comp_forget_iff 𝒮'.toBasedCategory.p
          (BasedFunctor.w_obj g.hom a) _).1 (η.isHomLift' a) }
  invFun η :=
    { toNatTrans := η.toNatTrans,
      isHomLift' := fun a ↦
        (Functor.isHomLift_id_comp_forget_iff 𝒮'.toBasedCategory.p
          (BasedFunctor.w_obj g.hom a) _).2 (η.isHomLift' a) }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Construction A preserves identity 2-morphisms. -/
@[simp]
lemma stackConstructionHom₂Equiv_id
    {𝒮 𝒮' : BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U)} (f : 𝒮 ⟶ 𝒮') :
    stackConstructionHom₂Equiv U J hU f f (𝟙 f) = 𝟙 _ :=
  rfl

/-- Construction A preserves vertical composition of 2-morphisms. -/
@[simp]
lemma stackConstructionHom₂Equiv_comp
    {𝒮 𝒮' : BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U)} {f g h : 𝒮 ⟶ 𝒮'}
    (η : f ⟶ g) (θ : g ⟶ h) :
    stackConstructionHom₂Equiv U J hU f h (η ≫ θ) =
      stackConstructionHom₂Equiv U J hU f g η ≫ stackConstructionHom₂Equiv U J hU g h θ :=
  rfl

/-- Construction A preserves left whiskering. -/
@[simp]
lemma stackConstructionHom₂Equiv_whiskerLeft
    {𝒮 𝒮' 𝒮'' : BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U)} (f : 𝒮 ⟶ 𝒮')
    {g h : 𝒮' ⟶ 𝒮''} (η : g ⟶ h) :
    stackConstructionHom₂Equiv U J hU (f ≫ g) (f ≫ h) (BasedStack.whiskerLeft f η) =
      BasedStack.whiskerLeft (stackConstructionHomEquiv U J hU 𝒮 𝒮' f).val
        (stackConstructionHom₂Equiv U J hU g h η) :=
  rfl

/-- Construction A preserves right whiskering. -/
@[simp]
lemma stackConstructionHom₂Equiv_whiskerRight
    {𝒮 𝒮' 𝒮'' : BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U)} {f g : 𝒮 ⟶ 𝒮'}
    (η : f ⟶ g) (h : 𝒮' ⟶ 𝒮'') :
    stackConstructionHom₂Equiv U J hU (f ≫ h) (g ≫ h) (BasedStack.whiskerRight η h) =
      BasedStack.whiskerRight (stackConstructionHom₂Equiv U J hU f g η)
        (stackConstructionHomEquiv U J hU 𝒮' 𝒮'' h).val :=
  rfl

end Stacks

end Over

end CategoryTheory
