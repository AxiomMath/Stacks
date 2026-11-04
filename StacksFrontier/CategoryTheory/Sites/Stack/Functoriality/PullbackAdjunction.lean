module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackFibred
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.Pushforward

/-! # The pullback of a fibred category is adjoint to the pushforward

Let `u : 𝒞 ⥤ 𝒟` be a functor, let `p : 𝒮 ⥤ 𝒞` be a category over `𝒞` and let `q : 𝒯 ⥤ 𝒟` be a
category over `𝒟`. Two constructions move a category over one base to a category over the other
along `u`. The *pushforward* `u^p 𝒯` (Stacks 04WB) is the strict pullback of `u` and `q`, whose
objects are the pairs `(U, y)` with `q(y) = u(U)` and whose morphisms are the pairs `(a, β)` with
`q(β) = u(a)`, viewed over `𝒞` by `(U, y) ↦ U`; it is a fibred category as soon as `q` is. The
*pullback* `u_p 𝒮` (Stacks 04WG) is the localization of the comma category
`u_pp 𝒮 = Comma (𝟭 𝒟) (p ⋙ u)` of triples `(U, φ : V ⟶ u(U), x ∈ 𝒮_U)` at the right multiplicative
system `R` of morphisms with identity `𝒟`-component and strongly cartesian `𝒮`-component
(Stacks 04WF), viewed over `𝒟` by the extension `p_p` of `(U, φ : V ⟶ u(U), x) ↦ V`; it is a fibred
category as soon as `p` is, `𝒞` has nonempty finite limits and `u` commutes with nonempty finite
limits.

Stacks 04WI says that the two constructions are adjoint on the nose, at the level of the
2-categories of fibred categories (Stacks 02XP): under those hypotheses the morphism category
`Mor_{Fib/𝒞}(𝒮, u^p 𝒯)` is equivalent to the morphism category `Mor_{Fib/𝒟}(u_p 𝒮, 𝒯)`.

## Main results

* `CategoryTheory.equivalenceIsFibredOneMorphismStrictPullbackPullbackLocalization`: the canonical
  equivalence of the two morphism categories (Stacks 04WI).

## Implementation notes

A morphism category `Mor_{Fib/ℰ}(𝒳, 𝒴)` of Stacks 02XP has as objects the functors `𝒳 ⥤ 𝒴` over
`ℰ` carrying strongly cartesian morphisms to strongly cartesian morphisms, and as morphisms the
morphisms of functors all of whose components lie over an identity of `ℰ`. The morphisms are
therefore exactly Mathlib's `CategoryTheory.BasedNatTrans`, and the objects are exactly the based
functors satisfying `CategoryTheory.Functor.IsFibredOneMorphism`, so the morphism category is the
full subcategory of Mathlib's category of based functors cut out by that predicate. That is the
spelling used here, as in the statement of Stacks 04WI: a `CategoryTheory.Bicategory` has a single
pair of universes for the objects and morphisms of all of its objects, whereas `𝒮` and `u^p 𝒯` —
and `u_p 𝒮` and `𝒯` — live in different universes for independent `𝒞, 𝒟, 𝒮, 𝒯`, so the tree's
2-category `CategoryTheory.CatFibered` could not state the result at this generality.

The equivalence is produced by exhibiting *one* of its two directions and proving that functor
fully faithful and essentially surjective. The direction chosen is the easy one, restriction along
the unit

`ι : 𝒮 ⥤ u_pp 𝒮`, `x ↦ (p(x), id_{u(p(x))}, x)`,

which sends a 1-morphism `G : u_p 𝒮 ⟶ 𝒯` over `𝒟` to the 1-morphism `𝒮 ⟶ u^p 𝒯` over `𝒞` given on
`x` by `(p(x), G(ι(x)))`; this is the functor `A` of the source's proof, here
`CategoryTheory.restrictAlongPullbackUnit`. The source's `B`, the extension of
`(U, φ : V ⟶ u(U), x) ↦ φ^* pr(H(x))` over the localization, is here
`CategoryTheory.PullbackAdjunction.leftToRight`; it is used only to witness essential
surjectivity, so its functoriality in `H` — and the two natural isomorphisms exhibiting `A` and `B`
as quasi-inverse, which the source omits — are replaced by the fullness and faithfulness of `A`.

The two properties of `A` rest on one observation, which is also what replaces the
characterization of *all* strongly cartesian morphisms of `u_p 𝒮` that the source uses and that
Stacks 04WG omits: every object `Z = (V, φ : V ⟶ u(U), x)` of `u_pp 𝒮` carries a canonical
morphism `c_Z = (φ, id_x) : Z ⟶ ι(x)`, whose image in `u_p 𝒮` is strongly cartesian over `φ` by
the case `α = id` of Stacks 04WG (`CategoryTheory.Comma.isStronglyCartesian_Q_baseChangeHom`), and
which is natural in the sense that `f ≫ c_{Z'} = c_Z ≫ ι(f_𝒮)` for every `f : Z ⟶ Z'`. A based
morphism of functors on `u_p 𝒮` is therefore determined by, and can be built from, its restriction
along `ι`.

Hypothesis (4) of the source, that `u` commutes with nonempty finite limits, is spelled as in
Stacks 04WF: the tree has no class for it, so it is `Limits.PreservesLimitsOfShape J u` for every
small finite nonempty shape `J`, the same quantification `HasNonemptyFiniteLimits` uses.

Universes. `𝒞, 𝒟, 𝒮, 𝒯` carry four independent universe pairs, as in Stacks 04WF and 04WG. None
needs bounding and none is bounded: `CategoryTheory.Equivalence` relates two categories in
arbitrary independent universes, `Functor.IsFibered` and `Functor.IsFibredOneMorphism` relate no
source and target universes, and `CategoryTheory.BasedFunctor` takes its two based categories in
independent universe pairs. The only data produced are morphisms and objects of the four given
categories.

## References

* [StacksProject 04WI](https://stacks.math.columbia.edu/tag/04WI)
-/


@[expose] public section

set_option backward.isDefEq.respectTransparency false
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

/-! ### Generalities on 1-morphisms of fibred categories -/

namespace PullbackAdjunction

section General

variable {ℰ : Type u₁} [Category.{v₁} ℰ] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃}
  [Category.{v₃} 𝒴]

/-- `IsStronglyCartesian` of a value of a functor only depends on the functor. -/
lemma isStronglyCartesian_map_of_functor_eq (T : 𝒴 ⥤ ℰ) {F₁ F₂ : 𝒳 ⥤ 𝒴} (e : F₁ = F₂) {a b : 𝒳}
    (φ : a ⟶ b) {R S : ℰ} (f : R ⟶ S) (h : T.IsStronglyCartesian f (F₂.map φ)) :
    T.IsStronglyCartesian f (F₁.map φ) := by
  subst e; exact h

/-- Appending an `eqToHom` to the base morphism preserves `IsStronglyCartesian`. -/
lemma isStronglyCartesian_comp_eqToHom {P : 𝒳 ⥤ ℰ} {R S S' : ℰ} {a b : 𝒳} (hS : S = S') (f : R ⟶ S)
    (φ : a ⟶ b) (h : P.IsStronglyCartesian f φ) : P.IsStronglyCartesian (f ≫ eqToHom hS) φ := by
  subst hS; simpa using h

/-- Precomposing a strongly cartesian morphism with one which is strongly cartesian over an
identity does not change the base morphism it is strongly cartesian over. -/
lemma isStronglyCartesian_id_comp {P : 𝒴 ⥤ ℰ} {R S : ℰ} {a b c : 𝒴} {g : R ⟶ S} {φ : a ⟶ b}
    {ψ : b ⟶ c} (hφ : P.IsStronglyCartesian (𝟙 R) φ) (hψ : P.IsStronglyCartesian g ψ) :
    P.IsStronglyCartesian g (φ ≫ ψ) := by
  have := hφ
  have := hψ
  simpa using Functor.IsStronglyCartesian.comp (p := P) (f := 𝟙 R) (g := g) (φ := φ) (ψ := ψ)

/-- Two strongly cartesian morphisms over the same base morphism differ by an isomorphism of
domains lying over an identity. -/
private lemma exists_iso_isHomLift_id_comp_eq {P : 𝒳 ⥤ ℰ} {R S : ℰ} {f : R ⟶ S} {a a' b : 𝒳}
    {g : a' ⟶ b} {φ : a ⟶ b} (hg : P.IsStronglyCartesian f g) (hφ : P.IsStronglyCartesian f φ) :
    ∃ e : a ≅ a', P.IsHomLift (𝟙 R) e.hom ∧ e.hom ≫ g = φ := by
  have hrefl : f = (Iso.refl R).hom ≫ f := by simp
  exact ⟨Functor.IsStronglyCartesian.domainIsoOfBaseIso P hrefl g φ,
    by simpa using Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift P hrefl g φ,
    by simp⟩

/-- A functor strictly over the base which carries **one** strongly cartesian lift of every
morphism of the base into every object to a strongly cartesian morphism is a 1-morphism of
fibred categories: any other strongly cartesian lift differs from that one by an isomorphism
lying over an identity, and an isomorphism lying over an identity is strongly cartesian. -/
lemma isFibredOneMorphism_of_exists_lift (P : 𝒳 ⥤ ℰ) (T : 𝒴 ⥤ ℰ) (G : 𝒳 ⥤ 𝒴) (hG : G ⋙ T = P)
    (h :
      ∀ (b : 𝒳) (V : ℰ) (β : V ⟶ P.obj b),
        ∃ (a : 𝒳) (g : a ⟶ b), P.IsStronglyCartesian β g ∧ T.IsStronglyCartesian β (G.map g)) :
    Functor.IsFibredOneMorphism P T G
    where
  comp_eq := hG
  map_isStronglyCartesian := by
    intro R S f a b φ hφ
    have := hφ
    have hb : P.obj b = S := IsHomLift.codomain_eq P f φ
    obtain ⟨a', g, hg, hGg⟩ := h b R (f ≫ eqToHom hb.symm)
    have := hg
    have := hGg
    have hφ' : P.IsStronglyCartesian (f ≫ eqToHom hb.symm) φ :=
      isStronglyCartesian_comp_eqToHom hb.symm f φ hφ
    obtain ⟨e, hlift, hfac⟩ := exists_iso_isHomLift_id_comp_eq hg hφ'
    have : T.IsHomLift (𝟙 R) (G.map e.hom) := Functor.isHomLift_map_of_comp_eq hG _ _
    have : IsIso (G.map e.hom) := inferInstance
    have : T.IsStronglyCartesian (𝟙 R) (G.map e.hom) := Functor.IsStronglyCartesian.of_isIso T _ _
    have hcomp :=
      Functor.IsStronglyCartesian.comp (p := T) (f := 𝟙 R) (g := f ≫ eqToHom hb.symm) (φ :=
        G.map e.hom) (ψ := G.map g)
    refine Functor.IsStronglyCartesian.of_comp_eqToHom hb.symm f (G.map φ) ?_
    rw [← hfac, G.map_comp]
    simpa using hcomp

end General

end PullbackAdjunction

/-! ### The strict pullback: the projection to `𝒯`, and functors into it -/

namespace StrictPullback

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] {𝒮 : Type u₃}
  [Category.{v₃} 𝒮] {𝒯 : Type u₄} [Category.{v₄} 𝒯] {u : 𝒞 ⥤ 𝒟} {q : 𝒯 ⥤ 𝒟}

/-- The projection `pr : u^p 𝒯 ⥤ 𝒯`, `(U, y) ↦ y` and `(a, β) ↦ β`. -/
def pr (u : 𝒞 ⥤ 𝒟) (q : 𝒯 ⥤ 𝒟) : StrictPullback u q ⥤ 𝒯 where
  obj X := X.fib
  map f := f.fib

/-- The projection `pr` sends `(U, y)` to `y`. -/
@[simp]
lemma pr_obj (X : StrictPullback u q) : (pr u q).obj X = X.fib :=
  rfl

/-- The projection `pr` sends `(a, β)` to `β`. -/
@[simp]
lemma pr_map {X Y : StrictPullback u q} (f : X ⟶ Y) : (pr u q).map f = f.fib :=
  rfl

/-- The defining square of the strict pullback: `pr ⋙ q = structureFunctor ⋙ u`. -/
lemma pr_comp_eq (u : 𝒞 ⥤ 𝒟) (q : 𝒯 ⥤ 𝒟) : pr u q ⋙ q = StrictPullback.structureFunctor u q ⋙ u :=
  Functor.ext (fun X => X.over) (fun _ _ f => f.over)

/-- The `𝒯`-component of a morphism of `u^p 𝒯` whose `𝒞`-component is the canonical
`eqToHom` — in particular an identity — lies over an identity. -/
lemma isHomLift_fib_of_base_id {X Y : StrictPullback u q} (f : X ⟶ Y) (h : X.base = Y.base)
    (hb : f.base = eqToHom h) : q.IsHomLift (𝟙 (u.obj X.base)) f.fib := by
  refine
    IsHomLift.of_fac' q (𝟙 (u.obj X.base)) f.fib X.over (Y.over.trans (congrArg u.obj h).symm) ?_
  rw [f.over, hb, eqToHom_map]
  simp

/-- A morphism of `u^p 𝒯` both of whose components are isomorphisms is an isomorphism: the
componentwise inverse again satisfies the compatibility `q β = u a`, because inverting the
defining equation only turns the `eqToHom`s around. -/
lemma isIso_of_isIso_base_fib {X Y : StrictPullback u q} (f : X ⟶ Y) [IsIso f.base] [IsIso f.fib] :
    IsIso f := by
  have hover : q.map (inv f.fib) = eqToHom Y.over ≫ u.map (inv f.base) ≫ eqToHom X.over.symm := by
    rw [Functor.map_inv]
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [f.over]
    simp
  refine ⟨⟨⟨inv f.base, inv f.fib, hover⟩, ?_, ?_⟩⟩
  · apply Hom.ext <;> simp
  · apply Hom.ext <;> simp

/-- The universal property of the strict pullback: a functor `F : 𝒮 ⥤ 𝒯` and a functor
`P : 𝒮 ⥤ 𝒞` with `F ⋙ q = P ⋙ u` induce a functor `𝒮 ⥤ u^p 𝒯` strictly over `P`. -/
def liftFib (P : 𝒮 ⥤ 𝒞) (F : 𝒮 ⥤ 𝒯) (h : F ⋙ q = P ⋙ u) : 𝒮 ⥤ StrictPullback u q where
  obj x := ⟨P.obj x, F.obj x, Functor.congr_obj h x⟩
  map f := ⟨P.map f, F.map f, Functor.congr_hom h f⟩
  map_id x := by apply StrictPullback.Hom.ext <;> simp
  map_comp f g := by apply StrictPullback.Hom.ext <;> simp

/-- The `𝒞`-component of `liftFib P F h` at `x` is `P(x)`. -/
@[simp]
lemma liftFib_obj_base (P : 𝒮 ⥤ 𝒞) (F : 𝒮 ⥤ 𝒯) (h : F ⋙ q = P ⋙ u) (x : 𝒮) :
    ((liftFib P F h).obj x).base = P.obj x :=
  rfl

/-- The `𝒯`-component of `liftFib P F h` at `x` is `F(x)`. -/
@[simp]
lemma liftFib_obj_fib (P : 𝒮 ⥤ 𝒞) (F : 𝒮 ⥤ 𝒯) (h : F ⋙ q = P ⋙ u) (x : 𝒮) :
    ((liftFib P F h).obj x).fib = F.obj x :=
  rfl

/-- The `𝒞`-component of `liftFib P F h` at a morphism `f` is `P(f)`. -/
@[simp]
lemma liftFib_map_base (P : 𝒮 ⥤ 𝒞) (F : 𝒮 ⥤ 𝒯) (h : F ⋙ q = P ⋙ u) {x y : 𝒮} (f : x ⟶ y) :
    ((liftFib P F h).map f).base = P.map f :=
  rfl

/-- The `𝒯`-component of `liftFib P F h` at a morphism `f` is `F(f)`. -/
@[simp]
lemma liftFib_map_fib (P : 𝒮 ⥤ 𝒞) (F : 𝒮 ⥤ 𝒯) (h : F ⋙ q = P ⋙ u) {x y : 𝒮} (f : x ⟶ y) :
    ((liftFib P F h).map f).fib = F.map f :=
  rfl

/-- The functor `liftFib P F h` lies strictly over `P`. -/
lemma liftFib_comp_structureFunctor (P : 𝒮 ⥤ 𝒞) (F : 𝒮 ⥤ 𝒯) (h : F ⋙ q = P ⋙ u) :
    liftFib P F h ⋙ StrictPullback.structureFunctor u q = P :=
  rfl

/-- `liftFib` depends on `F` only through `F` itself, so equal functors give equal lifts. -/
lemma liftFib_congr (P : 𝒮 ⥤ 𝒞) {F₁ F₂ : 𝒮 ⥤ 𝒯} (e : F₁ = F₂) (h₁ : F₁ ⋙ q = P ⋙ u)
    (h₂ : F₂ ⋙ q = P ⋙ u) : liftFib P F₁ h₁ = liftFib P F₂ h₂ := by
  subst e; rfl

/-- A morphism of functors into `𝒯` all of whose components lie over an identity induces a
morphism of the corresponding functors into `u^p 𝒯`. -/
def liftFibNatTrans (P : 𝒮 ⥤ 𝒞) {F₁ F₂ : 𝒮 ⥤ 𝒯} (h₁ : F₁ ⋙ q = P ⋙ u) (h₂ : F₂ ⋙ q = P ⋙ u)
    (τ : F₁ ⟶ F₂) (hτ : ∀ x, q.IsHomLift (𝟙 (u.obj (P.obj x))) (τ.app x)) :
    liftFib P F₁ h₁ ⟶ liftFib P F₂ h₂
    where
  app x :=
    ⟨𝟙 (P.obj x), τ.app x, by
      have := hτ x
      have hfac := IsHomLift.fac' q (𝟙 (u.obj (P.obj x))) (τ.app x)
      simp only [Category.id_comp] at hfac ⊢
      simp [hfac]⟩
  naturality _ _ f := by apply StrictPullback.Hom.ext <;> simp

/-- The `𝒯`-component of `liftFibNatTrans` at `x` is `τ.app x`. -/
@[simp]
lemma liftFibNatTrans_app_fib (P : 𝒮 ⥤ 𝒞) {F₁ F₂ : 𝒮 ⥤ 𝒯} (h₁ : F₁ ⋙ q = P ⋙ u)
    (h₂ : F₂ ⋙ q = P ⋙ u) (τ : F₁ ⟶ F₂) (hτ : ∀ x, q.IsHomLift (𝟙 (u.obj (P.obj x))) (τ.app x))
    (x : 𝒮) : ((liftFibNatTrans P h₁ h₂ τ hτ).app x).fib = τ.app x :=
  rfl

/-- The `𝒞`-component of `liftFibNatTrans` at `x` is the identity of `P(x)`. -/
@[simp]
lemma liftFibNatTrans_app_base (P : 𝒮 ⥤ 𝒞) {F₁ F₂ : 𝒮 ⥤ 𝒯} (h₁ : F₁ ⋙ q = P ⋙ u)
    (h₂ : F₂ ⋙ q = P ⋙ u) (τ : F₁ ⟶ F₂) (hτ : ∀ x, q.IsHomLift (𝟙 (u.obj (P.obj x))) (τ.app x))
    (x : 𝒮) : ((liftFibNatTrans P h₁ h₂ τ hτ).app x).base = 𝟙 (P.obj x) :=
  rfl

/-- The converse of `CategoryTheory.StrictPullback.isStronglyCartesian_of_fib`: in the
pushforward of a fibred category, the `𝒯`-component of a strongly cartesian morphism is
strongly cartesian. -/
lemma isStronglyCartesian_fib_over [q.IsFibered] {X Y : StrictPullback u q} (f : X ⟶ Y)
    (hf : (StrictPullback.structureFunctor u q).IsStronglyCartesian f.base f) :
    q.IsStronglyCartesian (eqToHom X.over ≫ u.map f.base ≫ eqToHom Y.over.symm) f.fib := by
  have := hf
  obtain ⟨y, β, hβc⟩ :=
    Functor.IsPreFibered.exists_isCartesian' (p := q) (a := Y.fib)
      (u.map f.base ≫ eqToHom Y.over.symm)
  have := hβc
  have hβs : q.IsStronglyCartesian (u.map f.base ≫ eqToHom Y.over.symm) β := inferInstance
  have hy : q.obj y = u.obj X.base := IsHomLift.domain_eq q (u.map f.base ≫ eqToHom Y.over.symm) β
  have hover : q.map β = eqToHom hy ≫ u.map f.base ≫ eqToHom Y.over.symm := by
    rw [IsHomLift.fac' q (u.map f.base ≫ eqToHom Y.over.symm) β]; simp
  set X₀ : StrictPullback u q := ⟨X.base, y, hy⟩ with hX₀
  set f₀ : X₀ ⟶ Y := ⟨f.base, β, hover⟩ with hf₀
  have hf₀s : (StrictPullback.structureFunctor u q).IsStronglyCartesian f.base f₀ := by
    have : (StrictPullback.structureFunctor u q).IsStronglyCartesian f₀.base f₀ :=
      StrictPullback.isStronglyCartesian_of_fib f₀
        (Functor.IsStronglyCartesian.eqToHom_comp hy _ β hβs)
    exact this
  obtain ⟨e, hel, hefac⟩ := PullbackAdjunction.exists_iso_isHomLift_id_comp_eq hf₀s hf
  have hebase : e.hom.base = 𝟙 X.base :=
    StrictPullback.base_eq (X := X) (Y := X₀) (𝟙 X.base) e.hom
  have hiso : IsIso e.hom.fib := by
    have : IsIso ((pr u q).map e.hom) := inferInstance
    simpa using this
  have hlift : q.IsHomLift (𝟙 (u.obj X.base)) e.hom.fib := by
    refine IsHomLift.of_fac' q _ _ X.over hy ?_
    rw [e.hom.over, hebase]
    simp
  have h1 : q.IsStronglyCartesian (𝟙 (u.obj X.base)) e.hom.fib :=
    Functor.IsStronglyCartesian.of_isIso q _ _
  have hcomp :
    q.IsStronglyCartesian (𝟙 (u.obj X.base) ≫ u.map f.base ≫ eqToHom Y.over.symm)
      (e.hom.fib ≫ β) :=
    Functor.IsStronglyCartesian.comp q
  have hfib : f.fib = e.hom.fib ≫ β := by
    rw [← hefac]; rfl
  rw [hfib]
  refine Functor.IsStronglyCartesian.eqToHom_comp X.over _ _ ?_
  simpa using hcomp

end StrictPullback

/-! ### The unit `ι : 𝒮 ⥤ u_pp 𝒮` -/

namespace Comma

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] {𝒮 : Type u₃}
  [Category.{v₃} 𝒮]
variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)

/-- The unit `ι : 𝒮 ⥤ u_pp 𝒮`, `x ↦ (U, id_{u(U)}, x)` with `U = p(x)`, and
`α ↦ (p(α), u(p(α)), α)`. -/
def pullbackUnit : 𝒮 ⥤ Comma (𝟭 𝒟) (p ⋙ u) where
  obj x := Comma.mk (u.obj (p.obj x)) x (𝟙 (u.obj (p.obj x)))
  map α := { left := u.map (p.map α), right := α, w := by simp }
  map_id x := Comma.hom_ext _ _ (by simp) (by simp)
  map_comp f g := Comma.hom_ext _ _ (by simp) (by simp)

/-- The `𝒟`-component of `ι(x)` is `u(p(x))`. -/
@[simp]
lemma pullbackUnit_obj_left (x : 𝒮) : ((pullbackUnit p u).obj x).left = u.obj (p.obj x) :=
  rfl

/-- The `𝒮`-component of `ι(x)` is `x`. -/
@[simp]
lemma pullbackUnit_obj_right (x : 𝒮) : ((pullbackUnit p u).obj x).right = x :=
  rfl

/-- The structure morphism of `ι(x)` is the identity of `u(p(x))`. -/
@[simp]
lemma pullbackUnit_obj_hom (x : 𝒮) : ((pullbackUnit p u).obj x).hom = 𝟙 (u.obj (p.obj x)) :=
  rfl

/-- The `𝒟`-component of `ι(α)` is `u(p(α))`. -/
@[simp]
lemma pullbackUnit_map_left {x y : 𝒮} (α : x ⟶ y) :
    ((pullbackUnit p u).map α).left = u.map (p.map α) :=
  rfl

/-- The `𝒮`-component of `ι(α)` is `α`. -/
@[simp]
lemma pullbackUnit_map_right {x y : 𝒮} (α : x ⟶ y) : ((pullbackUnit p u).map α).right = α :=
  rfl

/-- The unit is a functor over `𝒟`: it lifts `p ⋙ u` along `p_pp`. -/
lemma pullbackUnit_comp_fst : pullbackUnit p u ⋙ Comma.fst (𝟭 𝒟) (p ⋙ u) = p ⋙ u :=
  rfl

/-- The canonical morphism `c_Z = (φ, id_x) : Z ⟶ ι(x)` out of `Z = (U, φ : V ⟶ u(U), x)`. -/
def toPullbackUnit (Z : Comma (𝟭 𝒟) (p ⋙ u)) : Z ⟶ (pullbackUnit p u).obj Z.right where
  left := Z.hom
  right := 𝟙 Z.right
  w := by simp

/-- The `𝒟`-component of `c_Z` is the structure morphism `φ` of `Z`. -/
@[simp]
lemma toPullbackUnit_left (Z : Comma (𝟭 𝒟) (p ⋙ u)) : (toPullbackUnit p u Z).left = Z.hom :=
  rfl

/-- The `𝒮`-component of `c_Z` is the identity of `x`. -/
@[simp]
lemma toPullbackUnit_right (Z : Comma (𝟭 𝒟) (p ⋙ u)) : (toPullbackUnit p u Z).right = 𝟙 Z.right :=
  rfl

/-- `c` is natural: `f ≫ c_{Z'} = c_Z ≫ ι(f_𝒮)`. This is exactly the commutativity of the
square defining a morphism of `u_pp 𝒮`. -/
lemma comp_toPullbackUnit {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    f ≫ toPullbackUnit p u Z' = toPullbackUnit p u Z ≫ (pullbackUnit p u).map f.right :=
  Comma.hom_ext _ _ (by simpa using f.w) (by simp)

/-- At an object in the image of the unit, `c` is the identity. -/
lemma toPullbackUnit_pullbackUnit (x : 𝒮) :
    toPullbackUnit p u ((pullbackUnit p u).obj x) = 𝟙 ((pullbackUnit p u).obj x) :=
  Comma.hom_ext _ _ (by simp) (by simp)

/-- The `𝒟`-component of an `eqToHom` of `u_pp 𝒮`. -/
lemma eqToHom_left_comma {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (h : Z = Z') :
    (eqToHom h).left = eqToHom (congrArg Comma.left h) := by
  subst h; simp

/-- The `𝒮`-component of an `eqToHom` of `u_pp 𝒮`. -/
lemma eqToHom_right_comma {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (h : Z = Z') :
    (eqToHom h).right = eqToHom (congrArg Comma.right h) := by
  subst h; simp

section

variable [p.IsFibered] [HasNonemptyFiniteLimits 𝒞]

omit [p.IsFibered] [HasNonemptyFiniteLimits 𝒞] in
/-- The image in `u_p 𝒮` of an element of the right multiplicative system `R` is strongly
cartesian over an identity: it is an isomorphism lying over an `eqToHom`. -/
lemma isStronglyCartesian_Q_of_mem {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (r : Z ⟶ Z')
    (hr : idBaseStronglyCartesian p u r) :
    (pullbackProj p u).IsStronglyCartesian (𝟙 Z.left) ((idBaseStronglyCartesian p u).Q.map r) := by
  have : IsIso ((idBaseStronglyCartesian p u).Q.map r) :=
    Localization.inverts _ (idBaseStronglyCartesian p u) _ hr
  obtain ⟨⟨h, hl⟩, -⟩ := hr
  have : (pullbackProj p u).IsHomLift (𝟙 Z.left) ((idBaseStronglyCartesian p u).Q.map r) := by
    refine
      IsHomLift.of_fac' _ _ _ (pullbackProj_obj p u Z) ((pullbackProj_obj p u Z').trans h.symm) ?_
    rw [pullbackProj_map, hl]
    simp
  exact Functor.IsStronglyCartesian.of_isIso _ _ _

/-- **The canonical morphism `c_Z : Z ⟶ ι(x)` becomes strongly cartesian in `u_p 𝒮`.** This is
the case `α = id` of the claim of Stacks 04WG, restated at the object `ι(x)`. -/
lemma isStronglyCartesian_Q_toPullbackUnit
    (hu :
      ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
        Limits.PreservesLimitsOfShape J u)
    (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    (pullbackProj p u).IsStronglyCartesian Z.hom
      ((idBaseStronglyCartesian p u).Q.map (toPullbackUnit p u Z)) := by
  have hZ :
    (Comma.mk Z.left Z.right (Z.hom ≫ 𝟙 ((p ⋙ u).obj Z.right)) : Comma (𝟭 𝒟) (p ⋙ u)) = Z := by
    simp
  have hbc := isStronglyCartesian_Q_baseChangeHom p u hu ((pullbackUnit p u).obj Z.right) Z.hom
  have hfac :
    (eqToHom hZ.symm ≫ baseChangeHom p u ((pullbackUnit p u).obj Z.right) Z.hom) =
      toPullbackUnit p u Z := by
    refine Comma.hom_ext _ _ ?_ ?_
    · rw [Comma.comp_left, eqToHom_left_comma, toPullbackUnit_left, baseChangeHom_left]
      simp
    · rw [Comma.comp_right, eqToHom_right_comma, toPullbackUnit_right, baseChangeHom_right]
      simp
  rw [← hfac, Functor.map_comp]
  have :
    (pullbackProj p u).IsHomLift (𝟙 ((𝟭 𝒟).obj Z.left))
      ((idBaseStronglyCartesian p u).Q.map (eqToHom hZ.symm)) := by
    rw [eqToHom_map]
    exact IsHomLift.eqToHom_domain_lift_id _ (pullbackProj_obj p u Z)
  have : IsIso ((idBaseStronglyCartesian p u).Q.map (eqToHom hZ.symm)) := inferInstance
  exact
    PullbackAdjunction.isStronglyCartesian_id_comp
      (Functor.IsStronglyCartesian.of_isIso (pullbackProj p u) (𝟙 ((𝟭 𝒟).obj Z.left)) _) hbc

/-- The image of `ι(α)` in `u_p 𝒮` is strongly cartesian over `u(p(α))` when `α` is strongly
cartesian: `ι(α)` factors as an element of `R` followed by a reindexing morphism. -/
lemma isStronglyCartesian_Q_pullbackUnit_map
    (hu :
      ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
        Limits.PreservesLimitsOfShape J u)
    {x y : 𝒮} (α : x ⟶ y) (hα : p.IsStronglyCartesian (p.map α) α) :
    (pullbackProj p u).IsStronglyCartesian (u.map (p.map α))
      ((idBaseStronglyCartesian p u).Q.map ((pullbackUnit p u).map α)) := by
  have hbc :=
    isStronglyCartesian_Q_baseChangeHom p u hu ((pullbackUnit p u).obj y) (u.map (p.map α))
  have hrsc :=
    isStronglyCartesian_Q_of_mem p u (Z := (pullbackUnit p u).obj x) (Z' :=
      (Comma.mk (u.obj (p.obj x)) y (u.map (p.map α) ≫ 𝟙 ((p ⋙ u).obj y)) : Comma (𝟭 𝒟) (p ⋙ u)))
      ⟨𝟙 (u.obj (p.obj x)), α, by simp⟩ ⟨⟨rfl, by simp⟩, hα⟩
  have hfactor :
    (pullbackUnit p u).map α =
      (⟨𝟙 (u.obj (p.obj x)), α, by simp⟩ :
          (pullbackUnit p u).obj x ⟶
            (Comma.mk (u.obj (p.obj x)) y (u.map (p.map α) ≫ 𝟙 ((p ⋙ u).obj y)) :
              Comma (𝟭 𝒟) (p ⋙ u))) ≫
        baseChangeHom p u ((pullbackUnit p u).obj y) (u.map (p.map α)) :=
    Comma.hom_ext _ _ (by simp) (by simp)
  rw [hfactor, Functor.map_comp]
  exact PullbackAdjunction.isStronglyCartesian_id_comp hrsc hbc

end

end Comma

/-! ### Restriction along the unit: the functor `A` -/

namespace PullbackAdjunction

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] {𝒮 : Type u₃}
  [Category.{v₃} 𝒮] {𝒯 : Type u₄} [Category.{v₄} 𝒯]
variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) (q : 𝒯 ⥤ 𝒟)

/-- The morphism category `Mor_{Fib/𝒞}(𝒮, u^p 𝒯)`: the full subcategory of the based functors
`𝒮 ⥤ᵇ u^p 𝒯` over `𝒞` on those which preserve strongly cartesian morphisms. -/
abbrev morFibLeft :=
  ObjectProperty.FullSubcategory
    (fun G :
        BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor (StrictPullback.structureFunctor u q) =>
      Functor.IsFibredOneMorphism p (StrictPullback.structureFunctor u q) G.toFunctor)

/-- The morphism category `Mor_{Fib/𝒟}(u_p 𝒮, 𝒯)`: the full subcategory of the based functors
`u_p 𝒮 ⥤ᵇ 𝒯` over `𝒟` on those which preserve strongly cartesian morphisms. -/
abbrev morFibRight :=
  ObjectProperty.FullSubcategory
    (fun G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q =>
      Functor.IsFibredOneMorphism (Comma.pullbackProj p u) q G.toFunctor)

/-- The functor `𝒮 ⥤ 𝒯` underlying `A(G) = (p, G ∘ ι)`. -/
noncomputable def restrictFib
    (G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q) : 𝒮 ⥤ 𝒯 :=
  Comma.pullbackUnit p u ⋙ (Comma.idBaseStronglyCartesian p u).Q ⋙ G.toFunctor

/-- The functor `G ∘ ι : 𝒮 ⥤ 𝒯` lies over `u` along `p`: `(G ∘ ι) ⋙ q = p ⋙ u`. -/
lemma restrictFib_comp
    (G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q) :
    restrictFib p u q G ⋙ q = p ⋙ u := by
  have hG : G.toFunctor ⋙ q = Comma.pullbackProj p u := G.w
  calc
    restrictFib p u q G ⋙ q =
        Comma.pullbackUnit p u ⋙ (Comma.idBaseStronglyCartesian p u).Q ⋙ (G.toFunctor ⋙ q) :=
      rfl
    _ = Comma.pullbackUnit p u ⋙ (Comma.idBaseStronglyCartesian p u).Q ⋙ Comma.pullbackProj p u :=
      by rw [hG]
    _ = Comma.pullbackUnit p u ⋙ Comma.fst (𝟭 𝒟) (p ⋙ u) := by rw [Comma.pullbackProj_fac]
    _ = p ⋙ u := rfl

/-- `A(G) : 𝒮 ⥤ u^p 𝒯`, the based functor `x ↦ (p(x), G(ι(x)))`. -/
noncomputable def restrictBased
    (G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q) :
    BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (StrictPullback.structureFunctor u q)
    where
  toFunctor := StrictPullback.liftFib p (restrictFib p u q G) (restrictFib_comp p u q G)
  w := rfl

/-- The `𝒞`-component of `A(G)(x)` is `p(x)`. -/
@[simp]
lemma restrictBased_obj_base
    (G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q) (x : 𝒮) :
    ((restrictBased p u q G).obj x).base = p.obj x :=
  rfl

/-- The `𝒯`-component of `A(G)(x)` is `G(ι(x))`. -/
@[simp]
lemma restrictBased_obj_fib
    (G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q) (x : 𝒮) :
    ((restrictBased p u q G).obj x).fib = (restrictFib p u q G).obj x :=
  rfl

/-- The `𝒞`-component of `A(G)(α)` is `p(α)`. -/
@[simp]
lemma restrictBased_map_base
    (G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q) {x y : 𝒮}
    (α : x ⟶ y) : ((restrictBased p u q G).map α).base = p.map α :=
  rfl

/-- The `𝒯`-component of `A(G)(α)` is `G(ι(α))`. -/
@[simp]
lemma restrictBased_map_fib
    (G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q) {x y : 𝒮}
    (α : x ⟶ y) : ((restrictBased p u q G).map α).fib = (restrictFib p u q G).map α :=
  rfl

/-- The morphism of functors `𝒮 ⥤ u^p 𝒯` induced by a morphism of functors on `u_p 𝒮`. -/
noncomputable def restrictNatTrans
    {G₁ G₂ : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q}
    (σ : G₁ ⟶ G₂) : (restrictBased p u q G₁).toFunctor ⟶ (restrictBased p u q G₂).toFunctor :=
  StrictPullback.liftFibNatTrans p (restrictFib_comp p u q G₁) (restrictFib_comp p u q G₂)
    (Functor.whiskerLeft (Comma.pullbackUnit p u ⋙ (Comma.idBaseStronglyCartesian p u).Q)
      σ.toNatTrans)
    (fun x =>
      σ.isHomLift' ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)))

/-- The `𝒯`-component of `restrictNatTrans σ` at `x` is the component of `σ` at `ι(x)`. -/
@[simp]
lemma restrictNatTrans_app_fib
    {G₁ G₂ : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q}
    (σ : G₁ ⟶ G₂) (x : 𝒮) :
    ((restrictNatTrans p u q σ).app x).fib =
      σ.toNatTrans.app
        ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) :=
  rfl

/-- The `𝒞`-component of `restrictNatTrans σ` at `x` is the identity of `p(x)`. -/
@[simp]
lemma restrictNatTrans_app_base
    {G₁ G₂ : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q}
    (σ : G₁ ⟶ G₂) (x : 𝒮) : ((restrictNatTrans p u q σ).app x).base = 𝟙 (p.obj x) :=
  rfl

/-- A morphism of functors over `𝒟` on `u_p 𝒮` induces one over `𝒞` between the restrictions
along the unit. -/
noncomputable def restrictBasedMap
    {G₁ G₂ : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q}
    (σ : G₁ ⟶ G₂) : restrictBased p u q G₁ ⟶ restrictBased p u q G₂
    where
  toNatTrans := restrictNatTrans p u q σ
  isHomLift' := fun x => StrictPullback.isHomLift_hom ((restrictNatTrans p u q σ).app x)

/-- The `𝒯`-component of `restrictBasedMap σ` at `x` is the component of `σ` at `ι(x)`. -/
@[simp]
lemma restrictBasedMap_app_fib
    {G₁ G₂ : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q}
    (σ : G₁ ⟶ G₂) (x : 𝒮) :
    ((restrictBasedMap p u q σ).toNatTrans.app x).fib =
      σ.toNatTrans.app
        ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) :=
  rfl

/-- The `𝒞`-component of `restrictBasedMap σ` at `x` is the identity of `p(x)`. -/
@[simp]
lemma restrictBasedMap_app_base
    {G₁ G₂ : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q}
    (σ : G₁ ⟶ G₂) (x : 𝒮) : ((restrictBasedMap p u q σ).toNatTrans.app x).base = 𝟙 (p.obj x) :=
  rfl

section

variable [p.IsFibered] [HasNonemptyFiniteLimits 𝒞]

omit [p.IsFibered] [HasNonemptyFiniteLimits 𝒞] in
/-- A functor `F : 𝒮 ⥤ 𝒯` over `u` carries `p`-strongly cartesian morphisms to `q`-strongly
cartesian ones exactly when its lift `𝒮 ⥤ u^p 𝒯` does. This is the forward direction. -/
lemma isStronglyCartesian_liftFib_map {F : 𝒮 ⥤ 𝒯} (h : F ⋙ q = p ⋙ u) {R T : 𝒞} (f : R ⟶ T)
    {a b : 𝒮} (α : a ⟶ b) (hα : p.IsStronglyCartesian f α)
    (hF : q.IsStronglyCartesian (u.map f) (F.map α)) :
    (StrictPullback.structureFunctor u q).IsStronglyCartesian f
      ((StrictPullback.liftFib p F h).map α) := by
  have := hα
  subst_hom_lift p f α
  refine StrictPullback.isStronglyCartesian_of_fib ((StrictPullback.liftFib p F h).map α) ?_
  exact Functor.IsStronglyCartesian.eqToHom_comp_eqToHom _ _ _ _ hF

/-- `A(G)` is a 1-morphism of fibred categories over `𝒞`. -/
lemma isFibredOneMorphism_restrictBased
    (hu :
      ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
        Limits.PreservesLimitsOfShape J u)
    (G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q)
    (hG : Functor.IsFibredOneMorphism (Comma.pullbackProj p u) q G.toFunctor) :
    Functor.IsFibredOneMorphism p (StrictPullback.structureFunctor u q)
      (restrictBased p u q G).toFunctor := by
  refine isFibredOneMorphism_of_exists_lift _ _ _ rfl ?_
  intro b V β
  obtain ⟨a, g, hg⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) (a := b) β
  have hgs : p.IsStronglyCartesian β g := inferInstance
  refine ⟨a, g, hgs, isStronglyCartesian_liftFib_map p u q (restrictFib_comp p u q G) β g hgs ?_⟩
  have hβ :
    p.map g =
      eqToHom (IsHomLift.domain_eq p β g) ≫ β ≫ eqToHom (IsHomLift.codomain_eq p β g).symm :=
    IsHomLift.fac' p β g
  have hsc : p.IsStronglyCartesian (p.map g) g := by
    rw [hβ]
    exact Functor.IsStronglyCartesian.eqToHom_comp_eqToHom _ _ _ _ hgs
  have hmap : q.IsStronglyCartesian (u.map (p.map g)) ((restrictFib p u q G).map g) :=
    hG.map_isStronglyCartesian _ _ (Comma.isStronglyCartesian_Q_pullbackUnit_map p u hu g hsc)
  rw [hβ] at hmap
  simp only [Functor.map_comp, eqToHom_map, eqToHom_refl, Category.comp_id] at hmap
  exact Functor.IsStronglyCartesian.of_eqToHom_comp _ _ _ hmap

/-- **Restriction along the unit**, the functor `A` of the source's proof: it sends a 1-morphism
`G : u_p 𝒮 ⟶ 𝒯` of fibred categories over `𝒟` to the 1-morphism `𝒮 ⟶ u^p 𝒯` over `𝒞` given on an
object `x` over `U` by `(U, G(U, id_{u(U)}, x))`. -/
noncomputable def restrictAlongPullbackUnit
    (hu :
      ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
        Limits.PreservesLimitsOfShape J u) :
    morFibRight p u q ⥤ morFibLeft p u q
    where
  obj G := ⟨restrictBased p u q G.obj, isFibredOneMorphism_restrictBased p u q hu G.obj G.property⟩
  map σ := InducedCategory.homMk (restrictBasedMap p u q σ.hom)
  map_id G := by
    apply InducedCategory.hom_ext
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext x
    apply StrictPullback.Hom.ext <;> rfl
  map_comp σ τ := by
    apply InducedCategory.hom_ext
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext x
    apply StrictPullback.Hom.ext
    · exact (Category.comp_id (𝟙 (p.obj x))).symm
    · rfl

/-- The `𝒯`-component of `A(σ)` at `x` is the component of `σ` at `ι(x)`. -/
@[simp]
lemma restrictAlongPullbackUnit_map_app_fib
    (hu :
      ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
        Limits.PreservesLimitsOfShape J u)
    {G₁ G₂ : morFibRight p u q} (σ : G₁ ⟶ G₂) (x : 𝒮) :
    (((restrictAlongPullbackUnit p u q hu).map σ).hom.toNatTrans.app x).fib =
      σ.hom.toNatTrans.app
        ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) :=
  rfl

end

/-! ### The extension over the localization: the functor `B` -/

section B

variable [q.IsFibered] (F : 𝒮 ⥤ 𝒯) (hF : F ⋙ q = p ⋙ u)

include hF

omit [q.IsFibered] in
/-- `F(α)` lies over `u(p(α))`. -/
lemma isHomLift_map_of_comp {x y : 𝒮} (α : x ⟶ y) : q.IsHomLift ((p ⋙ u).map α) (F.map α) :=
  Functor.isHomLift_map_of_comp_eq hF _ α

/-- `φ^* F(x)`, the chosen pullback of `F(x)` along `φ`, for `Z = (U, φ : V ⟶ u(U), x)`. -/
noncomputable def leftToRightObj (Z : Comma (𝟭 𝒟) (p ⋙ u)) : 𝒯 :=
  Functor.IsPreFibered.pullbackObj (p := q) (Functor.congr_obj hF Z.right) Z.hom

/-- The chosen strongly cartesian morphism `φ^* F(x) ⟶ F(x)` over `φ`. -/
noncomputable def leftToRightMap (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    leftToRightObj p u q F hF Z ⟶ F.obj Z.right :=
  Functor.IsPreFibered.pullbackMap (p := q) (Functor.congr_obj hF Z.right) Z.hom

/-- The chosen morphism `φ^* F(x) ⟶ F(x)` is strongly cartesian over `φ`. -/
instance leftToRightMap_isStronglyCartesian (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    q.IsStronglyCartesian Z.hom (leftToRightMap p u q F hF Z) := by
  unfold leftToRightMap
  infer_instance

/-- The pullback `φ^* F(x)` lies over `V`, for `Z = (U, φ : V ⟶ u(U), x)`. -/
lemma leftToRightObj_proj (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    q.obj (leftToRightObj p u q F hF Z) = Z.left :=
  Functor.IsPreFibered.pullbackObj_proj _ _

/-- The composite `φ^* F(x) ⟶ F(x) ⟶ F(x')` lies over the `𝒟`-component of `(a, b, α)`. -/
lemma isHomLift_leftToRightMap_comp {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    q.IsHomLift (f.left ≫ Z'.hom) (leftToRightMap p u q F hF Z ≫ F.map f.right) := by
  have h2 := isHomLift_map_of_comp p u q F hF f.right
  have h3 :
    q.IsHomLift (Z.hom ≫ (p ⋙ u).map f.right) (leftToRightMap p u q F hF Z ≫ F.map f.right) :=
    inferInstance
  have hw : f.left ≫ Z'.hom = Z.hom ≫ (p ⋙ u).map f.right := by simpa using f.w
  rw [hw]
  exact h3

/-- The morphism `φ^* F(x) ⟶ (φ')^* F(x')` induced by a morphism `(a, b, α)` of `u_pp 𝒮`. -/
noncomputable def leftToRightHom {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    leftToRightObj p u q F hF Z ⟶ leftToRightObj p u q F hF Z' :=
  haveI := isHomLift_leftToRightMap_comp p u q F hF f
  Functor.IsStronglyCartesian.map q Z'.hom (leftToRightMap p u q F hF Z') (g := f.left) (f' :=
    f.left ≫ Z'.hom) rfl (leftToRightMap p u q F hF Z ≫ F.map f.right)

/-- The morphism `leftToRightHom f` lies over the `𝒟`-component of `f`. -/
instance leftToRightHom_isHomLift {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    q.IsHomLift f.left (leftToRightHom p u q F hF f) := by
  unfold leftToRightHom
  have := isHomLift_leftToRightMap_comp p u q F hF f
  exact Functor.IsStronglyCartesian.map_isHomLift q Z'.hom _ _ _

/-- The defining square of `leftToRightHom f`: composed with `φ'^* F(x') ⟶ F(x')` it equals
`φ^* F(x) ⟶ F(x)` followed by `F` of the `𝒮`-component of `f`. -/
@[simp, reassoc]
lemma leftToRightHom_fac {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    leftToRightHom p u q F hF f ≫ leftToRightMap p u q F hF Z' =
      leftToRightMap p u q F hF Z ≫ F.map f.right := by
  unfold leftToRightHom
  have := isHomLift_leftToRightMap_comp p u q F hF f
  exact Functor.IsStronglyCartesian.fac q Z'.hom _ _ _

/-- `G'(f)` is the *unique* morphism over the `𝒟`-component of `f` making the defining square
commute. -/
lemma leftToRightHom_eq {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z')
    (χ : leftToRightObj p u q F hF Z ⟶ leftToRightObj p u q F hF Z') (hlift : q.IsHomLift f.left χ)
    (hχ : χ ≫ leftToRightMap p u q F hF Z' = leftToRightMap p u q F hF Z ≫ F.map f.right) :
    χ = leftToRightHom p u q F hF f := by
  have := hlift
  have := isHomLift_leftToRightMap_comp p u q F hF f
  exact
    Functor.IsStronglyCartesian.map_uniq q Z'.hom (leftToRightMap p u q F hF Z') (g := f.left)
      (f' := f.left ≫ Z'.hom) rfl (leftToRightMap p u q F hF Z ≫ F.map f.right) χ hχ

/-- The functor `G' : u_pp 𝒮 ⥤ 𝒯`, `(U, φ : V ⟶ u(U), x) ↦ φ^* F(x)`. -/
noncomputable def leftToRightPre : Comma (𝟭 𝒟) (p ⋙ u) ⥤ 𝒯 where
  obj := leftToRightObj p u q F hF
  map := leftToRightHom p u q F hF
  map_id Z := by
    refine (leftToRightHom_eq p u q F hF (𝟙 Z) (𝟙 (leftToRightObj p u q F hF Z)) ?_ ?_).symm
    · exact IsHomLift.id (leftToRightObj_proj p u q F hF Z)
    · simp
  map_comp {Z Z' Z''} f g := by
    refine
      (leftToRightHom_eq p u q F hF (f ≫ g)
          (leftToRightHom p u q F hF f ≫ leftToRightHom p u q F hF g) ?_ ?_).symm
    · exact IsHomLift.comp q f.left g.left _ _
    · rw [Category.assoc, leftToRightHom_fac, ← Category.assoc, leftToRightHom_fac, Category.assoc,
        ← F.map_comp]
      simp

/-- `G'` sends `Z` to `leftToRightObj Z`. -/
@[simp]
lemma leftToRightPre_obj (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    (leftToRightPre p u q F hF).obj Z = leftToRightObj p u q F hF Z :=
  rfl

/-- `G'` sends `f` to `leftToRightHom f`. -/
@[simp]
lemma leftToRightPre_map {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    (leftToRightPre p u q F hF).map f = leftToRightHom p u q F hF f :=
  rfl

/-- `G'` lies over `𝒟`: `G' ⋙ q` is the projection `u_pp 𝒮 ⥤ 𝒟`. -/
lemma leftToRightPre_comp_fst : leftToRightPre p u q F hF ⋙ q = Comma.fst (𝟭 𝒟) (p ⋙ u) :=
  Functor.ext (fun Z => leftToRightObj_proj p u q F hF Z)
    (fun _ _ f => IsHomLift.fac' q f.left (leftToRightHom p u q F hF f))

/-- `G'` carries a morphism whose `𝒮`-component is strongly cartesian to a strongly cartesian
morphism: in the square defining `G'(f)` the other three arrows are strongly cartesian. -/
lemma isStronglyCartesian_leftToRightHom
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z')
    (hf : p.IsStronglyCartesian (p.map f.right) f.right) :
    q.IsStronglyCartesian f.left (leftToRightHom p u q F hF f) := by
  have h1 : q.IsStronglyCartesian ((p ⋙ u).map f.right) (F.map f.right) := hFsc f.right hf
  have h2 :
    q.IsStronglyCartesian (Z.hom ≫ (p ⋙ u).map f.right)
      (leftToRightMap p u q F hF Z ≫ F.map f.right) :=
    Functor.IsStronglyCartesian.comp q
  have hw : f.left ≫ Z'.hom = Z.hom ≫ (p ⋙ u).map f.right := by simpa using f.w
  rw [← hw, ← leftToRightHom_fac p u q F hF f] at h2
  exact
    Functor.IsStronglyCartesian.of_comp (p := q) (f := f.left) (g := Z'.hom) (φ :=
      leftToRightHom p u q F hF f) (ψ := leftToRightMap p u q F hF Z')

/-- `G'` inverts `R`: an element of `R` has `𝒟`-component an `eqToHom` and `𝒮`-component
strongly cartesian, so its image is strongly cartesian over an isomorphism. -/
lemma isInvertedBy_leftToRightPre
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α)) :
    (Comma.idBaseStronglyCartesian p u).IsInvertedBy (leftToRightPre p u q F hF) := by
  intro Z Z' r hr
  obtain ⟨⟨h, hl⟩, hr2⟩ := hr
  have := isStronglyCartesian_leftToRightHom p u q F hF hFsc r hr2
  have : IsIso r.left := by
    rw [hl]; infer_instance
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso q r.left (leftToRightHom p u q F hF r)

/-- **The functor `B(H) : u_p 𝒮 ⥤ 𝒯`**, the extension of `G'` over the localization. -/
noncomputable def leftToRight
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α)) :
    Comma.pullbackLocalization p u ⥤ 𝒯 :=
  Localization.Construction.lift (leftToRightPre p u q F hF)
    (isInvertedBy_leftToRightPre p u q F hF hFsc)

/-- `B(H)` restricts to `G'` along the localization functor `u_pp 𝒮 ⥤ u_p 𝒮`. -/
lemma leftToRight_fac
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α)) :
    (Comma.idBaseStronglyCartesian p u).Q ⋙ leftToRight p u q F hF hFsc =
      leftToRightPre p u q F hF :=
  Localization.Construction.fac _ _

/-- `B(H)` lies over `𝒟`: `B(H) ⋙ q = p_p`. -/
lemma leftToRight_comp_q
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α)) :
    leftToRight p u q F hF hFsc ⋙ q = Comma.pullbackProj p u := by
  refine Comma.pullbackProj_uniq p u _ ?_
  calc
    (Comma.idBaseStronglyCartesian p u).Q ⋙ (leftToRight p u q F hF hFsc ⋙ q) =
        ((Comma.idBaseStronglyCartesian p u).Q ⋙ leftToRight p u q F hF hFsc) ⋙ q :=
      rfl
    _ = leftToRightPre p u q F hF ⋙ q := by rw [leftToRight_fac]
    _ = Comma.fst (𝟭 𝒟) (p ⋙ u) := leftToRightPre_comp_fst p u q F hF

/-- `B(H)` is a 1-morphism of fibred categories over `𝒟`. -/
lemma isFibredOneMorphism_leftToRight [p.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (hu :
      ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
        Limits.PreservesLimitsOfShape J u)
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α)) :
    Functor.IsFibredOneMorphism (Comma.pullbackProj p u) q (leftToRight p u q F hF hFsc) := by
  refine isFibredOneMorphism_of_exists_lift _ _ _ (leftToRight_comp_q p u q F hF hFsc) ?_
  intro b V β
  obtain ⟨Z, rfl⟩ : ∃ Z, (Comma.idBaseStronglyCartesian p u).Q.obj Z = b :=
    ⟨_,
      (Localization.Construction.objEquiv (Comma.idBaseStronglyCartesian p u)).apply_symm_apply b⟩
  have hZ : (Comma.pullbackProj p u).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z) = Z.left :=
    Comma.pullbackProj_obj p u Z
  refine
    ⟨_, (Comma.idBaseStronglyCartesian p u).Q.map (Comma.baseChangeHom p u Z (β ≫ eqToHom hZ)), ?_,
      ?_⟩
  · exact
      Functor.IsStronglyCartesian.of_comp_eqToHom hZ β _
        (Comma.isStronglyCartesian_Q_baseChangeHom p u hu Z (β ≫ eqToHom hZ))
  · have h1 :
      q.IsStronglyCartesian (β ≫ eqToHom hZ)
        ((leftToRightPre p u q F hF).map (Comma.baseChangeHom p u Z (β ≫ eqToHom hZ))) := by
      have h0 :=
        isStronglyCartesian_leftToRightHom p u q F hF hFsc
          (Comma.baseChangeHom p u Z (β ≫ eqToHom hZ))
          (by simpa [stronglyCartesianOver] using stronglyCartesianOver_id p Z.right)
      simpa using h0
    have h2 :=
      isStronglyCartesian_map_of_functor_eq q (leftToRight_fac p u q F hF hFsc)
        (Comma.baseChangeHom p u Z (β ≫ eqToHom hZ)) (β ≫ eqToHom hZ) h1
    exact Functor.IsStronglyCartesian.of_comp_eqToHom hZ β _ h2

/-! #### The counit `A(B(F)) ≅ F`

Restricting `B(F)` back along the unit returns, at an object `x` of `𝒮`, the chosen pullback of
`F(x)` along the identity of `u(p(x))`; the chosen strongly cartesian lift is therefore an
isomorphism onto `F(x)`, and these isomorphisms assemble into an isomorphism of 1-morphisms. -/

/-- `B(F)` packaged as a based functor `u_p 𝒮 ⥤ᵇ 𝒯` over `𝒟`. -/
noncomputable def leftToRightBased
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α)) :
    BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q
    where
  toFunctor := leftToRight p u q F hF hFsc
  w := leftToRight_comp_q p u q F hF hFsc

/-- At an object in the image of the unit, `B(F)` is the chosen pullback of `F(x)` along the
identity. -/
lemma leftToRight_obj_pullbackUnit
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    (x : 𝒮) :
    (leftToRight p u q F hF hFsc).obj
        ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) =
      leftToRightObj p u q F hF ((Comma.pullbackUnit p u).obj x) :=
  Functor.congr_obj (leftToRight_fac p u q F hF hFsc) _

/-- The component of the counit at `x`: the chosen strongly cartesian lift of the identity of
`u(p(x))` with target `F(x)`. -/
noncomputable def counitHom
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    (x : 𝒮) : (restrictFib p u q (leftToRightBased p u q F hF hFsc)).obj x ⟶ F.obj x :=
  eqToHom (leftToRight_obj_pullbackUnit p u q F hF hFsc x) ≫
    leftToRightMap p u q F hF ((Comma.pullbackUnit p u).obj x)

/-- The component of the counit at `x` lies over the identity of `u(p(x))`. -/
lemma counitHom_isHomLift
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    (x : 𝒮) : q.IsHomLift (𝟙 (u.obj (p.obj x))) (counitHom p u q F hF hFsc x) := by
  have h1 :
    q.IsHomLift (𝟙 (u.obj (p.obj x))) (eqToHom (leftToRight_obj_pullbackUnit p u q F hF hFsc x)) :=
    IsHomLift.eqToHom_domain_lift_id _
      (by
        rw [leftToRight_obj_pullbackUnit]
        exact leftToRightObj_proj p u q F hF ((Comma.pullbackUnit p u).obj x))
  have h2 :
    q.IsHomLift (𝟙 (u.obj (p.obj x)))
      (leftToRightMap p u q F hF ((Comma.pullbackUnit p u).obj x)) :=
    (leftToRightMap_isStronglyCartesian p u q F hF ((Comma.pullbackUnit p u).obj x)).toIsHomLift
  have hc :=
    IsHomLift.comp q (𝟙 (u.obj (p.obj x))) (𝟙 (u.obj (p.obj x)))
      (eqToHom (leftToRight_obj_pullbackUnit p u q F hF hFsc x))
      (leftToRightMap p u q F hF ((Comma.pullbackUnit p u).obj x))
  simpa [counitHom] using hc

/-- The component of the counit at `x` is an isomorphism. -/
instance counitHom_isIso
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    (x : 𝒮) : IsIso (counitHom p u q F hF hFsc x) := by
  have h2 :
    q.IsStronglyCartesian (𝟙 (u.obj (p.obj x)))
      (leftToRightMap p u q F hF ((Comma.pullbackUnit p u).obj x)) :=
    leftToRightMap_isStronglyCartesian p u q F hF ((Comma.pullbackUnit p u).obj x)
  have : IsIso (leftToRightMap p u q F hF ((Comma.pullbackUnit p u).obj x)) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso q (𝟙 (u.obj (p.obj x))) _
  unfold counitHom
  infer_instance

/-- The components of the counit are natural in `x`. -/
lemma counitHom_naturality
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    {x y : 𝒮} (α : x ⟶ y) :
    (restrictFib p u q (leftToRightBased p u q F hF hFsc)).map α ≫ counitHom p u q F hF hFsc y =
      counitHom p u q F hF hFsc x ≫ F.map α := by
  have hfac := Functor.congr_hom (leftToRight_fac p u q F hF hFsc) ((Comma.pullbackUnit p u).map α)
  simp only [Functor.comp_map] at hfac
  dsimp only [restrictFib, leftToRightBased, Functor.comp_map]
  rw [hfac]
  simp only [counitHom, leftToRightPre_map, Category.assoc, eqToHom_refl, Category.id_comp]
  rw [leftToRightHom_fac]
  simp

/-- The counit `A(B(F)) ⟶ F` as a morphism of functors `𝒮 ⥤ u^p 𝒯`. -/
noncomputable def counitNatTrans
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α)) :
    (restrictBased p u q (leftToRightBased p u q F hF hFsc)).toFunctor ⟶
      StrictPullback.liftFib p F hF :=
  StrictPullback.liftFibNatTrans p (restrictFib_comp p u q (leftToRightBased p u q F hF hFsc)) hF
    { app := counitHom p u q F hF hFsc
      naturality := fun _ _ α => counitHom_naturality p u q F hF hFsc α }
    (counitHom_isHomLift p u q F hF hFsc)

/-- Each component of `counitNatTrans` is an isomorphism of `u^p 𝒯`. -/
instance counitNatTrans_app_isIso
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    (x : 𝒮) : IsIso ((counitNatTrans p u q F hF hFsc).app x) := by
  have : IsIso ((counitNatTrans p u q F hF hFsc).app x).base := by
    change IsIso (𝟙 (p.obj x)); infer_instance
  have : IsIso ((counitNatTrans p u q F hF hFsc).app x).fib := by
    rw [counitNatTrans, StrictPullback.liftFibNatTrans_app_fib]; infer_instance
  exact StrictPullback.isIso_of_isIso_base_fib _

/-- The counit `A(B(F)) ⟶ F` is an isomorphism of functors. -/
instance counitNatTrans_isIso
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α)) :
    IsIso (counitNatTrans p u q F hF hFsc) :=
  NatIso.isIso_of_isIso_app _

/-- **The counit is an isomorphism**: restricting `B(F)` along the unit gives back `F`. -/
noncomputable def counitIso
    (hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        p.IsStronglyCartesian (p.map α) α → q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α)) :
    restrictBased p u q (leftToRightBased p u q F hF hFsc) ≅
      (⟨StrictPullback.liftFib p F hF, rfl⟩ :
        BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor (StrictPullback.structureFunctor u q)) :=
  BasedNatIso.mkNatIso (asIso (counitNatTrans p u q F hF hFsc))
    (fun x => StrictPullback.isHomLift_hom ((counitNatTrans p u q F hF hFsc).app x))

end B

end PullbackAdjunction

/-! ### The equivalence -/

namespace PullbackAdjunction

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] {𝒮 : Type u₃}
  [Category.{v₃} 𝒮] {𝒯 : Type u₄} [Category.{v₄} 𝒯]
variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) (q : 𝒯 ⥤ 𝒟) [p.IsFibered] [q.IsFibered]
  [HasNonemptyFiniteLimits 𝒞]
  (hu :
    ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J], Limits.PreservesLimitsOfShape J u)

include hu

omit [q.IsFibered] in
/-- The image of `c_Z` under a 1-morphism `G` of fibred categories over `𝒟` is strongly
cartesian over `φ`. This is the observation on which fullness and faithfulness rest. -/
lemma isStronglyCartesian_map_Q_toPullbackUnit
    (G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q)
    (hG : Functor.IsFibredOneMorphism (Comma.pullbackProj p u) q G.toFunctor)
    (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    q.IsStronglyCartesian Z.hom
      (G.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z))) :=
  hG.map_isStronglyCartesian _ _ (Comma.isStronglyCartesian_Q_toPullbackUnit p u hu Z)

/-- Restriction along the unit is faithful. -/
instance : (restrictAlongPullbackUnit p u q hu).Faithful where
  map_injective {G₁ G₂} σ τ h := by
    have hx :
      ∀ x : 𝒮,
        σ.hom.toNatTrans.app
            ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) =
          τ.hom.toNatTrans.app
            ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) := by
      intro x
      have :=
        congrArg
          (fun m :
              (restrictAlongPullbackUnit p u q hu).obj G₁ ⟶
                (restrictAlongPullbackUnit p u q hu).obj G₂ =>
            (m.hom.toNatTrans.app x).fib)
          h
      simpa using this
    apply InducedCategory.hom_ext
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext X
    obtain ⟨Z, rfl⟩ : ∃ Z, (Comma.idBaseStronglyCartesian p u).Q.obj Z = X :=
      ⟨_,
        (Localization.Construction.objEquiv (Comma.idBaseStronglyCartesian p u)).apply_symm_apply
          X⟩
    have hZ :
      (Comma.pullbackProj p u).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z) = Z.left :=
      Comma.pullbackProj_obj p u Z
    have hsc := isStronglyCartesian_map_Q_toPullbackUnit p u q hu G₂.obj G₂.property Z
    have hσ :
      q.IsHomLift (𝟙 Z.left)
        (σ.hom.toNatTrans.app ((Comma.idBaseStronglyCartesian p u).Q.obj Z)) := by
      have h0 :
        q.IsHomLift
          (𝟙 ((Comma.pullbackProj p u).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z)))
          (σ.hom.toNatTrans.app ((Comma.idBaseStronglyCartesian p u).Q.obj Z)) :=
        σ.hom.isHomLift' ((Comma.idBaseStronglyCartesian p u).Q.obj Z)
      rwa [hZ] at h0
    have hτ :
      q.IsHomLift (𝟙 Z.left)
        (τ.hom.toNatTrans.app ((Comma.idBaseStronglyCartesian p u).Q.obj Z)) := by
      have h0 :
        q.IsHomLift
          (𝟙 ((Comma.pullbackProj p u).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z)))
          (τ.hom.toNatTrans.app ((Comma.idBaseStronglyCartesian p u).Q.obj Z)) :=
        τ.hom.isHomLift' ((Comma.idBaseStronglyCartesian p u).Q.obj Z)
      rwa [hZ] at h0
    refine
      Functor.IsStronglyCartesian.ext q Z.hom
        (G₂.obj.toFunctor.map
          ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)))
        (𝟙 Z.left) ?_
    rw [← σ.hom.toNatTrans.naturality, ← τ.hom.toNatTrans.naturality, hx Z.right]

/-- Restriction along the unit is full. -/
instance : (restrictAlongPullbackUnit p u q hu).Full where
  map_surjective {G₁ G₂} σ := by
    have hG₁w : G₁.obj.toFunctor ⋙ q = Comma.pullbackProj p u := G₁.obj.w
    have hG₂w : G₂.obj.toFunctor ⋙ q = Comma.pullbackProj p u := G₂.obj.w
    set s :
      ∀ x : 𝒮,
        G₁.obj.toFunctor.obj
            ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) ⟶
          G₂.obj.toFunctor.obj
            ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) :=
      fun x => (σ.hom.toNatTrans.app x).fib with hs
    have hslift : ∀ x : 𝒮, q.IsHomLift (𝟙 (u.obj (p.obj x))) (s x) := by
      intro x
      have hσx :
        (StrictPullback.structureFunctor u q).IsHomLift (𝟙 (p.obj x)) (σ.hom.toNatTrans.app x) :=
        σ.hom.isHomLift' x
      have hb : ((σ.hom.toNatTrans.app x)).base = 𝟙 (p.obj x) :=
        StrictPullback.base_eq (𝟙 (p.obj x)) (σ.hom.toNatTrans.app x)
      exact StrictPullback.isHomLift_fib_of_base_id (σ.hom.toNatTrans.app x) rfl hb
    have hexists :
      ∃ t :
        ∀ Z : Comma (𝟭 𝒟) (p ⋙ u),
          G₁.obj.toFunctor.obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z) ⟶
            G₂.obj.toFunctor.obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z),
        (∀ Z, q.IsHomLift (𝟙 Z.left) (t Z)) ∧
          (∀ Z,
            t Z ≫
                G₂.obj.toFunctor.map
                  ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)) =
              G₁.obj.toFunctor.map
                  ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)) ≫
                s Z.right) := by
      have key :
        ∀ Z : Comma (𝟭 𝒟) (p ⋙ u),
          q.IsHomLift Z.hom
            (G₁.obj.toFunctor.map
                ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)) ≫
              s Z.right) := by
        intro Z
        have :
          (Comma.pullbackProj p u).IsHomLift Z.hom
            ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)) :=
          (Comma.isStronglyCartesian_Q_toPullbackUnit p u hu Z).toIsHomLift
        have :
          q.IsHomLift Z.hom
            (G₁.obj.toFunctor.map
              ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z))) :=
          Functor.isHomLift_map_of_comp_eq hG₁w _ _
        have := hslift Z.right
        have hcomp :=
          IsHomLift.comp q Z.hom (𝟙 (u.obj (p.obj Z.right)))
            (G₁.obj.toFunctor.map
              ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)))
            (s Z.right)
        simpa using hcomp
      have hZex :
        ∀ Z : Comma (𝟭 𝒟) (p ⋙ u),
          ∃ tZ :
            G₁.obj.toFunctor.obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z) ⟶
              G₂.obj.toFunctor.obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z),
            q.IsHomLift (𝟙 Z.left) tZ ∧
              tZ ≫
                  G₂.obj.toFunctor.map
                    ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)) =
                G₁.obj.toFunctor.map
                    ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)) ≫
                  s Z.right := by
        intro Z
        have := isStronglyCartesian_map_Q_toPullbackUnit p u q hu G₂.obj G₂.property Z
        have := key Z
        refine
          ⟨Functor.IsStronglyCartesian.map q Z.hom
              (G₂.obj.toFunctor.map
                ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)))
              (g := 𝟙 Z.left) (f' := Z.hom) (by simp)
              (G₁.obj.toFunctor.map
                  ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)) ≫
                s Z.right),
            ?_, ?_⟩
        · exact Functor.IsStronglyCartesian.map_isHomLift q Z.hom _ _ _
        · exact Functor.IsStronglyCartesian.fac q Z.hom _ _ _
      choose t htlift htfac using hZex
      exact ⟨t, htlift, htfac⟩
    obtain ⟨t, htlift, htfac⟩ := hexists
    have hnat :
      ∀ {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z'),
        G₁.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f) ≫ t Z' =
          t Z ≫ G₂.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f) := by
      intro Z Z' f
      have hsc := isStronglyCartesian_map_Q_toPullbackUnit p u q hu G₂.obj G₂.property Z'
      have h1 :
        (Comma.pullbackProj p u).IsHomLift f.left
          ((Comma.idBaseStronglyCartesian p u).Q.map f) := by
        refine
          IsHomLift.of_fac' (Comma.pullbackProj p u) _ _ (Comma.pullbackProj_obj p u Z)
            (Comma.pullbackProj_obj p u Z') ?_
        simp
      have h2 :
        q.IsHomLift f.left (G₁.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f)) :=
        Functor.isHomLift_map_of_comp_eq hG₁w _ _
      have h3 :
        q.IsHomLift f.left (G₂.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f)) :=
        Functor.isHomLift_map_of_comp_eq hG₂w _ _
      have := htlift Z
      have := htlift Z'
      have hl1 :
        q.IsHomLift f.left
          (G₁.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f) ≫ t Z') := by
        have hc :=
          IsHomLift.comp q f.left (𝟙 Z'.left)
            (G₁.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f)) (t Z')
        simpa using hc
      have hl2 :
        q.IsHomLift f.left
          (t Z ≫ G₂.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f)) := by
        have hc :=
          IsHomLift.comp q (𝟙 Z.left) f.left (t Z)
            (G₂.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f))
        simpa using hc
      refine
        Functor.IsStronglyCartesian.ext q Z'.hom
          (G₂.obj.toFunctor.map
            ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z')))
          f.left ?_
      have hσnat := σ.hom.toNatTrans.naturality f.right
      have hσfib :
        G₁.obj.toFunctor.map
              ((Comma.idBaseStronglyCartesian p u).Q.map ((Comma.pullbackUnit p u).map f.right)) ≫
            s Z'.right =
          s Z.right ≫
            G₂.obj.toFunctor.map
              ((Comma.idBaseStronglyCartesian p u).Q.map
                ((Comma.pullbackUnit p u).map f.right)) := by
        simp only [hs]
        exact congrArg StrictPullback.Hom.fib hσnat
      calc
        (G₁.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f) ≫ t Z') ≫
              G₂.obj.toFunctor.map
                ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z')) =
            G₁.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f) ≫
              (G₁.obj.toFunctor.map
                  ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z')) ≫
                s Z'.right) :=
          by rw [Category.assoc, htfac Z']
        _ =
            G₁.obj.toFunctor.map
                ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)) ≫
              (G₁.obj.toFunctor.map
                  ((Comma.idBaseStronglyCartesian p u).Q.map
                    ((Comma.pullbackUnit p u).map f.right)) ≫
                s Z'.right) :=
          by
          rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ←
            Functor.map_comp, ← Functor.map_comp, Comma.comp_toPullbackUnit]
        _ =
            (G₁.obj.toFunctor.map
                  ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z)) ≫
                s Z.right) ≫
              G₂.obj.toFunctor.map
                ((Comma.idBaseStronglyCartesian p u).Q.map
                  ((Comma.pullbackUnit p u).map f.right)) :=
          by rw [hσfib, Category.assoc]
        _ =
            (t Z ≫
                G₂.obj.toFunctor.map
                  ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z))) ≫
              G₂.obj.toFunctor.map
                ((Comma.idBaseStronglyCartesian p u).Q.map
                  ((Comma.pullbackUnit p u).map f.right)) :=
          by rw [htfac Z]
        _ =
            (t Z ≫ G₂.obj.toFunctor.map ((Comma.idBaseStronglyCartesian p u).Q.map f)) ≫
              G₂.obj.toFunctor.map
                ((Comma.idBaseStronglyCartesian p u).Q.map (Comma.toPullbackUnit p u Z')) :=
          by
          rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ←
            Functor.map_comp, ← Functor.map_comp, ← Comma.comp_toPullbackUnit]
    set τ₀ :
      (Comma.idBaseStronglyCartesian p u).Q ⋙ G₁.obj.toFunctor ⟶
        (Comma.idBaseStronglyCartesian p u).Q ⋙ G₂.obj.toFunctor :=
      { app := t, naturality := fun _ _ f => hnat f } with hτ₀
    refine
      ⟨InducedCategory.homMk
          { toNatTrans := Localization.Construction.natTransExtension τ₀
            isHomLift' := ?_ },
        ?_⟩
    · intro X
      obtain ⟨Z, rfl⟩ : ∃ Z, (Comma.idBaseStronglyCartesian p u).Q.obj Z = X :=
        ⟨_,
          (Localization.Construction.objEquiv (Comma.idBaseStronglyCartesian p u)).apply_symm_apply
            X⟩
      have hZ :
        (Comma.pullbackProj p u).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z) = Z.left :=
        Comma.pullbackProj_obj p u Z
      have happ :
        (Localization.Construction.natTransExtension τ₀).app
            ((Comma.idBaseStronglyCartesian p u).Q.obj Z) =
          t Z := by
        simp [hτ₀]
      change
        q.IsHomLift
          (𝟙 ((Comma.pullbackProj p u).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z)))
          ((Localization.Construction.natTransExtension τ₀).app
            ((Comma.idBaseStronglyCartesian p u).Q.obj Z))
      rw [hZ, happ]
      exact htlift Z
    · apply InducedCategory.hom_ext
      apply BasedNatTrans.ext
      apply NatTrans.ext
      funext x
      apply StrictPullback.Hom.ext
      · have hσx :
          (StrictPullback.structureFunctor u q).IsHomLift (𝟙 (p.obj x)) (σ.hom.toNatTrans.app x) :=
          σ.hom.isHomLift' x
        exact (StrictPullback.base_eq (𝟙 (p.obj x)) (σ.hom.toNatTrans.app x)).symm
      · change (Localization.Construction.natTransExtension τ₀).app _ = _
        have h1 :
          (Localization.Construction.natTransExtension τ₀).app
              ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) =
            t ((Comma.pullbackUnit p u).obj x) := by
          simp [hτ₀]
        rw [show
            (Localization.Construction.natTransExtension τ₀).app
                ((Comma.pullbackUnit p u ⋙ (Comma.idBaseStronglyCartesian p u).Q).obj x) =
              t ((Comma.pullbackUnit p u).obj x)
            from h1]
        have := hslift x
        have :
          q.IsHomLift (𝟙 (u.obj (p.obj x)))
            (𝟙
              (G₂.obj.toFunctor.obj
                ((Comma.idBaseStronglyCartesian p u).Q.obj
                  ((Comma.pullbackUnit p u).obj x)))) := by
          have hZ :
            (Comma.pullbackProj p u).obj
                ((Comma.idBaseStronglyCartesian p u).Q.obj ((Comma.pullbackUnit p u).obj x)) =
              u.obj (p.obj x) :=
            Comma.pullbackProj_obj p u _
          refine IsHomLift.id ?_
          rw [← hZ]
          exact Functor.congr_obj G₂.obj.w _
        have :=
          isStronglyCartesian_map_Q_toPullbackUnit p u q hu G₂.obj G₂.property
            ((Comma.pullbackUnit p u).obj x)
        have ht : q.IsHomLift (𝟙 (u.obj (p.obj x))) (t ((Comma.pullbackUnit p u).obj x)) :=
          htlift ((Comma.pullbackUnit p u).obj x)
        refine
          Functor.IsStronglyCartesian.ext q (((Comma.pullbackUnit p u).obj x).hom)
            (G₂.obj.toFunctor.map
              ((Comma.idBaseStronglyCartesian p u).Q.map
                (Comma.toPullbackUnit p u ((Comma.pullbackUnit p u).obj x))))
            (𝟙 (u.obj (p.obj x))) ?_
        rw [htfac ((Comma.pullbackUnit p u).obj x)]
        simp [Comma.toPullbackUnit_pullbackUnit, hs]

/-- Restriction along the unit is essentially surjective. -/
instance : (restrictAlongPullbackUnit p u q hu).EssSurj where
  mem_essImage H := by
    obtain ⟨⟨H, hw⟩, hsc⟩ := H
    change 𝒮 ⥤ StrictPullback u q at H
    have hw' : H ⋙ StrictPullback.structureFunctor u q = p := hw
    subst hw'
    set F : 𝒮 ⥤ 𝒯 := H ⋙ StrictPullback.pr u q with hFdef
    have hF : F ⋙ q = (H ⋙ StrictPullback.structureFunctor u q) ⋙ u := by
      rw [hFdef, Functor.assoc, StrictPullback.pr_comp_eq]
      rfl
    have hFsc :
      ∀ {x y : 𝒮} (α : x ⟶ y),
        (H ⋙ StrictPullback.structureFunctor u q).IsStronglyCartesian
            ((H ⋙ StrictPullback.structureFunctor u q).map α) α →
          q.IsStronglyCartesian (((H ⋙ StrictPullback.structureFunctor u q) ⋙ u).map α)
            (F.map α) := by
      intro x y α hα
      have h1 := hsc.map_isStronglyCartesian _ α hα
      have h2 := StrictPullback.isStronglyCartesian_fib_over (H.map α) h1
      have h3 := Functor.IsStronglyCartesian.of_eqToHom_comp (p := q) _ _ _ h2
      exact Functor.IsStronglyCartesian.of_comp_eqToHom (p := q) _ _ _ h3
    exact
      ⟨⟨leftToRightBased _ u q F hF hFsc, isFibredOneMorphism_leftToRight _ u q F hF hu hFsc⟩,
        ⟨InducedCategory.isoMk (counitIso _ u q F hF hFsc)⟩⟩

end PullbackAdjunction

/-- **The pullback of a fibred category along `u` is adjoint to the pushforward along `u`**
(Stacks 04WI). Let `u : 𝒞 ⥤ 𝒟` be a functor, let `p : 𝒮 ⥤ 𝒞` and `q : 𝒯 ⥤ 𝒟` be fibred
categories, assume `𝒞` has nonempty finite limits and that `u` commutes with nonempty finite
limits. Then the morphism category `Mor_{Fib/𝒞}(𝒮, u^p 𝒯)` of 1-morphisms `𝒮 ⟶ u^p 𝒯` of fibred
categories over `𝒞` is canonically equivalent to the morphism category `Mor_{Fib/𝒟}(u_p 𝒮, 𝒯)` of
1-morphisms `u_p 𝒮 ⟶ 𝒯` of fibred categories over `𝒟`, where `u^p 𝒯` is the pushforward of `𝒯`
along `u` (Stacks 04WB) and `u_p 𝒮` is the pullback of `𝒮` along `u` (Stacks 04WG). Each morphism
category is realized as the full subcategory of the category of based functors on those which
preserve strongly cartesian morphisms, its morphisms being the morphisms of functors whose
components lie over identities of the base. -/
@[stacks 04WI]
noncomputable def equivalenceIsFibredOneMorphismStrictPullbackPullbackLocalization {𝒞 : Type u₁}
    [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] {𝒮 : Type u₃} [Category.{v₃} 𝒮] {𝒯 : Type u₄}
    [Category.{v₄} 𝒯] (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒞) (q : 𝒯 ⥤ 𝒟) [p.IsFibered] [q.IsFibered]
    [HasNonemptyFiniteLimits 𝒞]
    (hu :
      ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
        Limits.PreservesLimitsOfShape J u) :
    ObjectProperty.FullSubcategory
        (fun G :
            BasedCategory.ofFunctor p ⥤ᵇ
              BasedCategory.ofFunctor (StrictPullback.structureFunctor u q) =>
          Functor.IsFibredOneMorphism p (StrictPullback.structureFunctor u q) G.toFunctor) ≌
      ObjectProperty.FullSubcategory
        (fun G : BasedCategory.ofFunctor (Comma.pullbackProj p u) ⥤ᵇ BasedCategory.ofFunctor q =>
          Functor.IsFibredOneMorphism (Comma.pullbackProj p u) q G.toFunctor) :=
  haveI : (PullbackAdjunction.restrictAlongPullbackUnit p u q hu).IsEquivalence := {}
  (PullbackAdjunction.restrictAlongPullbackUnit p u q hu).asEquivalence.symm

end CategoryTheory

end
