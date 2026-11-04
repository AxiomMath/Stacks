module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Logic.Equiv.Fin.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The product of a simplicial set with a simplicial object

For a simplicial set `U` and a simplicial object `V` of a category with coproducts, the product
`U × V` is the simplicial object `n ↦ ∐_{u ∈ U_n} V_n`. This file constructs it, shows that it
corepresents families of morphisms indexed by the simplices of `U`, and describes morphisms out of
`U × V` when `U` is a standard simplex.
-/

/-!
## Families of morphisms indexed by the simplices of a simplicial set

Let `U` be a simplicial set and let `V`, `W` be simplicial objects of a category `C`.
[Stacks, Tag 017B] displays the set of families of morphisms `f_{n, u} : V_n ⟶ W_n`, indexed by the
integers `n ≥ 0` and the `n`-simplices `u ∈ U_n`, such that
`f_{m, U(φ)(u)} ∘ V(φ) = W(φ) ∘ f_{n, u}` for every `φ : [m] → [n]`.

Such a family is a morphism of functors on the category of elements of `U`: an object of
`U.Elements` is a pair `(n, u)` with `u ∈ U_n`, a morphism `(n, u) ⟶ (m, u')` is a `φ : [m] → [n]`
with `U(φ)(u) = u'`, and the naturality square of a natural transformation `f : π U ⋙ V ⟶ π U ⋙ W`
at that morphism is the displayed equation. So the displayed set is the hom-set `π U ⋙ V ⟶ π U ⋙ W`
of the functor category `U.Elements ⥤ C`, and its elements are described by the faces and the
degeneracies alone, these generating `Δ`.

### Main results

* `SSet.existsUnique_hom_app_eq`: a family of morphisms `d n u : V_n ⟶ W_n`, indexed by `n : ℕ` and
  `u ∈ U_n`, commuting with the face maps and with the degeneracy maps of `U`, `V` and `W`, is the
  family of components of a unique element of the set of [Stacks, Tag 017B].

### References

* [Stacks, Tag 017B](https://stacks.math.columbia.edu/tag/017B)
-/

section

open CategoryTheory Opposite Simplicial

universe w v u

@[expose] public section

namespace SSet

variable {C : Type u} [Category.{v} C]

section

variable (U : SSet.{w}) {V W : SimplicialObject C}
  (d : ∀ n : ℕ, U.obj (op ⦋n⦌) → (V.obj (op ⦋n⦌) ⟶ W.obj (op ⦋n⦌)))

/-- The property of a morphism `φ : x ⟶ y` of `Δ` that the family `d` satisfies the equation of
[Stacks, Tag 017B] at `φ`, namely `f_{x, U(φ)(u)} ∘ V(φ) = W(φ) ∘ f_{y, u}` for every simplex
`u ∈ U_y`.

This is not an instance of `CategoryTheory.MorphismProperty.naturalityProperty`, whose two sides
are `F₁.map φ ≫ app y` and `app x ≫ F₂.map φ` for a family `app` indexed by the objects of the
base category alone: here the family is indexed by the simplices of `U` as well, and the simplex
is transported, `d x.len (U.map φ.op u)` against `d y.len u`. -/
private def naturalityProperty : MorphismProperty SimplexCategory := fun x y φ =>
  ∀ u : U.obj (op y), V.map φ.op ≫ d x.len (U.map φ.op u) = d y.len u ≫ W.map φ.op

/-- Membership in `naturalityProperty U d` is the equation of [Stacks, Tag 017B]. -/
private theorem naturalityProperty_iff {x y : SimplexCategory} (φ : x ⟶ y) :
    naturalityProperty U d φ ↔
      ∀ u : U.obj (op y), V.map φ.op ≫ d x.len (U.map φ.op u) = d y.len u ≫ W.map φ.op :=
  Iff.rfl

/-- The equation of [Stacks, Tag 017B] holds for identities, and for a composite as soon as it
holds for the two factors. -/
private theorem naturalityProperty_isMultiplicative :
    (naturalityProperty U d).IsMultiplicative where
  id_mem x u := by simp
  comp_mem {x y z} φ ψ hφ hψ u := by
    have harg : U.map (φ ≫ ψ).op u = U.map φ.op (U.map ψ.op u) := by simp
    rw [harg, op_comp, Functor.map_comp, Functor.map_comp, Category.assoc,
      (naturalityProperty_iff U d φ).mp hφ (U.map ψ.op u), ← Category.assoc,
      (naturalityProperty_iff U d ψ).mp hψ u, Category.assoc]

/-- A family commuting with the faces and the degeneracies commutes with every morphism of `Δ`. -/
private theorem naturality_of_δ_σ
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)) (u : U.obj (op ⦋n + 1⦌)),
      V.δ i ≫ d n (U.δ i u) = d (n + 1) u ≫ W.δ i)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)) (u : U.obj (op ⦋n⦌)),
      V.σ i ≫ d (n + 1) (U.σ i u) = d n u ≫ W.σ i)
    {x y : SimplexCategory} (φ : x ⟶ y) (u : U.obj (op y)) :
    V.map φ.op ≫ d x.len (U.map φ.op u) = d y.len u ≫ W.map φ.op := by
  have := naturalityProperty_isMultiplicative U d
  have h : naturalityProperty U d = ⊤ :=
    SimplexCategory.morphismProperty_eq_top _ (fun {n} i => hδ n i) (fun {n} i => hσ n i)
  exact (naturalityProperty_iff U d φ).mp (h ▸ MorphismProperty.top_apply φ) u

end

/-- **Stacks 017B**.
Let `U` be a simplicial set, let `V`, `W` be simplicial objects of a category `C`, and let
`d n u : V_n ⟶ W_n` be a family of morphisms, indexed by `n : ℕ` and by the `n`-simplices `u` of
`U`, which commutes with the face maps and with the degeneracy maps. Then `d` is the family of
components of a unique element of the displayed set of families
`(f_{n, u} : V_n ⟶ W_n)_{n ≥ 0, u ∈ U_n}` satisfying `f_{m, U(φ)(u)} ∘ V(φ) = W(φ) ∘ f_{n, u}` for
every `φ : [m] → [n]`, that set being the hom-set `π U ⋙ V ⟶ π U ⋙ W` of functors on the category
of elements of `U`. -/
@[stacks 017B "the displayed set is the hom-set `π U ⋙ V ⟶ π U ⋙ W` over the category of \
  elements of `U`; here its elements are described by the faces and the degeneracies"]
public theorem existsUnique_hom_app_eq (U : SSet.{w}) {V W : SimplicialObject C}
    (d : ∀ n : ℕ, U.obj (op ⦋n⦌) → (V.obj (op ⦋n⦌) ⟶ W.obj (op ⦋n⦌)))
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)) (u : U.obj (op ⦋n + 1⦌)),
      V.δ i ≫ d n (U.δ i u) = d (n + 1) u ≫ W.δ i)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)) (u : U.obj (op ⦋n⦌)),
      V.σ i ≫ d (n + 1) (U.σ i u) = d n u ≫ W.σ i) :
    ∃! f : CategoryOfElements.π U ⋙ V ⟶ CategoryOfElements.π U ⋙ W,
      ∀ (n : ℕ) (u : U.obj (op ⦋n⦌)), f.app ⟨op ⦋n⦌, u⟩ = d n u := by
  refine ⟨{ app := fun p => d p.1.unop.len p.2, naturality := ?_ }, fun n u => rfl, ?_⟩
  · intro p q g
    have h := naturality_of_δ_σ U d hδ hσ g.1.unop p.2
    rw [Quiver.Hom.op_unop, g.2] at h
    exact h
  · intro f hf
    ext ⟨⟨n⟩, u⟩
    exact hf n.len u

end SSet

end

end

/-!
## The product of a simplicial set with a simplicial object

Let `C` be a category, let `U` be a simplicial set and let `V` be a simplicial object of `C`. When
the coproduct of `U_n`-many copies of `V_n` exists in `C` for every `n`, the *product* `U × V` is
the simplicial object of `C` with `(U × V)_n = ∐_{u ∈ U_n} V_n`, whose structure map attached to
`φ : [m] → [n]` sends the component indexed by `u ∈ U_n` into the component indexed by
`U(φ)(u) ∈ U_m` by `V(φ)` [Stacks, Tag 017C]. The construction uses nothing about the simplex
category: for functors `V : J ⥤ C` and `U : J ⥤ Type w` out of any category `J` the same formula
defines the *copower of `V` by `U`*, the functor `j ↦ ∐_{u ∈ U j} V j`, and the product of a
simplicial set with a simplicial object is its value at `J = Δᵒᵖ`.

### Main definitions

* `CategoryTheory.Functor.copower`: the copower `V.copower U : J ⥤ C` of `V : J ⥤ C` by
  `U : J ⥤ Type w`, with `(V.copower U).obj j = ∐ (fun _ : U.obj j => V.obj j)`. For
  `J = SimplexCategoryᵒᵖ`, `U : SSet` and `V : SimplicialObject C` this is the product `U × V` of
  [Stacks, Tag 017C], on the nose in each degree.

### References

* [Stacks, Tag 017C](https://stacks.math.columbia.edu/tag/017C)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

namespace CategoryTheory.Functor

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]

/-- **Stacks 017C**.
The copower of `V : J ⥤ C` by `U : J ⥤ Type w`, defined whenever the coproduct of `U j`-many copies
of `V j` exists for every `j`: the functor `j ↦ ∐_{u ∈ U j} V j` whose value on `f : i ⟶ j` sends
the component indexed by `u ∈ U i` into the component indexed by `U f u ∈ U j` by `V f`.

For `J = SimplexCategoryᵒᵖ`, a simplicial set `U` and a simplicial object `V` of `C` this is the
product `U × V` of [Stacks, Tag 017C]: `(U × V)_n = ∐_{u ∈ U_n} V_n`, and for `φ : [m] → [n]` the
component `V_n` indexed by `u ∈ U_n` maps to the component `V_m` indexed by `U(φ)(u) ∈ U_m` via
`V(φ)`. It exists in particular when `C` has the coproduct of any two objects and every `U_n` is
finite nonempty. -/
@[stacks 017C "stated for an arbitrary index category `J` in place of `SimplexCategoryᵒᵖ`, \
  and under the source's looser hypothesis that the coproducts exist",
  simps,
  implicit_reducible,
  sga "4 IV 4.3" "more general"]
public noncomputable def copower (V : J ⥤ C) (U : J ⥤ Type w)
    [∀ j, HasCoproduct fun _ : U.obj j => V.obj j] : J ⥤ C where
  obj j := ∐ fun _ : U.obj j => V.obj j
  map f := Sigma.map' (U.map f) fun _ => V.map f
  map_id j := by
    apply Sigma.hom_ext
    intro u
    simp
  map_comp f g := by
    apply Sigma.hom_ext
    intro u
    simp

section copowerMap

variable {V V' V'' : J ⥤ C} {U U' U'' : J ⥤ Type w}
  [∀ j, HasCoproduct fun _ : U.obj j => V.obj j] [∀ j, HasCoproduct fun _ : U'.obj j => V'.obj j]
  [∀ j, HasCoproduct fun _ : U''.obj j => V''.obj j]

/-- The injection at `u` followed by `copower.map f` is `V.map f` followed by the injection at
`U.map f u`. -/
private lemma ι_comp_copower_map {i j : J} (f : i ⟶ j) (u : U.obj i) :
    Sigma.ι (fun _ : U.obj i => V.obj i) u ≫ (V.copower U).map f =
      V.map f ≫ Sigma.ι (fun _ : U.obj j => V.obj j) (U.map f u) :=
  Sigma.ι_comp_map' _ _ u

/-- The morphism `V.copower U ⟶ V'.copower U'` induced by `b : V ⟶ V'` and `a : U ⟶ U'`: its
component at `j` carries the summand indexed by `u ∈ U j` into the summand indexed by `a j u`
by `b j`. -/
noncomputable def copowerMap (b : V ⟶ V') (a : U ⟶ U') : V.copower U ⟶ V'.copower U' where
  app j := Sigma.map' (a.app j) fun _ => b.app j
  naturality i j f := by
    refine Sigma.hom_ext _ _ fun u => ?_
    simp [NatTrans.naturality_apply a f u, reassoc_of% b.naturality f]

/-- The component of `copowerMap b a` at `j` carries the summand indexed by `u` by `b j` into
the summand indexed by `a j u`. -/
@[reassoc (attr := simp)]
lemma ι_copowerMap_app (b : V ⟶ V') (a : U ⟶ U') (j : J) (u : U.obj j) :
    Sigma.ι (fun _ : U.obj j => V.obj j) u ≫ (copowerMap b a).app j =
      b.app j ≫ Sigma.ι (fun _ : U'.obj j => V'.obj j) (a.app j u) :=
  Sigma.ι_comp_map' _ _ u

variable (V U) in
/-- `copowerMap` carries a pair of identities to the identity. -/
@[simp]
lemma copowerMap_id : copowerMap (𝟙 V) (𝟙 U) = 𝟙 (V.copower U) := by
  ext j
  refine Sigma.hom_ext _ _ fun u => ?_
  simp

/-- `copowerMap` is compatible with composition. -/
@[reassoc (attr := simp)]
lemma copowerMap_comp (b : V ⟶ V') (b' : V' ⟶ V'') (a : U ⟶ U') (a' : U' ⟶ U'') :
    copowerMap b a ≫ copowerMap b' a' = copowerMap (b ≫ b') (a ≫ a') := by
  ext j
  refine Sigma.hom_ext _ _ fun u => ?_
  simp

end copowerMap

end CategoryTheory.Functor

end

end

/-!
## The product of a simplicial set with a simplicial object corepresents families of morphisms

Let `C` be a category, let `U` be a simplicial set and let `V` be a simplicial object of `C`,
and assume the product `U × V` of [Stacks, Tag 017C] exists, with
`(U × V)_n = ∐_{u ∈ U_n} V_n`. [Stacks, Tag 017D] says that the covariant functor
`W ↦ Mor_{Simp(C)}(U × V, W)` is canonically isomorphic to the covariant functor sending `W`
to the set of Equation [Stacks, Tag 017B] of families `(f_{n, u} : V_n ⟶ W_n)` with
`f_{m, U(φ)(u)} ∘ V(φ) = W(φ) ∘ f_{n, u}` for every `φ : [m] → [n]`.

That set is the hom-set `π U ⋙ V ⟶ π U ⋙ W` of the category of functors on the category of
elements of `U`, and the functor in `W` is restriction along `π U : U.Elements ⥤ Δᵒᵖ`
followed by `coyoneda` at `π U ⋙ V`. So the lemma says that this functor is corepresented by
`U × V`, and "canonically" says which bijection: a morphism `g : U × V ⟶ W` goes to the family
of its restrictions `f_{n, u} = Sigma.ι _ u ≫ g_n` to the components of the coproduct.

### Main results

* `CategoryTheory.Functor.exists_corepresentableBy_copower`: the functor
  `W ↦ (π U ⋙ V ⟶ π U ⋙ W)` is corepresented by the copower `V.copower U`, by the bijection
  sending `g` to the family of its restrictions to the components of the coproducts.

### References

* [Stacks, Tag 017D](https://stacks.math.columbia.edu/tag/017D)
-/

section

open Opposite CategoryTheory.Limits

universe w v u v' u'

namespace CategoryTheory.Functor

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]

/-- **Stacks 017D**.
Let `V : J ⥤ C` and `U : J ⥤ Type w` be such that the coproducts defining the copower
`V.copower U` exist. Then the covariant functor sending `W : J ⥤ C` to the hom-set
`π U ⋙ V ⟶ π U ⋙ W` of functors on the category of elements of `U` is corepresented by
`V.copower U`, by the bijection which sends `g : V.copower U ⟶ W` to the family of its
restrictions `Sigma.ι _ u ≫ g.app j : V.obj j ⟶ W.obj j` to the components of the coproducts.

For `J = SimplexCategoryᵒᵖ`, a simplicial set `U` and simplicial objects `V`, `W` of `C` this
says that the functor `W ↦ Mor_{Simp(C)}(U × V, W)` is canonically isomorphic to the functor
sending `W` to the set of Equation [Stacks, Tag 017B] of families
`(f_{n, u} : V_n ⟶ W_n)_{n ≥ 0, u ∈ U_n}` with `f_{m, U(φ)(u)} ∘ V(φ) = W(φ) ∘ f_{n, u}`, the
isomorphism sending `g : U × V ⟶ W` to `f_{n, u} = Sigma.ι _ u ≫ g_n`. -/
@[stacks 017D "stated for an arbitrary index category `J` in place of `SimplexCategoryᵒᵖ`, \
  under the source's looser hypothesis that the coproducts exist, and with the canonical \
  isomorphism pinned by its components; the set of Equation 017B is the hom-set \
  `π U ⋙ V ⟶ π U ⋙ W` over the category of elements of `U`",
  sga "3 I 1.8" "(1.8.2)",
  sga "4 IV 4.3" "For each set I"]
public theorem exists_corepresentableBy_copower (V : J ⥤ C) (U : J ⥤ Type w)
    [∀ j, HasCoproduct fun _ : U.obj j => V.obj j] :
    ∃ h : ((whiskeringLeft U.Elements J C).obj (CategoryOfElements.π U) ⋙
        coyoneda.obj (op (CategoryOfElements.π U ⋙ V))).CorepresentableBy (V.copower U),
      ∀ (W : J ⥤ C) (g : V.copower U ⟶ W) (j : J) (u : U.obj j),
        (h.homEquiv g).app ⟨j, u⟩ =
          Sigma.ι (fun _ : U.obj j => V.obj j) u ≫ g.app j := by
  refine ⟨⟨fun {W} => ?_, ?_⟩, ?_⟩
  · refine Equiv.mk
      (fun g => { app := fun p => Sigma.ι (fun _ : U.obj p.1 => V.obj p.1) p.2 ≫ g.app p.1
                  naturality := ?_ })
      (fun f => { app := fun j =>
                    Limits.Sigma.desc fun u =>
                      (f.app ⟨j, u⟩ : V.obj j ⟶ W.obj j)
                  naturality := ?_ }) ?_ ?_
    · intro p q ψ
      obtain ⟨φ, hφ⟩ := ψ
      obtain ⟨j, u⟩ := p
      obtain ⟨j', u'⟩ := q
      dsimp at hφ
      induction hφ
      change V.map φ ≫ _ = (_ ≫ g.app j) ≫ W.map φ
      rw [← Category.assoc, ← ι_comp_copower_map, Category.assoc, g.naturality, Category.assoc]
    · intro j j' φ
      apply Limits.Sigma.hom_ext
      intro u
      rw [reassoc_of% ι_comp_copower_map, Sigma.ι_desc, Sigma.ι_desc_assoc]
      exact f.naturality (X := (⟨j, u⟩ : U.Elements)) (Y := ⟨j', U.map φ u⟩) ⟨φ, rfl⟩
    · intro g
      ext j
      exact Limits.Sigma.hom_ext _ _ fun u => Limits.Sigma.ι_desc _ _
    · exact fun f => NatTrans.ext (funext fun ⟨_, _⟩ => Limits.Sigma.ι_desc _ _)
  · intro W W' k g
    exact NatTrans.ext (funext fun ⟨_, _⟩ => (Category.assoc _ _ _).symm)
  · intro W g j u
    rfl

end CategoryTheory.Functor

end

/-!
## Products with simplicial sets

Let `C` be a category in which the coproduct of any two objects exists, let `U` be a
simplicial set all of whose simplex sets are finite and nonempty, and let `V` be a simplicial
object of `C`. Then the coproducts `∐_{u ∈ U_n} V_n` exist, so the product `U × V` of
[Stacks, Tag 017C] exists; it is the copower `V.copower U`. This section shows that the product
is a functor in the pair `(U, V)` and constructs the canonical projection onto `V`.

### Main definitions

* `SSet.isFSSet`: the property of a simplicial set that each of its simplex sets is finite and
  nonempty.
* `SSet.FSSets`: the full subcategory of simplicial sets with that property.
* `CategoryTheory.Functor.copowerProj`: the canonical projection `V.copower U ⟶ V`, the
  identity of `V j` on each summand of `(V.copower U) j`; for `J = SimplexCategoryᵒᵖ` this is the
  projection `U × V ⟶ V`.
* `CategoryTheory.SimplicialObject.prodFunctor`: the functor
  `FSSets × SimplicialObject C ⥤ SimplicialObject C` sending `(U, V)` to `U × V`.

### Main results

* `CategoryTheory.Limits.hasCoproduct_of_finite_nonempty`: a family indexed by a finite
  nonempty type has a coproduct as soon as binary coproducts exist, with no initial object.
* `CategoryTheory.Functor.copowerMap_comp_copowerProj`: the projection is natural in `(U, V)`.

### References

* [Stacks, Tag 017C](https://stacks.math.columbia.edu/tag/017C)
* [Stacks, Tag 017E](https://stacks.math.columbia.edu/tag/017E)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

section Sum

variable {α β : Type w} (f : α ⊕ β → C)
  [HasCoproduct (f ∘ Sum.inl)] [HasCoproduct (f ∘ Sum.inr)]

/-- The cofan over `f : α ⊕ β → C` whose point is the binary coproduct
`∐ (f ∘ Sum.inl) ⨿ ∐ (f ∘ Sum.inr)` and whose injection at `Sum.inl a`, resp. `Sum.inr b`, is
the coproduct injection at `a`, resp. `b`, followed by `coprod.inl`, resp. `coprod.inr`. -/
@[implicit_reducible]
noncomputable def cofanSum : Cofan f :=
  Cofan.mk (∐ (f ∘ Sum.inl) ⨿ ∐ (f ∘ Sum.inr))
    (fun
      | Sum.inl a => Sigma.ι (f ∘ Sum.inl) a ≫ coprod.inl
      | Sum.inr b => Sigma.ι (f ∘ Sum.inr) b ≫ coprod.inr)

/-- The injection of `cofanSum f` at `Sum.inl a` is the injection of `∐ (f ∘ Sum.inl)` at `a`
followed by `coprod.inl`. -/
@[simp] lemma cofanSum_inj_inl (a : α) :
    (cofanSum f).inj (Sum.inl a) = Sigma.ι (f ∘ Sum.inl) a ≫ coprod.inl := rfl

/-- The injection of `cofanSum f` at `Sum.inr b` is the injection of `∐ (f ∘ Sum.inr)` at `b`
followed by `coprod.inr`. -/
@[simp] lemma cofanSum_inj_inr (b : β) :
    (cofanSum f).inj (Sum.inr b) = Sigma.ι (f ∘ Sum.inr) b ≫ coprod.inr := rfl

/-- `cofanSum f` is a colimit cofan, hence computes the coproduct of `f : α ⊕ β → C`. -/
noncomputable def cofanSumIsColimit : IsColimit (cofanSum f) :=
  Cofan.IsColimit.mk _
    (fun s => coprod.desc (Sigma.desc fun a => s.inj (Sum.inl a))
      (Sigma.desc fun b => s.inj (Sum.inr b)))
    (fun s x => by cases x <;> simp [coprod.inl_desc, coprod.inr_desc])
    (fun s m hm => coprod.hom_ext
      (Sigma.hom_ext _ _ fun a => by simpa [coprod.inl_desc] using hm (Sum.inl a))
      (Sigma.hom_ext _ _ fun b => by simpa [coprod.inr_desc] using hm (Sum.inr b)))

/-- If `C` has binary coproducts and the restrictions of `f : α ⊕ β → C` to the two summands
have coproducts, then `f` has a coproduct. -/
theorem hasCoproduct_sum : HasCoproduct f :=
  ⟨⟨⟨_, cofanSumIsColimit f⟩⟩⟩

end Sum

/-- Every family `f : Fin (n + 1) → C` has a coproduct as soon as `C` has binary coproducts;
the index type is nonempty, so no initial object is needed. -/
theorem hasCoproduct_fin_succ (n : ℕ) (f : Fin (n + 1) → C) : HasCoproduct f := by
  induction n with
  | zero =>
    have : Unique (Fin (0 + 1)) := Fin.instUnique
    exact hasCoproduct_unique f
  | succ k ih =>
    let e : Fin (k + 1) ⊕ Fin 1 ≃ Fin (k + 1 + 1) := finSumFinEquiv
    let g : Fin (k + 1) ⊕ Fin 1 → C := f ∘ e
    have : HasCoproduct (g ∘ Sum.inl) := ih _
    have : HasCoproduct (g ∘ Sum.inr) := hasCoproduct_unique _
    have : HasCoproduct g := hasCoproduct_sum g
    exact hasCoproduct_of_equiv_of_iso g f e.symm fun j => eqToIso (by simp [g, e])

/-- For a finite nonempty index type `ι`, every family `f : ι → C` has a coproduct as soon as
`C` has binary coproducts; no initial object is needed. -/
instance (priority := 100) hasCoproduct_of_finite_nonempty {ι : Type w} [Finite ι] [Nonempty ι]
    (f : ι → C) : HasCoproduct f := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  cases n with
  | zero => exact (e (Classical.arbitrary ι)).elim0
  | succ m =>
    have : HasCoproduct fun j : Fin (m + 1) => f (e.symm j) := hasCoproduct_fin_succ m _
    exact hasCoproduct_of_equiv_of_iso (fun j : Fin (m + 1) => f (e.symm j)) f e
      fun j => eqToIso (by simp)

end CategoryTheory.Limits

namespace SSet

/-- The property of a simplicial set that each of its simplex sets is finite and nonempty. -/
def isFSSet : ObjectProperty SSet.{w} :=
  fun U => (∀ n, Finite (U.obj n)) ∧ (∀ n, Nonempty (U.obj n))

/-- The full subcategory of simplicial sets all of whose simplex sets are finite and
nonempty. -/
abbrev FSSets : Type (w + 1) := isFSSet.{w}.FullSubcategory

/-- Each simplex set of an object of `FSSets` is finite. -/
instance (U : FSSets.{w}) (n : SimplexCategoryᵒᵖ) : Finite (U.obj.obj n) := U.property.left n

/-- Each simplex set of an object of `FSSets` is nonempty. -/
instance (U : FSSets.{w}) (n : SimplexCategoryᵒᵖ) : Nonempty (U.obj.obj n) :=
  U.property.right n

end SSet

namespace CategoryTheory.Functor

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]

/-- **Stacks 017E** (2).
The canonical projection `V.copower U ⟶ V`, whose component at `j` is the identity of `V j` on
each summand of `(V.copower U) j = ∐_{u ∈ U j} V j`. For `J = SimplexCategoryᵒᵖ`, a simplicial
set `U` and a simplicial object `V` this is the projection `U × V ⟶ V`. -/
@[stacks 017E "(2); stated for an arbitrary index category `J` in place of \
  `SimplexCategoryᵒᵖ`, and under the looser hypothesis that the coproducts exist"]
noncomputable def copowerProj (V : J ⥤ C) (U : J ⥤ Type w)
    [∀ j, HasCoproduct fun _ : U.obj j => V.obj j] : V.copower U ⟶ V where
  app j := Sigma.desc fun _ => 𝟙 (V.obj j)
  naturality i j f := by
    refine Sigma.hom_ext _ _ fun u => ?_
    simp

/-- The projection `copowerProj` is natural in `(U, V)`: for all `b : V ⟶ V'` and `a : U ⟶ U'`,
`copowerMap b a ≫ V'.copowerProj U' = V.copowerProj U ≫ b`. -/
@[reassoc]
lemma copowerMap_comp_copowerProj {V V' : J ⥤ C} {U U' : J ⥤ Type w}
    [∀ j, HasCoproduct fun _ : U.obj j => V.obj j] [∀ j, HasCoproduct fun _ : U'.obj j => V'.obj j]
    (b : V ⟶ V') (a : U ⟶ U') :
    copowerMap b a ≫ V'.copowerProj U' = V.copowerProj U ≫ b := by
  ext j
  refine Sigma.hom_ext _ _ fun u => ?_
  simp [copowerProj]

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

/-- **Stacks 017E** (1).
The functor `FSSets × SimplicialObject C ⥤ SimplicialObject C` sending a pair `(U, V)` to the
product `U × V = V.copower U` and a pair of morphisms `(a, b)` to `Functor.copowerMap b a`. -/
@[stacks 017E "(1)"]
noncomputable def prodFunctor : SSet.FSSets.{w} × SimplicialObject C ⥤ SimplicialObject C where
  obj := fun ⟨U, V⟩ => V.copower U.obj
  map := fun ⟨a, b⟩ => Functor.copowerMap b a.hom
  map_id := fun ⟨U, V⟩ => Functor.copowerMap_id V U.obj
  map_comp := fun ⟨a, b⟩ ⟨a', b'⟩ => (Functor.copowerMap_comp b b' a.hom a'.hom).symm

end CategoryTheory.SimplicialObject

end

end

/-!
## Morphisms out of the product of an object with a standard simplex

Let `C` be a category, let `X` be an object of `C` and let `k ≥ 0`, and assume the coproducts
forming the product `X × Δ[k]` of the standard `k`-simplex with the constant simplicial object
`X` exist in `C`. [Stacks, Tag 017F] says that for every simplicial object `V` of `C` the map
`Mor_{Simp(C)}(X × Δ[k], V) → Mor_C(X, V_k)` restricting `γ` to the component of `(X × Δ[k])_k`
indexed by `id_[k]` is a bijection, and that the same holds for an `n`-truncated simplicial
object `W` with `n ≥ k`, the source then being `Mor_{Simp_n(C)}(sk_n (X × Δ[k]), W)`.

Both bijections have the same inverse: `f : X ⟶ V_k` goes to the morphism whose component at
level `m` sends the summand indexed by `α : [m] → [k]` via `f ≫ V(α)`.

### Main definitions

* `CategoryTheory.SimplicialObject.constProdStd`: the product `X × Δ[k]`, for `X` a constant
  simplicial object, the standard `k`-simplex being the representable `yoneda.obj ⦋k⦌`.
* `CategoryTheory.SimplicialObject.constProdStd.phi`, `constProdStd.phiTrunc`: the restriction
  maps `Mor(X × Δ[k], V) → Mor(X, V_k)` and `Mor(sk_n (X × Δ[k]), W) → Mor(X, W_k)`.
* `CategoryTheory.SimplicialObject.constProdStd.psi`, `constProdStd.psiTrunc`: their inverses.

### Main results

* `CategoryTheory.SimplicialObject.constProdStd.phi_bijective`: `phi` is a bijection.
* `CategoryTheory.SimplicialObject.constProdStd.phi_trunc_bijective`: `phiTrunc` is a bijection
  for every `n ≥ k`.

### References

* [Stacks, Tag 017F](https://stacks.math.columbia.edu/tag/017F)
-/

section

@[expose] public section

open CategoryTheory SimplexCategory Simplicial Limits

namespace CategoryTheory.SimplicialObject

noncomputable section
variable {C : Type*} [Category C]

variable (X : C) (k : ℕ)
variable [∀ (n : SimplexCategoryᵒᵖ),
  HasCoproduct (fun (_ : (yoneda.obj ⦋k⦌).obj n) => ((SimplicialObject.const C).obj X).obj n)]

/-- The product `X × Δ[k]`, where `X` is viewed as the constant simplicial object and the
standard `k`-simplex `Δ[k]_n = Mor_Δ([n], [k])` is the representable functor `yoneda.obj ⦋k⦌`.
Explicitly, `(X × Δ[k])_n = ∐_{α ∈ Mor_Δ([n], [k])} X`. -/
abbrev constProdStd : SimplicialObject C :=
  ((SimplicialObject.const C).obj X).copower (yoneda.obj ⦋k⦌)

namespace constProdStd

/-- The coproduct inclusion `ι_{id_[k]} : X ⟶ (X × Δ[k])_k` of the component indexed
by `id_[k] ∈ Δ[k]_k = Mor_Δ([k],[k])`. -/
def incl : X ⟶ (constProdStd X k).obj (Opposite.op ⦋k⦌) :=
  Sigma.ι (fun _ : (yoneda.obj ⦋k⦌).obj (Opposite.op ⦋k⦌) =>
    ((SimplicialObject.const C).obj X).obj (Opposite.op ⦋k⦌)) (𝟙 ⦋k⦌)

/-- The restriction map `Φ : Mor_{Simp(C)}(X × Δ[k], V) → Mor_C(X, V_k)`,
`Φ(γ) = γ_k ∘ ι_{id_[k]}`. -/
def phi (V : SimplicialObject C) (γ : constProdStd X k ⟶ V) :
    X ⟶ V.obj (Opposite.op ⦋k⦌) :=
  incl X k ≫ γ.app (Opposite.op ⦋k⦌)

/-- The object `[k]` of the truncated simplex category `Δ_{≤ n}`, for `k ≤ n`. -/
abbrev truncObjK (n : ℕ) (hkn : k ≤ n) : SimplexCategory.Truncated n :=
  ⟨⦋k⦌, by simpa using hkn⟩

omit [∀ (n : SimplexCategoryᵒᵖ),
  HasCoproduct (fun (_ : (yoneda.obj ⦋k⦌).obj n) => ((SimplicialObject.const C).obj X).obj n)] in
/-- The `n`-truncation of a simplicial object `Y` is the composite of `Y` with the inclusion
`Δ_{≤ n} ⟶ Δ`. -/
def truncationObjIso (n : ℕ) (Y : SimplicialObject C) :
    (SimplicialObject.truncation n).obj Y ≅ (Truncated.inclusion n).op ⋙ Y :=
  Iso.refl _

/-- The coproduct inclusion `ι_{id_[k]} : X ⟶ (sk_n (X × Δ[k]))_k` of the component indexed by
`id_[k]`, for `k ≤ n`. -/
def inclTrunc (n : ℕ) (hkn : k ≤ n) :
    X ⟶ ((Truncated.inclusion n).op ⋙ constProdStd X k).obj (Opposite.op (truncObjK k n hkn)) :=
  Sigma.ι (fun (_ : (yoneda.obj ⦋k⦌).obj
      ((Truncated.inclusion n).op.obj (Opposite.op (truncObjK k n hkn)))) =>
    ((SimplicialObject.const C).obj X).obj
      ((Truncated.inclusion n).op.obj (Opposite.op (truncObjK k n hkn))))
    (𝟙 ((Truncated.inclusion n).obj (truncObjK k n hkn)))

/-- The restriction map `Φ_n : Mor_{Simp_n(C)}(sk_n (X × Δ[k]), W) → Mor_C(X, W_k)` for an
`n`-truncated simplicial object `W` and `k ≤ n`, given by `Φ_n(γ) = γ_k ∘ ι_{id_[k]}`. -/
def phiTrunc (n : ℕ) (hkn : k ≤ n) (W : SimplicialObject.Truncated C n)
    (γ : (SimplicialObject.truncation n).obj (constProdStd X k) ⟶ W) :
    X ⟶ W.obj (Opposite.op (truncObjK k n hkn)) :=
  inclTrunc X k n hkn ≫ ((truncationObjIso n (constProdStd X k)).inv ≫ γ).app
    (Opposite.op (truncObjK k n hkn))

/-- The inverse of `phi`: given `f : X ⟶ V_k`, the morphism `psi f : X × Δ[k] ⟶ V` whose
component at level `n` sends the summand indexed by `α : [n] → [k]` via
`f ≫ V(α) : X ⟶ V_n`. -/
def psi (V : SimplicialObject C) (f : X ⟶ V.obj (Opposite.op ⦋k⦌)) :
    constProdStd X k ⟶ V where
  app n := Sigma.desc (fun (α : (yoneda.obj ⦋k⦌).obj n) => f ≫ V.map α.op)
  naturality {n m} φ := by
    refine Sigma.hom_ext _ _ fun α => ?_
    rw [Functor.copower_map, Sigma.ι_comp_map'_assoc, Sigma.ι_desc, Sigma.ι_desc_assoc]
    simp

/-- The component of `psi f` at level `n` sends the summand indexed by `α : [n] → [k]` via
`f ≫ V(α)`. -/
@[reassoc]
lemma ι_psi_app (V : SimplicialObject C) (f : X ⟶ V.obj (Opposite.op ⦋k⦌))
    (n : SimplexCategoryᵒᵖ) (α : (yoneda.obj ⦋k⦌).obj n) :
    Sigma.ι (fun (_ : (yoneda.obj ⦋k⦌).obj n) => ((SimplicialObject.const C).obj X).obj n) α ≫
      (psi X k V f).app n = f ≫ V.map α.op := by
  dsimp only [psi]
  exact Sigma.ι_desc _ _

/-- `Φ(psi f) = f` for every `f : X ⟶ V_k`. -/
theorem phi_psi (V : SimplicialObject C) (f : X ⟶ V.obj (Opposite.op ⦋k⦌)) :
    phi X k V (psi X k V f) = f := by
  rw [phi, incl, ι_psi_app]
  simp

/-- `psi (Φ γ) = γ` for every `γ : X × Δ[k] ⟶ V`. -/
theorem psi_phi (V : SimplicialObject C) (γ : constProdStd X k ⟶ V) :
    psi X k V (phi X k V γ) = γ := by
  ext n
  refine Sigma.hom_ext _ _ fun α => ?_
  rw [ι_psi_app, phi, incl, Category.assoc, ← γ.naturality,
    reassoc_of% Functor.ι_comp_copower_map]
  simp

/-- **Stacks 017F** (part 1).
For any simplicial object `V` of `C`, the map
`Φ : Mor_{Simp(C)}(X × Δ[k], V) → Mor_C(X, V_k)`, `Φ(γ) = γ_k ∘ ι_{id_[k]}`, is a bijection. -/
@[stacks 017F "(1)"]
theorem phi_bijective (V : SimplicialObject C) :
    Function.Bijective (phi X k V) := by
  rw [Function.bijective_iff_has_inverse]
  exact ⟨psi X k V, psi_phi X k V, phi_psi X k V⟩

/-- The inverse of `phiTrunc`, as a morphism out of `(Truncated.inclusion n).op ⋙ X × Δ[k]`:
given `f : X ⟶ W_k`, its component at level `m` sends the summand indexed by `α : m ⟶ [k]` via
`f ≫ W(α)`. -/
def psiTruncComp (n : ℕ) (hkn : k ≤ n) (W : SimplicialObject.Truncated C n)
    (f : X ⟶ W.obj (Opposite.op (truncObjK k n hkn))) :
    (Truncated.inclusion n).op ⋙ constProdStd X k ⟶ W where
  app m := Sigma.desc
    (fun (α : (yoneda.obj ⦋k⦌).obj ((Truncated.inclusion n).op.obj m)) =>
      f ≫ W.map ((Truncated.inclusion n).preimage (Y := truncObjK k n hkn) α).op)
  naturality {m m'} φ := by
    refine Sigma.hom_ext _ _ fun α => ?_
    rw [Functor.comp_map, Functor.copower_map, Sigma.ι_comp_map'_assoc, Sigma.ι_desc,
      Sigma.ι_desc_assoc]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    rw [Category.assoc, ← W.map_comp]
    congr 2
    exact Quiver.Hom.unop_inj.eq_iff.mp ((Truncated.inclusion n).map_injective.eq_iff.mp
      (by simp [-ObjectProperty.ι_map]))

/-- The component of `psiTruncComp f` at level `m` sends the summand indexed by `α : m ⟶ [k]`
via `f ≫ W(α)`. -/
lemma ι_psiTruncComp_app (n : ℕ) (hkn : k ≤ n) (W : SimplicialObject.Truncated C n)
    (f : X ⟶ W.obj (Opposite.op (truncObjK k n hkn))) (m : (SimplexCategory.Truncated n)ᵒᵖ)
    (α : (yoneda.obj ⦋k⦌).obj ((Truncated.inclusion n).op.obj m)) :
    Sigma.ι (fun (_ : (yoneda.obj ⦋k⦌).obj ((Truncated.inclusion n).op.obj m)) =>
        ((SimplicialObject.const C).obj X).obj ((Truncated.inclusion n).op.obj m)) α ≫
      (psiTruncComp X k n hkn W f).app m =
      f ≫ W.map ((Truncated.inclusion n).preimage (Y := truncObjK k n hkn) α).op := by
  dsimp only [psiTruncComp]
  exact Sigma.ι_desc _ _

/-- The inverse of `phiTrunc`: given `f : X ⟶ W_k`, the morphism `sk_n (X × Δ[k]) ⟶ W` whose
component at level `m` sends the summand indexed by `α : m ⟶ [k]` via `f ≫ W(α)`. -/
def psiTrunc (n : ℕ) (hkn : k ≤ n) (W : SimplicialObject.Truncated C n)
    (f : X ⟶ W.obj (Opposite.op (truncObjK k n hkn))) :
    (SimplicialObject.truncation n).obj (constProdStd X k) ⟶ W :=
  (truncationObjIso n (constProdStd X k)).hom ≫ psiTruncComp X k n hkn W f

/-- `Φ_n(psiTrunc f) = f` for every `f : X ⟶ W_k`. -/
theorem phi_trunc_psi_trunc (n : ℕ) (hkn : k ≤ n) (W : SimplicialObject.Truncated C n)
    (f : X ⟶ W.obj (Opposite.op (truncObjK k n hkn))) :
    phiTrunc X k n hkn W (psiTrunc X k n hkn W f) = f := by
  rw [phiTrunc, psiTrunc, Iso.inv_hom_id_assoc, inclTrunc, ι_psiTruncComp_app,
    Functor.preimage_id]
  simp

/-- `psiTrunc (Φ_n γ) = γ` for every `γ : sk_n (X × Δ[k]) ⟶ W`. -/
theorem psi_trunc_phi_trunc (n : ℕ) (hkn : k ≤ n) (W : SimplicialObject.Truncated C n)
    (γ : (SimplicialObject.truncation n).obj (constProdStd X k) ⟶ W) :
    psiTrunc X k n hkn W (phiTrunc X k n hkn W γ) = γ := by
  rw [psiTrunc, ← Iso.eq_inv_comp, phiTrunc]
  ext m
  refine Sigma.hom_ext _ _ fun α => ?_
  rw [ι_psiTruncComp_app, inclTrunc, Category.assoc, ← NatTrans.naturality, Functor.comp_map,
    reassoc_of% Functor.ι_comp_copower_map]
  simp [-ObjectProperty.ι_map]

/-- `phiTrunc` admits a two-sided inverse, namely `psiTrunc`. -/
theorem psi_trunc_exists (n : ℕ) (hkn : k ≤ n) (W : SimplicialObject.Truncated C n) :
    ∃ Ψ : (X ⟶ W.obj (Opposite.op (truncObjK k n hkn))) →
        ((SimplicialObject.truncation n).obj (constProdStd X k) ⟶ W),
      Function.LeftInverse (phiTrunc X k n hkn W) Ψ ∧
      Function.RightInverse (phiTrunc X k n hkn W) Ψ :=
  ⟨psiTrunc X k n hkn W, phi_trunc_psi_trunc X k n hkn W, psi_trunc_phi_trunc X k n hkn W⟩

/-- **Stacks 017F** (part 2).
Let `n ≥ k` and let `W` be an `n`-truncated simplicial object of `C`. Then the map
`Φ_n : Mor_{Simp_n(C)}(sk_n (X × Δ[k]), W) → Mor_C(X, W_k)`, `Φ_n(γ) = γ_k ∘ ι_{id_[k]}`, is a
bijection. -/
@[stacks 017F "(2)"]
theorem phi_trunc_bijective (n : ℕ) (hkn : k ≤ n) (W : SimplicialObject.Truncated C n) :
    Function.Bijective (phiTrunc X k n hkn W) := by
  obtain ⟨Ψ, hL, hR⟩ := psi_trunc_exists X k n hkn W
  rw [Function.bijective_iff_has_inverse]
  exact ⟨Ψ, hR, hL⟩

end constProdStd

end

end CategoryTheory.SimplicialObject

end

end
