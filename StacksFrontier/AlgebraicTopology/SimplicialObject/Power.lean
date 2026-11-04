module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Powers of (co)simplicial objects by (co)simplicial sets

For a cosimplicial set `K` and a simplicial object `V`, the simplicial object `Hom(K, V)` with
`Hom(K, V)_n = ∏_{K_n} V_n`, and dually for a simplicial set and a cosimplicial object. The self
product of a simplicial object represents evaluation in a fixed degree.
-/

/-!
## Hom from a cosimplicial set into a simplicial object

Let `C` be a category, let `V` be a simplicial object of `C`, i.e. a functor `Δᵒᵖ ⥤ C`, and let
`U` be a cosimplicial set, i.e. a functor `Δ ⥤ Type w`. Whenever the products involved exist, the
degreewise powers `∏_{u ∈ U_n} V_n` assemble into a simplicial object `Hom(U, V)` of `C`: the
structure map at `φ : [m] ⟶ [n]` of `Δ` is the unique morphism
`∏_{u ∈ U_n} V_n ⟶ ∏_{u ∈ U_m} V_m` whose `u`-th component, for `u ∈ U_m`, is the `U(φ)(u)`-th
projection followed by `V(φ)`. On `X`-valued points, where
`Mor_C(X, ∏_{u ∈ U_n} V_n) = Map(U_n, Mor_C(X, V_n))`, this is the map `f ↦ V(φ) ∘ f ∘ U(φ)`. It
is the analogue, for a cosimplicial set `U`, of the simplicial set `n ↦ Mor_C(U_n, V_n)` attached
to a cosimplicial object `U` and a simplicial object `V` of `C`, and it is dual to the cosimplicial
object `Hom(U, V)` attached to a simplicial set and a cosimplicial object in [Stacks, Tag 019V].
Applied to the standard cosimplicial sets `C[k]` of [Stacks, Tag 0B13] it gives the simplicial
objects `Hom(C[k], X)` of [Stacks, Tag 017M], out of which the hypercoverings of
[Stacks, Tag 0B16] are built.

### Main definitions

* `CategoryTheory.SimplicialObject.power`: the simplicial object `Hom(U, V)` of `C` with
  `Hom(U, V)_n = ∏_{u ∈ U_n} V_n`, written `V.power U`.

### Main results

* `CategoryTheory.SimplicialObject.power_map_π`: the `u`-th component of the structure map
  `Hom(U, V)(φ)` is the `U(φ)(u)`-th projection followed by `V(φ)`.

### Implementation notes

The source assumes that `C` has finite products and that each `U_n` is finite and nonempty; those
hypotheses are used only to produce the products `∏_{u ∈ U_n} V_n`, so the definition asks for
exactly those products and nothing more. `HasFiniteProducts C` together with `Finite (U.obj n)`
supplies the instance, so the source's situation is a special case, while an infinite `U_n` is
allowed as soon as `C` has the corresponding product, and an empty one as soon as `C` has a
terminal object. `HasFiniteProducts` itself lies outside this file's imports, in
`Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts`.

The name and the argument order are those of the dual `CategoryTheory.CosimplicialObject.power` of
[Stacks, Tag 019V]: `Hom(U, V)_n` is the power `V_n ^ (U_n)`, with the structure maps twisted by
`U`, and the powered object comes first so that the dot notation `V.power U` is available; the
source writes `Hom(U, V)`.

Nothing in the construction is special to `Δᵒᵖ`: for a category `J`, a functor `V : Jᵒᵖ ⥤ C` and a
copresheaf of types `U : J ⥤ Type w` the same two formulas define the pointwise power of `V` by
`U`, a functor `Jᵒᵖ ⥤ C`, under the same instance hypothesis; at `J = Δ` it is this definition on
the nose, equal to it by `rfl`. Because a power twists variance, it is instead the mirrored form,
on `V : J ⥤ C` and `U : Jᵒᵖ ⥤ Type w`, that specialises to [Stacks, Tag 019V] on the nose, and no
single form covers both without transporting `U` along the equivalence `Δᵒᵖᵒᵖ ≌ Δ`, along which the
product hypothesis is no longer found by instance search. Both are therefore stated simplicially,
and nothing is lost by it: a pointwise power over a general `J` absorbs each of them
definitionally, in the matching orientation.

The codomain of `Hom(U, V)(φ)` is recorded as `Hom(U, V)_m`, which is the product
`∏_{u ∈ U_m} V_m` by definition but not syntactically, so a composite of a structure map with a
projection of that product is well formed only after unfolding `power`. `power_map_π` states such
a composite in closed form; `power_map`, which describes the structure map alone, rewrites one into
a `Limits.Pi.lift` whose codomain is again `Hom(U, V)_m`, where `Limits.Pi.lift_π` no longer
applies, so it is generated without `@[simp]`.

### References

* [Stacks, Tag 0B15](https://stacks.math.columbia.edu/tag/0B15)
* [Stacks, Tag 019V](https://stacks.math.columbia.edu/tag/019V)
-/

section

@[expose] public section

namespace CategoryTheory.SimplicialObject

open Limits

universe w v u

variable {C : Type u} [Category.{v} C]

/-- **Stacks 0B15.** `Hom(U, V)`, the simplicial object of maps from a cosimplicial set `U` into a
simplicial object `V` of `C`. Its degree `n` part is the power `Hom(U, V)_n = ∏_{u ∈ U_n} V_n`, the
object of `C` whose `X`-valued points are the maps `U_n → Mor_C(X, V_n)`, and for `φ : [m] ⟶ [n]`
in `Δ` the structure map `Hom(U, V)_n ⟶ Hom(U, V)_m` is the morphism whose `u`-th component, for
`u ∈ U_m`, is the projection to the `U(φ)(u)`-th factor followed by `V(φ)`; on `X`-valued points it
is `f ↦ V(φ) ∘ f ∘ U(φ)`. -/
@[stacks 0B15 "the finiteness and nonemptiness of the `U_n` are replaced by the existence of \
  the products they index, which is all they are used for; dual to `CosimplicialObject.power` \
  of Tag 019V", simps obj, simps -isSimp map]
noncomputable def power (V : SimplicialObject C) (U : CosimplicialObject (Type w))
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : U.obj n.unop => V.obj n] :
    SimplicialObject C where
  obj n := ∏ᶜ fun _ : U.obj n.unop => V.obj n
  map φ := Pi.lift fun u => Pi.π _ (U.map φ.unop u) ≫ V.map φ
  map_id _ := Pi.hom_ext _ _ fun _ => by simp
  map_comp _ _ := Pi.hom_ext _ _ fun _ => by simp

/-- **The components of the structure maps of `Hom(U, V)`.** For `φ : [m] ⟶ [n]` in `Δ` and an
element `u ∈ U_m`, the `u`-th component of the structure map `Hom(U, V)(φ)` is the projection of
`Hom(U, V)_n = ∏_{u ∈ U_n} V_n` to the factor indexed by `U(φ)(u)`, followed by `V(φ)`. -/
@[reassoc]
lemma power_map_π (V : SimplicialObject C) (U : CosimplicialObject (Type w))
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : U.obj n.unop => V.obj n]
    {m n : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (u : U.obj m.unop) :
    (V.power U).map φ ≫ Pi.π (fun _ : U.obj m.unop => V.obj m) u
      = Pi.π (fun _ : U.obj n.unop => V.obj n) (U.map φ.unop u) ≫ V.map φ :=
  Pi.lift_π ..

end CategoryTheory.SimplicialObject

end

end

/-!
## The simplicial object of self products represents evaluation in degree `k`

Let `X` be an object of a category `C` and let `k` be a natural number. Following the source,
consider a simplicial object `U` of `C` with terms the self products

`U_n = ∏_{α ∈ Mor_Δ(⦋k⦌, ⦋n⦌)} X`

on which `φ : ⦋m⦌ ⟶ ⦋n⦌` acts on coordinates by `(x_α)_α ↦ (x_{φ ∘ α'})_{α'}`. The index sets are
the terms `C[k]_n = Mor_Δ(⦋k⦌, ⦋n⦌)` of the standard cosimplicial set `C[k]` of
[Stacks, Tag 0B13] and the reindexing is `C[k](φ)`, so `U` is an incarnation of `Hom(C[k], X)`
for `X` read as the constant simplicial object. Such a `U` represents evaluation in degree `k`:
for every simplicial object `V` of `C` the map

`Mor_{Simp(C)}(V, U) → Mor_C(V_k, X)`, `γ ↦ γ_k ≫ pr_{id_⦋k⦌}`,

is a bijection, and so is its truncated analogue `Mor_{Simp_j(C)}(W, sk_j U) → Mor_C(W_k, X)` for
every `j ≥ k`.

### Main results

* `CategoryTheory.SimplicialObject.bijective_comp_proj_id_of_prod_coyoneda`: a simplicial object
  whose terms are the self products of `X` indexed by `C[k]_n`, with the reindexing of the source
  as its structure maps, represents evaluation in degree `k`, both on simplicial objects and on
  `j`-truncated simplicial objects for every `j ≥ k`.

### Implementation notes

The source's `U` is characterised rather than constructed: the hypotheses are that the coordinates
`pr n : C[k]_n → (U_n ⟶ X)` exhibit `U_n` as the product of copies of `X` indexed by `C[k]_n` — in
the source's own phrasing, that `T`-valued points of `U_n` are the maps of sets
`C[k]_n → Mor_C(T, X)` via `f ↦ (f ≫ pr n α)_α` — and that the structure maps reindex along
`C[k]`, that is `U(φ) ≫ pr_α = pr_{C[k](φ)(α)}`, which for `C[k]` is the source's `pr_{φ ∘ α}`.
Those two are the definition of `Hom(C[k], X)_n` and of its structure maps, so they *are* part (3)
of the source: they say `U` is an incarnation of `Hom(C[k], X)`, and they pin `U` down together
with its projections up to unique isomorphism. Parts (1) and (2) are the conclusion. In particular
no product is assumed to exist, only that the given `U` behaves as one.

Part (2) is stated for an arbitrary truncation level `j ≥ k`; the source states the case `j = k`.
The argument applies verbatim as soon as the degree `k` lies in the truncation, and `j ≥ k` is the
form a hypercovering needs, being truncated at a level above the degree it is tested in.

Models of the hypotheses: `U = (CategoryTheory.evaluationRightAdjoint C (op ⦋k⦌)).obj X` with
`pr n α = Limits.Pi.π _ α.down.op`, available whenever `C` has products indexed by the hom sets
of `Δᵒᵖ` — for instance whenever `C` has finite products — and the `Hom(C[k], X)` of
[Stacks, Tag 0B15], that is `(const C).obj X |>.power (uliftCoyoneda.obj (op ⦋k⦌))`, with
`pr n α = Limits.Pi.π _ α`. For `k = 0` such a `U` has `U_n = ∏_{α : ⦋0⦌ ⟶ ⦋n⦌} X`, a product of
`n + 1` copies of `X`, and part (1) with `V = U` reads `Mor(U, U) = Mor(U_0, X) = Mor(X, X)`.

For the first model Mathlib has part (1), in the generality of an arbitrary index category, as the
adjunction `CategoryTheory.evaluationAdjunctionLeft C (op ⦋k⦌)`. That API assumes products indexed
by every hom set of `Δᵒᵖ`, which is more than the source assumes and more than is needed here, and
it says nothing about truncated objects.

Terms of `C[k]_n` are `ULift`ed morphisms of `Δ`, as in [Stacks, Tag 0B13], so the coordinate at
`α : ⦋k⦌ ⟶ ⦋n⦌` is `pr n (ULift.up α)`, and the source's projection onto the factor of
`id_{⦋k⦌}` is `pr k (ULift.up (𝟙 ⦋k⦌))`. The truncation `sk_j` is `SimplicialObject.truncation j`,
restriction along `Δ_{≤ j} ⥤ Δ`, not its left adjoint `SimplicialObject.Truncated.sk`.

### References

* [Stacks, Tag 017M](https://stacks.math.columbia.edu/tag/017M)
* [Stacks, Tag 0B13](https://stacks.math.columbia.edu/tag/0B13)
* [Stacks, Tag 0B15](https://stacks.math.columbia.edu/tag/0B15)
-/

section

@[expose] public section

open Opposite Simplicial

universe w v u v₂ u₂

/-- Reindexing the coordinates of a product along a bijection of the index sets preserves the
property of being a product. -/
private lemma Function.Bijective.comp_equiv {ι κ A B : Type*} {f : A → κ → B}
    (hf : Function.Bijective f) (e : ι ≃ κ) :
    Function.Bijective fun (x : A) (i : ι) => f x (e i) :=
  (e.arrowCongr (Equiv.refl B)).symm.bijective.comp hf

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The structure map of `uliftCoyoneda.obj X` at `ψ` is `α ↦ α ≫ ψ`. For `X = op ⦋k⦌` in the
simplex category this is the structure map of the standard cosimplicial set `C[k]`, the second
conjunct of [Stacks, Tag 0B13]. -/
private lemma uliftCoyoneda_obj_map_apply {J : Type u₂} [Category.{v₂} J] {X : Jᵒᵖ} {m l : J}
    (ψ : m ⟶ l) (α : (uliftCoyoneda.{w}.obj X).obj m) :
    (uliftCoyoneda.{w}.obj X).map ψ α = ULift.up (α.down ≫ ψ) :=
  rfl

section Abstract

variable {D : Type u₂} [Category.{v₂} D] {X : C} {G : D ⥤ C} {d₀ : D}
  (π : ∀ d : D, (d ⟶ d₀) → (G.obj d ⟶ X))

/-- The coordinate of a morphism `γ : F ⟶ G` at `a : d ⟶ d₀` is determined by its coordinate at
`𝟙 d₀`: it is the latter precomposed with `F.map a`. -/
private lemma app_comp_proj
    (hmap : ∀ (d e : D) (φ : d ⟶ e) (a : e ⟶ d₀), G.map φ ≫ π e a = π d (φ ≫ a))
    {F : D ⥤ C} (γ : F ⟶ G) {d : D} (a : d ⟶ d₀) :
    γ.app d ≫ π d a = F.map a ≫ (γ.app d₀ ≫ π d₀ (𝟙 d₀)) := by
  have h : π d a = G.map a ≫ π d₀ (𝟙 d₀) := by simpa using (hmap d d₀ a (𝟙 d₀)).symm
  rw [h, ← Category.assoc, ← γ.naturality a, Category.assoc]

/-- **A pointwise product of copies of `X` over the hom sets into `d₀` represents evaluation at
`d₀`.** Let `G : D ⥤ C` be a functor with coordinates `π d : (d ⟶ d₀) → (G.obj d ⟶ X)` that
exhibit `G.obj d` as the product of copies of `X` indexed by `d ⟶ d₀`, and that are compatible
with the maps of `G` in the sense that `G.map φ ≫ π e a = π d (φ ≫ a)`. Then for every
`F : D ⥤ C` the map `γ ↦ γ.app d₀ ≫ π d₀ (𝟙 d₀)` is a bijection
`(F ⟶ G) → (F.obj d₀ ⟶ X)`. -/
private theorem bijective_comp_proj_id
    (hπ : ∀ (d : D) (T : C), Function.Bijective fun (f : T ⟶ G.obj d) (a : d ⟶ d₀) => f ≫ π d a)
    (hmap : ∀ (d e : D) (φ : d ⟶ e) (a : e ⟶ d₀), G.map φ ≫ π e a = π d (φ ≫ a))
    (F : D ⥤ C) :
    Function.Bijective fun γ : F ⟶ G => γ.app d₀ ≫ π d₀ (𝟙 d₀) := by
  refine ⟨fun γ δ (h : γ.app d₀ ≫ π d₀ (𝟙 d₀) = δ.app d₀ ≫ π d₀ (𝟙 d₀)) => ?_, fun f => ?_⟩
  · ext d
    refine (hπ d (F.obj d)).injective (funext fun a => ?_)
    rw [app_comp_proj π hmap γ a, app_comp_proj π hmap δ a, h]
  · choose g hg using fun d : D => (hπ d (F.obj d)).surjective fun a : d ⟶ d₀ => F.map a ≫ f
    replace hg : ∀ (d : D) (a : d ⟶ d₀), g d ≫ π d a = F.map a ≫ f := fun d a => congrFun (hg d) a
    refine ⟨⟨g, fun d e φ => (hπ e (F.obj d)).injective (funext fun a => ?_)⟩, ?_⟩
    · rw [Category.assoc, hg e a, Category.assoc, hmap d e φ a, hg d (φ ≫ a), F.map_comp,
        Category.assoc]
    · simpa using hg d₀ (𝟙 d₀)

end Abstract

namespace SimplicialObject

section Simplicial

variable {X : C} {k : ℕ} {U : SimplicialObject C}
  {pr : ∀ n : ℕ, uliftCoyoneda.{w}.obj (op ⦋k⦌) ^⦋n⦌ → (U _⦋n⦌ ⟶ X)}

/-- **A simplicial object of self products indexed by `C[k]` represents evaluation in degree `k`,
along any index category over `Δᵒᵖ`.** Let the coordinates `pr` exhibit `U_n` as the product of
copies of `X` indexed by `C[k]_n`, with the structure maps of `U` reindexing along `C[k]`. Let
`R : D ⥤ Δᵒᵖ`, let `d₀ : D`, and let `ε d : (d ⟶ d₀) ≃ Mor_Δ(⦋k⦌, (R d)ᵒᵖ)` be identifications
of the hom sets into `d₀` with the terms of `C[k]` compatible with composition. Then
`γ ↦ γ_{d₀} ≫ pr_{ε (𝟙 d₀)}` is a bijection `(F ⟶ R ⋙ U) → (F.obj d₀ ⟶ X)` for every
`F : D ⥤ C`. -/
private theorem bijective_comp_pr_id
    (hpr : ∀ (n : ℕ) (T : C), Function.Bijective fun (f : T ⟶ U _⦋n⦌)
      (α : uliftCoyoneda.{w}.obj (op ⦋k⦌) ^⦋n⦌) => f ≫ pr n α)
    (hmap : ∀ (n m : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (α : uliftCoyoneda.{w}.obj (op ⦋k⦌) ^⦋m⦌),
      U.map φ.op ≫ pr m α = pr n ((uliftCoyoneda.{w}.obj (op ⦋k⦌)).map φ α))
    {D : Type u₂} [Category.{v₂} D] (R : D ⥤ SimplexCategoryᵒᵖ) {d₀ : D}
    (ε : ∀ d : D, (d ⟶ d₀) ≃ (⦋k⦌ ⟶ (R.obj d).unop))
    (hε : ∀ (d e : D) (φ : d ⟶ e) (a : e ⟶ d₀), ε d (φ ≫ a) = ε e a ≫ (R.map φ).unop)
    (F : D ⥤ C) :
    Function.Bijective fun γ : F ⟶ R ⋙ U =>
      γ.app d₀ ≫ pr (R.obj d₀).unop.len (ULift.up (ε d₀ (𝟙 d₀))) :=
  bijective_comp_proj_id (G := R ⋙ U) (fun d a => pr (R.obj d).unop.len (ULift.up (ε d a)))
    (fun d T => (hpr _ T).comp_equiv ((ε d).trans Equiv.ulift.symm))
    (fun d e φ a => (hmap _ _ (R.map φ).unop (ULift.up (ε e a))).trans (congrArg (pr _)
      ((uliftCoyoneda_obj_map_apply _ _).trans (congrArg ULift.up (hε d e φ a).symm)))) F

end Simplicial

/-- **`Hom(C[k], X)` represents evaluation in degree `k`.** Let `X` be an object of a category
`C`, let `k : ℕ`, and let `U` be a simplicial object of `C` with coordinates
`pr n : C[k]_n → (U_n ⟶ X)` indexed by the terms `C[k]_n = Mor_Δ(⦋k⦌, ⦋n⦌)` of the standard
cosimplicial set `C[k]` of [Stacks, Tag 0B13], such that the coordinates exhibit `U_n` as the
self product `∏_{α ∈ C[k]_n} X` — the `T`-valued points of `U_n` are the maps of sets
`C[k]_n → Mor_C(T, X)`, `f ↦ (f ≫ pr n α)_α` — and such that the structure maps reindex along
`C[k]`, that is `U(φ) ≫ pr_α = pr_{C[k](φ)(α)} = pr_{φ ∘ α}`; so `U` is an incarnation of
`Hom(C[k], X)` for `X` read as the constant simplicial object. Then `U` represents evaluation in
degree `k`: (1) for every simplicial object `V` of `C` the map `γ ↦ γ_k ≫ pr_{id_⦋k⦌}` is a
bijection `Mor_{Simp(C)}(V, U) → Mor_C(V_k, X)`, and (2) for every `j ≥ k` and every
`j`-truncated simplicial object `W` of `C` the same formula is a bijection
`Mor_{Simp_j(C)}(W, sk_j U) → Mor_C(W_k, X)`. -/
@[stacks 017M "the source's U is characterised rather than constructed: its terms being the self \
  products indexed by C[k]_n of Tag 0B13, and its structure maps the reindexing, are the \
  hypotheses, which is part (3); the two conjuncts are parts (1) and (2), the latter for an \
  arbitrary truncation level j ≥ k"]
public theorem bijective_comp_proj_id_of_prod_coyoneda (X : C) (k : ℕ) (U : SimplicialObject C)
    (pr : ∀ n : ℕ, uliftCoyoneda.{w}.obj (op ⦋k⦌) ^⦋n⦌ → (U _⦋n⦌ ⟶ X))
    (hpr : ∀ (n : ℕ) (T : C), Function.Bijective fun (f : T ⟶ U _⦋n⦌)
      (α : uliftCoyoneda.{w}.obj (op ⦋k⦌) ^⦋n⦌) => f ≫ pr n α)
    (hmap : ∀ (n m : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (α : uliftCoyoneda.{w}.obj (op ⦋k⦌) ^⦋m⦌),
      U.map φ.op ≫ pr m α = pr n ((uliftCoyoneda.{w}.obj (op ⦋k⦌)).map φ α)) :
    (∀ V : SimplicialObject C, Function.Bijective fun γ : V ⟶ U =>
        (γ.app (op ⦋k⦌) ≫ pr k (ULift.up (𝟙 ⦋k⦌)) : V _⦋k⦌ ⟶ X)) ∧
    (∀ (j : ℕ) (hkj : k ≤ j) (W : Truncated C j),
      Function.Bijective fun γ : W ⟶ (truncation j).obj U =>
        (γ.app (op ⟨⦋k⦌, hkj⟩) ≫ pr k (ULift.up (𝟙 ⦋k⦌)) :
          W.obj (op (⟨⦋k⦌, hkj⟩ : SimplexCategory.Truncated j)) ⟶ X)) :=
  ⟨bijective_comp_pr_id hpr hmap (𝟭 _) (d₀ := op ⦋k⦌) (fun d => opEquiv d (op ⦋k⦌))
      fun _ _ _ _ => rfl,
   fun j hkj => bijective_comp_pr_id hpr hmap (SimplexCategory.Truncated.inclusion j).op
      (d₀ := op ⟨⦋k⦌, hkj⟩)
      (fun _ => (SimplexCategory.Truncated.inclusion.fullyFaithful j).homEquiv.trans
        (opEquiv _ _)) fun _ _ _ _ => rfl⟩

end SimplicialObject

end CategoryTheory

end

end

/-!
## Hom from a simplicial set into a cosimplicial object

Let `C` be a category, let `V` be a cosimplicial object of `C`, i.e. a functor `Δ ⥤ C`, and let
`U` be a simplicial set, i.e. a functor `Δᵒᵖ ⥤ Type w`. Whenever the products involved exist, the
degreewise powers `∏_{u ∈ U_n} V_n` assemble into a cosimplicial object `Hom(U, V)` of `C`: the
structure map at `φ : [m] ⟶ [n]` of `Δ` is the unique morphism
`∏_{u ∈ U_m} V_m ⟶ ∏_{u ∈ U_n} V_n` whose `u`-th component, for `u ∈ U_n`, is the `U(φ)(u)`-th
projection followed by `V(φ)`. On `X`-valued points, where
`Mor_C(X, ∏_{u ∈ U_n} V_n) = Map(U_n, Mor_C(X, V_n))`, this is the map `f ↦ V(φ) ∘ f ∘ U(φ)`. It
is the analogue, for a simplicial set `U`, of the cosimplicial set `Hom(U, V)_n = Mor_C(U_n, V_n)`
attached to a simplicial object `U` and a cosimplicial object `V` of `C`.

### Main definitions

* `CategoryTheory.CosimplicialObject.power`: the cosimplicial object `Hom(U, V)` of `C` with
  `Hom(U, V)_n = ∏_{u ∈ U_n} V_n`, written `V.power U`.

### Main results

* `CategoryTheory.CosimplicialObject.power_map_π`: the componentwise description of the structure
  maps of `Hom(U, V)`, namely that the `u`-th component of `Hom(U, V)(φ)` is the `U(φ)(u)`-th
  projection followed by `V(φ)`. Together with `power_obj` and `power_map` it is what lets a
  morphism into `Hom(U, V)` be handled without unfolding the definition.

### Implementation notes

The source assumes that `C` has finite products and that each `U_n` is finite and nonempty; those
hypotheses are used only to produce the products `∏_{u ∈ U_n} V_n`, so the definition asks for
exactly those products and nothing more. `HasFiniteProducts C` together with
`Finite (U.obj (op n))` supplies the instance, so the source's situation is a special case, while
an infinite `U_n` is allowed as soon as `C` has the corresponding product, and an empty one as
soon as `C` has a terminal object.

Nothing in the construction is special to `Δ`: for a category `J`, a functor `V : J ⥤ C` and a
presheaf of types `U : Jᵒᵖ ⥤ Type w` the same formulas define the pointwise power of `V` by `U`, a
functor `J ⥤ C`. The simplicial degree of generality is the one the source and its neighbours use.

`power_map_π` is needed even though the `@[simps]` lemma `power_map` already describes the
structure maps: the codomain of `Hom(U, V)(φ)` is recorded as `Hom(U, V)_n`, which is the product
`∏_{u ∈ U_n} V_n` by definition but not syntactically, so a composite of a structure map with a
projection of that product is well formed only up to unfolding `power`, and `rw` and `simp` refuse
to rewrite inside one. `power_map_π` states such a composite once and for all and closes it by
`Limits.Pi.lift_π`, so it is the identity to apply — by `exact`, or by congruence inside a larger
composite — where rewriting is unavailable. For the same reason `power_map` is not a `simp` lemma:
rewriting a composite `Hom(U, V)(φ) ≫ π u` with it leaves a `Limits.Pi.lift` whose codomain is
still recorded as `Hom(U, V)_n`, where `Limits.Pi.lift_π` in turn no longer applies, so it takes a
provable goal to a stuck one. It remains available for `rw` and `exact`.

The name follows `CategoryTheory.Limits.FormalCoproduct.power` for the power of an object by a
type: `Hom(U, V)_n` is the power `V_n ^ (U_n)`, with the structure maps twisted by `U`. The
powered object comes first, so that the dot notation `V.power U` is available; the source writes
`Hom(U, V)`.

### References

* [Stacks 019V](https://stacks.math.columbia.edu/tag/019V)
-/

section

@[expose] public section

namespace CategoryTheory.CosimplicialObject

open Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C]

/-- **Stacks 019V.** `Hom(U, V)`, the cosimplicial object of maps from a simplicial set `U` into a
cosimplicial object `V` of `C`. Its degree `n` part is the power `Hom(U, V)_n = ∏_{u ∈ U_n} V_n`,
the object of `C` whose `X`-valued points are the maps `U_n → Mor_C(X, V_n)`, and for
`φ : [m] ⟶ [n]` in `Δ` the structure map `Hom(U, V)_m ⟶ Hom(U, V)_n` is the morphism whose `u`-th
component, for `u ∈ U_n`, is the projection to the `U(φ)(u)`-th factor followed by `V(φ)`; on
`X`-valued points it is `f ↦ V(φ) ∘ f ∘ U(φ)`. -/
@[stacks 019V "the finiteness and nonemptiness of the `U_n` are replaced by the \
  existence of the products they index, which is all they are used for",
  simps obj, simps -isSimp map]
noncomputable def power (V : CosimplicialObject C) (U : SSet.{w})
    [∀ n : SimplexCategory, HasProduct fun _ : U.obj (op n) => V.obj n] :
    CosimplicialObject C where
  obj n := ∏ᶜ fun _ : U.obj (op n) => V.obj n
  map φ := Pi.lift fun u => Pi.π _ (U.map φ.op u) ≫ V.map φ
  map_id _ := Pi.hom_ext _ _ fun _ => by simp
  map_comp _ _ := Pi.hom_ext _ _ fun _ => by simp

/-- **The components of the structure maps of `Hom(U, V)`.** For `φ : [m] ⟶ [n]` in `Δ` and a
simplex `u ∈ U_n`, the `u`-th component of the structure map `Hom(U, V)(φ)` is the projection of
`Hom(U, V)_m = ∏_{u ∈ U_m} V_m` to the factor indexed by `U(φ)(u)`, followed by `V(φ)`. -/
@[reassoc]
lemma power_map_π (V : CosimplicialObject C) (U : SSet.{w})
    [∀ n : SimplexCategory, HasProduct fun _ : U.obj (op n) => V.obj n]
    {m n : SimplexCategory} (φ : m ⟶ n) (u : U.obj (op n)) :
    (V.power U).map φ ≫ Pi.π (fun _ : U.obj (op n) => V.obj n) u
      = Pi.π (fun _ : U.obj (op m) => V.obj m) (U.map φ.op u) ≫ V.map φ :=
  Pi.lift_π ..

end CategoryTheory.CosimplicialObject

end

end
