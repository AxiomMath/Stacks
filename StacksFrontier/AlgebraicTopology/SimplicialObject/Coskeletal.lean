module

public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal.Existence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coskeleton functors

The coskeleton functors `cosk_n`, right adjoint to truncation, their description as limits over
truncated slice categories, and their compatibility with products.
-/

/-!
## Coskeleton functors

Let `C` be a category. Restriction along the inclusion `Δ_{≤ n} ⊆ Δ` is the skeleton functor
`sk_n : Simp(C) ⥤ Simp_n(C)`, `CategoryTheory.SimplicialObject.truncation n`, and its right
adjoint — right Kan extension along `(Δ_{≤ n})ᵒᵖ ⥤ Δᵒᵖ` — is the `n`-th *coskeleton* functor
`cosk_n`, `CategoryTheory.SimplicialObject.Truncated.cosk n`, with adjunction
`CategoryTheory.SimplicialObject.coskAdj n`.

At level `0` a truncated simplicial object is just an object `X` of `C`, and `cosk₀ X` is the
self-product simplicial object `n ↦ X^{n + 1}`, a nondecreasing map acting on coordinates by
reindexing: a morphism into it is determined by, and determines, a single morphism out of the
object of `0`-simplices of the source.

At higher levels the coskeleton is built one degree at a time out of *matching families*. A
matching family of `n + 3` morphisms `f_i : T ⟶ U_{n + 1}` into the top term of an
`(n + 1)`-truncated simplicial object `U` is one glueing along the faces as the faces of an
`(n + 2)`-simplex do, `d_{j - 1} ∘ f_i = d_i ∘ f_j` for `i < j`. Such a family is the same thing
as a cone with vertex `T` over the truncated slice category `(Δ/⦋n + 2⦌)^{opp}_{≤ n + 1}` — the
shape whose limit computes the coskeleton in degree `n + 2` — the bijection being restriction of
a cone to its legs at the `n + 3` face maps. Consequently, when the functor of matching families
is representable, the representing object extends `U` by one degree: it is the top term of an
`(n + 2)`-truncated simplicial object which is a right Kan extension of `U`, equivalently which
satisfies the adjointness `Mor(V, Ũ) = Mor(sk_{n + 1} V, U)`.

Being a right adjoint, `cosk_n` preserves all limits that exist; in particular it commutes with
fibre products, and this already holds when only the coskeleta of the objects involved exist, by the
same hom-set computation. Coskeleta of different levels are compatible: for `n ≤ m` the further
truncation `Simp_m(C) ⥤ Simp_n(C)` is left adjoint to `sk_m cosk_n`, every `cosk_n U` is
`m`-coskeletal, and an `n`-coskeletal simplicial object is `m`-coskeletal. Finally, for `m ≥ 1` the
coskeleton of a truncated simplicial object of a slice category `C/X` may be computed in `C`,
because the comma categories indexing the defining limits are then connected and `Over.forget X`
preserves connected limits.

### Main results

* `CategoryTheory.SimplicialObject.bijective_app_zero_comp_π`: the `0`-coskeleton of an object
  `X` is the self-product simplicial object `n ↦ X^{n + 1}`.
* `CategoryTheory.SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff`: a family of `n + 3`
  morphisms into the top term of an `(n + 1)`-truncated simplicial object extends, uniquely, to a
  cone over the truncated slice category with prescribed legs at the faces, if and only if it is
  a matching family.
* `CategoryTheory.SimplicialObject.Truncated.exists_isRightKanExtension_of_matchingFamily`: a
  universal matching family extends an `(n + 1)`-truncated simplicial object by one degree, the
  extension being a right Kan extension along the inclusion of truncated simplex categories.
* `CategoryTheory.SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app`: for
  `n ≤ m`, the further truncation `Simp_m(C) ⥤ Simp_n(C)` has right adjoint `sk_m cosk_n`, every
  `cosk_n U` is `m`-coskeletal, and an `n`-coskeletal object is `m`-coskeletal.
* `CategoryTheory.SimplicialObject.Truncated.cosk.preservesLimitsOfSize`: `cosk_n` preserves
  limits of every shape and size.
* `CategoryTheory.SimplicialObject.Truncated.isIso_pullback_lift_coskMap`: for a category with
  fibre products, `cosk_n (U ×_V W) = cosk_n U ×_{cosk_n V} cosk_n W` whenever the coskeleta
  involved exist.
* `CategoryTheory.Over.preservesPointwiseRightKanExtensions_forget_inclusion_succ_op`: for
  `m ≥ 1` the forgetful functor of a slice category commutes with `cosk_m`.

### References

* [Stacks, Tag 0182](https://stacks.math.columbia.edu/tag/0182)
* [Stacks, Tag 0186](https://stacks.math.columbia.edu/tag/0186)
* [Stacks, Tag 0187](https://stacks.math.columbia.edu/tag/0187)
* [Stacks, Tag 018B](https://stacks.math.columbia.edu/tag/018B)
* [Stacks, Tag 018D](https://stacks.math.columbia.edu/tag/018D)
* [Stacks, Tag 08NJ](https://stacks.math.columbia.edu/tag/08NJ)
-/

section

universe w w' v u v₁ u₁ v₂ u₂

namespace CategoryTheory.SimplicialObject

open Opposite Simplicial Limits

variable {C : Type u} [Category.{v} C]

/-- The components of the fan `Limits.Fan.mk P p` are the given morphisms `p`. -/
private lemma fan_mk_π_app {β : Type w} {f : β → C} (P : C) (p : ∀ b, P ⟶ f b)
    (j : Discrete β) : (Fan.mk P p).π.app j = p j.as :=
  rfl

section SelfProduct

variable {X : C} {U : SimplicialObject C}
  {π : ∀ n : ℕ, Fin (n + 1) → (U.obj (op ⦋n⦌) ⟶ X)}

/-- The `i`-th projection of `U_n` is the `i`-th vertex map followed by the projection of `U_0`;
the case of the coordinate formula `hπ` at the vertex maps `i : ⦋0⦌ ⟶ ⦋n⦌`. -/
private lemma map_const_op_comp_π_zero
    (hπ : ∀ {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)),
      U.map φ.op ≫ π n i = π m (φ.toOrderHom i))
    (n : ℕ) (i : Fin (n + 1)) :
    U.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op ≫ π 0 0 = π n i :=
  hπ _ 0

/-- A morphism `V ⟶ U` into the self-product simplicial object of `X` is determined by the
composite of its degree-`0` component with the projection `π 0 0`. -/
private lemma injective_app_zero_comp_π
    (hU : ∀ n : ℕ, IsLimit (Fan.mk (U.obj (op ⦋n⦌)) (π n)))
    (hπ : ∀ {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)),
      U.map φ.op ≫ π n i = π m (φ.toOrderHom i))
    (V : SimplicialObject C) :
    Function.Injective (fun f : V ⟶ U => f.app (op ⦋0⦌) ≫ π 0 0) := by
  intro f g h
  have h' : f.app (op ⦋0⦌) ≫ π 0 0 = g.app (op ⦋0⦌) ≫ π 0 0 := h
  ext n
  obtain ⟨⟨k⟩⟩ := n
  refine (hU k).hom_ext fun j => ?_
  have hf := f.naturality (SimplexCategory.const ⦋0⦌ ⦋k⦌ j.as).op
  have hg := g.naturality (SimplexCategory.const ⦋0⦌ ⦋k⦌ j.as).op
  rw [fan_mk_π_app, ← map_const_op_comp_π_zero hπ k j.as, ← Category.assoc, ← Category.assoc,
    ← hf, ← hg, Category.assoc, Category.assoc, h']

/-- Every morphism `g : V_0 ⟶ X` comes from a morphism `V ⟶ U` into the self-product simplicial
object of `X`, namely from the one whose coordinates are the composites `V(i) ≫ g` of `g` with
the vertex maps. -/
private lemma surjective_app_zero_comp_π
    (hU : ∀ n : ℕ, IsLimit (Fan.mk (U.obj (op ⦋n⦌)) (π n)))
    (hπ : ∀ {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)),
      U.map φ.op ≫ π n i = π m (φ.toOrderHom i))
    (V : SimplicialObject C) :
    Function.Surjective (fun f : V ⟶ U => f.app (op ⦋0⦌) ≫ π 0 0) := by
  intro g
  refine ⟨⟨fun n => (hU n.unop.len).lift (Fan.mk _ (fun i =>
      V.map (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ i).op ≫ g)), ?_⟩, ?_⟩
  · intro n m ψ
    obtain ⟨⟨a⟩⟩ := n; obtain ⟨⟨b⟩⟩ := m
    refine (hU b).hom_ext fun j => ?_
    have h1 : U.map ψ ≫ π b j.as = π a (ψ.unop.toOrderHom j.as) := hπ ψ.unop j.as
    rw [fan_mk_π_app, Category.assoc, Category.assoc, h1, ← fan_mk_π_app _ (π b) j,
      ← fan_mk_π_app _ (π a) (Discrete.mk (ψ.unop.toOrderHom j.as)), IsLimit.fac, IsLimit.fac,
      fan_mk_π_app, fan_mk_π_app, ← Category.assoc, ← V.map_comp, ← Quiver.Hom.op_unop ψ,
      ← op_comp, SimplexCategory.const_comp, Quiver.Hom.unop_op]
  · have h0 : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by ext x : 3; simp [Fin.eq_zero]
    dsimp only
    rw [← fan_mk_π_app _ (π 0) (Discrete.mk 0), IsLimit.fac, fan_mk_π_app, h0, op_id, V.map_id,
      Category.id_comp]

end SelfProduct

/-- **Stacks 0182**.
The `0`-coskeleton of an object `X` is the simplicial object `n ↦ X^{n + 1}`. Let `U` be a
simplicial object of `C` whose term `U_n` is the product of `n + 1` copies of `X`, with projections
`π n i : U_n ⟶ X` indexed by the vertices `i` of `⦋n⦌` (`hU`), the simplicial structure maps acting
on coordinates by `(x_0, …, x_m) ↦ (x_{φ(0)}, …, x_{φ(n)})` (`hπ`). Then for every simplicial
object `V` of `C`, a morphism `V ⟶ U` is determined by and determines a single morphism `V_0 ⟶ X`,
namely the composite of its degree-`0` component with the projection `π 0 0`. In other words
`Mor(V, U) = Mor(V_0, X)`, so that `U` is the coskeleton `cosk₀(X)`. -/
@[stacks 0182 "the self-product simplicial object is stated abstractly, by product cones on \
  the terms of an arbitrary `U`, rather than by choosing a model of `X ^ (n + 1)`; the \
  hom-set formula is reduced, as in the source, to `Mor(V, U) = Mor(V₀, X)`"]
public theorem bijective_app_zero_comp_π {X : C} {U : SimplicialObject C}
    (π : ∀ n : ℕ, Fin (n + 1) → (U.obj (op ⦋n⦌) ⟶ X))
    (hU : ∀ n : ℕ, IsLimit (Fan.mk (U.obj (op ⦋n⦌)) (π n)))
    (hπ : ∀ {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)),
      U.map φ.op ≫ π n i = π m (φ.toOrderHom i))
    (V : SimplicialObject C) :
    Function.Bijective (fun f : V ⟶ U => f.app (op ⦋0⦌) ≫ π 0 0) :=
  ⟨injective_app_zero_comp_π hU hπ V, surjective_app_zero_comp_π hU hπ V⟩

end CategoryTheory.SimplicialObject

namespace CategoryTheory.SimplicialObject.Truncated

open Opposite Simplicial Limits

section MatchingFamilies

variable {Δ : SimplexCategory} {m : ℕ}

/-- A face map omits its own index. -/
public lemma δ_apply_ne (i : Fin (m + 2)) (x : Fin (m + 1)) :
    (SimplexCategory.δ i).toOrderHom x ≠ i := by
  dsimp [SimplexCategory.δ]
  rw [OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  exact Fin.succAbove_ne i x

/-- A monotone map `Δ ⟶ ⦋m + 1⦌` whose source has dimension at most `m` omits a value. -/
private lemma exists_notMem_range (hΔ : Δ.len ≤ m) (α : Δ ⟶ ⦋m + 1⦌) :
    ∃ i : Fin (m + 2), ∀ x, α.toOrderHom x ≠ i := by
  by_contra hcon
  simp only [not_exists, not_forall, not_not] at hcon
  have h := Fintype.card_le_of_surjective α.toOrderHom hcon
  simp only [Fintype.card_fin, SimplexCategory.len_mk] at h
  omega

/-- The square of faces `δ i ≫ δ j.succ = δ j ≫ δ i.castSucc`, `i ≤ j`, is a pullback: two maps to
`⦋m + 1⦌` that agree after those two faces have a common factor through the codimension-two face.
-/
private lemma exists_comp_δ_eq_of_comp_δ_eq {i j : Fin (m + 2)} (hij : i ≤ j)
    {ψ φ : Δ ⟶ ⦋m + 1⦌} (h : ψ ≫ SimplexCategory.δ i.castSucc = φ ≫ SimplexCategory.δ j.succ) :
    ∃ ξ : Δ ⟶ ⦋m⦌, ψ = ξ ≫ SimplexCategory.δ j ∧ φ = ξ ≫ SimplexCategory.δ i := by
  have hφ : ∀ x, φ.toOrderHom x ≠ i := by
    intro x hx
    refine δ_apply_ne i.castSucc (ψ.toOrderHom x) ?_
    have hval : (SimplexCategory.δ j.succ).toOrderHom (φ.toOrderHom x) = i.castSucc := by
      rw [hx]
      dsimp [SimplexCategory.δ]
      rw [OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
      exact Fin.succAbove_of_castSucc_lt _ _ (by rwa [Fin.castSucc_lt_succ_iff])
    have hx' := congrArg (fun θ : Δ ⟶ ⦋m + 2⦌ => θ.toOrderHom x) h
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] at hx'
    exact hx'.trans hval
  obtain ⟨ξ, hξ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' φ i hφ
  refine ⟨ξ, (cancel_mono (SimplexCategory.δ i.castSucc)).mp ?_, hξ⟩
  rw [h, hξ, Category.assoc, SimplexCategory.δ_comp_δ hij, Category.assoc]

/-- Every object of the `(n + 1)`-truncated slice category over `⦋n + 2⦌` factors through a face
`δ i : ⦋n + 1⦌ ⟶ ⦋n + 2⦌`. -/
private lemma exists_comp_δ_eq {n : ℕ}
    (X : StructuredArrow (op ⦋n + 2⦌) (SimplexCategory.Truncated.inclusion (n + 1)).op) :
    ∃ (i : Fin (n + 3)) (ψ : X.right.unop.obj ⟶ ⦋n + 1⦌),
      ψ ≫ SimplexCategory.δ i = X.hom.unop := by
  obtain ⟨i, hi⟩ := exists_notMem_range X.right.unop.property X.hom.unop
  obtain ⟨ψ, hψ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' X.hom.unop i hi
  exact ⟨i, ψ, hψ.symm⟩

end MatchingFamilies

section

variable {C : Type u} [Category.{v} C] {n : ℕ}
  (U : SimplicialObject.Truncated C (n + 1)) {T : C}

/-- A family `(f_0, …, f_{n + 2})` of morphisms `T ⟶ U_{n + 1}` is a *matching family* if
`d_{j - 1} ∘ f_i = d_i ∘ f_j` for all `i < j`, written as in the first simplicial identity. -/
private abbrev IsMatching
    (f : Fin (n + 3) →
      (T ⟶ U.obj (op (⟨⦋n + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (n + 1))))) : Prop :=
  ∀ i j : Fin (n + 2), i ≤ j →
    f i.castSucc ≫ U.map (SimplexCategory.Truncated.δ (n + 1) j n.le_succ le_rfl).op =
      f j.succ ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i n.le_succ le_rfl).op

variable {f : Fin (n + 3) →
  (T ⟶ U.obj (op (⟨⦋n + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (n + 1))))}

/-- `U` applied to a map that factors through the face `δ i`, split into its two factors. -/
private lemma map_homMk_comp_δ {a : SimplexCategory.Truncated (n + 1)} (ξ : a.obj ⟶ ⦋n⦌)
    (i : Fin (n + 2)) :
    U.map (ObjectProperty.homMk (ξ ≫ SimplexCategory.δ i) :
        a ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op =
      U.map (SimplexCategory.Truncated.δ (n + 1) i n.le_succ le_rfl).op ≫
        U.map (ObjectProperty.homMk ξ : a ⟶ ⟨⦋n⦌, n.le_succ⟩).op := by
  rw [← U.map_comp]
  rfl

/-- `U` applied to a map precomposed with a morphism of the truncated simplex category, split
into its two factors. -/
private lemma map_homMk_comp {a b : (SimplexCategory.Truncated (n + 1))ᵒᵖ} (g : a ⟶ b)
    (ψ : a.unop.obj ⟶ ⦋n + 1⦌) :
    U.map (ObjectProperty.homMk (g.unop.hom ≫ ψ) : b.unop ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op =
      U.map (ObjectProperty.homMk ψ : a.unop ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op ≫ U.map g := by
  rw [← U.map_comp]
  rfl

/-- **Independence of the omitted vertex.** If `ψ ≫ δ i` and `φ ≫ δ (j + 1)` are the same map
`⦋k⦌ ⟶ ⦋n + 2⦌`, with `i ≤ j`, then the two legs `f i ≫ U(ψ)` and `f (j + 1) ≫ U(φ)` that a
matching family prescribes for it agree. -/
private lemma comp_map_eq_of_comp_δ_eq_le (hf : IsMatching U f)
    {a : SimplexCategory.Truncated (n + 1)} {i j : Fin (n + 2)} (hij : i ≤ j)
    {ψ φ : a.obj ⟶ ⦋n + 1⦌}
    (h : ψ ≫ SimplexCategory.δ i.castSucc = φ ≫ SimplexCategory.δ j.succ) :
    f i.castSucc ≫ U.map (ObjectProperty.homMk ψ : a ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op =
      f j.succ ≫ U.map (ObjectProperty.homMk φ : a ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op := by
  obtain ⟨ξ, rfl, rfl⟩ := exists_comp_δ_eq_of_comp_δ_eq hij h
  rw [map_homMk_comp_δ, map_homMk_comp_δ, ← Category.assoc, ← Category.assoc, hf i j hij]

/-- Independence of the omitted vertex for a pair of distinct vertices, written `I < J` instead
of `I = i` and `J = j + 1` with `i ≤ j`. -/
private lemma comp_map_eq_of_comp_δ_eq_lt (hf : IsMatching U f)
    {a : SimplexCategory.Truncated (n + 1)} {I J : Fin (n + 3)} (hIJ : I < J)
    {ψ φ : a.obj ⟶ ⦋n + 1⦌}
    (h : ψ ≫ SimplexCategory.δ I = φ ≫ SimplexCategory.δ J) :
    f I ≫ U.map (ObjectProperty.homMk ψ : a ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op =
      f J ≫ U.map (ObjectProperty.homMk φ : a ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op := by
  obtain ⟨i, rfl⟩ : ∃ i, I = i.castSucc :=
    ⟨I.castPred (Fin.ne_last_of_lt hIJ), (Fin.castSucc_castPred I _).symm⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j.succ :=
    ⟨J.pred (Fin.ne_of_gt ((Fin.zero_le _).trans_lt hIJ)), (Fin.succ_pred J _).symm⟩
  exact comp_map_eq_of_comp_δ_eq_le U hf (Fin.castSucc_lt_succ_iff.mp hIJ) h

/-- Independence of the omitted vertex, for an arbitrary pair of vertices: the leg a matching
family prescribes at an object of the slice category is well defined. -/
private lemma comp_map_eq_of_comp_δ_eq (hf : IsMatching U f)
    {a : SimplexCategory.Truncated (n + 1)} {I J : Fin (n + 3)} {ψ φ : a.obj ⟶ ⦋n + 1⦌}
    (h : ψ ≫ SimplexCategory.δ I = φ ≫ SimplexCategory.δ J) :
    f I ≫ U.map (ObjectProperty.homMk ψ : a ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op =
      f J ≫ U.map (ObjectProperty.homMk φ : a ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op := by
  rcases lt_trichotomy I J with hIJ | rfl | hIJ
  · exact comp_map_eq_of_comp_δ_eq_lt U hf hIJ h
  · rw [(cancel_mono (SimplexCategory.δ I)).mp h]
  · exact (comp_map_eq_of_comp_δ_eq_lt U hf hIJ h.symm).symm

/-- **A cone's leg at an object of the slice category is its leg at any face through which that
object factors.** If `ψ ≫ δ i = X.hom`, i.e. `ψ` is a morphism `X ⟶ δ i` of the slice category,
then `π.app X = π.app (δ i) ≫ U(ψ)`; this is naturality of `π` at that morphism. -/
private lemma app_comp_map
    (π : (Functor.const (StructuredArrow (op ⦋n + 2⦌)
        (SimplexCategory.Truncated.inclusion (n + 1)).op)).obj T ⟶
      StructuredArrow.proj (op ⦋n + 2⦌)
        (SimplexCategory.Truncated.inclusion (n + 1)).op ⋙ U)
    {X : StructuredArrow (op ⦋n + 2⦌) (SimplexCategory.Truncated.inclusion (n + 1)).op}
    (i : Fin (n + 3)) (ψ : X.right.unop.obj ⟶ ⦋n + 1⦌)
    (hi : ψ ≫ SimplexCategory.δ i = X.hom.unop) :
    π.app (StructuredArrow.mk
          (Y := op (⟨⦋n + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (n + 1)))
          (SimplexCategory.δ i).op) ≫
        U.map (ObjectProperty.homMk ψ :
          X.right.unop ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op = π.app X := by
  have h := π.naturality (StructuredArrow.homMk
    (f := StructuredArrow.mk
      (Y := op (⟨⦋n + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (n + 1)))
      (SimplexCategory.δ i).op)
    (f' := X)
    (ObjectProperty.homMk ψ : X.right.unop ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op
    (by exact Quiver.Hom.unop_inj.eq_iff.mp hi))
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map,
    StructuredArrow.proj_map, StructuredArrow.homMk_right, Category.id_comp] at h
  exact h.symm

/-- **The legs of a cone at the faces form a matching family**: the two composites
`f i ≫ U(δ_j)` and `f (j + 1) ≫ U(δ_i)` are the leg of the cone at one and the same object of
the slice category, namely at `δ_i ∘ δ_{j - 1} = δ_j ∘ δ_i : ⦋n⦌ ⟶ ⦋n + 2⦌`. -/
private lemma isMatching_of_app_δ
    (π : (Functor.const (StructuredArrow (op ⦋n + 2⦌)
        (SimplexCategory.Truncated.inclusion (n + 1)).op)).obj T ⟶
      StructuredArrow.proj (op ⦋n + 2⦌)
        (SimplexCategory.Truncated.inclusion (n + 1)).op ⋙ U)
    (hπ : ∀ i : Fin (n + 3), π.app (StructuredArrow.mk
      (Y := op (⟨⦋n + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (n + 1)))
      (SimplexCategory.δ i).op) = f i) :
    IsMatching U f := by
  intro i j hij
  have h := app_comp_map U π (X := StructuredArrow.mk
    (Y := op (⟨⦋n⦌, n.le_succ⟩ : SimplexCategory.Truncated (n + 1)))
    (SimplexCategory.δ j ≫ SimplexCategory.δ i.castSucc).op)
  rw [← hπ i.castSucc, ← hπ j.succ, h i.castSucc (SimplexCategory.δ j) rfl,
    h j.succ (SimplexCategory.δ i) (SimplexCategory.δ_comp_δ hij)]

end

variable {C : Type u} [Category.{v} C] {n : ℕ}

/-- **Stacks 0186**.
A matching family of morphisms into the top term of a truncated simplicial object is the same thing
as a cone over the truncated slice category. Let `U` be an `(n + 1)`-truncated simplicial object of
`C` and let `f i : T ⟶ U_{n + 1}`, `i = 0, …, n + 2`, be a family of morphisms. Then `f` extends,
in exactly one way, to a cone over the diagram `(Δ/⦋n + 2⦌)^{opp}_{≤ n + 1} → C` defined by `U`
whose leg at the face `δ_i : ⦋n + 1⦌ ⟶ ⦋n + 2⦌` is `f i`, if and only if `f` is a matching family:
`f i ≫ d_j = f (j + 1) ≫ d_i` for all `i ≤ j`.
Consequently, if the functor of matching families is represented by an object `U_{n + 2}`, then
`U_{n + 2} = lim_{(Δ/⦋n + 2⦌)^{opp}_{≤ n + 1}} U`. -/
@[stacks 0186 "the representing object of the functor of matching families is the limit over \
  the truncated slice category, via restriction of a cone to its legs at the faces"]
public theorem existsUnique_cone_app_δ_eq_iff (U : SimplicialObject.Truncated C (n + 1)) (T : C)
    (f : Fin (n + 3) →
      (T ⟶ U.obj (op (⟨⦋n + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (n + 1))))) :
    (∃! π : (Functor.const (StructuredArrow (op ⦋n + 2⦌)
          (SimplexCategory.Truncated.inclusion (n + 1)).op)).obj T ⟶
        StructuredArrow.proj (op ⦋n + 2⦌)
          (SimplexCategory.Truncated.inclusion (n + 1)).op ⋙ U,
      ∀ i : Fin (n + 3), π.app (StructuredArrow.mk
        (Y := op (⟨⦋n + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (n + 1)))
        (SimplexCategory.δ i).op) = f i) ↔
      ∀ i j : Fin (n + 2), i ≤ j →
        f i.castSucc ≫ U.map (SimplexCategory.Truncated.δ (n + 1) j n.le_succ le_rfl).op =
          f j.succ ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i n.le_succ le_rfl).op := by
  refine ⟨fun ⟨π, hπ, _⟩ => isMatching_of_app_δ U π hπ, fun hf => ?_⟩
  choose i ψ hψ using exists_comp_δ_eq (n := n)
  refine ⟨⟨fun X => f (i X) ≫
    U.map (ObjectProperty.homMk (ψ X) : X.right.unop ⟶ ⟨⦋n + 1⦌, le_rfl⟩).op, ?_⟩, ?_, ?_⟩
  · intro X Y g
    have h := comp_map_eq_of_comp_δ_eq U hf (ψ := g.right.unop.hom ≫ ψ X) (φ := ψ Y)
      (by rw [Category.assoc, hψ X, hψ Y]
          exact congrArg Quiver.Hom.unop (StructuredArrow.w g))
    rw [map_homMk_comp, ← Category.assoc] at h
    simpa using h.symm
  · intro i₀
    refine (comp_map_eq_of_comp_δ_eq U hf (J := i₀) (φ := 𝟙 ⦋n + 1⦌)
      (by rw [hψ]; simp)).trans ?_
    simp
  · intro π' hπ'
    exact NatTrans.ext (funext fun X => by
      rw [← app_comp_map U π' (i X) (ψ X) (hψ X), hπ'])

end CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory.SimplicialObject.Truncated

open Opposite Simplicial Limits
open scoped SimplexCategory.Truncated CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C] {n : ℕ}

section OneStepExtension

/-- The truncated slice category `(Δ/⦋n + 2⦌)_{≤ n + 1}`. -/
@[sga "4 Vbis 3.0.1" "partial"]
private abbrev slice (n : ℕ) := StructuredArrow (op (⦋n + 2⦌ : SimplexCategory))
    (SimplexCategory.Truncated.inclusion (n + 1)).op

/-- The diagram over the truncated slice category defined by `U`. -/
private abbrev diagram (U : SimplicialObject.Truncated C (n + 1)) : slice n ⥤ C :=
  StructuredArrow.proj _ _ ⋙ U

/-- The object `δ_i : ⦋n + 1⦌ ⟶ ⦋n + 2⦌` of the truncated slice category. -/
private abbrev faceObj (i : Fin (n + 3)) : slice n :=
  StructuredArrow.mk (Y := op ⦋n + 1⦌ₙ₊₁) (SimplexCategory.δ i).op

/-- The inclusion of the `(n + 1)`-truncated into the `(n + 2)`-truncated simplex category,
opposed. -/
private abbrev inclOp (n : ℕ) :
    (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ (SimplexCategory.Truncated (n + 2))ᵒᵖ :=
  (SimplexCategory.Truncated.incl (n + 1) (n + 2) (by lia)).op

/-- The identification of the slice of `inclOp n` over `⦋n + 2⦌ₙ₊₂` with the slice of
`SimplexCategory.Truncated.inclusion (n + 1)` over `⦋n + 2⦌`, an equivalence because
`SimplexCategory.Truncated.inclusion (n + 2)` is fully faithful. -/
private abbrev postEquiv (n : ℕ) :=
  StructuredArrow.post (op ⦋n + 2⦌ₙ₊₂) (inclOp n)
    (SimplexCategory.Truncated.inclusion (n + 2)).op

/-- The legs of a cone over the truncated slice category at the `n + 3` faces
`δ_i : ⦋n + 1⦌ ⟶ ⦋n + 2⦌` form a matching family: both composites are the leg at the object
`δ_j ∘ δ_{i.castSucc} = δ_i ∘ δ_{j.succ}`. -/
private theorem matchingFamily_cone_app_face (U : SimplicialObject.Truncated C (n + 1))
    (s : Cone (diagram U)) : IsMatching U (fun i => s.π.app (faceObj i)) :=
  isMatching_of_app_δ U s.π fun _ => rfl

/-- A cone over the truncated slice category is determined by its legs at the `n + 3` faces
`δ_i : ⦋n + 1⦌ ⟶ ⦋n + 2⦌`. -/
private theorem cone_hom_ext {U : SimplicialObject.Truncated C (n + 1)} {T : C}
    {π π' : (Functor.const (slice n)).obj T ⟶ diagram U}
    (h : ∀ i, π.app (faceObj i) = π'.app (faceObj i)) : π = π' := by
  obtain ⟨π₀, -, huq⟩ := (existsUnique_cone_app_δ_eq_iff U T
    fun i => π.app (faceObj i)).mpr (matchingFamily_cone_app_face U (Cone.mk T π))
  exact (huq π fun _ => rfl).trans (huq π' fun i => (h i).symm).symm

/-- A morphism to the vertex of a cone over the truncated slice category factors that cone as
soon as it factors its legs at the `n + 3` faces, a cone being determined by those legs. -/
private theorem comp_π_app_eq_iff {U : SimplicialObject.Truncated C (n + 1)}
    {s t : Cone (diagram U)} (h : t.pt ⟶ s.pt) :
    (∀ j, h ≫ s.π.app j = t.π.app j) ↔ ∀ i, h ≫ s.π.app (faceObj i) = t.π.app (faceObj i) :=
  ⟨fun H _ => H _, fun H j => congrArg (fun σ => NatTrans.app σ j)
    (cone_hom_ext (π := (Functor.const (slice n)).map h ≫ s.π) H)⟩

/-- A cone whose legs at the faces are a universal matching family is a limit cone. -/
private noncomputable def isLimitOfIsUniversal {U : SimplicialObject.Truncated C (n + 1)}
    (s : Cone (diagram U))
    (huniv : ∀ (T : C) (g : Fin (n + 3) → (T ⟶ U _⦋n + 1⦌ₙ₊₁)), IsMatching U g →
      ∃! h : T ⟶ s.pt, ∀ i, h ≫ s.π.app (faceObj i) = g i) :
    IsLimit s :=
  IsLimit.ofExistsUnique fun t =>
    (existsUnique_congr comp_π_app_eq_iff).mpr
      (huniv t.pt _ (matchingFamily_cone_app_face U t))

/-- A limit cone over `(Δ/⦋n + 2⦌)_{≤ n + 1}`, read along the identification `postEquiv n` as a
limit cone over the slice taken inside the `(n + 2)`-truncated simplex category. -/
private noncomputable def isLimitWhiskerPost {U : SimplicialObject.Truncated C (n + 1)}
    {s : Cone (diagram U)} (hs : IsLimit s) : IsLimit (s.whisker (postEquiv n)) :=
  hs.whiskerEquivalence (postEquiv n).asEquivalence

/-- `U` admits a pointwise right Kan extension along `inclOp n` as soon as `U` has a limit over the
truncated slice category of `⦋n + 2⦌`. -/
private theorem hasPointwiseRightKanExtension_of_isLimit
    {U : SimplicialObject.Truncated C (n + 1)} {s : Cone (diagram U)} (hs : IsLimit s) :
    (inclOp n).HasPointwiseRightKanExtension U := by
  intro d
  obtain ⟨⟨x, hx⟩⟩ := d
  by_cases hd : x.len ≤ n + 1
  · exact (inferInstance :
      HasLimit (StructuredArrow.proj ((inclOp n).obj (op ⟨x, hd⟩)) (inclOp n) ⋙ U))
  · obtain ⟨m⟩ := x
    obtain rfl : m = n + 2 := by dsimp only at hx hd; omega
    exact ⟨_, isLimitWhiskerPost hs⟩

end OneStepExtension

/-- **Stacks 0187**.
One-step extension of a truncated simplicial object, and its adjointness. Let `U` be an
`(n + 1)`-truncated simplicial object of `C`, and suppose that the contravariant functor sending
`T` to the set of families `(g_0, …, g_{n + 2})` of morphisms `T ⟶ U_{n + 1}` with
`d_{j - 1} ∘ g_i = d_i ∘ g_j` for `i < j` is representable: it is represented by an object `Y`
together with a universal such family `f`. Then `U` extends to an `(n + 2)`-truncated simplicial
object `Ũ` whose `(n + 1)`-skeleton is identified with `U` by an isomorphism `α` and whose degree
`n + 2` part is identified with `Y` compatibly with the faces, such that `(Ũ, α)` is a right Kan
extension of `U` along the inclusion of truncated simplex categories; the latter is the adjointness
`Mor(V, Ũ) = Mor(sk_{n + 1} V, U)`, natural in `V` and given by restricting along the skeleton. -/
@[stacks 0187 "the adjointness is stated as the universal property of a right Kan extension \
  along the inclusion of the truncated simplex categories"]
public theorem exists_isRightKanExtension_of_matchingFamily {n : ℕ}
    (U : SimplicialObject.Truncated C (n + 1)) (Y : C)
    (f : Fin (n + 3) → (Y ⟶ U _⦋n + 1⦌ₙ₊₁))
    (hf : ∀ i j : Fin (n + 2), i ≤ j →
      f i.castSucc ≫ U.map (SimplexCategory.Truncated.δ (n + 1) j (by trunc) (by trunc)).op =
        f j.succ ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op)
    (huniv : ∀ (T : C) (g : Fin (n + 3) → (T ⟶ U _⦋n + 1⦌ₙ₊₁)),
      (∀ i j : Fin (n + 2), i ≤ j →
        g i.castSucc ≫ U.map (SimplexCategory.Truncated.δ (n + 1) j (by trunc) (by trunc)).op =
          g j.succ ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op) →
      ∃! h : T ⟶ Y, ∀ i, h ≫ f i = g i) :
    ∃ (Ũ : SimplicialObject.Truncated C (n + 2))
      (α : (SimplicialObject.Truncated.trunc C (n + 2) (n + 1)).obj Ũ ⟶ U),
      IsIso α ∧ Ũ.IsRightKanExtension α ∧
        ∃ e : Ũ _⦋n + 2⦌ₙ₊₂ ≅ Y, ∀ i : Fin (n + 3),
          e.hom ≫ f i =
            Ũ.map (SimplexCategory.Truncated.δ (n + 2) i (by trunc) (by trunc)).op ≫
              α.app (op ⦋n + 1⦌ₙ₊₁) := by
  obtain ⟨π, hπ, -⟩ := (existsUnique_cone_app_δ_eq_iff U Y f).mpr hf
  have hlim : IsLimit (Cone.mk Y π) :=
    isLimitOfIsUniversal _ fun T g hg => by simpa only [hπ] using huniv T g hg
  have hpt : (inclOp n).HasPointwiseRightKanExtension U :=
    hasPointwiseRightKanExtension_of_isLimit hlim
  have hpw := Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension (inclOp n) U
  have hpw₂ := hpw (op ⦋n + 2⦌ₙ₊₂)
  rw [Functor.RightExtension.IsPointwiseRightKanExtensionAt] at hpw₂
  refine ⟨(inclOp n).pointwiseRightKanExtension U,
    (inclOp n).pointwiseRightKanExtensionCounit U, hpw.isIso_hom, inferInstance,
    IsLimit.conePointUniqueUpToIso hpw₂ (isLimitWhiskerPost hlim), fun i => ?_⟩
  rw [← hπ i]
  exact IsLimit.conePointUniqueUpToIso_hom_comp hpw₂ (isLimitWhiskerPost hlim)
    (StructuredArrow.mk (Y := op ⦋n + 1⦌ₙ₊₁)
      (SimplexCategory.Truncated.δ (n + 2) i (by trunc) (by trunc)).op)

end CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory.SimplicialObject

open Limits _root_.CategoryTheory.Functor

section KanExtension

variable {A B D H : Type*} [Category A] [Category B] [Category D] [Category H]

/-- A right extension whose universal property holds as a bijection of hom-sets is a right Kan
extension. -/
private lemma isRightKanExtension_of_bijective {L : A ⥤ D} {F : A ⥤ H} (F' : D ⥤ H)
    (α : L ⋙ F' ⟶ F)
    (hα : ∀ G : D ⥤ H, Function.Bijective (fun φ : G ⟶ F' ↦ whiskerLeft L φ ≫ α)) :
    F'.IsRightKanExtension α where
  nonempty_isUniversal := ⟨IsTerminal.ofUniqueHom
    (fun E ↦ CostructuredArrow.homMk ((Equiv.ofBijective _ (hα E.left)).symm E.hom)
      ((Equiv.ofBijective _ (hα E.left)).apply_symm_apply E.hom))
    fun E φ ↦ CostructuredArrow.hom_ext _ _ <| (hα E.left).injective <|
      (CostructuredArrow.w φ).trans
        ((Equiv.ofBijective _ (hα E.left)).apply_symm_apply E.hom).symm⟩

/-- If `L₂` is fully faithful and `X` is a pointwise right Kan extension of `F` along `L₁ ⋙ L₂`,
then `L₂ ⋙ X` is a right Kan extension of `F` along `L₁`, with the same structure map. -/
private lemma isRightKanExtension_restrict_of_comp (L₁ : A ⥤ B) (L₂ : B ⥤ D) [L₂.Full]
    [L₂.Faithful] {F : A ⥤ H} (X : D ⥤ H) (α : (L₁ ⋙ L₂) ⋙ X ⟶ F)
    [(L₁ ⋙ L₂).HasPointwiseRightKanExtension F] [X.IsRightKanExtension α] :
    (L₂ ⋙ X).IsRightKanExtension (L := L₁) α :=
  Functor.RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (E := Functor.RightExtension.mk (L := L₁) (L₂ ⋙ X) α) fun Y ↦
      Truncated.restrictIsPointwiseRightKanExtensionAt (Functor.RightExtension.mk X α) Y
        (Functor.isPointwiseRightKanExtensionOfIsRightKanExtension X α _)

/-- Right Kan extensions compose: if `L₂` is fully faithful and `X` is a pointwise right Kan
extension of `F` along `L₁ ⋙ L₂`, then `X` is a right Kan extension of `L₂ ⋙ X` along `L₂`, via
the identity. -/
private lemma isRightKanExtension_id_of_comp (L₁ : A ⥤ B) (L₂ : B ⥤ D) [L₂.Full] [L₂.Faithful]
    {F : A ⥤ H} (X : D ⥤ H) (α : (L₁ ⋙ L₂) ⋙ X ⟶ F)
    [(L₁ ⋙ L₂).HasPointwiseRightKanExtension F] [X.IsRightKanExtension α] :
    X.IsRightKanExtension (𝟙 (L₂ ⋙ X)) := by
  have := isRightKanExtension_restrict_of_comp L₁ L₂ X α
  refine isRightKanExtension_of_bijective _ _ fun G ↦ ?_
  have key : (fun φ : G ⟶ X ↦ whiskerLeft L₂ φ ≫ 𝟙 (L₂ ⋙ X)) =
      (Functor.homEquivOfIsRightKanExtension X α G).trans
        (Functor.homEquivOfIsRightKanExtension (L := L₁) (L₂ ⋙ X) α (L₂ ⋙ G)).symm := by
    funext φ
    simp only [Equiv.trans_apply]
    refine (Equiv.eq_symm_apply _).mpr ?_
    ext a
    simp
  rw [key]
  exact Equiv.bijective _

/-- Precomposition with `L` is left adjoint to any functor `R` equipped with a natural
transformation `ε` exhibiting each `R.obj F` as a right Kan extension of `F` along `L`. This is
`Functor.ranAdjunction` for a chosen right Kan extension functor rather than for `L.ran`. -/
private noncomputable def adjunctionOfIsRightKanExtension (L : A ⥤ B) (R : (A ⥤ H) ⥤ (B ⥤ H))
    (ε : R ⋙ (whiskeringLeft A B H).obj L ⟶ 𝟭 _)
    (hR : ∀ F, (R.obj F).IsRightKanExtension (ε.app F)) :
    (whiskeringLeft A B H).obj L ⊣ R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G F ↦
        have := hR F
        (Functor.homEquivOfIsRightKanExtension (α := ε.app F) _ G).symm
      homEquiv_naturality_right := fun {G F₁ F₂} β f ↦ by
        have := hR F₁
        have := hR F₂
        refine Functor.hom_ext_of_isRightKanExtension _ (ε.app F₂) _ _ ?_
        ext X
        dsimp [Functor.homEquivOfIsRightKanExtension]
        rw [Functor.liftOfIsRightKanExtension_fac_app, NatTrans.comp_app, Category.assoc]
        have h := congr_app (ε.naturality f) X
        dsimp at h ⊢
        rw [h, Functor.liftOfIsRightKanExtension_fac_app_assoc]
      homEquiv_naturality_left_symm := fun {G₁ G₂ F} β f ↦ by
        have := hR F
        dsimp [Functor.homEquivOfIsRightKanExtension]
        rw [Category.assoc] }

/-- A fibre product of right Kan extensions is a right Kan extension of the fibre product. Let
`(U', εU)`, `(V', εV)`, `(W', εW)` be right Kan extensions along `L` of `U`, `V`, `W`, and let
`f' : U' ⟶ V'`, `g' : W' ⟶ V'` be compatible with `f : U ⟶ V`, `g : W ⟶ V`. Then
`U' ×_{V'} W'` is a right Kan extension of `U ×_V W`, with the structure map induced by `εU` and
`εW`. -/
private lemma isRightKanExtension_pullback {L : A ⥤ D} {U V W : A ⥤ H} (f : U ⟶ V)
    (g : W ⟶ V) [HasPullback f g] {U' V' W' : D ⥤ H} (εU : L ⋙ U' ⟶ U) (εV : L ⋙ V' ⟶ V)
    (εW : L ⋙ W' ⟶ W) [U'.IsRightKanExtension εU] [V'.IsRightKanExtension εV]
    [W'.IsRightKanExtension εW] (f' : U' ⟶ V') (g' : W' ⟶ V')
    (hf : whiskerLeft L f' ≫ εV = εU ≫ f) (hg : whiskerLeft L g' ≫ εV = εW ≫ g)
    [HasPullback f' g'] :
    (pullback f' g').IsRightKanExtension
      (pullback.lift (whiskerLeft L (pullback.fst f' g') ≫ εU)
        (whiskerLeft L (pullback.snd f' g') ≫ εW) (by
          rw [Category.assoc, Category.assoc, ← hf, ← hg, ← whiskerLeft_comp_assoc,
            ← whiskerLeft_comp_assoc, pullback.condition]) :
        L ⋙ pullback f' g' ⟶ pullback f g) := by
  refine isRightKanExtension_of_bijective _ _ fun G ↦ ⟨fun φ ψ h ↦ ?_, fun β ↦ ?_⟩
  · have h₁ := h =≫ pullback.fst f g
    have h₂ := h =≫ pullback.snd f g
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
    refine pullback.hom_ext (U'.hom_ext_of_isRightKanExtension εU _ _ ?_)
      (W'.hom_ext_of_isRightKanExtension εW _ _ ?_)
    · simpa only [whiskerLeft_comp, Category.assoc] using h₁
    · simpa only [whiskerLeft_comp, Category.assoc] using h₂
  · let a := U'.liftOfIsRightKanExtension εU G (β ≫ pullback.fst f g)
    let b := W'.liftOfIsRightKanExtension εW G (β ≫ pullback.snd f g)
    have hab : a ≫ f' = b ≫ g' := V'.hom_ext_of_isRightKanExtension εV _ _ (by
      simp only [whiskerLeft_comp, Category.assoc, hf, hg, a, b,
        liftOfIsRightKanExtension_fac_assoc, pullback.condition])
    refine ⟨pullback.lift a b hab, pullback.hom_ext ?_ ?_⟩
    · simp only [Category.assoc, pullback.lift_fst, ← whiskerLeft_comp_assoc, a,
        liftOfIsRightKanExtension_fac]
    · simp only [Category.assoc, pullback.lift_snd, ← whiskerLeft_comp_assoc, b,
        liftOfIsRightKanExtension_fac]

end KanExtension

variable {C : Type u} [Category.{v} C]

section TwoLevels

variable {n m : ℕ} (h : n ≤ m)
  [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]

/-- The inclusion `(Δ_{≤n} ⊆ Δ)ᵒᵖ` is the composite of `(Δ_{≤n} ⊆ Δ_{≤m})ᵒᵖ` and `(Δ_{≤m} ⊆ Δ)ᵒᵖ`,
so the coskeleton hypothesis at level `n` provides pointwise right Kan extensions along that
composite. -/
private lemma hasPointwiseRightKanExtension_op_incl_comp
    (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    ((SimplexCategory.Truncated.incl n m h).op ⋙
      (SimplexCategory.Truncated.inclusion m).op).HasPointwiseRightKanExtension F :=
  inferInstanceAs ((SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F)

include h in
/-- A simplicial object which is a right Kan extension of an `n`-truncated object along
`(Δ_{≤n} ⊆ Δ)ᵒᵖ` is `m`-coskeletal for every `m ≥ n`. -/
private lemma isCoskeletal_of_isRightKanExtension' (X : SimplicialObject C)
    {U : SimplicialObject.Truncated C n}
    (α : (SimplexCategory.Truncated.inclusion n).op ⋙ X ⟶ U)
    (hX : X.IsRightKanExtension α) : X.IsCoskeletal m :=
  have := hasPointwiseRightKanExtension_op_incl_comp h U
  have : X.IsRightKanExtension (L := (SimplexCategory.Truncated.incl n m h).op ⋙
    (SimplexCategory.Truncated.inclusion m).op) α := hX
  ⟨isRightKanExtension_id_of_comp (SimplexCategory.Truncated.incl n m h).op
    (SimplexCategory.Truncated.inclusion m).op X α⟩

/-- The `m`-truncation of the `n`-th coskeleton of an `n`-truncated simplicial object `U` is a
right Kan extension of `U` along `(Δ_{≤n} ⊆ Δ_{≤m})ᵒᵖ`, with structure map the counit of
`cosk_n`. -/
private lemma isRightKanExtension_ranCounit_app (U : SimplicialObject.Truncated C n) :
    ((Truncated.cosk n ⋙ truncation m).obj U).IsRightKanExtension
      (L := (SimplexCategory.Truncated.incl n m h).op) (F := U)
      ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app U) :=
  have := hasPointwiseRightKanExtension_op_incl_comp h U
  have : ((Truncated.cosk n).obj U).IsRightKanExtension
      (L := (SimplexCategory.Truncated.incl n m h).op ⋙
        (SimplexCategory.Truncated.inclusion m).op)
      ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app U) :=
    inferInstanceAs ((((SimplexCategory.Truncated.inclusion n).op.ran).obj U).IsRightKanExtension
      ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app U))
  isRightKanExtension_restrict_of_comp _ _ ((Truncated.cosk n).obj U) _

/-- The further truncation `sk_n : Simp_m(C) ⥤ Simp_n(C)` is left adjoint to `sk_m cosk_n`. -/
private noncomputable def truncCoskAdj :
    Truncated.trunc C m n h ⊣ Truncated.cosk n ⋙ truncation m :=
  adjunctionOfIsRightKanExtension (SimplexCategory.Truncated.incl n m h).op _
    (SimplexCategory.Truncated.inclusion n).op.ranCounit (isRightKanExtension_ranCounit_app h)

end TwoLevels

/-- **Stacks 018B** (parts 2, 3 and 4).
Coskeleta of different levels. Let `C` be a category, let `n ≤ m` and assume the `n`-th and `m`-th
coskeleton functors of `C` exist. Then:

* (2) the further truncation `sk_n : Simp_m(C) ⥤ Simp_n(C)` has a right adjoint, namely
  `sk_m cosk_n`;
* (3) for every `n`-truncated simplicial object `U` of `C` the canonical map
  `cosk_n U ⟶ cosk_m sk_m cosk_n U` is an isomorphism, i.e. `cosk_m sk_m cosk_n U = cosk_n U`;
* (4) if the canonical map `X ⟶ cosk_n sk_n X` is an isomorphism for a simplicial object `X` of
  `C`, then so is the canonical map `X ⟶ cosk_m sk_m X`. -/
@[stacks 018B "parts (2), (3) and (4); part (1) is the hypothesis that the coskeleta exist, \
  i.e. Tag 0183 for a category with finite limits", sga "4 V 7.1.2" "1) cosk composition"]
public theorem nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app {n m : ℕ} (h : n ≤ m)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion m).op.HasPointwiseRightKanExtension F] :
    Nonempty (Truncated.trunc C m n h ⊣ Truncated.cosk n ⋙ truncation m) ∧
      (∀ U : SimplicialObject.Truncated C n,
        IsIso ((coskAdj m).unit.app ((Truncated.cosk n).obj U))) ∧
      (∀ X : SimplicialObject C,
        IsIso ((coskAdj n).unit.app X) → IsIso ((coskAdj m).unit.app X)) :=
  ⟨⟨truncCoskAdj h⟩,
    fun U ↦ (SimplicialObject.isCoskeletal_iff_isIso _ m).mp
      (isCoskeletal_of_isRightKanExtension' h _
        ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app U) inferInstance),
    fun X hX ↦
      have hc : X.IsCoskeletal n := (SimplicialObject.isCoskeletal_iff_isIso X n).mpr hX
      (SimplicialObject.isCoskeletal_iff_isIso X m).mp
        (isCoskeletal_of_isRightKanExtension' h X _ hc.isRightKanExtension)⟩

end CategoryTheory.SimplicialObject

namespace CategoryTheory.SimplicialObject.Truncated

open Limits

variable {C : Type u} [Category.{v} C]

/-- The `n`-th coskeleton functor `cosk n : Simp_n(C) ⥤ Simp(C)`, when it exists on all of
`Simp_n(C)`, preserves all limits, being right adjoint to `truncation n`. In particular it
commutes with fibre products; the form of Stacks 018D that assumes only the existence of the
coskeleta involved is `isIso_pullback_lift_coskMap`. -/
public instance cosk.preservesLimitsOfSize (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    PreservesLimitsOfSize.{w, w'} (Truncated.cosk (C := C) n) :=
  (SimplicialObject.coskAdj n).rightAdjoint_preservesLimits

/-- The morphism `cosk_n U ⟶ cosk_n V` induced by a morphism `f : U ⟶ V` of `n`-truncated
simplicial objects, for `U` and `V` whose coskeleta exist (as chosen right Kan extensions along
`(Δ_{≤ n} ⊆ Δ)ᵒᵖ`); it is the morphism corresponding to `sk_n cosk_n U ⟶ U ⟶ V` under the
universal property of `cosk_n V`. -/
public noncomputable def coskMap {n : ℕ} {U V : SimplicialObject.Truncated C n}
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension U]
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension V] (f : U ⟶ V) :
    (SimplexCategory.Truncated.inclusion n).op.rightKanExtension U ⟶
      (SimplexCategory.Truncated.inclusion n).op.rightKanExtension V :=
  ((SimplexCategory.Truncated.inclusion n).op.rightKanExtension V).liftOfIsRightKanExtension
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit V) _
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit U ≫ f)

/-- The morphism `coskMap f` is compatible with the structure maps of the coskeleta. -/
@[reassoc (attr := simp)]
public lemma whiskerLeft_coskMap_comp_counit {n : ℕ} {U V : SimplicialObject.Truncated C n}
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension U]
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension V] (f : U ⟶ V) :
    Functor.whiskerLeft (SimplexCategory.Truncated.inclusion n).op (coskMap f) ≫
        (SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit V =
      (SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit U ≫ f :=
  Functor.liftOfIsRightKanExtension_fac _ _ _ _

/-- `coskMap` is compatible with composition. -/
public lemma coskMap_comp {n : ℕ} {U V W : SimplicialObject.Truncated C n}
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension U]
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension V]
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension W]
    (f : U ⟶ V) (g : V ⟶ W) : coskMap (f ≫ g) = coskMap f ≫ coskMap g := by
  refine Functor.rightKanExtension_hom_ext _ _ _ _ ?_
  simp [Functor.whiskerLeft_comp]

/-- **Stacks 018D**.
Let `C` be a category with fibre products, and let `f : U ⟶ V`, `g : W ⟶ V` be morphisms of
`n`-truncated simplicial objects of `C`. Whenever the coskeleta `cosk_n U`, `cosk_n V`,
`cosk_n W` and `cosk_n (U ×_V W)` exist (as right Kan extensions along `(Δ_{≤ n} ⊆ Δ)ᵒᵖ`, not
assuming that the coskeleton functor exists), the canonical comparison morphism
`cosk_n (U ×_V W) ⟶ cosk_n U ×_{cosk_n V} cosk_n W`, with components `cosk_n` of the two
projections, is an isomorphism. The fibre product on the right exists since `C` has fibre
products. -/
@[stacks 018D "the equality is the statement that the canonical comparison morphism is an \
  isomorphism; the coskeleta are the right Kan extensions along `(Δ_{≤ n} ⊆ Δ)ᵒᵖ`, assumed to \
  exist for `U`, `V`, `W` and `U ×_V W` only"]
public theorem isIso_pullback_lift_coskMap [HasPullbacks C] {n : ℕ}
    {U V W : SimplicialObject.Truncated C n} (f : U ⟶ V) (g : W ⟶ V)
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension U]
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension V]
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension W]
    [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension (pullback f g)] :
    IsIso (pullback.lift (coskMap (pullback.fst f g)) (coskMap (pullback.snd f g))
      (by rw [← coskMap_comp, ← coskMap_comp, pullback.condition]) :
      (SimplexCategory.Truncated.inclusion n).op.rightKanExtension (pullback f g) ⟶
        pullback (coskMap f) (coskMap g)) := by
  have := SimplicialObject.isRightKanExtension_pullback f g
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit U)
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit V)
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit W)
    (coskMap f) (coskMap g) (whiskerLeft_coskMap_comp_counit f)
    (whiskerLeft_coskMap_comp_counit g)
  refine (Functor.isRightKanExtension_iff_isIso _
    (pullback.lift
      (Functor.whiskerLeft _ (pullback.fst (coskMap f) (coskMap g)) ≫
        (SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit U)
      (Functor.whiskerLeft _ (pullback.snd (coskMap f) (coskMap g)) ≫
        (SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit W) _)
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit (pullback f g)) ?_).mp
    inferInstance
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, ← Functor.whiskerLeft_comp_assoc, pullback.lift_fst,
      whiskerLeft_coskMap_comp_counit]
  · rw [Category.assoc, pullback.lift_snd, ← Functor.whiskerLeft_comp_assoc, pullback.lift_snd,
      whiskerLeft_coskMap_comp_counit]

end CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory.Functor

/-- **A functor preserving connected limits preserves the pointwise right Kan extensions along a
final functor.** The limit computing a pointwise right Kan extension along `L : J ⥤ K` at `k : K`
is indexed by the comma category `StructuredArrow k L`, which is connected precisely because `L`
is final, so preservation of connected limits of that one shape is all that is used. -/
public lemma preservesPointwiseRightKanExtensions_of_final {J : Type u₁} [Category.{v₁} J]
    {K : Type u₂} [Category.{v₂} K] {B : Type u} [Category.{v} B] {D : Type w}
    [Category.{w'} D] (G : B ⥤ D) (L : J ⥤ K) [L.Final]
    (hG : ∀ (I : Type (max u₁ v₂)) [Category.{v₁} I] [IsConnected I],
      Limits.PreservesLimitsOfShape I G) :
    G.PreservesPointwiseRightKanExtensions L := by
  intro Z k
  have := hG (StructuredArrow k L)
  infer_instance

end CategoryTheory.Functor

namespace CategoryTheory.Over

/-- The forgetful functor `Over.forget X : C/X ⥤ C` of a slice category preserves the pointwise
right Kan extensions along a final functor `L : J ⥤ K`. -/
private lemma preservesPointwiseRightKanExtensions_forget_of_final {J : Type u₁}
    [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K] {C : Type u} [Category.{v} C] (X : C)
    (L : J ⥤ K) [L.Final] : (Over.forget X).PreservesPointwiseRightKanExtensions L :=
  fun _ _ => inferInstance

variable {C : Type u} [Category.{v} C]

/-- **Stacks 08NJ**.
For a category `C` and an object `X : C`, the forgetful functor `Over.forget X : C/X ⥤ C` commutes
with the coskeleton functors `cosk_m` for `m ≥ 1`: it carries a pointwise right Kan extension along
`(Δ_{≤m} ⊆ Δ)ᵒᵖ` of an `m`-truncated simplicial object of `C/X`, with its structure map, to one of
the underlying `m`-truncated simplicial object of `C`. Hence `cosk_m U` computed in `C/X` is
computed in `C`, the comparison being the whiskering of the structure map. -/
@[stacks 08NJ "stated as preservation of the pointwise right Kan extensions along \
  `(Δ_{≤m} ⊆ Δ)ᵒᵖ`, which is what \"cosk_m computed in C/X is computed in C\" says with the \
  comparison map pinned; the source's finite limits in `C` are not needed"]
public instance preservesPointwiseRightKanExtensions_forget_inclusion_succ_op (X : C) (k : ℕ) :
    (Over.forget X).PreservesPointwiseRightKanExtensions
      (SimplexCategory.Truncated.inclusion (k + 1)).op :=
  preservesPointwiseRightKanExtensions_forget_of_final X _

end CategoryTheory.Over

end

/-!
## The limit of a truncated simplicial object over a truncated slice category

Let `C` be a category and let `U` be an `m`-truncated simplicial object of `C`, that is a functor
`(Δ_{≤ m})ᵒᵖ ⥤ C`. For `n : ℕ` the truncated slice category `(Δ/[n])_{≤ m}` has as objects the
morphisms `α : [k] → [n]` of the simplex category with `k ≤ m`, and as morphisms `α' → α` the
maps `ψ : [k'] → [k]` with `α ∘ ψ = α'`; the diagram `U(n) : ((Δ/[n])_{≤ m})ᵒᵖ ⥤ C` sends such an
`α` to `U_k` and such a `ψ` to `U(ψ) : U_k → U_{k'}`. For `n ≤ m` the limit of `U(n)` exists in
`C` and is canonically isomorphic to `U_n`: the cone with apex `U_n` whose component at
`α : [k] → [n]` is `U(α) : U_n → U_k` is a limit cone. This is because `id_{[n]} : [n] → [n]`
lies in `(Δ/[n])_{≤ m}` when `n ≤ m` and is a final object there, so that it is an initial object
of the opposite category and the limit is the value of the diagram at it.

### Main definitions

* `TruncSlice`: the truncated slice category `(Δ/[n])_{≤ m}`.
* `nTrunc`: the object `[n]` of the `m`-truncated simplex category, available for `n ≤ m`.
* `sliceDiagram`: the diagram `U(n) : ((Δ/[n])_{≤ m})ᵒᵖ ⥤ C`.
* `sliceConeComponent`: the morphism `U(α) : U_n → U_k` attached to an object `α : [k] → [n]`.
* `sliceCone`: the cone over `U(n)` with apex `U_n` and components `sliceConeComponent`.

### Main results

* `sliceCone_pt`, `sliceCone_π_app`: the apex of `sliceCone` is `U_n` and its component at
  `α` is `sliceConeComponent`.
* `sliceCone_isLimit`: `sliceCone` is a limit cone, for `n ≤ m`.
* `hasLimit_sliceDiagram`: the diagram `U(n)` has a limit, for `n ≤ m`.
* `nonempty_limit_sliceDiagram_iso`: that limit is isomorphic to `U_n`.

### References

* [Stacks, Tag 0184](https://stacks.math.columbia.edu/tag/0184)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type*} [Category C]

/-- The truncated slice category `(Δ/[n])_{≤ m}`, whose objects are the morphisms
`α : [k] → [n]` of the simplex category with `k ≤ m` and whose morphisms `α' → α` are the
simplex-category maps `ψ : [k'] → [k]` with `α ∘ ψ = α'`, realized as the category of
`CostructuredArrow` objects over `[n]` for the inclusion of the `m`-truncated simplex
category. -/
@[sga "4 Vbis 3.0.1"]
abbrev TruncSlice (m n : ℕ) : Type :=
  CostructuredArrow (SimplexCategory.Truncated.inclusion m) (SimplexCategory.mk n)

/-- The object `[n]` viewed as an object of the `m`-truncated simplex category,
available precisely when `n ≤ m`. -/
abbrev nTrunc {m n : ℕ} (h : n ≤ m) : SimplexCategory.Truncated m :=
  ⟨SimplexCategory.mk n, by simpa using h⟩

/-- The diagram `U(n) : ((Δ/[n])_{≤ m})ᵒᵖ ⥤ C`, the composite of the opposite of the projection
`(Δ/[n])_{≤ m} → Δ_{≤ m}` with `U`. It sends an object `α : [k] → [n]` to `U_k = U([k])` and a
morphism `ψ : α' → α` with underlying simplex map `ψ : [k'] → [k]` to `U(ψ) : U_k → U_{k'}`. -/
@[implicit_reducible]
noncomputable def sliceDiagram (m : ℕ) (U : SimplicialObject.Truncated C m) (n : ℕ) :
    (TruncSlice m n)ᵒᵖ ⥤ C :=
  (CostructuredArrow.proj (SimplexCategory.Truncated.inclusion m) (SimplexCategory.mk n)).op ⋙ U

/-- The morphism `U(α) : U_n → U_k` attached to an object `α : [k] → [n]` of the truncated slice
category, where `U_n = U([n])` makes sense because `n ≤ m`. It is `U` applied to the lift of `α`
to `Δ_{≤ m}`. -/
noncomputable def sliceConeComponent {m n : ℕ} (U : SimplicialObject.Truncated C m) (h : n ≤ m)
    (α : TruncSlice m n) :
    U.obj (Opposite.op (nTrunc h)) ⟶ (sliceDiagram m U n).obj (Opposite.op α) :=
  U.map (Opposite.op ((SimplexCategory.Truncated.inclusion m).preimage α.hom))

/-- For `n ≤ m`, the identity `id_{[n]} : [n] → [n]` is a final object of the truncated slice
category `(Δ/[n])_{≤ m}`. -/
noncomputable def sliceIdIsTerminal {m n : ℕ} (h : n ≤ m) :
    IsTerminal (CostructuredArrow.mk (S := SimplexCategory.Truncated.inclusion m)
      (Y := nTrunc h) (𝟙 _)) :=
  CostructuredArrow.mkIdTerminal

/-- Dually, `id_{[n]}` is an initial object of `(Δ/[n])_{≤ m}^opp`. -/
noncomputable def sliceOpIdIsInitial {m n : ℕ} (h : n ≤ m) :
    Limits.IsInitial (Opposite.op (CostructuredArrow.mk (S := SimplexCategory.Truncated.inclusion m)
      (Y := nTrunc h) (𝟙 _))) :=
  initialOpOfTerminal (sliceIdIsTerminal h)

/-- The cone over `U(n)` with apex `U_n` and components the morphisms `U(α)`, obtained from the
initial object `id_{[n]}` of `((Δ/[n])_{≤ m})ᵒᵖ`. -/
@[implicit_reducible]
noncomputable def sliceCone {m n : ℕ} (U : SimplicialObject.Truncated C m) (h : n ≤ m) :
    Cone (sliceDiagram m U n) :=
  coneOfDiagramInitial (sliceOpIdIsInitial h) (sliceDiagram m U n)

/-- The apex of the canonical cone is `U_n`. -/
theorem sliceCone_pt {m : ℕ} (U : SimplicialObject.Truncated C m) {n : ℕ} (h : n ≤ m) :
    (sliceCone U h).pt = U.obj (Opposite.op (nTrunc h)) :=
  rfl

/-- The component of the canonical cone at an object `α : [k] → [n]` is the morphism
`U(α) : U_n → U_k`. -/
theorem sliceCone_π_app {m : ℕ} (U : SimplicialObject.Truncated C m) {n : ℕ} (h : n ≤ m)
    (α : TruncSlice m n) :
    (sliceCone U h).π.app (Opposite.op α) = sliceConeComponent U h α := by
  simp only [sliceCone, coneOfDiagramInitial, sliceConeComponent, sliceDiagram]
  rw [Functor.comp_map]
  congr 1

/-- **Stacks 0184**.
Let `C` be a category and let `U` be an `m`-truncated simplicial object of `C`. For `n ≤ m` the
limit of the diagram `U(n)` exists in `C` and is canonically isomorphic to `U_n`: the canonical
cone, with apex `U_n` and component `U(α) : U_n → U_k` at an object `α : [k] → [n]`, is a limit
cone. -/
@[stacks 0184]
theorem sliceCone_isLimit {m : ℕ} (U : SimplicialObject.Truncated C m) {n : ℕ} (h : n ≤ m) :
    Nonempty (IsLimit (sliceCone U h)) :=
  ⟨limitOfDiagramInitial (sliceOpIdIsInitial h) (sliceDiagram m U n)⟩

/-- For `n ≤ m` the diagram `U(n)` has a limit in `C`. -/
theorem hasLimit_sliceDiagram {m : ℕ} (U : SimplicialObject.Truncated C m) {n : ℕ} (h : n ≤ m) :
    HasLimit (sliceDiagram m U n) :=
  HasLimit.mk ⟨sliceCone U h, limitOfDiagramInitial (sliceOpIdIsInitial h) (sliceDiagram m U n)⟩

/-- For `n ≤ m` the limit object of the diagram `U(n)` is isomorphic to `U_n`. -/
theorem nonempty_limit_sliceDiagram_iso {m : ℕ} (U : SimplicialObject.Truncated C m) {n : ℕ}
    (h : n ≤ m)
    [HasLimit (sliceDiagram m U n)] :
    Nonempty (limit (sliceDiagram m U n) ≅ U.obj (Opposite.op (nTrunc h))) :=
  ⟨(limit.isLimit (sliceDiagram m U n)).conePointUniqueUpToIso
    (limitOfDiagramInitial (sliceOpIdIsInitial h) (sliceDiagram m U n))⟩

end CategoryTheory.SimplicialObject.Truncated

end

end

/-!
## The coskeleton of a product of truncated simplicial objects

Let `C` be a category and let `U`, `V` be `n`-truncated simplicial objects of `C`, that is
functors `(Δ_{≤ n})ᵒᵖ ⥤ C`. The coskeleton `cosk_n W` of a single truncated simplicial object
`W` exists when `W` has a right Kan extension along the inclusion `(Δ_{≤ n})ᵒᵖ ⥤ Δᵒᵖ`: the
counit `sk_n cosk_n W ⟶ W` then induces bijections `Mor(T, cosk_n W) = Mor(sk_n T, W)` for every
simplicial object `T`. Whenever `cosk_n U`, `cosk_n V`, `cosk_n (U ⨯ V)` and the products
`U ⨯ V` in `Simp_n(C)` and `cosk_n U ⨯ cosk_n V` in `Simp(C)` exist, the canonical comparison
morphism `cosk_n (U ⨯ V) ⟶ cosk_n U ⨯ cosk_n V` is an isomorphism. The proof uses the universal
property of each of the three right Kan extensions separately, so no other coskeleton, and no
completeness assumption on `C`, is needed. The source states the conclusion as an equality of
coskeleta; since a coskeleton is determined by a universal property, its content is that this
*canonical* map is invertible.

When the whole coskeleton functor `Truncated.cosk n` exists, the comparison morphism is
`prodComparison (Truncated.cosk n) U V`, and the statement is also an instance of the
preservation of limits by a right adjoint.

### Main definitions

* `prodLiftOfIsRightKanExtension`: for right Kan extensions `CU`, `CV`, `CUV` of `U`, `V`,
  `U ⨯ V`, the canonical morphism `CUV ⟶ CU ⨯ CV`.
* `prodIsoOfIsRightKanExtension`: the resulting isomorphism `CUV ≅ CU ⨯ CV`.
* `rightKanExtensionProdIso`: the isomorphism `cosk_n (U ⨯ V) ≅ cosk_n U ⨯ cosk_n V`, assuming
  only that these three coskeleta and the two products exist.
* `coskProdIso`: the same isomorphism, when the whole coskeleton functor exists.

### Main results

* `isIso_prodLiftOfIsRightKanExtension`: the canonical morphism `CUV ⟶ CU ⨯ CV` is an
  isomorphism.
* `isIso_prodComparison_cosk`: the comparison morphism
  `prodComparison (Truncated.cosk n) U V` is an isomorphism.
* `coskProdIso_hom`: the underlying morphism of `coskProdIso` is that comparison
  morphism.

### References

* [Stacks, Tag 018C](https://stacks.math.columbia.edu/tag/018C)
-/

section

@[expose] public section

open CategoryTheory SimplicialObject Limits

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

section general

variable {n : ℕ} {U V : SimplicialObject.Truncated C n} [HasBinaryProduct U V]
  {CU CV CUV : SimplicialObject C}
  (αU : (SimplexCategory.Truncated.inclusion n).op ⋙ CU ⟶ U) [CU.IsRightKanExtension αU]
  (αV : (SimplexCategory.Truncated.inclusion n).op ⋙ CV ⟶ V) [CV.IsRightKanExtension αV]
  (αUV : (SimplexCategory.Truncated.inclusion n).op ⋙ CUV ⟶ U ⨯ V)
  [CUV.IsRightKanExtension αUV] [HasBinaryProduct CU CV]

/-- For right Kan extensions `(CU, αU)`, `(CV, αV)` and `(CUV, αUV)` of `n`-truncated simplicial
objects `U`, `V` and `U ⨯ V` along the inclusion `(Δ_{≤ n})ᵒᵖ ⥤ Δᵒᵖ`, the canonical morphism
`CUV ⟶ CU ⨯ CV`, whose components are induced by the projections of `U ⨯ V`. -/
noncomputable def prodLiftOfIsRightKanExtension : CUV ⟶ CU ⨯ CV :=
  prod.lift (CU.liftOfIsRightKanExtension αU CUV (αUV ≫ prod.fst))
    (CV.liftOfIsRightKanExtension αV CUV (αUV ≫ prod.snd))

/-- The inverse of `prodLiftOfIsRightKanExtension`, induced by the universal property of `CUV`. -/
noncomputable def prodLiftOfIsRightKanExtensionInv : CU ⨯ CV ⟶ CUV :=
  CUV.liftOfIsRightKanExtension αUV (CU ⨯ CV)
    (prod.lift (Functor.whiskerLeft _ prod.fst ≫ αU) (Functor.whiskerLeft _ prod.snd ≫ αV))

omit [CUV.IsRightKanExtension αUV] in
@[reassoc (attr := simp)]
lemma prodLiftOfIsRightKanExtension_fst :
    prodLiftOfIsRightKanExtension αU αV αUV ≫ prod.fst =
      CU.liftOfIsRightKanExtension αU CUV (αUV ≫ prod.fst) :=
  prod.lift_fst _ _

omit [CUV.IsRightKanExtension αUV] in
@[reassoc (attr := simp)]
lemma prodLiftOfIsRightKanExtension_snd :
    prodLiftOfIsRightKanExtension αU αV αUV ≫ prod.snd =
      CV.liftOfIsRightKanExtension αV CUV (αUV ≫ prod.snd) :=
  prod.lift_snd _ _

@[reassoc (attr := simp)]
lemma prodLiftOfIsRightKanExtension_hom_inv_id :
    prodLiftOfIsRightKanExtension αU αV αUV ≫ prodLiftOfIsRightKanExtensionInv αU αV αUV =
      𝟙 CUV := by
  apply CUV.hom_ext_of_isRightKanExtension αUV
  apply prod.hom_ext <;>
    simp [prodLiftOfIsRightKanExtensionInv, ← Functor.whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
lemma prodLiftOfIsRightKanExtension_inv_hom_id :
    prodLiftOfIsRightKanExtensionInv αU αV αUV ≫ prodLiftOfIsRightKanExtension αU αV αUV =
      𝟙 (CU ⨯ CV) := by
  apply prod.hom_ext
  · apply CU.hom_ext_of_isRightKanExtension αU
    simp [prodLiftOfIsRightKanExtensionInv]
  · apply CV.hom_ext_of_isRightKanExtension αV
    simp [prodLiftOfIsRightKanExtensionInv]

/-- For right Kan extensions `CU`, `CV`, `CUV` of `n`-truncated simplicial objects `U`, `V` and
`U ⨯ V` along the inclusion `(Δ_{≤ n})ᵒᵖ ⥤ Δᵒᵖ`, the canonical morphism `CUV ⟶ CU ⨯ CV` is an
isomorphism, whenever the product `CU ⨯ CV` exists. -/
theorem isIso_prodLiftOfIsRightKanExtension :
    IsIso (prodLiftOfIsRightKanExtension αU αV αUV) :=
  ⟨prodLiftOfIsRightKanExtensionInv αU αV αUV, by simp, by simp⟩

/-- For right Kan extensions `CU`, `CV`, `CUV` of `n`-truncated simplicial objects `U`, `V` and
`U ⨯ V` along the inclusion `(Δ_{≤ n})ᵒᵖ ⥤ Δᵒᵖ`, the canonical isomorphism `CUV ≅ CU ⨯ CV`,
with underlying morphism `prodLiftOfIsRightKanExtension`. -/
@[simps]
noncomputable def prodIsoOfIsRightKanExtension : CUV ≅ CU ⨯ CV where
  hom := prodLiftOfIsRightKanExtension αU αV αUV
  inv := prodLiftOfIsRightKanExtensionInv αU αV αUV

end general

section single

variable (n : ℕ) (U V : SimplicialObject.Truncated C n) [HasBinaryProduct U V]
  [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension U]
  [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension V]
  [(SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension (U ⨯ V)]
  [HasBinaryProduct ((SimplexCategory.Truncated.inclusion n).op.rightKanExtension U)
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtension V)]

/-- **Stacks 018C**.
For `n`-truncated simplicial objects `U`, `V` of `C`, the canonical isomorphism
`cosk_n (U ⨯ V) ≅ cosk_n U ⨯ cosk_n V`, whenever the coskeleta `cosk_n U`, `cosk_n V`,
`cosk_n (U ⨯ V)` (right Kan extensions along `(Δ_{≤ n})ᵒᵖ ⥤ Δᵒᵖ`) and the products `U ⨯ V`,
`cosk_n U ⨯ cosk_n V` exist. Its underlying morphism is the canonical comparison morphism
(`rightKanExtensionProdIso_hom`). -/
@[stacks 018C "the coskeleton of a single truncated simplicial object is its right Kan \
extension along the inclusion of truncated simplex categories; the equality is the canonical \
isomorphism, whose underlying morphism is the comparison morphism"]
noncomputable def rightKanExtensionProdIso :
    (SimplexCategory.Truncated.inclusion n).op.rightKanExtension (U ⨯ V) ≅
      (SimplexCategory.Truncated.inclusion n).op.rightKanExtension U ⨯
        (SimplexCategory.Truncated.inclusion n).op.rightKanExtension V :=
  prodIsoOfIsRightKanExtension
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit U)
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit V)
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit (U ⨯ V))

/-- The underlying morphism of `rightKanExtensionProdIso` is the canonical comparison morphism
`cosk_n (U ⨯ V) ⟶ cosk_n U ⨯ cosk_n V` induced by the projections of `U ⨯ V`. -/
theorem rightKanExtensionProdIso_hom :
    (rightKanExtensionProdIso n U V).hom = prodLiftOfIsRightKanExtension
      ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit U)
      ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit V)
      ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit (U ⨯ V)) :=
  rfl

end single

/-- When the whole coskeleton functor exists, the comparison morphism
`prodComparison (Truncated.cosk n) U V` is the underlying morphism of
`rightKanExtensionProdIso`. -/
theorem prodComparison_cosk_eq_rightKanExtensionProdIso_hom (n : ℕ)
    [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
    (U V : SimplicialObject.Truncated C n)
    [HasBinaryProduct U V]
    [HasBinaryProduct ((Truncated.cosk n).obj U) ((Truncated.cosk n).obj V)] :
    haveI : HasBinaryProduct ((SimplexCategory.Truncated.inclusion n).op.rightKanExtension U)
        ((SimplexCategory.Truncated.inclusion n).op.rightKanExtension V) :=
      ‹HasBinaryProduct ((Truncated.cosk n).obj U) ((Truncated.cosk n).obj V)›
    prodComparison (Truncated.cosk n) U V = (rightKanExtensionProdIso n U V).hom :=
  rfl

/-- The canonical comparison morphism `cosk_n (U ⨯ V) ⟶ cosk_n U ⨯ cosk_n V` is an isomorphism,
i.e. the coskeleton functor preserves the binary product of the `n`-truncated simplicial objects
`U` and `V`. -/
theorem isIso_prodComparison_cosk (n : ℕ)
    [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
    (U V : SimplicialObject.Truncated C n)
    [HasBinaryProduct U V]
    [HasBinaryProduct ((Truncated.cosk n).obj U) ((Truncated.cosk n).obj V)] :
    IsIso (prodComparison (Truncated.cosk n) U V) := by
  have : PreservesLimitsOfSize.{0, 0} (Truncated.cosk (C := C) n) :=
    (coskAdj n).rightAdjoint_preservesLimits
  have h : (PreservesLimitPair.iso (Truncated.cosk n) U V).hom
      = prodComparison (Truncated.cosk n) U V := rfl
  rw [← h]
  infer_instance

/-- The canonical isomorphism `cosk_n (U ⨯ V) ≅ cosk_n U ⨯ cosk_n V` in `Simp(C)`, for `U`, `V`
`n`-truncated simplicial objects of `C`, coming from the preservation of the binary product of
`U` and `V` by the coskeleton functor. This assumes that the whole coskeleton functor exists;
`rightKanExtensionProdIso` (Stacks 018C) needs only the coskeleta and products in the
statement. -/
noncomputable def coskProdIso (n : ℕ)
    [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
    (U V : SimplicialObject.Truncated C n)
    [HasBinaryProduct U V]
    [HasBinaryProduct ((Truncated.cosk n).obj U) ((Truncated.cosk n).obj V)] :
    (Truncated.cosk n).obj (U ⨯ V) ≅
      (Truncated.cosk n).obj U ⨯ (Truncated.cosk n).obj V :=
  haveI : PreservesLimitsOfSize.{0, 0} (Truncated.cosk (C := C) n) :=
    (coskAdj n).rightAdjoint_preservesLimits
  PreservesLimitPair.iso (Truncated.cosk n) U V

/-- The underlying morphism of the isomorphism `coskProdIso` is the canonical comparison
morphism `prodComparison (Truncated.cosk n) U V`. -/
theorem coskProdIso_hom (n : ℕ)
    [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
    (U V : SimplicialObject.Truncated C n)
    [HasBinaryProduct U V]
    [HasBinaryProduct ((Truncated.cosk n).obj U) ((Truncated.cosk n).obj V)] :
    (coskProdIso n U V).hom = prodComparison (Truncated.cosk n) U V := by
  rfl

end CategoryTheory.SimplicialObject.Truncated

end

end
