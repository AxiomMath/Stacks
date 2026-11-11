module

public import StacksFrontier.AlgebraicTopology.EilenbergMacLane
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Abelian
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal.Existence
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Skeleton and coskeleton of a truncated simplicial object concentrated in its top degree

Let `𝒜` be an abelian category, let `k : ℕ` and let `U` be a `k`-truncated simplicial object of
`𝒜` with `U_i = 0` for `i < k`; write `A = U_k`. Since `𝒜` has finite limits and finite colimits,
both the left Kan extension `i_{k!}U` (`(Truncated.sk k).obj U`) and the right Kan extension
`cosk_k U` (`(Truncated.cosk k).obj U`) of `U` along `(Δ_{≤ k} ⊆ Δ)ᵒᵖ` exist. This file describes
both of them, and the canonical morphism `c : i_{k!}U ⟶ cosk_k U` between them.

* `i_{k!}U` is the simplicial object `surjSum A k` with `n`-th term `⨁_α A`, the sum over the
  surjections `α : ⦋n⦌ ⟶ ⦋k⦌`, whose operator attached to `φ : ⦋m⦌ ⟶ ⦋n⦌` maps the summand `α` by
  the identity to the summand `α ∘ φ` if `α ∘ φ` is surjective, and to zero otherwise.
* `cosk_k U` is the simplicial object `injSum A k` with `n`-th term `⨁_β A`, the sum over the
  injections `β : ⦋k⦌ ⟶ ⦋n⦌`, whose operator attached to `φ : ⦋m⦌ ⟶ ⦋n⦌` maps the summand `β` by
  the identity to each summand `β'` with `β = φ ∘ β'`, and to zero if `β` does not factor through
  `φ`.
* In these terms `c` has, in degree `n`, `(α, β)` coefficient `id_A` if `α ∘ β = id_{⦋k⦌}` and `0`
  otherwise, and `c` is a monomorphism.

The descriptions are proved as in the Stacks project, by checking the universal properties of the
two Kan extensions directly on `surjSum A k` and `injSum A k`, using the description of the
morphisms out of and into `U` by their top components
(`CategoryTheory.SimplicialObject.Truncated.app_top_injective_and_exists_iff`). Injectivity of `c`
is proved directly on its matrix: a surjection `α' : ⦋n⦌ ⟶ ⦋k⦌` has the section
`β(j) = min {i | j ≤ α'(i)}`, and every surjection `α` with `α ∘ β = id` satisfies `α' ≤ α`
pointwise, so the matrix is unitriangular for the order by `∑ᵢ α(i)`.

## Main definitions

* `CategoryTheory.SimplicialObject.Truncated.surjSum`,
  `CategoryTheory.SimplicialObject.Truncated.injSum`: the two simplicial objects above.
* `CategoryTheory.SimplicialObject.Truncated.skToCosk`: the canonical morphism
  `c : i_{k!}U ⟶ cosk_k U`.

## Main results

* `CategoryTheory.SimplicialObject.Truncated.app_top_injective_and_exists_iff_faces`: part (1)
  of [Stacks, Tag 0190], with the conditions `d^k_i ∘ f = 0` and `f ∘ s^{k-1}_i = 0`.
* `CategoryTheory.SimplicialObject.Truncated.exists_iso_sk_surjSum_cosk_injSum`: all parts of
  [Stacks, Tag 0190].

## References

* [Stacks, Tag 0190](https://stacks.math.columbia.edu/tag/0190)
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial
open scoped SimplexCategory.Truncated CategoryTheory.SimplicialObject.Truncated

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

open CategoryTheory.SimplicialObject.EilenbergMacLane

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

section SimplexCategory

/-- A face map `δ i : ⦋j⦌ ⟶ ⦋j + 1⦌` is not surjective. -/
private lemma not_surjective_δ {j : ℕ} (i : Fin (j + 2)) :
    ¬ Function.Surjective (SimplexCategory.δ i).toOrderHom := fun h => by
  have : Epi (SimplexCategory.δ i) := SimplexCategory.epi_iff_surjective.mpr h
  have := SimplexCategory.len_le_of_epi (SimplexCategory.δ i)
  simp at this

/-- A degeneracy map `σ i : ⦋j + 1⦌ ⟶ ⦋j⦌` is not injective. -/
private lemma not_injective_σ {j : ℕ} (i : Fin (j + 1)) :
    ¬ Function.Injective (SimplexCategory.σ i).toOrderHom := fun h => by
  have : Mono (SimplexCategory.σ i) := SimplexCategory.mono_iff_injective.mpr h
  have := SimplexCategory.len_le_of_mono (SimplexCategory.σ i)
  simp at this

/-- If `f ≫ g` is surjective, so is `g`. -/
lemma surjective_of_comp {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (h : Function.Surjective (f ≫ g).toOrderHom) : Function.Surjective g.toOrderHom :=
  Function.Surjective.of_comp (f := g.toOrderHom) (g := f.toOrderHom) h

/-- If `f ≫ g` is injective, so is `f`. -/
lemma injective_of_comp {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (h : Function.Injective (f ≫ g).toOrderHom) : Function.Injective f.toOrderHom :=
  Function.Injective.of_comp (f := g.toOrderHom) (g := f.toOrderHom) h

/-- A surjective endomorphism of an object of `Δ` is the identity. -/
private lemma eq_id_of_surjective {x : SimplexCategory} (f : x ⟶ x)
    (hf : Function.Surjective f.toOrderHom) : f = 𝟙 x :=
  have := SimplexCategory.isIso_of_bijective ⟨Finite.injective_iff_surjective.mpr hf, hf⟩
  SimplexCategory.eq_id_of_isIso f

/-- An injective endomorphism of an object of `Δ` is the identity. -/
private lemma eq_id_of_injective {x : SimplexCategory} (f : x ⟶ x)
    (hf : Function.Injective f.toOrderHom) : f = 𝟙 x :=
  have := SimplexCategory.isIso_of_bijective ⟨hf, Finite.injective_iff_surjective.mp hf⟩
  SimplexCategory.eq_id_of_isIso f

/-- The identity of `⦋k⦌`, as a surjection. -/
def topSurj (k : ℕ) : {α : ⦋k⦌ ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom} :=
  ⟨𝟙 _, fun y => ⟨y, rfl⟩⟩

/-- The identity of `⦋k⦌`, as an injection. -/
def topInj (k : ℕ) : {β : ⦋k⦌ ⟶ ⦋k⦌ // Function.Injective β.toOrderHom} :=
  ⟨𝟙 _, fun _ _ h => h⟩

private lemma eq_topSurj {k : ℕ} (α : {α : ⦋k⦌ ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom}) :
    α = topSurj k :=
  Subtype.ext (eq_id_of_surjective α.1 α.2)

private lemma eq_topInj {k : ℕ} (β : {β : ⦋k⦌ ⟶ ⦋k⦌ // Function.Injective β.toOrderHom}) :
    β = topInj k :=
  Subtype.ext (eq_id_of_injective β.1 β.2)

end SimplexCategory

section Faces

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- For `k = j + 1`, a morphism `f : X ⟶ V_k` is killed by every non-surjective operator into
`⦋k⦌` as soon as it is killed by the faces `d^k_i`, `i = 0, …, k`. -/
private lemma forall_not_surjective_iff_faces {j : ℕ} {V : SimplicialObject.Truncated C (j + 1)}
    {X : C} (f : X ⟶ V.obj (op ⟨⦋j + 1⦌, le_rfl⟩)) :
    (∀ (m : SimplexCategory.Truncated (j + 1)) (φ : m ⟶ ⟨⦋j + 1⦌, le_rfl⟩),
        ¬ Function.Surjective φ.hom.toOrderHom → f ≫ V.map φ.op = 0) ↔
      ∀ i : Fin (j + 2),
        f ≫ V.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i)).op = 0 := by
  refine ⟨fun h i => h _ _ (not_surjective_δ i), fun h m φ hφ => ?_⟩
  obtain ⟨i, θ, hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective φ.hom hφ
  have : φ = (ObjectProperty.homMk θ : m ⟶ ⟨⦋j⦌, by simp⟩) ≫
      SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i) :=
    ObjectProperty.hom_ext _ hθ
  rw [this, op_comp, V.map_comp, ← Category.assoc, h i, zero_comp]

/-- For `k = j + 1`, a morphism `f : V_k ⟶ X` is killed by every non-injective operator out of
`⦋k⦌` as soon as it is killed by the degeneracies `s^{k-1}_i`, `i = 0, …, k - 1`. -/
private lemma forall_not_injective_iff_degeneracies {j : ℕ}
    {V : SimplicialObject.Truncated C (j + 1)} {X : C} (f : V.obj (op ⟨⦋j + 1⦌, le_rfl⟩) ⟶ X) :
    (∀ (m : SimplexCategory.Truncated (j + 1)) (ψ : ⟨⦋j + 1⦌, le_rfl⟩ ⟶ m),
        ¬ Function.Injective ψ.hom.toOrderHom → V.map ψ.op ≫ f = 0) ↔
      ∀ i : Fin (j + 1),
        V.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ i)).op ≫ f = 0 := by
  refine ⟨fun h i => h _ _ (not_injective_σ i), fun h m ψ hψ => ?_⟩
  obtain ⟨i, θ, hθ⟩ := SimplexCategory.eq_σ_comp_of_not_injective ψ.hom hψ
  have : ψ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ i) ≫
      (ObjectProperty.homMk θ : ⟨⦋j⦌, by simp⟩ ⟶ m) :=
    ObjectProperty.hom_ext _ hθ
  rw [this, op_comp, V.map_comp, Category.assoc, h i, comp_zero]

/-- **Stacks 0190** (1), in terms of faces and degeneracies.
Let `k = j + 1 ≥ 1` and let `U` be a `k`-truncated simplicial object of `C` with `U_i = 0` for
`i < k`; write `A = U_k`. For every `k`-truncated simplicial object `V`:

* a morphism `U ⟶ V` is determined by its top component `A ⟶ V_k`, and
  `Mor(U, V) = {f : A → V_k | d^k_i ∘ f = 0, i = 0, …, k}`;
* a morphism `V ⟶ U` is determined by its top component `V_k ⟶ A`, and
  `Mor(V, U) = {f : V_k → A | f ∘ s^{k - 1}_i = 0, i = 0, …, k - 1}`.

For `k = 0` both conditions are empty, and the statement is the case `k = 0` of
`exists_iso_sk_surjSum_cosk_injSum` (1). -/
@[stacks 0190 "(1) for `k ≥ 1`, written `k = j + 1`, with the faces `d^k_i` and degeneracies \
  `s^{k-1}_i`; each hom-set is identified with its set of top components. For `k = 0` (where \
  both conditions are empty) see `exists_iso_sk_surjSum_cosk_injSum`."]
theorem app_top_injective_and_exists_iff_faces {j : ℕ}
    {U : SimplicialObject.Truncated C (j + 1)}
    (hU : ∀ (m : ℕ) (hm : m < j + 1), IsZero (U.obj (op ⟨⦋m⦌, hm.le⟩)))
    (V : SimplicialObject.Truncated C (j + 1)) :
    (Function.Injective (fun g : U ⟶ V => g.app (op ⟨⦋j + 1⦌, le_rfl⟩)) ∧
      ∀ f : U.obj (op ⟨⦋j + 1⦌, le_rfl⟩) ⟶ V.obj (op ⟨⦋j + 1⦌, le_rfl⟩),
        (∃ g : U ⟶ V, g.app (op ⟨⦋j + 1⦌, le_rfl⟩) = f) ↔
          ∀ i : Fin (j + 2),
            f ≫ V.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i)).op = 0) ∧
    (Function.Injective (fun g : V ⟶ U => g.app (op ⟨⦋j + 1⦌, le_rfl⟩)) ∧
      ∀ f : V.obj (op ⟨⦋j + 1⦌, le_rfl⟩) ⟶ U.obj (op ⟨⦋j + 1⦌, le_rfl⟩),
        (∃ g : V ⟶ U, g.app (op ⟨⦋j + 1⦌, le_rfl⟩) = f) ↔
          ∀ i : Fin (j + 1),
            V.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ i)).op ≫ f = 0) := by
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := app_top_injective_and_exists_iff hU V
  exact ⟨⟨h₁, fun f => (h₂ f).trans (forall_not_surjective_iff_faces f)⟩,
    h₃, fun f => (h₄ f).trans (forall_not_injective_iff_degeneracies f)⟩

end Faces

section Biproducts

/-- The `(j, k)` entry of a matrix of morphisms between biproducts. -/
lemma biproduct_ι_matrix_π {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    {J K : Type} [Finite J] [Finite K] {f : J → C} {g : K → C} (m : ∀ j k, f j ⟶ g k) (j : J)
    (k : K) : biproduct.ι f j ≫ biproduct.matrix m ≫ biproduct.π g k = m j k := by
  simp

end Biproducts

section KanExtension

/-- A left extension `(F', α)` is a left Kan extension as soon as every left extension `(G, β)`
factors uniquely through it. -/
private lemma isLeftKanExtension_of_existsUnique {C D H : Type*} [Category C] [Category D]
    [Category H] {L : C ⥤ D} {F : C ⥤ H} (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
    (h : ∀ (G : D ⥤ H) (β : F ⟶ L ⋙ G), ∃! γ : F' ⟶ G, α ≫ Functor.whiskerLeft L γ = β) :
    F'.IsLeftKanExtension α :=
  ⟨⟨IsInitial.ofUniqueHom
    (fun Y => StructuredArrow.homMk (h Y.right Y.hom).exists.choose
      (h Y.right Y.hom).exists.choose_spec)
    (fun Y m => StructuredArrow.hom_ext _ _
      ((h Y.right Y.hom).unique (StructuredArrow.w m) (h Y.right Y.hom).exists.choose_spec))⟩⟩

/-- A right extension `(F', α)` is a right Kan extension as soon as every right extension
`(G, β)` factors uniquely through it. -/
private lemma isRightKanExtension_of_existsUnique {C D H : Type*} [Category C] [Category D]
    [Category H] {L : C ⥤ D} {F : C ⥤ H} (F' : D ⥤ H) (α : L ⋙ F' ⟶ F)
    (h : ∀ (G : D ⥤ H) (β : L ⋙ G ⟶ F), ∃! γ : G ⟶ F', Functor.whiskerLeft L γ ≫ α = β) :
    F'.IsRightKanExtension α :=
  ⟨⟨IsTerminal.ofUniqueHom
    (fun Y => CostructuredArrow.homMk (h Y.left Y.hom).exists.choose
      (h Y.left Y.hom).exists.choose_spec)
    (fun Y m => CostructuredArrow.hom_ext _ _
      ((h Y.left Y.hom).unique (CostructuredArrow.w m) (h Y.left Y.hom).exists.choose_spec))⟩⟩

end KanExtension

section Abelian

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The simplicial object of [Stacks, Tag 0190] (2), (3): its `n`-th term is `⨁_α A`, the sum
over the surjections `α : ⦋n⦌ ⟶ ⦋k⦌`, and its operator attached to `φ : ⦋m⦌ ⟶ ⦋n⦌` is the
matrix whose `(α, α')` entry is `id_A` if `α' = α ∘ φ` and `0` otherwise; that is, it maps the
summand `α` by the identity to the summand `α ∘ φ` if `α ∘ φ` is surjective, and to zero
otherwise. -/
noncomputable abbrev surjSum (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 :=
  emObject A ⦋k⦌ (fun _ α => Function.Surjective α.toOrderHom)
    fun g h α _ hs => surjective_of_comp g (h ≫ α) hs

/-- The simplicial object of [Stacks, Tag 0190] (4), (5): its `n`-th term is `⨁_β A`, the sum
over the injections `β : ⦋k⦌ ⟶ ⦋n⦌`, and its operator attached to `φ : ⦋m⦌ ⟶ ⦋n⦌` is the
matrix whose `(β, β')` entry is `id_A` if `β = φ ∘ β'` and `0` otherwise; that is, it maps the
summand `β` to zero if `β` does not factor through `φ`, and by the identity to each summand `β'`
with `β = φ ∘ β'` if it does. -/
@[implicit_reducible]
noncomputable def injSum (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 where
  obj n := ⨁ fun _ : {β : ⦋k⦌ ⟶ n.unop // Function.Injective β.toOrderHom} => A
  map {a b} φ := biproduct.matrix fun β β' => if β.1 = β'.1 ≫ φ.unop then 𝟙 A else 0
  map_id X := by
    refine biproduct.hom_ext' _ _ fun β => biproduct.hom_ext _ _ fun β' => ?_
    rw [Category.assoc, biproduct_ι_matrix_π, Category.comp_id]
    by_cases h : β = β'
    · subst h
      rw [ite_eq_left (by simp), biproduct.ι_π_self]
    · rw [ite_eq_right (fun e => h (Subtype.ext (by simpa using e))), biproduct.ι_π_ne _ h]
  map_comp {X Y Z} f g := by
    rw [biproduct_matrix_comp]
    refine biproduct.hom_ext' _ _ fun β => biproduct.hom_ext _ _ fun β'' => ?_
    rw [Category.assoc, biproduct_ι_matrix_π, Category.assoc, biproduct_ι_matrix_π]
    have hs : ∀ (x : ⦋k⦌ ⟶ Y.unop) (mor : {β' : ⦋k⦌ ⟶ Y.unop //
        Function.Injective β'.toOrderHom} → (A ⟶ A)),
        (∑ β', mor β' ≫ (if β'.1 = x then 𝟙 A else 0)) =
          if h : Function.Injective x.toOrderHom then mor ⟨x, h⟩ else 0 := by
      intro x mor
      by_cases hx : Function.Injective x.toOrderHom
      · rw [dite_eq_left hx, Finset.sum_eq_single (⟨x, hx⟩ : {β' : ⦋k⦌ ⟶ Y.unop //
          Function.Injective β'.toOrderHom})]
        · simp
        · intro β' _ hβ'
          rw [ite_eq_right (fun e => hβ' (Subtype.ext e)), comp_zero]
        · simp
      · rw [dite_eq_right hx]
        refine Finset.sum_eq_zero fun β' _ => ?_
        rw [ite_eq_right (fun (e : β'.1 = x) => hx (e ▸ β'.2)), comp_zero]
    try dsimp only
    rw [hs (β''.1 ≫ g.unop) fun β' => if β.1 = β'.1 ≫ f.unop then 𝟙 A else 0]
    by_cases hx : Function.Injective (β''.1 ≫ g.unop).toOrderHom
    · simp only [dite_eq_left hx, unop_comp, Category.assoc]
    · rw [dite_eq_right hx, ite_eq_right]
      intro e
      refine hx (injective_of_comp _ f.unop ?_)
      rw [unop_comp] at e
      rw [Category.assoc, ← e]
      exact β.2

lemma injSum_map (A : 𝒜) (k : ℕ) {a b : SimplexCategoryᵒᵖ} (φ : a ⟶ b) :
    (injSum A k).map φ =
      biproduct.matrix fun (β : {β : ⦋k⦌ ⟶ a.unop // Function.Injective β.toOrderHom})
        (β' : {β : ⦋k⦌ ⟶ b.unop // Function.Injective β.toOrderHom}) =>
          if β.1 = β'.1 ≫ φ.unop then 𝟙 A else 0 :=
  rfl

lemma surjSum_map (A : 𝒜) (k : ℕ) {a b : SimplexCategoryᵒᵖ} (φ : a ⟶ b) :
    (surjSum A k).map φ =
      biproduct.matrix fun (α : {α : a.unop ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom})
        (α' : {α : b.unop ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom}) =>
          if α'.1 = φ.unop ≫ α.1 then 𝟙 A else 0 :=
  rfl

variable {k : ℕ}

/-- A morphism out of `surjSum A k` is determined by its restriction to the summand `id` of the
degree `k` term: the summand `α` of the degree `n` term is the image of that one under
`surjSum A k (α)`. -/
private lemma ι_comp_app_surjSum {A : 𝒜} {G : SimplicialObject 𝒜} (γ : surjSum A k ⟶ G)
    (n : SimplexCategory) (α : {α : n ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom}) :
    biproduct.ι (fun _ => A) α ≫ γ.app (op n) =
      (biproduct.ι (fun _ => A) (topSurj k) ≫ γ.app (op ⦋k⦌)) ≫ G.map α.1.op := by
  have h : biproduct.ι (fun _ => A) (topSurj k) ≫ (surjSum A k).map α.1.op =
      biproduct.ι (fun _ => A) α := by
    refine biproduct.hom_ext _ _ fun β => ?_
    rw [Category.assoc]
    refine (biproduct_ι_matrix_π _ _ _).trans ?_
    by_cases hβ : β = α
    · subst hβ
      rw [ite_eq_left (by simp [topSurj]), biproduct.ι_π_self]
    · rw [ite_eq_right (fun e => hβ (Subtype.ext (by simpa [topSurj] using e))),
        biproduct.ι_π_ne _ (Ne.symm hβ)]
  calc biproduct.ι (fun _ => A) α ≫ γ.app (op n)
      = (biproduct.ι (fun _ => A) (topSurj k) ≫ (surjSum A k).map α.1.op) ≫ γ.app (op n) := by
        rw [h]
    _ = _ := by rw [Category.assoc, γ.naturality, Category.assoc]

/-- A morphism into `injSum A k` is determined by its composite with the projection onto the
summand `id` of the degree `k` term. -/
private lemma app_comp_π_injSum {A : 𝒜} {G : SimplicialObject 𝒜} (γ : G ⟶ injSum A k)
    (n : SimplexCategory) (β : {β : ⦋k⦌ ⟶ n // Function.Injective β.toOrderHom}) :
    γ.app (op n) ≫ biproduct.π (fun _ => A) β =
      G.map β.1.op ≫ γ.app (op ⦋k⦌) ≫ biproduct.π (fun _ => A) (topInj k) := by
  have h : (injSum A k).map β.1.op ≫ biproduct.π (fun _ => A) (topInj k) =
      biproduct.π (fun _ => A) β := by
    refine biproduct.hom_ext' _ _ fun β'' => ?_
    refine (biproduct_ι_matrix_π _ _ _).trans ?_
    by_cases hβ : β'' = β
    · subst hβ
      rw [ite_eq_left (by simp [topInj]), biproduct.ι_π_self]
    · rw [ite_eq_right (fun e => hβ (Subtype.ext (by simpa [topInj] using e))),
        biproduct.ι_π_ne _ hβ]
  calc γ.app (op n) ≫ biproduct.π (fun _ => A) β
      = γ.app (op n) ≫ (injSum A k).map β.1.op ≫ biproduct.π (fun _ => A) (topInj k) := by
        rw [h]
    _ = _ := by rw [← Category.assoc, ← γ.naturality, Category.assoc]

/-- A morphism `f : X ⟶ G_k` killed by the non-surjective operators of `Δ_{≤ k}` into `⦋k⦌` is
killed by every non-surjective operator `ψ : ⦋n⦌ ⟶ ⦋k⦌` of `Δ`: such a `ψ` factors through a
face `δ i : ⦋k - 1⦌ ⟶ ⦋k⦌`. -/
private lemma comp_map_eq_zero_of_not_surjective {G : SimplicialObject 𝒜} {X : 𝒜}
    {f : X ⟶ G _⦋k⦌}
    (hf : ∀ (m : SimplexCategory.Truncated k) (φ : m ⟶ ⦋k⦌ₖ),
      ¬ Function.Surjective φ.hom.toOrderHom →
        f ≫ ((SimplexCategory.Truncated.inclusion k).op ⋙ G).map φ.op = 0)
    (n : SimplexCategory) (ψ : n ⟶ ⦋k⦌) (hψ : ¬ Function.Surjective ψ.toOrderHom) :
    f ≫ G.map ψ.op = 0 := by
  obtain _ | j := k
  · exact absurd (fun y => ⟨0, Subsingleton.elim (α := Fin 1) _ _⟩) hψ
  obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective ψ hψ
  have h := hf ⟨⦋j⦌, by simp⟩ (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i))
    (not_surjective_δ i)
  change f ≫ G.map (SimplexCategory.δ i).op = 0 at h
  rw [op_comp, G.map_comp, ← Category.assoc, h, zero_comp]

/-- A morphism `f : G_k ⟶ X` killed by the non-injective operators of `Δ_{≤ k}` out of `⦋k⦌` is
killed by every non-injective operator `ψ : ⦋k⦌ ⟶ ⦋n⦌` of `Δ`: such a `ψ` factors through a
degeneracy `σ i : ⦋k⦌ ⟶ ⦋k - 1⦌`. -/
private lemma map_comp_eq_zero_of_not_injective {G : SimplicialObject 𝒜} {X : 𝒜}
    {f : G _⦋k⦌ ⟶ X}
    (hf : ∀ (m : SimplexCategory.Truncated k) (ψ : ⦋k⦌ₖ ⟶ m),
      ¬ Function.Injective ψ.hom.toOrderHom →
        ((SimplexCategory.Truncated.inclusion k).op ⋙ G).map ψ.op ≫ f = 0)
    (n : SimplexCategory) (ψ : ⦋k⦌ ⟶ n) (hψ : ¬ Function.Injective ψ.toOrderHom) :
    G.map ψ.op ≫ f = 0 := by
  obtain _ | j := k
  · exact absurd (fun a b _ => Subsingleton.elim (α := Fin 1) a b) hψ
  obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective ψ hψ
  have h := hf ⟨⦋j⦌, by simp⟩ (SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ i))
    (not_injective_σ i)
  change G.map (SimplexCategory.σ i).op ≫ f = 0 at h
  rw [op_comp, G.map_comp, Category.assoc, h, comp_zero]

/-- The morphism `surjSum A k ⟶ G` given on the summand `α` of the degree `n` term by
`G(α) ∘ f`. -/
private noncomputable def surjDesc {A : 𝒜} {G : SimplicialObject 𝒜} (f : A ⟶ G _⦋k⦌)
    (hf : ∀ (n : SimplexCategory) (ψ : n ⟶ ⦋k⦌), ¬ Function.Surjective ψ.toOrderHom →
      f ≫ G.map ψ.op = 0) :
    surjSum A k ⟶ G where
  app n := biproduct.desc fun α => f ≫ G.map α.1.op
  naturality a b φ := by
    refine biproduct.hom_ext' _ _ fun α => ?_
    rw [surjSum_map]
    simp only [biproduct.ι_matrix_assoc, biproduct.lift_desc, biproduct.ι_desc_assoc]
    rw [subtype_indicator_sum (fun β : b.unop ⟶ ⦋k⦌ => Function.Surjective β.toOrderHom) A
      (G.obj b) (φ.unop ≫ α.1) fun β => f ≫ G.map β.1.op]
    by_cases hs : Function.Surjective (φ.unop ≫ α.1).toOrderHom
    · simp only [dite_eq_left hs, op_comp, Quiver.Hom.op_unop, Functor.map_comp, Category.assoc]
    · have e : α.1.op ≫ φ = (φ.unop ≫ α.1).op := by simp
      rw [dite_eq_right hs, Category.assoc, ← G.map_comp, e, hf _ _ hs]

/-- The morphism `G ⟶ injSum A k` given on the summand `β` of the degree `n` term by
`f ∘ G(β)`. -/
private noncomputable def injLift {A : 𝒜} {G : SimplicialObject 𝒜} (f : G _⦋k⦌ ⟶ A)
    (hf : ∀ (n : SimplexCategory) (ψ : ⦋k⦌ ⟶ n), ¬ Function.Injective ψ.toOrderHom →
      G.map ψ.op ≫ f = 0) :
    G ⟶ injSum A k where
  app n := biproduct.lift fun β => G.map β.1.op ≫ f
  naturality a b φ := by
    refine biproduct.hom_ext _ _ fun β' => ?_
    simp only [Category.assoc, biproduct.lift_π, injSum_map, biproduct.matrix_π,
      biproduct.lift_desc]
    have hs : ∀ (x : ⦋k⦌ ⟶ a.unop) (mor : {β : ⦋k⦌ ⟶ a.unop //
        Function.Injective β.toOrderHom} → (G.obj a ⟶ G _⦋k⦌)),
        (∑ β, mor β ≫ f ≫ (if β.1 = x then 𝟙 A else 0)) =
          if h : Function.Injective x.toOrderHom then mor ⟨x, h⟩ ≫ f else 0 := by
      intro x mor
      by_cases hx : Function.Injective x.toOrderHom
      · rw [dite_eq_left hx, Finset.sum_eq_single (⟨x, hx⟩ : {β : ⦋k⦌ ⟶ a.unop //
          Function.Injective β.toOrderHom})]
        · simp
        · intro β _ hβ
          rw [ite_eq_right (fun e => hβ (Subtype.ext e)), comp_zero, comp_zero]
        · simp
      · rw [dite_eq_right hx]
        refine Finset.sum_eq_zero fun β _ => ?_
        rw [ite_eq_right (fun (e : β.1 = x) => hx (e ▸ β.2)), comp_zero, comp_zero]
    rw [hs (β'.1 ≫ φ.unop) fun β => G.map β.1.op]
    have e : φ ≫ β'.1.op = (β'.1 ≫ φ.unop).op := by simp
    by_cases hi : Function.Injective (β'.1 ≫ φ.unop).toOrderHom
    · simp only [dite_eq_left hi, op_comp, Quiver.Hom.op_unop, Functor.map_comp, Category.assoc]
    · rw [dite_eq_right hi, ← Category.assoc, ← G.map_comp, e, hf _ _ hi]

variable {U : SimplicialObject.Truncated 𝒜 k}
  (hU : ∀ (m : ℕ) (hm : m < k), IsZero (U _⦋m,hm.le⦌ₖ))

/-- The top component `id` of the unit `U ⟶ sk_k (surjSum A k)` is killed by the non-surjective
operators into `⦋k⦌`. -/
private lemma ι_topSurj_comp_map_eq_zero (m : SimplexCategory.Truncated k) (φ : m ⟶ ⦋k⦌ₖ)
    (hφ : ¬ Function.Surjective φ.hom.toOrderHom) :
    biproduct.ι (fun _ => U _⦋k⦌ₖ) (topSurj k) ≫
      ((SimplexCategory.Truncated.inclusion k).op ⋙ surjSum (U _⦋k⦌ₖ) k).map φ.op = 0 := by
  refine biproduct.hom_ext _ _ fun α => ?_
  rw [Category.assoc, zero_comp]
  refine (biproduct_ι_matrix_π _ _ _).trans (ite_eq_right fun h => hφ ?_)
  have := α.2
  rw [h] at this
  simp only [topSurj] at this
  exact this

/-- The top component `id` of the counit `sk_k (injSum A k) ⟶ U` is killed by the non-injective
operators out of `⦋k⦌`. -/
private lemma map_comp_π_topInj_eq_zero (m : SimplexCategory.Truncated k) (ψ : ⦋k⦌ₖ ⟶ m)
    (hψ : ¬ Function.Injective ψ.hom.toOrderHom) :
    ((SimplexCategory.Truncated.inclusion k).op ⋙ injSum (U _⦋k⦌ₖ) k).map ψ.op ≫
      biproduct.π (fun _ => U _⦋k⦌ₖ) (topInj k) = 0 := by
  refine biproduct.hom_ext' _ _ fun β => ?_
  rw [comp_zero]
  refine (biproduct_ι_matrix_π _ _ _).trans (ite_eq_right fun h => hψ ?_)
  have := β.2
  rw [h] at this
  simp only [topInj, Category.id_comp] at this
  exact this

include hU

/-- The unit `U ⟶ sk_k (surjSum A k)`: the identity of `A` in degree `k`. -/
private noncomputable def surjUnit :
    U ⟶ (SimplexCategory.Truncated.inclusion k).op ⋙ surjSum (U _⦋k⦌ₖ) k :=
  Classical.choose (((app_top_injective_and_exists_iff hU
    ((SimplexCategory.Truncated.inclusion k).op ⋙ surjSum (U _⦋k⦌ₖ) k)).1.2
    (biproduct.ι (fun _ => U _⦋k⦌ₖ) (topSurj k))).2 (ι_topSurj_comp_map_eq_zero (U := U)))

private lemma surjUnit_app_top :
    (surjUnit hU).app (op ⦋k⦌ₖ) = biproduct.ι (fun _ => U _⦋k⦌ₖ) (topSurj k) :=
  Classical.choose_spec (((app_top_injective_and_exists_iff hU
    ((SimplexCategory.Truncated.inclusion k).op ⋙ surjSum (U _⦋k⦌ₖ) k)).1.2
    (biproduct.ι (fun _ => U _⦋k⦌ₖ) (topSurj k))).2 (ι_topSurj_comp_map_eq_zero (U := U)))

/-- The counit `sk_k (injSum A k) ⟶ U`: the identity of `A` in degree `k`. -/
private noncomputable def injCounit :
    (SimplexCategory.Truncated.inclusion k).op ⋙ injSum (U _⦋k⦌ₖ) k ⟶ U :=
  Classical.choose (((app_top_injective_and_exists_iff hU
    ((SimplexCategory.Truncated.inclusion k).op ⋙ injSum (U _⦋k⦌ₖ) k)).2.2
    (biproduct.π (fun _ => U _⦋k⦌ₖ) (topInj k))).2 (map_comp_π_topInj_eq_zero (U := U)))

private lemma injCounit_app_top :
    (injCounit hU).app (op ⦋k⦌ₖ) = biproduct.π (fun _ => U _⦋k⦌ₖ) (topInj k) :=
  Classical.choose_spec (((app_top_injective_and_exists_iff hU
    ((SimplexCategory.Truncated.inclusion k).op ⋙ injSum (U _⦋k⦌ₖ) k)).2.2
    (biproduct.π (fun _ => U _⦋k⦌ₖ) (topInj k))).2 (map_comp_π_topInj_eq_zero (U := U)))

/-- `surjSum A k` is the left Kan extension `i_{k!}U` of `U`. -/
private lemma isLeftKanExtension_surjSum :
    (surjSum (U _⦋k⦌ₖ) k).IsLeftKanExtension (surjUnit hU) := by
  refine isLeftKanExtension_of_existsUnique _ _ fun G β => ?_
  have hf := ((app_top_injective_and_exists_iff hU
    ((SimplexCategory.Truncated.inclusion k).op ⋙ G)).1.2 (β.app (op ⦋k⦌ₖ))).1 ⟨β, rfl⟩
  have hf' := comp_map_eq_zero_of_not_surjective hf
  refine ⟨surjDesc _ hf', ?_, fun γ hγ => ?_⟩
  · refine (app_top_injective_and_exists_iff hU
      ((SimplexCategory.Truncated.inclusion k).op ⋙ G)).1.1 ?_
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, surjUnit_app_top]
    exact (biproduct.ι_desc (f := fun _ : {α : ⦋k⦌ ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom} =>
      U _⦋k⦌ₖ) _ _).trans (by simp [topSurj])
  · have htop : biproduct.ι (fun _ => U _⦋k⦌ₖ) (topSurj k) ≫ γ.app (op ⦋k⦌) =
        β.app (op ⦋k⦌ₖ) := by
      simpa [surjUnit_app_top] using NatTrans.congr_app hγ (op ⦋k⦌ₖ)
    refine NatTrans.ext (funext fun n => ?_)
    obtain ⟨n⟩ := n
    refine biproduct.hom_ext' _ _ fun α => ?_
    rw [ι_comp_app_surjSum γ n α, htop]
    exact (biproduct.ι_desc (fun α' : {α : n ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom} =>
      β.app (op ⦋k⦌ₖ) ≫ G.map α'.1.op) α).symm

/-- `injSum A k` is the right Kan extension `cosk_k U` of `U`. -/
private lemma isRightKanExtension_injSum :
    (injSum (U _⦋k⦌ₖ) k).IsRightKanExtension (injCounit hU) := by
  refine isRightKanExtension_of_existsUnique _ _ fun G β => ?_
  have hf := ((app_top_injective_and_exists_iff hU
    ((SimplexCategory.Truncated.inclusion k).op ⋙ G)).2.2 (β.app (op ⦋k⦌ₖ))).1 ⟨β, rfl⟩
  have hf' := map_comp_eq_zero_of_not_injective hf
  refine ⟨injLift _ hf', ?_, fun γ hγ => ?_⟩
  · refine (app_top_injective_and_exists_iff hU
      ((SimplexCategory.Truncated.inclusion k).op ⋙ G)).2.1 ?_
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, injCounit_app_top]
    exact (biproduct.lift_π (f := fun _ : {β : ⦋k⦌ ⟶ ⦋k⦌ // Function.Injective β.toOrderHom} =>
      U _⦋k⦌ₖ) _ _).trans (by simp [topInj])
  · have htop : γ.app (op ⦋k⦌) ≫ biproduct.π (fun _ => U _⦋k⦌ₖ) (topInj k) =
        β.app (op ⦋k⦌ₖ) := by
      simpa [injCounit_app_top] using NatTrans.congr_app hγ (op ⦋k⦌ₖ)
    refine NatTrans.ext (funext fun n => ?_)
    obtain ⟨n⟩ := n
    refine biproduct.hom_ext _ _ fun β' => ?_
    rw [app_comp_π_injSum γ n β', htop]
    exact (biproduct.lift_π (fun β'' : {β : ⦋k⦌ ⟶ n // Function.Injective β.toOrderHom} =>
      G.map β''.1.op ≫ β.app (op ⦋k⦌ₖ)) β').symm

omit hU

end Abelian

section Matrix

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The section `j ↦ min {i | j ≤ α(i)}` of a surjection `α : n ⟶ ⦋k⦌`. -/
private noncomputable def sec {n : SimplexCategory} {k : ℕ} (α : n ⟶ ⦋k⦌)
    (hα : Function.Surjective α.toOrderHom) : ⦋k⦌ ⟶ n :=
  SimplexCategory.Hom.mk
    { toFun := fun j => (Finset.univ.filter fun i => j ≤ α.toOrderHom i).min'
        (by obtain ⟨i, hi⟩ := hα j; exact ⟨i, by simp [hi]⟩)
      monotone' := fun j j' hjj' => Finset.min'_subset _ fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hjj'.trans hi }

private lemma sec_spec {n : SimplexCategory} {k : ℕ} (α : n ⟶ ⦋k⦌)
    (hα : Function.Surjective α.toOrderHom) (j : Fin (k + 1)) :
    α.toOrderHom ((sec α hα).toOrderHom j) = j := by
  obtain ⟨i, hi⟩ := hα j
  have hmem := Finset.min'_mem (Finset.univ.filter fun i => j ≤ α.toOrderHom i)
    ⟨i, by simp [hi]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact le_antisymm
    ((α.toOrderHom.monotone (Finset.min'_le _ i (by simp [hi]))).trans_eq hi) hmem

private lemma sec_comp {n : SimplexCategory} {k : ℕ} (α : n ⟶ ⦋k⦌)
    (hα : Function.Surjective α.toOrderHom) : sec α hα ≫ α = 𝟙 _ :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun j => by
    simpa using sec_spec α hα j))

private lemma sec_injective {n : SimplexCategory} {k : ℕ} (α : n ⟶ ⦋k⦌)
    (hα : Function.Surjective α.toOrderHom) : Function.Injective (sec α hα).toOrderHom :=
  fun a b h => by rw [← sec_spec α hα a, ← sec_spec α hα b, h]

/-- If `α ∘ sec α' = id`, then `α' ≤ α` pointwise. -/
private lemma le_of_sec_comp {n : SimplexCategory} {k : ℕ} (α α' : n ⟶ ⦋k⦌)
    (hα' : Function.Surjective α'.toOrderHom) (h : sec α' hα' ≫ α = 𝟙 _) (i : Fin (n.len + 1)) :
    α'.toOrderHom i ≤ α.toOrderHom i := by
  have hj : α.toOrderHom ((sec α' hα').toOrderHom (α'.toOrderHom i)) = α'.toOrderHom i := by
    have := congrArg (fun f : ⦋k⦌ ⟶ ⦋k⦌ => f.toOrderHom (α'.toOrderHom i)) h
    simpa using this
  rw [← hj]
  exact α.toOrderHom.monotone (Finset.min'_le _ _ (by simp))

/-- The matrix `⨁_α A ⟶ ⨁_β A`, over the surjections `α : n ⟶ ⦋k⦌` and the injections
`β : ⦋k⦌ ⟶ n`, with `(α, β)` entry `id_A` if `α ∘ β = id` and `0` otherwise, is a
monomorphism. -/
private lemma mono_matrix (A : 𝒜) (n : SimplexCategory) (k : ℕ) :
    Mono (biproduct.matrix fun (α : {α : n ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom})
      (β : {β : ⦋k⦌ ⟶ n // Function.Injective β.toOrderHom}) =>
        if β.1 ≫ α.1 = 𝟙 _ then 𝟙 A else 0) := by
  refine Preadditive.mono_of_cancel_zero _ fun {P} g hg => ?_
  have hcomp : ∀ β : {β : ⦋k⦌ ⟶ n // Function.Injective β.toOrderHom},
      ∑ α : {α : n ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom},
        (g ≫ biproduct.π (fun _ => A) α) ≫ (if β.1 ≫ α.1 = 𝟙 _ then 𝟙 A else 0) = 0 := by
    intro β
    have h1 := congrArg (· ≫ biproduct.π (fun _ => A) β) hg
    simp only [Category.assoc, biproduct.matrix_π, zero_comp] at h1
    rw [← h1, biproduct.desc_eq, Preadditive.comp_sum]
    simp only [Category.assoc]
  let weight : (n ⟶ ⦋k⦌) → ℕ := fun α => ∑ i, ((α.toOrderHom i : Fin (k + 1)) : ℕ)
  let N : ℕ := ∑ _i : Fin (n.len + 1), k
  have hN : ∀ α, weight α ≤ N := fun α =>
    Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (α.toOrderHom i).isLt
  have key : ∀ α' : {α : n ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom},
      g ≫ biproduct.π (fun _ => A) α' = 0 := by
    intro α'
    refine WellFounded.induction
      (C := fun α'' => g ≫ biproduct.π (fun _ => A) α'' = 0)
      (measure fun α'' : {α : n ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom} =>
        N - weight α''.1).wf α' fun α' ih => ?_
    have h := hcomp ⟨sec α'.1 α'.2, sec_injective α'.1 α'.2⟩
    rw [Finset.sum_eq_single α'] at h
    · rwa [ite_eq_left (sec_comp α'.1 α'.2), Category.comp_id] at h
    · intro α _ hne
      by_cases hα : sec α'.1 α'.2 ≫ α.1 = 𝟙 _
      · have hle := le_of_sec_comp α.1 α'.1 α'.2 hα
        have hex : ∃ i ∈ Finset.univ, ((α'.1.toOrderHom i : Fin (k + 1)) : ℕ) <
            ((α.1.toOrderHom i : Fin (k + 1)) : ℕ) := by
          by_contra hcon
          push Not at hcon
          exact hne (Subtype.ext (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i =>
            le_antisymm (Fin.le_iff_val_le_val.mpr (hcon i (Finset.mem_univ _))) (hle i)))))
        have hlt : weight α'.1 < weight α.1 :=
          Finset.sum_lt_sum (fun i _ => Fin.le_iff_val_le_val.mp (hle i)) hex
        have := hN α.1
        rw [ih α (show N - weight α.1 < N - weight α'.1 by omega), zero_comp]
      · rw [ite_eq_right hα, comp_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact biproduct.hom_ext _ _ fun α => by rw [key α, zero_comp]

end Matrix

section Comparison

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {k : ℕ}

attribute [local instance] hasPointwiseRightKanExtension_of_hasFiniteLimits

/-- The unit `U ⟶ sk_k i_{k!}U` of the left Kan extension `i_{k!}U`. -/
noncomputable abbrev skUnit (U : SimplicialObject.Truncated 𝒜 k) :
    U ⟶ (SimplexCategory.Truncated.inclusion k).op ⋙ (Truncated.sk k).obj U :=
  (SimplexCategory.Truncated.inclusion k).op.lanUnit.app U

/-- The counit `sk_k cosk_k U ⟶ U` of the right Kan extension `cosk_k U`. -/
noncomputable abbrev coskCounit (U : SimplicialObject.Truncated 𝒜 k) :
    (SimplexCategory.Truncated.inclusion k).op ⋙ (Truncated.cosk k).obj U ⟶ U :=
  (SimplexCategory.Truncated.inclusion k).op.ranCounit.app U

instance (U : SimplicialObject.Truncated 𝒜 k) :
    ((Truncated.sk k).obj U).IsLeftKanExtension (skUnit U) :=
  (inferInstance : ((SimplexCategory.Truncated.inclusion k).op.lan.obj U).IsLeftKanExtension
    ((SimplexCategory.Truncated.inclusion k).op.lanUnit.app U))

instance (U : SimplicialObject.Truncated 𝒜 k) :
    ((Truncated.cosk k).obj U).IsRightKanExtension (coskCounit U) :=
  (inferInstance : ((SimplexCategory.Truncated.inclusion k).op.ran.obj U).IsRightKanExtension
    ((SimplexCategory.Truncated.inclusion k).op.ranCounit.app U))

instance (U : SimplicialObject.Truncated 𝒜 k) : IsIso (coskCounit U) :=
  (inferInstance : IsIso ((SimplexCategory.Truncated.inclusion k).op.ranCounit.app U))

/-- The canonical morphism `c : i_{k!}U ⟶ cosk_k U` of [Stacks, Tag 0190] (6), (7): the unique
morphism whose restriction to `Δ_{≤ k}`, composed with the unit `U ⟶ sk_k i_{k!}U` and with the
counit `sk_k cosk_k U ⟶ U` (an isomorphism), is the identity of `U`. Equivalently it corresponds,
under the adjunction `i_{k!} ⊣ sk_k`, to the inverse of the isomorphism `sk_k cosk_k U ⟶ U`. -/
noncomputable def skToCosk (U : SimplicialObject.Truncated 𝒜 k) :
    (Truncated.sk k).obj U ⟶ (Truncated.cosk k).obj U :=
  ((Truncated.sk k).obj U).descOfIsLeftKanExtension (skUnit U) ((Truncated.cosk k).obj U)
    (inv (coskCounit U))

@[reassoc]
lemma skUnit_comp_whiskerLeft_skToCosk (U : SimplicialObject.Truncated 𝒜 k) :
    skUnit U ≫ Functor.whiskerLeft (SimplexCategory.Truncated.inclusion k).op (skToCosk U) =
      inv (coskCounit U) :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

/-- A morphism `surjSum A k ⟶ injSum A k` which is the identity on the summands `id` of the degree
`k` terms has, in degree `n`, `(α, β)` entry `id_A` if `α ∘ β = id` and `0` otherwise. -/
private lemma app_eq_matrix {A : 𝒜} (c : surjSum A k ⟶ injSum A k)
    (htop : biproduct.ι (fun _ => A) (topSurj k) ≫ c.app (op ⦋k⦌) ≫
      biproduct.π (fun _ => A) (topInj k) = 𝟙 A) (n : SimplexCategory) :
    c.app (op n) =
      biproduct.matrix fun (α : {α : n ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom})
        (β : {β : ⦋k⦌ ⟶ n // Function.Injective β.toOrderHom}) =>
          if β.1 ≫ α.1 = 𝟙 _ then 𝟙 A else 0 := by
  have h' : c.app (op ⦋k⦌) ≫ biproduct.π (fun _ => A) (topInj k) =
      biproduct.π (fun _ => A) (topSurj k) := by
    refine biproduct.hom_ext' _ _ fun α₀ => ?_
    rw [eq_topSurj α₀, biproduct.ι_π_self, htop]
  refine biproduct.hom_ext' _ _ fun α => biproduct.hom_ext _ _ fun β => ?_
  simp only [Category.assoc]
  rw [biproduct_ι_matrix_π, app_comp_π_injSum c n β, h']
  refine (biproduct_ι_matrix_π _ _ _).trans ?_
  simp only [topSurj, Quiver.Hom.unop_op]
  exact if_congr eq_comm rfl rfl

/-- **Stacks 0190**.
Let `𝒜` be an abelian category, let `k : ℕ` and let `U` be a `k`-truncated simplicial object of
`𝒜` with `U_i = 0` for `i < k`; write `A = U_k`. (All operators `U(φ)` other than
`U(id_{⦋k⦌}) = id_A` then vanish, so this is the object `U` of the Stacks project.)

1. For every `k`-truncated simplicial object `V`, a morphism `U ⟶ V` (resp. `V ⟶ U`) is
   determined by its top component, and the top components are exactly the `f : A ⟶ V_k` with
   `f ≫ V(φ) = 0` for every non-surjective `φ : ⦋m⦌ ⟶ ⦋k⦌` (resp. the `f : V_k ⟶ A` with
   `V(ψ) ≫ f = 0` for every non-injective `ψ : ⦋k⦌ ⟶ ⦋m⦌`); these are the conditions
   `d^k_i ∘ f = 0`, `i = 0, …, k` (resp. `f ∘ s^{k-1}_i = 0`, `i = 0, …, k - 1`), see
   `app_top_injective_and_exists_iff_faces`.
2. and 3. `i_{k!}U` is isomorphic to `surjSum A k`: its `n`-th term is `⨁_α A` over the
   surjections `α : ⦋n⦌ ⟶ ⦋k⦌`, and `i_{k!}U(φ)` maps the summand `α` by the identity to the
   summand `α ∘ φ` if `α ∘ φ` is surjective, and to zero otherwise.
4. and 5. `cosk_k U` is isomorphic to `injSum A k`: its `n`-th term is `⨁_β A` over the
   injections `β : ⦋k⦌ ⟶ ⦋n⦌`, and `cosk_k U(φ)` maps the summand `β` to zero if `β` does not
   factor through `φ`, and by the identity to each summand `β'` with `β = φ ∘ β'` if it does.
6. Under these isomorphisms the canonical map `c : i_{k!}U ⟶ cosk_k U` (`skToCosk U`) has, in
   degree `n`, `(α, β)` coefficient `id_A` if `α ∘ β = id_{⦋k⦌}` and `0` otherwise.
7. `c` is injective, i.e. a monomorphism. -/
@[stacks 0190 "(1)–(7). (1) is the first conjunct, with the conditions stated over all \
  non-surjective (resp. non-injective) operators, which also covers `k = 0`; the face and \
  degeneracy form for `k ≥ 1` is `app_top_injective_and_exists_iff_faces`. (2)–(5) are the \
  isomorphisms `e₁`, `e₂` onto `surjSum` and `injSum`, whose terms and operators are by \
  definition the sums and matrices of the statement. (6) is the matrix of `e₁⁻¹ ≫ c ≫ e₂` in each \
  degree, `c = skToCosk U` being the unique morphism restricting to the identity of `U`. (7) is \
  `Mono c`."]
theorem exists_iso_sk_surjSum_cosk_injSum {U : SimplicialObject.Truncated 𝒜 k}
    (hU : ∀ (m : ℕ) (hm : m < k), IsZero (U _⦋m,hm.le⦌ₖ)) :
    (∀ V : SimplicialObject.Truncated 𝒜 k,
      (Function.Injective (fun g : U ⟶ V => g.app (op ⦋k⦌ₖ)) ∧
        ∀ f : U _⦋k⦌ₖ ⟶ V _⦋k⦌ₖ, (∃ g : U ⟶ V, g.app (op ⦋k⦌ₖ) = f) ↔
          ∀ (m : SimplexCategory.Truncated k) (φ : m ⟶ ⦋k⦌ₖ),
            ¬ Function.Surjective φ.hom.toOrderHom → f ≫ V.map φ.op = 0) ∧
      (Function.Injective (fun g : V ⟶ U => g.app (op ⦋k⦌ₖ)) ∧
        ∀ f : V _⦋k⦌ₖ ⟶ U _⦋k⦌ₖ, (∃ g : V ⟶ U, g.app (op ⦋k⦌ₖ) = f) ↔
          ∀ (m : SimplexCategory.Truncated k) (ψ : ⦋k⦌ₖ ⟶ m),
            ¬ Function.Injective ψ.hom.toOrderHom → V.map ψ.op ≫ f = 0)) ∧
    ∃ (e₁ : (Truncated.sk k).obj U ≅ surjSum (U _⦋k⦌ₖ) k)
      (e₂ : (Truncated.cosk k).obj U ≅ injSum (U _⦋k⦌ₖ) k),
      (∀ n : SimplexCategory, (e₁.inv ≫ skToCosk U ≫ e₂.hom).app (op n) =
        biproduct.matrix fun (α : {α : n ⟶ ⦋k⦌ // Function.Surjective α.toOrderHom})
          (β : {β : ⦋k⦌ ⟶ n // Function.Injective β.toOrderHom}) =>
            if β.1 ≫ α.1 = 𝟙 _ then 𝟙 (U _⦋k⦌ₖ) else 0) ∧
      Mono (skToCosk U) := by
  refine ⟨app_top_injective_and_exists_iff hU, ?_⟩
  have := isLeftKanExtension_surjSum hU
  have := isRightKanExtension_injSum hU
  let e₁ : (Truncated.sk k).obj U ≅ surjSum (U _⦋k⦌ₖ) k :=
    Functor.leftKanExtensionUnique ((Truncated.sk k).obj U) (skUnit U) _ (surjUnit hU)
  let e₂ : (Truncated.cosk k).obj U ≅ injSum (U _⦋k⦌ₖ) k :=
    Functor.rightKanExtensionUnique ((Truncated.cosk k).obj U) (coskCounit U) _ (injCounit hU)
  have h₁ : surjUnit hU ≫ Functor.whiskerLeft (SimplexCategory.Truncated.inclusion k).op e₁.inv =
      skUnit U := by
    simp [e₁]
  have h₂ : Functor.whiskerLeft (SimplexCategory.Truncated.inclusion k).op e₂.hom ≫
      injCounit hU = coskCounit U := by
    simp [e₂]
  obtain ⟨c, hc⟩ : ∃ c, e₁.inv ≫ skToCosk U ≫ e₂.hom = c := ⟨_, rfl⟩
  have key : surjUnit hU ≫ Functor.whiskerLeft (SimplexCategory.Truncated.inclusion k).op c ≫
      injCounit hU = 𝟙 U := by
    rw [← hc]
    simp only [Functor.whiskerLeft_comp, Category.assoc]
    rw [reassoc_of% h₁, skUnit_comp_whiskerLeft_skToCosk_assoc, h₂, IsIso.inv_hom_id]
  have htop : biproduct.ι (fun _ => U _⦋k⦌ₖ) (topSurj k) ≫ c.app (op ⦋k⦌) ≫
      biproduct.π (fun _ => U _⦋k⦌ₖ) (topInj k) = 𝟙 _ := by
    have := NatTrans.congr_app key (op ⦋k⦌ₖ)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app, surjUnit_app_top,
      injCounit_app_top] at this
    exact this
  have hmat := app_eq_matrix c htop
  refine ⟨e₁, e₂, fun n => hc ▸ hmat n, ?_⟩
  have : ∀ X, Mono (c.app X) := fun X => by
    obtain ⟨n⟩ := X
    rw [hmat n]
    exact mono_matrix _ n k
  have : Mono c := NatTrans.mono_of_mono_app _
  have hc' : skToCosk U = e₁.hom ≫ c ≫ e₂.inv := by
    rw [← hc]
    simp
  rw [hc']
  infer_instance

end Comparison

end CategoryTheory.SimplicialObject.Truncated
