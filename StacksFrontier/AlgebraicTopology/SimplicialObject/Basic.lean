module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.IsoCat
public import StacksFrontier.AlgebraicTopology.SimplexCategory.GeneratorsRelations.ToSimplexCategory

/-!
# Simplicial and cosimplicial objects as faces and degeneracies

Simplicial and cosimplicial objects, and their morphisms, described by face and degeneracy data
subject to the simplicial identities; simplicial objects as presheaves; the split monomorphisms
among the structure maps; and the standard cosimplicial sets.
-/

/-!
## Simplicial objects are faces and degeneracies subject to the simplicial identities

Let `C` be a category. A simplicial object of `C` is a functor `Δᵒᵖ ⥤ C`, so it consists of
objects `U_n = U([n])` together with faces `d^n_j = U(δ^n_j) : U_n ⟶ U_{n - 1}` and
degeneracies `s^n_j = U(σ^n_j) : U_n ⟶ U_{n + 1}`, and these satisfy the opposites of the
simplicial identities [Stacks, Tag 0167]. Conversely such a system of objects and morphisms
comes from a unique simplicial object, and a morphism of simplicial objects is a family
`U_n ⟶ U'_n` commuting with the faces and the degeneracies.

Both converses say that `Δ` is *presented* by the `δ^n_j` and the `σ^n_j` subject to those
relations ([Stacks, Tag 0166] and [Stacks, Tag 0168]). That presented category is
`SimplexCategoryGenRel`, the path category on generators `δ i`, `σ i` modulo exactly the
relations of [Stacks, Tag 0167], and it comes with the canonical comparison functor
`SimplexCategoryGenRel.toSimplexCategory`. A functor `SimplexCategoryGenRelᵒᵖ ⥤ C` is
therefore the same thing as a system `(U_n, d^n_j, s^n_j)` satisfying the relations (1)(a) –
(e), and a natural transformation between two such is the same thing as a family of morphisms
commuting with the `d^n_j` and the `s^n_j`. In this language the content of the lemma is that
restriction along `toSimplexCategory.op` is bijective on functors and on natural
transformations, i.e. an isomorphism of categories `SimplicialObject C ≅
(SimplexCategoryGenRelᵒᵖ ⥤ C)`.

### Main results

* `CategoryTheory.SimplicialObject.bijective_comp_toSimplexCategory_op_and_whiskerLeft`: a
  simplicial object of `C` is the same datum as a functor `SimplexCategoryGenRelᵒᵖ ⥤ C`, and a
  morphism of simplicial objects is the same datum as a natural transformation between the
  associated functors — both bijectively, and on the nose.

### References

* [Stacks, Tag 016B](https://stacks.math.columbia.edu/tag/016B)
* [Stacks, Tag 0167](https://stacks.math.columbia.edu/tag/0167)
* [Stacks, Tag 0168](https://stacks.math.columbia.edu/tag/0168)
-/

section

open CategoryTheory Opposite Simplicial SimplexCategoryGenRel

universe v u

namespace CategoryTheory.SimplicialObject

/-- **Stacks 016B** (parts (2) and (3), via the presented category `SimplexCategoryGenRel`).
Restriction along the canonical functor `SimplexCategoryGenRel.toSimplexCategory` from the
category presented by the generators `δ^n_j`, `σ^n_j` and the relations of [Stacks, Tag 0167]
is bijective on simplicial objects of `C` and on morphisms of simplicial objects: every system
`(U_n, d^n_j, s^n_j)` satisfying those relations — that is, every functor
`SimplexCategoryGenRelᵒᵖ ⥤ C` — comes from a unique simplicial object `U` with `U_n = U([n])`,
`d^n_j = U(δ^n_j)` and `s^n_j = U(σ^n_j)`, and every family of morphisms `U_n ⟶ U'_n`
commuting with the faces and the degeneracies comes from a unique morphism of simplicial
objects. -/
@[stacks 016B "part (1) is `CategoryTheory.SimplicialObject.δ_comp_δ` and its \
  companions in Mathlib; parts (2) and (3) are stated in terms of the presented \
  category `SimplexCategoryGenRel`, so that no equality of objects of `C` is \
  transported"]
public theorem bijective_comp_toSimplexCategory_op_and_whiskerLeft (C : Type u)
    [Category.{v} C] :
    Function.Bijective (fun X : SimplicialObject C => toSimplexCategory.op ⋙ X) ∧
      ∀ X Y : SimplicialObject C,
        Function.Bijective (fun f : X ⟶ Y => Functor.whiskerLeft toSimplexCategory.op f) := by
  have hfaithful : toSimplexCategory.Faithful := toSimplexCategory_faithful
  have hfull : toSimplexCategory.Full := toSimplexCategory_full
  have hiso : toSimplexCategory.op.IsIso :=
    { bijective_obj := toSimplexCategory_op_bijective_obj }
  obtain ⟨G, hunit, hcounit⟩ :
      ∃ G : SimplexCategoryᵒᵖ ⥤ SimplexCategoryGenRelᵒᵖ,
        𝟭 _ = toSimplexCategory.op ⋙ G ∧ G ⋙ toSimplexCategory.op = 𝟭 _ :=
    ⟨(Functor.asIsomorphism toSimplexCategory.op).inverse,
      (Functor.asIsomorphism toSimplexCategory.op).unit_eq,
      (Functor.asIsomorphism toSimplexCategory.op).counit_eq⟩
  have hcomp : ∀ F : SimplexCategoryGenRelᵒᵖ ⥤ C, toSimplexCategory.op ⋙ G ⋙ F = F := by
    intro F
    rw [← Functor.assoc, ← hunit, Functor.id_comp]
  have hcomp' : ∀ X : SimplicialObject C, G ⋙ toSimplexCategory.op ⋙ X = X := by
    intro X
    rw [← Functor.assoc, hcounit, Functor.id_comp]
  refine ⟨⟨fun X Y hXY => ?_, fun F => ⟨G ⋙ F, hcomp F⟩⟩,
    fun X Y => ⟨fun f g hfg => ?_, fun τ => ?_⟩⟩
  · have h : toSimplexCategory.op ⋙ X = toSimplexCategory.op ⋙ Y := hXY
    rw [← hcomp' X, ← hcomp' Y, h]
  · exact ((Functor.whiskeringLeft _ _ C).obj toSimplexCategory.op).map_injective hfg
  · exact ⟨((Functor.whiskeringLeft _ _ C).obj toSimplexCategory.op).preimage τ,
      ((Functor.whiskeringLeft _ _ C).obj toSimplexCategory.op).map_preimage τ⟩

end CategoryTheory.SimplicialObject

end

/-!
## Degeneracy maps of a simplicial object are split monomorphisms

Let `C` be a category and let `X` be a simplicial object of `C`. Each degeneracy map
`σ i : Xₙ ⟶ Xₙ₊₁` has a left inverse: the face map `δ i.castSucc`, and also the face map
`δ i.succ`, composes with it to the identity of `Xₙ`. Hence `σ i` is a split monomorphism, and in
particular a monomorphism.

### Main results

* `CategoryTheory.SimplicialObject.isSplitMono_σ`: the degeneracy `X.σ i` of a simplicial object
  `X` is a split monomorphism.

### References

* [Stacks, Tag 016F](https://stacks.math.columbia.edu/tag/016F)
-/

section

open CategoryTheory

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- **Stacks 016F**.
Each degeneracy map `X.σ i : Xₙ ⟶ Xₙ₊₁` of a simplicial object `X` of a category `C` has a left
inverse, namely the face map `X.δ i.castSucc`; in particular `X.σ i` is a monomorphism. -/
@[stacks 016F]
public instance isSplitMono_σ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    IsSplitMono (X.σ i) :=
  IsSplitMono.mk' ⟨X.δ i.castSucc, X.δ_comp_σ_self⟩

end CategoryTheory.SimplicialObject

end

/-!
## Simplicial objects as presheaves

A simplicial object of a category `C` is a contravariant functor from the category `Δ` of finite
nonempty ordered sets to `C`, which is precisely a `C`-valued presheaf on `Δ`. Consequently a
morphism of simplicial objects and a morphism of presheaves on `Δ` are the same thing:
`Mor(U, U') = Mor_{PSh(Δ)}(U, U')`.

Mathlib *defines* `CategoryTheory.SimplicialObject C` to be the presheaf category
`SimplexCategoryᵒᵖ ⥤ C`, and a morphism of simplicial objects to be a natural transformation, so
the displayed equality of hom-sets holds by definition: the two sides are the same type, and
`SimplicialObject C = (SimplexCategoryᵒᵖ ⥤ C)` is `rfl`. What the equality asserts, once one uses
the source's concrete presentation of a simplicial object by its terms `U_n` together with faces
`d^n_j` and degeneracies `s^n_j`, is that this common hom-set is computed by the generators of `Δ`:
a morphism `U ⟶ U'` is the same thing as a family of morphisms `U_n ⟶ U'_n` commuting with all the
`d^n_j` and all the `s^n_j`. It is also [Stacks, Tag 016B] part (3).

### Main results

* `CategoryTheory.SimplicialObject.existsUnique_hom_app_eq`: a family of morphisms `U_n ⟶ U'_n`
  commuting with the faces and the degeneracies extends uniquely to a morphism of simplicial
  objects, i.e. to a morphism of `C`-valued presheaves on `Δ`, with the given morphisms as its
  components.

### References

* [Stacks, Tag 016H](https://stacks.math.columbia.edu/tag/016H)
-/

section

open CategoryTheory Opposite Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

section

variable {U U' : SimplicialObject C}
  (d : ∀ n : ℕ, U.obj (op ⦋n⦌) ⟶ U'.obj (op ⦋n⦌))

/-- A family commuting with the faces and the degeneracies satisfies the naturality square at every
morphism of `Δ`.

The property of `φ : x ⟶ y` that the square commutes at `φ` is
`(MorphismProperty.naturalityProperty (fun X => d X.unop.len)).unop`, Mathlib's naturality
property for the pair of functors `U`, `U'` out of `Δᵒᵖ`, read back along `op`; it is
multiplicative by `MorphismProperty.IsMultiplicative.naturalityProperty` and
`MorphismProperty.IsMultiplicative.unop`, so the hypotheses on `δ` and `σ` force it to be `⊤`. -/
public theorem naturality_of_δ_σ
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)), U.δ i ≫ d n = d (n + 1) ≫ U'.δ i)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), U.σ i ≫ d (n + 1) = d n ≫ U'.σ i)
    {x y : SimplexCategory} (φ : x ⟶ y) :
    U.map φ.op ≫ d x.len = d y.len ≫ U'.map φ.op := by
  have h : (MorphismProperty.naturalityProperty
      (F₁ := U) (F₂ := U') (fun X => d X.unop.len)).unop = ⊤ :=
    SimplexCategory.morphismProperty_eq_top _ (fun {n} i => hδ n i) (fun {n} i => hσ n i)
  exact h.symm.le φ (by simp)

end

/-- **Stacks 016H**.
Let `U`, `U'` be simplicial objects of a category `C`, and let `d n : U_n ⟶ U'_n` be a family of
morphisms commuting with the face maps `δ i` and with the degeneracy maps `σ i`. Then there is a
unique morphism of simplicial objects `f : U ⟶ U'` — equivalently, by definition, a unique morphism
`U ⟶ U'` of `C`-valued presheaves on `Δ` — whose component in degree `n` is `d n`. -/
@[stacks 016H "the common hom-set is the set of degreewise families \
  commuting with the faces and the degeneracies"]
public theorem existsUnique_hom_app_eq {U U' : SimplicialObject C}
    (d : ∀ n : ℕ, U.obj (op ⦋n⦌) ⟶ U'.obj (op ⦋n⦌))
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)), U.δ i ≫ d n = d (n + 1) ≫ U'.δ i)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), U.σ i ≫ d (n + 1) = d n ≫ U'.σ i) :
    ∃! f : U ⟶ U', ∀ n : ℕ, f.app (op ⦋n⦌) = d n := by
  refine ⟨{ app := fun x => d x.unop.len
            naturality := fun _ _ g => naturality_of_δ_σ d hδ hσ g.unop }, fun _ => rfl, ?_⟩
  intro f hf
  ext x
  exact hf x.unop.len

end CategoryTheory.SimplicialObject

end

/-!
## Cosimplicial objects are their coface and codegeneracy data

A cosimplicial object of a category `C` is a covariant functor `U : Δ ⥤ C`, Mathlib's
`CategoryTheory.CosimplicialObject C`. Such a functor amounts to the objects `Uₙ = U ⦋n⦌`
together with the coface maps `δⁿⱼ = U (δ j) : Uₙ ⟶ Uₙ₊₁` and the codegeneracy maps
`σⁿⱼ = U (σ j) : Uₙ₊₁ ⟶ Uₙ`, which satisfy the cosimplicial identities of [Stacks, Tag 0167];
conversely every family of objects and morphisms satisfying those identities is the data of a
*unique* cosimplicial object, and a morphism of cosimplicial objects is nothing but a family
of morphisms `Uₙ ⟶ U'ₙ` commuting with the `δ`'s and the `σ`'s. Equivalently: restriction
along the presentation of `Δ` by the generators `δ`, `σ` and the cosimplicial identities is an
isomorphism from the cosimplicial objects of `C` onto the functors out of that presentation.

### Main results

* `CategoryTheory.CosimplicialObject.existsUnique_comp_toSimplexCategory_and_hom_app_eq`:
  every coface–codegeneracy datum in `C` comes from a unique cosimplicial object of `C`, and
  every family `Uₙ ⟶ U'ₙ` commuting with the coface and codegeneracy maps comes from a unique
  morphism of cosimplicial objects.

### References

* [Stacks, Tag 016K](https://stacks.math.columbia.edu/tag/016K)
* [Stacks, Tag 0167](https://stacks.math.columbia.edu/tag/0167)
* [Stacks, Tag 0168](https://stacks.math.columbia.edu/tag/0168)
-/

section

universe v u

open CategoryTheory Simplicial

namespace CategoryTheory.CosimplicialObject

section Naturality

variable {C : Type u} [Category.{v} C] (U U' : CosimplicialObject C)
  (a : ∀ n : ℕ, U ^⦋n⦌ ⟶ U' ^⦋n⦌)

/-- A family `a n : Uₙ ⟶ U'ₙ` commuting with the coface and the codegeneracy maps of cosimplicial
objects `U`, `U'` is natural for every morphism of `Δ`.

The property of `φ : x ⟶ y` that the square commutes at `φ` is
`MorphismProperty.naturalityProperty (fun x => a x.len)`, Mathlib's naturality property for the
pair of functors `U`, `U'` out of `Δ`; it is multiplicative by
`MorphismProperty.IsMultiplicative.naturalityProperty`, so the hypotheses on `δ` and `σ` force it
to be `⊤`. -/
private lemma app_naturality
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)), U.δ i ≫ a (n + 1) = a n ≫ U'.δ i)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), U.σ i ≫ a n = a (n + 1) ≫ U'.σ i)
    {x y : SimplexCategory} (φ : x ⟶ y) : U.map φ ≫ a y.len = a x.len ≫ U'.map φ := by
  have h : MorphismProperty.naturalityProperty (F₁ := U) (F₂ := U') (fun x => a x.len) = ⊤ :=
    SimplexCategory.morphismProperty_eq_top _ (fun {n} i => hδ n i) (fun {n} i => hσ n i)
  exact h.symm.le φ (by simp)

end Naturality

/-- **Stacks 016K** (parts (2) and (3), via the presented category `SimplexCategoryGenRel`).
Let `C` be a category. (2) Given objects `Uₙ` of `C` and morphisms `δⁿⱼ : Uₙ ⟶ Uₙ₊₁`,
`σⁿⱼ : Uₙ₊₁ ⟶ Uₙ` satisfying the cosimplicial identities — that is, a functor `F` out of the
presentation `SimplexCategoryGenRel` of `Δ` by these generators and relations — there is a unique
cosimplicial object `U` of `C` with `Uₙ = U ⦋n⦌`, `δⁿⱼ = U (δ j)` and `σⁿⱼ = U (σ j)`. (3) Given
cosimplicial objects `U`, `U'` and a family of morphisms `a n : Uₙ ⟶ U'ₙ` commuting with the coface
and the codegeneracy maps, there is a unique morphism `f : U ⟶ U'` of cosimplicial objects with
`f.app ⦋n⦌ = a n`. -/
@[stacks 016K "part (1) is `CategoryTheory.CosimplicialObject.δ_comp_δ` and its \
  companions in Mathlib; parts (2) and (3) are stated with the coface–codegeneracy \
  datum encoded as a functor out of the presented category `SimplexCategoryGenRel`, \
  so that no equality of objects of `C` is transported"]
public theorem existsUnique_comp_toSimplexCategory_and_hom_app_eq
    (C : Type u) [Category.{v} C] :
    (∀ F : SimplexCategoryGenRel ⥤ C,
        ∃! U : CosimplicialObject C, SimplexCategoryGenRel.toSimplexCategory ⋙ U = F) ∧
      ∀ (U U' : CosimplicialObject C) (a : ∀ n : ℕ, U ^⦋n⦌ ⟶ U' ^⦋n⦌),
        (∀ (n : ℕ) (i : Fin (n + 2)), U.δ i ≫ a (n + 1) = a n ≫ U'.δ i) →
        (∀ (n : ℕ) (i : Fin (n + 1)), U.σ i ≫ a n = a (n + 1) ≫ U'.σ i) →
        ∃! f : U ⟶ U', ∀ n : ℕ, f.app ⦋n⦌ = a n := by
  constructor
  · intro F
    refine ⟨SimplexCategoryGenRel.toSimplexCategoryInv ⋙ F, ?_, ?_⟩
    · beta_reduce
      rw [← Functor.assoc, SimplexCategoryGenRel.toSimplexCategory_comp_toSimplexCategoryInv,
        Functor.id_comp]
    · intro U hU
      rw [← hU, ← Functor.assoc,
        SimplexCategoryGenRel.toSimplexCategoryInv_comp_toSimplexCategory, Functor.id_comp]
  · intro U U' a hδ hσ
    refine ⟨{ app := fun x => a x.len
              naturality := fun x y φ => app_naturality U U' a hδ hσ φ },
      fun n => rfl, ?_⟩
    intro f hf
    ext x
    exact hf x.len

end CategoryTheory.CosimplicialObject

end

/-!
## The cosimplicial identities with unindexed coface and codegeneracy maps

Let `U` be a cosimplicial object of a category `C`, with coface maps `δⁿᵢ : Uₙ₋₁ ⟶ Uₙ` and
codegeneracy maps `σⁿᵢ : Uₙ₊₁ ⟶ Uₙ` as in [Stacks, Tag 016K]. Dropping the superscript that records
the level and writing simply `δᵢ` and `σᵢ`, the cosimplicial identities of [Stacks, Tag 0167] read

* if `i < j` then `δⱼ ∘ δᵢ = δᵢ ∘ δⱼ₋₁`;
* if `i < j` then `σⱼ ∘ δᵢ = δᵢ ∘ σⱼ₋₁`;
* `σⱼ ∘ δⱼ = id = σⱼ ∘ δⱼ₊₁`;
* if `j + 1 < i` then `σⱼ ∘ δᵢ = δᵢ₋₁ ∘ σⱼ`;
* if `i ≤ j` then `σⱼ ∘ σᵢ = σᵢ ∘ σⱼ₊₁`,

each holding whenever the two composites it compares are defined — that is, whenever the indices
occurring in it are in range at the levels at which they occur.

### Main results

* `CategoryTheory.CosimplicialObject.cosimplicial_identities_of_val`: the five relations above, for
  an arbitrary cosimplicial object of an arbitrary category, at every level and for all indices in
  range.

### References

* [Stacks, Tag 016L](https://stacks.math.columbia.edu/tag/016L)
-/

section

@[expose] public section

universe v u

open CategoryTheory Simplicial

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/-- **Stacks 016L**.
Let `X` be a cosimplicial object of a category `C`. Writing `δᵢ : Xₙ₋₁ ⟶ Xₙ` for `X.δ` and
`σᵢ : Xₙ₊₁ ⟶ Xₙ` for `X.σ` without recording the level, and reading `f ∘ g` as `g ≫ f`:
(1) if `i < j` then `δⱼ ∘ δᵢ = δᵢ ∘ δⱼ₋₁`;
(2) if `i < j` then `σⱼ ∘ δᵢ = δᵢ ∘ σⱼ₋₁`;
(3) `σⱼ ∘ δⱼ = id` and `σⱼ ∘ δⱼ₊₁ = id`;
(4) if `j + 1 < i` then `σⱼ ∘ δᵢ = δᵢ₋₁ ∘ σⱼ`;
(5) if `i ≤ j` then `σⱼ ∘ σᵢ = σᵢ ∘ σⱼ₊₁`.
Each is asserted for all indices whose bounds make both composites defined, an index repeated
across levels being recognised by its value. -/
@[stacks 016L]
public theorem cosimplicial_identities_of_val (X : CosimplicialObject C) :
    (∀ {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 3)} {i' : Fin (n + 3)} {j' : Fin (n + 2)},
        (i : ℕ) < (j : ℕ) → (i' : ℕ) = (i : ℕ) → (j' : ℕ) + 1 = (j : ℕ) →
          X.δ i ≫ X.δ j = X.δ j' ≫ X.δ i') ∧
      (∀ {n : ℕ} {i : Fin (n + 3)} {j : Fin (n + 2)} {i' : Fin (n + 2)} {j' : Fin (n + 1)},
        (i : ℕ) < (j : ℕ) → (i' : ℕ) = (i : ℕ) → (j' : ℕ) + 1 = (j : ℕ) →
          X.δ i ≫ X.σ j = X.σ j' ≫ X.δ i') ∧
      (∀ {n : ℕ} {j : Fin (n + 1)} {i : Fin (n + 2)},
        (i : ℕ) = (j : ℕ) → X.δ i ≫ X.σ j = 𝟙 (X ^⦋n⦌)) ∧
      (∀ {n : ℕ} {j : Fin (n + 1)} {i : Fin (n + 2)},
        (i : ℕ) = (j : ℕ) + 1 → X.δ i ≫ X.σ j = 𝟙 (X ^⦋n⦌)) ∧
      (∀ {n : ℕ} {i : Fin (n + 3)} {j : Fin (n + 2)} {i' : Fin (n + 2)} {j' : Fin (n + 1)},
        (j : ℕ) + 1 < (i : ℕ) → (i' : ℕ) + 1 = (i : ℕ) → (j' : ℕ) = (j : ℕ) →
          X.δ i ≫ X.σ j = X.σ j' ≫ X.δ i') ∧
      ∀ {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} {i' : Fin (n + 1)} {j' : Fin (n + 2)},
        (i : ℕ) ≤ (j : ℕ) → (i' : ℕ) = (i : ℕ) → (j' : ℕ) = (j : ℕ) + 1 →
          X.σ i ≫ X.σ j = X.σ j' ≫ X.σ i' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i j i' j' hij hi hj
    obtain rfl : j = j'.succ := Fin.ext hj.symm
    obtain rfl : i' = i.castSucc := Fin.ext hi
    exact X.δ_comp_δ (by rw [Fin.le_def]; rw [Fin.val_succ] at hij; omega)
  · intro n i j i' j' hij hi hj
    obtain rfl : j = j'.succ := Fin.ext hj.symm
    obtain rfl : i = i'.castSucc := Fin.ext hi.symm
    exact X.δ_comp_σ_of_le
      (by rw [Fin.le_def, Fin.val_castSucc]
          rw [Fin.val_succ, Fin.val_castSucc] at hij; omega)
  · intro n j i hi
    exact X.δ_comp_σ_self' (Fin.ext hi : i = j.castSucc)
  · intro n j i hi
    exact X.δ_comp_σ_succ' (Fin.ext hi : i = j.succ)
  · intro n i j i' j' hij hi hj
    obtain rfl : i = i'.succ := Fin.ext hi.symm
    obtain rfl : j = j'.castSucc := Fin.ext hj.symm
    exact X.δ_comp_σ_of_gt
      (by rw [Fin.lt_def, Fin.val_castSucc]
          rw [Fin.val_succ, Fin.val_castSucc] at hij; omega)
  · intro n i j i' j' hij hi hj
    obtain rfl : i = i'.castSucc := Fin.ext hi.symm
    obtain rfl : j' = j.succ := Fin.ext hj
    exact X.σ_comp_σ (by rw [Fin.le_def]; omega)

end CategoryTheory.CosimplicialObject

end

end

/-!
## Coface maps of a cosimplicial object are split monomorphisms

Let `C` be a category and let `X` be a cosimplicial object of `C`. Each coface map
`δ i : Xₙ ⟶ Xₙ₊₁` has a left inverse: a degeneracy map `σ j` composes with it to the identity of
`Xₙ`, namely `j = i` read in `Fin (n + 1)` when `i ≠ Fin.last` and `j = Fin.last n` when
`i = Fin.last (n + 1)`. Hence `δ i` is a split monomorphism, and in particular a monomorphism.

### Main results

* `CategoryTheory.CosimplicialObject.isSplitMono_δ`: the coface map `X.δ i` of a cosimplicial
  object `X` is a split monomorphism.

### References

* [Stacks, Tag 016O](https://stacks.math.columbia.edu/tag/016O)
-/

section

open CategoryTheory

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The coface map `SimplexCategory.δ i : ⦋n⦌ ⟶ ⦋n + 1⦌` as a split monomorphism: its retraction
is `SimplexCategory.σ j` when `i = j.castSucc`, and `SimplexCategory.σ (Fin.last n)` when `i` is
the last coface index. -/
private def splitMonoδ {n : ℕ} (i : Fin (n + 2)) : SplitMono (SimplexCategory.δ i) :=
  i.lastCases ⟨SimplexCategory.σ (Fin.last n),
      SimplexCategory.δ_comp_σ_succ' (Fin.succ_last n).symm⟩
    fun j => ⟨SimplexCategory.σ j, SimplexCategory.δ_comp_σ_self⟩

/-- **Stacks 016O**.
Each coface map `X.δ i : Xₙ ⟶ Xₙ₊₁` of a cosimplicial object `X` of a category `C` has a left
inverse, namely a degeneracy map `X.σ j`; in particular `X.δ i` is a monomorphism. -/
@[stacks 016O]
public instance isSplitMono_δ (X : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    IsSplitMono (X.δ i) :=
  IsSplitMono.mk' ((splitMonoδ i).map X)

end CategoryTheory.CosimplicialObject

end

/-!
## The standard cosimplicial sets `C[n]`

For every `n ≥ 0` the standard cosimplicial set `C[n]` is the covariant functor

`Δ ⥤ Sets`, `⦋k⦌ ↦ Mor_Δ(⦋n⦌, ⦋k⦌)`,

that is, a cosimplicial set in the sense of [Stacks, Tag 016K] — an object of Mathlib's
`CategoryTheory.CosimplicialObject (Type u)` — whose structure map at `φ : ⦋k⦌ ⟶ ⦋l⦌` is
`α ↦ α ≫ φ`. Since `Mor_Δ(⦋n⦌, ⦋k⦌)` is contravariant in `⦋n⦌`, with `ψ : ⦋n⦌ ⟶ ⦋m⦌` acting by
`α ↦ ψ ≫ α`, the family `⦋n⦌ ↦ C[n]` is a simplicial object in cosimplicial sets. Thus `C[n]`
is the value at `⦋n⦌` of the covariant Yoneda embedding of `Δ`, and it corepresents evaluation
in degree `n`: for every cosimplicial set `U` the map `γ ↦ γ_n(id_⦋n⦌)` is a bijection
`Mor(C[n], U) → Uₙ`, which is what pins `C[n]` up to unique isomorphism. Each term
`C[n]ₖ = Mor_Δ(⦋n⦌, ⦋k⦌)` is a finite nonempty set.

This is dual to the standard simplicial set `Δ[n] : ⦋k⦌ ↦ Mor_Δ(⦋k⦌, ⦋n⦌)` of
[Stacks, Tag 0176], the *cosimplicial object in simplicial sets* `SSet.stdSimplex = uliftYoneda`;
dually `⦋n⦌ ↦ C[n]` is the *simplicial object in cosimplicial sets* `uliftCoyoneda`.

### Main results

* `CategoryTheory.CosimplicialObject.uliftCoyoneda_spec`: the cosimplicial sets
  `C[n] = uliftCoyoneda.obj (op ⦋n⦌)` have the terms and the structure maps of the source, the
  family `⦋n⦌ ↦ C[n]` is simplicial with `ψ` acting by `α ↦ ψ ≫ α`, and `C[n]` corepresents
  evaluation in degree `n`.

### References

* [Stacks, Tag 0B13](https://stacks.math.columbia.edu/tag/0B13)
-/

section

open CategoryTheory Opposite Simplicial

universe u

namespace CategoryTheory.CosimplicialObject

/-- **Stacks 0B13** (with `C[n]` as `uliftCoyoneda.obj (op n)`).
For every object `n` of `Δ` the cosimplicial set `C[n] = uliftCoyoneda.obj (op n)` is
`k ↦ Mor_Δ(n, k)`, with `φ : k ⟶ l` acting by `α ↦ α ≫ φ`; the family `n ↦ C[n]` is a simplicial
object in cosimplicial sets, with `ψ : n ⟶ m` acting by `α ↦ ψ ≫ α`; and `C[n]` corepresents
evaluation in degree `n`, in that `γ ↦ γ_n(id_n)` is a bijection `Mor(C[n], U) → Uₙ` for every
cosimplicial set `U`. -/
@[stacks 0B13 "C[n] is Mathlib's uliftCoyoneda.obj (op n), dual to Δ[n] = SSet.stdSimplex.obj n \
  of Tag 0176; the statement records its terms and structure maps, the simplicial structure of \
  the family in n, and the corepresentability that characterises it"]
public theorem uliftCoyoneda_spec :
    (∀ n k : SimplexCategory, (uliftCoyoneda.{u}.obj (op n)).obj k = ULift.{u} (n ⟶ k)) ∧
    (∀ (n k l : SimplexCategory) (φ : k ⟶ l) (α : ULift.{u} (n ⟶ k)),
      ((uliftCoyoneda.{u}.obj (op n)).map φ α).down = α.down ≫ φ) ∧
    (∀ (n m k : SimplexCategory) (ψ : n ⟶ m) (α : ULift.{u} (m ⟶ k)),
      ((uliftCoyoneda.{u}.map ψ.op).app k α).down = ψ ≫ α.down) ∧
    (∀ (n : SimplexCategory) (U : CosimplicialObject (Type u)),
      Function.Bijective fun γ : uliftCoyoneda.{u}.obj (op n) ⟶ U =>
        γ.app n (ULift.up (𝟙 n))) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ => ?_⟩
  exact uliftCoyonedaEquiv.bijective

end CategoryTheory.CosimplicialObject

end
