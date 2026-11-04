module

public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Finite products commute with filtered colimits of sets

Let `K` be a filtered category and let `G` be a family of functors `K ⥤ Type w` indexed by a
finite type `ι`. The pointwise product `k ↦ ∀ i, (G i).obj k` is again a functor on `K`, and the
tuple-of-germs map

  `colim_K (∀ i, G i) ⟶ ∀ i, colim_K (G i)`

is a bijection. Surjectivity holds because the finitely many stages at which the components are
represented have a common upper bound; injectivity because the finitely many morphisms that
equalize the components one at a time can be replaced by a single one. Both halves reduce to one
combinatorial fact about filtered categories, isolated here as
`Stacks.FilteredColimit.exists_hom_forall_of_finite`: finitely many conditions on morphisms out
of a fixed object, each stable under postcomposition, are met simultaneously.

This is the finite-product case of Stacks 002W, for a *single* filtered index category. It is
not Mathlib's `CategoryTheory.Limits.Types.isIso_colimitPointwiseProductToProductColimit`, whose
product is indexed by a family of *different* categories and whose colimit is therefore taken
over their product category, and which needs no finiteness of the index; nor is it Mathlib's
`CategoryTheory.Limits.colimitLimitIso`, which asks for a small index category. Here the index
category is unrestricted in size and the index type is finite, which is exactly the shape a
stalk computation needs.

## Main definitions

* `Stacks.FilteredColimit.pointwisePi` — the pointwise product of a family of functors into
  types.
* `Stacks.FilteredColimit.colimitPiComparison` — the tuple-of-germs map from the colimit of a
  pointwise product to the product of the colimits.
* `Stacks.FilteredColimit.colimitPiEquiv` — the same map as an equivalence.

## Main results

* `Stacks.FilteredColimit.exists_hom_forall_of_finite` — simultaneous realization of finitely
  many conditions on morphisms out of one object of a filtered category.
* `Stacks.FilteredColimit.colimitPiComparison_bijective` — the interchange.

## Implementation notes

The index type `ι` is only assumed `Finite`; the `Fintype` and `DecidableEq` instances needed to
run the induction over `Finset.univ` are obtained classically inside the proof, so no
decidability hypothesis reaches the statements.

## References

* [Stacks Project, Tag 002W](https://stacks.math.columbia.edu/tag/002W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w₂ v₁ u₁

namespace Stacks.FilteredColimit

variable {K : Type u₁} [Category.{v₁} K]

/-- **Finitely many conditions on morphisms out of one object are met simultaneously in a
filtered category.** Each `P i` is a property of morphisms out of `k`, stable under
postcomposition, and holds of at least one morphism out of `k`; then a single morphism out of
`k` satisfies all of them. The two filtered-category moves are taking an upper bound of two
objects and coequalizing two parallel morphisms. -/
public theorem exists_hom_forall_of_finite [IsFiltered K] {ι : Type w₂} [Finite ι] (k : K)
    (P : ι → ∀ j : K, (k ⟶ j) → Prop)
    (hmono : ∀ (i : ι) {j j' : K} (f : k ⟶ j) (g : j ⟶ j'), P i j f → P i j' (f ≫ g))
    (h : ∀ i, ∃ (j : K) (f : k ⟶ j), P i j f) :
    ∃ (j : K) (f : k ⟶ j), ∀ i, P i j f := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (j : K) (f : k ⟶ j), ∀ i ∈ s, P i j f by
    obtain ⟨j, f, hf⟩ := H Finset.univ
    exact ⟨j, f, fun i => hf i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, by simp⟩
  | insert a s ha ih =>
      obtain ⟨j, f, hf⟩ := ih
      obtain ⟨j', f', hf'⟩ := h a
      refine ⟨IsFiltered.coeq (f ≫ IsFiltered.leftToMax j j') (f' ≫ IsFiltered.rightToMax j j'),
        (f ≫ IsFiltered.leftToMax j j') ≫ IsFiltered.coeqHom _ _, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rw [IsFiltered.coeq_condition]
        exact hmono i (f' ≫ IsFiltered.rightToMax j j') _ (hmono i f' _ hf')
      · exact hmono i (f ≫ IsFiltered.leftToMax j j') _ (hmono i f _ (hf i hi))

/-- The pointwise product of a family of functors into types: its value at `k` is the type of
tuples `∀ i, (G i).obj k`, and a morphism acts componentwise. -/
public def pointwisePi {ι : Type w₂} (G : ι → (K ⥤ Type w)) : K ⥤ Type (max w w₂) where
  obj k := ∀ i, (G i).obj k
  map f := ↾ (fun t i => (G i).map f (t i))

/-- The cocone on the pointwise product whose component at a stage sends a tuple of sections to
the tuple of their germs. -/
public def pointwisePiCocone {ι : Type w₂} (G : ι → (K ⥤ Type w)) [∀ i, HasColimit (G i)] :
    Cocone (pointwisePi G) where
  pt := ∀ i, colimit (G i)
  ι :=
    { app := fun U => ↾ (fun t i => colimit.ι (G i) U (t i))
      naturality := by
        intro U V f
        ext t
        funext i
        exact congrArg (fun m => m (t i)) (colimit.w (G i) f) }

/-- **The tuple-of-germs map** from the colimit of a pointwise product to the product of the
colimits. -/
public def colimitPiComparison {ι : Type w₂} (G : ι → (K ⥤ Type w)) [∀ i, HasColimit (G i)]
    [HasColimit (pointwisePi G)] :
    colimit (pointwisePi G) → ∀ i, colimit (G i) :=
  fun z => colimit.desc _ (pointwisePiCocone G) z

/-- The tuple-of-germs map computes the germ of a tuple componentwise. -/
public theorem colimitPiComparison_ι {ι : Type w₂} (G : ι → (K ⥤ Type w))
    [∀ i, HasColimit (G i)] [HasColimit (pointwisePi G)] (U : K)
    (t : ∀ i, (G i).obj U) (i : ι) :
    colimitPiComparison G (colimit.ι (pointwisePi G) U t) i = colimit.ι (G i) U (t i) :=
  congrFun (colimit.ι_desc_apply (pointwisePiCocone G) U t) i

/-- **The tuple-of-germs map is surjective** over a filtered index category, for a finite
index type: the finitely many stages at which the components are represented have a common
upper bound. -/
public theorem colimitPiComparison_surjective [IsFiltered K] {ι : Type w₂} [Finite ι]
    (G : ι → (K ⥤ Type w)) [∀ i, HasColimit (G i)] [HasColimit (pointwisePi G)] :
    Function.Surjective (colimitPiComparison G) := by
  intro s
  obtain ⟨k⟩ : Nonempty K := IsFiltered.nonempty
  obtain ⟨j, f, hj⟩ := exists_hom_forall_of_finite k
    (fun i j _ => ∃ t : (G i).obj j, colimit.ι (G i) j t = s i)
    (by
      rintro i j j' f g ⟨t, ht⟩
      exact ⟨(G i).map g t, by rw [← ht]; exact colimit.w_apply (G i) g t⟩)
    (by
      intro i
      obtain ⟨U, t, ht⟩ := Types.jointly_surjective' (s i)
      refine ⟨IsFiltered.max k U, IsFiltered.leftToMax k U,
        (G i).map (IsFiltered.rightToMax k U) t, ?_⟩
      rw [← ht]
      exact colimit.w_apply (G i) (IsFiltered.rightToMax k U) t)
  choose t ht using hj
  exact ⟨colimit.ι (pointwisePi G) j t,
    funext fun i => (colimitPiComparison_ι G j t i).trans (ht i)⟩

/-- **The tuple-of-germs map is injective** over a filtered index category, for a finite index
type: two tuples with the same germs are equalized componentwise by finitely many morphisms,
hence by a single one. -/
public theorem colimitPiComparison_injective [IsFiltered K] {ι : Type w₂} [Finite ι]
    (G : ι → (K ⥤ Type w)) [∀ i, HasColimit (G i)] [HasColimit (pointwisePi G)] :
    Function.Injective (colimitPiComparison G) := by
  intro a b hab
  obtain ⟨U, t, t', rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (colimit.isColimit (pointwisePi G)) a b
  obtain ⟨j, g, hg⟩ := exists_hom_forall_of_finite U
    (fun i j g => (G i).map g (t i) = (G i).map g (t' i))
    (fun i j j' f g hf => by rw [(G i).map_comp, types_comp_apply, types_comp_apply, hf])
    fun i => (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (G i)) (t i) (t' i)).mp <|
      (colimitPiComparison_ι G U t i).symm.trans <|
        (congrFun hab i).trans (colimitPiComparison_ι G U t' i)
  exact (Types.colimit_sound g rfl).trans <|
    (congrArg _ (funext hg : (pointwisePi G).map g t = (pointwisePi G).map g t')).trans
      (Types.colimit_sound g rfl).symm

/-- **Filtered colimits of sets commute with finite products**, in the form of the
tuple-of-germs map being a bijection. -/
public theorem colimitPiComparison_bijective [IsFiltered K] {ι : Type w₂} [Finite ι]
    (G : ι → (K ⥤ Type w)) [∀ i, HasColimit (G i)] [HasColimit (pointwisePi G)] :
    Function.Bijective (colimitPiComparison G) :=
  ⟨colimitPiComparison_injective G, colimitPiComparison_surjective G⟩

/-- Filtered colimits of sets commute with finite products, as an equivalence. -/
public def colimitPiEquiv [IsFiltered K] {ι : Type w₂} [Finite ι] (G : ι → (K ⥤ Type w))
    [∀ i, HasColimit (G i)] [HasColimit (pointwisePi G)] :
    colimit (pointwisePi G) ≃ ∀ i, colimit (G i) :=
  Equiv.ofBijective _ (colimitPiComparison_bijective G)

end Stacks.FilteredColimit

end
