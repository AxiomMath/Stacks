module

public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Final

/-!
# A colimit over a disjoint union of categories is the coproduct of the colimits

Let `Cs : I → Type*` be a family of categories, let `Σ i, Cs i` be their disjoint union and let
`X : (Σ i, Cs i) ⥤ A` be a diagram in a category `A` with the relevant colimits and coproducts.
The comparison maps `colimit.pre X (CategoryTheory.Sigma.incl i)` assemble into an isomorphism

`∐ i, colimit (Sigma.incl i ⋙ X) ≅ colimit X`

and this isomorphism is natural in `X`. Consequently, if a category `J` is presented as a
disjoint union of a family of categories — that is, if the functor `Sigma.desc e` induced by a
family `e i : Cs i ⥤ J` is an equivalence — then the comparison maps `colimit.pre F (e i)`
assemble into an isomorphism `∐ i, colimit (e i ⋙ F) ≅ colimit F` for every `F : J ⥤ A`.

The last section records the criterion for `Sigma.desc e` to be an equivalence in the form in
which a decomposition is usually available: each `e i` is fully faithful, there are no morphisms
between the images of different summands, and every object lies in the image of some summand.

In an abelian category the coproduct is a direct sum, so this is the formal content of a *sum
formula* for a left Kan extension along a functor whose comma categories are disjoint unions —
the shape of Stacks 09WG's sum formula for the lower shriek of a simplicial component inclusion.

## Main results

* `Stacks.Sites.AbelianSumFormula.sigmaColimitIso`: the isomorphism
  `∐ i, colimit (Sigma.incl i ⋙ X) ≅ colimit X`, whose `hom` is the assembled comparison map.
* `Stacks.Sites.AbelianSumFormula.sigmaMap_comp_sigmaColimitIso_hom`: it is natural in `X`.
* `Stacks.Sites.AbelianSumFormula.isIso_sigmaDesc_colimitPre` and
  `Stacks.Sites.AbelianSumFormula.colimitDecompositionIso`: the same statement for a category
  presented as the disjoint union of a family of categories, together with
  `Stacks.Sites.AbelianSumFormula.sigmaMap_comp_colimitDecompositionIso_hom`, its naturality.
* `Stacks.Sites.AbelianSumFormula.sigmaDesc_isEquivalence`: the criterion for a family of
  functors to present its target as a disjoint union.

## Implementation notes

Every isomorphism is stated through `CategoryTheory.Limits.colimit.pre`, the canonical comparison
map, so that its composites with the colimit injections are computed by the lemmas about
`colimit.pre`.

The universes of the index type, of the summand categories and of the target category are
independent.

## References

* [Stacks Project, Tag 04B0](https://stacks.math.columbia.edu/tag/04B0)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v u

namespace Stacks.Sites.AbelianSumFormula

variable {I : Type w} {Cs : I → Type u₁} [∀ i, Category.{v₁} (Cs i)]
  {A : Type u} [Category.{v} A]

section SigmaCategory

variable (X : (Σ i, Cs i) ⥤ A) [HasColimit X]
  [∀ i, HasColimit (CategoryTheory.Sigma.incl i ⋙ X)]
  [HasCoproduct fun i => colimit (CategoryTheory.Sigma.incl i ⋙ X)]

/-- **A colimit over a disjoint union of categories is the coproduct of the colimits over the
summands.** The comparison maps `colimit.pre X (Sigma.incl i)` assemble into an isomorphism
`∐ i, colimit (Sigma.incl i ⋙ X) ≅ colimit X`. -/
@[simps hom]
noncomputable def sigmaColimitIso :
    (∐ fun i => colimit (CategoryTheory.Sigma.incl i ⋙ X)) ≅ colimit X where
  hom := Limits.Sigma.desc fun i => colimit.pre X (CategoryTheory.Sigma.incl i)
  inv := colimit.desc X (Cocone.mk _
    { app := fun p => colimit.ι (CategoryTheory.Sigma.incl p.1 ⋙ X) p.2 ≫
        Limits.Sigma.ι (fun i => colimit (CategoryTheory.Sigma.incl i ⋙ X)) p.1
      naturality := by
        rintro ⟨i, x⟩ ⟨-, y⟩ ⟨f⟩
        simpa using colimit.w_assoc (CategoryTheory.Sigma.incl i ⋙ X) f
          (Limits.Sigma.ι (fun i => colimit (CategoryTheory.Sigma.incl i ⋙ X)) i) })
  hom_inv_id := by
    ext i x
    simp only [Limits.Sigma.ι_comp_desc_assoc, colimit.ι_pre_assoc, colimit.ι_desc,
      Category.comp_id]
    rfl
  inv_hom_id := by
    ext ⟨i, x⟩
    simp only [colimit.ι_desc_assoc, Category.comp_id]
    exact (Category.assoc ..).trans <|
      (whisker_eq (colimit.ι (CategoryTheory.Sigma.incl i ⋙ X) x)
        (Limits.Sigma.ι_comp_desc _ i)).trans (colimit.ι_pre X (CategoryTheory.Sigma.incl i) x)

end SigmaCategory

section SigmaNaturality

variable {X₁ X₂ : (Σ i, Cs i) ⥤ A} [HasColimit X₁] [HasColimit X₂]
  [∀ i, HasColimit (CategoryTheory.Sigma.incl i ⋙ X₁)]
  [∀ i, HasColimit (CategoryTheory.Sigma.incl i ⋙ X₂)]
  [HasCoproduct fun i => colimit (CategoryTheory.Sigma.incl i ⋙ X₁)]
  [HasCoproduct fun i => colimit (CategoryTheory.Sigma.incl i ⋙ X₂)]

/-- `Stacks.Sites.AbelianSumFormula.sigmaColimitIso` is natural: under it, the map induced on
colimits by `φ` is the coproduct of the maps induced on the colimits over the summands. -/
theorem sigmaMap_comp_sigmaColimitIso_hom (φ : X₁ ⟶ X₂) :
    (Limits.Sigma.map fun i => colimMap (Functor.whiskerLeft (CategoryTheory.Sigma.incl i) φ)) ≫
        (sigmaColimitIso X₂).hom = (sigmaColimitIso X₁).hom ≫ colimMap φ := by
  ext i x
  simp only [sigmaColimitIso_hom, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_comp_desc,
    Limits.Sigma.ι_comp_desc_assoc, ι_colimMap_assoc, colimit.ι_pre, colimit.ι_pre_assoc,
    ι_colimMap, Functor.whiskerLeft_app]

end SigmaNaturality

section Decomposition

variable {J : Type u₂} [Category.{v₂} J] (e : ∀ i, Cs i ⥤ J)
  [(CategoryTheory.Sigma.desc e).IsEquivalence]

section

variable (F : J ⥤ A) [HasColimit F] [∀ i, HasColimit (e i ⋙ F)]
  [HasCoproduct fun i => colimit (e i ⋙ F)]

/-- **A colimit over a category presented as a disjoint union of a family of categories is the
coproduct of the colimits over the family.** The assembled comparison map is an isomorphism. -/
theorem isIso_sigmaDesc_colimitPre :
    IsIso (Limits.Sigma.desc fun i => colimit.pre F (e i)) := by
  have : ∀ i, HasColimit (CategoryTheory.Sigma.incl i ⋙
      (CategoryTheory.Sigma.desc e ⋙ F)) := fun i => inferInstanceAs (HasColimit (e i ⋙ F))
  have : HasCoproduct fun i => colimit (CategoryTheory.Sigma.incl i ⋙
      (CategoryTheory.Sigma.desc e ⋙ F)) :=
    inferInstanceAs (HasCoproduct fun i => colimit (e i ⋙ F))
  have hsigma : IsIso (Limits.Sigma.desc fun i =>
      colimit.pre (CategoryTheory.Sigma.desc e ⋙ F) (CategoryTheory.Sigma.incl i)) := by
    rw [← sigmaColimitIso_hom]
    infer_instance
  have key : (Limits.Sigma.desc fun i => colimit.pre F (e i)) =
      (Limits.Sigma.desc fun i =>
          colimit.pre (CategoryTheory.Sigma.desc e ⋙ F) (CategoryTheory.Sigma.incl i)) ≫
        colimit.pre F (CategoryTheory.Sigma.desc e) := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    have h1 : Limits.Sigma.ι (fun i => colimit (e i ⋙ F)) i ≫
        (Limits.Sigma.desc fun i =>
          colimit.pre (CategoryTheory.Sigma.desc e ⋙ F) (CategoryTheory.Sigma.incl i)) =
          colimit.pre (CategoryTheory.Sigma.desc e ⋙ F) (CategoryTheory.Sigma.incl i) :=
      Limits.Sigma.ι_comp_desc _ i
    have h2 : Limits.Sigma.ι (fun i => colimit (e i ⋙ F)) i ≫
        (Limits.Sigma.desc fun i => colimit.pre F (e i)) = colimit.pre F (e i) :=
      Limits.Sigma.ι_comp_desc _ i
    exact h2.trans (((colimit.pre_pre (F := F) (E := CategoryTheory.Sigma.desc e)
      (D := CategoryTheory.Sigma.incl i)).symm.trans
        (congrArg (· ≫ colimit.pre F (CategoryTheory.Sigma.desc e)) h1.symm)).trans
          (Category.assoc _ _ _))
  have hcomp : IsIso ((Limits.Sigma.desc fun i =>
      colimit.pre (CategoryTheory.Sigma.desc e ⋙ F) (CategoryTheory.Sigma.incl i)) ≫
        colimit.pre F (CategoryTheory.Sigma.desc e)) := inferInstance
  exact key ▸ hcomp

/-- The isomorphism `∐ i, colimit (e i ⋙ F) ≅ colimit F` attached to a decomposition of `J` as a
disjoint union, whose `hom` is the map out of the coproduct induced by the maps
`colimit.pre F (e i)`. -/
noncomputable def colimitDecompositionIso : (∐ fun i => colimit (e i ⋙ F)) ≅ colimit F :=
  haveI := isIso_sigmaDesc_colimitPre e F
  asIso (Limits.Sigma.desc fun i => colimit.pre F (e i))

/-- The `hom` of the decomposition isomorphism is the map out of the coproduct induced by the maps
`colimit.pre F (e i)`. -/
@[simp]
theorem colimitDecompositionIso_hom :
    (colimitDecompositionIso e F).hom = Limits.Sigma.desc fun i => colimit.pre F (e i) := rfl

/-- The `i`-th coprojection followed by the decomposition isomorphism is `colimit.pre F (e i)`. -/
@[reassoc (attr := simp)]
theorem ι_colimitDecompositionIso_hom (i : I) :
    Limits.Sigma.ι (fun i => colimit (e i ⋙ F)) i ≫ (colimitDecompositionIso e F).hom =
      colimit.pre F (e i) :=
  Limits.Sigma.ι_comp_desc _ i

end

variable {F G : J ⥤ A} [HasColimit F] [HasColimit G] [∀ i, HasColimit (e i ⋙ F)]
  [∀ i, HasColimit (e i ⋙ G)] [HasCoproduct fun i => colimit (e i ⋙ F)]
  [HasCoproduct fun i => colimit (e i ⋙ G)]

/-- The decomposition isomorphism is natural: under it, the map induced on colimits by `α` is the
coproduct of the maps induced on the colimits over the summands. -/
theorem sigmaMap_comp_colimitDecompositionIso_hom (α : F ⟶ G) :
    (Limits.Sigma.map fun i => colimMap (Functor.whiskerLeft (e i) α)) ≫
        (colimitDecompositionIso e G).hom =
      (colimitDecompositionIso e F).hom ≫ colimMap α := by
  refine Limits.Sigma.hom_ext _ _ fun i => colimit.hom_ext fun x => ?_
  simp only [colimitDecompositionIso_hom, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_comp_desc,
    Limits.Sigma.ι_comp_desc_assoc, ι_colimMap_assoc, colimit.ι_pre, colimit.ι_pre_assoc,
    ι_colimMap, Functor.whiskerLeft_app]

end Decomposition

section Criterion

variable {J : Type u₂} [Category.{v₂} J] (e : ∀ i, Cs i ⥤ J)

/-- A family of faithful functors induces a faithful functor out of the disjoint union of their
sources. -/
theorem sigmaDesc_faithful [∀ i, (e i).Faithful] : (CategoryTheory.Sigma.desc e).Faithful where
  map_injective := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩ ⟨g⟩ h
    exact congrArg CategoryTheory.Sigma.SigmaHom.mk ((e i).map_injective h)

/-- A family of full functors with no morphisms between the images of different members induces a
full functor out of the disjoint union of their sources. -/
theorem sigmaDesc_full [∀ i, (e i).Full]
    (hdisj : ∀ (i j : I) (X : Cs i) (Y : Cs j), ((e i).obj X ⟶ (e j).obj Y) → i = j) :
    (CategoryTheory.Sigma.desc e).Full where
  map_surjective := by
    rintro ⟨i, X⟩ ⟨j, Y⟩ f
    obtain rfl := hdisj i j X Y f
    obtain ⟨g, hg⟩ := (e i).map_surjective f
    exact ⟨CategoryTheory.Sigma.SigmaHom.mk g, hg⟩

/-- A family of functors whose images jointly exhaust the objects of the target up to isomorphism
induces an essentially surjective functor out of the disjoint union of their sources. -/
theorem sigmaDesc_essSurj
    (hsurj : ∀ x : J, ∃ (i : I) (X : Cs i), IsIsomorphic ((e i).obj X) x) :
    (CategoryTheory.Sigma.desc e).EssSurj where
  mem_essImage x := by
    obtain ⟨i, X, hX⟩ := hsurj x
    exact ⟨⟨i, X⟩, hX⟩

/-- **The criterion for a family of functors to present its target as a disjoint union.** A
family of fully faithful functors, with no morphisms between the images of two different members
and whose images jointly exhaust the objects of the target up to isomorphism, induces an
equivalence from the disjoint union of their sources. -/
theorem sigmaDesc_isEquivalence [∀ i, (e i).Full] [∀ i, (e i).Faithful]
    (hdisj : ∀ (i j : I) (X : Cs i) (Y : Cs j), ((e i).obj X ⟶ (e j).obj Y) → i = j)
    (hsurj : ∀ x : J, ∃ (i : I) (X : Cs i), Nonempty ((e i).obj X ≅ x)) :
    (CategoryTheory.Sigma.desc e).IsEquivalence :=
  have := sigmaDesc_faithful e
  have := sigmaDesc_full e hdisj
  have := sigmaDesc_essSurj e hsurj
  { }

end Criterion

end Stacks.Sites.AbelianSumFormula

end
