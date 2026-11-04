module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.BoundedEquivalence

/-!
# The filtered left derived functor

Let `A` and `B` be abelian categories and `G : A ⥤ B` an additive functor. Applying `G` to a
filtered object of `A` and taking the images of the filtration steps produces a filtered
object of `B`, and this is functorial and additive. Carrying it out degreewise on a bounded
above complex of filtered projective objects and passing to the bounded above filtered
derived category of `B` gives one route in the defining diagram of the filtered left derived
functor. If `A` has enough projectives, the comparison functor of
`CategoryTheory.FilteredDerived.filteredProjectiveMinusToDerivedMinus` is an equivalence, and
composing with a chosen inverse gives the filtered left derived functor `LF : DF⁻(A) ⥤
DF⁻(B)` together with the natural isomorphism that makes the diagram commute.

## Main definitions

* `CategoryTheory.FilteredDerived.mapFilteredObject`,
  `CategoryTheory.FilteredDerived.mapFiniteFiltered`: the image filtration of `G.obj X`, and
  the induced functor `Fil^f(A) ⥤ Fil^f(B)`.
* `CategoryTheory.FilteredDerived.filteredProjectiveMinusMapToDerivedMinus`: the
  projective-complex route in the defining diagram.
* `CategoryTheory.FilteredDerived.filteredLeftDerivedFunctor`: the filtered left derived
  functor.
* `CategoryTheory.FilteredDerived.filteredLeftDerivedFunctorComparison`: the natural
  isomorphism expressing commutativity of the diagram.

## Implementation notes

The image filtration is built with `CategoryTheory.Filtration.ofAntitone` from the family
`p ↦ Im(G(F^p X) ⟶ G X)`, which is antitone because `G` carries the inclusions of the
filtration to maps factoring through one another. Finiteness is preserved: the top step is
carried to an epimorphism, hence to the whole of `G X`, and the bottom step is carried to a
zero object, hence to the bottom subobject.

Additivity of `G` is all that is used, so the construction is stated for additive functors;
in particular it applies to the right exact functors for which the source states the result.
The top route in the defining diagram uses a chosen inverse of the equivalence of Tag 03TB,
and its comparison with the projective route is therefore the inverse unit isomorphism of
that equivalence.

## References

* [Stacks Project, Tag 03TD](https://stacks.math.columbia.edu/tag/03TD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject Opposite

universe vA vB uA uB

namespace CategoryTheory.FilteredDerived

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]

/-- The image filtration of `G.obj X`: its `p`-th step is the image of `G(F^p X)` in
`G X`. -/
noncomputable def mapFilteredObject (G : A ⥤ B)
    (X : FilteredObject A ℤᵒᵖ) : FilteredObject B ℤᵒᵖ where
  X := G.obj X.X
  filtration := Filtration.ofAntitone
    (fun p => imageSubobject (G.map (X.filtration.ι.app (op p)))) (by
      intro p q hpq
      have e : G.map (X.filtration.ι.app (op q)) =
          G.map (X.filtration.step (opHomOfLE hpq)) ≫
            G.map (X.filtration.ι.app (op p)) := by
        rw [← G.map_comp, X.filtration.step_comp_ι_app (opHomOfLE hpq)]
      dsimp only
      rw [e]
      exact imageSubobject_comp_le _ _)

/-- The image filtration of a finite filtration is finite. -/
lemma mapFilteredObject_finite (G : A ⥤ B) [G.Additive]
    (X : FiniteFilteredObject A) : (mapFilteredObject G X.obj).filtration.IsFinite := by
  obtain ⟨p, hp⟩ := X.property.exists_isIso_ι
  obtain ⟨q, hq⟩ := X.property.exists_isZero_obj
  apply Filtration.IsFinite.of_exists
  · refine ⟨p, ?_⟩
    change IsIso ((imageSubobject (G.map (X.obj.filtration.ι.app (op p)))).arrow)
    rw [Subobject.isIso_iff_mk_eq_top]
    simpa only [Subobject.mk_arrow] using Subobject.imageSubobject_eq_top_of_epi
      (G.map (X.obj.filtration.ι.app (op p)))
  · refine ⟨q, ?_⟩
    change IsZero (imageSubobject (G.map (X.obj.filtration.ι.app (op q))) : B)
    rw [(G.map_isZero hq).eq_of_src (G.map (X.obj.filtration.ι.app (op q))) 0,
      imageSubobject_zero]
    exact (isZero_zero B).of_iso Subobject.botCoeIsoZero

/-- A morphism of filtered objects induces a morphism of the image filtrations. -/
noncomputable def mapFilteredObjectMap (G : A ⥤ B)
    {X Y : FilteredObject A ℤᵒᵖ} (f : X ⟶ Y) :
    mapFilteredObject G X ⟶ mapFilteredObject G Y :=
  FilteredObject.homMk (G.map f.hom)
    (fun i =>
      (imageSubobjectIso (G.map (X.filtration.ι.app i))).hom ≫
        image.map (Arrow.homMk' (f := G.map (X.filtration.ι.app i))
          (g := G.map (Y.filtration.ι.app i))
          (G.map (f.natTrans.app i)) (G.map f.hom) (by
            rw [← G.map_comp, ← G.map_comp, f.comm i])) ≫
        (imageSubobjectIso (G.map (Y.filtration.ι.app i))).inv)
    (by
      intro i
      cases i with
      | op p =>
        unfold mapFilteredObject
        change _ ≫ (imageSubobject (G.map (Y.filtration.ι.app (op p)))).arrow =
          (imageSubobject (G.map (X.filtration.ι.app (op p)))).arrow ≫ G.map f.hom
        simp only [Category.assoc, imageSubobject_arrow']
        rw [image.map_homMk'_ι, ← Category.assoc, imageSubobject_arrow])

/-- The functor `Fil^f(A) ⥤ Fil^f(B)` induced by an additive functor `G : A ⥤ B`. -/
noncomputable def mapFiniteFiltered (G : A ⥤ B) [G.Additive] :
    FiniteFilteredObject A ⥤ FiniteFilteredObject B where
  obj X := ⟨mapFilteredObject G X.obj, mapFilteredObject_finite G X⟩
  map f := ObjectProperty.homMk (mapFilteredObjectMap G f.hom)
  map_id _ := ObjectProperty.hom_ext _ (FilteredObject.hom_ext (G.map_id _))
  map_comp _ _ := ObjectProperty.hom_ext _ (FilteredObject.hom_ext (G.map_comp _ _))

/-- The functor induced on finite filtered objects by an additive functor is additive. -/
instance mapFiniteFiltered_additive (G : A ⥤ B) [G.Additive] :
    (mapFiniteFiltered G).Additive where
  map_add := ObjectProperty.hom_ext _ (FilteredObject.hom_ext G.map_add)

/-- The lower route in the defining diagram: apply `G` termwise to a bounded-above
complex of filtered projective objects, then pass to the bounded-above filtered
derived category. -/
@[implicit_reducible, stacks 03TD "filtered_left_derived_functor"]
noncomputable def filteredProjectiveMinusMapToDerivedMinus
    (G : A ⥤ B) [G.Additive] :
    (filteredProjectiveMinus A).FullSubcategory ⥤
      (CochainComplex.FilteredDerivedCategory.minus B).FullSubcategory := by
  let F : HomotopyCategory (FiniteFilteredObject A) (.up ℤ) ⥤
      HomotopyCategory (FiniteFilteredObject B) (.up ℤ) :=
    (mapFiniteFiltered G).mapHomotopyCategory (.up ℤ)
  let H : (filteredProjectiveMinus A).FullSubcategory ⥤
      CochainComplex.FilteredDerivedCategory B :=
    (filteredProjectiveMinus A).ι ⋙
      (CochainComplex.FilteredDerivedCategory.Kminus (𝒜 := A)).ι ⋙ F ⋙
      CochainComplex.FilteredDerivedCategory.Qh
  exact (CochainComplex.FilteredDerivedCategory.minus B).lift
    H (by
      rintro ⟨⟨X, hK⟩, hX⟩
      change ((filteredProjectiveMinusC A).strictMap
        (HomotopyCategory.quotient _ _)) X at hX
      obtain ⟨K, ⟨⟨n, hn⟩, _⟩, rfl⟩ :=
        (ObjectProperty.strictMap_iff _ _ _).1 hX
      have : CochainComplex.IsStrictlyLE
          (((mapFiniteFiltered G).mapHomologicalComplex (.up ℤ)).obj K) n := by
        rw [CochainComplex.isStrictlyLE_iff] at hn ⊢
        intro i hi
        exact (mapFiniteFiltered G).map_isZero (hn i hi)
      exact CochainComplex.FilteredDerivedCategory.minus_Qh_obj
        (((mapFiniteFiltered G).mapHomologicalComplex (.up ℤ)).obj K) n)

/-- The filtered left derived functor on bounded-above filtered derived categories. -/
@[implicit_reducible, stacks 03TD "filtered_left_derived_functor"]
noncomputable def filteredLeftDerivedFunctor
    (G : A ⥤ B) [G.Additive] [EnoughProjectives A] :
    (CochainComplex.FilteredDerivedCategory.minus A).FullSubcategory ⥤
      (CochainComplex.FilteredDerivedCategory.minus B).FullSubcategory :=
  have : (filteredProjectiveMinusToDerivedMinus A).IsEquivalence :=
    filteredProjectiveMinusToDerivedMinus_isEquivalence A
  (filteredProjectiveMinusToDerivedMinus A).inv ⋙
    filteredProjectiveMinusMapToDerivedMinus G

/-- The natural isomorphism making the projective-resolution diagram commute. -/
@[stacks 03TD "filtered_left_derived_functor"]
noncomputable def filteredLeftDerivedFunctorComparison
    (G : A ⥤ B) [G.Additive] [EnoughProjectives A] :
    filteredProjectiveMinusToDerivedMinus A ⋙ filteredLeftDerivedFunctor G ≅
      filteredProjectiveMinusMapToDerivedMinus G :=
  have : (filteredProjectiveMinusToDerivedMinus A).IsEquivalence :=
    filteredProjectiveMinusToDerivedMinus_isEquivalence A
  Functor.isoWhiskerRight
    (filteredProjectiveMinusToDerivedMinus A).asEquivalence.unitIso.symm
    (filteredProjectiveMinusMapToDerivedMinus G)

end CategoryTheory.FilteredDerived

end
