module

public import StacksFrontier.CategoryTheory.Triangulated.LocallySmallTransport

/-!
# Roofs between images of compact objects, for locally small triangulated categories

`CategoryTheory.Pretriangulated.exists_roof` ([Stacks, Tag 08EH] in Neeman's form) is stated for
a triangulated category whose morphisms live in the universe indexing its coproducts. This file
transports it, along the triangulated equivalence with a model with small morphisms of
`CategoryTheory.Pretriangulated.exists_triangulatedEquivalence_of_locallySmall`, to a category
which is only `LocallySmall.{w}` and has `Type w`-indexed coproducts, such as a derived category
of the standard model.

## Main results

* `CategoryTheory.Pretriangulated.exists_roof_of_locallySmall`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated ObjectProperty

namespace CategoryTheory.Pretriangulated

universe w v v' u u'

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
  [LocallySmall.{w} T] [HasCoproducts.{w} T]
  {T' : Type u'} [Category.{v'} T'] [Preadditive T'] [HasZeroObject T'] [HasShift T' ℤ]
  [∀ n : ℤ, (shiftFunctor T' n).Additive] [Pretriangulated T'] [IsTriangulated T']
  [LocallySmall.{w} T'] [HasCoproducts.{w} T']

/-- **Roofs between images of compact objects, for locally small categories** ([Stacks, Tag
08EH] in Neeman's form). Let `L ⊣ G` with `L` exact, `G` fully faithful, and let the kernel of
`L` be detected by compact objects `K i` killed by `L`. Every morphism `g : L c₁ ⟶ L c₂` with
`c₁` compact is `L g' ∘ (L s)⁻¹` for a compact `c`, `s : c ⟶ c₁` with `L s` invertible and
`g' : c ⟶ c₂`. -/
theorem exists_roof_of_locallySmall
    {L : T ⥤ T'} {G : T' ⥤ T} (adj : L ⊣ G) [L.CommShift ℤ] [L.IsTriangulated]
    [IsIso adj.counit] {ι : Type w} (K : ι → T)
    (hK : ∀ i, IsCompactObject.{w} (K i)) (hLK : ∀ i, IsZero (L.obj (K i)))
    (hloc : ∀ E : T, (∀ i (n : ℤ) (g : (K i)⟦n⟧ ⟶ E), g = 0) → IsIso (adj.unit.app E))
    {c₁ c₂ : T} (hc₁ : IsCompactObject.{w} c₁) (g : L.obj c₁ ⟶ L.obj c₂) :
    ∃ (c : T) (s : c ⟶ c₁) (g' : c ⟶ c₂), IsCompactObject.{w} c ∧ IsIso (L.map s) ∧
      L.map g' = L.map s ≫ g := by
  obtain ⟨D, _, _, _, _, _, _, e, _, _, _, _, _, _, hD⟩ :=
    exists_triangulatedEquivalence_of_locallySmall.{w} T
  have := hD inferInstance
  obtain ⟨D', _, _, _, _, _, _, e', _, _, _, _, _, _, hD'⟩ :=
    exists_triangulatedEquivalence_of_locallySmall.{w} T'
  have := hD' inferInstance
  have : HasCoproducts.{w} D := fun _ => Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  have : HasCoproducts.{w} D' := fun _ => Adjunction.hasColimitsOfShape_of_equivalence e'.inverse
  let hGff := adj.fullyFaithfulROfIsIsoCounit
  have : G.Full := hGff.full
  have : G.Faithful := hGff.faithful
  let adjs : e.inverse ⋙ L ⋙ e'.functor ⊣ e'.inverse ⋙ G ⋙ e.functor :=
    e.symm.toAdjunction.comp (adj.comp e'.toAdjunction)
  let Ks : ι → D := fun i => e.functor.obj (K i)
  have hKs : ∀ i, IsCompactObject.{w} (Ks i) := fun i =>
    (isCompactObject_iff_isCompactObject_obj e.functor (K i)).1 (hK i)
  have hLKs : ∀ i, IsZero ((e.inverse ⋙ L ⋙ e'.functor).obj (Ks i)) := fun i =>
    Functor.map_isZero e'.functor ((hLK i).of_iso (L.mapIso (e.unitIso.app (K i)).symm))
  have hlocs : ∀ E : D, (∀ i (n : ℤ) (g : (Ks i)⟦n⟧ ⟶ E), g = 0) →
      IsIso (adjs.unit.app E) := by
    intro E hE
    have hE0 := rightOrthogonal_shiftClosure_ofObj_inverse e K E
      ((rightOrthogonal_shiftClosure_ofObj_iff _ _).2 hE)
    rw [rightOrthogonal_shiftClosure_ofObj_iff] at hE0
    obtain ⟨Y, ⟨eY⟩⟩ := (adj.isIso_unit_app_iff_mem_essImage).1 (hloc _ hE0)
    exact (adjs.isIso_unit_app_iff_mem_essImage).2 ⟨e'.functor.obj Y,
      ⟨e.functor.mapIso (G.mapIso (e'.unitIso.app Y).symm ≪≫ eY) ≪≫ e.counitIso.app E⟩⟩
  have : IsIso adjs.counit := inferInstance
  let L' := e.inverse ⋙ L ⋙ e'.functor
  have hc₁s : IsCompactObject.{w} (e.functor.obj c₁) :=
    (isCompactObject_iff_isCompactObject_obj e.functor c₁).1 hc₁
  let a₁ : L'.obj (e.functor.obj c₁) ≅ e'.functor.obj (L.obj c₁) :=
    e'.functor.mapIso (L.mapIso (e.unitIso.app c₁).symm)
  let a₂ : L'.obj (e.functor.obj c₂) ≅ e'.functor.obj (L.obj c₂) :=
    e'.functor.mapIso (L.mapIso (e.unitIso.app c₂).symm)
  obtain ⟨cs, ss, gs, hcs, hLss, hgs⟩ := exists_roof adjs Ks hKs hLKs hlocs
    (c₁ := e.functor.obj c₁) (c₂ := e.functor.obj c₂) (a₁.hom ≫ e'.functor.map g ≫ a₂.inv)
  refine ⟨e.inverse.obj cs, e.inverse.map ss ≫ e.unitIso.inv.app c₁,
    e.inverse.map gs ≫ e.unitIso.inv.app c₂,
    (isCompactObject_iff_isCompactObject_obj e.inverse cs).1 hcs, ?_, ?_⟩
  · have : IsIso (e'.functor.map (L.map (e.inverse.map ss))) := hLss
    have : IsIso (L.map (e.inverse.map ss)) := isIso_of_reflects_iso _ e'.functor
    rw [Functor.map_comp]
    infer_instance
  · apply e'.functor.map_injective
    have hgs' : e'.functor.map (L.map (e.inverse.map gs)) =
        e'.functor.map (L.map (e.inverse.map ss)) ≫ a₁.hom ≫ e'.functor.map g ≫ a₂.inv := hgs
    have h2 : e'.functor.map (L.map (e.inverse.map gs ≫ e.unitIso.inv.app c₂)) =
        e'.functor.map (L.map (e.inverse.map gs)) ≫ a₂.hom := by
      simp [a₂]
    have h1 : e'.functor.map (L.map (e.inverse.map ss ≫ e.unitIso.inv.app c₁)) =
        e'.functor.map (L.map (e.inverse.map ss)) ≫ a₁.hom := by
      simp [a₁]
    rw [h2, hgs', Functor.map_comp, h1]
    simp

end CategoryTheory.Pretriangulated

end
