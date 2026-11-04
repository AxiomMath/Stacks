module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The connecting morphism of a shifted short exact sequence

Let `S : 0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0` be a short exact sequence of cochain complexes in an abelian
category and `n : ℤ`. Its translate `S⟦n⟧ : 0 ⟶ S₁⟦n⟧ ⟶ S₂⟦n⟧ ⟶ S₃⟦n⟧ ⟶ 0` is again short exact,
and the connecting morphism of its distinguished triangle in the derived category is the
translate of the connecting morphism of `S`, **up to the sign `(-1)^n`**:

`δ_{S⟦n⟧} = (-1)^n · δ_S⟦n⟧`,

read through the commutation of the localization functor with the shifts. The sign is the one by
which the translation of triangles multiplies the three morphisms of a triangle
(`CategoryTheory.Pretriangulated.Triangle.shiftFunctor`): the translate of `S` has the unsigned
morphisms `S.f⟦n⟧`, `S.g⟦n⟧`, so its third morphism differs from the one of the translated
triangle by `(-1)^n`.

## Main results

* `DerivedCategory.triangleOfSESδ_shift`: the formula above.
* `DerivedCategory.map_triangleOfSESδ_shift`: the same after a functor commuting with the shifts.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated Preadditive CochainComplex.HomComplex

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex C ℤ)}

omit [HasDerivedCategory C] in
/-- The projection of the mapping cone of the translate of `S.f` onto the translate of `S.X₃` is
the translate of the projection of the mapping cone of `S.f`, through the identification of the
mapping cone of a translate with the translate of the mapping cone. -/
lemma shiftIso_inv_descShortComplex_shift (n : ℤ) :
    (CochainComplex.mappingCone.shiftIso S.f n).inv ≫
        (CochainComplex.mappingCone.descShortComplex S)⟦n⟧' =
      CochainComplex.mappingCone.descShortComplex
          (S.map (shiftFunctor (CochainComplex C ℤ) n)) := by
  ext p
  dsimp
  rw [CochainComplex.mappingCone.ext_from_iff _ (p + 1) _ rfl]
  simp [CochainComplex.mappingCone.shiftIso, CochainComplex.mappingCone.descShortComplex,
    Cochain.shift_v']

omit [HasDerivedCategory C] in
/-- The third morphism of the mapping cone triangle of a translate. -/
lemma shiftIso_hom_triangle_shift_mor₃ (n : ℤ) :
    (CochainComplex.mappingCone.shiftIso S.f n).hom ≫
        (CochainComplex.mappingCone.triangle ((shiftFunctor (CochainComplex C ℤ) n).map S.f)).mor₃ =
      n.negOnePow • ((CochainComplex.mappingCone.triangle S.f).mor₃⟦n⟧' ≫
          (shiftFunctorComm (CochainComplex C ℤ) 1 n).hom.app S.X₁) := by
  have h₃ := (CochainComplex.mappingCone.shiftTriangleIso S.f n).hom.comm₃
  change ((Triangle.shiftFunctor _ n).obj (CochainComplex.mappingCone.triangle S.f)).mor₃ ≫
      (𝟙 _)⟦(1 : ℤ)⟧' = (CochainComplex.mappingCone.shiftIso S.f n).hom ≫ _ at h₃
  rw [CategoryTheory.Functor.map_id, comp_id] at h₃
  exact h₃.symm

/-- `Q` of a translated morphism `t⟦n⟧ : K⟦n⟧ ⟶ X⟦1⟧⟦n⟧`, followed by the commutation of the two
shifts and of `Q` with the shift by `1`, is the translate of `Q t`. -/
lemma map_shift_shiftFunctorComm {K X : CochainComplex C ℤ} (t : K ⟶ X⟦(1 : ℤ)⟧) (n : ℤ) :
    Q.map (t⟦n⟧' ≫ (shiftFunctorComm (CochainComplex C ℤ) 1 n).hom.app X) ≫
        (Q.commShiftIso (1 : ℤ)).hom.app (X⟦n⟧) =
      (Q.commShiftIso n).hom.app K ≫ (Q.map t ≫ (Q.commShiftIso (1 : ℤ)).hom.app X)⟦n⟧' ≫
        (shiftFunctorComm (DerivedCategory C) 1 n).hom.app (Q.obj X) ≫
          ((Q.commShiftIso n).inv.app X)⟦(1 : ℤ)⟧' := by
  rw [Functor.map_comp, Functor.map_shiftFunctorComm_hom_app, Functor.map_comp]
  simp [Functor.commShiftIso_hom_naturality_assoc]

/-- The formal part of `triangleOfSESδ_shift`, with every object a variable: a morphism `δ'`
determined by `Q d' ≫ δ' = Q t' ≫ (commutation)` for an invertible `Q d'` is the signed translate
of a morphism `δ` determined in the same way by `d` and `t`, as soon as `d'` and `t'` are the
translates of `d` and `t` up to an isomorphism `e` and the sign `ε`. -/
lemma eq_units_smul_shift_of_comp {K₁ K₃ M M' : CochainComplex C ℤ} (n : ℤ) (ε : ℤˣ)
    (e : M' ≅ M⟦n⟧) (d : M ⟶ K₃) (d' : M' ⟶ K₃⟦n⟧) (t : M ⟶ K₁⟦(1 : ℤ)⟧)
    (t' : M' ⟶ K₁⟦n⟧⟦(1 : ℤ)⟧) [IsIso (Q.map d')] (hd : e.hom ≫ d⟦n⟧' = d')
    (ht : t' = e.hom ≫ (ε • (t⟦n⟧' ≫ (shiftFunctorComm (CochainComplex C ℤ) 1 n).hom.app K₁)))
    (δ : Q.obj K₃ ⟶ (Q.obj K₁)⟦(1 : ℤ)⟧) (δ' : Q.obj (K₃⟦n⟧) ⟶ (Q.obj (K₁⟦n⟧))⟦(1 : ℤ)⟧)
    (hδ : Q.map d ≫ δ = Q.map t ≫ (Q.commShiftIso (1 : ℤ)).hom.app K₁)
    (hδ' : Q.map d' ≫ δ' = Q.map t' ≫ (Q.commShiftIso (1 : ℤ)).hom.app (K₁⟦n⟧)) :
    δ' = ε • ((Q.commShiftIso n).hom.app K₃ ≫ δ⟦n⟧' ≫
        (shiftFunctorComm (DerivedCategory C) 1 n).hom.app (Q.obj K₁) ≫
          ((Q.commShiftIso n).inv.app K₁)⟦(1 : ℤ)⟧') := by
  rw [← cancel_epi (Q.map d'), hδ', ht, ← hd, Functor.map_comp, Functor.map_comp, assoc,
    Functor.map_units_smul, Linear.units_smul_comp, map_shift_shiftFunctorComm, ← hδ]
  simp only [Linear.comp_units_smul, Functor.map_comp, assoc,
    Functor.commShiftIso_hom_naturality_assoc]

/-- **The connecting morphism of a translated short exact sequence**: for `S` short exact and
`n : ℤ`, the connecting morphism of `S⟦n⟧` is `(-1)^n` times the translate of that of `S`, read
through the commutation isomorphisms of `Q` with the shifts and the commutation of the shifts by
`1` and by `n`. -/
theorem triangleOfSESδ_shift (hS : S.ShortExact) (n : ℤ) :
    triangleOfSESδ (hS.map_of_exact (shiftFunctor (CochainComplex C ℤ) n)) =
      n.negOnePow • ((Q.commShiftIso n).hom.app S.X₃ ≫ (triangleOfSESδ hS)⟦n⟧' ≫
        (shiftFunctorComm (DerivedCategory C) 1 n).hom.app (Q.obj S.X₁) ≫
          ((Q.commShiftIso n).inv.app S.X₁)⟦(1 : ℤ)⟧') := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex
    (hS.map_of_exact (shiftFunctor (CochainComplex C ℤ) n))
  exact eq_units_smul_shift_of_comp n n.negOnePow (CochainComplex.mappingCone.shiftIso S.f n).symm
    (CochainComplex.mappingCone.descShortComplex S)
    (CochainComplex.mappingCone.descShortComplex (S.map (shiftFunctor (CochainComplex C ℤ) n)))
    (CochainComplex.mappingCone.triangle S.f).mor₃
    (CochainComplex.mappingCone.triangle ((shiftFunctor (CochainComplex C ℤ) n).map S.f)).mor₃
    (shiftIso_inv_descShortComplex_shift n)
    ((Iso.eq_inv_comp _).2 (shiftIso_hom_triangle_shift_mor₃ n)) _ _
    (descShortComplex_triangleOfSESδ hS)
    (descShortComplex_triangleOfSESδ (hS.map_of_exact (shiftFunctor (CochainComplex C ℤ) n)))

/-- **The connecting morphism of a translated short exact sequence, after a functor commuting
with the shifts.** For `G : D(𝒞) ⥤ 𝒯` commuting with the shifts and `H = Q ⋙ G`, the connecting
morphism of `S⟦n⟧`, read through `G`, is `(-1)^n` times the translate of that of `S`, read through
the commutation of `H` with the shift by `n`. -/
theorem map_triangleOfSESδ_shift {T : Type*} [Category* T] [Preadditive T] [HasShift T ℤ]
    [∀ a : ℤ, (shiftFunctor T a).Additive] (G : DerivedCategory C ⥤ T) [G.CommShift ℤ]
    [G.Additive] (hS : S.ShortExact) (n : ℤ) :
    G.map (triangleOfSESδ (hS.map_of_exact (shiftFunctor (CochainComplex C ℤ) n))) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (Q.obj (S.X₁⟦n⟧)) =
      n.negOnePow • (((Q ⋙ G).commShiftIso n).hom.app S.X₃ ≫
        (G.map (triangleOfSESδ hS) ≫ (G.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁))⟦n⟧' ≫
          (shiftFunctorComm T 1 n).hom.app (G.obj (Q.obj S.X₁)) ≫
            (((Q ⋙ G).commShiftIso n).inv.app S.X₁)⟦(1 : ℤ)⟧') := by
  rw [triangleOfSESδ_shift hS n, Functor.map_units_smul, Linear.units_smul_comp]
  congr 1
  have h₁ := (G.commShiftIso (1 : ℤ)).hom.naturality ((Q.commShiftIso n).inv.app S.X₁)
  have h₂ := (G.commShiftIso n).hom.naturality (triangleOfSESδ hS)
  dsimp at h₁ h₂
  simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    Functor.map_comp, assoc, Functor.map_shiftFunctorComm_hom_app, h₁, Iso.inv_hom_id_app_assoc,
    reassoc_of% h₂]

end DerivedCategory
