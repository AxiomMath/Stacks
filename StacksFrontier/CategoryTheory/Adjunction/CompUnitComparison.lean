module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Units of composite adjunctions, and lifting along units in an adjoint triple

Let `L_g ⊣ R_g` and `L_f ⊣ R_f` be composable adjunctions and let `L_k ⊣ R_k` be a third
adjunction whose left adjoint is identified with the composite, `e : L_g ⋙ L_f ≅ L_k`.  The
composite adjunction `L_g ⋙ L_f ⊣ R_f ⋙ R_g` and `L_k ⊣ R_k` are then two adjunctions with
isomorphic left adjoints, so the right adjoints are isomorphic by the conjugate of `e`, and the
two units agree through the resulting comparison
`(L_g ⋙ L_f) ⋙ (R_f ⋙ R_g) ≅ L_k ⋙ R_k`.

Let `L ⊣ G ⊣ P` be an adjoint triple. If the counit `L (G O) ⟶ O` is a monomorphism and `I` is
injective, then every morphism `O ⟶ P (G I)` factors through the unit `I ⟶ P (G I)`.

## Main definitions

* `CategoryTheory.Adjunction.compUnitComparisonIso`: the comparison
  `(L_g ⋙ L_f) ⋙ (R_f ⋙ R_g) ≅ L_k ⋙ R_k` attached to `e : L_g ⋙ L_f ≅ L_k`.

## Main results

* `CategoryTheory.Adjunction.unit_app_eq_comp_compUnitComparisonIso`: the unit of `L_k ⊣ R_k`
  is the unit of `L_g ⊣ R_g`, followed by `R_g` of the unit of `L_f ⊣ R_f`, followed by the
  comparison.
* `CategoryTheory.Adjunction.conjugateEquiv_id_comp_counit`: in an adjoint triple
  `L ⊣ G ⊣ P`, the counit `G ⋙ L ⟶ 𝟭` is conjugate to the unit `𝟭 ⟶ G ⋙ P`.
* `CategoryTheory.Adjunction.unit_comp_conjugateEquiv_comp`: a transformation of the left
  adjoints compatible with the counits is conjugate to one compatible with the units.
* `CategoryTheory.Adjunction.exists_comp_unit_app_eq_of_mono_counit`: lifting along the unit of
  the right half of an adjoint triple, at an injective object.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Adjunction

section Composite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {Lg : C ⥤ D} {Rg : D ⥤ C} {Lf : D ⥤ E} {Rf : E ⥤ D} {Lk : C ⥤ E} {Rk : E ⥤ C}
  (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adjk : Lk ⊣ Rk) (e : Lg ⋙ Lf ≅ Lk)

/-- **The comparison of the composite adjunction with an adjunction along an isomorphic left
adjoint.**  For `e : L_g ⋙ L_f ≅ L_k`, the isomorphism `(L_g ⋙ L_f) ⋙ (R_f ⋙ R_g) ≅ L_k ⋙ R_k`
given by `e` on the left and by its conjugate, the isomorphism of right adjoints
`R_f ⋙ R_g ≅ R_k`, on the right. -/
def compUnitComparisonIso : (Lg ⋙ Lf) ⋙ (Rf ⋙ Rg) ≅ Lk ⋙ Rk :=
  Functor.isoWhiskerRight e (Rf ⋙ Rg) ≪≫
    Functor.isoWhiskerLeft Lk (conjugateIsoEquiv (adjg.comp adjf) adjk e.symm)

/-- **The unit of an adjunction along a composite.**  If `L_k ≅ L_g ⋙ L_f`, then the unit
`X ⟶ R_k L_k X` is the unit `X ⟶ R_g L_g X` followed by `R_g` of the unit
`L_g X ⟶ R_f L_f L_g X`, read through `CategoryTheory.Adjunction.compUnitComparisonIso`. -/
theorem unit_app_eq_comp_compUnitComparisonIso (X : C) :
    adjk.unit.app X = adjg.unit.app X ≫ Rg.map (adjf.unit.app (Lg.obj X)) ≫
      (compUnitComparisonIso adjg adjf adjk e).hom.app X := by
  have h := unit_conjugateEquiv (adjg.comp adjf) adjk e.inv X
  have hn := (conjugateEquiv (adjg.comp adjf) adjk e.inv).naturality (e.hom.app X)
  simp only [comp_unit_app, Functor.comp_obj, Functor.comp_map, Category.assoc] at h hn
  simp only [compUnitComparisonIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, conjugateIsoEquiv_apply_hom, Iso.symm_hom, Functor.comp_map]
  rw [hn, reassoc_of% h, ← Functor.map_comp, e.inv_hom_id_app, Functor.map_id,
    Category.comp_id]

end Composite

section Triple

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {G : C ⥤ D} {P : D ⥤ C} {L : D ⥤ C}

/-- **The counit of the left half of an adjoint triple is conjugate to the unit of the right
half.**  For `L ⊣ G ⊣ P`, the conjugate of the counit `G ⋙ L ⟶ 𝟭`, between the identity
adjunction and the composite adjunction `G ⋙ L ⊣ G ⋙ P`, is the unit `𝟭 ⟶ G ⋙ P`. -/
theorem conjugateEquiv_id_comp_counit (adjR : G ⊣ P) (adjL : L ⊣ G) :
    conjugateEquiv Adjunction.id (adjR.comp adjL) adjL.counit = adjR.unit := by
  ext X
  simp [conjugateEquiv_apply_app, ← Functor.map_comp]

/-- **Conjugates of maps compatible with the counits are compatible with the units.**  Let
`L ⊣ G ⊣ P` and `L' ⊣ G' ⊣ P'` be adjoint triples on the same category `C`, and let
`α : G' ⋙ L' ⟶ G ⋙ L` be compatible with the two counits.  Then its conjugate
`G ⋙ P ⟶ G' ⋙ P'`, for the composite adjunctions, is compatible with the two units. -/
theorem unit_comp_conjugateEquiv_comp {D' : Type u₃} [Category.{v₃} D'] {G' : C ⥤ D'}
    {P' : D' ⥤ C} {L' : D' ⥤ C} (adjR : G ⊣ P) (adjL : L ⊣ G) (adjR' : G' ⊣ P')
    (adjL' : L' ⊣ G') (α : G' ⋙ L' ⟶ G ⋙ L) (h : α ≫ adjL.counit = adjL'.counit) :
    adjR.unit ≫ conjugateEquiv (adjR.comp adjL) (adjR'.comp adjL') α = adjR'.unit := by
  rw [← conjugateEquiv_id_comp_counit adjR adjL, ← conjugateEquiv_id_comp_counit adjR' adjL',
    conjugateEquiv_comp, h]

/-- **Lifting along the unit of the right half of an adjoint triple.**  Let `L ⊣ G ⊣ P` and let
`O` be an object whose counit `L (G O) ⟶ O` is a monomorphism.  For an injective object `I`,
every morphism `O ⟶ P (G I)` factors through the unit `I ⟶ P (G I)`. -/
theorem exists_comp_unit_app_eq_of_mono_counit (adjR : G ⊣ P) (adjL : L ⊣ G) {O : C}
    [Mono (adjL.counit.app O)] (I : C) [Injective I] (a : O ⟶ P.obj (G.obj I)) :
    ∃ b : O ⟶ I, b ≫ adjR.unit.app I = a := by
  refine ⟨Injective.factorThru ((adjL.homEquiv _ _).symm ((adjR.homEquiv _ _).symm a))
    (adjL.counit.app O), ?_⟩
  apply (adjR.homEquiv _ _).symm.injective
  apply (adjL.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm,
    (by simp [homEquiv_counit] : (adjR.homEquiv I (G.obj I)).symm (adjR.unit.app I) = 𝟙 _),
    Category.comp_id]
  conv_lhs => rw [homEquiv_counit, counit_naturality]
  exact Injective.comp_factorThru _ _

end Triple

end CategoryTheory.Adjunction

end
