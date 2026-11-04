module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive

/-!
# An additive functor commutes with extending a complex along an embedding

For a functor `F : C ⥤ D` preserving zero morphisms and zero objects, a complex `K` of `C` with
shape `c`, and an embedding of complex shapes `e : c ⥪ c'`, applying `F` degreewise to the
extension `K.extend e` is the extension of `F` applied degreewise to `K`:

`(F.mapHomologicalComplex c').obj (K.extend e) ≅ ((F.mapHomologicalComplex c).obj K).extend e`,

naturally in `K` (`mapExtendIso`, `mapExtendIso_hom_naturality`).

## References

* [Stacks Project, Tag 0FCU](https://stacks.math.columbia.edu/tag/0FCU), extension by zero of
  complexes
-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  (e : c.Embedding c')

namespace MapExtend

/-- The comparison of the terms of the two extensions at the index `o : Option ι`: the identity
when `o` is `some i`, and the isomorphism of zero objects when `o` is `none`. -/
noncomputable def isoX (K : HomologicalComplex C c) :
    ∀ (o : Option ι), F.obj (extend.X K o) ≅ extend.X ((F.mapHomologicalComplex c).obj K) o
  | some _ => Iso.refl _
  | none => IsZero.iso (F.map_isZero (extend.isZero_X K rfl)) (extend.isZero_X _ rfl)

/-- The comparisons `isoX` commute with the differentials of the two extensions. -/
lemma isoX_hom_d (K : HomologicalComplex C c) (o o' : Option ι) :
    (isoX F K o).hom ≫ extend.d ((F.mapHomologicalComplex c).obj K) o o' =
      F.map (extend.d K o o') ≫ (isoX F K o').hom :=
  match o, o' with
  | none, _ => by
      simp only [extend.d_none_eq_zero, comp_zero, Functor.map_zero, zero_comp]
  | some _, some _ => (Category.id_comp _).trans (Category.comp_id _).symm
  | some _, none => by
      simp only [extend.d_none_eq_zero', comp_zero, Functor.map_zero, zero_comp]

/-- The comparisons `isoX` commute with the maps `extend.mapX` induced by a morphism of
complexes. -/
lemma isoX_hom_mapX {K L : HomologicalComplex C c} (φ : K ⟶ L) (o : Option ι) :
    (isoX F K o).hom ≫ extend.mapX ((F.mapHomologicalComplex c).map φ) o =
      F.map (extend.mapX φ o) ≫ (isoX F L o).hom :=
  match o with
  | some _ => (Category.id_comp _).trans (Category.comp_id _).symm
  | none => by
      simp only [extend.mapX_none _ rfl, comp_zero, Functor.map_zero, zero_comp]

end MapExtend

/-- **Applying `F` degreewise commutes with extending along `e`.** -/
noncomputable def mapExtendIso (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun i' => MapExtend.isoX F K (e.r i'))
    (fun i' j' _ => MapExtend.isoX_hom_d F K (e.r i') (e.r j'))

/-- The comparison `mapExtendIso` is natural in the complex. -/
@[reassoc]
lemma mapExtendIso_hom_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (F.mapHomologicalComplex c').map (extendMap φ e) ≫ (mapExtendIso F e L).hom =
      (mapExtendIso F e K).hom ≫ extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i'
  exact (MapExtend.isoX_hom_mapX F φ (e.r i')).symm

end HomologicalComplex
