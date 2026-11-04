module

public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor

/-!
# Naturality of the single-row identification of a total complex

Let `F : A ⥤ B ⥤ D` be a bifunctor, additive in each variable, and let `M` be an object of `B`.
Placing `M` in the degree zero and forming the total complex gives a functor of the first
complex, and `CochainComplex.KFlatBifunctor.totalSingleIso` identifies it with the termwise
complex `p ↦ F(K^p, M)`.  This file proves that identification natural in `K` and in `M`,
together with the naturality statements it rests on.

## Main definitions

* `CochainComplex.KFlatBifunctor.rowComplexMap`: the action of the termwise complex
  `p ↦ F(K^p, M)` on a morphism of `K`.
* `CochainComplex.KFlatBifunctor.rowComplexMapRight`: its action on a morphism of `M`.

## Main results

* `StacksDraft.TotalSingleRow.totalSingleRowUnit_naturality`: the identification
  `W⟦-q⟧ ≅ Tot(singleRow W q)` is natural in `W`.
* `CochainComplex.KFlatBifunctor.mapBifunctorSingleIso_naturality`: the double complex of a
  complex concentrated in one degree is concentrated in one row, naturally in the other
  complex.
* `CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality`:
  `Tot(F(K, M[0])) ≅ (p ↦ F(K^p, M))` is natural in `K`.
* `CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right`: the same identification is
  natural in `M`.

## Implementation notes

Each statement is the naturality of the corresponding construction in the variable the
construction was built in, and is proved from the naturality of the pieces rather than from a
formula for the induced map on a summand of the total complex.  For
`StacksDraft.TotalSingleRow.totalSingleRowUnit` that means `HomologicalComplex₂.ιTotal_map`
together with `HomologicalComplex.single_map_f_self`; for
`CochainComplex.KFlatBifunctor.mapBifunctorSingleIso` it is
`StacksDraft.TotalSingleRow.singleMapHomologicalComplex_naturality`, the naturality of placing
an object in a degree in the *functor*; and for
`CochainComplex.KFlatBifunctor.totalSingleIso` it is those two together with the functoriality
of `HomologicalComplex₂.total` and the naturality of
`CategoryTheory.shiftFunctorZero'`.

`CochainComplex.KFlatBifunctor.rowComplex` is written out rather than being
`((F.flip.obj M).mapHomologicalComplex _).obj K`, so its action on morphisms is supplied here
as `CochainComplex.KFlatBifunctor.rowComplexMap` instead of being inherited.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TotalSingleRow

variable {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]

/-- **The identification `W⟦-q⟧ ≅ Tot(singleRow W q)` is natural in `W`.**  On the single
possibly nonzero summand of each total degree both sides are the component of the morphism in
that degree, read through the identification of a complex concentrated in the degree `q` with
its value there, and the sign is the same on both. -/
lemma totalSingleRowUnit_naturality {W W' : CochainComplex A ℤ} (φ : W ⟶ W') (q : ℤ)
    [(singleRow W q).HasTotal (ComplexShape.up ℤ)]
    [(singleRow W' q).HasTotal (ComplexShape.up ℤ)] :
    (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-q)).map φ ≫ totalSingleRowUnit W' q =
      totalSingleRowUnit W q ≫
        HomologicalComplex₂.total.map
          (((HomologicalComplex.single A (ComplexShape.up ℤ) q).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  have hι := HomologicalComplex₂.ιTotal_map (singleRow W q) (singleRow W' q)
    (((HomologicalComplex.single A (ComplexShape.up ℤ) q).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) (ComplexShape.up ℤ) (n + -q) q n (by dsimp; omega)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctor_map_f' φ (-q) n]
  dsimp only [totalSingleRowUnit]
  rw [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc, hι]
  simp only [Functor.mapHomologicalComplex_map_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]

end StacksDraft.TotalSingleRow

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]

/-- **The action of the termwise complex `p ↦ F(K^p, M)` on a morphism of `K`**: in each degree
the image of its component under `F` in the first variable. -/
def rowComplexMap {K K' : CochainComplex A ℤ} (f : K ⟶ K') (M : B) :
    rowComplex F K M ⟶ rowComplex F K' M where
  f p := (F.map (f.f p)).app M
  comm' p p' _ := by
    dsimp [rowComplex]
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← F.map_comp, ← F.map_comp, f.comm]

/-- **The single-row identification of the double complex is natural in the first complex.**
In each first degree it is `HomologicalComplex.singleMapHomologicalComplex` for the functor
`F(K^p, -)`, and the square is the naturality of that construction in the functor. -/
lemma mapBifunctorSingleIso_naturality {K K' : CochainComplex A ℤ} (f : K ⟶ K') (M : B)
    (q : ℤ) :
    ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).app
          ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M) ≫
        (mapBifunctorSingleIso F K' M q).hom =
      (mapBifunctorSingleIso F K M q).hom ≫
        ((HomologicalComplex.single D (ComplexShape.up ℤ) q).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (rowComplexMap F f M) := by
  refine HomologicalComplex.hom_ext _ _ (fun p => ?_)
  exact (StacksDraft.TotalSingleRow.singleMapHomologicalComplex_naturality
    (F.map (f.f p)) q M).symm

/-- **The action of the termwise complex `p ↦ F(K^p, M)` on a morphism of `M`**: in each degree
the image of the morphism under `F(K^p, -)`. -/
def rowComplexMapRight (K : CochainComplex A ℤ) {M M' : B} (g : M ⟶ M') :
    rowComplex F K M ⟶ rowComplex F K M' where
  f p := (F.obj (K.X p)).map g
  comm' p p' _ := by
    dsimp [rowComplex]
    exact (F.map (K.d p p')).naturality g

/-- **The single-row identification of the double complex is natural in the object placed in
one degree.** In each first degree it is `HomologicalComplex.singleMapHomologicalComplex` for the
functor `F(K^p, -)`, which is a natural isomorphism. -/
lemma mapBifunctorSingleIso_naturality_right (K : CochainComplex A ℤ) {M M' : B} (g : M ⟶ M')
    (q : ℤ) :
    ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map
          ((HomologicalComplex.single B (ComplexShape.up ℤ) q).map g) ≫
        (mapBifunctorSingleIso F K M' q).hom =
      (mapBifunctorSingleIso F K M q).hom ≫
        ((HomologicalComplex.single D (ComplexShape.up ℤ) q).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (rowComplexMapRight F K g) := by
  refine HomologicalComplex.hom_ext _ _ (fun p => ?_)
  exact (HomologicalComplex.singleMapHomologicalComplex (F.obj (K.X p))
    (ComplexShape.up ℤ) q).hom.naturality g

variable [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- Naturality of `totalSingleIso` for a morphism of double complexes whose composite with the
single-row identification is the image of a morphism `ψ` of row complexes. -/
private theorem mapBifunctorMap_comp_totalSingleIso_hom {K K' : CochainComplex A ℤ} {M M' : B}
    (f : K ⟶ K') (g : (HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M ⟶
      (HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M')
    (ψ : rowComplex F K M ⟶ rowComplex F K' M')
    (h : (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).app
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) ≫
        ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K').map
          g) ≫ (mapBifunctorSingleIso F K' M' 0).hom =
      (mapBifunctorSingleIso F K M 0).hom ≫
        ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ψ) :
    HomologicalComplex.mapBifunctorMap f g F (ComplexShape.up ℤ) ≫
        (totalSingleIso F K' M').hom =
      (totalSingleIso F K M).hom ≫ ψ := by
  let _hT : (StacksDraft.TotalSingleRow.singleRow (rowComplex F K M) 0).HasTotal
      (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K M 0) _
  let _hT' : (StacksDraft.TotalSingleRow.singleRow (rowComplex F K' M') 0).HasTotal
      (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K' M' 0) _
  have : IsIso (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) 0) :=
    StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit _ _
  have : IsIso (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K' M') 0) :=
    StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit _ _
  have hK : (totalSingleIso F K M).hom =
      HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M 0).hom (ComplexShape.up ℤ) ≫
        CategoryTheory.inv
            (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) 0) ≫
          (CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).hom.app
            (rowComplex F K M) := rfl
  have hK' : (totalSingleIso F K' M').hom =
      HomologicalComplex₂.total.map (mapBifunctorSingleIso F K' M' 0).hom (ComplexShape.up ℤ) ≫
        CategoryTheory.inv
            (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K' M') 0) ≫
          (CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).hom.app
            (rowComplex F K' M') := rfl
  have h1 : HomologicalComplex₂.total.map
          (((HomologicalComplex.single D (ComplexShape.up ℤ) 0).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ) (ComplexShape.up ℤ) ≫
        CategoryTheory.inv
          (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K' M') 0) =
      CategoryTheory.inv
          (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) 0) ≫
        (CategoryTheory.shiftFunctor (CochainComplex D ℤ) (-0 : ℤ)).map ψ := by
    rw [IsIso.comp_inv_eq, Category.assoc,
      StacksDraft.TotalSingleRow.totalSingleRowUnit_naturality ψ 0, IsIso.inv_hom_id_assoc]
  have h2 := (CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ)
    neg_zero).hom.naturality ψ
  rw [show HomologicalComplex.mapBifunctorMap f g F (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map _ (ComplexShape.up ℤ) from rfl, hK, hK', ← Category.assoc,
    ← HomologicalComplex₂.total.map_comp, h, HomologicalComplex₂.total.map_comp, Category.assoc,
    reassoc_of% h1, h2, Category.assoc, Category.assoc]
  exact rfl

/-- **The termwise identification of the total complex is natural in the complex.**  The three
pieces of `CochainComplex.KFlatBifunctor.totalSingleIso` are natural: the single-row
identification by `CochainComplex.KFlatBifunctor.mapBifunctorSingleIso_naturality`, the
comparison with the shift by `StacksDraft.TotalSingleRow.totalSingleRowUnit_naturality`, and
the trivialization of the shift by zero because it is a natural isomorphism. -/
lemma totalSingleIso_hom_naturality {K K' : CochainComplex A ℤ} (f : K ⟶ K') (M : B) :
    HomologicalComplex.mapBifunctorMap f
          (𝟙 ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M)) F
          (ComplexShape.up ℤ) ≫
        (totalSingleIso F K' M).hom =
      (totalSingleIso F K M).hom ≫ rowComplexMap F f M :=
  mapBifunctorMap_comp_totalSingleIso_hom F f _ _ (by
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact mapBifunctorSingleIso_naturality F f M 0)

/-- **The termwise identification of the total complex is natural in the object placed in degree
zero.** The proof is that of `CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality` with the
roles of the two variables exchanged: the single-row identification is natural by
`CochainComplex.KFlatBifunctor.mapBifunctorSingleIso_naturality_right`, and the other two pieces
are natural in the row complex. -/
lemma totalSingleIso_hom_naturality_right (K : CochainComplex A ℤ) {M M' : B} (g : M ⟶ M') :
    HomologicalComplex.mapBifunctorMap (𝟙 K)
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map g) F
          (ComplexShape.up ℤ) ≫
        (totalSingleIso F K M').hom =
      (totalSingleIso F K M).hom ≫ rowComplexMapRight F K g :=
  mapBifunctorMap_comp_totalSingleIso_hom F (𝟙 K) _ _ (by
    rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
    exact mapBifunctorSingleIso_naturality_right F K g 0)


end CochainComplex.KFlatBifunctor


end
