module

public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensorDegrees
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# The transport of a total complex at two single complexes

Let `P : A ⥤ A'` be an additive functor carrying a bifunctor `F` on `A` to a bifunctor `F'` on
`A'` by a natural isomorphism `ε : P(F(a, b)) ≅ F'(P a, P b)`, let `ν : P M ≅ M'`, and let
`λ : F(M, M) ≅ M` and `λ' : F'(M', M') ≅ M'`. If `ε` at `(M, M)` followed by `F'(ν, ν)` and `λ'` is
`P(λ)` followed by `ν`, then the comparison of total complexes
`P(Tot(F(M[-a], M[-b]))) ≅ Tot(F'(P(M[-a]), P(M[-b])))` of
`CategoryTheory.Functor.mapBifunctorTotalIso` is compatible with the identifications of both
total complexes with `M[-a-b]` and `M'[-a-b]`.

## Main results

* `CategoryTheory.Functor.total_single_single_comp`: the compatibility above, for any comparison
  of total complexes which is `ε` on the summand `(a, b)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A A' : Type*} [Category A] [Category A'] [Preadditive A] [Preadditive A']
  [HasZeroObject A] [HasZeroObject A']
  (F : A ⥤ A ⥤ A) (F' : A' ⥤ A' ⥤ A') (P : A ⥤ A')
  [F.Additive] [∀ X, (F.obj X).Additive] [F'.Additive] [∀ X, (F'.obj X).Additive] [P.Additive]
  (ε : ∀ a b : A, P.obj ((F.obj a).obj b) ≅ (F'.obj (P.obj a)).obj (P.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : A),
    P.map ((F.map f).app b) ≫ (ε a' b).hom = (ε a b).hom ≫ (F'.map (P.map f)).app (P.obj b))
  (hε₂ : ∀ (a : A) {b b' : A} (g : b ⟶ b'),
    P.map ((F.obj a).map g) ≫ (ε a b').hom = (ε a b).hom ≫ (F'.obj (P.obj a)).map (P.map g))
  {M : A} {M' : A'} (ν : P.obj M ≅ M') (lam : (F.obj M).obj M ≅ M)
  (lam' : (F'.obj M').obj M' ≅ M')

/-- Two morphisms of a bifunctor, each a map in the first variable followed by a map in the
second, compose to the map of the composites. -/
@[reassoc]
theorem map_app_comp_map_comp_map_app {C D E : Type*} [Category C] [Category D] [Category E]
    (G : C ⥤ D ⥤ E) {X X' X'' : C} {Y Y' Y'' : D} (g : X ⟶ X') (g' : X' ⟶ X'') (h : Y ⟶ Y')
    (h' : Y' ⟶ Y'') :
    (G.map g).app Y ≫ (G.obj X').map h ≫ (G.map g').app Y' ≫ (G.obj X'').map h' =
      (G.map (g ≫ g')).app Y ≫ (G.obj X'').map (h ≫ h') := by
  rw [(G.map g').naturality_assoc h]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]

/-- The image under `P` of `M` placed in degree `p` is `M'` placed in degree `p`. -/
def singleMapIso (p : ℤ) :
    (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single A (ComplexShape.up ℤ) p).obj M) ≅
      (HomologicalComplex.single A' (ComplexShape.up ℤ) p).obj M' :=
  (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) p).app M ≪≫
    (HomologicalComplex.single A' (ComplexShape.up ℤ) p).mapIso ν

/-- The component of `singleMapIso` in its degree. -/
theorem singleMapIso_hom_f_self (p : ℤ) :
    (singleMapIso P ν p).hom.f p =
      P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p M).hom ≫ ν.hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p M').inv := by
  simp [singleMapIso, HomologicalComplex.single_map_f_self]

/-- The identification of the total complex of `F` at `M[-a]` and `M[-b]` with `M[-a-b]`. -/
def mapBifunctorSingleSingleUnitIso (a b : ℤ)
    [HomologicalComplex.HasMapBifunctor ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M)
      ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M) F (ComplexShape.up ℤ)] :
    HomologicalComplex.mapBifunctor ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M)
        ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M) F (ComplexShape.up ℤ) ≅
      (HomologicalComplex.single A (ComplexShape.up ℤ) (a + b)).obj M :=
  HomologicalComplex.mapBifunctorSingleSingleIso F M M a b ≪≫
    (HomologicalComplex.single A (ComplexShape.up ℤ) (a + b)).mapIso lam

/-- The identification on the summand `(a, b)`. -/
@[reassoc]
theorem ι_mapBifunctorSingleSingleUnitIso_hom_f (a b : ℤ)
    [HomologicalComplex.HasMapBifunctor ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M)
      ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M) F (ComplexShape.up ℤ)] :
    HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M)
        ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M) F (ComplexShape.up ℤ) a b
        (a + b) rfl ≫ (mapBifunctorSingleSingleUnitIso F lam a b).hom.f (a + b) =
      (F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).hom).app _ ≫
        (F.obj M).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b M).hom ≫
        lam.hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (a + b) M).inv := by
  simp [mapBifunctorSingleSingleUnitIso,
    HomologicalComplex.ι_mapBifunctorSingleSingleIso_hom_f_assoc,
    HomologicalComplex.single_map_f_self]

include hε₁ hε₂ in
/-- **A comparison of total complexes which is `ε` on the summand `(a, b)` is compatible with the
identifications with a single complex**, as soon as `ε` at `(M, M)` is compatible with `λ`, `λ'`
and `ν`. This applies to `CategoryTheory.Functor.mapBifunctorTotalIso`, by
`CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom`. -/
theorem total_single_single_comp
    (hU : (ε M M).hom ≫ (F'.map ν.hom).app _ ≫ (F'.obj M').map ν.hom ≫ lam'.hom =
      P.map lam.hom ≫ ν.hom)
    (a b : ℤ)
    {inst₁ : HomologicalComplex.HasMapBifunctor
      ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M)
      ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M) F (ComplexShape.up ℤ)}
    {inst₂ : HomologicalComplex.HasMapBifunctor
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M))
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M)) F' (ComplexShape.up ℤ)}
    {inst₃ : HomologicalComplex.HasMapBifunctor
      ((HomologicalComplex.single A' (ComplexShape.up ℤ) a).obj M')
      ((HomologicalComplex.single A' (ComplexShape.up ℤ) b).obj M') F' (ComplexShape.up ℤ)}
    (T : (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor
          ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M)
          ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M) F (ComplexShape.up ℤ)) ⟶
      HomologicalComplex.mapBifunctor
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M))
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M)) F' (ComplexShape.up ℤ))
    (hT : P.map (HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M)
          ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M) F (ComplexShape.up ℤ) a b
          (a + b) rfl) ≫ T.f (a + b) =
      (ε _ _).hom ≫ HomologicalComplex.ιMapBifunctor
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M))
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M)) F' (ComplexShape.up ℤ) a b
        (a + b) rfl) :
    T ≫ HomologicalComplex.mapBifunctorMap (singleMapIso P ν a).hom (singleMapIso P ν b).hom F'
        (ComplexShape.up ℤ) ≫
      (mapBifunctorSingleSingleUnitIso F' lam' a b).hom =
    (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (mapBifunctorSingleSingleUnitIso F lam a b).hom ≫ (singleMapIso P ν (a + b)).hom := by
  apply HomologicalComplex.to_single_hom_ext
  have := HomologicalComplex.isIso_ιMapBifunctor_single_single F M M a b
  rw [← cancel_epi (P.map (HomologicalComplex.ιMapBifunctor
    ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M)
    ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj M) F (ComplexShape.up ℤ) a b
    (a + b) rfl))]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [reassoc_of% hT, HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_mapBifunctorSingleSingleUnitIso_hom_f, ← P.map_comp_assoc,
    ι_mapBifunctorSingleSingleUnitIso_hom_f, singleMapIso_hom_f_self, singleMapIso_hom_f_self,
    singleMapIso_hom_f_self]
  have h₁ := map_app_comp_map_comp_map_app F'
    (P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).hom ≫ ν.hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M').inv)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M').hom
    (P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b M).hom ≫ ν.hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b M').inv)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b M').hom
  have h₁' := map_app_comp_map_comp_map_app F'
    (P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).hom) ν.hom
    (P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b M).hom) ν.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h₁
  rw [← h₁'] at h₁
  have h₂ : P.map ((F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).hom).app _) ≫
      P.map ((F.obj M).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b M).hom) ≫
        (ε M M).hom =
      (ε _ _).hom ≫ (F'.map (P.map (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℤ) a M).hom)).app _ ≫
        (F'.obj _).map (P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b M).hom) := by
    rw [hε₂, ← Category.assoc, hε₁, Category.assoc]
  simp only [Functor.mapHomologicalComplex_obj_X]
  rw [reassoc_of% h₁, ← reassoc_of% h₂, reassoc_of% hU]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]

end CategoryTheory.Functor

end
