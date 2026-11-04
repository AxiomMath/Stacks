module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.FibreHomologyDeltaFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.LowerShriekAsAFibrewiseColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriek

/-!
# The fibre homology presheaves in degree zero

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site `(D, O_D)`, as in
Stacks 08P8, with small fibres. The presheaf of fibre homology `L_{n,p}(F)` of Stacks 08PI has
value `H_n(C_V, F|_{C_V})` at an object `V` of the base, and `H_n(C_V, -)` is by Stacks 08PF the
`n`th left derived functor of `colim_{(C_V)ᵒᵖ}`. Since `colim` is right exact, in degree zero
`L_{0,p}(F)` is the presheaf `V ↦ colim_{(C_V)ᵒᵖ} F|_{C_V}` of fibrewise colimits, which by
Stacks 08PE is the left Kan extension `p_!F` of `F` along `p.op`, before sheafification. This
identification holds as an isomorphism of functors, and `π_!` is the sheafification of
`L_{0,p}`.

For a functor `f : C' ⥤ C` of small categories and a morphism `t : F' ⟶ f.op ⋙ F` of
coefficients, the canonical map of Stacks 08PH in degree zero is compatible with the canonical
map on colimits: the square

```
H_0(C', F') → H_0(C, F)
     ↓             ↓
colim F'  →  colim F
```

commutes, the vertical maps being `colim`'s right exactness and the lower map the composite of
`colim t` with `Limits.colimit.pre`.

## Main definitions

* `Stacks.CategoryHomology.colimitIsoCategoryHomologyZero`: the identification of the colimit of
  an abelian presheaf with its degree-zero homology.
* `Stacks.Sites.FibredCategory.fiberColimitHomologyZeroIso`: the comparison at an object of the
  base, between the value of the left Kan extension and the degree-zero fibre homology.
* `Stacks.Sites.FibredCategory.lanObjIsoFiberHomologyPresheaf`: the comparison as an isomorphism
  of presheaves on the base.
* `Stacks.Sites.FibredCategory.lanIsoFiberHomologyPresheafFunctorZero`: the comparison as an
  isomorphism of functors of the coefficient presheaf, `p_! ≅ L_{0,p}`.
* `Stacks.Sites.FibredCategory.abelianLowerShriekIsoFiberHomologySheafZero`: the sheafified
  comparison `π_! ≅ L_0`.

## Main results

* `Stacks.CategoryHomology.homologyMapAux_zero_comp_fromLeftDerivedZero` and
  `Stacks.CategoryHomology.categoryHomologyMap_zero_comp_fromLeftDerivedZero`: the canonical map
  of Stacks 08PH in degree zero is the canonical map on colimits.
* `Stacks.CategoryHomology.colimitIsoCategoryHomologyZero_hom_naturality`: the identification of
  the colimit with the degree-zero homology is natural in the presheaf.
* `Stacks.Sites.FibredCategory.fiberColimitHomologyZeroIso_naturality_base` and
  `Stacks.Sites.FibredCategory.fiberColimitHomologyZeroIso_naturality_coefficients`: the
  comparison is natural in the base object and in the coefficients.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08PE](https://stacks.math.columbia.edu/tag/08PE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category Opposite

namespace Stacks.CategoryHomology

attribute [local implicit_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor

/-! ### The canonical map on homology in degree zero -/

/-- The canonical map of Stacks 08PH in degree zero is the canonical map on colimits. -/
theorem homologyMapAux_zero_comp_fromLeftDerivedZero.{u, u', v}
    {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C']
    [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]
    [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]
    (f : C' ⥤ C) {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} (t : F' ⟶ f.op ⋙ F) :
    homologyMapAux.{u, u', v} f t 0 ≫
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).fromLeftDerivedZero.app F =
      (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).fromLeftDerivedZero.app F' ≫
        colim.map t ≫ colimit.pre F f.op := by
  have hφ := ProjectiveResolution.lift'_commutes t (ProjectiveResolution.of F')
    ((presheafRestriction.{u, u', v} f).mapAugmentation (ProjectiveResolution.of F).π)
  set φ := ProjectiveResolution.lift' t (ProjectiveResolution.of F')
    ((presheafRestriction.{u, u', v} f).mapAugmentation (ProjectiveResolution.of F).π)
  have h0 : φ.f 0 ≫
        Functor.whiskerLeft f.op ((ProjectiveResolution.of F).π.f 0) =
      (ProjectiveResolution.of F').π.f 0 ≫ t := by
    have h := congrArg (fun α => HomologicalComplex.Hom.f α 0) hφ
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      Functor.mapAugmentation_f_zero, ChainComplex.single₀_map_f_zero] at h
    exact h
  have key : HomologicalComplex.opcyclesMap
        ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).map φ ≫
          colimitRestrictionPreComplex.{u, u', v} f (ProjectiveResolution.of F).complex) 0 ≫
        (ProjectiveResolution.of F).fromLeftDerivedZero' colim =
      (ProjectiveResolution.of F').fromLeftDerivedZero' colim ≫
        colim.map t ≫ colimit.pre F f.op := by
    refine (cancel_epi (HomologicalComplex.pOpcycles
      ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (ProjectiveResolution.of F').complex) 0)).mp ?_
    rw [← assoc, HomologicalComplex.p_opcyclesMap, assoc,
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, colimitRestrictionPre_app, assoc,
      colimit.pre_map ((ProjectiveResolution.of F).π.f 0) f.op, ← assoc,
      ← CategoryTheory.Functor.map_comp, h0, CategoryTheory.Functor.map_comp, assoc]
    rfl
  rw [homologyMapAux_eq f t 0 _ hφ,
    ProjectiveResolution.fromLeftDerivedZero_eq (ProjectiveResolution.of F) colim,
    ProjectiveResolution.fromLeftDerivedZero_eq (ProjectiveResolution.of F') colim]
  simp only [assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
  rw [HomologicalComplex.homologyFunctor_map, ← Iso.inv_comp_eq, ← assoc,
    ChainComplex.isoHomologyι₀_inv_naturality]
  simp only [assoc, Iso.inv_hom_id_assoc]
  exact key

/-- For two small categories in one universe, the canonical map of Stacks 08PH on homology in
degree zero is the canonical map on colimits, read through the right exactness of `colim`. -/
theorem categoryHomologyMap_zero_comp_fromLeftDerivedZero.{u, v}
    {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (t : F' ⟶ f.op ⋙ F) :
    categoryHomologyMap.{u, u, v} f t 0 ≫
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).fromLeftDerivedZero.app F =
      (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).fromLeftDerivedZero.app F' ≫
        colim.map t ≫ colimit.pre F f.op :=
  homologyMapAux_zero_comp_fromLeftDerivedZero.{u, u, v} f t

/-- The same statement with the right exactness of `colim` presented as the isomorphism
`CategoryTheory.Functor.leftDerivedZeroIsoSelf`. -/
theorem categoryHomologyMap_zero_comp_leftDerivedZeroIsoSelf.{u, v}
    {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (t : F' ⟶ f.op ⋙ F) :
    categoryHomologyMap.{u, u, v} f t 0 ≫
        (Iso.app (Functor.leftDerivedZeroIsoSelf
          (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _)) F).hom =
      (Iso.app (Functor.leftDerivedZeroIsoSelf
          (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _)) F').hom ≫
        colim.map t ≫ colimit.pre F f.op :=
  categoryHomologyMap_zero_comp_fromLeftDerivedZero.{u, v} f t

/-- The inverse form of the degree-zero compatibility: the canonical map on homology read from
the colimits. -/
theorem leftDerivedZeroIsoSelf_inv_comp_categoryHomologyMap_zero.{u, v}
    {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (t : F' ⟶ f.op ⋙ F) :
    (Iso.app (Functor.leftDerivedZeroIsoSelf
          (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _)) F').inv ≫
        categoryHomologyMap.{u, u, v} f t 0 =
      (colim.map t ≫ colimit.pre F f.op) ≫
        (Iso.app (Functor.leftDerivedZeroIsoSelf
          (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _)) F).inv := by
  rw [Iso.inv_comp_eq, ← assoc, Iso.eq_comp_inv]
  exact categoryHomologyMap_zero_comp_leftDerivedZeroIsoSelf.{u, v} f t

/-! ### Degree-zero homology of a category is the colimit -/

/-- The colimit of an abelian presheaf on a small category is its degree-zero homology. -/
def colimitIsoCategoryHomologyZero.{u, v} {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    colimit F ≅ categoryHomology.{u, v} F 0 :=
  (Iso.app (Functor.leftDerivedZeroIsoSelf
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _)) F).symm

/-- The degree-zero identification of homology with the colimit is natural in the presheaf, with
the canonical map of Stacks 08PH for the identity functor on homology. -/
theorem colimitIsoCategoryHomologyZero_hom_naturality.{u, v} {C : Type u} [SmallCategory C]
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (β : F ⟶ G) :
    colim.map β ≫ (colimitIsoCategoryHomologyZero.{u, v} G).hom =
      (colimitIsoCategoryHomologyZero.{u, v} F).hom ≫
        categoryHomologyMap.{u, u, v} (𝟭 C) β 0 := by
  rw [categoryHomologyMap_id_eq_leftDerived_map.{u, v}]
  exact (Functor.leftDerivedZeroIsoSelf
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _)).inv.naturality β

/-- The degree-zero compatibility of Stacks 08PH, with the right exactness of `colim` presented as
`colimitIsoCategoryHomologyZero`. -/
theorem colimitIsoCategoryHomologyZero_hom_comp_categoryHomologyMap_zero.{u, v}
    {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (t : F' ⟶ f.op ⋙ F) :
    (colimitIsoCategoryHomologyZero.{u, v} F').hom ≫ categoryHomologyMap.{u, u, v} f t 0 =
      colim.map t ≫ colimit.pre F f.op ≫ (colimitIsoCategoryHomologyZero.{u, v} F).hom := by
  rw [← assoc]
  exact leftDerivedZeroIsoSelf_inv_comp_categoryHomologyMap_zero.{u, v} f t

end Stacks.CategoryHomology

namespace Stacks.Sites.FibredCategory

open Stacks.CategoryHomology

universe uD vD uC w

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

/-! ### The comparison at an object of the base -/

/-- The degree-zero comparison of Stacks 08PJ at an object `V` of the base: the value at `V` of
the left Kan extension of `F` along `p.op` is the degree-zero homology of the fibre at `V`. -/
def fiberColimitHomologyZeroIso (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (V : s.base.C) :
    (s.p.op.lan.obj F).obj (op V) ≅
      CategoryHomology.categoryHomology.{uC, max w uD vD uC}
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) 0 :=
  fiberColimitIso s F V ≪≫
    CategoryHomology.colimitIsoCategoryHomologyZero.{uC, max w uD vD uC} _

/-- The comparison at `V` is the fibrewise-colimit comparison of Stacks 08PE followed by the
degree-zero identification of the colimit with homology. -/
lemma fiberColimitHomologyZeroIso_hom (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
    (V : s.base.C) :
    (fiberColimitHomologyZeroIso s F V).hom = (fiberColimitIso s F V).hom ≫
      (CategoryHomology.colimitIsoCategoryHomologyZero.{uC, max w uD vD uC}
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F)).hom :=
  rfl

/-- The fibrewise-colimit comparison of Stacks 08PE is natural in the base object: the
restriction map of the left Kan extension along `h : V' ⟶ V` becomes, on fibrewise colimits, the
map induced by restriction of `F` along the chosen cartesian lifts followed by the canonical
comparison of the two colimits. -/
lemma fiberColimitIso_naturality_base (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
    {V V' : s.base.C} (h : V' ⟶ V) :
    (s.p.op.lan.obj F).map h.op ≫ (fiberColimitIso s F V').hom =
      (fiberColimitIso s F V).hom ≫
        colim.map (fiberCartesianRestriction s F h) ≫
          colimit.pre ((Functor.Fiber.fiberInclusion (p := s.p) (S := V')).op ⋙ F)
            ((Functor.chosenPullbacks s.p).pullbackFunctor h).op := by
  refine (Iso.inv_comp_eq _).mp (colimit.hom_ext fun x => ?_)
  have hr : colimit.ι ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) x ≫
        (fiberColimitIso s F V).inv ≫ (s.p.op.lan.obj F).map h.op ≫
          (fiberColimitIso s F V').hom =
      F.map (.op ((Functor.chosenPullbacks s.p).map h x.unop)) ≫
        colimit.ι ((Functor.Fiber.fiberInclusion (p := s.p) (S := V')).op ⋙ F)
          (.op ((Functor.chosenPullbacks s.p).obj h x.unop)) :=
    (fiberwiseColimitFormula s).restriction F h x.unop
  rw [hr, ← assoc, colimit.ι_map, assoc, colimit.ι_pre, fiberCartesianRestriction_app]
  rfl

/-- Naturality of the degree-zero comparison in the base object: in degree zero the canonical map
of Stacks 08PH attached to a chosen pullback functor and to restriction along the chosen
cartesian lifts is the canonical map on fibrewise colimits. -/
lemma fiberColimitHomologyZeroIso_naturality_base
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) {V V' : s.base.C} (h : V' ⟶ V) :
    (s.p.op.lan.obj F).map h.op ≫ (fiberColimitHomologyZeroIso s F V').hom =
      (fiberColimitHomologyZeroIso s F V).hom ≫
        CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC}
          ((Functor.chosenPullbacks s.p).pullbackFunctor h)
          (fiberCartesianRestriction s F h) 0 := by
  conv_lhs => rw [fiberColimitHomologyZeroIso_hom, ← assoc, fiberColimitIso_naturality_base]
  conv_rhs => rw [fiberColimitHomologyZeroIso_hom, assoc,
    CategoryHomology.colimitIsoCategoryHomologyZero_hom_comp_categoryHomologyMap_zero.{uC,
      max w uD vD uC}]
  simp only [assoc]

/-- Naturality of the degree-zero comparison in the coefficients: the left Kan extension and the
degree-zero fibre homology act on a morphism `α : F ⟶ G` through the colimit of `α` restricted to
each fibre. -/
lemma fiberColimitHomologyZeroIso_naturality_coefficients
    {F G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}} (α : F ⟶ G) (V : s.base.C) :
    (s.p.op.lan.map α).app (op V) ≫ (fiberColimitHomologyZeroIso s G V).hom =
      (fiberColimitHomologyZeroIso s F V).hom ≫
        CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC} (𝟭 (s.p.Fiber V))
          (Functor.whiskerLeft (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op α) 0 := by
  have hc : (s.p.op.lan.map α).app (op V) ≫ (fiberColimitIso s G V).hom =
      (fiberColimitIso s F V).hom ≫ colim.map (Functor.whiskerLeft
        (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op α) :=
    (fiberwiseColimitFormula s).comparison_naturality F G α V
  conv_lhs => rw [fiberColimitHomologyZeroIso_hom, ← assoc, hc]
  conv_rhs => rw [fiberColimitHomologyZeroIso_hom, assoc,
    ← CategoryHomology.colimitIsoCategoryHomologyZero_hom_naturality.{uC, max w uD vD uC}]
  simp only [assoc]

/-! ### The comparison of functors -/

/-- The degree-zero comparison of Stacks 08PJ, as an isomorphism of presheaves on the base: the
left Kan extension of `F` along `p.op` is the presheaf `L_{0,p}(F)` of degree-zero fibre homology
of Stacks 08PI. -/
def lanObjIsoFiberHomologyPresheaf (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) :
    s.p.op.lan.obj F ≅ fiberHomologyPresheaf s F 0 :=
  NatIso.ofComponents (fun V => fiberColimitHomologyZeroIso s F V.unop)
    fun {_V _V'} h => fiberColimitHomologyZeroIso_naturality_base s F h.unop

/-- The degree-zero comparison of Stacks 08PJ, as an isomorphism of functors: before
sheafification, the lower shriek of Stacks 08PE agrees with the presheaf of fibre homology of
Stacks 08PI in degree zero, naturally in the coefficient presheaf. -/
def lanIsoFiberHomologyPresheafFunctorZero :
    s.p.op.lan ≅ fiberHomologyPresheafFunctor s 0 :=
  NatIso.ofComponents (fun F => lanObjIsoFiberHomologyPresheaf s F)
    fun {_F _G} α => NatTrans.ext (funext fun V =>
      fiberColimitHomologyZeroIso_naturality_coefficients s α V.unop)

/-- The degree-zero comparison of Stacks 08PJ for the sheafified functors: the lower shriek `π_!`
on abelian sheaves is the sheafification of the presheaf of degree-zero fibre homology, that is
the sheaf `L_0` of Stacks 08PI. -/
def abelianLowerShriekIsoFiberHomologySheafZero :
    s.abelianLowerShriek ≅
      sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
        fiberHomologyPresheafFunctor s 0 ⋙
          presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} :=
  s.abelianLowerShriekIsoConstruction ≪≫ (fiberwiseColimitFormula s).sheafIso ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (lanIsoFiberHomologyPresheafFunctorZero s) _)

end Stacks.Sites.FibredCategory

end
