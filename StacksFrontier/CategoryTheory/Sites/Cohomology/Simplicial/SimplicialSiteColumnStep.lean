module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerFibreContractible
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteMooreSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.StdCoverResolution
public import StacksFrontier.Cotangent.Triangle.DerivedFirstVertex

/-!
# The column step of Stacks 08RX on the simplicial site of Stacks 09D0

Let `(C, J)` be a small site and let `Δ × C` be the simplicial site of [Stacks, Tag 09D0]. Fix a
homomorphism `θ : O ⟶ O'` of sheaves of commutative rings on `Δ × C` and write `s(-)` for the
complex of abelian sheaves attached to a simplicial module by
`Stacks.SimplicialModules.mooreSheafCochain`. The **column step** of [Stacks, Tag 08RX], run on
`Δ × C` rather than at a fibre, says that the base-change unit

`s(F) ⟶ s(F ⊗_O O')`

is a quasi-isomorphism at each term of a resolution of a simplicial module by standard covers,
under the single hypothesis that the unit is a quasi-isomorphism on the copower of the structure
ring by a *pulled-back representable*, that is by `pr₂^* h_U = h_U ∘ pr₂` for an object `U` of
`C`. Nothing about the fibres of `O` or `O'` is assumed.

## Main results

* `AlgebraicTopology.quasiIso_alternatingFaceMapCochainComplex_map_of_homotopyEquivalences`: a
  simplicial homotopy equivalence in an abelian category is a quasi-isomorphism on reindexed
  Moore complexes.
* `Stacks.SimplicialModules.quasiIso_mooreAbPresheafCochain_map_of_forall` and
  `Stacks.SimplicialModules.quasiIso_mooreAbPresheafCochain_map_of_forall_whiskerLeft`: a
  quasi-isomorphism question about the presheaf-level Moore complex of a morphism of abelian
  presheaves on `Δ × C` is a question about each object of `C` separately.
* `Stacks.SimplicialModules.quasiIso_mooreAbPresheafCochain_copowerMap_prodProjIndex` and
  `Stacks.SimplicialModules.quasiIso_mooreAbSheafCochain_copowerMap_prodProjIndex`: multiplying
  by the projection away from the simplex factor is a Moore quasi-isomorphism.
* `Stacks.SimplicialModules.quasiIso_mooreAbSheafCochain_copowerMap_uliftYoneda`: the transfer
  from the pulled-back representable to the representable.
* `Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_free` and
  `Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_freeUliftYoneda`: the base-change
  unit at a free simplicial module, and at a free simplicial module on a representable, which is
  the summand the standard cover is built from.
* `Stacks.SimplicialModules.hasCoproducts_sheaf_addCommGrp` and
  `Stacks.SimplicialModules.hasExactColimitsOfShape_discrete_sheaf_addCommGrp`: coproducts of
  abelian sheaves exist and are exact (Grothendieck's AB4), recorded for the site at hand.
* `Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_stdCover` and
  `Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_isStdCover`: **the column step**
  — the base-change unit is a quasi-isomorphism at a standard cover, and hence at every term of
  a resolution by standard covers.

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

universe u

namespace AlgebraicTopology

/-- A simplicial homotopy equivalence in an abelian category is a quasi-isomorphism on the
reindexed Moore complexes. -/
theorem quasiIso_alternatingFaceMapCochainComplex_map_of_homotopyEquivalences {A : Type*}
    [Category* A] [Abelian A] {P P' : SimplicialObject A} {f : P ⟶ P'}
    (hf : SimplicialObject.homotopyEquivalences A f) :
    QuasiIso ((alternatingFaceMapCochainComplex A).map f) :=
  (quasiIso_alternatingFaceMapCochainComplex_map_iff f).2 fun n =>
    SimplicialObject.isInvertedBy_homologyFunctor_alternatingFaceMapComplex n f hf

end AlgebraicTopology

namespace Stacks.SimplicialModules

open Stacks.PresheafOfModules.ChangeOfRings Stacks.SimplicialSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-! ### Reading a presheaf-level question one object of `C` at a time -/


/-- The presheaf-level Moore complex of a morphism of abelian presheaves on `Δ × C` is a
quasi-isomorphism as soon as its evaluation at every object of `C` is one. -/
theorem quasiIso_mooreAbPresheafCochain_map_of_forall
    {P P' : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ P')
    (hf : ∀ V : C, QuasiIso ((((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op V)
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((mooreAbPresheafCochain (C := C)).map f))) :
    QuasiIso ((mooreAbPresheafCochain (C := C)).map f) :=
  (HomologicalComplex.quasiIso_iff_evaluation _).2 fun V => hf V.unop

/-- The presheaf-level Moore complex of a morphism of abelian presheaves on `Δ × C` is a
quasi-isomorphism as soon as, for every object `V` of `C`, the reindexed Moore complex of its
restriction to the slice `Δ × {V}` is one. -/
theorem quasiIso_mooreAbPresheafCochain_map_of_forall_whiskerLeft
    {P P' : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ P')
    (hf : ∀ V : C, QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
      (Functor.whiskerLeft (Functor.prodSectionFst V).op f))) :
    QuasiIso ((mooreAbPresheafCochain (C := C)).map f) := by
  refine quasiIso_mooreAbPresheafCochain_map_of_forall f fun V => ?_
  have h2 : QuasiIso (((SimplicialObject.whiskering (Cᵒᵖ ⥤ AddCommGrpCat.{u})
      AddCommGrpCat.{u}).obj ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op V)) ⋙
        alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
          ((simplicialCurry AddCommGrpCat.{u}).map f)) := hf V
  refine quasiIso_of_comp_right _ ((alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
    ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom.app
      ((simplicialCurry AddCommGrpCat.{u}).obj P'))
    (hφφ' := ?_)
  erw [(alternatingFaceMapCochainComplexCompMapHomologicalComplexIso _).hom.naturality]
  infer_instance

/-! ### The projection away from the simplex factor -/

/-- Multiplying an abelian presheaf on `Δ × C` by the projection
`Stacks.SimplicialSite.prodProjIndex X : h_X ⟶ h_{X₂} ∘ pr₂` away from the simplex factor is a
quasi-isomorphism of presheaf-level Moore complexes. -/
theorem quasiIso_mooreAbPresheafCochain_copowerMap_prodProjIndex
    (P : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (X : SimplexCategory × C) :
    QuasiIso ((mooreAbPresheafCochain (C := C)).map
      (Functor.copowerMap (𝟙 P) (prodProjIndex X))) :=
  quasiIso_mooreAbPresheafCochain_map_of_forall_whiskerLeft _ fun V =>
    quasiIso_alternatingFaceMapCochainComplex_map_of_homotopyEquivalences
      (homotopyEquivalences_copowerMap_prodProjIndex_fibre
        ((Functor.prodSectionFst V).op ⋙ P) X V)

/-- Multiplying an abelian presheaf on `Δ × C` by the projection
`Stacks.SimplicialSite.prodProjIndex X` away from the simplex factor is a quasi-isomorphism of
the complexes `s(-)`. -/
theorem quasiIso_mooreAbSheafCochain_copowerMap_prodProjIndex
    (P : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (X : SimplexCategory × C) :
    QuasiIso ((mooreAbSheafCochain J).map (Functor.copowerMap (𝟙 P) (prodProjIndex X))) :=
  quasiIso_mapHomologicalComplex_presheafToSheaf J _
    (quasiIso_mooreAbPresheafCochain_copowerMap_prodProjIndex P X)

/-! ### Base change at a free simplicial module and at a standard cover -/

variable {O O' : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u}} (θ : O ⟶ O')

/-- If the copower of the homomorphism of structure rings by the pulled-back representable
`h_{X₂} ∘ pr₂` is a quasi-isomorphism of complexes `s(-)`, then so is its copower by the
representable `h_X` itself. -/
theorem quasiIso_mooreAbSheafCochain_copowerMap_uliftYoneda (X : SimplexCategory × C)
    (hstep : QuasiIso ((mooreAbSheafCochain J).map (Functor.copowerMap (unitMap' θ)
      (𝟙 ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ uliftYoneda.{u}.obj X.2))))) :
    QuasiIso ((mooreAbSheafCochain J).map
      (Functor.copowerMap (unitMap' θ) (𝟙 (uliftYoneda.{u}.obj X)))) := by
  have hsq : Functor.copowerMap (unitMap' θ) (𝟙 (uliftYoneda.{u}.obj X)) ≫
        Functor.copowerMap (𝟙 (unitPresheaf' O')) (prodProjIndex X) =
      Functor.copowerMap (𝟙 (unitPresheaf' O)) (prodProjIndex X) ≫
        Functor.copowerMap (unitMap' θ)
          (𝟙 ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ uliftYoneda.{u}.obj X.2)) := by
    simp only [Functor.copowerMap_comp, Category.comp_id, Category.id_comp]
  have h₂ : QuasiIso ((mooreAbSheafCochain J).map
      (Functor.copowerMap (𝟙 (unitPresheaf' O')) (prodProjIndex X))) :=
    quasiIso_mooreAbSheafCochain_copowerMap_prodProjIndex J (unitPresheaf' O') X
  have h₁ : QuasiIso ((mooreAbSheafCochain J).map
      (Functor.copowerMap (𝟙 (unitPresheaf' O)) (prodProjIndex X))) :=
    quasiIso_mooreAbSheafCochain_copowerMap_prodProjIndex J (unitPresheaf' O) X
  refine quasiIso_of_comp_right _ ((mooreAbSheafCochain J).map
    (Functor.copowerMap (𝟙 (unitPresheaf' O')) (prodProjIndex X))) (hφφ' := ?_)
  rw [← Functor.map_comp, hsq, Functor.map_comp]
  infer_instance

/-- The base-change unit is a quasi-isomorphism of complexes `s(-)` at the free simplicial
module `O⟨F⟩` as soon as the copower by `F` of the homomorphism of structure rings is one. -/
theorem quasiIso_mooreSheafBaseChange_app_free {F : (SimplexCategory × C)ᵒᵖ ⥤ Type u}
    (hF : QuasiIso ((mooreAbSheafCochain J).map (Functor.copowerMap (unitMap' θ) (𝟙 F)))) :
    QuasiIso ((mooreSheafBaseChange J θ).app
      ((PresheafOfModules.free (ringPresheaf O)).obj F)) := by
  have key : (mooreSheafBaseChange J θ).app
        ((PresheafOfModules.free (ringPresheaf O)).obj F) =
      (mooreAbSheafCochain J).map
        ((PresheafOfModules.copowerFreeIso' (ringPresheaf O) F).inv ≫
          Functor.copowerMap (unitMap' θ) (𝟙 F) ≫ (changeOfRingsFreeCopowerIso' θ F).hom) := by
    rw [copowerFreeIso_unitMap_copowerMap', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl
  rw [key, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- The base-change unit is a quasi-isomorphism of complexes `s(-)` at the free simplicial
module on a universe-lifted representable, provided it is one on the copower of the structure
ring by every pulled-back representable. -/
theorem quasiIso_mooreSheafBaseChange_app_freeUliftYoneda
    (hstep : ∀ U : C, QuasiIso ((mooreAbSheafCochain J).map (Functor.copowerMap (unitMap' θ)
      (𝟙 ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ uliftYoneda.{u}.obj U)))))
    (X : SimplexCategory × C) :
    QuasiIso ((mooreSheafBaseChange J θ).app
      ((PresheafOfModules.free (ringPresheaf O)).obj (uliftYoneda.{u}.obj X))) :=
  quasiIso_mooreSheafBaseChange_app_free J θ
    (quasiIso_mooreAbSheafCochain_copowerMap_uliftYoneda J θ X (hstep X.2))

/-- Coproducts of abelian sheaves exist, and are the sheafifications of the coproducts of the
underlying presheaves. -/
instance hasCoproducts_sheaf_addCommGrp : HasCoproducts.{u} (Sheaf J AddCommGrpCat.{u}) := by
  have i₁ : HasSheafify J AddCommGrpCat.{u} := inferInstance
  have i₂ : HasWeakSheafify J AddCommGrpCat.{u} := HasSheafify.isRightAdjoint
  have i₃ : HasCoproducts.{u} AddCommGrpCat.{u} := fun _ => inferInstance
  have i₄ : HasCoproducts.{u} (Cᵒᵖ ⥤ AddCommGrpCat.{u}) := fun _ => inferInstance
  exact fun _ => ⟨fun F => HasColimit.mk
    ⟨Sheaf.sheafifyCocone (colimit.cocone (F ⋙ sheafToPresheaf J AddCommGrpCat.{u})),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-- Grothendieck's axiom AB4 for abelian sheaves: coproducts of abelian sheaves are exact. -/
instance hasExactColimitsOfShape_discrete_sheaf_addCommGrp (I : Type u) :
    HasExactColimitsOfShape (Discrete I) (Sheaf J AddCommGrpCat.{u}) := by
  have i₁ : HasSheafify J AddCommGrpCat.{u} := inferInstance
  have i₂ : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} := inferInstance
  have i₃ : HasExactColimitsOfShape (Discrete I) AddCommGrpCat.{u} := inferInstance
  exact Sheaf.hasExactColimitsOfShape (J := J)

/-- A natural transformation between coproduct-preserving functors to cochain complexes of
abelian sheaves is a quasi-isomorphism at a coproduct as soon as it is one at each summand. -/
theorem quasiIso_app_sigma_sheaf {D : Type*} [Category* D] {I : Type u}
    {T₁ T₂ : D ⥤ CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ} (η : T₁ ⟶ T₂)
    [PreservesColimitsOfShape (Discrete I) T₁] [PreservesColimitsOfShape (Discrete I) T₂]
    (N : I → D) [HasCoproduct N] (h : ∀ i, QuasiIso (η.app (N i))) :
    QuasiIso (η.app (∐ N)) :=
  CochainComplex.quasiIso_app_sigma η N h

/-- The column step at a standard cover: the base-change unit of complexes `s(-)` is a
quasi-isomorphism at the standard cover `M.stdCover'` of a simplicial module `M`, provided it is
one on the copower of the structure ring by every pulled-back representable. -/
theorem quasiIso_mooreSheafBaseChange_app_stdCover
    (hstep : ∀ U : C, QuasiIso ((mooreAbSheafCochain J).map (Functor.copowerMap (unitMap' θ)
      (𝟙 ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ uliftYoneda.{u}.obj U)))))
    (M : PresheafOfModules.{u} (ringPresheaf O)) :
    QuasiIso ((mooreSheafBaseChange J θ).app M.stdCover') := by
  have h : ∀ m : M.Elements, QuasiIso ((mooreSheafBaseChange J θ).app
      ((PresheafOfModules.free (ringPresheaf O)).obj (uliftYoneda.{u}.obj m.1.unop))) :=
    fun m => quasiIso_mooreSheafBaseChange_app_freeUliftYoneda J θ hstep m.1.unop
  have i₁ : PreservesColimitsOfShape (Discrete M.Elements) (mooreSheafCochain J O) :=
    inferInstance
  have i₂ : PreservesColimitsOfShape (Discrete M.Elements)
      (changeOfRings θ ⋙ mooreSheafCochain J O') := inferInstance
  exact quasiIso_app_sigma_sheaf J (mooreSheafBaseChange J θ)
    (fun m : M.Elements =>
      (PresheafOfModules.free (ringPresheaf O)).obj (uliftYoneda.{u}.obj m.1.unop)) h

/-- **The column step of [Stacks, Tag 08RX] on the simplicial site `Δ × C` of
[Stacks, Tag 09D0]: the base-change unit `s(F) ⟶ s(F ⊗_O O')` is a quasi-isomorphism at every
term of a resolution by standard covers**, provided it is one on the copower of the structure
ring by every pulled-back representable `h_U ∘ pr₂`. -/
theorem quasiIso_mooreSheafBaseChange_app_of_isStdCover
    (hstep : ∀ U : C, QuasiIso ((mooreAbSheafCochain J).map (Functor.copowerMap (unitMap' θ)
      (𝟙 ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ uliftYoneda.{u}.obj U)))))
    {N : PresheafOfModules.{u} (ringPresheaf O)} (hN : PresheafOfModules.IsStdCover N) :
    QuasiIso ((mooreSheafBaseChange J θ).app N) := by
  obtain hz | ⟨N', ⟨e⟩⟩ := hN
  · have h₁ : IsZero ((mooreSheafCochain J O).obj N) := Functor.map_isZero _ hz
    have h₂ : IsZero ((changeOfRings θ ⋙ mooreSheafCochain J O').obj N) :=
      Functor.map_isZero _ hz
    have : IsIso ((mooreSheafBaseChange J θ).app N) :=
      ⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩
    infer_instance
  · have h := (mooreSheafBaseChange J θ).naturality e.hom
    have key : (mooreSheafBaseChange J θ).app N =
        (mooreSheafCochain J O).map e.hom ≫ (mooreSheafBaseChange J θ).app N'.stdCover' ≫
          (changeOfRings θ ⋙ mooreSheafCochain J O').map e.inv := by
      rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp, e.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
    rw [key]
    have := quasiIso_mooreSheafBaseChange_app_stdCover J θ hstep N'
    infer_instance

end Stacks.SimplicialModules

end
