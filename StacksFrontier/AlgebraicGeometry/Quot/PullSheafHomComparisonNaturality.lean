module

public import StacksFrontier.AlgebraicGeometry.Quot.PullSheafHomComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality

/-!
# Dinaturality of Stacks 08J8 on an algebraic space, and naturality of Stacks 08JF

Let `X` be an algebraic space.  The tensor–Hom adjunction of Stacks 08J8,
`Hom(A ⊗^L P, Z) ≃ Hom(A, R𝓗om(P, Z))`, is *dinatural* in `P`: for `v : P' ⟶ P`, postcomposing
`h : A ⟶ R𝓗om(P, Z)` with `R𝓗om(v, Z)` corresponds to precomposing the transpose of `h` with
`1 ⊗ v`.  This file proves it, by transporting the dinaturality of the equi-universe model
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality`) along the derived equivalence
with the model, and deduces that the canonical map of Stacks 08JF
`Lg^* R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)` is natural in `P`.  With the invertibility of that map
for perfect `P` this gives the isomorphism of inverse systems
`AlgebraicGeometry.Space.PullSheafHomPerfectSystemIso`.

## Main results

* `CategoryTheory.Adjunction.homEquiv_symm_comp_map_transport`: dinaturality of a family of
  tensor–Hom adjunctions survives transport along an equivalence.
* `CategoryTheory.Adjunction.homComparison_naturality`: the comparison
  `L R(P, M) ⟶ R(L P, L M)` built from a comparison of tensor products and two dinatural
  families of adjunctions is natural in `P`.
* `AlgebraicGeometry.Space.smallEtaleDerivedTensorSheafHomAdjunction_dinaturality`: **Stacks 08J8
  on an algebraic space, dinaturality in the internal-Hom variable.**
* `AlgebraicGeometry.Space.pullSheafHomComparison_naturality`: the map of Stacks 08JF is natural
  in its first variable.
* `AlgebraicGeometry.Space.pullSheafHomPerfectSystemIso_of_pullSheafHomComparisonIsIso`:
  `AlgebraicGeometry.Space.PullSheafHomPerfectSystemIso` from
  `AlgebraicGeometry.Space.PullSheafHomComparisonIsIso`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The comparison `T(-, P) ≅ E ⋙ T'(-, E P) ⋙ E⁻¹` of a bifunctor `T` with a bifunctor `T'`
through an equivalence `E` and an isomorphism `τ` of the uncurried bifunctors. -/
def Functor.flipObjIsoOfUncurryIsoConj {C M : Type*} [Category* C] [Category* M] (e : C ≌ M)
    {T : C ⥤ C ⥤ C} {TM : M ⥤ M ⥤ M}
    (τ : Functor.uncurry.obj T ⋙ e.functor ≅ e.functor.prod e.functor ⋙ Functor.uncurry.obj TM)
    (P : C) : T.flip.obj P ≅ e.functor ⋙ TM.flip.obj (e.functor.obj P) ⋙ e.inverse :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ e.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.flipObjIsoOfUncurryIso τ P) _ ≪≫ Functor.associator _ _ _

/-- The comparison `Functor.flipObjIsoOfUncurryIsoConj` is natural in `P`. -/
theorem Functor.flipObjIsoOfUncurryIsoConj_naturality {C M : Type*} [Category* C] [Category* M]
    (e : C ≌ M) {T : C ⥤ C ⥤ C} {TM : M ⥤ M ⥤ M}
    (τ : Functor.uncurry.obj T ⋙ e.functor ≅ e.functor.prod e.functor ⋙ Functor.uncurry.obj TM)
    {P' P : C} (v : P' ⟶ P) (X : C) :
    (T.obj X).map v ≫ (Functor.flipObjIsoOfUncurryIsoConj e τ P).hom.app X =
      (Functor.flipObjIsoOfUncurryIsoConj e τ P').hom.app X ≫
        e.inverse.map ((TM.obj (e.functor.obj X)).map (e.functor.map v)) := by
  have hn := τ.hom.naturality (X := (X, P')) (Y := (X, P)) (Prod.mkHom (𝟙 X) v)
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.map_id,
    NatTrans.id_app, Category.id_comp, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj] at hn
  simp only [flipObjIsoOfUncurryIsoConj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id, Category.assoc]
  rw [show (Functor.flipObjIsoOfUncurryIso τ P').hom.app X = τ.hom.app (X, P') from rfl,
    show (Functor.flipObjIsoOfUncurryIso τ P).hom.app X = τ.hom.app (X, P) from rfl,
    ← e.inverse.map_comp, ← hn, e.inverse.map_comp]
  exact e.unitIso.hom.naturality_assoc _ _

namespace Adjunction

/-- **Dinaturality of a family of tensor–Hom adjunctions survives transport along an
equivalence.**  Let `E : C ≌ M`, let `TM(-, b) ⊣ RM(b, -)` be adjunctions on `M` which are
dinatural in `b`, and let `T(-, P) ≅ E ⋙ TM(-, E P) ⋙ E⁻¹` be natural in `P`.  Then the
transported adjunctions `T(-, P) ⊣ E ⋙ RM(E P, -) ⋙ E⁻¹` are dinatural in `P`. -/
theorem homEquiv_symm_comp_map_transport {C M : Type*} [Category* C] [Category* M] (e : C ≌ M)
    (T : C ⥤ C ⥤ C) (TM : M ⥤ M ⥤ M) (RM : Mᵒᵖ ⥤ M ⥤ M)
    (adjM : ∀ b : M, TM.flip.obj b ⊣ RM.obj (Opposite.op b))
    (hM : ∀ {b' b : M} (v : b' ⟶ b) (a z : M) (h : a ⟶ (RM.obj (Opposite.op b)).obj z),
      ((adjM b').homEquiv a z).symm (h ≫ (RM.map v.op).app z) =
        (TM.obj a).map v ≫ ((adjM b).homEquiv a z).symm h)
    (ρ : ∀ P : C, T.flip.obj P ≅ e.functor ⋙ TM.flip.obj (e.functor.obj P) ⋙ e.inverse)
    (hρ : ∀ {P' P : C} (v : P' ⟶ P) (X : C), (T.obj X).map v ≫ (ρ P).hom.app X =
      (ρ P').hom.app X ≫ e.inverse.map ((TM.obj (e.functor.obj X)).map (e.functor.map v)))
    {P' P : C} (v : P' ⟶ P) (X Z : C)
    (h : X ⟶ e.inverse.obj ((RM.obj (Opposite.op (e.functor.obj P))).obj (e.functor.obj Z))) :
    ((((e.toAdjunction.comp (adjM (e.functor.obj P'))).comp e.symm.toAdjunction).ofNatIsoLeft
        (ρ P').symm).homEquiv X Z).symm
        (h ≫ e.inverse.map ((RM.map (e.functor.map v).op).app (e.functor.obj Z))) =
      (T.obj X).map v ≫
        ((((e.toAdjunction.comp (adjM (e.functor.obj P))).comp e.symm.toAdjunction).ofNatIsoLeft
          (ρ P).symm).homEquiv X Z).symm h := by
  rw [homEquiv_ofNatIsoLeft_symm_apply, homEquiv_ofNatIsoLeft_symm_apply]
  simp only [comp_homEquiv, Equiv.symm_trans_apply, Iso.symm_inv, Equivalence.symm_inverse,
    Equivalence.symm_functor]
  rw [homEquiv_naturality_right_symm, hM, homEquiv_naturality_left_symm]
  rw [← Category.assoc, ← hρ v X, Category.assoc]
  rfl

/-- `CategoryTheory.Adjunction.homEquiv_symm_comp_map_transport` for a family of adjunctions `adj`
given as equal to the transported ones, so that it applies to a family defined as the transport
without unfolding its definition. -/
theorem homEquiv_symm_comp_map_transport' {C M : Type*} [Category* C] [Category* M] (e : C ≌ M)
    (T : C ⥤ C ⥤ C) (TM : M ⥤ M ⥤ M) (RM : Mᵒᵖ ⥤ M ⥤ M)
    (adjM : ∀ b : M, TM.flip.obj b ⊣ RM.obj (Opposite.op b))
    (hM : ∀ {b' b : M} (v : b' ⟶ b) (a z : M) (h : a ⟶ (RM.obj (Opposite.op b)).obj z),
      ((adjM b').homEquiv a z).symm (h ≫ (RM.map v.op).app z) =
        (TM.obj a).map v ≫ ((adjM b).homEquiv a z).symm h)
    (ρ : ∀ P : C, T.flip.obj P ≅ e.functor ⋙ TM.flip.obj (e.functor.obj P) ⋙ e.inverse)
    (hρ : ∀ {P' P : C} (v : P' ⟶ P) (X : C), (T.obj X).map v ≫ (ρ P).hom.app X =
      (ρ P').hom.app X ≫ e.inverse.map ((TM.obj (e.functor.obj X)).map (e.functor.map v)))
    (adj : ∀ P : C, T.flip.obj P ⊣ (e.functor.op ⋙ RM ⋙
      (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
        (Functor.whiskeringRight _ _ _).obj e.inverse).obj (Opposite.op P))
    (hadj : ∀ P : C, adj P = (((e.toAdjunction.comp (adjM (e.functor.obj P))).comp
      e.symm.toAdjunction).ofNatIsoLeft (ρ P).symm))
    {P' P : C} (v : P' ⟶ P) (X Z : C)
    (h : X ⟶ e.inverse.obj ((RM.obj (Opposite.op (e.functor.obj P))).obj (e.functor.obj Z))) :
    ((adj P').homEquiv X Z).symm
        (h ≫ e.inverse.map ((RM.map (e.functor.map v).op).app (e.functor.obj Z))) =
      (T.obj X).map v ≫ ((adj P).homEquiv X Z).symm h := by
  rw [hadj, hadj]
  exact homEquiv_symm_comp_map_transport e T TM RM adjM hM ρ hρ v X Z h

/-- The counit form of dinaturality: for `v : P' ⟶ P`, `R(v, Z)` followed by the counit at `P'`
is `1 ⊗ v` followed by the counit at `P`. -/
theorem counit_dinaturality_of {C : Type*} [Category* C] (T : C ⥤ C ⥤ C) (R : Cᵒᵖ ⥤ C ⥤ C)
    (adj : ∀ P : C, T.flip.obj P ⊣ R.obj (Opposite.op P))
    (hd : ∀ {P' P : C} (v : P' ⟶ P) (A Z : C) (h : A ⟶ (R.obj (Opposite.op P)).obj Z),
      ((adj P').homEquiv A Z).symm (h ≫ (R.map v.op).app Z) =
        (T.obj A).map v ≫ ((adj P).homEquiv A Z).symm h)
    {P' P : C} (v : P' ⟶ P) (Z : C) :
    (T.map ((R.map v.op).app Z)).app P' ≫ (adj P').counit.app Z =
      (T.obj ((R.obj (Opposite.op P)).obj Z)).map v ≫ (adj P).counit.app Z := by
  have h := hd v ((R.obj (Opposite.op P)).obj Z) Z (𝟙 _)
  rw [Category.id_comp, homEquiv_counit, homEquiv_counit, Functor.map_id, Category.id_comp] at h
  exact h

/-- **The comparison `L R(P, M) ⟶ R(L P, L M)` is natural in `P`.**  Let `L` be a functor with a
comparison `μ : L(- ⊗ -) ≅ L(-) ⊗ L(-)`, and let the tensor–Hom adjunctions on the source and
target of `L` be dinatural.  Then the transpose of `L R(P, M) ⊗ L P ≅ L(R(P, M) ⊗ P) ⟶ L M` is
natural in `P`. -/
theorem homComparison_naturality' {CY CX : Type*} [Category* CY] [Category* CX] (L : CY ⥤ CX)
    (TY : CY ⥤ CY ⥤ CY) (TX : CX ⥤ CX ⥤ CX) (RY : CYᵒᵖ ⥤ CY ⥤ CY) (RX : CXᵒᵖ ⥤ CX ⥤ CX)
    (adjY : ∀ P : CY, TY.flip.obj P ⊣ RY.obj (Opposite.op P))
    (adjX : ∀ Q : CX, TX.flip.obj Q ⊣ RX.obj (Opposite.op Q))
    (hY : ∀ {P' P : CY} (v : P' ⟶ P) (A Z : CY) (h : A ⟶ (RY.obj (Opposite.op P)).obj Z),
      ((adjY P').homEquiv A Z).symm (h ≫ (RY.map v.op).app Z) =
        (TY.obj A).map v ≫ ((adjY P).homEquiv A Z).symm h)
    (hX : ∀ {Q' Q : CX} (v : Q' ⟶ Q) (A Z : CX) (h : A ⟶ (RX.obj (Opposite.op Q)).obj Z),
      ((adjX Q').homEquiv A Z).symm (h ≫ (RX.map v.op).app Z) =
        (TX.obj A).map v ≫ ((adjX Q).homEquiv A Z).symm h)
    (μ : Functor.uncurry.obj TY ⋙ L ≅ L.prod L ⋙ Functor.uncurry.obj TX)
    (tr : ∀ P M : CY, (TX.obj (L.obj ((RY.obj (Opposite.op P)).obj M))).obj (L.obj P) ⟶ L.obj M)
    (htr : ∀ P M : CY, tr P M =
      μ.inv.app ((RY.obj (Opposite.op P)).obj M, P) ≫ L.map ((adjY P).counit.app M))
    {P' P : CY} (v : P' ⟶ P) (M : CY) :
    L.map ((RY.map v.op).app M) ≫ (adjX (L.obj P')).homEquiv _ _ (tr P' M) =
      (adjX (L.obj P)).homEquiv _ _ (tr P M) ≫ (RX.map (L.map v).op).app (L.obj M) := by
  rw [htr, htr]
  apply ((adjX (L.obj P')).homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  simp only [Functor.id_obj]
  rw [hX, Equiv.symm_apply_apply]
  have cY := counit_dinaturality_of TY RY adjY hY v M
  have n1 := μ.inv.naturality (X := ((RY.obj (Opposite.op P)).obj M, P'))
    (Y := ((RY.obj (Opposite.op P')).obj M, P')) (Prod.mkHom ((RY.map v.op).app M) (𝟙 P'))
  have n2 := μ.inv.naturality (X := ((RY.obj (Opposite.op P)).obj M, P'))
    (Y := ((RY.obj (Opposite.op P)).obj M, P)) (Prod.mkHom (𝟙 _) v)
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.comp_id, Functor.comp_obj,
    Functor.uncurry_obj_obj, Functor.prod_obj] at n1 n2
  simp only [Functor.flip_obj_map, Functor.flip_obj_obj]
  rw [reassoc_of% n1, reassoc_of% n2, ← L.map_comp, ← L.map_comp]
  exact congrArg (fun k => _ ≫ L.map k) cY

/-- `CategoryTheory.Adjunction.homComparison_naturality'` for a family `cmp` given through its
transposes. -/
theorem homComparison_naturality {CY CX : Type*} [Category* CY] [Category* CX] (L : CY ⥤ CX)
    (TY : CY ⥤ CY ⥤ CY) (TX : CX ⥤ CX ⥤ CX) (RY : CYᵒᵖ ⥤ CY ⥤ CY) (RX : CXᵒᵖ ⥤ CX ⥤ CX)
    (adjY : ∀ P : CY, TY.flip.obj P ⊣ RY.obj (Opposite.op P))
    (adjX : ∀ Q : CX, TX.flip.obj Q ⊣ RX.obj (Opposite.op Q))
    (hY : ∀ {P' P : CY} (v : P' ⟶ P) (A Z : CY) (h : A ⟶ (RY.obj (Opposite.op P)).obj Z),
      ((adjY P').homEquiv A Z).symm (h ≫ (RY.map v.op).app Z) =
        (TY.obj A).map v ≫ ((adjY P).homEquiv A Z).symm h)
    (hX : ∀ {Q' Q : CX} (v : Q' ⟶ Q) (A Z : CX) (h : A ⟶ (RX.obj (Opposite.op Q)).obj Z),
      ((adjX Q').homEquiv A Z).symm (h ≫ (RX.map v.op).app Z) =
        (TX.obj A).map v ≫ ((adjX Q).homEquiv A Z).symm h)
    (μ : Functor.uncurry.obj TY ⋙ L ≅ L.prod L ⋙ Functor.uncurry.obj TX)
    (cmp : ∀ P M : CY, L.obj ((RY.obj (Opposite.op P)).obj M) ⟶
      (RX.obj (Opposite.op (L.obj P))).obj (L.obj M))
    (hcmp : ∀ P M : CY, ((adjX (L.obj P)).homEquiv _ _).symm (cmp P M) =
      μ.inv.app ((RY.obj (Opposite.op P)).obj M, P) ≫ L.map ((adjY P).counit.app M))
    {P' P : CY} (v : P' ⟶ P) (M : CY) :
    L.map ((RY.map v.op).app M) ≫ cmp P' M = cmp P M ≫ (RX.map (L.map v).op).app (L.obj M) := by
  have e : ∀ P M : CY, cmp P M = (adjX (L.obj P)).homEquiv _ _
      (μ.inv.app ((RY.obj (Opposite.op P)).obj M, P) ≫ L.map ((adjY P).counit.app M)) :=
    fun P M => (Equiv.symm_apply_eq _).1 (hcmp P M)
  rw [e, e]
  exact homComparison_naturality' L TY TX RY RX adjY adjX hY hX μ _ (fun _ _ => rfl) v M

/-- **The comparison `L R(Fⱼ, E) ⟶ R(L Fⱼ, L E)` along a diagram**, an isomorphism of diagrams
when each component is invertible. -/
theorem nonempty_homComparison_iso {CY CX : Type*} [Category* CY] [Category* CX] (L : CY ⥤ CX)
    (TY : CY ⥤ CY ⥤ CY) (TX : CX ⥤ CX ⥤ CX) (RY : CYᵒᵖ ⥤ CY ⥤ CY) (RX : CXᵒᵖ ⥤ CX ⥤ CX)
    (adjY : ∀ P : CY, TY.flip.obj P ⊣ RY.obj (Opposite.op P))
    (adjX : ∀ Q : CX, TX.flip.obj Q ⊣ RX.obj (Opposite.op Q))
    (hY : ∀ {P' P : CY} (v : P' ⟶ P) (A Z : CY) (h : A ⟶ (RY.obj (Opposite.op P)).obj Z),
      ((adjY P').homEquiv A Z).symm (h ≫ (RY.map v.op).app Z) =
        (TY.obj A).map v ≫ ((adjY P).homEquiv A Z).symm h)
    (hX : ∀ {Q' Q : CX} (v : Q' ⟶ Q) (A Z : CX) (h : A ⟶ (RX.obj (Opposite.op Q)).obj Z),
      ((adjX Q').homEquiv A Z).symm (h ≫ (RX.map v.op).app Z) =
        (TX.obj A).map v ≫ ((adjX Q).homEquiv A Z).symm h)
    (μ : Functor.uncurry.obj TY ⋙ L ≅ L.prod L ⋙ Functor.uncurry.obj TX)
    (cmp : ∀ P M : CY, L.obj ((RY.obj (Opposite.op P)).obj M) ⟶
      (RX.obj (Opposite.op (L.obj P))).obj (L.obj M))
    (hcmp : ∀ P M : CY, ((adjX (L.obj P)).homEquiv _ _).symm (cmp P M) =
      μ.inv.app ((RY.obj (Opposite.op P)).obj M, P) ≫ L.map ((adjY P).counit.app M))
    {J : Type*} [Category* J] (F : J ⥤ CY) (E : CY) (hF : ∀ j, IsIso (cmp (F.obj j) E)) :
    Nonempty (F.op ⋙ RY.flip.obj E ⋙ L ≅ (F ⋙ L).op ⋙ RX.flip.obj (L.obj E)) :=
  ⟨NatIso.ofComponents (fun j => @asIso _ _ _ _ (cmp (F.obj j.unop) E) (hF j.unop))
    (fun {_ _} k => homComparison_naturality L TY TX RY RX adjY adjX hY hX μ cmp hcmp
      (F.map k.unop) E)⟩

end Adjunction

end CategoryTheory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_smallEtaleModel

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Model

/- Forced, as in `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom`: the model's
derived tensor product and internal Hom are those of the standard derived category, and at plain
priority instance search picks another model for them. -/
attribute [local instance 10000] HasDerivedCategory.standard

/-- Stacks 08J8 on the equi-universe model of an algebraic space, dinaturality in the
internal-Hom variable, in the adjunction form. -/
theorem smallEtaleModel_derivedTensorSheafHomAdjunction_dinaturality (X : AlgebraicSpaces B S hS)
    {b' b : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O))}
    (v : b' ⟶ b) (a z : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)))
    (h : a ⟶ ((RingedSite.derivedSheafHomBifunctor
      (smallEtaleModelRingedSite B S hS X.1 X.2)).obj (op b)).obj z) :
    ((RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2)
        b').homEquiv a z).symm
        (h ≫ ((RingedSite.derivedSheafHomBifunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).map v.op).app z) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).obj a).map v ≫
        ((RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2)
          b).homEquiv a z).symm h := by
  simp only [RingedSite.derivedTensorSheafHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    Equiv.coe_fn_symm_mk]
  rw [RingedSite.derivedCurryHomEquiv_dinaturality]

/-- **Stacks 08J8 on an algebraic space, dinaturality in the internal-Hom variable.**  For
`v : P' ⟶ P` and `h : A ⟶ R𝓗om(P, Z)`, the morphism `A ⊗^L P' ⟶ Z` matched with
`h ≫ R𝓗om(v, Z)` is `1 ⊗ v` followed by the morphism `A ⊗^L P ⟶ Z` matched with `h`. -/
theorem smallEtaleDerivedTensorSheafHomAdjunction_dinaturality (X : AlgebraicSpaces B S hS)
    {P' P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (v : P' ⟶ P)
    (A Z : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (h : A ⟶ ((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj Z) :
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P').homEquiv A Z).symm
        (h ≫ ((smallEtaleDerivedSheafHom B S hS X).map v.op).app Z) =
      ((smallEtaleDerivedTensor B S hS X).obj A).map v ≫
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P).homEquiv A Z).symm h := by
  rw [show ((smallEtaleDerivedSheafHom B S hS X).map v.op).app Z =
      (smallEtaleModelDerivedEquivalence B S hS X).inverse.map
        (((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.map v).op).app
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj Z)) from rfl]
  exact Adjunction.homEquiv_symm_comp_map_transport' (smallEtaleModelDerivedEquivalence B S hS X)
    (smallEtaleDerivedTensor B S hS X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (fun b => RingedSite.derivedTensorSheafHomAdjunction
      (smallEtaleModelRingedSite B S hS X.1 X.2) b)
    (fun v a z h => smallEtaleModel_derivedTensorSheafHomAdjunction_dinaturality X v a z h)
    (smallEtaleDerivedTensorRightIso B S hS X)
    (fun v X' => Functor.flipObjIsoOfUncurryIsoConj_naturality
      (smallEtaleModelDerivedEquivalence B S hS X) (smallEtaleModelDerivedTensorIso B S hS X) v X')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X) (fun _ => rfl) v A Z h

end Model

/-- The dinaturality of Stacks 08J8 on an algebraic space, read on `D(𝒪_X)` as the target of
the derived pullback. -/
theorem smallEtaleDerivedTensorSheafHomAdjunction_dinaturality' (X : AlgebraicSpaces B S hS)
    {P' P : derivedModules B S hS X} (v : P' ⟶ P) (A Z : derivedModules B S hS X)
    (h : A ⟶ ((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj Z) :
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P').homEquiv A Z).symm
        (h ≫ ((smallEtaleDerivedSheafHom B S hS X).map v.op).app Z) =
      ((smallEtaleDerivedTensor B S hS X).obj A).map v ≫
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P).homEquiv A Z).symm h :=
  smallEtaleDerivedTensorSheafHomAdjunction_dinaturality X v A Z h

/-- **The map of Stacks 08JF is natural in its first variable**: for `g : X ⟶ Y`, `v : P' ⟶ P`
and `M` in `D(𝒪_Y)`, `Lg^* R𝓗om(v, M)` followed by the map of Stacks 08JF at `P'` is the map of
Stacks 08JF at `P` followed by `R𝓗om(Lg^* v, Lg^* M)`. -/
theorem pullSheafHomComparison_naturality {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    {P' P : derivedModules B S hS Y} (v : P' ⟶ P) (M : derivedModules B S hS Y) :
    ((smallEtaleDerivedPullbackData B S hS).pull g).map
        (((smallEtaleDerivedSheafHom B S hS Y).map v.op).app M) ≫
        pullSheafHomComparison g P' M =
      pullSheafHomComparison g P M ≫
        ((smallEtaleDerivedSheafHom B S hS X).map
          (((smallEtaleDerivedPullbackData B S hS).pull g).map v).op).app
          (((smallEtaleDerivedPullbackData B S hS).pull g).obj M) :=
  Adjunction.homComparison_naturality ((smallEtaleDerivedPullbackData B S hS).pull g)
    (smallEtaleDerivedTensor B S hS Y) (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction_dinaturality' Y)
    (smallEtaleDerivedTensorSheafHomAdjunction_dinaturality' X)
    (smallEtaleDerivedPullbackTensorIso g) (pullSheafHomComparison g)
    (homEquiv_symm_pullSheafHomComparison g) v M

variable (B S hS) in
/-- **`AlgebraicGeometry.Space.PullSheafHomPerfectSystemIso` from Stacks 08JF.**  If the map of
Stacks 08JF is invertible for perfect sources
(`AlgebraicGeometry.Space.PullSheafHomComparisonIsIso`), then for every system `n ↦ Fₙ` of perfect
objects the inverse systems `Lg^* R𝓗om(Fₙ, E)` and `R𝓗om(Lg^*Fₙ, Lg^*E)` are isomorphic,
through the maps of Stacks 08JF, which are natural in `n`
(`AlgebraicGeometry.Space.pullSheafHomComparison_naturality`). -/
theorem pullSheafHomPerfectSystemIso_of_pullSheafHomComparisonIsIso
    (hH : PullSheafHomComparisonIsIso B S hS) : PullSheafHomPerfectSystemIso B S hS :=
  fun g F hF E => Adjunction.nonempty_homComparison_iso
    ((smallEtaleDerivedPullbackData B S hS).pull g)
    (smallEtaleDerivedTensor B S hS _) (smallEtaleDerivedTensor B S hS _)
    (smallEtaleDerivedSheafHom B S hS _) (smallEtaleDerivedSheafHom B S hS _)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS _)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS _)
    (smallEtaleDerivedTensorSheafHomAdjunction_dinaturality' _)
    (smallEtaleDerivedTensorSheafHomAdjunction_dinaturality' _)
    (smallEtaleDerivedPullbackTensorIso g) (pullSheafHomComparison g)
    (homEquiv_symm_pullSheafHomComparison g) F E (fun n => hH g _ E (hF n))

end AlgebraicGeometry.Space

end
