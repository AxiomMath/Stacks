module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExt
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
import StacksCore.Tactic.StacksAttribute

/-!
# The maps of the Mayer–Vietoris sequence of homomorphisms

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` and let `E`, `F` be objects of `D(𝒪_X)`.  Stacks 08H9 is the
Mayer–Vietoris long exact sequence

`⋯ ⟶ Ext⁻¹(E|_P, F|_P) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊕ Hom(E|_V, F|_V) ⟶ Hom(E|_P, F|_P) ⟶ ⋯`

whose maps are, in the source, the restrictions along the morphisms of the square, their
difference over the intersection, and the connecting homomorphism of the Mayer–Vietoris
distinguished triangle.  `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExt` obtains
the exactness with its three maps quantified over.  This file says what they are.

## Main definitions

* `CategoryTheory.comparisonShiftedHomMap`: the map `Ext^n(E|_U, F|_U) ⟶ Ext^n(E|_P, F|_P)`
  induced by a comparison `j_{P!}((-)|_P) ⟶ j_{U!}((-)|_U)` of extensions by zero, read through
  the identifications of Stacks 08FJ.
* `CategoryTheory.mayerVietorisShiftedHomBoundary`: the connecting homomorphism attached to a
  connecting morphism of the Mayer–Vietoris triangle.
* `AlgebraicGeometry.Space.edsDerivedHomRestrictionOpen`,
  `AlgebraicGeometry.Space.edsDerivedHomRestrictionEtale` and
  `AlgebraicGeometry.Space.edsDerivedHomBoundary`: those three for an elementary distinguished
  square and the extension by zero `AlgebraicGeometry.Space.etaleModuleLowerShriek`.

## Main results

* `CategoryTheory.Adjunction.mapDerivedCategory_counit_eq`: **the derived form of the counit of
  an adjunction of exact functors is the counit of the derived adjunction.**  This is what turns
  the first map of the sequence into a restriction map; the triangle of Stacks 08GV is built from
  the former and the identification of Stacks 08FJ is built from the latter.
* `CategoryTheory.Adjunction.shiftedHomMapDerivedCategoryEquiv_derivedCounit`: across the
  identification of Stacks 08FJ, precomposition with that counit is the action
  `CategoryTheory.ShiftedHom.map` of derived restriction.
* `CategoryTheory.comparisonShiftedHomMap_map`: a comparison compatible with the counits induces
  restriction to the intersection.
* `CategoryTheory.mayerVietoris_shiftedHom_longExactSequence_restrictions`: for a Mayer–Vietoris
  triangle of three exact adjunctions, the sequence **with those maps** is exact at each of its
  three kinds of spot and in every integer degree.
* `AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedShriekMayerVietoris`: part (2) of
  Stacks 08GV read at the composites of the derived functors, which is the triangle the
  connecting homomorphism comes from.
* `AlgebraicGeometry.Space.edsDerivedHomRestrictionOpen_map` and
  `AlgebraicGeometry.Space.edsDerivedHomRestrictionEtale_map`: each of the two maps out of the
  summands carries the restriction of a morphism of `D(𝒪_X)` to the restriction of that morphism
  to the intersection.

Stacks 08H9 itself is registered on
`AlgebraicGeometry.Space.mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek` of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtTag`, which assembles these.

## Implementation notes

The content of the file is the identification of the counit.  The triangle of Stacks 08GV is
built from `CategoryTheory.NatTrans.mapDerivedCategory` of the degreewise counit, read
through the comparison `CategoryTheory.Functor.mapDerivedCategoryComp` of the derived functor of
a composite and the comparison `CategoryTheory.Functor.mapDerivedCategoryIdIso` for the identity;
the identification of homomorphism groups is built from the counit of
`CategoryTheory.Adjunction.mapDerivedCategory`, the localization of the degreewise adjunction.
That the two agree is proved where a transformation out of a localized category is determined,
namely on the image of `DerivedCategory.Q`: `CategoryTheory.Localization.natTrans_ext` reduces it
to a computation with the three comparisons at a cochain complex, which is then a degreewise
identity.  The two `Q`-formulas that the computation needs,
`CategoryTheory.Functor.mapDerivedCategoryComp_inv_app_Q` and
`CategoryTheory.Functor.mapDerivedCategoryIdIso_hom_app_Q`, are proved here; the second has to
cross from `DerivedCategory.Qh` to `DerivedCategory.Q`, since the comparison for the identity is
a lift along the first, and that crossing goes through
`CategoryTheory.DerivedCategory.quotientCompQhIso` because `Qh` carries `no_expose`.

The two maps out of the summands are *not* produced from a restriction-of-a-restriction functor:
that would need the comparison of the two legs of the square on derived categories to commute
with the shift.  They are produced from the comparisons of the square, and
`AlgebraicGeometry.Space.edsDerivedHomRestrictionOpen_map` is what says that such a comparison
really does restrict — it carries the restriction of `x` to `U` to the restriction of `x` to `P`.

The three geometric maps are given names, and the carrier of the tag mentions those names rather
than their definitions; written out inline they make the statement unreadable, and elaborating
the structure maps of the triangle through a wrapper is what exhausts the heartbeat budget in
this chapter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

attribute [local instance] HasDerivedCategory.standard

section Comparisons

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- The comparison of the derived functor of a composite with the composite of the derived
functors, at an object in the image of the localization. -/
theorem Functor.mapDerivedCategoryComp_inv_app_Q (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategoryComp F G).inv.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
            (ComplexShape.up ℤ)).hom.app K) ≫
        (F ⋙ G).mapDerivedCategoryFactors.inv.app K := by
  rw [Functor.mapDerivedCategoryComp, Localization.liftNatIso_inv,
    Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

/-- The comparison of the derived functor of the identity with the identity, at an object in the
image of the localization. -/
theorem Functor.mapDerivedCategoryIdIso_hom_app_Q (K : CochainComplex C₁ ℤ) :
    (𝟭 C₁).mapDerivedCategoryFactors.inv.app K ≫
        Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app K) := by
  have hQh : Functor.mapDerivedCategoryIdIso.hom.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) =
      (𝟭 C₁).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryIdIso C₁
          (ComplexShape.up ℤ)).hom.app
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) := by
    simp [Functor.mapDerivedCategoryIdIso]
  have hnat := (Functor.mapDerivedCategoryIdIso (C := C₁)).hom.naturality
    ((DerivedCategory.quotientCompQhIso C₁).hom.app K)
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map] at hnat
  rw [hQh, (𝟭 C₁).mapDerivedCategoryFactorsh_hom_app K] at hnat
  simp only [Category.assoc] at hnat
  have hcancel := (cancel_epi ((𝟭 C₁).mapDerivedCategory.map
    ((DerivedCategory.quotientCompQhIso C₁).hom.app K))).1 hnat
  have hkey : ((𝟭 C₁).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K ≫
      (Functor.mapHomotopyCategoryIdIso C₁ (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app K) :=
    Category.id_comp _
  have hnat₂ := (DerivedCategory.quotientCompQhIso C₁).hom.naturality
    ((Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app K)
  dsimp only [Functor.comp_map, Functor.id_obj] at hnat₂
  rw [hcancel, Iso.inv_hom_id_app_assoc,
    ← Category.assoc (DerivedCategory.Qh.map _) (DerivedCategory.Qh.map _),
    ← Functor.map_comp, hkey, hnat₂, Iso.inv_hom_id_app_assoc]

end Comparisons

section Counit

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

omit [HasDerivedCategory C] [HasDerivedCategory D] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
/-- The counit of an adjunction of exact functors, degreewise on cochain complexes, read
through the two comparisons for a composite and for the identity. -/
private theorem counit_mapHomologicalComplex_key (adj : L ⊣ R) (K : CochainComplex D ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ L))
          (ComplexShape.up ℤ)).hom.app K ≫
        (NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexIdIso D (ComplexShape.up ℤ)).hom.app K =
      (adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K := by
  ext i
  simp [Adjunction.mapHomologicalComplex]

/-- **The derived form of the counit of an adjunction of exact functors is the counit of the
derived adjunction.** -/
theorem Adjunction.mapDerivedCategory_counit_eq (adj : L ⊣ R) :
    (Functor.mapDerivedCategoryComp R L).inv ≫
        NatTrans.mapDerivedCategory adj.counit ≫
        Functor.mapDerivedCategoryIdIso.hom =
      (Adjunction.mapDerivedCategory adj).counit := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) fun K => ?_
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.mapDerivedCategoryComp_inv_app_Q,
    NatTrans.mapDerivedCategory_app_Q,
    Adjunction.mapDerivedCategory, Adjunction.localization_counit_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Q, ← Functor.map_comp, ← Functor.map_comp,
    counit_mapHomologicalComplex_key]
  simp only [Iso.symm_inv]

/-- **Across the identification of Stacks 08FJ, precomposition with the counit of the derived
adjunction is the action of derived restriction on shifted morphisms.** -/
theorem Adjunction.shiftedHomMapDerivedCategoryEquiv_counit (adj : L ⊣ R)
    (E F : DerivedCategory D) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    adj.shiftedHomMapDerivedCategoryEquiv (R.mapDerivedCategory.obj E) F n
        ((Adjunction.mapDerivedCategory adj).counit.app E ≫ x) =
      ShiftedHom.map x R.mapDerivedCategory := by
  simp [Adjunction.shiftedHomMapDerivedCategoryEquiv, Stacks.ExtensionByZero.postcompAddEquiv,
    Adjunction.homEquiv_unit, ShiftedHom.map]

/-- The derived counit of an adjunction of exact functors, read at an object: the composite of
the comparison of the derived functor of a composite, the derived form of the counit, and the
comparison of the derived functor of the identity. -/
theorem Adjunction.derivedCounit_app (adj : L ⊣ R) (E : DerivedCategory D) :
    (Functor.mapDerivedCategoryComp R L).inv.app E ≫
        (NatTrans.mapDerivedCategory adj.counit).app E ≫
        Functor.mapDerivedCategoryIdIso.hom.app E =
      (Adjunction.mapDerivedCategory adj).counit.app E := by
  simpa only [NatTrans.comp_app] using
    NatTrans.congr_app (Adjunction.mapDerivedCategory_counit_eq adj) E

/-- **The restriction map of the Mayer–Vietoris sequence is the action of derived restriction on
shifted morphisms.** -/
theorem Adjunction.shiftedHomMapDerivedCategoryEquiv_derivedCounit (adj : L ⊣ R)
    (E F : DerivedCategory D) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    adj.shiftedHomMapDerivedCategoryEquiv (R.mapDerivedCategory.obj E) F n
        ((Functor.mapDerivedCategoryComp R L).inv.app E ≫
          (NatTrans.mapDerivedCategory adj.counit).app E ≫
          Functor.mapDerivedCategoryIdIso.hom.app E ≫ x) =
      ShiftedHom.map x R.mapDerivedCategory := by
  have h := adj.shiftedHomMapDerivedCategoryEquiv_counit E F n x
  rwa [← Adjunction.derivedCounit_app adj E, Category.assoc, Category.assoc] at h

/-- The inverse form of `Adjunction.shiftedHomMapDerivedCategoryEquiv_derivedCounit`. -/
theorem Adjunction.shiftedHomMapDerivedCategoryEquiv_symm_map (adj : L ⊣ R)
    (E F : DerivedCategory D) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    (adj.shiftedHomMapDerivedCategoryEquiv (R.mapDerivedCategory.obj E) F n).symm
        (ShiftedHom.map x R.mapDerivedCategory) =
      (Functor.mapDerivedCategoryComp R L).inv.app E ≫
        (NatTrans.mapDerivedCategory adj.counit).app E ≫
        Functor.mapDerivedCategoryIdIso.hom.app E ≫ x :=
  (AddEquiv.symm_apply_eq _).2
    (adj.shiftedHomMapDerivedCategoryEquiv_derivedCounit E F n x).symm

end Counit

section Factor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {CP : Type u₃} [Category.{v₃} CP] [Abelian CP] [HasDerivedCategory.{w₃} CP]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  {LP : CP ⥤ D} {RP : D ⥤ CP} [LP.Additive] [PreservesFiniteLimits LP]
  [PreservesFiniteColimits LP] [RP.Additive] [PreservesFiniteLimits RP]
  [PreservesFiniteColimits RP]

/-- **A comparison of left adjoints compatible with the counits stays compatible with the
derived counits.** -/
theorem derivedComparison_comp_derivedCounit (adj : L ⊣ R) (adjP : LP ⊣ RP)
    (c : RP ⋙ LP ⟶ R ⋙ L) (hc : c ≫ adj.counit = adjP.counit) :
    ((Functor.mapDerivedCategoryComp RP LP).inv ≫ NatTrans.mapDerivedCategory c ≫
          (Functor.mapDerivedCategoryComp R L).hom) ≫
        ((Functor.mapDerivedCategoryComp R L).inv ≫
          NatTrans.mapDerivedCategory adj.counit ≫
          Functor.mapDerivedCategoryIdIso.hom) =
      (Functor.mapDerivedCategoryComp RP LP).inv ≫
        NatTrans.mapDerivedCategory adjP.counit ≫
        Functor.mapDerivedCategoryIdIso.hom := by
  rw [← hc, NatTrans.mapDerivedCategory_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **The map out of the intersection term is the restriction to the intersection, on the
restrictions of a morphism of the ambient derived category.** -/
theorem shiftedHomMapDerivedCategoryEquiv_comparison (adj : L ⊣ R) (adjP : LP ⊣ RP)
    (c : RP ⋙ LP ⟶ R ⋙ L) (hc : c ≫ adj.counit = adjP.counit)
    (E F : DerivedCategory D) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    adjP.shiftedHomMapDerivedCategoryEquiv (RP.mapDerivedCategory.obj E) F n
        (((Functor.mapDerivedCategoryComp RP LP).inv.app E ≫
            (NatTrans.mapDerivedCategory c).app E ≫
            (Functor.mapDerivedCategoryComp R L).hom.app E) ≫
          (adj.shiftedHomMapDerivedCategoryEquiv (R.mapDerivedCategory.obj E) F n).symm
            (ShiftedHom.map x R.mapDerivedCategory)) =
      ShiftedHom.map x RP.mapDerivedCategory := by
  have h := NatTrans.congr_app (derivedComparison_comp_derivedCounit adj adjP c hc) E
  simp only [NatTrans.comp_app] at h
  rw [adj.shiftedHomMapDerivedCategoryEquiv_symm_map E F n x,
    ← adjP.shiftedHomMapDerivedCategoryEquiv_derivedCounit E F n x]
  congr 1
  simpa only [Category.assoc] using h =≫ x

end Factor

section Sequence

variable {AX : Type*} [Category* AX] [Abelian AX] [HasDerivedCategory AX]
  {AU : Type*} [Category* AU] [Abelian AU] [HasDerivedCategory AU]
  {AV : Type*} [Category* AV] [Abelian AV] [HasDerivedCategory AV]
  {AP : Type*} [Category* AP] [Abelian AP] [HasDerivedCategory AP]
  {rU : AX ⥤ AU} {shriekU : AU ⥤ AX} {rV : AX ⥤ AV} {shriekV : AV ⥤ AX}
  {rP : AX ⥤ AP} {shriekP : AP ⥤ AX}
  [rU.Additive] [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]
  [rV.Additive] [PreservesFiniteLimits rV] [PreservesFiniteColimits rV]
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]
  [rP.Additive] [PreservesFiniteLimits rP] [PreservesFiniteColimits rP]
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]

/-- Exactness is transported along three additive equivalences described pointwise. -/
private theorem exact_of_conj_addEquiv {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*}
    [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    [AddCommGroup Y₁] [AddCommGroup Y₂] [AddCommGroup Y₃]
    (e₁ : X₁ ≃+ Y₁) (e₂ : X₂ ≃+ Y₂) (e₃ : X₃ ≃+ Y₃)
    {g₁₂ : Y₁ →+ Y₂} {g₂₃ : Y₂ →+ Y₃} (H : Function.Exact g₁₂ g₂₃)
    {f₁₂ : X₁ → X₂} {f₂₃ : X₂ → X₃}
    (h₁₂ : ∀ x, g₁₂ (e₁ x) = e₂ (f₁₂ x)) (h₂₃ : ∀ x, g₂₃ (e₂ x) = e₃ (f₂₃ x)) :
    Function.Exact f₁₂ f₂₃ := by
  have hf₁₂ : f₁₂ = ⇑(e₂.symm.toAddMonoidHom.comp (g₁₂.comp e₁.toAddMonoidHom)) :=
    funext fun x => by simp [h₁₂]
  have hf₂₃ : f₂₃ = ⇑(e₃.symm.toAddMonoidHom.comp (g₂₃.comp e₂.toAddMonoidHom)) :=
    funext fun x => by simp [h₂₃]
  rw [hf₁₂, hf₂₃]
  exact Function.Exact.of_ladder_addEquiv_of_exact' e₁ e₂ e₃
    (AddMonoidHom.ext fun x => by simp) (AddMonoidHom.ext fun x => by simp) H

/-- **The pair of the two derived restrictions of a shifted morphism corresponds, under the two
identifications of Stacks 08FJ, to the pair of its composites with the two derived counits**:
the first map of the Mayer–Vietoris sequence is the pair of the two restrictions. -/
private theorem shiftedHomRestriction_eq_restrictions (adjU : shriekU ⊣ rU) (adjV : shriekV ⊣ rV)
    (E F : DerivedCategory AX) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    shiftedHomRestriction
        ((Functor.mapDerivedCategoryComp rU shriekU).inv.app E ≫
          (NatTrans.mapDerivedCategory adjU.counit).app E ≫
          Functor.mapDerivedCategoryIdIso.hom.app E)
        ((Functor.mapDerivedCategoryComp rV shriekV).inv.app E ≫
          (NatTrans.mapDerivedCategory adjV.counit).app E ≫
          Functor.mapDerivedCategoryIdIso.hom.app E) F n x =
      ((adjU.shiftedHomMapDerivedCategoryEquiv (rU.mapDerivedCategory.obj E) F n).symm
          (ShiftedHom.map x rU.mapDerivedCategory),
        (adjV.shiftedHomMapDerivedCategoryEquiv (rV.mapDerivedCategory.obj E) F n).symm
          (ShiftedHom.map x rV.mapDerivedCategory)) := by
  rw [shiftedHomRestriction_apply, adjU.shiftedHomMapDerivedCategoryEquiv_symm_map E F n x,
    adjV.shiftedHomMapDerivedCategoryEquiv_symm_map E F n x]
  simp only [Category.assoc]

/-- **The Mayer–Vietoris combination of the two derived comparisons corresponds, under the
identifications of Stacks 08FJ, to the difference of the two maps they induce**: the second map
of the Mayer–Vietoris sequence is that difference. -/
private theorem shiftedHomDifference_eq_sub (adjU : shriekU ⊣ rU) (adjV : shriekV ⊣ rV)
    (adjP : shriekP ⊣ rP) (cO : rP ⋙ shriekP ⟶ rU ⋙ shriekU)
    (cE : rP ⋙ shriekP ⟶ rV ⋙ shriekV) (E F : DerivedCategory AX) (n : ℤ)
    (w : (rU.mapDerivedCategory.obj E ⟶ (rU.mapDerivedCategory.obj F)⟦n⟧) ×
      (rV.mapDerivedCategory.obj E ⟶ (rV.mapDerivedCategory.obj F)⟦n⟧)) :
    shiftedHomDifference
        ((Functor.mapDerivedCategoryComp rP shriekP).inv.app E ≫
          (NatTrans.mapDerivedCategory cO).app E ≫
          (Functor.mapDerivedCategoryComp rU shriekU).hom.app E)
        (-((Functor.mapDerivedCategoryComp rP shriekP).inv.app E ≫
          (NatTrans.mapDerivedCategory cE).app E ≫
          (Functor.mapDerivedCategoryComp rV shriekV).hom.app E)) F n
        ((adjU.shiftedHomMapDerivedCategoryEquiv (rU.mapDerivedCategory.obj E) F n).symm w.1,
          (adjV.shiftedHomMapDerivedCategoryEquiv (rV.mapDerivedCategory.obj E) F n).symm w.2) =
      (adjP.shiftedHomMapDerivedCategoryEquiv (rP.mapDerivedCategory.obj E) F n).symm
        ((adjP.shiftedHomMapDerivedCategoryEquiv (rP.mapDerivedCategory.obj E) F n)
            (((Functor.mapDerivedCategoryComp rP shriekP).inv.app E ≫
                (NatTrans.mapDerivedCategory cO).app E ≫
                (Functor.mapDerivedCategoryComp rU shriekU).hom.app E) ≫
              (adjU.shiftedHomMapDerivedCategoryEquiv
                (rU.mapDerivedCategory.obj E) F n).symm w.1) -
          (adjP.shiftedHomMapDerivedCategoryEquiv (rP.mapDerivedCategory.obj E) F n)
            (((Functor.mapDerivedCategoryComp rP shriekP).inv.app E ≫
                (NatTrans.mapDerivedCategory cE).app E ≫
                (Functor.mapDerivedCategoryComp rV shriekV).hom.app E) ≫
              (adjV.shiftedHomMapDerivedCategoryEquiv
                (rV.mapDerivedCategory.obj E) F n).symm w.2)) := by
  rw [map_sub, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, shiftedHomDifference_apply,
    Preadditive.neg_comp, ← sub_eq_add_neg]

/-- **The map on shifted morphism groups induced by a comparison of extensions by zero.**  For a
natural transformation `c : j_{P!}((-)|_P) ⟶ j_{U!}((-)|_U)`, this is the map
`Ext^n(E|_U, F|_U) ⟶ Ext^n(E|_P, F|_P)` obtained by precomposing with the derived form of `c`,
read through the two identifications of Stacks 08FJ.  When `c` is compatible with the counits
it carries the restriction of a morphism of `D(𝒪_X)` to `U` to its restriction to `P`, by
`CategoryTheory.comparisonShiftedHomMap_map`. -/
def comparisonShiftedHomMap (adjU : shriekU ⊣ rU) (adjP : shriekP ⊣ rP)
    (c : rP ⋙ shriekP ⟶ rU ⋙ shriekU) (E F : DerivedCategory AX) (n : ℤ) :
    (rU.mapDerivedCategory.obj E ⟶ (rU.mapDerivedCategory.obj F)⟦n⟧) →+
      (rP.mapDerivedCategory.obj E ⟶ (rP.mapDerivedCategory.obj F)⟦n⟧) :=
  (adjP.shiftedHomMapDerivedCategoryEquiv (rP.mapDerivedCategory.obj E) F n).toAddMonoidHom.comp
    ((shiftedHomPrecomp ((Functor.mapDerivedCategoryComp rP shriekP).inv.app E ≫
        (NatTrans.mapDerivedCategory c).app E ≫
        (Functor.mapDerivedCategoryComp rU shriekU).hom.app E) F n).comp
      (adjU.shiftedHomMapDerivedCategoryEquiv
        (rU.mapDerivedCategory.obj E) F n).symm.toAddMonoidHom)

/-- **A comparison compatible with the counits induces restriction to the intersection.**  The
map of `CategoryTheory.comparisonShiftedHomMap` carries the restriction of `x : E ⟶ F⟦n⟧` to `U`
to the restriction of `x` to `P`. -/
theorem comparisonShiftedHomMap_map (adjU : shriekU ⊣ rU) (adjP : shriekP ⊣ rP)
    (c : rP ⋙ shriekP ⟶ rU ⋙ shriekU) (hc : c ≫ adjU.counit = adjP.counit)
    (E F : DerivedCategory AX) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    comparisonShiftedHomMap adjU adjP c E F n (ShiftedHom.map x rU.mapDerivedCategory) =
      ShiftedHom.map x rP.mapDerivedCategory :=
  shiftedHomMapDerivedCategoryEquiv_comparison adjU adjP c hc E F n x

/-- **The connecting homomorphism of the Mayer–Vietoris sequence of a triangle.**  It is
composition with the third map `δ` of the Mayer–Vietoris triangle, read through the
identification of Stacks 08FJ over the intersection. -/
def mayerVietorisShiftedHomBoundary (adjU : shriekU ⊣ rU) (adjV : shriekV ⊣ rV)
    (adjP : shriekP ⊣ rP) (cO : rP ⋙ shriekP ⟶ rU ⋙ shriekU)
    (cE : rP ⋙ shriekP ⟶ rV ⋙ shriekV) (E F : DerivedCategory AX)
    (δ : E ⟶ (shriekP.mapDerivedCategory.obj (rP.mapDerivedCategory.obj E))⟦(1 : ℤ)⟧) (n : ℤ) :
    (rP.mapDerivedCategory.obj E ⟶ (rP.mapDerivedCategory.obj F)⟦n⟧) →+ (E ⟶ F⟦n + 1⟧) :=
  (biprodTriangleShiftedHomδ
      ((Functor.mapDerivedCategoryComp rP shriekP).inv.app E ≫
        (NatTrans.mapDerivedCategory cO).app E ≫
        (Functor.mapDerivedCategoryComp rU shriekU).hom.app E)
      (-((Functor.mapDerivedCategoryComp rP shriekP).inv.app E ≫
        (NatTrans.mapDerivedCategory cE).app E ≫
        (Functor.mapDerivedCategoryComp rV shriekV).hom.app E))
      ((Functor.mapDerivedCategoryComp rU shriekU).inv.app E ≫
        (NatTrans.mapDerivedCategory adjU.counit).app E ≫
        Functor.mapDerivedCategoryIdIso.hom.app E)
      ((Functor.mapDerivedCategoryComp rV shriekV).inv.app E ≫
        (NatTrans.mapDerivedCategory adjV.counit).app E ≫
        Functor.mapDerivedCategoryIdIso.hom.app E) δ F n (n + 1) rfl).comp
    (adjP.shiftedHomMapDerivedCategoryEquiv
      (rP.mapDerivedCategory.obj E) F n).symm.toAddMonoidHom

/-- **The connecting homomorphism is composition with `δ`.** -/
theorem mayerVietorisShiftedHomBoundary_apply (adjU : shriekU ⊣ rU) (adjV : shriekV ⊣ rV)
    (adjP : shriekP ⊣ rP) (cO : rP ⋙ shriekP ⟶ rU ⋙ shriekU)
    (cE : rP ⋙ shriekP ⟶ rV ⋙ shriekV) (E F : DerivedCategory AX)
    (δ : E ⟶ (shriekP.mapDerivedCategory.obj (rP.mapDerivedCategory.obj E))⟦(1 : ℤ)⟧) (n : ℤ)
    (z : rP.mapDerivedCategory.obj E ⟶ (rP.mapDerivedCategory.obj F)⟦n⟧) :
    mayerVietorisShiftedHomBoundary adjU adjV adjP cO cE E F δ n z =
      δ ≫ ((adjP.shiftedHomMapDerivedCategoryEquiv
            (rP.mapDerivedCategory.obj E) F n).symm z)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory AX) n 1 (n + 1) rfl).inv.app F :=
  biprodTriangleShiftedHomδ_apply _ _ _ _ δ F n (n + 1) rfl _

/-- **The Mayer–Vietoris long exact sequence of a triangle of three exact adjunctions, with its
maps.**  The first map of the sequence is the pair of the actions of the two derived restrictions
on shifted morphisms; the second is the difference of two maps into the shifted morphisms over
the intersection, each of which carries the restriction of a morphism of the ambient derived
category to its restriction to the intersection; and the connecting map is the one attached to
the given triangle. -/
theorem mayerVietoris_shiftedHom_longExactSequence_restrictions
    (adjU : shriekU ⊣ rU) (adjV : shriekV ⊣ rV) (adjP : shriekP ⊣ rP)
    (cO : rP ⋙ shriekP ⟶ rU ⋙ shriekU) (cE : rP ⋙ shriekP ⟶ rV ⋙ shriekV)
    (_hcO : cO ≫ adjU.counit = adjP.counit) (_hcE : cE ≫ adjV.counit = adjP.counit)
    (E F : DerivedCategory AX)
    (δ : E ⟶ (shriekP.mapDerivedCategory.obj (rP.mapDerivedCategory.obj E))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
        (biprod.lift
          ((Functor.mapDerivedCategoryComp rP shriekP).inv.app E ≫
            (NatTrans.mapDerivedCategory cO).app E ≫
            (Functor.mapDerivedCategoryComp rU shriekU).hom.app E)
          (-((Functor.mapDerivedCategoryComp rP shriekP).inv.app E ≫
            (NatTrans.mapDerivedCategory cE).app E ≫
            (Functor.mapDerivedCategoryComp rV shriekV).hom.app E)))
        (biprod.desc
          ((Functor.mapDerivedCategoryComp rU shriekU).inv.app E ≫
            (NatTrans.mapDerivedCategory adjU.counit).app E ≫
            Functor.mapDerivedCategoryIdIso.hom.app E)
          ((Functor.mapDerivedCategoryComp rV shriekV).inv.app E ≫
            (NatTrans.mapDerivedCategory adjV.counit).app E ≫
            Functor.mapDerivedCategoryIdIso.hom.app E)) δ ∈
      distTriang (DerivedCategory AX)) (n : ℤ) :
    Function.Exact
        (fun x : E ⟶ F⟦n⟧ =>
          (ShiftedHom.map x rU.mapDerivedCategory, ShiftedHom.map x rV.mapDerivedCategory))
        (fun w => comparisonShiftedHomMap adjU adjP cO E F n w.1 -
          comparisonShiftedHomMap adjV adjP cE E F n w.2) ∧
      Function.Exact
        (fun w : (rU.mapDerivedCategory.obj E ⟶ (rU.mapDerivedCategory.obj F)⟦n⟧) ×
            (rV.mapDerivedCategory.obj E ⟶ (rV.mapDerivedCategory.obj F)⟦n⟧) =>
          comparisonShiftedHomMap adjU adjP cO E F n w.1 -
            comparisonShiftedHomMap adjV adjP cE E F n w.2)
        (mayerVietorisShiftedHomBoundary adjU adjV adjP cO cE E F δ n) ∧
      Function.Exact (mayerVietorisShiftedHomBoundary adjU adjV adjP cO cE E F δ n)
        (fun x : E ⟶ F⟦n + 1⟧ =>
          (ShiftedHom.map x rU.mapDerivedCategory, ShiftedHom.map x rV.mapDerivedCategory)) := by
  let eUV (m : ℤ) := (AddEquiv.prodCongr
    (adjU.shiftedHomMapDerivedCategoryEquiv (rU.mapDerivedCategory.obj E) F m)
    (adjV.shiftedHomMapDerivedCategoryEquiv (rV.mapDerivedCategory.obj E) F m)).symm
  let eP := (adjP.shiftedHomMapDerivedCategoryEquiv (rP.mapDerivedCategory.obj E) F n).symm
  refine ⟨?_, ?_, ?_⟩
  · exact exact_of_conj_addEquiv (AddEquiv.refl (E ⟶ F⟦n⟧)) (eUV n) eP
      (exact_shiftedHomRestriction_shiftedHomDifference _ _ _ _ δ hT F n)
      (shiftedHomRestriction_eq_restrictions adjU adjV E F n)
      (shiftedHomDifference_eq_sub adjU adjV adjP cO cE E F n)
  · exact exact_of_conj_addEquiv (eUV n) eP (AddEquiv.refl (E ⟶ F⟦n + 1⟧))
      (exact_shiftedHomDifference_biprodTriangleShiftedHomδ _ _ _ _ δ hT F n (n + 1) rfl)
      (shiftedHomDifference_eq_sub adjU adjV adjP cO cE E F n) (fun z => rfl)
  · exact exact_of_conj_addEquiv eP (AddEquiv.refl (E ⟶ F⟦n + 1⟧)) (eUV (n + 1))
      (exact_biprodTriangleShiftedHomδ_shiftedHomRestriction _ _ _ _ δ hT F n (n + 1) rfl)
      (fun z => rfl) (shiftedHomRestriction_eq_restrictions adjU adjV E F (n + 1))

end Sequence

end CategoryTheory

namespace AlgebraicGeometry.Space

open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

section Data

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]
include adjU adjV adjP in
/-- **The Mayer–Vietoris distinguished triangle of part (2) of Stacks 08GV, read at the
composites of the derived functors.**  Its first map is the pair of the derived forms of the two
comparisons of the square, and its second the sum of the two derived adjunction counits. -/
theorem exists_mem_distTriang_edsDerivedShriekMayerVietoris
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ δ : E ⟶ (shriekP.mapDerivedCategory.obj
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E))⟦(1 : ℤ)⟧,
      Triangle.mk
          (biprod.lift
            ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                  (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)) shriekP).inv.app E ≫
              (NatTrans.mapDerivedCategory
                (edsShriekOpenComparison B S hS hsq adjU adjP)).app E ≫
              (Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)) shriekU).hom.app E)
            (-((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                  (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)) shriekP).inv.app E ≫
              (NatTrans.mapDerivedCategory
                (edsShriekEtaleComparison B S hS hsq adjV adjP)).app E ≫
              (Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) shriekV).hom.app E)))
          (biprod.desc
            ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                  (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)) shriekU).inv.app E ≫
              (NatTrans.mapDerivedCategory adjU.counit).app E ≫
              Functor.mapDerivedCategoryIdIso.hom.app E)
            ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                  (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) shriekV).inv.app E ≫
              (NatTrans.mapDerivedCategory adjV.counit).app E ≫
              Functor.mapDerivedCategoryIdIso.hom.app E)) δ ∈
        distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) := by
  obtain ⟨δ₀, hδ₀⟩ := mem_distTriang_mayerVietoris B S hS hsq adjU adjV
    (edsShriekOpenComparison B S hS hsq adjU adjP)
    (edsShriekEtaleComparison B S hS hsq adjV adjP)
    (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP)
    (shortExact_edsShriekMayerVietoris B S hS hsq adjU adjV adjP) E
  have hT := mem_distTriang_biprod_of_iso
    ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
      (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)) shriekP).app E)
    ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)) shriekU).app E)
    ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) shriekV).app E)
    _ _ _ _ _ δ₀ hδ₀
  simp only [Iso.app_inv, Iso.app_hom, Preadditive.neg_comp, Preadditive.comp_neg] at hT
  exact ⟨_, hT⟩

end Data

section LowerShriek

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  (E F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))

/-- **Restriction to the intersection of an elementary distinguished square, out of its open
subspace, on shifted homomorphism groups.**  It is `CategoryTheory.comparisonShiftedHomMap` at
the comparison `AlgebraicGeometry.Space.edsShriekOpenComparison` attached to the factorization of
the morphism from the intersection through the open subspace, for the extension by zero
`AlgebraicGeometry.Space.etaleModuleLowerShriek`.  It carries the restriction to `U` of a
morphism of `D(𝒪_X)` to the restriction of that morphism to `P`, by
`AlgebraicGeometry.Space.edsDerivedHomRestrictionOpen_map`. -/
def edsDerivedHomRestrictionOpen (n : ℤ) :
    ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E ⟶
        ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) →+
      ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) :=
  comparisonShiftedHomMap
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    (edsShriekOpenComparison B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq))) E F n

/-- **Restriction to the intersection of an elementary distinguished square, out of its étale
algebraic space, on shifted homomorphism groups.**  It is
`CategoryTheory.comparisonShiftedHomMap` at the comparison
`AlgebraicGeometry.Space.edsShriekEtaleComparison` attached to the factorization of the morphism
from the intersection through the étale algebraic space.  It carries the restriction to `V` of a
morphism of `D(𝒪_X)` to the restriction of that morphism to `P`, by
`AlgebraicGeometry.Space.edsDerivedHomRestrictionEtale_map`. -/
def edsDerivedHomRestrictionEtale (n : ℤ) :
    ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E ⟶
        ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) →+
      ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) :=
  comparisonShiftedHomMap
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    (edsShriekEtaleComparison B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq))) E F n

/-- **The connecting homomorphism of the Mayer–Vietoris sequence of an elementary distinguished
square**, attached to a connecting morphism `δ` of the Mayer–Vietoris triangle of part (2) of
Stacks 08GV: composition with `δ`, read through the identification of Stacks 08FJ over the
intersection.  See `AlgebraicGeometry.Space.edsDerivedHomBoundary_apply`. -/
def edsDerivedHomBoundary
    (δ : E ⟶ ((etaleModuleLowerShriek B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E))⟦(1 : ℤ)⟧) (n : ℤ) :
    ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) →+
      (E ⟶ F⟦n + 1⟧) :=
  mayerVietorisShiftedHomBoundary
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    (edsShriekOpenComparison B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)))
    (edsShriekEtaleComparison B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq))) E F δ n

/-- **The map out of the open subspace is restriction to the intersection**: it carries the
restriction to `U` of a morphism of `D(𝒪_X)` to the restriction of that morphism to `P`. -/
theorem edsDerivedHomRestrictionOpen_map (n : ℤ) (x : E ⟶ F⟦n⟧) :
    edsDerivedHomRestrictionOpen B S hS hsq E F n
        (ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory) =
      ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory :=
  comparisonShiftedHomMap_map _ _ _
    (edsShriekOpenComparison_comp_counit B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq))) E F n x

/-- **The map out of the étale algebraic space is restriction to the intersection**: it carries
the restriction to `V` of a morphism of `D(𝒪_X)` to the restriction of that morphism to `P`. -/
theorem edsDerivedHomRestrictionEtale_map (n : ℤ) (x : E ⟶ F⟦n⟧) :
    edsDerivedHomRestrictionEtale B S hS hsq E F n
        (ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory) =
      ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory :=
  comparisonShiftedHomMap_map _ _ _
    (edsShriekEtaleComparison_comp_counit B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq))) E F n x

/-- **The connecting homomorphism is composition with `δ`.** -/
theorem edsDerivedHomBoundary_apply
    (δ : E ⟶ ((etaleModuleLowerShriek B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E))⟦(1 : ℤ)⟧) (n : ℤ)
    (z : (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
      ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) :
    edsDerivedHomBoundary B S hS hsq E F δ n z =
      δ ≫ (((etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).shiftedHomMapDerivedCategoryEquiv
            ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E) F n).symm
          z)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
          n 1 (n + 1) rfl).inv.app F :=
  mayerVietorisShiftedHomBoundary_apply _ _ _ _ _ E F δ n z

end LowerShriek

end AlgebraicGeometry.Space

end
