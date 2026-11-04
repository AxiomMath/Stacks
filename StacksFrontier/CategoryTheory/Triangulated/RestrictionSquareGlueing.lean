module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Glueing along a square of restriction functors, and its transport

Let `r_U : D_X ⥤ D_U`, `r_V : D_X ⥤ D_V`, `r_{UP} : D_U ⥤ D_P`, `r_{VP} : D_V ⥤ D_P` be functors
with an isomorphism `κ : r_U ⋙ r_{UP} ≅ r_V ⋙ r_{VP}`: the restrictions to the pieces of an
elementary distinguished square `(U ⊆ X, V ⟶ X)` and to their intersection `P` (Stacks 08HB). This
file isolates the three properties of such a square that the gluing of objects along it uses, and
proves that they are carried along equivalences compatible with the restrictions, and that the
three of them glue objects over a limit from a stage.

## Main definitions

* `CategoryTheory.RestrictionSquare.HomsGlue`: a pair of morphisms of restrictions agreeing on `P`
  is the pair of restrictions of a morphism.
* `CategoryTheory.RestrictionSquare.ObjectsGlue`: objects on `U` and `V` with an isomorphism of
  their restrictions to `P` are the restrictions of an object (the first assertion of 08HB).
* `CategoryTheory.RestrictionSquare.ReflectsIso`: a morphism whose restrictions to `U` and `V` are
  isomorphisms is one.

## Main results

* `CategoryTheory.RestrictionSquare.HomsGlue.transport`, `…ObjectsGlue.transport`,
  `…ReflectsIso.transport`: the three properties transported along equivalences.
* `CategoryTheory.RestrictionSquare.reflectsIso_of_isZero`: for triangulated restrictions, it
  suffices that an object restricting to zero on `U` and on `V` is zero.
* `CategoryTheory.RestrictionSquare.exists_iso_of_objectsGlue_of_homsGlue`: an object over the
  limit whose restrictions to `U` and `V` come from a stage, compatibly over `P`, comes from the
  stage (the step of Stacks 09RJ across an elementary distinguished square).

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace CategoryTheory.RestrictionSquare

variable {DX : Type u₁} [Category.{v₁} DX] {DU : Type u₂} [Category.{v₂} DU]
  {DV : Type u₃} [Category.{v₃} DV] {DP : Type u₄} [Category.{v₄} DP]
  (rU : DX ⥤ DU) (rV : DX ⥤ DV) (rUP : DU ⥤ DP) (rVP : DV ⥤ DP)
  (κ : rU ⋙ rUP ≅ rV ⋙ rVP)

/-- **Morphisms glue along the square**: morphisms `φ_U : r_U F ⟶ r_U E`, `φ_V : r_V F ⟶ r_V E`
whose restrictions to `P` agree through `κ` are the restrictions of a morphism `F ⟶ E`. -/
def HomsGlue : Prop :=
  ∀ ⦃F E : DX⦄ (φU : rU.obj F ⟶ rU.obj E) (φV : rV.obj F ⟶ rV.obj E),
    rUP.map φU ≫ κ.hom.app E = κ.hom.app F ≫ rVP.map φV →
      ∃ φ : F ⟶ E, rU.map φ = φU ∧ rV.map φ = φV

/-- **Objects glue along the square** (the first assertion of Stacks 08HB): for objects `A` on
`U`, `Bo` on `V` and an isomorphism `c : r_{UP} A ≅ r_{VP} Bo`, there are an object `F` and
isomorphisms `f : r_U F ≅ A`, `g : r_V F ≅ Bo` with `c = r_{VP} g ∘ κ_F ∘ r_{UP} f⁻¹`. -/
def ObjectsGlue : Prop :=
  ∀ (A : DU) (Bo : DV) (c : rUP.obj A ≅ rVP.obj Bo),
    ∃ (F : DX) (f : rU.obj F ≅ A) (g : rV.obj F ≅ Bo),
      c.hom = rUP.map f.inv ≫ κ.hom.app F ≫ rVP.map g.hom

/-- **The restrictions to `U` and `V` jointly reflect isomorphisms.** -/
def ReflectsIso : Prop :=
  ∀ ⦃F E : DX⦄ (φ : F ⟶ E), IsIso (rU.map φ) → IsIso (rV.map φ) → IsIso φ

section Transport

variable {rU rV rUP rVP κ}
variable {DX' : Type u₅} [Category.{v₅} DX'] {DU' : Type u₆} [Category.{v₆} DU']
  {DV' : Type u₇} [Category.{v₇} DV'] {DP' : Type u₈} [Category.{v₈} DP']
  {rU' : DX' ⥤ DU'} {rV' : DX' ⥤ DV'} {rUP' : DU' ⥤ DP'} {rVP' : DV' ⥤ DP'}
  {κ' : rU' ⋙ rUP' ≅ rV' ⋙ rVP'}
  {eX : DX ⥤ DX'} {eU : DU ⥤ DU'} {eV : DV ⥤ DV'} {eP : DP ⥤ DP'}
  {TU : rU ⋙ eU ≅ eX ⋙ rU'} {TV : rV ⋙ eV ≅ eX ⋙ rV'}
  {TUP : rUP ⋙ eP ≅ eU ⋙ rUP'} {TVP : rVP ⋙ eP ≅ eV ⋙ rVP'}

/-- The compatibility of the comparisons with `κ` and `κ'`, which every transport below uses:
`eP κ_F` followed by the comparisons on the `V`-side is the comparisons on the `U`-side followed
by `κ'`. -/
abbrev Coherent (κ : rU ⋙ rUP ≅ rV ⋙ rVP) (κ' : rU' ⋙ rUP' ≅ rV' ⋙ rVP')
    (TU : rU ⋙ eU ≅ eX ⋙ rU') (TV : rV ⋙ eV ≅ eX ⋙ rV')
    (TUP : rUP ⋙ eP ≅ eU ⋙ rUP') (TVP : rVP ⋙ eP ≅ eV ⋙ rVP') : Prop :=
  ∀ F : DX, eP.map (κ.hom.app F) ≫ TVP.hom.app (rV.obj F) ≫ rVP'.map (TV.hom.app F) =
    TUP.hom.app (rU.obj F) ≫ rUP'.map (TU.hom.app F) ≫ κ'.hom.app (eX.obj F)

private theorem map_hom_inv_app_assoc {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂]
    {C₃ : Type*} [Category* C₃] {F₁ F₂ : C₁ ⥤ C₂} (G : C₂ ⥤ C₃) (α : F₁ ≅ F₂) (X : C₁)
    {Z : C₃} (h : G.obj (F₁.obj X) ⟶ Z) : G.map (α.hom.app X) ≫ G.map (α.inv.app X) ≫ h = h := by
  rw [← G.map_comp_assoc, Iso.hom_inv_id_app, G.map_id, Category.id_comp]

private theorem map_inv_hom_app_assoc {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂]
    {C₃ : Type*} [Category* C₃] {F₁ F₂ : C₁ ⥤ C₂} (G : C₂ ⥤ C₃) (α : F₁ ≅ F₂) (X : C₁)
    {Z : C₃} (h : G.obj (F₂.obj X) ⟶ Z) : G.map (α.inv.app X) ≫ G.map (α.hom.app X) ≫ h = h := by
  rw [← G.map_comp_assoc, Iso.inv_hom_id_app, G.map_id, Category.id_comp]

private theorem map_map_inv_hom_assoc {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂]
    {C₃ : Type*} [Category* C₃] (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₂) {X Y : C₁} (ι : X ≅ Y)
    {Z : C₃} (h : G.obj (H.obj Y) ⟶ Z) : G.map (H.map ι.inv) ≫ G.map (H.map ι.hom) ≫ h = h := by
  rw [← G.map_comp_assoc, ← H.map_comp, Iso.inv_hom_id, H.map_id, G.map_id, Category.id_comp]

/-- If the comparisons are compatible with `κ` and `κ'`, then the component of `κ'` at `eX.obj F`
is the composite of the inverses of the comparisons over `U`, the image of `κ` under `eP`, and
the comparisons over `V`. -/
theorem Coherent.inv_eq (h : Coherent (eX := eX) κ κ' TU TV TUP TVP) (F : DX) :
    κ'.hom.app (eX.obj F) = rUP'.map (TU.inv.app F) ≫ TUP.inv.app (rU.obj F) ≫
      eP.map (κ.hom.app F) ≫ TVP.hom.app (rV.obj F) ≫ rVP'.map (TV.hom.app F) := by
  rw [h F, Iso.inv_hom_id_app_assoc, map_inv_hom_app_assoc]

/-- **The coherence of the comparisons from their coherence with composites.** If `κ` and `κ'`
are composites `c₁ ≫ C ≫ c₂⁻¹` and `s₁ ≫ C' ≫ s₂⁻¹` of identifications `c_•`, `s_•` of the iterated
restrictions with restrictions `R_•`, `R'_•` and identifications `C : R₁ ≅ R₂`, `C' : R₁' ≅ R₂'`,
and the comparisons `T₁`, `T₂` of `R_•` with `R'_•` are compatible with `c_•`, `s_•` and with
`C`, `C'`, then the comparisons are compatible with `κ` and `κ'`. -/
theorem Coherent.of_comp {R₁ R₂ : DX ⥤ DP} {R₁' R₂' : DX' ⥤ DP'}
    (c₁ : rU ⋙ rUP ≅ R₁) (c₂ : rV ⋙ rVP ≅ R₂) (C : R₁ ≅ R₂)
    (s₁ : rU' ⋙ rUP' ≅ R₁') (s₂ : rV' ⋙ rVP' ≅ R₂') (C' : R₁' ≅ R₂')
    (T₁ : R₁ ⋙ eP ≅ eX ⋙ R₁') (T₂ : R₂ ⋙ eP ≅ eX ⋙ R₂')
    (hκ : ∀ F, κ.hom.app F = c₁.hom.app F ≫ C.hom.app F ≫ c₂.inv.app F)
    (hκ' : ∀ F, κ'.hom.app F = s₁.hom.app F ≫ C'.hom.app F ≫ s₂.inv.app F)
    (h₁ : ∀ F, eP.map (c₁.hom.app F) ≫ T₁.hom.app F =
      TUP.hom.app (rU.obj F) ≫ rUP'.map (TU.hom.app F) ≫ s₁.hom.app (eX.obj F))
    (h₂ : ∀ F, eP.map (c₂.hom.app F) ≫ T₂.hom.app F =
      TVP.hom.app (rV.obj F) ≫ rVP'.map (TV.hom.app F) ≫ s₂.hom.app (eX.obj F))
    (hC : ∀ F, eP.map (C.hom.app F) ≫ T₂.hom.app F = T₁.hom.app F ≫ C'.hom.app (eX.obj F)) :
    Coherent (eX := eX) κ κ' TU TV TUP TVP := by
  intro F
  have h₂' : TVP.hom.app (rV.obj F) ≫ rVP'.map (TV.hom.app F) =
      eP.map (c₂.hom.app F) ≫ T₂.hom.app F ≫ s₂.inv.app (eX.obj F) := by
    rw [reassoc_of% (h₂ F)]
    simp
  rw [hκ F, hκ' (eX.obj F), Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    h₂', map_inv_hom_app_assoc, reassoc_of% (hC F), reassoc_of% (h₁ F)]

/-- `r_{UP}' (e_U φ)` through the comparison `T_{UP}`. -/
theorem map_eU_eq (TUP : rUP ⋙ eP ≅ eU ⋙ rUP') {A A' : DU} (φ : A ⟶ A') :
    rUP'.map (eU.map φ) = TUP.inv.app A ≫ eP.map (rUP.map φ) ≫ TUP.hom.app A' := by
  have := TUP.hom.naturality φ
  simp only [Functor.comp_map] at this
  rw [this, Iso.inv_hom_id_app_assoc]

/-- A morphism `φ'` whose image under `r'` is the transport of `ψ` along `T` has `ψ` as the image
of its preimage under `r`. -/
private theorem map_preimage_eq_of_map_eq {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂]
    {C₁' : Type*} [Category* C₁'] {C₂' : Type*} [Category* C₂'] {r : C₁ ⥤ C₂} {r' : C₁' ⥤ C₂'}
    {e : C₁ ⥤ C₁'} {e' : C₂ ⥤ C₂'} [e.Full] [e'.Faithful] (T : r ⋙ e' ≅ e ⋙ r') {F E : C₁}
    (ψ : r.obj F ⟶ r.obj E) (φ' : e.obj F ⟶ e.obj E)
    (h : r'.map φ' = T.inv.app F ≫ e'.map ψ ≫ T.hom.app E) : r.map (e.preimage φ') = ψ := by
  apply e'.map_injective
  have := T.hom.naturality (e.preimage φ')
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_preimage] at this
  rw [← cancel_epi (T.inv.app F), ← cancel_mono (T.hom.app E)]
  simp only [Category.assoc, this, h, Iso.inv_hom_id_app_assoc]

/-- **Glueing of morphisms is carried along equivalences** compatible with the restrictions. -/
theorem HomsGlue.transport [eX.Full] [eU.Faithful] [eV.Faithful] [eP.Faithful]
    (h : HomsGlue rU' rV' rUP' rVP' κ') (hc : Coherent (eX := eX) κ κ' TU TV TUP TVP) :
    HomsGlue rU rV rUP rVP κ := by
  intro F E φU φV hφ
  obtain ⟨φ', hU, hV⟩ := h (TU.inv.app F ≫ eU.map φU ≫ TU.hom.app E)
    (TV.inv.app F ≫ eV.map φV ≫ TV.hom.app E) (by
      rw [hc.inv_eq E, hc.inv_eq F, Functor.map_comp, Functor.map_comp, Functor.map_comp,
        Functor.map_comp, map_eU_eq TUP, map_eU_eq TVP]
      simp only [Category.assoc, map_hom_inv_app_assoc, Iso.hom_inv_id_app_assoc]
      rw [← eP.map_comp_assoc, hφ, eP.map_comp_assoc])
  exact ⟨eX.preimage φ', map_preimage_eq_of_map_eq TU _ _ hU,
    map_preimage_eq_of_map_eq TV _ _ hV⟩

/-- **Glueing of objects is carried along equivalences** compatible with the restrictions. -/
theorem ObjectsGlue.transport [eX.EssSurj] [eU.Full] [eU.Faithful] [eV.Full] [eV.Faithful]
    [eP.Faithful]
    (h : ObjectsGlue rU' rV' rUP' rVP' κ') (hc : Coherent (eX := eX) κ κ' TU TV TUP TVP) :
    ObjectsGlue rU rV rUP rVP κ := by
  intro A Bo c
  obtain ⟨F', f', g', hfg⟩ := h (eU.obj A) (eV.obj Bo)
    (TUP.symm.app A ≪≫ eP.mapIso c ≪≫ TVP.app Bo)
  let F := eX.objPreimage F'
  let ι : eX.obj F ≅ F' := eX.objObjPreimageIso F'
  let fU : eU.obj (rU.obj F) ≅ eU.obj A := TU.app F ≪≫ rU'.mapIso ι ≪≫ f'
  let gV : eV.obj (rV.obj F) ≅ eV.obj Bo := TV.app F ≪≫ rV'.mapIso ι ≪≫ g'
  refine ⟨F, eU.preimageIso fU, eV.preimageIso gV, eP.map_injective ?_⟩
  have e1 : eP.map (rUP.map (eU.preimageIso fU).inv) =
      TUP.hom.app _ ≫ rUP'.map fU.inv ≫ TUP.inv.app _ := by
    have := map_eU_eq TUP (eU.preimageIso fU).inv
    simp only [Functor.preimageIso_inv, Functor.map_preimage] at this
    rw [this]
    simp
  have e2 : eP.map (rVP.map (eV.preimageIso gV).hom) =
      TVP.hom.app _ ≫ rVP'.map gV.hom ≫ TVP.inv.app _ := by
    have := map_eU_eq TVP (eV.preimageIso gV).hom
    simp only [Functor.preimageIso_hom, Functor.map_preimage] at this
    rw [this]
    simp
  have hι := κ'.hom.naturality ι.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hι
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom] at hfg
  have hc' : eP.map c.hom = TUP.hom.app A ≫ (rUP'.map f'.inv ≫ κ'.hom.app F' ≫
      rVP'.map g'.hom) ≫ TVP.inv.app Bo := by
    rw [← hfg]
    simp
  rw [hc', Functor.map_comp, Functor.map_comp, e1, e2]
  simp only [fU, gV, Iso.trans_inv, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hc F)]
  simp only [Iso.inv_hom_id_app_assoc, map_inv_hom_app_assoc]
  rw [← reassoc_of% hι, map_map_inv_hom_assoc]

/-- **Joint reflection of isomorphisms is carried along equivalences** compatible with the
restrictions. -/
theorem ReflectsIso.transport [eX.ReflectsIsomorphisms]
    (h : ReflectsIso rU' rV') (TU : rU ⋙ eU ≅ eX ⋙ rU') (TV : rV ⋙ eV ≅ eX ⋙ rV') :
    ReflectsIso rU rV := by
  intro F E φ hU hV
  have hU' : IsIso (rU'.map (eX.map φ)) := by
    rw [map_eU_eq TU]
    infer_instance
  have hV' : IsIso (rV'.map (eX.map φ)) := by
    rw [map_eU_eq TV]
    infer_instance
  have := h (eX.map φ) hU' hV'
  exact isIso_of_reflects_iso φ eX

end Transport

section Triangulated

variable {rU rV}
variable [HasZeroObject DX] [HasShift DX ℤ] [Preadditive DX]
  [∀ n : ℤ, (shiftFunctor DX n).Additive] [Pretriangulated DX]
  [HasZeroObject DU] [HasShift DU ℤ] [Preadditive DU]
  [∀ n : ℤ, (shiftFunctor DU n).Additive] [Pretriangulated DU]
  [HasZeroObject DV] [HasShift DV ℤ] [Preadditive DV]
  [∀ n : ℤ, (shiftFunctor DV n).Additive] [Pretriangulated DV]
  [rU.CommShift ℤ] [rU.IsTriangulated] [rV.CommShift ℤ] [rV.IsTriangulated]

/-- For triangulated restrictions, joint reflection of isomorphisms follows from joint
reflection of zero objects: the cone of a morphism restricting to isomorphisms restricts to
zero. -/
theorem reflectsIso_of_isZero
    (h : ∀ F : DX, IsZero (rU.obj F) → IsZero (rV.obj F) → IsZero F) : ReflectsIso rU rV := by
  intro F E φ hU hV
  obtain ⟨C, b, c, hT⟩ := distinguished_cocone_triangle φ
  have hTU := rU.map_distinguished _ hT
  have hTV := rV.map_distinguished _ hT
  have hzU : IsZero (rU.obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ hTU).2 hU
  have hzV : IsZero (rV.obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ hTV).2 hV
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (h C hzU hzV)

end Triangulated

section Stage

variable {rU rV rUP rVP κ}
variable {CX : Type u₅} [Category.{v₅} CX] {CU : Type u₆} [Category.{v₆} CU]
  {CV : Type u₇} [Category.{v₇} CV] {CP : Type u₈} [Category.{v₈} CP]
  {sU : CX ⥤ CU} {sV : CX ⥤ CV} {sUP : CU ⥤ CP} {sVP : CV ⥤ CP}
  {κs : sU ⋙ sUP ≅ sV ⋙ sVP}
  {pX : CX ⥤ DX} {pU : CU ⥤ DU} {pV : CV ⥤ DV} {pP : CP ⥤ DP}
  {σU : sU ⋙ pU ≅ pX ⋙ rU} {σV : sV ⋙ pV ≅ pX ⋙ rV}
  {σUP : sUP ⋙ pP ≅ pU ⋙ rUP} {σVP : sVP ⋙ pP ≅ pV ⋙ rVP}

/-- **An object over the limit whose restrictions come from a stage, compatibly over `P`, comes
from the stage.** Let `s_•` be the restrictions at a stage, `r_•` those over the limit, `p_•` the
pullbacks from the stage to the limit with comparisons `σ_•` satisfying the cube condition
`Coherent κs κ σU σV σUP σVP`. If objects glue at the stage, morphisms glue over the limit and the
restrictions over the limit jointly reflect isomorphisms, then for an object `E` over the limit,
objects `A`, `Bo` at the stage with `αU : p_U A ≅ r_U E`, `αV : p_V Bo ≅ r_V E` and an isomorphism
`c : s_{UP} A ≅ s_{VP} Bo` that pulls back to the comparison of `αU` and `αV` through `κ`, there is
an object `F` at the stage with `s_U F ≅ A`, `s_V F ≅ Bo` and `p_X F ≅ E`. -/
theorem exists_iso_of_objectsGlue_of_homsGlue (hglue : ObjectsGlue sU sV sUP sVP κs)
    (hhom : HomsGlue rU rV rUP rVP κ) (hiso : ReflectsIso rU rV)
    (hcube : Coherent (eX := pX) κs κ σU σV σUP σVP)
    (E : DX) (A : CU) (Bo : CV) (αU : pU.obj A ≅ rU.obj E) (αV : pV.obj Bo ≅ rV.obj E)
    (c : sUP.obj A ≅ sVP.obj Bo)
    (hc : pP.map c.hom ≫ σVP.hom.app Bo ≫ rVP.map αV.hom =
      σUP.hom.app A ≫ rUP.map αU.hom ≫ κ.hom.app E) :
    ∃ (F : CX) (_ : sU.obj F ≅ A) (_ : sV.obj F ≅ Bo), Nonempty (pX.obj F ≅ E) := by
  obtain ⟨F, f, g, hfg⟩ := hglue A Bo c
  obtain ⟨φ, hφU, hφV⟩ := hhom (σU.inv.app F ≫ pU.map f.hom ≫ αU.hom)
    (σV.inv.app F ≫ pV.map g.hom ≫ αV.hom) (by
      have hfg' : sUP.map f.hom ≫ c.hom = κs.hom.app F ≫ sVP.map g.hom := by
        rw [hfg, ← Functor.map_comp_assoc, f.hom_inv_id, Functor.map_id, Category.id_comp]
      rw [hcube.inv_eq F]
      simp only [Functor.map_comp, Category.assoc, map_hom_inv_app_assoc]
      rw [map_eU_eq σVP g.hom, map_eU_eq σUP f.hom]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      rw [← pP.map_comp_assoc, ← hfg', pP.map_comp_assoc, hc])
  have : IsIso (rU.map φ) := by rw [hφU]; infer_instance
  have : IsIso (rV.map φ) := by rw [hφV]; infer_instance
  have := hiso φ inferInstance inferInstance
  exact ⟨F, f, g, ⟨asIso φ⟩⟩

/-- **The compatibility over `P` moves to a later stage.** In the situation of
`CategoryTheory.RestrictionSquare.exists_iso_of_objectsGlue_of_homsGlue`, let `αU`, `αV` be the
identifications over the limit of the pullbacks of objects `A`, `Bo` of an earlier stage, `ρU`,
`ρV`, `ρPU`, `ρPV` the identifications of the pullbacks from a later stage of their transitions
with the pullbacks from the earlier stage, `σ₁`, `σ'` the comparisons of the restrictions to `P` at
the two stages with those over the limit and `τU`, `τV` those of the transitions with the
restrictions to `P`, related by the prism identities `hU`, `hV`. If an isomorphism `ψ` at the later
stage pulls back to the comparison of `αU` and `αV` through `k` read at the earlier stage, then
`τU⁻¹ ≫ ψ ≫ τV` pulls back to the comparison of the transported identifications through `k`. -/
theorem compat_of_stageTransition {DU' : Type u₁} [Category.{v₁} DU'] {DV' : Type u₂}
    [Category.{v₂} DV'] {DP' : Type u₃} [Category.{v₃} DP'] {CP : Type u₄} [Category.{v₄} CP]
    (qU : DU' ⥤ DP') (qV : DV' ⥤ DP') (pP : CP ⥤ DP')
    {EU AU AU' : DU'} {EV AV AV' : DV'} {Z₁ Z₂ : DP'} {Y₁ Y₂ Y₁' Y₂' : CP}
    (αU : AU ≅ EU) (αV : AV ≅ EV) (ρU : AU' ≅ AU) (ρV : AV' ≅ AV) (k : qU.obj EU ⟶ qV.obj EV)
    (σ₁U : Z₁ ≅ qU.obj AU) (σ₁V : Z₂ ≅ qV.obj AV) (ρPU : pP.obj Y₁ ≅ Z₁) (ρPV : pP.obj Y₂ ≅ Z₂)
    (τU : Y₁ ≅ Y₁') (τV : Y₂ ≅ Y₂') (σ'U : pP.obj Y₁' ≅ qU.obj AU')
    (σ'V : pP.obj Y₂' ≅ qV.obj AV') (ψ : Y₁ ≅ Y₂)
    (hU : pP.map τU.hom ≫ σ'U.hom ≫ qU.map ρU.hom = ρPU.hom ≫ σ₁U.hom)
    (hV : pP.map τV.hom ≫ σ'V.hom ≫ qV.map ρV.hom = ρPV.hom ≫ σ₁V.hom)
    (hψ : ρPU.inv ≫ pP.map ψ.hom ≫ ρPV.hom =
      σ₁U.hom ≫ qU.map αU.hom ≫ k ≫ qV.map αV.inv ≫ σ₁V.inv) :
    pP.map (τU.symm ≪≫ ψ ≪≫ τV).hom ≫ σ'V.hom ≫ qV.map (ρV ≪≫ αV).hom =
      σ'U.hom ≫ qU.map (ρU ≪≫ αU).hom ≫ k := by
  rw [Iso.inv_comp_eq] at hψ
  have hψ' : pP.map ψ.hom ≫ ρPV.hom ≫ σ₁V.hom ≫ qV.map αV.hom =
      ρPU.hom ≫ σ₁U.hom ≫ qU.map αU.hom ≫ k := by
    rw [reassoc_of% hψ]
    simp
  have hU' : pP.map τU.inv ≫ ρPU.hom ≫ σ₁U.hom = σ'U.hom ≫ qU.map ρU.hom := by
    rw [← hU, ← pP.map_comp_assoc, Iso.inv_hom_id, pP.map_id, Category.id_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hV, hψ', reassoc_of% hU']

end Stage

end CategoryTheory.RestrictionSquare

end
