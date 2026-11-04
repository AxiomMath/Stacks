module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit

/-!
# Transporting a trivialisation along the section square is pseudofunctorial

Let `σ : B ⟶ X` be a section of the structure morphism of a Picard situation (Stacks 0D25).
A morphism `(g, φ) : (T, L) ⟶ (T', L')` of `Picardstack_{X/B}` transports a trivialisation
`α' : 𝒪_{T'} ⟶ σ_{T'}^*L'` to `σ_T^*φ ∘ g^*α'`, read through `𝒪_T ≅ g^*𝒪_{T'}` and the
comparison of Stacks 03LU for the section square
(`AlgebraicGeometry.Space.PicardSituation.transportTrivialization`).  The rigidified category
`Picardstack_{X/B, σ}` of Stacks 0D29 needs this transport to be pseudofunctorial, which is
`AlgebraicGeometry.Space.SectionTransportCoherence`.  This file proves it **for every
pseudofunctoriality datum `hc` of Stacks 03LU**.

The unit law `idIso` of `hc` is not unconstrained relative to the identification `q^*𝒪 ≅ 𝒪`:
through the unit law `id_comp` of `hc` it is pinned down by the comparison along a composite, and
that comparison is compatible with the identification by
`AlgebraicGeometry.Space.modulePullbackTriangle_hom_app_unit_comp`.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.sectionTransportIso`: the transport isomorphism
  `g^*σ_{T'}^*L' ≅ σ_T^*L` of a morphism of `Picardstack_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.ModulePushforwardCoherence.structureModulePullbackIso_id` and
  `AlgebraicGeometry.Space.structureModulePullbackIso_comp`: the identification `𝒪 ≅ q^*𝒪` along
  an identity is the unit law of `hc`, and along a composite it is the composite of the two
  identifications and the comparison of Stacks 03LU.
* `AlgebraicGeometry.Space.PicardSituation.sectionTransportIso_id` and
  `AlgebraicGeometry.Space.PicardSituation.sectionTransportIso_comp`: the same two laws for the
  transport isomorphism.
* `AlgebraicGeometry.Space.sectionTransportCoherence`: **the restriction along the section is
  pseudofunctorial**, with no hypothesis.

## Implementation notes

Every law is first proved for abstract functors and isomorphisms
(`CategoryTheory.Functor.sectionIso_id_cancel`, `CategoryTheory.Functor.sectionIso_comp_cancel`,
`CategoryTheory.Functor.transport_comp_iso`) and then instantiated with the inputs given as
*isomorphisms*.  The inverse images along `𝟙 ≫ σ` and `σ`, or along
`(PicardHom.comp m n).base` and `m.base ≫ n.base`, agree definitionally, but comparing them
beneath `CategoryTheory.NatTrans.app` exceeds the elaborator's and the kernel's budgets; read on
isomorphisms the same identifications are cheap.

## References

* [Stacks Project, Tag 0D29](https://stacks.math.columbia.edu/tag/0D29)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

/-- The composition law of the transport isomorphism, abstractly: under the coherences `hA`, `hB`
and `hC`, the transport isomorphism of a composite is the comparison `Th`, the inverse image of
the transport isomorphism of the second factor and the transport isomorphism of the first. -/
theorem Functor.sectionIso_comp_cancel {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* D₁] [Category* D₂] [Category* D₃]
    {F₁ : D₁ ⥤ C₁} {F₂ : D₂ ⥤ C₂} {F₃ : D₃ ⥤ C₃}
    {E₁₂ : C₂ ⥤ C₁} {E₂₃ : C₃ ⥤ C₂} {E₁₃ : C₃ ⥤ C₁}
    {X₁₂ : D₂ ⥤ D₁} {X₂₃ : D₃ ⥤ D₂} {X₁₃ : D₃ ⥤ D₁}
    {K₁₂ : D₂ ⥤ C₁} {K₂₃ : D₃ ⥤ C₂} {K₁₃ : D₃ ⥤ C₁}
    (R₁₂ : K₁₂ ≅ F₂ ⋙ E₁₂) (N₁₂ : K₁₂ ≅ X₁₂ ⋙ F₁) (R₂₃ : K₂₃ ≅ F₃ ⋙ E₂₃)
    (N₂₃ : K₂₃ ≅ X₂₃ ⋙ F₂) (R₁₃ : K₁₃ ≅ F₃ ⋙ E₁₃) (N₁₃ : K₁₃ ≅ X₁₃ ⋙ F₁)
    (Th : E₁₃ ≅ E₂₃ ⋙ E₁₂) (Tx : X₁₃ ≅ X₂₃ ⋙ X₁₂) (Thr : K₁₃ ≅ K₂₃ ⋙ E₁₂)
    (Thk : K₁₃ ≅ X₂₃ ⋙ K₁₂)
    (hA : R₁₃ ≪≫ Functor.isoWhiskerLeft F₃ Th =
      Thr ≪≫ Functor.isoWhiskerRight R₂₃ E₁₂ ≪≫ Functor.associator F₃ E₂₃ E₁₂)
    (hB : Thk ≪≫ Functor.isoWhiskerLeft X₂₃ N₁₂ =
      N₁₃ ≪≫ Functor.isoWhiskerRight Tx F₁ ≪≫ Functor.associator X₂₃ X₁₂ F₁)
    (hC : Thk ≪≫ Functor.isoWhiskerLeft X₂₃ R₁₂ =
      Thr ≪≫ Functor.isoWhiskerRight N₂₃ E₁₂ ≪≫ Functor.associator X₂₃ F₂ E₁₂)
    (Sq₁₂ : X₁₂ ⋙ F₁ ≅ F₂ ⋙ E₁₂) (Sq₂₃ : X₂₃ ⋙ F₂ ≅ F₃ ⋙ E₂₃) (Sq₁₃ : X₁₃ ⋙ F₁ ≅ F₃ ⋙ E₁₃)
    (hS₁₂ : Sq₁₂ = N₁₂.symm ≪≫ R₁₂) (hS₂₃ : Sq₂₃ = N₂₃.symm ≪≫ R₂₃)
    (hS₁₃ : Sq₁₃ = N₁₃.symm ≪≫ R₁₃)
    {L₁ : D₁} {L₂ : D₂} {L₃ : D₃} (Ψ₁₂ : X₁₂.obj L₂ ≅ L₁) (Ψ₂₃ : X₂₃.obj L₃ ≅ L₂)
    (Ψ₁₃ : X₁₃.obj L₃ ≅ L₁) (hΨ : Ψ₁₃ = Tx.app L₃ ≪≫ X₁₂.mapIso Ψ₂₃ ≪≫ Ψ₁₂) :
    (Sq₁₃.app L₃).symm ≪≫ F₁.mapIso Ψ₁₃ =
      Th.app (F₃.obj L₃) ≪≫ E₁₂.mapIso ((Sq₂₃.app L₃).symm ≪≫ F₂.mapIso Ψ₂₃) ≪≫
        (Sq₁₂.app L₂).symm ≪≫ F₁.mapIso Ψ₁₂ := by
  subst hS₁₂ hS₂₃ hS₁₃ hΨ
  have hA'' := congrArg (fun i ↦ i.inv.app L₃) hA
  have hB' := congrArg (fun i ↦ i.hom.app L₃) hB
  have hC' := congrArg (fun i ↦ i.hom.app L₃) hC
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp] at hA'' hB' hC'
  have hC'' : Thk.hom.app L₃ =
      Thr.hom.app L₃ ≫ E₁₂.map (N₂₃.hom.app L₃) ≫ R₁₂.inv.app (X₂₃.obj L₃) := by
    rw [← reassoc_of% hC', Iso.hom_inv_id_app, Category.comp_id]
  have key : Th.inv.app (F₃.obj L₃) ≫ R₁₃.inv.app L₃ ≫ N₁₃.hom.app L₃ ≫
        F₁.map (Tx.hom.app L₃) =
      E₁₂.map (R₂₃.inv.app L₃) ≫ E₁₂.map (N₂₃.hom.app L₃) ≫ R₁₂.inv.app (X₂₃.obj L₃) ≫
        N₁₂.hom.app (X₂₃.obj L₃) := by
    rw [← hB', hC'', reassoc_of% hA'']
    simp
  have hnat := (N₁₂.symm ≪≫ R₁₂).inv.naturality Ψ₂₃.hom
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.comp_map,
    Category.assoc] at hnat
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← cancel_epi (Th.inv.app (F₃.obj L₃)), Iso.inv_hom_id_app_assoc, reassoc_of% key,
    reassoc_of% hnat]

/-- The identity law of the transport isomorphism, abstractly: the comparison `(E' ⋙ F) ≅ (F ⋙ E)`
of two unit laws, followed by `F` of the unit law on `E'`, is the unit law on `E`. -/
theorem Functor.sectionIso_id_cancel {C D : Type*} [Category* C] [Category* D] (F : D ⥤ C)
    {K : D ⥤ C} {E : C ⥤ C} {E' : D ⥤ D} (J : E ≅ 𝟭 C) (J' : E' ≅ 𝟭 D) (Φ : K ≅ F)
    (T₁ : K ≅ F ⋙ E) (T₂ : K ≅ E' ⋙ F)
    (hT₁ : T₁ = Φ ≪≫ F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F J.symm)
    (hT₂ : T₂ = Φ ≪≫ F.leftUnitor.symm ≪≫ Functor.isoWhiskerRight J'.symm F)
    (Sq : E' ⋙ F ≅ F ⋙ E) (hSq : Sq = T₂.symm ≪≫ T₁) {L : D} (Ψ : E'.obj L ≅ L)
    (hΨ : Ψ = J'.app L) :
    (Sq.app L).symm ≪≫ F.mapIso Ψ = J.app (F.obj L) := by
  subst hT₁ hT₂ hSq hΨ
  ext
  simp

/-- Conjugating by an isomorphism `E ≅ 𝟭` undoes `E`. -/
theorem Functor.iso_id_conj {C : Type*} [Category* C] {E : C ⥤ C} (J : E ≅ 𝟭 C) {O Y : C}
    (α : O ⟶ Y) : (J.app O).symm.hom ≫ E.map α ≫ (J.app Y).hom = α := by
  simp

/-- Transporting along a composite, abstractly: identifications `Uᵢⱼ : Oᵢ ≅ Eᵢⱼ Oⱼ` and
transport isomorphisms `Θᵢⱼ : Eᵢⱼ Mⱼ ≅ Mᵢ` both compatible with `Th : E₁₃ ≅ E₂₃ ⋙ E₁₂`. -/
theorem Functor.transport_comp_iso {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] {E₁₂ : C₂ ⥤ C₁} {E₂₃ : C₃ ⥤ C₂} {E₁₃ : C₃ ⥤ C₁} (Th : E₁₃ ≅ E₂₃ ⋙ E₁₂)
    {O₁ : C₁} {O₂ : C₂} {O₃ : C₃} (U₁₂ : O₁ ≅ E₁₂.obj O₂) (U₂₃ : O₂ ≅ E₂₃.obj O₃)
    (U₁₃ : O₁ ≅ E₁₃.obj O₃) (hU : U₁₃.symm = Th.app O₃ ≪≫ E₁₂.mapIso U₂₃.symm ≪≫ U₁₂.symm)
    {M₁ : C₁} {M₂ : C₂} {M₃ : C₃} (Θ₁₂ : E₁₂.obj M₂ ≅ M₁) (Θ₂₃ : E₂₃.obj M₃ ≅ M₂)
    (Θ₁₃ : E₁₃.obj M₃ ≅ M₁) (hΘ : Θ₁₃ = Th.app M₃ ≪≫ E₁₂.mapIso Θ₂₃ ≪≫ Θ₁₂)
    (α : O₃ ⟶ M₃) :
    U₁₃.hom ≫ E₁₃.map α ≫ Θ₁₃.hom =
      U₁₂.hom ≫ E₁₂.map (U₂₃.hom ≫ E₂₃.map α ≫ Θ₂₃.hom) ≫ Θ₁₂.hom := by
  subst hΘ
  have hU' : U₁₃.hom = U₁₂.hom ≫ E₁₂.map U₂₃.hom ≫ Th.inv.app O₃ := by
    have := congrArg Iso.inv hU
    simpa using this
  rw [hU']
  have hnat := Th.inv.naturality α
  simp only [Functor.comp_map] at hnat
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnat, Iso.inv_hom_id_app_assoc]

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The identification `q^*𝒪 ≅ 𝒪` and the comparisons of Stacks 03LU -/

/-- A natural transformation out of an inverse image takes the same value at the two spellings
of the structure sheaf.  Stated for a variable natural transformation, where the identification
of the two spellings is cheap. -/
theorem natTrans_app_structureModule {X X' X'' : AlgebraicSpaces B S hS} (a : X ⟶ X')
    (b : X' ⟶ X'') (c : X ⟶ X'')
    (τ : modulePullback B S hS c ⟶ modulePullback B S hS b ⋙ modulePullback B S hS a) :
    τ.app (structureModule X'') = τ.app (SheafOfModules.unit (structureRingSheaf B S hS X'')) :=
  rfl

/-- **The identification `c^*𝒪 ≅ 𝒪` is compatible with the comparison of inverse images along a
composite**, at the spelling `AlgebraicGeometry.Space.structureModule` of the structure sheaf. -/
theorem modulePullbackTriangle_hom_app_structureModule_comp {X X' X'' : AlgebraicSpaces B S hS}
    (a : X ⟶ X') (b : X' ⟶ X'') {c : X ⟶ X''} (hk : a ≫ b = c) :
    (modulePullbackTriangle B S hS hk).hom.app (structureModule X'') ≫
        (modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).hom ≫
        (modulePullbackUnitIso B S hS a).hom =
      (modulePullbackUnitIso B S hS c).hom :=
  (congrArg (· ≫ (modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).hom ≫
      (modulePullbackUnitIso B S hS a).hom)
    (natTrans_app_structureModule a b c (modulePullbackTriangle B S hS hk).hom)).trans
    (modulePullbackTriangle_hom_app_unit_comp B S hS a b hk)

/-- `AlgebraicGeometry.Space.structureModulePullbackIso` is the inverse of
`AlgebraicGeometry.Space.modulePullbackUnitIso`. -/
theorem structureModulePullbackIso_eq {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) :
    structureModulePullbackIso q = (modulePullbackUnitIso B S hS q).symm :=
  rfl

namespace ModulePushforwardCoherence

variable (hc : ModulePushforwardCoherence B S hS)

/-- **The identification `(𝟙 X)^*𝒪_X ≅ 𝒪_X` is the unit law of Stacks 03LU at `𝒪_X`.** -/
theorem modulePullbackUnitIso_id_hom (X : AlgebraicSpaces B S hS) :
    (modulePullbackUnitIso B S hS (𝟙 X)).hom =
      (hc.modulePullbackIdIso X).hom.app (structureModule X) := by
  have h := modulePullbackTriangle_hom_app_structureModule_comp (𝟙 X) (𝟙 X)
    (Category.id_comp (𝟙 X))
  have hA : (modulePullbackTriangle B S hS (Category.id_comp (𝟙 X))).hom.app
        (structureModule X) =
      (hc.modulePullbackIdIso X).inv.app
        ((modulePullback B S hS (𝟙 X)).obj (structureModule X)) := by
    rw [hc.modulePullbackTriangle_id]
    simp
  have hn : (hc.modulePullbackIdIso X).inv.app
        ((modulePullback B S hS (𝟙 X)).obj (structureModule X)) ≫
        (modulePullback B S hS (𝟙 X)).map (modulePullbackUnitIso B S hS (𝟙 X)).hom =
      (modulePullbackUnitIso B S hS (𝟙 X)).hom ≫
        (hc.modulePullbackIdIso X).inv.app (structureModule X) :=
    ((hc.modulePullbackIdIso X).inv.naturality (modulePullbackUnitIso B S hS (𝟙 X)).hom).symm
  rw [hA, ← Category.assoc, hn, Category.assoc] at h
  have h2 : (hc.modulePullbackIdIso X).inv.app (structureModule X) ≫
        (modulePullbackUnitIso B S hS (𝟙 X)).hom = 𝟙 _ := by
    rw [← cancel_epi (modulePullbackUnitIso B S hS (𝟙 X)).hom, h]
    exact (Category.comp_id _).symm
  exact ((Iso.app (hc.modulePullbackIdIso X) _).inv_comp_eq.mp h2).trans (Category.comp_id _)

/-- **The comparison of inverse images along a composite whose second factor is an identity is
the unit law `(𝟙 Y)^* ≅ 𝟭`.** -/
theorem modulePullbackTriangle_id_right {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (hk : f ≫ 𝟙 Y = f) :
    modulePullbackTriangle B S hS hk =
      (Functor.leftUnitor (modulePullback B S hS f)).symm ≪≫
        Functor.isoWhiskerRight (hc.modulePullbackIdIso Y).symm (modulePullback B S hS f) := by
  have hE : modulePullbackTriangle B S hS hk =
      (modulePullbackCompIso B S hS f (𝟙 Y)).symm := by
    rw [modulePullbackTriangle_eq]
    have h0 : eqToIso (congrArg (modulePullback B S hS) hk.symm) =
        eqToIso (congrArg (modulePullback B S hS) (rfl : f = f)) := rfl
    rw [h0]
    simp
  rw [hE, hc.modulePullbackCompIso_id_right f]
  simp [Functor.isoWhiskerRight_symm]

/-- The identification `𝒪_W ≅ (𝟙 W)^*𝒪_W` is the unit law of Stacks 03LU at `𝒪_W`. -/
theorem structureModulePullbackIso_id_hom (W : AlgebraicSpaces B S hS) :
    (structureModulePullbackIso (𝟙 W)).hom =
      (hc.modulePullbackIdIso W).inv.app (structureModule W) := by
  rw [structureModulePullbackIso_eq, Iso.symm_hom, ← Iso.app_inv]
  congr 1
  exact Iso.ext (hc.modulePullbackUnitIso_id_hom W)

/-- `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_id` for the
composite `𝟙 W ≫ σ'` presented as itself. -/
theorem modulePullbackTriangle_id_rfl {W P : AlgebraicSpaces B S hS} (σ' : W ⟶ P) :
    modulePullbackTriangle B S hS (rfl : 𝟙 W ≫ σ' = 𝟙 W ≫ σ') =
      (Functor.rightUnitor (modulePullback B S hS σ')).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS σ') (hc.modulePullbackIdIso W).symm :=
  hc.modulePullbackTriangle_id (Category.id_comp σ')

/-- `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_id_right` for the
composite `σ' ≫ 𝟙 P` presented as `𝟙 W ≫ σ'`. -/
theorem modulePullbackTriangle_id_right' {W P : AlgebraicSpaces B S hS} (σ' : W ⟶ P)
    (hn : σ' ≫ 𝟙 P = 𝟙 W ≫ σ') :
    modulePullbackTriangle B S hS hn =
      (Functor.leftUnitor (modulePullback B S hS σ')).symm ≪≫
        Functor.isoWhiskerRight (hc.modulePullbackIdIso P).symm (modulePullback B S hS σ') :=
  hc.modulePullbackTriangle_id_right (Category.comp_id σ')

/-- The identification `𝒪_W ≅ (𝟙 W)^*𝒪_W` is the unit law of Stacks 03LU at `𝒪_W`, as an
isomorphism. -/
theorem structureModulePullbackIso_id (W : AlgebraicSpaces B S hS) :
    structureModulePullbackIso (𝟙 W) = ((hc.modulePullbackIdIso W).app (structureModule W)).symm :=
  Iso.ext (hc.structureModulePullbackIso_id_hom W)

/-- The identification `𝒪_W ≅ e^*𝒪_W` for a morphism `e` equal to the identity. -/
theorem structureModulePullbackIso_of_eq_id {W : AlgebraicSpaces B S hS} {e : W ⟶ W}
    (he : e = 𝟙 W) :
    structureModulePullbackIso e =
      ((eqToIso (congrArg (modulePullback B S hS) he) ≪≫ hc.modulePullbackIdIso W).app
        (structureModule W)).symm := by
  subst he
  rw [eqToIso_refl, Iso.refl_trans]
  exact hc.structureModulePullbackIso_id W

/-- The comparison of inverse images along `e ≫ σ'` read as a composite, for a morphism `e`
equal to the identity. -/
theorem modulePullbackTriangle_rfl_of_eq_id {W P : AlgebraicSpaces B S hS} (σ' : W ⟶ P)
    {e : W ⟶ W} (he : e = 𝟙 W) (hk : e ≫ σ' = σ') :
    modulePullbackTriangle B S hS (rfl : e ≫ σ' = e ≫ σ') =
      eqToIso (congrArg (modulePullback B S hS) hk) ≪≫
        (Functor.rightUnitor (modulePullback B S hS σ')).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS σ')
          (eqToIso (congrArg (modulePullback B S hS) he) ≪≫ hc.modulePullbackIdIso W).symm := by
  subst he
  rw [eqToIso_refl, eqToIso_refl, Iso.refl_trans, Iso.refl_trans]
  exact hc.modulePullbackTriangle_id_rfl σ'

/-- The comparison of inverse images along a commuting square `σ' ≫ x = e ≫ σ'` whose two
horizontal morphisms equal identities. -/
theorem modulePullbackTriangle_of_eq_id {W P : AlgebraicSpaces B S hS} (σ' : W ⟶ P)
    {e : W ⟶ W} {x : P ⟶ P} (he : e = 𝟙 W) (hx : x = 𝟙 P) (hn : σ' ≫ x = e ≫ σ')
    (hk : e ≫ σ' = σ') :
    modulePullbackTriangle B S hS hn =
      eqToIso (congrArg (modulePullback B S hS) hk) ≪≫
        (Functor.leftUnitor (modulePullback B S hS σ')).symm ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (modulePullback B S hS) hx) ≪≫ hc.modulePullbackIdIso P).symm
          (modulePullback B S hS σ') := by
  subst he
  subst hx
  rw [eqToIso_refl, eqToIso_refl, Iso.refl_trans, Iso.refl_trans]
  exact hc.modulePullbackTriangle_id_right' σ' hn

/-- **The identification `𝒪 ≅ c^*𝒪` along a composite**, as an isomorphism: for `a ≫ b = c` it
is the identification along `a`, the inverse image along `a` of the identification along `b`,
and the comparison of inverse images along the composite. -/
theorem structureModulePullbackIso_symm_of_comp {X X' X'' : AlgebraicSpaces B S hS}
    (a : X ⟶ X') (b : X' ⟶ X'') {c : X ⟶ X''} (hk : a ≫ b = c) :
    (structureModulePullbackIso c).symm =
      (modulePullbackTriangle B S hS hk).app (structureModule X'') ≪≫
        (modulePullback B S hS a).mapIso (structureModulePullbackIso b).symm ≪≫
        (structureModulePullbackIso a).symm := by
  rw [structureModulePullbackIso_eq, structureModulePullbackIso_eq, structureModulePullbackIso_eq,
    Iso.symm_symm_eq, Iso.symm_symm_eq, Iso.symm_symm_eq]
  ext1
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  exact (modulePullbackTriangle_hom_app_structureModule_comp a b hk).symm

end ModulePushforwardCoherence

/-! ### The pseudofunctoriality of the restriction along the section -/

/-- The comparison of modules of an identity of `Picardstack_{X/B}`. -/
theorem PicardHom.id_fibre (hc : ModulePushforwardCoherence B S hS) {s : PicardSituation B S hS}
    (A : PicardObject s) :
    (PicardHom.id hc A).fibre = (baseChangeIdComparison hc s.f A.T).hom.app A.lineBundle :=
  rfl

/-- **The identification `𝒪 ≅ (q ≫ q')^*𝒪` along a composite** is the identification along `q`,
the inverse image along `q` of the identification along `q'`, and the comparison of inverse images
of Stacks 03LU. -/
theorem structureModulePullbackIso_comp {X X' X'' : AlgebraicSpaces B S hS} (q : X ⟶ X')
    (q' : X' ⟶ X'') :
    structureModulePullbackIso (q ≫ q') =
      structureModulePullbackIso q ≪≫
        (modulePullback B S hS q).mapIso (structureModulePullbackIso q') ≪≫
        (modulePullbackCompIso B S hS q q').app (structureModule X'') := by
  have h := ModulePushforwardCoherence.structureModulePullbackIso_symm_of_comp q q' rfl
  rw [modulePullbackTriangle_rfl] at h
  rw [← Iso.symm_symm_eq (structureModulePullbackIso (q ≫ q')), h]
  ext
  simp [Functor.mapIso_symm]

namespace PicardSituation

variable {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)

/-- **The transport isomorphism of a morphism of `Picardstack_{X/B}`** along the section square:
for `(g, φ) : (T, L) ⟶ (T', L')`, the isomorphism `g^*σ_{T'}^*L' ≅ σ_T^*L` made of the
comparison of Stacks 03LU for the section square and the restriction `σ_T^*φ` of the comparison
of modules. -/
def sectionTransportIso {A C : PicardObject s} (m : PicardHom A C) :
    (modulePullback B S hS ((schemeSpaceFunctor B S hS).map m.base.left)).obj
        ((sectionPullback σ hσ C.T).obj C.lineBundle) ≅
      (sectionPullback σ hσ A.T).obj A.lineBundle :=
  ((sectionSquareIso σ hσ m.base).app C.lineBundle).symm ≪≫
    (sectionPullback σ hσ A.T).mapIso (asIso m.fibre)

/-- The transported trivialisation is the identification `𝒪_T ≅ g^*𝒪_{T'}`, the inverse image of
the trivialisation and the transport isomorphism. -/
theorem transportTrivialization_eq_sectionTransportIso {A C : PicardObject s} (m : PicardHom A C)
    (α : structureModule (s.baseSpaceAt C.T) ⟶ (sectionPullback σ hσ C.T).obj C.lineBundle) :
    transportTrivialization (σ := σ) (hσ := hσ) m α =
      (structureModulePullbackIso ((schemeSpaceFunctor B S hS).map m.base.left)).hom ≫
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map m.base.left)).map α ≫
        (sectionTransportIso σ hσ m).hom :=
  rfl

/-- The morphism of base spaces underlying an identity of `Picardstack_{X/B}` is the identity. -/
theorem schemeSpaceFunctor_map_id_base (hc : ModulePushforwardCoherence B S hS)
    (A : PicardObject s) :
    (schemeSpaceFunctor B S hS).map (PicardHom.id hc A).base.left = 𝟙 _ := by
  rw [show (PicardHom.id hc A).base = 𝟙 A.T from rfl, CostructuredArrow.id_left,
    CategoryTheory.Functor.map_id]

/-- **The transport isomorphism of an identity is the unit law of Stacks 03LU.** -/
theorem sectionTransportIso_id (hc : ModulePushforwardCoherence B S hS) (A : PicardObject s) :
    sectionTransportIso σ hσ (PicardHom.id hc A) =
      (eqToIso (congrArg (modulePullback B S hS) (schemeSpaceFunctor_map_id_base hc A)) ≪≫
        hc.modulePullbackIdIso _).app ((sectionPullback σ hσ A.T).obj A.lineBundle) := by
  have he := schemeSpaceFunctor_map_id_base hc A
  have hk : (schemeSpaceFunctor B S hS).map (PicardHom.id hc A).base.left ≫
      baseChangeSection σ hσ A.T = baseChangeSection σ hσ A.T := by
    rw [he, Category.id_comp]
  have hn := baseChangeSection_naturality σ hσ (PicardHom.id hc A).base
  have hx : baseChangeMap s.f (PicardHom.id hc A).base = 𝟙 _ := baseChangeMap_id s.f A.T
  exact Functor.sectionIso_id_cancel (sectionPullback σ hσ A.T)
    (eqToIso (congrArg (modulePullback B S hS) he) ≪≫ hc.modulePullbackIdIso _)
    (baseChangeIdComparison hc s.f A.T) (eqToIso (congrArg (modulePullback B S hS) hk))
    (modulePullbackTriangle B S hS rfl) (modulePullbackTriangle B S hS hn)
    (hc.modulePullbackTriangle_rfl_of_eq_id _ he hk)
    (hc.modulePullbackTriangle_of_eq_id _ he hx hn hk) _ rfl
    (@asIso _ _ _ _ (PicardHom.id hc A).fibre (PicardHom.id hc A).isIso_fibre)
    (Iso.ext (PicardHom.id_fibre hc A))

/-- The morphisms of base spaces underlying a composite of `Picardstack_{X/B}` compose. -/
theorem schemeSpaceFunctor_map_comp_base {A C D : PicardObject s} (m : PicardHom A C)
    (n : PicardHom C D) :
    (schemeSpaceFunctor B S hS).map m.base.left ≫ (schemeSpaceFunctor B S hS).map n.base.left =
      (schemeSpaceFunctor B S hS).map (PicardHom.comp m n).base.left := by
  rw [show (PicardHom.comp m n).base = m.base ≫ n.base from rfl, CostructuredArrow.comp_left,
    CategoryTheory.Functor.map_comp]

/-- The comparison of modules of a composite of `Picardstack_{X/B}`, written out. -/
theorem picardHom_comp_fibre_eq {A C D : PicardObject s} (m : PicardHom A C) (n : PicardHom C D)
    (hx : baseChangeMap s.f m.base ≫ baseChangeMap s.f n.base =
      baseChangeMap s.f (PicardHom.comp m n).base) :
    (PicardHom.comp m n).fibre = (modulePullbackTriangle B S hS hx).hom.app D.lineBundle ≫
      (modulePullback B S hS (baseChangeMap s.f m.base)).map n.fibre ≫ m.fibre := by
  rw [PicardHom.comp_fibre]
  unfold Functor.fibreComp baseChangeCompComparison
  rw [modulePullbackTriangle_congr _ hx (rfl : baseChangeMap s.f (m.base ≫ n.base) =
    baseChangeMap s.f (PicardHom.comp m n).base)]
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc]
  exact Category.id_comp _

/-- **The transport isomorphism of a composite** is the comparison of Stacks 03LU along the
composite of the base maps, the inverse image of the transport isomorphism of the second factor
and the transport isomorphism of the first. -/
theorem sectionTransportIso_comp (hc : ModulePushforwardCoherence B S hS) {A C D : PicardObject s}
    (m : PicardHom A C) (n : PicardHom C D) :
    sectionTransportIso σ hσ (PicardHom.comp m n) =
      (modulePullbackTriangle B S hS (schemeSpaceFunctor_map_comp_base m n)).app
          ((sectionPullback σ hσ D.T).obj D.lineBundle) ≪≫
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map m.base.left)).mapIso
          (sectionTransportIso σ hσ n) ≪≫ sectionTransportIso σ hσ m := by
  have he := schemeSpaceFunctor_map_comp_base m n
  have hx : baseChangeMap s.f m.base ≫ baseChangeMap s.f n.base =
      baseChangeMap s.f (PicardHom.comp m n).base := (baseChangeMap_comp s.f m.base n.base).symm
  have n₁₂ := baseChangeSection_naturality σ hσ m.base
  have n₂₃ := baseChangeSection_naturality σ hσ n.base
  have n₁₃ := baseChangeSection_naturality σ hσ (PicardHom.comp m n).base
  have hr : (schemeSpaceFunctor B S hS).map m.base.left ≫
      (schemeSpaceFunctor B S hS).map n.base.left ≫ baseChangeSection σ hσ D.T =
      (schemeSpaceFunctor B S hS).map (PicardHom.comp m n).base.left ≫
        baseChangeSection σ hσ D.T := by
    rw [← he, Category.assoc]
  have hkr : ((schemeSpaceFunctor B S hS).map m.base.left ≫ baseChangeSection σ hσ C.T) ≫
      baseChangeMap s.f n.base =
      (schemeSpaceFunctor B S hS).map (PicardHom.comp m n).base.left ≫
        baseChangeSection σ hσ D.T := by
    rw [Category.assoc, n₂₃, hr]
  exact Functor.sectionIso_comp_cancel _ _ _ _ _ _ (modulePullbackTriangle B S hS he)
    (modulePullbackTriangle B S hS hx) (modulePullbackTriangle B S hS hr)
    (modulePullbackTriangle B S hS hkr)
    (hc.modulePullbackTriangle_comp he rfl hr rfl)
    (hc.modulePullbackTriangle_comp n₁₂ hx n₁₃ hkr)
    (hc.modulePullbackTriangle_comp rfl n₂₃ hr hkr)
    (sectionSquareIso σ hσ m.base) (sectionSquareIso σ hσ n.base)
    (sectionSquareIso σ hσ (PicardHom.comp m n).base) rfl rfl rfl
    (@asIso _ _ _ _ m.fibre m.isIso_fibre) (@asIso _ _ _ _ n.fibre n.isIso_fibre)
    (@asIso _ _ _ _ (PicardHom.comp m n).fibre (PicardHom.comp m n).isIso_fibre)
    (Iso.ext (picardHom_comp_fibre_eq m n hx))

/-- **The restriction along the section is pseudofunctorial**, for every pseudofunctoriality
datum of Stacks 03LU: transporting a trivialisation along an identity of `Picardstack_{X/B}`
returns it, and transporting along a composite is transporting along its two factors in turn. -/
theorem sectionTransportCoherence_transport_id (hc : ModulePushforwardCoherence B S hS)
    (A : PicardObject s)
    (α : structureModule (s.baseSpaceAt A.T) ⟶ (sectionPullback σ hσ A.T).obj A.lineBundle) :
    transportTrivialization (σ := σ) (hσ := hσ) (PicardHom.id hc A) α = α := by
  rw [transportTrivialization_eq_sectionTransportIso, sectionTransportIso_id,
    hc.structureModulePullbackIso_of_eq_id (schemeSpaceFunctor_map_id_base hc A)]
  exact Functor.iso_id_conj _ α

/-- Transporting a trivialisation along a composite of `Picardstack_{X/B}` is transporting it
along the two factors in turn. -/
theorem sectionTransportCoherence_transport_comp (hc : ModulePushforwardCoherence B S hS)
    {A C D : PicardObject s} (m : PicardHom A C) (n : PicardHom C D)
    (α : structureModule (s.baseSpaceAt D.T) ⟶ (sectionPullback σ hσ D.T).obj D.lineBundle) :
    transportTrivialization (σ := σ) (hσ := hσ) (PicardHom.comp m n) α =
      transportTrivialization (σ := σ) (hσ := hσ) m
        (transportTrivialization (σ := σ) (hσ := hσ) n α) := by
  rw [transportTrivialization_eq_sectionTransportIso,
    transportTrivialization_eq_sectionTransportIso,
    transportTrivialization_eq_sectionTransportIso]
  exact Functor.transport_comp_iso _ _ _ _
    (ModulePushforwardCoherence.structureModulePullbackIso_symm_of_comp _ _
      (schemeSpaceFunctor_map_comp_base m n)) _ _ _ (sectionTransportIso_comp σ hσ hc m n) α

end PicardSituation

/-- **The restriction along the section is pseudofunctorial**, for every pseudofunctoriality
datum of Stacks 03LU: `AlgebraicGeometry.Space.SectionTransportCoherence` holds unconditionally. -/
theorem sectionTransportCoherence (hc : ModulePushforwardCoherence B S hS)
    {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) :
    SectionTransportCoherence hc σ hσ where
  transport_id A α := PicardSituation.sectionTransportCoherence_transport_id σ hσ hc A α
  transport_comp m n α := PicardSituation.sectionTransportCoherence_transport_comp σ hσ hc m n α

end AlgebraicGeometry.Space

end
