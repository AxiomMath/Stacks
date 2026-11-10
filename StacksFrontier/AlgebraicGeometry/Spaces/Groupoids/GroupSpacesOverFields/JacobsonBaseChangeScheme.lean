module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.RepresentableGroupScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.TensorFibre
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.CompactImageAffineOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.AffineOpenFiniteSubextension
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.AlgClosureSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleAtlasQuasiSeparated

/-!
# A group algebraic space whose geometric base change is a Jacobson scheme

Let `K` be a field with algebraic closure `Ω`, and let `H` be a group algebraic space over `K`
whose base change `H_Ω` is a scheme which is Jacobson and all of whose closed points are
`Ω`-rational. If `H` is quasi-separated, then `H` is a scheme.

This is the heart of the proof of Stacks 0B8G, after the reduction of the ground field to a
purely transcendental extension of large transcendence degree.

## Main results

* `AlgebraicGeometry.Space.GroupOverField.isRepresentable_of_jacobsonSpace_algebraicClosure`:
  the statement above.
* `AlgebraicGeometry.Space.GroupOverField.exists_stage_isAffine_isOpenImmersion`: an affine open
  subspace of the base change of a space to an algebraic extension `Ω` comes from a finite
  subextension, provided the space is a quasi-separated scheme over some finite subextension.

## Implementation notes

The argument follows the source with two changes, which make Stacks 0B83, 0B86 and 0B87
unnecessary.

Let `g` be the image in `|H|` of a closed point of `H_Ω`. The fibre of `H_Ω ⟶ H` over `g` is
covered by `Spec(Ω ⊗_F Ω)` for `F` the perfect closure of `K` in `Ω`
(`AlgebraicGeometry.Space.GroupOverField.mem_range_of_pointsMap_snd_eq`), and `Ω ⊗_F Ω` is a
filtered colimit of finite products of copies of `Ω` since `Ω/F` is separable. So Stacks 0B7U
puts the fibre into an affine open `U` of `H_Ω`, without passing to the perfect closure of `K`
as the source does (that passage is what Stacks 0B83 is used for).

A quasi-compact open subspace `V ⊆ H` containing the image of `U` becomes a scheme over a finite
extension of `K` (Stacks 0B84), so `U` comes from an affine open `U_E` of `V_E` for a finite
subextension `E` of `Ω/K` (Stacks 01Z4). The fibre of the finite locally free surjection
`H_E ⟶ H` over `g` lies in `U_E`, so `g` is in the schematic locus of `H` by Stacks 0BA1; the
source instead passes to a Galois extension and uses Stacks 0B86 and 0B87.

The schematic locus of `H` is open, and its preimage in the Jacobson scheme `H_Ω` contains every
closed point, hence is everything; so the schematic locus is all of `H`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space.GroupOverField

attribute [local instance] pointTopology Over.cartesianMonoidalCategory

/-- Products of presheaves (instance search times out without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_JacobsonBaseChangeScheme
    {D : Type (u + 1)} [Category.{u} D] (J : Type) :
    HasLimitsOfShape (Discrete J) (Dᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

variable (K : Type u) [Field K] (C : BigFppfSite.{u}) (hK : C.Contains (Spec (.of K)))

/-- **The base change of a represented product, represented.** If `ζ₀` represents `h_{E₀} × V`
by `Z₀`, then the fibre product `L ×_{E₀} Z₀` along any `q : L ⟶ E₀` represents `h_L × V`. -/
noncomputable def pullbackProdIso {D : Type (u + 1)} [Category.{u} D] [HasPullbacks D]
    {V : Dᵒᵖ ⥤ Type u} {E₀ L Z₀ : D} (ζ₀ : yoneda.obj Z₀ ≅ yoneda.obj E₀ ⨯ V) (q : L ⟶ E₀) :
    yoneda.obj (pullback q (yoneda.preimage (ζ₀.hom ≫ prod.fst))) ≅ yoneda.obj L ⨯ V where
  hom := prod.lift (yoneda.map (pullback.fst _ _))
    (yoneda.map (pullback.snd _ _) ≫ ζ₀.hom ≫ prod.snd)
  inv := ((IsPullback.of_hasPullback q (yoneda.preimage (ζ₀.hom ≫ prod.fst))).map yoneda).lift
    prod.fst (prod.map (yoneda.map q) (𝟙 V) ≫ ζ₀.inv) (by simp)
  hom_inv_id := by
    let hpb := (IsPullback.of_hasPullback q (yoneda.preimage (ζ₀.hom ≫ prod.fst))).map yoneda
    apply hpb.hom_ext
    · rw [Category.assoc, hpb.lift_fst, Category.id_comp, prod.lift_fst]
    · rw [Category.assoc, hpb.lift_snd, Category.id_comp, ← Iso.cancel_iso_hom_right _ _ ζ₀]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply prod.hom_ext
      · simp only [Category.assoc, prod.map_fst, prod.lift_fst_assoc]
        rw [← Functor.map_comp, pullback.condition, Functor.map_comp, Functor.map_preimage]
      · simp
  inv_hom_id := by
    let hpb := (IsPullback.of_hasPullback q (yoneda.preimage (ζ₀.hom ≫ prod.fst))).map yoneda
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, Category.id_comp]
      exact hpb.lift_fst _ _ _
    · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
      rw [← Category.assoc, hpb.lift_snd]
      simp

/-- The first component of `pullbackProdIso` is the image under `yoneda` of the first pullback
projection. -/
@[reassoc (attr := simp)]
theorem pullbackProdIso_hom_fst {D : Type (u + 1)} [Category.{u} D] [HasPullbacks D]
    {V : Dᵒᵖ ⥤ Type u} {E₀ L Z₀ : D} (ζ₀ : yoneda.obj Z₀ ≅ yoneda.obj E₀ ⨯ V) (q : L ⟶ E₀) :
    (pullbackProdIso ζ₀ q).hom ≫ prod.fst = yoneda.map (pullback.fst _ _) :=
  prod.lift_fst _ _

/-- The second component of `pullbackProdIso` is the second pullback projection followed by the
second component of `ζ₀`. -/
@[reassoc (attr := simp)]
theorem pullbackProdIso_hom_snd {D : Type (u + 1)} [Category.{u} D] [HasPullbacks D]
    {V : Dᵒᵖ ⥤ Type u} {E₀ L Z₀ : D} (ζ₀ : yoneda.obj Z₀ ≅ yoneda.obj E₀ ⨯ V) (q : L ⟶ E₀) :
    (pullbackProdIso ζ₀ q).hom ≫ prod.snd =
      yoneda.map (pullback.snd _ _) ≫ ζ₀.hom ≫ prod.snd :=
  prod.lift_snd _ _

/-- `pullbackProdIso` is natural in the base change. -/
theorem pullbackProdIso_naturality {D : Type (u + 1)} [Category.{u} D] [HasPullbacks D]
    {V : Dᵒᵖ ⥤ Type u} {E₀ L L' Z₀ : D} (ζ₀ : yoneda.obj Z₀ ≅ yoneda.obj E₀ ⨯ V) (q : L ⟶ E₀)
    (q' : L' ⟶ E₀) (m : L' ⟶ L) (hm : m ≫ q = q') :
    yoneda.map (pullback.map q' _ q _ m (𝟙 _) (𝟙 _) (by simp [hm]) (by simp)) ≫
        (pullbackProdIso ζ₀ q).hom =
      (pullbackProdIso ζ₀ q').hom ≫ prod.map (yoneda.map m) (𝟙 V) := by
  apply prod.hom_ext
  · simp only [Category.assoc, pullbackProdIso_hom_fst, prod.map_fst,
      pullbackProdIso_hom_fst_assoc, ← Functor.map_comp, pullback.lift_fst]
  · simp only [Category.assoc, pullbackProdIso_hom_snd, prod.map_snd, Category.comp_id,
      ← Functor.map_comp_assoc, pullback.lift_snd]

/-- **An affine open of a base change to an algebraic extension comes from a finite stage,
for spaces.** Let `V` be a presheaf on the big fppf site of `Spec K` whose base change to a finite
subextension `E₀` of an algebraic extension `Ω/K` is represented by a quasi-separated scheme.
Every affine open subspace of `V_Ω` maps into an affine open subspace of `V_E` for some finite
subextension `E₀ ⊆ E ⊆ Ω`. -/
theorem exists_stage_isAffine_isOpenImmersion (Ω : Type u) [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (hΩ : C.Contains (Spec (.of Ω)))
    (V : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (E₀ : Stacks.Chow.FiniteSubextension K Ω) (hE₀ : C.Contains (Spec (.of E₀.1)))
    (Z₀ : BigFppfOver C (Spec (.of K)) hK)
    (ζ₀ : yoneda.obj Z₀ ≅ yoneda.obj (extObj C _ hK (Iso.refl _) E₀.1 hE₀) ⨯ V)
    [QuasiSeparatedSpace ((BigFppfOver.toScheme C _ hK).obj Z₀)]
    (A : BigFppfOver C (Spec (.of K)) hK) [IsAffine ((BigFppfOver.toScheme C _ hK).obj A)]
    (i : yoneda.obj A ⟶ yoneda.obj (extObj C _ hK (Iso.refl _) Ω hΩ) ⨯ V)
    (hi : IsOpenImmersion C _ hK i) :
    ∃ (E : Stacks.Chow.FiniteSubextension K Ω) (hE : C.Contains (Spec (.of E.1)))
      (A' : BigFppfOver C (Spec (.of K)) hK)
      (i' : yoneda.obj A' ⟶ yoneda.obj (extObj C _ hK (Iso.refl _) E.1 hE) ⨯ V),
      IsAffine ((BigFppfOver.toScheme C _ hK).obj A') ∧ IsOpenImmersion C _ hK i' ∧
        ∀ w ∈ Set.range (pointsMap C _ hK _ i),
          pointsMap C _ hK _ (prod.map (yoneda.map (extMap C _ hK (Iso.refl _)
            (hK := hE) (hK' := hΩ) E.1.val)) (𝟙 V)) w ∈ Set.range (pointsMap C _ hK _ i') := by
  classical
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme C _ hK) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  let T := BigFppfOver.toScheme C (Spec (.of K)) hK
  let E₀obj := extObj C _ hK (Iso.refl _) E₀.1 hE₀
  let s₀ : Z₀ ⟶ E₀obj := yoneda.preimage (ζ₀.hom ≫ prod.fst)
  let f : T.obj Z₀ ⟶ Spec (.of E₀.1) := T.map s₀
  let qΩ : extObj C _ hK (Iso.refl _) Ω hΩ ⟶ E₀obj :=
    extMap C _ hK (Iso.refl _) (hK := hE₀) (hK' := hΩ) E₀.1.val
  let ζΩ := pullbackProdIso ζ₀ qΩ
  let isoΩ : T.obj (pullback qΩ s₀) ≅
      pullback (Spec.map (CommRingCat.ofHom E₀.1.val.toRingHom)) f :=
    PreservesPullback.iso T qΩ s₀
  let j : A ⟶ pullback qΩ s₀ := yoneda.preimage (i ≫ ζΩ.inv)
  have hj : _root_.AlgebraicGeometry.IsOpenImmersion (T.map j) := by
    have h : IsOpenImmersion C _ hK (yoneda.map j) := by
      rw [Functor.map_preimage]
      exact MorphismProperty.RespectsIso.postcomp _ ζΩ.inv _ hi
    exact (MorphismProperty.of_relative_map (F := yoneda)
      (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) T) h :)
  let W := (T.map j ≫ isoΩ.hom).opensRange
  obtain ⟨E, h, U, hU, hpre⟩ :=
    exists_isAffineOpen_preimage_eq_finiteSubextension K Ω E₀ f W (isAffineOpen_opensRange _)
  have hE : C.Contains (Spec (.of E.1)) := contains_spec_of_isAlgebraic C K E.1 hK
  let qE : extObj C _ hK (Iso.refl _) E.1 hE ⟶ E₀obj :=
    extMap C _ hK (Iso.refl _) (hK := hE₀) (hK' := hE) (IntermediateField.inclusion h)
  let ζE := pullbackProdIso ζ₀ qE
  let isoE : T.obj (pullback qE s₀) ≅
      pullback (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)) f :=
    PreservesPullback.iso T qE s₀
  let U' := isoE.hom ⁻¹ᵁ U
  have hU' : IsAffineOpen U' := hU.preimage isoE.hom
  obtain ⟨A', u, hu, hrange, hA'⟩ := BigFppfOver.exists_affineOpen_restrict C _ hK _ ⟨U', hU'⟩
  refine ⟨E, hE, A', yoneda.map u ≫ ζE.hom, hA', ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.postcomp _ ζE.hom _
      (presheaf_yoneda_map_of_inverseImage C _ hK inferInstance u hu)
  rintro w ⟨a, rfl⟩
  let m : extObj C _ hK (Iso.refl _) Ω hΩ ⟶ extObj C _ hK (Iso.refl _) E.1 hE :=
    extMap C _ hK (Iso.refl _) (hK := hE) (hK' := hΩ) E.1.val
  have hm : m ≫ qE = qΩ := by
    simp only [m, qE, qΩ, extMap_comp]
    congr 1
  let r : pullback qΩ s₀ ⟶ pullback qE s₀ :=
    pullback.map qΩ s₀ qE s₀ m (𝟙 _) (𝟙 _) (by simp [hm]) (by simp)
  have hij : i = yoneda.map j ≫ ζΩ.hom := by simp [j]
  have hcomm : isoΩ.hom ≫ pullback.lift
      (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom E.1.val.toRingHom)) (pullback.snd _ _)
        (by rw [Category.assoc, ← Spec.map_comp, ← pullback.condition]; rfl) =
      T.map r ≫ isoE.hom := by
    have hΩfst : isoΩ.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom E₀.1.val.toRingHom)) f =
        T.map (pullback.fst qΩ s₀) := PreservesPullback.iso_hom_fst T qΩ s₀
    have hΩsnd : isoΩ.hom ≫ pullback.snd (Spec.map (CommRingCat.ofHom E₀.1.val.toRingHom)) f =
        T.map (pullback.snd qΩ s₀) := PreservesPullback.iso_hom_snd T qΩ s₀
    have hEfst : isoE.hom ≫ pullback.fst
        (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)) f =
        T.map (pullback.fst qE s₀) := PreservesPullback.iso_hom_fst T qE s₀
    have hEsnd : isoE.hom ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)) f =
        T.map (pullback.snd qE s₀) := PreservesPullback.iso_hom_snd T qE s₀
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hΩfst, Category.assoc, hEfst,
        ← T.map_comp, pullback.lift_fst, T.map_comp]
      rfl
    · rw [Category.assoc, pullback.lift_snd, hΩsnd, Category.assoc, hEsnd, ← T.map_comp,
        pullback.lift_snd, Category.comp_id]
  let x := schemePointsHomeomorph C _ hK A a
  have hx : T.map (j ≫ r) x ∈ U' := by
    change isoE.hom (T.map r (T.map j x)) ∈ U
    have h1 : (T.map j ≫ isoΩ.hom) x ∈ W := ⟨x, rfl⟩
    rw [← hpre] at h1
    change (isoΩ.hom ≫ pullback.lift _ _ _) (T.map j x) ∈ U at h1
    rwa [hcomm] at h1
  obtain ⟨y, hy⟩ : T.map (j ≫ r) x ∈ Set.range (T.map u) := by rwa [hrange]
  refine ⟨(schemePointsHomeomorph C _ hK A').symm y, ?_⟩
  have e1 : i ≫ prod.map (yoneda.map m) (𝟙 V) = yoneda.map (j ≫ r) ≫ ζE.hom := by
    rw [hij, Category.assoc, ← pullbackProdIso_naturality ζ₀ qE qΩ m hm, Functor.map_comp,
      Category.assoc]
  have e2 : (schemePointsHomeomorph C _ hK A).symm x = a := Homeomorph.symm_apply_apply _ _
  calc pointsMap C _ hK _ (yoneda.map u ≫ ζE.hom) ((schemePointsHomeomorph C _ hK A').symm y)
      = pointsMap C _ hK _ ζE.hom ((schemePointsHomeomorph C _ hK _).symm (T.map u y)) := by
        rw [pointsMap_comp, Function.comp_apply, schemePointsHomeomorph_symm_naturality]
    _ = pointsMap C _ hK _ ζE.hom (pointsMap C _ hK _ (yoneda.map (j ≫ r))
          ((schemePointsHomeomorph C _ hK A).symm x)) := by
        rw [hy, schemePointsHomeomorph_symm_naturality]
    _ = pointsMap C _ hK _ (prod.map (yoneda.map m) (𝟙 V)) (pointsMap C _ hK _ i a) := by
        rw [e2, ← Function.comp_apply (f := pointsMap C _ hK _ ζE.hom), ← pointsMap_comp,
          ← e1, pointsMap_comp, Function.comp_apply]

/-! ### Products with an open subspace -/

section ProdSubfunctor

variable {K C hK}

variable (X : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
  {H : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u} (V : Subfunctor H)

/-- The comparison of `X × V` with the preimage of `V` in `X × H`. -/
noncomputable def prodSubfunctorIso :
    X ⨯ V.toFunctor ≅ (V.preimage (prod.snd : X ⨯ H ⟶ H)).toFunctor :=
  (isPullback_prod_map_id_left V.ι X).isoIsPullback _ _ (Subfunctor.isPullback_preimage _ V)

/-- Composing `prodSubfunctorIso` with the inclusion of the preimage of `V` gives the map
`X × V ⟶ X × H` induced by the inclusion of `V`. -/
@[reassoc (attr := simp)]
theorem prodSubfunctorIso_hom_ι :
    (prodSubfunctorIso X V).hom ≫ (V.preimage (prod.snd : X ⨯ H ⟶ H)).ι =
      prod.map (𝟙 X) V.ι :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The points of `X × V` are the points of `X × H` whose second projection lies in `V`. -/
theorem range_pointsMap_prod_map_ι :
    Set.range (pointsMap C _ hK _ (prod.map (𝟙 X) V.ι)) =
      pointsMap C _ hK _ (prod.snd : X ⨯ H ⟶ H) ⁻¹'
        Set.range (pointsMap C _ hK _ V.ι) := by
  rw [← range_pointsMap_preimage_ι, ← prodSubfunctorIso_hom_ι, pointsMap_comp, Set.range_comp,
    (pointsMap_surjective_of_isIso C _ hK (prodSubfunctorIso X V).hom).range_eq, Set.image_univ]

/-- The product `X × V ⟶ X × H` with an open subspace is an open immersion. -/
theorem isOpenImmersion_prod_map_ι (hV : IsOpenSubspace C _ hK V) :
    IsOpenImmersion C _ hK (prod.map (𝟙 X) V.ι) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_prod_map_id_left V.ι X) hV.2

/-- The product of a representable product with an open subspace is representable. -/
theorem isRepresentable_prod_of_isOpenSubspace (hXH : IsAlgebraicSpace C _ hK (X ⨯ H))
    (hH : IsAlgebraicSpace C _ hK H) (hV : IsOpenSubspace C _ hK V)
    (hrep : (X ⨯ H).IsRepresentable) : (X ⨯ V.toFunctor).IsRepresentable := by
  have := isRepresentable_of_isOpenSubspace C _ hK hrep _
    (isOpenSubspace_preimage C _ hK (prod.snd : X ⨯ H ⟶ H) V hH hXH hV)
  exact isRepresentable_of_natIso _ (prodSubfunctorIso X V).symm

/-- An open immersion `h_A ⟶ X × H` whose points lie over an open subspace `V` of `H` factors
through an open immersion `h_A ⟶ X × V`. -/
private theorem exists_isOpenImmersion_comp_prod_map_ι (hXH : IsAlgebraicSpace C _ hK (X ⨯ H))
    (hH : IsAlgebraicSpace C _ hK H) (hV : IsOpenSubspace C _ hK V)
    {A : BigFppfOver C (Spec (.of K)) hK} (i : yoneda.obj A ⟶ X ⨯ H)
    (hi : IsOpenImmersion C _ hK i)
    (hsub : ∀ b, pointsMap C _ hK _ (prod.snd : X ⨯ H ⟶ H) (pointsMap C _ hK _ i b) ∈
      Set.range (pointsMap C _ hK _ V.ι)) :
    ∃ i' : yoneda.obj A ⟶ X ⨯ V.toFunctor,
      IsOpenImmersion C _ hK i' ∧ i' ≫ prod.map (𝟙 X) V.ι = i := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points C _ hK hXH
    (isAlgebraicSpace_yoneda C _ hK A) _
    (isOpenSubspace_preimage C _ hK (prod.snd : X ⨯ H ⟶ H) V hH hXH hV) i).2 (by
      rintro _ ⟨b, rfl⟩
      rw [range_pointsMap_preimage_ι]
      exact hsub b)
  have h : (g ≫ (prodSubfunctorIso X V).inv) ≫ prod.map (𝟙 X) V.ι = i := by
    rw [Category.assoc, ← prodSubfunctorIso_hom_ι, Iso.inv_hom_id_assoc, hg]
  exact ⟨g ≫ (prodSubfunctorIso X V).inv,
    isOpenImmersion_of_comp_mono C _ hK _ (prod.map (𝟙 X) V.ι) (by rwa [h]), h⟩

end ProdSubfunctor

/-- **A compact set of points lies in a quasi-compact open subspace.** Every point of an algebraic
space has a quasi-compact open neighbourhood (Stacks 04NN); finitely many of them cover a
compact set, their union is a compact open set of points, which is the point set of an open
subspace (Stacks 03BZ), quasi-compact by Stacks 03E4. -/
theorem exists_isQuasiCompactSpace_isOpenSubspace_superset
    {F : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace C _ hK F)
    (T : Set (points C _ hK F)) (hT : IsCompact T) :
    ∃ V : Subfunctor F, IsOpenSubspace C _ hK V ∧ IsQuasiCompactSpace C _ hK V.toFunctor ∧
      T ⊆ Set.range (pointsMap C _ hK V.toFunctor V.ι) := by
  classical
  have hW : ∀ x : points C _ hK F, ∃ W : Set (points C _ hK F), IsOpen W ∧ IsCompact W ∧ x ∈ W :=
    fun x => (hasBasis_nhds_isOpen_isCompact C _ hK F hF x).ex_mem
  choose W hWo hWc hxW using hW
  obtain ⟨t, -, ht⟩ := hT.elim_nhds_subcover W fun x _ => (hWo x).mem_nhds (hxW x)
  let O := ⋃ x ∈ t, W x
  have hOc : IsCompact O := t.isCompact_biUnion fun x _ => hWc x
  obtain ⟨V, hV, hVrange⟩ :=
    exists_isOpenSubspace_range_pointsMap_eq C _ hK hF O (isOpen_biUnion fun x _ => hWo x)
  refine ⟨V, hV, ?_, hVrange ▸ ht⟩
  refine (isQuasiCompactSpace_iff_compactSpace_points C _ hK V.toFunctor hV.1).2 ⟨?_⟩
  refine (isEmbedding_pointsMap_of_isImmersion C _ hK hF V.ι
    (isImmersion_of_isOpenImmersion C _ hK hV.2)).isCompact_iff.mpr ?_
  rwa [Set.image_univ, hVrange]

/-- The spectrum of an extension `L/K` as an object of the big fppf site of `Spec K` is the same
in the two spellings `extObj` (for the identity of `Spec K`) and `Over.mk (specExtensionHom _)`. -/
theorem over_mk_specExtensionHom_eq_extObj (L : Type u) [Field L] [Algebra K L]
    (hL : C.Contains (Spec (.of L))) :
    Over.mk (specExtensionHom K L C hK hL) = extObj C (Spec (.of K)) hK (Iso.refl _) L hL := by
  unfold extObj specExtensionHom
  congr 1

/-- A quasi-separated algebraic space over a field is absolutely quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparatedOver
    {F : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace C _ hK F)
    (hFqs : IsQuasiSeparatedOver C _ hK F) :
    IsAbsolutelyQuasiSeparated C _ hK C.contains_terminal F :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated C _ hK C.contains_terminal hF
    (isAbsolutelyQuasiSeparated_yoneda_obj_of_isAffine K C hK (Over.mk (𝟙 (C.obj hK)))
      (inferInstanceAs (IsAffine (Spec (.of K)))))
    (isQuasiSeparated_of_isQuasiSeparatedOver C _ hK hFqs
      ((IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).from F))

/-- Naturality of the identification of the points of a represented presheaf with the points of
the representing scheme. -/
private theorem map_schemePointsHomeomorph {U V : BigFppfOver C (Spec (.of K)) hK} (g : U ⟶ V)
    (t : points C _ hK (yoneda.obj U)) :
    (BigFppfOver.toScheme C _ hK).map g (schemePointsHomeomorph C _ hK U t) =
      schemePointsHomeomorph C _ hK V (pointsMap C _ hK _ (yoneda.map g) t) := by
  apply (schemePointsHomeomorph C _ hK V).symm.injective
  rw [Homeomorph.symm_apply_apply, ← schemePointsHomeomorph_symm_naturality,
    Homeomorph.symm_apply_apply]

/-- A point of `F` lies in the image of `h_A ⟶ h_Y ≅ F` exactly when the corresponding point of
the scheme of `Y` lies in the image of the scheme of `A`. -/
private theorem mem_range_pointsMap_yoneda_map_comp_iff
    {F : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u} {Y A : BigFppfOver C (Spec (.of K)) hK}
    (ε : yoneda.obj Y ≅ F) (u : A ⟶ Y) (w : points C _ hK F) :
    w ∈ Set.range (pointsMap C _ hK _ (yoneda.map u ≫ ε.hom)) ↔
      ((pointsHomeomorphOfIso C _ hK ε).symm.trans (schemePointsHomeomorph C _ hK Y)) w ∈
        Set.range ((BigFppfOver.toScheme C _ hK).map u) := by
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨schemePointsHomeomorph C _ hK _ b, ?_⟩
    change _ = schemePointsHomeomorph C _ hK Y (pointsMap C _ hK _ ε.inv
      (pointsMap C _ hK _ (yoneda.map u ≫ ε.hom) b))
    rw [← Function.comp_apply (f := pointsMap C _ hK _ ε.inv), ← pointsMap_comp,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact map_schemePointsHomeomorph K C hK u b
  · rintro ⟨y, hy⟩
    refine ⟨(schemePointsHomeomorph C _ hK A).symm y, ?_⟩
    rw [pointsMap_comp, Function.comp_apply, schemePointsHomeomorph_symm_naturality, hy]
    change pointsMap C _ hK _ ε.hom ((schemePointsHomeomorph C _ hK Y).symm
      (schemePointsHomeomorph C _ hK Y (pointsMap C _ hK _ ε.inv w))) = w
    rw [Homeomorph.symm_apply_apply, ← Function.comp_apply (f := pointsMap C _ hK _ ε.hom),
      ← pointsMap_comp, Iso.inv_hom_id, pointsMap_id, id_eq]

/-- The base change `h_Ω × H ⟶ h_E × H` along a subextension `E` of `Ω/K` is surjective on
points. -/
private theorem surjective_pointsMap_prod_map_extMap (Ω : Type u) [Field Ω] [Algebra K Ω]
    (hΩ : C.Contains (Spec (.of Ω))) (E : IntermediateField K Ω)
    (hE : C.Contains (Spec (.of E))) (H : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u) :
    Function.Surjective (pointsMap C _ hK _ (prod.map (yoneda.map
      (extMap C _ hK (Iso.refl _) (hK := hE) (hK' := hΩ) E.val)) (𝟙 H))) := by
  apply isSurjective_of_presheafSurjective
  refine (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_prod_fst_with_id _ H) ?_
  refine presheaf_yoneda_map_of_inverseImage C _ hK inferInstance _ ?_
  change Surjective (Spec.map _)
  exact ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

/-- **A finite base change that is a scheme, inside the algebraic closure.** Let `V` be a
quasi-separated algebraic space over `Spec K` whose base change to a finite extension `k'/K` is
a scheme. Then for the image `E₀` of an embedding of `k'` into the algebraic closure `Ω` of `K`,
the product `h_{E₀} × V` is represented by an object of the site whose scheme is
quasi-separated. -/
theorem exists_finiteSubextension_representation
    (V : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace C _ hK V)
    (hVqs : IsQuasiSeparatedOver C _ hK V) (k' : Type u) [Field k'] [Algebra K k']
    [FiniteDimensional K k'] (hk' : C.Contains (Spec (.of k')))
    (h : ((OverShriek.relocalizeRestrict (specExtensionHom K k' C hK hk')).obj V).IsRepresentable) :
    ∃ (E₀ : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K E₀)
      (hE₀ : C.Contains (Spec (.of E₀))) (Z₀ : BigFppfOver C (Spec (.of K)) hK)
      (_ : yoneda.obj Z₀ ≅ yoneda.obj (extObj C _ hK (Iso.refl _) E₀ hE₀) ⨯ V),
      QuasiSeparatedSpace ((BigFppfOver.toScheme C _ hK).obj Z₀) := by
  classical
  let Ω := AlgebraicClosure K
  let σ : k' →ₐ[K] Ω := IsAlgClosed.lift
  let E₀ : IntermediateField K Ω := σ.fieldRange
  let τ : k' ≃ₐ[K] E₀ := AlgEquiv.ofInjectiveField σ
  have : FiniteDimensional K E₀ := LinearEquiv.finiteDimensional τ.toLinearEquiv
  have hE₀ : C.Contains (Spec (.of E₀)) := contains_spec_of_isAlgebraic C K E₀ hK
  -- the base change to `E₀` is a scheme
  let g : C.obj hE₀ ⟶ C.obj hk' := ObjectProperty.homMk (Spec.map (CommRingCat.ofHom τ.toRingHom))
  have hg : g ≫ specExtensionHom K k' C hK hk' = specExtensionHom K E₀ C hK hE₀ := by
    apply ObjectProperty.hom_ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact congrArg Subtype.val (τ.commutes c)
  have hE₀rep : ((OverShriek.relocalizeRestrict (specExtensionHom K E₀ C hK hE₀)).obj
      V).IsRepresentable := by
    rw [← hg]
    exact isRepresentable_relocalizeRestrict_comp g _ V h
  have hprod := isRepresentable_prod_of_isRepresentable_relocalizeRestrict C (Spec (.of E₀))
    (Spec (.of K)) hE₀ hK (specExtensionHom K E₀ C hK hE₀) V hE₀rep
  rw [over_mk_specExtensionHom_eq_extObj K C hK E₀ hE₀] at hprod
  let EE := extObj C (Spec (.of K)) hK (Iso.refl _) E₀ hE₀
  refine ⟨E₀, inferInstance, hE₀, (yoneda.obj EE ⨯ V).reprX, (yoneda.obj EE ⨯ V).reprW, ?_⟩
  -- quasi-separatedness
  let Z₀ := (yoneda.obj EE ⨯ V).reprX
  have hsnd : IsQuasiSeparated C _ hK (prod.snd : yoneda.obj EE ⨯ V ⟶ V) :=
    isQuasiSeparated_of_isPullback C _ hK (isPullback_prod_fst_snd_yoneda_obj EE V)
      ((isQuasiSeparated_yoneda_map_iff C _ hK _).2 (by
        rw [toScheme_map_from_extObj]
        infer_instance))
  have hprodqs : IsQuasiSeparatedOver C _ hK (yoneda.obj EE ⨯ V) :=
    isQuasiSeparatedOver_of_isQuasiSeparated C _ hK (isAlgebraicSpace_prod_yoneda_obj EE hV)
      hVqs hsnd
  have : Mono (yoneda.obj EE ⨯ V).reprW.hom := IsIso.mono_of_iso _
  have hZqs : IsQuasiSeparatedOver C _ hK (yoneda.obj Z₀) :=
    isQuasiSeparatedOver_of_mono C _ hK (yoneda.obj EE ⨯ V).reprW.hom hprodqs
  have hterm : IsTerminal (yoneda.obj (Over.mk (𝟙 (C.obj hK)))) :=
    IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  have hdiag := (isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal C _ hK hterm
    (yoneda.map (Over.mkIdTerminal.from Z₀))).1 hZqs
  have hqs := (diagonalProp_quasiCompact_yoneda_map_iff C _ hK _).1 hdiag
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme C _ hK).obj (Over.mk (𝟙 (C.obj hK)))) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of K)))
  exact quasiSeparatedSpace_of_quasiSeparated
    ((BigFppfOver.toScheme C _ hK).map (Over.mkIdTerminal.from Z₀))

/-- **Stacks 0B84 (2) for a quasi-compact open subspace.** If `V` is a quasi-compact open
subspace of a quasi-separated space `H` over `K` with `h_Ω × V` representable, then `h_{E₀} × V`
is represented by a quasi-separated scheme for a finite subextension `E₀` of `Ω/K`. -/
private theorem exists_finiteSubextension_representation_of_isQuasiCompactSpace
    {H : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u} (hHqs : IsQuasiSeparatedOver C _ hK H)
    (V : Subfunctor H) (hVo : IsOpenSubspace C _ hK V)
    (hVqc : IsQuasiCompactSpace C _ hK V.toFunctor)
    (hVΩ : (yoneda.obj (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
      (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯
        V.toFunctor).IsRepresentable) :
    ∃ (E₀ : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K E₀)
      (hE₀ : C.Contains (Spec (.of E₀))) (Z₀ : BigFppfOver C (Spec (.of K)) hK)
      (_ : yoneda.obj Z₀ ≅ yoneda.obj (extObj C _ hK (Iso.refl _) E₀ hE₀) ⨯ V.toFunctor),
      QuasiSeparatedSpace ((BigFppfOver.toScheme C _ hK).obj Z₀) := by
  have hVqs : IsQuasiSeparatedOver C _ hK V.toFunctor :=
    isQuasiSeparatedOver_subfunctor C _ hK hHqs V
  rw [← over_mk_specExtensionHom_eq_extObj] at hVΩ
  obtain ⟨k', _, _, _, _, hk', hk'rep⟩ :=
    exists_finite_separable_isRepresentable_relocalizeRestrict K (AlgebraicClosure K) C hK
      (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK) V.toFunctor hVo.1 hVqc
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedOver K C hK hVo.1 hVqs)
      (isRepresentable_relocalizeRestrict_of_isRepresentable_prod _ _
        (isRepresentable_of_natIso _ (FunctorToTypes.binaryProductIso _ _)))
  exact exists_finiteSubextension_representation K C hK V.toFunctor hVo.1 hVqs k' hk' hk'rep

/-- **A rational point of `H_Ω` over a point of `H`.** If `x` is a point of `H_Ω` in the image of
a section `s` of `H_Ω ⟶ Spec Ω`, then the image of `x` in `H` is the class of an `Ω`-point
of `H`. -/
private theorem exists_pointsMap_snd_eq_class_ptOf (Ω : Type u) [Field Ω] [Algebra K Ω]
    (hΩ : C.Contains (Spec (.of Ω))) {H : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u}
    {Y : Over (extObj C _ hK (Iso.refl _) Ω hΩ)}
    (ε : yoneda.obj Y.left ≅ yoneda.obj (extObj C _ hK (Iso.refl _) Ω hΩ) ⨯ H)
    (s : (BigFppfOver.toScheme C _ hK).obj (extObj C _ hK (Iso.refl _) Ω hΩ) ⟶
      (BigFppfOver.toScheme C _ hK).obj Y.left)
    (hs : s ≫ (BigFppfOver.toScheme C _ hK).map Y.hom = 𝟙 _)
    (x : (BigFppfOver.toScheme C _ hK).obj Y.left) (hx : x ∈ Set.range s.base) :
    ∃ x₀ : yoneda.obj (extObj C _ hK (Iso.refl _) Ω hΩ) ⟶ H,
      pointsMap C _ hK _ (prod.snd : yoneda.obj (extObj C _ hK (Iso.refl _) Ω hΩ) ⨯ H ⟶ H)
          (((pointsHomeomorphOfIso C _ hK ε).symm.trans
            (schemePointsHomeomorph C _ hK Y.left)).symm x) =
        (ptOf C _ hK (Iso.refl _) H Ω hΩ x₀).class C _ hK H := by
  let T := BigFppfOver.toScheme C (Spec (.of K)) hK
  let EΩ := extObj C (Spec (.of K)) hK (Iso.refl _) Ω hΩ
  have hYw : Y.hom.left ≫ EΩ.hom = Y.left.hom := Over.w Y.hom
  let a₀ : EΩ ⟶ Y.left := Over.homMk ⟨s⟩ (by
    rw [← hYw, ← Category.assoc]
    apply ObjectProperty.hom_ext
    change (s ≫ T.map Y.hom) ≫ EΩ.hom.hom = EΩ.hom.hom
    rw [hs, Category.id_comp])
  obtain ⟨z, hz⟩ := hx
  obtain ⟨z, hxa⟩ : ∃ z : T.obj EΩ, x = T.map a₀ z := ⟨z, hz.symm⟩
  have := subsingleton_points_yoneda_fieldSpec C _ hK Ω hΩ
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ (Iso.refl _).inv)
  refine ⟨yoneda.map a₀ ≫ ε.hom ≫ prod.snd, ?_⟩
  have h1 : pointsMap C _ hK _ ε.hom ((schemePointsHomeomorph C _ hK Y.left).symm x) =
      pointsMap C _ hK _ (yoneda.map a₀ ≫ ε.hom)
        ((ptOf C _ hK (Iso.refl _) _ Ω hΩ (𝟙 _)).class C _ hK _) := by
    rw [hxa, ← schemePointsHomeomorph_symm_naturality, pointsMap_comp, Function.comp_apply]
    congr 2
    exact Subsingleton.elim _ _
  change pointsMap C _ hK _ prod.snd
    (pointsMap C _ hK _ ε.hom ((schemePointsHomeomorph C _ hK Y.left).symm x)) = _
  rw [h1, ← Function.comp_apply (f := pointsMap C _ hK _ prod.snd), ← pointsMap_comp,
    pointsMap_class, ptOf_map, Category.id_comp, Category.assoc]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search through binary products (`⨯`, `prod.map`) of presheaves on the big fppf site
/-- **An affine open of `H_Ω` descends to a finite stage.** If `H` is a quasi-separated algebraic
space over `K` with `h_Y ≅ h_Ω × H`, then an affine open `U` of the scheme of `Y` maps into an
affine open subspace of `h_E × H` for a finite subextension `E` of `Ω/K`. -/
private theorem exists_stage_isAffine_isOpenImmersion_of_isAffineOpen
    {H : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace C _ hK H)
    (hPqs : IsQuasiSeparatedOver C _ hK H) (Y : BigFppfOver C (Spec (.of K)) hK)
    (ε : yoneda.obj Y ≅ yoneda.obj (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
      (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯ H)
    (U : ((BigFppfOver.toScheme C _ hK).obj Y).Opens) (hU : IsAffineOpen U) :
    ∃ (E : Stacks.Chow.FiniteSubextension K (AlgebraicClosure K))
      (hE : C.Contains (Spec (.of E.1))) (A' : BigFppfOver C (Spec (.of K)) hK)
      (i' : yoneda.obj A' ⟶ yoneda.obj (extObj C _ hK (Iso.refl _) E.1 hE) ⨯ H),
      IsAffine ((BigFppfOver.toScheme C _ hK).obj A') ∧ IsOpenImmersion C _ hK i' ∧
        ∀ w, ((pointsHomeomorphOfIso C _ hK ε).symm.trans (schemePointsHomeomorph C _ hK Y)) w ∈
            U →
          pointsMap C _ hK _ (prod.map (yoneda.map (extMap C _ hK (Iso.refl _) (hK := hE)
            (hK' := contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK) E.1.val)) (𝟙 H))
              w ∈ Set.range (pointsMap C _ hK _ i') := by
  classical
  let Ω := AlgebraicClosure K
  let hΩ : C.Contains (Spec (.of Ω)) := contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK
  let EΩ := extObj C (Spec (.of K)) hK (Iso.refl _) Ω hΩ
  let θ : points C _ hK (yoneda.obj EΩ ⨯ H) ≃ₜ (BigFppfOver.toScheme C _ hK).obj Y :=
    (pointsHomeomorphOfIso C _ hK ε).symm.trans (schemePointsHomeomorph C _ hK Y)
  let πΩ := pointsMap C _ hK _ (prod.snd : yoneda.obj EΩ ⨯ H ⟶ H)
  have hπΩ : Continuous πΩ := continuous_pointsMap C _ hK _
  obtain ⟨V, hVo, hVqc, hVsub⟩ := exists_isQuasiCompactSpace_isOpenSubspace_superset K C hK hP
    (πΩ '' (θ.symm '' (U : Set ((BigFppfOver.toScheme C _ hK).obj Y))))
    ((hU.isCompact.image θ.symm.continuous).image hπΩ)
  have hHΩ : IsAlgebraicSpace C _ hK (yoneda.obj EΩ ⨯ H) := isAlgebraicSpace_prod_yoneda_obj EΩ hP
  obtain ⟨E₀, hfin, hE₀, Z₀, ζ₀, hqs⟩ :=
    exists_finiteSubextension_representation_of_isQuasiCompactSpace K C hK hPqs V hVo hVqc
      (isRepresentable_prod_of_isOpenSubspace (yoneda.obj EΩ) V hHΩ hP hVo
        (isRepresentable_of_natIso _ ε))
  obtain ⟨AΩ, u, hu, hrange, hAaff⟩ := BigFppfOver.exists_affineOpen_restrict C _ hK Y ⟨U, hU⟩
  let iH : yoneda.obj AΩ ⟶ yoneda.obj EΩ ⨯ H := yoneda.map u ≫ ε.hom
  have hiH : IsOpenImmersion C _ hK iH := MorphismProperty.RespectsIso.postcomp _ ε.hom _
    (presheaf_yoneda_map_of_inverseImage C _ hK inferInstance u hu)
  have hrangeH : ∀ w, w ∈ Set.range (pointsMap C _ hK _ iH) ↔ θ w ∈ U := fun w =>
    (mem_range_pointsMap_yoneda_map_comp_iff K C hK ε u w).trans (Set.ext_iff.mp hrange _)
  obtain ⟨iΩ, hiΩo, hiΩ⟩ := exists_isOpenImmersion_comp_prod_map_ι (yoneda.obj EΩ) V hHΩ hP hVo
    iH hiH fun b => hVsub ⟨pointsMap C _ hK _ iH b,
      ⟨θ (pointsMap C _ hK _ iH b), (hrangeH _).1 ⟨b, rfl⟩, θ.symm_apply_apply _⟩, rfl⟩
  obtain ⟨E, hE, A', i', hA', hi', hcompat⟩ := exists_stage_isAffine_isOpenImmersion K C hK Ω
    hΩ V.toFunctor ⟨E₀, hfin⟩ hE₀ Z₀ ζ₀ AΩ iΩ hiΩo
  refine ⟨E, hE, A', i' ≫ prod.map (𝟙 _) V.ι, hA',
    MorphismProperty.comp_mem _ _ _ hi' (isOpenImmersion_prod_map_ι _ V hVo), fun w hw => ?_⟩
  obtain ⟨b, hb⟩ := (hrangeH w).2 hw
  obtain ⟨c, hc⟩ := hcompat _ ⟨b, rfl⟩
  refine ⟨c, ?_⟩
  rw [pointsMap_comp, Function.comp_apply, hc, ← hb, ← hiΩ]
  simp only [← Function.comp_apply (f := pointsMap C _ hK _ _), ← pointsMap_comp]
  congr 1
  apply prod.hom_ext <;> simp <;> rfl

/-- **A point whose geometric fibre lies in an affine open is schematic.** Let `H` be a
quasi-separated algebraic space over `K` with `h_Y ≅ h_Ω × H`. If the fibre of `H_Ω ⟶ H` over a
point `g` of `H` lies in an affine open of the scheme of `Y`, then `g` lies in the schematic
locus of `H` (Stacks 0BA1). -/
private theorem mem_range_schematicLocus_of_forall_mem_isAffineOpen
    {H : (BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace C _ hK H)
    (hPqs : IsQuasiSeparatedOver C _ hK H) (Y : BigFppfOver C (Spec (.of K)) hK)
    (ε : yoneda.obj Y ≅ yoneda.obj (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
      (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯ H)
    (U : ((BigFppfOver.toScheme C _ hK).obj Y).Opens) (hU : IsAffineOpen U)
    (g : points C _ hK H)
    (hfibU : ∀ w : points C _ hK (yoneda.obj (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
        (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯ H),
      pointsMap C _ hK _ prod.snd w = g →
        ((pointsHomeomorphOfIso C _ hK ε).symm.trans (schemePointsHomeomorph C _ hK Y)) w ∈ U) :
    g ∈ Set.range (pointsMap C _ hK _ (schematicLocus C _ hK H).ι) := by
  let Ω := AlgebraicClosure K
  let hΩ : C.Contains (Spec (.of Ω)) := contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK
  let EΩ := extObj C (Spec (.of K)) hK (Iso.refl _) Ω hΩ
  let πΩ := pointsMap C _ hK _ (prod.snd : yoneda.obj EΩ ⨯ H ⟶ H)
  obtain ⟨E, hE, A', i', hA', hi', hcompat⟩ :=
    exists_stage_isAffine_isOpenImmersion_of_isAffineOpen K C hK hP hPqs Y ε U hU
  have : FiniteDimensional K E.1 := E.2
  let EE := extObj C _ hK (Iso.refl _) E.1 hE
  have hHE : IsAlgebraicSpace C _ hK (yoneda.obj EE ⨯ H) := isAlgebraicSpace_prod_yoneda_obj EE hP
  let mE : EΩ ⟶ EE := extMap C _ hK (Iso.refl _) (hK := hE) (hK' := hΩ) E.1.val
  let ρ : yoneda.obj EΩ ⨯ H ⟶ yoneda.obj EE ⨯ H := prod.map (yoneda.map mE) (𝟙 H)
  have hρsurj : Function.Surjective (pointsMap C _ hK _ ρ) :=
    surjective_pointsMap_prod_map_extMap K C hK Ω hΩ E.1 hE H
  have hsurjE := presheaf_prod_snd (P := @Surjective) inferInstance EE H
    (surjective_extObj C _ hK (Iso.refl _) E.1 hE)
  have hflfE := presheaf_prod_snd (P := @Stacks.Morphisms.IsFiniteLocallyFree) inferInstance EE H
    (isFiniteLocallyFree_extObj C _ hK (Iso.refl _) E.1 hE)
  refine (mem_range_pointsMap_schematicLocus_iff_exists_isAffine_isOpenImmersion C _ hK
    (X := ⟨yoneda.obj EE ⨯ H, hHE⟩) (Y := ⟨H, hP⟩) (ObjectProperty.homMk prod.snd)
    hsurjE hflfE _).2 ⟨A', i', hA', hi', ?_⟩
  intro z hz
  obtain ⟨w, rfl⟩ := hρsurj z
  refine hcompat w (hfibU w ?_)
  rw [← hz]
  change πΩ w = pointsMap C _ hK _ prod.snd (pointsMap C _ hK _ ρ w)
  rw [← Function.comp_apply (f := pointsMap C _ hK _ prod.snd), ← pointsMap_comp,
    show ρ ≫ prod.snd = prod.snd by simp [ρ]]

/-- **The fibre over the image of a rational point lies in an affine open.** In the setting of
`isRepresentable_of_jacobsonSpace_algebraicClosure`, the fibre of `H_Ω ⟶ H` over the class of an
`Ω`-point `x₀` of `H` lies in an affine open of `H_Ω` (Stacks 0B7U, applied to the cover of the
fibre by `Spec (Ω ⊗_F Ω)`). -/
private theorem exists_isAffineOpen_forall_mem_of_pointsMap_snd_eq
    (P : Grp ((BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u))
    (Y : Over (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
      (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)))
    (eY : (Over.post yoneda).obj Y ≅ Over.mk (prod.fst : yoneda.obj (extObj C _ hK (Iso.refl _)
      (AlgebraicClosure K) (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯ P.X ⟶ _))
    (hJ : JacobsonSpace (grpOverOfIso C _ hK _ (Grp.mk (Over.mk (prod.fst : yoneda.obj
      (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
        (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯ P.X ⟶ _))) Y eY).X.left)
    (hrat : ∀ x : (grpOverOfIso C _ hK _ (Grp.mk (Over.mk (prod.fst : yoneda.obj
        (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
          (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯
          P.X ⟶ _))) Y eY).X.left, IsClosed ({x} : Set _) →
      ∃ p : Over.mk (𝟙 (Spec (.of (AlgebraicClosure K)))) ⟶
          (grpOverOfIso C _ hK _ (Grp.mk (Over.mk (prod.fst : yoneda.obj
            (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
              (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯ P.X ⟶ _))) Y eY).X,
        p.left.base (⊥ : PrimeSpectrum (AlgebraicClosure K)) = x)
    (x₀ : yoneda.obj (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
      (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⟶ P.X) :
    ∃ U : ((BigFppfOver.toScheme C _ hK).obj Y.left).Opens, IsAffineOpen U ∧
      ∀ w : points C _ hK (yoneda.obj (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
          (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯ P.X),
        pointsMap C _ hK _ prod.snd w = (ptOf C _ hK (Iso.refl _) P.X (AlgebraicClosure K)
          (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK) x₀).class C _ hK P.X →
        ((pointsHomeomorphOfIso C _ hK ((Over.forget _).mapIso eY)).symm.trans
          (schemePointsHomeomorph C _ hK Y.left)) w ∈ U := by
  classical
  let Ω := AlgebraicClosure K
  let hΩ : C.Contains (Spec (.of Ω)) := contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK
  let EΩ := extObj C (Spec (.of K)) hK (Iso.refl _) Ω hΩ
  let H := P.X
  let Γ := grpOverOfIso C _ hK _ (Grp.mk (Over.mk (prod.fst : yoneda.obj EΩ ⨯ H ⟶ _))) Y eY
  let ε : yoneda.obj Y.left ≅ yoneda.obj EΩ ⨯ H := (Over.forget _).mapIso eY
  have hε : ε.hom ≫ prod.fst = yoneda.map Y.hom := Over.w eY.hom
  let A := Ω ⊗[perfectClosure K Ω] Ω
  have hA : C.Contains (Spec (.of A)) := C.contains_spec_tensorProduct hΩ hΩ
  let i₁ : Ω →ₐ[K] A := (Algebra.TensorProduct.includeLeft
    (S := perfectClosure K Ω)).restrictScalars K
  let i₂ : Ω →ₐ[K] A := (Algebra.TensorProduct.includeRight
    (R := perfectClosure K Ω) (A := Ω) (B := Ω)).restrictScalars K
  let Φ : yoneda.obj (algObj C _ hK (Iso.refl _) A hA) ⟶ yoneda.obj EΩ ⨯ H :=
    prod.lift (yoneda.map (algMap C _ hK (Iso.refl _) (hA := hA) (hK := hΩ) i₁))
      (yoneda.map (algMap C _ hK (Iso.refl _) (hA := hA) (hK := hΩ) i₂) ≫ x₀)
  let Φ' : algObj C _ hK (Iso.refl _) A hA ⟶ Y.left := yoneda.preimage (Φ ≫ ε.inv)
  have hΦ' : yoneda.map Φ' = Φ ≫ ε.inv := Functor.map_preimage _ _
  have hΦ'Y : Φ' ≫ Y.hom = algMap C _ hK (Iso.refl _) (hA := hA) (hK := hΩ) i₁ := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hΦ', Category.assoc, ← hε, Iso.inv_hom_id_assoc, prod.lift_fst]
  let fT : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ω A))) ⟶ Γ.X :=
    Over.homMk ((BigFppfOver.toScheme C _ hK).map Φ') (by
      change (BigFppfOver.toScheme C _ hK).map Φ' ≫
        (BigFppfOver.toScheme C _ hK).map Y.hom = _
      rw [← Functor.map_comp, hΦ'Y]
      change Spec.map (CommRingCat.ofHom i₁.toRingHom) = _
      congr 2)
  have := hJ
  obtain ⟨U, hU, hUT⟩ := exists_affineOpen_range_subset Ω A Γ hrat
    (isFilteredColimitOfFiniteProducts_perfectClosureTensor (k := K) Ω) fT
  refine ⟨U, hU, fun w hw => ?_⟩
  obtain ⟨t, rfl⟩ := mem_range_of_pointsMap_snd_eq C _ hK (Iso.refl _) H Ω hΩ x₀ A hA i₁ i₂
    (fun M _ _ α β => exists_algHom_perfectClosureTensor Ω M α β) w hw
  apply hUT
  refine ⟨schemePointsHomeomorph C _ hK _ t, ?_⟩
  change (BigFppfOver.toScheme C _ hK).map Φ' (schemePointsHomeomorph C _ hK _ t) =
    schemePointsHomeomorph C _ hK Y.left (pointsMap C _ hK _ ε.inv (pointsMap C _ hK _ Φ t))
  rw [← Function.comp_apply (f := pointsMap C _ hK _ ε.inv), ← pointsMap_comp, ← hΦ']
  exact map_schemePointsHomeomorph K C hK Φ' t

/-- **A group algebraic space over `K` whose base change to `Ω` is a Jacobson scheme with
rational closed points is a scheme.** Here `P` is a group object of presheaves on the big fppf
site of `Spec K` whose underlying presheaf is an algebraic space, `Y` represents its base change
to the algebraic closure `Ω` of `K`, and the group scheme it defines is Jacobson with all closed
points `Ω`-rational. Quasi-separatedness of `P.X` is what Stacks 0B84 part (2) needs for the
quasi-compact open subspaces of `P.X`. -/
theorem isRepresentable_of_jacobsonSpace_algebraicClosure
    (P : Grp ((BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u))
    (hP : IsAlgebraicSpace C _ hK P.X)
    (Y : Over (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
      (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)))
    (eY : (Over.post yoneda).obj Y ≅ Over.mk (prod.fst : yoneda.obj (extObj C _ hK (Iso.refl _)
      (AlgebraicClosure K) (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯ P.X ⟶ _))
    (hJ : JacobsonSpace (grpOverOfIso C _ hK _ (Grp.mk (Over.mk (prod.fst : yoneda.obj
      (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
        (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯
        P.X ⟶ _))) Y eY).X.left)
    (hrat : ∀ x : (grpOverOfIso C _ hK _ (Grp.mk (Over.mk (prod.fst : yoneda.obj
        (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
          (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯
          P.X ⟶ _))) Y eY).X.left, IsClosed ({x} : Set _) →
      ∃ p : Over.mk (𝟙 (Spec (.of (AlgebraicClosure K)))) ⟶
          (grpOverOfIso C _ hK _ (Grp.mk (Over.mk (prod.fst : yoneda.obj
            (extObj C _ hK (Iso.refl _) (AlgebraicClosure K)
              (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK)) ⨯ P.X ⟶ _))) Y eY).X,
        p.left.base (⊥ : PrimeSpectrum (AlgebraicClosure K)) = x)
    (hPqs : IsQuasiSeparatedOver C _ hK P.X) :
    P.X.IsRepresentable := by
  classical
  let Ω := AlgebraicClosure K
  let hΩ : C.Contains (Spec (.of Ω)) := contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK
  let EΩ := extObj C (Spec (.of K)) hK (Iso.refl _) Ω hΩ
  let H := P.X
  let Γ := grpOverOfIso C _ hK _ (Grp.mk (Over.mk (prod.fst : yoneda.obj EΩ ⨯ H ⟶ _))) Y eY
  let ε : yoneda.obj Y.left ≅ yoneda.obj EΩ ⨯ H := (Over.forget _).mapIso eY
  let θ : points C _ hK (yoneda.obj EΩ ⨯ H) ≃ₜ Γ.X.left :=
    (pointsHomeomorphOfIso C _ hK ε).symm.trans (schemePointsHomeomorph C _ hK Y.left)
  let πΩ := pointsMap C _ hK _ (prod.snd : yoneda.obj EΩ ⨯ H ⟶ H)
  have hπΩ : Continuous πΩ := continuous_pointsMap C _ hK _
  obtain ⟨hLo, hLr⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace C _ hK hP
  let L := schematicLocus C _ hK H
  -- the main claim: images of closed points lie in the schematic locus
  have key : ∀ x : Γ.X.left, IsClosed ({x} : Set _) →
      πΩ (θ.symm x) ∈ Set.range (pointsMap C _ hK L.toFunctor L.ι) := by
    intro x hx
    obtain ⟨p, hp⟩ := hrat x hx
    have hpw : p.left ≫ (BigFppfOver.toScheme C _ hK).map Y.hom = 𝟙 _ := by
      have h := Over.w p
      simp only [Over.mk_hom] at h
      exact h
    obtain ⟨x₀, hg⟩ := exists_pointsMap_snd_eq_class_ptOf K C hK Ω hΩ ε p.left hpw x ⟨_, hp⟩
    obtain ⟨U, hU, hfibU⟩ :=
      exists_isAffineOpen_forall_mem_of_pointsMap_snd_eq K C hK P Y eY hJ hrat x₀
    exact mem_range_schematicLocus_of_forall_mem_isAffineOpen K C hK hP hPqs Y.left ε U hU
      (πΩ (θ.symm x)) fun w hw => hfibU w (hw.trans hg)
  -- every point of `H` is the image of a point of `H_Ω`
  have hπsurj : Function.Surjective πΩ :=
    isSurjective_of_presheafSurjective C _ hK _
      (presheaf_prod_snd inferInstance EΩ H (surjective_extObj C _ hK (Iso.refl _) Ω hΩ))
  have hsurj : Function.Surjective (pointsMap C _ hK L.toFunctor L.ι) := by
    by_contra h
    obtain ⟨y, hy⟩ := not_forall.mp h
    have hopen : IsOpen (Set.range (pointsMap C _ hK L.toFunctor L.ι)) :=
      isOpen_range_pointsMap_of_isOpenImmersion C _ hK _ hLo.2
    let Z : Set Γ.X.left := (πΩ ∘ θ.symm) ⁻¹' (Set.range (pointsMap C _ hK L.toFunctor L.ι))ᶜ
    have hZ : IsClosed Z := hopen.isClosed_compl.preimage (hπΩ.comp θ.symm.continuous)
    obtain ⟨w, hw⟩ := hπsurj y
    have hZne : Z.Nonempty := ⟨θ w, by
      simp only [Z, Set.mem_preimage, Function.comp_apply, Homeomorph.symm_apply_apply, hw]
      exact hy⟩
    obtain ⟨x, hxZ, hxc⟩ := nonempty_inter_closedPoints hZne hZ.isLocallyClosed
    exact hxZ (key x hxc)
  have : IsIso L.ι := isIso_of_isOpenImmersion_of_surjective_pointsMap C _ hK _ hLo.2 hsurj
  have := hLr
  exact isRepresentable_of_natIso _ (asIso L.ι)

end AlgebraicGeometry.Space.GroupOverField

end
