module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeInitial
public import StacksFrontier.AlgebraicGeometry.Scheme.OpensTopIsoNaturality

/-!
# Relative weak normalization and open restrictions

The relative weak normalization of a quasi-compact, quasi-separated, dominant
morphism of schemes commutes with restriction to an open subscheme of its target.

## Main results

* `AlgebraicGeometry.weakNormalization_isPullback_open` identifies the chosen
  factorization of the restricted morphism with the pullback of the chosen
  relative weak normalization.

## Implementation notes

The pullback square and the equation on the source maps state compatibility of
both legs of the factorization. Uniqueness records the canonical comparison
between the chosen initial factorizations. Dominance of the restricted map is
obtained from the target-locality of dominance.

The comparison is checked on the affine charts supplied by
`AlgebraicGeometry.weakNormalizationAffineGluingData`: over an affine open `V`
of the open subscheme the two charts are the spectra of the relative weak
normalizations of isomorphic algebras, and the comparison map agrees with that
isomorphism because both are determined by their effect on the subalgebra of
sections, which is a monomorphism.

## References

* [Stacks Project, Tag 0H3N](https://stacks.math.columbia.edu/tag/0H3N)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

private theorem universalHomeomorphism_comp_isIso_left
    {A B C : Scheme.{u}} (f : A ⟶ C) (q : B ⟶ A)
    (hf : UniversalHomeomorphism f) (hq : IsIso q) :
    UniversalHomeomorphism (q ≫ f) := by
  have hres : (topologically @IsHomeomorph).universally.RespectsLeft
      (MorphismProperty.isomorphisms Scheme) :=
    (MorphismProperty.universally_respectsIso _).toRespectsLeft
  exact (universalHomeomorphism_iff _).mpr
    (hres.precomp q hq f ((universalHomeomorphism_iff f).mp hf))

private theorem mapped_relativeWeakNormalization_isUniversalHomeomorphism
    {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A B'] (e : B ≃ₐ[A] B')
    (N : Subalgebra A B)
    (hN : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op)) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (N.map e.toAlgHom))).op) := by
  let M : Subalgebra A B' := N.map e.toAlgHom
  let eN : N ≃ₐ[A] M := N.equivMapOfInjective e.toAlgHom e.injective
  let q := Scheme.Spec.map (CommRingCat.ofHom eN.toRingHom).op
  have : IsIso (CommRingCat.ofHom eN.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr eN.bijective
  have hq : IsIso q := by
    dsimp [q]
    exact (Scheme.Spec.mapIso (asIso (CommRingCat.ofHom eN.toRingHom)).op).isIso_hom
  let fN := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op
  have hcomp : q ≫ fN = Scheme.Spec.map (CommRingCat.ofHom (algebraMap A M)).op := by
    change Scheme.Spec.map (CommRingCat.ofHom eN.toRingHom).op ≫
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op = _
    rw [← Scheme.Spec.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    ext a
    simp [eN.commutes a]
  rw [← hcomp]
  exact universalHomeomorphism_comp_isIso_left fN q hN hq

private noncomputable def commRingIsoToRingEquiv {R S : CommRingCat.{u}} (e : R ≅ S) :
    (R : Type u) ≃+* (S : Type u) :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext x; simp) (by ext x; simp)

private theorem specSectionsMap_dominant
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    (V : X.Opens) (hV : IsAffineOpen V) :
    IsDominant (Scheme.Spec.map (CommRingCat.ofHom (f.app V).hom).op) := by
  let : IsDominant (f ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant f› V
  have hfac : (f ⁻¹ᵁ V).toSpecΓ ≫
      Scheme.Spec.map (CommRingCat.ofHom (f.app V).hom).op ≫ hV.isoSpec.inv = f ∣_ V := by
    calc
      (f ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (f.app V) ≫ hV.isoSpec.inv =
          ((f ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (f.app V)) ≫ hV.isoSpec.inv := by
            simp [Category.assoc]
      _ = (f ∣_ V ≫ V.toSpecΓ) ≫ hV.isoSpec.inv := by
        rw [Scheme.Opens.toSpecΓ_naturality f V]
      _ = f ∣_ V := by simp [Category.assoc, IsAffineOpen.toSpecΓ_isoSpec_inv]
  have hcomp : IsDominant ((f ⁻¹ᵁ V).toSpecΓ ≫
      Scheme.Spec.map (CommRingCat.ofHom (f.app V).hom).op ≫ hV.isoSpec.inv) := by
    rw [hfac]
    infer_instance
  have htail : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (f.app V).hom).op ≫ hV.isoSpec.inv) :=
    IsDominant.of_comp ((f ⁻¹ᵁ V).toSpecΓ)
      (Scheme.Spec.map (CommRingCat.ofHom (f.app V).hom).op ≫ hV.isoSpec.inv)
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsDominant)
    (Scheme.Spec.map (CommRingCat.ofHom (f.app V).hom).op) hV.isoSpec.inv).mp htail

private noncomputable def relativeWeakNormalizationAlgEquiv
    {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A B'] (e : B ≃ₐ[A] B')
    (hB : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hB' : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op)) :
    relativeWeakNormalization A B ≃ₐ[A]
      relativeWeakNormalization A B' := by
  let N := relativeWeakNormalization A B
  let N' := relativeWeakNormalization A B'
  let M : Subalgebra A B' := N.map e.toAlgHom
  let eN : N ≃ₐ[A] M := N.equivMapOfInjective e.toAlgHom e.injective
  have hN : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op) :=
    relativeWeakNormalization_isUniversalHomeomorphism A B hB
  have hM : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A M)).op) := by
    simpa [M] using mapped_relativeWeakNormalization_isUniversalHomeomorphism e N hN
  have hle : M ≤ N' := by
    simpa only [Subalgebra.range_val] using
      range_le_relativeWeakNormalization A B' M M.val hB' hM
  have hN' : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N')).op) :=
    relativeWeakNormalization_isUniversalHomeomorphism A B' hB'
  have hM' : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom
        (algebraMap A (N'.map e.symm.toAlgHom))).op) := by
    simpa using mapped_relativeWeakNormalization_isUniversalHomeomorphism e.symm N' hN'
  have hle' : N'.map e.symm.toAlgHom ≤ N := by
    simpa only [Subalgebra.range_val] using range_le_relativeWeakNormalization A B
      (N'.map e.symm.toAlgHom) (N'.map e.symm.toAlgHom).val hB hM'
  have heq : M = N' :=
    le_antisymm hle fun x hx => ⟨e.symm x, hle' ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩
  exact eN.trans (Subalgebra.equivOfEq M N' heq)

private theorem relativeWeakNormalizationAlgEquiv_apply_val
    {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A B'] (e : B ≃ₐ[A] B')
    (hB : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hB' : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op))
    (x : relativeWeakNormalization A B) :
    ((relativeWeakNormalizationAlgEquiv e hB hB' x :
      relativeWeakNormalization A B') : B') = e (x : B) := by
  classical
  dsimp [relativeWeakNormalizationAlgEquiv]
  simp only [Subalgebra.equivOfEq_apply]
  rfl

/-- The identification of the sections of `Y` over the preimage of the image of `V` with the
sections of `f ⁻¹ᵁ U` over the preimage of `V`. -/
private noncomputable def restrictedSectionsIso {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (V : U.toScheme.Opens) :
    Γ(Y, f ⁻¹ᵁ (U.ι ''ᵁ V)) ≅ Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V) :=
  asIso (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op) ≪≫
    eqToIso (Scheme.Opens.toScheme_presheaf_obj (f ⁻¹ᵁ U) ((f ∣_ U) ⁻¹ᵁ V)).symm

/-- The identification of sections is compatible with the maps from the base sections. -/
private theorem restrictedSectionsIso_hom_apply {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (V : U.toScheme.Opens) (a : Γ(X, U.ι ''ᵁ V)) :
    (restrictedSectionsIso f U V).hom.hom ((f.app (U.ι ''ᵁ V)).hom a) =
      ((f ∣_ U).app V).hom a := by
  exact congrArg (fun k : Γ(X, U.ι ''ᵁ V) ⟶ _ => k.hom a) (morphismRestrict_app f U V).symm

private noncomputable def restrictedChartAlgEquiv
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f] (U : X.Opens)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V) :
    let Vx : X.Opens := U.ι ''ᵁ V
    let Wx : Y.Opens := f ⁻¹ᵁ Vx
    let Wu : (f ⁻¹ᵁ U).toScheme.Opens := (f ∣_ U) ⁻¹ᵁ V
    letI : Algebra (X.presheaf.obj (Opposite.op Vx))
        (Y.presheaf.obj (Opposite.op Wx)) := (f.app Vx).hom.toAlgebra
    letI : Algebra (X.presheaf.obj (Opposite.op Vx))
        ((f ⁻¹ᵁ U).toScheme.presheaf.obj (Opposite.op Wu)) :=
      (f ∣_ U).app V |>.hom.toAlgebra
    let _Wimg : Y.Opens := (f ⁻¹ᵁ U).ι ''ᵁ Wu
    relativeWeakNormalization
        (X.presheaf.obj (Opposite.op Vx))
        (Y.presheaf.obj (Opposite.op Wx)) ≃ₐ[
          X.presheaf.obj (Opposite.op Vx)]
      relativeWeakNormalization
        (X.presheaf.obj (Opposite.op Vx))
        ((f ⁻¹ᵁ U).toScheme.presheaf.obj (Opposite.op Wu)) := by
  let Vx : X.Opens := U.ι ''ᵁ V
  let A := X.presheaf.obj (Opposite.op Vx)
  let Bx := Y.presheaf.obj (Opposite.op (f ⁻¹ᵁ Vx))
  let Bu := (f ⁻¹ᵁ U).toScheme.presheaf.obj (Opposite.op ((f ∣_ U) ⁻¹ᵁ V))
  letI : Algebra A Bx := (f.app Vx).hom.toAlgebra
  letI : Algebra A Bu := (f ∣_ U).app V |>.hom.toAlgebra
  let eAlg : Bx ≃ₐ[A] Bu := AlgEquiv.ofRingEquiv
    (f := commRingIsoToRingEquiv (restrictedSectionsIso f U V))
    (restrictedSectionsIso_hom_apply f U V)
  letI : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsDominant f› U
  have hVx : IsAffineOpen Vx := hV.image_of_isOpenImmersion U.ι
  exact relativeWeakNormalizationAlgEquiv eAlg
    (specSectionsMap_dominant f Vx hVx)
    (specSectionsMap_dominant (f ∣_ U) V hV)

private noncomputable def restrictedAffineWeakNormalizationChartIso
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f] (U : X.Opens)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V) :
    Spec (affineWeakNormalizationAlgebra (f ∣_ U) V) ≅
      Spec (affineWeakNormalizationAlgebra f (U.ι ''ᵁ V)) := by
  let Vx : X.Opens := U.ι ''ᵁ V
  let Wx : Y.Opens := f ⁻¹ᵁ Vx
  let Wu : (f ⁻¹ᵁ U).toScheme.Opens := (f ∣_ U) ⁻¹ᵁ V
  let A := X.presheaf.obj (Opposite.op Vx)
  let Bx := Y.presheaf.obj (Opposite.op Wx)
  let Bu := (f ⁻¹ᵁ U).toScheme.presheaf.obj (Opposite.op Wu)
  letI : CommRing A := inferInstance
  letI : CommRing Bx := inferInstance
  letI : CommRing Bu := inferInstance
  letI : Algebra A Bx := (f.app Vx).hom.toAlgebra
  letI : Algebra A Bu := (f ∣_ U).app V |>.hom.toAlgebra
  letI : CommRing (relativeWeakNormalization A Bx) := inferInstance
  letI : CommRing (relativeWeakNormalization A Bu) := inferInstance
  let e := restrictedChartAlgEquiv f U V hV
  dsimp [affineWeakNormalizationAlgebra]
  simp only [Scheme.Opens.toScheme_presheaf_obj]
  change Spec (CommRingCat.of (relativeWeakNormalization A Bu)) ≅
    Spec (CommRingCat.of (relativeWeakNormalization A Bx))
  letI : Algebra A (relativeWeakNormalization A Bu) := inferInstance
  letI : Algebra A (relativeWeakNormalization A Bx) := inferInstance
  let eR := e.toRingEquiv
  haveI : IsIso (CommRingCat.ofHom eR.toRingHom) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact eR.bijective
  exact Scheme.Spec.mapIso (asIso (CommRingCat.ofHom eR.toRingHom)).op

private lemma isoImage_topIso_appTop
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsOpenImmersion g] (U : Z.Opens) :
    (g ''ᵁ U).topIso.inv ≫ (g.isoImage U).hom.appTop =
      (g.appIso U).hom ≫ U.topIso.inv := by
  let V := g ''ᵁ U
  let e := g.isoImage U
  let q₁ := e.hom ≫ V.ι
  let q₂ := U.ι ≫ g
  have hcomp : (g.isoImage U).hom ≫ V.ι = U.ι ≫ g :=
    Scheme.Hom.isoImage_hom_ι g U
  have hq₁ : ⊤ ≤ q₁ ⁻¹ᵁ V := (show q₁ ⁻¹ᵁ V = ⊤ by simp [q₁, V]).ge
  have hq₂ : ⊤ ≤ q₂ ⁻¹ᵁ V := (show q₂ ⁻¹ᵁ V = ⊤ by simp [q₂, V]).ge
  let p₁ : {q : U.toScheme ⟶ Y // ⊤ ≤ q ⁻¹ᵁ V} := ⟨q₁, hq₁⟩
  let p₂ : {q : U.toScheme ⟶ Y // ⊤ ≤ q ⁻¹ᵁ V} := ⟨q₂, hq₂⟩
  have happ := congrArg (fun p : {q : U.toScheme ⟶ Y // ⊤ ≤ q ⁻¹ᵁ V} =>
    p.1.appLE V ⊤ p.2) (Subtype.ext hcomp : p₁ = p₂)
  have hfirstComp :
      V.ι.appLE V ⊤ V.ι_preimage_self.ge ≫
          e.hom.appLE ⊤ ⊤ (by simp) = q₁.appLE V ⊤ hq₁ := by
    dsimp [q₁]
    simpa using (Scheme.Hom.appLE_comp_appLE e.hom V.ι V ⊤ ⊤
      V.ι_preimage_self.ge (by simp))
  have hVinc : V.ι.appLE V ⊤ V.ι_preimage_self.ge = V.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso]
    congr 1
  have heTop : e.hom.appLE ⊤ ⊤ (by simp) = e.hom.appTop := by
    simpa using (Scheme.Hom.appLE_eq_app (f := e.hom) (U := (⊤ : V.toScheme.Opens)))
  have hUle : U ≤ g ⁻¹ᵁ V := by simp [V]
  have hsecondComp :
      g.appLE V U hUle ≫ U.ι.appLE U ⊤ (by simp) =
        q₂.appLE V ⊤ hq₂ := by
    dsimp [q₂]
    simpa using (Scheme.Hom.appLE_comp_appLE U.ι g V U ⊤ hUle (by simp))
  have hgIso : g.appLE V U hUle = (g.appIso U).hom := by
    simpa [V] using (Scheme.Hom.appIso_hom' g U).symm
  have hUinc : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso]
    congr 1
  calc
    V.topIso.inv ≫ e.hom.appTop = q₁.appLE V ⊤ hq₁ := by
      rw [← hVinc, ← heTop, hfirstComp]
    _ = q₂.appLE V ⊤ hq₂ := happ
    _ = (g.appIso U).hom ≫ U.topIso.inv := by
      rw [← hsecondComp, hgIso, hUinc]

private noncomputable def restrictedSourceOpenIso
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (V : U.toScheme.Opens) :
    let Wu : (f ⁻¹ᵁ U).toScheme.Opens := (f ∣_ U) ⁻¹ᵁ V
    let Wx : Y.Opens := f ⁻¹ᵁ (U.ι ''ᵁ V)
    Wu.toScheme ≅ Wx.toScheme := by
  let Wu : (f ⁻¹ᵁ U).toScheme.Opens := (f ∣_ U) ⁻¹ᵁ V
  let Wx : Y.Opens := f ⁻¹ᵁ (U.ι ''ᵁ V)
  let Wimg : Y.Opens := (f ⁻¹ᵁ U).ι ''ᵁ Wu
  have heq : Wx = Wimg := (image_morphismRestrict_preimage f U V).symm
  exact ((f ⁻¹ᵁ U).ι.isoImage Wu) ≪≫
    Y.isoOfEq heq.symm

private noncomputable def restrictFactorization
    {Y X : Scheme.{u}} {f : Y ⟶ X}
    [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    (F : UniversalHomeomorphismFactorization f) (U : X.Opens) :
    UniversalHomeomorphismFactorization (f ∣_ U) := by
  letI : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict (‹IsDominant f›) U
  refine ⟨F.toBase ⁻¹ᵁ U,
    F.toMiddle.resLE (F.toBase ⁻¹ᵁ U) (f ⁻¹ᵁ U) ?_, F.toBase ∣_ U, ?_, ?_⟩
  · change f ⁻¹ᵁ U ≤ (F.toMiddle ≫ F.toBase) ⁻¹ᵁ U
    rw [F.fac]
  · apply (cancel_mono U.ι).1
    simp [Category.assoc, F.fac]
  · constructor
    intro Z W i₁ i₂ g H
    exact F.universalHomeomorphism.universally_isHomeomorph
      (i₁ ≫ (F.toBase ⁻¹ᵁ U).ι) (i₂ ≫ U.ι) g
      (H.paste_vert (isPullback_morphismRestrict F.toBase U))

/-- The chart isomorphism identifying the restricted relative weak normalization
chart over an affine open `V` of `U` with the chart of `f` over its image is
compatible with the two maps to the base. -/
private theorem restrictedChartIso_comp_toBase
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f] (U : X.Opens)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V) :
    (restrictedAffineWeakNormalizationChartIso f U V hV).hom ≫
        affineWeakNormalizationToBase f (hV.image_of_isOpenImmersion U.ι) =
      affineWeakNormalizationToBase (f ∣_ U) hV ≫ (U.ι.isoImage V).hom := by
  let : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsDominant f› U
  have hVx : IsAffineOpen (U.ι ''ᵁ V) := hV.image_of_isOpenImmersion U.ι
  let A := X.presheaf.obj (Opposite.op (U.ι ''ᵁ V))
  let Bx := Y.presheaf.obj (Opposite.op (f ⁻¹ᵁ (U.ι ''ᵁ V)))
  let Bu := (f ⁻¹ᵁ U).toScheme.presheaf.obj (Opposite.op ((f ∣_ U) ⁻¹ᵁ V))
  let : CommRing A := inferInstance
  let : CommRing Bx := inferInstance
  let : CommRing Bu := inferInstance
  let : Algebra A Bx := (f.app (U.ι ''ᵁ V)).hom.toAlgebra
  let : Algebra A Bu := ((f ∣_ U).app V).hom.toAlgebra
  let : CommRing (relativeWeakNormalization A Bx) := inferInstance
  let : CommRing (relativeWeakNormalization A Bu) := inferInstance
  let Nx := relativeWeakNormalization A Bx
  let Nu := relativeWeakNormalization A Bu
  let : Algebra A Nx := inferInstance
  let : Algebra A Nu := inferInstance
  let eAlg := restrictedChartAlgEquiv f U V hV
  let e := restrictedAffineWeakNormalizationChartIso f U V hV
  have hAlgMaps :
      CommRingCat.ofHom (algebraMap A Nx) ≫
          CommRingCat.ofHom eAlg.toRingEquiv.toRingHom =
        CommRingCat.ofHom (algebraMap A Nu) := by
    ext a
    exact congrArg Subtype.val (eAlg.commutes a)
  have hVU : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V) := fun x hx => ⟨x, hx, rfl⟩
  have hImg : (U.ι.isoImage V).hom ≫ (U.ι ''ᵁ V).ι = V.ι ≫ U.ι :=
    Scheme.Hom.isoImage_hom_ι U.ι V
  have hAppLE : U.ι.appLE (U.ι ''ᵁ V) V hVU = 𝟙 A := by
    rw [Scheme.Opens.ι_appLE]
    change X.presheaf.map
      (homOfLE (le_rfl : U.ι ''ᵁ V ≤ U.ι ''ᵁ V)).op = 𝟙 _
    simp
  -- The comparison map on sections is the identity, so the two `fromSpec`
  -- maps differ only by the inclusion of `U` in `X`.
  have hVspec : hVx.fromSpec = hV.fromSpec ≫ U.ι := by
    have h0 := hVx.SpecMap_appLE_fromSpec U.ι hV hVU
    rw [hAppLE] at h0
    have h1 : Spec.map (𝟙 A) ≫ hVx.fromSpec = hVx.fromSpec := by
      rw [Spec.map_id, Category.id_comp]
    exact h1.symm.trans h0
  have hSpecRaw :
      Spec.map (CommRingCat.ofHom eAlg.toRingEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A Nx)) =
      (Spec.map (CommRingCat.ofHom (algebraMap A Nu)) :
        Spec (CommRingCat.of Nu) ⟶ Spec (CommRingCat.of A)) := by
    rw [← Spec.map_comp, hAlgMaps]
  have hSpecAlg : e.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A Nx)) =
      Spec.map (CommRingCat.ofHom (algebraMap A Nu)) := by
    dsimp [e, restrictedAffineWeakNormalizationChartIso,
      affineWeakNormalizationAlgebra]
    simp only [Scheme.Opens.toScheme_presheaf_obj]
    simp only [id_eq]
    change
      Spec.map (CommRingCat.ofHom eAlg.toRingEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A Nx)) = _
    exact hSpecRaw
  -- The two affine identifications differ exactly by the inclusion of `V`.
  have hIso : hVx.isoSpec.inv = hV.isoSpec.inv ≫ (U.ι.isoImage V).hom := by
    refine (cancel_mono (U.ι ''ᵁ V).ι).1 ?_
    have h1 : hVx.isoSpec.inv ≫ (U.ι ''ᵁ V).ι = hV.fromSpec ≫ U.ι :=
      (IsAffineOpen.isoSpec_inv_ι hVx).trans hVspec
    have h2 : hV.fromSpec ≫ U.ι =
        hV.isoSpec.inv ≫ (U.ι.isoImage V).hom ≫ (U.ι ''ᵁ V).ι := by
      rw [hImg, IsAffineOpen.isoSpec_inv_ι_assoc]
    exact h1.trans (h2.trans (Category.assoc _ _ _).symm)
  have hstep1 : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A Nx)) ≫
        hVx.isoSpec.inv =
      (e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A Nx))) ≫
        (hV.isoSpec.inv ≫ (U.ι.isoImage V).hom) :=
    (congrArg (fun q => e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A Nx)) ≫ q)
      hIso).trans (Category.assoc _ _ _).symm
  have hstep2 : (e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A Nx))) ≫
        (hV.isoSpec.inv ≫ (U.ι.isoImage V).hom) =
      (Spec.map (CommRingCat.ofHom (algebraMap A Nu)) ≫ hV.isoSpec.inv) ≫
        (U.ι.isoImage V).hom :=
    (congrArg (fun q => q ≫ (hV.isoSpec.inv ≫ (U.ι.isoImage V).hom)) hSpecAlg).trans
      (Category.assoc _ _ _).symm
  exact hstep1.trans hstep2

/-- The chart isomorphism is compatible with the two maps from the source. -/
private theorem restrictedChartIso_fromSource
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f] (U : X.Opens)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V) :
    affineWeakNormalizationFromSource (f ∣_ U) V ≫
        (restrictedAffineWeakNormalizationChartIso f U V hV).hom =
      (restrictedSourceOpenIso f U V).hom ≫
        affineWeakNormalizationFromSource f (U.ι ''ᵁ V) := by
  let : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsDominant f› U
  let Vx : X.Opens := U.ι ''ᵁ V
  have hVx : IsAffineOpen Vx := hV.image_of_isOpenImmersion U.ι
  let A := X.presheaf.obj (Opposite.op Vx)
  let Bx := Y.presheaf.obj (Opposite.op (f ⁻¹ᵁ Vx))
  let Bu := (f ⁻¹ᵁ U).toScheme.presheaf.obj (Opposite.op ((f ∣_ U) ⁻¹ᵁ V))
  let : CommRing A := inferInstance
  let : CommRing Bx := inferInstance
  let : CommRing Bu := inferInstance
  let : Algebra A Bx := (f.app Vx).hom.toAlgebra
  let : Algebra A Bu := ((f ∣_ U).app V).hom.toAlgebra
  let : CommRing (relativeWeakNormalization A Bx) := inferInstance
  let : CommRing (relativeWeakNormalization A Bu) := inferInstance
  let Nx := relativeWeakNormalization A Bx
  let Nu := relativeWeakNormalization A Bu
  let : Algebra A Nx := inferInstance
  let : Algebra A Nu := inferInstance
  let eAlg := restrictedChartAlgEquiv f U V hV
  let e := restrictedAffineWeakNormalizationChartIso f U V hV
  let Wx : Y.Opens := f ⁻¹ᵁ Vx
  let Wu : (f ⁻¹ᵁ U).toScheme.Opens := (f ∣_ U) ⁻¹ᵁ V
  let Wimg : Y.Opens := (f ⁻¹ᵁ U).ι ''ᵁ Wu
  have heq : Wx = Wimg := by
    dsimp [Wx, Wimg, Vx]
    exact (image_morphismRestrict_preimage f U V).symm
  -- The chart ring maps must be compared through the section-ring
  -- identifications induced by the two open immersions.
  let hRing : Y.presheaf.obj (Opposite.op Wimg) = Bu := rfl
  have hRingRfl : hRing = rfl := by rfl
  let eBComm : Bx ≅ Bu := restrictedSectionsIso f U V
  let eB : Bx ≃+* Bu := commRingIsoToRingEquiv eBComm
  have heBComm : eBComm.hom =
      Y.presheaf.map (eqToHom heq.symm).op ≫ (eqToIso hRing).hom := by
    simp [eBComm, restrictedSectionsIso]
  have hEqTop :
      Wx.topIso.inv ≫ (Y.isoOfEq heq.symm).hom.appTop =
        Y.presheaf.map (homOfLE heq.symm.le).op ≫ Wimg.topIso.inv := by
    rw [Scheme.isoOfEq_hom]
    have hnat := AlgebraicGeometry.opens_topIso_naturality (X := Y) (U := Wimg) (V := Wx)
      heq.symm.le
    calc
      Wx.topIso.inv ≫ (Y.homOfLE heq.symm.le).appTop =
        (Wx.topIso.inv ≫ (Y.homOfLE heq.symm.le).appTop ≫ Wimg.topIso.hom) ≫
            Wimg.topIso.inv := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = Y.presheaf.map (homOfLE heq.symm.le).op ≫ Wimg.topIso.inv := by rw [hnat]
  have hImgTop :
      Wimg.topIso.inv ≫ ((f ⁻¹ᵁ U).ι.isoImage Wu).hom.appTop =
        (((f ⁻¹ᵁ U).ι).appIso Wu).hom ≫ Wu.topIso.inv :=
    isoImage_topIso_appTop (g := (f ⁻¹ᵁ U).ι) Wu
  have hE :
      Y.presheaf.map (homOfLE heq.symm.le).op ≫
          (((f ⁻¹ᵁ U).ι).appIso Wu).hom =
        Y.presheaf.map (eqToHom heq.symm).op ≫ (eqToIso hRing).hom := by
    have harr : (homOfLE heq.symm.le : Wimg ⟶ Wx) = eqToHom heq.symm :=
      Subsingleton.elim _ _
    rw [harr]
    refine congrArg (fun q => Y.presheaf.map (eqToHom heq.symm).op ≫ q) ?_
    rw [hRingRfl]
    exact (Scheme.Opens.ι_appIso (f ⁻¹ᵁ U) Wu) ▸ rfl
  have hJComp : Wx.topIso.inv ≫ (restrictedSourceOpenIso f U V).hom.appTop =
      CommRingCat.ofHom eB.toRingHom ≫ Wu.topIso.inv := by
    delta restrictedSourceOpenIso
    have heB : CommRingCat.ofHom eB.toRingHom = eBComm.hom := by
      ext x
      rfl
    rw [Iso.trans_hom, Scheme.Hom.comp_appTop, ← Category.assoc, hEqTop, Category.assoc, hImgTop,
      ← Category.assoc, hE, ← heBComm, heB]
  have hJGeom : (restrictedSourceOpenIso f U V).hom ≫ Wx.toSpecΓ =
      Wu.toSpecΓ ≫ Spec.map (CommRingCat.ofHom eB.toRingHom) := by
    calc
      (restrictedSourceOpenIso f U V).hom ≫ Wx.toSpecΓ =
          (restrictedSourceOpenIso f U V).hom ≫ AlgebraicGeometry.Scheme.toSpecΓ Wx.toScheme ≫
            Spec.map Wx.topIso.inv := by
              simp only [Scheme.Opens.toSpecΓ]
      _ = Wu.toScheme.toSpecΓ ≫ Spec.map (restrictedSourceOpenIso f U V).hom.appTop ≫
            Spec.map Wx.topIso.inv :=
        congrArg (fun k => k ≫ Spec.map Wx.topIso.inv)
          (AlgebraicGeometry.Scheme.toSpecΓ_naturality (restrictedSourceOpenIso f U V).hom)
      _ = Wu.toSpecΓ ≫ Spec.map (CommRingCat.ofHom eB.toRingHom) := by
              have h1 : Spec.map (restrictedSourceOpenIso f U V).hom.appTop ≫
                    Spec.map Wx.topIso.inv =
                  Spec.map (Wx.topIso.inv ≫
                    (restrictedSourceOpenIso f U V).hom.appTop) :=
                (Spec.map_comp _ _).symm
              have h2 : Spec.map (CommRingCat.ofHom eB.toRingHom ≫
                    Wu.topIso.inv) =
                  Spec.map Wu.topIso.inv ≫
                    Spec.map (CommRingCat.ofHom eB.toRingHom) := Spec.map_comp _ _
              have h3 : Wu.toScheme.toSpecΓ ≫ Spec.map Wu.topIso.inv ≫
                    Spec.map (CommRingCat.ofHom eB.toRingHom) =
                  Wu.toSpecΓ ≫ Spec.map (CommRingCat.ofHom eB.toRingHom) := by
                simp only [Scheme.Opens.toSpecΓ, Category.assoc]
              refine Eq.trans ?_ h3
              refine congrArg (fun q => Wu.toScheme.toSpecΓ ≫ q) ?_
              exact h1.trans ((congrArg Spec.map hJComp).trans h2)
  have hdomx := specSectionsMap_dominant f Vx hVx
  have hdomu := specSectionsMap_dominant (f ∣_ U) V hV
  let eBase : Bx ≃ₐ[A] Bu :=
    AlgEquiv.ofRingEquiv (f := eB) (restrictedSectionsIso_hom_apply f U V)
  have hWNVal (x : Nx) : ((eAlg x : Nu) : Bu) = eB (x : Bx) := by
    change ((relativeWeakNormalizationAlgEquiv eBase hdomx hdomu x : Nu) : Bu) = _
    exact relativeWeakNormalizationAlgEquiv_apply_val eBase hdomx hdomu x
  have hWNComp :
      CommRingCat.ofHom eAlg.toRingEquiv.toRingHom ≫
          CommRingCat.ofHom (Nu.val.toRingHom) =
        CommRingCat.ofHom (Nx.val.toRingHom) ≫
          CommRingCat.ofHom eB.toRingHom := by
    ext x
    exact hWNVal x
  change (Wu.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Nu.val.toRingHom))) ≫ e.hom =
    (restrictedSourceOpenIso f U V).hom ≫
      (Wx.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Nx.val.toRingHom)))
  dsimp [e, restrictedAffineWeakNormalizationChartIso]
  have c1 : (Wu.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Nu.val.toRingHom))) ≫
        Spec.map (CommRingCat.ofHom eAlg.toRingEquiv.toRingHom) =
      Wu.toSpecΓ ≫ Spec.map (CommRingCat.ofHom eAlg.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom (Nu.val.toRingHom)) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun q => Wu.toSpecΓ ≫ q) (Spec.map_comp _ _).symm)
  have c2 : Wu.toSpecΓ ≫ Spec.map (CommRingCat.ofHom eAlg.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom (Nu.val.toRingHom)) =
      Wu.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Nx.val.toRingHom) ≫
        CommRingCat.ofHom eB.toRingHom) :=
    congrArg (fun q => Wu.toSpecΓ ≫ Spec.map q) hWNComp
  have c3 : Wu.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Nx.val.toRingHom) ≫
        CommRingCat.ofHom eB.toRingHom) =
      (restrictedSourceOpenIso f U V).hom ≫
        (Wx.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Nx.val.toRingHom))) :=
    (congrArg (fun q => Wu.toSpecΓ ≫ q) (Spec.map_comp _ _)).trans
      (((Category.assoc _ _ _).symm).trans
        ((congrArg (fun q => q ≫ Spec.map (CommRingCat.ofHom (Nx.val.toRingHom)))
            hJGeom.symm).trans (Category.assoc _ _ _)))
  exact c1.trans (c2.trans c3)

/-- A morphism out of an affine relative weak normalization chart into an affine
scheme is determined by its composite with the map from the source, because that
map is the subalgebra inclusion on sections. -/
private theorem eq_of_fromSource_comp_eq
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (V : U.toScheme.Opens)
    {T : CommRingCat.{u}}
    (k₁ k₂ : Spec (affineWeakNormalizationAlgebra (f ∣_ U) V) ⟶ Spec T)
    (hk : affineWeakNormalizationFromSource (f ∣_ U) V ≫ k₁ =
      affineWeakNormalizationFromSource (f ∣_ U) V ≫ k₂) :
    k₁ = k₂ := by
  let : Algebra Γ(U.toScheme, V) Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V) :=
    ((f ∣_ U).app V).hom.toAlgebra
  have hSections : Γ((f ∣_ U) ⁻¹ᵁ V, ⊤) =
      Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V) := by
    simpa using Scheme.Opens.toScheme_presheaf_obj ((f ∣_ U) ⁻¹ᵁ V) ⊤
  have htopSections : ((f ∣_ U) ⁻¹ᵁ V).topIso.inv = eqToHom hSections.symm := by
    change (f ⁻¹ᵁ U).toScheme.presheaf.map
      (eqToHom ((f ∣_ U) ⁻¹ᵁ V).ι_image_top).op = _
    rw [eqToHom_op, eqToHom_map]
    rfl
  let inc := CommRingCat.ofHom
      ((relativeWeakNormalization Γ(U.toScheme, V)
        Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V)).val.toRingHom) ≫
    eqToHom hSections.symm
  have hsrcMap :
      (Scheme.ΓSpecIso (affineWeakNormalizationAlgebra (f ∣_ U) V)).inv ≫
        (affineWeakNormalizationFromSource (f ∣_ U) V).appTop = inc := by
    change (Scheme.ΓSpecIso (CommRingCat.of
        (relativeWeakNormalization Γ(U.toScheme, V)
          Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V)))).inv ≫
      (Spec.map (CommRingCat.ofHom
        ((relativeWeakNormalization Γ(U.toScheme, V)
          Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V)).val.toRingHom))).appTop ≫
        ((f ∣_ U) ⁻¹ᵁ V).toSpecΓ.appTop = inc
    calc
      _ = (CommRingCat.ofHom
            ((relativeWeakNormalization Γ(U.toScheme, V)
              Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V)).val.toRingHom) ≫
            (Scheme.ΓSpecIso (Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V))).inv) ≫
              ((f ∣_ U) ⁻¹ᵁ V).toSpecΓ.appTop :=
        congrArg (fun q => q ≫ ((f ∣_ U) ⁻¹ᵁ V).toSpecΓ.appTop)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
            ((relativeWeakNormalization Γ(U.toScheme, V)
              Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V)).val.toRingHom))).symm
      _ = CommRingCat.ofHom
            ((relativeWeakNormalization Γ(U.toScheme, V)
              Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V)).val.toRingHom) ≫
            ((Scheme.ΓSpecIso (Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V))).inv ≫
              ((f ∣_ U) ⁻¹ᵁ V).toSpecΓ.appTop) := Category.assoc _ _ _
      _ = inc := by
        dsimp [inc]
        rw [Scheme.Opens.toSpecΓ_appTop]
        simp only [Iso.inv_hom_id_assoc]
        rw [htopSections]
  have hmap (q : Spec (affineWeakNormalizationAlgebra (f ∣_ U) V) ⟶ Spec T) :
      (Scheme.ΓSpecIso T).inv ≫ q.appTop = Spec.homEquiv q ≫
        (Scheme.ΓSpecIso (affineWeakNormalizationAlgebra (f ∣_ U) V)).inv := by
    have hq : Spec.map (Spec.homEquiv q) = q := Spec.homEquiv.symm_apply_apply q
    rw [← hq, Scheme.ΓSpecIso_inv_naturality]
    simp
  have hkey (q : Spec (affineWeakNormalizationAlgebra (f ∣_ U) V) ⟶ Spec T) :
      Spec.homEquiv q ≫ inc = (Scheme.ΓSpecIso T).inv ≫
        (affineWeakNormalizationFromSource (f ∣_ U) V ≫ q).appTop := by
    rw [Scheme.Hom.comp_appTop, ← hsrcMap, ← Category.assoc, ← hmap q,
      Category.assoc]
  have hring : Spec.homEquiv k₁ ≫ inc = Spec.homEquiv k₂ ≫ inc := by
    rw [hkey k₁, hkey k₂, hk]
  have hringVal : Spec.homEquiv k₁ ≫ CommRingCat.ofHom
        ((relativeWeakNormalization Γ(U.toScheme, V)
          Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V)).val.toRingHom) =
      Spec.homEquiv k₂ ≫ CommRingCat.ofHom
        ((relativeWeakNormalization Γ(U.toScheme, V)
          Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V)).val.toRingHom) := by
    apply (cancel_mono (eqToHom hSections.symm)).1
    simpa [inc, Category.assoc] using hring
  have : Mono (CommRingCat.ofHom
      ((relativeWeakNormalization Γ(U.toScheme, V)
        Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V)).val.toRingHom)) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  exact Spec.homEquiv.injective ((cancel_mono _).1 hringVal)

private theorem comparison_isPullback_of_affineCharts
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens)
    (F : UniversalHomeomorphismFactorization f)
    (F_U : UniversalHomeomorphismFactorization (f ∣_ U))
    (D : F.AffineGluingData) (D_U : F_U.AffineGluingData)
    (h : F_U.middle ⟶ F.middle)
    (hhBase : h ≫ F.toBase = F_U.toBase ≫ U.ι)
    (hhSource : F_U.toMiddle ≫ h = (f ⁻¹ᵁ U).ι ≫ F.toMiddle) :
    IsPullback h F_U.toBase F.toBase U.ι := by
  let : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsDominant f› U
  have hp : IsPullback F_U.toBase h U.ι F.toBase := by
    let 𝒰 := U.toScheme.affineOpenCover.openCover
    let 𝒱 := 𝒰.copy 𝒰.I₀ (fun i => (𝒰.f i).opensRange)
      (fun i => ((𝒰.f i).opensRange).ι) (Equiv.refl 𝒰.I₀)
      (fun i => (𝒰.f i).isoOpensRange.symm) (by simp)
    apply Scheme.isPullback_of_openCover F_U.toBase h U.ι F.toBase 𝒱
    intro i
    have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have : IsAffine (𝒰.X i) :=
      Scheme.isAffine_affineOpenCover U.toScheme U.toScheme.affineOpenCover i
    let V : U.toScheme.Opens := (𝒰.f i).opensRange
    have hV : IsAffineOpen V := isAffineOpen_opensRange (𝒰.f i)
    let Vx : X.Opens := U.ι ''ᵁ V
    have hVx : IsAffineOpen Vx := hV.image_of_isOpenImmersion U.ι
    let e := restrictedAffineWeakNormalizationChartIso f U V hV
    have hBaseChart : e.hom ≫ affineWeakNormalizationToBase f hVx =
        affineWeakNormalizationToBase (f ∣_ U) hV ≫ (U.ι.isoImage V).hom :=
      restrictedChartIso_comp_toBase f U V hV
    let Wx : Y.Opens := f ⁻¹ᵁ Vx
    let Wu : (f ⁻¹ᵁ U).toScheme.Opens := (f ∣_ U) ⁻¹ᵁ V
    let Wimg : Y.Opens := (f ⁻¹ᵁ U).ι ''ᵁ Wu
    have hSourceChart :
        affineWeakNormalizationFromSource (f ∣_ U) V ≫ e.hom =
          (restrictedSourceOpenIso f U V).hom ≫
            affineWeakNormalizationFromSource f Vx :=
      restrictedChartIso_fromSource f U V hV
    let srcU := affineWeakNormalizationFromSource (f ∣_ U) V
    let srcX := affineWeakNormalizationFromSource f Vx
    let chartU := D_U.ι V hV
    let chartX := D.ι Vx hVx
    let : Algebra Γ(U.toScheme, V) Γ((f ⁻¹ᵁ U).toScheme, Wu) :=
      ((f ∣_ U).app V).hom.toAlgebra
    have hbaseU : chartU ≫ h ≫ F.toBase =
        affineWeakNormalizationToBase (f ∣_ U) hV ≫
          (U.ι.isoImage V).hom ≫ Vx.ι := by
      rw [hhBase, reassoc_of% (D_U.isPullback V hV).w, Scheme.Hom.isoImage_hom_ι]
    let k : Spec (affineWeakNormalizationAlgebra (f ∣_ U) V) ⟶
        Spec (affineWeakNormalizationAlgebra f Vx) :=
      (D.isPullback Vx hVx).lift (chartU ≫ h)
        (affineWeakNormalizationToBase (f ∣_ U) hV ≫ (U.ι.isoImage V).hom) hbaseU
    have hkChart : k ≫ chartX = chartU ≫ h :=
      (D.isPullback Vx hVx).lift_fst _ _ _
    have hOpen : (restrictedSourceOpenIso f U V).hom ≫ Wx.ι =
        Wu.ι ≫ (f ⁻¹ᵁ U).ι := by
      dsimp [restrictedSourceOpenIso, Wx, Wu, Wimg]
      calc
        _ = ((f ⁻¹ᵁ U).ι.isoImage ((f ∣_ U) ⁻¹ᵁ V)).hom ≫
              ((Y.isoOfEq (image_morphismRestrict_preimage f U V)).hom ≫
                (f ⁻¹ᵁ Vx).ι) := by
              rw [Category.assoc]
        _ = ((f ⁻¹ᵁ U).ι.isoImage ((f ∣_ U) ⁻¹ᵁ V)).hom ≫
              (((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)).ι) := by
              rw [Scheme.isoOfEq_hom_ι]
        _ = ((f ∣_ U) ⁻¹ᵁ V).ι ≫ (f ⁻¹ᵁ U).ι := by
              simp [Scheme.Hom.isoImage_hom_ι]
    have hsrcChart : srcU ≫ chartU ≫ h = srcU ≫ e.hom ≫ chartX := by
      calc
        srcU ≫ chartU ≫ h = Wu.ι ≫ (f ⁻¹ᵁ U).ι ≫ F.toMiddle := by
          rw [← Category.assoc, D_U.fromSource_ι, Category.assoc, hhSource]
        _ = (restrictedSourceOpenIso f U V).hom ≫ srcX ≫ chartX := by
          rw [← reassoc_of% hOpen, ← D.fromSource_ι]
        _ = srcU ≫ e.hom ≫ chartX := by rw [reassoc_of% hSourceChart]
    have hsrc : srcU ≫ k = srcU ≫ e.hom := by
      rw [← cancel_mono chartX, Category.assoc, hkChart, Category.assoc, hsrcChart]
    have hk : k = e.hom := eq_of_fromSource_comp_eq f U V k e.hom hsrc
    have htop : chartU ≫ h = e.hom ≫ chartX := by
      rw [← hk, hkChart]
    have hchart : IsPullback (chartU ≫ h)
        (affineWeakNormalizationToBase (f ∣_ U) hV)
        F.toBase ((U.ι.isoImage V).hom ≫ Vx.ι) := by
      have he : IsPullback e.hom
          (affineWeakNormalizationToBase (f ∣_ U) hV)
          (affineWeakNormalizationToBase f hVx) (U.ι.isoImage V).hom :=
        IsPullback.of_horiz_isIso ⟨hBaseChart⟩
      simpa only [htop, Scheme.Hom.isoImage_hom_ι] using he.paste_horiz (D.isPullback Vx hVx)
    let iP := (D_U.isPullback V hV).isoPullback
    exact hchart.flip.of_iso iP (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        change affineWeakNormalizationToBase (f ∣_ U) hV =
          iP.hom ≫ pullback.snd F_U.toBase V.ι
        exact (D_U.isPullback V hV).isoPullback_hom_snd.symm)
      (by
        change chartU ≫ h =
          (D_U.isPullback V hV).isoPullback.hom ≫
            pullback.fst F_U.toBase V.ι ≫ h
        rw [← Category.assoc, (D_U.isPullback V hV).isoPullback_hom_fst])
      (Scheme.Hom.isoImage_hom_ι U.ι V)
      (by simp)
  exact hp.flip

/-- Relative weak normalization commutes with restriction to an open subscheme
of the target, as a factorization of the restricted morphism. -/
@[stacks 0H3N "weak_open"]
public theorem weakNormalization_isPullback_open
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens) :
    letI : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict (‹IsDominant f›) U
    let F := weakNormalizationFactorization f
    let F_U := weakNormalizationFactorization (f ∣_ U)
    ∃! h : F_U.middle ⟶ F.middle,
      IsPullback h F_U.toBase F.toBase U.ι ∧
      F_U.toMiddle ≫ h = (f ⁻¹ᵁ U).ι ≫ F.toMiddle :=
  by
    classical
    let : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict (‹IsDominant f›) U
    let F := weakNormalizationFactorization f
    let F_U := weakNormalizationFactorization (f ∣_ U)
    let R := restrictFactorization F U
    let α : F_U ⟶ R := weakNormalizationFactorizationIsInitial (f ∣_ U) |>.to R
    let i : R.middle ⟶ F.middle := by
      dsimp [R, restrictFactorization]
      exact (F.toBase ⁻¹ᵁ U).ι
    have hi : Mono i := by
      dsimp [i, R, restrictFactorization]
      infer_instance
    let h : F_U.middle ⟶ F.middle := α.hom ≫ i
    have hRi : R.toMiddle ≫ i = (f ⁻¹ᵁ U).ι ≫ F.toMiddle := by
      dsimp [R, restrictFactorization, i]
      simp
    have hbase : h ≫ F.toBase = F_U.toBase ≫ U.ι := by
      dsimp [h]
      rw [Category.assoc]
      have hiBase : i ≫ F.toBase = R.toBase ≫ U.ι := by
        dsimp [i, R, restrictFactorization]
        simp
      rw [hiBase, ← Category.assoc, α.hom_toBase]
    have hsource : F_U.toMiddle ≫ h = (f ⁻¹ᵁ U).ι ≫ F.toMiddle := by
      rw [← hRi, ← α.toMiddle_hom, Category.assoc]
    refine ⟨h, ⟨comparison_isPullback_of_affineCharts f U F F_U
      (weakNormalizationAffineGluingData f)
      (weakNormalizationAffineGluingData (f ∣_ U)) h hbase hsource, hsource⟩, ?_⟩
    · intro g hg
      let p := isPullback_morphismRestrict F.toBase U
      let β : F_U.middle ⟶ R.middle := p.lift F_U.toBase g hg.1.w.symm
      have hβi : β ≫ i = g := by
        change β ≫ (F.toBase ⁻¹ᵁ U).ι = g
        exact p.lift_snd F_U.toBase g hg.1.w.symm
      have hβb : β ≫ R.toBase = F_U.toBase := by
        change β ≫ (F.toBase ∣_ U) = F_U.toBase
        exact p.lift_fst F_U.toBase g hg.1.w.symm
      have hβs : F_U.toMiddle ≫ β = R.toMiddle := by
        apply (cancel_mono i).1
        rw [Category.assoc, hβi, hg.2, hRi]
      let βhom : F_U ⟶ R := ⟨β, hβs, hβb⟩
      have heq : βhom = α :=
        (weakNormalizationFactorizationIsInitial (f ∣_ U)).hom_ext βhom α
      calc
        g = β ≫ i := hβi.symm
        _ = α.hom ≫ i := by rw [← congrArg (fun k : F_U ⟶ R => k.hom) heq]
        _ = h := rfl

end AlgebraicGeometry

end
