module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.AffineWeaklyNormal
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeInitial
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.GermInjective

/-!
# Weak normality is local on a scheme

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components. Weak
normality of `X` can be tested on every affine open, on a single affine open covering, or on an
open covering by weakly normal schemes, the test on an affine open being the pair of ring
conditions of Tag 0H3T applied to its ring of sections. Consequently every open subscheme of a
weakly normal scheme is weakly normal.

## Main results

* `AlgebraicGeometry.isIso_weakNormalization_restrict_iff`: over an affine open of a reduced
  scheme the weak normalization morphism restricts to an isomorphism exactly when the ring of
  sections is weakly normal.
* `AlgebraicGeometry.isReduced_of_isWeaklyNormal`: a weakly normal scheme is reduced.
* `AlgebraicGeometry.isWeaklyNormal_tfae`: the four equivalent criteria for weak normality.
* `AlgebraicGeometry.isWeaklyNormal_open`: an open subscheme of a weakly normal scheme is weakly
  normal.
* `AlgebraicGeometry.finite_irreducibleComponents_of_isOpenImmersion`: the finiteness hypothesis
  on quasi-compact opens passes to open subschemes, which is what makes the weak normalization of
  an open subscheme available.

## Implementation notes

The argument is local on the target throughout: the chosen relative weak normalization of the
normalization morphism is glued from its affine charts, and over an affine open `U` the chart is
the spectrum of the relative weak normalization of `Γ(X, U)` in the sections of the normalization
there — this is `AlgebraicGeometry.UniversalHomeomorphismFactorization.AffineGluingData`, so the
restriction of the weak normalization morphism over `U` needs no gluing argument. For a reduced
scheme those sections are the integral closure of `Γ(X, U)` in its total ring of fractions by
Tag 035P, in a form that does not refer to the presenting ring; transporting the relative weak
normalization along that identification therefore reduces the affine open of `X` and the whole of
`Spec Γ(X, U)` to the same ring-theoretic statement, and Tag 0H3T identifies it with the two ring
conditions. No comparison of the weak normalization of an open subscheme with that of the ambient
scheme is needed.

Reducedness is not assumed: it is a consequence of each of the four conditions. An affine chart is
a subalgebra of the sections of the normalization, which is reduced, so an affine open over which
the weak normalization morphism is an isomorphism has reduced sections.

The finiteness hypothesis on quasi-compact opens is an explicit argument rather than a typeclass,
matching the form in which the normalization — and hence the weak normalization — is constructed;
in the covering condition it is therefore asserted existentially alongside weak normality of the
member of the covering.

## References

* [Stacks Project, Tag 0H3U](https://stacks.math.columbia.edu/tag/0H3U)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Finiteness of irreducible components on open subschemes -/


/-- If every quasi-compact open of `X` has finitely many irreducible components, the same holds
for any scheme admitting an open immersion into `X`. -/
theorem finite_irreducibleComponents_of_isOpenImmersion
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) :
    (irreducibleComponents V).Finite := by
  let g := V.ι ≫ f
  let W : X.Opens := ⟨Set.range g, g.isOpenEmbedding.isOpen_range⟩
  have hWc : IsCompact (W : Set X) := by
    let : CompactSpace V := (isCompact_iff_compactSpace).mp (by simpa using hV)
    simpa [W, Set.image_univ] using (isCompact_univ.image g.continuous)
  have hHomeo : V ≃ₜ W := g.isOpenEmbedding.isEmbedding.toHomeomorph
  exact finite_irreducibleComponents_of_isOpenEmbedding hHomeo
    hHomeo.isOpenEmbedding (hX W hWc)

/-! ### Reducedness from reduced affine sections -/

/-- A scheme covered by affine opens with reduced rings of sections is reduced. -/
private lemma isReduced_of_isOpenCover_sections {X : Scheme.{u}} {ι : Type*}
    (U : ι → X.Opens) (htop : (⨆ i, U i) = ⊤) (haff : ∀ i, IsAffineOpen (U i))
    (hred : ∀ i, _root_.IsReduced Γ(X, U i)) : IsReduced X := by
  have hi : ∀ i, IsReduced ((X.openCoverOfIsOpenCover U htop).X i) := fun i => by
    change IsReduced (U i).toScheme
    have := hred i
    have : IsReduced (Spec Γ(X, U i)) := inferInstance
    exact isReduced_of_isOpenImmersion (haff i).isoSpec.hom
  exact IsReduced.of_openCover X (X.openCoverOfIsOpenCover U htop)

/-! ### Affine charts of the weak normalization -/

/-- A ring map is an isomorphism of spectra exactly when it is bijective. -/
private lemma isIso_specMap_ofHom_iff {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    IsIso (Spec.map (CommRingCat.ofHom φ)) ↔ Function.Bijective φ := by
  have hφ : IsIso (CommRingCat.ofHom φ) ↔ Function.Bijective φ := by
    simpa using ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom φ)
  rw [← hφ]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : IsIso (Scheme.Spec.map (CommRingCat.ofHom φ).op) := h
    exact (isIso_op_iff (CommRingCat.ofHom φ)).mp
      (isIso_of_reflects_iso (CommRingCat.ofHom φ).op Scheme.Spec)
  · have := h
    infer_instance

/-- Read through chosen presentations of an affine open of the target and of its inverse image,
the map on sections induced by a morphism is the given map of presenting rings. -/
private lemma app_affineOpenCoordinateRingEquiv
    {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    {A B : Type u} [CommRing A] [CommRing B]
    (eU : Spec (.of A) ≅ U.toScheme) (eV : Spec (.of B) ≅ (f ⁻¹ᵁ U).toScheme) (φ : A →+* B)
    (hφ : eV.inv ≫ Spec.map (CommRingCat.ofHom φ) = (f ∣_ U) ≫ eU.inv) (x : A) :
    (f.app U).hom (affineOpenCoordinateRingEquiv U eU x) =
      affineOpenCoordinateRingEquiv (f ⁻¹ᵁ U) eV (φ x) := by
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := by
    have : IsAffine (Spec (.of B)) := inferInstance
    exact IsAffine.of_isIso eV.inv
  have key : CommRingCat.ofHom (affineOpenCoordinateRingEquiv U eU).toRingHom ≫ f.app U =
      CommRingCat.ofHom φ ≫
        CommRingCat.ofHom (affineOpenCoordinateRingEquiv (f ⁻¹ᵁ U) eV).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, affineOpenCoordinateRingEquiv_specMap U hU eU,
      affineOpenCoordinateRingEquiv_specMap (f ⁻¹ᵁ U) hV eV]
    calc Spec.map (f.app U) ≫ hU.isoSpec.inv ≫ eU.inv
        = (hV.isoSpec.inv ≫ hV.isoSpec.hom ≫ Spec.map (f.app U)) ≫
            hU.isoSpec.inv ≫ eU.inv := by rw [Iso.inv_hom_id_assoc]
      _ = (hV.isoSpec.inv ≫ (f ∣_ U) ≫ hU.isoSpec.hom) ≫ hU.isoSpec.inv ≫ eU.inv := by
            rw [show hV.isoSpec.hom ≫ Spec.map (f.app U) = (f ∣_ U) ≫ hU.isoSpec.hom from
              Scheme.Opens.toSpecΓ_naturality f U]
      _ = hV.isoSpec.inv ≫ (f ∣_ U) ≫ eU.inv := by simp
      _ = hV.isoSpec.inv ≫ eV.inv ≫ Spec.map (CommRingCat.ofHom φ) := by rw [hφ]
      _ = (hV.isoSpec.inv ≫ eV.inv) ≫ Spec.map (CommRingCat.ofHom φ) :=
            (Category.assoc _ _ _).symm
  exact congrArg (fun g : CommRingCat.of A ⟶ Γ(Y, f ⁻¹ᵁ U) => g.hom x) key

/-- Over an affine open the chart of the relative weak normalization maps isomorphically to that
open exactly when the sections of the target coincide with their relative weak normalization. -/
private lemma isIso_affineWeakNormalizationToBase_iff
    {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) :
    let := (f.app U).hom.toAlgebra
    IsIso (affineWeakNormalizationToBase f hU) ↔
      Function.Bijective (algebraMap Γ(X, U)
        (relativeWeakNormalization Γ(X, U) Γ(Y, f ⁻¹ᵁ U))) := by
  let := (f.app U).hom.toAlgebra
  change IsIso (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
      (relativeWeakNormalization Γ(X, U) Γ(Y, f ⁻¹ᵁ U)))) ≫ hU.isoSpec.inv) ↔ _
  rw [isIso_comp_right_iff]
  exact isIso_specMap_ofHom_iff _

/-- Over an affine open the restriction of the weak normalization morphism is the chart of the
relative weak normalization of the normalization morphism. -/
private lemma isIso_weakNormalization_restrict_iff_bijective_sections
    {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    let := ((Scheme.normalization X hX).app U).hom.toAlgebra
    IsIso (Scheme.weakNormalization X hX ∣_ U) ↔
      Function.Bijective (algebraMap Γ(X, U)
        (relativeWeakNormalization Γ(X, U)
          Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U))) := by
  let := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X
  let : IsDominant (Scheme.normalization X hX) := Scheme.normalization_isDominant X hX
  let := ((Scheme.normalization X hX).app U).hom.toAlgebra
  have h1 : IsIso (Scheme.weakNormalization X hX ∣_ U) ↔
      IsIso (affineWeakNormalizationToBase (Scheme.normalization X hX) hU) := by
    have hD := (weakNormalizationAffineGluingData
      (Scheme.normalization X hX)).restrictIso_hom_toBase U hU
    rw [← hD]
    exact (isIso_comp_left_iff _ _).symm
  exact h1.trans (isIso_affineWeakNormalizationToBase_iff (Scheme.normalization X hX) hU)

/-- The ring of sections of the normalization over an affine open is reduced, hence so is every
affine chart of the weak normalization. -/
private lemma isReduced_sections_of_isIso_weakNormalization_restrict
    {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U)
    (h : IsIso (Scheme.weakNormalization X hX ∣_ U)) : _root_.IsReduced Γ(X, U) := by
  let := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X
  let := ((Scheme.normalization X hX).app U).hom.toAlgebra
  have hbij := (isIso_weakNormalization_restrict_iff_bijective_sections hX hU).mp h
  have : _root_.IsReduced
      ↥(relativeWeakNormalization Γ(X, U)
        Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)) :=
    isReduced_of_injective (Subalgebra.val _) Subtype.val_injective
  exact isReduced_of_injective _ hbij.1

/-! ### The affine criterion over an affine open -/

/-- Over an affine open of a reduced scheme presented by a ring `A`, the weak normalization
morphism restricts to an isomorphism exactly when `A` coincides with its relative weak
normalization in the integral closure of its total ring of fractions. -/
private lemma isIso_weakNormalization_restrict_iff_bijective
    {X : Scheme.{u}} [IsReduced X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {A : Type u} [CommRing A] (U : X.Opens) (e : Spec (.of A) ≅ U.toScheme) :
    IsIso (Scheme.weakNormalization X hX ∣_ U) ↔
      Function.Bijective (algebraMap A
        (relativeWeakNormalization A (integralClosure A (FractionRing A)))) := by
  have hU : IsAffineOpen U := IsAffine.of_isIso e.inv
  let := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X
  let : IsDominant (Scheme.normalization X hX) := Scheme.normalization_isDominant X hX
  let := ((Scheme.normalization X hX).app U).hom.toAlgebra
  let ePre := preimageNormalizationIsoSpecIntegralClosure hX U e
  have hcomp : ePre.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap A (integralClosure A (FractionRing A)))) =
      (Scheme.normalization X hX ∣_ U) ≫ e.inv :=
    preimageNormalizationIsoSpecIntegralClosure_hom_comp hX U e
  have hdom : IsDominant (Spec.map (CommRingCat.ofHom
      (algebraMap A (integralClosure A (FractionRing A))))) := by
    have : IsDominant (Scheme.normalization X hX ∣_ U) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) inferInstance U
    have hc : IsDominant (ePre.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap A (integralClosure A (FractionRing A))))) := by
      rw [hcomp]; infer_instance
    exact IsDominant.of_comp ePre.hom _
  have hdom' : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
      Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)))) :=
    sections_specMap_isDominant (Scheme.normalization X hX) hU
  have hcompat : (algebraMap Γ(X, U)
        Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)).comp
        (affineOpenCoordinateRingEquiv U e).toRingHom =
      (affineOpenCoordinateRingEquiv
        (Scheme.normalization X hX ⁻¹ᵁ U) ePre.symm).toRingHom.comp
          (algebraMap A (integralClosure A (FractionRing A))) := by
    ext x
    exact app_affineOpenCoordinateRingEquiv (Scheme.normalization X hX) hU e ePre.symm
      (algebraMap A (integralClosure A (FractionRing A))) hcomp x
  exact (isIso_weakNormalization_restrict_iff_bijective_sections hX hU).trans
    (bijective_algebraMap_relativeWeakNormalization_congr
      (affineOpenCoordinateRingEquiv U e)
      (affineOpenCoordinateRingEquiv (Scheme.normalization X hX ⁻¹ᵁ U) ePre.symm)
      hcompat hdom hdom').symm

/-- **Stacks Project, Tag 0H3U.** Over an affine open of a reduced scheme the weak normalization
morphism restricts to an isomorphism exactly when the ring of sections satisfies the two
conditions of Tag 0H3T. -/
theorem isIso_weakNormalization_restrict_iff {X : Scheme.{u}} [IsReduced X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    IsIso (Scheme.weakNormalization X hX ∣_ U) ↔ IsWeaklyNormalRing Γ(X, U) := by
  have hA : ∀ V : (Spec Γ(X, U)).Opens, IsCompact (V : Set (Spec Γ(X, U))) →
      (irreducibleComponents V).Finite := fun V hV =>
    finite_irreducibleComponents_of_isOpenImmersion hU.isoSpec.inv
      (fun W hW => finite_irreducibleComponents_of_isOpenImmersion U.ι hX W hW) V hV
  have : IsReduced (Spec Γ(X, U)) := inferInstance
  have hTop : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), IsIso (g ∣_ ⊤) ↔ IsIso g := by
    intro Z W g
    have hloc := IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := MorphismProperty.isomorphisms Scheme) (f := g) (fun _ : Unit => ⊤) (by simp)
    exact ⟨fun h => hloc.mpr fun _ => h, fun h => hloc.mp h ()⟩
  refine (isIso_weakNormalization_restrict_iff_bijective hX U hU.isoSpec.symm).trans ?_
  refine (isIso_weakNormalization_restrict_iff_bijective (X := Spec Γ(X, U)) hA ⊤
    (Spec Γ(X, U)).topIso.symm).symm.trans ?_
  exact (hTop _).trans (isWeaklyNormal_spec_iff Γ(X, U) hA)

/-! ### The local criteria -/

/-- A weakly normal scheme is reduced. -/
theorem isReduced_of_isWeaklyNormal {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (hWN : Scheme.IsWeaklyNormal X hX) : IsReduced X :=
  isReduced_of_isOpenCover_sections (fun U : X.affineOpens => U.1)
    (iSup_affineOpens_eq_top X) (fun U => U.2) fun U =>
      isReduced_sections_of_isIso_weakNormalization_restrict hX U.2
        (IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hWN U.1)

/-- The ring of sections of a weakly normal scheme over an affine open is weakly normal. -/
private lemma isWeaklyNormalRing_of_isWeaklyNormal {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (hWN : Scheme.IsWeaklyNormal X hX) (U : X.affineOpens) :
    IsWeaklyNormalRing Γ(X, U.1) := by
  have : IsReduced X := isReduced_of_isWeaklyNormal hX hWN
  exact (isIso_weakNormalization_restrict_iff hX U.2).mp
    (IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hWN U.1)

/-- A scheme covered by affine opens with weakly normal rings of sections is weakly normal. -/
private lemma isWeaklyNormal_of_affine_cover {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {ι : Type*} (U : ι → X.affineOpens) (htop : (⨆ i, (U i).1) = ⊤)
    (hring : ∀ i, IsWeaklyNormalRing Γ(X, (U i).1)) : Scheme.IsWeaklyNormal X hX := by
  have : IsReduced X :=
    isReduced_of_isOpenCover_sections (fun i => (U i).1) htop (fun i => (U i).2)
      fun i => seminormalRing_isReduced (hring i).1
  change MorphismProperty.isomorphisms Scheme (Scheme.weakNormalization X hX)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun i => (U i).1) htop]
  exact fun i => (isIso_weakNormalization_restrict_iff hX (U i).2).mpr (hring i)

/-- **Stacks Project, Tag 0H3U.** Every open subscheme of a weakly normal scheme is weakly
normal. -/
@[stacks 0H3U "open subschemes"]
theorem isWeaklyNormal_open {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (hWN : Scheme.IsWeaklyNormal X hX) (U : X.Opens) :
    ∃ hU : ∀ V : U.toScheme.Opens,
      IsCompact (V : Set U.toScheme) → (irreducibleComponents V).Finite,
      Scheme.IsWeaklyNormal U.toScheme hU := by
  refine ⟨fun V hV => finite_irreducibleComponents_of_isOpenImmersion U.ι hX V hV, ?_⟩
  refine isWeaklyNormal_of_affine_cover _ (fun V : U.toScheme.affineOpens => V)
    (iSup_affineOpens_eq_top U.toScheme) fun V => ?_
  exact isWeaklyNormalRing_of_isWeaklyNormal hX hWN
    ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩

/-- **Stacks Project, Tag 0H3U.** For a scheme whose quasi-compact opens have finitely many
irreducible components, weak normality is equivalent to the two ring conditions of Tag 0H3T on
every affine open, to those conditions on a single affine open covering, and to the existence of
an open covering by weakly normal schemes. -/
@[stacks 0H3U "equivalent conditions"]
theorem isWeaklyNormal_tfae (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    List.TFAE [
      Scheme.IsWeaklyNormal X hX,
      ∀ U : X.affineOpens, IsWeaklyNormalRing Γ(X, U.1),
      ∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).1) = ⊤ ∧ ∀ i, IsWeaklyNormalRing Γ(X, (U i).1),
      ∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧
          ∀ i, ∃ hUi : ∀ V : (U i).toScheme.Opens,
            IsCompact (V : Set (U i).toScheme) → (irreducibleComponents V).Finite,
            Scheme.IsWeaklyNormal (U i).toScheme hUi] := by
  tfae_have 1 → 2 := fun hWN U => isWeaklyNormalRing_of_isWeaklyNormal hX hWN U
  tfae_have 2 → 3 := fun h =>
    ⟨X.affineOpens, fun U => U, iSup_affineOpens_eq_top X, fun U => h U⟩
  tfae_have 3 → 1 := by
    rintro ⟨I, U, htop, hring⟩
    exact isWeaklyNormal_of_affine_cover hX U htop hring
  tfae_have 1 → 4 := fun hWN =>
    ⟨X.affineOpens, fun U => U.1, iSup_affineOpens_eq_top X,
      fun U => isWeaklyNormal_open hX hWN U.1⟩
  tfae_have 4 → 1 := by
    rintro ⟨I, U, htop, hWN⟩
    refine isWeaklyNormal_of_affine_cover hX
      (fun p : Σ i : I, (U i).toScheme.affineOpens =>
        ⟨(U p.1).ι ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion (U p.1).ι⟩) ?_ ?_
    · refine top_unique fun x _ => ?_
      have hx : x ∈ ⨆ i, U i := htop ▸ Set.mem_univ x
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      obtain ⟨V, hV⟩ := Opens.mem_iSup.mp (show (⟨x, hi⟩ : U i) ∈
        ⨆ V : (U i).toScheme.affineOpens, (V : (U i).toScheme.Opens) from
          (iSup_affineOpens_eq_top (U i).toScheme) ▸ Set.mem_univ _)
      exact Opens.mem_iSup.mpr ⟨⟨i, V⟩, ⟨⟨x, hi⟩, hV, rfl⟩⟩
    · intro p
      obtain ⟨hUi, hWNi⟩ := hWN p.1
      exact isWeaklyNormalRing_of_isWeaklyNormal hUi hWNi p.2
  tfae_finish

end AlgebraicGeometry

end
