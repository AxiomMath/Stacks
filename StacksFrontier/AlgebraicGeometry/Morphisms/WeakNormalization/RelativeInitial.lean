module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Factorization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Localization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeWeakNormalization
import StacksFrontier.AlgebraicGeometry.Morphisms.PullbackRestrictTransport

/-!
# Relative weak normalization of a morphism of schemes

A quasi-compact, quasi-separated, dominant morphism of schemes `f : Y ⟶ X` admits an initial
factorization through a universal homeomorphism. The intermediate scheme is built by gluing the
spectra of the relative weak normalizations of the rings of sections over the affine opens of
the target: over an affine open `U` the chart is `Spec` of the relative weak normalization of
`Γ(X, U)` in `Γ(Y, f ⁻¹ᵁ U)`, and the transition maps along an inclusion of affine opens are
supplied by the compatibility of the relative weak normalization with localization.

## Main definitions

* `AlgebraicGeometry.affineWeakNormalizationAlgebra` is the algebra of an affine chart.
* `AlgebraicGeometry.affineWeakNormalizationFromSource` and
  `AlgebraicGeometry.affineWeakNormalizationToBase` are the two legs of an affine chart.
* `AlgebraicGeometry.UniversalHomeomorphismFactorization.AffineGluingData` records that a
  factorization is glued from the affine charts: the chart inclusions, the pullback squares
  identifying each chart with the inverse image of its affine open, and the identification of
  the first leg.
* `AlgebraicGeometry.weakNormalizationFactorization` is a chosen initial factorization, with
  `AlgebraicGeometry.weakNormalizationFactorizationIsInitial` its initiality and
  `AlgebraicGeometry.weakNormalizationAffineGluingData` its affine gluing data.

## Main results

* `AlgebraicGeometry.affineWeakNormalization_fac` says that the two legs of an affine chart
  factor the restricted morphism.
* `AlgebraicGeometry.exists_initial_universalHomeomorphismFactorization` says that the category
  of factorizations through a universal homeomorphism has an initial object, together with the
  affine gluing characterization used to construct it.
* `AlgebraicGeometry.sections_specMap_isDominant` says that a dominant morphism induces a
  dominant spectrum map on the sections over an affine open of the target.
* `AlgebraicGeometry.bijective_algebraMap_relativeWeakNormalization_congr` says that whether an
  algebra equals its own relative weak normalization is invariant under isomorphisms of the base
  ring and of the ambient algebra.
* The `AffineGluingData` API records that the transition maps between charts are canonical
  (`restriction_ι`, `restriction_toBase`, `restriction_refl`, `restriction_comp`), that they
  respect the first legs (`fromSource_restriction`), and that each one exhibits the smaller
  chart as a base change of the larger (`isPullback_restriction`).

## Implementation notes

The two factorization categories are defined in
`StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Factorization`, independently of this
existence theorem, so that the reduction to the relative normalization is available here.

The existence theorem retains the affine gluing data as well as initiality, because the
description of the glued scheme on affine opens is what the compatibility with restriction to an
open of the target needs.

The charts are indexed by `Scheme.AffineZariskiSite`, which is a plain `def` wrapping a subtype
of `X.Opens`. Its elements are therefore not visibly subtypes at reducible transparency, so
rewriting inside a goal mentioning `U.1` for `U : X.AffineZariskiSite` does not work. Every step
that needs such a rewrite is stated as a separate lemma whose binders are an open of `X`
together with a proof that it is affine, and applied at the use site as a term; this is why
`pullbackRestrictIsoRestrict_trans_eq_homOfLE`,
`pullbackRestrictIsoRestrict_hom_fromSource_comp`, `restriction_desc_compat`, `ι_desc_compat`
and `affineChartι` exist.

## References

* [Stacks Project, Tag 0H3N](https://stacks.math.columbia.edu/tag/0H3N)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The algebra of an affine chart of relative weak normalization. On an affine
inverse image `Spec B` of `Spec A`, this is `relativeWeakNormalization A B`.
Using sections also describes the construction before reducing to an integral
morphism by relative normalization. -/
public abbrev affineWeakNormalizationAlgebra
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) : CommRingCat.{u} :=
  letI := (f.app U).hom.toAlgebra
  CommRingCat.of (relativeWeakNormalization Γ(X, U) Γ(Y, f ⁻¹ᵁ U))

/-- The map from the inverse image of an open to its weak normalization chart. -/
public def affineWeakNormalizationFromSource
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    (f ⁻¹ᵁ U).toScheme ⟶ Spec (affineWeakNormalizationAlgebra f U) :=
  letI := (f.app U).hom.toAlgebra
  (f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (relativeWeakNormalization Γ(X, U) Γ(Y, f ⁻¹ᵁ U)).val.toRingHom)

/-- The map from a weak normalization chart to the corresponding affine open. -/
public def affineWeakNormalizationToBase
    {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) :
    Spec (affineWeakNormalizationAlgebra f U) ⟶ U :=
  letI := (f.app U).hom.toAlgebra
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
    (relativeWeakNormalization Γ(X, U) Γ(Y, f ⁻¹ᵁ U)))) ≫ hU.isoSpec.inv

/-- Both maps of an affine chart factor the restricted morphism. -/
@[reassoc]
public theorem affineWeakNormalization_fac
    {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) :
    affineWeakNormalizationFromSource f U ≫ affineWeakNormalizationToBase f hU = f ∣_ U := by
  dsimp [affineWeakNormalizationFromSource, affineWeakNormalizationToBase,
    affineWeakNormalizationAlgebra]
  rw [Category.assoc, ← Spec.map_comp_assoc]
  show (f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (f.app U) ≫ hU.isoSpec.inv = _
  rw [← Category.assoc, Scheme.Opens.toSpecΓ_naturality]
  simp

namespace UniversalHomeomorphismFactorization

/-- A gluing characterization of a factorization by the affine relative weak
normalizations. The pullback condition identifies each chart with the inverse
image of its affine open, and `fromSource_ι` identifies the first leg as well.
The transition maps along affine-open inclusions are consequently canonical;
their pullback property is the gluing input supplied by Tag 0H3K. -/
public structure AffineGluingData {Y X : Scheme.{u}} {f : Y ⟶ X}
    (F : UniversalHomeomorphismFactorization f) where
  /-- The inclusion of each affine weak normalization chart. -/
  ι : ∀ (U : X.Opens) (_ : IsAffineOpen U),
    Spec (affineWeakNormalizationAlgebra f U) ⟶ F.middle
  /-- The chart is the entire inverse image of the affine open. -/
  isPullback : ∀ (U : X.Opens) (hU : IsAffineOpen U),
    IsPullback (ι U hU) (affineWeakNormalizationToBase f hU) F.toBase U.ι
  /-- The source maps glue to the first leg of the factorization. -/
  fromSource_ι : ∀ (U : X.Opens) (hU : IsAffineOpen U),
    affineWeakNormalizationFromSource f U ≫ ι U hU = (f ⁻¹ᵁ U).ι ≫ F.toMiddle

namespace AffineGluingData

variable {Y X : Scheme.{u}} {f : Y ⟶ X}
    {F : UniversalHomeomorphismFactorization f} (D : F.AffineGluingData)

/-- Each affine chart of the gluing data is an open immersion, being a base change of the open
immersion of its affine open. -/
public instance (U : X.Opens) (hU : IsAffineOpen U) : IsOpenImmersion (D.ι U hU) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (D.isPullback U hU).flip
    inferInstance

/-- The affine algebra chart is isomorphic to the restriction of the glued
factorization over its affine open. -/
public def restrictIso (U : X.Opens) (hU : IsAffineOpen U) :
    Spec (affineWeakNormalizationAlgebra f U) ≅ (F.toBase ⁻¹ᵁ U).toScheme :=
  (D.isPullback U hU).isoPullback ≪≫ pullbackRestrictIsoRestrict F.toBase U

/-- The identification of a chart with the restriction over its affine open is compatible with
the inclusions into the middle scheme. -/
@[reassoc (attr := simp)]
public theorem restrictIso_hom_ι (U : X.Opens) (hU : IsAffineOpen U) :
    (D.restrictIso U hU).hom ≫ (F.toBase ⁻¹ᵁ U).ι = D.ι U hU := by
  simp [restrictIso]

/-- The identification of a chart with the restriction over its affine open is compatible with
the maps to the affine open. -/
@[reassoc (attr := simp)]
public theorem restrictIso_hom_toBase (U : X.Opens) (hU : IsAffineOpen U) :
    (D.restrictIso U hU).hom ≫ F.toBase ∣_ U = affineWeakNormalizationToBase f hU := by
  simp [restrictIso]

/-- The canonical transition map between two affine weak normalization charts. -/
public def restriction {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ V) :
    Spec (affineWeakNormalizationAlgebra f U) ⟶ Spec (affineWeakNormalizationAlgebra f V) :=
  (D.isPullback V hV).lift (D.ι U hU)
    (affineWeakNormalizationToBase f hU ≫ X.homOfLE hUV)
    (by rw [Category.assoc, Scheme.homOfLE_ι, (D.isPullback U hU).w])

/-- Transition maps commute with the inclusions of the charts into the middle scheme. -/
@[reassoc (attr := simp)]
public theorem restriction_ι {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ V) : D.restriction hU hV hUV ≫ D.ι V hV = D.ι U hU := by
  simp [restriction]

/-- Transition maps cover the inclusion of affine opens of the base. -/
@[reassoc (attr := simp)]
public theorem restriction_toBase {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ V) :
    D.restriction hU hV hUV ≫ affineWeakNormalizationToBase f hV =
      affineWeakNormalizationToBase f hU ≫ X.homOfLE hUV := by
  simp [restriction]

/-- Transition maps respect the first legs of the affine factorizations. -/
@[reassoc]
public theorem fromSource_restriction {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ V) :
    affineWeakNormalizationFromSource f U ≫ D.restriction hU hV hUV =
      Y.homOfLE (f.preimage_mono hUV) ≫ affineWeakNormalizationFromSource f V := by
  rw [← cancel_mono (D.ι V hV)]
  simp [Category.assoc, D.fromSource_ι]

/-- The transition map from a chart to itself is the identity. -/
@[simp]
public theorem restriction_refl {U : X.Opens} (hU : IsAffineOpen U) :
    D.restriction hU hU le_rfl = 𝟙 _ := by
  rw [← cancel_mono (D.ι U hU)]
  simp

/-- Transition maps satisfy the cocycle identity for affine-open inclusions. -/
@[reassoc (attr := simp)]
public theorem restriction_comp {U V W : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hUV : U ≤ V) (hVW : V ≤ W) :
    D.restriction hU hV hUV ≫ D.restriction hV hW hVW =
      D.restriction hU hW (hUV.trans hVW) := by
  rw [← cancel_mono (D.ι W hW)]
  simp

/-- Affine transitions identify the smaller chart with the base change of
the larger one. This is the compatibility supplied by localization in the
construction in Tag 0H3N. -/
public theorem isPullback_restriction {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ V) :
    IsPullback (D.restriction hU hV hUV) (affineWeakNormalizationToBase f hU)
      (affineWeakNormalizationToBase f hV) (X.homOfLE hUV) := by
  have H : IsPullback (D.restriction hU hV hUV ≫ D.ι V hV)
      (affineWeakNormalizationToBase f hU) F.toBase (X.homOfLE hUV ≫ V.ι) := by
    simpa using D.isPullback U hU
  exact H.of_right (D.restriction_toBase hU hV hUV) (D.isPullback V hV)

end AffineGluingData

end UniversalHomeomorphismFactorization

section

private lemma relativeWeakNormalization_restrict_mem
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (a : A →+* A') (b : B →+* B')
    (hcompat : (algebraMap A' B').comp a = b.comp (algebraMap A B))
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A' B')).op))
    (hC : UniversalHomeomorphism (Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A (relativeWeakNormalization A B))).op))
    (c : relativeWeakNormalization A B) :
    b c.1 ∈ relativeWeakNormalization A' B' := by
  classical
  let C := relativeWeakNormalization A B
  let D : Subalgebra A' B' := Algebra.adjoin A' (Set.range (fun x : C => b x.1))
  let : Algebra A A' := a.toAlgebra
  let : Algebra A B' := ((algebraMap A' B').comp a).toAlgebra
  let : Algebra A D :=
    ((algebraMap A' D).comp (algebraMap A A')).toAlgebra
  let : IsScalarTower A A' D := IsScalarTower.of_algebraMap_eq fun x => rfl
  let e : C →+* D := RingHom.codRestrict (b.comp C.val.toRingHom) D
    (fun x => Algebra.subset_adjoin ⟨x, rfl⟩)
  have heA : e.comp (algebraMap A C) = algebraMap A D := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    show b (algebraMap A B x) = (algebraMap A' B') (a x)
    simpa [e, D, RingHom.comp_apply] using
      (congrArg (fun g : A →+* B' => g x) hcompat).symm
  have hIntC : Algebra.IsIntegral A C := algebraMap_isIntegral_iff.mp <|
    IsIntegralHom.SpecMap_iff.mp
      ((universalHomeomorphism_iff_integral_universallyInjective_surjective
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)).mp hC).1
  have hIntD : Algebra.IsIntegral A' D := Algebra.IsIntegral.adjoin fun x hx => by
    rcases hx with ⟨c, rfl⟩
    have hc : _root_.IsIntegral A (c.1 : B) := IsIntegral.map C.val (hIntC.isIntegral c)
    exact IsIntegral.map_of_comp_eq a b hcompat hc
  have hIntSpec : IsIntegralHom
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A' D)).op) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr hIntD)
  have hker : RingHom.ker (algebraMap A' D) ≤ nilradical A' := fun x hx =>
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap A' B')).mp
      hdom.denseRange <| RingHom.mem_ker.mpr <| by
        simpa using congrArg (fun z : D => (z : B')) (RingHom.mem_ker.mp hx)
  have hsurj := specMap_surjective_of_integral_of_ker_le_nilradical hIntSpec hker
  have hUnique : ∀ (K : Type u) [Field K] (φ ψ : D →+* K),
      φ.comp (algebraMap A' D) = ψ.comp (algebraMap A' D) → φ = ψ := by
    intro K hK φ ψ hφψ
    have hA : ∀ x : A, (φ.comp e).comp (algebraMap A C) x =
        (ψ.comp e).comp (algebraMap A C) x := by
      intro x
      have hrewrite : algebraMap A' D (a x) = e (algebraMap A C x) :=
        (congrArg (fun q : A →+* D => q x) heA).symm
      simpa [RingHom.comp_apply, hrewrite] using congrArg (fun q : A' →+* K => q (a x)) hφψ
    have hφψC := ringHom_eq_of_universalHomeomorphism
      (algebraMap A C) hC (φ.comp e) (ψ.comp e) hA
    apply RingHom.ext
    intro x
    exact Algebra.adjoin_induction (s := Set.range (fun z : C => b z.1))
      (p := fun y hy => φ ⟨y, hy⟩ = ψ ⟨y, hy⟩)
      (fun y hy => by
        obtain ⟨c, rfl⟩ := hy
        exact congrArg (fun q : C →+* K => q c) hφψC)
      (fun a' => congrArg (fun q : A' →+* K => q a') hφψ)
      (fun y z hy hz hfy hfz => by
        show φ ((⟨y, hy⟩ : D) + ⟨z, hz⟩) = ψ ((⟨y, hy⟩ : D) + ⟨z, hz⟩)
        calc
          φ ((⟨y, hy⟩ : D) + ⟨z, hz⟩) = φ ⟨y, hy⟩ + φ ⟨z, hz⟩ := map_add _ _ _
          _ = ψ ⟨y, hy⟩ + ψ ⟨z, hz⟩ := by rw [hfy, hfz]
          _ = ψ ((⟨y, hy⟩ : D) + ⟨z, hz⟩) := (map_add _ _ _).symm)
      (fun y z hy hz hfy hfz => by
        show φ ((⟨y, hy⟩ : D) * ⟨z, hz⟩) = ψ ((⟨y, hy⟩ : D) * ⟨z, hz⟩)
        calc
          φ ((⟨y, hy⟩ : D) * ⟨z, hz⟩) = φ ⟨y, hy⟩ * φ ⟨z, hz⟩ := map_mul _ _ _
          _ = ψ ⟨y, hy⟩ * ψ ⟨z, hz⟩ := by rw [hfy, hfz]
          _ = ψ ((⟨y, hy⟩ : D) * ⟨z, hz⟩) := (map_mul _ _ _).symm)
      (x := x.1) x.2
  have hUI := universallyInjective_specMap_of_ringHom_unique
    (algebraMap A' D) hUnique
  have hD := universalHomeomorphism_of_integral_universallyInjective_surjective
    hIntSpec hUI hsurj
  have hle := range_le_relativeWeakNormalization A' B' D
    D.val hdom hD
  rw [Subalgebra.range_val D] at hle
  exact hle (Algebra.subset_adjoin ⟨c, rfl⟩)

/-- The spectrum map of the sections of a dominant morphism over an affine open of the target is
again dominant. -/
theorem sections_specMap_isDominant
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    {U : X.Opens} (hU : IsAffineOpen U) : IsDominant (Spec.map (f.app U)) := by
  have : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsDominant f› U
  have : IsDominant ((f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (f.app U)) := by
    rw [Scheme.Opens.toSpecΓ_naturality]
    show IsDominant ((f ∣_ U) ≫ hU.isoSpec.hom)
    infer_instance
  exact IsDominant.of_comp (f ⁻¹ᵁ U).toSpecΓ (Spec.map (f.app U))

/-- The restriction map between two affine weak normalization charts along an inclusion of
affine opens. -/
private def weakNormalizationRestrictionOfLE
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V) :
    affineWeakNormalizationAlgebra f V ⟶ affineWeakNormalizationAlgebra f U :=
  letI := (f.app U).hom.toAlgebra
  letI := (f.app V).hom.toAlgebra
  CommRingCat.ofHom <| RingHom.codRestrict
    ((Y.presheaf.map (homOfLE (f.preimage_mono hUV)).op).hom.comp
      (relativeWeakNormalization Γ(X, V) Γ(Y, f ⁻¹ᵁ V)).val.toRingHom)
    (relativeWeakNormalization Γ(X, U) Γ(Y, f ⁻¹ᵁ U))
    (relativeWeakNormalization_restrict_mem
      (X.presheaf.map (homOfLE hUV).op).hom
      (Y.presheaf.map (homOfLE (f.preimage_mono hUV)).op).hom
      (congrArg CommRingCat.Hom.hom (f.naturality (homOfLE hUV).op))
      (sections_specMap_isDominant f hU)
      (relativeWeakNormalization_isUniversalHomeomorphism _ _
        (sections_specMap_isDominant f hV)))

private def weakNormalizationRestriction
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    affineWeakNormalizationAlgebra f V.1 ⟶ affineWeakNormalizationAlgebra f U.1 :=
  weakNormalizationRestrictionOfLE f U.2 V.2 (Scheme.AffineZariskiSite.toOpens_mono i.le)

/-- The first legs of two affine charts are compatible with the restriction map between
them. -/
private lemma homOfLE_affineWeakNormalizationFromSource
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V) :
    Y.homOfLE (f.preimage_mono hUV) ≫ affineWeakNormalizationFromSource f V =
      affineWeakNormalizationFromSource f U ≫
        Spec.map (weakNormalizationRestrictionOfLE f hU hV hUV) := by
  dsimp only [affineWeakNormalizationFromSource]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
    (f.preimage_mono hUV), Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl

private def weakNormalizationDiagram
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f] :
    X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := affineWeakNormalizationAlgebra f U.unop.1
  map i := weakNormalizationRestriction f i.unop
  map_id U := by
    apply CommRingCat.hom_ext
    ext x
    simp [weakNormalizationRestriction, weakNormalizationRestrictionOfLE]
  map_comp i j := by
    apply CommRingCat.hom_ext
    ext x
    simp only [weakNormalizationRestriction, weakNormalizationRestrictionOfLE,
      CommRingCat.hom_ofHom, RingHom.comp_apply, CommRingCat.hom_comp]
    change (Y.presheaf.map _).hom x.1 =
      (Y.presheaf.map _).hom ((Y.presheaf.map _).hom x.1)
    rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
    rfl

private def weakNormalizationDiagramMap
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f] :
    (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶
      weakNormalizationDiagram f where
  app U := letI := (f.app U.unop.1).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(X, U.unop.1)
      (relativeWeakNormalization Γ(X, U.unop.1) Γ(Y, f ⁻¹ᵁ U.unop.1)))
  naturality {U V} i := by
    ext x
    exact Subtype.ext
      congr($(f.naturality
        (homOfLE (Scheme.AffineZariskiSite.toOpens_mono i.unop.le)).op) x)

/-- The compatibility of two structure maps with isomorphisms of the base ring and of the
ambient algebra, transported to the inverse isomorphisms. -/
private lemma algebraMap_comp_symm_of_compat
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (a : A ≃+* A') (b : B ≃+* B')
    (hcompat : (algebraMap A' B').comp a.toRingHom = b.toRingHom.comp (algebraMap A B)) :
    (algebraMap A B).comp a.symm.toRingHom = b.symm.toRingHom.comp (algebraMap A' B') := by
  ext x
  apply b.injective
  simpa using (congrArg (fun g : A →+* B' => g (a.symm x)) hcompat).symm

private def relativeWeakNormalizationRingEquiv
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (a : A ≃+* A') (b : B ≃+* B')
    (hcompat : (algebraMap A' B').comp a.toRingHom = b.toRingHom.comp (algebraMap A B))
    (hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hdom' : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A' B')))) :
    relativeWeakNormalization A B ≃+*
      relativeWeakNormalization A' B' := by
  let C := relativeWeakNormalization A B
  let C' := relativeWeakNormalization A' B'
  let g : C →+* C' := RingHom.codRestrict (b.toRingHom.comp C.val.toRingHom) C'
    (relativeWeakNormalization_restrict_mem a.toRingHom b.toRingHom hcompat hdom'
      (relativeWeakNormalization_isUniversalHomeomorphism A B hdom))
  refine RingEquiv.ofBijective g ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (b.injective (congrArg Subtype.val h))
  · intro y
    have hy : b.symm y.1 ∈ C :=
      relativeWeakNormalization_restrict_mem a.symm.toRingHom b.symm.toRingHom
        (algebraMap_comp_symm_of_compat a b hcompat) hdom
        (relativeWeakNormalization_isUniversalHomeomorphism A' B' hdom') y
    exact ⟨⟨b.symm y.1, hy⟩, Subtype.ext (b.apply_symm_apply y.1)⟩

/-- Along isomorphisms of the base ring and of the ambient algebra, a relative weak
normalization equal to the base ring stays equal to the base ring. -/
private lemma bijective_algebraMap_relativeWeakNormalization_of_ringEquiv
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (a : A ≃+* A') (b : B ≃+* B')
    (hcompat : (algebraMap A' B').comp a.toRingHom = b.toRingHom.comp (algebraMap A B))
    (hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hdom' : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A' B'))))
    (h : Function.Bijective (algebraMap A (relativeWeakNormalization A B))) :
    Function.Bijective (algebraMap A' (relativeWeakNormalization A' B')) := by
  have hab (x : A) : algebraMap A' B' (a x) = b (algebraMap A B x) :=
    congrArg (fun g : A →+* B' => g x) hcompat
  refine ⟨fun x y hxy => ?_, fun c => ?_⟩
  · apply a.symm.injective
    apply h.1
    apply Subtype.ext
    show algebraMap A B (a.symm x) = algebraMap A B (a.symm y)
    apply b.injective
    rw [← hab, ← hab, a.apply_symm_apply, a.apply_symm_apply]
    exact congrArg Subtype.val hxy
  · have hmem : b.symm (c : B') ∈ relativeWeakNormalization A B :=
      relativeWeakNormalization_restrict_mem a.symm.toRingHom b.symm.toRingHom
        (algebraMap_comp_symm_of_compat a b hcompat) hdom
        (relativeWeakNormalization_isUniversalHomeomorphism A' B' hdom') c
    obtain ⟨x, hx⟩ := h.2 ⟨b.symm (c : B'), hmem⟩
    have hxv : algebraMap A B x = b.symm (c : B') := congrArg Subtype.val hx
    refine ⟨a x, Subtype.ext ?_⟩
    show algebraMap A' B' (a x) = (c : B')
    rw [hab, hxv, b.apply_symm_apply]

/-- Whether the relative weak normalization of a dominant algebra map is the base ring itself
depends only on the isomorphism class of the base ring and the ambient algebra. -/
theorem bijective_algebraMap_relativeWeakNormalization_congr
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (a : A ≃+* A') (b : B ≃+* B')
    (hcompat : (algebraMap A' B').comp a.toRingHom = b.toRingHom.comp (algebraMap A B))
    (hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hdom' : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A' B')))) :
    Function.Bijective (algebraMap A (relativeWeakNormalization A B)) ↔
      Function.Bijective (algebraMap A' (relativeWeakNormalization A' B')) :=
  ⟨bijective_algebraMap_relativeWeakNormalization_of_ringEquiv a b hcompat hdom hdom',
    bijective_algebraMap_relativeWeakNormalization_of_ringEquiv a.symm b.symm
      (algebraMap_comp_symm_of_compat a b hcompat) hdom' hdom⟩

private lemma specMap_isDominant_of_ringEquiv
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (a : A ≃+* A') (b : B ≃+* B')
    (hcompat : (algebraMap A' B').comp a.toRingHom = b.toRingHom.comp (algebraMap A B))
    (hdom' : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A' B')))) :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  let e : Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap A' B'))) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    Arrow.isoMk (Scheme.Spec.mapIso b.toCommRingCatIso.op)
      (Scheme.Spec.mapIso a.toCommRingCatIso.op) (by
        show Spec.map (CommRingCat.ofHom b.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap A B)) =
          Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫
            Spec.map (CommRingCat.ofHom a.toRingHom)
        rw [← Spec.map_comp, ← Spec.map_comp]
        exact congrArg (fun g : A →+* B' => Spec.map (CommRingCat.ofHom g)) hcompat.symm)
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsDominant) e).mp hdom'

private lemma localizedSubalgebra_isLocalization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (C : Subalgebra A B) (S : Submonoid A) :
    let SB := S.map (algebraMap A B)
    let L := Localization S
    let LB := Localization SB
    let f : L →+* LB := IsLocalization.map LB (algebraMap A B) S.le_comap_map
    let _ : Algebra L LB := f.toAlgebra
    let H : Subalgebra L LB := Algebra.adjoin L (algebraMap B LB '' (C : Set B))
    let j : C →+* H := RingHom.codRestrict
      ((algebraMap B LB).comp C.val.toRingHom) H
      (fun c => Algebra.subset_adjoin ⟨c.1, c.2, rfl⟩)
    let _ : Algebra C H := j.toAlgebra
    IsLocalization (S.map (algebraMap A C)) H := by
  let SB := S.map (algebraMap A B)
  let L := Localization S
  let LB := Localization SB
  let f : L →+* LB := IsLocalization.map LB (algebraMap A B) S.le_comap_map
  let : Algebra L LB := f.toAlgebra
  let H : Subalgebra L LB := Algebra.adjoin L (algebraMap B LB '' (C : Set B))
  let j : C →+* H := RingHom.codRestrict
    ((algebraMap B LB).comp C.val.toRingHom) H
    (fun c => Algebra.subset_adjoin ⟨c.1, c.2, rfl⟩)
  let : Algebra C H := j.toAlgebra
  let d (s : S) : LB := algebraMap B LB (algebraMap A B s.1)
  let k : C →+* LB := (algebraMap B LB).comp C.val.toRingHom
  have hd (s t : S) : d (s * t) = d s * d t := by simp [d]
  have hdk (s : S) : d s = k (algebraMap A C s.1) := by
    simp [d, k]
  have hfractions : ∀ x : LB, x ∈ H →
      ∃ c : C, ∃ s : S, x * d s = k c := by
    apply Algebra.adjoin_induction (p := fun x _ =>
      ∃ c : C, ∃ s : S, x * d s = k c)
    · rintro x ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, 1, by simp [d, k]⟩
    · intro r
      obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj S r
      refine ⟨algebraMap A C a, s, ?_⟩
      show f r * d s = k (algebraMap A C a)
      simpa [d, k, f, IsLocalization.map_eq, Subalgebra.algebraMap_eq] using
        congrArg f hs
    · intro x y _ _ hx hy
      obtain ⟨c, s, hs⟩ := hx
      obtain ⟨e, t, ht⟩ := hy
      refine ⟨c * algebraMap A C t.1 + e * algebraMap A C s.1, s * t, ?_⟩
      calc
        (x + y) * d (s * t) = (x * d s) * d t + (y * d t) * d s := by
          rw [hd]; ring
        _ = k (c * algebraMap A C t.1 + e * algebraMap A C s.1) := by
          rw [hs, ht, map_add, map_mul, map_mul, ← hdk, ← hdk]
    · intro x y _ _ hx hy
      obtain ⟨c, s, hs⟩ := hx
      obtain ⟨e, t, ht⟩ := hy
      refine ⟨c * e, s * t, ?_⟩
      calc
        (x * y) * d (s * t) = (x * d s) * (y * d t) := by rw [hd]; ring
        _ = k (c * e) := by rw [hs, ht, map_mul]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha, rfl⟩ := hs
    have hu := (IsLocalization.map_units L (⟨a, ha⟩ : S)).map (algebraMap L H)
    convert hu using 1
    apply Subtype.ext
    show (algebraMap B LB) (algebraMap A B a) = f (algebraMap A L a)
    simp [f]
  · intro x
    obtain ⟨c, s, hs⟩ := hfractions x.1 x.2
    refine ⟨⟨c, ⟨algebraMap A C s.1, ⟨s.1, s.2, rfl⟩⟩⟩, ?_⟩
    apply Subtype.ext
    show x.1 * d s = k c
    exact hs
  · intro x y hxy
    have hval : algebraMap B LB x.1 = algebraMap B LB y.1 :=
      congrArg (fun z : H => (z : LB)) hxy
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists SB LB).mp hval
    obtain ⟨a, ha, he⟩ := t.2
    refine ⟨⟨algebraMap A C a, ⟨a, ha, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    simpa [Subalgebra.algebraMap_eq, he] using ht

private lemma relativeWeakNormalization_isLocalization
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A A' B'] [IsScalarTower A B B'] (S : Submonoid A)
    [IsLocalization S A'] [IsLocalization (S.map (algebraMap A B)) B']
    (hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hdom' : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A' B'))))
    (g : relativeWeakNormalization A B →+*
      relativeWeakNormalization A' B')
    (hg : ∀ c, (g c : B') = algebraMap B B' c.1) :
    letI := g.toAlgebra
    IsLocalization (S.map (algebraMap A (relativeWeakNormalization A B)))
      (relativeWeakNormalization A' B') := by
  let C := relativeWeakNormalization A B
  let SB := S.map (algebraMap A B)
  let L := Localization S
  let LB := Localization SB
  let f : L →+* LB := IsLocalization.map LB (algebraMap A B) S.le_comap_map
  let : Algebra L LB := f.toAlgebra
  let a : L ≃ₐ[A] A' := IsLocalization.algEquiv S L A'
  let b : LB ≃ₐ[B] B' := IsLocalization.algEquiv SB LB B'
  have hab : (algebraMap A' B').comp a.toRingEquiv.toRingHom =
      b.toRingEquiv.toRingHom.comp (algebraMap L LB) := by
    apply IsLocalization.ringHom_ext S
    ext x
    show algebraMap A' B' (a (algebraMap A L x)) = b (f (algebraMap A L x))
    rw [a.commutes, IsLocalization.map_eq, b.commutes]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hlocdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap L LB))) :=
    specMap_isDominant_of_ringEquiv a.toRingEquiv b.toRingEquiv hab hdom'
  let D := relativeWeakNormalization L LB
  let H : Subalgebra L LB := Algebra.adjoin L (algebraMap B LB '' (C : Set B))
  have hHD : H = D := relativeWeakNormalization_localization A B hdom S
  let j : C →+* H := RingHom.codRestrict
    ((algebraMap B LB).comp C.val.toRingHom) H
    (fun c => Algebra.subset_adjoin ⟨c.1, c.2, rfl⟩)
  let : Algebra C H := j.toAlgebra
  have : IsLocalization (S.map (algebraMap A C)) H :=
    localizedSubalgebra_isLocalization C S
  let eHD : H ≃+* D := (Subalgebra.equivOfEq _ _ hHD).toRingEquiv
  let eDD := relativeWeakNormalizationRingEquiv a.toRingEquiv b.toRingEquiv
    hab hlocdom hdom'
  let := g.toAlgebra
  let e : H ≃ₐ[C] relativeWeakNormalization A' B' :=
    { eHD.trans eDD with
      commutes' := fun c => by
        apply Subtype.ext
        show b (algebraMap B LB c.1) = (g c : B')
        rw [AlgEquiv.commutes, hg] }
  exact IsLocalization.isLocalization_of_algEquiv (S.map (algebraMap A C)) e

private lemma coequifibered_weakNormalizationDiagramMap
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : (weakNormalizationDiagramMap f).Coequifibered := by
  refine Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  let := (f.app U.1).hom.toAlgebra
  let := (f.app (X.basicOpen r)).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  let inst : Algebra Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ X.basicOpen r) :=
    (Y.presheaf.map (homOfLE (f.preimage_mono (X.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(X, X.basicOpen r) := U.2.isLocalization_basicOpen _
  have : IsLocalization.Away ((algebraMap Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)) r)
      Γ(Y, f ⁻¹ᵁ X.basicOpen r) := by
    let : Algebra Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, Y.basicOpen (f.app _ r)) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
      (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  let : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ X.basicOpen r) :=
    (f.appLE _ _ (f.preimage_mono (X.basicOpen_le _))).hom.toAlgebra
  have : IsScalarTower Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ X.basicOpen r) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen r) Γ(Y, f ⁻¹ᵁ X.basicOpen r) :=
    .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
  have : IsLocalization ((Submonoid.powers r).map
      (algebraMap Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1))) Γ(Y, f ⁻¹ᵁ X.basicOpen r) := by
    simpa only [Submonoid.map_powers] using
      (inferInstance : IsLocalization.Away (algebraMap Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) r) _)
  have H := relativeWeakNormalization_isLocalization
    (A' := Γ(X, X.basicOpen r)) (B' := Γ(Y, f ⁻¹ᵁ X.basicOpen r)) (Submonoid.powers r)
    (sections_specMap_isDominant f U.2)
    (sections_specMap_isDominant f (U.basicOpen r).2)
    (weakNormalizationRestriction f (homOfLE (U.basicOpen_le r))).hom (fun _ => rfl)
  let : Algebra
      (relativeWeakNormalization Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1))
      (relativeWeakNormalization Γ(X, X.basicOpen r) Γ(Y, f ⁻¹ᵁ X.basicOpen r)) :=
    (weakNormalizationRestriction f (homOfLE (U.basicOpen_le r))).hom.toAlgebra
  rw [Submonoid.map_powers] at H
  exact H

private def weakNormalizationGlueData
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] :=
  Scheme.AffineZariskiSite.relativeGluingData (coequifibered_weakNormalizationDiagramMap f)

private lemma relativeGluingData_hasColimit
    {X : Scheme.{u}} {𝒰 : X.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
    [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] (D : 𝒰.RelativeGluingData) :
    Limits.HasColimit D.functor := by infer_instance

/-- The compatibility of two affine charts needed to glue the first legs into a single
morphism out of the source. -/
private lemma pullbackRestrictIsoRestrict_hom_fromSource_comp
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
    {G : Scheme.{u}} (cU : Spec (affineWeakNormalizationAlgebra f U) ⟶ G)
    (cV : Spec (affineWeakNormalizationAlgebra f V) ⟶ G)
    (hc : Spec.map (weakNormalizationRestrictionOfLE f hU hV hUV) ≫ cV = cU)
    (t : Limits.pullback f U.ι ⟶ Limits.pullback f V.ι)
    (ht : t ≫ Limits.pullback.fst f V.ι = Limits.pullback.fst f U.ι) :
    t ≫ (pullbackRestrictIsoRestrict f V).hom ≫
        affineWeakNormalizationFromSource f V ≫ cV =
      (pullbackRestrictIsoRestrict f U).hom ≫
        affineWeakNormalizationFromSource f U ≫ cU := by
  have H := (Iso.inv_comp_eq _).mp
    (pullbackRestrictIsoRestrict_trans_eq_homOfLE f hUV t ht)
  rw [← Category.assoc, H, Category.assoc,
    ← Category.assoc (Y.homOfLE (f.preimage_mono hUV)),
    homOfLE_affineWeakNormalizationFromSource f hU hV hUV, Category.assoc, hc]

private def toWeakNormalization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : Y ⟶ (weakNormalizationGlueData f).glued :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f)
    (fun U => (pullbackRestrictIsoRestrict f U.1).hom ≫
      affineWeakNormalizationFromSource f U.1 ≫
        (weakNormalizationGlueData f).cover.f U) fun {U V : X.AffineZariskiSite} i => by
  let : Preorder ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f).I₀ :=
    inferInstanceAs (Preorder X.AffineZariskiSite)
  let : Limits.HasColimit (weakNormalizationGlueData f).functor :=
    relativeGluingData_hasColimit (weakNormalizationGlueData f)
  have hc : Spec.map (weakNormalizationRestrictionOfLE f U.2 V.2
        (Scheme.AffineZariskiSite.toOpens_mono i.le)) ≫
      (weakNormalizationGlueData f).cover.f V =
      (weakNormalizationGlueData f).cover.f U :=
    Limits.colimit.w (weakNormalizationGlueData f).functor i
  exact pullbackRestrictIsoRestrict_hom_fromSource_comp f U.2 V.2
    (Scheme.AffineZariskiSite.toOpens_mono i.le) _ _ hc
    (Scheme.Cover.trans ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f) i)
    (Scheme.Cover.trans_map ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f) i)

/-- The affine weak normalization chart over an affine open, as an open subscheme of the
glued scheme. -/
private def affineChartι
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] {U : X.Opens} (hU : IsAffineOpen U) :
    Spec (affineWeakNormalizationAlgebra f U) ⟶ (weakNormalizationGlueData f).glued :=
  (weakNormalizationGlueData f).cover.f ⟨U, hU⟩

private lemma ι_toWeakNormalization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toWeakNormalization f =
      affineWeakNormalizationFromSource f U.1 ≫ affineChartι f U.2 := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f).f U ≫ toWeakNormalization f
  · congr 1
    simp only [pullbackRestrictIsoRestrict_hom_ι]
    rfl
  delta toWeakNormalization
  generalize_proofs
  apply Scheme.OpenCover.map_glueMorphismsOfLocallyDirected
  assumption

private noncomputable abbrev affineWeakNormalizationFactorization
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    UniversalHomeomorphismFactorization
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) where
  middle := Spec (CommRingCat.of (relativeWeakNormalization A B))
  toMiddle :=
    Scheme.Spec.map (CommRingCat.ofHom (relativeWeakNormalization A B).val.toRingHom).op
  toBase :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (relativeWeakNormalization A B))).op
  fac := by
    rw [← Scheme.Spec.map_comp]
    rfl
  universalHomeomorphism := relativeWeakNormalization_isUniversalHomeomorphism A B h

private noncomputable def affineWeakNormalizationFactorizationIsInitial
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    Limits.IsInitial (affineWeakNormalizationFactorization A B h) := by
  classical
  let C := relativeWeakNormalization A B
  letI : CommRing C := inferInstance
  let F := affineWeakNormalizationFactorization A B h
  have key (T : UniversalHomeomorphismFactorization
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
      ∃ α : F ⟶ T, ∀ m : F ⟶ T, m = α := by
    let : IsIntegralHom T.toBase :=
      (universalHomeomorphism_iff_integral_universallyInjective_surjective
        T.toBase).mp T.universalHomeomorphism |>.1
    let : IsAffine T.middle := isAffine_of_isAffineHom T.toBase
    let e : T.middle ≅ Spec (CommRingCat.of Γ(T.middle, ⊤)) := T.middle.isoSpec
    let g₀ : CommRingCat.of Γ(T.middle, ⊤) ⟶ CommRingCat.of B :=
      Spec.homEquiv (T.toMiddle ≫ e.hom)
    let a₀ : CommRingCat.of A ⟶ CommRingCat.of Γ(T.middle, ⊤) :=
      Spec.homEquiv (e.inv ≫ T.toBase)
    have hg : Spec.map g₀ = T.toMiddle ≫ e.hom := Spec.map_preimage _
    have ha : Spec.map a₀ = e.inv ≫ T.toBase := Spec.map_preimage _
    have hcomp : a₀ ≫ g₀ = CommRingCat.ofHom (algebraMap A B) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, ha]
      simp [Category.assoc, T.fac]
    let : Algebra A Γ(T.middle, ⊤) := a₀.hom.toAlgebra
    let g : Γ(T.middle, ⊤) →ₐ[A] B :=
      { toRingHom := g₀.hom
        commutes' := fun x =>
          congrArg (fun q : A →+* B => q x) (congrArg CommRingCat.Hom.hom hcomp) }
    have hC : UniversalHomeomorphism (Spec.map a₀) := by
      constructor
      have hArrow : Arrow.mk (Spec.map a₀) ≅ Arrow.mk T.toBase :=
        Arrow.isoMk e.symm (Iso.refl _) (by simp [ha])
      exact (MorphismProperty.arrow_mk_iso_iff
        (P := MorphismProperty.universally (topologically @IsHomeomorph)) hArrow).mpr
          T.universalHomeomorphism.universally_isHomeomorph
    have hle := range_le_relativeWeakNormalization A B
      Γ(T.middle, ⊤) g h hC
    let ψ : Γ(T.middle, ⊤) →ₐ[A] C :=
      g.codRestrict C (fun x => hle ⟨x, rfl⟩)
    let m₀ : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of Γ(T.middle, ⊤)) :=
      Spec.map (CommRingCat.ofHom ψ.toRingHom)
    let mhom : F.middle ⟶ T.middle := m₀ ≫ e.inv
    have hψ : CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C) ≫
        CommRingCat.ofHom C.val.toRingHom = g₀ := by
      apply CommRingCat.hom_ext
      ext x
      rfl
    have hψBase : a₀ ≫ CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C) =
        CommRingCat.ofHom (algebraMap A C) := by
      apply CommRingCat.hom_ext
      ext x
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
        RingHom.coe_comp, Function.comp_apply]
      change (ψ (algebraMap A Γ(T.middle, ⊤) x) : B) =
        (algebraMap A C x : B)
      exact congrArg Subtype.val (ψ.commutes x)
    let α : UniversalHomeomorphismFactorization.Hom F T := by
      refine ⟨mhom, ?_, ?_⟩
      · dsimp [mhom, m₀, F, affineWeakNormalizationFactorization]
        apply (cancel_mono e.hom).1
        calc
          (Spec.map (CommRingCat.ofHom C.val.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C)) ≫ e.inv) ≫ e.hom =
              Spec.map (CommRingCat.ofHom C.val.toRingHom) ≫
                Spec.map (CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C)) := by
                  simp [Category.assoc]
          _ = Spec.map ((CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C)) ≫
              CommRingCat.ofHom C.val.toRingHom) := by rw [← Spec.map_comp]
          _ = Spec.map g₀ := congrArg Spec.map hψ
          _ = T.toMiddle ≫ e.hom := hg
      · dsimp [mhom, m₀, F, affineWeakNormalizationFactorization]
        calc
          Spec.map (CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C)) ≫ e.inv ≫ T.toBase =
              Spec.map (CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C)) ≫ Spec.map a₀ := by
                rw [ha]
          _ = Spec.map (a₀ ≫ CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C)) := by
                rw [← Spec.map_comp]
          _ = Spec.map (CommRingCat.ofHom (algebraMap A C)) := congrArg Spec.map hψBase
    refine ⟨α, fun m => ?_⟩
    apply UniversalHomeomorphismFactorization.Hom.ext
    let k : CommRingCat.of Γ(T.middle, ⊤) ⟶ CommRingCat.of C :=
      Spec.homEquiv (m.hom ≫ e.hom)
    have hk : Spec.map k = m.hom ≫ e.hom := Spec.map_preimage _
    have hki : k ≫ CommRingCat.ofHom C.val.toRingHom = g₀ := by
      apply Spec.map_injective
      have hm : F.toMiddle ≫ m.hom = T.toMiddle := m.toMiddle_hom
      change Spec.map (CommRingCat.ofHom C.val.toRingHom) ≫ m.hom = T.toMiddle at hm
      calc
        Spec.map (k ≫ CommRingCat.ofHom C.val.toRingHom) =
            Spec.map (CommRingCat.ofHom C.val.toRingHom) ≫ Spec.map k := by
              rw [Spec.map_comp]
        _ = Spec.map (CommRingCat.ofHom C.val.toRingHom) ≫ (m.hom ≫ e.hom) :=
              congrArg (fun q => Spec.map (CommRingCat.ofHom C.val.toRingHom) ≫ q) hk
        _ = (Spec.map (CommRingCat.ofHom C.val.toRingHom) ≫ m.hom) ≫ e.hom :=
              (Category.assoc _ _ _).symm
        _ = T.toMiddle ≫ e.hom := congrArg (fun q => q ≫ e.hom) hm
        _ = Spec.map g₀ := hg.symm
    have hkψ : k = CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C) := by
      have hincl : k ≫ CommRingCat.ofHom C.val.toRingHom =
          CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C) ≫
            CommRingCat.ofHom C.val.toRingHom := hki.trans hψ.symm
      apply CommRingCat.hom_ext
      ext x
      have hx := congrArg (fun q => (CommRingCat.Hom.hom q) x) hincl
      change C.val.toRingHom (k.hom x) = C.val.toRingHom (ψ x)
      exact hx
    have hm_eq : m.hom ≫ e.hom =
        Spec.map (CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C)) := by
      rw [← hk, hkψ]
    have hm_eq' : m.hom ≫ e.hom =
        Spec.map (CommRingCat.ofHom (ψ : Γ(T.middle, ⊤) →+* C)) := by
      simpa [F, affineWeakNormalizationFactorization] using hm_eq
    dsimp [F, affineWeakNormalizationFactorization] at hm_eq'
    have hm_final : m.hom = m₀ ≫ e.inv := by
      dsimp [F, affineWeakNormalizationFactorization]
      apply (cancel_mono e.hom).1
      simpa [m₀, Category.assoc] using hm_eq'
    exact hm_final
  exact Limits.IsInitial.ofUniqueHom (fun T => (key T).choose) fun T m => (key T).choose_spec m

private lemma opens_toSpecΓ_bijective
    {Y : Scheme.{u}} (V : Y.Opens) (T : Scheme.{u}) [IsAffine T] :
    Function.Bijective (fun h : Spec Γ(Y, V) ⟶ T => V.toSpecΓ ≫ h) := by
  constructor
  · intro g h H
    apply AlgebraicGeometry.ext_of_isAffine
    have E := congrArg Scheme.Hom.appTop H
    simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop] at E
    exact (cancel_mono ((Scheme.ΓSpecIso Γ(Y, V)).hom ≫ V.topIso.inv)).mp E
  · intro g
    refine ⟨Spec.map (g.appTop ≫ V.topIso.hom) ≫ T.isoSpec.inv, ?_⟩
    show (V.toScheme.toSpecΓ ≫ Spec.map V.topIso.inv) ≫
      (Spec.map (g.appTop ≫ V.topIso.hom) ≫ T.isoSpec.inv) = g
    rw [Category.assoc, ← Spec.map_comp_assoc]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp

private lemma affineChart_existsUnique_desc
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    {U : X.Opens} (hU : IsAffineOpen U)
    (T : Scheme.{u}) (q : T ⟶ U.toScheme)
    (hq : UniversalHomeomorphism q)
    (g : (f ⁻¹ᵁ U).toScheme ⟶ T) (hg : g ≫ q = f ∣_ U) :
    ∃! m : Spec (affineWeakNormalizationAlgebra f U) ⟶ T,
      affineWeakNormalizationFromSource f U ≫ m = g ∧
        m ≫ q = affineWeakNormalizationToBase f hU := by
  have : IsAffine U.toScheme := hU
  have : IsIntegralHom q :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective q).mp hq).1
  have : IsAffine T := isAffine_of_isAffineHom q
  let := (f.app U).hom.toAlgebra
  let A := Γ(X, U)
  let B := Γ(Y, f ⁻¹ᵁ U)
  have hdom := sections_specMap_isDominant f hU
  obtain ⟨g₀, hg₀⟩ := (opens_toSpecΓ_bijective (f ⁻¹ᵁ U) T).2 g
  change (f ⁻¹ᵁ U).toSpecΓ ≫ g₀ = g at hg₀
  let q₀ := q ≫ hU.isoSpec.hom
  have hq₀ : UniversalHomeomorphism q₀ := ⟨(MorphismProperty.cancel_right_of_respectsIso
      (topologically @IsHomeomorph).universally q hU.isoSpec.hom).mpr hq.1⟩
  have hfac : g₀ ≫ q₀ = Spec.map (f.app U) := by
    apply (opens_toSpecΓ_bijective (f ⁻¹ᵁ U) (Spec A)).1
    show (f ⁻¹ᵁ U).toSpecΓ ≫ g₀ ≫ q ≫ hU.isoSpec.hom = _
    rw [← Category.assoc, hg₀, ← Category.assoc, hg]
    exact (Scheme.Opens.toSpecΓ_naturality f U).symm
  let G : UniversalHomeomorphismFactorization (Spec.map (f.app U)) :=
    ⟨T, g₀, q₀, hfac, hq₀⟩
  let I := affineWeakNormalizationFactorizationIsInitial A B hdom
  let m := I.to G
  refine ⟨m.hom, ⟨?_, ?_⟩, ?_⟩
  · show (f ⁻¹ᵁ U).toSpecΓ ≫
      (affineWeakNormalizationFactorization A B hdom).toMiddle ≫ m.hom = g
    rw [m.toMiddle_hom]
    exact hg₀
  · rw [← cancel_mono hU.isoSpec.hom, Category.assoc]
    show m.hom ≫ G.toBase = _
    rw [m.hom_toBase]
    simp [affineWeakNormalizationToBase, affineWeakNormalizationFactorization, A, B]
  · rintro n ⟨hn₁, hn₂⟩
    let n' : affineWeakNormalizationFactorization A B hdom ⟶ G :=
      ⟨n, (opens_toSpecΓ_bijective (f ⁻¹ᵁ U) T).1 (by
          show affineWeakNormalizationFromSource f U ≫ n = _
          exact hn₁.trans hg₀.symm), by
        show n ≫ q ≫ hU.isoSpec.hom = _
        rw [← Category.assoc, hn₂]
        simp [affineWeakNormalizationToBase, A, B]⟩
    exact congrArg UniversalHomeomorphismFactorization.Hom.hom (I.hom_ext n' m)

/-- Transport a morphism property along an equality of morphisms. -/
lemma morphismProperty_congr {C : Type*} [Category C] (P : MorphismProperty C)
    {X Y : C} {g h : X ⟶ Y} (e : g = h) (hg : P g) : P h := e ▸ hg

private lemma property_relativeGluing_toBase
    {X : Scheme.{u}} {𝒰 : X.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
    [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    (D : 𝒰.RelativeGluingData) (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] (H : ∀ i, P (D.natTrans.app i)) : P D.toBase := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) 𝒰
  intro i
  show P (Limits.pullback.snd D.toBase (𝒰.f i))
  exact (MorphismProperty.cancel_left_of_respectsIso P
      (D.isPullback_natTrans_ι_toBase i).flip.isoPullback.hom
      (Limits.pullback.snd D.toBase (𝒰.f i))).mp
    (morphismProperty_congr P
      (IsPullback.isoPullback_hom_snd (D.isPullback_natTrans_ι_toBase i).flip).symm (H i))

private lemma weakNormalizationGlueData_toBase_universalHomeomorphism
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : UniversalHomeomorphism (weakNormalizationGlueData f).toBase := by
  have H (U : X.AffineZariskiSite) :
      UniversalHomeomorphism ((weakNormalizationGlueData f).natTrans.app U) := by
    let := (f.app U.1).hom.toAlgebra
    have h := relativeWeakNormalization_isUniversalHomeomorphism
      Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) (sections_specMap_isDominant f U.2)
    exact ⟨(MorphismProperty.cancel_right_of_respectsIso
      (topologically @IsHomeomorph).universally _ U.2.isoSpec.inv).mpr h.1⟩
  have hzl : IsZariskiLocalAtTarget @IsIntegralHom :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  have H' (U : X.AffineZariskiSite) :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp (H U)
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
    ⟨property_relativeGluing_toBase (weakNormalizationGlueData f) (@IsIntegralHom)
        fun U => (H' U).1,
      property_relativeGluing_toBase (weakNormalizationGlueData f) (@UniversallyInjective)
        fun U => (H' U).2.1,
      property_relativeGluing_toBase (weakNormalizationGlueData f) (@Surjective)
        fun U => (H' U).2.2⟩

/-- Over each affine open of the target, the glued first leg followed by the structure map of
the gluing is the original morphism. -/
private lemma ι_toWeakNormalization_comp_toBase
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toWeakNormalization f ≫ (weakNormalizationGlueData f).toBase =
      (f ⁻¹ᵁ U.1).ι ≫ f := by
  have hU : IsAffineOpen U.1 := U.2
  rw [← Category.assoc, ι_toWeakNormalization, Category.assoc,
    show affineChartι f U.2 ≫ (weakNormalizationGlueData f).toBase =
      affineWeakNormalizationToBase f hU ≫ U.1.ι from
        (weakNormalizationGlueData f).ι_toBase ⟨U.1, U.2⟩,
    ← Category.assoc, affineWeakNormalization_fac, morphismRestrict_ι]

private def gluedWeakNormalizationFactorization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : UniversalHomeomorphismFactorization f where
  middle := (weakNormalizationGlueData f).glued
  toMiddle := toWeakNormalization f
  toBase := (weakNormalizationGlueData f).toBase
  fac := Scheme.Cover.hom_ext (Y.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top X) f.base.1)) _ _ fun U =>
      ι_toWeakNormalization_comp_toBase f U
  universalHomeomorphism := weakNormalizationGlueData_toBase_universalHomeomorphism f

private def gluedWeakNormalizationAffineGluingData
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : (gluedWeakNormalizationFactorization f).AffineGluingData where
  ι _ hU := affineChartι f hU
  isPullback U hU := ((weakNormalizationGlueData f).isPullback_natTrans_ι_toBase ⟨U, hU⟩).flip
  fromSource_ι U hU := (ι_toWeakNormalization f ⟨U, hU⟩).symm

private lemma affineChart_global_existsUnique_desc
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    {U : X.Opens} (hU : IsAffineOpen U) (T : UniversalHomeomorphismFactorization f) :
    ∃! m : Spec (affineWeakNormalizationAlgebra f U) ⟶ T.middle,
      affineWeakNormalizationFromSource f U ≫ m = (f ⁻¹ᵁ U).ι ≫ T.toMiddle ∧
        m ≫ T.toBase = affineWeakNormalizationToBase f hU ≫ U.ι := by
  let q := Limits.pullback.snd T.toBase U.ι
  have hq : UniversalHomeomorphism q :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback T.toBase U.ι) T.universalHomeomorphism.1⟩
  let g := Limits.pullback.lift ((f ⁻¹ᵁ U).ι ≫ T.toMiddle) (f ∣_ U)
    (by rw [Category.assoc, T.fac, morphismRestrict_ι])
  obtain ⟨m, hm, huniq⟩ := affineChart_existsUnique_desc f hU _ q hq g
    (Limits.pullback.lift_snd _ _ _)
  refine ⟨m ≫ Limits.pullback.fst _ _, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, hm.1]
    exact Limits.pullback.lift_fst _ _ _
  · rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hm.2]
  · rintro n ⟨hn₁, hn₂⟩
    let n' := Limits.pullback.lift n (affineWeakNormalizationToBase f hU) hn₂
    have hn' : n' = m := huniq n' ⟨by
      apply Limits.pullback.hom_ext <;>
        simp [n', g, Category.assoc, hn₁, affineWeakNormalization_fac,
          Limits.pullback.lift_fst, Limits.pullback.lift_snd],
      Limits.pullback.lift_snd _ _ _⟩
    simpa [n', Limits.pullback.lift_fst] using
      congrArg (fun k => k ≫ Limits.pullback.fst T.toBase U.ι) hn'

/-- The descent map of a larger affine chart, precomposed with a transition map, satisfies the
characterizing equations of the descent map of the smaller chart. -/
private lemma restriction_desc_compat
    {Y X : Scheme.{u}} {f : Y ⟶ X} {F : UniversalHomeomorphismFactorization f}
    (D : F.AffineGluingData) {T : UniversalHomeomorphismFactorization f}
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
    (mV : Spec (affineWeakNormalizationAlgebra f V) ⟶ T.middle)
    (hmV₁ : affineWeakNormalizationFromSource f V ≫ mV = (f ⁻¹ᵁ V).ι ≫ T.toMiddle)
    (hmV₂ : mV ≫ T.toBase = affineWeakNormalizationToBase f hV ≫ V.ι) :
    affineWeakNormalizationFromSource f U ≫ D.restriction hU hV hUV ≫ mV =
        (f ⁻¹ᵁ U).ι ≫ T.toMiddle ∧
      (D.restriction hU hV hUV ≫ mV) ≫ T.toBase =
        affineWeakNormalizationToBase f hU ≫ U.ι := by
  refine ⟨?_, ?_⟩
  · rw [← Category.assoc, D.fromSource_restriction, Category.assoc, hmV₁, ← Category.assoc,
      Scheme.homOfLE_ι]
  · rw [Category.assoc, hmV₂, ← Category.assoc, D.restriction_toBase, Category.assoc,
      Scheme.homOfLE_ι]

/-- A morphism of factorizations out of the glued one restricts on each affine chart to a
morphism satisfying the characterizing equations of the chart's descent map. -/
private lemma ι_desc_compat
    {Y X : Scheme.{u}} {f : Y ⟶ X} {F : UniversalHomeomorphismFactorization f}
    (D : F.AffineGluingData) {T : UniversalHomeomorphismFactorization f} (n : F ⟶ T)
    {U : X.Opens} (hU : IsAffineOpen U) :
    affineWeakNormalizationFromSource f U ≫ D.ι U hU ≫ n.hom =
        (f ⁻¹ᵁ U).ι ≫ T.toMiddle ∧
      (D.ι U hU ≫ n.hom) ≫ T.toBase = affineWeakNormalizationToBase f hU ≫ U.ι := by
  refine ⟨?_, ?_⟩
  · rw [← Category.assoc, D.fromSource_ι, Category.assoc, n.toMiddle_hom]
  · rw [Category.assoc, n.hom_toBase]
    exact (D.isPullback U hU).w

private def gluedWeakNormalizationIsInitial
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : Limits.IsInitial (gluedWeakNormalizationFactorization f) := by
  classical
  let d := weakNormalizationGlueData f
  letI : Small.{u} (Scheme.AffineZariskiSite.directedCover X).I₀ :=
    inferInstanceAs (Small.{u} X.AffineZariskiSite)
  letI : Quiver.IsThin (Scheme.AffineZariskiSite.directedCover X).I₀ :=
    inferInstanceAs (Quiver.IsThin X.AffineZariskiSite)
  letI : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin d
  letI : Limits.HasColimit d.functor := Scheme.IsLocallyDirected.instHasColimit d.functor
  let D := gluedWeakNormalizationAffineGluingData f
  have hlocal (T : UniversalHomeomorphismFactorization f) (U : X.AffineZariskiSite) :=
    affineChart_global_existsUnique_desc f U.2 T
  choose m hm huniq using hlocal
  let c (T : UniversalHomeomorphismFactorization f) : Limits.Cocone d.functor :=
    { pt := T.middle
      ι := { app := fun U => m T U
             naturality := fun {U V} i => by
               have ht : d.functor.map i =
                   D.restriction U.2 V.2 (Scheme.AffineZariskiSite.toOpens_mono i.le) := by
                 apply (cancel_mono (D.ι V.1 V.2)).mp
                 change d.functor.map i ≫ Limits.colimit.ι d.functor V = _
                 rw [Limits.colimit.w]
                 exact (D.restriction_ι U.2 V.2
                   (Scheme.AffineZariskiSite.toOpens_mono i.le)).symm
               change d.functor.map i ≫ m T V = m T U ≫ 𝟙 T.middle
               rw [ht, Category.comp_id]
               exact huniq T U _ (restriction_desc_compat D U.2 V.2
                 (Scheme.AffineZariskiSite.toOpens_mono i.le) (m T V) (hm T V).1
                 (hm T V).2) } }
  let g (T : UniversalHomeomorphismFactorization f) :
      (gluedWeakNormalizationFactorization f).middle ⟶ T.middle :=
    Limits.colimit.desc d.functor (c T)
  have hg (T : UniversalHomeomorphismFactorization f) (U : X.affineOpens) :
      D.ι U.1 U.2 ≫ g T = m T U := Limits.colimit.ι_desc _ _
  have hmid (T : UniversalHomeomorphismFactorization f) (U : X.affineOpens) :
      (f ⁻¹ᵁ U.1).ι ≫ (gluedWeakNormalizationFactorization f).toMiddle ≫ g T =
        (f ⁻¹ᵁ U.1).ι ≫ T.toMiddle := by
    rw [← Category.assoc, ← D.fromSource_ι U.1 U.2, Category.assoc, hg]
    exact (hm T U).1
  have hbase (T : UniversalHomeomorphismFactorization f) (U : X.affineOpens) :
      D.ι U.1 U.2 ≫ g T ≫ T.toBase =
        D.ι U.1 U.2 ≫ (gluedWeakNormalizationFactorization f).toBase := by
    rw [← Category.assoc, hg, (hm T U).2]
    exact (D.isPullback U.1 U.2).w.symm
  let G (T : UniversalHomeomorphismFactorization f) :
      gluedWeakNormalizationFactorization f ⟶ T :=
    { hom := g T
      toMiddle_hom := Scheme.Cover.hom_ext (Y.openCoverOfIsOpenCover _
        (.comap (iSup_affineOpens_eq_top X) f.base.1)) _ _ fun U => hmid T U
      hom_toBase := d.cover.hom_ext _ _ fun U => hbase T U }
  refine Limits.IsInitial.ofUniqueHom G (fun T n => ?_)
  apply UniversalHomeomorphismFactorization.Hom.ext
  have hfin (U : X.affineOpens) : D.ι U.1 U.2 ≫ n.hom = D.ι U.1 U.2 ≫ g T := by
    rw [hg]
    exact huniq T U _ (ι_desc_compat D n U.2)
  exact d.cover.hom_ext _ _ fun U => hfin U

end

/-- **Relative weak normalization** ([Stacks, Tag 0H3N]). A quasi-compact, quasi-separated,
dominant morphism `f : Y ⟶ X` has an initial factorization `Y ⟶ X' ⟶ X` with `X' ⟶ X` a universal
homeomorphism, and this factorization is glued from the affine relative weak normalizations. -/
@[stacks 0H3N "weak_initial"]
public theorem exists_initial_universalHomeomorphismFactorization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] :
    ∃ F : UniversalHomeomorphismFactorization f,
      Nonempty (Limits.IsInitial F) ∧ Nonempty F.AffineGluingData :=
  ⟨gluedWeakNormalizationFactorization f, ⟨gluedWeakNormalizationIsInitial f⟩,
    ⟨gluedWeakNormalizationAffineGluingData f⟩⟩

/-- A chosen relative weak normalization factorization. -/
public noncomputable def weakNormalizationFactorization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : UniversalHomeomorphismFactorization f :=
  Classical.choose (exists_initial_universalHomeomorphismFactorization f)

/-- The chosen relative weak normalization factorization is initial. -/
public noncomputable def weakNormalizationFactorizationIsInitial
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : Limits.IsInitial (weakNormalizationFactorization f) :=
  Classical.choice
    (Classical.choose_spec (exists_initial_universalHomeomorphismFactorization f)).1

/-- The chosen factorization is the gluing of the affine relative weak
normalizations, with both legs identified on each affine open. -/
public def weakNormalizationAffineGluingData
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : (weakNormalizationFactorization f).AffineGluingData :=
  Classical.choice
    (Classical.choose_spec (exists_initial_universalHomeomorphismFactorization f)).2

end AlgebraicGeometry

end
