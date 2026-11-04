module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCurveOverCompleteLocalProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Uniqueness of contractions over a complete Noetherian local ring, for algebraic spaces

Let `Λ` be a complete Noetherian local ring with residue field `κ`, let `X`, `Y₁`, `Y₂` be
algebraic spaces, proper and flat over `Spec Λ`, whose closed fibres have dimension at most one,
and let `cᵢ : X ⟶ Yᵢ` be morphisms over `Spec Λ`. Suppose the closed fibres are presented by
schemes, the closed fibres `Y₁,ₛ`, `Y₂,ₛ` are identified compatibly with `c₁,ₛ` and `c₂,ₛ`, and
`c₁,ₛ` satisfies `𝒪 ≅ c₁,ₛ,* 𝒪` and `R¹c₁,ₛ,* 𝒪 = 0`. Then there is an isomorphism `Y₁ ≅ Y₂`
over `Spec Λ` compatible with `c₁`, `c₂` and the identification of closed fibres.

The three spaces are schemes, projective over `Λ`, by [Stacks, Tag 0AE7]
(`AlgebraicGeometry.Space.exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one`),
and the statement is then the scheme case
`AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds`, read through the
Yoneda embedding. This is the complete case of the proof of [Stacks, Tag 0E89] for families of
curves, whose total spaces are algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.exists_schemeModel_of_isProper_of_dimension_adicFibre_le_one`: a
  proper algebraic space over `Spec Λ` with closed fibre of dimension at most one is, over
  `Spec Λ`, the algebraic space of a proper scheme.
* `AlgebraicGeometry.Space.exists_schemeHom_of_iso`: a morphism between two such spaces is the
  morphism of a morphism of schemes over `Spec Λ`.
* `AlgebraicGeometry.Space.exists_isPullback_closedPoint_of_isPullback`: a scheme presentation of
  the closed fibre of such a space is the closed fibre of the scheme.
* `AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isAdicComplete_of_isAlgebraicSpace`: the
  statement above, from the statement of Stacks 0A4Z as `halg`.
* `AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isAdicComplete_of_isAlgebraicSpace_holds`:
  the statement above, with Stacks 0A4Z supplied by
  `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq`.

## Implementation notes

[Stacks, Tag 0AE7] is available in this library from Grothendieck's algebraization of morphisms
of algebraic spaces, [Stacks, Tag 0A4Z], which enters the first statements here as the hypothesis
`halg` in the form `exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one` takes it,
and is discharged in the last one by `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq`.

## References

* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of A)))

local notation "𝒯" => BigFppfOver.toScheme B (Spec (CommRingCat.of A)) hS

/-- **A proper algebraic space over a complete local base with closed fibre of dimension at most
one is the algebraic space of a proper scheme over the base**, by [Stacks, Tag 0AE7], which is
taken from [Stacks, Tag 0A4Z] in the form `halg`. -/
theorem exists_schemeModel_of_isProper_of_dimension_adicFibre_le_one
    (halg : ∀ {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B (Spec (.of A)) hS X → IsAlgebraicSpace B (Spec (.of A)) hS Y →
      ∀ (fX : X ⟶ yoneda.obj (baseObject A B hS)) (fY : Y ⟶ yoneda.obj (baseObject A B hS)),
      IsProper B (Spec (.of A)) hS fX → IsSeparated B (Spec (.of A)) hS fY →
      IsFiniteType B (Spec (.of A)) hS fY →
      ∀ (g : ∀ n, adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX n ⟶
          adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fY n),
      (∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A (maximalIdeal A) B hS
          (contains_adicThickening A _ B hS) n)) =
        pullback.snd fX (yoneda.map (adicThickeningMap A (maximalIdeal A) B hS
          (contains_adicThickening A _ B hS) n))) →
      (∀ n, adicFibreSucc A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX n ≫
          g (n + 1) =
        g n ≫ adicFibreSucc A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fY n) →
      ∃! φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n,
        adicFibreMap A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) φ hφ n = g n)
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (Spec (.of A)) hS X)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (hproper : IsProper B (Spec (.of A)) hS fX)
    (hdim : dimension B (Spec (.of A)) hS
      (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hX fX 0) ≤ 1) :
    ∃ (Y : Scheme.{u}) (hY : B.Contains Y) (fY : Y ⟶ Spec (.of A))
      (_ : _root_.AlgebraicGeometry.IsProper fY)
      (e : X ≅ yoneda.obj (siteObject B (Spec (.of A)) hS hY fY)),
      e.hom ≫ yoneda.map (siteObjectToBase A B hS hY fY) = fX := by
  obtain ⟨Y, hY, fY, hproj, -, e, he⟩ :=
    exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one A B hS halg hX fX hproper
      hdim
  exact ⟨Y, hY, fY, hproj.isProper, e, he⟩

omit [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] in
/-- **A morphism between algebraic spaces of schemes over `Spec Λ` is a morphism of schemes over
`Spec Λ`.** Given isomorphisms `eᵢ` of algebraic spaces `Zᵢ` with the algebraic spaces of schemes
`Zᵢ'` over `Spec Λ`, a morphism `c : Z₁ ⟶ Z₂` is, through them, the algebraic space of a morphism
of schemes `γ : Z₁' ⟶ Z₂'` over `Spec Λ`. -/
theorem exists_schemeHom_of_iso {Z₁ Z₂ : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    {Y₁ Y₂ : Scheme.{u}} {hY₁ : B.Contains Y₁} {hY₂ : B.Contains Y₂} {f₁ : Y₁ ⟶ Spec (.of A)}
    {f₂ : Y₂ ⟶ Spec (.of A)} (e₁ : Z₁ ≅ yoneda.obj (siteObject B (Spec (.of A)) hS hY₁ f₁))
    (e₂ : Z₂ ≅ yoneda.obj (siteObject B (Spec (.of A)) hS hY₂ f₂)) (c : Z₁ ⟶ Z₂) :
    ∃ γ : siteObject B (Spec (.of A)) hS hY₁ f₁ ⟶ siteObject B (Spec (.of A)) hS hY₂ f₂,
      e₁.hom ≫ yoneda.map γ = c ≫ e₂.hom ∧ (𝒯).map γ ≫ f₂ = f₁ := by
  refine ⟨Yoneda.fullyFaithful.preimage (e₁.inv ≫ c ≫ e₂.hom), ?_, ?_⟩
  · rw [Functor.FullyFaithful.map_preimage, Iso.hom_inv_id_assoc]
  · exact congrArg (fun k => (𝒯).map k) (eq_of_hom_baseObject A B hS
      (Yoneda.fullyFaithful.preimage (e₁.inv ≫ c ≫ e₂.hom) ≫ siteObjectToBase A B hS hY₂ f₂)
      (siteObjectToBase A B hS hY₁ f₁))

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] in
/-- **A scheme presentation of the closed fibre of the space of a scheme.** Let `Z` be the
algebraic space of a scheme `fY : Y ⟶ Spec Λ` through `e`, and let `F ⟶ K` be a morphism of the
site presenting the fibre of `Z` over a point `k : K ⟶ Spec Λ` by a cartesian square. If `K` is,
through `ι`, the closed point of `Spec Λ`, then `F` is the closed fibre `Y ×_{Spec Λ} Spec κ` of
`Y`, by a cartesian square of schemes whose top morphism is read off `e`. -/
theorem exists_isPullback_closedPoint_of_isPullback
    {Z : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} {Y : Scheme.{u}} {hY : B.Contains Y}
    {fY : Y ⟶ Spec (.of A)} (e : Z ≅ yoneda.obj (siteObject B (Spec (.of A)) hS hY fY))
    {fZ : Z ⟶ yoneda.obj (baseObject A B hS)}
    (he : e.hom ≫ yoneda.map (siteObjectToBase A B hS hY fY) = fZ)
    {K F : BigFppfOver B (Spec (.of A)) hS} (k : K ⟶ baseObject A B hS) (t : F ⟶ K)
    (i : yoneda.obj F ⟶ Z) (hi : IsPullback i (yoneda.map t) fZ (yoneda.map k))
    (ι : Spec (.of (ResidueField A)) ≅ (𝒯).obj K)
    (hι : ι.hom ≫ (𝒯).map k = ContractionUniquenessComplete.closedPoint A) :
    ∃ j : F ⟶ siteObject B (Spec (.of A)) hS hY fY, yoneda.map j = i ≫ e.hom ∧
      IsPullback ((𝒯).map j) ((𝒯).map t ≫ ι.inv) fY
        (ContractionUniquenessComplete.closedPoint A) := by
  set j := Yoneda.fullyFaithful.preimage (i ≫ e.hom)
  have hj : yoneda.map j = i ≫ e.hom := Functor.FullyFaithful.map_preimage _ _
  refine ⟨j, hj, ?_⟩
  have h₁ : IsPullback (yoneda.map j) (yoneda.map t)
      (yoneda.map (siteObjectToBase A B hS hY fY)) (yoneda.map k) :=
    IsPullback.of_iso hi (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, hj]) (by simp) (by simp [he]) (by simp)
  have h₂ : IsPullback j t (siteObjectToBase A B hS hY fY) k :=
    IsPullback.of_map yoneda (yoneda.map_injective (by simpa only [Functor.map_comp] using h₁.w))
      h₁
  have _ : PreservesLimitsOfShape WalkingCospan (𝒯) :=
    preservesLimitsOfShape_walkingCospan_toScheme B _ hS
  have h₃ := h₂.map (𝒯)
  exact IsPullback.of_iso h₃ (Iso.refl _) (Iso.refl _) ι.symm (Iso.refl _) (by simp) (by simp)
    (by simp) (by simp [← hι])

omit [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] in
/-- A flat morphism of algebraic spaces which is, through an isomorphism, the algebraic space of a
scheme over `Spec Λ` makes that scheme flat over `Spec Λ`. -/
theorem flat_of_iso_yoneda {Z : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} {Y : Scheme.{u}}
    {hY : B.Contains Y} {fY : Y ⟶ Spec (.of A)}
    (e : Z ≅ yoneda.obj (siteObject B (Spec (.of A)) hS hY fY))
    {fZ : Z ⟶ yoneda.obj (baseObject A B hS)}
    (he : e.hom ≫ yoneda.map (siteObjectToBase A B hS hY fY) = fZ)
    (h : IsFlat B (Spec (.of A)) hS fZ) : Flat fY := by
  rw [← he] at h
  exact (holdsOnEveryEtaleChart_yoneda_map_iff B _ hS Flat.isEtaleLocalOnSourceAndTarget _).1
    ((holdsOnEveryEtaleChart_iso_comp_iff B _ hS _ e.hom _).1 h)

open Stacks.AlgebraicGeometry.TopDegreeBaseChange ContractionUniquenessComplete in
/-- **The complete Noetherian local case of [Stacks, Tag 0E89] for algebraic spaces.** Let `Λ` be
a complete Noetherian local ring, `X`, `Y₁`, `Y₂` algebraic spaces proper and flat over `Spec Λ`
whose closed fibres have dimension at most one, and `cᵢ : X ⟶ Yᵢ` morphisms. Let `k : K ⟶ Spec Λ`
be the closed point, identified with `Spec κ ⟶ Spec Λ` through `ι`, and let the fibres of `X`,
`Y₁`, `Y₂` over it be presented by schemes `F_X`, `F₁`, `F₂` (cartesian squares `iX`, `i₁`, `i₂`),
with `aᵢ : F_X ⟶ Fᵢ` the fibres of `cᵢ` and `φ : F₁ ≅ F₂` an isomorphism over `K` with
`a₁ ≫ φ = a₂`. If `a₁` has fibres of dimension at most one, `𝒪_{F₁} ≅ a₁,* 𝒪_{F_X}` and
`R¹a₁,* 𝒪_{F_X} = 0`, there is an isomorphism `ψ : Y₁ ≅ Y₂` with `c₁ ≫ ψ = c₂` whose restriction to
the closed fibre is `φ`.

[Stacks, Tag 0AE7] makes the three spaces schemes (it enters from [Stacks, Tag 0A4Z] as `halg`),
and the statement is then the scheme case
`AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds`, the hypotheses on
`a₁` passing to the special fibre of the scheme morphism along the identifications of the fibres
(`AlgebraicGeometry.Space.exists_isPullback_closedPoint_of_isPullback`). -/
theorem exists_iso_of_closedFibre_of_isAdicComplete_of_isAlgebraicSpace
    (halg : ∀ {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B (Spec (.of A)) hS X → IsAlgebraicSpace B (Spec (.of A)) hS Y →
      ∀ (fX : X ⟶ yoneda.obj (baseObject A B hS)) (fY : Y ⟶ yoneda.obj (baseObject A B hS)),
      IsProper B (Spec (.of A)) hS fX → IsSeparated B (Spec (.of A)) hS fY →
      IsFiniteType B (Spec (.of A)) hS fY →
      ∀ (g : ∀ n, adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX n ⟶
          adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fY n),
      (∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A (maximalIdeal A) B hS
          (contains_adicThickening A _ B hS) n)) =
        pullback.snd fX (yoneda.map (adicThickeningMap A (maximalIdeal A) B hS
          (contains_adicThickening A _ B hS) n))) →
      (∀ n, adicFibreSucc A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX n ≫
          g (n + 1) =
        g n ≫ adicFibreSucc A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fY n) →
      ∃! φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n,
        adicFibreMap A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) φ hφ n = g n)
    {X Y₁ Y₂ : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (hY₁ : IsAlgebraicSpace B (Spec (.of A)) hS Y₁)
    (hY₂ : IsAlgebraicSpace B (Spec (.of A)) hS Y₂)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (g₁ : Y₁ ⟶ yoneda.obj (baseObject A B hS))
    (g₂ : Y₂ ⟶ yoneda.obj (baseObject A B hS))
    (hpX : IsProper B (Spec (.of A)) hS fX) (hp₁ : IsProper B (Spec (.of A)) hS g₁)
    (hp₂ : IsProper B (Spec (.of A)) hS g₂)
    (hfX : IsFlat B (Spec (.of A)) hS fX) (hf₁ : IsFlat B (Spec (.of A)) hS g₁)
    (hf₂ : IsFlat B (Spec (.of A)) hS g₂)
    (hdX : dimension B (Spec (.of A)) hS
      (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hX fX 0) ≤ 1)
    (hd₁ : dimension B (Spec (.of A)) hS
      (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) g₁ 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hY₁ g₁ 0) ≤ 1)
    (hd₂ : dimension B (Spec (.of A)) hS
      (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) g₂ 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hY₂ g₂ 0) ≤ 1)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂)
    {K : BigFppfOver B (Spec (.of A)) hS} (k : K ⟶ baseObject A B hS)
    (ι : Spec (.of (ResidueField A)) ≅ (𝒯).obj K)
    (hι : ι.hom ≫ (𝒯).map k = ContractionUniquenessComplete.closedPoint A)
    {FX F₁ F₂ : BigFppfOver B (Spec (.of A)) hS} (tX : FX ⟶ K) (t₁ : F₁ ⟶ K) (t₂ : F₂ ⟶ K)
    (iX : yoneda.obj FX ⟶ X) (i₁ : yoneda.obj F₁ ⟶ Y₁) (i₂ : yoneda.obj F₂ ⟶ Y₂)
    (hiX : IsPullback iX (yoneda.map tX) fX (yoneda.map k))
    (hi₁ : IsPullback i₁ (yoneda.map t₁) g₁ (yoneda.map k))
    (hi₂ : IsPullback i₂ (yoneda.map t₂) g₂ (yoneda.map k))
    (a₁ : FX ⟶ F₁) (a₂ : FX ⟶ F₂) (ha₁ : a₁ ≫ t₁ = tX) (ha₂ : a₂ ≫ t₂ = tX)
    (hia₁ : iX ≫ c₁ = yoneda.map a₁ ≫ i₁) (hia₂ : iX ≫ c₂ = yoneda.map a₂ ≫ i₂)
    (φ : F₁ ≅ F₂) (hφ : φ.hom ≫ t₂ = t₁) (hφa : a₁ ≫ φ.hom = a₂)
    (hdimF : ∀ y, topologicalKrullDim (((𝒯).map a₁).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁))) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ g₂ = g₁ ∧ c₁ ≫ ψ.hom = c₂ ∧ i₁ ≫ ψ.hom = yoneda.map φ.hom ≫ i₂ := by
  -- the three spaces are schemes (Stacks 0AE7)
  obtain ⟨X', hX', fX', _, eX, heX⟩ :=
    exists_schemeModel_of_isProper_of_dimension_adicFibre_le_one A B hS halg hX fX hpX hdX
  obtain ⟨Y₁', hY₁', fY₁', _, e₁, he₁⟩ :=
    exists_schemeModel_of_isProper_of_dimension_adicFibre_le_one A B hS halg hY₁ g₁ hp₁ hd₁
  obtain ⟨Y₂', hY₂', fY₂', _, e₂, he₂⟩ :=
    exists_schemeModel_of_isProper_of_dimension_adicFibre_le_one A B hS halg hY₂ g₂ hp₂ hd₂
  have : Flat fX' := flat_of_iso_yoneda A B hS eX heX hfX
  have : Flat fY₁' := flat_of_iso_yoneda A B hS e₁ he₁ hf₁
  have : Flat fY₂' := flat_of_iso_yoneda A B hS e₂ he₂ hf₂
  -- the morphisms of schemes
  obtain ⟨γ₁, hγ₁, hγ₁b⟩ := exists_schemeHom_of_iso A B hS eX e₁ c₁
  obtain ⟨γ₂, hγ₂, hγ₂b⟩ := exists_schemeHom_of_iso A B hS eX e₂ c₂
  -- the closed fibres
  obtain ⟨jX, hjX, sqX⟩ :=
    exists_isPullback_closedPoint_of_isPullback A B hS eX heX k tX iX hiX ι hι
  obtain ⟨j₁, hj₁, sq₁⟩ :=
    exists_isPullback_closedPoint_of_isPullback A B hS e₁ he₁ k t₁ i₁ hi₁ ι hι
  obtain ⟨j₂, hj₂, sq₂⟩ :=
    exists_isPullback_closedPoint_of_isPullback A B hS e₂ he₂ k t₂ i₂ hi₂ ι hι
  have hja : ∀ {F : BigFppfOver B (Spec (.of A)) hS} {Y' : Scheme.{u}} {hY' : B.Contains Y'}
      {fY' : Y' ⟶ Spec (.of A)} {Z : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
      (e : Z ≅ yoneda.obj (siteObject B (Spec (.of A)) hS hY' fY')) (c : X ⟶ Z)
      (γ : siteObject B (Spec (.of A)) hS hX' fX' ⟶ siteObject B (Spec (.of A)) hS hY' fY')
      (hγ : eX.hom ≫ yoneda.map γ = c ≫ e.hom) (a : FX ⟶ F) (i : yoneda.obj F ⟶ Z)
      (j : F ⟶ siteObject B (Spec (.of A)) hS hY' fY') (hj : yoneda.map j = i ≫ e.hom)
      (hia : iX ≫ c = yoneda.map a ≫ i), jX ≫ γ = a ≫ j := by
    intro F Y' hY' fY' Z e c γ hγ a i j hj hia
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hjX, hj, Category.assoc, hγ, ← Category.assoc, hia,
      Category.assoc]
  have hθ : ∀ {F : BigFppfOver B (Spec (.of A)) hS} {Y' : Scheme.{u}} {hY' : B.Contains Y'}
      {fY' : Y' ⟶ Spec (.of A)}
      (γ : siteObject B (Spec (.of A)) hS hX' fX' ⟶ siteObject B (Spec (.of A)) hS hY' fY')
      (hγb : (𝒯).map γ ≫ fY' = fX') (a : FX ⟶ F) (t : F ⟶ K) (ha : a ≫ t = tX)
      (j : F ⟶ siteObject B (Spec (.of A)) hS hY' fY')
      (sq : IsPullback ((𝒯).map j) ((𝒯).map t ≫ ι.inv) fY'
        (ContractionUniquenessComplete.closedPoint A))
      (hjγ : jX ≫ γ = a ≫ j),
      sqX.isoPullback.hom ≫ specialMap fX' fY' ((𝒯).map γ) hγb =
        (𝒯).map a ≫ sq.isoPullback.hom := by
    intro F Y' hY' fY' γ hγb a t ha j sq hjγ
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst,
        Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp,
        hjγ]
    · rw [Category.assoc, specialMap_snd, IsPullback.isoPullback_hom_snd, Category.assoc,
        IsPullback.isoPullback_hom_snd, ← Category.assoc, ← Functor.map_comp, ha]
  have hθ₁ := hθ γ₁ hγ₁b a₁ t₁ ha₁ j₁ sq₁ (hja e₁ c₁ γ₁ hγ₁ a₁ i₁ j₁ hj₁ hia₁)
  have hθ₂ := hθ γ₂ hγ₂b a₂ t₂ ha₂ j₂ sq₂ (hja e₂ c₂ γ₂ hγ₂ a₂ i₂ j₂ hj₂ hia₂)
  -- the special-fibre hypotheses, transported to the scheme morphism
  set sm₁ := specialMap fX' fY₁' ((𝒯).map γ₁) hγ₁b
  have : _root_.AlgebraicGeometry.IsProper ((𝒯).map γ₁) := by
    have : _root_.AlgebraicGeometry.IsProper ((𝒯).map γ₁ ≫ fY₁') := by rw [hγ₁b]; infer_instance
    exact _root_.AlgebraicGeometry.IsProper.of_comp _ fY₁'
  have : _root_.AlgebraicGeometry.IsProper sm₁ := by
    have : _root_.AlgebraicGeometry.IsProper
        (sm₁ ≫ pullback.snd fY₁' (ContractionUniquenessComplete.closedPoint A)) := by
      rw [specialMap_snd]; infer_instance
    exact _root_.AlgebraicGeometry.IsProper.of_comp _
      (pullback.snd fY₁' (ContractionUniquenessComplete.closedPoint A))
  have ha₁e : (𝒯).map a₁ = sqX.isoPullback.hom ≫ sm₁ ≫ sq₁.isoPullback.inv := by
    rw [← Category.assoc, hθ₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : _root_.AlgebraicGeometry.IsProper ((𝒯).map a₁) := by rw [ha₁e]; infer_instance
  have H : IsPullback sqX.isoPullback.inv sm₁ ((𝒯).map a₁) sq₁.isoPullback.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [ha₁e, Iso.inv_hom_id_assoc]⟩
  obtain ⟨hR', h0'⟩ := isZero_and_isIso_of_isPullback H hdimF hR h0
  have hR'' : IsZero (((Scheme.Modules.pushforward sm₁).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback fX' (ContractionUniquenessComplete.closedPoint A)).ringCatSheaf)) := by
    let := HasDerivedCategory.standard
      (pullback fX' (ContractionUniquenessComplete.closedPoint A)).Modules
    let := HasDerivedCategory.standard
      (pullback fY₁' (ContractionUniquenessComplete.closedPoint A)).Modules
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (Scheme.Modules.pushforward sm₁)
      (m := (1 : ℤ)) (n := 1) rfl _).1 hR'
  -- the identification of the closed fibres of `Y₁` and `Y₂`
  set φ' : pullback fY₁' (ContractionUniquenessComplete.closedPoint A) ≅
      pullback fY₂' (ContractionUniquenessComplete.closedPoint A) :=
    sq₁.isoPullback.symm ≪≫ (𝒯).mapIso φ ≪≫ sq₂.isoPullback
  have hφ' : φ'.hom ≫ pullback.snd fY₂' (ContractionUniquenessComplete.closedPoint A) =
      pullback.snd fY₁' (ContractionUniquenessComplete.closedPoint A) := by
    show (sq₁.isoPullback.inv ≫ (𝒯).map φ.hom ≫ sq₂.isoPullback.hom) ≫ _ = _
    rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd,
      ← Category.assoc ((𝒯).map φ.hom), ← Functor.map_comp, hφ, Iso.inv_comp_eq,
      IsPullback.isoPullback_hom_snd]
  have hφc' : sm₁ ≫ φ'.hom = specialMap fX' fY₂' ((𝒯).map γ₂) hγ₂b := by
    show sm₁ ≫ sq₁.isoPullback.inv ≫ (𝒯).map φ.hom ≫ sq₂.isoPullback.hom = _
    rw [← cancel_epi sqX.isoPullback.hom, hθ₂, ← Category.assoc, hθ₁, Category.assoc,
      Iso.hom_inv_id_assoc, ← Category.assoc ((𝒯).map a₁), ← Functor.map_comp, hφa]
  -- the scheme case
  obtain ⟨ψ', hψ'b, hψ'c, hψ'f⟩ := exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds
    (Λ := A) inferInstance fX' fY₁' fY₂' ((𝒯).map γ₁) hγ₁b ((𝒯).map γ₂) hγ₂b φ' hφ' hφc' h0' hR''
  -- back to algebraic spaces
  set Ψ : siteObject B (Spec (.of A)) hS hY₁' fY₁' ≅ siteObject B (Spec (.of A)) hS hY₂' fY₂' :=
    Over.isoMk (ObjectProperty.isoMk _ ψ') (ObjectProperty.hom_ext _ hψ'b)
  have hΨ : ∀ {F : BigFppfOver B (Spec (.of A)) hS}
      (u : F ⟶ siteObject B (Spec (.of A)) hS hY₁' fY₁')
      (v : F ⟶ siteObject B (Spec (.of A)) hS hY₂' fY₂'), (𝒯).map u ≫ ψ'.hom = (𝒯).map v →
      u ≫ Ψ.hom = v := by
    intro F u v h
    exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ h)
  refine ⟨e₁ ≪≫ yoneda.mapIso Ψ ≪≫ e₂.symm,
    (isTerminal_yoneda_obj_base B _ hS).hom_ext _ _, ?_, ?_⟩
  · have h := hΨ γ₁ γ₂ hψ'c
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ← hγ₁, Category.assoc, ← Category.assoc (yoneda.map γ₁),
      ← Functor.map_comp, h, ← Category.assoc, hγ₂, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · have h : j₁ ≫ Ψ.hom = φ.hom ≫ j₂ := by
      refine hΨ _ _ ?_
      rw [Functor.map_comp, ← IsPullback.isoPullback_hom_fst sq₁, Category.assoc, hψ'f,
        ← IsPullback.isoPullback_hom_fst sq₂]
      show sq₁.isoPullback.hom ≫ (sq₁.isoPullback.inv ≫ (𝒯).map φ.hom ≫
        sq₂.isoPullback.hom) ≫ _ = _
      rw [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc]
    have hi₂' : i₂ = yoneda.map j₂ ≫ e₂.inv := by rw [hj₂, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ← hj₁, ← Category.assoc, ← Functor.map_comp, h, Functor.map_comp,
      Category.assoc, hi₂']

open Stacks.AlgebraicGeometry.TopDegreeBaseChange ContractionUniquenessComplete in
/-- **The complete Noetherian local case of [Stacks, Tag 0E89] for algebraic spaces**, with no
further input:
`AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isAdicComplete_of_isAlgebraicSpace` with
the algebraization of morphisms of algebraic spaces, the statement of [Stacks, Tag 0A4Z], supplied
by `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq`. -/
theorem exists_iso_of_closedFibre_of_isAdicComplete_of_isAlgebraicSpace_holds
    {X Y₁ Y₂ : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (hY₁ : IsAlgebraicSpace B (Spec (.of A)) hS Y₁)
    (hY₂ : IsAlgebraicSpace B (Spec (.of A)) hS Y₂)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (g₁ : Y₁ ⟶ yoneda.obj (baseObject A B hS))
    (g₂ : Y₂ ⟶ yoneda.obj (baseObject A B hS))
    (hpX : IsProper B (Spec (.of A)) hS fX) (hp₁ : IsProper B (Spec (.of A)) hS g₁)
    (hp₂ : IsProper B (Spec (.of A)) hS g₂)
    (hfX : IsFlat B (Spec (.of A)) hS fX) (hf₁ : IsFlat B (Spec (.of A)) hS g₁)
    (hf₂ : IsFlat B (Spec (.of A)) hS g₂)
    (hdX : dimension B (Spec (.of A)) hS
      (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hX fX 0) ≤ 1)
    (hd₁ : dimension B (Spec (.of A)) hS
      (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) g₁ 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hY₁ g₁ 0) ≤ 1)
    (hd₂ : dimension B (Spec (.of A)) hS
      (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) g₂ 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hY₂ g₂ 0) ≤ 1)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂)
    {K : BigFppfOver B (Spec (.of A)) hS} (k : K ⟶ baseObject A B hS)
    (ι : Spec (.of (ResidueField A)) ≅ (𝒯).obj K)
    (hι : ι.hom ≫ (𝒯).map k = ContractionUniquenessComplete.closedPoint A)
    {FX F₁ F₂ : BigFppfOver B (Spec (.of A)) hS} (tX : FX ⟶ K) (t₁ : F₁ ⟶ K) (t₂ : F₂ ⟶ K)
    (iX : yoneda.obj FX ⟶ X) (i₁ : yoneda.obj F₁ ⟶ Y₁) (i₂ : yoneda.obj F₂ ⟶ Y₂)
    (hiX : IsPullback iX (yoneda.map tX) fX (yoneda.map k))
    (hi₁ : IsPullback i₁ (yoneda.map t₁) g₁ (yoneda.map k))
    (hi₂ : IsPullback i₂ (yoneda.map t₂) g₂ (yoneda.map k))
    (a₁ : FX ⟶ F₁) (a₂ : FX ⟶ F₂) (ha₁ : a₁ ≫ t₁ = tX) (ha₂ : a₂ ≫ t₂ = tX)
    (hia₁ : iX ≫ c₁ = yoneda.map a₁ ≫ i₁) (hia₂ : iX ≫ c₂ = yoneda.map a₂ ≫ i₂)
    (φ : F₁ ≅ F₂) (hφ : φ.hom ≫ t₂ = t₁) (hφa : a₁ ≫ φ.hom = a₂)
    (hdimF : ∀ y, topologicalKrullDim (((𝒯).map a₁).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁))) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ g₂ = g₁ ∧ c₁ ≫ ψ.hom = c₂ ∧ i₁ ≫ ψ.hom = yoneda.map φ.hom ≫ i₂ :=
  exists_iso_of_closedFibre_of_isAdicComplete_of_isAlgebraicSpace A B hS
    (fun hX hY fX fY hpX hsY hfY g hg hgc =>
      existsUnique_adicFibreMap_eq A (maximalIdeal A) B hS (contains_adicThickening A _ B hS)
        hX hY fX fY hpX hsY hfY g hg hgc)
    hX hY₁ hY₂ fX g₁ g₂ hpX hp₁ hp₂ hfX hf₁ hf₂ hdX hd₁ hd₂ c₁ c₂ k ι hι tX t₁ t₂ iX i₁ i₂
    hiX hi₁ hi₂ a₁ a₂ ha₁ ha₂ hia₁ hia₂ φ hφ hφa hdimF h0 hR

end AlgebraicGeometry.Space

end
