module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineCartesianBaseChange
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization

/-!
# The fpqc covering of `Spec A` by the henselization of a pair and the complement of `V(I)`

Let `A ⟶ Aʰ` be the henselization of a pair `(A, I)`. The morphism `Spec Aʰ ⟶ Spec A` is flat
but not surjective — its image is the closed set `V(I)` — so it is not by itself an fpqc covering
of `Spec A`; it becomes one, for `I` finitely generated, after adding the open complement
`Spec A ∖ V(I)` as a second member. The two-member family is read as the single morphism out of
the coproduct of its members, whose flatness, surjectivity and quasi-compactness are proved for
arbitrary morphisms out of a binary coproduct.

## Main results

* `AlgebraicGeometry.flat_coprod_desc`, `AlgebraicGeometry.surjective_coprod_desc`,
  `AlgebraicGeometry.quasiCompact_coprod_desc`: **flatness, surjectivity and quasi-compactness
  of `coprod.desc g₁ g₂`**, for arbitrary morphisms `g₁ : Y₁ ⟶ S` and `g₂ : Y₂ ⟶ S` to a common
  base. Surjectivity asks only that the two ranges cover `S`.
* `AlgebraicGeometry.flat_specMap_algebraMap_henselization`: **the morphism of spectra induced by
  the henselization of a pair is flat**, the scheme-level form of the ring-level flatness in Tag
  0AGU.
* `AlgebraicGeometry.singleton_coprod_desc_specMap_mem_fpqcPrecoverage`: **the two-member family
  `{Spec Aʰ ⟶ Spec A, Spec A ∖ V(I) ⟶ Spec A}` is an fpqc covering**, read as the single
  morphism out of the coproduct of its two members.

## Implementation notes

The index of a two-member family is `PUnit ⊕ PUnit` rather than `Fin 2`, because that is the
index of `AlgebraicGeometry.coprodOpenCover`, through which flatness — Zariski local at the
source — passes from the two members to the morphism out of the coproduct.

Flatness of `Spec Aʰ ⟶ Spec A` is read off the flatness of `Aʰ` as an `A`-module by
`Stacks.AffineCartesianBaseChange.flat_specMap_algebraMap`, which states exactly that for an
arbitrary flat algebra.

Joint surjectivity is where the arithmetic of the henselization enters: the image of
`Spec Aʰ ⟶ Spec A` contains `V(I)` because `A / I ⟶ Aʰ / IAʰ` is an isomorphism, which is the
second half of Tag 0AGU. Quasi-compactness of the second member needs `I` to be finitely
generated; `Spec A ∖ V(I)` is a quasi-compact open exactly then.

The open complement is passed as a binder `U` together with the equation `hU` naming its
underlying set, rather than constructed in the statement, so that no transport of the opens
appears in the statement.

## References

* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace

section Coprod

variable {S Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ S) (g₂ : Y₂ ⟶ S)

/-- A property of morphisms which is Zariski local at the source holds for `coprod.desc g₁ g₂`
as soon as it holds for `g₁` and for `g₂`: the two coprojections are an open cover of the
coproduct. -/
theorem IsZariskiLocalAtSource.coprodDesc {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] (h₁ : P g₁) (h₂ : P g₂) : P (coprod.desc g₁ g₂) := by
  refine IsZariskiLocalAtSource.of_openCover (coprodOpenCover.{_, 0} Y₁ Y₂) ?_
  rintro (⟨⟩ | ⟨⟩)
  · show P (coprod.inl ≫ coprod.desc g₁ g₂)
    rwa [coprod.inl_desc]
  · show P (coprod.inr ≫ coprod.desc g₁ g₂)
    rwa [coprod.inr_desc]

/-- **The morphism out of a binary coproduct described by two flat morphisms is flat.** -/
instance flat_coprod_desc [Flat g₁] [Flat g₂] : Flat (coprod.desc g₁ g₂) := by
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  exact IsZariskiLocalAtSource.coprodDesc g₁ g₂ ‹Flat g₁› ‹Flat g₂›

/-- `coprod.desc g₁ g₂` restricts to `g₁` along the first coprojection, on points. -/
private theorem coprod_desc_inl_apply (y : Y₁) :
    coprod.desc g₁ g₂ ((coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) y) = g₁ y := by
  rw [← Scheme.Hom.comp_apply, coprod.inl_desc]

/-- `coprod.desc g₁ g₂` restricts to `g₂` along the second coprojection, on points. -/
private theorem coprod_desc_inr_apply (y : Y₂) :
    coprod.desc g₁ g₂ ((coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂) y) = g₂ y := by
  rw [← Scheme.Hom.comp_apply, coprod.inr_desc]

/-- **The morphism out of a binary coproduct described by two jointly surjective morphisms is
surjective.** -/
theorem surjective_coprod_desc (h : Set.range g₁ ∪ Set.range g₂ = Set.univ) :
    Surjective (coprod.desc g₁ g₂) := by
  refine ⟨fun s ↦ ?_⟩
  have hs : s ∈ Set.range g₁ ∪ Set.range g₂ := h ▸ Set.mem_univ s
  obtain (⟨y, hy⟩ | ⟨y, hy⟩) := hs
  · exact ⟨(coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) y, (coprod_desc_inl_apply g₁ g₂ y).trans hy⟩
  · exact ⟨(coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂) y, (coprod_desc_inr_apply g₁ g₂ y).trans hy⟩

/-- The preimage of a subset of the base under `coprod.desc g₁ g₂` is the union of the images,
under the two coprojections, of the two preimages. -/
theorem preimage_coprod_desc (U : Set S) :
    coprod.desc g₁ g₂ ⁻¹' U =
      (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) '' (g₁ ⁻¹' U) ∪
        (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂) '' (g₂ ⁻¹' U) := by
  have e₁ : (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) ⁻¹' (coprod.desc g₁ g₂ ⁻¹' U) = g₁ ⁻¹' U := by
    ext y
    simp [coprod_desc_inl_apply]
  have e₂ : (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂) ⁻¹' (coprod.desc g₁ g₂ ⁻¹' U) = g₂ ⁻¹' U := by
    ext y
    simp [coprod_desc_inr_apply]
  have hcov : Set.range (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) ∪
      Set.range (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂) = Set.univ := by
    simpa using (isCompl_range_inl_inr Y₁ Y₂).sup_eq_top
  rw [← e₁, ← e₂, Set.image_preimage_eq_inter_range, Set.image_preimage_eq_inter_range,
    ← Set.inter_union_distrib_left, hcov, Set.inter_univ]

/-- **The morphism out of a binary coproduct described by two quasi-compact morphisms is
quasi-compact.** -/
instance quasiCompact_coprod_desc [QuasiCompact g₁] [QuasiCompact g₂] :
    QuasiCompact (coprod.desc g₁ g₂) := by
  refine ⟨fun U hU hU' ↦ ?_⟩
  rw [preimage_coprod_desc g₁ g₂ U]
  exact ((QuasiCompact.isCompact_preimage (f := g₁) U hU hU').image
      (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂).continuous).union
    ((QuasiCompact.isCompact_preimage (f := g₂) U hU hU').image
      (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂).continuous)

end Coprod

section Henselization

variable {A Ah : Type u} [CommRing A] [CommRing Ah]

/-- Bijectivity of the induced map on quotients only depends on the ideal, not on the name it is
given. -/
theorem bijective_quotientMap_congr (f : A →+* Ah) {I J : Ideal A} (h : I = J)
    (hq : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap (J.map f) f Ideal.le_comap_map) := by
  subst h
  exact hq

/-- If `A / I ⟶ Ah / IAh` is bijective then the image of `Spec Ah ⟶ Spec A` contains `V(I)`. -/
theorem zeroLocus_subset_range_comap_of_bijective_quotientMap (f : A →+* Ah) (I : Ideal A)
    (hq : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) :
    PrimeSpectrum.zeroLocus (I : Set A) ⊆ Set.range (PrimeSpectrum.comap f) := by
  intro p hp
  have hrI : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  obtain ⟨p', hp'⟩ := hrI.ge hp
  have hrq : Set.range (PrimeSpectrum.comap
      (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) = Set.univ := by
    rw [_root_.range_comap_of_surjective _ _ hq.surjective,
      (RingHom.injective_iff_ker_eq_bot _).mp hq.injective, PrimeSpectrum.zeroLocus_bot]
  obtain ⟨q', hq'⟩ := hrq.ge (Set.mem_univ p')
  have hsq : (Ideal.Quotient.mk (I.map f)).comp f
      = (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).comp (Ideal.Quotient.mk I) :=
    (Ideal.quotientMap_comp_mk Ideal.le_comap_map).symm
  refine ⟨PrimeSpectrum.comap (Ideal.Quotient.mk (I.map f)) q', ?_⟩
  calc PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk (I.map f)) q')
      = PrimeSpectrum.comap ((Ideal.Quotient.mk (I.map f)).comp f) q' := rfl
    _ = PrimeSpectrum.comap
          ((Ideal.quotientMap (I.map f) f Ideal.le_comap_map).comp (Ideal.Quotient.mk I)) q' := by
        rw [hsq]
    _ = PrimeSpectrum.comap (Ideal.Quotient.mk I)
          (PrimeSpectrum.comap (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) q') := rfl
    _ = PrimeSpectrum.comap (Ideal.Quotient.mk I) p' := by rw [hq']
    _ = p := hp'

/-- **The two members `Spec Ah ⟶ Spec A` and `Spec A ∖ V(I) ⟶ Spec A` are jointly surjective**,
as soon as `A / I ⟶ Ah / IAh` is bijective. -/
theorem surjective_coprod_desc_specMap (f : A →+* Ah) (I : Ideal A)
    (hq : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (U : (Spec (CommRingCat.of A)).Opens)
    (hU : (U : Set ↥(Spec (CommRingCat.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ) :
    Surjective (coprod.desc (Spec.map (CommRingCat.ofHom f)) U.ι) := by
  refine surjective_coprod_desc _ _ (Set.eq_univ_of_forall fun p ↦ ?_)
  by_cases hp : p ∈ PrimeSpectrum.zeroLocus (I : Set A)
  · exact Or.inl (show p ∈ Set.range (PrimeSpectrum.comap f) from
      zeroLocus_subset_range_comap_of_bijective_quotientMap f I hq hp)
  · refine Or.inr ?_
    rwa [Scheme.Opens.range_ι, hU]

/-- **The two-member family `{Spec Ah ⟶ Spec A, Spec A ∖ V(I) ⟶ Spec A}` is an fpqc covering**,
read as the single morphism out of the coproduct of its two members, for `Ah` a flat `A`-algebra
with `A / I ⟶ Ah / IAh` bijective and `I` finitely generated. -/
theorem singleton_coprod_desc_specMap_mem_fpqcPrecoverage [Algebra A Ah] (I : Ideal A)
    (hflat : Module.Flat A Ah)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A Ah)) (algebraMap A Ah) Ideal.le_comap_map))
    (hI : I.FG) (U : (Spec (CommRingCat.of A)).Opens)
    (hU : (U : Set ↥(Spec (CommRingCat.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ) :
    Presieve.singleton (coprod.desc (Spec.map (CommRingCat.ofHom (algebraMap A Ah))) U.ι)
      ∈ Scheme.fpqcPrecoverage (Spec (CommRingCat.of A)) := by
  have _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap A Ah))) :=
    have := hflat
    Stacks.AffineCartesianBaseChange.flat_specMap_algebraMap A Ah
  have hcpt : IsCompact (U : Set ↥(Spec (CommRingCat.of A))) := by
    rw [hU]
    exact (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨I, hI, rfl⟩).1
  have _ : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hcpt
  have _ : Surjective (coprod.desc (Spec.map (CommRingCat.ofHom (algebraMap A Ah))) U.ι) :=
    surjective_coprod_desc_specMap _ I hq U hU
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

/-! ### The closed fibre is unchanged -/

/-- **The closed fibre of `Spec Ah ⟶ Spec A` is the closed fibre of `Spec A`**, as soon as
`A / I ⟶ Ah / IAh` is bijective: the isomorphism `Spec (Ah / IAh) ≅ Spec (A / I)` it induces
sits in the commuting square identifying `V(IAh) ⊆ Spec Ah` with `V(I) ⊆ Spec A`. -/
theorem exists_isIso_specMap_quotientMk_of_bijective_quotientMap (f : A →+* Ah) (I : Ideal A)
    (hq : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) :
    ∃ e : Spec (CommRingCat.of (Ah ⧸ I.map f)) ≅ Spec (CommRingCat.of (A ⧸ I)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))) ≫
          Spec.map (CommRingCat.ofHom f) := by
  let q : CommRingCat.of (A ⧸ I) ⟶ CommRingCat.of (Ah ⧸ I.map f) :=
    CommRingCat.ofHom (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)
  have _ : IsIso q := (ConcreteCategory.isIso_iff_bijective q).mpr hq
  refine ⟨asIso (Spec.map q), ?_⟩
  show Spec.map q ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    Ideal.quotientMap_comp_mk Ideal.le_comap_map]

end Henselization

section HenselizationPair

/-- **The morphism of spectra induced by the henselization of a pair is flat.** This is the
scheme-level form of the flatness half of
[Stacks, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU), whose statement there is
ring-level. -/
theorem flat_specMap_algebraMap_henselization (A : Type u) [CommRing A] (I : Ideal A)
    (Ah : Type u) [CommRing Ah] [Algebra A Ah]
    (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
    (hι : ∀ (B : Type u) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : A →+* B, I ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap A Ah))) :=
  have := (flat_henselization_and_bijective_quotientMap A I Ah hh hι).1
  Stacks.AffineCartesianBaseChange.flat_specMap_algebraMap A Ah

/-- **`{Spec Aʰ ⟶ Spec A, Spec A ∖ V(I) ⟶ Spec A}` is an fpqc covering of `Spec A`**, for `Aʰ`
the henselization of the pair `(A, I)` and `I` finitely generated. -/
theorem singleton_coprod_desc_specMap_henselization_mem_fpqcPrecoverage
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (Ah : Type u) [CommRing Ah] [Algebra A Ah]
    (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
    (hι : ∀ (B : Type u) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : A →+* B, I ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g)
    (U : (Spec (CommRingCat.of A)).Opens)
    (hU : (U : Set ↥(Spec (CommRingCat.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ) :
    Presieve.singleton (coprod.desc (Spec.map (CommRingCat.ofHom (algebraMap A Ah))) U.ι)
      ∈ Scheme.fpqcPrecoverage (Spec (CommRingCat.of A)) :=
  have h := flat_henselization_and_bijective_quotientMap A I Ah hh hι
  singleton_coprod_desc_specMap_mem_fpqcPrecoverage I h.1
    (bijective_quotientMap_congr (algebraMap A Ah) (pow_one I) (h.2 1)) hI U hU

end HenselizationPair

end AlgebraicGeometry

end
