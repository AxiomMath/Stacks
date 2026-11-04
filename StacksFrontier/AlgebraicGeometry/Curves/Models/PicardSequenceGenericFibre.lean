module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.GorensteinGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentProperCurve
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
public import StacksFrontier.AlgebraicGeometry.Models.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Decomposition
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppGenericFibre

/-!
# The generic fibre of a regular model is the complement of the special fibre

Let `X ⟶ Spec(R)` be a regular model of a smooth curve `C` over the fraction field of a discrete
valuation ring with uniformizer `π`. The morphism `C ⟶ X` identifying `C` with the generic fibre
is an open immersion, its image is the basic open of the global function that `π` cuts out on
`X`, and that basic open is exactly the complement of the support of the special fibre. This is
the geometric input of the Picard sequence of [Stacks, Tag 0C63]: the two groups `Pic(X)` and
`Pic(C)` are the Picard groups of a scheme and of an open subscheme of it whose closed complement
is the special fibre.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.uniformizerGlobalSection` — the global function on
  `X` cut out by the chosen uniformizer.

## Main results

* `Stacks.Models.RegularModelSituation.isOpenImmersion_genericFiberToModel` — the generic-fibre
  inclusion `C ⟶ X` is an open immersion.
* `Stacks.Models.RegularModelSituation.isIntegral_X` — the total space of a regular model is
  integral.
* `Stacks.Models.RegularProperModelSituation.isNoetherian_X` — the total space of a regular
  proper model is a Noetherian scheme.
* `Stacks.Models.RegularModelSituation.range_genericFiberToModel` — the image of the generic
  fibre is the basic open of the uniformizer.
* `Stacks.Models.RegularModelSituation.coe_support_specialFiberIdeal_eq_compl_basicOpen` — the
  support of the special fibre is the complement of that basic open.
* `Stacks.Models.RegularModelSituation.notMem_supportSet_specialFiberIdeal` — no point of the
  generic fibre lies on the special fibre.
* `Stacks.Models.RegularProperModelSituation.finite_irreducibleComponents_specialFiber` — the
  special fibre has finitely many irreducible components, so the free abelian group on them is
  the group `ℤ^{⊕n}` of [Stacks, Tag 0C63].
* `Stacks.Models.RegularProperModelSituation.exists_specialFiberIdeal_eq_prod` — the
  decomposition `X_k = Σ mᵢ Cᵢ` of the special fibre into its irreducible components, which the
  standing situation of [Stacks, Tag 0C61] opens by writing down.

## Implementation notes

**Where the open immersion comes from.** `Stacks.Models.genericFiberSpec_isOpenImmersion` says
that `Spec(K) ⟶ Spec(R)` is an open immersion, because `K` is the localization of `R` away from a
uniformizer; open immersions are stable under base change, so the projection
`X ×_{Spec R} Spec(K) ⟶ X` is one, and `C ⟶ X` is that projection precomposed with the
identification carried by the situation.

**Which complement.** The image of `Spec(K) ⟶ Spec(R)` is the basic open `D(π)`, by the
description `PrimeSpectrum.localization_away_comap_range` of the spectrum of a localization away
from an element, and the image of `Spec(k) ⟶ Spec(R)` is its closed complement `V(π)`, because
`R ⟶ k` is surjective with kernel `(π)`. Pulling both back along `X ⟶ Spec(R)` gives the two
statements about `X`, the support of the special fibre being the range of `X_k ⟶ X` by
`Stacks.Models.RegularModelSituation.coe_support_specialFiberIdeal`.

**Why the components are finitely many.** The special fibre is locally of finite type over the
residue field and quasi-compact, both by base change from `X ⟶ Spec(R)`, hence a Noetherian
scheme; and a Noetherian topological space has finitely many irreducible components.

## References

* [Stacks Project, Tag 0C63](https://stacks.math.columbia.edu/tag/0C63)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 0BCP](https://stacks.math.columbia.edu/tag/0BCP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Models

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-! ### The generic fibre is an open subscheme -/

/-- **The generic-fibre inclusion of a regular model is an open immersion.** The fraction field
of a discrete valuation ring is a localization away from a uniformizer, so `Spec(K) ⟶ Spec(R)` is
an open immersion; open immersions are stable under base change, and the identification of `C`
with the generic fibre is an isomorphism. -/
theorem isOpenImmersion_genericFiberToModel : IsOpenImmersion S.genericFiberToModel := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) :=
    Stacks.Models.genericFiberSpec_isOpenImmersion
  show IsOpenImmersion (S.genericFiberIso.hom ≫ pullback.fst S.X_to_R
    (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))))
  infer_instance

/-- **The total space of a regular model is integral**: it is flat over the integral scheme
`Spec(R)` and its fibre over the generic point is the integral scheme `C`, which is
[Stacks, Tag 0BCM]. -/
theorem isIntegral_X : IsIntegral S.X := by
  have : IsIntegral (S.X_to_R.fiber (genericPoint (Spec (.of S.R)))) :=
    S.isIntegral_fiber_genericPoint
  exact AlgebraicGeometry.isIntegral_of_flat_of_isIntegral_genericFiber S.X_to_R

/-- The range of the generic-fibre inclusion is the range of the projection from the fibre
product, the identification of `C` with the generic fibre being an isomorphism. -/
theorem range_genericFiberToModel_eq_range_pullbackFst :
    Set.range S.genericFiberToModel.base =
      Set.range (pullback.fst S.X_to_R
        (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))).base := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨S.genericFiberIso.hom.base c, ?_⟩
    simpa only [genericFiberToModel] using
      (Scheme.Hom.comp_apply S.genericFiberIso.hom
        (pullback.fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))) c).symm
  · rintro ⟨y, rfl⟩
    exact ⟨S.genericFiberIso.inv.base y, by simp [genericFiberToModel]⟩

/-- The composite `C ⟶ X ⟶ Spec(R)` is the structure morphism of `C` followed by
`Spec(K) ⟶ Spec(R)`. -/
theorem genericFiberToModel_comp :
    S.genericFiberToModel ≫ S.X_to_R =
      S.C_to_K ≫ Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) := by
  simp only [genericFiberToModel, Category.assoc, pullback.condition]
  rw [← Category.assoc, S.genericFiberIso_over_K]

/-! ### The uniformizer as a global function, and the two complementary loci -/

/-- **The uniformizer read as a global function on the total space of a model.** -/
abbrev uniformizerGlobalSection (π : S.R) : Γ(S.X, (⊤ : S.X.Opens)) :=
  S.X_to_R.appTop ((Scheme.ΓSpecIso (.of S.R)).inv π)

/-- The ring map cutting out functions on the whole space from the base ring is the canonical
one through global sections. -/
theorem chartHom_top : chartHom S.X_to_R (⊤ : S.X.Opens) =
    (Scheme.ΓSpecIso (.of S.R)).inv ≫ S.X_to_R.appTop := by
  dsimp only [chartHom]
  congr 1
  exact Scheme.Hom.appLE_eq_app (U := (⊤ : (Spec (.of S.R)).Opens)) S.X_to_R

/-- The global function cut out on the whole space by an element of the base ring is the one
`Stacks.Models.chartHom` cuts out there. -/
theorem chartHom_top_apply (r : S.R) :
    (chartHom S.X_to_R (⊤ : S.X.Opens)).hom r = S.uniformizerGlobalSection r := by
  rw [S.chartHom_top]
  rfl

/-- A point of the model lies on the basic open of a base-ring element exactly when its image
lies on the corresponding basic open of `Spec(R)`. -/
theorem coe_basicOpen_uniformizerGlobalSection (r : S.R) :
    (S.X.basicOpen (S.uniformizerGlobalSection r) : Set S.X) =
      S.X_to_R.base ⁻¹'
        (((Spec (.of S.R)).basicOpen ((Scheme.ΓSpecIso (.of S.R)).inv r) :
          (Spec (.of S.R)).Opens) : Set ↥(Spec (.of S.R))) := by
  rw [← Scheme.preimage_basicOpen_top]
  rfl

/-- **The basic open of a uniformizer in `Spec(R)` is the image of `Spec(K)`**, because `K` is
the localization of `R` away from the uniformizer. -/
theorem coe_basicOpen_spec_eq_range {π : S.R} (hπ : Irreducible π) :
    (((Spec (.of S.R)).basicOpen ((Scheme.ΓSpecIso (.of S.R)).inv π) :
        (Spec (.of S.R)).Opens) : Set ↥(Spec (.of S.R))) =
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))).base := by
  have : IsLocalization.Away π S.K :=
    Stacks.EppTheorem.isLocalization_away_of_irreducible S.R S.K hπ
  rw [basicOpen_eq_of_affine (R := CommRingCat.of S.R) (f := π)]
  exact (PrimeSpectrum.localization_away_comap_range S.K π).symm

/-- **The complement of the basic open of a uniformizer in `Spec(R)` is the image of
`Spec(k)`**, because `R ⟶ k` is surjective with kernel the ideal generated by the
uniformizer. -/
theorem compl_coe_basicOpen_spec_eq_range {π : S.R} (hπ : Irreducible π) :
    (((Spec (.of S.R)).basicOpen ((Scheme.ΓSpecIso (.of S.R)).inv π) :
        (Spec (.of S.R)).Opens) : Set ↥(Spec (.of S.R)))ᶜ =
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))).base := by
  have hmap : algebraMap S.R S.k =
      S.residueEquiv.toRingHom.comp (IsLocalRing.residue S.R) :=
    RingHom.ext fun r => (S.residueEquiv.commutes r).symm
  have hker : RingHom.ker (algebraMap S.R S.k) = Ideal.span {π} := by
    rw [hmap, RingHom.ker_equiv_comp, IsLocalRing.ker_residue, hπ.maximalIdeal_eq]
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap S.R S.k)) =
      (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum S.R))ᶜ := by
    rw [range_comap_of_surjective _ _ S.surjective_algebraMap_residueField, hker,
      PrimeSpectrum.zeroLocus_span, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl]
  rw [basicOpen_eq_of_affine (R := CommRingCat.of S.R) (f := π)]
  exact hrange.symm

/-- **The image of the generic fibre is the basic open of a uniformizer.** The image of
`Spec(K) ⟶ Spec(R)` is `D(π)`, because `K` is the localization of `R` away from `π`, and the
range of a projection from a fibre product of schemes is the preimage of the range. -/
theorem range_genericFiberToModel {π : S.R} (hπ : Irreducible π) :
    Set.range S.genericFiberToModel.base =
      (S.X.basicOpen (S.uniformizerGlobalSection π) : Set S.X) := by
  rw [S.range_genericFiberToModel_eq_range_pullbackFst, Scheme.Pullback.range_fst,
    S.coe_basicOpen_uniformizerGlobalSection π, S.coe_basicOpen_spec_eq_range hπ]

/-- **The support of the special fibre is the complement of the basic open of a uniformizer.**
The image of `Spec(k) ⟶ Spec(R)` is the closed set `V(π)`; the support of the special fibre is
the closure of its preimage, and a closed immersion has closed range. -/
theorem coe_support_specialFiberIdeal_eq_compl_basicOpen {π : S.R} (hπ : Irreducible π) :
    (S.specialFiberIdeal.support : Set S.X) =
      (S.X.basicOpen (S.uniformizerGlobalSection π) : Set S.X)ᶜ := by
  rw [S.coe_support_specialFiberIdeal, Scheme.Pullback.range_fst,
    S.coe_basicOpen_uniformizerGlobalSection π, ← Set.preimage_compl,
    S.compl_coe_basicOpen_spec_eq_range hπ]

/-- **No point of the generic fibre lies on the special fibre**: the two loci are complementary
open and closed subsets of `X`. -/
theorem notMem_supportSet_specialFiberIdeal (c : S.C) :
    S.genericFiberToModel.base c ∉ S.specialFiberIdeal.supportSet := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S.R
  intro hc
  have hc' : S.genericFiberToModel.base c ∈ (S.specialFiberIdeal.support : Set S.X) := hc
  rw [S.coe_support_specialFiberIdeal_eq_compl_basicOpen hπ] at hc'
  exact hc' ((S.range_genericFiberToModel hπ) ▸ Set.mem_range_self c)

end RegularModelSituation

/-! ### Noetherianness, the finitely many components, and the decomposition of `X_k` -/

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The total space of a regular proper model is a Noetherian scheme**: it is locally
Noetherian because it is regular, and quasi-compact because it is proper over the quasi-compact
scheme `Spec(R)`. -/
theorem isNoetherian_X : IsNoetherian S.X :=
  have : IsLocallyNoetherian S.X := S.isLocallyNoetherian_X
  have : CompactSpace S.X := QuasiCompact.compactSpace_of_compactSpace S.X_to_R
  ⟨⟩

/-- **The special fibre of a regular proper model is a Noetherian scheme**: it is locally of
finite type and quasi-compact over the residue field, both by base change from the structure
morphism of the model. -/
theorem isNoetherian_specialFiber : IsNoetherian S.specialFiber :=
  have : IsLocallyNoetherian S.specialFiber :=
    LocallyOfFiniteType.isLocallyNoetherian S.specialFiberToSpec
  have : CompactSpace S.specialFiber :=
    QuasiCompact.compactSpace_of_compactSpace S.specialFiberToSpec
  ⟨⟩

/-- **The special fibre of a regular proper model has finitely many irreducible components**, it
being a Noetherian scheme. This is what makes the free abelian group on the components of `X_k`
the group `ℤ^{⊕n}` of the Picard sequence of [Stacks, Tag 0C63]. -/
theorem finite_irreducibleComponents_specialFiber :
    (irreducibleComponents S.specialFiber).Finite :=
  have : IsNoetherian S.specialFiber := S.isNoetherian_specialFiber
  NoetherianSpace.finite_irreducibleComponents

/-- **Every point of the special fibre lies on one of its irreducible components**, read on the
supports of the corresponding ideal sheaves of the model. -/
theorem exists_mem_supportSet_specialFiberComponentIdeal {x : S.X}
    (hx : x ∈ S.specialFiberIdeal.supportSet) :
    ∃ Z, x ∈ (S.toRegularModelSituation.specialFiberComponentIdeal Z).supportSet := by
  have hx' : x ∈ (S.specialFiberIdeal.support : Set S.X) := hx
  rw [S.coe_support_specialFiberIdeal] at hx'
  obtain ⟨y, rfl⟩ := hx'
  refine ⟨⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩, ?_⟩
  show S.specialFiberι.base y ∈
    ((S.toRegularModelSituation.specialFiberComponentIdeal _).support : Set S.X)
  rw [S.toRegularModelSituation.coe_support_specialFiberComponentIdeal]
  exact ⟨y, mem_irreducibleComponent, rfl⟩

/-- **Stacks Project, Tag 0C61.** The decomposition `X_k = Σ mᵢ Cᵢ` of the special fibre of a
regular proper model as a nonnegative combination of its irreducible components, each taken with
its reduced induced structure: the special fibre is an effective Cartier divisor whose support is
covered by the components, which are integral effective Cartier divisors by [Stacks, Tag 0C5Z],
so [Stacks, Tag 0BCP] writes it as a product of their powers. -/
theorem exists_specialFiberIdeal_eq_prod :
    ∃ m : irreducibleComponents S.specialFiber →₀ ℕ,
      S.specialFiberIdeal =
        m.prod fun Z n => S.toRegularModelSituation.specialFiberComponentIdeal Z ^ n := by
  have : IsNoetherian S.X := S.isNoetherian_X
  exact AlgebraicGeometry.exists_finsupp_eq_prod_of_support_cover S.specialFiberIdeal
    inferInstance (S.toRegularModelSituation.specialFiberComponentIdeal)
    (fun Z => ⟨inferInstance, S.isEffectiveCartierDivisor_specialFiberComponent Z⟩)
    fun _ hx => S.exists_mem_supportSet_specialFiberComponentIdeal hx

end RegularProperModelSituation

end Stacks.Models

end
