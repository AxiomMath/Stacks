module

public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalChart
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Product
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Restriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A common admissible blowup dominating finitely many admissible blowups

Let `X` be a scheme, `U ⊆ X` an open subscheme and `b_i : Y_i ⟶ X`, `i ∈ ι`, a finite family of
`U`-admissible blowups. Then there is a `U`-admissible blowup `b : X' ⟶ X` which factors through
every `b_i`, each factor map `X' ⟶ Y_i` itself being a `b_i⁻¹(U)`-admissible blowup.

The centre of the dominating blowup is the product of the centres: if `Y_i` is the blowup of `X`
in `I_i`, then `X'` is the blowup of `X` in `I = I_1 ⋯ I_n`. A product of finitely many
finite-type ideal sheaves is of finite type and its support is the union of the supports, so the
product is again a legitimate centre; and blowing up a product is the same as blowing up the
factors one after another (Stacks tag 080A), which is what produces the factorization.

## Main results

* `Stacks.Blowup.exists_admissibleBlowup_dominating`: the dominating `U`-admissible blowup, with
  its admissible factorization through each member of the family.

Along the way this file supplies, for the blowup `Stacks.Blowup.blowUp` of
`StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean`, the three geometric inputs of the
universal property that were so far available only for the parallel construction
`AlgebraicGeometry.blowUp` of
`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/BlowUp.lean`:

* `Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData`: Stacks tag 02OS, second
  assertion;
* `Stacks.Blowup.isIso_blowUpToBase_restrict_compl_support_reesData`: Stacks tag 02OS, first
  assertion;
* `Stacks.Blowup.isTerminal_blowUp_reesData`: Stacks tag 0806.

These give `Stacks.Blowup.blowUpOverIso`, the canonical isomorphism over the base between the two
constructions, and hence `Stacks.Blowup.isAdmissibleBlowup_iff`, which says that admissibility may
equally be tested against either one.

No `@[stacks]` attribute is attached to any of those three: tags 02OS and 0806 are already carried
by `Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`,
`AlgebraicGeometry.isIso_blowUp_restrict_compl_support` and `Stacks.Blowup.isTerminal_blowUp`,
which state the same mathematics for `AlgebraicGeometry.blowUp`. What is proved here is that
content for the second construction, which the admissibility predicate happens to be phrased
against; it is a duplication forced by the two parallel models, not a second formalization of the
tags.

## Implementation notes

The statement is more general than the source. Stacks assumes `X` quasi-compact and
quasi-separated and `U` quasi-compact, and indexes the family by `Fin n`; none of that is used.
The construction by a product of ideal sheaves needs no finiteness hypothesis on `X` or on `U`,
and an arbitrary finite index type in its own universe does as well as `Fin n`. The open relative
to which a factor map is admissible is the inverse image `b_i⁻¹(U)` of the original open.

The repository carries **two** constructions of the blowup of a scheme in a quasi-coherent ideal
sheaf, both relative `Proj`s of the Rees algebra but glued from different local data, with
disjoint import closures: `Stacks.Blowup.blowUp`, the relative `Proj` of the family of ordinary
Rees algebras `Γ(X, V)[I(V)t]`, and `AlgebraicGeometry.blowUp`, the relative `Proj` of the Rees
algebra as a quasi-coherent graded sheaf. `Stacks.Blowup.IsAdmissibleBlowup` is phrased in terms
of the former, while Stacks tags 0806, 080A and 0805 — the universal property, blowing up a
product, and flat base change — are available only for the latter. Rather than state the result
about a different notion of admissibility, or duplicate those three tags, the two constructions
are compared once and for all: both are final objects of the category of `X`-schemes on which the
inverse image of the centre is an effective Cartier divisor, so they are canonically isomorphic
over `X`. What this file has to prove for `Stacks.Blowup.blowUp` is that it *is* such a final
object, which needs the two assertions of tag 02OS and the existence of the classifying morphism.
Both halves of tag 02OS are proved from the affine charts of tag 0804 that
`StacksFrontier/AlgebraicGeometry/Blowup/AffineChart.lean` and
`StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalChart.lean` already supply, and the classifying
morphism from the ring-level one of
`StacksFrontier/AlgebraicGeometry/Blowup/Existence.lean` together with the chart square
`Stacks.Blowup.isPullback_blowUpChart`. Everything else — the gluing of the classifying morphism
and the reduction of tag 0806 to its geometric inputs — is already stated for an arbitrary
morphism and applies verbatim.

The helper names carry the suffix `reesData` after `Stacks.Blowup.reesData`, the relative-`Proj`
datum the construction they are about is glued from, because the namespace `Stacks.Blowup`
already holds the homonymous statements for `AlgebraicGeometry.blowUp`.

## References

* [Stacks Project, Tag 080N](https://stacks.math.columbia.edu/tag/080N)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Polynomial

universe u

namespace Stacks.Blowup

/-! ### The exceptional divisor is an effective Cartier divisor -/

/-- **Stacks Project, Tag 02OS, second assertion**, for `Stacks.Blowup.blowUp`. The exceptional
divisor of the blowup of a scheme in a quasi-coherent sheaf of ideals is an effective Cartier
divisor: every point of the blowup lies on one of the affine charts of tag 0804, and
`Stacks.Blowup.exists_span_eq_ideal_exceptionalIdeal_blowUpAffineChart` exhibits the exceptional
ideal there as generated by a single nonzerodivisor.

No attribute is attached: the tag is carried by
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`, which is the same statement for
`AlgebraicGeometry.blowUp`. -/
@[ega "IV 19.4.1", sga "6 XIII 7.1.4" "more general"]
theorem isEffectiveCartierDivisor_exceptionalIdeal_reesData {S : Scheme.{u}}
    (ℐ : S.IdealSheafData) :
    Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Blowup.exceptionalIdeal ℐ) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x ↦ ?_
  obtain ⟨U, hU⟩ := Stacks.Divisors.exists_affineOpens_mem ((Stacks.Blowup.blowUpToBase ℐ).base x)
  have hmem : x ∈ Stacks.Blowup.blowUpToBase ℐ ⁻¹ᵁ (U : S.Opens) := hU
  rw [← iSup_opensRange_blowUpAffineChart ℐ U, TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨r, hr⟩ := hmem
  obtain ⟨t, ht, hspan⟩ := exists_span_eq_ideal_exceptionalIdeal_blowUpAffineChart ℐ U r.2
  refine ⟨_, (isAffineOpen_top _).image_of_isOpenImmersion _, ?_, t,
    isRegular_iff_mem_nonZeroDivisors.mpr ht, hspan⟩
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact hr

/-! ### The blowup is an isomorphism away from its centre -/

section Ring

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A degree-one element of the Rees algebra attached to `r ∈ I` is the one attached to `1 ∈ I`
scaled by `r`. -/
theorem reesDegOne_eq_mul {r : R} (hr : r ∈ I) (h1 : (1 : R) ∈ I) :
    reesDegOne I hr = algebraMap R (reesAlgebra I) r * reesDegOne I h1 := by
  apply Subtype.ext
  show monomial 1 r = (algebraMap R R[X] r) * monomial 1 1
  rw [Polynomial.algebraMap_eq, C_mul_monomial, mul_one]

/-- **The chart at the unit section is the whole `Proj` of the Rees algebra.** When `1 ∈ I` every
standard affine chart `D₊(r⁽¹⁾)`, `r ∈ I`, is contained in `D₊(1⁽¹⁾)`, because `r⁽¹⁾` is a
multiple of `1⁽¹⁾`; and those charts cover. -/
theorem basicOpen_reesDegOne_one_eq_top (h1 : (1 : R) ∈ I) :
    Proj.basicOpen (reesGrading I) (reesDegOne I h1) = ⊤ := by
  rw [eq_top_iff, ← iSup_basicOpen_reesDegOne_eq_top I]
  refine iSup_le fun r x hx ↦ ?_
  rw [Proj.mem_basicOpen] at hx ⊢
  intro hmem
  exact hx (by rw [reesDegOne_eq_mul I r.2 h1]; exact Ideal.mul_mem_left _ _ hmem)

/-- **The affine blowup algebra at the unit section is the base ring.** Its generators `y/1` are
the images of elements of `R`, and a localization away from `1` is faithful. -/
theorem bijective_algebraMap_affineBlowup_one :
    Function.Bijective (algebraMap R (affineBlowup I (1 : R))) := by
  have hM : Submonoid.powers (1 : R) ≤ nonZeroDivisors R := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    simp
  have hinj : Function.Injective (algebraMap R (Localization.Away (1 : R))) :=
    IsLocalization.injective _ hM
  have hval : ∀ x : R, ((algebraMap R (affineBlowup I (1 : R)) x :
      affineBlowup I (1 : R)) : Localization.Away (1 : R)) =
      algebraMap R (Localization.Away (1 : R)) x := fun _ ↦ rfl
  have hle : affineBlowup I (1 : R) ≤ (⊥ : Subalgebra R (Localization.Away (1 : R))) := by
    refine Algebra.adjoin_le ?_
    rintro z ⟨y, -, rfl⟩
    refine Algebra.mem_bot.mpr ⟨y, ?_⟩
    rw [← Localization.mk_one_eq_algebraMap]
    congr 1
  refine ⟨fun p q hpq ↦ hinj ?_, fun z ↦ ?_⟩
  · rw [← hval p, ← hval q, hpq]
  · obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (hle z.2)
    exact ⟨r, Subtype.ext ((hval r).trans hr)⟩

end Ring

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData)

/-- **The blowup is an isomorphism over an affine open where the centre is the unit ideal.** The
chart attached to the unit section is then the whole of the part of the blowup lying over that
open, and its structure morphism is `Spec` of an isomorphism. -/
theorem isIso_blowUpToBase_restrict_affine_reesData (U : S.affineOpens) (hI : ℐ.ideal U = ⊤) :
    IsIso (Stacks.Blowup.blowUpToBase ℐ ∣_ (U : S.Opens)) := by
  have h1 : (1 : Γ(S, U.1)) ∈ ℐ.ideal U := hI ▸ Submodule.mem_top
  have hrange : (blowUpAffineChart ℐ U h1).opensRange
      = Stacks.Blowup.blowUpToBase ℐ ⁻¹ᵁ (U : S.Opens) := by
    simp only [blowUpAffineChart, Scheme.Hom.opensRange_comp, opensRange_specAffineBlowupι,
      basicOpen_reesDegOne_one_eq_top, Scheme.Hom.image_top_eq_opensRange,
      ← blowUpToBase_preimage_coe]
  have hset : Set.range (blowUpAffineChart ℐ U h1).base
      = Set.range (Stacks.Blowup.blowUpToBase ℐ ⁻¹ᵁ (U : S.Opens)).ι.base := by
    rw [Scheme.Opens.range_ι, ← hrange]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq (blowUpAffineChart ℐ U h1)
    (Stacks.Blowup.blowUpToBase ℐ ⁻¹ᵁ (U : S.Opens)).ι hset
  have hfac : e.hom ≫ (Stacks.Blowup.blowUpToBase ℐ ⁻¹ᵁ (U : S.Opens)).ι
      = blowUpAffineChart ℐ U h1 := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hset
  have hunit : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, U.1) (affineBlowup (ℐ.ideal U) (1 : Γ(S, U.1)))))) := by
    have : IsIso (CommRingCat.ofHom
        (algebraMap Γ(S, U.1) (affineBlowup (ℐ.ideal U) (1 : Γ(S, U.1))))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (bijective_algebraMap_affineBlowup_one (ℐ.ideal U))
    infer_instance
  have key : e.hom ≫ (Stacks.Blowup.blowUpToBase ℐ ∣_ (U : S.Opens))
      = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1)
          (affineBlowup (ℐ.ideal U) (1 : Γ(S, U.1)))))
        ≫ (Stacks.RelativeProj.isAffineOpen U).isoSpec.inv := by
    rw [← cancel_mono (U : S.Opens).ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      ← Category.assoc e.hom, hfac, blowUpAffineChart_blowUpToBase,
      IsAffineOpen.isoSpec_inv_ι]
  have hiso : IsIso (e.hom ≫ (Stacks.Blowup.blowUpToBase ℐ ∣_ (U : S.Opens))) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

/-- **The blowup is an isomorphism over any open disjoint from the centre.** The affine opens of
such an open cover it, and on each of them the centre is the unit ideal. -/
theorem isIso_blowUpToBase_restrict_of_subset_compl_support_reesData (W : S.Opens)
    (hW : (W : Set S) ⊆ (ℐ.support : Set S)ᶜ) :
    IsIso (Stacks.Blowup.blowUpToBase ℐ ∣_ W) := by
  refine AlgebraicGeometry.isIso_morphismRestrict_of_iSup _ W (fun V : W.toScheme.affineOpens ↦ V.1)
    (iSup_affineOpens_eq_top _) fun V ↦ ?_
  have haff : IsAffineOpen (W.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion _
  exact isIso_blowUpToBase_restrict_affine_reesData ℐ ⟨_, haff⟩
    (AlgebraicGeometry.Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support ℐ ⟨_, haff⟩
      (Set.subset_compl_iff_disjoint_right.mp
        fun z hz ↦ hW (Scheme.Opens.ι_image_le W V.1 hz)))

/-- **Stacks Project, Tag 02OS, first assertion**, for `Stacks.Blowup.blowUp`. The blowup is an
isomorphism over the open complement of the closed subscheme cut out by the centre.

No attribute is attached: the tag is carried by
`AlgebraicGeometry.isIso_blowUp_restrict_compl_support`, which is the same statement for
`AlgebraicGeometry.blowUp`. -/
instance isIso_blowUpToBase_restrict_compl_support_reesData :
    IsIso (Stacks.Blowup.blowUpToBase ℐ ∣_ ℐ.support.compl) :=
  isIso_blowUpToBase_restrict_of_subset_compl_support_reesData ℐ _ fun _ hz ↦ hz

/-! ### The universal property -/

/-- The structure morphism of the chart of the blowup over an affine open `U` of the base is the
structure morphism of the blowup of `Spec Γ(S, U)` in `ℐ(U)`, read through the affine
identification of `U`. The two sides differ only by associativity. -/
theorem chartToOpen_eq_toSpec_comp (U : S.affineOpens) :
    Stacks.RelativeProj.chartToOpen (fun V : S.affineOpens ↦ reesGrading (ℐ.ideal V)) U
        (reesBase ℐ U)
      = toSpec (ℐ.ideal U) ≫ (Stacks.RelativeProj.isAffineOpen U).isoSpec.inv :=
  (Category.assoc (Proj.toSpecZero (reesGrading (ℐ.ideal U))) (Spec.map (reesBase ℐ U))
    (Stacks.RelativeProj.isAffineOpen U).isoSpec.inv).symm

/-- **The classifying morphism into the blowup, locally over an affine open of the base.** If the
centre becomes the principal ideal generated by a nonzerodivisor along a morphism `w : W ⟶ U` to
an affine open of the base, then `W` admits a morphism to the blowup over the base. The chart of
the blowup over `U` is the blowup of `Spec Γ(S, U)` in `ℐ(U)`, where the morphism is
`Stacks.Blowup.exists_hom_toSpec`, and the chart square carries it to the blowup. -/
theorem exists_hom_blowUp_of_ideal_eq_span_reesData (U : S.affineOpens) {W : Scheme.{u}}
    (w : W ⟶ (U : S.Opens).toScheme) (t : Γ(W, ⊤)) (ht : t ∈ nonZeroDivisors Γ(W, ⊤))
    (hIt : (ℐ.ideal U).map (specHomRingHom
      (w ≫ (Stacks.RelativeProj.isAffineOpen U).isoSpec.hom)) = Ideal.span {t}) :
    ∃ g : W ⟶ Stacks.Blowup.blowUp ℐ,
      g ≫ Stacks.Blowup.blowUpToBase ℐ = w ≫ (U : S.Opens).ι := by
  obtain ⟨c, hc⟩ : ∃ c : W ⟶ Proj (reesGrading (ℐ.ideal U)),
      c ≫ Stacks.RelativeProj.chartToOpen (fun V : S.affineOpens ↦ reesGrading (ℐ.ideal V)) U
        (reesBase ℐ U) = w := by
    obtain ⟨g₀, hg₀⟩ := exists_hom_toSpec (ℐ.ideal U)
      (w ≫ (Stacks.RelativeProj.isAffineOpen U).isoSpec.hom) t hIt ht
    have key : g₀ ≫ toSpec (ℐ.ideal U) ≫
        (Stacks.RelativeProj.isAffineOpen U).isoSpec.inv = w := by
      rw [← Category.assoc, hg₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    refine ⟨g₀, ?_⟩
    rw [chartToOpen_eq_toSpec_comp]
    exact key
  refine ⟨c ≫ blowUpChart ℐ U, ?_⟩
  calc (c ≫ blowUpChart ℐ U) ≫ Stacks.Blowup.blowUpToBase ℐ
      = c ≫ blowUpChart ℐ U ≫ Stacks.Blowup.blowUpToBase ℐ := Category.assoc _ _ _
    _ = c ≫ Stacks.RelativeProj.chartToOpen (fun V : S.affineOpens ↦ reesGrading (ℐ.ideal V)) U
          (reesBase ℐ U) ≫ (U : S.Opens).ι := by rw [blowUpChart_blowUpToBase]
    _ = (c ≫ Stacks.RelativeProj.chartToOpen
          (fun V : S.affineOpens ↦ reesGrading (ℐ.ideal V)) U (reesBase ℐ U)) ≫
          (U : S.Opens).ι := (Category.assoc _ _ _).symm
    _ = w ≫ (U : S.Opens).ι := by rw [hc]

/-- **The existence half of Stacks Project, Tag 0806**, for `Stacks.Blowup.blowUp`. A scheme over
`S` on which the inverse image of the centre is an effective Cartier divisor admits a morphism to
the blowup over `S`. The construction is local on the source: by tag 01WS every point has an
affine neighbourhood lying over an affine open of the base on which the inverse image of the
centre is cut out by a nonzerodivisor, and the local morphisms glue by the uniqueness half. -/
theorem exists_hom_blowUp_of_isEffectiveCartierDivisor_reesData {Y : Scheme.{u}} (f : Y ⟶ S)
    (hcartier : Stacks.Divisors.IsEffectiveCartierDivisor (ℐ.comap f)) :
    ∃ g : Y ⟶ Stacks.Blowup.blowUp ℐ, g ≫ Stacks.Blowup.blowUpToBase ℐ = f := by
  classical
  have hdense : ∀ (Z : Scheme.{u}) (p : Z ⟶ Y), IsOpenImmersion p →
      Scheme.Opens.IsSchemeTheoreticallyDense ((p ≫ f) ⁻¹ᵁ ℐ.support.compl) := by
    intro Z p hp
    have hpre : (p ≫ f) ⁻¹ᵁ ℐ.support.compl = p ⁻¹ᵁ (ℐ.comap f).support.compl := by
      rw [preimage_compl_support ℐ (p ≫ f), Scheme.IdealSheafData.comap_comp,
        ← preimage_compl_support (ℐ.comap f) p]
    rw [hpre]
    exact Scheme.Opens.isSchemeTheoreticallyDense_preimage_of_isOpenImmersion _
      (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _
        hcartier) p
  choose U hU using fun y : Y ↦ Stacks.Divisors.exists_affineOpens_mem (f.base y)
  choose V hyV hVU g hg hgen using fun y : Y ↦
    exists_affineOpens_ideal_eq_span_le (ℐ.comap f) hcartier y (f ⁻¹ᵁ (U y : S.Opens)) (hU y)
  refine exists_hom_of_isOpenCover (Stacks.Blowup.blowUpToBase ℐ) f hdense
    (fun y ↦ (V y : Y.Opens)) (TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun z _ ↦
      TopologicalSpace.Opens.mem_iSup.2 ⟨z, hyV z⟩)) fun y ↦ ?_
  obtain ⟨h, hh⟩ := exists_hom_blowUp_of_ideal_eq_span_reesData ℐ (U y)
    (f.resLE (U y : S.Opens) (V y : Y.Opens) (hVU y))
    ((V y : Y.Opens).topIso.inv.hom (g y))
    (mem_nonZeroDivisors_iso (V y : Y.Opens).topIso.symm
      (isRegular_iff_mem_nonZeroDivisors.mp (hg y)))
    (by
      rw [ideal_map_specHomRingHom_resLE ℐ f (U y) (V y) (hVU y), hgen y, Ideal.map_span,
        Set.image_singleton])
  exact ⟨h, by rw [hh, Scheme.Hom.resLE_comp_ι]⟩

/-- **Stacks Project, Tag 0806**, for `Stacks.Blowup.blowUp`. The blowup of a scheme in a
quasi-coherent sheaf of ideals is a final object of the category of schemes over the base on which
the inverse image of the centre is an effective Cartier divisor. Unconditional: separatedness is
`Stacks.RelativeProj.Data.isSeparated_toBase`, the two assertions of tag 02OS are
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData` and
`Stacks.Blowup.isIso_blowUpToBase_restrict_compl_support_reesData`, density of the complement of
an effective Cartier divisor is tag 07ZU, and the classifying morphism is
`Stacks.Blowup.exists_hom_blowUp_of_isEffectiveCartierDivisor_reesData`.

No attribute is attached: the tag is carried by `Stacks.Blowup.isTerminal_blowUp`, which is the
same statement for `AlgebraicGeometry.blowUp`. -/
@[ega "IV 19.4.1", sga "6 XIII 7.1.4" "more general"]
theorem isTerminal_blowUp_reesData :
    ∃ h : IsCartierOver ℐ (Over.mk (Stacks.Blowup.blowUpToBase ℐ)),
      Nonempty (IsTerminal (⟨Over.mk (Stacks.Blowup.blowUpToBase ℐ), h⟩ : CartierOver ℐ)) :=
  exists_nonempty_isTerminal ℐ (Stacks.Blowup.blowUpToBase ℐ)
    (isEffectiveCartierDivisor_exceptionalIdeal_reesData ℐ) inferInstance
    (fun _ J hJ ↦
      Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor J hJ)
    fun Y hY ↦ exists_hom_blowUp_of_isEffectiveCartierDivisor_reesData ℐ Y.hom hY

/-! ### Comparison of the two constructions of the blowup -/

/-- **The two constructions of the blowup agree.** The canonical isomorphism over the base between
`Stacks.Blowup.blowUp` and `AlgebraicGeometry.blowUp`: both are final objects of the same
category, by `Stacks.Blowup.isTerminal_blowUp_reesData` and `Stacks.Blowup.isTerminal_blowUp`. -/
def blowUpOverIso : Over.mk (Stacks.Blowup.blowUpToBase ℐ) ≅
    Over.mk (AlgebraicGeometry.blowUpToBase ℐ) :=
  (ObjectProperty.ι (IsCartierOver ℐ)).mapIso
    ((Classical.choice (Classical.choose_spec (isTerminal_blowUp_reesData ℐ))).uniqueUpToIso
      (Classical.choice (Classical.choose_spec (isTerminal_blowUp ℐ))))

/-- The comparison isomorphism carries one blowup morphism to the other. -/
theorem blowUpOverIso_hom_left_comp :
    (blowUpOverIso ℐ).hom.left ≫ AlgebraicGeometry.blowUpToBase ℐ =
      Stacks.Blowup.blowUpToBase ℐ :=
  Over.w (blowUpOverIso ℐ).hom

/-- The comparison isomorphism, as an isomorphism of schemes. -/
def blowUpIso : Stacks.Blowup.blowUp ℐ ≅ AlgebraicGeometry.blowUp ℐ :=
  (Over.forget S).mapIso (blowUpOverIso ℐ)

/-- The scheme-level comparison isomorphism carries one blowup morphism to the other. -/
@[simp]
theorem blowUpIso_hom_comp :
    (blowUpIso ℐ).hom ≫ AlgebraicGeometry.blowUpToBase ℐ = Stacks.Blowup.blowUpToBase ℐ :=
  blowUpOverIso_hom_left_comp ℐ

/-- **Admissibility may be tested against either construction of the blowup.**
`Stacks.Blowup.IsAdmissibleBlowup` is phrased with `Stacks.Blowup.blowUp`; this says the same
condition with `AlgebraicGeometry.blowUp` defines the same predicate. -/
theorem isAdmissibleBlowup_iff {X X' : Scheme.{u}} (U : X.Opens) (f : X' ⟶ X) :
    IsAdmissibleBlowup U f ↔ ∃ I : X.IdealSheafData,
      AlgebraicGeometry.FinitePresentation I.subschemeι ∧
        Disjoint (U : Set X) (I.support : Set X) ∧
          ∃ e : X' ≅ AlgebraicGeometry.blowUp I,
            e.hom ≫ AlgebraicGeometry.blowUpToBase I = f := by
  constructor
  · rintro ⟨I, hfp, hdisj, e, he⟩
    refine ⟨I, hfp, hdisj, e ≪≫ blowUpIso I, ?_⟩
    rw [Iso.trans_hom, Category.assoc, blowUpIso_hom_comp, he]
  · rintro ⟨I, hfp, hdisj, e, he⟩
    refine ⟨I, hfp, hdisj, e ≪≫ (blowUpIso I).symm, ?_⟩
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← blowUpIso_hom_comp I,
      Iso.inv_hom_id_assoc, he]

/-! ### Products of centres -/

/-- A product of finitely many finite-type quasi-coherent ideal sheaves is of finite type. -/
theorem isFiniteType_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (hI : ∀ i, (I i).IsFiniteType) :
    (s.prod I).IsFiniteType := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro V
    simpa using Ideal.fg_top Γ(X, V.1)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hI a).mul ih

/-- The support of a product of finitely many quasi-coherent ideal sheaves, each supported away
from an open `U`, is again disjoint from `U`: the support of a product is the union of the
supports. -/
theorem disjoint_support_prod {X : Scheme.{u}} (U : X.Opens) {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData)
    (hI : ∀ i ∈ s, Disjoint (U : Set X) ((I i).support : Set X)) :
    Disjoint (U : Set X) ((∏ i ∈ s, I i).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    refine Set.disjoint_left.mpr fun x hxU hx ↦ ?_
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup, Set.mem_union] at hx
    rcases hx with hx | hx
    · exact (Set.disjoint_left.mp (hI a (Finset.mem_insert_self ..))) hxU hx
    · exact (Set.disjoint_left.mp (ih fun j hj ↦ hI j (Finset.mem_insert_of_mem hj))) hxU hx

/-! ### The dominating admissible blowup -/

/-- **Stacks Project, Tag 080N.** Let `U` be an open subscheme of a scheme `X` and let
`b_i : Y_i ⟶ X`, `i ∈ ι`, be a finite family of `U`-admissible blowups. There is a `U`-admissible
blowup `b : X' ⟶ X` which factors through every `b_i`, with each factor map `X' ⟶ Y_i` itself a
`b_i⁻¹(U)`-admissible blowup.

Take `X'` to be the blowup of `X` in the product `I = ∏ I_i` of the centres. The product is again
of finite type and supported away from `U`, so `b` is `U`-admissible. Writing `I = I_i · J_i`,
blowing up a product is blowing up the factors in succession (Stacks tag 080A), so `X'` is the
blowup of `Y_i` in the inverse image of `J_i`; flat base change along the isomorphism
`Y_i ≅ Bl_{I_i}(X)` (Stacks tag 0805) identifies that inverse image taken on `Y_i` with the one
taken on `Bl_{I_i}(X)`. The inverse image of `J_i` on `Y_i` is again of finite type and supported
away from `b_i⁻¹(U)`, so the factor map is `b_i⁻¹(U)`-admissible. -/
@[stacks 080N]
theorem exists_admissibleBlowup_dominating {X : Scheme.{u}} (U : X.Opens)
    {ι : Type*} [Finite ι] (Y : ι → Scheme.{u})
    (f : ∀ i, Y i ⟶ X)
    (hf : ∀ i, IsAdmissibleBlowup U (f i)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        ∃ g : ∀ i, X' ⟶ Y i,
          (∀ i, g i ≫ f i = b) ∧
            (∀ i, IsAdmissibleBlowup (f i ⁻¹ᵁ U) (g i)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose I hIfp hIdisj e he using fun i ↦ (isAdmissibleBlowup_iff U (f i)).mp (hf i)
  have hprodfp : ∀ s : Finset ι,
      AlgebraicGeometry.FinitePresentation (∏ i ∈ s, I i).subschemeι := fun s ↦
    (finitePresentation_subschemeι_iff_isFiniteType _).mpr (isFiniteType_prod s I fun i ↦
      (finitePresentation_subschemeι_iff_isFiniteType (I i)).mp (hIfp i))
  have hproddisj : ∀ s : Finset ι, Disjoint (U : Set X) ((∏ i ∈ s, I i).support : Set X) :=
    fun s ↦ disjoint_support_prod U s I fun j _ ↦ hIdisj j
  let K : X.IdealSheafData := Finset.univ.prod I
  refine ⟨AlgebraicGeometry.blowUp K, AlgebraicGeometry.blowUpToBase K,
    (isAdmissibleBlowup_iff U _).mpr
      ⟨K, hprodfp _, hproddisj _, Iso.refl _, Category.id_comp _⟩, ?_⟩
  let J : ∀ i, X.IdealSheafData := fun i ↦ (Finset.univ.erase i).prod I
  let L : ∀ i, (AlgebraicGeometry.blowUp (I i)).IdealSheafData := fun i ↦
    (J i).comap (AlgebraicGeometry.blowUpToBase (I i))
  let M : ∀ i, (Y i).IdealSheafData := fun i ↦ (L i).comap (e i).hom
  let eprod : ∀ i, Over.mk (AlgebraicGeometry.blowUpToBase (L i) ≫
      AlgebraicGeometry.blowUpToBase (I i)) ≅ Over.mk (AlgebraicGeometry.blowUpToBase K) := by
    intro i
    have hprod : I i * J i = K :=
      Finset.mul_prod_erase Finset.univ I (Finset.mem_univ i)
    exact (AlgebraicGeometry.blowUpMulIso (I i) (J i)).trans (eqToIso
      (congrArg (fun T : X.IdealSheafData ↦ Over.mk (AlgebraicGeometry.blowUpToBase T)) hprod))
  let q : ∀ i, AlgebraicGeometry.blowUp K ≅ AlgebraicGeometry.blowUp (L i) := fun i ↦
    (Over.forget X).mapIso (eprod i).symm
  have hMfp : ∀ i, AlgebraicGeometry.FinitePresentation (M i).subschemeι := fun i ↦
    finitePresentation_comap_subschemeι (L i) (e i).hom
      (finitePresentation_comap_subschemeι (J i) (AlgebraicGeometry.blowUpToBase (I i))
        (hprodfp _))
  have H : ∀ i, ∃ h : AlgebraicGeometry.blowUp (M i) ⟶ AlgebraicGeometry.blowUp (L i),
      IsPullback (AlgebraicGeometry.blowUpToBase (M i)) h (e i).hom
        (AlgebraicGeometry.blowUpToBase (L i)) := by
    intro i
    have : IsIso (e i).hom := (e i).isIso_hom
    have : IsOpenImmersion (e i).hom := IsOpenImmersion.of_isIso _
    have : Flat (e i).hom := inferInstance
    exact AlgebraicGeometry.exists_isPullback_blowUpToBase_comap (e i).hom (L i)
  let r : ∀ i, AlgebraicGeometry.blowUp (M i) ≅ AlgebraicGeometry.blowUp (L i) := fun i ↦ by
    have : IsIso (Classical.choose (H i)) :=
      (Classical.choose_spec (H i)).isIso_snd_of_isIso (e i).isIso_hom
    exact asIso (Classical.choose (H i))
  have hMeq : ∀ i, M i = (J i).comap (f i) := by
    intro i
    show ((J i).comap (AlgebraicGeometry.blowUpToBase (I i))).comap (e i).hom = _
    rw [← Scheme.IdealSheafData.comap_comp, he i]
  have hMdisj : ∀ i,
      Disjoint ((f i ⁻¹ᵁ U : (Y i).Opens) : Set (Y i)) ((M i).support : Set (Y i)) := by
    intro i
    rw [hMeq i, Scheme.IdealSheafData.support_comap]
    exact (hproddisj _).preimage (f i).base
  refine ⟨fun i ↦ (q i).hom ≫ (r i).inv ≫ AlgebraicGeometry.blowUpToBase (M i), fun i ↦ ?_,
    fun i ↦ (isAdmissibleBlowup_iff (f i ⁻¹ᵁ U) _).mpr
      ⟨M i, hMfp i, hMdisj i, (q i) ≪≫ (r i).symm, Category.assoc _ _ _⟩⟩
  have hq : (q i).hom ≫ AlgebraicGeometry.blowUpToBase (L i) ≫
      AlgebraicGeometry.blowUpToBase (I i) = AlgebraicGeometry.blowUpToBase K :=
    Over.w (eprod i).symm.hom
  have hcompat : AlgebraicGeometry.blowUpToBase (M i) ≫ (e i).hom =
      (r i).hom ≫ AlgebraicGeometry.blowUpToBase (L i) := (Classical.choose_spec (H i)).w
  rw [← he i, ← hq]
  simp only [Category.assoc, reassoc_of% hcompat, Iso.inv_hom_id_assoc]

end Stacks.Blowup

end
