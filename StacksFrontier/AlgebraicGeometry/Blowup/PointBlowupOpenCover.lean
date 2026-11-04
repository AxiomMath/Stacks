module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenBase
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange

/-!
# The blowup of a scheme in an ideal sheaf supported in an open

Let `X` be a scheme and `I` a quasi-coherent sheaf of ideals on `X` whose support is contained
in an open `V`. Then the blowup `b : X' ⟶ X` of `X` in `I` is covered by two opens:

* the part `b⁻¹(V)` over `V`, which is the blowup of `V` in the restriction `I|_V` — this is
  flat base change along the open immersion `V ⟶ X`, [Stacks, Tag 0805];
* the part over the complement of the support of `I`, over which `b` is an isomorphism,
  [Stacks, Tag 02OS].

Those two opens cover `X'` because `V` together with the complement of the support covers `X`.

The case this is written for is the blowup of `X` at a closed point `p`, that is in the reduced
ideal sheaf `Scheme.IdealSheafData.vanishingIdeal {p}`, whose support is `{p}`: on an open `V`
containing `p` that ideal sheaf restricts to the reduced ideal sheaf of `p` as a point of `V`,
so that the blowup of `X` at `p` is covered by the blowup of `V` at `p` and by a copy of
`X ∖ {p}`. When `V` is affine this reduces the blowup of a scheme at a closed point to a blowup
of an affine scheme in an ideal of its ring, which is what makes a chain of blowups at closed
points computable chart by chart.

## Main results

* `AlgebraicGeometry.radical_comap_open` — the radical of an ideal sheaf commutes with
  restriction to an open.
* `AlgebraicGeometry.pointIdeal_comap_open` — the reduced ideal sheaf of a closed point
  restricts, on an open containing it, to the reduced ideal sheaf of that point.
* `AlgebraicGeometry.exists_isOpenImmersion_blowUp_comap` — the blowup of the source of an open
  immersion into the base, in the restricted ideal sheaf, is the part of the blowup lying over
  the image.
* `AlgebraicGeometry.exists_iso_blowUp_comap_opens` — the same for an open `V` of the base: the
  blowup of `V` in the restricted ideal sheaf is the part of the blowup lying over `V`.
* `AlgebraicGeometry.sup_preimage_compl_support_eq_top` — the part over an open containing the
  support and the part over the complement of the support cover the blowup.
* `AlgebraicGeometry.exists_openCover_blowUp_of_support_subset` — the two pieces together, in
  the shape a property local at the source consumes them.

## Implementation notes

The comparison morphism of [Stacks, Tag 0805] is `exists_isPullback_blowUpToBase_comap`, whose
hypothesis is flatness of the morphism of bases; an open immersion is flat, and a base change of
an open immersion is an open immersion, so the comparison morphism is an open immersion whose
range is `b⁻¹(V)`. Identifying that range is the computation already performed inside
`AlgebraicGeometry.exists_strictTransformBlowUp_iso_restrict`, where the resulting isomorphism is
bundled with the strict-transform data; here it is isolated, and that proof consumes this one.

The two lemmas about radicals and reduced point ideals were previously private to
`StacksFrontier/AlgebraicGeometry/NodalContraction/FiniteType.lean`; they are generic statements
about ideal sheaves along an open immersion, so they live here and that file imports them.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Reduced point ideals along an open immersion -/

/-- Taking the radical of an ideal sheaf commutes with restriction to an open. -/
public theorem radical_comap_open {X Y : Scheme.{u}} (I : Y.IdealSheafData) (j : X ⟶ Y)
    [IsOpenImmersion j] : (I.comap j).radical = I.radical.comap j := by
  ext V
  simp only [Scheme.IdealSheafData.radical_ideal,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Ideal.comap_radical]

/-- Restricting the reduced ideal sheaf of a closed point along an open immersion hitting it gives
the reduced ideal sheaf of the point it comes from. -/
private theorem comap_vanishingIdeal_singleton {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (z : U) (hz : IsClosed ({z} : Set U))
    (hjz : IsClosed ({j.base z} : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{j.base z}, hjz⟩ : Closeds X)).comap j =
      Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds U) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{j.base z}, hjz⟩ : Closeds X)
  have hrad : I.radical = I := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    show Scheme.IdealSheafData.vanishingIdeal I.support =
      Scheme.IdealSheafData.vanishingIdeal (⟨{j.base z}, hjz⟩ : Closeds X)
    congr 1
  have hrad' : (I.comap j).radical = I.comap j := by
    rw [radical_comap_open, hrad]
  rw [← hrad', ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  ext y
  show y ∈ (I.comap j).support ↔ y = z
  rw [Scheme.IdealSheafData.support_comap]
  show j.base y ∈ (I.support : Set X) ↔ y = z
  rw [show (I.support : Set X) = {j.base z} by simp [I]]
  exact ⟨fun h ↦ j.isOpenEmbedding.injective h, fun h ↦ congrArg j.base h⟩


/-- The reduced ideal sheaf of a closed point restricts, on an open containing that point, to the
reduced ideal sheaf of the point. -/
public theorem pointIdeal_comap_open {X : Scheme.{u}} (z : X) (hz : IsClosed ({z} : Set X))
    (U : X.Opens) (hzU : z ∈ U) (hz' : IsClosed ({(⟨z, hzU⟩ : U)} : Set U)) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X)).comap U.ι =
      Scheme.IdealSheafData.vanishingIdeal (⟨{(⟨z, hzU⟩ : U)}, hz'⟩ : Closeds U) :=
  comap_vanishingIdeal_singleton U.ι ⟨z, hzU⟩ hz' hz

/-- The reduced ideal sheaf of a closed point restricts, along any open immersion hitting that
point, to the reduced ideal sheaf of the point it comes from. -/
public theorem pointIdeal_comap_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (z : U) (hz : IsClosed ({z} : Set U))
    (hjz : IsClosed ({j.base z} : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{j.base z}, hjz⟩ : Closeds X)).comap j =
      Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds U) :=
  comap_vanishingIdeal_singleton j z hz hjz

/-! ### The part of a blowup over an open of the base -/

/-- **The blowup of the source of an open immersion into the base, in the restricted ideal sheaf,
is the part of the blowup lying over the image**, compatibly with the two blowup morphisms. This
is the open-immersion case of the flat base change of [Stacks, Tag 0805]. -/
public theorem exists_isOpenImmersion_blowUp_comap (K : X.IdealSheafData) {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ hj : blowUp (K.comap j) ⟶ blowUp K, IsOpenImmersion hj ∧
      blowUpToBase (K.comap j) ≫ j = hj ≫ blowUpToBase K ∧
      Set.range hj.base = blowUpToBase K ⁻¹' Set.range j.base := by
  obtain ⟨hBl, hBlPB⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap j K
  have : IsOpenImmersion hBl := MorphismProperty.of_isPullback hBlPB inferInstance
  refine ⟨hBl, inferInstance, hBlPB.w, ?_⟩
  have hcan := IsPullback.of_hasPullback j (blowUpToBase K)
  have hsnd := hBlPB.isoIsPullback_hom_snd _ _ hcan
  have h1 : Set.range hBl.base = Set.range (pullback.snd j (blowUpToBase K)).base := by
    rw [← hsnd]
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    rw [(surjective_base_of_isIso (hBlPB.isoIsPullback _ _ hcan).hom).range_eq, Set.image_univ]
  rw [h1, Scheme.Pullback.range_snd]

/-- **The blowup of an open `V` of the base in the restricted ideal sheaf is the part of the
blowup lying over `V`**, compatibly with the two blowup morphisms. This is the open-immersion
case of the flat base change of [Stacks, Tag 0805]. -/
public theorem exists_iso_blowUp_comap_opens (K : X.IdealSheafData) (V : X.Opens) :
    ∃ e : blowUp (K.comap V.ι) ≅ (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).toScheme,
      e.hom ≫ (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι ≫ blowUpToBase K =
        blowUpToBase (K.comap V.ι) ≫ V.ι := by
  obtain ⟨hBl, hoi, hw, hrange⟩ := exists_isOpenImmersion_blowUp_comap K V.ι
  have := hoi
  have hBlRange : Set.range hBl.base =
      Set.range (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι.base := by
    rw [hrange, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl
  refine ⟨IsOpenImmersion.isoOfRangeEq hBl
    (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι hBlRange, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac hBl _ hBlRange]
  exact hw.symm

/-! ### The two pieces cover -/

/-- **The part of the blowup over an open containing the support and the part over the
complement of the support cover the blowup.** -/
public theorem sup_preimage_compl_support_eq_top (K : X.IdealSheafData) (V : X.Opens)
    (hV : (K.support : Set X) ⊆ V) :
    (blowUpToBase K ⁻¹ᵁ V) ⊔ (blowUpToBase K ⁻¹ᵁ K.support.compl) = ⊤ := by
  have hXV : V ⊔ K.support.compl = ⊤ := by
    refine le_antisymm le_top fun z _ ↦ ?_
    by_cases hz : z ∈ (K.support : Set X)
    · exact Or.inl (hV hz)
    · exact Or.inr hz
  rw [← Scheme.Hom.preimage_sup, hXV, Scheme.Hom.preimage_top]

/-- **The blowup of `X` in an ideal sheaf supported inside an open `V` is covered by the blowup
of `V` and by a copy of the complement of the support.** The first piece is flat base change
along `V ⟶ X` ([Stacks, Tag 0805]) and the second is the isomorphism off the centre
([Stacks, Tag 02OS]). -/
public theorem exists_openCover_blowUp_of_support_subset (K : X.IdealSheafData) (V : X.Opens)
    (hV : (K.support : Set X) ⊆ V) :
    ∃ (eV : blowUp (K.comap V.ι) ≅ (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).toScheme),
      (eV.hom ≫ (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι ≫ blowUpToBase K =
          blowUpToBase (K.comap V.ι) ≫ V.ι) ∧
        IsIso (blowUpToBase K ∣_ K.support.compl) ∧
        (blowUpToBase K ⁻¹ᵁ V) ⊔ (blowUpToBase K ⁻¹ᵁ K.support.compl) = ⊤ := by
  obtain ⟨eV, heV⟩ := exists_iso_blowUp_comap_opens K V
  exact ⟨eV, heV, isIso_blowUpToBase_restrict_of_subset_compl_support K _ fun _ hz ↦ hz,
    sup_preimage_compl_support_eq_top K V hV⟩

end AlgebraicGeometry

end
