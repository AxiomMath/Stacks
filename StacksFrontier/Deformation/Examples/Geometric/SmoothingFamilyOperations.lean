module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Families over a base: disjoint unions and open pieces

This file collects the operations on families of schemes over a base `S` used to assemble a
smoothing out of pieces, as in the proofs of [Stacks, Tag 0E7Y] and [Stacks, Tag 0E7Z]: a
smoothing of `X` is built from smoothings of the two members of a decomposition `X = X' ⊔ X''`
into complementary open and closed pieces, and in Tag 0E7Z a smoothing of an open subscheme is
cut out of a smoothing of a compactification.

Everything is phrased through a fixed morphism `h : T ⟶ S` along which the families are pulled
back; in the application `S = Spec k⟦t⟧` and `h` is either the generic point or the closed
point.

* The pullback of `coprod.desc g₁ g₂ : Y₁ ⨿ Y₂ ⟶ S` along `h` is the disjoint union of the
  pullbacks of `g₁` and `g₂`: `Deformation.Examples.Smoothing.pullbackCoprodDescIso`.
* A property of morphisms local on the source holds for the pullback of `coprod.desc g₁ g₂` as
  soon as it holds for the pullbacks of `g₁` and `g₂`:
  `Deformation.Examples.Smoothing.pullback_snd_coprodDesc`; and it holds for the pullback of
  the restriction `V.ι ≫ g` of `g` to an open `V` as soon as it holds for the pullback of `g`:
  `Deformation.Examples.Smoothing.pullback_snd_ι_comp`.
* Separatedness and quasi-compactness of `coprod.desc g₁ g₂`.
* A scheme with two complementary opens `U`, `V` is their disjoint union:
  `Deformation.Examples.Smoothing.isIso_coprodDesc_ι_of_isCompl`.

## Main results

* `Deformation.Examples.Smoothing.exists_smoothing_of_isCompl`: smoothings of the two members of
  a decomposition of `X` into complementary opens give a smoothing of `X`, for any class of
  morphisms stable under `coprod.desc` added to flatness.
* `Deformation.Examples.Smoothing.exists_smoothing_of_opens`: a smoothing of `Xb` restricts to a
  smoothing of an open `X ⊆ Xb` whose complement lies in the special fibre.

## References

* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 0E7Z](https://stacks.math.columbia.edu/tag/0E7Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples.Smoothing

section Coprod

variable {Y₁ Y₂ S T : Scheme.{u}} (g₁ : Y₁ ⟶ S) (g₂ : Y₂ ⟶ S) (h : T ⟶ S)

/-- A property of morphisms which is local on the source holds for `coprod.desc g₁ g₂` once it
holds for `g₁` and for `g₂`. -/
theorem coprodDesc_of_isZariskiLocalAtSource (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] (h₁ : P g₁) (h₂ : P g₂) : P (coprod.desc g₁ g₂) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (coprodOpenCover.{u, 0} Y₁ Y₂)]
  rintro (i | i)
  · show P (coprod.inl ≫ coprod.desc g₁ g₂)
    rwa [coprod.inl_desc]
  · show P (coprod.inr ≫ coprod.desc g₁ g₂)
    rwa [coprod.inr_desc]

/-- `coprod.desc g₁ g₂` factors as `coprod.map g₁ g₂` followed by the codiagonal of `S`. -/
theorem coprodDesc_eq_coprodMap_comp :
    coprod.desc g₁ g₂ = coprod.map g₁ g₂ ≫ coprod.desc (𝟙 S) (𝟙 S) := by
  apply coprod.hom_ext <;> simp

/-- A disjoint union of two separated morphisms to `S` is separated: it is `coprod.map g₁ g₂`,
which is separated since separatedness is local on the target, followed by the codiagonal of
`S`, which is finite. -/
theorem isSeparated_coprodDesc [IsSeparated g₁] [IsSeparated g₂] :
    IsSeparated (coprod.desc g₁ g₂) := by
  have : IsSeparated (coprod.map g₁ g₂) :=
    IsZariskiLocalAtTarget.coprodMap g₁ g₂ inferInstance inferInstance
  have : IsFinite (coprod.desc (𝟙 S) (𝟙 S)) := inferInstance
  rw [coprodDesc_eq_coprodMap_comp]
  infer_instance

/-- A disjoint union of two quasi-compact morphisms to `S` is quasi-compact: the preimage of an
open is the union of the images of the two preimages. -/
theorem quasiCompact_coprodDesc [QuasiCompact g₁] [QuasiCompact g₂] :
    QuasiCompact (coprod.desc g₁ g₂) := by
  refine ⟨fun U hU hUc => ?_⟩
  have hpre : (coprod.desc g₁ g₂) ⁻¹' U =
      (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) '' (g₁ ⁻¹' U) ∪ (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂) '' (g₂ ⁻¹' U) := by
    ext z
    obtain ⟨z | z, rfl⟩ := (coprodMk Y₁ Y₂).surjective z
    · simp only [coprodMk_inl, Set.mem_preimage, Set.mem_union, Set.mem_image]
      rw [← Scheme.Hom.comp_apply, coprod.inl_desc]
      refine ⟨fun h => Or.inl ⟨z, h, rfl⟩, ?_⟩
      rintro (⟨w, hw, hwz⟩ | ⟨w, hw, hwz⟩)
      · rwa [← (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂).isOpenEmbedding.injective hwz]
      · exact (inr_ne_inl _ _ z w hwz).elim
    · simp only [coprodMk_inr, Set.mem_preimage, Set.mem_union, Set.mem_image]
      rw [← Scheme.Hom.comp_apply, coprod.inr_desc]
      refine ⟨fun h => Or.inr ⟨z, h, rfl⟩, ?_⟩
      rintro (⟨w, hw, hwz⟩ | ⟨w, hw, hwz⟩)
      · exact (inl_ne_inr _ _ w z hwz).elim
      · rwa [← (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂).isOpenEmbedding.injective hwz]
  rw [hpre]
  exact ((QuasiCompact.isCompact_preimage (f := g₁) U hU hUc).image
      (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂).continuous).union
    ((QuasiCompact.isCompact_preimage (f := g₂) U hU hUc).image
      (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂).continuous)

/-- Two open immersions with complementary ranges induce an isomorphism from the coproduct. -/
private theorem isIso_coprodDesc_of_isCompl_opensRange {A B X : Scheme.{u}} (a : A ⟶ X)
    (b : B ⟶ X) [IsOpenImmersion a] [IsOpenImmersion b] (hab : IsCompl a.opensRange b.opensRange) :
    IsIso (coprod.desc a b) := by
  obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl a b hab
  change IsIso ((coprodIsCoprod _ _).coconePointUniqueUpToIso hc).hom
  infer_instance

/-- The two open pieces of the pullback of `coprod.desc g₁ g₂` along `h`, cut out by the two
summands, are complementary. -/
theorem isCompl_opensRange_pullback_snd_inl_inr :
    IsCompl (pullback.snd (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂)
        (pullback.fst (coprod.desc g₁ g₂) h)).opensRange
      (pullback.snd (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂)
        (pullback.fst (coprod.desc g₁ g₂) h)).opensRange := by
  rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Hom.opensRange_pullbackSnd]
  convert! (isCompl_range_inl_inr Y₁ Y₂).map
    (CompleteLatticeHom.setPreimage (pullback.fst (coprod.desc g₁ g₂) h))
  simp [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]

/-- The pullback of `coprod.desc g₁ g₂` along `h` is the disjoint union of its two pieces. -/
theorem isIso_coprodDesc_pullback_snd_inl_inr :
    IsIso (coprod.desc
      (pullback.snd (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) (pullback.fst (coprod.desc g₁ g₂) h))
      (pullback.snd (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂) (pullback.fst (coprod.desc g₁ g₂) h))) := by
  exact isIso_coprodDesc_of_isCompl_opensRange _ _ (isCompl_opensRange_pullback_snd_inl_inr g₁ g₂ h)

/-- The piece of the pullback of `coprod.desc g₁ g₂` over the first summand is the pullback of
`g₁`. -/
def pullbackInlIso :
    pullback (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) (pullback.fst (coprod.desc g₁ g₂) h) ≅
      pullback g₁ h :=
  pullbackRightPullbackFstIso (coprod.desc g₁ g₂) h coprod.inl ≪≫
    pullback.congrHom (coprod.inl_desc g₁ g₂) rfl

/-- The piece of the pullback of `coprod.desc g₁ g₂` over the second summand is the pullback of
`g₂`. -/
def pullbackInrIso :
    pullback (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂) (pullback.fst (coprod.desc g₁ g₂) h) ≅
      pullback g₂ h :=
  pullbackRightPullbackFstIso (coprod.desc g₁ g₂) h coprod.inr ≪≫
    pullback.congrHom (coprod.inr_desc g₁ g₂) rfl

/-- The inverse of `pullbackInlIso` followed by the projections to `T` is the projection
`pullback.snd g₁ h`. -/
@[reassoc (attr := simp)]
theorem pullbackInlIso_inv_snd_snd :
    (pullbackInlIso g₁ g₂ h).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pullback.snd g₁ h := by
  rw [pullbackInlIso, Iso.trans_inv, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd,
    pullback.congrHom_inv, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The inverse of `pullbackInrIso` followed by the projections to `T` is the projection
`pullback.snd g₂ h`. -/
@[reassoc (attr := simp)]
theorem pullbackInrIso_inv_snd_snd :
    (pullbackInrIso g₁ g₂ h).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pullback.snd g₂ h := by
  rw [pullbackInrIso, Iso.trans_inv, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd,
    pullback.congrHom_inv, pullback.map, pullback.lift_snd, Category.comp_id]

/-- **The pullback of a disjoint union is the disjoint union of the pullbacks.** -/
def pullbackCoprodDescIso :
    pullback g₁ h ⨿ pullback g₂ h ≅ pullback (coprod.desc g₁ g₂) h :=
  have := isIso_coprodDesc_pullback_snd_inl_inr g₁ g₂ h
  coprod.mapIso (pullbackInlIso g₁ g₂ h).symm (pullbackInrIso g₁ g₂ h).symm ≪≫
    asIso (coprod.desc
      (pullback.snd (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) (pullback.fst (coprod.desc g₁ g₂) h))
      (pullback.snd (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂) (pullback.fst (coprod.desc g₁ g₂) h)))

/-- On the first summand, `pullbackCoprodDescIso` followed by the projection to `T` is
`pullback.snd g₁ h`. -/
@[reassoc (attr := simp)]
theorem inl_pullbackCoprodDescIso_hom_snd :
    coprod.inl ≫ (pullbackCoprodDescIso g₁ g₂ h).hom ≫ pullback.snd _ _ = pullback.snd g₁ h := by
  rw [pullbackCoprodDescIso, Iso.trans_hom, coprod.mapIso_hom, asIso_hom, Category.assoc,
    coprod.inl_map_assoc, coprod.inl_desc_assoc, Iso.symm_hom, pullbackInlIso_inv_snd_snd]

/-- On the second summand, `pullbackCoprodDescIso` followed by the projection to `T` is
`pullback.snd g₂ h`. -/
@[reassoc (attr := simp)]
theorem inr_pullbackCoprodDescIso_hom_snd :
    coprod.inr ≫ (pullbackCoprodDescIso g₁ g₂ h).hom ≫ pullback.snd _ _ = pullback.snd g₂ h := by
  rw [pullbackCoprodDescIso, Iso.trans_hom, coprod.mapIso_hom, asIso_hom, Category.assoc,
    coprod.inr_map_assoc, coprod.inr_desc_assoc, Iso.symm_hom, pullbackInrIso_inv_snd_snd]

/-- The pullback of `coprod.desc g₁ g₂` along `h` followed by the projection to `T` is the
disjoint union of the two projections. -/
theorem pullbackCoprodDescIso_hom_snd :
    (pullbackCoprodDescIso g₁ g₂ h).hom ≫ pullback.snd _ _ =
      coprod.desc (pullback.snd g₁ h) (pullback.snd g₂ h) := by
  apply coprod.hom_ext
  · rw [inl_pullbackCoprodDescIso_hom_snd, coprod.inl_desc]
  · rw [inr_pullbackCoprodDescIso_hom_snd, coprod.inr_desc]

/-- A property local on the source holds for the base change of `coprod.desc g₁ g₂` along `h`
once it holds for the base changes of `g₁` and of `g₂`. -/
theorem pullback_snd_coprodDesc (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (h₁ : P (pullback.snd g₁ h)) (h₂ : P (pullback.snd g₂ h)) :
    P (pullback.snd (coprod.desc g₁ g₂) h) := by
  have hP := coprodDesc_of_isZariskiLocalAtSource _ _ P h₁ h₂
  rw [← pullbackCoprodDescIso_hom_snd] at hP
  exact (P.cancel_left_of_respectsIso _ _).mp hP

end Coprod

section Opens

variable {Y S T : Scheme.{u}} (g : Y ⟶ S) (h : T ⟶ S) (V : Y.Opens)

/-- A property local on the source which holds for the base change of `g` along `h` holds for
the base change of its restriction to an open `V`: that base change is the restriction of the
base change of `g` to the preimage of `V`. -/
theorem pullback_snd_ι_comp (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (hg : P (pullback.snd g h)) : P (pullback.snd (V.ι ≫ g) h) := by
  have hcomp : P (pullback.snd V.ι (pullback.fst g h) ≫ pullback.snd g h) :=
    IsZariskiLocalAtSource.comp hg _
  rw [← pullbackRightPullbackFstIso_hom_snd] at hcomp
  exact (P.cancel_left_of_respectsIso _ _).mp hcomp

end Opens

section Decomposition

/-- **A scheme with two complementary opens is their disjoint union.** -/
theorem isIso_coprodDesc_ι_of_isCompl {X : Scheme.{u}} {U V : X.Opens} (hUV : IsCompl U V) :
    IsIso (coprod.desc U.ι V.ι) := by
  exact isIso_coprodDesc_of_isCompl_opensRange _ _
    (by rwa [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι])

end Decomposition

section Smoothing

variable (k : Type u) [Field k]

/-- **Smoothings of the members of a decomposition into complementary opens give a smoothing.**
Let `X` be a scheme over a field `k` and let `U`, `V` be complementary opens of `X`. Let `P` be
a class of morphisms to `Spec k⟦t⟧` stable under `coprod.desc`. If the open subschemes `U` and
`V` are each the special fibre of a flat family in `P` over `Spec k⟦t⟧` with smooth generic
fibre, then so is `X`: the family is the disjoint union of the two families. -/
theorem exists_smoothing_of_isCompl {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {U V : X.Opens}
    (hUV : IsCompl U V) (P : MorphismProperty Scheme.{u})
    (hP : ∀ {Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ Spec (.of (PowerSeries k)))
      (g₂ : Y₂ ⟶ Spec (.of (PowerSeries k))), P g₁ → P g₂ → P (coprod.desc g₁ g₂))
    (hU : ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      P g ∧ Flat g ∧
        Smooth (g.fiberToSpecResidueField
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k))) ∧
        ∃ e : U.toScheme ≅
            pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
          e.hom ≫ pullback.snd g
              (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = U.ι ≫ f)
    (hV : ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      P g ∧ Flat g ∧
        Smooth (g.fiberToSpecResidueField
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k))) ∧
        ∃ e : V.toScheme ≅
            pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
          e.hom ≫ pullback.snd g
              (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = V.ι ≫ f) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      P g ∧ Flat g ∧
        Smooth (g.fiberToSpecResidueField
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k))) ∧
        ∃ e : X ≅
            pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
          e.hom ≫ pullback.snd g
              (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = f := by
  obtain ⟨Y₁, g₁, hP₁, hfl₁, hsm₁, e₁, he₁⟩ := hU
  obtain ⟨Y₂, g₂, hP₂, hfl₂, hsm₂, e₂, he₂⟩ := hV
  let c := Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
  refine ⟨Y₁ ⨿ Y₂, coprod.desc g₁ g₂, hP g₁ g₂ hP₁ hP₂, ?_, ?_, ?_⟩
  · have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    exact coprodDesc_of_isZariskiLocalAtSource g₁ g₂ @Flat hfl₁ hfl₂
  · have : IsZariskiLocalAtSource (@Smooth : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
    exact pullback_snd_coprodDesc g₁ g₂ _ @Smooth hsm₁ hsm₂
  · have := isIso_coprodDesc_ι_of_isCompl hUV
    refine ⟨(asIso (coprod.desc U.ι V.ι)).symm ≪≫ coprod.mapIso e₁ e₂ ≪≫
      pullbackCoprodDescIso g₁ g₂ c, ?_⟩
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, asIso_inv, coprod.mapIso_hom, Category.assoc,
      IsIso.inv_comp_eq]
    apply coprod.hom_ext
    · rw [Category.assoc, coprod.inl_map_assoc, inl_pullbackCoprodDescIso_hom_snd,
        coprod.inl_desc_assoc, he₁]
    · rw [Category.assoc, coprod.inr_map_assoc, inr_pullbackCoprodDescIso_hom_snd,
        coprod.inr_desc_assoc, he₂]

/-- **A smoothing restricts to an open of its special fibre.** Let `g : Yb ⟶ Spec k⟦t⟧` be a
family whose special fibre is identified with a scheme `Xb` over `k` by `eb`, and let `X` be an
open of `Xb`. Removing from `Yb` the image of the closed set `Xb ∖ X` — closed in `Yb`, the special
fibre being a closed subscheme — leaves an open `W` of `Yb` whose special fibre is `X`. The
generic fibre and flatness of `W.ι ≫ g` are controlled by
`Deformation.Examples.Smoothing.pullback_snd_ι_comp`. -/
theorem exists_smoothing_of_opens {Xb Yb : Scheme.{u}} (fb : Xb ⟶ Spec (.of k))
    (g : Yb ⟶ Spec (.of (PowerSeries k)))
    (eb : Xb ≅ pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))))
    (heb : eb.hom ≫ pullback.snd g
        (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = fb)
    (X : Xb.Opens) :
    ∃ W : Yb.Opens, ∃ e : X.toScheme ≅
        pullback (W.ι ≫ g) (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
      e.hom ≫ pullback.snd (W.ι ≫ g)
          (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = X.ι ≫ fb := by
  let c := Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
  have : IsClosedImmersion c :=
    IsClosedImmersion.spec_of_surjective _ PowerSeries.constantCoeff_surj
  let j : Xb ⟶ Yb := eb.hom ≫ pullback.fst g c
  have : IsClosedImmersion j := inferInstance
  have hclosed : IsClosed (j '' (X : Set Xb)ᶜ) :=
    j.isClosedEmbedding.isClosedMap _ X.isOpen.isClosed_compl
  let W : Yb.Opens := ⟨(j '' (X : Set Xb)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hrange : Set.range (X.ι ≫ eb.hom) =
      Set.range (pullback.snd W.ι (pullback.fst g c)) := by
    rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.opensRange_ι]
    ext z
    obtain ⟨x, rfl⟩ := eb.hom.surjective z
    constructor
    · rintro ⟨x', hx'⟩
      rw [Scheme.Hom.comp_apply] at hx'
      obtain rfl := eb.hom.isOpenEmbedding.injective hx'
      have hxX := Set.mem_range_self (f := X.ι) x'
      rw [Scheme.Opens.range_ι] at hxX
      show j (X.ι x') ∈ W
      rintro ⟨y, hy, hjy⟩
      exact hy ((j.isClosedEmbedding.injective hjy) ▸ hxX)
    · intro hz
      change j x ∈ W at hz
      exact ⟨⟨x, Classical.byContradiction fun hx => hz ⟨x, hx, rfl⟩⟩, rfl⟩
  refine ⟨W, IsOpenImmersion.isoOfRangeEq (X.ι ≫ eb.hom) (pullback.snd W.ι (pullback.fst g c))
    hrange ≪≫ pullbackRightPullbackFstIso g c W.ι, ?_⟩
  rw [Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, Category.assoc, heb]

end Smoothing

end Deformation.Examples.Smoothing

end
