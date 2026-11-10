module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.WeaklyEtaleAffineRefinementSize
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# Weakly étale covers through which a flat morphism factors

Let `a : U ⟶ T` be weakly étale and let `φ : W ⟶ U` be a morphism over `T` from a flat
`T`-scheme `W`. This file covers the image of `φ` by weakly étale morphisms `h : U' ⟶ U` from
affine schemes, *exactly*: over a basis of affine opens `O` of `W` the image of `O` is the image
of one such `h`, so that `O ×_U U' ⟶ O` and `O ×_U U' ⟶ U'` are both surjective. The schemes
`U'` are moreover no larger than `U`.

It also proves two ways of recognizing quasi-compact coverings: a family of morphisms refined by
a quasi-compact covering is one as soon as it is jointly surjective, which is automatic; and a
family of morphisms from quasi-compact schemes whose images are open and form a basis of the
target is one.

## Main results

* `AlgebraicGeometry.Scheme.mem_propQCPrecoverage_of_refinement`: a family of `P`-morphisms
  through which the members of a quasi-compact covering factor is a quasi-compact `P`-covering.
* `AlgebraicGeometry.Scheme.ofArrows_mem_propQCPrecoverage_of_isBasis`: a family of
  `P`-morphisms from quasi-compact schemes whose images are open and form a basis is a
  quasi-compact `P`-covering.
* `AlgebraicGeometry.ProEtale.exists_weaklyEtale_affine_cover_of_flat`: the covers described
  above.

## References

* [Stacks Project, Tag 0F65](https://stacks.math.columbia.edu/tag/0F65)
* [Stacks Project, Tag 03L8](https://stacks.math.columbia.edu/tag/03L8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A family refined by a quasi-compact covering is a quasi-compact covering: if every member
of a quasi-compact `Q`-covering of `X` factors through a member of a family `R` of
`P`-morphisms, then `R` is a quasi-compact `P`-covering of `X`. -/
theorem mem_propQCPrecoverage_of_refinement {P Q : MorphismProperty Scheme.{u}} {X : Scheme.{u}}
    {R R' : Presieve X} (hR' : R' ∈ propQCPrecoverage Q X)
    (hP : ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), R f → P f)
    (hfac : ∀ ⦃Z : Scheme.{u}⦄ (g : Z ⟶ X), R' g →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (e : Z ⟶ Y), R f ∧ e ≫ f = g) :
    R ∈ propQCPrecoverage P X := by
  obtain ⟨hqc, hcov⟩ := hR'
  have hE : ∀ S : Presieve X, S = S.preZeroHypercover.presieve₀ :=
    fun S ↦ (Presieve.presieve₀_preZeroHypercover S).symm
  choose Y f e hf he using fun (i : R'.preZeroHypercover.I₀) ↦ hfac i.1.2 i.2
  let φ : R'.preZeroHypercover.Hom R.preZeroHypercover :=
    { s₀ := fun i ↦ ⟨⟨Y i, f i⟩, hf i⟩
      h₀ := fun i ↦ e i
      w₀ := fun i ↦ he i }
  refine ⟨?_, ?_⟩
  · rw [hE R, presieve₀_mem_qcPrecoverage_iff]
    rw [hE R', presieve₀_mem_qcPrecoverage_iff] at hqc
    exact QuasiCompactCover.of_hom φ
  · rw [hE R, PreZeroHypercover.presieve₀, ofArrows_mem_precoverage_iff]
    rw [hE R', PreZeroHypercover.presieve₀, ofArrows_mem_precoverage_iff] at hcov
    refine ⟨fun x ↦ ?_, fun i ↦ hP _ i.2⟩
    obtain ⟨i, z, rfl⟩ := hcov.1 x
    refine ⟨φ.s₀ i, e i z, ?_⟩
    change (φ.h₀ i ≫ R.preZeroHypercover.f (φ.s₀ i)) z = _
    rw [φ.w₀ i]

/-- A family of `P`-morphisms from quasi-compact schemes whose images are open and form a basis
of the topology of `X` is a quasi-compact `P`-covering of `X`. -/
theorem ofArrows_mem_propQCPrecoverage_of_isBasis {P : MorphismProperty Scheme.{u}}
    {X : Scheme.{u}} {ι : Type*} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) (hP : ∀ i, P (f i))
    (hc : ∀ i, CompactSpace (Y i)) (ho : ∀ i, IsOpen (Set.range (f i)))
    (hbasis : ∀ (V : X.Opens) (x : X), x ∈ V → ∃ i, x ∈ Set.range (f i) ∧ Set.range (f i) ⊆ V) :
    Presieve.ofArrows Y f ∈ propQCPrecoverage P X := by
  let E : PreZeroHypercover X := ⟨ι, Y, f⟩
  refine ⟨?_, ?_⟩
  · change E.presieve₀ ∈ _
    rw [presieve₀_mem_qcPrecoverage_iff]
    refine ⟨fun {V} hV ↦ ?_⟩
    refine IsCompactOpenCovered.of_isCompact_of_forall_exists_isCompactOpenCovered hV.isCompact
      fun x hx ↦ ?_
    obtain ⟨i, hxi, hiV⟩ := hbasis V x hx
    refine ⟨Set.range (f i), hiV, hxi, ho i, ?_⟩
    have := IsCompactOpenCovered.image (f := fun i ↦ (E.f i : Y i → X)) (i := i) ⊤
      (by simpa using (hc i).isCompact_univ)
    simpa [Set.image_univ] using this
  · rw [ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, hP⟩
    obtain ⟨i, hxi, -⟩ := hbasis ⊤ x trivial
    exact ⟨i, hxi⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Weakly étale covers of the image of a flat morphism: let `a : U ⟶ T` be weakly étale, let
`b : W ⟶ T` be flat and let `φ : W ⟶ U` be a morphism over `T`. There is a family of affine
opens `O i` of `W`, forming a basis of its topology, and of weakly étale morphisms
`h i : U' i ⟶ U` from affine schemes no larger than `U`, such that the fibre product of
`O i ⟶ U` and `h i` is affine with both projections surjective. -/
theorem exists_weaklyEtale_affine_cover_of_flat {T U W : Scheme.{u}} (a : U ⟶ T) (b : W ⟶ T)
    (φ : W ⟶ U) [WeaklyEtale a] [Flat b] (hφ : φ ≫ a = b) :
    ∃ (ι : Type u) (O : ι → W.Opens) (U' : ι → Scheme.{u}) (h : ∀ i, U' i ⟶ U),
      (∀ i, IsAffineOpen (O i)) ∧ (∀ i, IsAffine (U' i)) ∧ (∀ i, WeaklyEtale (h i)) ∧
        (∀ i, (U' i).size ≤ U.size) ∧
        (∀ i, IsAffine (pullback ((O i).ι ≫ φ) (h i))) ∧
        (∀ i, Surjective (pullback.fst ((O i).ι ≫ φ) (h i))) ∧
        (∀ i, Surjective (pullback.snd ((O i).ι ≫ φ) (h i))) ∧
        ∀ (V : W.Opens) (x : W), x ∈ V → ∃ i, x ∈ O i ∧ O i ≤ V := by
  have := flat_hasOfPostcompProperty_weaklyEtale.{u}
  have hcomp : Flat (φ ≫ a) := by rw [hφ]; infer_instance
  have hflat : Flat φ :=
    MorphismProperty.of_postcomp (W' := @WeaklyEtale) _ φ a inferInstance hcomp
  let ι := {p : W.affineOpens × U.affineOpens // (p.1 : W.Opens) ≤ φ ⁻¹ᵁ (p.2 : U.Opens)}
  have key : ∀ i : ι, ∃ (U' : Scheme.{u}) (_ : IsAffine U')
      (h' : U' ⟶ (i.1.2 : U.Opens).toScheme), WeaklyEtale h' ∧
      IsAffine (pullback (φ.resLE _ _ i.2) h') ∧
        Surjective (pullback.fst (φ.resLE _ _ i.2) h') ∧
          Surjective (pullback.snd (φ.resLE _ _ i.2) h') ∧ U'.size ≤ U.size := by
    intro i
    have : IsAffine (i.1.1 : W.Opens).toScheme := i.1.1.2
    have : IsAffine (i.1.2 : U.Opens).toScheme := i.1.2.2
    obtain ⟨U'', hU'', h'', hwe, hpaff, -, hfst, hsnd, hsize⟩ :=
      exists_weaklyEtale_affine_surjective_pullback_and_size_le (𝟙 _) (φ.resLE _ _ i.2)
        (φ.resLE _ _ i.2) (Category.comp_id _)
    refine ⟨U'', hU'', h'', by simpa using hwe, hpaff, hfst, hsnd,
      hsize.trans (Scheme.size_le_of_isOpenImmersion (i.1.2 : U.Opens).ι)⟩
  choose U' hU' h' hwe hpaff hfst hsnd hsize using key
  have hsq : ∀ i : ι, φ.resLE _ _ i.2 ≫ (i.1.2 : U.Opens).ι = (i.1.1 : W.Opens).ι ≫ φ :=
    fun i ↦ Scheme.Hom.resLE_comp_ι _ _
  have hpb : ∀ i : ι, IsPullback (pullback.fst (φ.resLE _ _ i.2) (h' i))
      (pullback.snd (φ.resLE _ _ i.2) (h' i)) ((i.1.1 : W.Opens).ι ≫ φ)
      (h' i ≫ (i.1.2 : U.Opens).ι) := fun i ↦ by
    rw [← hsq i]
    exact IsPullback.of_isLimit (pullbackIsPullbackOfCompMono _ _ _)
  refine ⟨ι, fun i ↦ i.1.1, U', fun i ↦ h' i ≫ (i.1.2 : U.Opens).ι, fun i ↦ i.1.1.2, hU',
    fun i ↦ by have := hwe i; infer_instance, hsize, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · have := hpaff i
    exact IsAffine.of_isIso (hpb i).isoPullback.inv
  · have := hfst i
    rw [← (hpb i).isoPullback_inv_fst]
    infer_instance
  · have := hsnd i
    rw [← (hpb i).isoPullback_inv_snd]
    infer_instance
  · intro V x hx
    obtain ⟨Vu, hVu, hxVu, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens)
      (show φ x ∈ (⊤ : U.Opens) from trivial)
    obtain ⟨O, hO, hxO, hOV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens)
      (show x ∈ V ⊓ φ ⁻¹ᵁ Vu from ⟨hx, hxVu⟩)
    exact ⟨⟨(⟨O, hO⟩, ⟨Vu, hVu⟩), fun y hy ↦ (hOV hy).2⟩, hxO, fun y hy ↦ (hOV hy).1⟩

end AlgebraicGeometry.ProEtale

end
