module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TopDifferentialStein
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleLocalSection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Open
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import Mathlib.AlgebraicGeometry.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The top de Rham differential: reduction to morphisms with a section

Let `g : Y ⟶ Spec B` be proper, surjective and smooth of relative dimension `n` with
`B ⟶ Γ(Y, 𝒪_Y)` bijective. By [Stacks, Tag 055U] there are finitely many affine schemes
`Spec Rᵢ` étale over `Spec B`, jointly surjective, over each of which `g` has a section. With
`B' = ∏ Rᵢ`, the map `B ⟶ B'` is faithfully flat and étale, the base change `Y' ⟶ Spec B'` of `g`
has a section, and `B' ⟶ Γ(Y', 𝒪_{Y'})` is bijective by flat base change
([Stacks, Tag 02KH]). Vanishing of `d : H^n(Y, Ω^{n-1}) ⟶ H^n(Y, Ω^n)` descends along
`B ⟶ B'`, so it suffices to treat morphisms with a section: this is the second step of the proof
of [Stacks, Tag 0G8J].

## Main results

* `AlgebraicGeometry.exists_affine_etale_section_of_smooth`: affine étale local sections of a
  smooth morphism through a point of its image.
* `AlgebraicGeometry.exists_finite_affine_etale_sections_of_smooth`: finitely many of them cover
  the base of a smooth surjective morphism to a quasi-compact scheme.
* `AlgebraicGeometry.TopDegreeDifferential.topDifferentialVanishes_of_section_of_mem`: the
  reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Affine étale local sections of a smooth morphism** ([Stacks, Tag 055U]): through every
point `s` of the image of a smooth `f : X ⟶ S` there is an affine scheme `Spec R` étale over `S`,
with `s` in its image, over which `f` has a section. -/
theorem exists_affine_etale_section_of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (s : S)
    (hs : s ∈ Set.range f.base) :
    ∃ (R : CommRingCat.{u}) (e : Spec R ⟶ S) (_ : Etale e) (σ : Spec R ⟶ X),
      σ ≫ f = e ∧ s ∈ Set.range e.base := by
  obtain ⟨W, σ, hσ⟩ := exists_etaleNeighborhood_lift_of_smooth f s hs
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := W.scheme) (x := W.point) (U := ⊤) trivial
  refine ⟨Γ(W.scheme, V), hV.fromSpec ≫ W.toBase, inferInstance, hV.fromSpec ≫ σ,
    by rw [Category.assoc, hσ], ?_⟩
  obtain ⟨y, hy⟩ : W.point ∈ Set.range hV.fromSpec.base := by rwa [hV.range_fromSpec]
  exact ⟨y, by rw [Scheme.Hom.comp_apply, hy, W.map_point]⟩

/-- **Finitely many affine étale local sections cover the base** of a smooth surjective morphism
to a quasi-compact scheme. -/
@[sga "7 XII 1.2" "more general"]
theorem exists_finite_affine_etale_sections_of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [Surjective f] [CompactSpace S] :
    ∃ (ι : Type u) (_ : Finite ι) (R : ι → CommRingCat.{u}) (e : ∀ i, Spec (R i) ⟶ S)
      (_ : ∀ i, Etale (e i)) (σ : ∀ i, Spec (R i) ⟶ X),
      (∀ i, σ i ≫ f = e i) ∧ ⋃ i, Set.range (e i).base = Set.univ := by
  choose R e he σ hσ hs using
    fun s : S => exists_affine_etale_section_of_smooth f s (f.surjective s)
  have hopen : ∀ s, IsOpen (Set.range (e s).base) := fun s =>
    have := he s; (e s).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s => Set.range (e s).base) hopen
    (fun s _ => Set.mem_iUnion.2 ⟨s, hs s⟩)
  refine ⟨t, inferInstance, fun i => R i, fun i => e i, fun i => he i, fun i => σ i,
    fun i => hσ i, Set.eq_univ_of_forall fun x => ?_⟩
  obtain ⟨s, hst, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact Set.mem_iUnion.2 ⟨⟨s, hst⟩, hx⟩

namespace TopDegreeDifferential

/-- **Descent of the top de Rham differential along a faithfully flat `B ⟶ B'`** through which
`g : Y ⟶ Spec B` has a lift `Spec B' ⟶ Y`: if `d` vanishes for every proper `Y' ⟶ Spec B'` smooth
of relative dimension `m + 1` with a section and with `B' ⟶ Γ(Y', 𝒪_{Y'})` bijective, then it
vanishes for `g`. -/
private theorem topDifferentialVanishes_succ_of_faithfullyFlat_of_lift
    {B B' : CommRingCat.{u}} (φ : B ⟶ B') (hφ : φ.hom.FaithfullyFlat) (m : ℕ) {Y : Scheme.{u}}
    (g : Y ⟶ Spec B) [IsProper g] [SmoothOfRelativeDimension (m + 1) g] [IsIso g.appTop]
    (σ₀ : Spec B' ⟶ Y) (hσ₀ : σ₀ ≫ g = Spec.map φ)
    (h : ∀ (Y' : Scheme.{u}) (f' : Y' ⟶ Spec B') [IsProper f']
      [SmoothOfRelativeDimension (m + 1) f'] [IsIso f'.appTop] (σ : Spec B' ⟶ Y'),
      σ ≫ f' = 𝟙 _ → TopDifferentialVanishes f' (m + 1)) :
    TopDifferentialVanishes g (m + 1) := by
  have : CompactSpace Y := (quasiCompact_iff_compactSpace g).1 inferInstance
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  have : Flat (Spec.map φ) := (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.1 hφ).1
  let f' := pullback.snd g (Spec.map φ)
  have hsq := IsPullback.of_hasPullback g (Spec.map φ)
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := m + 1)
  have : IsProper f' :=
    MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : SmoothOfRelativeDimension (m + 1) f' :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension (m + 1)) hsq inferInstance
  have : IsIso f'.appTop := by
    have hΓ := Stacks.Descent.isPullback_SpecMap_appTop_of_isPullback_of_flat hsq
    have : IsIso (Spec.map f'.appTop) := hΓ.isIso_fst_of_isIso
    exact (ConcreteCategory.isIso_iff_bijective _).2 (isIso_SpecMap_iff.1 inferInstance)
  exact rightDerived_map_deRham_d_eq_zero_of_faithfullyFlat φ.hom hφ g f' _ hsq m m
    (h _ f' (pullback.lift σ₀ (𝟙 _) (by rw [hσ₀, Category.id_comp])) (pullback.lift_snd _ _ _))

/-- **Reduction of the top de Rham differential to morphisms with a section** (the étale-local
step of [Stacks, Tag 0G8J]), within a class `P` of rings stable under ring maps of finite type.
If `d : H^n(Y, Ω^{n-1}_{Y/B}) ⟶ H^n(Y, Ω^n_{Y/B})` vanishes for every proper `Y ⟶ Spec B` smooth
of relative dimension `n` with `B` in `P`, with a section and with `B ⟶ Γ(Y, 𝒪_Y)` bijective, then
it vanishes for every such morphism which is surjective, with or without a section. -/
theorem topDifferentialVanishes_of_section_of_mem (P : CommRingCat.{u} → Prop)
    (hP : ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B), P A → φ.hom.FiniteType → P B) (n : ℕ)
    (h : ∀ (B : CommRingCat.{u}), P B → ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec B) [IsProper g]
      [SmoothOfRelativeDimension n g] [IsIso g.appTop] (σ : Spec B ⟶ Y), σ ≫ g = 𝟙 _ →
      TopDifferentialVanishes g n)
    {B : CommRingCat.{u}} (hB : P B) {Y : Scheme.{u}} (g : Y ⟶ Spec B) [IsProper g]
    [SmoothOfRelativeDimension n g] [Surjective g] [IsIso g.appTop] :
    TopDifferentialVanishes g n := by
  cases n with
  | zero => exact topDifferentialVanishes_zero g
  | succ m =>
  have : Smooth g := SmoothOfRelativeDimension.smooth (m + 1) g
  obtain ⟨ι, _, R, e, he, σ, hσ, hcov⟩ := exists_finite_affine_etale_sections_of_smooth g
  let ψ : ∀ i, B ⟶ R i := fun i => Spec.preimage (e i)
  have hψ : ∀ i, Spec.map (ψ i) = e i := fun i => Spec.map_preimage (e i)
  let B' : CommRingCat.{u} := .of (Π i, R i)
  let φ : B ⟶ B' := CommRingCat.ofHom (Pi.ringHom fun i => (ψ i).hom)
  have hev : ∀ i, Sigma.ι (fun i => Spec (R i)) i ≫ sigmaSpec R ≫ Spec.map φ = e i := by
    intro i
    rw [ι_sigmaSpec_assoc, ← Spec.map_comp, ← hψ i]
    rfl
  have hdesc : Spec.map φ = inv (sigmaSpec R) ≫ Sigma.desc e := by
    rw [IsIso.eq_inv_comp]
    exact Sigma.hom_ext _ _ fun i => (hev i).trans (Sigma.ι_desc _ _).symm
  have hψet : ∀ i, RingHom.Etale (ψ i).hom := fun i =>
    (HasRingHomProperty.Spec_iff (P := @Etale)).1 (by rw [hψ i]; exact he i)
  have hφet : φ.hom.Etale := by
    let : ∀ i, Algebra B (R i) := fun i => (ψ i).hom.toAlgebra
    have : ∀ i, Algebra.Etale B (R i) := hψet
    exact (inferInstance : Algebra.Etale B (Π i, R i))
  have : Etale (Spec.map φ) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 hφet
  have hB' : P B' := by
    refine hP φ hB ?_
    algebraize [φ.hom]
    exact (inferInstance : Algebra.FiniteType B B')
  have : Surjective (Sigma.desc e) := Surjective.sigmaDesc_of_union_range_eq_univ hcov
  have : Surjective (Spec.map φ) := hdesc ▸ inferInstance
  have hφ : φ.hom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2
      ⟨HasRingHomProperty.Spec_iff (P := @Flat).1 inferInstance, (Spec.map φ).surjective⟩
  refine topDifferentialVanishes_succ_of_faithfullyFlat_of_lift φ hφ m g
    (inv (sigmaSpec R) ≫ Sigma.desc σ) ?_ (h B' hB')
  rw [hdesc, Category.assoc]
  congr 1
  exact Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_desc_assoc, Sigma.ι_desc, hσ i]

/-- **The top de Rham differential vanishes on `H^n` over affine bases, from the case of a
section**, within a class `P` of rings stable under ring maps of finite type: if
`d : H^n(Y, Ω^{n-1}_{Y/B}) ⟶ H^n(Y, Ω^n_{Y/B})` vanishes for every proper `Y ⟶ Spec B` smooth of
relative dimension `n` with `B` in `P`, with a section and with `B ⟶ Γ(Y, 𝒪_Y)` bijective, then it
vanishes for every proper `Y ⟶ Spec A` smooth of relative dimension `n` with `A` in `P`. -/
theorem topDifferentialVanishes_of_section_of_affine_of_mem (P : CommRingCat.{u} → Prop)
    (hP : ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B), P A → φ.hom.FiniteType → P B) (n : ℕ)
    (h : ∀ (B : CommRingCat.{u}), P B → ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec B) [IsProper g]
      [SmoothOfRelativeDimension n g] [IsIso g.appTop] (σ : Spec B ⟶ Y), σ ≫ g = 𝟙 _ →
      TopDifferentialVanishes g n)
    {A : CommRingCat.{u}} (hA : P A) {Y : Scheme.{u}} (g : Y ⟶ Spec A) [IsProper g]
    [SmoothOfRelativeDimension n g] : TopDifferentialVanishes g n :=
  topDifferentialVanishes_of_isIso_appTop_of_mem P hP n
    (fun _ hB _ g _ _ _ _ => topDifferentialVanishes_of_section_of_mem P hP n h hB g) hA g

end TopDegreeDifferential

end AlgebraicGeometry
