module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.EtaleSlice
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Section
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.Flat.FiniteFreeResidueExtension

/-!
# A power series chart of a smooth morphism through a point of finite residue degree

Let `f : X ⟶ S` be a smooth morphism with `S` locally Noetherian and let `z ∈ X` be a point closed
in its fibre, so that `κ(z)` is finite over `κ(f(z))`. There are a Noetherian local ring `A`, a
flat morphism `α : Spec A ⟶ S` taking the closed point to `f(z)` and no other point there, and a
flat morphism `φ : Spec A[[t_1, …, t_d]] ⟶ X` over `α` taking the closed point to `z`.

## Main results

* `Stacks.FundamentalGroup.isSeparableExtension_of_bijective_algebraMap` — a trivial field
  extension is separable in the sense of [Stacks, Tag 030O].
* `Stacks.FundamentalGroup.exists_flat_quasiSection_of_isClosed_asFiber` — a point closed in its
  fibre is the image of a point `z₀` of a flat locally Noetherian `S`-scheme mapping to `X` over
  `S`, such that no other generalization of `z₀` lies over the image of `z` in `S`.
* `Stacks.FundamentalGroup.exists_flat_powerSeries_chart` — the power series chart.

## References

* [Stacks Project, Tag 030O](https://stacks.math.columbia.edu/tag/030O)
* [Stacks Project, Tag 057G](https://stacks.math.columbia.edu/tag/057G)
* [Stacks Project, Tag 05D5](https://stacks.math.columbia.edu/tag/05D5)
* [Stacks Project, Tag 05D9](https://stacks.math.columbia.edu/tag/05D9)
* [Stacks Project, Tag 07NE](https://stacks.math.columbia.edu/tag/07NE)
* [Stacks Project, Tag 0EYB](https://stacks.math.columbia.edu/tag/0EYB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.FundamentalGroup

/-- **A trivial field extension is separable** in the sense of [Stacks, Tag 030O]: if the
structure map `k ⟶ K` is bijective, every subextension of `K/k` of finite type is separably
generated. -/
public theorem isSeparableExtension_of_bijective_algebraMap (k K : Type*) [Field k] [Field K]
    [Algebra k K] (h : Function.Bijective (algebraMap k K)) :
    Algebra.IsSeparableExtension k K := by
  refine ⟨fun K' _ => ?_⟩
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K'
  have halg : Algebra.IsAlgebraic k K' := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, ha⟩ := h.2 (x : K)
    have hx : algebraMap k K' a = x := Subtype.ext ha
    rw [← hx]
    exact isAlgebraic_algebraMap a
  refine ⟨s, hs, ⟨fun x => ?_⟩⟩
  obtain ⟨a, ha⟩ := h.2 (x : K)
  have hx : algebraMap k K' a = x := Subtype.ext ha
  rw [← hx, IsScalarTower.algebraMap_apply k (IntermediateField.adjoin k (s : Set K')) K']
  exact isSeparable_algebraMap _

/-- The spectrum map of a flat algebra map is flat. -/
private theorem flat_specMap_algebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- A prime of a finite algebra over a local ring lying over the maximal ideal is maximal. -/
private theorem isMaximal_of_comap_eq_maximalIdeal {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] (q : Ideal S) [q.IsPrime]
    (h : q.comap (algebraMap R S) = maximalIdeal R) : q.IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q
    ((show q.under R = maximalIdeal R from h) ▸ maximalIdeal.isMaximal R)

/-- **A flat quasi-section through a point closed in its fibre.** Let `f : X ⟶ S` be smooth with
`S` locally Noetherian and let `z ∈ X` be closed in its fibre. There are a locally Noetherian
scheme `Z`, a point `z₀ ∈ Z`, a flat `β : Z ⟶ S` and a `γ : Z ⟶ X` over `β`, with `γ(z₀) = z` and
`β(z₀) = f(z)`. Moreover no generalization of `z₀` other than `z₀` itself lies over `f(z)`. -/
public theorem exists_flat_quasiSection_of_isClosed_asFiber {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsLocallyNoetherian S] (z : X)
    (hz : IsClosed ({f.asFiber z} : Set (f.fiber (f z)))) :
    ∃ (Z : Scheme.{u}) (_ : IsLocallyNoetherian Z) (z₀ : Z) (β : Z ⟶ S) (γ : Z ⟶ X),
      Flat β ∧ γ ≫ f = β ∧ γ z₀ = z ∧ β z₀ = f z ∧
      ∀ w : Z, w ⤳ z₀ → β w = f z → w = z₀ := by
  classical
  let s := f z
  let A₀ := S.presheaf.stalk s
  let m₀ := maximalIdeal A₀
  have hfin : (f.residueFieldMap z).hom.Finite :=
    (isClosed_asFiber_iff_finite_residueField f z).mp hz
  let e₀ : ResidueField A₀ ≃+* m₀.ResidueField :=
    RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField m₀)
  let ρ : S.residueField s →+* X.residueField z := (f.residueFieldMap z).hom
  let : Algebra (ResidueFieldAtPrime A₀ m₀) (X.residueField z) :=
    (ρ.comp e₀.symm.toRingHom).toAlgebra
  have : Module.Finite (ResidueFieldAtPrime A₀ m₀) (X.residueField z) :=
    hfin.comp (RingHom.Finite.of_surjective _ e₀.symm.surjective)
  obtain ⟨S₁, _, φ₁, hff, hprime, hpq, Φ, hΦ⟩ :=
    exists_isFiniteFree_residueField_equiv A₀ m₀ (X.residueField z)
  let q₁ : Ideal S₁ := Ideal.map φ₁ m₀
  let : Algebra A₀ S₁ := φ₁.toAlgebra
  have : Module.Free A₀ S₁ := hff.1
  have : Module.Finite A₀ S₁ := hff.2
  have hmax₁ : q₁.IsMaximal := isMaximal_of_comap_eq_maximalIdeal (R := A₀) q₁ hpq.symm
  have : IsNoetherianRing S₁ := IsNoetherianRing.of_finite A₀ S₁
  let χ : S₁ →+* X.residueField z :=
    Φ.toRingHom.comp (algebraMap S₁ (ResidueFieldAtPrime S₁ q₁))
  have hχsurj : Function.Surjective χ := by
    refine Φ.surjective.comp fun y => ?_
    obtain ⟨x, rfl⟩ := (Ideal.bijective_algebraMap_quotient_residueField q₁).2 y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, rfl⟩
  have hχker : RingHom.ker χ = q₁ := by
    rw [RingHom.ker_comp_of_injective _ Φ.injective, Ideal.ker_algebraMap_residueField]
  have hχφ : ∀ a : A₀, χ (φ₁ a) = ρ (IsLocalRing.residue A₀ a) := by
    intro a
    have h1 := inducedResidueMap_algebraMap φ₁ m₀ q₁ hpq a
    have h2 := RingHom.congr_fun hΦ (algebraMap A₀ (ResidueFieldAtPrime A₀ m₀) a)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] at h2
    rw [h1] at h2
    show Φ (algebraMap S₁ (ResidueFieldAtPrime S₁ q₁) (φ₁ a)) = _
    rw [IsScalarTower.algebraMap_apply S₁ (S₁ ⧸ q₁) (ResidueFieldAtPrime S₁ q₁)]
    refine h2.trans ?_
    show ρ (e₀.symm (algebraMap A₀ (ResidueFieldAtPrime A₀ m₀) a)) = _
    congr 1
    apply e₀.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  let α₁ : Spec (.of S₁) ⟶ S := Spec.map (CommRingCat.ofHom φ₁) ≫ S.fromSpecStalk s
  have : Flat (Spec.map (CommRingCat.ofHom φ₁)) := flat_specMap_algebraMap A₀ S₁
  have : Flat (S.fromSpecStalk s) := flat_fromSpecStalk S s
  have : Flat α₁ := inferInstance
  let X₁ := pullback f α₁
  let f₁ : X₁ ⟶ Spec (.of S₁) := pullback.snd f α₁
  have : Smooth f₁ :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f α₁) inferInstance
  have hw : X.fromSpecResidueField z ≫ f = Spec.map (CommRingCat.ofHom χ) ≫ α₁ := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [α₁, Scheme.fromSpecResidueField, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact (hχφ a).symm
  let ψ : Spec (X.residueField z) ⟶ X₁ :=
    pullback.lift (X.fromSpecResidueField z) (Spec.map (CommRingCat.ofHom χ)) hw
  let z₁ : X₁ := ψ (IsLocalRing.closedPoint (X.residueField z))
  have hz₁ : pullback.fst f α₁ z₁ = z := by
    have h1 : ψ ≫ pullback.fst f α₁ = X.fromSpecResidueField z := pullback.lift_fst _ _ _
    exact ((Scheme.Hom.comp_apply ψ (pullback.fst f α₁) _).symm.trans
      (congrArg (fun g : Spec (X.residueField z) ⟶ X => g _) h1)).trans
      (Scheme.fromSpecResidueField_apply z _)
  let s₁ : Spec (.of S₁) := ⟨q₁, hmax₁.isPrime⟩
  have hψ : ψ ≫ f₁ = Spec.map (CommRingCat.ofHom χ) := pullback.lift_snd _ _ _
  have hs₁ : f₁ z₁ = s₁ := by
    refine ((Scheme.Hom.comp_apply ψ f₁ _).symm.trans
      (congrArg (fun g : Spec (X.residueField z) ⟶ Spec (.of S₁) => g _) hψ)).trans ?_
    refine PrimeSpectrum.ext ?_
    show (maximalIdeal (X.residueField z)).comap χ = q₁
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hχker]
  have hDsurj : Function.Surjective
      (@Scheme.descResidueField _ _ _ _ (Scheme.stalkClosedPointTo (ψ ≫ f₁))
        (Scheme.isLocalHom_stalkClosedPointTo _)).hom := by
    have key : ∀ g : Spec (X.residueField z) ⟶ Spec (.of S₁),
        g = Spec.map (CommRingCat.ofHom χ) →
          Function.Surjective (@Scheme.descResidueField _ _ _ _ (Scheme.stalkClosedPointTo g)
            (Scheme.isLocalHom_stalkClosedPointTo g)).hom := by
      intro g hg
      have h1 := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk g).trans hg
      rw [Spec.fromSpecStalk_eq, ← Spec.map_comp, Spec.map_inj] at h1
      intro y
      obtain ⟨a, rfl⟩ := hχsurj y
      refine ⟨(Spec (.of S₁)).residue _ (((Scheme.ΓSpecIso (.of S₁)).inv ≫
        (Spec (.of S₁)).presheaf.germ ⊤ _ trivial).hom a), ?_⟩
      have h2 := congrArg (fun φ => φ.hom a) h1
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 ⊢
      rw [← h2]
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (@Scheme.residue_descResidueField _ _ _ _ (Scheme.stalkClosedPointTo g)
          (Scheme.isLocalHom_stalkClosedPointTo g))) _
    exact key _ hψ
  have hδ := Scheme.descResidueField_stalkClosedPointTo_comp (f := f₁) ψ
  have hres : Function.Bijective (f₁.residueFieldMap z₁).hom := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨x, hx⟩ := hDsurj
      ((@Scheme.descResidueField _ _ _ _ (Scheme.stalkClosedPointTo ψ)
        (Scheme.isLocalHom_stalkClosedPointTo ψ)).hom y)
    have hδ' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hδ) x
    exact ⟨x, RingHom.injective
      (@Scheme.descResidueField _ _ _ _ (Scheme.stalkClosedPointTo ψ)
        (Scheme.isLocalHom_stalkClosedPointTo ψ)).hom (hδ'.symm.trans hx)⟩
  let := (f₁.residueFieldMap z₁).hom.toAlgebra
  have halg : Algebra.IsAlgebraic ((Spec (.of S₁)).residueField (f₁ z₁)) (X₁.residueField z₁) :=
    ⟨fun x => by
      obtain ⟨a, rfl⟩ := hres.2 x
      exact isAlgebraic_algebraMap a⟩
  have hclosed := isClosed_asFiber_of_isAlgebraic_residueField f₁ z₁ halg
  have hsep := isSeparableExtension_of_bijective_algebraMap
    ((Spec (.of S₁)).residueField (f₁ z₁)) (X₁.residueField z₁) hres
  obtain ⟨Z, i, z₀, hi, hiz, het, hfib⟩ :=
    Stacks.AlgebraicGeometry.exists_etale_immersion_with_singleton_fiber f₁ z₁
      (InfinitesimalLifting.smoothAt_of_smooth f₁ z₁) hclosed hsep
  have : IsImmersion i := hi
  have : Etale (i ≫ f₁) := het
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f₁)
  have hα₁s₁ : α₁ s₁ = s := by
    have hcomap : (Spec.map (CommRingCat.ofHom φ₁)) s₁ = IsLocalRing.closedPoint A₀ := by
      refine PrimeSpectrum.ext ?_
      show q₁.comap φ₁ = maximalIdeal A₀
      exact hpq.symm
    show S.fromSpecStalk s ((Spec.map (CommRingCat.ofHom φ₁)) s₁) = s
    rw [hcomap]
    exact Scheme.fromSpecStalk_closedPoint
  refine ⟨Z, inferInstance, z₀, i ≫ f₁ ≫ α₁, i ≫ pullback.fst f α₁, ?_, ?_, ?_, ?_, ?_⟩
  · have : Flat (i ≫ f₁) := inferInstance
    rw [← Category.assoc]
    infer_instance
  · rw [Category.assoc, pullback.condition]
  · rw [Scheme.Hom.comp_apply, hiz, hz₁]
  · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hiz, hs₁, hα₁s₁]
  · intro w hw hβ
    let u := (i ≫ f₁) w
    have hu : u ⤳ s₁ := by
      have := hw.map (i ≫ f₁).continuous
      rwa [Scheme.Hom.comp_apply (x := z₀), hiz, hs₁] at this
    have huA : (Spec.map (CommRingCat.ofHom φ₁)) u = IsLocalRing.closedPoint A₀ := by
      apply (S.fromSpecStalk s).isEmbedding.injective
      rw [Scheme.fromSpecStalk_closedPoint]
      show ((i ≫ f₁) ≫ α₁) w = s
      rwa [Category.assoc]
    have : u.asIdeal.IsPrime := u.isPrime
    have humax : u.asIdeal.IsMaximal :=
      isMaximal_of_comap_eq_maximalIdeal (R := A₀) u.asIdeal (congrArg PrimeSpectrum.asIdeal huA)
    have hus : u = s₁ := by
      refine PrimeSpectrum.ext (humax.eq_of_le hmax₁.ne_top ?_)
      exact (PrimeSpectrum.le_iff_specializes u s₁).2 hu
    have hmem : w ∈ {z' : Z | (i ≫ f₁) z' = f₁ z₁} := by
      show u = f₁ z₁
      rw [hus, hs₁]
    rw [hfib] at hmem
    exact hmem

/-- In the spectrum of a local ring, the only point to which the closed point specializes is the
closed point itself. -/
private theorem eq_closedPoint_of_closedPoint_specializes {R : Type u} [CommRing R]
    [IsLocalRing R] {p : PrimeSpectrum R} (h : IsLocalRing.closedPoint R ⤳ p) :
    p = IsLocalRing.closedPoint R :=
  PrimeSpectrum.ext ((IsLocalRing.le_maximalIdeal p.isPrime.ne_top).antisymm
    ((PrimeSpectrum.le_iff_specializes _ _).2 h))

/-- **A power series chart of a smooth morphism through a point closed in its fibre.** Let
`f : X ⟶ S` be smooth with `S` locally Noetherian and let `z ∈ X` be closed in its fibre. There
are a Noetherian local ring `A`, a flat `α : Spec A ⟶ S` sending the closed point, and only the
closed point, to `f(z)`, an integer `d`, and a flat `φ : Spec A[[t_1, …, t_d]] ⟶ X` lying over
`α` and sending the closed point to `z`. -/
public theorem exists_flat_powerSeries_chart {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [IsLocallyNoetherian S] (z : X) (hz : IsClosed ({f.asFiber z} : Set (f.fiber (f z)))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsNoetherianRing A) (d : ℕ)
      (α : Spec (.of A) ⟶ S) (φ : Spec (.of (MvPowerSeries (Fin d) A)) ⟶ X),
      Flat α ∧ Flat φ ∧ α (IsLocalRing.closedPoint A) = f z ∧
      (∀ t, α t = f z → t = IsLocalRing.closedPoint A) ∧
      φ ≫ f = Spec.map (CommRingCat.ofHom MvPowerSeries.C) ≫ α ∧
      φ (IsLocalRing.closedPoint (MvPowerSeries (Fin d) A)) = z := by
  classical
  obtain ⟨Z, _, z₀, β, γ, hβflat, hγ, hγz, hβz, hq⟩ :=
    exists_flat_quasiSection_of_isClosed_asFiber f z hz
  let A'' := Z.presheaf.stalk z₀
  let ι := Z.fromSpecStalk z₀
  have : Flat ι := flat_fromSpecStalk Z z₀
  let α'' : Spec A'' ⟶ S := ι ≫ β
  let τ : Spec A'' ⟶ X := ι ≫ γ
  have hτ : τ ≫ f = α'' := by rw [Category.assoc, hγ]
  have : Flat α'' := inferInstance
  have hα''c : α'' (IsLocalRing.closedPoint A'') = f z :=
    (Scheme.Hom.comp_apply ι β _).trans (by rw [Scheme.fromSpecStalk_closedPoint, hβz])
  have hτc : τ (IsLocalRing.closedPoint A'') = z :=
    (Scheme.Hom.comp_apply ι γ _).trans (by rw [Scheme.fromSpecStalk_closedPoint, hγz])
  have hα''q : ∀ t, α'' t = f z → t = IsLocalRing.closedPoint A'' := by
    intro t ht
    have hmem : ι t ∈ Set.range ι := Set.mem_range_self t
    rw [Scheme.range_fromSpecStalk] at hmem
    have h1 : ι t = z₀ := hq _ hmem ((Scheme.Hom.comp_apply ι β t).symm.trans ht)
    apply ι.isEmbedding.injective
    rw [h1, Scheme.fromSpecStalk_closedPoint]
  have hsq : IsPullback (pullback.fst f α'') (pullback.snd f α'') f α'' :=
    IsPullback.of_hasPullback f α''
  let X'' := pullback f α''
  let f'' : X'' ⟶ Spec A'' := pullback.snd f α''
  have : Smooth f'' := MorphismProperty.of_isPullback hsq inferInstance
  have : Flat (pullback.fst f α'') := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : IsLocallyNoetherian X'' := LocallyOfFiniteType.isLocallyNoetherian f''
  let σ : Spec A'' ⟶ X'' := pullback.lift τ (𝟙 _) (by rw [hτ, Category.id_comp])
  have hσ : σ ≫ f'' = 𝟙 _ := pullback.lift_snd _ _ _
  have hσfst : σ ≫ pullback.fst f α'' = τ := pullback.lift_fst _ _ _
  obtain ⟨U, V, hU, hV, hsU, hσV, hVU, hUV, sectionHom, hsec, hfree, ⟨eAdic₀⟩⟩ :=
    exists_affineOpens_free_conormal_powerSeries f'' σ hσ (IsLocalRing.closedPoint A'')
      (InfinitesimalLifting.smoothAt_of_smooth f'' _)
  have hUtop : U = ⊤ := by
    refine eq_top_iff.mpr fun t _ => ?_
    exact (IsLocalRing.specializes_closedPoint t).mem_open U.isOpen hsU
  subst hUtop
  let A := Γ(Spec A'', ⊤)
  let eΓ : A ≃+* A'' := (Scheme.ΓSpecIso A'').commRingCatIsoToRingEquiv
  have : Nontrivial A := eΓ.toEquiv.nontrivial
  have : IsLocalRing A := IsLocalRing.of_surjective' eΓ.symm.toRingHom eΓ.symm.surjective
  have : IsNoetherianRing A := isNoetherianRing_of_ringEquiv A'' eΓ.symm
  have hfromc : hU.fromSpec (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint A'' := by
    refine eq_closedPoint_of_closedPoint_specializes ?_
    obtain ⟨t, ht⟩ : IsLocalRing.closedPoint A'' ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]; trivial
    rw [← ht]
    exact (IsLocalRing.specializes_closedPoint t).map hU.fromSpec.continuous
  have : IsNoetherianRing Γ(X'', V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : Algebra A Γ(X'', V) := (f''.appLE ⊤ V hVU).hom.toAlgebra
  let I := RingHom.ker sectionHom.toRingHom
  obtain ⟨d, ⟨eAdic⟩⟩ : ∃ d : ℕ,
      Nonempty (AdicCompletion I Γ(X'', V) ≃ₐ[A] MvPowerSeries (Fin d) A) := ⟨_, ⟨eAdic₀⟩⟩
  let e₁ := eAdic.toRingEquiv.toCommRingCatIso
  let α : Spec (.of A) ⟶ S := hU.fromSpec ≫ α''
  let φ := Spec.map e₁.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X'', V) (AdicCompletion I Γ(X'', V)))) ≫
      hV.fromSpec ≫ pullback.fst f α''
  have hφα : φ ≫ f = Spec.map (CommRingCat.ofHom MvPowerSeries.C) ≫ α := by
    have h1 : hV.fromSpec ≫ pullback.fst f α'' ≫ f =
        Spec.map (f''.appLE ⊤ V hVU) ≫ hU.fromSpec ≫ α'' := by
      rw [pullback.condition, ← Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f'' hU hV hVU,
        Category.assoc]
    simp only [φ, α, Category.assoc]
    rw [h1, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show eAdic (algebraMap A (AdicCompletion I Γ(X'', V)) a) = _
    rw [AlgEquiv.commutes, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    rfl
  let mB : Ideal Γ(X'', V) := RingHom.ker ((IsLocalRing.residue A).comp sectionHom.toRingHom)
  have hsecsurj : Function.Surjective sectionHom :=
    fun a => ⟨algebraMap A Γ(X'', V) a, sectionHom.commutes a⟩
  have hmB : mB.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _
      (IsLocalRing.residue_surjective.comp hsecsurj)
  have hImB : I ≤ mB := fun x hx => by
    show IsLocalRing.residue A (sectionHom x) = 0
    rw [show sectionHom x = 0 from hx, map_zero]
  have : Nontrivial (AdicCompletion I Γ(X'', V)) := eAdic.toEquiv.nontrivial
  have : IsLocalRing (AdicCompletion I Γ(X'', V)) :=
    IsLocalRing.of_surjective' eAdic.symm.toRingEquiv.toRingHom eAdic.symm.surjective
  have hmaxmap := AdicCompletion.isMaximal_map_of_le I mB hImB (Ideal.fg_of_isNoetherianRing I)
  have hmaxAdic : maximalIdeal (AdicCompletion I Γ(X'', V)) =
      mB.map (algebraMap Γ(X'', V) (AdicCompletion I Γ(X'', V))) :=
    (IsLocalRing.eq_maximalIdeal hmaxmap).symm
  have : (mB.map (algebraMap Γ(X'', V) (AdicCompletion I Γ(X'', V)))).IsPrime := hmaxmap.isPrime
  let pT : Spec (.of (MvPowerSeries (Fin d) A)) :=
    IsLocalRing.closedPoint (MvPowerSeries (Fin d) A)
  let pAdic : Spec (.of (AdicCompletion I Γ(X'', V))) :=
    IsLocalRing.closedPoint (AdicCompletion I Γ(X'', V))
  let pA : Spec Γ(Spec A'', ⊤) := IsLocalRing.closedPoint A
  let pA'' : Spec A'' := IsLocalRing.closedPoint A''
  have h4 : (Spec.map e₁.hom) pT = pAdic := by
    refine PrimeSpectrum.ext ?_
    show (maximalIdeal _).comap e₁.hom.hom = _
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ (ConcreteCategory.bijective_of_isIso e₁.hom).2)
  have h5 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X'', V) (AdicCompletion I Γ(X'', V)))))
      pAdic = ⟨mB, hmB.isPrime⟩ := by
    refine PrimeSpectrum.ext ?_
    show (maximalIdeal _).comap (algebraMap Γ(X'', V) (AdicCompletion I Γ(X'', V))) = mB
    rw [hmaxAdic]
    exact (hmB.eq_of_le (Ideal.IsPrime.comap _).ne_top Ideal.le_comap_map).symm
  have h6 : hV.fromSpec ⟨mB, hmB.isPrime⟩ = σ pA'' := by
    have hsq6 := IsAffineOpen.SpecMap_appLE_fromSpec σ hV hU hUV
    have hpt : (Spec.map (σ.appLE V ⊤ hUV)) pA = ⟨mB, hmB.isPrime⟩ := by
      refine PrimeSpectrum.ext ?_
      show (maximalIdeal A).comap (σ.appLE V ⊤ hUV).hom = mB
      rw [← hsec]
      ext x
      simp [mB, IsLocalRing.residue_eq_zero_iff]
    rw [← hpt]
    exact (Scheme.Hom.comp_apply _ _ pA).symm.trans
      ((congrArg (fun g : Spec Γ(Spec A'', ⊤) ⟶ X'' => g pA) hsq6).trans
        ((Scheme.Hom.comp_apply _ _ pA).trans (congrArg σ hfromc)))
  have hφc : φ pT = z := by
    show (pullback.fst f α'') (hV.fromSpec ((Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X'', V) (AdicCompletion I Γ(X'', V))))) ((Spec.map e₁.hom) pT))) = z
    rw [h4, h5, h6]
    exact (Scheme.Hom.comp_apply σ _ pA'').symm.trans
      ((congrArg (fun g : Spec A'' ⟶ X => g pA'') hσfst).trans hτc)
  have : Flat α := inferInstance
  have : Flat φ := by
    have := flat_specMap_algebraMap Γ(X'', V) (AdicCompletion I Γ(X'', V))
    infer_instance
  refine ⟨A, inferInstance, inferInstance, inferInstance, d, α, φ, inferInstance, inferInstance,
    ?_, ?_, hφα, hφc⟩
  · exact (Scheme.Hom.comp_apply hU.fromSpec α'' pA).trans ((congrArg α'' hfromc).trans hα''c)
  · intro t ht
    have h1 : hU.fromSpec t = pA'' :=
      hα''q _ ((Scheme.Hom.comp_apply hU.fromSpec α'' t).symm.trans ht)
    exact hU.fromSpec.isOpenEmbedding.injective (h1.trans hfromc.symm)

end Stacks.FundamentalGroup

end
