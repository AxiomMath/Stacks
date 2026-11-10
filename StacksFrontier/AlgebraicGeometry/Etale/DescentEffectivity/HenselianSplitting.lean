module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

/-!
# Splitting an étale scheme over a henselian pair

Let `(A, I)` be a henselian pair and let `U` be a quasi-compact separated étale scheme over
`Spec A` whose closed fibre `U ×_{Spec A} Spec (A ⧸ I)` is finite over `Spec (A ⧸ I)`. Then `U`
splits as a disjoint union `U = U_fin ⊔ U_away` in which `U_fin` is finite over `Spec A` and
`U_away` has no point above `Spec (A ⧸ I)`.

## Main results

* `Stacks.Etale.exists_coprod_isFinite_and_isEmpty_closedFiber` — Stacks Project, Tag 0BTN.
* `Stacks.Etale.exists_coprod_isOpenImmersion_isFinite_etale_and_isEmpty_closedFiber` — the same
  splitting, in which both pieces are open subschemes of `U` and the finite piece is finite étale
  over the base.

## Implementation notes

The finite piece is cut out of the relative normalization `f.normalization`, an affine scheme
integral over `Spec A` containing `U` as an open subscheme, by an idempotent lifted along the
henselian pair (Stacks Project, Tag 09XI).

The disjoint union is expressed by requiring the morphism out of the binary coproduct of the two
pieces to be an isomorphism, and having no points over `Spec (A ⧸ I)` by emptiness of the
corresponding fibre product.

## References

* [Stacks Project, Tag 0BTN](https://stacks.math.columbia.edu/tag/0BTN)
* [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open AlgebraicGeometry

/-- A finite open immersion has clopen image. -/
private lemma isClopen_range_of_isFinite_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsOpenImmersion f] : IsClopen (Set.range f) := by
  have : IsClosedImmersion f := (IsClosedImmersion.iff_isFinite_and_mono f).2
    ⟨inferInstance, inferInstance⟩
  exact ⟨f.isClosedEmbedding.isClosed_range, f.isOpenEmbedding.isOpen_range⟩

/-- Idempotents of an integral algebra over a henselian pair lift along the extended ideal.
This is the integral case of Stacks Project, Tag 09XI. -/
private lemma exists_isIdempotentElem_lift_of_henselianPair
    {A : Type u} [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (e : B ⧸ I.map (algebraMap A B)) (he : IsIdempotentElem e) :
    ∃ b : B, IsIdempotentElem b ∧ Ideal.Quotient.mk _ b = e := by
  have hall : ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.IsIntegral A C],
      InducesBijectionOnIdempotents (I.map (algebraMap A C)) :=
    ((henselianPair_tfae.{u, u} A I).out 1 4).mp hI
  obtain ⟨b, hb⟩ := (hall B).2 ⟨e, he⟩
  exact ⟨b.1, b.2, congrArg Subtype.val hb⟩

/-- A nonempty closed subset of an affine scheme contains a closed point, and the prime of a
closed point contains every ideal contained in the Jacobson radical. -/
private lemma exists_isMaximal_mem_of_isClosed
    {R : Type u} [CommRing R] (s : Set (PrimeSpectrum R)) (hs : IsClosed s)
    (hne : s.Nonempty) (J : Ideal R) (hJ : J ≤ Ring.jacobson R) :
    ∃ (m : Ideal R) (hm : m.IsMaximal),
      (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ s ∧ J ≤ m := by
  obtain ⟨K, hK⟩ := PrimeSpectrum.isClosed_iff_zeroLocus_ideal s |>.mp hs
  have hKne : K ≠ ⊤ := by
    intro h
    subst K
    obtain ⟨x, hx⟩ := hne
    rw [hK] at hx
    have hx' : x.asIdeal = ⊤ := by simpa [PrimeSpectrum.zeroLocus] using hx
    exact x.2.ne_top hx'
  obtain ⟨m, hm, hKm⟩ := (Ideal.ne_top_iff_exists_maximal).mp hKne
  have : m.IsMaximal := hm
  refine ⟨m, hm, ?_, hJ.trans (Ring.jacobson_le_of_isMaximal m)⟩
  rw [hK]
  exact (PrimeSpectrum.mem_zeroLocus ⟨m, hm.isPrime⟩ K).2 hKm

/-- The splitting of Stacks Project, Tag 0BTN, in which moreover the two pieces are open
subschemes of `U` and the finite piece is finite *étale* over the base. -/
lemma exists_coprod_isOpenImmersion_isFinite_etale_and_isEmpty_closedFiber
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (U : Scheme.{u}) (f : U ⟶ Spec (.of A))
    [QuasiCompact f] [IsSeparated f] [Etale f]
    [IsFinite (pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ∃ (Ufin Uaway : Scheme.{u}) (iFin : Ufin ⟶ U) (iAway : Uaway ⟶ U),
      IsIso (coprod.desc iFin iAway) ∧ IsFinite (iFin ≫ f) ∧
        IsEmpty ((pullback (iAway ≫ f)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) ∧
        IsOpenImmersion iFin ∧ IsOpenImmersion iAway ∧ Etale (iFin ≫ f) := by
  classical
  let z : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let T : Scheme.{u} := f.normalization
  let j : U ⟶ T := f.toNormalization
  let π : T ⟶ Spec (.of A) := f.fromNormalization
  have hj : IsOpenImmersion j := inferInstance
  have hπ : IsIntegralHom π := inferInstance
  have hcomp : j ≫ π = f := f.toNormalization_fromNormalization
  have : IsAffine T := isAffine_of_isAffineHom π
  let B := Γ(T, ⊤)
  let α : A →+* B := (π.appTop).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
  let _ : Algebra A B := α.toAlgebra
  have hπeq : π = T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom α) := by
    have hn := Scheme.isoSpec_hom_naturality π
    calc
      π = π ≫ (Spec (.of A)).isoSpec.hom ≫ (Spec (.of A)).isoSpec.inv := by simp
      _ = T.isoSpec.hom ≫ Spec.map (π.appTop) ≫ (Spec (.of A)).isoSpec.inv := by
        rw [← Category.assoc, ← hn]
        simp [Category.assoc]
      _ = T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom α) := by
        rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
        rfl
  have hαint : Algebra.IsIntegral A B := by
    have hsp : IsIntegralHom (Spec.map (CommRingCat.ofHom α)) := by
      have hrw : Spec.map (CommRingCat.ofHom α) = T.isoSpec.inv ≫ π := by
        rw [hπeq, Iso.inv_hom_id_assoc]
      rw [hrw]
      infer_instance
    exact ⟨fun x ↦ IsIntegralHom.SpecMap_iff.mp hsp x⟩
  have hcompSpec : (j ≫ T.isoSpec.hom) ≫ Spec.map (CommRingCat.ofHom α) = f := by
    simpa only [Category.assoc, ← hπeq] using hcomp
  let P := pullback (Spec.map (CommRingCat.ofHom α)) z
  let eP : P ≅ Spec (.of (TensorProduct A B (A ⧸ I))) := pullbackSpecIso A B (A ⧸ I)
  let jZ : pullback f z ⟶ P :=
    pullback.map f z (Spec.map (CommRingCat.ofHom α)) z (j ≫ T.isoSpec.hom)
      (𝟙 _) (𝟙 _) hcompSpec.symm (by simp)
  have hjZfinite : IsFinite jZ := by
    have heq : jZ ≫ pullback.snd (Spec.map (CommRingCat.ofHom α)) z = pullback.snd f z := by
      dsimp [jZ]
      rw [pullback.lift_snd]
      simp
    have : IsFinite (jZ ≫ pullback.snd (Spec.map (CommRingCat.ofHom α)) z) := by
      rw [heq]; infer_instance
    exact IsFinite.of_comp jZ (pullback.snd (Spec.map (CommRingCat.ofHom α)) z)
  have hjZopen : IsOpenImmersion jZ := by
    dsimp [jZ]
    exact Scheme.pullback_map_isOpenImmersion f z (Spec.map (CommRingCat.ofHom α)) z
      (j ≫ T.isoSpec.hom) (𝟙 _) (𝟙 _) hcompSpec.symm (by simp)
  have hcl : IsClopen (Set.range (jZ ≫ eP.hom)) :=
    isClopen_range_of_isFinite_of_isOpenImmersion (jZ ≫ eP.hom)
  obtain ⟨e₀, he₀, hq⟩ := PrimeSpectrum.isClopen_iff.mp hcl
  let qEquiv := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := A) B I
  let eMod := qEquiv.symm e₀
  have heMod : IsIdempotentElem eMod := he₀.map qEquiv.symm.toRingHom
  obtain ⟨b, hb, hred⟩ := exists_isIdempotentElem_lift_of_henselianPair I hI B eMod heMod
  have he₀b : e₀ = algebraMap B (TensorProduct A B (A ⧸ I)) b := by
    calc
      e₀ = qEquiv eMod := by simp [eMod]
      _ = qEquiv (Ideal.Quotient.mk (I.map (algebraMap A B)) b) := by rw [← hred]
      _ = algebraMap B (TensorProduct A B (A ⧸ I)) b := by simp [qEquiv]
  have hePfst : eP.hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap B (TensorProduct A B (A ⧸ I)))) =
      pullback.fst (Spec.map (CommRingCat.ofHom α)) z := by
    change (pullbackSpecIso A B (A ⧸ I)).hom ≫ Spec.map
        (CommRingCat.ofHom (algebraMap B (TensorProduct A B (A ⧸ I)))) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
    exact pullbackSpecIso_hom_fst' A B (A ⧸ I)
  let D₀ : (Spec (.of (TensorProduct A B (A ⧸ I)))).Opens := PrimeSpectrum.basicOpen e₀
  let D_b : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen b
  have hbOpen : Spec.map
      (CommRingCat.ofHom (algebraMap B (TensorProduct A B (A ⧸ I)))) ⁻¹ᵁ D_b = D₀ := by
    apply TopologicalSpace.Opens.ext
    ext p
    change b ∉ Ideal.comap (algebraMap B (TensorProduct A B (A ⧸ I))) p.asIdeal ↔
      e₀ ∉ p.asIdeal
    simp [he₀b]
  have hqOpen : (jZ ≫ eP.hom).opensRange = D₀ := TopologicalSpace.Opens.ext hq
  have hjZfiber : jZ.opensRange = eP.hom ⁻¹ᵁ D₀ := by
    rw [← hqOpen, Scheme.Hom.opensRange_comp, eP.hom.preimage_image_eq]
  have hFiber : (pullback.fst (Spec.map (CommRingCat.ofHom α)) z) ⁻¹ᵁ D_b =
      jZ.opensRange := by
    calc
      (pullback.fst (Spec.map (CommRingCat.ofHom α)) z) ⁻¹ᵁ D_b =
          (eP.hom ≫ Spec.map
            (CommRingCat.ofHom (algebraMap B (TensorProduct A B (A ⧸ I))))) ⁻¹ᵁ D_b := by
            rw [hePfst]
      _ = eP.hom ⁻¹ᵁ D₀ := by
        simpa only [← Scheme.Hom.comp_preimage] using
          congrArg (fun V : (Spec (.of (TensorProduct A B (A ⧸ I)))).Opens => eP.hom ⁻¹ᵁ V) hbOpen
      _ = jZ.opensRange := hjZfiber.symm
  let k : U ⟶ Spec (.of B) := j ≫ T.isoSpec.hom
  have hk : IsOpenImmersion k := inferInstance
  have hjZfst : jZ ≫ pullback.fst (Spec.map (CommRingCat.ofHom α)) z = pullback.fst f z ≫ k := by
    dsimp [jZ, k]
    simp
  have hkfst : ∀ xZ, k (pullback.fst f z xZ) =
      pullback.fst (Spec.map (CommRingCat.ofHom α)) z (jZ xZ) := fun xZ ↦ by
    simpa only [Scheme.Hom.comp_apply] using (congrArg (fun g => g xZ) hjZfst).symm
  have hbClopen : IsClopen (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨b, hb, rfl⟩
  let s : Set (PrimeSpectrum B) := (PrimeSpectrum.basicOpen b : Set _) \ Set.range k.base
  have hsClosed : IsClosed s :=
    hbClopen.1.inter
      (isClosed_compl_iff.mpr k.isOpenEmbedding.isOpen_range)
  have hsEmpty : s = ∅ := by
    by_contra hne
    have hJ : I.map (algebraMap A B) ≤ Ring.jacobson B := by
      have hIA : I ≤ Ring.jacobson A := by
        simpa [Ideal.jacobson_bot] using hI.1
      rw [Ring.jacobson_eq_sInf_isMaximal]
      apply le_sInf
      intro m hm
      have hmmax : m.IsMaximal := by simpa using hm
      have : m.IsMaximal := hmmax
      have hmc : (m.comap (algebraMap A B)).IsMaximal :=
        Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) m
      exact Ideal.map_le_iff_le_comap.mpr
        (hIA.trans (Ring.jacobson_le_of_isMaximal (m.comap (algebraMap A B))))
    obtain ⟨m, hm, hp, hJm⟩ := exists_isMaximal_mem_of_isClosed s hsClosed
      (Set.nonempty_iff_ne_empty.mpr hne) (I.map (algebraMap A B)) hJ
    have : m.IsMaximal := hm
    let p : Spec (.of B) := ⟨m, hm.isPrime⟩
    have hbp : b ∉ m := by simpa [p] using (PrimeSpectrum.mem_basicOpen b p).mp hp.1
    let ρ : B ⧸ I.map (algebraMap A B) →+* B ⧸ m :=
      Ideal.Quotient.lift (I.map (algebraMap A B)) (Ideal.Quotient.mk m)
        (fun x hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hJm hx))
    have _ : Field (B ⧸ m) := Ideal.Quotient.field m
    let qbar : PrimeSpectrum (B ⧸ I.map (algebraMap A B)) :=
      PrimeSpectrum.comap ρ ⟨⊥, inferInstance⟩
    let qRaw : PrimeSpectrum (TensorProduct A B (A ⧸ I)) :=
      PrimeSpectrum.comap qEquiv.symm.toRingHom qbar
    let q : Spec (.of (TensorProduct A B (A ⧸ I))) := ⟨qRaw.asIdeal, qRaw.2⟩
    have hqD₀ : q ∈ D₀ := by
      change e₀ ∉ q.asIdeal
      change eMod ∉ qbar.asIdeal
      change ρ eMod ∉ (⊥ : Ideal (B ⧸ m))
      rw [← hred]
      change Ideal.Quotient.mk m b ≠ 0
      intro hz
      exact hbp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have hmap : q ∈ Spec.map
        (CommRingCat.ofHom (algebraMap B (TensorProduct A B (A ⧸ I)))) ⁻¹ᵁ D_b :=
      hbOpen.symm ▸ hqD₀
    let y : P := eP.inv q
    have hproj : (pullback.fst (Spec.map (CommRingCat.ofHom α)) z) y =
        Spec.map (CommRingCat.ofHom (algebraMap B (TensorProduct A B (A ⧸ I)))) q := by
      rw [← hePfst]
      change (eP.inv ≫ eP.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap B (TensorProduct A B (A ⧸ I))))) q = _
      rw [Iso.inv_hom_id_assoc]
    have hy : y ∈ (pullback.fst (Spec.map (CommRingCat.ofHom α)) z) ⁻¹ᵁ D_b := by
      change (pullback.fst (Spec.map (CommRingCat.ofHom α)) z) y ∈ D_b
      rw [hproj]
      exact hmap
    obtain ⟨xZ, hxZ⟩ := Scheme.Hom.mem_opensRange.mp (hFiber ▸ hy)
    have hxbase : (pullback.fst (Spec.map (CommRingCat.ofHom α)) z) y = p := by
      rw [hproj]
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap B (TensorProduct A B (A ⧸ I))) q.asIdeal = m
      ext a
      change (algebraMap B (TensorProduct A B (A ⧸ I)) a) ∈ q.asIdeal ↔ a ∈ m
      change (qEquiv.symm (algebraMap B (TensorProduct A B (A ⧸ I)) a)) ∈ qbar.asIdeal ↔ a ∈ m
      dsimp only [qbar, PrimeSpectrum.comap]
      change ρ (qEquiv.symm (algebraMap B (TensorProduct A B (A ⧸ I)) a)) ∈
          (⊥ : Ideal (B ⧸ m)) ↔ a ∈ m
      rw [show algebraMap B (TensorProduct A B (A ⧸ I)) a = a ⊗ₜ[A] (1 : A ⧸ I) by simp]
      have hone : (1 : A ⧸ I) = Ideal.Quotient.mk I 1 := rfl
      rw [hone, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
      simp only [ρ, one_smul, Ideal.mem_bot]
      change Ideal.Quotient.mk m a = 0 ↔ a ∈ m
      exact Ideal.Quotient.eq_zero_iff_mem
    have hxrange : p ∈ Set.range k.base := by
      refine ⟨(pullback.fst f z) xZ, ?_⟩
      rw [hkfst, hxZ, hxbase]
    exact hp.2 hxrange
  have hDsubset : ∀ x : PrimeSpectrum B, x ∈ PrimeSpectrum.basicOpen b →
      x ∈ Set.range k.base := fun x hx ↦ by
    by_contra hxk
    exact hsEmpty.subset ⟨hx, hxk⟩
  let UfinO : U.Opens := k ⁻¹ᵁ D_b
  let UawayO : U.Opens := UfinOᶜ
  have hUfinClopen : IsClopen (UfinO : Set U) :=
    hbClopen.preimage k.continuous
  let iFin : UfinO.toScheme ⟶ U := UfinO.ι
  let iAway : UawayO.toScheme ⟶ U := UawayO.ι
  let gFin : UfinO.toScheme ⟶ T := iFin ≫ j
  have hUaway_coe : (UawayO : Set U) = (UfinO : Set U)ᶜ := by
    rw [TopologicalSpace.Opens.coe_compl_eq_interior_compl,
      interior_eq_iff_isOpen.mpr hUfinClopen.1.isOpen_compl]
  let Tfin : T.Opens := T.isoSpec.hom ⁻¹ᵁ D_b
  have hTfin_clopen : IsClopen (Tfin : Set T) :=
    hbClopen.preimage T.isoSpec.hom.continuous
  have hrangeFin : Set.range gFin = Set.range Tfin.ι := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨⟨j u.1, ?_⟩, rfl⟩
      have huD : k u.1 ∈ D_b := u.2
      change T.isoSpec.hom (j u.1) ∈ D_b
      simpa only [k, Scheme.Hom.comp_apply] using huD
    · rintro ⟨x, rfl⟩
      have hxD : T.isoSpec.hom x.1 ∈ D_b := x.2
      obtain ⟨u, hu⟩ := hDsubset (T.isoSpec.hom x.1) hxD
      have hu' : k u = T.isoSpec.hom x.1 := by simpa using hu
      have hju : j u = x.1 := T.isoSpec.hom.injective hu'
      refine ⟨⟨u, ?_⟩, hju⟩
      change k u ∈ D_b
      rw [hu']
      exact hxD
  have hTfinClosedImmersion : IsClosedImmersion Tfin.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      simpa only [Scheme.Opens.range_ι] using hTfin_clopen.1)
  let eFin : UfinO.toScheme ≅ Tfin.toScheme :=
    IsOpenImmersion.isoOfRangeEq gFin Tfin.ι hrangeFin
  have hgFin : IsFinite gFin := by
    have heq : eFin.hom ≫ Tfin.ι = gFin :=
      IsOpenImmersion.isoOfRangeEq_hom_fac gFin Tfin.ι hrangeFin
    rw [← heq]
    infer_instance
  have hfinite : IsFinite (iFin ≫ f) := by
    have heq : gFin ≫ π = iFin ≫ f := by
      dsimp [gFin]
      rw [Category.assoc, hcomp]
    have hint : IsIntegralHom (gFin ≫ π) := inferInstance
    rw [heq] at hint
    rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
    exact ⟨hint, inferInstance⟩
  have hcompl : IsCompl iFin.opensRange iAway.opensRange := by
    simp only [Scheme.Opens.opensRange_ι, iFin, iAway]
    rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    refine ⟨by simp [UawayO], ?_⟩
    apply TopologicalSpace.Opens.ext
    ext x
    simp [hUaway_coe]
  obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl iFin iAway hcompl
  have hcoprod : IsIso (coprod.desc iFin iAway) := by
    let φ : (BinaryCofan.mk (coprod.inl : UfinO.toScheme ⟶ _) coprod.inr) ⟶
        BinaryCofan.mk iFin iAway :=
      { hom := coprod.desc iFin iAway
        w := by
          rintro ⟨_ | _⟩
          · change coprod.inl ≫ coprod.desc iFin iAway = iFin
            exact coprod.inl_desc iFin iAway
          · change coprod.inr ≫ coprod.desc iFin iAway = iAway
            exact coprod.inr_desc iFin iAway }
    have : IsIso φ := IsColimit.hom_isIso (coprodIsCoprod _ _) hc φ
    exact (inferInstance : IsIso ((Cocone.forget _).map φ))
  have hfibreSub : Set.range (pullback.fst f z) ⊆ (UfinO : Set U) := by
    rintro x ⟨xZ, rfl⟩
    change k (pullback.fst f z xZ) ∈ D_b
    have hxD : pullback.fst (Spec.map (CommRingCat.ofHom α)) z (jZ xZ) ∈ D_b := by
      change jZ xZ ∈ (pullback.fst (Spec.map (CommRingCat.ofHom α)) z) ⁻¹ᵁ D_b
      rw [hFiber]
      exact ⟨xZ, rfl⟩
    rw [hkfst]
    exact hxD
  have hdisj : Disjoint (Set.range iAway) (Set.range (pullback.fst f z)) := by
    rw [Set.disjoint_left]
    intro x hxAway hxFin
    have hxAway' : x ∈ (UfinO : Set U)ᶜ := by
      rw [← hUaway_coe]
      simpa [iAway, Scheme.Opens.range_ι] using hxAway
    exact hxAway' (hfibreSub hxFin)
  have hAwayFiberEmpty : IsEmpty (pullback iAway (pullback.fst f z) : Scheme.{u}) :=
    Scheme.isEmpty_pullback iAway (pullback.fst f z) hdisj
  let eAway : pullback iAway (pullback.fst f z) ≅ pullback (iAway ≫ f) z :=
    pullbackRightPullbackFstIso f z iAway
  have hAwayEmpty : IsEmpty (pullback (iAway ≫ f) z : Scheme.{u}) :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso eAway)).toEquiv.isEmpty_congr.mp
      hAwayFiberEmpty
  exact ⟨UfinO.toScheme, UawayO.toScheme, iFin, iAway, hcoprod, hfinite, hAwayEmpty,
    inferInstance, inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 0BTN.** A quasi-compact separated étale scheme over a henselian pair,
with finite closed fibre, is the disjoint union of a finite scheme over the base and a scheme
with empty closed fibre. -/
@[stacks 0BTN]
lemma exists_coprod_isFinite_and_isEmpty_closedFiber
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (U : Scheme.{u}) (f : U ⟶ Spec (.of A))
    [QuasiCompact f] [IsSeparated f] [Etale f]
    [IsFinite (pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ∃ (Ufin Uaway : Scheme.{u}) (iFin : Ufin ⟶ U) (iAway : Uaway ⟶ U),
      IsIso (coprod.desc iFin iAway) ∧ IsFinite (iFin ≫ f) ∧
        IsEmpty ((pullback (iAway ≫ f)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) := by
  obtain ⟨Ufin, Uaway, iFin, iAway, hiso, hfin, hempty, -, -, -⟩ :=
    exists_coprod_isOpenImmersion_isFinite_etale_and_isEmpty_closedFiber A I hI U f
  exact ⟨Ufin, Uaway, iFin, iAway, hiso, hfin, hempty⟩

end Stacks.Etale

end

end
