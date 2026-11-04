module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.CategoryTheory.Sites.JointlyLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleModWeakIdeal
public import StacksFrontier.Topology.Algebra.AdicTopology.FaithfullyFlatModWeakIdeal

/-!
# A jointly surjective family of completed étale charts of `Spf R` has a finite subfamily

Let `S` be a scheme contained in a big fppf site `B` and let `R` be a weakly admissible
topological ring presented over `S`. Let `{Spf (Cₖ^∧) ⟶ Spf R}` be a family of formal spectra
of completions of étale `R`-algebras `Cₖ`, jointly surjective as a family of morphisms of fppf
sheaves. Then finitely many of the `Cₖ` already make `R → ∏ₖ Cₖ` faithfully flat.

This is the quasi-compactness of an affine formal algebraic space used in the proof of Stacks
0ANG to cut a covering of a chart down to a finite one.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_prime_comap_eq_of_isLocallySurjective`: every prime of
  `R` containing a weak ideal of definition lies under a prime of one of the `Cₖ`.
* `AlgebraicGeometry.FormalSpace.exists_finite_faithfullyFlat_of_isLocallySurjective`: the finite
  subfamily.

## Implementation notes

The canonical section of `Spf R` over a stage `T = Spec (R ⧸ J)` lies, locally on `T`, in the
image of a member of the family. A point of `T` is met by such a local piece, which may be
taken affine; there the lifted section factors through a stage of `Spf (Cₖ^∧)` (Stacks 0AIA),
and comparing the two resulting maps to stages of `Spf R` — they agree in `Spf R`, and the
stage inclusions are monomorphisms — gives a prime of `Cₖ^∧`, hence of `Cₖ`, over the point.
The images of `Spec (Cₖ ⧸ J Cₖ) ⟶ Spec (R ⧸ J)` are open (an étale map is open), so compactness
of `Spec (R ⧸ J)` gives finitely many of them covering it; the maximal ideals of `R` contain `J`,
so the finite product is faithfully flat.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]

/-- Two morphisms from an object of the site into stages `Spec (R ⧸ J)` and `Spec (R ⧸ L)` of a
formal spectrum which agree in `Spf R` send every point to the same prime of `R`. -/
theorem comap_mk_eq_of_formalSpectrumInclusion_eq (_hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem B S hS R) {V : BigFppfOver B S hS}
    {J L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }}
    (a : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage J))
    (b : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage L))
    (h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map a ≫
        formalSpectrumInclusion D (OrderDual.toDual J) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫
        formalSpectrumInclusion D (OrderDual.toDual L))
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    PrimeSpectrum.comap (Ideal.Quotient.mk J.1)
        (show PrimeSpectrum (R ⧸ J.1) from ((BigFppfOver.toScheme B S hS).map a).base v) =
      PrimeSpectrum.comap (Ideal.Quotient.mk L.1)
        (show PrimeSpectrum (R ⧸ L.1) from ((BigFppfOver.toScheme B S hS).map b).base v) := by
  let M : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨J.1 ⊓ L.1, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 L.2.1⟩
  have hMJ : M.1 ≤ J.1 := inf_le_left
  have hML : M.1 ≤ L.1 := inf_le_right
  let _ : Nonempty (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :=
    ⟨OrderDual.toDual J⟩
  let _ : IsDirected (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) :=
    ⟨fun K₁ K₂ ↦ ⟨OrderDual.toDual ⟨K₁.1 ⊓ K₂.1,
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right K₁.2 K₂.2.1⟩,
      show K₁.1 ⊓ K₂.1 ≤ K₁.1 from inf_le_left, show K₁.1 ⊓ K₂.1 ≤ K₂.1 from inf_le_right⟩⟩
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have hmono : Mono (formalSpectrumInclusion D (OrderDual.toDual M)) := by
    refine Sheaf.mono_colimit_ι_of_mono_transition (formalSpectrumDiagram D) (fun K₁ K₂ g ↦ ?_) _
    refine Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying _ (BigFppfOver.toScheme B S hS) _ ?_
    show Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom g))))
    have : AlgebraicGeometry.IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom g)))) :=
      IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective (leOfHom g))
    infer_instance
  let hJM : OrderDual.toDual J ⟶ OrderDual.toDual M := homOfLE hMJ
  let hLM : OrderDual.toDual L ⟶ OrderDual.toDual M := homOfLE hML
  have he : a ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map hJM) =
      b ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map hLM) := by
    apply (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_injective
    apply (cancel_mono (formalSpectrumInclusion D (OrderDual.toDual M))).1
    have hwJ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D.diagram.map hJM)) ≫
          formalSpectrumInclusion D (OrderDual.toDual M) =
        formalSpectrumInclusion D (OrderDual.toDual J) := colimit.w (formalSpectrumDiagram D) hJM
    have hwL : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D.diagram.map hLM)) ≫
          formalSpectrumInclusion D (OrderDual.toDual M) =
        formalSpectrumInclusion D (OrderDual.toDual L) := colimit.w (formalSpectrumDiagram D) hLM
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    exact ((congrArg (fun z ↦ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map a ≫ z)
      hwJ).trans h).trans
      (congrArg (fun z ↦ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫ z) hwL).symm
  have hpt := congrArg (fun q ↦ ((BigFppfOver.toScheme B S hS).map q).base v) he
  simp only [Functor.map_comp, Scheme.Hom.comp_apply] at hpt
  change PrimeSpectrum.comap (Ideal.Quotient.factor hMJ)
      (show PrimeSpectrum (R ⧸ J.1) from ((BigFppfOver.toScheme B S hS).map a).base v) =
    PrimeSpectrum.comap (Ideal.Quotient.factor hML)
      (show PrimeSpectrum (R ⧸ L.1) from ((BigFppfOver.toScheme B S hS).map b).base v) at hpt
  rw [← Ideal.Quotient.factor_comp_mk hMJ, ← Ideal.Quotient.factor_comp_mk hML,
    PrimeSpectrum.comap_comp_apply, PrimeSpectrum.comap_comp_apply, hpt]

/-- Contracting a prime of `B ⧸ I'` along `quotientMap` and then `mk` agrees with contracting it
along `mk` and then `f`. -/
private theorem comap_mk_comap_quotientMap {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (I' : Ideal B) (f : A →+* B) (h : I ≤ I'.comap f) (q : PrimeSpectrum (B ⧸ I')) :
    (q.comap (Ideal.quotientMap I' f h)).comap (Ideal.Quotient.mk I) =
      (q.comap (Ideal.Quotient.mk I')).comap f := by
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
    Ideal.quotientMap_comp_mk]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **A jointly surjective family of completed étale charts meets every point of a stage.** Let
`fₖ : R → Cₖ` be ring maps with completions `Cₖ^∧` over `R`, presented compatibly with `R`, whose
formal spectra map to `Spf R` jointly surjectively as morphisms of sheaves. Then every prime of
`R` containing a weak ideal of definition `J` is the contraction of a prime of some `Cₖ`. -/
theorem exists_prime_comap_eq_of_isLocallySurjective (hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem B S hS R) {K : Type (u + 1)} {C : K → Type u} [∀ k, CommRing (C k)]
    (f : ∀ k, R →+* C k) (Q : ∀ k, QuotientSystem B S hS (CompletionOver (f k)))
    (g : ∀ k, ContinuousHom D (Q k))
    (hg : ∀ k, (g k).toRingHom = CompletionOver.canonicalMap (f k))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun k ↦ formalSpectrumMap hR (g k)))
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (x : PrimeSpectrum (R ⧸ J.1)) :
    ∃ (k : K) (q : PrimeSpectrum (C k)),
      q.comap (f k) = x.comap (Ideal.Quotient.mk J.1) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let Jt := BigFppfOver.topology B S hS
  let Yo := Sheaf.sheafifiedYoneda Jt
  let T : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D.stage J)
  let s : (formalSpectrum D).obj.obj (op T) :=
    Sheaf.sectionEquiv Jt (formalSpectrumInclusion D (OrderDual.toDual J))
  obtain ⟨Sv, hSv, hlift⟩ := Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc _ hcov s
  obtain ⟨V, h, hh, v, rfl⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS hSv
    (show (BigFppfOver.toScheme B S hS).obj T from x)
  obtain ⟨k, t, ht⟩ := hlift h hh
  obtain ⟨Ia, Va, πa, hVa, -, hcovA⟩ := BigFppfOver.exists_affine_open_cover B S hS V
  obtain ⟨V', _, ⟨Z, c, _, ⟨i⟩, rfl⟩, v', rfl⟩ :=
    BigFppfOver.exists_mem_range_of_mem_topology B S hS hcovA v
  let a := (Sheaf.sectionEquiv Jt).symm ((formalSpectrum (Q k)).obj.map (πa i).op t)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (Va i)) := hVa i
  obtain ⟨K₁, p, hp⟩ := exists_factorsThroughStage_of_compactSpace
    (completionOver_isWeaklyAdmissible (f k) hR).1 (Q k) (Va i) inferInstance a
  let J₁ : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨J.1 ⊓ K₁.1.comap (g k).toRingHom, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right
      J.2 (K₁.2.1.preimage (g k).continuous)⟩
  have hJ₁ : J₁.1 ≤ Ideal.comap (g k).toRingHom K₁.1 := inf_le_right
  have hspec := formalSpectrumMap_spec hR (g k) J₁ K₁ hJ₁
  have hsec : a ≫ formalSpectrumMap hR (g k) =
      Yo.map (πa i ≫ h) ≫ formalSpectrumInclusion D (OrderDual.toDual J) := by
    have h1 : a = Yo.map (πa i) ≫ (Sheaf.sectionEquiv Jt).symm t :=
      Sheaf.sectionEquiv_symm_map Jt (πa i) t
    have h2 : (Sheaf.sectionEquiv Jt).symm t ≫ formalSpectrumMap hR (g k) =
        Yo.map h ≫ formalSpectrumInclusion D (OrderDual.toDual J) := by
      rw [← Sheaf.sectionEquiv_symm_comp Jt, ht, Sheaf.sectionEquiv_symm_map Jt h s]
      exact congrArg (fun z ↦ Yo.map h ≫ z) (Equiv.symm_apply_apply _ _)
    rw [h1, Category.assoc, h2, Functor.map_comp]
    exact (Category.assoc _ _ _).symm
  have hstage : Yo.map (p ≫ (BigAffineFppf.inclusion B S hS).map ((g k).stageMap J₁ K₁ hJ₁)) ≫
        formalSpectrumInclusion D (OrderDual.toDual J₁) =
      Yo.map (πa i ≫ h) ≫ formalSpectrumInclusion D (OrderDual.toDual J) := by
    rw [Functor.map_comp]
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z ↦ Yo.map p ≫ z) hspec.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (fun z ↦ z ≫ formalSpectrumMap hR (g k)) hp).trans hsec
  set w := ((BigFppfOver.toScheme B S hS).map c).base v' with hw
  have hpt := comap_mk_eq_of_formalSpectrumInclusion_eq hR D _ _ hstage w
  let P : PrimeSpectrum (CompletionOver (f k)) :=
    PrimeSpectrum.comap (Ideal.Quotient.mk K₁.1)
      (show PrimeSpectrum (CompletionOver (f k) ⧸ K₁.1) from
        ((BigFppfOver.toScheme B S hS).map p).base w)
  refine ⟨k, P.comap (CompletionOver.ofTarget (f k)), ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, CompletionOver.ofTarget_comp, ← hg k]
  have hl : PrimeSpectrum.comap (Ideal.Quotient.mk J₁.1)
      (show PrimeSpectrum (R ⧸ J₁.1) from ((BigFppfOver.toScheme B S hS).map
        (p ≫ (BigAffineFppf.inclusion B S hS).map ((g k).stageMap J₁ K₁ hJ₁))).base w) =
      P.comap (g k).toRingHom := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact comap_mk_comap_quotientMap J₁.1 K₁.1 (g k).toRingHom hJ₁ _
  rw [← hl, hpt, Functor.map_comp, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    ← Functor.map_comp]
  rfl

/-- **A jointly surjective family of completed étale charts of `Spf R` has a finite faithfully
flat subfamily.** Let `fₖ : R → Cₖ` be étale ring maps whose completions over `R`, presented
compatibly with `R`, have formal spectra mapping to `Spf R` jointly surjectively as morphisms of
sheaves. Then for finitely many indices `k₁, …, kₙ`, indexed by a finite type, the ring
`∏ᵢ C_{kᵢ}` is faithfully flat over `R`.

By `exists_prime_comap_eq_of_isLocallySurjective` the images of the open maps
`Spec (Cₖ ⧸ J Cₖ) ⟶ Spec (R ⧸ J)` cover the compact space `Spec (R ⧸ J)`; every maximal ideal of
`R` contains `J`, so it lies under a prime of one of finitely many `Cₖ`. -/
theorem exists_finite_faithfullyFlat_of_isLocallySurjective
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem B S hS R) {K : Type (u + 1)} {C : K → Type u} [∀ k, CommRing (C k)]
    (f : ∀ k, R →+* C k) (hf : ∀ k, (f k).Etale)
    (Q : ∀ k, QuotientSystem B S hS (CompletionOver (f k)))
    (g : ∀ k, ContinuousHom D (Q k))
    (hg : ∀ k, (g k).toRingHom = CompletionOver.canonicalMap (f k))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun k ↦ formalSpectrumMap hR (g k))) :
    ∃ (σ : Type u) (_ : Fintype σ) (k : σ → K),
      letI : ∀ i, Algebra R (C (k i)) := fun i ↦ (f (k i)).toAlgebra
      Module.FaithfullyFlat R (∀ i, C (k i)) := by
  classical
  let J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨hR.1.choose, hR.1.choose_spec⟩
  let φ : ∀ k, R ⧸ J.1 →+* C k ⧸ J.1.map (f k) := fun k ↦
    Ideal.quotientMap (J.1.map (f k)) (f k) Ideal.le_comap_map
  let O : K → Set (PrimeSpectrum (R ⧸ J.1)) := fun k ↦ Set.range (PrimeSpectrum.comap (φ k))
  have hO : ∀ k, IsOpen (O k) := by
    intro k
    let : Algebra (R ⧸ J.1) (C k ⧸ J.1.map (f k)) := (φ k).toAlgebra
    have : Algebra.Etale (R ⧸ J.1) (C k ⧸ J.1.map (f k)) :=
      RingHom.Etale.quotientMap (f k) (hf k) J.1
    exact (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation).isOpen_range
  have hmem : ∀ (k : K) (q : PrimeSpectrum (C k)) (x : PrimeSpectrum (R ⧸ J.1)),
      q.comap (f k) = x.comap (Ideal.Quotient.mk J.1) → x ∈ O k := by
    intro k q x hq
    have hle : J.1.map (f k) ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      show r ∈ (q.comap (f k)).asIdeal
      rw [hq]
      show Ideal.Quotient.mk J.1 r ∈ x.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact x.asIdeal.zero_mem
    have hq' : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J.1.map (f k)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker]
      exact hle
    obtain ⟨q', rfl⟩ := hq'
    refine ⟨q', PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_⟩
    rw [← hq]
    exact comap_mk_comap_quotientMap J.1 (J.1.map (f k)) (f k) _ q'
  have hcover : (Set.univ : Set (PrimeSpectrum (R ⧸ J.1))) ⊆ ⋃ k, O k := by
    intro x _
    obtain ⟨k, q, hq⟩ := exists_prime_comap_eq_of_isLocallySurjective hR D f Q g hg hcov J x
    exact Set.mem_iUnion.2 ⟨k, hmem k q x hq⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let e : F ≃ ULift.{u} (Fin F.card) := F.equivFin.trans Equiv.ulift.symm
  let k : ULift.{u} (Fin F.card) → K := fun i ↦ (e.symm i).1
  refine ⟨ULift.{u} (Fin F.card), inferInstance, k, ?_⟩
  let : ∀ i, Algebra R (C (k i)) := fun i ↦ (f (k i)).toAlgebra
  have : ∀ i, Algebra.Etale R (C (k i)) := fun i ↦ hf (k i)
  refine ⟨fun m hm hmtop ↦ ?_⟩
  obtain ⟨x, hx⟩ : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J.1)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact (le_ringJacobson_of_isWeakIdealOfDefinition hR J.2).trans
      (Ring.jacobson_le_of_isMaximal m)
  obtain ⟨k₀, hk₀F, q', hq'⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
  obtain ⟨i₀, rfl⟩ : ∃ i₀, k i₀ = k₀ := ⟨e ⟨k₀, hk₀F⟩, by simp [k]⟩
  let P : Ideal (C (k i₀)) :=
    (PrimeSpectrum.comap (Ideal.Quotient.mk (J.1.map (f (k i₀)))) q').asIdeal
  have hP : P.comap (f (k i₀)) = m := by
    have h := congrArg (fun y : PrimeSpectrum (R ⧸ J.1) ↦
      (y.comap (Ideal.Quotient.mk J.1)).asIdeal) hq'
    simp only [hx] at h
    rw [← h]
    exact congrArg PrimeSpectrum.asIdeal
      (comap_mk_comap_quotientMap J.1 (J.1.map (f (k i₀))) (f (k i₀)) _ q').symm
  have hPne : (1 : C (k i₀)) ∉ P := fun h ↦ (PrimeSpectrum.comap
    (Ideal.Quotient.mk (J.1.map (f (k i₀)))) q').2.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hone : (1 : ∀ i, C (k i)) ∈ m • (⊤ : Submodule R (∀ i, C (k i))) := by
    simp [hmtop]
  have hall : ∀ z ∈ m • (⊤ : Submodule R (∀ i, C (k i))), z i₀ ∈ P := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun r hr n _ ↦ ?_) (fun x y hx hy ↦ P.add_mem hx hy)
    have hfr : f (k i₀) r ∈ P := by rwa [← Ideal.mem_comap, hP]
    rw [Pi.smul_apply, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ hfr
  exact hPne (hall 1 hone)

end AlgebraicGeometry.FormalSpace

end
