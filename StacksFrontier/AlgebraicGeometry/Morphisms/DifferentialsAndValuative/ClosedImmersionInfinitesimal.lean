module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.RingTheory.Nilpotent.Descent

/-!
# Closed immersions checked infinitesimally

A morphism of schemes is a closed immersion if its base change along a point-bijective closed
immersion is a closed immersion, provided either the original morphism is of finite type or the
base-changing morphism is of finite presentation.

A point-bijective closed immersion is a universal homeomorphism, so the first projection of the
pullback square is a homeomorphism; that makes the original morphism affine. On an affine open of
the target the square of section rings is a pushout, so the original morphism is surjective on
sections modulo the ideal defining the base-changing morphism. That ideal consists of nilpotents,
by density of the image of the spectra, and either finite type of the morphism or finite
generation of the ideal upgrades the surjectivity modulo nilpotents to surjectivity.

## Main results

* `AlgebraicGeometry.isClosedImmersion_of_infinitesimal_baseChange`: a closed immersion is
  detected after a closed, point-bijective base change.

## Implementation notes

Finite type is expressed as local finite type together with quasi-compactness. Finite
presentation uses `AlgebraicGeometry.FinitePresentation`. The base-changed morphism is the second
projection of the scheme pullback.

## References

* [Stacks Project, Tag 0896](https://stacks.math.columbia.edu/tag/0896)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A point-bijective closed immersion is a universal homeomorphism. -/
private lemma universalHomeomorphism_of_closedImmersion_of_bijective
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsClosedImmersion g]
    (hg : Function.Bijective g.base) : UniversalHomeomorphism g := by
  rw [universalHomeomorphism_iff_integral_universallyInjective_surjective]
  exact ⟨inferInstance, inferInstance, ⟨hg.2⟩⟩

/-- If the base change of `f` along a point-bijective closed immersion is a closed immersion,
then `f` is affine. -/
@[ega "II 1.6.2" "more general"]
private lemma isAffineHom_of_baseChange_closedImmersion
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsClosedImmersion g] (hg : Function.Bijective g.base)
    [IsClosedImmersion (pullback.snd f g)] : IsAffineHom f := by
  let p := pullback.fst f g
  have hp : IsHomeomorph p.base :=
    (universalHomeomorphism_of_closedImmersion_of_bijective g hg).universally_isHomeomorph
      _ _ _ (IsPullback.of_hasPullback f g)
  let ep : pullback (C := Scheme.{u}) f g ≃ₜ X := hp.homeomorph
  have hcomp : Topology.IsClosedEmbedding (p.base ≫ f.base) := by
    change Topology.IsClosedEmbedding (p ≫ f).base
    rw [show p ≫ f = pullback.snd f g ≫ g from pullback.condition]
    exact g.isClosedEmbedding.comp (pullback.snd f g).isClosedEmbedding
  have hfemb : Topology.IsClosedEmbedding f.base := by
    convert hcomp.comp ep.symm.isClosedEmbedding using 1
    funext x
    exact congrArg f.base (ep.apply_symm_apply x).symm
  exact isAffineHom_of_isInducing f hfemb.isInducing hfemb.isClosed_range

/-- A ring map which is surjective modulo the image of an ideal with nilpotent image is
surjective. -/
private lemma surjective_of_surjective_mod_nilpotent
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A)
    (hI : ∃ N : ℕ, (I.map f) ^ N = ⊥)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk (I.map f)).comp f)) :
    Function.Surjective f := by
  let J : Ideal B := I.map f
  have happrox : ∀ n : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ J ^ n := by
    intro n
    induction n with
    | zero =>
        intro b
        exact ⟨0, by simp⟩
    | succ n ih =>
        intro b
        obtain ⟨a₀, ha₀⟩ := hsurj (Ideal.Quotient.mk J b)
        have hbase : b - f a₀ ∈ J := Ideal.Quotient.eq.mp ha₀.symm
        have hm : b - f a₀ ∈ Ideal.span (f '' (I : Set A)) := by
          simpa [J, Ideal.map] using hbase
        rw [Submodule.mem_span_iff_exists_finset_subset] at hm
        obtain ⟨c, t, ht, _, hs⟩ := hm
        have hex : ∀ x ∈ t, ∃ a : A, a ∈ I ∧ f a = x := fun x hx ↦ by
          simpa only [Set.mem_image, SetLike.mem_coe] using ht hx
        choose! i hi hfi using hex
        choose d hd using ih
        have hcalc : b - f (a₀ + ∑ x ∈ t, i x * d (c x)) =
            ∑ x ∈ t, (f (i x) * (c x - f (d (c x)))) := by
          calc
            b - f (a₀ + ∑ x ∈ t, i x * d (c x)) =
                b - f a₀ - f (∑ x ∈ t, i x * d (c x)) := by simp [map_add]; ring
            _ = (∑ x ∈ t, c x • x) - ∑ x ∈ t, (f (i x) * f (d (c x))) := by
              rw [hs]
              simp only [map_sum, map_mul]
            _ = ∑ x ∈ t, (f (i x) * (c x - f (d (c x)))) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              rw [hfi x hx]
              simp only [smul_eq_mul]
              ring
        refine ⟨a₀ + ∑ x ∈ t, i x * d (c x), ?_⟩
        rw [hcalc]
        apply Ideal.sum_mem
        intro x hx
        rw [pow_succ]
        simpa [mul_comm] using
          Ideal.mul_mem_mul (hd (c x)) (Ideal.mem_map_of_mem f (hi x hx))
  obtain ⟨N, hN⟩ := hI
  intro b
  obtain ⟨a, ha⟩ := happrox N b
  rw [show J ^ N = ⊥ from hN, Ideal.mem_bot, sub_eq_zero] at ha
  exact ⟨a, ha.symm⟩

/-- In a pushout square of commutative rings whose two maps out of the initial corner are
surjective, the remaining map is surjective modulo the image of the kernel. -/
private theorem surjective_quotient_of_ringPushout
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (α : A →+* B) (β : A →+* C) (γ : B →+* D) (δ : C →+* D)
    (hp : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom β)
      (CommRingCat.ofHom γ) (CommRingCat.ofHom δ))
    (hβ : Function.Surjective β) (hδ : Function.Surjective δ) :
    Function.Surjective
      ((Ideal.Quotient.mk ((RingHom.ker β).map α)).comp α) := by
  classical
  let I := RingHom.ker β
  let eC : A ⧸ I ≃+* C := RingHom.quotientKerEquivOfSurjective hβ
  let e3 : CommRingCat.of C ≅ CommRingCat.of (A ⧸ I) := RingEquiv.toCommRingCatIso eC.symm
  let δ' : A ⧸ I →+* D := δ.comp eC.toRingHom
  have hp' : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom γ) (CommRingCat.ofHom δ') := by
    apply IsPushout.of_iso hp (Iso.refl _) (Iso.refl _) e3 (Iso.refl _)
    · simp
    · ext a
      exact RingHom.quotientKerEquivOfSurjective_symm_apply hβ a
    · simp
    · ext x
      simp [δ', e3]
  algebraize [α, Ideal.Quotient.mk I, γ, δ']
  let : Algebra A D := (γ.comp α).toAlgebra
  have hcomp : γ.comp α = δ'.comp (Ideal.Quotient.mk I) :=
    congrArg CommRingCat.Hom.hom hp'.w
  let : IsScalarTower A B D := .of_algebraMap_eq' rfl
  let : IsScalarTower A (A ⧸ I) D := .of_algebraMap_eq' hcomp
  let : Algebra.IsPushout A B (A ⧸ I) D := CommRingCat.isPushout_iff_isPushout.mp hp'
  let ePush : TensorProduct A B (A ⧸ I) ≃ₐ[B] D := Algebra.IsPushout.equiv A B (A ⧸ I) D
  let eQuot : (B ⧸ I.map (algebraMap A B)) ≃ₐ[B] TensorProduct A B (A ⧸ I) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  let eD : (B ⧸ I.map (algebraMap A B)) ≃ₐ[B] D := eQuot.trans ePush
  have hsurjAD : Function.Surjective (δ'.comp (Ideal.Quotient.mk I)) :=
    hδ.comp (eC.surjective.comp Ideal.Quotient.mk_surjective)
  have hleft (b : B) : ePush (b ⊗ₜ[A] (1 : A ⧸ I)) = algebraMap B D b :=
    (congrArg ePush (Algebra.IsPushout.equiv_symm_algebraMap_left A B (A ⧸ I) D b).symm).trans
      (ePush.apply_symm_apply _)
  have hmk (a : A) : eD (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (δ'.comp (Ideal.Quotient.mk I)) a := by
    change ePush (eQuot (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, hleft]
    exact congrArg (fun f => f a) hcomp
  intro x
  obtain ⟨a, ha⟩ := hsurjAD (eD x)
  exact ⟨a, eD.injective ((hmk a).trans ha)⟩

/-- The kernel of the map on sections over an affine open induced by a point-bijective closed
immersion consists of nilpotents. -/
private lemma ker_appLE_le_nilradical
    {S S' : Scheme.{u}} (g : S' ⟶ S) [IsClosedImmersion g]
    (hg : Function.Bijective g.base) (U : S.Opens) (hU : IsAffineOpen U) :
    RingHom.ker (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom ≤ nilradical Γ(S, U) := by
  classical
  let W := g ⁻¹ᵁ U
  let hW : IsAffineOpen W := hU.preimage g
  let β := g.appLE U W le_rfl
  have hcomm := IsAffineOpen.SpecMap_appLE_fromSpec g hU hW le_rfl
  have hsurjSpec : Function.Surjective (PrimeSpectrum.comap β.hom) := by
    intro x
    let sx := hU.fromSpec.base x
    have hsxU : sx ∈ (U : Set S) := by
      rw [← hU.range_fromSpec]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hg.2 sx
    obtain ⟨z, hz⟩ : y ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      exact show g.base y ∈ (U : Set S) from hy ▸ hsxU
    have hxEq : hU.fromSpec.base ((Spec.map β).base z) = sx := by
      simpa only [Scheme.Hom.comp_base, TopCat.comp_app, hz, hy] using
        congrArg (fun k : Scheme.Hom _ _ => k.base z) hcomm
    exact ⟨z, hU.fromSpec.isOpenEmbedding.injective hxEq⟩
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical β.hom).mp hsurjSpec.denseRange

/-- A closed immersion can be detected after a closed, point-bijective base change
under a finite-type or finite-presentation hypothesis. -/
@[stacks 0896]
public theorem isClosedImmersion_of_infinitesimal_baseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsClosedImmersion g] (hg : Function.Bijective g.base)
    [IsClosedImmersion (pullback.snd f g)]
    (hfinite : (LocallyOfFiniteType f ∧ QuasiCompact f) ∨ FinitePresentation g) :
    IsClosedImmersion f := by
  have hfaff : IsAffineHom f := isAffineHom_of_baseChange_closedImmersion f g hg
  rw [isClosedImmersion_iff_isAffineHom]
  refine ⟨hfaff, fun U hU ↦ ?_⟩
  classical
  let V := f ⁻¹ᵁ U
  let W := g ⁻¹ᵁ U
  let p := pullback.fst f g
  let q := pullback.snd f g
  let H : IsPullback p q f g := IsPullback.of_hasPullback f g
  let Z := q ⁻¹ᵁ W
  have hV : IsAffineOpen V := hU.preimage f
  have hW : IsAffineOpen W := hU.preimage g
  have hpq : p ⁻¹ᵁ V = q ⁻¹ᵁ W := by
    ext z
    change f.base (p.base z) ∈ (U : Set S) ↔ g.base (q.base z) ∈ (U : Set S)
    have hz := congrArg (fun k : Scheme.Hom _ _ => k.base z)
      (show p ≫ f = q ≫ g from pullback.condition)
    rw [show f.base (p.base z) = g.base (q.base z) by
      simpa only [Scheme.Hom.comp_base, ConcreteCategory.comp_apply,
        ContinuousMap.comp_apply] using hz]
  have hUY : Z = p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ W := by
    ext z
    change z ∈ q ⁻¹ᵁ W ↔ z ∈ p ⁻¹ᵁ V ∧ z ∈ q ⁻¹ᵁ W
    rw [← hpq]
    simp
  let α := f.appLE U V le_rfl
  let β := g.appLE U W le_rfl
  let γ := p.appLE V Z (by change q ⁻¹ᵁ W ≤ p ⁻¹ᵁ V; rw [hpq])
  let δ := q.appLE W Z le_rfl
  have hβ : Function.Surjective β.hom := by
    simpa only [β, W, ← Scheme.Hom.app_eq_appLE] using g.app_surjective U hU
  have hδ : Function.Surjective δ.hom := by
    simpa only [δ, Z, W, ← Scheme.Hom.app_eq_appLE] using q.app_surjective W hW
  have hpushIso : IsIso (pushoutSection H le_rfl le_rfl hUY) :=
    isIso_pushoutSection_of_isAffineOpen H le_rfl le_rfl hUY hU hW hV
  have hpush : IsPushout α β γ δ :=
    (isIso_pushoutSection_iff H le_rfl le_rfl hUY).mp hpushIso
  have hmod : Function.Surjective
      ((Ideal.Quotient.mk ((RingHom.ker β.hom).map α.hom)).comp α.hom) :=
    surjective_quotient_of_ringPushout α.hom β.hom γ.hom δ.hom hpush hβ hδ
  let I := RingHom.ker β.hom
  have hrad : I ≤ (⊥ : Ideal Γ(S, U)).radical := by
    simpa [I, β, nilradical] using ker_appLE_le_nilradical g hg U hU
  have hα : Function.Surjective α.hom := by
    rcases hfinite with hfiniteType | hfinitePresentation
    · let : LocallyOfFiniteType f := hfiniteType.1
      have hαft : α.hom.FiniteType := f.finiteType_appLE hU hV le_rfl
      let : Algebra Γ(S, U) Γ(X, V) := α.hom.toAlgebra
      have hILN : Ideal.IsLocallyNilpotent I := fun x hx => mem_nilradical.mp (hrad hx)
      exact surjective_of_surjective_mod_locallyNilpotent I hILN
        (Algebra.ofId _ _) hmod hαft
    · let : LocallyOfFinitePresentation g :=
        FinitePresentation.locallyOfFinitePresentation hfinitePresentation
      have hβfp : β.hom.FinitePresentation := g.finitePresentation_appLE hU hW le_rfl
      let : Algebra Γ(S, U) Γ(S', W) := β.hom.toAlgebra
      let : Algebra.FinitePresentation Γ(S, U) Γ(S', W) := hβfp
      have hIfg : I.FG :=
        Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId _ _) hβ
      obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hIfg
      have hnilpotent : ∃ n, (I.map α.hom) ^ n = ⊥ :=
        ⟨n, by rw [← Ideal.map_pow, le_bot_iff.mp hn, Ideal.map_bot]⟩
      exact surjective_of_surjective_mod_nilpotent α.hom I hnilpotent hmod
  change Function.Surjective (f.app U).hom
  rwa [Scheme.Hom.app_eq_appLE]

end AlgebraicGeometry

end
