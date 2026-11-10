module

public import StacksFrontier.Deformation.Examples.Geometric.CompletionSmooth
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationTangentSpace
public import StacksFrontier.Deformation.FlatAlgebraLiftLocalizationRelative

/-!
# Smoothness of the localization functor on deformations

Let `k` be a field, `P` a finite type `k`-algebra and `S ⊆ P` a multiplicative subset such that
`Spec(P) → Spec(k)` is smooth at every point of `V(g)` for every `g ∈ S`. Localization of
deformations is a functor `𝓓_P ⟶ 𝓓_{S⁻¹P}` over `𝒞_Λ` (**Stacks 0DYS**), and **Stacks 0DZ9**
asserts that it is smooth and induces an isomorphism on tangent spaces. The tangent-space
conclusion is `Deformation.Examples.bijective_differential_localizationFunctorData`. This file
supplies the other input of the criterion of **Stacks 0DYP**, the correspondence of
liftability, and concludes smoothness.

The correspondence of liftability is **Stacks 0DZ7** for the ideal `𝔟 = π⁻¹(J)` of the flat
algebra `Q` of the deformation, `π : Q → P` being the reduction and `J ⊆ P` the vanishing ideal
of the non-smooth locus of `Spec(P) → Spec(k)`: the localized deformation is the localization
of `Q` at `π⁻¹(S)`, by the `isLocalization` clause of the functor datum. Its hypotheses hold:
`B → A` is a small extension, so its kernel is square-zero; `Q` is flat and of finite type over
the Artinian base; `A → Q_h` is syntomic for every `h ∈ 𝔟`, because `h ∈ 𝔟` means `π(h) ∈ J`,
so `D(π(h))` lies in the smooth locus; and no prime of `Q` containing `𝔟` meets `π⁻¹(S)`,
because `Spec(Q) = Spec(P)` and a prime of `P` meeting `S` is a smooth point, hence outside
`V(J)`.

Because the kernel of a small extension is square-zero, the form of Stacks 0DZ7 used is
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_of_sqZero`, which carries no
hypothesis: the case of Stacks 0DZ2 it rests on is the one proved in this repository.

## Main results

* `Deformation.Examples.exists_ideal_vanishing_smoothLocus`: the smooth locus of a finite type
  algebra over a field is open, so its complement is cut out by an ideal; under the hypothesis
  of Stacks 0DZ9 no prime containing that ideal meets `S`.
* `Deformation.Examples.lifts_localizationFunctorData`: **the correspondence of liftability**.
* `Deformation.Examples.isSmooth_localizationFunctorData`: **the smoothness conclusion of
  Stacks 0DZ9**, for an arbitrary functor datum of Stacks 0DYS.
* `Deformation.Examples.isSmooth_localizationFunctor`: the same at the canonical localization
  functor.

## References

* [Stacks Project, Tag 0DZ9](https://stacks.math.columbia.edu/tag/0DZ9)
* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
* [Stacks Project, Tag 0DYP](https://stacks.math.columbia.edu/tag/0DYP)
* [Stacks Project, Tag 0DYS](https://stacks.math.columbia.edu/tag/0DYS)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u w

namespace Deformation.Examples

/-! ### The ideal cutting out the non-smooth locus -/

/-- **The non-smooth locus of a finite type algebra over a field is cut out by an ideal, and
under the hypothesis of Stacks 0DZ9 no prime containing that ideal meets `S`.** The smooth
locus is open by `Algebra.isOpen_smoothLocus`, so its complement is the zero set of its
vanishing ideal; a prime containing `g ∈ S` is a smooth point by hypothesis, hence is not in
that zero set. -/
theorem exists_ideal_vanishing_smoothLocus (k P : Type w) [Field k] [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] (S : Submonoid P)
    (hsm : ∀ g ∈ S, ∀ q : PrimeSpectrum P, g ∈ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    ∃ J : Ideal P,
      (∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) ∧
      (∀ q : PrimeSpectrum P, J ≤ q.asIdeal → ∀ g ∈ S, g ∉ q.asIdeal) := by
  have : Algebra.FinitePresentation k P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hclosed : IsClosed (Algebra.smoothLocus k P)ᶜ :=
    isClosed_compl_iff.mpr Algebra.isOpen_smoothLocus
  refine ⟨PrimeSpectrum.vanishingIdeal (Algebra.smoothLocus k P)ᶜ, fun q hq => ?_,
    fun q hq g hg hgq => ?_⟩
  · by_contra hcon
    exact hq fun z hz => (PrimeSpectrum.mem_vanishingIdeal _ _).mp hz q hcon
  · have hmem : q ∈ PrimeSpectrum.zeroLocus
        ((PrimeSpectrum.vanishingIdeal (Algebra.smoothLocus k P)ᶜ : Ideal P) : Set P) :=
      PrimeSpectrum.mem_zeroLocus _ _ |>.mpr hq
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hclosed.closure_eq] at hmem
    exact hmem (hsm g hg q hgq)

/-! ### The correspondence of liftability, and smoothness -/

section Smoothness

open InfinitesimalLifting

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (P : Type w) [CommRing P] [Algebra k P] (S : Submonoid P)

/-- **The correspondence of liftability for the localization functor.** This is the second
input of the criterion of **Stacks 0DYP**: a deformation of `P` lifts along a small extension
of its Artinian base whenever its localization does.

Under the translation of `Deformation.Examples.hasFlatAlgebraLift_of_flatAlgebraHom` and
`Deformation.Examples.exists_isHomLift_of_hasFlatAlgebraLift` the assertion is **Stacks 0DZ7**
at a square-zero kernel, for the ideal `𝔟 = π⁻¹(J)` of the flat algebra `Q`, where `J` is the
vanishing ideal of the non-smooth locus of `Spec(P) → Spec(k)`. -/
theorem lifts_localizationFunctorData [Algebra.FiniteType k P]
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (hsm : ∀ g ∈ S, ∀ q : PrimeSpectrum P, g ∈ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    ∀ ⦃B A : ArtinianLocalAlgCat.{u, w, w} Λ k⦄ (f : B ⟶ A),
      IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
        ∀ x : (ringDeformationBasedCategory Λ k P).p.Fiber A,
          (∃ (y' : (ringDeformationBasedCategory Λ k (Localization S)).obj)
              (g : y' ⟶ F.functor.obj x.1),
            (ringDeformationBasedCategory Λ k (Localization S)).p.IsHomLift f g) →
            ∃ (x' : (ringDeformationBasedCategory Λ k P).obj) (h : x' ⟶ x.1),
              (ringDeformationBasedCategory Λ k P).p.IsHomLift f h := by
  obtain ⟨J, hJsm, hJS⟩ := exists_ideal_vanishing_smoothLocus k P S hsm
  intro B A f hsmall x hyp
  obtain ⟨y', g, hg⟩ := hyp
  obtain ⟨X, hXA⟩ := x
  have hXA : X.left.base = A := hXA
  have hdomB : y'.left.base = B :=
    IsHomLift.domain_eq (ringDeformationBasedCategory Λ k (Localization S)).p f g
  have hcodA : (F.functor.obj X).left.base = A :=
    IsHomLift.codomain_eq (ringDeformationBasedCategory Λ k (Localization S)).p f g
  have hb : (F.functor.obj X).left.base = X.left.base := F.functor.w_obj X
  set f₁ : y'.left.base ⟶ (F.functor.obj X).left.base :=
    eqToHom hdomB ≫ f ≫ eqToHom hcodA.symm with hf₁
  set f₂ : y'.left.base ⟶ X.left.base :=
    eqToHom hdomB ≫ f ≫ eqToHom (hcodA.symm.trans hb) with hf₂
  have hf₁₂ : f₁ ≫ eqToHom hb = f₂ := by
    simp only [hf₁, hf₂, Category.assoc, eqToHom_trans]
  have hgb : g.left.base = f₁ :=
    IsHomLift.fac' (ringDeformationBasedCategory Λ k (Localization S)).p f g
  let : Algebra ((y'.left.base : Type w)) ((F.functor.obj X).left.base : Type w) :=
    f₁.hom.toRingHom.toAlgebra
  let : Algebra ((y'.left.base : Type w)) ((X.left.base : Type w)) :=
    f₂.hom.toRingHom.toAlgebra
  -- the flat algebra of the localized deformation is a flat lift along the base map of `g`
  have hliftC : Deformation.HasFlatAlgebraLift ((y'.left.base : Type w))
      ((F.functor.obj X).left.base : Type w) (F.functor.obj X).left.fiber :=
    hasFlatAlgebraLift_of_flatAlgebraHom g.left (by
      rw [RingHom.algebraMap_toAlgebra, hgb])
  -- read it over the base of `X`
  let : Algebra ((X.left.base : Type w)) (F.functor.obj X).left.fiber :=
    ((algebraMap ((F.functor.obj X).left.base : Type w) (F.functor.obj X).left.fiber).comp
      (ringEquivOfEq hb).symm.toRingHom).toAlgebra
  have hbaseC : ∀ a : (X.left.base : Type w),
      algebraMap ((X.left.base : Type w)) (F.functor.obj X).left.fiber a =
        algebraMap ((F.functor.obj X).left.base : Type w) (F.functor.obj X).left.fiber
          ((ringEquivOfEq hb).symm a) := fun _ => rfl
  have hliftA : Deformation.HasFlatAlgebraLift ((y'.left.base : Type w))
      ((X.left.base : Type w)) (F.functor.obj X).left.fiber := by
    refine Deformation.hasFlatAlgebraLift_of_ringEquiv (ringEquivOfEq hb) (fun a => ?_)
      (RingEquiv.refl (F.functor.obj X).left.fiber) (fun z => ?_) hliftC
    · rw [← hom_eqToHom_apply, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      exact congrArg (fun m : y'.left.base ⟶ X.left.base => m.hom a) hf₁₂
    · change algebraMap ((F.functor.obj X).left.base : Type w) _ z = _
      rw [hbaseC, RingEquiv.symm_apply_apply]
  -- the structures of the deformation over its special fibre
  let : Algebra ((X.left.base : Type w)) k := X.hom.base.hom.toRingHom.toAlgebra
  let : Algebra X.left.fiber P := X.hom.map.hom.toAlgebra
  let : Algebra ((X.left.base : Type w)) P :=
    ((algebraMap k P).comp (algebraMap ((X.left.base : Type w)) k)).toAlgebra
  have : IsScalarTower ((X.left.base : Type w)) k P := IsScalarTower.of_algebraMap_eq' rfl
  have hwX : (algebraMap X.left.fiber P).comp
      (algebraMap ((X.left.base : Type w)) X.left.fiber)
      = (algebraMap k P).comp (algebraMap ((X.left.base : Type w)) k) :=
    congrArg CommRingCat.Hom.hom X.hom.cartesian.w
  have : IsScalarTower ((X.left.base : Type w)) X.left.fiber P :=
    IsScalarTower.of_algebraMap_eq' hwX.symm
  have : Algebra.IsPushout ((X.left.base : Type w)) k X.left.fiber P :=
    isPushout_deformationSpecialFiber X rfl rfl
  have hsurjBase : Function.Surjective (algebraMap ((X.left.base : Type w)) k) :=
    surjective_deformationHomBase P X
  have : Algebra.FiniteType ((X.left.base : Type w)) X.left.fiber :=
    Deformation.finiteType_of_isPushout_specialFiber (P := P) hsurjBase
  obtain ⟨-, -, hsurjf, hker2⟩ := hsmall.isSquareZeroSurjection
  obtain ⟨hsurj₂, hsq₂⟩ :=
    surjective_and_sq_ker_comp_eqToHom f hdomB (hcodA.symm.trans hb) hsurjf hker2
  have hsurjA : Function.Surjective (algebraMap ((y'.left.base : Type w))
      ((X.left.base : Type w))) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hsurj₂
  have hzeroA : (RingHom.ker (algebraMap ((y'.left.base : Type w))
      ((X.left.base : Type w)))) ^ 2 = ⊥ := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hsq₂
  -- the localized deformation is the localization of the flat algebra of `X`
  let : Algebra X.left.fiber (F.functor.obj X).left.fiber := (F.localizationMap X).toAlgebra
  have : IsLocalization (S.comap X.hom.map.hom) (F.functor.obj X).left.fiber :=
    F.isLocalization X
  have : IsScalarTower ((X.left.base : Type w)) X.left.fiber
      (F.functor.obj X).left.fiber :=
    IsScalarTower.of_algebraMap_eq fun a => by
      have he : (eqToHom (F.functor.w_obj X)).hom ((ringEquivOfEq hb).symm a) = a :=
        (hom_eqToHom_apply (F.functor.w_obj X) ((ringEquivOfEq hb).symm a)).trans
          ((ringEquivOfEq hb).apply_symm_apply a)
      rw [hbaseC, ← localizationMap_algebraMap F X ((ringEquivOfEq hb).symm a), he]
      rfl
  -- the two hypotheses of Stacks 0DZ7
  have hsyn : ∀ h ∈ J.comap X.hom.map.hom,
      Algebra.Syntomic ((X.left.base : Type w)) (Localization.Away h) := fun h hh =>
    Deformation.syntomic_localizationAway_specialFiber (P := P) hsurjBase J hJsm h hh
  have hsurjpi : Function.Surjective (algebraMap X.left.fiber P) :=
    deformationSpecialFiberMap_surjective X
  have hnilmax : IsNilpotent (IsLocalRing.maximalIdeal ((X.left.base : Type w))) := by
    rw [← IsLocalRing.ringJacobson_eq_maximalIdeal, ← Ideal.jacobson_bot]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  have hnilker : IsNilpotent (RingHom.ker (algebraMap X.left.fiber P)) := by
    obtain ⟨n, hn⟩ := Deformation.isNilpotent_ideal_map hnilmax
      (algebraMap ((X.left.base : Type w)) X.left.fiber)
    have hle : RingHom.ker (algebraMap X.left.fiber P) ^ n ≤ ⊥ := by
      refine le_trans ?_ (le_of_eq (hn.trans Ideal.zero_eq_bot))
      exact pow_le_pow_left' (deformationSpecialFiber_ker_le_map_maximalIdeal X) n
    exact ⟨n, (le_bot_iff.mp hle).trans Ideal.zero_eq_bot.symm⟩
  have hSb : ∀ q : Ideal X.left.fiber, q.IsPrime → (J.comap X.hom.map.hom) ≤ q →
      ∀ s ∈ S.comap X.hom.map.hom, s ∉ q := by
    intro q hq hJq s hs hsq
    have := hq
    have hkerle : RingHom.ker (algebraMap X.left.fiber P) ≤ q := by
      obtain ⟨n, hn⟩ := hnilker
      intro z hz
      have hzn : z ^ n = 0 := by
        have hp := Ideal.pow_mem_pow hz n
        rwa [hn, Ideal.zero_eq_bot, Submodule.mem_bot] at hp
      exact hq.mem_of_pow_mem n (by rw [hzn]; exact q.zero_mem)
    refine hJS ⟨q.map (algebraMap X.left.fiber P),
      Ideal.map_isPrime_of_surjective hsurjpi hkerle⟩ ?_ _ hs
      (Ideal.mem_map_of_mem _ hsq)
    have : (J.comap (algebraMap X.left.fiber P)).map (algebraMap X.left.fiber P) = J :=
      Ideal.map_comap_of_surjective _ hsurjpi J
    rw [← this]
    exact Ideal.map_mono hJq
  -- Stacks 0DZ7, read backwards
  have hliftQ : Deformation.HasFlatAlgebraLift ((y'.left.base : Type w))
      ((X.left.base : Type w)) X.left.fiber :=
    Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_of_sqZero
      ((y'.left.base : Type w)) ((X.left.base : Type w)) X.left.fiber hsurjA hzeroA
      (S.comap X.hom.map.hom) (F.functor.obj X).left.fiber
      (J.comap X.hom.map.hom) hsyn hSb hliftA
  -- translate back into the deformation category
  obtain ⟨X', mm, hmm⟩ := exists_isHomLift_of_hasFlatAlgebraLift X f₂
    (RingHom.algebraMap_toAlgebra _) hliftQ
  refine ⟨X', mm, ?_⟩
  have hinst : (ringDeformationProjection Λ k P).IsHomLift f₂ mm := hmm
  have h1 : (ringDeformationProjection Λ k P).IsHomLift (f₂ ≫ eqToHom hXA) mm :=
    IsHomLift.lift_comp_eqToHom (ringDeformationProjection Λ k P) f₂ mm hXA
  have h2 : (ringDeformationProjection Λ k P).IsHomLift
      (eqToHom hdomB.symm ≫ f₂ ≫ eqToHom hXA) mm :=
    IsHomLift.lift_eqToHom_comp (ringDeformationProjection Λ k P) (f₂ ≫ eqToHom hXA) mm
      hdomB.symm
  have heq : eqToHom hdomB.symm ≫ f₂ ≫ eqToHom hXA = f := by
    simp only [hf₂, Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  exact heq ▸ h2

/-- **Stacks 0DZ9, the smoothness conclusion.** Let `k` be a field, `P` a finite type
`k`-algebra and `S ⊆ P` a multiplicative subset such that `Spec(P) → Spec(k)` is smooth at
every point of `V(g)` for every `g ∈ S`. The localization functor `𝓓_P ⟶ 𝓓_{S⁻¹P}` of
**Stacks 0DYS** is smooth. -/
@[stacks 0DZ9 "the first conclusion, smoothness: the functor of Stacks 0DYS is smooth. Under \
the tag's own hypotheses: (1) is `Algebra.FiniteType k P` and (2) is `hsm`, smoothness of \
`Spec(P) → Spec(k)` at every point of `V(g)` for every `g` of `S`. Stated for an arbitrary \
functor datum of Stacks 0DYS, with no extra hypothesis on the datum. The criterion of \
Stacks 0DYP reduces it to surjectivity of the differential, which is \
`Deformation.Examples.bijective_differential_localizationFunctorData`, and to the \
correspondence of liftability, which is proved here in \
`Deformation.Examples.lifts_localizationFunctorData`"]
theorem isSmooth_localizationFunctorData [Algebra.FiniteType k P]
    (F : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (hsm : ∀ g ∈ S, ∀ q : PrimeSpectrum P, g ∈ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    IsSmooth F.functor :=
  (isSmooth_iff_differential_surjective_and_lifts
      (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P)
      (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) (Localization S))
      F.functor).mpr
    ⟨(bijective_differential_localizationFunctorData P S F hsm).2,
      lifts_localizationFunctorData P S F hsm⟩

/-- **Stacks 0DZ9, the smoothness conclusion, at the canonical localization functor.** This is
`Deformation.Examples.isSmooth_localizationFunctorData` specialized to
`Deformation.Examples.localizationFunctor`, the functor datum built in the proof of
**Stacks 0DYS**. -/
@[stacks 0DZ9 "the first conclusion, smoothness, at the canonical localization functor \
`Deformation.Examples.localizationFunctor` of Stacks 0DYS. Under the tag's own hypotheses"]
theorem isSmooth_localizationFunctor [Algebra.FiniteType k P]
    (hsm : ∀ g ∈ S, ∀ q : PrimeSpectrum P, g ∈ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    IsSmooth (localizationFunctor (Λ := Λ) (k := k) S).functor :=
  isSmooth_localizationFunctorData P S (localizationFunctor (Λ := Λ) (k := k) S) hsm

end Smoothness

end Deformation.Examples

end
