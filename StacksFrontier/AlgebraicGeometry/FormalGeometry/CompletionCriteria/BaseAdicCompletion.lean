module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Algebraization is detected after adically completing the base

Let `A` be a Noetherian ring with ideals `I ⊆ 𝔞`, let `X = Spec A`, `Y = V(I)` and
`U = X ∖ V(𝔞)`. Write `A'`, `I'`, `𝔞'` for the `I`-adic completions of `A`, `I`, `𝔞`, and set
`X' = Spec A'` and `U' = X' ∖ V(𝔞')`. A coherent `I`-adic system `(F_n)` on `U` extends to a
coherent `I`-adic system on `X` if and only if its pullback to `U'` is the completion of a
coherent `𝒪_{U'}`-module.

The map `A → A'` is flat and induces an isomorphism `A/I → A'/I'`, so `X' ⟶ X` is flat and
carries `Y' = V(I')` isomorphically onto `Y`; the same then holds for `U' ⟶ U` and
`U' ∩ Y' ⟶ U ∩ Y`. Hence the pullback functors `Coh(X, I𝒪_X) ⟶ Coh(X', I𝒪_{X'})` and
`Coh(U, I𝒪_U) ⟶ Coh(U', I𝒪_{U'})` are both equivalences, and the square they form with the two
restriction functors commutes. Extendability is therefore the same question over `A` and over
`A'`, and over `A'` the base is `I`-adically complete, where extendability is exactly membership
in the essential image of the completion functor.

## Main definitions

* `Stacks.Algebraization.completedSituation` — the algebraization situation over the `I`-adic
  completion of the base.
* `Stacks.Algebraization.completionMap` — the morphism `X' ⟶ X` induced by `A → A'`.

## Main results

* `Stacks.Algebraization.extendsToX_iff_pullback_isCompletion` — extendability to `X` is
  equivalent to the pullback to `U'` being a completion.
* `Stacks.Algebraization.completedSituation_U_eq_preimage` — the open `U'` is the inverse image
  of `U`.
* `AlgebraicGeometry.Scheme.Opens.isNoetherian` — an open subscheme of a Noetherian scheme is
  Noetherian.

## Implementation notes

The open `U'` is presented as the inverse image `completionMap S ⁻¹ᵁ S.U`, which
`completedSituation_U_eq_preimage` identifies with the complement of `V(𝔞')`; the induced
morphism `U' ⟶ U` is the restriction `completionMap S ∣_ S.U`. That the pullback is a completion
is expressed as membership in the essential image of the completion functor on `U'`, the spelling
used for the companion conditions of Stacks 0EIL.

The fibre product of `X' ⟶ X` with `Y ⟶ X` is computed as `Spec` of
`A' ⊗_A A/I ≅ A'/I'`, and the two projections out of it are identified with the closed immersion
`Y' ⟶ X'` and with the isomorphism `Y' ≅ Y`.

## References

* [Stacks Project, Tag 0EIN](https://stacks.math.columbia.edu/tag/0EIN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

/-- An open subscheme of a Noetherian scheme is Noetherian. -/
public instance Scheme.Opens.isNoetherian {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens) :
    IsNoetherian U.toScheme := by
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    TopologicalSpace.NoetherianSpace.set (U : Set X)
  exact ⟨⟩

end AlgebraicGeometry

namespace Stacks.Algebraization

/-- The residue ring of the completion `A'` along the extended ideal `I' = I A'` is the residue
ring `A/I`. -/
private def completionResidueEquiv (S : AlgebraizationSituation.{u}) :
    (AdicCompletion S.I S.A) ⧸
      S.I.map (algebraMap S.A (AdicCompletion S.I S.A)) ≃+* S.A ⧸ S.I :=
  (Ideal.quotEquivOfEq (AdicCompletion.ker_evalOneₐ_eq_map S.I
      (Ideal.fg_of_isNoetherianRing S.I)).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (AdicCompletion.evalOneₐ S.I).toRingHom)
      (AdicCompletion.evalOneₐ_surjective S.I))

private lemma completionResidueEquiv_symm_mk (S : AlgebraizationSituation.{u}) (x : S.A) :
    (completionResidueEquiv S).symm (Ideal.Quotient.mk S.I x) =
      Ideal.Quotient.mk (S.I.map (algebraMap S.A (AdicCompletion S.I S.A)))
        (algebraMap S.A (AdicCompletion S.I S.A) x) := by
  apply (completionResidueEquiv S).injective
  simp only [completionResidueEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [← AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
  rfl

/-- The algebraization situation over the `I`-adic completion of the base: the completed ring,
with both ideals extended to it. -/
public def completedSituation (S : AlgebraizationSituation.{u}) :
    AlgebraizationSituation.{u} where
  A := AdicCompletion S.I S.A
  I := S.I.map (algebraMap S.A (AdicCompletion S.I S.A))
  a := S.a.map (algebraMap S.A (AdicCompletion S.I S.A))
  I_le_a := Ideal.map_mono S.I_le_a

/-- The morphism `X' = Spec(A') ⟶ X = Spec(A)` induced by the completion map `A → A'`. -/
public def completionMap (S : AlgebraizationSituation.{u}) :
    (completedSituation S).X ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (algebraMap S.A (AdicCompletion S.I S.A)))

/-- The closed subscheme `Y' = V(I')` of `X'` is carried isomorphically onto `Y = V(I)`. -/
private def completionYIso (S : AlgebraizationSituation.{u}) :
    (completedSituation S).Y ≅ S.Y :=
  Scheme.Spec.mapIso ((completionResidueEquiv S).symm.toCommRingCatIso.op)

/-- The base change of `A/I` along the completion map is the residue ring `A'/I'`. -/
private def completionTensorResidueEquiv (S : AlgebraizationSituation.{u}) :
    AdicCompletion S.I S.A ⊗[S.A] (S.A ⧸ S.I) ≃+*
      AdicCompletion S.I S.A ⧸
        S.I.map (algebraMap S.A (AdicCompletion S.I S.A)) := by
  have hr : Ideal.map
        ((Algebra.TensorProduct.rid S.A (AdicCompletion S.I S.A)
          (AdicCompletion S.I S.A)).toRingEquiv :
          AdicCompletion S.I S.A ⊗[S.A] S.A →+* AdicCompletion S.I S.A)
        (S.I.map (Algebra.TensorProduct.includeRight :
          S.A →ₐ[S.A] AdicCompletion S.I S.A ⊗[S.A] S.A)) =
      S.I.map (algebraMap S.A (AdicCompletion S.I S.A)) := by
    change Ideal.map
        ((Algebra.TensorProduct.rid S.A (AdicCompletion S.I S.A)
          (AdicCompletion S.I S.A)).toRingEquiv :
          AdicCompletion S.I S.A ⊗[S.A] S.A →+* AdicCompletion S.I S.A)
        (Ideal.map (Algebra.TensorProduct.includeRight :
          S.A →ₐ[S.A] AdicCompletion S.I S.A ⊗[S.A] S.A).toRingHom S.I) = _
    rw [Ideal.map_map]
    congr 1
    ext x
    simp [Algebra.TensorProduct.rid_tmul, Algebra.algebraMap_eq_smul_one]
  exact (Algebra.TensorProduct.tensorQuotientEquiv
      (R := S.A) (S := AdicCompletion S.I S.A) (T := S.A)
      (A := AdicCompletion S.I S.A) S.I).toRingEquiv.trans
    (Ideal.quotientEquiv _ _
      (Algebra.TensorProduct.rid S.A (AdicCompletion S.I S.A)
        (AdicCompletion S.I S.A)).toRingEquiv hr.symm)

private lemma completionTensorResidueEquiv_symm_mk (S : AlgebraizationSituation.{u})
    (x : AdicCompletion S.I S.A) :
    (completionTensorResidueEquiv S).symm
        (Ideal.Quotient.mk (S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) x) =
      x ⊗ₜ[S.A] (1 : S.A ⧸ S.I) := by
  rw [completionTensorResidueEquiv, RingEquiv.symm_trans_apply,
    Ideal.quotientEquiv_symm_mk]
  simp [Algebra.TensorProduct.rid_symm_apply]

private lemma completionTensorResidueEquiv_tmul_one (S : AlgebraizationSituation.{u})
    (x : AdicCompletion S.I S.A) :
    completionTensorResidueEquiv S (x ⊗ₜ[S.A] (1 : S.A ⧸ S.I)) =
      Ideal.Quotient.mk (S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) x := by
  rw [← completionTensorResidueEquiv_symm_mk S x]
  exact (completionTensorResidueEquiv S).apply_symm_apply _

/-- The fibre product of `X' ⟶ X` with `Y ⟶ X` is the closed subscheme `Y' = V(I')` of `X'`. -/
private def completionSpecPullbackIso (S : AlgebraizationSituation.{u}) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap S.A (AdicCompletion S.I S.A))))
        (Spec.map (CommRingCat.ofHom (algebraMap S.A (S.A ⧸ S.I)))) ≅
      Spec (.of (AdicCompletion S.I S.A ⧸
        S.I.map (algebraMap S.A (AdicCompletion S.I S.A)))) :=
  pullbackSpecIso S.A (AdicCompletion S.I S.A) (S.A ⧸ S.I) ≪≫
    (Scheme.Spec.mapIso (completionTensorResidueEquiv S).toCommRingCatIso.op).symm

private lemma completionSpecPullbackIso_inv_eq (S : AlgebraizationSituation.{u}) :
    (completionSpecPullbackIso S).inv =
      Spec.map ((completionTensorResidueEquiv S).toCommRingCatIso.hom) ≫
        (pullbackSpecIso S.A (AdicCompletion S.I S.A) (S.A ⧸ S.I)).inv :=
  rfl

private lemma completionSpecPullbackIso_inv_fst (S : AlgebraizationSituation.{u}) :
    (completionSpecPullbackIso S).inv ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap S.A (AdicCompletion S.I S.A))))
          (Spec.map (CommRingCat.ofHom (algebraMap S.A (S.A ⧸ S.I)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (S.I.map (algebraMap S.A (AdicCompletion S.I S.A))))) := by
  have hring : CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          AdicCompletion S.I S.A →+* AdicCompletion S.I S.A ⊗[S.A] (S.A ⧸ S.I)) ≫
      (completionTensorResidueEquiv S).toCommRingCatIso.hom =
      CommRingCat.ofHom (Ideal.Quotient.mk
        (S.I.map (algebraMap S.A (AdicCompletion S.I S.A)))) := by
    ext x
    exact completionTensorResidueEquiv_tmul_one S x
  rw [completionSpecPullbackIso_inv_eq, Category.assoc, pullbackSpecIso_inv_fst,
    ← Spec.map_comp, hring]

private lemma completionSpecPullbackIso_inv_snd (S : AlgebraizationSituation.{u}) :
    (completionSpecPullbackIso S).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap S.A (AdicCompletion S.I S.A))))
          (Spec.map (CommRingCat.ofHom (algebraMap S.A (S.A ⧸ S.I)))) =
      Spec.map ((completionResidueEquiv S).symm.toCommRingCatIso.hom) := by
  have hring : CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          S.A ⧸ S.I →+* AdicCompletion S.I S.A ⊗[S.A] (S.A ⧸ S.I)) ≫
      (completionTensorResidueEquiv S).toCommRingCatIso.hom =
      (completionResidueEquiv S).symm.toCommRingCatIso.hom := by
    ext x
    have hx : (algebraMap S.A (AdicCompletion S.I S.A) x) ⊗ₜ[S.A] (1 : S.A ⧸ S.I) =
        (1 : AdicCompletion S.I S.A) ⊗ₜ[S.A] (Ideal.Quotient.mk S.I x) := by
      change _ = (1 : AdicCompletion S.I S.A) ⊗ₜ[S.A] (algebraMap S.A (S.A ⧸ S.I) x)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    change completionTensorResidueEquiv S
        ((1 : AdicCompletion S.I S.A) ⊗ₜ[S.A] (Ideal.Quotient.mk S.I x)) =
      (completionResidueEquiv S).symm (Ideal.Quotient.mk S.I x)
    rw [completionResidueEquiv_symm_mk, ← hx, completionTensorResidueEquiv_tmul_one]
  rw [completionSpecPullbackIso_inv_eq, Category.assoc, pullbackSpecIso_inv_snd,
    ← Spec.map_comp]
  exact congrArg Spec.map hring

/-- The fibre product of `X' ⟶ X` with `Y ⟶ X`, read as the closed subscheme `Y'` of `X'`. -/
private def completionFibreIso (S : AlgebraizationSituation.{u}) :
    pullback (completionMap S) S.Yι ≅ (completedSituation S).Y :=
  completionSpecPullbackIso S

private lemma completionFibreIso_fst (S : AlgebraizationSituation.{u}) :
    (completionFibreIso S).hom ≫ (completedSituation S).Yι =
      pullback.fst (completionMap S) S.Yι :=
  ((Iso.inv_comp_eq _).1 (completionSpecPullbackIso_inv_fst S)).symm

/-- The fibre product of `X' ⟶ X` with `Y ⟶ X` is carried isomorphically onto `Y`. -/
private def completionFibreIsoY (S : AlgebraizationSituation.{u}) :
    pullback (completionMap S) S.Yι ≅ S.Y :=
  completionFibreIso S ≪≫ completionYIso S

private lemma completionFibreIsoY_hom (S : AlgebraizationSituation.{u}) :
    (completionFibreIsoY S).hom = pullback.snd (completionMap S) S.Yι :=
  ((Iso.inv_comp_eq _).1 (completionSpecPullbackIso_inv_snd S)).symm

private lemma completionMap_flat (S : AlgebraizationSituation.{u}) :
    Flat (completionMap S) :=
  Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian S.I))

private lemma completionMap_comap_ker (S : AlgebraizationSituation.{u}) :
    S.Yι.ker.comap (completionMap S) = (completedSituation S).Yι.ker :=
  (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion S.Yι (completionMap S)).symm.trans
    ((congrArg Scheme.Hom.ker (completionFibreIso_fst S)).symm.trans
      (Scheme.Hom.ker_comp_of_isIso (completionFibreIso S).hom (completedSituation S).Yι))

private lemma isIso_pullback_snd_subschemeι
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z) [IsClosedImmersion j]
    [IsIso (pullback.snd f j)] : IsIso (pullback.snd f j.ker.subschemeι) := by
  let a := pullback.map f j f j.ker.subschemeι (𝟙 _) j.toImage (𝟙 _)
    (by simp) (by simp)
  have : IsIso a := inferInstance
  have : IsIso (a ≫ pullback.snd f j.ker.subschemeι) := by
    dsimp [a]
    rw [pullback.lift_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left a _

private lemma completionMap_closedFiber_isIso (S : AlgebraizationSituation.{u}) :
    IsIso (pullback.snd (completionMap S) S.Yι.ker.subschemeι) := by
  have : IsIso (pullback.snd (completionMap S) S.Yι) :=
    completionFibreIsoY_hom S ▸ Iso.isIso_hom (completionFibreIsoY S)
  exact isIso_pullback_snd_subschemeι _ _

/-- Base change of an isomorphism of closed fibres along a cartesian square. -/
private lemma isIso_pullback_snd_baseChange
    {C : Type*} [Category C] [HasPullbacks C]
    {X X' U U' Y : C} {f : X' ⟶ X} {i : U ⟶ X}
    {i' : U' ⟶ X'} {g : U' ⟶ U} (h : IsPullback g i' i f)
    (j : Y ⟶ X) [IsIso (pullback.snd f j)] :
    IsIso (pullback.snd g (pullback.fst i j)) := by
  let p := pullback.fst g (pullback.fst i j)
  let q := pullback.snd g (pullback.fst i j)
  let t : pullback g (pullback.fst i j) ⟶ pullback f j :=
    pullback.lift (p ≫ i') (q ≫ pullback.snd i j) (by
      simp only [Category.assoc, ← h.w, p, q]
      rw [pullback.condition_assoc, pullback.condition])
  have ht₁ : t ≫ pullback.fst f j = p ≫ i' := by simp [t]
  have ht₂ : t ≫ pullback.snd f j = q ≫ pullback.snd i j := by simp [t]
  have h₁ : IsPullback p t i' (pullback.fst f j) := by
    apply IsPullback.of_bot (t := IsPullback.of_hasPullback f j)
      (h₁₁ := p) (v₁₁ := t)
    · rw [ht₂, ← h.w]
      exact (IsPullback.of_hasPullback g (pullback.fst i j)).paste_vert
        (IsPullback.of_hasPullback i j)
    · exact ht₁.symm
  have h₂ : IsPullback q t (pullback.snd i j) (pullback.snd f j) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback i j)
      (h₁₁ := q) (v₁₁ := t)
    · rw [← pullback.condition, ← pullback.condition]
      exact h₁.paste_horiz h
    · exact ht₂.symm
  exact h₂.isIso_fst_of_isIso

/-- Restricting a flat morphism that is an isomorphism over a closed subscheme to an open of the
target leaves the pullback functor on coherent adic systems an equivalence. -/
private lemma coherentAdicPullback_restrict_isEquivalence
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso (pullback.snd f J.subschemeι)] (U : Y.Opens) :
    (Stacks.Coherent.coherentAdicPullback (f ∣_ U) (J.comap U.ι)).IsEquivalence := by
  have : IsIso (pullback.snd (f ∣_ U) (pullback.fst U.ι J.subschemeι)) :=
    isIso_pullback_snd_baseChange (isPullback_morphismRestrict f U) _
  have : IsIso (pullback.snd (f ∣_ U) (J.comap U.ι).subschemeι) :=
    isIso_pullback_snd_subschemeι _ _
  exact Stacks.Coherent.coherentAdicPullback_isEquivalence _ _

/-- The open `U' = X' ∖ V(𝔞')` of the completed base is the inverse image of `U` along
`X' ⟶ X`. -/
public theorem completedSituation_U_eq_preimage (S : AlgebraizationSituation.{u}) :
    (completedSituation S).U = completionMap S ⁻¹ᵁ S.U := by
  ext x
  change ¬(S.a.map (algebraMap S.A (AdicCompletion S.I S.A)) ≤
      (x : PrimeSpectrum (AdicCompletion S.I S.A)).asIdeal) ↔
    ¬(S.a ≤ (x : PrimeSpectrum (AdicCompletion S.I S.A)).asIdeal.comap
      (algebraMap S.A (AdicCompletion S.I S.A)))
  exact not_congr Ideal.map_le_iff_le_comap

/-- Over an `I`-adically complete base, extendability to `X` is membership in the essential image
of the completion functor on `U`. -/
private lemma extendsToX_iff_essImage_completionFunctor (S : AlgebraizationSituation.{u})
    [IsAdicComplete S.I S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) :
    ExtendsToX S F ↔
      (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage F :=
  ⟨fun h => (isCompletion_iff_ofRestriction S F).2
      ((isCompletionOfRestriction_iff_isRestrictionOfCompletion S F).2
        (isRestrictionOfCompletion_of_extendsToX S F h)),
    fun h => extendsToX_of_isRestrictionOfCompletion S F
      ((isCompletionOfRestriction_iff_isRestrictionOfCompletion S F).1
        ((isCompletion_iff_ofRestriction S F).1 h))⟩

/-- An isomorphism with the pullback along an open immersion is the same as one with the
restriction. -/
private lemma nonempty_pullback_iso_iff_nonempty_restrict_iso {X : Scheme.{u}} (V : X.Opens)
    (H : ℕᵒᵖ ⥤ X.Modules) (T : ℕᵒᵖ ⥤ V.toScheme.Modules) :
    Nonempty (H ⋙ Scheme.Modules.pullback V.ι ≅ T) ↔
      Nonempty (H ⋙ Scheme.Modules.restrictFunctor V.ι ≅ T) :=
  ⟨fun ⟨e⟩ => ⟨Functor.isoWhiskerLeft H (Scheme.Modules.restrictFunctorIsoPullback _) ≪≫ e⟩,
    fun ⟨e⟩ => ⟨(Functor.isoWhiskerLeft H (Scheme.Modules.restrictFunctorIsoPullback _)).symm
      ≪≫ e⟩⟩

/-- Over the completed base, a coherent adic system on `U'` is the restriction of one on `X'`
exactly when it is the completion of a coherent module on `U'`. The ideal and the open are taken
as arbitrary presentations, so that the criterion applies to the inverse image of `U` along
`X' ⟶ X`. -/
private lemma completedSituation_extension_iff_completion (S : AlgebraizationSituation.{u})
    (J : (completedSituation S).X.IdealSheafData) (hJ : J = (completedSituation S).Yι.ker)
    (V : (completedSituation S).X.Opens) (hV : V = (completedSituation S).U)
    (K : V.toScheme.IdealSheafData) (hK : K = J.comap V.ι)
    (F : Stacks.Coherent.CoherentAdicSystems K) :
    (∃ H : Stacks.Coherent.CoherentAdicSystems J,
      Nonempty (H.obj ⋙ Scheme.Modules.pullback V.ι ≅ F.obj)) ↔
      (completionFunctor V.toScheme K).essImage F := by
  subst hK hJ hV
  have : IsAdicComplete (completedSituation S).I (completedSituation S).A :=
    AdicCompletion.isAdicComplete_self S.I (Ideal.fg_of_isNoetherianRing S.I)
  rw [← extendsToX_iff_essImage_completionFunctor (completedSituation S) F]
  exact exists_congr fun H => nonempty_pullback_iso_iff_nonempty_restrict_iso _ _ _

/-- Transport of extendability along a cartesian square whose horizontal pullback functors on
coherent adic systems are equivalences. -/
private lemma adicExtension_iff_pullback
    {X X' U U' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian U] [IsNoetherian U']
    (f : X' ⟶ X) (i : U ⟶ X) (i' : U' ⟶ X') (g : U' ⟶ U)
    (h : i' ≫ f = g ≫ i) (J : X.IdealSheafData)
    [(Stacks.Coherent.coherentAdicPullback f J).IsEquivalence]
    [(Stacks.Coherent.coherentAdicPullback g (J.comap i)).IsEquivalence]
    (F : Stacks.Coherent.CoherentAdicSystems (J.comap i)) :
    (∃ H : Stacks.Coherent.CoherentAdicSystems J,
      Nonempty (H.obj ⋙ Scheme.Modules.pullback i ≅ F.obj)) ↔
    ∃ H : Stacks.Coherent.CoherentAdicSystems (J.comap f),
      Nonempty (H.obj ⋙ Scheme.Modules.pullback i' ≅
        F.obj ⋙ Scheme.Modules.pullback g) := by
  let E := Stacks.Coherent.coherentAdicPullback f J
  let E' := Stacks.Coherent.coherentAdicPullback g (J.comap i)
  let R := Stacks.Coherent.coherentAdicPullback i J
  let η := Scheme.Modules.pullbackComp i' f ≪≫
    Scheme.Modules.pullbackCongr h ≪≫ (Scheme.Modules.pullbackComp g i).symm
  have comparison (H : Stacks.Coherent.CoherentAdicSystems J) :
      (E.obj H).obj ⋙ Scheme.Modules.pullback i' ≅ (E'.obj (R.obj H)).obj :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H.obj η ≪≫
      (Functor.associator _ _ _).symm
  constructor
  · rintro ⟨H, ⟨e⟩⟩
    exact ⟨E.obj H, ⟨comparison H ≪≫
      Functor.isoWhiskerRight e (Scheme.Modules.pullback g)⟩⟩
  · rintro ⟨H', ⟨e⟩⟩
    let H := E.objPreimage H'
    let a := (ObjectProperty.ι _).mapIso (E.objObjPreimageIso H')
    let b : (E'.obj (R.obj H)).obj ≅ (E'.obj F).obj :=
      (comparison H).symm ≪≫ Functor.isoWhiskerRight a
        (Scheme.Modules.pullback i') ≪≫ e
    exact ⟨H, ⟨(ObjectProperty.ι _).mapIso
      (E'.preimageIso (ObjectProperty.isoMk _ b))⟩⟩

/-- **Stacks Project, Tag 0EIN.** A coherent `I`-adic system on `U = Spec(A) ∖ V(𝔞)` extends to
`Spec(A)` if and only if its pullback to `U' = Spec(A') ∖ V(𝔞')`, for `A'` the `I`-adic
completion of `A`, is the completion of a coherent `𝒪_{U'}`-module. -/
@[stacks 0EIN]
public theorem extendsToX_iff_pullback_isCompletion (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) :
    ExtendsToX S F ↔
      (completionFunctor (completionMap S ⁻¹ᵁ S.U).toScheme
          ((S.Yι.ker.comap S.U.ι).comap (completionMap S ∣_ S.U))).essImage
        ((Stacks.Coherent.coherentAdicPullback (completionMap S ∣_ S.U)
          (S.Yι.ker.comap S.U.ι)).obj F) := by
  have : Flat (completionMap S) := completionMap_flat S
  have : IsIso (pullback.snd (completionMap S) S.Yι.ker.subschemeι) :=
    completionMap_closedFiber_isIso S
  have : (Stacks.Coherent.coherentAdicPullback (completionMap S) S.Yι.ker).IsEquivalence :=
    Stacks.Coherent.coherentAdicPullback_isEquivalence _ _
  have : (Stacks.Coherent.coherentAdicPullback (completionMap S ∣_ S.U)
      (S.Yι.ker.comap S.U.ι)).IsEquivalence :=
    coherentAdicPullback_restrict_isEquivalence _ _ _
  have hK : (S.Yι.ker.comap S.U.ι).comap (completionMap S ∣_ S.U) =
      (S.Yι.ker.comap (completionMap S)).comap (completionMap S ⁻¹ᵁ S.U).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι,
      Scheme.IdealSheafData.comap_comp]
  rw [← completedSituation_extension_iff_completion S _ (completionMap_comap_ker S) _
    (completedSituation_U_eq_preimage S).symm _ hK]
  change ExtendsToX S F ↔
    ∃ H : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap (completionMap S)),
      Nonempty (H.obj ⋙ Scheme.Modules.pullback (completionMap S ⁻¹ᵁ S.U).ι ≅
        F.obj ⋙ Scheme.Modules.pullback (completionMap S ∣_ S.U))
  rw [← adicExtension_iff_pullback (completionMap S) S.U.ι
    (completionMap S ⁻¹ᵁ S.U).ι (completionMap S ∣_ S.U)
    (morphismRestrict_ι _ _).symm S.Yι.ker F]
  exact exists_congr fun H => (nonempty_pullback_iso_iff_nonempty_restrict_iso _ _ _).symm

end Stacks.Algebraization

end
