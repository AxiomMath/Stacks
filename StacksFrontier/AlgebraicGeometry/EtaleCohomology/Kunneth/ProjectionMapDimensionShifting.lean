module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ProjectionMapFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsTorAmplitude
public import StacksFrontier.Algebra.Homology.DerivedCategory.DimensionShiftingNatTrans

/-!
# The projection map of Tag 0F1J at a single sheaf, by dimension shifting

The penultimate step of the proof of [Stacks, Tag 0F1J]: for a constructible sheaf `M` embedded
into a finite sum of `π_{i,*}𝔽_ℓ`, "by dimension shifting, i.e., induction on `q`, ... it
suffices to prove the result for the sheaves `π_{i,*}𝔽_ℓ`". On the projection map of `h` this is
`isIso_projectionMap_pullback_singleFunctor_of_exists_finite_embedding`: for a class `𝒞` of flat
sheaves of `ℤ/mℤ`-modules each member of which embeds into some `⨁ₖ Rπₖ_*Λ̲`, `πₖ` finite, with
cokernel in `𝒞`, the projection map `p⁻¹M[-j] ⊗^L Rh_*(e⁻¹F) ⟶ Rh_*(h⁻¹p⁻¹M[-j] ⊗^L e⁻¹F)` is
invertible for every `M` in `𝒞`.

## Main results

* `isIso_projectionMap_pullback_singleFunctor_of_exists_finite_embedding`: the projection map
  above is invertible for every `M` in `𝒞`, given derived base change along `X ⟶ S` and along
  the finite `X`-schemes ([Stacks, Tag 0F1I] for `S = Spec K`), [Stacks, Tag 0F0G] on
  `D(-_étale, ℤ/m)`, and the embedding of the members of `𝒞` ([Stacks, Tag 09Z7] for
  constructible sheaves of `𝔽_ℓ`-vector spaces) as hypotheses.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 09Z7](https://stacks.math.columbia.edu/tag/09Z7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.BaseChangeOverField

variable (m : ℕ) {S X X' S' T Y : Scheme.{u}}

/-- A flat sheaf of `ℤ/mℤ`-modules placed in degree zero and shifted by `s` has Tor amplitude in
`[-s, ∞]`. -/
theorem hasTorAmplitudeGE_shift_singleFunctor_obj
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) X).O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (ringedTopos (ULift.{u + 1} (ZMod m)) X).O) M) (s : ℤ) :
    HasTorAmplitudeGE (ULift.{u + 1} (ZMod m))
      (((DerivedCategory.singleFunctor _ 0).obj M)⟦s⟧) (-s) :=
  Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE.of_iso
    (hasTorAmplitudeGE_singleFunctor_obj _ M hM (-s))
    (((DerivedCategory.singleFunctors _).shiftIso s (-s) 0 (by omega)).app M)

/-- **The projection map of Tag 0F1J at a single sheaf, by dimension shifting.** In the setting
of [Stacks, Tag 0F1J] over an arbitrary base `S` (cartesian squares `X' = X ×_S S'`,
`Y = X' ×_{S'} T`, `g` quasi-compact and quasi-separated), let `𝒞` be a class of flat sheaves of
`ℤ/mℤ`-modules on `X_étale` every member `M` of which sits in a short exact sequence
`0 → M → I → Q → 0` with `Q` in `𝒞` and `I[0] ≅ ⨁ₖ Rπₖ_*Λ̲` for finitely many finite
`πₖ : Zₖ ⟶ X`. Suppose derived base change holds for sheaves annihilated by `m` along `X ⟶ S`
and along every finite `X`-scheme, and the projection formula of [Stacks, Tag 0F0G] holds on
`D(-_étale, ℤ/m)` for proper morphisms. Then for `M` in `𝒞`, `F ∈ D⁺(T_étale, ℤ/m)` and every
`j`, the projection map

`p⁻¹M[-j] ⊗^L Rh_*(e⁻¹F) ⟶ Rh_*(h⁻¹p⁻¹M[-j] ⊗^L e⁻¹F)`

is an isomorphism. This is the dimension shifting of the source's proof
(`CategoryTheory.NatTrans.isIso_app_shift_singleFunctor_of_exists_shortExact`), with the case
of `Rπ_*Λ̲` from `isIso_projectionMap_shift_pullback_pushforward_unit`: both sides lie in
`D^{≥b-s}` at `M[0]⟦s⟧` for `F ∈ D^{≥b}`, `M` being flat. -/
theorem isIso_projectionMap_pullback_singleFunctor_of_exists_finite_embedding (πX : X ⟶ S)
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S')
    (h : Y ⟶ X') (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (hBC : DerivedBaseChangeHolds πX m)
    (hBCfin : ∀ {Z : Scheme.{u}} (π : Z ⟶ X) [IsFinite π], DerivedBaseChangeHolds (π ≫ πX) m)
    (hProjectionFormula : ∀ {A B : Scheme.{u}} (f : A ⟶ B) [IsProper f]
      (E : DerivedModules (ULift.{u + 1} (ZMod m)) A)
      (K : DerivedModules (ULift.{u + 1} (ZMod m)) B),
      IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        (ringedToposHom (ULift.{u + 1} (ZMod m)) f)
        (isMorphismOfSites_ringedToposHom (ULift.{u + 1} (ZMod m)) f) E K))
    (𝒞 : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) X).O) → Prop)
    (hflat : ∀ M, 𝒞 M → AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (ringedTopos (ULift.{u + 1} (ZMod m)) X).O) M)
    (hres : ∀ M, 𝒞 M → ∃ (S : ShortComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod m)) X).O)))
      (_ : S.ShortExact) (_ : S.X₁ ≅ M), 𝒞 S.X₃ ∧
        ∃ (n : ℕ) (Z : Fin n → Scheme.{u}) (π : ∀ k, Z k ⟶ X) (_ : ∀ k, IsFinite (π k)),
          Nonempty ((DerivedCategory.singleFunctor _ 0).obj S.X₂ ≅
            ⨁ fun k => (pushforward (ULift.{u + 1} (ZMod m)) (π k)).obj
              (unit (ULift.{u + 1} (ZMod m)) (Z k))))
    (F : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)))
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) X).O)) (hM : 𝒞 M) (j : ℤ) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod m)) h
      ((pullback (ULift.{u + 1} (ZMod m)) p).obj ((DerivedCategory.singleFunctor _ j).obj M))
      ((pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj F))) := by
  obtain ⟨c, hc⟩ := F.property
  let B := (pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj F)
  have hB : B.IsGE c := isGE_pullback_obj _ e _ c hc
  let η := Functor.whiskerLeft (pullback (ULift.{u + 1} (ZMod m)) p)
    (projectionNatTrans (ULift.{u + 1} (ZMod m)) h B)
  have hη : ∀ A, η.app A = projectionMap (ULift.{u + 1} (ZMod m)) h
      ((pullback (ULift.{u + 1} (ZMod m)) p).obj A) B := fun _ => rfl
  have hT : ∀ M, 𝒞 M → ∀ s : ℤ, _ := fun M hM s =>
    hasTorAmplitudeGE_pullback_obj _ p _ (-s)
      (hasTorAmplitudeGE_shift_singleFunctor_obj m M (hflat M hM) s)
  have key := CategoryTheory.NatTrans.isIso_app_shift_singleFunctor_of_exists_shortExact η c 𝒞
    (fun M hM s => by
      rw [← neg_add_eq_sub]
      exact isGE_tensor_obj_of_hasTorAmplitudeGE _ _ _ (-s) c
        (hT M hM s) (isGE_pushforward_obj _ h B c hB))
    (fun M hM s => by
      rw [← neg_add_eq_sub]
      exact isGE_pushforward_obj _ h _ (-s + c)
        (isGE_tensor_obj_of_hasTorAmplitudeGE _ _ _ (-s) c
          (hasTorAmplitudeGE_pullback_obj _ h _ (-s) (hT M hM s)) hB))
    (fun M hM => by
      obtain ⟨S, hS, eS, hQ, n, Z, π, hπ, ⟨i⟩⟩ := hres M hM
      refine ⟨S, hS, eS, hQ, fun t => ?_⟩
      refine (η.isIso_app_iff_of_iso ((shiftFunctor _ t).mapIso i ≪≫
        (shiftFunctor _ t).mapBiproduct _)).2 ?_
      refine CategoryTheory.NatTrans.isIso_app_biproduct η _ fun k => ?_
      have := hπ k
      rw [hη]
      refine (isIso_projectionMap_iff_of_iso _ h
        (((pullback (ULift.{u + 1} (ZMod m)) p).commShiftIso t).app _) _).2 ?_
      exact isIso_projectionMap_shift_pullback_pushforward_unit m πX s p f' hX' g h e hY (π k)
        (pullback.fst (π k) p) (pullback.snd (π k) p) (IsPullback.of_hasPullback (π k) p)
        (pullback.fst (pullback.snd (π k) p) h) (pullback.snd (pullback.snd (π k) p) h)
        (IsPullback.of_hasPullback _ h) hBC (hBCfin (π k)) hProjectionFormula F t)
    M hM (-j)
  rw [hη] at key
  exact (isIso_projectionMap_iff_of_iso _ h ((pullback (ULift.{u + 1} (ZMod m)) p).mapIso
    (((DerivedCategory.singleFunctors _).shiftIso (-j) j 0 (by omega)).app M)) _).1 key

end Stacks.EtaleCohomology.EtaleCoefficients

end
