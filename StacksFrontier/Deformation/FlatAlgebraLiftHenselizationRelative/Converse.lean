module

public import StacksFrontier.Deformation.FlatAlgebraLiftHenselization
public import StacksFrontier.Deformation.FlatAlgebraLiftLocalizationRelative
public import StacksFrontier.Deformation.SquareZero.ConormalCokernelBaseChange
public import StacksFrontier.Deformation.SquareZero.ConormalTorsion
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleTorsion
public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationRelative.FlatModuleLiftInstance
import all StacksFrontier.Deformation.FlatAlgebraLiftHenselization

/-!
# Stacks 0DZB: the converse, relativized and at a square-zero kernel

**The converse is relativized, and proved at a square-zero kernel.**
`Deformation.hasFlatAlgebraLift_henselization_iff_at` carries
`Deformation.FlatModuleLiftBaseChangeStatementAt A' A`, and
`Deformation.hasFlatAlgebraLift_henselization_iff_of_sqZero` is that equivalence with the
hypothesis discharged by `Deformation.flatModuleLiftBaseChangeStatementAt_of_sq_zero`. A
square-zero kernel is what a small extension of Artinian local rings supplies, which is the only
case the smoothness criterion of Stacks 0DYP consumes; so this is the form in which Stacks 0DZD
uses Stacks 0DZB. Stacks 0DZB itself says `nilpotent kernel`, and that case stays open.

## Main results

* `Deformation.hasFlatAlgebraLift_henselization_iff_at`: Stacks 0DZB with Stacks 0DZ2 taken only
  at the surjection in hand.
* `Deformation.hasFlatAlgebraLift_henselization_iff_of_sqZero` and
  `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization_of_sqZero`: the same at a
  square-zero kernel, with no hypothesis standing for Stacks 0DZ2.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DZB](https://stacks.math.columbia.edu/tag/0DZB)
* [Stacks Project, Tag 0DYE](https://stacks.math.columbia.edu/tag/0DYE)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The chain of isomorphisms identifying `(P ⊗_{P'} Q') ⊗_P B` with `Bʰ`, given the
isomorphism `Q' ⊗_{P'} B ≅ Bʰ` of Stacks 0DYE.

The isomorphism is recorded on both tensor factors: it sends `p ⊗ 1 ⊗ 1` to the image of `p` in
`Bʰ` and `1 ⊗ x ⊗ 1` to `g x`. The first clause alone is
`Deformation.exists_ringEquiv_tensorHenselization`. -/
private theorem exists_ringEquiv_tensorHenselization_apply_right
    (P' P B Q' Bh : Type u) [CommRing P'] [CommRing P] [CommRing B] [CommRing Q'] [CommRing Bh]
    [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q'] [Algebra P' Bh] [Algebra B Bh]
    [IsScalarTower P' P B] [IsScalarTower P' B Bh]
    (g : Q' →ₐ[P'] Bh)
    (hbij : Function.Bijective (Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom P' B Bh)
      (fun _ _ => Commute.all _ _))) :
    ∃ e : ((P ⊗[P'] Q') ⊗[P] B) ≃+* Bh,
      (∀ p : P, e ((p ⊗ₜ[P'] (1 : Q')) ⊗ₜ[P] (1 : B)) = algebraMap B Bh (algebraMap P B p)) ∧
        ∀ x : Q', e (((1 : P) ⊗ₜ[P'] x) ⊗ₜ[P] (1 : B)) = g x := by
  refine ⟨(Algebra.TensorProduct.comm P (P ⊗[P'] Q') B).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange P' P B B Q').toRingEquiv.trans
      ((Algebra.TensorProduct.comm P' B Q').toRingEquiv.trans
        (RingEquiv.ofBijective _ hbij))), fun p => ?_, fun x => ?_⟩
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.trans_apply]
    simp only [AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.cancelBaseChange_tmul]
    rw [Algebra.smul_def, mul_one]
    change Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom P' B Bh)
      (fun _ _ => Commute.all _ _) ((1 : Q') ⊗ₜ[P'] (algebraMap P B p)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.trans_apply]
    simp only [AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    change Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom P' B Bh)
      (fun _ _ => Commute.all _ _) (x ⊗ₜ[P'] (1 : B)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]

/-- The preimage in `P'` of an ideal `b` of `B` lies in the preimage of its extension to `Bh`. -/
private theorem comap_le_comap_map_algebraMap_of_tower (P' B Bh : Type u) [CommRing P']
    [CommRing B] [CommRing Bh] [Algebra P' B] [Algebra P' Bh] [Algebra B Bh]
    [IsScalarTower P' B Bh] (b : Ideal B) :
    b.comap (algebraMap P' B) ≤ (b.map (algebraMap B Bh)).comap (algebraMap P' Bh) := by
  intro x hx
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply P' B Bh]
  exact Ideal.mem_map_of_mem _ hx

/-- Stacks 0DYE for a surjection `P' → B`: the henselization `Q'` of the preimage of `b` maps to
`Bh` by some `gh`, and `(P ⊗_{P'} Q') ⊗_P B ≅ Bh` by an isomorphism recording `P` and `gh`. -/
private theorem exists_ringEquiv_tensorHenselization_of_surjective
    (P' P B Q' Bh : Type u) [CommRing P'] [CommRing P] [CommRing B] [CommRing Q'] [CommRing Bh]
    [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q'] [Algebra P' Bh] [Algebra B Bh]
    [IsScalarTower P' P B] [IsScalarTower P' B Bh]
    (hsurj : Function.Surjective (algebraMap P' B)) (b : Ideal B)
    (hhensQ : HenselianPair Q' ((b.comap (algebraMap P' B)).map (algebraMap P' Q')))
    (hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ g : P' →+* D, b.comap (algebraMap P' B) ≤ K.comap g →
        ∃! G : Q' →+* D, G.comp (algebraMap P' Q') = g ∧
          (b.comap (algebraMap P' B)).map (algebraMap P' Q') ≤ K.comap G)
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g) :
    ∃ gh : Q' →+* Bh, gh.comp (algebraMap P' Q') = algebraMap P' Bh ∧
      ∃ e : ((P ⊗[P'] Q') ⊗[P] B) ≃+* Bh,
        (∀ p : P, e ((p ⊗ₜ[P'] (1 : Q')) ⊗ₜ[P] (1 : B)) = algebraMap B Bh (algebraMap P B p)) ∧
          ∀ x : Q', e (((1 : P) ⊗ₜ[P'] x) ⊗ₜ[P] (1 : B)) = gh x := by
  have : Algebra.IsIntegral P' B := Algebra.isIntegral_of_surjective hsurj
  obtain ⟨gh, ⟨hgh1, hgh2⟩, -⟩ := hunivQ Bh inferInstance (b.map (algebraMap B Bh)) hhens
    (algebraMap P' Bh) (comap_le_comap_map_algebraMap_of_tower P' B Bh b)
  have hzero : PrimeSpectrum.zeroLocus (b : Set B) =
      PrimeSpectrum.zeroLocus ((b.comap (algebraMap P' B)).map (algebraMap P' B) : Set B) := by
    rw [Ideal.map_comap_of_surjective _ hsurj b]
  have hbij := henselization_tensorProduct_bijective_of_isIntegral P' Q' B Bh
    (b.comap (algebraMap P' B)) b le_rfl hzero hhensQ hhens hunivQ huniv
    { gh with commutes' := fun x => RingHom.congr_fun hgh1 x } hgh2
  obtain ⟨e, he, heQ⟩ := exists_ringEquiv_tensorHenselization_apply_right P' P B Q' Bh _ hbij
  exact ⟨gh, hgh1, e, he, heQ⟩

/-! ### The comparison along a henselized presentation -/

/-- **Stacks 0DZB for a chosen presentation.** Let `A' → A` be a surjection of Noetherian rings
with nilpotent kernel, let `P' → P` be a surjection of Noetherian `A'`-algebras over it with
kernel `ker(A' → A) · P'` and `P = A ⊗_{A'} P'`, let `P → B` be a surjection, let `(Q', J'Q')`
be the henselization of a pair `(P', J')` and let `C` be a ring carrying a henselian ideal `𝔠`
and presented by `Q = P ⊗_{P'} Q'` as `Q ⊗_P B`. If the localizations of `B` at the elements of
`J'` have `A'`-flat module lifts, then `B` has a flat lift to `A'` if and only if `C` does.

Stacks 0DZ2 is taken here only at the surjection `A' → A` in hand, as
`Deformation.FlatModuleLiftBaseChangeStatementAt`. The form quantified over every surjection is
`Deformation.hasFlatAlgebraLift_henselization_iff_of_presentation`, which specializes `h0DZ2` to
this one. -/
private theorem hasFlatAlgebraLift_henselization_iff_of_presentation_at
    (A' A P' P B Q' C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q'] [Algebra A' C]
    [Algebra A P] [Algebra A B] [Algebra A C] [Algebra P' P] [Algebra P' B] [Algebra P B]
    [Algebra P' Q']
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C]
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B]
    (h0DZ2 : FlatModuleLiftBaseChangeStatementAt.{u} A' A)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (J' : Ideal P')
    (hhensQ : HenselianPair Q' (J'.map (algebraMap P' Q')))
    (hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : P' →+* D, J' ≤ K.comap f →
        ∃! g : Q' →+* D, g.comp (algebraMap P' Q') = f ∧
          J'.map (algebraMap P' Q') ≤ K.comap g)
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        (Localization.awayMap (algebraMap P' P) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' P g)]
              (Localization.Away (algebraMap P' P g) ⊗[P] B)))
    (c : Ideal C) (hc : HenselianPair C c)
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)))
    (hJc : ∀ g ∈ J', e (((algebraMap P' P g) ⊗ₜ[P'] (1 : Q')) ⊗ₜ[P] (1 : B)) ∈ c) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C := by
  -- Stacks 0AGU and 0AGV for the henselization `Q'` of the pair `(P', J')`
  obtain ⟨hflatQ, hpowQ⟩ :=
    flat_henselization_and_bijective_quotientMap P' J' Q' hhensQ hunivQ
  have hquot : Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q'))
      (algebraMap P' Q') Ideal.le_comap_map) := by
    have h := hpowQ 1
    rwa [pow_one] at h
  have : Module.Flat P' Q' := hflatQ
  have : IsNoetherianRing Q' :=
    (henselization_isNoetherian_and_completion_equiv P' J' Q' hhensQ hunivQ).2.1
  -- the algebra structures on `C` over the henselized presentation
  let : Algebra (P ⊗[P'] Q') C :=
    (e.toRingHom.comp (algebraMap (P ⊗[P'] Q') ((P ⊗[P'] Q') ⊗[P] B))).toAlgebra
  let : Algebra Q' C :=
    ((algebraMap (P ⊗[P'] Q') C).comp (algebraMap Q' (P ⊗[P'] Q'))).toAlgebra
  let : Algebra P' C := ((algebraMap Q' C).comp (algebraMap P' Q')).toAlgebra
  have h1 : ∀ a' : A', algebraMap A' (P ⊗[P'] Q') a' =
      algebraMap Q' (P ⊗[P'] Q') (algebraMap A' Q' a') := by
    intro a'
    have e1 : algebraMap A' (P ⊗[P'] Q') a' = (algebraMap A' P a') ⊗ₜ[P'] (1 : Q') := rfl
    have e2 : algebraMap Q' (P ⊗[P'] Q') (algebraMap A' Q' a') =
        (1 : P) ⊗ₜ[P'] (algebraMap A' Q' a') := rfl
    rw [e1, e2, IsScalarTower.algebraMap_apply A' P' P,
      IsScalarTower.algebraMap_apply A' P' Q',
      Algebra.algebraMap_eq_smul_one (R := P') (A := P),
      Algebra.algebraMap_eq_smul_one (R := P') (A := Q'), TensorProduct.smul_tmul]
  have : IsScalarTower A' Q' (P ⊗[P'] Q') := IsScalarTower.of_algebraMap_eq h1
  have : IsScalarTower Q' (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq hAe
  have : IsScalarTower A' (P ⊗[P'] Q') C := IsScalarTower.to₁₃₄ A' A (P ⊗[P'] Q') C
  have : IsScalarTower A' Q' C := IsScalarTower.to₁₂₄ A' Q' (P ⊗[P'] Q') C
  have : IsScalarTower P' Q' C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' P' C := IsScalarTower.to₁₂₄ A' P' Q' C
  -- the image of `J'` in `C` lies in the henselian ideal
  have htmul : ∀ x : P', ((1 : P) ⊗ₜ[P'] (algebraMap P' Q' x) : P ⊗[P'] Q') =
      (algebraMap P' P x) ⊗ₜ[P'] (1 : Q') := by
    intro x
    rw [Algebra.algebraMap_eq_smul_one (R := P') (A := Q'),
      Algebra.algebraMap_eq_smul_one (R := P') (A := P), TensorProduct.smul_tmul]
  have hJcC : ∀ g ∈ J', algebraMap P' C g ∈ c := by
    intro g hg
    have hval : algebraMap P' C g =
        e (((1 : P) ⊗ₜ[P'] (algebraMap P' Q' g)) ⊗ₜ[P] (1 : B)) := rfl
    rw [hval, htmul g]
    exact hJc g hg
  -- the one instance of Stacks 0DZ2 that both implications consume
  have h0DZ2' : FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B :=
    flatModuleLiftBaseChangeInstance_of_statementAt A' A P' P B Q' h0DZ2 hsurjA hnilA hsurjP
      hkerP hsurjB J' hquot hloc
  refine ⟨hasFlatAlgebraLift_imp_baseChange_of_presentation_at A' A P' P B Q' h0DZ2'
      hsurjA hnilA hsurjP hkerP hsurjB C e hAe,
    hasFlatAlgebraLift_of_baseChange_of_presentation_at A' A P' P B Q' C h0DZ2'
      hsurjA hnilA hsurjP hkerP hsurjB ePP hePP e hAe (fun _ => rfl)
      (fun C' _ _ eCa => ?_)⟩
  exact exists_algHom_henselization_of_algebraLift A' A P' Q' C C' hsurjA hnilA J' hunivQ
    c hc hJcC eCa

/-! ### Stacks 0DZB -/

/-- **Stacks 0DZB with Stacks 0DZ2 taken only at the surjection `A' → A` in hand.** For a
surjection `A' → A` of Noetherian rings with nilpotent kernel and a
finite type flat `A`-algebra `B` with `A → B_h` syntomic for every `h` in an ideal `𝔟`, flat
lifts of `B` to `A'` exist exactly when flat lifts of the henselization `Bʰ` of the pair
`(B, 𝔟)` do.

Only the converse consumes `h0DZ2`, and it consumes the relativized statement
`Deformation.FlatModuleLiftBaseChangeStatementAt`, because it applies Stacks 0DZ2 only at the
surjection the lemma is given. The forward implication is
`Deformation.hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective`, which
assumes nothing beyond surjectivity of `A' → A`. -/
public theorem hasFlatAlgebraLift_henselization_iff_at
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (h0DZ2 : FlatModuleLiftBaseChangeStatementAt.{u} A' A)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A Bh := by
  classical
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A' Bh := ((algebraMap A Bh).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A Bh := IsScalarTower.of_algebraMap_eq' rfl
  -- the polynomial presentation of `B`
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  let : Algebra (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) :=
    (MvPolynomial.map (algebraMap A' A)).toAlgebra
  have hsurjP : Function.Surjective
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A)) :=
    MvPolynomial.map_surjective _ hsurjA
  have hkerP : RingHom.ker
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A)) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' (MvPolynomial (Fin n) A')) :=
    MvPolynomial.ker_map (algebraMap A' A)
  have : IsScalarTower A' (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) := by
    refine IsScalarTower.of_algebraMap_eq fun a' => ?_
    change MvPolynomial.C (algebraMap A' A a') =
      MvPolynomial.map (algebraMap A' A) (MvPolynomial.C a')
    rw [MvPolynomial.map_C]
  let : Algebra (MvPolynomial (Fin n) A) B := f.toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have hsurjB : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B) := hf
  let : Algebra (MvPolynomial (Fin n) A') B :=
    ((algebraMap (MvPolynomial (Fin n) A) B).comp
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A))).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' (MvPolynomial (Fin n) A) B :=
    IsScalarTower.to₁₃₄ A' A (MvPolynomial (Fin n) A) B
  have : IsScalarTower A' (MvPolynomial (Fin n) A') B :=
    IsScalarTower.to₁₂₄ A' (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B
  have hsurjPB : Function.Surjective (algebraMap (MvPolynomial (Fin n) A') B) :=
    hsurjB.comp hsurjP
  have hnoethB : IsNoetherianRing B :=
    isNoetherianRing_of_surjective (MvPolynomial (Fin n) A) B
      (algebraMap (MvPolynomial (Fin n) A) B) hsurjB
  -- the preimage of `𝔟` in the lifted polynomial algebra, and its henselization
  set I' : Ideal (MvPolynomial (Fin n) A') :=
    Ideal.comap (algebraMap (MvPolynomial (Fin n) A') B) b
  let Q' : Type u := (henselization (MvPolynomial (Fin n) A') I' : Type u)
  let : Algebra A' Q' :=
    ((algebraMap (MvPolynomial (Fin n) A') Q').comp
      (algebraMap A' (MvPolynomial (Fin n) A'))).toAlgebra
  have : IsScalarTower A' (MvPolynomial (Fin n) A') Q' :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hhensQ : HenselianPair Q'
      (I'.map (algebraMap (MvPolynomial (Fin n) A') Q')) :=
    henselianPair_henselization (MvPolynomial (Fin n) A') I'
  have hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ g : MvPolynomial (Fin n) A' →+* D, I' ≤ K.comap g →
        ∃! G : Q' →+* D,
          G.comp (algebraMap (MvPolynomial (Fin n) A') Q') = g ∧
            I'.map (algebraMap (MvPolynomial (Fin n) A') Q') ≤ K.comap G :=
    henselization_universalProperty (MvPolynomial (Fin n) A') I'
  -- Stacks 0DYE for the surjection `(P', 𝔭') → (B, 𝔟)`
  let : Algebra (MvPolynomial (Fin n) A') Bh :=
    ((algebraMap B Bh).comp (algebraMap (MvPolynomial (Fin n) A') B)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A') B Bh :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨-, -, e, he, -⟩ := exists_ringEquiv_tensorHenselization_of_surjective
    (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B Q' Bh hsurjPB b hhensQ hunivQ hhens huniv
  -- the base change of the polynomial presentation along `A' → A`
  have hePP : ∀ x : MvPolynomial (Fin n) A',
      MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A ((1 : A) ⊗ₜ[A'] x) =
        algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) x := by
    intro x
    rw [← MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := Fin n) A' A x,
      AlgEquiv.apply_symm_apply]
    rfl
  -- the image of `𝔭'` in `Bʰ` lies in the henselian ideal
  have hJc : ∀ g ∈ I',
      e (((algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g)
          ⊗ₜ[MvPolynomial (Fin n) A'] (1 : Q'))
        ⊗ₜ[MvPolynomial (Fin n) A] (1 : B)) ∈ b.map (algebraMap B Bh) := by
    intro g hg
    rw [he (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g),
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) A')
        (MvPolynomial (Fin n) A) B g]
    exact Ideal.mem_map_of_mem _ hg
  -- the forward implication needs none of this: it is Stacks 0AGU and Stacks 0DYE
  refine ⟨hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective A' A B hsurjA b
    Bh hhens huniv, ?_⟩
  refine (hasFlatAlgebraLift_henselization_iff_of_presentation_at A' A
    (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B Q' Bh h0DZ2 hsurjA hnilA hsurjP hkerP
    hsurjB (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A) hePP I' hhensQ hunivQ
    (fun g hg => exists_flatModuleLift_localization_of_syntomic A' A
      (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B hsurjA hnilA hsurjP hkerP b hsyn
      g hg)
    (b.map (algebraMap B Bh)) hhens e (fun a => ?_) hJc).mpr
  change algebraMap A Bh a = e (((algebraMap A (MvPolynomial (Fin n) A) a)
    ⊗ₜ[MvPolynomial (Fin n) A'] (1 : Q')) ⊗ₜ[MvPolynomial (Fin n) A] (1 : B))
  rw [he (algebraMap A (MvPolynomial (Fin n) A) a),
    ← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A) B,
    ← IsScalarTower.algebraMap_apply A B Bh]

/-! ### Deformations of henselizations along a square-zero thickening -/

/-- **Stacks 0DZB at a square-zero kernel, unconditionally.** For a surjection `A' → A` of
Noetherian rings whose kernel has square zero and a finite type flat `A`-algebra `B` with
`A → B_h` syntomic for every `h` in an ideal `𝔟`: flat lifts of `B` to `A'` exist exactly when
flat lifts of the henselization `Bʰ` of the pair `(B, 𝔟)` do.

This is `Deformation.hasFlatAlgebraLift_henselization_iff_at` with its hypothesis `h0DZ2`
discharged by `Deformation.flatModuleLiftBaseChangeStatementAt_of_sq_zero`, which proves
Stacks 0DZ2 in the shape that proof consumes whenever the kernel of `A' → A` has square zero.
A square-zero kernel is what a small extension of Artinian local rings supplies, which is the
only case the smoothness criterion of Stacks 0DYP consumes; so this is the form in which
Stacks 0DZD uses Stacks 0DZB. It subsumes
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization_of_sqZero`, which is the
same statement's second implication. -/
theorem hasFlatAlgebraLift_henselization_iff_of_sqZero
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A Bh :=
  hasFlatAlgebraLift_henselization_iff_at A' A B
    (flatModuleLiftBaseChangeStatementAt_of_sq_zero A' A hsurjA hzeroA) hsurjA ⟨2, hzeroA⟩ b
    hsyn Bh hhens huniv

/-- **The second implication of Stacks 0DZB at a square-zero kernel.**  For a surjection
`A' → A` of Noetherian rings with square-zero kernel and a finite type flat `A`-algebra `B` with
`A → B_h` syntomic for every `h` in an ideal `𝔟`: if the henselization `Bʰ` of the pair
`(B, 𝔟)` has a flat lift to `A'`, so does `B`.

This is `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization` with the hypothesis
`h0DZ2` discharged.  The presentation used is `P = P' ⊗_{A'} A` for the polynomial algebra
`P' = A'[x_1, …, x_n]`, which is the shape at which Stacks 0DZ2 is proved for a square-zero
kernel; the polynomial algebra over `A` is brought across `MvPolynomial.algebraTensorAlgEquiv`,
exactly as in `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_of_sqZero`.

A square-zero kernel is what a small extension of Artinian local rings supplies, which is the
only case the smoothness criterion of Stacks 0DYP consumes; so this is the form in which
Stacks 0DZD uses Stacks 0DZB. -/
theorem hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization_of_sqZero
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : (RingHom.ker (algebraMap A' A)) ^ 2 = ⊥)
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g) :
    HasFlatAlgebraLift A' A Bh → HasFlatAlgebraLift A' A B := by
  classical
  have hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)) := ⟨2, hzeroA⟩
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A' Bh := ((algebraMap A Bh).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A Bh := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  -- the presentation, taken as the literal base change of the polynomial algebra over `A'`
  obtain ⟨ψ, hψP, hψA⟩ :
      ∃ ψ : TensorProduct A' (MvPolynomial (Fin n) A') A ≃+* MvPolynomial (Fin n) A,
        (∀ x : MvPolynomial (Fin n) A',
          ψ (algebraMap (MvPolynomial (Fin n) A')
            (TensorProduct A' (MvPolynomial (Fin n) A') A) x) =
              MvPolynomial.map (algebraMap A' A) x) ∧
        (∀ a : A, ψ (algebraMap A (TensorProduct A' (MvPolynomial (Fin n) A') A) a) =
          algebraMap A (MvPolynomial (Fin n) A) a) := by
    refine ⟨((Algebra.TensorProduct.comm A' (MvPolynomial (Fin n) A') A).trans
      ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A).restrictScalars A')).toRingEquiv,
      fun x => ?_, fun a => ?_⟩
    · change MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A'
        A ((Algebra.TensorProduct.comm A' (MvPolynomial (Fin n) A') A)
          (x ⊗ₜ[A'] (1 : A))) = _
      rw [Algebra.TensorProduct.comm_tmul,
        ← MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := Fin n) A' A x,
        AlgEquiv.apply_symm_apply]
    · change MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A'
        A ((Algebra.TensorProduct.comm A' (MvPolynomial (Fin n) A') A)
          ((1 : MvPolynomial (Fin n) A') ⊗ₜ[A'] a)) = _
      rw [Algebra.TensorProduct.comm_tmul]
      exact (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A).commutes a
  let : Algebra (TensorProduct A' (MvPolynomial (Fin n) A') A) B :=
    ((f : MvPolynomial (Fin n) A →+* B).comp (ψ : _ →+* MvPolynomial (Fin n) A)).toAlgebra
  have hPB : ∀ z, algebraMap (TensorProduct A' (MvPolynomial (Fin n) A') A) B z =
    f (ψ z) := fun _ => rfl
  have : IsScalarTower A (TensorProduct A' (MvPolynomial (Fin n) A') A) B :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [hPB, hψA]
      exact (f.commutes a).symm
  let : Algebra (MvPolynomial (Fin n) A') B :=
    ((algebraMap (TensorProduct A' (MvPolynomial (Fin n) A') A) B).comp
      (algebraMap (MvPolynomial (Fin n) A')
        (TensorProduct A' (MvPolynomial (Fin n) A') A))).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A')
      (TensorProduct A' (MvPolynomial (Fin n) A') A) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' (TensorProduct A' (MvPolynomial (Fin n) A') A) B :=
    IsScalarTower.to₁₃₄ A' A (TensorProduct A' (MvPolynomial (Fin n) A') A) B
  have : IsScalarTower A' (MvPolynomial (Fin n) A') B :=
    IsScalarTower.of_algebraMap_eq fun a' => by
      rw [IsScalarTower.algebraMap_apply A' (TensorProduct A' (MvPolynomial (Fin n) A') A) B,
        IsScalarTower.algebraMap_apply A' (MvPolynomial (Fin n) A')
          (TensorProduct A' (MvPolynomial (Fin n) A') A)]
      rfl
  have hsurjP : Function.Surjective (algebraMap (MvPolynomial (Fin n) A')
      (TensorProduct A' (MvPolynomial (Fin n) A') A)) :=
    surjective_tmul_one A' A hsurjA (MvPolynomial (Fin n) A')
  have hkerP : RingHom.ker (algebraMap (MvPolynomial (Fin n) A')
      (TensorProduct A' (MvPolynomial (Fin n) A') A)) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' (MvPolynomial (Fin n) A')) :=
    Algebra.ker_algebraMap_tensorProduct_left A' (MvPolynomial (Fin n) A') A
  have hsurjB : Function.Surjective
      (algebraMap (TensorProduct A' (MvPolynomial (Fin n) A') A) B) := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨ψ.symm x, by rw [hPB, RingEquiv.apply_symm_apply]⟩
  have hsurjPB : Function.Surjective (algebraMap (MvPolynomial (Fin n) A') B) := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin n) A')
      (TensorProduct A' (MvPolynomial (Fin n) A') A) B]
    exact hsurjB.comp hsurjP
  -- the preimage of `𝔟` in the polynomial algebra over `A'`, and its henselization
  set I' : Ideal (MvPolynomial (Fin n) A') :=
    Ideal.comap (algebraMap (MvPolynomial (Fin n) A') B) b
  let Q' : Type u := (henselization (MvPolynomial (Fin n) A') I' : Type u)
  let : Algebra A' Q' :=
    ((algebraMap (MvPolynomial (Fin n) A') Q').comp
      (algebraMap A' (MvPolynomial (Fin n) A'))).toAlgebra
  have : IsScalarTower A' (MvPolynomial (Fin n) A') Q' :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hhensQ : HenselianPair Q' (I'.map (algebraMap (MvPolynomial (Fin n) A') Q')) :=
    henselianPair_henselization (MvPolynomial (Fin n) A') I'
  have hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ g : MvPolynomial (Fin n) A' →+* D, I' ≤ K.comap g →
        ∃! G : Q' →+* D,
          G.comp (algebraMap (MvPolynomial (Fin n) A') Q') = g ∧
            I'.map (algebraMap (MvPolynomial (Fin n) A') Q') ≤ K.comap G :=
    henselization_universalProperty (MvPolynomial (Fin n) A') I'
  obtain ⟨hflatQ, hpowQ⟩ :=
    flat_henselization_and_bijective_quotientMap (MvPolynomial (Fin n) A') I' Q' hhensQ hunivQ
  have : Module.Flat (MvPolynomial (Fin n) A') Q' := hflatQ
  have : IsNoetherianRing Q' :=
    (henselization_isNoetherian_and_completion_equiv (MvPolynomial (Fin n) A') I' Q'
      hhensQ hunivQ).2.1
  have hquot : Function.Bijective (Ideal.quotientMap
      (I'.map (algebraMap (MvPolynomial (Fin n) A') Q'))
      (algebraMap (MvPolynomial (Fin n) A') Q') Ideal.le_comap_map) := by
    have h := hpowQ 1
    rwa [pow_one] at h
  -- Stacks 0DYE for the surjection `(P', 𝔭') → (B, 𝔟)`: `Q' ⊗_{P'} B ≅ Bʰ`
  let : Algebra (MvPolynomial (Fin n) A') Bh :=
    ((algebraMap B Bh).comp (algebraMap (MvPolynomial (Fin n) A') B)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A') B Bh :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' (MvPolynomial (Fin n) A') Bh :=
    IsScalarTower.of_algebraMap_eq fun a' => by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) A') B Bh,
        ← IsScalarTower.algebraMap_apply A' (MvPolynomial (Fin n) A') B,
        IsScalarTower.algebraMap_apply A' A B, ← IsScalarTower.algebraMap_apply A B Bh,
        ← IsScalarTower.algebraMap_apply A' A Bh]
  obtain ⟨gh, hgh1, e, he, heQ⟩ := exists_ringEquiv_tensorHenselization_of_surjective
    (MvPolynomial (Fin n) A') (TensorProduct A' (MvPolynomial (Fin n) A') A) B Q' Bh hsurjPB b
    hhensQ hunivQ hhens huniv
  -- the structure map of `Bʰ` over `Q'` is the one `e` induces
  let : Algebra Q' Bh := gh.toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A') Q' Bh :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hgh1 x).symm
  have : IsScalarTower A' Q' Bh :=
    IsScalarTower.to₁₃₄ A' (MvPolynomial (Fin n) A') Q' Bh
  have hAe : ∀ a : A, algebraMap A Bh a =
      e ((algebraMap A (TensorProduct A' (MvPolynomial (Fin n) A') A ⊗[MvPolynomial (Fin n) A']
        Q') a) ⊗ₜ[TensorProduct A' (MvPolynomial (Fin n) A') A] (1 : B)) := by
    intro a
    change algebraMap A Bh a =
      e (((algebraMap A (TensorProduct A' (MvPolynomial (Fin n) A') A) a)
        ⊗ₜ[MvPolynomial (Fin n) A'] (1 : Q'))
          ⊗ₜ[TensorProduct A' (MvPolynomial (Fin n) A') A] (1 : B))
    rw [he (algebraMap A (TensorProduct A' (MvPolynomial (Fin n) A') A) a),
      ← IsScalarTower.algebraMap_apply A
        (TensorProduct A' (MvPolynomial (Fin n) A') A) B,
      ← IsScalarTower.algebraMap_apply A B Bh]
  have hQe : ∀ x : Q', algebraMap Q' Bh x =
      e (((1 : TensorProduct A' (MvPolynomial (Fin n) A') A) ⊗ₜ[MvPolynomial (Fin n) A'] x)
        ⊗ₜ[TensorProduct A' (MvPolynomial (Fin n) A') A] (1 : B)) :=
    fun x => (heQ x).symm
  refine hasFlatAlgebraLift_of_baseChange_of_presentation_of_sqZero A' A
    (MvPolynomial (Fin n) A') B Q' Bh hsurjA hzeroA hsurjB I' hquot
    (fun g hg => exists_flatModuleLift_localization_of_syntomic A' A
      (MvPolynomial (Fin n) A') (TensorProduct A' (MvPolynomial (Fin n) A') A) B
      hsurjA hnilA hsurjP hkerP b hsyn g hg)
    e hAe hQe (fun C' _ _ eCa => ?_)
  exact exists_algHom_henselization_of_algebraLift A' A (MvPolynomial (Fin n) A') Q' Bh C'
    hsurjA hnilA I' hunivQ (b.map (algebraMap B Bh)) hhens
    (comap_le_comap_map_algebraMap_of_tower _ B Bh b) eCa

end Deformation

end
