module

public import StacksFrontier.Deformation.FlatAlgebraLiftHenselization
public import StacksFrontier.Deformation.FlatAlgebraLiftLocalizationRelative
public import StacksFrontier.Deformation.SquareZero.ConormalCokernelBaseChange
public import StacksFrontier.Deformation.SquareZero.ConormalTorsion
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleTorsion
public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationRelative.ForwardImplication

/-!
# Stacks 0DZB: the instance of Stacks 0DZ2 the converse consumes

**Where the narrowing stops, and why.** At the data the converse supplies, the instance of
Stacks 0DZ2 is *equivalent* to the implication the converse is —
`Deformation.flatModuleLiftBaseChangeInstance_iff_hasFlatAlgebraLift_imp` — and that equivalence
spends `Algebra.FormallySmooth A' P'`, which is all the proof uses. So restricting Stacks 0DZ2
to a smooth `P'` is no reduction either, and the instance cannot be hypothesized in place of the
statement.

## Main results

* `Deformation.flatModuleLiftBaseChangeInstance_iff_hasFlatAlgebraLift_imp`: the instance of
  Stacks 0DZ2 is equivalent to the implication that consumes it.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DZB](https://stacks.math.columbia.edu/tag/0DZB)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Base change of a flat module lift along a flat map -/

/-- **A flat module lift base-changes along a flat map of algebras.** Let `R → S` be a flat map
of `A'`-algebras, let `T` be an `R`-algebra and let `U` be a ring receiving `S` and `T` over
`R`. If a `T`-module `M` is the base change of an `A'`-flat `R`-module, then `U ⊗_T M` is the
base change of an `A'`-flat `S`-module, namely of `S ⊗_R M'`.

`A'`-flatness of `S ⊗_R M'` is `Module.Flat.tensorProduct_of_flat_base`: tensoring with `M'`
over `A'` is exact into `R`-modules and `S ⊗_R -` is exact. The comparison is the two
cancellations `U ⊗_S (S ⊗_R M') = U ⊗_R M' = U ⊗_T (T ⊗_R M')`.

This is the content of `Deformation.HasFlatModuleLift.baseChange`, which carries the tag
Stacks 0DZ2 for this direction, in the shape the statements of this file and of
`StacksFrontier.Deformation.FlatAlgebraLiftCompletion` are written in: raw `Type u`
existentials rather than `ModuleCat`, and a general `U` in place of the base change of `T`. In
that shape the hypotheses `Module.Finite T M`, surjectivity of `R → T` and nilpotence of its
kernel are **not** needed: they serve there only to present the witness `S ⊗_R M'` inside the
universe `max u₅ v` that `Deformation.HasFlatModuleLift` prescribes, and here every ring and
module is in one universe already. -/
theorem exists_flatModuleLift_baseChange_of_flat
    (A' R S T U M : Type u)
    [CommRing A'] [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra A' R] [Algebra A' S] [Algebra R S] [IsScalarTower A' R S]
    [Algebra R T] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R T U] [IsScalarTower R S U]
    [AddCommGroup M] [Module T M] [Module.Flat R S]
    (h : ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M') (_ : Module A' M')
      (_ : IsScalarTower A' R M'), Module.Flat A' M' ∧ Nonempty ((T ⊗[R] M') ≃ₗ[T] M)) :
    ∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module S N') (_ : Module A' N')
      (_ : IsScalarTower A' S N'), Module.Flat A' N' ∧
      Nonempty ((U ⊗[S] N') ≃ₗ[U] (U ⊗[T] M)) := by
  obtain ⟨M', _, _, _, _, hflatM', ⟨eM⟩⟩ := h
  have := hflatM'
  refine ⟨S ⊗[R] M', inferInstance, inferInstance, inferInstance, inferInstance,
    Module.Flat.tensorProduct_of_flat_base M', ⟨?_⟩⟩
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R S U U M') ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R T U U M').symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl U U) eM

/-- **The one instance of Stacks 0DZ2 is hardest at the largest flat algebra: the instance at
`H'` implies the instance at every flat `P'`-algebra `Q'` mapping to `H'` over `P'`.** The left
clause of `Deformation.FlatModuleLiftBaseChangeInstance` does not mention the upper right
corner, so the two instances share it; the right clause at `Q'` implies the right clause at
`H'` by base change along the flat map `Q' → H'`, and the right clause at `Q'` follows from the
left one by base change along `P' → Q'`. Both base changes are
`Deformation.exists_flatModuleLift_baseChange_of_flat`.

The consequence for Stacks 0DZB is a negative one, and it is why the henselization carries no
leverage; see the implementation note on it. Take `H'` to be the henselization of the pair
`(P', J')` and `Q'` an étale neighbourhood of that pair — an étale, hence flat, `P'`-algebra
with `P'/J' = Q'/J'Q'`. Such a `Q'` maps to `H'` over `P'`, because `Q' ⊗_{P'} H'` is étale
over `H'` with a section modulo `J'H'` and `(H', J'H')` is a henselian pair
(`henselianPair_tfae`), and `H'` is flat over it, being the henselization of the pair
`(Q', J'Q')` as well. Granted those two facts — neither is proved here, and they are the whole
content of the application — this theorem says the instance the converse of Stacks 0DZB needs
implies the instance at `Q'`. So no proof of it can use a property of the henselization that
an étale neighbourhood lacks, and a refutation at one neighbourhood refutes it. -/
theorem flatModuleLiftBaseChangeInstance_of_flat
    (A' P' P Q' H' B : Type u)
    [CommRing A'] [CommRing P'] [CommRing P] [CommRing Q'] [CommRing H'] [CommRing B]
    [Algebra A' P'] [Algebra A' Q'] [Algebra A' H']
    [Algebra P' P] [Algebra P' Q'] [Algebra P' H'] [Algebra Q' H'] [Algebra P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' Q' H'] [IsScalarTower P' Q' H']
    [Module.Flat P' Q'] [Module.Flat Q' H'] :
    FlatModuleLiftBaseChangeInstance.{u} A' P' P H' B →
      FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B := by
  intro hH
  -- the map between the two base changes of the presentation
  set φ : (P ⊗[P'] Q') →ₐ[P] (P ⊗[P'] H') :=
    Algebra.TensorProduct.map (AlgHom.id P P) (IsScalarTower.toAlgHom P' Q' H')
  let : Algebra (P ⊗[P'] Q') (P ⊗[P'] H') := φ.toRingHom.toAlgebra
  have : IsScalarTower P (P ⊗[P'] Q') (P ⊗[P'] H') :=
    IsScalarTower.of_algebraMap_eq fun p => (φ.commutes p).symm
  let : Algebra Q' (P ⊗[P'] H') :=
    ((algebraMap H' (P ⊗[P'] H')).comp (algebraMap Q' H')).toAlgebra
  have : IsScalarTower Q' H' (P ⊗[P'] H') := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Q' (P ⊗[P'] Q') (P ⊗[P'] H') :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  refine ⟨fun h => exists_flatModuleLift_baseChange_of_flat A' P' Q' P (P ⊗[P'] Q') B h,
    fun h => hH.mpr ?_⟩
  obtain ⟨N'', _, _, _, _, hflatN'', ⟨eN⟩⟩ := exists_flatModuleLift_baseChange_of_flat
    A' Q' H' (P ⊗[P'] Q') (P ⊗[P'] H') ((P ⊗[P'] Q') ⊗[P] B) h
  exact ⟨N'', inferInstance, inferInstance, inferInstance, inferInstance, hflatN'',
    ⟨eN.trans (TensorProduct.AlgebraTensorModule.cancelBaseChange P (P ⊗[P'] Q')
      (P ⊗[P'] H') (P ⊗[P'] H') B)⟩⟩

/-- **The one instance of Stacks 0DZ2 at the `J'`-adic completion of `P'` implies the instance
at the henselization of the pair `(P', J')`.** This is the reduction Stacks' *first* proof of
0DZB performs — the one the source calls a cheat — read at the level of the single instance
that both tags' converses consume. The source completes a flat algebra lift of the
henselization along the preimage of the henselian ideal and appeals to Stacks 0DZ3; here the
module lift is pushed along the comparison map instead, and what makes that legitimate is the
last conclusion of Stacks 0AGV: the canonical `P'`-algebra map from the henselization of a
Noetherian pair to the adic completion of `P'` is flat (indeed faithfully flat). So
`Deformation.flatModuleLiftBaseChangeInstance_of_flat` applies with `Q'` the henselization and
`H'` the completion, with no hypothesis beyond `P'` Noetherian and the two defining properties
of the henselization.

So the henselization instance that Stacks 0DZB's converse needs is **not independent** of the
completion instance that Stacks 0DZ3's converse needs: it is implied by it, and a proof of the
completion comparison discharges this one too. Together with
`Deformation.flatModuleLiftBaseChangeInstance_of_flat` applied the other way — at an étale
neighbourhood of the pair — the henselization instance is no harder than the completion
instance that Stacks 0DZ3 already assumes and no easier than the instances at the étale
neighbourhoods, which is the family the counterexample of
`Deformation.FlatModuleLiftBaseChangeStatement` lives in. -/
theorem flatModuleLiftBaseChangeInstance_henselization_of_adicCompletion
    (A' P' P Q' B : Type u) [CommRing A'] [CommRing P'] [CommRing P] [CommRing Q'] [CommRing B]
    [IsNoetherianRing P']
    [Algebra A' P'] [Algebra A' Q'] [Algebra P' P] [Algebra P' Q'] [Algebra P B]
    [IsScalarTower A' P' Q']
    (J' : Ideal P')
    (hhensQ : HenselianPair Q' (J'.map (algebraMap P' Q')))
    (hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : P' →+* D, J' ≤ K.comap f →
        ∃! g : Q' →+* D, g.comp (algebraMap P' Q') = f ∧
          J'.map (algebraMap P' Q') ≤ K.comap g) :
    FlatModuleLiftBaseChangeInstance.{u} A' P' P (AdicCompletion J' P') B →
      FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B := by
  intro hcomp
  -- Stacks 0AGU for the henselization, and Stacks 0AGV for its map to the completion
  obtain ⟨hflatQ, -⟩ := flat_henselization_and_bijective_quotientMap P' J' Q' hhensQ hunivQ
  have : Module.Flat P' Q' := hflatQ
  obtain ⟨-, -, -, g, hgflat, -⟩ :=
    henselization_isNoetherian_and_completion_equiv P' J' Q' hhensQ hunivQ
  let : Algebra Q' (AdicCompletion J' P') := g.toRingHom.toAlgebra
  have : IsScalarTower P' Q' (AdicCompletion J' P') :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : IsScalarTower A' Q' (AdicCompletion J' P') :=
    IsScalarTower.to₁₃₄ A' P' Q' (AdicCompletion J' P')
  have : Module.Flat Q' (AdicCompletion J' P') := hgflat
  exact flatModuleLiftBaseChangeInstance_of_flat A' P' P Q' (AdicCompletion J' P') B hcomp

/-! ### The one instance is the second implication itself -/

/-- **The one instance of Stacks 0DZ2 that the converse consumes follows from the second
implication of Stacks 0DZB at the same presentation.** Let `A' → A` be a surjection with
nilpotent kernel, let `P' → P` be a surjection over it with kernel `ker(A' → A) · P'` and `P'`
formally smooth over `A'`, let `P → B` be a surjection, let `Q'` be a flat `P'`-algebra and let
`C` present the base change `(P ⊗_{P'} Q') ⊗_P B`. If flat lifts of `C` to `A'` give flat lifts
of `B`, then `Deformation.FlatModuleLiftBaseChangeInstance A' P' P Q' B` holds.

Both clauses of the instance are algebra-lifting statements in disguise, and that is the whole
proof. Its left clause is `HasFlatAlgebraLift A' A B`, because `P'` is formally smooth over
`A'`: `Deformation.exists_flatModuleLift_of_hasFlatAlgebraLift` lifts the structure map of `B`
along `P'` into any flat algebra lift of `B`. Its right clause gives
`HasFlatAlgebraLift A' A C` with no smoothness at all, by Nakayama over the base-changed
presentation `Q' → P ⊗_{P'} Q' → C`, which is
`Deformation.hasFlatAlgebraLift_of_exists_flatModuleLift`. So the hypothesis carries the right
clause to the left one, and the remaining direction is free: the left clause base-changes to
the right one along the flat map `P' → Q'`, by
`Deformation.exists_flatModuleLift_baseChange_of_flat`.

**The consequence is negative, and it is the point of stating this.**
`Deformation.hasFlatAlgebraLift_of_baseChange_of_presentation_at` derives that same implication
*from* the instance, so under the hypotheses that both need the two are equivalent --
`Deformation.flatModuleLiftBaseChangeInstance_iff_hasFlatAlgebraLift_imp` below. The instance
is therefore strictly weaker than `Deformation.FlatModuleLiftBaseChangeStatement`, which
quantifies over every square and every finite module, but it is **not** weaker than the second
implication of Stacks 0DZB at the presentation that implication is proved at: it is that
implication. Neither the narrowing of `h0DZ2` to one instance nor the further narrowing to a
smooth `P'` -- `Algebra.FormallySmooth A' P'` is a hypothesis *of this theorem*, so it is
already spent -- reduces the open content of Stacks 0DZB to anything smaller than Stacks 0DZB's
own second implication. -/
theorem flatModuleLiftBaseChangeInstance_of_hasFlatAlgebraLift_imp
    (A' A P' P B Q' C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C]
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [Algebra A' C] [Algebra A C]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C]
    [Algebra.FormallySmooth A' P'] [Module.Flat P' Q']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)))
    (himp : HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B) :
    FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B := by
  have hsurjQ : Function.Surjective (algebraMap Q' (P ⊗[P'] Q')) :=
    surjective_includeRight P' P Q' hsurjP
  have hkerQ : RingHom.ker (algebraMap Q' (P ⊗[P'] Q')) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') := by
    have h := ker_includeRight P' P Q' hsurjP
    rwa [hkerP, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  have hnilQ : IsNilpotent (RingHom.ker (algebraMap Q' (P ⊗[P'] Q'))) := by
    rw [hkerQ]
    exact isNilpotent_ideal_map hnilA _
  -- the comparison of the two base changes of `Q'`
  obtain ⟨eQQ, heQQ⟩ := exists_algEquiv_tensorBaseChange A' A P' P Q' hsurjA hsurjP hkerP
    (fun a => IsScalarTower.algebraMap_apply A P (P ⊗[P'] Q') a)
  have : IsScalarTower A' Q' (P ⊗[P'] Q') := IsScalarTower.to₁₃₄ A' P' Q' (P ⊗[P'] Q')
  -- the presentation of `C` over `Q = P ⊗_{P'} Q'`
  let : Algebra (P ⊗[P'] Q') C :=
    (e.toRingHom.comp (algebraMap (P ⊗[P'] Q') ((P ⊗[P'] Q') ⊗[P] B))).toAlgebra
  let : Algebra Q' C :=
    ((algebraMap (P ⊗[P'] Q') C).comp (algebraMap Q' (P ⊗[P'] Q'))).toAlgebra
  have : IsScalarTower Q' (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq hAe
  have : IsScalarTower A' (P ⊗[P'] Q') C := IsScalarTower.to₁₃₄ A' A (P ⊗[P'] Q') C
  have : IsScalarTower A' Q' C := IsScalarTower.to₁₂₄ A' Q' (P ⊗[P'] Q') C
  have hsurjC : Function.Surjective (algebraMap (P ⊗[P'] Q') C) :=
    e.surjective.comp (surjective_tmul_one P B hsurjB (P ⊗[P'] Q'))
  have eC : (((P ⊗[P'] Q') ⊗[P] B)) ≃ₗ[P ⊗[P'] Q'] C :=
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)).toLinearEquiv
  refine ⟨fun h => exists_flatModuleLift_baseChange_of_flat A' P' Q' P (P ⊗[P'] Q') B h,
    fun h => ?_⟩
  obtain ⟨N', _, _, _, _, hflatN', ⟨eN⟩⟩ := h
  refine exists_flatModuleLift_of_hasFlatAlgebraLift hsurjA hnilA hsurjP hkerP (himp ?_)
  refine hasFlatAlgebraLift_of_exists_flatModuleLift hsurjQ hnilQ hsurjC eQQ heQQ ?_
  exact ⟨N', inferInstance, inferInstance, inferInstance, inferInstance, hflatN',
    ⟨eN.trans eC⟩⟩

/-- **The one instance of Stacks 0DZ2 that the converse consumes is exactly the second
implication of Stacks 0DZB at that presentation.** Under the hypotheses of
`Deformation.hasFlatAlgebraLift_of_baseChange_of_presentation_at`,
`Deformation.FlatModuleLiftBaseChangeInstance A' P' P Q' B` holds if and only if flat lifts of
`C` to `A'` give flat lifts of `B`.

The `mp` direction is that theorem itself; the `mpr` direction is
`Deformation.flatModuleLiftBaseChangeInstance_of_hasFlatAlgebraLift_imp`, which needs none of
the Noetherian hypotheses, neither flatness hypothesis over `A'`, and not `hlift`.

So the narrowing of `h0DZ2` from `Deformation.FlatModuleLiftBaseChangeStatement` to this one
instance, which is what `Deformation.hasFlatAlgebraLift_henselization_iff_of_presentation`
performs, loses nothing and also gains nothing: what remains to be proved after it is the tag's
second implication, stated in module language. In particular restricting `h0DZ2` further -- to
a smooth `P'`, to a cyclic `M`, to one half of 0DZ2's biconditional -- cannot produce a target
weaker than Stacks 0DZB. -/
theorem flatModuleLiftBaseChangeInstance_iff_hasFlatAlgebraLift_imp
    (A' A P' P B Q' C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [Algebra A' C] [Algebra A C] [Algebra Q' C]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C]
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B] [Module.Flat P' Q']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)))
    (hQe : ∀ x : Q', algebraMap Q' C x = e (((1 : P) ⊗ₜ[P'] x) ⊗ₜ[P] (1 : B)))
    (hlift : ∀ (C' : Type u) (_ : CommRing C') (_ : Algebra A' C')
      (eC : (A ⊗[A'] C') ≃ₐ[A] C), ∃ g : Q' →ₐ[A'] C',
        ∀ x : Q', eC (1 ⊗ₜ[A'] (g x)) = algebraMap Q' C x) :
    FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B ↔
      (HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B) :=
  ⟨fun hinst => hasFlatAlgebraLift_of_baseChange_of_presentation_at A' A P' P B Q' C hinst
      hsurjA hnilA hsurjP hkerP hsurjB ePP hePP e hAe hQe hlift,
    fun himp => flatModuleLiftBaseChangeInstance_of_hasFlatAlgebraLift_imp A' A P' P B Q' C
      hsurjA hnilA hsurjP hkerP hsurjB e hAe himp⟩

/-! ### Stacks 0DZ3's converse implies Stacks 0DZB's -/

/-- **The second implication of Stacks 0DZ3 at a completed presentation implies the second
implication of Stacks 0DZB at the henselized one.** Fix the presentation both tags' converses
are proved at: a surjection `A' → A` with nilpotent kernel, a surjection `P' → P` over it with
kernel `ker(A' → A) · P'` and `P = A ⊗_{A'} P'`, with `P'` formally smooth over `A'`, a
surjection `P → B`, and an ideal `J' ⊆ P'`. Let `D` present the base change of `B` along the
`J'`-adic completion of `P'`, and let `C` present its base change along the henselization `Q'`
of the pair `(P', J')`. Then

    (flat lifts of `D` give flat lifts of `B`)  →  (flat lifts of `C` give flat lifts of `B`),

the hypothesis being the conclusion of Stacks 0DZ3's converse at the completed presentation and
the conclusion being Stacks 0DZB's converse at the henselized one.

**The reduction runs from the completion to the henselization and not back.** It is the
composite of three results already in place, and the middle one is directed: the hypothesis
gives `Deformation.FlatModuleLiftBaseChangeInstance A' P' P (AdicCompletion J' P') B` by
`Deformation.flatModuleLiftBaseChangeInstance_of_hasFlatAlgebraLift_imp`;
`Deformation.flatModuleLiftBaseChangeInstance_henselization_of_adicCompletion` transports that
instance along the comparison map of Stacks 0AGV, which is flat in the direction
`Q' → (P')^∧_{J'}` and has no inverse; and
`Deformation.hasFlatAlgebraLift_of_baseChange_of_presentation_at` turns the resulting instance
at `Q'` back into the implication for algebra lifts. The opposite direction would need the
instance to transport *up* a flat map, which `Deformation.flatModuleLiftBaseChangeInstance_of_flat`
does not give: there the right clause is pushed forward, never descended.

So Stacks 0DZB's converse at this presentation is **no harder** than Stacks 0DZ3's, and no
hypothesis beyond the two presentations' own data is needed: everything here is assumed by
`Deformation.hasFlatAlgebraLift_of_baseChange_of_presentation_at` at `Q'` already, the completed
presentation contributing only `D` with its identification `eD` and `hAeD`. In particular
flatness of `(P')^∧_{J'}` over `P'` is not an extra hypothesis — it comes from
`IsNoetherianRing P'` through `AdicCompletion.flat_of_isNoetherian`, which is an instance.

Discharging the hypothesis is one application of Stacks 0DZ3's converse at the completed
presentation. The contrapositive, which is the reason for stating this, is
`Deformation.hasFlatAlgebraLift_adicCompletion_of_henselization_of_not_hasFlatAlgebraLift`: a
witness refuting Stacks 0DZB's converse here refutes Stacks 0DZ3's converse at the completed
presentation over the same `(A', A, P', P, B, J')`. -/
theorem hasFlatAlgebraLift_henselization_imp_of_adicCompletion_imp
    (A' A P' P B Q' C D : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C] [CommRing D]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [Algebra A' C] [Algebra A C] [Algebra Q' C] [Algebra A' D] [Algebra A D]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C] [IsScalarTower A' A D]
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B] [Module.Flat P' Q']
    (J' : Ideal P')
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (hhensQ : HenselianPair Q' (J'.map (algebraMap P' Q')))
    (hunivQ : ∀ (E : Type u) (_ : CommRing E) (K : Ideal E), HenselianPair E K →
      ∀ f : P' →+* E, J' ≤ K.comap f →
        ∃! g : Q' →+* E, g.comp (algebraMap P' Q') = f ∧
          J'.map (algebraMap P' Q') ≤ K.comap g)
    (eD : (((P ⊗[P'] AdicCompletion J' P') ⊗[P] B)) ≃+* D)
    (hAeD : ∀ a : A, algebraMap A D a =
      eD ((algebraMap A (P ⊗[P'] AdicCompletion J' P') a) ⊗ₜ[P] (1 : B)))
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)))
    (hQe : ∀ x : Q', algebraMap Q' C x = e (((1 : P) ⊗ₜ[P'] x) ⊗ₜ[P] (1 : B)))
    (hlift : ∀ (C' : Type u) (_ : CommRing C') (_ : Algebra A' C')
      (eC : (A ⊗[A'] C') ≃ₐ[A] C), ∃ g : Q' →ₐ[A'] C',
        ∀ x : Q', eC (1 ⊗ₜ[A'] (g x)) = algebraMap Q' C x) :
    (HasFlatAlgebraLift A' A D → HasFlatAlgebraLift A' A B) →
      (HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B) := fun himpD =>
  hasFlatAlgebraLift_of_baseChange_of_presentation_at A' A P' P B Q' C
    (flatModuleLiftBaseChangeInstance_henselization_of_adicCompletion A' P' P Q' B J' hhensQ
      hunivQ (flatModuleLiftBaseChangeInstance_of_hasFlatAlgebraLift_imp A' A P' P B
        (AdicCompletion J' P') D hsurjA hnilA hsurjP hkerP hsurjB eD hAeD himpD))
    hsurjA hnilA hsurjP hkerP hsurjB ePP hePP e hAe hQe hlift

/-- **A refutation of Stacks 0DZB's converse at a presentation is a refutation of Stacks 0DZ3's
converse at the completed one — and the witness is the same.** At the data of
`Deformation.hasFlatAlgebraLift_henselization_imp_of_adicCompletion_imp`, suppose `C` — the base
change of `B` along the henselization of the pair `(P', J')` — has a flat lift to `A'` while `B`
has none. Then `D`, the base change of `B` along the `J'`-adic completion of `P'`, also has a
flat lift to `A'`.

This is the contrapositive of that theorem, unpacked: `¬ (lifts of D give lifts of B)` is, `B`
having no lift, exactly a flat lift of `D`. So a counterexample to Stacks 0DZB at a presentation
does not merely deny Stacks 0DZ3's converse there — it exhibits the completed presentation's own
counterexample, with `B` and the whole left-hand square unchanged. -/
theorem hasFlatAlgebraLift_adicCompletion_of_henselization_of_not_hasFlatAlgebraLift
    (A' A P' P B Q' C D : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C] [CommRing D]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [Algebra A' C] [Algebra A C] [Algebra Q' C] [Algebra A' D] [Algebra A D]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C] [IsScalarTower A' A D]
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B] [Module.Flat P' Q']
    (J' : Ideal P')
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (hhensQ : HenselianPair Q' (J'.map (algebraMap P' Q')))
    (hunivQ : ∀ (E : Type u) (_ : CommRing E) (K : Ideal E), HenselianPair E K →
      ∀ f : P' →+* E, J' ≤ K.comap f →
        ∃! g : Q' →+* E, g.comp (algebraMap P' Q') = f ∧
          J'.map (algebraMap P' Q') ≤ K.comap g)
    (eD : (((P ⊗[P'] AdicCompletion J' P') ⊗[P] B)) ≃+* D)
    (hAeD : ∀ a : A, algebraMap A D a =
      eD ((algebraMap A (P ⊗[P'] AdicCompletion J' P') a) ⊗ₜ[P] (1 : B)))
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)))
    (hQe : ∀ x : Q', algebraMap Q' C x = e (((1 : P) ⊗ₜ[P'] x) ⊗ₜ[P] (1 : B)))
    (hlift : ∀ (C' : Type u) (_ : CommRing C') (_ : Algebra A' C')
      (eC : (A ⊗[A'] C') ≃ₐ[A] C), ∃ g : Q' →ₐ[A'] C',
        ∀ x : Q', eC (1 ⊗ₜ[A'] (g x)) = algebraMap Q' C x)
    (hC : HasFlatAlgebraLift A' A C) (hB : ¬ HasFlatAlgebraLift A' A B) :
    HasFlatAlgebraLift A' A D := by
  by_contra hD
  exact hB (hasFlatAlgebraLift_henselization_imp_of_adicCompletion_imp A' A P' P B Q' C D J'
    hsurjA hnilA hsurjP hkerP hsurjB ePP hePP hhensQ hunivQ eD hAeD e hAe hQe hlift
    (fun h => absurd h hD) hC)

end Deformation

end
