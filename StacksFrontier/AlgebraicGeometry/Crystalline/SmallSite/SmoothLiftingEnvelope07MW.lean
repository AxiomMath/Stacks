module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectFormsDPNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeOfExtendedIdeal
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetractPresentation
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalBridge
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.TensorPowerEnvelopeLifts
public import StacksFrontier.RingTheory.AdicCompletion.LiftToComplete

/-!
# The divided power envelope of a smooth lifting is the lifting itself

In the situation of Remark [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`): `S = Spec(A)`
affine with divided power ideal `(I, γ)`, `p` nilpotent in `A`, `Y` smooth over `S` and
`X = Y ×_S S₀`, assume moreover that `Y` is affine.  Write `P' = Γ(Y, ⊤)`, `C = Γ(X, ⊤)` and
`f' : P' → C` for the map on global sections of the closed immersion `X ⟶ Y`.  Then `f'` is a
surjective presentation of `C` by the smooth `A`-algebra `P'` in the affine crystalline
situation `affineSituation S _` of [Stacks, Tag 07MD], its kernel is `I · P'`, and the divided
power envelope `D_{P', γ}(ker f')` of [Stacks, Tag 07H8] is `P'` itself, with the divided powers
`γ_Y` of the object `(X, Y, γ)` of `Cris(X/S)` constructed in part (1) of the remark.  Since `p`
is nilpotent, the `p`-adically completed envelope is `P'` as well.

This is the affine input that lets the comparison of [Stacks, Tag 07LH] for the presentation
`f'` be read on the smooth lifting `Y` itself.

## Main definitions

* `Situation07MW.affineCrystallineSituation` — the affine situation `(A, I, γ) → C`.
* `Situation07MW.liftingAlgebra` — the `A`-algebra structure on `P'`; it agrees with
  `crysTopAlgebra` of `(X, Y, γ)` (`liftingAlgebra_eq_crysTopAlgebra`).
* `Situation07MW.liftingPresentation` — the presentation `f' : P' →ₐ[A] C`.
* `Situation07MW.envelopeEquiv` — `D_{P', γ}(ker f') ≃ₐ[A] P'`.
* `Situation07MW.completedEnvelopeEquiv` — `D_{P', γ}(ker f')^∧ ≃ₐ[A] P'`.

## Main results

* `surjective_liftingPresentation`, `smooth_liftingAlgebra` (an instance),
  `ker_liftingPresentation` — `f'` is surjective, `P'` is smooth over `A`, `ker f' = I · P'`.
* `isDPMorphism_envelopeEquiv`, `isDPMorphism_envelopeEquiv_symm`, `envelopeEquiv_algebraMap` —
  the identification of the envelope is a divided power isomorphism onto `γ_Y` over `P'`.
* `completedEnvelopeAugmentation_comp_completedEnvelopeEquiv_symm` — the augmentation of the
  completed envelope is `f'` under the identification.

## What is and is not proved

Everything stated is proved.  `Y` is assumed affine (`[IsAffine T.Y]`); `X` need not be assumed
affine.  No tag attribute is placed: this is an auxiliary step towards part (3) of
[Stacks, Tag 07MW], which is not proved here.  The divided power statement is about the
envelope itself; the completed divided powers of the completion are not compared with `γ_Y`.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite DividedPowers
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)

include T in
/-- **`p` is nilpotent in `Γ(X, ⊤)`.**  It is nilpotent in `A = Γ(S, ⊤)` by hypothesis, and
`Γ(S, ⊤) ⟶ Γ(X, ⊤)` is a ring map. -/
theorem primeNilpotentX : IsNilpotent (S.p : Γ(S.X, ⊤)) := by
  simpa only [map_natCast] using T.prime_nilpotent.map (sourceToBase S).appTop.hom

/-- The affine crystalline situation `(A, I, γ) → C` with `A = Γ(S, ⊤)` and `C = Γ(X, ⊤)`
attached to the situation of [Stacks, Tag 07MW]; this is `affineSituation S T.primeNilpotentX`. -/
abbrev affineCrystallineSituation : AffineCrystallineSituation.{u, u} :=
  affineSituation S T.primeNilpotentX

/-- The `A`-algebra structure on `P' = Γ(Y, ⊤)` given by the structure map `Y ⟶ S` on global
sections.  It is `crysTopAlgebra` of the object `(X, Y, γ)` of `Cris(X/S)`, up to the identification
of `appLE ⊤ ⊤` with `appTop`; see `liftingAlgebra_eq_crysTopAlgebra`.  It is not a global
instance: files using it activate it with `attribute [local instance]`. -/
abbrev liftingAlgebra :
    Algebra (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) :=
  T.toBase.appTop.hom.toAlgebra

attribute [local instance] liftingAlgebra presentationEnvelopeAlgebraInst

/-- The algebra structure `liftingAlgebra` is the algebra structure `crysTopAlgebra` which
`...affineBaseAppLE (V := ⊤)` puts on the global sections of the ambient scheme of the object
`(X, Y, γ)` of `Cris(X/S)`.  The two differ only by `appLE ⊤ ⊤` against `appTop`. -/
theorem liftingAlgebra_eq_crysTopAlgebra :
    T.liftingAlgebra = crysTopAlgebra S T.crystallineThickening.obj := by
  refine Algebra.algebra_ext _ _ fun a ↦ ?_
  change T.toBase.appTop.hom a = (T.toBase.appLE ⊤ ⊤ (le_preimage_top T.toBase ⊤)).hom a
  have h : T.toBase.appLE ⊤ ⊤ (le_preimage_top T.toBase ⊤) = T.toBase.appTop :=
    Scheme.Hom.appLE_eq_app _
  exact (congrArg (fun g : Γ(S.S.scheme, ⊤) ⟶ Γ(T.Y, ⊤) ↦ g.hom a) h).symm

/-- **The presentation `P' = Γ(Y, ⊤) → C = Γ(X, ⊤)`**: the map on global sections of the closed
immersion `X ⟶ Y`, as a map of `A`-algebras.  It commutes with the structure maps because the
square on `X`, `Y`, `S₀` and `S` commutes. -/
def liftingPresentation :
    Γ(T.Y, ⊤) →ₐ[(T.affineCrystallineSituation.A : Type u)] T.affineCrystallineSituation.C where
  toRingHom := T.toY.appTop.hom
  commutes' a := by
    change T.toY.appTop.hom (T.toBase.appTop.hom a) = (sourceToBase S).appTop.hom a
    rw [sourceToBase, ← T.cartesian.w, Scheme.Hom.comp_appTop]
    rfl

/-- The presentation is the map on global sections of `X ⟶ Y`. -/
theorem liftingPresentation_apply (x : Γ(T.Y, ⊤)) :
    T.liftingPresentation x = T.toY.appTop.hom x := rfl

/-- The map `X ⟶ Y` of the situation is a closed immersion: it is a thickening, being a base
change of the thickening `S₀ ⟶ S`. -/
theorem isClosedImmersion_toY : IsClosedImmersion T.toY :=
  have := T.isAffine
  have := T.isSmooth
  (isThickening_toY S T.prime_nilpotent T.Y T.toBase T.toY T.cartesian).1

/-- **The presentation is surjective**: `X ⟶ Y` is a closed immersion into an affine scheme. -/
theorem surjective_liftingPresentation [IsAffine T.Y] :
    Function.Surjective T.liftingPresentation := by
  have := T.isClosedImmersion_toY
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine T.toY).2

/-- **`P'` is smooth over `A`**: `Y ⟶ S` is smooth and both schemes are affine, so this is
`HasRingHomProperty.iff_of_isAffine` for `Smooth`. -/
instance smooth_liftingAlgebra [IsAffine T.Y] :
    Algebra.Smooth (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) := by
  have := T.isAffine
  have := T.isSmooth
  exact (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).1 this

/-- The kernel of the presentation is the ideal over `⊤` of the closed subscheme `X ⊆ Y`, which is
the divided power ideal of the object `(X, Y, γ)` on global sections. -/
theorem ker_liftingPresentation_eq_sectionIdeal [IsAffine T.Y] :
    RingHom.ker T.liftingPresentation.toRingHom =
      sectionIdeal T.Y.sheaf (DividedPowerScheme.idealSheafAsSubmodule T.toY.ker) (op ⊤) := by
  have := T.isClosedImmersion_toY
  refine Eq.trans ?_ (DividedPowerScheme.idealSheafAsSubmodule_obj_affine T.toY.ker
    ⟨⊤, isAffineOpen_top T.Y⟩).symm
  rw [Scheme.Hom.ker_apply]
  rfl

/-- **The kernel of the presentation is `I · P'`**, the ideal generated by the image of the divided
power ideal `I` of `A`.  This is `ideal_map_appTop_restrict` at the affine open `⊤ ⊆ Y`. -/
theorem ker_liftingPresentation [IsAffine T.Y] :
    RingHom.ker T.liftingPresentation.toRingHom =
      Ideal.map (algebraMap (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤))
        T.affineCrystallineSituation.A.ideal := by
  have := T.isAffine
  rw [ker_liftingPresentation_eq_sectionIdeal, ← ideal_map_appTop_restrict S T.prime_nilpotent
    T.Y T.toBase T.toY T.cartesian ⟨⊤, isAffineOpen_top T.Y⟩]
  congr 1
  rw [show homOfLE (show (⊤ : T.Y.Opens) ≤ ⊤ from le_top) = 𝟙 _ from Subsingleton.elim _ _,
    op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_comp]
  rfl

/-! ### The envelope -/

/-- A divided power morphism out of divided powers transported along an equality of ideals. -/
private theorem isDPMorphism_cast_left {R B : Type u} [CommRing R] [CommRing B] {J J' : Ideal R}
    (h : J = J') (δ : DividedPowers J') {K : Ideal B} (ε : DividedPowers K) (f : R →+* B) :
    IsDPMorphism (cast (congrArg DividedPowers h).symm δ) ε f ↔ IsDPMorphism δ ε f := by
  subst h
  rfl

/-- A divided power morphism into divided powers transported along an equality of ideals. -/
private theorem isDPMorphism_cast_right {R B : Type u} [CommRing R] [CommRing B]
    {J J' : Ideal R} (h : J = J') (δ : DividedPowers J') {K : Ideal B} (ε : DividedPowers K)
    (f : B →+* R) :
    IsDPMorphism ε (cast (congrArg DividedPowers h).symm δ) f ↔ IsDPMorphism ε δ f := by
  subst h
  rfl

variable [IsAffine T.Y]

/-- The divided powers `γ_Y` of the object `(X, Y, γ)` on global sections, as divided powers on
the kernel of the presentation, transported along `ker_liftingPresentation_eq_sectionIdeal`. -/
def kernelDividedPowers : DividedPowers (RingHom.ker T.liftingPresentation.toRingHom) :=
  cast (congrArg DividedPowers T.ker_liftingPresentation_eq_sectionIdeal).symm
    (crysDividedPowers S T.crystallineThickening.obj)

/-- The structure map `A → P'` is a divided power morphism from `γ` to `γ_Y`: this is
`isDPMorphism_appLE` over the affine opens `⊤` of `S` and of `Y`. -/
theorem isDPMorphism_algebraMap_kernelDividedPowers :
    IsDPMorphism T.affineCrystallineSituation.A.dividedPowers T.kernelDividedPowers
      (algebraMap (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤)) := by
  have := T.isAffine
  have := T.isSmooth
  refine (isDPMorphism_cast_right T.ker_liftingPresentation_eq_sectionIdeal _ _ _).2 ?_
  have h := isDPMorphism_appLE S T.prime_nilpotent T.Y T.toBase T.toY T.cartesian
    ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ (le_preimage_top T.toBase ⊤)
  have e : T.toBase.appLE ⊤ ⊤ (le_preimage_top T.toBase ⊤) = T.toBase.appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [e] at h
  exact h

/-- The divided power envelope `D_{P', γ}(ker f')` is `P'`, as rings: this is
`DividedPowerEnvelope.equivOfExtension`, since `ker f' = I · P'` carries the compatible divided
powers `γ_Y`. -/
def envelopeRingEquiv :
    (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object ≃+*
      Γ(T.Y, ⊤) :=
  DividedPowerEnvelope.equivOfExtension _ T.kernelDividedPowers
    T.isDPMorphism_algebraMap_kernelDividedPowers T.ker_liftingPresentation

/-- **The divided power envelope of the presentation of a smooth lifting is the lifting itself.**
The envelope `D_{P', γ}(ker f')` of `f' = liftingPresentation` is isomorphic as an `A`-algebra to
`P' = Γ(Y, ⊤)`; the isomorphism is a divided power isomorphism onto `γ_Y`
(`isDPMorphism_envelopeEquiv`, `isDPMorphism_envelopeEquiv_symm`) and is a retraction of the
canonical map `P' → D_{P', γ}(ker f')` (`envelopeEquiv_algebraMap`). -/
def envelopeEquiv :
    (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object ≃ₐ[
      (T.affineCrystallineSituation.A : Type u)] Γ(T.Y, ⊤) :=
  AlgEquiv.ofRingEquiv (f := T.envelopeRingEquiv) fun a ↦
    DividedPowerEnvelope.equivOfExtension_structureMap _ _ _ _ a

/-- The isomorphism `D_{P', γ}(ker f') ≃ P'` sends the image of `x : P'` to `x`. -/
theorem envelopeEquiv_algebraMap (x : Γ(T.Y, ⊤)) :
    T.envelopeEquiv
        (IdealPair.Hom.toRingHom
          (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).algebraMap x) =
      x :=
  DividedPowerEnvelope.equivOfExtension_algebraMap _ _ _ T.ker_liftingPresentation x

/-- The inverse of `D_{P', γ}(ker f') ≃ P'` is the canonical map `P' → D_{P', γ}(ker f')`. -/
theorem envelopeEquiv_symm_apply (x : Γ(T.Y, ⊤)) :
    T.envelopeEquiv.symm x =
      IdealPair.Hom.toRingHom
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).algebraMap x :=
  rfl

/-- The isomorphism `D_{P', γ}(ker f') ≃ P'` is a divided power morphism onto the divided powers of
the object `(X, Y, γ)` on global sections. -/
theorem isDPMorphism_envelopeEquiv :
    IsDPMorphism
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object.dividedPowers
      (crysDividedPowers S T.crystallineThickening.obj)
      T.envelopeEquiv.toRingEquiv.toRingHom := by
  have h := DividedPowerEnvelope.equivOfExtension_isDPMorphism
    (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation)
    T.kernelDividedPowers T.isDPMorphism_algebraMap_kernelDividedPowers T.ker_liftingPresentation
  exact (isDPMorphism_cast_right T.ker_liftingPresentation_eq_sectionIdeal _ _ _).1 h

/-- The inverse isomorphism `P' ≃ D_{P', γ}(ker f')` is a divided power morphism from the divided
powers of the object `(X, Y, γ)` on global sections. -/
theorem isDPMorphism_envelopeEquiv_symm :
    IsDPMorphism (crysDividedPowers S T.crystallineThickening.obj)
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object.dividedPowers
      T.envelopeEquiv.symm.toRingEquiv.toRingHom := by
  have h := DividedPowerEnvelope.equivOfExtension_symm_isDPMorphism
    (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation)
    T.kernelDividedPowers T.isDPMorphism_algebraMap_kernelDividedPowers T.ker_liftingPresentation
  exact (isDPMorphism_cast_left T.ker_liftingPresentation_eq_sectionIdeal _ _ _).1 h

/-! ### The completed envelope -/

omit [IsAffine T.Y] in
/-- The ideal `(p)` of the envelope is nilpotent, because `p` is nilpotent in `A`. -/
theorem isNilpotent_pAdicIdeal_envelope :
    IsNilpotent (pAdicIdeal (A :=
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object)
      T.affineCrystallineSituation.p) := by
  obtain ⟨n, hn⟩ := T.prime_nilpotent
  refine ⟨n, ?_⟩
  rw [Ideal.zero_eq_bot, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]
  have hp : ((T.affineCrystallineSituation.p : ℕ) :
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object) =
      (presentationEnvelope T.affineCrystallineSituation
        T.liftingPresentation).structureMap.toRingHom
        ((S.p : ℕ) : (T.affineCrystallineSituation.A : Type u)) := by
    exact (map_natCast (presentationEnvelope T.affineCrystallineSituation
      T.liftingPresentation).structureMap.toRingHom S.p).symm
  have hn' : ((S.p : ℕ) : (T.affineCrystallineSituation.A : Type u)) ^ n = 0 := hn
  rw [hp, ← map_pow, hn', map_zero]

/-- The envelope is its own `p`-adic completion, `(p)` being nilpotent: the canonical map
`D → D^∧` is an isomorphism of `A`-algebras. -/
def envelopeCompletionEquiv :
    (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object ≃ₐ[
      (T.affineCrystallineSituation.A : Type u)]
      AdicCompletion (pAdicIdeal (A :=
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object)
        T.affineCrystallineSituation.p)
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object :=
  haveI := IsAdicComplete.of_isNilpotent _ T.isNilpotent_pAdicIdeal_envelope
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom _ _ _)
    (AdicCompletion.ofLinearEquiv _ _).bijective

omit [IsAffine T.Y] in
/-- The map `D → D^∧` of `envelopeCompletionEquiv` is the canonical map. -/
theorem envelopeCompletionEquiv_apply
    (y : (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object) :
    T.envelopeCompletionEquiv y =
      algebraMap (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object
        (AdicCompletion (pAdicIdeal (A :=
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object)
        T.affineCrystallineSituation.p)
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object) y :=
  rfl

/-- **The completed divided power envelope of the presentation of a smooth lifting is the lifting
itself**: `D^∧ ≃ D ≃ P'` as `A`-algebras. -/
def completedEnvelopeEquiv :
    AdicCompletion (pAdicIdeal (A :=
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object)
        T.affineCrystallineSituation.p)
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object ≃ₐ[
      (T.affineCrystallineSituation.A : Type u)] Γ(T.Y, ⊤) :=
  T.envelopeCompletionEquiv.symm.trans T.envelopeEquiv

/-- The inverse of `D^∧ ≃ P'` sends `x` to the image in the completion of the image of `x` in the
envelope. -/
theorem completedEnvelopeEquiv_symm_apply (x : Γ(T.Y, ⊤)) :
    T.completedEnvelopeEquiv.symm x =
      algebraMap (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object
        _ (IdealPair.Hom.toRingHom
          (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).algebraMap
          x) := by
  rw [completedEnvelopeEquiv, AlgEquiv.symm_trans_apply, AlgEquiv.symm_symm,
    envelopeEquiv_symm_apply]
  exact T.envelopeCompletionEquiv_apply _

/-- **The augmentation is compatible with the identification, pointwise**: the augmentation
`D^∧ → C` of the completed envelope sends the element of `D^∧` corresponding to `x : P'` to
`f' x`. -/
theorem completedEnvelopeAugmentation_completedEnvelopeEquiv_symm_apply (x : Γ(T.Y, ⊤)) :
    completedEnvelopeAugmentation T.affineCrystallineSituation T.liftingPresentation
        T.surjective_liftingPresentation (T.completedEnvelopeEquiv.symm x) =
      T.liftingPresentation x := by
  rw [completedEnvelopeEquiv_symm_apply]
  exact completedEnvelopeAugmentation_algebraMap _ _ _ x

/-- **The augmentation is compatible with the identification**: the augmentation `D^∧ → C`
composed with `P' ≃ D^∧` is the presentation `f'`. -/
theorem completedEnvelopeAugmentation_comp_completedEnvelopeEquiv_symm :
    (completedEnvelopeAugmentation T.affineCrystallineSituation T.liftingPresentation
        T.surjective_liftingPresentation).comp
        T.completedEnvelopeEquiv.symm.toRingEquiv.toRingHom =
      T.liftingPresentation.toRingHom :=
  RingHom.ext T.completedEnvelopeAugmentation_completedEnvelopeEquiv_symm_apply

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW
