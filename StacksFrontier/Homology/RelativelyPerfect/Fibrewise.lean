module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.MvPolynomial.Localization
public import StacksFrontier.Homology.PseudoCoherent.FiniteFree
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.Perfect.FibreDescent
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.TorAmplitude.ChangeOfRings
public import StacksFrontier.Homology.TorAmplitude.Defs
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus
public import StacksFrontier.RingTheory.PseudoCoherentMap.Surjection
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public noncomputable section

/-!
# Tor amplitude of a localization from the cohomology of its fibre

Let `R` be a ring, let `A = R[x₁, …, x_d] / I` be flat and of finite presentation over `R`, let
`q ⊂ A` be a prime lying over `p ⊂ R` and let `K ∈ D(A)` be pseudo-coherent. If the cohomology of
`K_q ⊗ᴸ_{R_p} κ(p)` vanishes outside `[a, b]`, then `K_q` has Tor amplitude in `[a - d, b]`
over `R`.

## Main results

* `PseudoCoherence.hasTorAmplitude_localization_of_isZero_homology_fibre` (Stacks 0DJH).

## Implementation notes

The presentation `A = R[x₁, …, x_d] / I` is recorded as a surjective `R`-algebra map from
`MvPolynomial (Fin d) R`, whose kernel is `I`; the prime below `q` is `q.under R`. Localization of
`K` is derived extension of scalars along `A → A_q`, which is the datum
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars` of Stacks 064H — a functor
together with its comparison to termwise extension of scalars and the universal property making
it a total left derived functor. That datum is canonical, so it is used rather than assumed.

The proof is the source's: the presentation interposes the polynomial ring `B = R[x₁, …, x_d]`,
and `R_p → B_{q_B}` is a flat local map whose closed fibre is regular of dimension at most `d`
(`Ideal.isRegularLocalRing_fiberRing_mvPolynomial`,
`Ideal.ringKrullDim_fiberRing_mvPolynomial_le`). Stacks 09PC
(`StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_local_of_regular_closedFibre`) then
bounds the Tor amplitude of `K_q`, viewed over `B_{q_B}`, by `[a - e, b]` where `e` is the exact
fibre dimension; widening `e` to `d` is the last step. Pseudo-coherence of `K_q` over `B_{q_B}` is
what makes Stacks 09PC applicable, and it travels along three providers: Stacks 0650
(`StacksDraft.PseudoCoherence.baseChange_preserves_pseudoCoherent`) for the localization, Stacks
064Z (`StacksDraft.PseudoCoherence.pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars`) for
the restriction from `A_q` to `B_{q_B}`, and Stacks 0E1T
(`PseudoCoherence.pseudoCoherent_tfae_of_surjective`) together with Stacks 066C
(`StacksDraft.PseudoCoherence.extensionScalars_preserves_pseudoCoherent`) for the input that
`A_q` is pseudo-coherent as a `B_{q_B}`-module.

Stacks 09PC is stated in terms of flat representatives rather than a derived tensor product, and
so is Stacks 066J (`StacksDraft.TorAmplitude.hasTorAmplitudeIn_restrictScalars`), which performs
the descent of the amplitude from `R_p` to `R`. The whole middle of the argument therefore runs on
representatives, and Stacks 0654
(`StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative`) converts once, at the end.

The derived tensor product is not canonical in this tree, so — as in Stacks 0DHS and the other
modules of this directory — it is supplied as data: the bifunctor, its comparison with termwise
tensoring and the universal property making each `- ⊗ᴸ M[0]` a total left derived functor. Two
such data are needed, one over `R` for the conclusion and one over `R_p` for the hypothesis. The
hypothesis is converted into the termwise vanishing that Stacks 09PC consumes by
`StacksDraft.TorAmplitude.isIso_comparison_app_of_flat`, which identifies the two on a bounded
above complex of flat modules.

Pseudo-coherence over a ring has one provider in this tree,
`StacksDraft.PseudoCoherence.IsPseudoCoherent`, the constant carrying the Stacks 064Q (2) tag and
the one Stacks 09PC asks for; the shorter spelling `PseudoCoherence.IsPseudoCoherent` is an
`export` alias for it, from `StacksFrontier.Homology.PseudoCoherent.Characterization`, so no
conversion between the two is needed. All rings share one universe, which is the generality of
Stacks 09PC, Stacks 0654 and Stacks 0E1T.

## References

* [The Stacks Project, Lemma 15.84.4 (0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
-/

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

open CochainComplex.DerivedExtensionScalars StacksDraft.TorAmplitude

/-! ### Transport lemmas -/

section Transport

/-- The object `K` of the derived category restricted along `f` is the restriction of a
representing complex. -/
private def restrictScalarsObjIso {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (K : DerivedCategory (ModuleCat.{u} S)) :
    (ModuleCat.restrictScalars f).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)
        |>.obj (DerivedCategory.Q.objPreimage K)) :=
  (ModuleCat.restrictScalars f).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app _

/-- Restricting scalars twice along a factorization agrees with restricting once. -/
private def restrictScalarsCompIso {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (heq : h = g.comp f)
    (K : DerivedCategory (ModuleCat.{u} T)) :
    (ModuleCat.restrictScalars f).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars g).mapDerivedCategory.obj K) ≅
      (ModuleCat.restrictScalars h).mapDerivedCategory.obj K :=
  (ModuleCat.restrictScalars f).mapDerivedCategory.mapIso (restrictScalarsObjIso g K) ≪≫
    (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp' f g h heq).symm (ComplexShape.up ℤ)).app _) ≪≫
    (restrictScalarsObjIso h K).symm

/-- Pseudo-coherence descends along a ring map whose target is pseudo-coherent as a module over
its source, Stacks 064Z read on objects of the derived category. -/
private lemma pseudoCoherent_restrictScalars {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (hS : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := R)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
    (K : DerivedCategory (ModuleCat.{u} S))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K) :=
  StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso
    ((StacksDraft.PseudoCoherence.pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars
      f hS _ 0).2.mp (hK.ofIso (DerivedCategory.Q.objObjPreimageIso K).symm))
    (restrictScalarsObjIso f K).symm

/-- A flat and finitely presented `R`-algebra `A` that is a quotient of a flat and finitely
presented `R`-algebra `B` is pseudo-coherent as a `B`-module. -/
private lemma isModulePseudoCoherent_of_surjective {R B A : Type u} [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (hsurj : Function.Surjective (algebraMap B A)) :
    StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := B)
      ((ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A A)) :=
  StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso
    (((PseudoCoherence.pseudoCoherent_tfae_of_surjective (R := R) hsurj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) 0).1.out
        1 4).mp
      (StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free (ModuleCat.of A A)))
    (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategorySingleFunctor 0).app _)

/-- The underlying module of `A`, restricted along the structure map, is `A` itself. -/
private def restrictScalarsSelfEquiv (B A : Type u) [CommRing B] [CommRing A] [Algebra B A] :
    (ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A A) ≃ₗ[B] A :=
  { __ := Equiv.refl A
    map_add' := fun _ _ => rfl
    map_smul' := fun r x => (Algebra.smul_def r (show A from x)).symm }

/-- Pseudo-coherence of `A` as a `B`-module passes to `A'` as a `B'`-module along a pushout
square whose side `B → B'` is flat. -/
private lemma isModulePseudoCoherent_of_isPushout {B B' A A' : Type u} [CommRing B] [CommRing B']
    [CommRing A] [CommRing A'] [Algebra B B'] [Algebra B A] [Algebra B' A'] [Algebra A A']
    [Algebra B A'] [IsScalarTower B B' A'] [IsScalarTower B A A'] [Module.Flat B B']
    [Algebra.IsPushout B B' A A']
    (hA : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := B)
      ((ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A A))) :
    StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := B')
      ((ModuleCat.restrictScalars (algebraMap B' A')).obj (ModuleCat.of A' A')) := by
  let U := (ModuleCat.restrictScalars (algebraMap B B')).obj (ModuleCat.of B' B')
  let V := (ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A A)
  let : Module B' U := inferInstanceAs (Module B' B')
  have : IsScalarTower B B' U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eU : U ≃ₗ[B'] B' := LinearEquiv.refl B' B'
  let eTensor : U ⊗[B] V ≃ₗ[B'] B' ⊗[B] A :=
    TensorProduct.AlgebraTensorModule.congr eU (restrictScalarsSelfEquiv B A)
  let e : (ModuleCat.extendScalars (algebraMap B B')).obj
      ((ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A A)) ≅
      (ModuleCat.restrictScalars (algebraMap B' A')).obj (ModuleCat.of A' A') :=
    ((eTensor.trans (Algebra.IsPushout.equiv B B' A A').toLinearEquiv).trans
      (restrictScalarsSelfEquiv B' A').symm).toModuleIso
  exact StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso
    ((StacksDraft.PseudoCoherence.extensionScalars_preserves_pseudoCoherent
      (algebraMap B B') (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat B B'))
      ((ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A A))).2 hA)
    ((DerivedCategory.singleFunctor _ 0).mapIso e)

/-- The residue field `κ(p)` is the residue field of the local ring `R_p`, as an `R_p`-module. -/
private def residueFieldModuleIso {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ModuleCat.of (Localization.AtPrime p) p.ResidueField ≅
      ModuleCat.of (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField :=
  (AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField)
    (IsLocalRing.maximalIdeal
      (Localization.AtPrime p)).bijective_algebraMap_quotient_residueField).toLinearEquiv
      |>.toModuleIso

end Transport

/-! ### The fibrewise hypothesis on a flat representative -/

section Fibre

variable {R : Type u} [CommRing R]
  (derivedTensor :
    DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
  (comparison : ∀ N : ModuleCat.{u} R,
    DerivedCategory.Q ⋙
        derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
      (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerived : ∀ N : ModuleCat.{u} R,
    (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
      (comparison N) (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))

include comparison isLeftDerived in
/-- On a bounded above complex of flat modules the certified derived tensor product is computed
termwise, so the vanishing of the cohomology of `Q(P) ⊗ᴸ N[0]` is the vanishing of the cohomology
of the termwise tensor complex `P ⊗ N`. -/
private lemma isZero_homology_tensorComplex (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : BoundedAbove P) (hflat : IsComplexOfFlats P) (N : ModuleCat.{u} R) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((derivedTensor.obj (DerivedCategory.Q.obj P)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)))) :
    IsZero ((tensorComplex P N).homology i) := by
  have := isIso_comparison_app_of_flat comparison isLeftDerived P hbounded hflat N
  exact (h.of_iso (((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (asIso ((comparison N).app P))).symm)).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app (tensorComplex P N)).symm

include comparison isLeftDerived in
/-- Widening the interval weakens Tor amplitude. -/
private lemma hasTorAmplitude_mono (K : DerivedCategory (ModuleCat.{u} R)) {a b a' b' : ℤ}
    (ha : a' ≤ a) (hb : b ≤ b')
    (h : HasTorAmplitude derivedTensor comparison isLeftDerived K a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived K a' b' := by
  intro N i hi
  refine h N i ?_
  simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
  omega

include comparison isLeftDerived in
/-- The vanishing of the cohomology of `K ⊗ᴸ N[0]`, for `K` restricted along a factorization
`R → S → T`, read on a bounded above flat representative and a module isomorphic to `N`. -/
private lemma isZero_homology_tensorComplex_of_restrictScalars {S T : Type u} [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T) (h : R →+* T) (heq : h = g.comp f)
    (K : DerivedCategory (ModuleCat.{u} T)) {N N' : ModuleCat.{u} R} (eN : N ≅ N') (i : ℤ)
    (hK : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((derivedTensor.obj ((ModuleCat.restrictScalars h).mapDerivedCategory.obj K)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))))
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hbdd : BoundedAbove F) (hflat : IsComplexOfFlats F)
    (eF : (ModuleCat.restrictScalars f).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars g).mapDerivedCategory.obj K) ≅ DerivedCategory.Q.obj F) :
    IsZero ((tensorComplex F N').homology i) :=
  isZero_homology_tensorComplex derivedTensor comparison isLeftDerived F hbdd hflat N' i <|
    hK.of_iso <| (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((derivedTensor.obj (DerivedCategory.Q.obj F)).mapIso
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso eN.symm) ≪≫
        (derivedTensor.mapIso (eF.symm ≪≫ restrictScalarsCompIso f g h heq K)).app _)

include comparison isLeftDerived in
/-- Stacks 066J on the derived category: a flat representative in `[a, b]` over a flat
`R`-algebra `T` gives Tor amplitude in `[a, b]` over `R` to anything isomorphic to its
restriction to `R`. -/
private lemma hasTorAmplitude_of_flatRepresentative_restrictScalars {T : Type u} [CommRing T]
    [Algebra R T] [Module.Flat R T] {L : DerivedCategory (ModuleCat.{u} T)} {a b : ℤ}
    (hL : ∃ E : CochainComplex (ModuleCat.{u} T) ℤ, (∀ i : ℤ, Module.Flat T (E.X i)) ∧
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧ Nonempty (L ≅ DerivedCategory.Q.obj E))
    {M : DerivedCategory (ModuleCat.{u} R)}
    (eM : M ≅ (ModuleCat.restrictScalars (algebraMap R T)).mapDerivedCategory.obj L) :
    HasTorAmplitude derivedTensor comparison isLeftDerived M a b := by
  obtain ⟨E, hEflat, hEGE, hELE, ⟨eE⟩⟩ := hL
  obtain ⟨E', hE'flat, hE'GE, hE'LE, ⟨eE'⟩⟩ :=
    hasTorAmplitudeIn_restrictScalars R T E a b ⟨E, hEflat, hEGE, hELE, ⟨Iso.refl _⟩⟩
  exact (hasTorAmplitude_iff_hasFlatRepresentative comparison isLeftDerived M a b).mpr
    ⟨E', hE'flat, hE'GE, hE'LE, ⟨eM ≪≫
      (ModuleCat.restrictScalars (algebraMap R T)).mapDerivedCategory.mapIso eE ≪≫
      (ModuleCat.restrictScalars (algebraMap R T)).mapDerivedCategoryFactors.app E ≪≫ eE'⟩⟩

end Fibre

/-! ### Stacks 0DJH -/

/-- An upper bound on the Krull dimension of a nontrivial ring is attained by an actual
dimension. -/
@[ega "0 16.1.1" "special case"]
private lemma exists_ringKrullDim_eq_of_le {R : Type u} [CommRing R] [Nontrivial R] {d : ℕ}
    (h : ringKrullDim R ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, e ≤ d ∧ ringKrullDim R = (e : WithBot ℕ∞) := by
  have hle : (0 : WithBot ℕ∞) ≤ ringKrullDim R :=
    (zero_le_ringKrullDim_iff_nontrivial (R := R)).mpr inferInstance
  cases hx : ringKrullDim R with
  | bot => simp_all
  | coe x =>
      cases x with
      | top =>
          rw [hx] at h
          norm_cast at h
      | coe e =>
          refine ⟨e, ?_, by simp⟩
          simpa [hx] using h

/-- For a prime `Q` of `R[x₁, …, x_d]` and a local `R`-algebra `S` whose maximal ideal is generated
by `Q.under R`, the closed fibre of `S → R[x₁, …, x_d]_Q` is regular of dimension `e ≤ d`. -/
private lemma isRegularLocalRing_closedFibre_mvPolynomial {R S : Type u} [CommRing R]
    [CommRing S] [IsLocalRing S] {d : ℕ} (Q : Ideal (MvPolynomial (Fin d) R)) [Q.IsPrime]
    [Algebra R S] [Algebra S (Localization.AtPrime Q)]
    [IsScalarTower R S (Localization.AtPrime Q)]
    (hS : (Q.under R).map (algebraMap R S) = IsLocalRing.maximalIdeal S) :
    IsRegularLocalRing (Localization.AtPrime Q ⧸
        (IsLocalRing.maximalIdeal S).map (algebraMap S (Localization.AtPrime Q))) ∧
      ∃ e : ℕ, e ≤ d ∧ ringKrullDim (Localization.AtPrime Q ⧸
        (IsLocalRing.maximalIdeal S).map (algebraMap S (Localization.AtPrime Q))) = e := by
  have hQ : (IsLocalRing.maximalIdeal S).map (algebraMap S (Localization.AtPrime Q)) =
      (Q.under R).map (algebraMap R (Localization.AtPrime Q)) := by
    rw [← hS, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [hQ]
  have := Ideal.isRegularLocalRing_fiberRing_mvPolynomial Q
  exact ⟨this, exists_ringKrullDim_eq_of_le (Ideal.ringKrullDim_fiberRing_mvPolynomial_le Q)⟩

/-- **Stacks 0DJH.** Let `A` be flat and of finite presentation over `R`, presented by `d`
variables, let `q ⊂ A` be a prime lying over `p ⊂ R` and let `K ∈ D(A)` be pseudo-coherent. If the
cohomology of `K_q ⊗ᴸ_{R_p} κ(p)` vanishes outside `[a, b]`, then `K_q` has Tor amplitude in
`[a - d, b]` over `R`. -/
@[stacks 0DJH]
theorem hasTorAmplitude_localization_of_isZero_homology_fibre
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (d : ℕ) (presentation : MvPolynomial (Fin d) R →ₐ[R] A)
    (hpresentation : Function.Surjective presentation)
    (q : Ideal A) [q.IsPrime]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N) (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (fibreTensor :
      DerivedCategory (ModuleCat.{u} (Localization.AtPrime (q.under R))) ⥤
        DerivedCategory (ModuleCat.{u} (Localization.AtPrime (q.under R))) ⥤
          DerivedCategory (ModuleCat.{u} (Localization.AtPrime (q.under R))))
    (fibreComparison : ∀ N : ModuleCat.{u} (Localization.AtPrime (q.under R)),
      DerivedCategory.Q ⋙
          fibreTensor.flip.obj
            ((DerivedCategory.singleFunctor
              (ModuleCat.{u} (Localization.AtPrime (q.under R))) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (fibreIsLeftDerived : ∀ N : ModuleCat.{u} (Localization.AtPrime (q.under R)),
      (fibreTensor.flip.obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (Localization.AtPrime (q.under R))) 0).obj N)).IsLeftDerivedFunctor
        (fibreComparison N)
        (HomologicalComplex.quasiIso
          (ModuleCat.{u} (Localization.AtPrime (q.under R))) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (a b : ℤ)
    (hfibre : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Localization.AtPrime (q.under R))) i).obj
        ((fibreTensor.obj
          ((ModuleCat.restrictScalars
            (algebraMap (Localization.AtPrime (q.under R))
              (Localization.AtPrime q))).mapDerivedCategory.obj
            ((totalDerivedExtensionScalars
              (algebraMap A (Localization.AtPrime q))).functor.obj K))).obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (Localization.AtPrime (q.under R))) 0).obj
              (ModuleCat.of (Localization.AtPrime (q.under R))
                (q.under R).ResidueField))))) :
    HasTorAmplitude derivedTensor comparison isLeftDerived
      ((ModuleCat.restrictScalars
        ((algebraMap A (Localization.AtPrime q)).comp
          (algebraMap R A))).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars
          (algebraMap A (Localization.AtPrime q))).functor.obj K))
      (a - (d : ℤ)) b := by
  let Aq := Localization.AtPrime q
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Kq := (totalDerivedExtensionScalars (algebraMap A Aq)).functor.obj K
  let B := MvPolynomial (Fin d) R
  let : Algebra B A := presentation.toRingHom.toAlgebra
  have : IsScalarTower R B A :=
    IsScalarTower.of_algebraMap_eq fun r => (presentation.commutes r).symm
  let qB : Ideal B := q.under B
  have hp : p = qB.under R := (Ideal.under_under (A := R) (B := B) q).symm
  have : qB.LiesOver p := ⟨hp⟩
  let Bq := Localization.AtPrime qB
  let : Algebra Bq Aq := Localization.AtPrime.algebraOfLiesOver qB q
  let : Algebra Rp Bq := Localization.AtPrime.algebraOfLiesOver p qB
  have : IsScalarTower Rp Bq Aq := inferInstance
  have : IsScalarTower B Bq Aq := inferInstance
  have : Module.Flat R Bq := Module.Flat.trans R B Bq
  have : Module.Flat Rp Bq :=
    (Module.flat_iff_of_isLocalization Rp p.primeCompl Bq).mpr inferInstance
  have : IsLocalHom (algebraMap Rp Bq) :=
    Localization.isLocalHom_localRingHom p qB (algebraMap R B) hp
  have hsurj : Function.Surjective (algebraMap B A) := hpresentation
  have hsub : Algebra.algebraMapSubmonoid A qB.primeCompl = q.primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective q qB hsurj
  have : IsLocalization (Algebra.algebraMapSubmonoid A qB.primeCompl) Aq := by
    rw [hsub]; infer_instance
  have : Algebra.IsPushout B A Bq Aq :=
    Algebra.isPushout_of_isLocalization qB.primeCompl Bq A Aq
  have : Algebra.IsPushout B Bq A Aq := Algebra.IsPushout.symm inferInstance
  -- `A` is pseudo-coherent as a `B`-module, by Stacks 0E1T applied to `A` over itself.
  -- and `A_q` is pseudo-coherent as a `B_{q_B}`-module, by Stacks 066C and the pushout square.
  have hBqAq : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := Bq)
      ((ModuleCat.restrictScalars (algebraMap Bq Aq)).obj (ModuleCat.of Aq Aq)) :=
    isModulePseudoCoherent_of_isPushout (isModulePseudoCoherent_of_surjective (R := R) hsurj)
  -- Pseudo-coherence of `K` survives the localization and the restriction to `B_{q_B}`.
  have hKq : StacksDraft.PseudoCoherence.IsPseudoCoherent Kq :=
    (StacksDraft.PseudoCoherence.baseChange_preserves_pseudoCoherent (algebraMap A Aq)
      (totalDerivedExtensionScalars (algebraMap A Aq)).comparison
      (totalDerivedExtensionScalars (algebraMap A Aq)).isLeftDerived K).2 hK
  let L := (ModuleCat.restrictScalars (algebraMap Bq Aq)).mapDerivedCategory.obj Kq
  -- The closed fibre of `R_p → B_{q_B}` is regular of dimension at most `d`.
  obtain ⟨_, e, hed, hedim⟩ := isRegularLocalRing_closedFibre_mvPolynomial (S := Rp) qB
    (by rw [← hp]; exact IsLocalization.AtPrime.map_eq_maximalIdeal p Rp)
  -- The fibrewise hypothesis, read on an arbitrary bounded above flat representative over `R_p`.
  -- Stacks 09PC over `R_p → B_{q_B}`, then Stacks 066J to descend to `R`.
  exact hasTorAmplitude_mono derivedTensor comparison isLeftDerived _ (by omega) le_rfl
    (hasTorAmplitude_of_flatRepresentative_restrictScalars derivedTensor comparison isLeftDerived
      (StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_local_of_regular_closedFibre
        (A := Rp) (B := Bq) a b e hedim L (pseudoCoherent_restrictScalars _ hBqAq Kq hKq)
        fun F hbdd hflat ⟨eF⟩ i hi => isZero_homology_tensorComplex_of_restrictScalars
          fibreTensor fibreComparison fibreIsLeftDerived (algebraMap Rp Bq) (algebraMap Bq Aq)
          (algebraMap Rp Aq) (IsScalarTower.algebraMap_eq Rp Bq Aq) Kq (residueFieldModuleIso p)
          i (hfibre i hi) F hbdd hflat eF).2.1
      (restrictScalarsCompIso (algebraMap R Bq) (algebraMap Bq Aq)
        ((algebraMap A Aq).comp (algebraMap R A)) (by
          rw [← IsScalarTower.algebraMap_eq R A Aq, ← IsScalarTower.algebraMap_eq R Bq Aq])
        Kq).symm)

end PseudoCoherence
