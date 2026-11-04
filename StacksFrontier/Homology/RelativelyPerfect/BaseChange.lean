module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.RelativelyPerfect
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.Homology.TorAmplitude.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Relative perfectness under base change of the base ring

Let `R → A` be a flat ring map of finite presentation and let `R → R'` be arbitrary. Then
`A' = A ⊗[R] R'` is again flat and of finite presentation over `R'`, and derived extension of
scalars along `A → A'` carries an object of `D(A)` perfect relative to `R` (Stacks 0DHS) to an
object of `D(A')` perfect relative to `R'`.

## Main results

* `PseudoCoherence.derivedExtensionScalars_isRelativelyPerfect` (Stacks 0DHW).

## Implementation notes

Both halves of relative perfectness are transported by their own providers: pseudo-coherence over
`A'` by Stacks 0650, `StacksDraft.PseudoCoherence.baseChange_preserves_pseudoCoherent`, and Tor
amplitude over `R'` by Stacks 066L,
`StacksDraft.TorAmplitude.hasTorAmplitude_derivedExtendScalars`.

What links the two is that restricting to `R` and then extending to `R'` agrees with extending to
`A'` and then restricting to `R'`. The comparison between them is Stacks 065Z,
`RingTheory.TorIndependence.derivedBaseChangeComparison`, and it is invertible because `A` is flat
over `R`, hence Tor independent from `R'` over `R` (Stacks 0661). Flatness enters only through
that Tor independence, which `torIndependent_of_flat` below records untagged.

Derived extension of scalars is not a bare functor but the datum
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars` of Stacks 064H: a functor
together with its comparison to termwise extension of scalars and the universal property making
it a total left derived functor. Stacks 0661 consumes the last of these as an instance, and
recognizing it behind the bundling needs a relaxed transparency during unification, so the main
theorem repeats the `backward.isDefEq.respectTransparency` option of its provider.

The derived tensor products expressing finite Tor dimension are supplied in the shape of
Stacks 0DHS: a bifunctor with its comparison to termwise tensoring and the corresponding
universal property. All three rings share one universe, which is the generality of the source
statement: the base change square involves four rings and the comparison of Stacks 065Z is stated
with a single module universe common to all of them.

## References

* [The Stacks Project, Lemma 15.85.5 (0DHW)](https://stacks.math.columbia.edu/tag/0DHW)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open CochainComplex.DerivedExtensionScalars RingTheory.TorIndependence
open StacksDraft.PseudoCoherence StacksDraft.TorAmplitude

/-- A flat `R`-algebra `A` is Tor independent from every `R`-algebra `B`: the higher Tor modules
`Torᵢ^R(A, B)` are computed by tensoring a projective resolution of `B` with `A`, and tensoring
with a flat module preserves the exactness of that resolution. This is the hypothesis Stacks 0661
asks for; it carries no tag. -/
@[sga "6 VIII 1.4" "partial"]
lemma torIndependent_of_flat
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R A] :
    TorIndependent R A B := by
  rw [torIndependent_iff_isZero_tor]
  intro p hp
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  let P := ModuleCat.of R A
  let N := ModuleCat.of R B
  refine IsZero.of_iso ?_ ((projectiveResolution N).isoLeftDerivedObj (tensorLeft P) (n + 1))
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp ?_
  rw [HomologicalComplex.exactAt_iff]
  exact ((HomologicalComplex.exactAt_iff _ _).mp
    ((projectiveResolution N).complex_exactAt_succ n)).map_of_preservesLeftHomologyOf (tensorLeft P)

/-- Tor amplitude only depends on the isomorphism class of the object, since every `- ⊗ᴸ M[0]` is
a functor. This is the transport step that moves Tor amplitude across the comparison isomorphism
of Stacks 0661; it carries no tag. -/
private lemma hasTorAmplitude_of_iso
    {R : Type u} [CommRing R]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ M : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    {X Y : DerivedCategory (ModuleCat.{u} R)} (e : X ≅ Y) {a b : ℤ}
    (hX : HasTorAmplitude derivedTensor comparison isLeftDerived X a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived Y a b := fun M i hi ↦
  (hX M i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((derivedTensor.mapIso e).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0DHW.** If `A` is flat and finitely presented over `R`, then arbitrary base change
`R → R'` sends an `R`-perfect object of `D(A)` to an `R'`-perfect object of `D(A ⊗[R] R')`. -/
@[stacks 0DHW]
theorem derivedExtensionScalars_isRelativelyPerfect
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (derivedTensorR :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparisonR : ∀ M : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensorR.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedR : ∀ M : ModuleCat.{u} R,
      (derivedTensorR.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
        (comparisonR M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (derivedTensorR' :
      DerivedCategory (ModuleCat.{u} R') ⥤
        DerivedCategory (ModuleCat.{u} R') ⥤ DerivedCategory (ModuleCat.{u} R'))
    (comparisonR' : ∀ M : ModuleCat.{u} R',
      DerivedCategory.Q ⋙
          derivedTensorR'.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedR' : ∀ M : ModuleCat.{u} R',
      (derivedTensorR'.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj M)).IsLeftDerivedFunctor
        (comparisonR' M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativelyPerfect.{u, u, u} derivedTensorR comparisonR isLeftDerivedR K) :
    let A' := A ⊗[R] R'
    letI : Algebra R' A' := Algebra.TensorProduct.rightAlgebra
    let e : (R' ⊗[R] A) ≃ₐ[R'] A' :=
      AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R R' A).toRingEquiv)
        (fun r' => by
          change (Algebra.TensorProduct.comm R R' A)
            (algebraMap R' (R' ⊗[R] A) r') = _
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
            Algebra.TensorProduct.comm_tmul]
          rfl)
    letI : Module.Flat R' A' := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
    letI : Algebra.FinitePresentation R' A' := Algebra.FinitePresentation.equiv e
    let f : A →+* A' := Algebra.TensorProduct.includeLeftRingHom
    IsRelativelyPerfect.{u, u, u} derivedTensorR' comparisonR' isLeftDerivedR'
      ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · let T := totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')
    exact (baseChange_preserves_pseudoCoherent _ T.comparison T.isLeftDerived K).2 hK.1
  · obtain ⟨a, b, hab⟩ := hK.2
    refine ⟨a, b, ?_⟩
    let Tg := totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')
    let Th := totalDerivedExtensionScalars.{u, u, u} (algebraMap A (A ⊗[R] R'))
    let ResR := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory
    have hbase : HasTorAmplitude derivedTensorR' comparisonR' isLeftDerivedR'
        (Tg.functor.obj (ResR.obj K)) a b :=
      hasTorAmplitude_derivedExtendScalars Tg.functor Tg.comparison Tg.isLeftDerived
        derivedTensorR comparisonR isLeftDerivedR derivedTensorR' comparisonR' isLeftDerivedR'
        (ResR.obj K) a b hab
    let cmp := (derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
      (algebraMap R A) (algebraMap R R') (algebraMap A (A ⊗[R] R'))
      (algebraMap R' (A ⊗[R] R'))
      ((IsScalarTower.algebraMap_eq R A (A ⊗[R] R')).symm.trans
        (IsScalarTower.algebraMap_eq R R' (A ⊗[R] R')))
      Tg.functor Th.functor Tg.comparison Th.comparison).2.1
    have : IsIso cmp := derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u, u,
        u + 1, u + 1, u + 1, u + 1} (R := R) (A := A) (R' := R') (A' := A ⊗[R] R')
      torIndependent_of_flat Tg.functor Th.functor Tg.comparison Th.comparison
    exact hasTorAmplitude_of_iso derivedTensorR' comparisonR' isLeftDerivedR'
      (asIso (cmp.app K)) hbase

end PseudoCoherence
