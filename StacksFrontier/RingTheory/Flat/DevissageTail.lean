module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Pi
public import StacksFrontier.RingTheory.Flat.DevissageElementaryNeighborhood

/-!
# The tail of a complete dévissage

A complete dévissage of `N/S/R` presents `N` through a finite chain of modules `M₀, …, Mₙ`
together with maps `αᵢ : Bᵢ^(⊕ rᵢ) → Mᵢ` whose cokernel at stage `i` is the module at stage
`i + 1`, the last cokernel being zero. The induction step of Stacks 05I3 says that each `αᵢ` is
injective; this file supplies the remaining half of Stacks 05I4, namely the recursion that runs
down the chain and assembles the stages into a statement about `N` itself.

Two conclusions are drawn by the same downward recursion:

* `N` is a direct sum of the finite free modules `Bᵢ^(⊕ rᵢ)` as an `R`-module, once each `Bᵢ` is
  `R`-projective, and
* `N` is a finitely presented `S`-module, with no projectivity needed.

## Main definitions

There are no new definitions.

## Main results

* `Module.isScalarTower_compHom`: restricting a `B`-module along an `R`-algebra map `A →ₐ[R] B`
  and along `algebraMap R B` gives a scalar tower over `R`.
* `Module.nonempty_linearEquiv_directSum_of_exact_chain` is the recursion in purely
  module-theoretic form: a chain of short exact sequences `0 → Gᵢ → Pᵢ → Pᵢ₊₁ → 0` with
  `Gₙ ≅ Pₙ` and every `Gᵢ` projective exhibits `P₀` as `⨁ᵢ Gᵢ`.
* `Module.CompleteDevissage.nonempty_linearEquiv_directSum` is the decomposition half of
  Stacks 05I4 for a complete dévissage whose maps `αᵢ` are injective and whose lower algebras
  are `R`-projective.
* `Module.CompleteDevissage.finitePresentation_of_injective_alpha` is the finite-presentation
  half of Stacks 05I4 for a complete dévissage whose maps `αᵢ` are injective.

## Implementation notes

The recursion is stated for an abstract chain rather than for a complete dévissage, so that the
induction on the length of the chain is an induction on a natural number with the families
`Gᵢ`, `Pᵢ` as parameters. Phrasing the chain by maps `Pᵢ → Pᵢ₊₁` which are exact at `Pᵢ` avoids
the quotient `Pᵢ ⧸ range αᵢ`, whose scalars are those of the stage algebra and not of `R`.

Every stage module `Mᵢ` carries three module structures here: over `Aᵢ`, which is the one the
dévissage records; over `Bᵢ` or `Bᵢ₋₁`, by restriction along `toLeft i` or `toRight i`; and over
`R`, by restriction along `algebraMap R (Aᵢ)`. `Module.isScalarTower_compHom` records that
restricting an `R`-algebra map always produces a scalar tower over `R`, which is what makes the
`αᵢ` and the cokernel identifications `R`-linear.

Stacks 05I4 derives the injectivity of `αᵢ` from Stacks 05I3, whose library form
`Module.flat_localizedModule_tfae_of_projective` carries an extra `Module.Projective R S`
hypothesis coming from Stacks 05FT, and derives the projectivity of `Bᵢ` from Stacks 05FT
directly. Neither is available yet, so both appear here as hypotheses. The recursion itself is
independent of Stacks 05FT.

## References

* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
-/

@[expose] public section

open scoped DirectSum

universe u v w

namespace Module

/-- Restricting scalars along an `R`-algebra map `φ : A →ₐ[R] B` and along `algebraMap R B`
turns a `B`-module into a scalar tower over `R`. -/
public theorem isScalarTower_compHom (R A B M : Type*) [CommSemiring R] [CommSemiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [AddCommMonoid M] [Module B M] (φ : A →ₐ[R] B) :
    letI : Module A M := Module.compHom M φ.toRingHom
    letI : Module R M := Module.compHom M (algebraMap R B)
    IsScalarTower R A M := by
  let : Module A M := Module.compHom M φ.toRingHom
  let : Module R M := Module.compHom M (algebraMap R B)
  refine ⟨fun x a m => ?_⟩
  show φ (x • a) • m = algebraMap R B x • (φ a • m)
  rw [Algebra.smul_def, map_mul, φ.commutes, mul_smul]

/-- **The tail recursion of a dévissage, in module-theoretic form.** Let `0 → Gᵢ → Pᵢ → Pᵢ₊₁ → 0`
be a chain of short exact sequences of `R`-modules for `i < k`, let `Gₖ → Pₖ` be an isomorphism,
and let every `Gᵢ` be projective. Then `P₀` is the direct sum of the `Gᵢ`. -/
public theorem nonempty_linearEquiv_directSum_of_exact_chain {R : Type u} [CommRing R] (k : ℕ)
    (G : Fin (k + 1) → Type v) (P : Fin (k + 1) → Type w)
    [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, Module.Projective R (G i)]
    (f : ∀ i, G i →ₗ[R] P i) (g : ∀ i : Fin k, P i.castSucc →ₗ[R] P i.succ)
    (hinj : ∀ i, Function.Injective (f i))
    (hlast : Function.Surjective (f (Fin.last k)))
    (hexact : ∀ i : Fin k, Function.Exact (f i.castSucc) (g i))
    (hsurj : ∀ i : Fin k, Function.Surjective (g i)) :
    Nonempty (P 0 ≃ₗ[R] ⨁ i, G i) := by
  induction k with
  | zero =>
    let : Unique (Fin (0 + 1)) := ⟨⟨0⟩, fun i => Fin.ext (Nat.lt_one_iff.mp i.isLt)⟩
    have e : ((t : Fin (0 + 1)) → G t) ≃ₗ[R] G 0 := LinearEquiv.piUnique R G
    exact ⟨(LinearEquiv.ofBijective (f 0) ⟨hinj 0, hlast⟩).symm ≪≫ₗ e.symm ≪≫ₗ
      (DirectSum.linearEquivFunOnFintype R _ G).symm⟩
  | succ k ih =>
    obtain ⟨e⟩ := ih (fun i => G i.succ) (fun i => P i.succ) (fun i => f i.succ)
      (fun i => g i.succ) (fun i => hinj i.succ) hlast (fun i => hexact i.succ)
      (fun i => hsurj i.succ)
    have : Module.Projective R (P (0 : Fin (k + 1)).succ) := Module.Projective.of_equiv' e.symm
    obtain ⟨l, hl⟩ := (g 0).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (hsurj 0))
    exact ⟨((hexact 0).splitSurjectiveEquiv (hinj 0) ⟨l, hl⟩).1 ≪≫ₗ
      (LinearEquiv.refl R (G 0)).prodCongr (e ≪≫ₗ DirectSum.linearEquivFunOnFintype R _ _) ≪≫ₗ
      Fin.consLinearEquiv R G ≪≫ₗ (DirectSum.linearEquivFunOnFintype R _ G).symm⟩

namespace CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {r : Ideal R} [r.IsPrime]

/-- **Stacks Project, Tag 05I4, the decomposition**, with the injectivity of the maps `alpha i`
and the projectivity of the lower algebras as hypotheses rather than consequences of Stacks 05I3
and Stacks 05FT.

A complete dévissage whose maps `alpha i` are injective and whose lower algebras are projective
over the base decomposes the original module into the finite free modules `B i ^ (⊕ r i)`. -/
public theorem nonempty_linearEquiv_directSum [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissage R S N r)
    (hinj : ∀ i, letI : Module (D.B i) (D.M i) :=
        Module.compHom (D.M i) (D.toLeft i).toRingHom
      Function.Injective (D.alpha i))
    (hproj : ∀ i, Module.Projective R (D.B i)) :
    Nonempty (N ≃ₗ[R] ⨁ i : Fin (D.stepCount + 1), (Fin (D.multiplicity i) →₀ D.B i)) := by
  let : ∀ i, Module (D.B i) (D.M i) := fun i =>
    Module.compHom (D.M i) (D.toLeft i).toRingHom
  let : ∀ i, Module R (D.M i) := fun i =>
    Module.compHom (D.M i) (algebraMap R (D.A i))
  let : ∀ i, IsScalarTower R (D.B i) (D.M i) := fun i =>
    Module.isScalarTower_compHom R (D.B i) (D.A i) (D.M i) (D.toLeft i)
  have hprojG : ∀ i, Module.Projective R (Fin (D.multiplicity i) →₀ D.B i) := by
    intro i
    have : Module.Projective R (D.B i) := hproj i
    exact Module.Projective.of_equiv'
      (DirectSum.linearEquivFunOnFintype R (Fin (D.multiplicity i)) (fun _ => D.B i) ≪≫ₗ
        (Finsupp.linearEquivFunOnFinite R (D.B i) (Fin (D.multiplicity i))).symm)
  let : ∀ i, Module.Projective R (Fin (D.multiplicity i) →₀ D.B i) := hprojG
  let : ∀ i : Fin D.stepCount, Module (D.B i.castSucc) (D.M i.succ) := fun i =>
    Module.compHom (D.M i.succ) (D.toRight i).toRingHom
  have hg : ∀ i : Fin D.stepCount, IsScalarTower R (D.B i.castSucc) (D.M i.succ) := fun i =>
    Module.isScalarTower_compHom R (D.B i.castSucc) (D.A i.succ) (D.M i.succ) (D.toRight i)
  refine (nonempty_linearEquiv_directSum_of_exact_chain D.stepCount
    (fun i => Fin (D.multiplicity i) →₀ D.B i) D.M
    (fun i => (D.alpha i).restrictScalars R)
    (fun i =>
      let := hg i
      (((D.cokerEquiv i).toLinearMap ∘ₗ
        (LinearMap.range (D.alpha i.castSucc)).mkQ).restrictScalars R))
    hinj D.final_surjective
    (fun i =>
      (D.cokerEquiv i).injective.comp_exact_iff_exact.mpr
        (LinearMap.exact_map_mkQ_range _))
    (fun i => (D.cokerEquiv i).surjective.comp (Submodule.mkQ_surjective _))).map fun e => ?_
  let : Module S (D.M 0) := Module.compHom (D.M 0) D.toA₀.toRingHom
  let : IsScalarTower R S (D.M 0) :=
    Module.isScalarTower_compHom R S (D.A 0) (D.M 0) D.toA₀
  exact (D.initialEquiv.restrictScalars R) ≪≫ₗ e

/-- Every stage module of a complete dévissage whose maps `alpha i` are injective is finitely
presented over the lower algebra at that stage.

The recursion runs downwards from the last stage, where `alpha` is bijective and so presents the
stage module as a finite free module. -/
private theorem finitePresentation_lower [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N r)
    (hinj : ∀ i, letI : Module (D.B i) (D.M i) :=
        Module.compHom (D.M i) (D.toLeft i).toRingHom
      Function.Injective (D.alpha i))
    (i : Fin (D.stepCount + 1)) :
    letI : Module (D.B i) (D.M i) := Module.compHom (D.M i) (D.toLeft i).toRingHom
    Module.FinitePresentation (D.B i) (D.M i) := by
  let : ∀ i, Module (D.B i) (D.M i) := fun i =>
    Module.compHom (D.M i) (D.toLeft i).toRingHom
  let : ∀ i, Algebra (D.B i) (D.A i) := fun i => (D.toLeft i).toRingHom.toAlgebra
  let : ∀ i, IsScalarTower (D.B i) (D.A i) (D.M i) := fun i =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : ∀ i, Module.Finite (D.B i) (D.A i) := fun i =>
    RingHom.finite_algebraMap.mp (D.left_finite i)
  let : ∀ i, Algebra.FinitePresentation (D.B i) (D.A i) := fun i =>
    RingHom.finitePresentation_algebraMap.mp (left_finitePresentation D i)
  induction i using Fin.reverseInduction with
  | last =>
    exact (LinearEquiv.finitePresentation_iff
      (LinearEquiv.ofBijective (D.alpha (Fin.last D.stepCount))
        ⟨hinj _, D.final_surjective⟩)).mp inferInstance
  | cast i ih =>
    let : Module (D.B i.castSucc) (D.M i.succ) :=
      Module.compHom (D.M i.succ) (D.toRight i).toRingHom
    let : Algebra (D.B i.castSucc) (D.A i.succ) := (D.toRight i).toRingHom.toAlgebra
    let : IsScalarTower (D.B i.castSucc) (D.A i.succ) (D.M i.succ) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : Module.Finite (D.B i.castSucc) (D.A i.succ) :=
      RingHom.finite_algebraMap.mp
        (RingHom.Finite.of_surjective (D.toRight i).toRingHom (D.transition_surjective i))
    let : Algebra.FinitePresentation (D.B i.castSucc) (D.A i.succ) :=
      RingHom.finitePresentation_algebraMap.mp (D.transition_finitePresentation i)
    have hupper : Module.FinitePresentation (D.A i.succ) (D.M i.succ) :=
      (Module.FinitePresentation.restrictScalars_iff
        (D.B i.succ) (D.A i.succ) (D.M i.succ)).mp ih
    have hcoker : Module.FinitePresentation (D.B i.castSucc)
        (D.M i.castSucc ⧸ LinearMap.range (D.alpha i.castSucc)) :=
      (LinearEquiv.finitePresentation_iff (D.cokerEquiv i)).mpr
        ((Module.FinitePresentation.restrictScalars_iff
          (D.B i.castSucc) (D.A i.succ) (D.M i.succ)).mpr hupper)
    exact Module.FinitePresentation.of_exact_fst (D.alpha i.castSucc)
      (LinearMap.range (D.alpha i.castSucc)).mkQ (LinearMap.exact_map_mkQ_range _)
      (hinj i.castSucc) (Submodule.mkQ_surjective _)

/-- **Stacks Project, Tag 05I4, finite presentation**, with the injectivity of the maps
`alpha i` as a hypothesis rather than a consequence of Stacks 05I3.

A finite module over a finitely presented algebra which admits a complete dévissage whose maps
`alpha i` are injective is finitely presented. -/
public theorem finitePresentation_of_injective_alpha [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N r)
    (hinj : ∀ i, letI : Module (D.B i) (D.M i) :=
        Module.compHom (D.M i) (D.toLeft i).toRingHom
      Function.Injective (D.alpha i)) :
    Module.FinitePresentation S N := by
  let : Module (D.B 0) (D.M 0) := Module.compHom (D.M 0) (D.toLeft 0).toRingHom
  exact ((finitePresentation_iff_initial_over_upper D).trans
    (finitePresentation_iff_initial_over_lower D)).mpr (finitePresentation_lower D hinj 0)

end CompleteDevissage

end Module

end
