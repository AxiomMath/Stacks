module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Vanishing of local cohomology after inverting an element of the support ideal

Let `I` be a finitely generated ideal of a commutative ring `A`. If an element `f ∈ I` acts
invertibly on an object `K` of `D(A)`, then the local cohomology of `K` with support in `V(I)`
vanishes.

## Main results

* `Dualizing.localCohomology_isZero_of_isIso_smul` — local cohomology vanishes when an element
  of the support ideal acts invertibly.

## Implementation notes

The hypothesis is phrased in the derived category as invertibility of the scalar endomorphism
`f • 𝟙 K`; this covers in particular complexes of modules over the localization `A_f`. Local
cohomology is `Dualizing.localCohomologyFunctor`, valued in the full subcategory of derived
objects with `I`-power-torsion cohomology, so the vanishing is tested after applying the
inclusion into `D(A)`, which is fully faithful.

## References

* [Stacks Project, Tag 0A6M](https://stacks.math.columbia.edu/tag/0A6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- An `I`-power-torsion module on which some `f ∈ I` acts invertibly is zero: the invertible
action of `f` makes multiplication by every power of `f` injective, while torsion kills some
power of `f` on each element. -/
private lemma isIPowerTorsion_subsingleton_of_isIso_smul
    (A : Type u) [CommRing A] (I : Ideal A) {f : A} (hf : f ∈ I)
    (M : ModuleCat.{v} A) (htors : IsIPowerTorsion A M I)
    (hiso : IsIso (f • 𝟙 M)) : Subsingleton M := by
  have hpow : ∀ n : ℕ, Function.Injective (fun x : M => f ^ n • x) := by
    intro n
    induction n with
    | zero => intro x y hxy; simpa using hxy
    | succ n ih =>
      intro x y hxy
      have hinj : Function.Injective (fun x : M => f • x) :=
        (ModuleCat.mono_iff_injective (f • 𝟙 M)).mp inferInstance
      exact hinj (ih (by simpa only [pow_succ, mul_smul] using hxy))
  refine ⟨fun x y => ?_⟩
  obtain ⟨n, hn, hkill⟩ := htors (x - y)
  exact sub_eq_zero.mp ((hpow n) (by simpa using hkill (f ^ n) (Ideal.pow_mem_pow hf n)))

/-- Local cohomology is `A`-linear on scalar endomorphisms: being a right adjoint to an
`A`-linear functor, it sends `r • 𝟙 K` to `r • 𝟙` of its value. -/
private lemma localCohomologyFunctor_map_smul_id
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{v} A)) (r : A) :
    (localCohomologyFunctor A I hI).map (r • 𝟙 K) =
      r • 𝟙 ((localCohomologyFunctor A I hI).obj K) := by
  let adj : (derivedPowerTorsionProperty A I hI).ι ⊣
      localCohomologyFunctor A I hI :=
    localCohomologyAdjunction A I hI
  apply (adj.homEquiv _ K).symm.injective
  rw [adj.homEquiv_counit, adj.homEquiv_counit]
  simp only [Functor.map_smul, Linear.smul_comp]
  have h := adj.counit.naturality (r • 𝟙 K)
  simpa [Functor.comp_map, Linear.comp_smul] using h

/-- An object of the derived category of modules is zero exactly when every cohomology module
is a subsingleton. -/
private lemma isZero_iff_forall_homology_subsingleton
    (A : Type u) [CommRing A] (X : DerivedCategory (ModuleCat.{v} A)) :
    IsZero X ↔ ∀ n : ℤ,
      Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj X) := by
  rw [Coreflection.isZero_iff_zero_isIso, DerivedCategory.isIso_iff]
  refine forall_congr' fun n => ?_
  rw [(DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).map_zero,
    ← Coreflection.isZero_iff_zero_isIso, ModuleCat.isZero_iff_subsingleton]

/-- **Stacks 0A6M.** If some `f ∈ I` acts invertibly on `K`, then its local cohomology with
support in `V(I)` is zero. -/
@[stacks 0A6M]
theorem localCohomology_isZero_of_isIso_smul
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{v} A))
    (f : A) (hf : f ∈ I) (hiso : IsIso (f • 𝟙 K)) :
    IsZero ((localCohomologyFunctor A I hI).obj K) := by
  let F := localCohomologyFunctor A I hI
  let P := derivedPowerTorsionProperty A I hI
  let ι := P.ι
  let X := F.obj K
  have hιiso : IsIso (f • 𝟙 (ι.obj X)) := by
    have hmap := Functor.map_isIso (F ⋙ ι) (f • 𝟙 K)
    dsimp [Functor.comp_map] at hmap
    rw [localCohomologyFunctor_map_smul_id A I hI K f] at hmap
    exact hmap
  have hzero : IsZero (ι.obj X) := by
    rw [isZero_iff_forall_homology_subsingleton]
    intro n
    have hhomIso : IsIso
        (f • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj (ι.obj X))) := by
      let : Functor.Linear A (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n) :=
        DerivedCategory.homologyFunctor_linear (C := ModuleCat.{v} A) A n
      simpa using Functor.map_isIso
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n) (f • 𝟙 (ι.obj X))
    exact isIPowerTorsion_subsingleton_of_isIso_smul A I hf
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj (ι.obj X))
      (X.2 n) hhomIso
  exact IsZero.of_full_of_faithful_of_isZero ι X hzero

end Dualizing
