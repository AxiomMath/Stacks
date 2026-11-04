module

public import StacksFrontier.RingTheory.Length.RingEquiv
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing

/-!
# Formal branches and their multiplicities (Stacks 0DRA, 0DRC)

In the versal situation of **Stacks 0DQU** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a point with `k` a field of finite type
over `S`, and let `A` be a versal ring to `𝒳` at `x₀` in the sense of **Stacks 0DQV**. The *formal
branches* of `𝒳` through `x₀` are the irreducible components of `Spec A`, equivalently the minimal
primes of `A`, and the *multiplicity* of such a branch is the multiplicity of that component of
`Spec A`, namely the length of the local ring of `Spec A` at its generic point.

## Main definitions

* `AlgebraicGeometry.Stack.formalBranches`: **Stacks 0DRA**, relative to a chosen versal ring.
* `AlgebraicGeometry.Stack.formalBranchMultiplicity`: **Stacks 0DRC**, relative to a chosen versal
  ring.

## Main results

* `AlgebraicGeometry.Stack.formalBranchesOrderIsoIrreducibleComponents`: the formal branches
  correspond, reversing inclusion, to the irreducible components of `Spec A`.
* `AlgebraicGeometry.Stack.formalBranchMultiplicity_eq_length`: the multiplicity of a branch is
  the length over itself of any localization of `A` at that branch.
* `AlgebraicGeometry.Stack.formalBranchMultiplicity_eq_length_stalk`: in particular it is the
  length of the local ring of `Spec A` at the generic point of the component.
* `AlgebraicGeometry.Stack.formalBranchMultiplicity_ne_top`: multiplicities are finite.

## Implementation notes

Both definitions are stated relative to a chosen versal ring `A`, which the versality hypothesis
`AlgebraicGeometry.Stack.IsVersalRingAt` records as an argument. The source makes them absolute by
identifying the branches read off two versal rings `A` and `A'` along a formally smooth comparison
map `A → A'`; that identification depends on the existence of such a map (**Stacks 0DQX** together
with **Stacks 0DR1**) and on its uniqueness up to formal homotopy (**Stacks 0DQD**), neither of
which is available here. Only the last step of the identification is, namely that formally
homotopic maps extend a minimal prime to the same ideal
(`Deformation.Ideal.map_eq_of_formallyHomotopic_of_mem_minimalPrimes`, **Stacks 0DQE**).

A branch is recorded as a minimal prime of `A` rather than as a closed subset of `Spec A`: a
minimal prime is at the same time the generic point of the component it cuts out, which is the
point at which the multiplicity of that component is computed. The translation into the literal
reading of the source is
`AlgebraicGeometry.Stack.formalBranchesOrderIsoIrreducibleComponents`.

Multiplicities take values in `ℕ∞` through `Module.length`; finiteness is the separate statement
`AlgebraicGeometry.Stack.formalBranchMultiplicity_ne_top`, which holds because `A` is Noetherian
and so a localization of `A` at a minimal prime is Artinian.

## References

* [Stacks Project, Tag 0DQU](https://stacks.math.columbia.edu/tag/0DQU)
* [Stacks Project, Tag 0DQV](https://stacks.math.columbia.edu/tag/0DQV)
* [Stacks Project, Tag 0DR8](https://stacks.math.columbia.edu/tag/0DR8)
* [Stacks Project, Tag 0DRA](https://stacks.math.columbia.edu/tag/0DRA)
* [Stacks Project, Tag 0DRC](https://stacks.math.columbia.edu/tag/0DRC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (D : VersalSituation.{u, w})
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
  (x₀ : D.𝒳.val.val.obj)
  (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)

/-- **Stacks 0DRA.** The formal branches of `𝒳` through `x₀`, read off a versal ring `A` to `𝒳`
at `x₀`: the irreducible components of `Spec A`, each recorded by its generic point, that is, the
set of minimal primes of `A`. -/
@[stacks 0DRA "relative to a chosen versal ring"]
def formalBranches
    (_hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A) : Set (Ideal A) :=
  minimalPrimes A

variable (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A)

/-- The formal branches read off a versal ring are its minimal primes. -/
theorem formalBranches_eq_minimalPrimes :
    formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA = minimalPrimes A :=
  rfl

/-- An ideal of a versal ring is a formal branch exactly when it is a minimal prime. -/
theorem mem_formalBranches_iff {p : Ideal A} :
    p ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA ↔ p ∈ minimalPrimes A :=
  Iff.rfl

/-- A formal branch is a prime ideal of the versal ring. -/
theorem isPrime_of_mem_formalBranches {p : Ideal A}
    (hp : p ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA) : p.IsPrime :=
  hp.1.1

/-- **The formal branches are the irreducible components of `Spec A`.** A component is cut out by
the generic prime it contains, so the larger component corresponds to the smaller prime and the
bijection reverses the order. -/
def formalBranchesOrderIsoIrreducibleComponents :
    formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA ≃o
      (irreducibleComponents (PrimeSpectrum A))ᵒᵈ :=
  minimalPrimes.equivIrreducibleComponents A

/-- **The closed subset cut out by a formal branch is an irreducible component of `Spec A`.** -/
theorem zeroLocus_mem_irreducibleComponents_of_mem_formalBranches {p : Ideal A}
    (hp : p ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA) :
    PrimeSpectrum.zeroLocus (p : Set A) ∈ irreducibleComponents (PrimeSpectrum A) := by
  rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents, (hp.1.1 : p.IsPrime).radical]
  exact hp

/-- **There are finitely many formal branches.** A versal ring is Noetherian, so it has finitely
many minimal primes. -/
theorem formalBranches_finite :
    (formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA).Finite :=
  minimalPrimes.finite_of_isNoetherianRing A

/-- **Stacks 0DRC.** The multiplicity of a formal branch of `𝒳` through `x₀`: the multiplicity of
the corresponding irreducible component of `Spec A`, that is, the length over itself of the local
ring of `Spec A` at the generic point of that component. -/
@[stacks 0DRC "relative to a chosen versal ring"]
def formalBranchMultiplicity {p : Ideal A}
    (hp : p ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA) : ℕ∞ :=
  letI : p.IsPrime := hp.1.1
  Module.length (Localization.AtPrime p) (Localization.AtPrime p)

/-- **The multiplicity of a formal branch is the length of any localization of the versal ring at
it.** The local ring of `Spec A` at the generic point of the corresponding component is such a
localization. -/
theorem formalBranchMultiplicity_eq_length {p : Ideal A}
    (hp : p ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA)
    (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite A hA hp = Module.length S S :=
  letI : p.IsPrime := hp.1.1
  Module.length_eq_of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) S).toRingEquiv

/-- **The multiplicity of a formal branch is the length of the stalk of `Spec A` at its generic
point.** This is the multiplicity of an irreducible component of a locally Noetherian scheme in
the sense of **Stacks 0DR8**, applied to `Spec A`. -/
theorem formalBranchMultiplicity_eq_length_stalk {p : Ideal A}
    (hp : p ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA) :
    formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite A hA hp =
      Module.length ((structurePresheafInCommRingCat A).stalk ⟨p, hp.1.1⟩)
        ((structurePresheafInCommRingCat A).stalk ⟨p, hp.1.1⟩) :=
  letI : p.IsPrime := hp.1.1
  Module.length_eq_of_ringEquiv (StructureSheaf.stalkIso A ⟨p, hp.1.1⟩).toRingEquiv

/-- **The multiplicity of a formal branch is finite.** A versal ring is Noetherian and a minimal
prime has height zero, so the localization at a branch is an Artinian local ring. -/
theorem formalBranchMultiplicity_ne_top {p : Ideal A}
    (hp : p ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite A hA) :
    formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite A hA hp ≠ ⊤ := by
  have hprime : p.IsPrime := hp.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp _
  have : IsNoetherianRing (Localization.AtPrime p) := by
    unfold Localization.AtPrime; infer_instance
  have : IsArtinianRing (Localization.AtPrime p) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact Module.length_ne_top

end AlgebraicGeometry.Stack

end
