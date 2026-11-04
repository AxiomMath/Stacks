module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Formally smooth maps of topological rings

Stacks Project, Chapter 15 "More on Algebra", Section 15.38 "Formally smooth maps
of topological rings", Lemma 15.38.7 (Tag 07EF), with definitions from
Definition 15.38.1 (Tag 07EB) and Section 15.37 (Tag 07E8). The second half of
this file treats the purely algebraic variant "formally smooth for the `n`-adic
topology" and Lemma 15.38.6 (Tag 07EE).

Throughout, all rings are commutative with unit and ring maps are unital. An
ideal `J` of a ring `A` has *square zero* if `J ^ 2 = ⊥`.

## Main definitions

* `RingHom.FormallySmoothTop`: a continuous homomorphism `φ : R →+* S` of topological
  rings is *formally smooth* when every commutative solid diagram

      S  --gbar-->  A/J
      ↑φ            ↑π
      R  ---f--->   A

  with `A` discrete and `J ^ 2 = ⊥` admits a continuous dotted lift
  `g : S →+* A`.
* `RingHom.FormallySmoothNAdic` (Tag 07NI): the variant relative to an ideal `n ⊆ S`, where the
  test map `ψ : S →+* A ⧸ J` is in addition required to kill a power of `n`:

      S  --ψ-->  A / J
      ↑φ           ↑π
      R  --f-->  A

## Main results

* `RingHom.FormallySmoothTop.comp` (Tag 07EF): formal smoothness of continuous ring
  homomorphisms is stable under composition. A composition of continuous maps is
  continuous, so the substantive content is the lifting property.
* `RingHom.FormallySmoothNAdic.mono` (Tag 07EE): formal smoothness for the `n`-adic
  topology implies formal smoothness for the `n'`-adic topology when `n ≤ n'`.
  The content is the elementary inclusion `n ^ k ≤ n' ^ k`, which makes the
  `n'`-side condition on `ψ` the stronger one, so the diagrams to be lifted for
  `n'` form a subset of those for `n`.

## Implementation notes

* Stacks states both results for *linearly topologized* rings (Definition 15.37.1
  / Tag 07E8, `IsLinearTopology` in Mathlib): those for which `0` has a
  fundamental system of neighbourhoods consisting of ideals. Neither lifting
  argument uses that hypothesis, so it is omitted here and the statements are
  correspondingly stronger.
* `RingHom.FormallySmoothNAdic` unwinds the `n`-adic notion into a fully elementary,
  purely algebraic statement requiring no topology, using the equivalent
  characterization (2)(b) of Stacks Lemma 15.38.2 (Tag 07EC).
* Continuity is a genuine hypothesis in `RingHom.FormallySmoothTop`: every map of a
  lifting diagram, including the lift `g`, is required to be continuous, which
  for a map into a discrete ring means that point-preimages are open. The
  discrete topology on a ring yields an `IsTopologicalRing` instance, and `A ⧸ J`
  carries the quotient topology, which is again discrete.
* The test rings `A` range over an arbitrary universe `u`, independent of the
  universes of `R` and `S`: the Stacks statements put no size restriction on `A`.
  Taking `u := 0` recovers the `Type`-valued reading.
-/

universe u v w z

namespace RingHom

/-! ## Formal smoothness of a continuous ring homomorphism -/

/-- A continuous ring homomorphism `φ : R →+* S` of topological rings is
*formally smooth* (Stacks, Tag 07EB) if every lifting problem against a
square-zero thickening of a discrete ring admits a continuous solution.

Given a discrete (hence topological) ring `A`, an ideal `J ⊆ A` with `J ^ 2 = ⊥`,
a continuous `f : R →+* A` and a continuous `gbar : S →+* A ⧸ J` with
`gbar ∘ φ = π ∘ f` (where `π = Ideal.Quotient.mk J` and `A ⧸ J` carries the
discrete quotient topology), there is a continuous ring homomorphism
`g : S →+* A` with `g ∘ φ = f` and `π ∘ g = gbar`. -/
def FormallySmoothTop {R : Type v} {S : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (φ : R →+* S) : Prop :=
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    (J : Ideal A), J ^ 2 = ⊥ →
      ∀ (f : R →+* A), Continuous f →
        ∀ (gbar : S →+* A ⧸ J), Continuous gbar →
          gbar.comp φ = (Ideal.Quotient.mk J).comp f →
          ∃ g : S →+* A, Continuous g ∧ g.comp φ = f ∧
            (Ideal.Quotient.mk J).comp g = gbar

/-! ### Stability under composition -/

/-- Stacks Lemma 15.38.7 (Tag 07EF). A composition of formally smooth continuous
ring homomorphisms of topological rings is formally smooth: if `φ : R →+* S` and
`ψ : S →+* T` are formally smooth and `ψ` is continuous, then `ψ.comp φ` is
formally smooth. Usable as `hsφ.comp hsψ hψ`. Continuity of `ψ.comp φ` is not
part of the conclusion; it follows from `Continuous.comp` given that `φ` is
continuous. -/
@[stacks 07EF]
theorem FormallySmoothTop.comp {R : Type v} {S : Type w} {T : Type z}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] {φ : R →+* S} {ψ : S →+* T}
    (hsφ : FormallySmoothTop.{u, v, w} φ) (hsψ : FormallySmoothTop.{u, w, z} ψ)
    (hψ : Continuous ψ) : FormallySmoothTop.{u, v, z} (ψ.comp φ) := by
  intro A _ _ _ J hJ f hf gbar hgbar hcomm
  -- First lift along φ using formal smoothness of φ.
  -- Lifting problem: f : R →+* A, gbar.comp ψ : S →+* A ⧸ J.
  obtain ⟨h, hhcont, hhφ, hhπ⟩ :=
    hsφ A J hJ f hf (gbar.comp ψ) (hgbar.comp hψ) (by
      rw [RingHom.comp_assoc]
      exact hcomm)
  -- Now lift along ψ using formal smoothness of ψ.
  -- Lifting problem: h : S →+* A, gbar : T →+* A ⧸ J.
  obtain ⟨g, hgcont, hgψ, hgπ⟩ :=
    hsψ A J hJ h hhcont gbar hgbar hhπ.symm
  refine ⟨g, hgcont, ?_, hgπ⟩
  rw [← RingHom.comp_assoc, hgψ, hhφ]

-- ===== merged from StacksDraft.Sec37.Tag07EE =====

/-! ## Formal smoothness for the `n`-adic topology

Following Stacks Tag 07EE (Lemma 15.38.6), the notion "formally smooth for the
`n`-adic topology" is unwound into a fully elementary, purely algebraic statement
requiring no topology, using the equivalent characterization (2)(b) of Stacks
Lemma 15.38.2 (Tag 07EC). -/

/-- `φ : R →+* S` is *formally smooth for the `n`-adic topology*, where `n` is an
ideal of `S`: for every square-zero ideal `J` of a ring `A`, every ring map
`f : R → A`, and every ring map `ψ : S → A ⧸ J` making the square commute and
with `ψ` killing some power of `n` (some `k ≥ 1` with `n ^ k ≤ ker ψ`), there
exists a lift `g : S → A` with
`(Ideal.Quotient.mk J) ∘ g = ψ` and `g ∘ φ = f`. -/
@[stacks 07NI]
def FormallySmoothNAdic {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (φ : R →+* S) (n : Ideal S) : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Ideal A), J ^ 2 = ⊥ →
    ∀ (f : R →+* A) (ψ : S →+* A ⧸ J),
      ψ.comp φ = (Ideal.Quotient.mk J).comp f →
      (∃ k : ℕ, 1 ≤ k ∧ n ^ k ≤ RingHom.ker ψ) →
      ∃ g : S →+* A, (Ideal.Quotient.mk J).comp g = ψ ∧ g.comp φ = f

/-! ### Monotonicity in the ideal -/

/-- Stacks Tag 07EE, Lemma 15.38.6: if `n ≤ n'` are ideals of `S` and `φ : R → S`
is formally smooth for the `n`-adic topology, then it is formally smooth for the
`n'`-adic topology. Usable as `h.mono hnn'`. -/
@[stacks 07EE, ega "0 19.3.8" "adic topologies on S"]
theorem FormallySmoothNAdic.mono {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    {φ : R →+* S} {n n' : Ideal S} (h : FormallySmoothNAdic.{u, v, w} φ n) (hnn' : n ≤ n') :
    FormallySmoothNAdic.{u, v, w} φ n' := by
  intro A _ J hJ f ψ hcomm hk
  obtain ⟨k, hk1, hkle⟩ := hk
  exact h A J hJ f ψ hcomm ⟨k, hk1, (pow_le_pow_left' hnn' k).trans hkle⟩

end RingHom
