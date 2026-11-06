module


public import StacksFrontier.FieldTheory.Separable.Defs
import StacksFrontier.RingTheory.Smooth.Conormal
import Mathlib.RingTheory.Smooth.Field
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Injectivity of `d` on `I/I²` along a surjection onto a separable field extension

Proof of Stacks 00TU. Let `k` be a field, let `R` be a `k`-algebra and let `R → B` be a
surjection onto a field `B` which is a finitely generated separable extension of `k`, with kernel
`I`. Then the map `d : I/I² → B ⊗[R] Ω[R⁄k]`, `x ↦ 1 ⊗ dx`, is injective.

The content is that `B` is a formally smooth `k`-algebra. Indeed a finitely generated separable
extension is separably generated (Stacks 030O (2), applied to the subextension `B` itself), a
separably generated extension is formally smooth (Stacks 00TW), and for a formally smooth
quotient the conormal sequence `0 → I/I² → B ⊗[R] Ω[R⁄k] → Ω[B⁄k] → 0` of Stacks 00RU is split
short exact, which is Stacks 06A8.

## Main results

* `Stacks.KaehlerDifferential.ConormalKernel.solution`: the statement of Stacks 00TU, namely
  `KaehlerDifferential.kerCotangentToTensor_injective_of_isSeparableExtension`.

## Implementation notes

The source finishes by choosing a `k`-algebra section of `R/I² → B`, so that `R/I² ≅ B ⊕ I/I²` as
`k`-algebras, and retracting `d` by the `k`-derivation `(c, x) ↦ x` of that ring — which is Stacks
02HP. That whole passage, section included, is the already proved Stacks 06A8 stated for a
formally smooth quotient and an arbitrary surjection, so it is used as it stands rather than
redone; 02HP enters through it.

What Stacks 06A8 does not supply is formal smoothness of `B` over `k`, and the source does not
state it separately. It is proved here in two steps, neither of which is in Mathlib:

* `Algebra.FormallySmooth.of_isSeparablyGenerated` is Stacks 00TW. Mathlib's
  `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` is the same statement with the
  separating transcendence basis given as an algebraically independent family rather than as a
  transcendence basis, so only the identification `Set.range ((↑) : s → K) = s` separates the two.
* `Algebra.FormallySmooth.of_isSeparableExtension` specialises the separability of Stacks 030O (2)
  to the subextension `⊤`, whose finite generation over `k` is that of `K` transported along
  `IntermediateField.topEquiv`, and transports formal smoothness back along the same equivalence.
  Transporting the separating transcendence basis of `⊤` to one of `K` instead — so as to get
  `Algebra.IsSeparablyGenerated k K` on the nose — is the same mathematics done by hand, since
  formal smoothness already transports along an equivalence for free.

Both are stated under the weakest hypotheses they use: the first asks nothing of the extension
beyond being separably generated, and the second adds finite generation only, which is where the
separability of Stacks 030O (2) — a condition on the finitely generated subextensions — needs `K`
itself to be one of them.

## References

* [StacksProject 00TU](https://stacks.math.columbia.edu/tag/00TU)
* [StacksProject 00TW](https://stacks.math.columbia.edu/tag/00TW)
* [StacksProject 030O](https://stacks.math.columbia.edu/tag/030O)
* [StacksProject 06A8](https://stacks.math.columbia.edu/tag/06A8)
* [StacksProject 02HP](https://stacks.math.columbia.edu/tag/02HP)
-/

@[expose] public section

/-- **Stacks 00TW.** A separably generated field extension `K/k` is formally smooth over `k`. -/
@[ega "0 19.0.2" "partial",
  ega "0 19.6.1" "special case",
  ega "0 21.5.1" "special case",
  ega "0 22.2.1" "special case"]
private theorem Algebra.FormallySmooth.of_isSeparablyGenerated (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.IsSeparablyGenerated k K] : Algebra.FormallySmooth k K := by
  obtain ⟨s, hs, hsep⟩ :=
    Algebra.IsSeparablyGenerated.isSeparable (k := k) (K := K)
  rw [← Subtype.range_coe (s := s)] at hsep
  exact .of_algebraicIndependent_of_isSeparable hs.1

/-- A finitely generated separable field extension `K/k`, separability being that of
Stacks 030O (2), is formally smooth over `k`: it is one of its own finitely generated
subextensions, hence separably generated, hence formally smooth by Stacks 00TW. -/
@[ega "0 19.0.2" "partial",
  ega "0 19.10.3" "more general",
  ega "0 19.6.1" "special case",
  ega "0 21.5.1" "special case",
  ega "0 22.2.1" "special case", sga "1 III 1.2" "field base, special case"]
private theorem Algebra.FormallySmooth.of_isSeparableExtension (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] [Algebra.IsSeparableExtension k K] :
    Algebra.FormallySmooth k K :=
  have : Algebra.EssFiniteType k (⊤ : IntermediateField k K) :=
    (Algebra.EssFiniteType.iff_of_algEquiv (IntermediateField.topEquiv (F := k) (E := K))).mpr
      inferInstance
  have := Algebra.FormallySmooth.of_isSeparablyGenerated k (⊤ : IntermediateField k K)
  .of_equiv IntermediateField.topEquiv

namespace Stacks.KaehlerDifferential.ConormalKernel

/-- For a surjection `R → B` of `k`-algebras onto a field `B` that is a finitely generated
separable extension of the field `k`, the map `KaehlerDifferential.kerCotangentToTensor k R B`
from `I/I²` to `B ⊗[R] Ω[R⁄k]`, where `I = ker(R → B)`, is injective. -/
@[ega "0 20.6.9" "partial, special case"]
public theorem solution
    (k R B : Type*) [Field k] [CommRing R] [Field B] [Algebra k R] [Algebra R B] [Algebra k B]
    [IsScalarTower k R B] [Algebra.EssFiniteType k B] [Algebra.IsSeparableExtension k B]
    (h : Function.Surjective (algebraMap R B)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R B) :=
  have := Algebra.FormallySmooth.of_isSeparableExtension k B
  (KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange k R B h).1

end Stacks.KaehlerDifferential.ConormalKernel

end

/-!
# Injectivity of `d` on `I/I²` along a surjection onto a separable field extension

Let `k` be a field, let `R` be a `k`-algebra and let `R → B` be a surjection onto a field `B`
with kernel `I`, and assume that `B` is a finitely generated separable extension of `k`. Then the
map `d : I/I² → Ω_{R/k} ⊗_R B`, `x ↦ 1 ⊗ dx`, is injective; equivalently the conormal sequence
`0 → I/I² → Ω_{R/k} ⊗_R B → Ω_{B/k} → 0` of Stacks 00RU is short exact. For `R` local and `B` its
residue field `κ = R/𝔪` this is the source's statement, `I` being `𝔪` and `I/I²` the cotangent
space `𝔪/𝔪²`.

The mathematics is that separability of `B` splits the sequence. A finitely generated separable
extension is separably generated (Stacks 030O (2) applied to the subextension `B` itself), a
separably generated extension is formally smooth over `k` (Stacks 00TW), and formal smoothness
lifts the identity of `B` along the square-zero surjection `R/I² → B`. Such a `k`-algebra section
makes `R/I² ≅ B ⊕ I/I²` as `k`-algebras, and then the `k`-derivation `(c, x) ↦ x` of that ring
into `I/I²` retracts `d`, which is Stacks 02HP.

## Main results

* `KaehlerDifferential.kerCotangentToTensor_injective_of_isSeparableExtension`: the map `d` on
  `I/I²` is injective for a surjection `R → B` onto a finitely generated separable extension `B`
  of the base field.

## Implementation notes

The map `d` is Mathlib's `KaehlerDifferential.kerCotangentToTensor k R B`, the `R`-linear map on
`I/I²` induced by `x ↦ 1 ⊗ dx` for `I = ker(R → B)`
(`KaehlerDifferential.kerCotangentToTensor_toCotangent`), so nothing about it is left to a
choice. Its codomain is the base change `B ⊗[R] Ω[R⁄k]`, whose factors are transposed relative to
the source's `Ω_{R/k} ⊗_R κ` so that the left one carries the scalar action making it a
`B`-vector space.

Generalized in two ways from the source, neither of which the source's proof resists: the
quotient is any surjection onto a field rather than the residue field of a local ring, and `R` is
not assumed Noetherian. The proof replaces `R` by `R/I²`, which is local with nilpotent maximal
ideal `I/I²` whatever `R` was, and for which no finiteness enters; the source itself remarks that
the lemma can be significantly generalized. Taking `B := IsLocalRing.ResidueField R` and
`h := Ideal.Quotient.mk_surjective` returns the source's statement: the kernel of the residue map
is `IsLocalRing.maximalIdeal R` by `IsLocalRing.ker_residue`, and its `Ideal.Cotangent` is
`IsLocalRing.CotangentSpace R`.

That `R` *contains* `k` is `Algebra k R`; the structure map of a `k`-algebra admitting a
surjection onto a field is automatically injective, and the argument uses only the algebra
structure. `IsScalarTower k R B` says that the extension `B/k` is the one induced by `R`, as in
the source, where `κ` is a `k`-algebra through `R`. Finite generation of `B/k` as a field
extension is `Algebra.EssFiniteType k B` (`IntermediateField.essFiniteType_iff`), and
separability in the sense of Stacks 030O (2), which does not presuppose algebraicity, is
`Algebra.IsSeparableExtension k B`; Mathlib's `Algebra.IsSeparable` would be the algebraic case
only.

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead: surjectivity onto the field `B` is what makes `I` play the role of
`𝔪`, `Algebra.IsSeparableExtension` is the separability, and finite generation is what turns it
into a separating transcendence basis for `B` itself; Noetherianness, which the source assumes
and the proof never uses, is dropped rather than carried.
(2) The scalars and the base are the source's: the differentials are over `k`, the base change
and the linearity of `d` are over `R`, and `B` is separable over `k` — not over `R`, nor after a
localization.
(3) The canonical map is pinned, not merely asserted to exist: it is `kerCotangentToTensor`,
which by `kerCotangentToTensor_toCotangent` sends the class of `x ∈ I` to `1 ⊗ dx`.
(4) The instantiation is not degenerate: for `R = k[t]/(t²)` and `B = k` the map is an
isomorphism of one-dimensional `k`-vector spaces `k·t → k·dt`, and the separability hypothesis is
not decoration — for `k = 𝐅_p(u)` and `R = k[x]/((x^p - u)^2)`, whose residue field
`k(u^{1/p})` is purely inseparable over `k`, the source's `d` kills the generator `x^p - u` of
`𝔪/𝔪² ≠ 0` because `d(x^p - u) = p x^{p-1} dx = 0`.

## References

* [Stacks 00TU](https://stacks.math.columbia.edu/tag/00TU)
-/

@[expose] public section

/-- **The differential is injective on `I/I²` for a separable field quotient** (Stacks 00TU).
Let `k` be a field, let `R` be a `k`-algebra and let `R → B` be a surjection onto a field `B`
which is a finitely generated separable extension of `k`. Then `d : I/I² → Ω_{R/k} ⊗_R B`,
`x ↦ 1 ⊗ dx`, is injective, where `I = ker(R → B)`. For `R` local and `B = R/𝔪` this is
injectivity of `d` on `𝔪/𝔪²`. -/
@[stacks 00TU "`d` is `KaehlerDifferential.kerCotangentToTensor k R B`, whose domain
`(RingHom.ker (algebraMap R B)).Cotangent` is `I/I²` and whose codomain `B ⊗[R] Ω[R⁄k]` has the
factors of the source's `Ω_{R/k} ⊗_R κ` transposed, so that the left one carries the `B`-vector
space structure. Finitely generated separable is `Algebra.EssFiniteType` together with the notion
of Stacks 030O (2). Generalized: the quotient is an arbitrary surjection onto a field rather than
the residue field of a local ring, and `R` is not assumed Noetherian; the source's statement is
the case `B := IsLocalRing.ResidueField R`. See the module docstring."]
public theorem KaehlerDifferential.kerCotangentToTensor_injective_of_isSeparableExtension
    (k R B : Type*) [Field k] [CommRing R] [Field B] [Algebra k R] [Algebra R B] [Algebra k B]
    [IsScalarTower k R B] [Algebra.EssFiniteType k B] [Algebra.IsSeparableExtension k B]
    (h : Function.Surjective (algebraMap R B)) :
    Function.Injective (kerCotangentToTensor k R B) := by exact
        Stacks.KaehlerDifferential.ConormalKernel.solution k R B h

end
