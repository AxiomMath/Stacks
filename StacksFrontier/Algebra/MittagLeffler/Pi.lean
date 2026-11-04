module

public import StacksFrontier.Algebra.MittagLeffler.Flat
public import StacksFrontier.RingTheory.Coherent.Basic
public import StacksFrontier.RingTheory.Coherent.Flat

@[expose] public section

universe u v

/-!
# Products of copies of a Noetherian ring are flat and Mittag-Leffler

Let `R` be a Noetherian ring, let `A` be a set and let `M = R^A` be the `R`-module `A → R` of all
functions from `A` to `R`. This file proves that `M` is flat and Mittag-Leffler.

The argument is the source's, and it runs on the canonical comparison map
`TensorProduct.piScalarRightHom R R G A : G ⊗[R] (A → R) →ₗ[R] (A → G)`, which is bijective as soon
as `G` is finitely presented (Stacks 059K). Flatness is Chase's theorem: a Noetherian ring is
coherent (Lemma 05CY), and over a coherent ring the module `R^A` is flat for every `A`
(Proposition 05CZ). For the Mittag-Leffler condition it suffices, by Lemma 059S, to produce for
each finite free `R`-module `F` and each `x ∈ F ⊗[R] M` a smallest submodule `F' ⊆ F` with
`x ∈ F' ⊗[R] M`. Over a Noetherian `R` every submodule of `F` is again finite, hence finitely
presented, so the comparison map is bijective for `F` and for each of its submodules; naturality of
the comparison map in its left factor then identifies `F' ⊗[R] M → F ⊗[R] M` with `(F')^A → F^A`.
Writing `x` as `(x_α) ∈ F^A`, a submodule `N` of `F` satisfies `x ∈ N ⊗[R] M` exactly when every
`x_α` lies in `N`, so the span of the `x_α` is the smallest such submodule.

For a finite set `A` the module `R^A` is free, hence flat and Mittag-Leffler over any ring, so the
content of the statement is in the infinite sets `A`: an infinite product of copies of `R` is
neither free nor projective in general — over `R = ℤ` the module `ℤ^ℕ` is not free, by the
Baer–Specker theorem — and both conclusions can fail once `R` is not coherent.

## Main results

* `Module.flat_and_mittagLeffler_pi`: for a Noetherian ring `R` and a set `A`, the `R`-module
  `R^A` is flat and Mittag-Leffler.

## Implementation notes

Mathlib has no predicate for a Mittag-Leffler *module* — its
`CategoryTheory.Functor.IsMittagLeffler` is the Mittag-Leffler condition on an inverse *system*,
which is condition (4) of Proposition 059E for the system of duals — so being Mittag-Leffler is
spelled out inline in the intrinsic form 059E (1), exactly as in Proposition 059M, Lemma 059S and
Lemma 0AS6: every map `f : P → M` from a finitely presented module dominates and is dominated by
a map `g : P → Q` into a finitely presented module, domination meaning
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. Definition 059F defines "Mittag-Leffler"
to be the equivalent conditions of 059E, and (1) is the one of the five that needs no chosen
directed system, so inlining it is the definition rather than a reformulation. The second conjunct
is therefore the left-hand side of 059M and of 059S and the hypothesis `hML` of 0AS6, with `M`
instantiated at `A → R`.

`M = R^A` is the `R`-module `A → R` with its `Pi` module structure, which is how item (3) of
Chase's theorem 05CZ writes it; nothing is chosen, the module being the product itself.

The two conclusions are stated as one conjunction, as the source states them: they are two
properties of a single module, both consequences of the single hypothesis on `R`. Splitting them
would be worse than unfaithful, since Lemma 059S — the route to the second conjunct — carries
`[Module.Flat R M]`, so a separate Mittag-Leffler statement would have to assume the flatness the
first conjunct proves. The flat conjunct uses only that `R` is coherent, by 05CZ; generalizing it
in that direction is not a sharpening but a duplication of 05CZ item (3), which is already stated
as `IsCoherentRing.tfae_flat_pi`, whereas the Mittag-Leffler conjunct genuinely consumes
Noetherian, through the finite presentation of the submodules of a finite free module.

The set `A` and the ring `R` live in the same universe `Type u`, as they do in item (3) of 05CZ,
so that `M = A → R` lies in `Type u` and the test modules `P`, `Q`, `N` of the Mittag-Leffler
condition range over `Type u` as well; `Small.{u} R` then holds by `small_self`, so that quantifier
is the source's quantifier over all finitely presented `R`-modules, every such module being a
quotient of some `R^n`. An index set `A : Type v` that is merely `Small.{u}` — the shape Lemma
059T needs, its monomials lying in `Type 0` while `R` is arbitrary — is recovered by applying the
statement to `Shrink.{u} A` and transporting both conjuncts along the linear equivalence
`e := LinearEquiv.funCongrLeft R R (equivShrink A).symm : (A → R) ≃ₗ[R] (Shrink.{u} A → R)`: the
first by `Module.Flat.of_linearEquiv`, the second by post-composing the test map `f` with `e`,
which changes no kernel because `LinearMap.rTensor N e` is again an equivalence. So the collapse
costs nothing mathematically, `A` entering only through its cardinality.

The two halves of the argument are separated. `isLeast_span_range_piScalarRightHom` is the whole of
the Mittag-Leffler half: it exhibits the span of the coordinates of `x` as the least submodule `N`
of `F` with `x` in the range of `N.subtype.rTensor (A → R)`, and it needs of `F` only that it is
finite over the Noetherian ring `R`, not that it is free — freeness is a hypothesis of Lemma 059S
that this construction does not consume.

Naturality of `TensorProduct.piScalarRightHom` in the left tensor factor is not in Mathlib; it is
`TensorProduct.piScalarRightHom_rTensor_apply`, proved alongside Chase's theorem 05CZ, which needs
the same square.

Faithfulness. (1) No hypothesis is dead: `IsNoetherianRing R` is consumed by both conjuncts, and
by the first already through coherence — over the non-coherent
`R = k[x, y₁, y₂, …] / (x y₁, x y₂, …)` there is a set `A` with `R^A` not flat, by 05CZ — while
`A` is the source's arbitrary set, on which nothing is assumed. (2) The scalars and the base are
the source's: one commutative ring `R` throughout, `R^A` an `R`-module by the `Pi` structure,
flatness over `R`, every tensor product of the Mittag-Leffler condition over `R` and every map
`R`-linear; nothing is localized or base changed. (3) The source names no canonical map here; the
one map the statement does mention it pins, the Mittag-Leffler condition comparing the kernels of
`LinearMap.rTensor N f` and `LinearMap.rTensor N g` by equality rather than asserting a
factorization to exist. (4) The instantiation is not degenerate: for `R = ℤ` and `A = ℕ` both
conjuncts hold and neither is automatic — `ℤ^ℕ` is flat and Mittag-Leffler but not free, and the
Mittag-Leffler condition genuinely excludes flat modules, `ℚ` over `ℤ` being flat and not
Mittag-Leffler by Example 059I.

## References

* [StacksProject 05D0](https://stacks.math.columbia.edu/tag/05D0)
* [Chase, *Direct products of modules*, Theorem 2.1]
-/

namespace TensorProduct

/-- The comparison map `G ⊗[R] (A → R) → (A → G)` is bijective for a finitely presented module
`G`: this is item (1) ⇒ item (4) of Stacks 059K. -/
private lemma bijective_piScalarRightHom (R : Type u) [CommRing R] [Small.{v} R] (G : Type v)
    [AddCommGroup G] [Module R G] [Module.FinitePresentation R G] (A : Type v) :
    Function.Bijective (piScalarRightHom R R G A) := by
  have h : Module.FinitePresentation R G ↔
      ∀ B : Type v, Function.Bijective (piScalarRightHom R R G B) :=
    (Module.FinitePresentation.tfae_piRightHom_bijective R G).out 1 4
  exact h.mp ‹_› A

end TensorProduct

section MittagLeffler

open TensorProduct LinearMap

/-- The Mittag-Leffler half of Stacks 05D0. Let `R` be Noetherian, let `F` be a finite `R`-module
and let `x ∈ F ⊗[R] (A → R)`. Then the submodule of `F` spanned by the coordinates of `x` under
`TensorProduct.piScalarRightHom` is the least submodule `N` of `F` with `x` in the image of
`N ⊗[R] (A → R) → F ⊗[R] (A → R)`. -/
private theorem isLeast_span_range_piScalarRightHom (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Type u) (F : Type u) [AddCommGroup F] [Module R F] [Module.Finite R F]
    (x : F ⊗[R] (A → R)) :
    IsLeast {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor (A → R))}
      (Submodule.span R (Set.range (piScalarRightHom R R F A x))) := by
  have := Module.finitePresentation_of_finite R F
  have hbijF := bijective_piScalarRightHom R F A
  set F' := Submodule.span R (Set.range (piScalarRightHom R R F A x)) with hF'
  have hmem : ∀ α, piScalarRightHom R R F A x α ∈ F' := fun α => Submodule.subset_span ⟨α, rfl⟩
  constructor
  · have := Module.finitePresentation_of_finite R F'
    obtain ⟨y, hy⟩ := (bijective_piScalarRightHom R F' A).surjective
      fun α => (⟨_, hmem α⟩ : F')
    refine ⟨y, hbijF.injective (funext fun α => ?_)⟩
    rw [piScalarRightHom_rTensor_apply, hy]
    rfl
  · rintro N ⟨y, hy⟩
    rw [hF', Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    rw [← hy, piScalarRightHom_rTensor_apply]
    exact (piScalarRightHom R R (↥N) A y α).2

/-- Let `R` be a Noetherian ring and `A` a set. Then `M = R^A`, the `R`-module of functions
`A → R`, is a flat and Mittag-Leffler `R`-module.

Being Mittag-Leffler is spelled out inline as condition (1) of Proposition 059E: every map
`f : P → M` from a finitely presented `R`-module dominates and is dominated by a map `g : P → Q`
into a finitely presented `R`-module, that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every
`R`-module `N`. -/
@[stacks 05D0 "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M, 059S and
0AS6; `R^A` is the `Pi` module `A → R`, as in item (3) of 05CZ, and the two conclusions are one
conjunction, as in the source. Test data in the universe of `R` and `A`. See the module
docstring."]
theorem Module.flat_and_mittagLeffler_pi (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Type u) :
    Module.Flat R (A → R) ∧
      ∀ (P : Type u) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] (A → R)), ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type u) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  have hchase : IsCoherentRing R ↔ ∀ B : Type u, Module.Flat R (B → R) :=
    (IsCoherentRing.tfae_flat_pi R).out 1 3
  have hflat : Module.Flat R (A → R) := hchase.mp (isCoherentRing_of_isNoetherianRing R) A
  exact ⟨hflat, (Module.mittagLeffler_iff_exists_isLeast_mem_range_rTensor_subtype R (A → R)).mpr
    fun F _ _ _ _ x => ⟨_, isLeast_span_range_piScalarRightHom R A F x⟩⟩

end MittagLeffler

end
