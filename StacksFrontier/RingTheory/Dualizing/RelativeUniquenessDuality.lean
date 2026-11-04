module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Homothety
public import StacksFrontier.RingTheory.Dualizing.RelativeBiduality

/-!
# Uniqueness of relative dualizing complexes, through duality

Let `R → A` be flat of finite presentation, `B = A ⊗[R] A`, let `p₁, p₂ : A → B` be the two
coprojections and `Δ : B → A` the multiplication map.  [stacks 0E2D] asserts that any two
relative dualizing complexes for `R → A` are isomorphic, and the source proves it from the
tensor--Hom diagonal of [stacks 0BYN] at the two derived base changes, citing [stacks 0ATK] (3).

`StacksFrontier.RingTheory.Dualizing.RelativeUniqueness` and
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed` carry out that argument with the
invertibility of the two diagonals carried as the hypothesis `hdiag`, and record how far the
hypothesis can be reduced.  It reduces to a condition **on the ring** `A`: every
bounded-below acyclic complex of flat `A`-modules is pure acyclic.  That is not a theorem for
every ring — Positselski constructs bounded-below noncontractible acyclic complexes of finitely
generated projectives over certain rings of infinite matrices — so that reduction cannot be the
end of the story for a tag whose statement is true.

**This file records that the reduction is an artefact of the chain-level model, not of the tag.**
There is a second route to [stacks 0E2D] which never forms the tensor--Hom diagonal, never asks
for a K-flat representative of a base change, and whose remaining obligation is a condition on
`ω` and on `P` rather than on the ring.  That obligation is **not** a theorem — the section
"What is left" below states it exactly, and it is false at the witness this route was built to
reach — so what this file establishes is that the two routes stall at different places, not that
this one is finished.  Its two halves are described below; the `D(A)`-side half is proved here,
in full and with nothing carried.

## The duality route

Write `Δ^!(-) = RHom_B(A_B, -) : D(B) → D(A)` for the derived coextension of scalars of
[stacks 0A70] along the multiplication map, as `Dualizing.derivedHom` does, and
`T(X) = Δ^!(p₁^*X)` for the functor the defining condition of [stacks 0E2C] is about: `K` is a
relative dualizing complex exactly when it is `R`-perfect and `T(K) ≅ A`.

*Step 1 (the `D(B)` half, partly formalized in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessHomCommutation`).* `T` commutes with derived
Hom out of a pseudo-coherent object:

> `T(RHom_A(M, N)) ≅ RHom_A(M, T(N))` for `M` pseudo-coherent and `N` bounded below.

This is **four adjunctions and no criterion**: flat base change for derived Hom along the flat
coprojection `p₁` turns `p₁^*RHom_A(M, N)` into `RHom_B(p₁^*M, p₁^*N)` — that is [stacks 0A6A],
whose third case is exactly "`p₁` flat, `M` pseudo-coherent, `N` bounded below", available as
`Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange`; the currying isomorphism of
[stacks 0A65] (`StacksDraft.DerivedHom.derivedHomCurrying`) moves `A_B` across; the projection
formula identifies `A_B ⊗ᴸ_B p₁^*M` with the restriction `Δ_*M`; and the adjunction
`Δ_* ⊣ Δ^!` of [stacks 0A70] (`Dualizing.derivedHomAdjunction`) finishes.  **All four are now in
the library**: the third, which used to be available only in its `p₁`-restricted form
`Dualizing.nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso`, is
`Dualizing.nonempty_tensor_diagonalObject_iso_restrictScalars_lmul` of
`StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormula`, proved at an arbitrary retraction
of an arbitrary ring map and with no flatness, perfection or boundedness hypothesis.

The second, third and fourth do compose, unconditionally, into
`Dualizing.nonempty_derivedHom_modelHom_iso_restrictScalars_modelHom`, and the first is available
in the route's own vocabulary as `Dualizing.nonempty_diagonalDerivedExtension_derivedHom_iso` —
both in `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessHomCommutation`.  The two fragments
are joined in `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare`, where the
library's two internal-Hom bifunctors at one universe are reconciled naturally by adjoint
uniqueness, and the enriched form of `Δ_* ⊣ Δ^!` that the join still needed is proved in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessEnrichedAdjunction`.  **Step 1 is therefore
a theorem**, `Dualizing.nonempty_relativeDualizingFunctor_modelHom_commutation`, with no
hypothesis beyond those of [stacks 0A6A] (3).

*Step 2 (this file).* Suppose `ω` is a relative dualizing complex which is in addition a
dualizing complex for `A` in the sense of [stacks 0A7B].  Writing `D(-) = RHom_A(-, ω)` and
`P = D(K)`, biduality [stacks 0A7C] gives `K ≅ D(P)`, so Step 1 at `M = P`, `N = ω` turns the
defining condition of `K` into

> `RHom_A(P, A) ≅ A`,  `P = RHom_A(K, ω)`,

because `T(ω) ≅ A` is the defining condition of `ω`.  **No complex of flat modules appears, and
no acyclicity condition on the ring is involved.**  What is left is the implication

> `RHom_A(P, A) ≅ A`  ⟹  `P ≅ A`   for `P` with bounded coherent cohomology,

and `Dualizing.nonempty_iso_of_dual_iso_one` below then returns `K ≅ ω`, which is the tag.

## Why `ω` may be assumed dualizing, and where that is available

Over a Noetherian `R` admitting a dualizing complex `ω_R`, the upper-shriek complex
`φ^!(ω_R)` is a dualizing complex for `A` — `Dualizing.PolynomialPresentation`'s
`upperShriekFunctor_isDualizingComplex`, [stacks 0BZL] — and for `R` regular of finite dimension
one may take `ω_R = R`, so that `ω_{A/R} = φ^!(R)` is at once the relative dualizing complex of
[stacks 0E2E] and a dualizing complex for `A`.  **For `R` a field this is unconditional**
(`Dualizing.isDualizingComplex_single_self_field`), and that is exactly the case in which the
witness `R = k`, `A = k[x, y]/(x, y)²`, `ω = Hom_k(A, k)` lives — the witness at which all four
invertibility criteria for [stacks 0BYN] fail and at which the left/left `hdiag` is false.  So
the duality route reaches the hardest recorded case of the tag, which the diagonal route does
not.

## The remaining implication, and the one bound its proposed proof cannot produce

`RHom_A(P, A) ≅ A ⟹ P ≅ A` was to be proved as follows, and the argument is recorded here
because it is what distinguishes this route from the diagonal one: *it uses no property of `A`
beyond Noetherian.*  **It does use a property of `ω` and of `P`, and that is where the route now
stands: see the next-but-one section.**

Since `RHom_A(ω, ω) ≅ A` for a dualizing complex, `RHom_A(P, A) ≅ RHom_A(P ⊗ᴸ_A ω, ω)`, so
biduality turns the hypothesis into `P ⊗ᴸ_A ω ≅ ω`.  Localize at a prime and put
`T = ω ⊗ᴸ_A κ`, which is nonzero because `ω` is; then `P ⊗ᴸ_A T ≅ T`.  The cohomology of `T` is
killed by the maximal ideal, so filtering `T` by its cohomology makes the extremal nonvanishing
degrees add: the top and bottom nonvanishing degrees of `P ⊗ᴸ_A T` are those of `T` shifted by
those of `P ⊗ᴸ_A κ`.  Hence `P ⊗ᴸ_A κ` is concentrated in degree `0`, and a length count makes it
one-dimensional there, so `P` is perfect with a rank-one fibre at every maximal ideal —
`IsLocallyShiftedUnit` by
`DerivedCategory.Invertible.isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank` — hence an
invertible module `I` in degree zero, and `RHom_A(I, A) ≅ A` forces `I ≅ A`.  The library has:
`068U` at the maximal ideal for the nonvanishing, `068V`/`0BCC` for "fibre concentrated ⟹
perfect, with a free representative", `0FNT` and
`Dualizing.exists_iso_single_of_isLocallyShiftedUnit` for the endgame, and
`Dualizing.nonempty_iso_one_of_tensor_iso_one_of_hom_iso_one` below for the last line.

### The degree half of that computation is now a theorem, carried to this file's own tensor

**The extremal-degree Künneth statement is a theorem**, as
`StacksDraft.ExtremalDegrees.extremalDegrees` of `StacksFrontier.Homology.Tor.ExtremalDegrees`: for
an exact functor `F` of derived categories and a bounded `T`, the bottom and top nonvanishing
degrees of `F(T)` are those of `T` shifted by those of `F` on the single complexes of the
cohomology modules of `T` — the bounds by the truncation induction, the two nonvanishing
assertions by the long exact sequence of the truncation triangle at either end.

**Its hypotheses at `F = P ⊗ᴸ_A -` are a theorem as well**, and the obligation they used to
leave open — the comparison of `P ⊗ᴸ_A N[0]` with `P ⊗ᴸ_A κ` for an `A`-module `N` killed by the
maximal ideal, equal cohomological window and nonvanishing at both ends when `N ≠ 0` — is
discharged by `StacksDraft.ResidueDevissage.of_residueField` of
`StacksFrontier.Homology.Tor.ResidueDevissage`, the dévissage of a `κ`-vector space, which is no
condition on `A`.  Its nonvanishing half needs neither exactness of the functor nor finiteness of
`N`: the residue field is a retract of every nonzero module killed by `m`, and any functor at all
carries a retraction to a retraction.  Its window half is the induction on a finite spanning set,
stated once for an arbitrary property of the target closed under isomorphism, holding at zero
objects and two-out-of-three in the middle along a distinguished triangle; `isGE₂` and `isLE₂`
then give the two bounds.  The two are assembled into
`StacksDraft.ResidueDevissage.extremalDegrees_of_isTorsionBySet`.

**Reading the conclusion back off the fixed object is also a theorem.**  The rigidity argument
uses the Künneth step only at `P ⊗ᴸ_A T ≅ T`, and
`StacksDraft.ExtremalDegrees.extremalDegrees_eq_zero_of_iso` says that in that situation both
shifts are forced to vanish, so that `P ⊗ᴸ_A κ` is concentrated in degree zero.

**And all of that now applies to *this file's* tensor.**  The tensor of
`StacksDraft.DerivedHom.DerivedHomAdjunction`, in which every statement below is phrased, is a
bifunctor on a product category and carries no shift and no exactness data whatsoever, so the
theorems above did not literally apply to it.
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessResidueWindow` builds the missing slice of
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` — the one with the *first* variable fixed —
and transports the shift commutation and the exactness across it, so that `P ⊗ᴸ_A -` is exact
here as a theorem and not as a hypothesis.  Its conclusion,
`Dualizing.eq_zero_of_derivedTensor_iso_of_isTorsionBySet`, is the first step of the local
computation stated in this file's vocabulary, with no condition on `A` at all.

### The local computation is a theorem, and so is the endgame

1. **The length count is a theorem.**  Degree concentration is not enough; the argument needs
   `P ⊗ᴸ_A κ` to be *one-dimensional* in degree zero, and the extremal-degree theorem sees only
   which degrees are nonzero, never how large they are.  That count is
   `StacksDraft.ResidueLength.nonempty_homology_iso_residueField_of_iso_of_isTorsionBySet` of
   `StacksFrontier.Homology.Tor.ResidueLength`, carried to this route's own tensor as
   `Dualizing.nonempty_homology_derivedTensor_iso_residueField_of_isTorsionBySet`.  It runs
   entirely in the category of `A`-modules: the bottom cohomology module of `T` is a positive
   finite power `κⁿ`, an additive functor carries that to the power of the image, and a
   `κ`-dimension count on `G(κ)ⁿ ≅ κⁿ` gives `dim_κ G(κ) = 1`.  The derived half is the
   degeneration `H^a(F(T)) ≅ H⁰(F(H^a(T)[0]))`, which needs only the *lower* window bound — so
   the length count and the degree count are independent of each other.  No condition on `A` is
   used.

2. **Concentrated-and-one-dimensional fibres ⟹ the endgame is a theorem.**  The library's chain —
   `DerivedCategory.Invertible.isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank`, then
   `0FNT`, then `Dualizing.nonempty_iso_one_of_tensor_iso_one_of_hom_iso_one` below for the last
   line `RHom_A(I, A) ≅ A ⟹ I ≅ A` — is composed in
   `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessPerfectionChain` as
   `Dualizing.nonempty_iso_derivedTensorUnit_of_maximalFibre_finrank`, over an arbitrary
   commutative ring.  The bridge that composition needed, between the monoidal structure of
   [stacks 0FNQ] that `0FNT` speaks about and the tensor of [stacks 0A63] that this file is
   phrased in, is proved there as well.

### What is left

One thing: a **cohomological lower bound on the two fibres**, which is not a condition on the
ring but is not a theorem either.

**Step 1, the `D(B)` half described above, is no longer among them.**  Its last ingredient — the
**enriched** form of `Δ_* ⊣ Δ^!`, `p₁_* RHom_B(Δ_*M, Y) ≅ RHom_A(M, Δ^!Y)`, whose Yoneda
reduction needs the projection formula `Δ_*(Z ⊗ᴸ_A M) ≅ Δ_*Z ⊗ᴸ_B p₁^*M` *naturally in `Z`*,
which `Dualizing.nonempty_tensor_diagonalObject_iso_restrictScalars_lmul` of
`StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormula` supplies only pointwise — is
`Dualizing.enrichedDiagonalHomIso` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessEnrichedAdjunction`, on the strength of
`Dualizing.diagonalProjectionNatIso` of
`StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormulaNatural`, which is that projection
formula as an isomorphism of functors.  Step 1 itself is
`Dualizing.nonempty_relativeDualizingFunctor_modelHom_commutation`, and
`Dualizing.nonempty_modelHom_dual_iso_of_relativeDualizingCondition` of the same module already
spends it: from the defining condition of [stacks 0E2C] at `ω` and at `K`, and biduality at `K`,
it produces `RHom_A(P, 1) ≅ 1` with `P = RHom_A(K, ω)` — which is exactly the hypothesis `hP` of
`Dualizing.nonempty_derivedHom_iso_one_of_isIso_bidualityMor` and of
`Dualizing.nonempty_tensor_iso_of_hom_iso_one` below.  So what remains of the route is the local
computation alone.

**Its glue steps are no longer among them either.**  The change of spelling of the fibre — the
length count and the degree count are about `P ⊗ᴸ_A κ[0]` as an object of `D(A)`, with the
`A`-module structure of its cohomology, while the perfection chain states its hypothesis for
`(totalDerivedExtensionScalars (algebraMap A m.ResidueField)).functor.obj P` in
`D(m.ResidueField)` and a `finrank` over `m.ResidueField` — is
`StacksFrontier.Homology.Perfect.DerivedTensorFibre` for the canonical derived tensor product of
[stacks 068I] and `Dualizing.maximalFibre_finrank_of_fibre_concentrated` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation` for this file's tensor; the
fixed object `P ⊗ᴸ_A T ≅ T` at `T = ω ⊗ᴸ_A κ` is `Dualizing.tensorResidueIso`; perfectness of `P`
from fibre concentration is `Dualizing.isPerfect_of_fibre_concentrated`; and the degree count and
the length count are run together, the first discharging the lower-bound hypothesis of the
second, by `Dualizing.fibre_eq_residueField_of_derivedTensor_iso_of_isTorsionBySet`, whose
conclusion feeds `Dualizing.nonempty_iso_derivedTensorUnit_of_fibre_concentrated` — the endgame
in one statement, with no hypothesis on `A`.

**What is genuinely left is the lower bound.**  The degree count reads the extremal nonvanishing
degrees of cohomological windows it is *given*: `T.IsGE a` for `T = ω ⊗ᴸ_A κ` and
`(P ⊗ᴸ_A κ).IsGE c`.  For a pseudo-coherent factor that is finite Tor dimension at `m`, which a
dualizing complex does not have — at the witness `R = k`, `A = k[x, y]/(x, y)²`,
`ω = Hom_k(A, k)` of `StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation`, `ω` is not
free over the Artinian local `A`, hence has infinite projective dimension, hence
`Tor_i^A(ω, κ) ≠ 0` for every `i` and `ω ⊗ᴸ_A κ` is unbounded below.  And by [stacks 068V] such a
bound on the fibre is of the same strength as perfectness of the factor: with `ω` and `P` both
perfect so is `K ≅ RHom_A(P, ω)`, and [stacks 0E2D] is then already
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange`.  So the route
reaches the hardest recorded case of the tag only if the local computation is redone **one-sided**
— the top of the window alone, where no such bound is needed; the documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation` records what that would
take, and the first of the three things it names is now a theorem,
`StacksDraft.ExtremalDegrees.extremalDegrees_top` of
`StacksFrontier.Homology.Tor.ExtremalDegreesTop`: the extremal top degree adds for an `X` bounded
only above, provided the functor is way-out right exact, which `P ⊗ᴸ_A -` is.  The two that
remain are a top-end mirror of the length count and a rigidity step that is not a degree count
at all.

Beyond the route itself, `ω` has to be a dualizing complex for `A` as well as a relative dualizing
complex, which is where the next section's two cases come in.

## Main definitions

* `Dualizing.tensorOneRightIso` — the right unitor, from the symmetry and a left unitor.
* `Dualizing.homOneSourceIso` — **the unit law for internal Hom**, `RHom(1, M) ≅ M`.
* `Dualizing.tensorShuffleIso` — the shuffle `(Z ⊗ᴸ Y) ⊗ᴸ X ≅ (Z ⊗ᴸ X) ⊗ᴸ Y`.
* `Dualizing.homSourceSwapIso` — **internal Hom is symmetric in its two sources**,
  `RHom(X, RHom(Y, M)) ≅ RHom(Y, RHom(X, M))`.
* `Dualizing.homCurryIso` — **the currying isomorphism** of [stacks 0A65],
  `RHom(X ⊗ᴸ Y, M) ≅ RHom(X, RHom(Y, M))`, for an abstract adjunction.
* `Dualizing.homIso` — internal Hom applied to a pair of isomorphisms.
* `Dualizing.homOmegaDualIso` — **the duality conversion**: `RHom(ω, RHom(P, ω)) ≅ RHom(P, 1)`
  once `RHom(ω, ω) ≅ 1`.

## Main results

* `Dualizing.nonempty_iso_of_dual_iso_one` — **the last link of the duality route.** If
  biduality holds at `K` for `ω` and the `ω`-dual `RHom(ω ← K)` of `K` is the tensor unit, then
  `K ≅ ω`.  At the adjunction of [stacks 0A63] over a Noetherian ring this is
  `Dualizing.nonempty_iso_of_dualizingDerivedHom_iso_derivedTensorUnit`, whose only hypotheses
  are that `ω` is a dualizing complex, that `K` has finite cohomology in every degree, and that
  `RHom_A(K, ω) ≅ A`.
* `Dualizing.nonempty_derivedHom_iso_one_of_isIso_bidualityMor` — **the hypothesis of
  `Dualizing.nonempty_iso_of_isIso_evaluation` discharged.** That theorem — the conversion step
  of `StacksFrontier.RingTheory.Dualizing.RelativeBiduality`, which [stacks 0E2D] is after — needs
  `RHom_A(ω, K) ≅ A`, and its module documentation records that the defining condition of
  [stacks 0E2C] does not supply it, living as it does in `D(A ⊗[R] A)`.  It is supplied here,
  from `RHom_A(RHom_A(K, ω), A) ≅ A` and nothing else: that is the output of Step 1 above.  At
  the adjunction of [stacks 0A63] this is
  `Dualizing.nonempty_derivedHom_iso_derivedTensorUnit_of_dualDual`.
* `Dualizing.nonempty_tensor_iso_of_hom_iso_one` — **the first step of the rigidity argument**:
  `RHom(P, 1) ≅ 1` is `P ⊗ᴸ ω ≅ ω`, given biduality at `P ⊗ᴸ ω`. So the obligation the duality
  route leaves open is reduced here to the local computation alone, whose degree half is
  `Dualizing.eq_zero_of_derivedTensor_iso_of_isTorsionBySet` of
  `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessResidueWindow` and whose length half is
  `Dualizing.nonempty_homology_derivedTensor_iso_residueField_of_isTorsionBySet` of the same
  module.
* `Dualizing.nonempty_iso_one_of_tensor_iso_one_of_hom_iso_one` — an object with a tensor
  inverse whose internal Hom into the unit is the unit is itself the unit.  This is the last
  line of the rigidity argument above, and it is the one place where
  `Dualizing.isIso_evaluation_of_tensor_iso_one` is used positively rather than as a refutation.

## Implementation notes

Everything is proved for an abstract `StacksDraft.DerivedHom.DerivedHomAdjunction` with a chosen
tensor unit and left unitor, as `StacksFrontier.RingTheory.Dualizing.RelativeBiduality` is, and the
only coherence used is naturality of the symmetry, of the associator and of the unitor: never
the pentagon, the hexagon or the unitor triangle.  In particular the currying isomorphism of
[stacks 0A65] is *not* used — it is a field only of the model-level
`StacksDraft.DerivedHom.DerivedHomCurrying`, not of `DerivedHomAdjunction`, and the two
isomorphisms this file needs are instead obtained from the Hom equivalence by Yoneda, which is
why `Dualizing.homSourceSwapIso` needs no invertibility hypothesis anywhere.  For the same
reason the symmetry is never assumed involutive: the inverse of
`Dualizing.homSourceSwapIso` is written with the inverse of the shuffle rather than with the
shuffle of the transposed pair.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0BZL](https://stacks.math.columbia.edu/tag/0BZL)
-/

@[expose] public section

open CategoryTheory

namespace Dualizing

open StacksDraft.DerivedHom

noncomputable section

universe u₁ v₁ w₁

section Abstract

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (d : DerivedHomAdjunction R) (one : DerivedCategory (ModuleCat.{v₁} R))
    (lam : ∀ K : DerivedCategory (ModuleCat.{v₁} R), d.tensor.obj (one, K) ≅ K)

/-- The right unitor of a tensor unit with a chosen left unitor: the symmetry followed by the
left unitor. -/
def tensorOneRightIso (X : DerivedCategory (ModuleCat.{v₁} R)) :
    d.tensor.obj (X, one) ≅ X :=
  d.tensorSwap X one ≪≫ lam X

/-- The right unitor is natural, by naturality of the symmetry and of the left unitor. -/
theorem tensorOneRightIso_naturality
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    {X Y : DerivedCategory (ModuleCat.{v₁} R)} (f : X ⟶ Y) :
    d.tensor.map (show (X, one) ⟶ (Y, one) from (f, 𝟙 one)) ≫
        (tensorOneRightIso d one lam Y).hom =
      (tensorOneRightIso d one lam X).hom ≫ f := by
  dsimp only [tensorOneRightIso, Iso.trans_hom]
  rw [← Category.assoc, d.tensorSwap_naturality, Category.assoc, hlam f, Category.assoc]

/-- Naturality of the right unitor, read on inverses. -/
theorem tensorOneRightIso_inv_naturality
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    {X Y : DerivedCategory (ModuleCat.{v₁} R)} (f : X ⟶ Y) :
    (tensorOneRightIso d one lam X).inv ≫
        d.tensor.map (show (X, one) ⟶ (Y, one) from (f, 𝟙 one)) =
      f ≫ (tensorOneRightIso d one lam Y).inv := by
  rw [← cancel_epi (tensorOneRightIso d one lam X).hom, Iso.hom_inv_id_assoc,
    ← Category.assoc, ← tensorOneRightIso_naturality d one lam hlam f, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **The unit law for internal Hom**: `RHom(1, M) ≅ M`. Transposing a morphism `Z ⟶ RHom(1, M)`
gives a morphism `Z ⊗ᴸ 1 ⟶ M`, and the right unitor identifies `Z ⊗ᴸ 1` with `Z`; the two
operations are natural in `Z`, so Yoneda produces the isomorphism. Only naturality of the
symmetry and of the unitor is used. -/
def homOneSourceIso (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (M : DerivedCategory (ModuleCat.{v₁} R)) :
    d.hom.obj (Opposite.op one, M) ≅ M :=
  Yoneda.ext _ _
    (fun {Z} a => (tensorOneRightIso d one lam Z).inv ≫ d.homEquiv Z one M a)
    (fun {Z} b => (d.homEquiv Z one M).symm ((tensorOneRightIso d one lam Z).hom ≫ b))
    (fun {Z} a => by
      simp only [Iso.hom_inv_id_assoc, AddEquiv.symm_apply_apply])
    (fun {Z} b => by
      simp only [AddEquiv.apply_symm_apply, Iso.inv_hom_id_assoc])
    (fun {Z Z'} f g => by
      rw [d.homEquiv_naturality_left, ← Category.assoc,
        tensorOneRightIso_inv_naturality d one lam hlam f, Category.assoc])

/-- The shuffle isomorphism `(Z ⊗ᴸ Y) ⊗ᴸ X ≅ (Z ⊗ᴸ X) ⊗ᴸ Y`: associate, interchange the two
right factors, associate back. -/
def tensorShuffleIso (X Y Z : DerivedCategory (ModuleCat.{v₁} R)) :
    d.tensor.obj (d.tensor.obj (Z, Y), X) ≅ d.tensor.obj (d.tensor.obj (Z, X), Y) :=
  d.tensorAssoc Z Y X ≪≫ tensorIso d (Iso.refl Z) (d.tensorSwap Y X) ≪≫
    (d.tensorAssoc Z X Y).symm

/-- Naturality of the associator in its outer factor, with the identity of a tensor product on
the right. -/
private theorem tensorAssoc_naturality_id (X Y : DerivedCategory (ModuleCat.{v₁} R))
    {Z Z' : DerivedCategory (ModuleCat.{v₁} R)} (f : Z' ⟶ Z) :
    d.tensor.map ((d.tensor.map ((f, 𝟙 X) : (Z', X) ⟶ (Z, X)), 𝟙 Y) :
          (d.tensor.obj (Z', X), Y) ⟶ (d.tensor.obj (Z, X), Y)) ≫
        (d.tensorAssoc Z X Y).hom =
      (d.tensorAssoc Z' X Y).hom ≫
        d.tensor.map ((f, 𝟙 (d.tensor.obj (X, Y))) :
          (Z', d.tensor.obj (X, Y)) ⟶ (Z, d.tensor.obj (X, Y))) := by
  have h := d.tensorAssoc_naturality f (𝟙 X) (𝟙 Y)
  have hid : ((𝟙 X, 𝟙 Y) : ((X, Y) : _ × _) ⟶ (X, Y)) = 𝟙 (X, Y) := rfl
  rw [hid, CategoryTheory.Functor.map_id] at h
  exact h

/-- The shuffle isomorphism is natural in the outer factor, by naturality of the associator and
of the symmetry. -/
theorem tensorShuffleIso_naturality (X Y : DerivedCategory (ModuleCat.{v₁} R))
    {Z Z' : DerivedCategory (ModuleCat.{v₁} R)} (f : Z' ⟶ Z) :
    d.tensor.map ((d.tensor.map ((f, 𝟙 Y) : (Z', Y) ⟶ (Z, Y)), 𝟙 X) :
          (d.tensor.obj (Z', Y), X) ⟶ (d.tensor.obj (Z, Y), X)) ≫
        (tensorShuffleIso d X Y Z).hom =
      (tensorShuffleIso d X Y Z').hom ≫
        d.tensor.map ((d.tensor.map ((f, 𝟙 X) : (Z', X) ⟶ (Z, X)), 𝟙 Y) :
          (d.tensor.obj (Z', X), Y) ⟶ (d.tensor.obj (Z, X), Y)) := by
  have hone := tensorAssoc_naturality_id d X Y f
  have htwo := tensorAssoc_naturality_id d Y X f
  dsimp only [tensorShuffleIso, tensorIso, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom]
  simp only [Category.assoc]
  rw [reassoc_of% htwo, ← cancel_mono (d.tensorAssoc Z X Y).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hone, Iso.inv_hom_id_assoc]
  simp only [Category.id_comp, Category.comp_id,
    ← d.tensor.map_comp, prod_comp]

/-- **Internal Hom is symmetric in its two sources**:
`RHom(X, RHom(Y, M)) ≅ RHom(Y, RHom(X, M))`. A morphism out of `Z` into either side transposes
twice into a morphism out of a triple tensor product, and the two triple products differ by the
shuffle isomorphism; both operations are natural in `Z`. No invertibility hypothesis is needed,
and the currying isomorphism of [stacks 0A65] is not used. -/
def homSourceSwapIso (X Y M : DerivedCategory (ModuleCat.{v₁} R)) :
    d.hom.obj (Opposite.op X, d.hom.obj (Opposite.op Y, M)) ≅
      d.hom.obj (Opposite.op Y, d.hom.obj (Opposite.op X, M)) :=
  Yoneda.ext _ _
    (fun {Z} a => (d.homEquiv Z Y (d.hom.obj (Opposite.op X, M))).symm
      ((d.homEquiv (d.tensor.obj (Z, Y)) X M).symm
        ((tensorShuffleIso d X Y Z).hom ≫
          d.homEquiv (d.tensor.obj (Z, X)) Y M
            (d.homEquiv Z X (d.hom.obj (Opposite.op Y, M)) a))))
    (fun {Z} b => (d.homEquiv Z X (d.hom.obj (Opposite.op Y, M))).symm
      ((d.homEquiv (d.tensor.obj (Z, X)) Y M).symm
        ((tensorShuffleIso d X Y Z).inv ≫
          d.homEquiv (d.tensor.obj (Z, Y)) X M
            (d.homEquiv Z Y (d.hom.obj (Opposite.op X, M)) b))))
    (fun {Z} a => by
      simp only [AddEquiv.apply_symm_apply, Iso.inv_hom_id_assoc, AddEquiv.symm_apply_apply])
    (fun {Z} b => by
      simp only [AddEquiv.apply_symm_apply, Iso.hom_inv_id_assoc, AddEquiv.symm_apply_apply])
    (fun {Z Z'} f g => by
      apply (d.homEquiv Z' Y (d.hom.obj (Opposite.op X, M))).injective
      apply (d.homEquiv (d.tensor.obj (Z', Y)) X M).injective
      simp only [AddEquiv.apply_symm_apply, d.homEquiv_naturality_left]
      rw [reassoc_of% tensorShuffleIso_naturality d X Y f])

/-- Naturality of the associator in its outer factor, with the identity of a tensor product on
the right. -/
theorem tensorAssoc_hom_naturality (X Y : DerivedCategory (ModuleCat.{v₁} R))
    {Z Z' : DerivedCategory (ModuleCat.{v₁} R)} (f : Z' ⟶ Z) :
    d.tensor.map ((d.tensor.map ((f, 𝟙 X) : (Z', X) ⟶ (Z, X)), 𝟙 Y) :
          (d.tensor.obj (Z', X), Y) ⟶ (d.tensor.obj (Z, X), Y)) ≫
        (d.tensorAssoc Z X Y).hom =
      (d.tensorAssoc Z' X Y).hom ≫
        d.tensor.map ((f, 𝟙 (d.tensor.obj (X, Y))) :
          (Z', d.tensor.obj (X, Y)) ⟶ (Z, d.tensor.obj (X, Y))) :=
  tensorAssoc_naturality_id d X Y f

/-- **The currying isomorphism for internal Hom**:
`RHom(X ⊗ᴸ Y, M) ≅ RHom(X, RHom(Y, M))`. This is the isomorphism of [stacks 0A65], obtained
here from the Hom equivalence and the associator by Yoneda rather than from
`StacksDraft.DerivedHom.DerivedHomCurrying`, which is a structure only the model-level
adjunction carries. -/
def homCurryIso (X Y M : DerivedCategory (ModuleCat.{v₁} R)) :
    d.hom.obj (Opposite.op (d.tensor.obj (X, Y)), M) ≅
      d.hom.obj (Opposite.op X, d.hom.obj (Opposite.op Y, M)) :=
  Yoneda.ext _ _
    (fun {Z} a => (d.homEquiv Z X (d.hom.obj (Opposite.op Y, M))).symm
      ((d.homEquiv (d.tensor.obj (Z, X)) Y M).symm
        ((d.tensorAssoc Z X Y).hom ≫ d.homEquiv Z (d.tensor.obj (X, Y)) M a)))
    (fun {Z} b => (d.homEquiv Z (d.tensor.obj (X, Y)) M).symm
      ((d.tensorAssoc Z X Y).inv ≫
        d.homEquiv (d.tensor.obj (Z, X)) Y M
          (d.homEquiv Z X (d.hom.obj (Opposite.op Y, M)) b)))
    (fun {Z} a => by
      simp only [AddEquiv.apply_symm_apply, Iso.inv_hom_id_assoc, AddEquiv.symm_apply_apply])
    (fun {Z} b => by
      simp only [AddEquiv.apply_symm_apply, Iso.hom_inv_id_assoc, AddEquiv.symm_apply_apply])
    (fun {Z Z'} f g => by
      apply (d.homEquiv Z' X (d.hom.obj (Opposite.op Y, M))).injective
      apply (d.homEquiv (d.tensor.obj (Z', X)) Y M).injective
      simp only [AddEquiv.apply_symm_apply, d.homEquiv_naturality_left]
      rw [reassoc_of% tensorAssoc_hom_naturality d X Y f])

/-- Internal Hom applied to a pair of isomorphisms, as an isomorphism: contravariantly in the
source and covariantly in the target. -/
def homIso {X X' Y Y' : DerivedCategory (ModuleCat.{v₁} R)} (e : X ≅ X') (e' : Y ≅ Y') :
    d.hom.obj (Opposite.op X, Y) ≅ d.hom.obj (Opposite.op X', Y') where
  hom := d.hom.map ((e.inv.op, e'.hom) : (Opposite.op X, Y) ⟶ (Opposite.op X', Y'))
  inv := d.hom.map ((e.hom.op, e'.inv) : (Opposite.op X', Y') ⟶ (Opposite.op X, Y))
  hom_inv_id := by
    rw [← d.hom.map_comp]
    refine (congrArg d.hom.map ?_).trans (d.hom.map_id _)
    simp
  inv_hom_id := by
    rw [← d.hom.map_comp]
    refine (congrArg d.hom.map ?_).trans (d.hom.map_id _)
    simp

variable (ω : DerivedCategory (ModuleCat.{v₁} R))

/-- **The duality conversion.** If `RHom(ω, ω)` is the tensor unit then derived Hom from `ω` into
the `ω`-dual of `P` is derived Hom from `P` into the tensor unit:
`RHom(ω, RHom(P, ω)) ≅ RHom(P, 1)`. This is the symmetry of the internal Hom in its two sources
followed by the identification of `RHom(ω, ω)` with `1`. -/
def homOmegaDualIso (hone : d.hom.obj (Opposite.op ω, ω) ≅ one)
    (P : DerivedCategory (ModuleCat.{v₁} R)) :
    d.hom.obj (Opposite.op ω, d.hom.obj (Opposite.op P, ω)) ≅ d.hom.obj (Opposite.op P, one) :=
  homSourceSwapIso d ω P ω ≪≫ homIso d (Iso.refl P) hone

variable (K : DerivedCategory (ModuleCat.{v₁} R))

/-- **Derived Hom from `ω` into `K`, computed from the double dual.** If biduality holds at `K`
for `ω`, if `RHom(ω, ω)` is the tensor unit and if derived Hom from the `ω`-dual of `K` into the
tensor unit is the tensor unit, then `RHom(ω, K)` is the tensor unit.

This discharges the first hypothesis of `Dualizing.nonempty_iso_of_isIso_evaluation`, which the
module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeBiduality` records as not
following from the defining condition of [stacks 0E2C] in the diagonal vocabulary: the input
needed here is instead `RHom(RHom(K, ω), 1) ≅ 1`, which is what Step 1 of the module
documentation above produces out of that defining condition. -/
theorem nonempty_derivedHom_iso_one_of_isIso_bidualityMor
    (hbid : IsIso (bidualityMor d ω K))
    (hone : d.hom.obj (Opposite.op ω, ω) ≅ one)
    (hP : d.hom.obj (Opposite.op (d.hom.obj (Opposite.op K, ω)), one) ≅ one) :
    Nonempty (d.hom.obj (Opposite.op ω, K) ≅ one) :=
  ⟨homIso d (Iso.refl ω) (@asIso _ _ _ _ (bidualityMor d ω K) hbid) ≪≫
    homOmegaDualIso d one ω hone (d.hom.obj (Opposite.op K, ω)) ≪≫ hP⟩

/-- **The last link of the duality route to [stacks 0E2D].** If biduality holds at `K` for `ω`
and the `ω`-dual `RHom(K, ω)` of `K` is the tensor unit, then `K ≅ ω`.

Only the unit law for internal Hom is used beyond biduality: `K ≅ RHom(RHom(K, ω), ω)` is
biduality, the dual is the unit by hypothesis, and `RHom(1, ω) ≅ ω`. -/
theorem nonempty_iso_of_dual_iso_one
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (hbid : IsIso (bidualityMor d ω K))
    (hK : d.hom.obj (Opposite.op K, ω) ≅ one) :
    Nonempty (K ≅ ω) :=
  ⟨@asIso _ _ _ _ (bidualityMor d ω K) hbid ≪≫ homIso d hK (Iso.refl ω) ≪≫
    homOneSourceIso d one lam hlam ω⟩

/-- **The hypothesis `RHom(P, 1) ≅ 1` read as `P ⊗ᴸ ω ≅ ω`.** If `RHom(ω, ω)` is the tensor
unit, if derived Hom from `P` into the tensor unit is the tensor unit and if biduality holds at
`P ⊗ᴸ ω` for `ω`, then `P ⊗ᴸ ω ≅ ω`.

This is the first step of the rigidity argument of the module documentation: currying turns
`RHom(P ⊗ᴸ ω, ω)` into `RHom(P, RHom(ω, ω)) ≅ RHom(P, 1) ≅ 1`, and
`Dualizing.nonempty_iso_of_dual_iso_one` applies to `P ⊗ᴸ ω`. What is left of that argument is
the local computation, of which the degree half is now proved: the extremal nonvanishing degrees
of `(P ⊗ᴸ ω) ⊗ᴸ κ` against those of `ω ⊗ᴸ κ` are compared by
`Dualizing.eq_zero_of_derivedTensor_iso_of_isTorsionBySet` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessResidueWindow`, which puts `P ⊗ᴸ κ` in
degree zero, and the length half —
`Dualizing.nonempty_homology_derivedTensor_iso_residueField_of_isTorsionBySet` — makes it
one-dimensional there; the passage from that to the tensor unit is
`Dualizing.nonempty_iso_derivedTensorUnit_of_maximalFibre_finrank` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessPerfectionChain`. -/
theorem nonempty_tensor_iso_of_hom_iso_one
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (hone : d.hom.obj (Opposite.op ω, ω) ≅ one) (P : DerivedCategory (ModuleCat.{v₁} R))
    (hbid : IsIso (bidualityMor d ω (d.tensor.obj (P, ω))))
    (hP : d.hom.obj (Opposite.op P, one) ≅ one) :
    Nonempty (d.tensor.obj (P, ω) ≅ ω) :=
  nonempty_iso_of_dual_iso_one d one lam ω (d.tensor.obj (P, ω)) hlam hbid
    (homCurryIso d P ω ω ≪≫ homIso d (Iso.refl P) hone ≪≫ hP)

/-- **An object with a tensor inverse whose internal Hom into the unit is the unit is the unit.**
If `L ⊗ᴸ L' ≅ 1` and `RHom(L, 1) ≅ 1` then `L ≅ 1`.

A tensor inverse makes the evaluation map `RHom(L, 1) ⊗ᴸ L ⟶ 1` invertible, by
`Dualizing.isIso_evaluation_of_tensor_iso_one`; reading its source through the hypothesis and
the left unitor gives `L ≅ 1`. This is the last line of the rigidity argument of the module
documentation above. -/
theorem nonempty_iso_one_of_tensor_iso_one_of_hom_iso_one
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (L L' : DerivedCategory (ModuleCat.{v₁} R)) (e : d.tensor.obj (L, L') ≅ one)
    (h : d.hom.obj (Opposite.op L, one) ≅ one) :
    Nonempty (L ≅ one) :=
  ⟨(lam L).symm ≪≫ tensorIso d h.symm (Iso.refl L) ≪≫
    @asIso _ _ _ _ (d.evaluation L one)
      (isIso_evaluation_of_tensor_iso_one d one lam hlam L L' e one)⟩

end Abstract

section OverRing

universe u₂ v₂

attribute [local instance 5000] HasDerivedCategory.standard

variable (A : Type u₂) [CommRing A] [IsNoetherianRing A]

/-- **`RHom_A(ω, ω)` is the tensor unit for a dualizing complex**, as an isomorphism: the inverse
of the derived homothety, which [stacks 0A7B] makes invertible. -/
def dualizingHomSelfIsoUnit (ω : DerivedCategory (ModuleCat.{max u₂ v₂} A))
    (hω : IsDualizingComplex ω) :
    (derivedHomAdjunctionOverRing A).hom.obj (Opposite.op ω, ω) ≅ derivedTensorUnit A :=
  haveI := isIso_derivedHomothety_overRing_of_isDualizingComplex.{u₂, v₂} A ω hω
  (asIso (derivedHomothety (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
    (derivedTensorUnitLeft A) ω)).symm

/-- **The last link of the duality route to [stacks 0E2D], at the adjunction of [stacks 0A63].**
Let `A` be Noetherian, let `ω` be a dualizing complex and let `K` have finite cohomology in every
degree. If the `ω`-dual `RHom_A(K, ω)` of `K` is the tensor unit, then `K ≅ ω`.

Nothing is carried: biduality is [stacks 0A7C]
(`Dualizing.isIso_dualizingBidualityMor_of_finiteCohomology`) and the rest is the unit law for
internal Hom. -/
theorem nonempty_iso_of_dualizingDerivedHom_iso_derivedTensorUnit
    (ω K : DerivedCategory (ModuleCat.{max u₂ v₂} A)) (hω : IsDualizingComplex ω)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u₂ v₂} A) i).obj K))
    (h : (derivedHomAdjunctionOverRing A).hom.obj (Opposite.op K, ω) ≅ derivedTensorUnit A) :
    Nonempty (K ≅ ω) :=
  nonempty_iso_of_dual_iso_one (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
    (derivedTensorUnitLeft A) ω K (derivedTensorUnitLeft_natural A)
    (isIso_dualizingBidualityMor_of_finiteCohomology.{u₂, v₂} A ω K hω hK) h

/-- **The hypothesis of `Dualizing.nonempty_iso_of_isIso_evaluation` discharged, at the
adjunction of [stacks 0A63].** Let `A` be Noetherian, let `ω` be a dualizing complex and let `K`
have finite cohomology in every degree. If derived Hom from the `ω`-dual of `K` into `A` is `A`,
then `RHom_A(ω, K) ≅ A`.

This is the output of Step 1 of the module documentation fed into Step 2: the defining condition
of [stacks 0E2C] produces the hypothesis, and the conclusion is exactly what
`StacksFrontier.RingTheory.Dualizing.RelativeBiduality` records as missing for the evaluation route
to [stacks 0E2D]. -/
theorem nonempty_derivedHom_iso_derivedTensorUnit_of_dualDual
    (ω K : DerivedCategory (ModuleCat.{max u₂ v₂} A)) (hω : IsDualizingComplex ω)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u₂ v₂} A) i).obj K))
    (h : (derivedHomAdjunctionOverRing A).hom.obj
        (Opposite.op ((derivedHomAdjunctionOverRing A).hom.obj (Opposite.op K, ω)),
          derivedTensorUnit A) ≅ derivedTensorUnit A) :
    Nonempty ((derivedHomAdjunctionOverRing A).hom.obj (Opposite.op ω, K) ≅
      derivedTensorUnit A) :=
  nonempty_derivedHom_iso_one_of_isIso_bidualityMor (derivedHomAdjunctionOverRing A)
    (derivedTensorUnit A) ω K
    (isIso_dualizingBidualityMor_of_finiteCohomology.{u₂, v₂} A ω K hω hK)
    (dualizingHomSelfIsoUnit.{u₂, v₂} A ω hω) h

/-- **The first step of the rigidity argument, at the adjunction of [stacks 0A63].** Let `A` be
Noetherian, let `ω` be a dualizing complex and let `P ⊗ᴸ_A ω` have finite cohomology in every
degree. If `RHom_A(P, A) ≅ A` then `P ⊗ᴸ_A ω ≅ ω`.

This is the half of `RHom_A(P, A) ≅ A ⟹ P ≅ A` that is pure adjunction. The other half is the
local computation described in the module documentation, and its conclusion `P ≅ A` is now one
theorem away from this one: `Dualizing.tensorResidueIso` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation` turns the conclusion here
into the fixed object `P ⊗ᴸ_A T ≅ T` at `T = ω ⊗ᴸ_A κ`,
`Dualizing.fibre_eq_residueField_of_derivedTensor_iso_of_isTorsionBySet` runs the degree count
and the length count on it, and
`Dualizing.nonempty_iso_derivedTensorUnit_of_fibre_concentrated` reads `P ≅ A` off the result.
What is still genuinely open is none of those: it is the cohomological lower bound on
`ω ⊗ᴸ_A κ` and on `P ⊗ᴸ_A κ` that the degree count takes as an input, for which see the module
documentation and that of the local-computation module. -/
theorem nonempty_tensor_iso_of_derivedHom_iso_derivedTensorUnit
    (ω P : DerivedCategory (ModuleCat.{max u₂ v₂} A)) (hω : IsDualizingComplex ω)
    (hPω : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u₂ v₂} A) i).obj
        ((derivedHomAdjunctionOverRing A).tensor.obj (P, ω))))
    (h : (derivedHomAdjunctionOverRing A).hom.obj (Opposite.op P, derivedTensorUnit A) ≅
      derivedTensorUnit A) :
    Nonempty ((derivedHomAdjunctionOverRing A).tensor.obj (P, ω) ≅ ω) :=
  nonempty_tensor_iso_of_hom_iso_one (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
    (derivedTensorUnitLeft A) ω (derivedTensorUnitLeft_natural A)
    (dualizingHomSelfIsoUnit.{u₂, v₂} A ω hω) P
    (isIso_dualizingBidualityMor_of_finiteCohomology.{u₂, v₂} A ω _ hω hPω) h

end OverRing

end

end Dualizing

end
