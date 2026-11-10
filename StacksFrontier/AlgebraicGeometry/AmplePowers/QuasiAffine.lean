module

public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
public import Mathlib.AlgebraicGeometry.QuasiAffine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-affine schemes and ampleness of the structure sheaf

Stacks Tag 01QE says that a scheme `X` is quasi-affine precisely when `𝒪_X` is ample. This file
proves that equivalence, for the tensor powers of `𝒪_X` presented through the one property of
them that the argument uses: each power carries a global section that vanishes nowhere and whose
multiples exhaust the global sections of that power. That property is packaged as
`Stacks.Ample.NonvanishingBasis` and is **assumed**, not proved — see "The added hypothesis"
below.

With it, the equivalence is immediate from two facts: the nonvanishing locus of a multiple
`r · b` of such a section is exactly the basic open `X_r` of `r`
(`Stacks.Ample.NonvanishingBasis.nonvanishingLocus_smul_gen`, which is
`Stacks.Ample.nonvanishingLocus_smul` with the `X_b = X` factor removed), and Mathlib's
characterisation of quasi-affineness by a cover of affine basic opens of global sections
(`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen` and
`AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen`).

## Main definitions

* `Stacks.Ample.NonvanishingBasis M`: a global section of `M` vanishing nowhere whose scalar
  multiples are all of `Γ(M, ⊤)`.

## Main results

* `Stacks.Ample.NonvanishingBasis.nonvanishingLocus_smul_gen`: `X_{r · b} = X.basicOpen r`.
* `Stacks.Ample.NonvanishingBasis.exists_basicOpen_eq`: every nonvanishing locus of a global
  section of `M` is the basic open of a global section of `𝒪_X`.
* `Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers`: **Stacks Tag 01QE**, in the form described
  above: `X` is quasi-affine if and only if the family `pow` is ample, given a
  `NonvanishingBasis` in each degree.

## The added hypothesis, stated loudly

`isQuasiAffine_iff_isAmpleForPowers` carries the hypothesis `∀ n : ℤ, NonvanishingBasis (pow n)`,
which is **not** part of Stacks Tag 01QE. In the source the sheaf is `𝒪_X` itself, its tensor
powers are canonically `𝒪_X` again, and the global section in question is `1`, so the hypothesis
is automatic there. It is not provable from the material available here, for one reason: nothing in
this
repository identifies the stalk of the structure sheaf *as an abelian group* — which is the object
`Stacks.ModuleStalk.maximalSmul` is a submodule of — with the stalk `𝒪_{X,x}` *as a ring*. Without
that identification one cannot show that the germ of `1` avoids `𝔪_x · (𝒪_X)_x`, i.e. that
`X_1 = X`, which is the `nonvanishing` field of `NonvanishingBasis`. The `surjective` field is the
statement that the power is free of rank one on that section, which for the canonical powers of
`𝒪_X` follows from Tag 01CU and is likewise not available here.

So the theorem below is Tag 01QE reduced to that algebraic input: the scheme-theoretic half — the
one that in the source runs through `Proj` and Tags 01P9, 01MI, 01Q2 and 01Q1 — is proved
outright, against Mathlib's quasi-affine API rather than through `Proj`. No other hypothesis is
added, nothing is weakened, and the conclusion is the literal biconditional of the source.

## Implementation notes

`NonvanishingBasis` is a structure rather than a class: there is nothing canonical about the
choice of generator, and a consumer that has two of them should be able to say so. Its
`surjective` field is phrased as surjectivity of `fun r => r • gen` rather than as bijectivity;
injectivity is not needed, and demanding it would make the structure harder to supply.

The forward direction extracts a point's affine basic open from
`AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen` by the same destructuring that
Mathlib's own `AlgebraicGeometry.Scheme.openCoverBasicOpenTop` uses; the basis is a set of opens
described by a double image, so the pattern has two nested `rfl`s in it.

Degree `1` is the one used in the forward direction, matching the `n ≥ 1` of Tag 01PS with the
smallest admissible `n`.

## References

* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01P6](https://stacks.math.columbia.edu/tag/01P6)

## What is not done

`NonvanishingBasis` is never constructed, for any module; see "The added hypothesis". Of the
results the source's proof of Tag 01QE depends on, Tag 01Q2 is proved
(`Stacks.AlgebraicGeometry.ProjAmpleTwist.exists_isAmple_pullback_twistingSheaf`) while Tag 01Q1
and Tag 01P9 are not — the route taken here needs none of the three. Nothing here says anything
about ampleness of
a sheaf other than one presented with a `NonvanishingBasis` in every degree.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Ample

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A global section of an `𝒪_X`-module `M` that vanishes nowhere and whose scalar multiples are
all of `Γ(M, ⊤)`. Equivalently, a trivialisation of `M` by a global basis. The canonical tensor
powers of the structure sheaf carry one, with `gen = 1`. -/
structure NonvanishingBasis (M : X.Modules) where
  /-- The generating global section. -/
  gen : Γ(M, ⊤)
  /-- It vanishes nowhere. -/
  nonvanishing : nonvanishingLocus M gen = Set.univ
  /-- Its scalar multiples are all the global sections of `M`. -/
  surjective : Function.Surjective fun r : Γ(X, ⊤) => r • gen

namespace NonvanishingBasis

/-- The nonvanishing locus of `r · b` is the basic open of `r`. -/
theorem nonvanishingLocus_smul_gen (b : NonvanishingBasis M) (r : Γ(X, ⊤)) :
    nonvanishingLocus M (r • b.gen) = ↑(X.basicOpen r) := by
  rw [nonvanishingLocus_smul, b.nonvanishing, Set.inter_univ]

/-- Every nonvanishing locus of a global section of `M` is a basic open of the structure
sheaf. -/
theorem exists_basicOpen_eq (b : NonvanishingBasis M) (s : Γ(M, ⊤)) :
    ∃ r : Γ(X, ⊤), nonvanishingLocus M s = ↑(X.basicOpen r) := by
  obtain ⟨r, hr⟩ := b.surjective s
  exact ⟨r, hr ▸ b.nonvanishingLocus_smul_gen r⟩

/-- A nowhere-vanishing global basis transports along an isomorphism of `𝒪_X`-modules. So a
single `NonvanishingBasis` for the structure sheaf, together with the isomorphisms
`𝒪_X^{⊗ n} ≅ 𝒪_X` of Stacks Tag 01CU, supplies the hypothesis of
`Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers` in every degree. -/
noncomputable def ofIso (b : NonvanishingBasis M) (e : M ≅ N) : NonvanishingBasis N where
  gen := e.hom.app ⊤ b.gen
  nonvanishing := (nonvanishingLocus_congr e b.gen).trans b.nonvanishing
  surjective t := by
    obtain ⟨r, hr⟩ := b.surjective (e.inv.app ⊤ t)
    refine ⟨r, ?_⟩
    change r • e.hom.app ⊤ b.gen = t
    rw [← Scheme.Modules.Hom.app_smul, show r • b.gen = e.inv.app ⊤ t from hr,
      ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id,
      Scheme.Modules.Hom.id_app]
    rfl

end NonvanishingBasis

/-- **Stacks Tag 01QE.** A scheme is quasi-affine precisely when its structure sheaf is ample.
The tensor powers of the structure sheaf enter only through a `NonvanishingBasis` in each degree;
that hypothesis is automatic for the canonical powers of `𝒪_X` but is not proved here, and is
discussed at length in the module documentation. -/
@[ega "II 5.1.2" "more general", ega "II 6.6.13" "more general"]
theorem isQuasiAffine_iff_isAmpleForPowers (X : Scheme.{u}) (pow : ℤ → X.Modules)
    (b : ∀ n : ℤ, NonvanishingBasis (pow n)) :
    X.IsQuasiAffine ↔ IsAmpleForPowers X pow := by
  constructor
  · intro hqa
    refine ⟨hqa.toCompactSpace, fun x => ?_⟩
    obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
      (Scheme.IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
    exact ⟨1, le_refl 1, r • (b ((1 : ℕ) : ℤ)).gen, X.basicOpen r,
      ((b ((1 : ℕ) : ℤ)).nonvanishingLocus_smul_gen r).symm, hxr, hr⟩
  · rintro ⟨hc, h⟩
    refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x => ?_
    obtain ⟨n, -, s, U, hU, hxU, hUaff⟩ := h x
    obtain ⟨r, hr⟩ := (b ((n : ℕ) : ℤ)).exists_basicOpen_eq s
    have hUr : U = X.basicOpen r := Opens.ext (hU.trans hr)
    exact ⟨r, hUr ▸ hUaff, hUr ▸ hxU⟩

end Stacks.Ample

end
