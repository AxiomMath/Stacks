module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChangeDescent
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.Basic

/-!
# The linear system of sections vanishing on a subscheme, as a family of divisors

[Stacks, Tag 0FD5] produces, for `ℒ` ample on a proper `X/k` and `Z = V(I) ⊂ X` closed, a
bound `n₀` such that for `n ≥ n₀` the space `V_n ⊂ Γ(X, ℒ^{⊗ n})` of sections vanishing on `Z`
generates `ℒ^{⊗ n}` on `X ∖ Z` and the canonical morphism `X ∖ Z ⟶ 𝐏(V_n)` is an immersion.
[Stacks, Tag 0FD6] consumes a `Stacks.Bertini.FamilyDivisors` — a field, a scheme over it, an
invertible module, a finite dimensional linear system with a basis, and the linear map
presenting it — together with its hypothesis (2) `Stacks.Bertini.FamilyDivisors.Generates` and
its hypothesis (3) `Stacks.Bertini.FamilyDivisors.IsImmersive`.

The two tags are stated in disjoint vocabularies, so nothing composed them. This file supplies
the missing interface: the standing situation built from `V_n`, and the identification of each of
the two predicates of [Stacks, Tag 0FD6] with the corresponding conclusion of
[Stacks, Tag 0FD5].

## Main definitions

* `Stacks.SectionsVanishingOnSubscheme.restrictedSystemMap` is the `k`-linear map
  `V_n ⟶ Γ(X ∖ Z, ℒ^{⊗ n}|_{X ∖ Z})` restricting a vanishing section to the open complement:
  the map `ψ` of the standing situation.
* `Stacks.SectionsVanishingOnSubscheme.familyDivisors` is the standing situation of
  [Stacks, Tag 0FD6] built from `V_n`: the scheme is `X ∖ Z`, the invertible module is
  `ℒ^{⊗ n}|_{X ∖ Z}`, the linear system is `V_n` and `ψ` is `restrictedSystemMap`.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.generatesBy_familyDivisors` and
  `Stacks.SectionsVanishingOnSubscheme.generates_familyDivisors`: the generation conclusion of
  [Stacks, Tag 0FD5] **is** hypothesis (2) of [Stacks, Tag 0FD6] for this standing situation.
* `Stacks.SectionsVanishingOnSubscheme.isImmersive_familyDivisors_iff`: the immersion conclusion
  of [Stacks, Tag 0FD5] **is** hypothesis (3) of [Stacks, Tag 0FD6] for this standing situation,
  at the same basis — an equivalence, so neither side is a strengthening of the other.
* `Stacks.SectionsVanishingOnSubscheme.forGeneral_smooth_specializedDivisor_of_generatesOffSupport`
  is the composite: from the two conclusions of [Stacks, Tag 0FD5] at one degree, the conclusion
  of [Stacks, Tag 0FD6] for the family of divisors cut out by `V_n`.

## Implementation notes

`Stacks.Bertini.FamilyDivisors` has a mandatory `FiniteDimensional k V` field, and the finite
dimensionality of `Γ(X, ℒ^{⊗ n})` for `X` proper over `k` is not proved in this repository (see
the implementation notes of
`StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingLinearSystem`, where the dimension of the
basis is likewise supplied by the caller). It is therefore taken as an instance argument of
`Stacks.SectionsVanishingOnSubscheme.familyDivisors` rather than derived.

The structure field `isInvertible` and the predicate `Stacks.Ample.IsInvertibleModule` are two
spellings of invertibility differing in how the sheaf condition on the structure presheaf is
supplied, and instance search does not cross between them
(`Stacks.Bertini.FamilyDivisors.isInvertibleModule`); the field is therefore supplied here by an
explicit ascription rather than left to instance search.

The chosen basis of the standing situation is `Module.finBasis`, indexed by `Fin (dim V_n)`,
while [Stacks, Tag 0FD5] hands out its conclusion at a basis indexed by `Fin (N + 1)` for an
arbitrary `N`. Neither predicate of [Stacks, Tag 0FD6] depends on the basis it is stated at
(`Stacks.Bertini.FamilyDivisors.generates_iff_generatesBy_basis` and
`Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis'`), so the mismatch costs nothing: the
bridges below are stated at the `Fin (N + 1)` basis that [Stacks, Tag 0FD5] supplies and the
composite transports to every other basis.

## References

* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L] (n : ℤ)

/-- **The map `ψ` of the standing situation of [Stacks, Tag 0FD6] for the linear system `V_n`**:
the `k`-linear map `V_n ⟶ Γ(X ∖ Z, ℒ^{⊗ n}|_{X ∖ Z})` restricting a section vanishing on `Z` to
the open complement of `Z`. -/
def restrictedSystemMap :
    vanishingSections k f I L n →ₗ[k]
      Stacks.Bertini.globalSections k ((openComplement I).ι ≫ f)
        (restrictedPow I (L := L) (m := n)) where
  toFun s := restrictSection I (s : Stacks.Bertini.globalSections k f (tensorPowModule X L n))
  map_add' _ _ :=
    map_add (ConcreteCategory.hom
      (pullbackGlobalSections (openComplement I).ι (tensorPowModule X L n))) _ _
  map_smul' _ _ :=
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul
      (openComplement I).ι (tensorPowModule X L n) _ _

/-- **The standing situation of the Bertini theorems cut out by the sections vanishing on a
closed subscheme.** The scheme is the open complement `X ∖ Z`, the invertible module is
`ℒ^{⊗ n}|_{X ∖ Z}`, the linear system is `V_n = ker(Γ(X, ℒ^{⊗ n}) ⟶ Γ(Z, ℒ^{⊗ n}|_Z))` and the
map `ψ` restricts a vanishing section to `X ∖ Z`.

This is the datum [Stacks, Tag 0FD6] takes, built from the data [Stacks, Tag 0FD5] produces. -/
def familyDivisors [FiniteDimensional k (vanishingSections k f I L n)] :
    Stacks.Bertini.FamilyDivisors.{u, u} where
  k := k
  V := vanishingSections k f I L n
  X := (openComplement I).toScheme
  toBase := (openComplement I).ι ≫ f
  L := restrictedPow I (L := L) (m := n)
  ψ := restrictedSystemMap k f I (L := L) n
  basis := Module.finBasis k _
  isInvertible := (inferInstance : IsInvertibleModule (openComplement I).toScheme
    (restrictedPow I (L := L) (m := n)))

variable [FiniteDimensional k (vanishingSections k f I L n)]

/-- The field of `familyDivisors` is `k`. -/
@[simp]
theorem familyDivisors_k : (familyDivisors k f I (L := L) n).k = k := rfl

/-- The linear system of `familyDivisors` is `V_n`. -/
@[simp]
theorem familyDivisors_V :
    (familyDivisors k f I (L := L) n).V = vanishingSections k f I L n := rfl

/-- The scheme of `familyDivisors` is the open complement `X ∖ Z`. -/
@[simp]
theorem familyDivisors_X :
    (familyDivisors k f I (L := L) n).X = (openComplement I).toScheme := rfl

/-- The structure morphism of `familyDivisors` is the composite `X ∖ Z ⟶ X ⟶ Spec(k)`. -/
@[simp]
theorem familyDivisors_toBase :
    (familyDivisors k f I (L := L) n).toBase = (openComplement I).ι ≫ f := rfl

/-- The invertible module of `familyDivisors` is `ℒ^{⊗ n}|_{X ∖ Z}`. -/
@[simp]
theorem familyDivisors_L :
    (familyDivisors k f I (L := L) n).L = restrictedPow I (L := L) (m := n) := rfl

/-- **The section of a member of `V_n` is its restriction to `X ∖ Z`.** -/
@[simp]
theorem familyDivisors_sectionOf (s : vanishingSections k f I L n) :
    (familyDivisors k f I (L := L) n).sectionOf s =
      restrictSection I (s : Stacks.Bertini.globalSections k f (tensorPowModule X L n)) :=
  rfl

/-- **The sections of a basis of `V_n` are the restricted basis sections.** -/
theorem familyDivisors_sectionOf_basis {N : ℕ}
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n)) (i : Fin (N + 1)) :
    (familyDivisors k f I (L := L) n).sectionOf (b i) = restrictedBasisSection k f I b i :=
  rfl

/-! ### Hypothesis (2) of Stacks 0FD6 from the generation conclusion of Stacks 0FD5 -/

/-- **The generation conclusion of [Stacks, Tag 0FD5] is hypothesis (2) of [Stacks, Tag 0FD6] at
a basis.** If `V_n` generates `ℒ^{⊗ n}` off `Z`, then the sections of any basis of `V_n` generate
`ℒ^{⊗ n}|_{X ∖ Z}` stalkwise. -/
theorem generatesBy_familyDivisors {N : ℕ}
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n))
    (h : GeneratesOffSupport k f I L n) :
    (familyDivisors k f I (L := L) n).GeneratesBy b :=
  generatesStalks_restrictedBasisSection k f I b h

/-- **The generation conclusion of [Stacks, Tag 0FD5] is hypothesis (2) of
[Stacks, Tag 0FD6].** The hypothesis of [Stacks, Tag 0FD6] is basis free, and one basis of `V_n`
suffices to produce it. -/
theorem generates_familyDivisors {N : ℕ}
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n))
    (h : GeneratesOffSupport k f I L n) :
    (familyDivisors k f I (L := L) n).Generates :=
  ((familyDivisors k f I (L := L) n).generates_iff_generatesBy_basis b).mpr
    (generatesBy_familyDivisors k f I n b h)

/-! ### Hypothesis (3) of Stacks 0FD6 from the immersion conclusion of Stacks 0FD5 -/

/-- **The immersion conclusion of [Stacks, Tag 0FD5] is hypothesis (3) of
[Stacks, Tag 0FD6]**, at one and the same basis of `V_n`. The two morphisms are the same
morphism: `Stacks.SectionsVanishingOnSubscheme.toProjectiveSpaceOfVanishingSections_eq` says the
one glued over the charts of `X ∖ Z` is `AlgebraicGeometry.toProjectiveSpaceOfModule` of the
restricted basis sections, and those are the sections of the basis for the standing situation of
`Stacks.SectionsVanishingOnSubscheme.familyDivisors`. -/
theorem isImmersive_familyDivisors_iff {N : ℕ}
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n))
    (h : GeneratesOffSupport k f I L n) :
    (familyDivisors k f I (L := L) n).IsImmersive b
        (generatesBy_familyDivisors k f I n b h) ↔
      IsImmersion (toProjectiveSpaceOfVanishingSections k f b h) := by
  rw [toProjectiveSpaceOfVanishingSections_eq]
  rfl

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] at every basis**, from the immersion conclusion of
[Stacks, Tag 0FD5] at one. Hypothesis (3) does not depend on the basis it is stated at
(`Stacks.Bertini.FamilyDivisors.isImmersive_basis_of_isImmersive`), so this is the shape
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor` takes. -/
theorem isImmersive_familyDivisors {N : ℕ}
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n))
    (h : GeneratesOffSupport k f I L n)
    (himm : IsImmersion (toProjectiveSpaceOfVanishingSections k f b h))
    (m : ℕ) (b' : Module.Basis (Fin (m + 1)) k (vanishingSections k f I L n)) :
    (familyDivisors k f I (L := L) n).IsImmersive b'
      ((familyDivisors k f I (L := L) n).generatesBy_basis
        (generates_familyDivisors k f I n b h) b') :=
  (familyDivisors k f I (L := L) n).isImmersive_basis_of_isImmersive
    ((isImmersive_familyDivisors_iff k f I n b h).mpr himm) b'

/-! ### The composite: Stacks 0FD6 for the linear system of Stacks 0FD5 -/

/-- **[Stacks, Tag 0FD6] for the family of divisors cut out by the sections vanishing on a closed
subscheme.** Let `ℒ^{⊗ n}` be generated off `Z` by its sections `V_n` vanishing on `Z`, with the
canonical morphism `X ∖ Z ⟶ 𝐏(V_n)` an immersion in one basis of `V_n` — the two conclusions of
[Stacks, Tag 0FD5] — and let `X ∖ Z` be smooth over `k`. Then for general `v ∈ V_n ⊗_k k'` the
divisor `H_v` on `(X ∖ Z)_{k'}` is smooth over `k'`.

This is the composition the two tags did not admit: hypothesis (2) of [Stacks, Tag 0FD6] is the
generation conclusion of [Stacks, Tag 0FD5]
(`Stacks.SectionsVanishingOnSubscheme.generates_familyDivisors`) and its hypothesis (3) is the
immersion conclusion (`Stacks.SectionsVanishingOnSubscheme.isImmersive_familyDivisors_iff`). -/
theorem forGeneral_smooth_specializedDivisor_of_generatesOffSupport
    (hsm : Smooth ((openComplement I).ι ≫ f)) {N : ℕ}
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n))
    (h : GeneratesOffSupport k f I L n)
    (himm : IsImmersion (toProjectiveSpaceOfVanishingSections k f b h)) :
    (familyDivisors k f I (L := L) n).ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank (familyDivisors k f I (L := L) n).k
            (familyDivisors k f I (L := L) n).V) → K,
        w = ∑ i, TensorProduct.tmul (familyDivisors k f I (L := L) n).k
            ((familyDivisors k f I (L := L) n).basis i) (a i) →
          Smooth (((familyDivisors k f I (L := L) n).specializedDivisor K a).subschemeι ≫
            (familyDivisors k f I (L := L) n).baseChangeToSpec K)) :=
  have : Smooth (familyDivisors k f I (L := L) n).toBase := hsm
  (familyDivisors k f I (L := L) n).forGeneral_smooth_specializedDivisor
    (generates_familyDivisors k f I n b h)
    (isImmersive_familyDivisors k f I n b h himm)

end Stacks.SectionsVanishingOnSubscheme

end
