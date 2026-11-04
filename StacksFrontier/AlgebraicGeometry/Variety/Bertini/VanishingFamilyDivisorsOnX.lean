module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniVanishingJet
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingFamilyDivisors

/-!
# The linear system of sections vanishing on a subscheme, as a family of divisors on `X` itself

`Stacks.SectionsVanishingOnSubscheme.familyDivisors` is the standing situation of
[Stacks, Tag 0FD6] that the linear system `V_n` of [Stacks, Tag 0FD5] determines **on the open
complement `X ∖ Z`**: that is where `V_n` generates `ℒ ^⊗ n` and where the morphism to `𝐏(V_n)`
is an immersion, so that is where the smoothness conclusion of [Stacks, Tag 0FD6] lives.

The general-position step of [Stacks, Tag 0FH7] asks about the germ of a member of `V_n` **at a
point of `Z`** — the whole point of that system is that its members vanish at the points being
separated, and those points are not in `X ∖ Z`. The germ there is not visible to the standing
situation on `X ∖ Z` at all. This module supplies the second standing situation, on `X` itself,
whose linear system is the same `V_n` and whose module is `ℒ ^⊗ n` on the whole of `X`.

The two standing situations share their base field, their linear system and their basis, and the
parameter space of a standing situation is the affine space on `dim_k V` coordinates over `k`, so
the two parameter spaces are **the same scheme**
(`Stacks.SectionsVanishingOnSubscheme.parameterBase_familyDivisorsOnX`). Their opens therefore
live in one lattice: the open on which the divisor is smooth away from `Z`, produced by
[Stacks, Tag 0FD6] through the situation on `X ∖ Z`, and the open on which the germ at a point of
`Z` avoids `𝔪_x²ℒ_x`, produced through the situation on `X`, can be intersected.

## Main definitions

* `Stacks.SectionsVanishingOnSubscheme.ambientFamilyDivisors` is the standing situation on `X`
  whose linear system is the whole of `Γ(X, ℒ ^⊗ n)`, presented by the identity.
* `Stacks.SectionsVanishingOnSubscheme.familyDivisorsOnX` is the standing situation on `X` whose
  linear system is `V_n`: the subsystem of the preceding one cut out by the restriction map to
  `Z`, which is what `Stacks.SectionsVanishingOnSubscheme.vanishingSections` *is*.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.parameterBase_familyDivisorsOnX`: **the two standing
  situations have the same parameter space**, and the same basis of the same linear system.
* `Stacks.SectionsVanishingOnSubscheme.evalVector_ne_zero_familyDivisorsOnX`: **the `1`-jet
  surjection for `V_n`** — at a closed point `x` of `X`, smooth of dimension `n ≥ dim_k Γ(Z, ℒ ^⊗
  n|_Z)` there over an algebraically closed field, with the whole system `Γ(X, ℒ ^⊗ n)`
  generating and defining an immersion, some member of `V_n` has germ at `x` outside `𝔪_x²ℒ_x`.
* `Stacks.SectionsVanishingOnSubscheme.exists_nonempty_opens_notMem_maximalSqSmul_familyDivisors`
  `OnX`: the general-position open of [Stacks, Tag 0FH7] for `V_n`, in the parameter space the
  two standing situations share.

## Implementation notes

`Stacks.SectionsVanishingOnSubscheme.vanishingSections` is *defined* as the kernel of
`Stacks.SectionsVanishingOnSubscheme.restrictionMap`, so `familyDivisorsOnX` is literally
`Stacks.Bertini.FamilyDivisors.restrictSystem` of the ambient situation at that kernel, and the
`1`-jet surjection is `Stacks.Bertini.FamilyDivisors.evalVector_ne_zero_restrictSystem_ker` with
no re-presentation of the subspace. The dimension hypothesis is therefore stated as
`dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ n` rather than as a count of conditions: for the two reduced closed
points of [Stacks, Tag 0FH7] over an algebraically closed field that space is two dimensional and
the hypothesis is `2 ≤ n`, the dimension range of the Bertini branch of that proof.

Both standing situations take the finite dimensionality of their linear system as an instance
argument, as `Stacks.SectionsVanishingOnSubscheme.familyDivisors` already does and for the same
reason: the finite dimensionality of `Γ(X, ℒ ^⊗ n)` for `X` proper over `k` is not proved in this
repository. The ambient situation assumes it for `Γ(X, ℒ ^⊗ n)`, from which the subsystem's
follows, so `familyDivisorsOnX` needs no second assumption.

Hypotheses (2) and (3) of [Stacks, Tag 0FD6] are assumed here for the ambient system and not
derived. They say that `ℒ ^⊗ n` is very ample on `X` with its full space of sections; what this
repository lands from ampleness is [Stacks, Tag 0FD5], which gives generation and an immersion on
the open complement of a closed subscheme rather than on `X`, so the two do not compose. That is
the one input of the general-position step of [Stacks, Tag 0FH7] still carried as a hypothesis.

No `@[stacks]` attribute is attached: the standing situation on `X` is not asserted by any tag,
and the `1`-jet surjection is a step the proof of [Stacks, Tag 0FH7] omits.

## References

* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections
open Stacks.ImmersionEvaluationSurjective

universe u

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L] (n : ℤ)

/-- **`Γ(Z, ℒ ^⊗ n|_Z)`**, the target of the restriction map to the closed subscheme cut out by
`I`: the space of linear conditions that `V_n` is cut out by. -/
abbrev subschemeSections : Type u :=
  Stacks.Bertini.globalSections k (I.subschemeι ≫ f)
    ((Scheme.Modules.pullback I.subschemeι).obj (tensorPowModule X L n))

variable [FiniteDimensional k (Stacks.Bertini.globalSections k f (tensorPowModule X L n))]

/-- **The standing situation on `X` whose linear system is the whole of `Γ(X, ℒ ^⊗ n)`.** The
presentation `ψ` is the identity: the linear system *is* the space of global sections.

This is the ambient situation that `Stacks.SectionsVanishingOnSubscheme.familyDivisorsOnX` cuts
down to the sections vanishing on `Z`. -/
@[reducible]
def ambientFamilyDivisors : Stacks.Bertini.FamilyDivisors.{u, u} where
  k := k
  V := Stacks.Bertini.globalSections k f (tensorPowModule X L n)
  X := X
  toBase := f
  L := tensorPowModule X L n
  ψ := LinearMap.id
  basis := Module.finBasis k _
  isInvertible := (inferInstance : IsInvertibleModule X (tensorPowModule X L n))

/-- **The standing situation on `X` itself whose linear system is `V_n`.** The scheme is `X`, the
invertible module is `ℒ ^⊗ n`, the linear system is the space `V_n` of sections vanishing on `Z`
and `ψ` is the inclusion of `V_n` into `Γ(X, ℒ ^⊗ n)`.

This is the companion of `Stacks.SectionsVanishingOnSubscheme.familyDivisors`, which carries the
same linear system on the open complement `X ∖ Z`. The germ of a member at a point *of* `Z` is
visible here and not there, which is what the general-position step of [Stacks, Tag 0FH7] asks
about. -/
@[reducible]
def familyDivisorsOnX : Stacks.Bertini.FamilyDivisors.{u, u} :=
  (ambientFamilyDivisors k f (L := L) n).restrictSystem
    (LinearMap.ker (restrictionMap k f I (tensorPowModule X L n)))

/-- The base field of the standing situation on `X` is `k`. -/
@[simp]
theorem familyDivisorsOnX_k : (familyDivisorsOnX k f I (L := L) n).k = k := rfl

/-- The scheme of the standing situation on `X` is `X`. -/
@[simp]
theorem familyDivisorsOnX_X : (familyDivisorsOnX k f I (L := L) n).X = X := rfl

/-- The structure morphism of the standing situation on `X` is `f`. -/
@[simp]
theorem familyDivisorsOnX_toBase : (familyDivisorsOnX k f I (L := L) n).toBase = f := rfl

/-- The invertible module of the standing situation on `X` is `ℒ ^⊗ n`. -/
@[simp]
theorem familyDivisorsOnX_L :
    (familyDivisorsOnX k f I (L := L) n).L = tensorPowModule X L n := rfl

/-- **The linear system of the situation on `X` is `V_n`**, the same linear system as that of the
situation on `X ∖ Z`. -/
theorem familyDivisorsOnX_V :
    (familyDivisorsOnX k f I (L := L) n).V = vanishingSections k f I L n := rfl

/-- **The section of a member of `V_n` is that member**, the presentation being an inclusion. -/
theorem familyDivisorsOnX_sectionOf (s : vanishingSections k f I L n) :
    (familyDivisorsOnX k f I (L := L) n).sectionOf s =
      (s : Stacks.Bertini.globalSections k f (tensorPowModule X L n)) :=
  rfl

/-! ### The two standing situations share their parameter space -/

section SharedParameterSpace

variable [FiniteDimensional k (vanishingSections k f I L n)]

/-- **The two standing situations have the same parameter space.** The parameter space of a
standing situation is the affine space on `dim_k V` coordinates over `k`, and the two situations
have the same base field and the same linear system `V_n`; the scheme and the invertible module,
in which they differ, do not enter.

This is what lets the general-position open produced on `X` be intersected with the smoothness
open produced on `X ∖ Z`: the two are opens of one scheme. -/
theorem parameterBase_familyDivisorsOnX :
    (familyDivisorsOnX k f I (L := L) n).parameterBase =
      (familyDivisors k f I (L := L) n).parameterBase :=
  rfl

/-- **The two standing situations have the same basis of the same linear system.** Both take
`Module.finBasis` of `V_n`. -/
theorem basis_familyDivisorsOnX :
    (familyDivisorsOnX k f I (L := L) n).basis = (familyDivisors k f I (L := L) n).basis :=
  rfl

end SharedParameterSpace

/-! ### The 1-jet surjection for the vanishing system -/

/-- **The `1`-jet surjection for the linear system of sections vanishing on a closed
subscheme.** Let `X` be smooth over an algebraically closed field `k`, of dimension `n` at a
closed point `x`, let the whole space of sections `Γ(X, ℒ ^⊗ n)` generate `ℒ ^⊗ n` and define an
immersion `X → 𝐏(Γ(X, ℒ ^⊗ n))` — hypotheses (2) and (3) of [Stacks, Tag 0FD6] for the ambient
system — and let the space `Γ(Z, ℒ ^⊗ n|_Z)` of linear conditions have dimension at most `n`.
Then the evaluation of `V_n` at `x` is not identically zero: some section of `ℒ ^⊗ n` vanishing
on `Z` has germ at `x` outside `𝔪_x²ℒ_x`.

This is the hypothesis the general-position step of [Stacks, Tag 0FH7] rests on, for the system
that proof uses. The point `x` may lie on `Z`, and in the application it does: `Z` is the pair of
closed points being separated, `Γ(Z, ℒ ^⊗ n|_Z)` is two dimensional, and the hypothesis on it
reads `2 ≤ n`.

`Stacks.SectionsVanishingOnSubscheme.vanishingSections` is the kernel of
`Stacks.SectionsVanishingOnSubscheme.restrictionMap`, so this is
`Stacks.Bertini.FamilyDivisors.evalVector_ne_zero_restrictSystem_ker` at that map. -/
theorem evalVector_ne_zero_familyDivisorsOnX [IsAlgClosed k] [Smooth f]
    [Module.Finite k (subschemeSections k f I (L := L) n)] {p : ℕ}
    {b : Module.Basis (Fin (p + 1)) k
      (Stacks.Bertini.globalSections k f (tensorPowModule X L n))}
    {hb : (ambientFamilyDivisors k f (L := L) n).GeneratesBy b}
    (himm : (ambientFamilyDivisors k f (L := L) n).IsImmersive b hb) {x : X}
    (hx : IsClosed ({x} : Set X)) {m : ℕ}
    (hdim : topologicalKrullDimAt X x = (m : WithBot ℕ∞))
    (hcond : Module.finrank k (subschemeSections k f I (L := L) n) ≤ m) :
    (familyDivisorsOnX k f I (L := L) n).evalVector x ≠ 0 :=
  (ambientFamilyDivisors k f (L := L) n).evalVector_ne_zero_restrictSystem_ker himm hx hdim
    (restrictionMap k f I (tensorPowModule X L n)) hcond

/-- **The general-position assertion of [Stacks, Tag 0FH7] for the linear system of sections
vanishing on a closed subscheme.** There is a nonempty open of the parameter space `𝔸^{dim V_n}_k`
— the parameter space the two standing situations share — at every `k`-rational parameter of
which the corresponding member of `V_n` has germ at `x` outside `𝔪_x²ℒ_x`.

The two halves are
`Stacks.SectionsVanishingOnSubscheme.evalVector_ne_zero_familyDivisorsOnX`, the `1`-jet
surjection, and
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero`,
the openness. -/
theorem exists_nonempty_opens_notMem_maximalSqSmul_familyDivisorsOnX [IsAlgClosed k] [Smooth f]
    [Module.Finite k (subschemeSections k f I (L := L) n)] {p : ℕ}
    {b : Module.Basis (Fin (p + 1)) k
      (Stacks.Bertini.globalSections k f (tensorPowModule X L n))}
    {hb : (ambientFamilyDivisors k f (L := L) n).GeneratesBy b}
    (himm : (ambientFamilyDivisors k f (L := L) n).IsImmersive b hb) {x : X}
    (hx : IsClosed ({x} : Set X)) {m : ℕ}
    (hdim : topologicalKrullDimAt X x = (m : WithBot ℕ∞))
    (hcond : Module.finrank k (subschemeSections k f I (L := L) n) ≤ m) :
    ∃ U : (familyDivisors k f I (L := L) n).parameterBase.Opens,
      (U : Set (familyDivisors k f I (L := L) n).parameterBase).Nonempty ∧
      ∀ c : Fin (Module.finrank k (vanishingSections k f I L n)) → k,
        (∀ q : Spec (.of k), (familyDivisorsOnX k f I (L := L) n).parameterPoint c q ∈ U) →
          ((tensorPowModule X L n).presheaf.Γgerm x).hom
              ((familyDivisorsOnX k f I (L := L) n).constCoeffSection c) ∉
            maximalSqSmul (tensorPowModule X L n) x :=
  Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero
    (familyDivisorsOnX k f I (L := L) n)
    (evalVector_ne_zero_familyDivisorsOnX k f I n himm hx hdim hcond)

end Stacks.SectionsVanishingOnSubscheme

end
