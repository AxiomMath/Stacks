module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumberOfCtfTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumberOfCtfCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Lefschetz trace formula for a projective curve over a finite field

Let `X` be a projective curve over a finite field `k` with `p ^ q` elements, `k̄` an algebraic
closure of `k`, `Λ` a finite ring of cardinality prime to `p` and `K ∈ D_ctf(X, Λ)`.  Then the
global Lefschetz number `Tr(π_X^* | RΓ(X_k̄, K))` of [Stacks, Tag 03TX] equals the local Lefschetz
number `∑_{x ∈ X(k)} Tr(π_x | K_x̄)` of [Stacks, Tag 03TY] in `Λ^natural` ([Stacks, Tag 03TZ]).

## Proof

`X` is proper over `k`, so it is its own compactification
(`AlgebraicGeometry.CompactificationOf.ofProper`), and the trace formula of [Stacks, Tag 03UG]
(`Stacks.EtaleCohomology.traceFormulaUpToDim_one`) applies to it, `X` being of dimension one.  It
computes the canonical compactly supported Lefschetz number, which for the trivial compactification
is the trace of `π_X^*` on `RΓ(X_k̄, K)` computed as `RΓ(Spec k̄, Rf_*(K|_{X_k̄}))`.
`Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusGlobalSectionsEndo_eq` identifies it with the
global Lefschetz number of [Stacks, Tag 03TX].

## The hypothesis on `Λ`

The statement of Tag 03TZ says "`Λ` a finite ring".  The chapter fixes, in Section 64.10
([Stacks, Tag 03SZ]): "Fix a finite ring `Λ` with
cardinality prime to `p`", `p` the characteristic of `k`; the proof of Tag 03TZ ("See discussion
below") is the proof of [Stacks, Tag 03UG], which assumes this.  Without it the statement is
false: for `k = 𝔽₅`, the supersingular elliptic curve `E : y² = x³ + 1` (`5 ≡ 2 mod 3`),
`Λ = ℤ/25ℤ` and `K = Λ`, Artin–Schreier gives `H^i(E_k̄, 𝔽₅) = 0` for `i ≥ 1` (Frobenius is zero on
`H¹(E, 𝒪_E)`), hence `RΓ(E_k̄, ℤ/25ℤ) = ℤ/25ℤ` with trivial `π^*` and global Lefschetz number `1`,
while the local one is `#E(𝔽₅) = 6 ≠ 1` in `ℤ/25ℤ`.  So the theorem is stated under the
chapter's standing hypothesis `Nat.Coprime (Nat.card Λ) p`.

## Implementation notes

`Λ` lives in `Type`, as in the formalization of [Stacks, Tag 03UG] that this result is deduced
from.  `K` is a bounded below complex of sheaves of `Λ`-modules whose class lies in `D_ctf`: every
object of `D_ctf(X, Λ) ⊆ D⁺(X_étale, Λ)` is the class of such a complex, the global Lefschetz
number is that of its class, and the stalks `K_x̄` and the Frobenius `π_x` are those of
[Stacks, Tag 03UG] (`Stacks.EtaleCohomology.rationalPointStalkComplex`,
`Stacks.EtaleCohomology.rationalPointStalkFrobenius`), whose perfectness is part of the
conclusion.  The characteristic of `k̄` is read off the algebra `k → k̄`, not assumed.

## References

* [Stacks Project, Tag 03TZ](https://stacks.math.columbia.edu/tag/03TZ)
* [Stacks Project, Tag 03SZ](https://stacks.math.columbia.edu/tag/03SZ)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance high] etaleModules_hasSheafify

/-- **Stacks, Tag 03TZ: the Lefschetz trace formula.** Let `X` be a projective curve over a finite
field `k` with `p ^ q` elements, `k̄` an algebraic closure of `k`, `Λ` a finite, possibly
noncommutative, ring of cardinality prime to `p` (the standing hypothesis of the chapter, fixed in
[Stacks, Tag 03SZ]), and `K ∈ D_ctf(X, Λ)`, given as a bounded below complex of sheaves of
`Λ`-modules on `X_étale` whose class lies in `D_ctf(X, Λ)`. Then the stalks `K_x̄` at the rational
points are perfect, and the global and local Lefschetz numbers of `K` are equal:

`Tr(π_X^* | RΓ(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` in `Λ^natural`.

The left hand side is the global Lefschetz number of [Stacks, Tag 03TX]
(`Stacks.EtaleCohomology.globalLefschetzNumberOfCtf`); on the right `K_x̄` is the stalk at the
geometric point over `x` and `π_x` the geometric Frobenius of [Stacks, Tag 03SW] acting on it.
Without the hypothesis `#Λ` prime to `p` the statement fails (see the module documentation). -/
@[stacks 03TZ "the Lefschetz trace formula for a projective curve over a finite field: global \
Lefschetz number (03TX) = sum over X(k) of the traces of the geometric Frobenius on the stalks, \
in Λ^natural, with K in D_ctf(X, Λ) given by a bounded below complex. Λ is a finite ring of \
cardinality prime to p, the standing hypothesis of the chapter fixed in 03SZ \
(trace.tex:386: 'Fix a finite ring Λ with cardinality prime to p'); the literal reading with an \
arbitrary finite Λ is false (k = F_5, E : y^2 = x^3 + 1 supersingular, Λ = Z/25, K = Λ: global \
number 1, local number #E(F_5) = 6). Λ : Type as in the formalization of 03UG",
  sga "4½ Rapport 3.2" "partial",
  sga "5 IIIB 1.3" "special case"]
theorem globalLefschetzNumberOfCtf_eq_sum_rationalPointStalkTrace (B : BigEtaleSite.{u})
    (X : B.Scheme) (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
    (gk : X.obj ⟶ Spec (.of k)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
    [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (hcop : Nat.Coprime (Nat.card Λ) p)
    (hcurve : IsCurve k gk) (hproj : IsProjective gk)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsCtf.{u, 0} B X Λ (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj K))) :
    letI : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
    ∃ hs : ∀ x : rationalPoints gk, StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar x.1 K)),
      globalLefschetzNumberOfCtf.{u, 0} B X Λ gk kbar p q hcard hcurve hproj
          (DerivedCategory.Plus.Q.obj K) hK =
        ∑ᶠ x : rationalPoints gk, perfectDerivedTrace Λ ⟨_, hs x⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1 K)) := by
  let : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : IsProper gk := hproj.isProper
  have := hcurve.toIsVariety
  have hcop' : Nat.Coprime (Nat.card Λ) (Fintype.card k) := hcard ▸ hcop.pow_right q
  have hdim : topologicalKrullDim X.obj ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    hcurve.topologicalKrullDim_eq_one.le
  obtain ⟨hX, hs, h⟩ := traceFormulaUpToDim_one B Λ kbar p q hcard hcop' X gk hdim
    (CompactificationOf.ofProper gk) K hK
  refine ⟨hs, ?_⟩
  rw [← h, globalLefschetzNumberOfCtf_eq_perfectDerivedTrace]
  have e := etaleModuleExtensionByZeroIdMapCochainComplexPlusIso Λ X.obj K
  have hX' := isPerfect_frobeniusRestriction_of_iso Λ (Over.mk gk) kbar e hX
  refine Eq.trans ?_
    (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ (Over.mk gk) kbar p q
      hcard e hX hX').symm
  exact perfectDerivedTrace_frobeniusGlobalSectionsEndo_eq Λ (Over.mk gk) kbar p q hcard K _ hX'

/-- **The trace formula for an object of `D_ctf(X, Λ)`.** For `K ∈ D_ctf(X, Λ)` an object of the
bounded below derived category and any bounded below complex `C` representing it, the global
Lefschetz number of `K` is the sum over `X(k)` of the traces of the geometric Frobenius on the
stalks of `C`. This is `globalLefschetzNumberOfCtf_eq_sum_rationalPointStalkTrace` transported
along the isomorphism `Q(C) ≅ K`. -/
@[sga "5 IIIB 1.3" "special case"]
theorem globalLefschetzNumberOfCtf_eq_sum_rationalPointStalkTrace_of_iso (B : BigEtaleSite.{u})
    (X : B.Scheme) (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
    (gk : X.obj ⟶ Spec (.of k)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
    [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (hcop : Nat.Coprime (Nat.card Λ) p)
    (hcurve : IsCurve k gk) (hproj : IsProjective gk)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsCtf.{u, 0} B X Λ (DerivedCategory.Plus.ι.obj K))
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj)) (e : DerivedCategory.Plus.Q.obj C ≅ K) :
    letI : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
    ∃ hs : ∀ x : rationalPoints gk, StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar x.1 C)),
      globalLefschetzNumberOfCtf.{u, 0} B X Λ gk kbar p q hcard hcurve hproj K hK =
        ∑ᶠ x : rationalPoints gk, perfectDerivedTrace Λ ⟨_, hs x⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1 C)) := by
  have hC := IsCtf.of_iso B X Λ (DerivedCategory.Plus.ι.mapIso e).symm hK
  obtain ⟨hs, h⟩ := globalLefschetzNumberOfCtf_eq_sum_rationalPointStalkTrace B X Λ gk kbar p q
    hcard hcop hcurve hproj C hC
  exact ⟨hs,
    (globalLefschetzNumberOfCtf_congr B X Λ gk kbar p q hcard hcurve hproj e hC hK).symm.trans h⟩

end Stacks.EtaleCohomology

end
