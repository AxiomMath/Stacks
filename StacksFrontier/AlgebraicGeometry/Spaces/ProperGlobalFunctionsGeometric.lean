module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsIrreducible

/-!
# Global functions of a proper algebraic space over a field: the geometric clauses

Let `k` be a field, let `X` be a proper algebraic space over `k`, and let
`A = H⁰(X, 𝒪_X) = AlgebraicGeometry.Space.globalFunctions` be its ring of global regular
functions.  This file states parts (4) to (8) of Tag 0DMY:

* (4) if `X` is geometrically reduced, then each factor `k_i` of `A` is a finite separable
  field extension of `k`;
* (5) if `X` is geometrically connected, then `A` is geometrically irreducible over `k`;
* (6) if `X` is geometrically irreducible, then `A` is geometrically irreducible over `k`;
* (7) if `X` is geometrically reduced and geometrically connected, then `A = k`;
* (8) if `X` is geometrically integral, then `A = k`.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `isSeparable_componentFunctions_of_isProper`: **Tag 0DMY, part (4)**.
* `irreducibleSpace_primeSpectrum_globalFunctions_tensorProduct_of_isGeometricallyConnected`:
  **Tag 0DMY, part (5)**.
* `irreducibleSpace_primeSpectrum_globalFunctions_tensorProduct_of_isGeometricallyIrreducible`:
  **Tag 0DMY, part (6)**.
* `bijective_baseToGlobalFunctions_of_isGeometricallyConnected`: **Tag 0DMY, part (7)**, in its corrected form.
* `bijective_baseToGlobalFunctions_of_isGeometricallyIntegral`: **Tag 0DMY, part (8)**.

## Implementation notes

**Hypotheses.**  Each statement assumes exactly what the corresponding clause of the source
does:  `X` an algebraic space over `Spec k` with a proper structure morphism `f`, plus the
geometric hypothesis of the clause.  Finite dimensionality of `A`, part (1) of the tag, is
``AlgebraicGeometry.Space.moduleFinite_globalFunctions_of_isProper``, and the
descent arguments of `StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsDescent`,
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsIrreducible` and
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsSeparable` do the rest.

**Part (7) reads "geometrically reduced and geometrically connected".**  The source writes
"geometrically reduced and connected", and its proof uses part (5), whose hypothesis is
geometric connectedness;  with mere connectedness the clause is false, as `X = Spec ℚ(i)` over
`k = ℚ` shows — proper, geometrically reduced and connected, with `A = ℚ(i) ≠ ℚ`.

**The factors in part (4).**  The splitting `A = ∏ k_i` is part (2) of the tag, recorded as
`AlgebraicGeometry.Space.ComponentwiseArtinianFactorization`, whose equivalence is pinned to be
simultaneous restriction to the connected components and whose factors carry the `k`-algebra
structures that restriction induces.  Part (4) is asserted for every such factorization and every
factor.

**Geometric irreducibility of `A`.**  In parts (5) and (6) it is written as the source's
definition (Tag 037L) reads, irreducibility of `Spec (A ⊗_k K)` for every field extension `K/k`,
with `K` in an arbitrary universe;  `A` lives one universe above `k`, so the one-universe
predicate `Algebra.IsGeometricallyIrreducible` does not apply to the pair.

## References

* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 037L](https://stacks.math.columbia.edu/tag/037L)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.Space

section Tag0DMY

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (f : X ⟶ yoneda.obj (baseObject k B hS))

include hX

/-- **Stacks 0DMY, part (4).**  For a proper *geometrically* reduced algebraic space `X` over a
field `k`, each factor `k_i` of the global regular functions `A = ∏ k_i` is a finite separable
field extension of `k`:  for every componentwise factorization of `A` (part (2)) and every
connected component `c` of `|X|`, the factor at `c` is a field, finite over `k` and separable
over `k`. -/
@[stacks 0DMY "part (4): if X is geometrically reduced, each factor k_i is finite separable \
over k"]
theorem isSeparable_componentFunctions_of_isProper (hf : IsProper B (Spec (.of k)) hS f)
    (hgr : IsGeometricallyReduced k B hS X hX)
    (fac : ComponentwiseArtinianFactorization k B hS X)
    (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
    IsField (componentFunctions B (Spec (.of k)) hS X c) ∧
      @Module.Finite k (componentFunctions B (Spec (.of k)) hS X c) _ _
        (@Algebra.toModule k (componentFunctions B (Spec (.of k)) hS X c) _ _
          (fac.factorAlgebra c)) ∧
      @Algebra.IsSeparable k (componentFunctions B (Spec (.of k)) hS X c) _ _
        (fac.factorAlgebra c) :=
  isSeparable_componentFunctions_of_finite k B hS X hX
    (moduleFinite_globalFunctions_of_isProper k ⟨X, hX⟩
      (by rwa [(isTerminal_yoneda_obj_base B _ hS).hom_ext f
        ((isTerminal_yoneda_obj_base B _ hS).from X)] at hf)) hgr fac c

/-- **Stacks 0DMY, part (5).**  For a proper geometrically connected algebraic space `X` over a
field `k`, the ring `A = H⁰(X, 𝒪_X)` of global regular functions is geometrically irreducible
over `k`:  the spectrum of `A ⊗_k K` is irreducible for every field extension `K/k`. -/
@[stacks 0DMY "part (5): if X is geometrically connected, A is geometrically irreducible over k"]
theorem irreducibleSpace_primeSpectrum_globalFunctions_tensorProduct_of_isGeometricallyConnected
    (hf : IsProper B (Spec (.of k)) hS f) (hconn : IsGeometricallyConnected B k hS X) :
    ∀ (K : Type v) [Field K] [Algebra k K],
      IrreducibleSpace (PrimeSpectrum (globalFunctions B (Spec (.of k)) hS X ⊗[k] K)) :=
  irreducibleSpace_primeSpectrum_globalFunctions_tensorProduct_of_finite k B hS X hX f hf
    (moduleFinite_globalFunctions_of_isProper k ⟨X, hX⟩
      (by rwa [(isTerminal_yoneda_obj_base B _ hS).hom_ext f
        ((isTerminal_yoneda_obj_base B _ hS).from X)] at hf)) hconn

/-- **Stacks 0DMY, part (6).**  For a proper geometrically irreducible algebraic space `X` over
a field `k`, the ring `A = H⁰(X, 𝒪_X)` of global regular functions is geometrically irreducible
over `k`.

As in the source, this is part (5): every base change of `X` has an irreducible, hence
connected, point space. -/
@[stacks 0DMY "part (6): if X is geometrically irreducible, A is geometrically irreducible \
over k"]
theorem irreducibleSpace_primeSpectrum_globalFunctions_tensorProduct_of_isGeometricallyIrreducible
    (hf : IsProper B (Spec (.of k)) hS f) (hirr : IsGeometricallyIrreducible B k hS X) :
    ∀ (K : Type v) [Field K] [Algebra k K],
      IrreducibleSpace (PrimeSpectrum (globalFunctions B (Spec (.of k)) hS X ⊗[k] K)) := by
  refine irreducibleSpace_primeSpectrum_globalFunctions_tensorProduct_of_isGeometricallyConnected
    k B hS X hX f hf ?_
  intro K _ _ hK
  rw [← specMapOfExtension_eq_fieldExtensionMap B k hS K hK]
  exact (hirr K hK).connectedSpace

/-- **Stacks 0DMY, part (7), in its corrected form.**  For a proper geometrically reduced and
geometrically connected algebraic space `X` over a field `k`, the canonical homomorphism
`k ⟶ H⁰(X, 𝒪_X)` is bijective: `A = k`.

The source prints "geometrically reduced and connected".  With mere connectedness the clause is
false: `X = Spec ℚ(i)` over `k = ℚ` is proper, geometrically reduced and connected, yet
`A = ℚ(i) ≠ ℚ`.  The source's proof uses geometric irreducibility of `A`, which it obtains from
part (5), whose hypothesis is geometric connectedness; this is the hypothesis stated here, and
the wording of the scheme version, Tag 0BUG (7).  Recorded in `errata.md`. -/
@[stacks 0DMY "part (7), corrected form: if X is geometrically reduced and geometrically \
connected, A = k (the printed 'connected' is false: Spec Q(i) over Q)"]
theorem bijective_baseToGlobalFunctions_of_isGeometricallyConnected
    (hf : IsProper B (Spec (.of k)) hS f) (hgr : IsGeometricallyReduced k B hS X hX)
    (hconn : IsGeometricallyConnected B k hS X) :
    Function.Bijective (baseToGlobalFunctions k B hS X) :=
  bijective_baseToGlobalFunctions_of_finite k B hS X hX f hf
    (moduleFinite_globalFunctions_of_isProper k ⟨X, hX⟩
      (by rwa [(isTerminal_yoneda_obj_base B _ hS).hom_ext f
        ((isTerminal_yoneda_obj_base B _ hS).from X)] at hf)) hgr hconn

/-- **Stacks 0DMY, part (8).**  For a proper geometrically integral algebraic space `X` over a
field `k`, the canonical homomorphism `k ⟶ H⁰(X, 𝒪_X)` is bijective:  `A = k`.

As in the source, this is part (7):  a geometrically integral algebraic space is geometrically
reduced and geometrically connected. -/
@[stacks 0DMY "part (8): if X is geometrically integral, A = k"]
theorem bijective_baseToGlobalFunctions_of_isGeometricallyIntegral
    (hf : IsProper B (Spec (.of k)) hS f) (hint : IsGeometricallyIntegral B k hS X) :
    Function.Bijective (baseToGlobalFunctions k B hS X) :=
  have h := isGeometricallyReduced_and_isGeometricallyConnected_of_isGeometricallyIntegral
    k B hS X hX hint
  bijective_baseToGlobalFunctions_of_isGeometricallyConnected k B hS X hX f hf h.1 h.2

end Tag0DMY

end AlgebraicGeometry.Space

end
