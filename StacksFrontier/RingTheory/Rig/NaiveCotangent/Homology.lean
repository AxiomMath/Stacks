module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.SixTerm

/-!
# `H⁻¹` and `H⁰` of the completed naive cotangent complex

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `B` be an object of the category
(Stacks 0AL4), and let `P` be a completed polynomial presentation `B = A⟨x₁, …, x_r⟩ / J`.
The completed naive cotangent complex of `P` (Stacks 0AJR) is the two-term complex

`NL^∧_{B/A} = (J / J² --d--> ⨁ i, B dxᵢ)`

carried by `Rig.CompletedNaiveCotangentComplex P` through its `differential` field.  This
file reads that datum as a `NaiveCotangent.TwoTerm B.carrier` and names its two cohomology
modules as the kernel and the cokernel of the differential:

`H⁻¹(NL^∧_{B/A}) = ker d`,  `H⁰(NL^∧_{B/A}) = coker d`.

The library previously accessed the cohomology of this complex only through
`DerivedCategory.homologyFunctor` applied to `CompletedNaiveCotangentComplex.cochainComplex`.
That is the right form for the `Ext`-annihilation statements of Stacks 0G9F and 0GAL, but
every statement of Stacks §88.4–88.5 that mentions `H⁻¹` or `H⁰` directly — 0AJS, 0AJU (3)
and (4), 0ALM, 0AQJ, 0ALQ, 0GAW — is a statement about these two modules, and there was no
module-level name for either.

## Main definitions

* `Rig.CompletedNaiveCotangentComplex.twoTerm`: the complex as a two-term complex of
  `B`-modules, so that the generic machinery of
  `StacksFrontier/RingTheory/NaiveCotangent/Defs.lean` applies to it — in particular the
  six-term exact sequence of `StacksFrontier/RingTheory/Rig/NaiveCotangent/SixTerm.lean`.
* `Rig.CompletedNaiveCotangentComplex.Hneg`: `H⁻¹(NL^∧_{B/A}) = ker d`, a submodule of
  `J / J²`.
* `Rig.CompletedNaiveCotangentComplex.Hzero`: `H⁰(NL^∧_{B/A}) = coker d`, a quotient of
  `⨁ i, B dxᵢ`.

## Implementation notes

`Hneg` and `Hzero` are the cohomology of the *chosen* presentation `P`, exactly as the
complex itself is; their independence of `P` is the content of Stacks 0GAE, available as
`Rig.completedNaiveCotangentComplex_homotopyEquiv`, and is not used here.

The degree indices of `NaiveCotangent.TwoTerm` are homological (`X₁` and `X₀`), while the
source indexes the completed naive cotangent complex cohomologically (`-1` and `0`); `X₁`
corresponds to degree `-1`.  The names `Hneg`/`Hzero` follow the source.

## References

* [Stacks Project, Tag 0AJR](https://stacks.math.columbia.edu/tag/0AJR)
* [Stacks Project, Tag 0AL4](https://stacks.math.columbia.edu/tag/0AL4)
-/

@[expose] public section

open CategoryTheory

namespace Rig

namespace CompletedNaiveCotangentComplex

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  {P : CompletedPolynomialPresentation I B}

/-- The completed naive cotangent complex of a presentation, read as a two-term complex of
`B`-modules: `J / J²` in degree `-1`, `⨁ i, B dxᵢ` in degree `0`, and the formal-derivative
differential between them. -/
public noncomputable def twoTerm (K : CompletedNaiveCotangentComplex P) :
    NaiveCotangent.TwoTerm B.carrier where
  X₁ := P.extension.Cotangent
  X₀ := Fin P.variableCount → B.carrier
  d := K.differential

/-- The differential of the two-term reading is the differential of the complex. -/
@[simp] public theorem twoTerm_d (K : CompletedNaiveCotangentComplex P) :
    K.twoTerm.d = K.differential := rfl

/-- `H⁻¹(NL^∧_{B/A})`, the kernel of the differential, as a submodule of `J / J²`. -/
public noncomputable abbrev Hneg (K : CompletedNaiveCotangentComplex P) :
    Submodule B.carrier P.extension.Cotangent :=
  LinearMap.ker K.differential

/-- `H⁰(NL^∧_{B/A})`, the cokernel of the differential, as a quotient of `⨁ i, B dxᵢ`. -/
public abbrev Hzero (K : CompletedNaiveCotangentComplex P) :=
  (Fin P.variableCount → B.carrier) ⧸ LinearMap.range K.differential

/-- `H⁻¹` is the degree-`1` cohomology of the two-term reading. -/
public theorem Hneg_eq (K : CompletedNaiveCotangentComplex P) :
    K.Hneg = NaiveCotangent.H₁ K.twoTerm := rfl

/-- `H⁰` is the degree-`0` cohomology of the two-term reading. -/
public theorem Hzero_eq (K : CompletedNaiveCotangentComplex P) :
    K.Hzero = NaiveCotangent.H₀ K.twoTerm := rfl

/-- A class in `J / J²` is a cohomology class in degree `-1` exactly when its formal
derivatives all vanish in `B`. -/
public theorem mem_Hneg_iff (K : CompletedNaiveCotangentComplex P)
    (x : P.extension.Cotangent) : x ∈ K.Hneg ↔ K.differential x = 0 :=
  LinearMap.mem_ker

/-- A tuple of differentials vanishes in `H⁰` exactly when it is a formal derivative. -/
public theorem Hzero_mk_eq_zero_iff (K : CompletedNaiveCotangentComplex P)
    (y : Fin P.variableCount → B.carrier) :
    Submodule.mkQ (LinearMap.range K.differential) y = 0 ↔
      ∃ x, K.differential x = y := by
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact Iff.rfl

end CompletedNaiveCotangentComplex

end Rig

end
