module

public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiCokernel

/-!
# The zig-zag of the Jacobi-Zariski connecting map on a conormal class

Let `A ⟶ B ⟶ C` be ring maps and write `P = A[B] ⟶ B`, `N = A[C] ⟶ C` and `Q = B[C] ⟶ C` for the
three canonical presentations of [Stacks Project, Tag 07BL], with conormal modules `I/I²`,
`K/K²` and `J/J²`.

For `f` in the kernel of `B ⟶ C` the constant polynomial `f` lies in `J`, and its class in
`J/J²` is a cycle of `NL(Q) = NL_{C/B}` — the class of a constant has zero differential
(`Algebra.Extension.Cotangent.mk_C_mem_ker_cotangentComplex`).  This file writes that cycle as

`h (-(1 ⊗ d[f])) + g (class of the variable [0])`,

where `h` is the homotopy of [Stacks Project, Tag 07VC] base changed to `C`
(`NaiveCotangent.towerNullHomotopyBaseChange`) and `g` is the comparison `K/K² ⟶ J/J²` of
[Stacks Project, Tag 0E1Y] (`Algebra.Extension.Cotangent.map` of
`NaiveCotangent.towerTopHom`).  The identity is immediate from the value
`h (1 ⊗ d[b]) = [[φ b] - b]` of the homotopy on a basis element
(`NaiveCotangent.towerNullHomotopy_cotangentSpaceBasis`): for `f` in the kernel the variable
`[φ f]` is the variable `[0]`, which is the image of the variable `[0]` of `A[C]`.

That is exactly the zig-zag datum which
`CochainComplex.mappingCone.cycle_comp_connecting` consumes, so it computes the connecting
morphism of the six-term exact sequence of [Stacks Project, Tag 0E1Y] on a conormal class: the
answer is the class of `-(1 ⊗ d[f])`, that is `-(1 ⊗ d f)` in `C ⊗_B Ω_{B/A}`, which is **minus**
the first arrow of the conormal sequence of [Stacks Project, Tag 01UZ].

## Main results

* `NaiveCotangent.X_mem_ker`, `NaiveCotangent.C_mem_ker_of_algebraMap_eq_zero` and
  `NaiveCotangent.X_zero_sub_C_mem_ker`: the three elements of the two presentation ideals that
  the zig-zag uses.
* `NaiveCotangent.cotangentComplex_cotangent_mk_C`: the class of a constant is a cycle.
* `NaiveCotangent.towerNullHomotopy_cotangentSpaceBasis_of_algebraMap_eq_zero`: the homotopy of
  [Stacks Project, Tag 07VC] on the basis element of an element of the kernel.
* `NaiveCotangent.cotangent_mk_C_add_towerNullHomotopy`,
  `NaiveCotangent.cotangent_mk_C_eq_towerNullHomotopy_add` and
  `NaiveCotangent.cotangent_mk_eq_towerNullHomotopy_add`: **the zig-zag**, in its additive form,
  in the form the abstract computation of the connecting morphism consumes, and with the two
  members of the presentation ideals given as opaque variables.
* `NaiveCotangent.toKaehler_baseChange_neg_basis`: the class of `-(1 ⊗ d[f])` in
  `C ⊗_B Ω_{B/A}` is `-(1 ⊗ d f)`.

## References

* [Stacks Project, Tag 07VC](https://stacks.math.columbia.edu/tag/07VC), the explicit homotopy.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the six-term sequence
  and its connecting morphism.
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the conormal sequence,
  whose first arrow the connecting morphism is being compared with.
-/

@[expose] public section

universe u₁ u₂ u₃

open Algebra MvPolynomial TensorProduct

namespace NaiveCotangent

variable (A : Type u₁) (B : Type u₂) (C : Type u₃) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The variable `[0]` of the canonical presentation `A[C] ⟶ C` lies in the presentation
ideal. -/
theorem X_mem_ker : (X (0 : C) : (Generators.self A C).Ring) ∈ (Generators.self A C).ker := by
  rw [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]
  simp [Generators.self]

/-- The constant polynomial `f` lies in the presentation ideal `J = ker (B[C] ⟶ C)` of the
canonical presentation of `C` over `B` when `f` maps to zero in `C`. -/
theorem C_mem_ker_of_algebraMap_eq_zero {f : B} (hf : algebraMap B C f = 0) :
    (MvPolynomial.C f : (Generators.self B C).Ring) ∈ (Generators.self B C).ker := by
  rw [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]
  simp [Generators.self, hf]

/-- The element `[0] - f` of `B[C]`, the value of the homotopy of [Stacks Project, Tag 07VC] on
`d[f]` for `f` in the kernel, lies in the presentation ideal. -/
theorem X_zero_sub_C_mem_ker {f : B} (hf : algebraMap B C f = 0) :
    (X (0 : C) - MvPolynomial.C f : (Generators.self B C).Ring) ∈ (Generators.self B C).ker :=
  hf ▸ X_sub_C_mem_ker B C f

/-- **The class of a constant is a cycle of `NL_{C/B}`.**  The differential of the naive
cotangent complex of the canonical presentation kills the class of a constant polynomial, the
universal differential of a constant being zero. -/
theorem cotangentComplex_cotangent_mk_C {f : B} (hf : algebraMap B C f = 0) :
    (Generators.self B C).toExtension.cotangentComplex
        (Extension.Cotangent.mk ⟨MvPolynomial.C f, C_mem_ker_of_algebraMap_eq_zero B C hf⟩) = 0 :=
  Extension.Cotangent.mk_C_mem_ker_cotangentComplex (Generators.self B C)
    (C_mem_ker_of_algebraMap_eq_zero B C hf)

/-- **The homotopy of [Stacks Project, Tag 07VC] on the basis element of an element of the
kernel.**  For `f` in the kernel of `B ⟶ C` the variable `[φ f]` is the variable `[0]`, so the
homotopy sends `d[f]` to the class of `[0] - f`. -/
theorem towerNullHomotopy_cotangentSpaceBasis_of_algebraMap_eq_zero {f : B}
    (hf : algebraMap B C f = 0) :
    towerNullHomotopy A B C ((Generators.self A B).cotangentSpaceBasis f) =
      Extension.Cotangent.mk ⟨X (0 : C) - MvPolynomial.C f, X_zero_sub_C_mem_ker B C hf⟩ :=
  (towerNullHomotopy_cotangentSpaceBasis A B C f).trans
    (congrArg _ (Subtype.ext
      (congrArg (fun c : C => (X c - MvPolynomial.C f : (Generators.self B C).Ring)) hf)))

/-- The class of the variable `[0]` of `A[C]` maps to the class of the variable `[0]` of `B[C]`:
that is the correction term of the zig-zag, and it is what makes the cycle `[f]` and the value of
the homotopy differ by an element of the image of `K/K² ⟶ J/J²`. -/
theorem cotangentMap_towerTopHom_mk_X :
    Extension.Cotangent.map (towerTopHom A B C).toExtensionHom
        (Extension.Cotangent.mk ⟨X (0 : C), X_mem_ker A C⟩) =
      Extension.Cotangent.mk ⟨X (0 : C), X_mem_ker B C⟩ := by
  rw [Extension.Cotangent.map_mk]
  exact congrArg _ (Subtype.ext
    ((Generators.Hom.toAlgHom_X (towerTopHom A B C) (0 : C)).trans (by rw [towerTopHom_val])))

/-- The class of `[0] - f` is the difference of the classes of `[0]` and of `f`. -/
theorem cotangent_mk_X_zero_sub_C {f : B} (hf : algebraMap B C f = 0) :
    Extension.Cotangent.mk ⟨X (0 : C) - MvPolynomial.C f, X_zero_sub_C_mem_ker B C hf⟩ =
      Extension.Cotangent.mk ⟨X (0 : C), X_mem_ker B C⟩ -
        Extension.Cotangent.mk ⟨MvPolynomial.C f, C_mem_ker_of_algebraMap_eq_zero B C hf⟩ := by
  rw [← map_sub]
  rfl

/-- **The zig-zag of the connecting morphism of [Stacks Project, Tag 0E1Y] on a conormal class**,
in additive form: for `f` in the kernel of `B ⟶ C`, the cycle `[f]` of `NL_{C/B}` in degree `-1`
plus the value of the homotopy of [Stacks Project, Tag 07VC] on `1 ⊗ d[f]` is the image of the
class of the variable `[0]` of `A[C]` under the comparison `K/K² ⟶ J/J²`. -/
theorem cotangent_mk_C_add_towerNullHomotopy {f : B} (hf : algebraMap B C f = 0) :
    Extension.Cotangent.mk ⟨MvPolynomial.C f, C_mem_ker_of_algebraMap_eq_zero B C hf⟩ +
        towerNullHomotopyBaseChange A B C
          ((1 : C) ⊗ₜ[B] (Generators.self A B).cotangentSpaceBasis f) =
      Extension.Cotangent.map (towerTopHom A B C).toExtensionHom
        (Extension.Cotangent.mk ⟨X (0 : C), X_mem_ker A C⟩) := by
  rw [towerNullHomotopyBaseChange_one_tmul,
    towerNullHomotopy_cotangentSpaceBasis_of_algebraMap_eq_zero A B C hf,
    cotangentMap_towerTopHom_mk_X, cotangent_mk_X_zero_sub_C B C hf]
  abel

/-- **The zig-zag of the connecting morphism of [Stacks Project, Tag 0E1Y] on a conormal
class.**  For `f` in the kernel of `B ⟶ C`, the cycle `[f]` of `NL_{C/B}` in degree `-1` is the
value of the homotopy of [Stacks Project, Tag 07VC] on `-(1 ⊗ d[f])` plus an element of the image
of the comparison `K/K² ⟶ J/J²`.

By `CochainComplex.mappingCone.cycle_comp_connecting` this says that the connecting morphism of
the six-term exact sequence carries `[f]` to the class of `-(1 ⊗ d[f])`, which by
`NaiveCotangent.toKaehler_baseChange_neg_basis` is `-(1 ⊗ d f)` in `C ⊗_B Ω_{B/A}` — minus the
first arrow of the conormal sequence of [Stacks Project, Tag 01UZ]. -/
theorem cotangent_mk_C_eq_towerNullHomotopy_add {f : B} (hf : algebraMap B C f = 0) :
    Extension.Cotangent.mk ⟨MvPolynomial.C f, C_mem_ker_of_algebraMap_eq_zero B C hf⟩ =
      towerNullHomotopyBaseChange A B C
          (-((1 : C) ⊗ₜ[B] (Generators.self A B).cotangentSpaceBasis f)) +
        Extension.Cotangent.map (towerTopHom A B C).toExtensionHom
          (Extension.Cotangent.mk ⟨X (0 : C), X_mem_ker A C⟩) := by
  rw [map_neg, ← cotangent_mk_C_add_towerNullHomotopy A B C hf]
  abel

/-- **The zig-zag, with the two members of the presentation ideals given as opaque variables.**
This is `NaiveCotangent.cotangent_mk_C_eq_towerNullHomotopy_add` restated so that no element of a
presentation ideal is written out: a subterm `⟨C f, _⟩` is only type-correct after unfolding
`Algebra.Extension.Ring`, and a goal containing one is refused by `rw`.  Consumers at a stalk
supply the two members and their values. -/
theorem cotangent_mk_eq_towerNullHomotopy_add {f : B} (hf : algebraMap B C f = 0)
    (jf : (Generators.self B C).ker) (hjf : jf.1 = MvPolynomial.C f)
    (x0 : (Generators.self A C).ker) (hx0 : x0.1 = X (0 : C)) :
    Extension.Cotangent.mk jf =
      towerNullHomotopyBaseChange A B C
          (-((1 : C) ⊗ₜ[B] (Generators.self A B).cotangentSpaceBasis f)) +
        Extension.Cotangent.map (towerTopHom A B C).toExtensionHom
          (Extension.Cotangent.mk x0) := by
  rw [show jf = ⟨MvPolynomial.C f, C_mem_ker_of_algebraMap_eq_zero B C hf⟩ from Subtype.ext hjf,
    show x0 = ⟨X (0 : C), X_mem_ker A C⟩ from Subtype.ext hx0]
  exact cotangent_mk_C_eq_towerNullHomotopy_add A B C hf

omit [Algebra A C] [IsScalarTower A B C] in
/-- **The class of `-(1 ⊗ d[f])` in `C ⊗_B Ω_{B/A}` is `-(1 ⊗ d f)`.**  The degree `0` cohomology
of `NL(P) ⊗_B C` is `C ⊗_B Ω_{B/A}`, the quotient map being the base change of
`Algebra.Extension.toKaehler`, and that map carries the basis element `d[b]` to `d b`. -/
theorem toKaehler_baseChange_neg_basis (f : B) :
    ((Generators.self A B).toExtension.toKaehler.baseChange C)
        (-((1 : C) ⊗ₜ[B] (Generators.self A B).cotangentSpaceBasis f)) =
      -((1 : C) ⊗ₜ[B] KaehlerDifferential.D A B f) := by
  rw [map_neg, LinearMap.baseChange_tmul, Generators.toKaehler_cotangentSpaceBasis]
  rfl

end NaiveCotangent

end
