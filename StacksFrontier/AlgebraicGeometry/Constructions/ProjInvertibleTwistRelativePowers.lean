module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeChartIso

/-!
# The powers of a trivializing local section trivialize the powers of the twisting module

`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.TrivializesPower L V x d` says that the `d`-th
tensor power of the twisting module is trivialized over the open `V` by the `d`-th power of the
local section `x`. Every chartwise statement about Tag 02NC is conditional on that hypothesis, in
every positive degree; this file discharges all of them **from the degree-one case alone**, which
is what a section trivializing `ℒ` over `V` supplies.

The induction is the obvious one, and the point is that it closes definitionally. The
trivialization in degree `d + 1` is the composite

`(ℒ^{⊗ d+1})|_V ≅ (ℒ^{⊗ d} ⊗ ℒ)|_V ≅ (ℒ^{⊗ d})|_V ≅ 𝒪_V`,

the first arrow the reindexing and the coherent multiplication of Tag 01CU, the second
`Stacks.SheafOfModules.TensorGenerator.tensorTrivialIso` — tensoring with a module trivial over
`V` changes nothing over `V` — and the third the trivialization in degree `d`. Its generator is
the image of `1`, and reading that through
`Stacks.SheafOfModules.TensorGenerator.tensorTrivialIso_inv_app` gives the tensor pairing of the
degree-`d` generator with the degree-one generator, which is
`Stacks.SheafOfModules.TensorPower.mulBilinear_app` — by `rfl` — the Laurent multiplication of the
two, and that is the recursion defining `powSecAt`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.powSecAt_one`: the first power of a local
  section is the section.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.trivializesPower_succ`: **the inductive
  step.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.trivializesPower_of_one`: **the powers of a
  trivializing local section trivialize the powers**, in every positive degree.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- **The first power of a local section is the section itself.** The recursion defining
`powSecAt` multiplies the unit section of the Laurent algebra by `x` and reindexes, and both steps
are the identity up to heterogeneous equality. -/
theorem powSecAt_one (U : (Opens S)ᵒᵖ) (x : (tp L 1).val.obj U) :
    powSecAt L U x 1 = x :=
  eq_of_heq ((heq_reix L (succ_cast 0) U
      ((lmul L (0 : ℤ) 1).app U (powSecAt L U x 0) x)).trans
    (TensorPower.mulBilinear_one_mul S.sheaf.obj S.ringCatSheaf.property L 1 U x))

/-- **The inductive step**: if the `d`-th tensor power is trivialized over `V` by the `d`-th power
of `x` and the first is trivialized by `x`, then the `(d+1)`-st is trivialized by the
`(d+1)`-st power.

The trivialization is the reindexing and the coherent multiplication of Tag 01CU, followed by
`Stacks.SheafOfModules.TensorGenerator.tensorTrivialIso` for the degree-one factor, followed by
the degree-`d` trivialization. -/
theorem trivializesPower_succ {V : S.Opens} {x : (tp L 1).val.obj (op V)} {d : ℕ}
    (hd : TrivializesPower L V x d) (h1 : TrivializesPower L V x 1) :
    TrivializesPower L V x (d + 1) := by
  obtain ⟨ed, hed⟩ := hd
  obtain ⟨e1, he1⟩ := h1
  have he1' : TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property V (tp L 1) e1 = x :=
    he1.trans (powSecAt_one L (op V) x)
  refine ⟨(SheafOfModules.overFunctor _ V).mapIso (reix L (succ_cast d)).symm ≪≫
    (SheafOfModules.overFunctor _ V).mapIso
        (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L (d : ℤ) 1).symm ≪≫
      TensorGenerator.tensorTrivialIso S.sheaf.obj S.ringCatSheaf.property V
        (tp L (d : ℤ)) (tp L 1) e1 ≪≫ ed, ?_⟩
  show (reix L (succ_cast d)).hom.val.app (op V)
      ((TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L (d : ℤ) 1).hom.val.app
        (op V)
        (((TensorGenerator.tensorTrivialIso S.sheaf.obj S.ringCatSheaf.property V
            (tp L (d : ℤ)) (tp L 1) e1).inv.val.app (op (Over.mk (𝟙 V)))).hom
          (TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property V
            (tp L (d : ℤ)) ed))) =
    powSecAt L (op V) x (d + 1)
  rw [TensorGenerator.tensorTrivialIso_inv_app S.sheaf.obj S.ringCatSheaf.property V
    (tp L (d : ℤ)) (tp L 1) e1
    (TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property V (tp L (d : ℤ)) ed)]
  rw [he1', hed, powSecAt_succ]
  rfl

/-- **The powers of a trivializing local section trivialize the powers of the twisting module.**

This discharges, from the degree-one case alone, the hypothesis that every chartwise statement
about Tag 02NC over a base scheme carries. A section of `ℒ` trivializing it over an open of the
base therefore supplies the comparison, its invertibility, and its canonicity there. -/
theorem trivializesPower_of_one {V : S.Opens} {x : (tp L 1).val.obj (op V)}
    (h1 : TrivializesPower L V x 1) : ∀ d : ℕ, 0 < d → TrivializesPower L V x d := by
  intro d hd
  induction d with
  | zero => exact absurd hd (lt_irrefl 0)
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact hn ▸ h1
      · exact trivializesPower_succ L (ih hn) h1

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
