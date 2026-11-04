module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeScaling
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeChartIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistActionLinear

/-!
# Tag 02NC over a base scheme: the comparison over a chart does not depend on the section

Tag 02NC's isomorphism is asserted to be **canonical**, and its proof glues the comparisons
attached to the members of a trivializing covering of the base. For the glueing to be possible
the comparison over one open must not depend on the trivializing section chosen there: two
sections of `ℒ` trivializing it over the same open differ by a unit of the functions on that
open, and the two comparisons they induce must have the same homogeneous spectrum map.

This file proves the degreewise half of that statement. Rescaling the local section by a
function `u` rescales the comparison in degree `d` by `u ^ d`, which is a *degree scaling* in the
sense of `Stacks.GradedRing.degreeScale`; the absolute input that turns a degree scaling into an
equality of morphisms of homogeneous spectra is
`Stacks.GradedRing.Proj_map_eq_of_target_degreeScale`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.powSecAt_smul`: **the powers of a rescaled
  local section are the rescaled powers**, `(u · x) ^ d = u ^ d · x ^ d`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiPieceAt_smul`: **rescaling the section
  rescales the degree-`d` comparison by `u ^ d`**, stated at the tensor pairing of sections.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiSectionAt_smul_of`: the same at the graded
  ring of sections, with the scalar read through the structure map
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom` — which is the shape
  `Stacks.GradedRing.Proj_map_eq_of_target_degreeScale` asks its hypothesis in.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiSectionAt_eq_degreeScale_comp`: the
  comparison attached to `u · x` **is** the comparison attached to `x` followed by the degree
  scaling by `u`.

## Implementation notes

**The scalar is taken at `funsAt`, the `structureSheaf`-of-the-ringed-site spelling of the
functions on the open, and not at `Γ(S, V)`.** The two are the same type, but they carry
*different* `Module` instances on the local sections of a tensor power of the twisting module,
and only the first is found by instance search for `(tp L n).val.obj (op V)`: with the scalar
declared at `Γ(S, V)` the term `u • x` does not even elaborate. Conversely the structure map of
the graded ring of sections is stated at `Γ(S, V)`, and `(twist 𝒜 L).strHom V u` is applied to
the `funsAt` element directly — term elaboration accepts it because the types agree, which a
`rw` would not.

For the same reason `psiPieceAt_smul` states its right-hand side at the tensor pairing of
sections rather than as a rescaled section of the homogeneous piece of the twist: the
`Γ(S, V)`-action is the one instance search finds on `(twist 𝒜 L).sectionPieces V d`, so writing
the rescaling there would reintroduce the mismatch. The passage to the section ring in
`psiSectionAt_smul_of` crosses the two spellings once, in term mode, and the multiplication it
lands in is the ring multiplication of `(twist 𝒜 L).sectionRing V`, where no module instance
appears at all.

Every proof is an induction or a transcription of bilinearity: `powSecAt` is a recursion whose
value at `U` mentions only values at `U`, the multiplication of the Laurent algebra is bilinear
by the `map_smul_left` and `map_smul_right` fields of its `BilinearMap`, the reindexing
comparisons are morphisms of sheaves of modules and hence linear, and the tensor pairing of
sections is linear in its right argument by
`Stacks.TwistActionLinear.tensorSectionsAt_smul_right`, whose scalar on the sections of the
tensor product is read at the canonical ring sheaf `Stacks.SheafOfModules.Tensor.ringSheaf`;
`psiPieceAt_smul` states its right-hand side at that spelling.

The successor step rewrites `pow_succ` and `smul_smul` **first**, before unfolding `powSecAt`:
applied at the end, on the unfolded goal, both fail, because the unfolding leaves a target that
is not type-correct at `implicit` transparency and `rw` then reports a missing pattern that is
present.

## What is not proved here

**That two trivializing sections differ by a unit.** This file takes the rescaling as given, and
proves only its degreewise effect. The extraction of the unit itself is **no longer owed**: it is
`Stacks.SheafOfModules.TensorGenerator.exists_unit_smul_generator` of
`StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeUnit`, the relative form
of `Stacks.GradedRing.exists_unit_smul_of_bijective_toSpanSingleton`, proved for an arbitrary
sheaf of modules trivialized over an arbitrary object of an arbitrary site.

**The passage to the morphisms of homogeneous spectra.**
`Stacks.GradedRing.Proj_map_eq_of_target_degreeScale` is stated for
`AlgebraicGeometry.Proj.map`, the morphism of a graded ring homomorphism whose domain of
definition is everything, while
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.isIso_mapHom_psiSectionAt` is stated for the
partial `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`; the identification of the two when the
domain is everything is `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map`.

No `stacks` attribute is attached: this is one input to the tag's canonicity, not the canonicity
itself.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory Filter Opposite
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- The functions on an open of the base, at the spelling the local sections of a tensor power
of the twisting module are a module over.

This is the same type as `Γ(S, V)`, but the two carry different `Module` instances on the
sections of a tensor power — only this one is found by instance search for
`(tp L n).val.obj (op V)`, while only `Γ(S, V)` is found for `Γ(tpMod L n, V)`. Rescaling a
local section is written at this spelling so that `rw` never meets a goal that is ill-typed at
`implicit` transparency; the structure map of the graded ring of sections is applied to the same
element at the `Γ(S, V)` spelling, which term elaboration accepts because the types agree. -/
abbrev funsAt (V : S.Opens) : Type u :=
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.sheaf.obj
    S.ringCatSheaf.property).obj.obj (op V)

/-- **The powers of a rescaled local section are the rescaled powers.** Rescaling a section of
the twisting module over an open by a function on that open rescales its `d`-th power by the
`d`-th power of the function.

This is the section-level content of the canonicity of Tag 02NC's comparison over one chart of
the base: two sections trivializing `ℒ` over the same open differ by a unit `u` of the functions
there, and the comparison attached to the second is therefore the comparison attached to the
first with its degree-`d` component rescaled by `u ^ d`, which is a degree scaling in the sense
of `Stacks.GradedRing.degreeScale`. -/
theorem powSecAt_smul {V : S.Opens} (u : funsAt V) (x : (tp L 1).val.obj (op V)) :
    ∀ d : ℕ, powSecAt L (op V) (u • x) d = u ^ d • powSecAt L (op V) x d
  | 0 => by rw [powSecAt_zero, powSecAt_zero, pow_zero, one_smul]
  | (d + 1) => by
      rw [pow_succ, ← smul_smul, powSecAt_succ, powSecAt_succ, powSecAt_smul u x d,
        (lmul L (d : ℤ) 1).map_smul_left (op V) (u ^ d) _ _,
        (lmul L (d : ℤ) 1).map_smul_right (op V) u _ _, map_smul, map_smul]

variable (𝒜 : SheafGradedAlgebra S)

/-- **Rescaling the local section rescales the degree-`d` comparison by `u ^ d`**, written at the
tensor pairing of sections so that no module structure on the homogeneous pieces of the twist is
named. See the module docstring for why the pairing, and not the scaled section of the twist, is
the right-hand side here. -/
theorem psiPieceAt_smul {V : S.Opens} (u : funsAt V) (x : (tp L 1).val.obj (op V)) (d : ℕ)
    (a : 𝒜.sectionPieces V d) :
    psiPieceAt L 𝒜 V (u • x) d a =
      (show (Tensor.ringSheaf ⟨S.sheaf.obj, S.sheaf.property⟩).obj.obj (op V) from u ^ d) •
        tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op V) (𝒜.piece (d : ℤ))
          (tp L (d : ℤ)) a (powSecAt L (op V) x d) := by
  rw [psiPieceAt_apply, powSecAt_smul L u x d]
  exact Stacks.TwistActionLinear.tensorSectionsAt_smul_right S.sheaf.obj
    S.ringCatSheaf.property (op V) (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) (u ^ d) a
    (powSecAt L (op V) x d)

/-- **The comparison attached to a rescaled section, on a homogeneous element of the graded ring
of sections**: it is the comparison attached to the section, multiplied by the `d`-th power of
the image of the function under the structure map.

This is the hypothesis of `Stacks.GradedRing.Proj_map_eq_of_target_degreeScale` in the shape that
lemma asks for it. -/
theorem psiSectionAt_smul_of {V : S.Opens} (u : funsAt V) (x : (tp L 1).val.obj (op V)) {d : ℕ}
    (a : 𝒜.sectionPieces V d) :
    psiSectionAt L 𝒜 V (u • x) (DirectSum.of (𝒜.sectionPieces V) d a) =
      (twist 𝒜 L).strHom V u ^ d *
        psiSectionAt L 𝒜 V x (DirectSum.of (𝒜.sectionPieces V) d a) :=
  (psiSectionAt_of L 𝒜 V (u • x) a).trans
    ((congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces V) d)
        (psiPieceAt_smul L 𝒜 u x d a)).trans
      (((twist 𝒜 L).strHom_mul_of V (u ^ d) (psiPieceAt L 𝒜 V x d a)).symm.trans
        ((congrArg (fun w : (twist 𝒜 L).sectionRing V =>
              w * DirectSum.of ((twist 𝒜 L).sectionPieces V) d (psiPieceAt L 𝒜 V x d a))
            (map_pow ((twist 𝒜 L).strHom V) u d)).trans
          (congrArg (fun z : (twist 𝒜 L).sectionRing V => (twist 𝒜 L).strHom V u ^ d * z)
            (psiSectionAt_of L 𝒜 V x a).symm))))

/-- **The comparison attached to a rescaled section is the comparison attached to the section
followed by the degree scaling by the function.** This is the equality of graded ring
homomorphisms that the canonicity of Tag 02NC's comparison over one chart of the base reduces to:
the absolute input that turns it into an equality of morphisms of homogeneous spectra is
`Stacks.GradedRing.Proj_map_eq_of_target_degreeScale`. -/
theorem psiSectionAt_eq_degreeScale_comp {V : S.Opens} (u : funsAt V)
    (x : (tp L 1).val.obj (op V)) :
    psiSectionAt L 𝒜 V (u • x) =
      (Stacks.GradedRing.degreeScale ((twist 𝒜 L).grading V)
          ((twist 𝒜 L).strHom_mem V u)).comp (psiSectionAt L 𝒜 V x) :=
  Stacks.GradedRing.gradedRingHom_ext (𝒜.grading V) fun d a ha => by
    obtain ⟨y, rfl⟩ := ha
    refine Eq.trans (psiSectionAt_smul_of L 𝒜 u x y) ?_
    exact (Stacks.GradedRing.degreeScale_apply_of_mem ((twist 𝒜 L).grading V)
      ((twist 𝒜 L).strHom_mem V u)
      ((psiSectionAt L 𝒜 V x).map_mem (𝒜.of_mem_grading V y))).symm

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
