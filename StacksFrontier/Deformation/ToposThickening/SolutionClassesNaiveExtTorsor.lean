module

public import StacksFrontier.Deformation.ToposThickening.SquareZeroExtensionNaiveExt
import StacksCore.Tactic.StacksAttribute

/-!
# Isomorphism classes of solutions are a torsor under `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` (Stacks 08UK)

Fix the square-zero extension problem (91.13.0.1) of [Stacks Project, Tag 08UF] for ringed topoi:
a first order thickening `t : (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ'), 𝒪_{ℬ'})` with ideal `𝒥 = Ker(t^♯)`, a
morphism of ringed topoi `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)`, an `𝒪`-module `𝒢` and a map
`c : f⁻¹𝒥 ⟶ 𝒢`; this is `S : Deformation.ToposThickening.RingedToposExtensionProblem X B`, and a
solution is `S.CompatibleFirstOrderThickening`. **Stacks 08UK** says that if a solution exists,
the set of isomorphism classes of solutions is a principal homogeneous space under
`Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)`.

The proof is the source's, assembled from its three ingredients:

* the obstruction class `o(𝒪'₁, 𝒪'₂) ∈ Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` of two solutions, Step 1 of the
  proof of [Stacks 08UG]
  (`...CompatibleFirstOrderThickening.pairObstruction`),
  which is a cocycle (`...pairDatumObstruction_add`);
* "this element is the obstruction to the existence of an isomorphism, hence separates the
  isomorphism classes" (`...pairObstruction_eq_zero_iff_isomorphic`);
* for a solution `𝒪'` and `ξ`, the pushout solution `𝒪'_ξ` with `o(𝒪', 𝒪'_ξ) = ξ`, the source's
  last paragraph and its omitted calculation (`...CompatibleFirstOrderThickening.twist`,
  `...pairObstruction_twist`).

These are bundled as
`...CompatibleFirstOrderThickening.pairObstructionData`,
and the principal homogeneous structure is the one they induce,
`...CompatibleFirstOrderThickening.naiveIsomorphismClassesAddTorsor`; the theorem below pins its
action to the source's.

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.exists_addTorsor_isomorphismClasses`:
  **Stacks 08UK**. If a solution exists there is a principal homogeneous structure of
  `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` on the isomorphism classes of solutions whose action is the source's:
  `ξ` carries the class of `𝒪'` to the class of `𝒪'_ξ`, and it carries the class of `𝒪'₁` to that
  of `𝒪'₂` exactly when `o(𝒪'₁, 𝒪'₂) = ξ`.

## Implementation notes

`Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` is `Stacks.SheafOfModules.naiveCotangentExt` of the ring map
`f^♯ : f⁻¹𝒪_ℬ ⟶ 𝒪`, that is `Ext¹` in the derived category of `𝒪`-modules out of the naive
cotangent complex of `f⁻¹𝒪_ℬ ⟶ 𝒪` built from its canonical presentation, which is what
`NL_{𝒪/𝒪_ℬ}` denotes in the source. The isomorphism classes are
`CompatibleFirstOrderThickening.IsomorphismClasses S`, solutions modulo isomorphisms over the
fixed diagram that are the identity on `𝒢`.

The source ringed topos is `AlgebraicGeometry.RingedTopos.{u, u, u}`, as for the pushout
solution `𝒪'_ξ` in `StacksFrontier/Deformation/ToposThickening/SolutionPushoutRealization.lean`.

## References

* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UJ](https://stacks.math.columbia.edu/tag/08UJ)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe t u v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

open CompatibleFirstOrderThickening in
/-- **Stacks Project, Tag 08UK.** For the square-zero extension problem of [Stacks 08UF] — a
first order thickening of `(Sh(ℬ), 𝒪_ℬ)` with ideal `𝒥`, a morphism of ringed topoi
`f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)`, an `𝒪`-module `𝒢` and `c : f⁻¹𝒥 ⟶ 𝒢` — if a solution exists,
then the set of isomorphism classes of solutions is principal homogeneous under
`Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)`.

The structure is the source's: `ξ` carries the class of a solution `𝒪'` to the class of the
pushout solution `𝒪'_ξ` of the proof, and it carries the class of `𝒪'₁` to the class of `𝒪'₂`
exactly when the obstruction class `o(𝒪'₁, 𝒪'₂)` of [Stacks 08UG] is `ξ`. -/
@[stacks 08UK]
theorem exists_addTorsor_isomorphismClasses (S : RingedToposExtensionProblem X B)
    (hne : Nonempty S.CompatibleFirstOrderThickening) :
    ∃ T : AddTorsor
        (Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t} X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage S.G 1)
        (IsomorphismClasses S),
      (∀ (ξ : Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t} X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage S.G 1)
          (P Q : S.CompatibleFirstOrderThickening),
        T.vadd ξ (Quotient.mk (isomorphicSetoid S) P) = Quotient.mk (isomorphicSetoid S) Q ↔
          pairObstruction P Q = ξ) ∧
      ∀ (ξ : Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t} X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage S.G 1)
          (P : S.CompatibleFirstOrderThickening),
        T.vadd ξ (Quotient.mk (isomorphicSetoid S) P) =
          Quotient.mk (isomorphicSetoid S) (P.twist ξ) := by
  let := hne
  let T := naiveIsomorphismClassesAddTorsor S
  have h₁ : ∀ (ξ : Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t} X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage S.G 1)
      (P Q : S.CompatibleFirstOrderThickening),
      T.vadd ξ (Quotient.mk (isomorphicSetoid S) P) = Quotient.mk (isomorphicSetoid S) Q ↔
        pairObstruction P Q = ξ := by
    intro ξ P Q
    refine eq_comm.trans ((eq_vadd_iff_vsub_eq _ ξ _).trans ?_)
    exact Iff.of_eq (congrArg (· = ξ) (naiveIsomorphismClassesAddTorsor_vsub S Q P))
  refine ⟨T, h₁, fun ξ P => (h₁ ξ P (P.twist ξ)).2 (pairObstruction_twist P ξ)⟩

end Deformation.ToposThickening.RingedToposExtensionProblem

end
