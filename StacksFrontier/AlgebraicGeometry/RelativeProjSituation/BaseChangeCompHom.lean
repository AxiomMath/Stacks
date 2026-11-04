module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChangeCompAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeInG

/-!
# The composite identification of a relative `Proj` situation

`Stacks.RelativeProj.Situation.gradedBaseChange_comp` states the composition law for the base
change of graded section rings along a pair `q : S'' ⟶ S'`, `g : S' ⟶ S` for an identification
`Θ` of the graded algebra of `s''` with the pullback of the graded algebra of `s` along `q ≫ g`,
*given* the degreewise compatibility of `Θ` with the identifications `Φ` for `g` and `Ψ` for `q`.
`Θ` was a variable there, and the implementation notes of that file record why: multiplicativity
of the canonical comparison `(q ≫ g)^*𝒜ᵢ ≅ q^*(g^*𝒜ᵢ)` is an equation at arbitrary local
sections, which the section formula for a pullback does not reach.

This file constructs `Θ` from
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCompHom` — the composition law for
the base-changed graded algebra, whose multiplicativity is the morphism-level identity
`Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.mulSheaf_comp_pullbackComp` rather than a
computation on sections — and discharges the compatibility hypothesis, so the composition law
becomes unconditional.

## Main definitions

* `Stacks.RelativeProj.Situation.gradedPullbackComp`: **the composite identification `Θ`**, the
  canonical comparison of the iterated pullback inverted, then `q^*Φ`, then `Ψ`.

## Main results

* `Stacks.RelativeProj.Situation.canHom_comp_gradedPullbackComp`: **the compatibility
  hypothesis, discharged.** The hypothesis `hΘ` of
  `Stacks.RelativeProj.Situation.pieceSectionHom_comp` holds for `gradedPullbackComp`.
* `Stacks.RelativeProj.Situation.isIso_gradedPullbackComp_app`: the composite identification is
  an isomorphism in each degree in which `Φ` and `Ψ` are.
* `Stacks.RelativeProj.Situation.pieceSectionHom_comp_gradedPullbackComp` and
  `gradedBaseChange_comp_gradedPullbackComp`: **the composition law, unconditionally.**

## Implementation notes

The three spellings `Stacks.Conormal.gradedPullback g 𝒜`,
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebra g 𝒜` and
`Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom g) 𝒜` are equal by definition, as are
`s.base.ringCatSheaf` and `Stacks.RingedSpace.structureRingSheaf s.base.toRingedSpace`, so no
transport appears below and every identification is stated in the spelling its consumer uses.

`Stacks.AlgebraicGeometry.ModuleLimits.canHom_rfl` is what joins the two: the component of the
composition law in degree `n` is `AlgebraicGeometry.Scheme.Modules.pullbackComp`, and at the
composite written out that is the canonical comparison `canHom` the degreewise base-change
statements are phrased with.

No `@[stacks]` attribute is attached: this is a functoriality statement about a construction of
this development.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ModuleLimits
open SheafOfModules.GradedAlgebra

universe u

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {s s' s'' : Situation.{u}} (g : s'.base ⟶ s.base) (q : s''.base ⟶ s'.base)
  (Φ : UnitalHom (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (Ψ : UnitalHom (Stacks.Conormal.gradedPullback q s'.algebra) s''.algebra)

/-- **The composite identification.** Given identifications `Φ` of the graded algebra of `s'`
with the pullback of that of `s` along `g` and `Ψ` of that of `s''` with the pullback of that of
`s'` along `q`, the graded algebra of `s''` is identified with the pullback of that of `s` along
`q ≫ g`: undo the canonical comparison of the iterated pullback, then pull `Φ` back along `q`,
then apply `Ψ`. -/
def gradedPullbackComp :
    UnitalHom (Stacks.Conormal.gradedPullback (q ≫ g) s.algebra) s''.algebra :=
  (baseAlgebraCompHomInv s.algebra q g).comp ((baseAlgebraMapHom q Φ).comp Ψ)

/-- In degree `n`, the composite identification is the inverse of the canonical comparison of
the iterated pullback, followed by `q^*Φₙ`, followed by `Ψₙ`. -/
@[simp] theorem gradedPullbackComp_app (n : ℤ) :
    (gradedPullbackComp g q Φ Ψ).app n =
      (baseAlgebraCompHomInv s.algebra q g).app n ≫
        (Scheme.Modules.pullback q).map (Φ.app n) ≫ Ψ.app n := rfl

/-- **The compatibility hypothesis of the composition law, discharged.** The canonical
comparison `q^*(g^*𝒜ₙ) ≅ (q ≫ g)^*𝒜ₙ` followed by the composite identification is `q^*Φₙ`
followed by `Ψₙ`. This is the hypothesis `hΘ` of
`Stacks.RelativeProj.Situation.pieceSectionHom_comp` and the hypothesis `hcomp` of
`Stacks.RelativeProj.Situation.chartBaseChangeHom_comp`. -/
theorem canHom_comp_gradedPullbackComp (n : ℤ) :
    canHom q g (q ≫ g) rfl (s.algebra.piece n) ≫ (gradedPullbackComp g q Φ Ψ).app n =
      (Scheme.Modules.pullback q).map (Φ.app n) ≫ Ψ.app n := by
  have h1 : (baseAlgebraCompHom s.algebra q g).app n ≫
      (baseAlgebraCompHomInv s.algebra q g).app n = 𝟙 _ :=
    congrArg (fun φ : UnitalHom (baseAlgebra q (baseAlgebra g s.algebra))
        (baseAlgebra q (baseAlgebra g s.algebra)) => φ.app n)
      (baseAlgebraCompHom_comp_inv s.algebra q g)
  have key : (baseAlgebraCompHom s.algebra q g).app n ≫
      ((baseAlgebraCompHomInv s.algebra q g).app n ≫
        ((Scheme.Modules.pullback q).map (Φ.app n) ≫ Ψ.app n)) =
      (Scheme.Modules.pullback q).map (Φ.app n) ≫ Ψ.app n :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ ((Scheme.Modules.pullback q).map (Φ.app n) ≫ Ψ.app n)) h1)).trans
      (Category.id_comp _)
  exact (congrArg (fun z => z ≫ (gradedPullbackComp g q Φ Ψ).app n)
    (canHom_rfl q g (s.algebra.piece n))).trans key

/-- **The composite identification is an isomorphism in every degree in which both factors
are.** So the invertibility hypothesis that the comparison morphism along `q ≫ g` asks for is
not an extra assumption. -/
theorem isIso_gradedPullbackComp_app (n : ℤ) (hΦ : IsIso (Φ.app n)) (hΨ : IsIso (Ψ.app n)) :
    IsIso ((gradedPullbackComp g q Φ Ψ).app n) := by
  have hmap : IsIso ((Scheme.Modules.pullback q).map (Φ.app n)) :=
    @Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.pullback q) (Φ.app n) hΦ
  have hrhs : IsIso ((Scheme.Modules.pullback q).map (Φ.app n) ≫ Ψ.app n) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hmap hΨ
  have hinv : IsIso ((baseAlgebraCompHomInv s.algebra q g).app n) :=
    isIso_baseAlgebraCompHomInv_app s.algebra q g n
  rw [gradedPullbackComp_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hinv hrhs

/-- **The degreewise composition law, unconditionally.** Pulling a homogeneous section back
along `g` and then along `q` is pulling it back along `q ≫ g`, for the composite
identification. -/
theorem pieceSectionHom_comp_gradedPullbackComp (n : ℕ) (W : s.base.Opens)
    (W' : s'.base.Opens) (W'' : s''.base.Opens) (h : W' ≤ g ⁻¹ᵁ W) (h' : W'' ≤ q ⁻¹ᵁ W')
    (h'' : W'' ≤ (q ≫ g) ⁻¹ᵁ W) (a : s.sectionPieces W n) :
    pieceSectionHom q Ψ n W' W'' h' (pieceSectionHom g Φ n W W' h a)
      = pieceSectionHom (q ≫ g) (gradedPullbackComp g q Φ Ψ) n W W'' h'' a :=
  pieceSectionHom_comp g q Φ Ψ (gradedPullbackComp g q Φ Ψ) n
    (canHom_comp_gradedPullbackComp g q Φ Ψ (n : ℤ)) W W' W'' h h' h'' a

/-- **The composition law for the base change of graded section rings, unconditionally.**
Base-changing along `g` and then along `q` is base-changing along `q ≫ g`, for the composite
identification. This is the form `AlgebraicGeometry.Proj.map_comp` consumes. -/
theorem gradedBaseChange_comp_gradedPullbackComp (W : s.base.Opens) (W' : s'.base.Opens)
    (W'' : s''.base.Opens) (h : W' ≤ g ⁻¹ᵁ W) (h' : W'' ≤ q ⁻¹ᵁ W')
    (h'' : W'' ≤ (q ≫ g) ⁻¹ᵁ W) :
    (gradedBaseChange q Ψ W' W'' h').comp (gradedBaseChange g Φ W W' h)
      = gradedBaseChange (q ≫ g) (gradedPullbackComp g q Φ Ψ) W W'' h'' :=
  gradedBaseChange_comp g q Φ Ψ (gradedPullbackComp g q Φ Ψ) W W' W'' h h' h''
    fun n a => pieceSectionHom_comp_gradedPullbackComp g q Φ Ψ n W W' W'' h h' h'' a

end Stacks.RelativeProj.Situation

end
