module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemAmbient
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic

/-!
# From a compatible tower of generating sections to the cartesian tower of [Stacks, Tag 0899]

A generating tuple (`Stacks.ProjectiveSpaceModuli.GeneratingTuple`) on a scheme `X` is an
invertible module together with `N + 1` global sections generating it at every stalk; it induces
a morphism `X ⟶ ℙᴺ_ℤ`. A tower of schemes over the thickenings `Sₙ` of `Spec A` with cartesian
squares, together with a tower of generating tuples compatible under pullback, induces morphisms
into the adic base changes of `ℙᴺ_{Spec A}` whose squares are cartesian.

## Main definitions

* `Stacks.AmpleFormalSystemSections.tupleHom` — the morphism `X ⟶ ℙᴺ_ℤ` attached to a generating
  tuple; this is `φ_{(L, (s₀, …, s_N))}` of Section 27.13 read on the integral model.

## Main results

* `Stacks.AmpleFormalSystemSections.tupleHom_congr` — isomorphic tuples induce the same morphism.
* `Stacks.AmpleFormalSystemSections.comp_tupleHom` — the morphism is natural in the source.
* `Stacks.AmpleFormalSystemSections.isPullback_adicLift_tupleHom` — **the cartesian tower.** A
  tower of schemes over the thickenings with cartesian squares, together with a tower of
  generating tuples compatible under pullback, induces morphisms into the adic base changes of
  `ℙᴺ_{Spec A}` with cartesian squares.
* `Stacks.AmpleFormalSystemSections.isClosedImmersion_adicLift` — a closed immersion into
  `ℙᴺ_{Sₙ}` is a closed immersion into `ℙᴺ_S ×_S Sₙ`.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli
open Stacks.AmpleFormalSystemAmbient

universe u

namespace Stacks.AmpleFormalSystemSections

/-! ### The morphism attached to a generating tuple -/

variable {X Y : Scheme.{u}} {N : ℕ}

/-- **The morphism `X ⟶ ℙᴺ_ℤ` attached to a generating tuple**, that is `φ_{(L, (s₀, …, s_N))}`
of [Stacks, Tag 01ND] read on the integral model of projective space. -/
public def tupleHom (t : GeneratingTuple X N) : X ⟶ projectiveSpaceAtUniverse.{u} N :=
  toProjectiveSpaceAtUniverse t.coord t.generates

/-- **The class of `tupleHom t` under the classifying map of [Stacks, Tag 01NE] is the class of
`t`.** -/
public lemma pointsOfHom_tupleHom (t : GeneratingTuple X N) :
    pointsOfHom (tupleHom t) = ⟦t⟧ :=
  Quotient.sound (isomorphic_tautological_of_isPinned (t := t)
    fun k => ι_toProjectiveSpaceAtUniverse t.coord t.generates k)

/-- **Isomorphic generating tuples induce the same morphism to the integral model.** -/
public lemma tupleHom_congr {t t' : GeneratingTuple X N} (h : Isomorphic t t') :
    tupleHom t = tupleHom t' := by
  refine pointsOfHom_injective ?_
  rw [pointsOfHom_tupleHom, pointsOfHom_tupleHom]
  exact Quotient.sound h

/-- **The morphism attached to a tuple is natural in the source scheme.** -/
public lemma comp_tupleHom (h : Y ⟶ X) (t : GeneratingTuple X N) :
    h ≫ tupleHom t = tupleHom (pullbackTuple h t) := by
  refine pointsOfHom_injective ?_
  rw [pointsOfHom_comp, pointsOfHom_tupleHom, pullbackPoints_mk, pointsOfHom_tupleHom]

/-- **Every morphism to the integral model is the one attached to its own tautological tuple.**
-/
public lemma tupleHom_tautological (g : X ⟶ projectiveSpaceAtUniverse.{u} N) :
    tupleHom (tautological g) = g :=
  pointsOfHom_injective (pointsOfHom_tupleHom (tautological g))

/-- **The tautological tuple of a closed immersion into `ℙᴺ_S` over `S` induces a closed
immersion into `ℙᴺ_S`.** If `ψ : Y ⟶ ℙᴺ_S` is a closed immersion lying over `p : Y ⟶ S`, then
the lift over `p` of the morphism attached to the tautological tuple of `ψ` is a closed
immersion. -/
public lemma isClosedImmersion_liftOver_tupleHom_tautological {S : Scheme.{u}} (p : Y ⟶ S)
    (ψ : Y ⟶ projectiveSpaceOver N S)
    (hover : ψ ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} N)) = p)
    (hψ : IsClosedImmersion ψ) :
    IsClosedImmersion (Stacks.AmpleProjectiveImmersion.liftOver p
      (tupleHom (tautological (ψ ≫ projectiveSpaceOver.toIntegralAtUniverse N S)))) := by
  rw [tupleHom_tautological, Stacks.AmpleProjectiveImmersion.liftOver_eq p ψ hover]
  exact hψ

/-! ### The comparison of `ℙᴺ_{Sₙ}` with `ℙᴺ_S ×_S Sₙ` -/

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The thickening `Sₙ ⟶ Spec A` is a closed immersion. -/
public instance isClosedImmersion_adicThickeningι (n : ℕ) :
    IsClosedImmersion (adicThickeningι A I n) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

variable {A I}

/-- **The morphism into the ambient scheme factors through `ℙᴺ_{Sₙ}`.** The morphism attached to
`q : Y ⟶ Sₙ` and `g : Y ⟶ ℙᴺ_ℤ` is the corresponding morphism into `ℙᴺ_{Sₙ}` followed by the base
change morphism `ℙᴺ_{Sₙ} ⟶ ℙᴺ_{Spec A}`. -/
public lemma toAmbient_eq_liftOver_comp (n : ℕ) (q : Y ⟶ adicThickening A I n)
    (g : Y ⟶ projectiveSpaceAtUniverse.{u} N) :
    toAmbient (A := A) (I := I) (N := N) q g =
      Stacks.AmpleProjectiveImmersion.liftOver (n := N) q g ≫
        projectiveSpaceOverMap N (adicThickeningι A I n) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projectiveSpaceOverMap_fst, ← Category.assoc,
      Stacks.AmpleProjectiveImmersion.liftOver_fst]
    exact toAmbient_ambientHom q g
  · rw [Category.assoc, projectiveSpaceOverMap_snd,
      Stacks.AmpleProjectiveImmersion.liftOver_snd]
    exact toAmbient_toIntegralAtUniverse q g

/-- **A closed immersion into `ℙᴺ_{Sₙ}` is a closed immersion into `ℙᴺ_S ×_S Sₙ`.** -/
public lemma isClosedImmersion_adicLift (n : ℕ) (q : Y ⟶ adicThickening A I n)
    (g : Y ⟶ projectiveSpaceAtUniverse.{u} N)
    (h : IsClosedImmersion (Stacks.AmpleProjectiveImmersion.liftOver (n := N) q g)) :
    IsClosedImmersion (adicLift (A := A) (I := I) (N := N) q g) := by
  have hmap : IsClosedImmersion (projectiveSpaceOverMap N (adicThickeningι A I n)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_projectiveSpaceOverMap N (adicThickeningι A I n)).flip inferInstance
  have hcomp : IsClosedImmersion
      (adicLift (A := A) (I := I) (N := N) q g ≫
        pullback.fst (ambientHom A N) (adicThickeningι A I n)) := by
    rw [adicLift_fst, toAmbient_eq_liftOver_comp n q g]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (pullback.fst (ambientHom A N) (adicThickeningι A I n))

/-! ### The cartesian tower -/

variable (A I N)

/-- **The cartesian tower of [Stacks, Tag 0899] from a compatible tower of generating tuples.**

Let `Xₙ` be a tower of schemes over the thickenings `Sₙ = Spec (A / Iⁿ⁺¹)` whose squares are
cartesian, and let `tₙ` be a tower of generating tuples on the `Xₙ` — an invertible module with
`N + 1` generating global sections at each level — such that the pullback of `t_{n+1}` along
`Xₙ ⟶ X_{n+1}` is isomorphic to `tₙ`. Then the induced morphisms
`Xₙ ⟶ ℙᴺ_{Spec A} ×_{Spec A} Sₙ` have cartesian squares over the transition maps. -/
public lemma isPullback_adicLift_tupleHom {Xn : ℕ → Scheme.{u}}
    (q : ∀ n, Xn n ⟶ adicThickening A I n) (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (t : ∀ n, GeneratingTuple (Xn n) N)
    (ht : ∀ n, Isomorphic (pullbackTuple (i n) (t (n + 1))) (t n)) (n : ℕ) :
    IsPullback (i n) (adicLift (A := A) (I := I) (N := N) (q n) (tupleHom (t n)))
      (adicLift (q (n + 1)) (tupleHom (t (n + 1))))
      (adicBaseChangeSucc A I (ambientHom A N) n) :=
  isPullback_adicLift A I N q i hcart (fun m => tupleHom (t m))
    (fun m => (comp_tupleHom (i m) (t (m + 1))).trans (tupleHom_congr (ht m))) n

end Stacks.AmpleFormalSystemSections

end
