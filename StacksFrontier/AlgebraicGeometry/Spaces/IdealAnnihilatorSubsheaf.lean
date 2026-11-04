module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.Exactness

/-!
# Sections of a module annihilated by an ideal sheaf on an algebraic space

Let `F` be an algebraic space, `I ⊆ 𝒪_F` a sheaf of ideals and `G` an `𝒪_F`-module on the
small étale site of `F`.  The sections of `G` that `I` annihilates form a submodule sheaf of
`G`: over an étale chart `W` it consists of those `s ∈ G(W)` such that every section of `I`
over every chart `W' → W` kills the restriction of `s` to `W'`.  This is the subsheaf whose
quasi-coherence is the subject of [Stacks, Tag 0856].

## Main definitions

* `AlgebraicGeometry.Space.annihilatorSubmodule` is that submodule sheaf of `G`.  It is the
  object named by [Stacks, Tag 0857], the *subsheaf of sections annihilated by `I`*.

## Main results

* `AlgebraicGeometry.Space.mem_annihilatorSubmodule_obj` identifies its sections over every
  étale chart.
* `AlgebraicGeometry.Space.smul_annihilatorSubmodule_eq_zero`: `I` annihilates it.
* `AlgebraicGeometry.Space.le_annihilatorSubmodule`: it is the largest submodule sheaf of `G`
  that `I` annihilates.

## Implementation notes

An ideal sheaf is a submodule sheaf of the structure sheaf viewed as a module over itself,
which is the vocabulary `AlgebraicGeometry.Space.definingIdealSheaf` already uses; no
quasi-coherence or finiteness of `I` is needed for anything in this file.

The subsheaf is the general-site construction
`Stacks.SheafOfModules.annihilatorSubmodule` read on the small étale ringed site of `F`, so
its sheaf condition is not re-derived here.  That construction asks for commutativity of the
coefficient ring sheaf as a hypothesis, because sheaves of modules are indexed by a sheaf of
possibly non-commutative rings; on a ringed site the hypothesis is
`AlgebraicGeometry.RingedSite.mul_comm_ringSheaf`, commutativity being transported from the
`CommRingCat`-valued structure sheaf.  The module sections live in the universe of the
schemes, which is the universe the general construction forces them to share with the
coefficient rings.

## References

* [Stacks Project, Tag 0856](https://stacks.math.columbia.edu/tag/0856)
* [Stacks Project, Tag 0857](https://stacks.math.columbia.edu/tag/0857)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry

/-- The sections of the structure sheaf of a ringed site commute, in the shape the
general-site annihilator construction takes as a hypothesis.  Sheaves of modules are indexed
by a `RingCat`-valued sheaf, where commutativity is not an instance; it is transported here
from the `CommRingCat`-valued structure sheaf of the ringed site. -/
theorem RingedSite.mul_comm_ringSheaf (X : RingedSite.{u, v, w}) (U : (X.C)ᵒᵖ)
    (a b : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj U) : a * b = b * a := by
  let _ : CommRing (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj U) :=
    inferInstanceAs (CommRing (X.O.obj.obj U))
  exact mul_comm a b

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The subsheaf of sections annihilated by an ideal sheaf on an algebraic space**, the
object of [Stacks, Tag 0856].  Its sections over an étale chart `W` are the sections of `G`
over `W` all of whose restrictions are annihilated by the sections of `I` there, and that rule
defines a submodule sheaf of `G`. -/
@[stacks 0856 "the subsheaf"]
noncomputable def annihilatorSubmodule
    (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (G : Modules.{u, u} B S hS F hF) : G.Submodule :=
  Stacks.SheafOfModules.annihilatorSubmodule G
    (RingedSite.mul_comm_ringSheaf (smallEtaleRingedSite B S hS F hF)) I

-- Definition 0857 names the subsheaf of sections of `G` annihilated by `I`, which for a
-- quasi-coherent `I` of finite type is the subsheaf constructed in Lemma 0856; that
-- construction is `AlgebraicGeometry.Space.annihilatorSubmodule`, available for every `I`.
add_to_stacks 0857 "the subsheaf of sections annihilated by `I`" annihilatorSubmodule

variable {B S hS F hF}
  {I : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule}
  {G : Modules.{u, u} B S hS F hF}

/-- **The sections of the annihilator subsheaf of [Stacks, Tag 0856].**  A section `s` of `G`
over an étale chart is annihilated by `I` exactly when, over every chart `W'` over it, every
section of `I` kills the restriction of `s` to `W'`. -/
@[stacks 0856 "the sections"]
theorem mem_annihilatorSubmodule_obj (W : (SmallEtale B S hS F)ᵒᵖ) (s : G.val.obj W) :
    s ∈ (annihilatorSubmodule B S hS F hF I G).toSubmodule.obj W ↔
      ∀ (W' : (SmallEtale B S hS F)ᵒᵖ) (g : W ⟶ W')
        (a : ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)).obj.obj W'),
        a ∈ I.obj W' → a • G.val.restrictₛₗ g s = 0 :=
  Iff.rfl

/-- The ideal sheaf annihilates every section of its annihilator subsheaf. -/
theorem smul_annihilatorSubmodule_eq_zero (W : (SmallEtale B S hS F)ᵒᵖ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj.obj W)
    (ha : a ∈ I.obj W)
    (s : (annihilatorSubmodule B S hS F hF I G).toSheafOfModules.val.obj W) :
    a • s = 0 :=
  Stacks.SheafOfModules.smul_annihilatorSubmodule_eq_zero G _ I W a ha s

/-- **The annihilator subsheaf is the largest submodule sheaf of `G` that `I` annihilates.**
Together with `AlgebraicGeometry.Space.smul_annihilatorSubmodule_eq_zero` this characterizes
it among the submodule sheaves of `G`. -/
theorem le_annihilatorSubmodule (N : G.Submodule)
    (hN : ∀ (W : (SmallEtale B S hS F)ᵒᵖ) (s : G.val.obj W), s ∈ N.toSubmodule.obj W →
      ∀ a :
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj.obj W,
        a ∈ I.obj W → a • s = 0) :
    N ≤ annihilatorSubmodule B S hS F hF I G := by
  refine SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun W => ?_)
  intro s hs
  refine (mem_annihilatorSubmodule_obj (I := I) W s).mpr fun W' g a ha => ?_
  exact hN W' _ (N.toSubmodule.map_mem g hs) a ha

end Space

end AlgebraicGeometry

end
