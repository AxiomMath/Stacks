module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# A limiting fork of sheaves of modules is detected by the underlying sheaves of sets

Let `R` be a sheaf of rings on a site and let

`E --ι--> F ⇉ H`

be a fork of sheaves of `R`-modules.  This file proves that the fork is a limit as soon as the
fork of the *underlying sheaves of sets* is: the functor
`CategoryTheory.Sheaf.moduleSheafFunctor` reflects the limits of forks.

The proof is the elementary one.  A morphism of sheaves of modules is the same thing as a
morphism of the underlying sheaves of sets commuting with the addition and the scalar
multiplication (`Stacks.Sheaves.RingedToposModules.homEquivSubtype`), so the lift of a fork
produced by the limiting fork of sheaves of sets only has to be shown linear; and the first
arrow of a limiting fork is a monomorphism, so each of the two linearity squares may be
checked after composing with it, where it becomes the linearity of the arrows one started
from.  Uniqueness of the lift is the same monomorphy together with faithfulness of the functor
(`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`).

No hypothesis beyond the two `CategoryTheory.GrothendieckTopology.HasSheafCompose` instances
that `CategoryTheory.Sheaf.moduleSheafFunctor` itself needs is used; in particular neither
sheafification nor any smallness condition is required, and nothing is assumed about the
existence of limits in the category of sheaves of modules.

## Main results

* `Stacks.Sheaves.RingedToposModules.isLimitForkOfIsLimitForkModuleSheaf`: **a fork of sheaves
  of modules whose fork of underlying sheaves of sets is a limit is a limit.**
* `Stacks.Sheaves.RingedToposModules.isLimitForkOfIsLimitForkModuleSheafOfEq`: the same with the
  three arrows of the fork of sheaves of sets supplied separately, each pinned to the image of
  the corresponding arrow of modules by an equation.
* `Stacks.Sheaves.RingedToposModules.reflectsLimit_parallelPair_moduleSheafFunctor`: the same
  statement as an instance, **`CategoryTheory.Sheaf.moduleSheafFunctor` reflects the limit of a
  parallel pair**, which is what makes Mathlib's reflection API apply to it.

## Implementation notes

The second form exists because the image of a morphism of sheaves of modules under
`CategoryTheory.Sheaf.moduleSheafFunctor` is in practice available only up to a *proved*
equation with the arrow a consumer actually holds, and not up to definitional unfolding: the
direct images and restrictions those arrows are built from are not projections of a composite
of functors but are produced by choice, so asking the elaborator to identify two such spellings
unfolds them and does not come back.  Supplying the three equations as hypotheses lets the
consumer discharge them by the lemmas it has.

The fork condition of the image fork is named
(`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_fork_condition`) rather than written
inline, so that the hypothesis of the main result reads as the image of the given fork.

**Applying these at a concrete site: pass `R` explicitly.**  Where the category of sheaves of
modules carries a name of its own — `AlgebraicGeometry.Space.Modules` for the small étale site
of an algebraic space, say — the sheaf of rings is visible only once that name is unfolded, so
with `R` left to be inferred the two
`CategoryTheory.GrothendieckTopology.HasSheafCompose` instances are searched for while the
universe of the sections is still a metavariable, and the search stops undecided on a `UnivLE`
constraint instead of reaching the site's own instances.  Writing
`(R := AlgebraicGeometry.Space.structureRingSheaf B S hS Y)` in the application settles the
universe first and the instances are then found.  With that, either spelling of the three terms
of the fork of sheaves of sets is accepted — the `CategoryTheory.Sheaf.moduleSheafFunctor` one
and the `AlgebraicGeometry.Space.smallEtaleDirectImage` one — because at variable modules the
two are equal by `rfl` (`AlgebraicGeometry.Space.moduleSheaf_modulePushforward`); the object
crossing therefore costs the consumer nothing, and only the three arrows need equations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.RingedToposModules

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {E F H : SheafOfModules.{w} R} {ι : E ⟶ F} {φ ψ : F ⟶ H}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The fork condition of a fork of sheaves of modules, read on the underlying sheaves of
sets. -/
lemma moduleSheafFunctor_fork_condition (w : ι ≫ φ = ι ≫ ψ) :
    (Sheaf.moduleSheafFunctor R).map ι ≫ (Sheaf.moduleSheafFunctor R).map φ =
      (Sheaf.moduleSheafFunctor R).map ι ≫ (Sheaf.moduleSheafFunctor R).map ψ := by
  rw [← Functor.map_comp, ← Functor.map_comp, w]

section Fixed

variable (w : ι ≫ φ = ι ≫ ψ)
  (h : IsLimit (Fork.ofι ((Sheaf.moduleSheafFunctor R).map ι)
    (moduleSheafFunctor_fork_condition w)))

omit [J.HasSheafCompose (forget RingCat.{w})] in
include h in
/-- The first arrow of a fork of sheaves of modules whose image fork is a limit becomes a
monomorphism on the underlying sheaves of sets. -/
lemma mono_moduleSheafFunctor_map_of_isLimitFork :
    Mono ((Sheaf.moduleSheafFunctor R).map ι) :=
  Fork.IsLimit.mono h

/-- The lift of a fork of sheaves of modules through a limiting image fork, as a morphism of
the underlying sheaves of sets.  It is shown linear by
`Stacks.Sheaves.RingedToposModules.forkModuleSheafLift_add` and
`Stacks.Sheaves.RingedToposModules.forkModuleSheafLift_smul`. -/
noncomputable def forkModuleSheafLift (s : Fork φ ψ) :
    (Sheaf.moduleSheafFunctor R).obj s.pt ⟶ (Sheaf.moduleSheafFunctor R).obj E :=
  Fork.IsLimit.lift h ((Sheaf.moduleSheafFunctor R).map s.ι)
    (moduleSheafFunctor_fork_condition s.condition)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The lift `forkModuleSheafLift` composed with the image of `ι` is the image of the first
arrow of the given fork. -/
@[simp]
lemma forkModuleSheafLift_comp (s : Fork φ ψ) :
    forkModuleSheafLift w h s ≫ (Sheaf.moduleSheafFunctor R).map ι =
      (Sheaf.moduleSheafFunctor R).map s.ι :=
  Fork.IsLimit.lift_ι' h _ _

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The lift of a fork of sheaves of modules commutes with the addition maps. -/
lemma forkModuleSheafLift_add (s : Fork φ ψ) :
    Sheaf.moduleAddHom R s.pt ≫ forkModuleSheafLift w h s =
      prod.map (forkModuleSheafLift w h s) (forkModuleSheafLift w h s) ≫
        Sheaf.moduleAddHom R E := by
  have := mono_moduleSheafFunctor_map_of_isLimitFork w h
  refine (cancel_mono ((Sheaf.moduleSheafFunctor R).map ι)).mp ?_
  rw [Category.assoc, forkModuleSheafLift_comp, moduleAddHom_comp_moduleSheafFunctor_map,
    Category.assoc, moduleAddHom_comp_moduleSheafFunctor_map, ← Category.assoc, prod.map_map,
    forkModuleSheafLift_comp]

/-- The lift of a fork of sheaves of modules commutes with the scalar-multiplication maps. -/
lemma forkModuleSheafLift_smul (s : Fork φ ψ) :
    Sheaf.moduleSMulHom R s.pt ≫ forkModuleSheafLift w h s =
      prod.map (𝟙 (Sheaf.ringSheaf R)) (forkModuleSheafLift w h s) ≫ Sheaf.moduleSMulHom R E := by
  have := mono_moduleSheafFunctor_map_of_isLimitFork w h
  refine (cancel_mono ((Sheaf.moduleSheafFunctor R).map ι)).mp ?_
  rw [Category.assoc, forkModuleSheafLift_comp, moduleSMulHom_comp_moduleSheafFunctor_map,
    Category.assoc, moduleSMulHom_comp_moduleSheafFunctor_map, ← Category.assoc, prod.map_map,
    Category.comp_id, forkModuleSheafLift_comp]

/-- The lift of a fork of sheaves of modules through a limiting image fork, as a morphism of
sheaves of modules. -/
noncomputable def forkLift (s : Fork φ ψ) : s.pt ⟶ E :=
  homEquivSubtype.symm
    ⟨forkModuleSheafLift w h s, forkModuleSheafLift_add w h s, forkModuleSheafLift_smul w h s⟩

/-- The underlying morphism of sheaves of sets of `forkLift` is `forkModuleSheafLift`. -/
@[simp]
lemma moduleSheafFunctor_map_forkLift (s : Fork φ ψ) :
    (Sheaf.moduleSheafFunctor R).map (forkLift w h s) = forkModuleSheafLift w h s := rfl

/-- **A fork of sheaves of modules whose fork of underlying sheaves of sets is a limit is a
limit.**  Equivalently: the functor `CategoryTheory.Sheaf.moduleSheafFunctor` taking a sheaf of
`R`-modules to its underlying sheaf of sets reflects the limits of forks. -/
noncomputable def isLimitForkOfIsLimitForkModuleSheaf : IsLimit (Fork.ofι ι w) := by
  have := mono_moduleSheafFunctor_map_of_isLimitFork w h
  refine Fork.IsLimit.mk _ (forkLift w h) (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · refine hom_ext_moduleSheafFunctor ?_
    rw [Functor.map_comp, moduleSheafFunctor_map_forkLift, Fork.ι_ofι,
      forkModuleSheafLift_comp]
  · rw [Fork.ι_ofι] at hm
    refine hom_ext_moduleSheafFunctor ((cancel_mono ((Sheaf.moduleSheafFunctor R).map ι)).mp ?_)
    rw [moduleSheafFunctor_map_forkLift, forkModuleSheafLift_comp, ← Functor.map_comp, hm]

end Fixed

/-- **A fork of sheaves of modules whose fork of underlying sheaves of sets is a limit is a
limit**, with the three arrows of the fork of sheaves of sets supplied separately and each
pinned to the image of the corresponding arrow of modules by an equation.  This is the form in
which a consumer holds the limiting fork of sheaves of sets: its arrows are built from direct
images and restrictions, and agree with the images of the arrows of modules by a proved
equation rather than by unfolding. -/
noncomputable def isLimitForkOfIsLimitForkModuleSheafOfEq (w : ι ≫ φ = ι ≫ ψ)
    {ι' : (Sheaf.moduleSheafFunctor R).obj E ⟶ (Sheaf.moduleSheafFunctor R).obj F}
    {φ' ψ' : (Sheaf.moduleSheafFunctor R).obj F ⟶ (Sheaf.moduleSheafFunctor R).obj H}
    (hι : (Sheaf.moduleSheafFunctor R).map ι = ι')
    (hφ : (Sheaf.moduleSheafFunctor R).map φ = φ')
    (hψ : (Sheaf.moduleSheafFunctor R).map ψ = ψ')
    (w' : ι' ≫ φ' = ι' ≫ ψ') (h : IsLimit (Fork.ofι ι' w')) :
    IsLimit (Fork.ofι ι w) := by
  subst hι
  subst hφ
  subst hψ
  exact isLimitForkOfIsLimitForkModuleSheaf w h

/-- **The underlying sheaf of sets reflects the limit of a parallel pair of morphisms of sheaves
of modules.**  This is
`Stacks.Sheaves.RingedToposModules.isLimitForkOfIsLimitForkModuleSheaf` registered as an
instance, stated for an arbitrary cone over the parallel pair rather than for a fork in the
`CategoryTheory.Limits.Fork.ofι` spelling, so that Mathlib's reflection API — in particular
`CategoryTheory.Limits.isLimitOfReflects` and
`CategoryTheory.Limits.isLimitOfIsLimitForkMap` — applies to
`CategoryTheory.Sheaf.moduleSheafFunctor`. -/
instance reflectsLimit_parallelPair_moduleSheafFunctor :
    ReflectsLimit (parallelPair φ ψ) (Sheaf.moduleSheafFunctor R) where
  reflects {c} hc :=
    ⟨(isLimitForkOfIsLimitForkModuleSheaf (Fork.condition c)
      (isLimitMapConeForkEquiv (Sheaf.moduleSheafFunctor R) (Fork.condition c)
        (hc.ofIsoLimit ((Cone.functoriality (parallelPair φ ψ)
          (Sheaf.moduleSheafFunctor R)).mapIso (Fork.isoForkOfι c))))).ofIsoLimit
      (Fork.isoForkOfι c).symm⟩

end Stacks.Sheaves.RingedToposModules

end
