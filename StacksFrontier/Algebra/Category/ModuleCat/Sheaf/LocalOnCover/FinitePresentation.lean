module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentation of a sheaf of modules is local on a covering family

Stacks 03DN asserts that each of the local conditions of Stacks 03DL may be tested on the
members of any family covering the final object.  This file proves the clause for finite
presentation: a sheaf of modules on a site is of finite presentation exactly when its
restrictions to the members of some covering family are, and exactly when those restrictions
admit finite global presentations.

Both equivalences come down to moving a presentation between a slice site and an iterated
slice site.  In one direction a finite global presentation of `M` over `U` is transported
along the equivalence `Over.equivalenceOfIsTerminal` identifying the site with its slice over
a terminal object, which turns it into a quasi-coherence datum on a one-member covering
family and so into finite presentation of the restriction.  In the other direction the
presentations supplied on the iterated slices `(M.over (U i)).over V` are transported down to
the base objects `V.left` along `Over.iteratedSliceEquiv`, and the resulting family is a
quasi-coherence datum for `M` because a covering family of covering families covers.

## Main results

* `Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation`: finite
  presentation is equivalent to finite presentation of the restrictions to the members of
  some covering family.  This is the equivalence of conditions (a) and (b) of Stacks 03DN for
  finite presentation.
* `Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations`: finite
  presentation is equivalent to the existence of finite global presentations of those
  restrictions.  This is the equivalence of conditions (a) and (c).

## Implementation notes

The statements are made for a sheaf of rings on an arbitrary site rather than for the
structure sheaf of a bundled ringed site, which is the more general form and does not require
the site to have a final object: `GrothendieckTopology.CoversTop` expresses that a family
covers the final object without choosing one.

Mathlib's `SheafOfModules.IsFinitePresentation` is Stacks 03DL(7), so no new predicate is
introduced here; `SheafOfModules.QuasicoherentData` is the datum of a covering family together
with a presentation on each member, and `SheafOfModules.Presentation.IsFinite` is finiteness of
its generators and relations.

Transporting a presentation needs left exactness of sheafification on the sites involved,
which `AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective` supplies from the
`WEqualsLocallyBijective` hypotheses already present.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.SheafOfModules

universe u v w

/-- A finite global presentation of a sheaf of modules on a site with a terminal object makes
it of finite presentation: the terminal object is a one-member covering family, and the
presentation is transported to its slice along `Over.equivalenceOfIsTerminal`. -/
private theorem isFinitePresentation_of_isFinite_presentation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}}
    [CategoryTheory.Limits.HasTerminal C]
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ (U : C), HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ (U : C), (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (N : SheafOfModules.{w} R) (P : N.Presentation) (hP : P.IsFinite) :
    N.IsFinitePresentation := by
  let U : C := CategoryTheory.Limits.terminal C
  have hU : CategoryTheory.Limits.IsTerminal U := CategoryTheory.Limits.terminalIsTerminal
  let : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : HasSheafify (J.over U) AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let eCat := Over.equivalenceOfIsTerminal hU
  let : eCat.inverse.IsCocontinuous J (J.over U) := by
    constructor
    intro X S hS
    rw [GrothendieckTopology.mem_over_iff] at hS
    have hEq : S.functorPullback eCat.inverse = Sieve.overEquiv (eCat.inverse.obj X) S := by
      ext Y f
      let f' : Y ⟶ (eCat.inverse.obj X).left := (eCat.inverse.map f).left
      change S (eCat.inverse.map f) ↔ (Sieve.overEquiv (eCat.inverse.obj X) S) f'
      rw [Sieve.overEquiv_iff]
      let a : Over.mk (f' ≫ (eCat.inverse.obj X).hom) ≅ eCat.inverse.obj Y :=
        Over.isoMk (Iso.refl Y) (hU.hom_ext _ _)
      have hcomp : a.hom ≫ eCat.inverse.map f =
          (Over.homMk f' : Over.mk (f' ≫ (eCat.inverse.obj X).hom) ⟶ eCat.inverse.obj X) := by
        ext
        change a.hom.left ≫ (eCat.inverse.map f).left = f'
        rw [show a.hom.left = 𝟙 Y from rfl]
        exact Category.id_comp _
      constructor
      · intro hf
        rw [← hcomp]
        exact S.downward_closed hf a.hom
      · intro hf
        rw [(Iso.eq_inv_comp a).2 hcomp]
        exact S.downward_closed hf a.inv
    rw [hEq]
    exact hS
  let : eCat.functor.IsContinuous (J.over U) J :=
    inferInstanceAs ((Over.forget U).IsContinuous (J.over U) J)
  let : eCat.functor.IsCocontinuous (J.over U) J :=
    inferInstanceAs ((Over.forget U).IsCocontinuous (J.over U) J)
  have : eCat.functor.IsLeftAdjoint := eCat.isLeftAdjoint_functor
  have : eCat.inverse.IsLeftAdjoint := eCat.symm.isLeftAdjoint_functor
  let : eCat.inverse.IsContinuous J (J.over U) :=
    eCat.toAdjunction.isContinuous_of_isCocontinuous (J.over U) J
  let e := SheafOfModules.pushforwardPushforwardEquivalence eCat
    (S := R.over U) (R := R) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  have : CategoryTheory.Limits.PreservesColimitsOfSize.{w, w} e.functor :=
    CategoryTheory.Adjunction.isEquivalence_preservesColimits e.functor
  let P' : (e.functor.obj N).Presentation := P.map e.functor (.refl _)
  have hP' : P'.IsFinite := by
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · exact inferInstanceAs (Finite P.generators.I)
    · exact inferInstanceAs (Finite P.relations.I)
  let iso : e.functor.obj N ≅ N.over U := Iso.refl _
  let q : N.QuasicoherentData.{u} :=
    { I := ULift.{u} Unit
      X := fun _ => U
      coversTop := fun X => by
        apply (GrothendieckTopology.coversTop_iff_of_isTerminal J U hU
          (fun _ : ULift.{u} Unit => U)).2
        have htop : Sieve.ofObjects (fun _ : ULift.{u} Unit => U) U = ⊤ := by
          apply le_antisymm le_top
          intro Y f _
          rw [Sieve.mem_ofObjects_iff]
          exact ⟨ULift.up (), ⟨hU.from Y⟩⟩
        rw [htop]
        exact J.top_mem U
      presentation _ := P'.ofIsIso iso.hom }
  refine ⟨q, ⟨fun i => ?_⟩⟩
  let : P'.IsFinite := hP'
  exact inferInstanceAs ((P'.ofIsIso iso.hom).IsFinite)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)
  [∀ (U : C), HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ (U : C), (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03DN, finite presentation.** A sheaf of modules is of finite presentation if and
only if its restrictions to the members of some covering family of the final object are of
finite presentation. -/
@[stacks 03DN "finite_presentation"]
theorem isFinitePresentation_iff_exists_cover_isFinitePresentation
    [∀ (U : C), ∀ (V : Over U),
      HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
    [∀ (U : C), ∀ (V : Over U),
      ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    M.IsFinitePresentation ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, (M.over (U i)).IsFinitePresentation := by
  constructor
  · intro hM
    let : M.IsFinitePresentation := hM
    obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
    refine ⟨q.I, q.X, q.coversTop, fun i => ?_⟩
    exact isFinitePresentation_of_isFinite_presentation (M.over (q.X i))
      (q.presentation i) (hq.isFinite_presentation i)
  · rintro ⟨I, U, hU, hM⟩
    let (V : C) : HasSheafify (J.over V) AddCommGrpCat.{w} :=
      AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    let (V : C) (W : Over V) : HasSheafify ((J.over V).over W) AddCommGrpCat.{w} :=
      AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    let D (i : I) :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData (M.over (U i))).choose
    have hD (i : I) : (D i).IsFinitePresentation :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData (M.over (U i))).choose_spec
    let q : M.QuasicoherentData :=
      { I := Σ i, (D i).I
        X ij := ((D ij.1).X ij.2).left
        coversTop := hU.over (fun i => (D i).coversTop)
        presentation ij := by
          letI e := SheafOfModules.pushforwardPushforwardEquivalence
            (Over.iteratedSliceEquiv ((D ij.1).X ij.2))
            (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
            (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
          exact (((D ij.1).presentation ij.2).map e.inverse (.refl _)).ofIsIso
            (e.fullyFaithfulFunctor.preimageIso
              (by exact e.counitIso.app ((M.over (U ij.1)).over ((D ij.1).X ij.2)))).hom }
    have hq : q.IsFinitePresentation := by
      refine ⟨fun i => ⟨⟨?_⟩, ⟨?_⟩⟩⟩
      · exact inferInstanceAs (Finite ((D i.1).presentation i.2).generators.I)
      · exact inferInstanceAs (Finite ((D i.1).presentation i.2).relations.I)
    exact ⟨q.shrink, ⟨fun i => hq.isFinite_presentation i.2.choose⟩⟩

/-- **Stacks 03DN, finite presentation.** A sheaf of modules is of finite presentation if and
only if its restrictions to the members of some covering family of the final object have
finite global presentations. -/
@[stacks 03DN "finite_presentation"]
theorem isFinitePresentation_iff_exists_cover_finite_presentations :
    M.IsFinitePresentation ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, ∃ (p : (M.over (U i)).Presentation), p.IsFinite := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.I, q.X, q.coversTop, fun i => ⟨q.presentation i, hq.isFinite_presentation i⟩⟩
  · rintro ⟨I, U, hU, hP⟩
    exact ⟨⟨I, U, hU, fun i => (hP i).choose⟩, ⟨fun i => (hP i).choose_spec⟩⟩

end Stacks.SheafOfModules

end
