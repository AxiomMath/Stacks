module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStrata
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Factoring through a closed subspace, read on a diagram of affine étale charts

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `Z ⊆ Y` be a closed subspace with defining ideal `𝓘_Z ⊆ 𝒪_Y`.  Stacks 03MB
says that `f` factors through `Z` exactly when `f^{-1}𝓘_Z · 𝒪_X = 0`.  The forms of that
criterion already in this tree —
`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_ker_le` and
`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_isAffine_definingIdealAt_le` — read the
vanishing at an *arbitrary* object of the site mapping to a chart of `Y`.  This file reads it
instead on a commuting square of affine étale charts over `f`
(`AlgebraicGeometry.Space.ChartDiagram`), where it becomes the statement that the defining
ideal of `Z` at the chart of `Y` is killed by pullback of regular functions to the chart of
`X`: that is, that the ideal *generated* by the inverse image of `𝓘_Z` vanishes chart by
chart, which is the shape in which inverse-image ideal sheaves are constructed here.

## Main results

* `AlgebraicGeometry.Space.topClosedSubspace`: the whole space, as a closed subspace of itself,
  by `AlgebraicGeometry.Space.isClosedSubspace_top_subfunctor` of
  `StacksFrontier/AlgebraicGeometry/Spaces/FittingRankStrata.lean`.
* `AlgebraicGeometry.Space.definingIdealAt_topClosedSubspace`: the defining ideal of the whole
  space vanishes on every affine étale chart.
* `AlgebraicGeometry.Space.eq_zero_of_sieve_definingIdealAt`: a section of the structure sheaf
  over an affine étale chart which vanishes along a covering sieve of that chart is zero.
* `AlgebraicGeometry.Space.definingIdealAt_eq_bot_iff_le_ker_of_chartDiagram`: over one diagram
  of affine étale charts, the defining ideal of the inverse image of `Z` vanishes on the chart
  of `X` exactly when the defining ideal of `Z` at the chart of `Y` is killed by pullback of
  regular functions along the diagram.
* `AlgebraicGeometry.Space.exists_comp_eq_iff_forall_chartDiagram_definingIdealAt_le` is
  **Stacks 03MB** with the vanishing condition read on the diagrams of affine étale charts
  over `f`.

## Implementation notes

No `@[stacks 03MB]` attribute is added.  The part string `factor_iff_ideal_vanishes` of Tag
03MB is already carried by `AlgebraicGeometry.Space.exists_comp_eq_iff_forall_ker_le` in
`StacksFrontier/AlgebraicGeometry/Spaces/FactorThroughClosedSubspace.lean`, and what is proved
here is that same part with an equivalent right-hand side, exactly as in the sibling file
`StacksFrontier/AlgebraicGeometry/Spaces/FactorThroughClosedSubspaceAffine.lean`; tagging it
again would count one part of the tag twice.

The two sides of the criterion are read through the *same point of* `Y`.  A diagram of charts
over `f` carries the tautological point of its chart `U` of `X` to the point of `Y` given by
the vertical morphism `g : U ⟶ V` of the diagram, because the diagram commutes.  Membership of
that point in `Z` is, by `AlgebraicGeometry.Space.mem_obj_iff_definingIdealAt_le` applied on
the affine chart `V` of `Y`, the inclusion of `𝓘_Z(V)` into the kernel of pullback along `g`;
and it is, by the same lemma applied on the affine chart `U` of `X` to the inverse-image closed
subspace, the vanishing of the defining ideal of that inverse image at `U`.  So the two sides
are two readings of one membership, and neither the base change of an ideal sheaf nor a
fibre-product computation of `Z ×_Y U` is needed.

Passing from the charts of the diagrams, which are only cofinal, to *all* affine charts of `X`
uses no covering of an object of the big site: a section of the defining ideal of the inverse
image over an affine chart restricts into that ideal over the charts of a covering sieve by
`AlgebraicGeometry.Space.definingIdealAt_map`, where it vanishes, and a section of the
structure sheaf vanishing along a covering sieve of the small étale site is zero.  That last
step is `AlgebraicGeometry.Space.mem_definingIdealAt_of_sieve` applied to the whole space as a
closed subspace, whose defining ideal is zero.  The conclusion is then
`AlgebraicGeometry.Space.le_of_forall_definingIdealAt_le`, which already contains the covering
argument on the big site.

The inverse-image closed subspace is not constructed here: it is
`AlgebraicGeometry.Space.preimageClosedSubspace` of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupFlatBaseChange.lean`, which this file may not
import, so the statements below take the closed subspace together with the hypothesis that its
underlying subfunctor is the inverse image.  That is also the weaker and more usable form: any
closed subspace with that underlying subfunctor will do, and closedness is a proposition.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The whole space as a closed subspace -/

/-- The whole of an algebraic space, as a closed subspace of itself. -/
def topClosedSubspace (X : AlgebraicSpaces B S hS) : ClosedSubspaces B S hS X.1 :=
  ⟨⊤, isClosedSubspace_top_subfunctor B S hS X.2⟩

/-- The underlying subfunctor of `topClosedSubspace X` is the top subfunctor. -/
@[simp]
theorem topClosedSubspace_coe (X : AlgebraicSpaces B S hS) :
    (topClosedSubspace B S hS X).1 = ⊤ := rfl

/-! ### The defining ideal of the whole space -/

/-- If the tautological point of an affine chart lies in a closed subspace, the defining ideal of
that subspace vanishes at the chart. -/
private theorem definingIdealAt_eq_bot_of_mem (X : AlgebraicSpaces B S hS)
    (P : ClosedSubspaces B S hS X.1) (U : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)]
    (h : U.1.hom.app (op U.1.left) (𝟙 U.1.left) ∈ P.1.obj (op U.1.left)) :
    definingIdealAt B S hS X P (op U) = ⊥ := by
  have h := (mem_obj_iff_definingIdealAt_le B S hS X P U (k := 𝟙 U.1.left)).1 h
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id,
    (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id] at h
  exact le_bot_iff.1 h

/-- **The defining ideal of the whole space vanishes.** On an affine étale scheme chart of `X`
the defining ideal of `X` itself, seen as a closed subspace of `X`, is the zero ideal: the
tautological point of the chart lies in it, so that ideal is killed by pullback of regular
functions along the identity. -/
theorem definingIdealAt_topClosedSubspace (X : AlgebraicSpaces B S hS)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    definingIdealAt B S hS X (topClosedSubspace B S hS X) (op U) = ⊥ := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  exact definingIdealAt_eq_bot_of_mem B S hS X _ U trivial

/-- **A section vanishing along a covering sieve is zero.** A section of the structure sheaf
over an affine étale chart of `X` whose restriction along every arrow of a covering sieve of
that chart vanishes is itself zero: it lies in the defining ideal of `X` as a closed subspace
of itself, which is the zero ideal. -/
theorem eq_zero_of_sieve_definingIdealAt (X : AlgebraicSpaces B S hS)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (s : ToType ((structureRingSheaf B S hS X).obj.obj (op U)))
    (T : Sieve U) (hT : T ∈ SmallEtale.topology B S hS X.1 U)
    (h : ∀ (W : SmallEtale B S hS X.1) (m : W ⟶ U), T m →
      ((structureRingSheaf B S hS X).obj.map m.op).hom s = 0) :
    s = 0 := by
  have hmem : s ∈ definingIdealAt B S hS X (topClosedSubspace B S hS X) (op U) :=
    mem_definingIdealAt_of_sieve B S hS X (topClosedSubspace B S hS X) (op U) s T hT
      fun W m hm ↦ by rw [h W m hm]; exact Submodule.zero_mem _
  rwa [definingIdealAt_topClosedSubspace B S hS X U hU, Submodule.mem_bot] at hmem

/-! ### The criterion on one diagram of affine étale charts -/

/-- **The two readings of one point of `Y`.**  Over a diagram of affine étale charts over
`f : X ⟶ Y`, the defining ideal of the inverse image of `Z` vanishes at the chart of `X`
exactly when the defining ideal of `Z` at the chart of `Y` is killed by pullback of regular
functions along the vertical morphism of the diagram.

Both sides say that the point of `Y` carried by the tautological point of the chart of `X` lies
in `Z`; the left-hand side reads it on the chart of `X` through the inverse image, the
right-hand side on the chart of `Y` through `Z`. -/
theorem definingIdealAt_eq_bot_iff_le_ker_of_chartDiagram {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (Z : ClosedSubspaces B S hS Y.1) (P : ClosedSubspaces B S hS X.1)
    (hP : P.1 = Z.1.preimage f.hom) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hdU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hdV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    definingIdealAt B S hS X P (op d.U) = ⊥ ↔
      definingIdealAt B S hS Y Z (op d.V) ≤
        RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left) := hdU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left) := hdV
  set A : BigFppfOver B S hS := (SmallEtale.toOver B S hS X.1).obj d.U
  have hY := mem_obj_iff_definingIdealAt_le B S hS Y Z d.V (k := d.g)
  have hPiff : ∀ x : X.1.obj (op A),
      x ∈ P.1.obj (op A) ↔ f.hom.app (op A) x ∈ Z.1.obj (op A) := by
    intro x
    rw [hP]
    exact Iff.rfl
  have hpt : f.hom.app (op A) (d.U.1.hom.app (op A) (𝟙 A)) = d.V.1.hom.app (op A) d.g := by
    simpa using congrArg (fun k ↦ k (𝟙 A)) (congr_app d.comm (op A))
  constructor
  · intro hbot
    refine hY.1 ?_
    rw [← hpt]
    exact (hPiff _).1
      ((mem_obj_iff_definingIdealAt_le B S hS X P d.U (k := 𝟙 A)).2 (hbot.le.trans bot_le))
  · intro hle
    refine definingIdealAt_eq_bot_of_mem B S hS X P d.U ((hPiff _).2 ?_)
    change f.hom.app (op A) (d.U.1.hom.app (op A) (𝟙 A)) ∈ _
    rw [hpt]
    exact hY.2 hle

/-- A morphism of algebraic spaces whose range lies in a closed subspace factors through it. -/
private theorem exists_comp_eq_of_range_le {X Y : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS Y.1) (f : X ⟶ Y) (h : Subfunctor.range f.hom ≤ Z.1) :
    ∃ g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
      g ≫ ObjectProperty.homMk Z.1.ι = f :=
  ⟨ObjectProperty.homMk (Subfunctor.lift f.hom h),
    ObjectProperty.hom_ext _ (Subfunctor.lift_ι f.hom h)⟩

/-! ### Stacks 03MB on the diagrams of affine étale charts -/

/-- **Stacks 03MB, with the vanishing condition read on the diagrams of affine étale charts
over `f`.**  A morphism `f : X ⟶ Y` of algebraic spaces over `S` factors through a closed
subspace `Z ⊆ Y` exactly when, for every commuting square of étale scheme charts over `f` whose
two charts are affine, the defining ideal of `Z` at the chart of `Y` is killed by pullback of
regular functions along the vertical morphism of the square.

Equivalently: the ideal generated by the inverse image of the defining ideal sheaf of `Z`
vanishes over the chart of `X` of every such square, which is how inverse-image ideal sheaves
are constructed in this development.

The condition is read on a smaller family of test objects than the one of
`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_isAffine_definingIdealAt_le` — only the
affine étale charts of `X` which map to a single affine étale chart of `Y` — and the two are
therefore equivalent, both being equivalent to factorization.  Those charts of `X` are cofinal
by Stacks 03G2, `AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology`. -/
theorem exists_comp_eq_iff_forall_chartDiagram_definingIdealAt_le
    {X Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS Y.1) (f : X ⟶ Y) :
    (∃ g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
        g ≫ ObjectProperty.homMk Z.1.ι = f) ↔
      ∀ d : ChartDiagram B S hS X.1 Y.1 f.hom,
        IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
          definingIdealAt B S hS Y Z (op d.V) ≤
            RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom := by
  constructor
  · rintro ⟨g, hg⟩ d - -
    exact definingIdealAt_le_ker_of_comp_eq B S hS Y X Z f g hg d.V d.g d.U.1.hom d.comm.symm
  · intro hker
    set P : ClosedSubspaces B S hS X.1 :=
      ⟨Z.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom Z.1 Y.2 X.2 Z.2⟩
    have hP : P.1 = Z.1.preimage f.hom := rfl
    -- the inverse image of `Z` has vanishing defining ideal on every affine chart of `X`
    have hbot : ∀ U : SmallEtale B S hS X.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
        definingIdealAt B S hS X P (op U) = ⊥ := by
      intro U hUaff
      refine le_antisymm (fun s hs ↦ (Submodule.mem_bot _).2 ?_) bot_le
      refine eq_zero_of_sieve_definingIdealAt B S hS X U hUaff s _
        (generate_affineChartDiagram_mem_topology B S hS f (fun _ ↦ True)
          (fun _ _ ↦ trivial) U) ?_
      rintro W m ⟨W', m', a, ⟨hW'aff, d, hdU, hdVaff, -⟩, rfl⟩
      subst hdU
      have hres : ((structureRingSheaf B S hS X).obj.map a.op).hom s = 0 := by
        have hmem := definingIdealAt_map B S hS X P a.op s hs
        rwa [(definingIdealAt_eq_bot_iff_le_ker_of_chartDiagram B S hS f Z P hP d hW'aff
          hdVaff).2 (hker d hW'aff hdVaff), Submodule.mem_bot] at hmem
      rw [op_comp, Functor.map_comp]
      show ((structureRingSheaf B S hS X).obj.map m'.op).hom
        (((structureRingSheaf B S hS X).obj.map a.op).hom s) = 0
      rw [hres, map_zero]
    -- hence the inverse image is the whole of `X`, that is, `f` lands in `Z`
    have htop : (topClosedSubspace B S hS X).1 ≤ P.1 :=
      le_of_forall_definingIdealAt_le B S hS X (topClosedSubspace B S hS X) P
        fun U hUaff ↦ (hbot U hUaff).le.trans bot_le
    have hPtop : P.1 = ⊤ := top_le_iff.1 (by simpa using htop)
    have hrange : Subfunctor.range f.hom ≤ Z.1 :=
      (Subfunctor.preimage_eq_top_iff Z.1 f.hom).1 (hP.symm.trans hPtop)
    exact exists_comp_eq_of_range_le B S hS Z f hrange

/-! ### Factoring through a subfunctor, as an inclusion of ranges -/

/-- A morphism factors through a subfunctor, necessarily uniquely, exactly when its range is
contained in that subfunctor. -/
theorem existsUnique_lift_iff_range_le {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Subfunctor F) (f : G ⟶ F) :
    (∃! g : G ⟶ W.toFunctor, g ≫ W.ι = f) ↔ Subfunctor.range f ≤ W := by
  constructor
  · rintro ⟨g, hg, -⟩ T x ⟨x₀, rfl⟩
    rw [← hg]
    exact (g.app T x₀).2
  · intro h
    exact ⟨Subfunctor.lift f h, Subfunctor.lift_ι f h,
      fun y hy ↦ (cancel_mono W.ι).1 (hy.trans (Subfunctor.lift_ι f h).symm)⟩

/-- A morphism of algebraic spaces factors through a closed subspace exactly when its range is
contained in that closed subspace. -/
theorem exists_comp_eq_iff_range_le {X Y : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS Y.1) (f : X ⟶ Y) :
    (∃ g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
        g ≫ ObjectProperty.homMk Z.1.ι = f) ↔ Subfunctor.range f.hom ≤ Z.1 := by
  constructor
  · rintro ⟨g, hg⟩
    have hgι : g.hom ≫ Z.1.ι = f.hom := congrArg InducedCategory.Hom.hom hg
    rintro T x ⟨x₀, rfl⟩
    rw [← hgι]
    exact (g.hom.app T x₀).2
  · exact exists_comp_eq_of_range_le B S hS Z f

/-- **Stacks 03MB in terms of ranges.**  The range of `f` lies in the closed subspace `Z`
exactly when the defining ideal of `Z` is killed by pullback of regular functions along every
diagram of affine étale charts over `f`. -/
theorem range_le_iff_forall_chartDiagram_definingIdealAt_le
    {X Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS Y.1) (f : X ⟶ Y) :
    Subfunctor.range f.hom ≤ Z.1 ↔
      ∀ d : ChartDiagram B S hS X.1 Y.1 f.hom,
        IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
          definingIdealAt B S hS Y Z (op d.V) ≤
            RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom :=
  (exists_comp_eq_iff_range_le B S hS Z f).symm.trans
    (exists_comp_eq_iff_forall_chartDiagram_definingIdealAt_le B S hS Z f)

end AlgebraicGeometry.Space

end
