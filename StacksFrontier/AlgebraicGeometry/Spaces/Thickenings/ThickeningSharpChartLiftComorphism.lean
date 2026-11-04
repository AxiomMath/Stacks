module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionExt

/-!
# A solution of the lifting problem is the comorphism of the morphism it glues to

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`, let
`c : X ⟶ W`, let `r : W ⟶ W''`, and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be a solution of the
lifting problem agreeing with the comorphism of `c` read through the thickening on the regular
functions read from `W''`.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartLiftSections.lean` glues
the chartwise morphisms attached to `a` into one morphism `c' : X ⟶ W`, which agrees with `c` on
`Z`.

This file proves the converse identification: **`a` is the comorphism of `c'` read through the
thickening.**  It is the step which turns the glued morphism from something whose chart
morphisms are those of `a` into something whose *comorphism* is `a`, and so the step by which a
solution of the lifting problem of [Stacks Project, Tag 0618] is realized by a morphism of
algebraic spaces.

## The argument

A morphism of sheaves of rings on the small étale site of `W` is determined on the charts
carrying an affine chart diagram over `r`
(`AlgebraicGeometry.Space.ringSheafHom_ext_of_cover`), those being cover-dense.  Over such a
chart `Q` the solution has a morphism of charts
(`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram`), which by
hypothesis is a chart morphism of `c'`; and a section of `(i ≫ c)_*(i^{-1}𝒪_X)` over `Q` is
determined by its readings at the indices built from an index of `X` above `X ×_W Q` and an index
of `Z` above `Z ×_X P`
(`AlgebraicGeometry.Space.directImageChartProjection_comp_ext`), at which the two readings agree
by `AlgebraicGeometry.Space.directImageChartProjection_comp_eq_of_thickeningLiftChartSiteHom`.

Those indices are *constructed* from their two halves; no index of the composite is factored, and
none has to be.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjection_comp_ext`: two sections of `(f ≫ g)_*O`
  over a chart agree as soon as their readings at every index built from an index for `g` and an
  index for `f` agree.
* `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom`:
  **a solution of the lifting problem whose chart morphisms are chart morphisms of `c'` is the
  comorphism of `c'`** read in the common target of the morphisms agreeing on the thickening.
* `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_eq_of_eq_thickeningLiftOfIndex`: the
  same identification carried from the tautological index `i ≫ c` to a morphism `e` out of the
  thickening with `i ≫ c = e`, which is the spelling a solution of the lifting problem arrives
  in.

## Implementation notes

The affineness of a chart is an instance argument, as everywhere in these files: a `letI` for
affineness under a binder is, in this development, a deterministic heartbeat timeout.

**No `@[stacks]` attribute is placed.**  What is proved is a comparison internal to this
development of two readings of [Stacks Project, Tag 03G8].

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), iterated
  direct images.
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED), the small étale site.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the correspondence
  between lifts and linear maps.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this
  identification is an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Extensionality of the sections of an iterated direct image -/

section Comp

variable {X Y T : AlgebraicSpaces B S hS}

/-- **Two sections of `(f ≫ g)_*O` over an étale chart of `T` agree as soon as their readings at
the composite indices agree.**

The comparison of iterated direct images is invertible, so the section is determined by its
transport to `g_*(f_*O)`, which is determined by its chart projections along `g` and then along
`f` (`AlgebraicGeometry.Space.directImageChartProjection_ext`, twice); and
`AlgebraicGeometry.Space.directImageChartProjection_pushforwardRingSheafCompInv` identifies that
two-step reading with the reading at the index built from the two indices.

So the readings at the *constructed* indices suffice: no index of the composite has to be
factored through a chart of `Y`. -/
theorem directImageChartProjection_comp_ext (f : X ⟶ Y) (g : Y ⟶ T)
    (V : SmallEtale B S hS T.1)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u})
    {z z' : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS T.1)
      (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward O).obj.obj (op V))}
    (hzz : ∀ (j : StructuredArrow (op (chartBaseChange B S hS g V))
          (comparisonFunctor B S hS Y).op)
        (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
          (comparisonFunctor B S hS X).op),
      (directImageChartProjection B S hS (f ≫ g) V
            (StructuredArrow.mk ((chartBaseChangeComp B S hS f g V j).op ≫ k.hom))).app
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj O) z =
        (directImageChartProjection B S hS (f ≫ g) V
            (StructuredArrow.mk ((chartBaseChangeComp B S hS f g V j).op ≫ k.hom))).app
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj O) z') :
    z = z' := by
  have hcancel : ∀ y : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS T.1)
      (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward O).obj.obj (op V)),
      (pushforwardRingSheafCompHom B S hS f g O).hom.app (op V)
          ((pushforwardRingSheafCompInv B S hS f g O).hom.app (op V) y) = y :=
    fun y ↦ (ringSheafHom_comp_app_apply (pushforwardRingSheafCompInv B S hS f g O)
          (pushforwardRingSheafCompHom B S hS f g O) (op V) y).symm.trans
      (ringSheafHom_congr_app_apply
        (pushforwardRingSheafCompInv_comp_hom B S hS f g O) (op V) y)
  refine Function.LeftInverse.injective hcancel ?_
  refine directImageChartProjection_ext B S hS g V
    ((smallEtaleDirectImage B S hS f).obj
      ((sheafCompose (SmallEtale.topology B S hS X.1)
        (CategoryTheory.forget RingCat.{u})).obj O)) fun j ↦ ?_
  refine directImageChartProjection_ext B S hS f j.right.unop
    ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget RingCat.{u})).obj O) fun k ↦ ?_
  exact (directImageChartProjection_pushforwardRingSheafCompInv B S hS f g V j k O z).trans
    ((hzz j k).trans
      (directImageChartProjection_pushforwardRingSheafCompInv B S hS f g V j k O z').symm)

end Comp

/-! ### The solution is the comorphism of the glued morphism -/

section Identify

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The chart reading of a solution of the lifting problem is the chart reading of the
comorphism of `c'`**, over an affine étale chart `Q` of `W` carrying an affine chart diagram over
`r` and at a regular function on `Q`.

Here `c'` is a morphism agreeing with `c` on the thickening — in practice the morphism the
chartwise morphisms of `a` glue to, by
`AlgebraicGeometry.Space.exists_hom_eq_thickeningLiftChartSiteHom` — and the hypothesis `hchart`
is that the morphism of charts `a` attaches over `Q` is a chart morphism of `c'`, which is
exactly the conclusion of that gluing.

A section of `(i ≫ c)_*(i^{-1}𝒪_X)` over `Q` is determined by its readings at the indices built
from an index of `X` above `X ×_W Q` and an index of `Z` above `Z ×_X P`
(`AlgebraicGeometry.Space.directImageChartProjection_comp_ext`), and there the two readings agree
by `AlgebraicGeometry.Space.directImageChartProjection_comp_eq_of_thickeningLiftChartSiteHom`.

The affineness of `Q` and of the chart of `W''` below it are positional arguments, and the chart
diagram over `r` is spelled out rather than passed as
`AlgebraicGeometry.Space.HasAffineChartDiagram`: a consumer destructures that property once and
supplies this lemma one chart at a time. -/
theorem app_structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom
    (hZ : IsThickening B S hS X Z.1) (c c' : X ⟶ W)
    (hcc : subspaceInclusion B S hS X Z ≫ c' = subspaceInclusion B S hS X Z ≫ c)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    {W'' : AlgebraicSpaces B S hS} (r : W ⟶ W'')
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (Q : SmallEtale B S hS W.1)
    (hQaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj Q)))
    (V' : SmallEtale B S hS W''.1)
    (qq : (SmallEtale.toOver B S hS W.1).obj Q ⟶ (SmallEtale.toOver B S hS W''.1).obj V')
    (hqq : yoneda.map qq ≫ V'.1.hom = Q.1.hom ≫ r.hom)
    (hV'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W''.1).obj V')))
    (hchart : ∀ (j : StructuredArrow (op (chartBaseChange B S hS c Q))
          (comparisonFunctor B S hS X).op)
        (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
          (SmallEtale.toOver B S hS W.1).obj Q),
      (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a Q j →
      j.right.unop.1.hom ≫ c'.hom = yoneda.map ψ ≫ Q.1.hom)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op Q))) :
    (structureSharpThroughThickeningAt B S hS Z c'
        (subspaceInclusion B S hS X Z ≫ c) hcc).hom.app (op Q) b = a.hom.app (op Q) b := by
  have hex : ∀ j : StructuredArrow (op (chartBaseChange B S hS c Q))
      (comparisonFunctor B S hS X).op,
      ∃ ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
          (SmallEtale.toOver B S hS W.1).obj Q,
        (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a Q j :=
    fun j ↦ exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram B S hS Z hZ c a
      r hbase Q V' qq hqq.symm hV'aff j
  exact directImageChartProjection_comp_ext B S hS (subspaceInclusion B S hS X Z) c Q
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
    fun j k ↦ Exists.elim (hex j) fun ψ hψ ↦
      directImageChartProjection_comp_eq_of_thickeningLiftChartSiteHom B S hS Z hZ c c' hcc
        a hred Q j ψ hψ (hchart j ψ hψ) k b

/-- **A solution of the lifting problem whose chart morphisms are chart morphisms of `c'` is the
comorphism of `c'` read through the thickening.**

The charts of `W` carrying an affine chart diagram over `r` are cover-dense, so a morphism of
sheaves of rings is determined on them
(`AlgebraicGeometry.Space.ringSheafHom_ext_of_cover`), and over such a chart the two readings
agree by
`AlgebraicGeometry.Space.app_structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom`. -/
theorem structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom
    (hZ : IsThickening B S hS X Z.1) (c c' : X ⟶ W)
    (hcc : subspaceInclusion B S hS X Z ≫ c' = subspaceInclusion B S hS X Z ≫ c)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    {W'' : AlgebraicSpaces B S hS} (r : W ⟶ W'')
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (hchart : ∀ (Q : SmallEtale B S hS W.1)
        (_hQaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS W.1).obj Q)))
        (j : StructuredArrow (op (chartBaseChange B S hS c Q))
          (comparisonFunctor B S hS X).op)
        (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
          (SmallEtale.toOver B S hS W.1).obj Q),
      (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a Q j →
      j.right.unop.1.hom ≫ c'.hom = yoneda.map ψ ≫ Q.1.hom) :
    structureSharpThroughThickeningAt B S hS Z c'
      (subspaceInclusion B S hS X Z ≫ c) hcc = a := by
  refine ringSheafHom_ext_of_cover B S hS (X := W) (HasAffineChartDiagram B S hS r)
    (fun V R hR ↦ mem_topology_of_hasAffineChartDiagram B S hS r V R hR) _ _ ?_
  intro Q hQ b
  obtain ⟨V', qq, hqq, hV'aff⟩ := hQ.2
  exact app_structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom B S hS Z hZ c c' hcc
    a hred r hbase Q hQ.1 V' qq hqq hV'aff (hchart Q hQ.1) b

/-- **The identification carried to the index a solution of the lifting problem arrives in.**

A solution read at a morphism `e` out of the thickening with `i ≫ c = e` is identified with the
comorphism of `c'` read at that same `e`, as soon as its transport to the tautological index is
identified with the comorphism of `c'` read there.  The transport
`AlgebraicGeometry.Space.thickeningLiftOfIndex` is composition with an isomorphism of sheaves
which the equation makes an identity, so the two statements are one. -/
theorem structureSharpThroughThickeningAt_eq_of_eq_thickeningLiftOfIndex (c c' : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e)
    (A : structureRingSheaf B S hS W ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (key : structureSharpThroughThickeningAt B S hS Z c'
        (subspaceInclusion B S hS X Z ≫ c) (h'.trans h.symm) =
      thickeningLiftOfIndex B S hS Z c e h A) :
    structureSharpThroughThickeningAt B S hS Z c' e h' = A := by
  subst h
  simpa only [thickeningLiftOfIndex, eqToHom_refl, Category.comp_id] using key

end Identify

end AlgebraicGeometry.Space

end
