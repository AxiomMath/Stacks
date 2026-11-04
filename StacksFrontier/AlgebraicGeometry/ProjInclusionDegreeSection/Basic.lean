module

public import StacksFrontier.AlgebraicGeometry.ProjInclusionDegreeSection.Unit
public import StacksFrontier.AlgebraicGeometry.ProjInclusionTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection

/-!
# Tag 01NO's twist comparison on the homogeneous global sections

For an inclusion `U ⊆ V` of affine opens of the base of a graded algebra of sections, Tag 01NO's
comparison map on the `n`-th twist is a composite of six factors: a congruence, two
pseudofunctoriality isomorphisms of the inverse image, the functor image of Tag 01MY's twist map,
another congruence and the identification of the pullback along the identity
(`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap`). Tag 01MY, part (1) says
what the *third* factor does to the global section of `𝒪(k)` attached to a homogeneous element,
and says nothing about the other five. This file computes all six, and so computes the composite.

That is the hypothesis a rigidity argument for the twists needs:
`Stacks.AlgebraicGeometry.TwistRigidity.eq_id` forces a multiplicative endomorphism of the twists
that fixes the homogeneous global sections to be the identity, and the "fixes the homogeneous
global sections" half is the statement proved here. See the note on what this does **not** give.

## Main results

* `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.factor₃_degreeSection`: the third factor,
  which is Tag 01MY part (1) under the inverse image of the leading morphism.
* `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.head_degreeSection`: the first three
  factors.
* `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.tail_degreeSection`: the last three
  factors.
* `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.composite_degreeSection`: **the whole
  composite.** It carries the pulled-back global section of `𝒪(k)` on `Proj Γ(V, A)` attached to
  a homogeneous element `c` to the global section of `𝒪(k)` on `Proj Γ(U, A)` attached to the
  restriction of `c`.
* `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.projInclusionTwistMap_degreeSection`: the
  same statement about the **named** comparison morphism
  `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap`, which is the form every
  consumer of the comparison needs.

## The route

Every factor other than the third is a structural isomorphism of the inverse image, and
`StacksFrontier/AlgebraicGeometry/ProjInclusionDegreeSection/Unit.lean` says what each of those
does to a pulled-back global section — four general lemmas, none of them about `Proj`. The third
factor is the functor image of Tag 01MY's twist map, so naturality of the unit reduces it to
`Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection`.

So the content of this file is only the bookkeeping, and the bookkeeping is the hard part.

## Implementation notes

**The statement is the written-out composite, not the named `def`.** Unifying
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap` with a composite pattern
requires weak-head-normalising it, which is the obstruction already recorded for
`Stacks.AlgebraicGeometry.RelativeProj.isIso_projInclusionTwistComposite`, whose statement
spells the composite out for the same reason. With the named `def` in the
statement, elaboration does not finish inside the budget; with the composite spelled out it is
immediate.

**The composite is split in two, and the split point is forced.** The source of the fourth factor
is spelled `(f^* ⋙ g^*) M` — it is a component of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, whose type mentions the composite functor —
while the target of the third factor is spelled `g^* (f^* M)`, the third factor being a functor
image. The two are definitionally equal by one unfolding of `CategoryTheory.Functor.comp`, and
the kernel accepts the identification without complaint. The *elaborator* does not: at the
junction where the composite-functor spelling has to be matched against a metavariable already
assigned the iterated-image spelling, unification abandons the cheap unfolding and starts
reducing `AlgebraicGeometry.Scheme.Modules.pullback`, which is a left adjoint produced by a
choice principle; the diagnostic counter shows 368374 unfoldings of
`CategoryTheory.SheafOfModules.pullback` and 414942 of `Classical.indefiniteDescription` before
the budget is gone. The *other* junction, where the composite-functor spelling is matched against
a metavariable that has been assigned nothing yet, costs nothing. Hence: the two halves are
separate declarations, each proved by a chain of single-factor steps, and they are joined by one
application of `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.comp_app_of` in which the
junction is a single assignment. Doing it in one chain, and doing it with a bespoke assembly
lemma carrying both spellings at the level of functor variables, both
fail — the first in the elaborator, the second in the kernel.

**No step is a `rfl` at these types.** Each factor is handled by applying one of the general
lemmas of the companion file, and the composite is decomposed by
`Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.comp_app_of`, which is a `congrArg` proved
at the level of variables. `rw` is not used.

## What this does not give

**The cocycle is not here, and the rigidity argument as usually sketched does not close it.**
`Stacks.AlgebraicGeometry.TwistRigidity.eq_id` requires the endomorphism to fix
`degreeSection 𝒜 k c` for *every* homogeneous `c` of the graded ring `𝒜 = A.grading U`, and the
generation-and-cancellation proof genuinely needs every one: a section of `𝒪(n)` over a standard
open is locally `β / c` with both `β` and `c` homogeneous and arbitrary, and both are used. What
this file supplies is that hypothesis only for the `c` in the image of
`Stacks.AlgebraicGeometry.RelativeProjBridge`'s restriction
`A.res h : A.grading V →+*ᵍ A.grading U`, which is not all of `A.grading U k`: that subgroup is by
definition the image of `Γ(U, A_k)`, and `Γ(V, A_k) → Γ(U, A_k)` is not surjective. Closing the
cocycle therefore needs a *relative* rigidity statement, whose extra input is the degreewise
surjectivity after multiplication by a power of a function,
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.exists_resPiece_eq`. That
statement does not exist yet.

Nothing is said about the comparison on sections over an open other than `⊤`, or about
multiplicativity of the factors other than the third.

The passage to `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap` — the version
of the map that carries Tag 01NO's invertibility — **is** done, as
`Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.projInclusionTwistMap_degreeSection`; it is
the one reassociation of `≫` needed there,
performed at the level of variables so that the junction is never revisited.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.PullbackUnit

namespace Stacks.AlgebraicGeometry.ProjInclusionDegreeSection

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

universe u

/-- One factor of a composite, read on a section: knowing what the first factor does to a
section, the composite is the rest applied to the image. Proved at the level of variables, which
is where the conversion is free. -/
public theorem comp_app_of {W : Scheme.{u}} {M₀ M₁ M₂ : W.Modules} (a : M₀ ⟶ M₁) (b : M₁ ⟶ M₂)
    (V : W.Opens) {x : M₀.val.obj (op V)} {y : M₁.val.obj (op V)}
    (he : a.val.app (op V) x = y) :
    (a ≫ b).val.app (op V) x = b.val.app (op V) y :=
  congrArg (b.val.app (op V)) he

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U V : S.Opens) (h : U ≤ V)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (k : ℕ)

/-- **The third factor on a homogeneous global section.** The functor image of Tag 01MY's twist
map carries the pulled-back global section of `𝒪(k)` attached to `c` to the pulled-back global
section attached to the restriction of `c`.

This is `Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection` — Tag 01MY, part (1) —
pushed under the inverse image along the leading morphism by naturality of the unit. -/
public theorem factor₃_degreeSection (c : (A.grading V) k) :
    ((Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
          ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap (k : ℤ))).val.app (op ⊤)
        (pullbackSection (projInclusionTopSection A U V h hU hV)
          ((Scheme.Modules.pullback
              (projMapData (A.grading V) (A.grading U) (A.res h)).hom).obj
            (twistingSheaf (A.grading V) (k : ℤ)))
          (pullbackSection (projMapData (A.grading V) (A.grading U) (A.res h)).hom
            (twistingSheaf (A.grading V) (k : ℤ)) (degreeSection (A.grading V) k c))) =
      pullbackSection (projInclusionTopSection A U V h hU hV)
        ((Scheme.Modules.pullback (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).obj
          (twistingSheaf (A.grading U) (k : ℤ)))
        (pullbackSection (mapDomain (A.grading V) (A.grading U) (A.res h)).ι
          (twistingSheaf (A.grading U) (k : ℤ))
          (degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩)) :=
  (pullback_map_pullbackSection (projInclusionTopSection A U V h hU hV)
      ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap (k : ℤ)) _).trans
    (congrArg (pullbackSection (projInclusionTopSection A U V h hU hV) _)
      (twistMap_degreeSection (A.grading V) (A.grading U) (A.res h) k c))

/-- **The first three factors of Tag 01NO's composite on a homogeneous global section:** the
congruence for the factorisation of the morphism, the pseudofunctoriality isomorphism for that
factorisation, and the functor image of Tag 01MY's twist map. -/
public theorem head_degreeSection (c : (A.grading V) k) :
    ((Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).inv.app
          (twistingSheaf (A.grading V) (k : ℤ)) ≫
        (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
            (projMapData (A.grading V) (A.grading U) (A.res h)).hom).inv.app
          (twistingSheaf (A.grading V) (k : ℤ)) ≫
        (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
          ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap
            (k : ℤ))).val.app (op ⊤)
        (pullbackSection (projInclusionMap A U V h hU hV)
          (twistingSheaf (A.grading V) (k : ℤ)) (degreeSection (A.grading V) k c)) =
      pullbackSection (projInclusionTopSection A U V h hU hV)
        ((Scheme.Modules.pullback (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).obj
          (twistingSheaf (A.grading U) (k : ℤ)))
        (pullbackSection (mapDomain (A.grading V) (A.grading U) (A.res h)).ι
          (twistingSheaf (A.grading U) (k : ℤ))
          (degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩)) := by
  refine Eq.trans (comp_app_of _ _ ⊤
    (pullbackCongr_inv_pullbackSection (projInclusionMap_eq_comp A U V h hU hV)
      (twistingSheaf (A.grading V) (k : ℤ)) (degreeSection (A.grading V) k c))) ?_
  refine Eq.trans (comp_app_of _ _ ⊤
    (pullbackComp_inv_pullbackSection (projInclusionTopSection A U V h hU hV)
      (projMapData (A.grading V) (A.grading U) (A.res h)).hom
      (twistingSheaf (A.grading V) (k : ℤ)) (degreeSection (A.grading V) k c))) ?_
  exact factor₃_degreeSection A U V h hU hV k c

/-- **The last three factors of Tag 01NO's composite on a homogeneous global section:** the
pseudofunctoriality isomorphism for the open-domain inclusion, the congruence for the section
identity, and the pullback along the identity. Together they undo the identification of the open
domain of the induced morphism with the whole projective spectrum, returning the global section
attached to the restricted element. -/
public theorem tail_degreeSection (c : (A.grading V) k) :
    (((Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
          (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).hom.app
            (twistingSheaf (A.grading U) (k : ℤ))) ≫
      (Scheme.Modules.pullbackCongr (projInclusionTopSection_ι A U V h hU hV)).hom.app
        (twistingSheaf (A.grading U) (k : ℤ)) ≫
      (Scheme.Modules.pullbackId
        (AlgebraicGeometry.Proj (A.grading U))).hom.app
          (twistingSheaf (A.grading U) (k : ℤ))).val.app (op ⊤)
        (pullbackSection (projInclusionTopSection A U V h hU hV)
          ((Scheme.Modules.pullback (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).obj
            (twistingSheaf (A.grading U) (k : ℤ)))
          (pullbackSection (mapDomain (A.grading V) (A.grading U) (A.res h)).ι
            (twistingSheaf (A.grading U) (k : ℤ))
            (degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩))) =
      degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩ := by
  refine Eq.trans (comp_app_of _ _ ⊤
    (pullbackComp_hom_pullbackSection (projInclusionTopSection A U V h hU hV)
      (mapDomain (A.grading V) (A.grading U) (A.res h)).ι
      (twistingSheaf (A.grading U) (k : ℤ))
      (degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩))) ?_
  refine Eq.trans (comp_app_of _ _ ⊤
    (pullbackCongr_hom_pullbackSection (projInclusionTopSection_ι A U V h hU hV)
      (twistingSheaf (A.grading U) (k : ℤ))
      (degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩))) ?_
  exact pullbackId_hom_pullbackSection (AlgebraicGeometry.Proj (A.grading U))
    (twistingSheaf (A.grading U) (k : ℤ))
    (degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩)

/-- **Tag 01NO's twist comparison carries the pulled-back homogeneous global section to the
homogeneous global section of the restricted element.**

For an inclusion `U ⊆ V` of affine opens of the base and a homogeneous element `c` of degree `k`
of the graded ring of sections over `V`, the six-factor comparison map on the `k`-th twist sends
the image of `degreeSection (A.grading V) k c` under the unit of the pullback--pushforward
adjunction to `degreeSection (A.grading U) k (A.res h c)`.

The composite is written as the first three factors followed by the last three; see the module
docstring for why the split point is not a matter of taste. -/
public theorem composite_degreeSection (c : (A.grading V) k) :
    (((Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).inv.app
            (twistingSheaf (A.grading V) (k : ℤ)) ≫
          (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
              (projMapData (A.grading V) (A.grading U) (A.res h)).hom).inv.app
            (twistingSheaf (A.grading V) (k : ℤ)) ≫
          (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
            ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap (k : ℤ))) ≫
        ((Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
              (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).hom.app
            (twistingSheaf (A.grading U) (k : ℤ)) ≫
          (Scheme.Modules.pullbackCongr (projInclusionTopSection_ι A U V h hU hV)).hom.app
            (twistingSheaf (A.grading U) (k : ℤ)) ≫
          (Scheme.Modules.pullbackId
            (AlgebraicGeometry.Proj (A.grading U))).hom.app
              (twistingSheaf (A.grading U) (k : ℤ)))).val.app (op ⊤)
        (pullbackSection (projInclusionMap A U V h hU hV)
          (twistingSheaf (A.grading V) (k : ℤ)) (degreeSection (A.grading V) k c)) =
      degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩ := by
  refine Eq.trans (comp_app_of _ _ ⊤ (head_degreeSection A U V h hU hV k c)) ?_
  exact tail_degreeSection A U V h hU hV k c

/-- **Tag 01NO's *named* comparison morphism carries the pulled-back homogeneous global section to
the homogeneous global section of the restricted element.**

This is `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.composite_degreeSection` with the
written-out composite replaced by
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap`, the morphism whose
invertibility Tag 01NO's third assertion asserts and which every consumer of the comparison is
stated against. The two differ by one reassociation of `≫`, performed at the level of variables
by `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq_split` and rewritten
under the section map, so no conversion at these types is requested of the kernel. -/
public theorem projInclusionTwistMap_degreeSection (c : (A.grading V) k) :
    (ProjInclusionTwist.projInclusionTwistMap A U V h hU hV (k : ℤ)).val.app (op ⊤)
        (pullbackSection (projInclusionMap A U V h hU hV)
          (twistingSheaf (A.grading V) (k : ℤ)) (degreeSection (A.grading V) k c)) =
      degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩ := by
  rw [ProjInclusionTwist.projInclusionTwistMap_eq_split]
  exact composite_degreeSection A U V h hU hV k c

end Stacks.AlgebraicGeometry.ProjInclusionDegreeSection

end
