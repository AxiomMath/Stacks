module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable

/-!
# The étale sites of a formal algebraic space at its canonical reduction

Let `S` be a scheme contained in a big fppf site `B`. The étale sites of Stacks 0DEA and their
functoriality, Stacks 0DEC, are constructed in
`StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSite` at an arbitrary bundled reduction datum
`AlgebraicGeometry.FormalSpace.Reduction`. That form is the more general one and carries the
mathematics. This file reads it at the reduction that Stacks 0AIN produces —
`AlgebraicGeometry.FormalSpace.canonicalReduction` — which is the form the source statements
have: they name the reduction of `X` and take no reduction as input.

## The canonical reduction

Passing from the reduction that Stacks 0AIN
(`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`) produces to the
bundled datum takes one step. That reduction is a sheaf of `Type (u + 1)`, like the formal
algebraic space itself, whereas the datum asks for an object of
`AlgebraicGeometry.AlgebraicSpaces`, a presheaf of `Type u`. An algebraic space with values in
`Type (u + 1)` is pointwise `u`-small, by the smallness argument carried out as
`AlgebraicGeometry.Space.small_of_isAlgebraicSpaceULift` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.Representable`, hence is the universe lift of one
with values in `Type u`; `AlgebraicGeometry.FormalSpace.IsReduction.precomp_iso` moves the
reduction condition along the resulting isomorphism and
`AlgebraicGeometry.FormalSpace.IsReduction.nonempty_reduction` assembles the datum.

## Main definitions

* `AlgebraicGeometry.FormalSpace.canonicalReduction` is the datum at the reduction Stacks 0AIN
  produces.
* `AlgebraicGeometry.FormalSpace.canonicalSmallEtale`,
  `AlgebraicGeometry.FormalSpace.canonicalSpacesEtale` and
  `AlgebraicGeometry.FormalSpace.canonicalAffineEtale`, with their topologies: **Stacks
  0DEA** at the canonical reduction, which is the form the source statement has.
* `AlgebraicGeometry.FormalSpace.canonicalSpacesBaseChange` and
  `AlgebraicGeometry.FormalSpace.canonicalSmallToposMorphism`: **Stacks 0DEC**, parts (1)
  and (3), at the canonical reduction.

## Main results

* `AlgebraicGeometry.FormalSpace.IsReduction.precomp_iso` and
  `AlgebraicGeometry.FormalSpace.IsReduction.nonempty_reduction`: a reduction in the sense of
  the predicate yields the bundled reduction datum.
* `AlgebraicGeometry.FormalSpace.isContinuous_canonicalSpacesBaseChange`,
  `AlgebraicGeometry.FormalSpace.canonicalSpacesBaseChange_isMorphismOfSites` and
  `AlgebraicGeometry.FormalSpace.canonicalSpacesBaseChangeComp_projection`: the remaining
  clauses of **Stacks 0DEC** at the canonical reduction.

## References

* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0DEC](https://stacks.math.columbia.edu/tag/0DEC)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### From the reduction predicate to the bundled reduction datum -/

namespace IsReduction

variable {B S hS}
variable {X Xred Xred' : FppfSheaf B S hS}

/-- Being a reduction of `X` transports along an isomorphism of the source: if `i : Xred ⟶ X`
exhibits `Xred` as a reduction of `X` and `e : Xred' ≅ Xred`, then `e.hom ≫ i` exhibits `Xred'`
as a reduction of `X`.

Each of the five conditions moves across: being an algebraic space and having a surjective
étale atlas by a reduced scheme transport along the isomorphism of underlying presheaves,
representability of the inclusion is unchanged by composing with an isomorphism on the left,
a cartesian square over `e.hom ≫ i` becomes one over `i` after composing its upper edge with
the isomorphism and so has the same lower edge, and the factorisation through `e.hom ≫ i` of a
morphism from a reduced algebraic space is its factorisation through `i` composed with
`e.inv`. -/
theorem precomp_iso {i : Xred ⟶ X} (h : IsReduction B S hS X Xred i) (e : Xred' ≅ Xred) :
    IsReduction B S hS X Xred' (e.hom ≫ i) := by
  have hcomp : (e.hom ≫ i).hom = e.hom.hom ≫ i.hom := rfl
  refine ⟨Space.isAlgebraicSpaceULift_of_iso B S hS (asIso e.inv.hom) h.algebraic, ?_, ?_, ?_,
    ?_⟩
  · obtain ⟨U, a, hsurj, hetale, hP⟩ := h.reduced
    exact ⟨U, a ≫ e.inv.hom, MorphismProperty.RespectsIso.postcomp _ e.inv.hom a hsurj,
      MorphismProperty.RespectsIso.postcomp _ e.inv.hom a hetale, hP⟩
  · rw [hcomp]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable)
      e.hom.hom i.hom).mpr h.representable
  · intro a b g fst snd sq
    rw [hcomp] at sq
    refine h.thickening g (fst ≫ e.hom.hom) snd ?_
    exact sq.of_iso (Iso.refl _) (asIso e.hom.hom) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp)
  · intro U hU hUred a
    obtain ⟨g, hg, hu⟩ := h.universal U hU hUred a
    refine ⟨g ≫ e.inv, ?_, ?_⟩
    · simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact hg
    · intro g' hg'
      have hgg : g' ≫ e.hom = g := hu (g' ≫ e.hom) (by simpa using hg')
      rw [← hgg, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- A reduction of `X` in the sense of `AlgebraicGeometry.FormalSpace.IsReduction` yields the
bundled datum `AlgebraicGeometry.FormalSpace.Reduction` that the three étale sites are built
from. The only gap between the two shapes is the value universe, and it closes by the smallness
descent; see the module docstring. -/
theorem nonempty_reduction {i : Xred ⟶ X} (h : IsReduction B S hS X Xred i) :
    Nonempty (Reduction B S hS X) := by
  obtain ⟨F, hF, ⟨ε⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS h.algebraic
  let space : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let e : liftSheaf B S hS space ≅ Xred :=
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).preimageIso ε
  exact ⟨⟨space, e.hom ≫ i, h.precomp_iso e⟩⟩

end IsReduction

/-! ### The canonical reduction of a formal algebraic space -/

section Canonical

variable {B S hS} {X Y Z : FppfSheaf B S hS}

/-- Every formal algebraic space over `S` has a bundled reduction datum: Stacks 0AIN produces a
reduction and `AlgebraicGeometry.FormalSpace.IsReduction.nonempty_reduction` packages it. -/
theorem nonempty_reduction_of_isFormalAlgebraicSpace (hX : IsFormalAlgebraicSpace B S hS X) :
    Nonempty (Reduction B S hS X) := by
  obtain ⟨Xred, i, hi⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS X hX
  exact hi.nonempty_reduction

/-- The reduction of a formal algebraic space over `S`, chosen from Stacks 0AIN. The choice is
immaterial: two reductions of one formal algebraic space are canonically isomorphic by
`AlgebraicGeometry.FormalSpace.Reduction.iso`, so the sites below at two choices are
isomorphic as well. -/
noncomputable def canonicalReduction (hX : IsFormalAlgebraicSpace B S hS X) :
    Reduction B S hS X :=
  (nonempty_reduction_of_isFormalAlgebraicSpace hX).some

/-! ### Stacks 0DEA at the canonical reduction -/

/-- **Stacks 0DEA, part (1).** The *small étale site* `X_étale` of a formal algebraic space `X`
over `S`, as a category: the small étale site `X_{red, étale}` of its reduction, in the sense of
Stacks 03ED, whose objects are the étale scheme charts of `X_red`. -/
@[stacks 0DEA "(1) the small étale site, as a category"]
abbrev canonicalSmallEtale (hX : IsFormalAlgebraicSpace B S hS X) :=
  (canonicalReduction hX).SmallEtale

/-- **Stacks 0DEA, part (1).** The topology of the small étale site of `X`: that of
`X_{red, étale}`. -/
@[stacks 0DEA "(1) the topology of the small étale site"]
noncomputable abbrev canonicalSmallEtaleTopology (hX : IsFormalAlgebraicSpace B S hS X) :
    GrothendieckTopology (canonicalSmallEtale hX) :=
  (canonicalReduction hX).smallEtaleTopology

/-- **Stacks 0DEA, part (2).** The site `X_{spaces, étale}` of a formal algebraic space `X` over
`S`, as a category: the spaces-étale site `X_{red, spaces, étale}` of its reduction, in the
sense of Stacks 03G0, whose objects are the algebraic spaces étale over `X_red`. -/
@[stacks 0DEA "(2) the spaces-étale site, as a category"]
abbrev canonicalSpacesEtale (hX : IsFormalAlgebraicSpace B S hS X) :=
  (canonicalReduction hX).SpacesEtale

/-- **Stacks 0DEA, part (2).** The topology of `X_{spaces, étale}`: that of
`X_{red, spaces, étale}`. -/
@[stacks 0DEA "(2) the topology of the spaces-étale site"]
noncomputable abbrev canonicalSpacesEtaleTopology (hX : IsFormalAlgebraicSpace B S hS X) :
    GrothendieckTopology (canonicalSpacesEtale hX) :=
  (canonicalReduction hX).spacesEtaleTopology

/-- **Stacks 0DEA, part (3).** The site `X_{affine, étale}` of a formal algebraic space `X` over
`S`, as a category: the affine étale site `X_{red, affine, étale}` of its reduction, whose
objects are the étale charts of `X_red` with affine source. -/
@[stacks 0DEA "(3) the affine étale site, as a category"]
abbrev canonicalAffineEtale (hX : IsFormalAlgebraicSpace B S hS X) :=
  (canonicalReduction hX).AffineEtale

/-- **Stacks 0DEA, part (3).** The topology of `X_{affine, étale}`: that of
`X_{red, affine, étale}`. -/
@[stacks 0DEA "(3) the topology of the affine étale site"]
noncomputable abbrev canonicalAffineEtaleTopology (hX : IsFormalAlgebraicSpace B S hS X) :
    GrothendieckTopology (canonicalAffineEtale hX) :=
  (canonicalReduction hX).affineEtaleTopology

/-! ### Stacks 0DEC at the canonical reduction -/

/-- **Stacks 0DEC, part (1).** The functor `Y_{spaces, étale} ⟶ X_{spaces, étale}` induced by a
morphism `f : X ⟶ Y` of formal algebraic spaces: base change along the induced morphism of
reductions, together with its cartesian projection, by Stacks 03G2, part (1). -/
@[stacks 0DEC "(1) the base-change functor `Y_spaces,étale ⟶ X_spaces,étale`"]
noncomputable def canonicalSpacesBaseChange (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    Space.SpacesBaseChange B S hS ((canonicalReduction hX).map (canonicalReduction hY) f) :=
  (canonicalReduction hX).spacesBaseChange (canonicalReduction hY) f

/-- **Stacks 0DEC, part (1).** The functor `Y_{spaces, étale} ⟶ X_{spaces, étale}` is
continuous. -/
@[stacks 0DEC "(1) continuity of the functor"]
theorem isContinuous_canonicalSpacesBaseChange (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (canonicalSpacesBaseChange hX hY f).functor.IsContinuous
      (canonicalSpacesEtaleTopology hY) (canonicalSpacesEtaleTopology hX) :=
  (canonicalReduction hX).isContinuous_spacesBaseChange (canonicalReduction hY) f

/-- **Stacks 0DEC, part (1).** The continuous functor `Y_{spaces, étale} ⟶ X_{spaces, étale}`
induces a morphism of sites `f_{spaces, étale} : X_{spaces, étale} ⟶ Y_{spaces, étale}`, in the
sense of Stacks 00X1. -/
@[stacks 0DEC "(1) the induced morphism of sites `f_spaces,étale`"]
theorem canonicalSpacesBaseChange_isMorphismOfSites (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (canonicalSpacesBaseChange hX hY f).functor.IsMorphismOfSites
      (canonicalSpacesEtaleTopology hY) (canonicalSpacesEtaleTopology hX) :=
  (canonicalReduction hX).spacesBaseChange_isMorphismOfSites (canonicalReduction hY) f

/-- **Stacks 0DEC, part (2).** The rule `f ↦ f_{spaces, étale}` is compatible with composition:
the underlying functor of `(f ≫ g)_{spaces, étale}` is canonically isomorphic to the composite
of those of `g_{spaces, étale}` and `f_{spaces, étale}`, which is the composition of morphisms
of sites of Stacks 03CC. -/
@[stacks 0DEC "(2) compatibility with composition, as a canonical isomorphism of the
  underlying functors"]
noncomputable def canonicalSpacesBaseChangeComp (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hZ : IsFormalAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (canonicalSpacesBaseChange hY hZ g).functor ⋙ (canonicalSpacesBaseChange hX hY f).functor ≅
      (canonicalSpacesBaseChange hX hZ (f ≫ g)).functor :=
  Reduction.spacesBaseChangeComp (canonicalReduction hX) (canonicalReduction hY)
    (canonicalReduction hZ) f g

/-- **Stacks 0DEC, part (2).** The composition isomorphism is compatible with the cartesian
projections to the original object of `Z_{spaces, étale}`, which pins it down. -/
@[stacks 0DEC "(2) the composition isomorphism is compatible with the cartesian projections,
  which pins it down"]
theorem canonicalSpacesBaseChangeComp_projection (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hZ : IsFormalAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (g : Y ⟶ Z) (V : canonicalSpacesEtale hZ) :
    ((canonicalSpacesBaseChangeComp hX hY hZ f g).hom.app V).hom.left ≫
        (canonicalSpacesBaseChange hX hZ (f ≫ g)).projection.app V =
      (canonicalSpacesBaseChange hX hY f).projection.app
          ((canonicalSpacesBaseChange hY hZ g).functor.obj V) ≫
        (canonicalSpacesBaseChange hY hZ g).projection.app V :=
  Reduction.spacesBaseChangeComp_projection (canonicalReduction hX) (canonicalReduction hY)
    (canonicalReduction hZ) f g V

/-- **Stacks 0DEC, part (3).** The morphism of topoi `f_small : Sh(X_étale) ⟶ Sh(Y_étale)`
associated to `f_{spaces, étale}`, via the identification (0DEB) of the small étale topos with
the spaces-étale topos. It is the morphism of small étale topoi of Stacks 03G2, part (3), at the
induced morphism of reductions. -/
@[stacks 0DEC "(3) the morphism of small étale topoi `f_small`, through the identification
  (0DEB)"]
noncomputable def canonicalSmallToposMorphism (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    MorphismOfTopoi (Sheaf (canonicalSmallEtaleTopology hX) (Type (u + 1)))
      (Sheaf (canonicalSmallEtaleTopology hY) (Type (u + 1))) :=
  (canonicalReduction hX).smallToposMorphism (canonicalReduction hY) f

/-- **Stacks 0DEC, part (3).** The construction of `f_small` is compatible with composition:
the direct image of the composite of `g_small` and `f_small` is canonically isomorphic to the
direct image of `(f ≫ g)_small`. -/
@[stacks 0DEC "(3) compatibility with composition of the morphisms of small étale topoi, on
  direct images"]
noncomputable def canonicalSmallToposMorphismComp (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hZ : IsFormalAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (MorphismOfTopoi.comp (canonicalSmallToposMorphism hY hZ g)
        (canonicalSmallToposMorphism hX hY f)).pushforward ≅
      (canonicalSmallToposMorphism hX hZ (f ≫ g)).pushforward :=
  Reduction.smallToposMorphismComp (canonicalReduction hX) (canonicalReduction hY)
    (canonicalReduction hZ) f g

end Canonical

end AlgebraicGeometry.FormalSpace

end
