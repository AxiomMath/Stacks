module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickeningDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningOfFormallyUnramified

/-!
# Étale localization of a universal first-order thickening

Let `Z ⟶ X` be a morphism of algebraic spaces over a scheme `S`, presented as a closed subspace
`Z` of an algebraic space `Z'` with structure morphism `p : Z' ⟶ X`, and suppose `Z ⊂ Z'` is a
universal first-order thickening of `Z` over `X`.  Let

```
  V ---→ U
  |      |
  ↓      ↓
  Z ---→ X
```

commute with étale vertical arrows.  Taking the universal first-order thickening commutes with
this localization: the étale extension `V'` of `V` across `Z ⊂ Z'` is a universal first-order
thickening of `V` over `U`, and the conormal module of `Z` in `Z'` restricts along `V ⟶ Z` to
the conormal module of `V` in `V'`.  Those are clauses (2) and (3) of Stacks 060D.

## Main definitions

* `AlgebraicGeometry.Space.conormalModuleEtaleLocalizationIso`: **Stacks 060D, clause (3)**, the
  identification `𝒞_{Z/X}|_V = 𝒞_{V/U}`.

## Main results

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.of_comp_formallyEtale`: a universal
  first-order thickening over `X` whose structure morphism factors through a formally étale
  `U ⟶ X` is a universal first-order thickening over `U`.  This is the converse of Stacks 0604.
* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etaleLocalization`:
  **Stacks 060D, clause (2)**.

## Implementation notes

**The étale extension is given, not produced — but both inputs the source uses are available.**
The source states clause (2) for *the* universal first-order thickening `V'` of `V` over `U`,
whose existence is Stacks 0606, and identifies it with the étale extension of `V` across
`Z ⊂ Z'` furnished by the topological invariance of the spaces-étale site, Stacks 05ZH.

* Stacks 0606 is `AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UniversalExistence.lean`, carried at full
  strength: a bare `@[stacks 0606]` with no clause string, taking nothing beyond
  `FormallyUnramified h.hom`.
* Stacks 05ZH is `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening`
  and `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEssSurj.lean`, together with
  `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsFirstOrderThickening` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleFullyFaithful.lean`, at a
  first-order thickening and with no hypothesis beyond `Mono` and the thickening itself — both
  of which are discharged by `AlgebraicGeometry.Space.mono_hom_inclusion` and
  `AlgebraicGeometry.Space.isFirstOrderThickening_range_inclusion`, as
  `AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsFirstOrderThickening` already does.  And
  essential surjectivity *is* the production of the extension: an object of the spaces-étale
  site of `Z` is, up to isomorphism, the base change along the inclusion of one over `Z'`.

So every argument of clause (2) below is reachable without hypothesis, and the bundle `(V', g,
hg, hsq)` is **already assembled in the library**:
`Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UniversalExistence.lean` proves, from that
essential surjectivity and unconditionally, that an algebraic space étale over the closed
subspace of a first-order thickening is the base change along the inclusion of an algebraic
space étale over the ambient space, with the cartesian square; and
`Stacks.Spaces.UniversalThickening.etale_lift_of_universalThickenings` in the same file already
repackages its `j` as the subfunctor `CategoryTheory.Subfunctor.range j` with the comparison
isomorphism, which is the `(V, c, hsq)` triple below.  The remaining argument `r` with `hr` is
free when `U` is `X` and `φ` the identity.

The shape is kept because every consumer in this library arrives with its extension already in
hand, so an existence statement would only have to be inverted again; and because the extension
these results produce is an étale **algebraic space** over the ambient space and not an étale
**scheme** chart.  That — a *represented* extension — is what the chart readings of the conormal
sequences need, and it is essential surjectivity on the small étale sites of scheme charts,
Stacks 07VW, a separate statement of which
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEquivalence.lean` carries only the
full faithfulness half,
`AlgebraicGeometry.Space.fullyFaithfulThickeningChartBaseChangeOfIsFirstOrderThickening`.

Read together with the uniqueness clause of
Stacks 0602 — a universal first-order thickening is unique up to a unique isomorphism, which is
`AlgebraicGeometry.Space.eq_universalThickeningMap` — clause (2) is the sentence of the source.
It is the same shape part (1) of Stacks 0605,
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etalePullback`, already takes in this
library.

**The base is descended from `X` to `U` by the converse of Stacks 0604.**  Part (1) of
Stacks 0605 gives the étale extension as a universal first-order thickening of `V` over `X`,
with structure morphism `g ≫ p`; what clause (2) asserts is that it is one over `U`.  The source
reaches that by applying Stacks 0604 to the other thickening and invoking uniqueness; here the
implication is run in the direction the data allow, as
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.of_comp_formallyEtale`.  Its proof is
the uniqueness clause of Stacks 0611 for the formally étale `U ⟶ X`: a dotted arrow over `X`
lies over `U` because its composite with `U ⟶ X`, and its restriction to the smaller space of
the test thickening, already agree with those of the given morphism `T' ⟶ U`.

**The conormal clause is the étale base change of Stacks 04CO, transported along the cartesian
square.**  Clause (3) is read, as the source reads it, through Stacks 0607: the conormal sheaf
`𝒞_{Z/X}` of a formally unramified morphism is the conormal module of `Z` in its universal
first-order thickening, and likewise `𝒞_{V/U}` is the conormal module of `V` in `V'` once clause
(2) identifies `V ⊂ V'` as that thickening.  So clause (3) is Stacks 04CO,
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`, for the étale `g : V' ⟶ Z'` and the
closed subspace `Z ⊂ Z'`.  What is added to it is the transport along the cartesian square: that
statement is about the inverse image `g⁻¹(Z)` and the canonical projection
`CategoryTheory.Subfunctor.fromPreimage`, whereas clause (3) is about the given `V` and the given
projection `V ⟶ Z`.  Being cartesian over the inclusion of `Z` forces `V` to be `g⁻¹(Z)`, by
`CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback`, and then forces the projection to be
the canonical one because the inclusion of a subfunctor is a monomorphism.

**Clause (1) is not proved here, and nothing here carries that part of the tag.**  Clause (1) of
Stacks 060D — that `V ⟶ U` is formally unramified, which is Stacks 04G8 — is independent of the
two clauses below: neither of them mentions formal unramifiedness, because the universal property
of Stacks 0602 is carried as a hypothesis rather than derived from it, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningFunctorial.lean`.

## References

* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
* [Stacks Project, Tag 0605](https://stacks.math.columbia.edu/tag/0605)
* [Stacks Project, Tag 0604](https://stacks.math.columbia.edu/tag/0604)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Lean v4.35.0: instance search for these limits on presheaves of the big fppf site times out;
supply them directly. -/
local instance hasLimitsOfSize_presheaf_UniversalThickeningEtaleLocalization :
    HasLimitsOfSize.{0, 0} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
local instance hasLimitsOfShape_discrete_presheaf_UniversalThickeningEtaleLocalization
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  HasLimitsOfSize.has_limits_of_shape _

/-! ### Descending the base along a formally étale morphism -/

/-- **The converse of Stacks 0604.**  Let `V ⊂ V'` be a first-order thickening of algebraic
spaces over `S`, let `r : V' ⟶ U` and let `φ : U ⟶ X` be formally étale.  If `V ⊂ V'` is a
universal first-order thickening of `V` over `X` with structure morphism `r ≫ φ`, then it is a
universal first-order thickening of `V` over `U` with structure morphism `r`.

Stacks 0604 is the implication in the other direction.  Both hold: a dotted arrow over `X` is
automatically one over `U`, because the uniqueness clause of Stacks 0611 for the formally étale
`φ` identifies its composite with `r` and the given morphism `T' ⟶ U`, these two agreeing after
composition with `φ` and on the smaller space of the test thickening. -/
theorem IsUniversalFirstOrderThickening.of_comp_formallyEtale {X U V' : AlgebraicSpaces B S hS}
    (V : Subfunctor V'.obj) (r : V' ⟶ U) (φ : U ⟶ X) (hφ : FormallyEtale φ.hom)
    (hV : IsUniversalFirstOrderThickening B S hS V (r ≫ φ)) :
    IsUniversalFirstOrderThickening B S hS V r := by
  have hrφ : (r ≫ φ).hom = r.hom ≫ φ.hom := rfl
  refine ⟨hV.firstOrder, ?_⟩
  intro T' T hT a b hcomm
  -- The solid diagram over `U` is a solid diagram over `X` after composing with `φ`.
  have hcomm' : T.ι ≫ b ≫ φ.hom = a ≫ V.ι ≫ (r ≫ φ).hom := by
    calc T.ι ≫ b ≫ φ.hom = (T.ι ≫ b) ≫ φ.hom := (Category.assoc _ _ _).symm
      _ = (a ≫ V.ι ≫ r.hom) ≫ φ.hom := by rw [hcomm]
      _ = a ≫ V.ι ≫ (r ≫ φ).hom := by rw [hrφ]; simp only [Category.assoc]
  obtain ⟨c, hc, hcu⟩ := hV.existsUnique_lift T hT a (b ≫ φ.hom) hcomm'
  -- The dotted arrow over `X` lies over `U`: its composite with `r` and the given `b` are two
  -- lifts of one solid diagram for the formally étale `φ`.
  have hlift : c ≫ r.hom = b := by
    refine (FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS φ hφ T hT
      (T.ι ≫ b) (b ≫ φ.hom) (Category.assoc _ _ _)).unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · calc T.ι ≫ c ≫ r.hom = (T.ι ≫ c) ≫ r.hom := (Category.assoc _ _ _).symm
        _ = (a ≫ V.ι) ≫ r.hom := by rw [hc.1]
        _ = a ≫ V.ι ≫ r.hom := Category.assoc _ _ _
        _ = T.ι ≫ b := hcomm.symm
    · calc (c ≫ r.hom) ≫ φ.hom = c ≫ r.hom ≫ φ.hom := Category.assoc _ _ _
        _ = c ≫ (r ≫ φ).hom := by rw [hrφ]
        _ = b ≫ φ.hom := hc.2
  refine ⟨c, ⟨hc.1, hlift⟩, fun c' hc' ↦ hcu c' ⟨hc'.1, ?_⟩⟩
  calc c' ≫ (r ≫ φ).hom = c' ≫ r.hom ≫ φ.hom := by rw [hrφ]
    _ = (c' ≫ r.hom) ≫ φ.hom := (Category.assoc _ _ _).symm
    _ = b ≫ φ.hom := by rw [hc'.2]

/-! ### Clause (2): the universal first-order thickening of the localization -/

/-- **Stacks 060D, clause (2).**  Let `Z ⊂ Z'` be a universal first-order thickening of `Z` over
an algebraic space `X`, with structure morphism `p : Z' ⟶ X`, let `φ : U ⟶ X` be étale, let
`g : V' ⟶ Z'` be étale with a morphism `r : V' ⟶ U` satisfying `r ≫ φ = g ≫ p`, and let
`V ⊂ V'` be a closed subspace whose inclusion sits in a cartesian square over the inclusion of
`Z`, so that `V = Z ×_{Z'} V'`.  Then `V ⊂ V'` is a universal first-order thickening of `V` over
`U`, with structure morphism `r`.

This says that the universal first-order thickening of `V` over `U` is the étale extension `V'`
of `V` across `Z ⊂ Z'`, and in particular that it is étale over `Z'`, which is the assertion of
the source.  The extension is a hypothesis rather than a conclusion of this statement, but it is
*not* an unavailable input: the topological invariance of the spaces-étale site which produces
it, Stacks 05ZH, is proved at a first-order thickening, and
`Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening` assembles the
extension from it unconditionally.  See the implementation notes for why the shape is kept.

The morphism `V ⟶ Z` of the source appears as the top edge `c` of the cartesian square, and is
automatically étale, being a base change of `g`. -/
@[stacks 060D "clause (2): the universal first-order thickening of the etale localization"]
theorem IsUniversalFirstOrderThickening.etaleLocalization
    {X U Z' V' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.obj) (p : Z' ⟶ X)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (g : V' ⟶ Z') (hg : IsEtale B S hS g.hom) (r : V' ⟶ U) (hr : r ≫ φ = g ≫ p)
    (V : Subfunctor V'.obj) (c : V.toFunctor ⟶ Z.toFunctor)
    (hsq : IsPullback c V.ι Z.ι g.hom) :
    IsUniversalFirstOrderThickening B S hS V r := by
  have hφFE : FormallyEtale φ.hom :=
    ((isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale B S hS
      U.property X.property φ.hom).mp hφ).2
  refine IsUniversalFirstOrderThickening.of_comp_formallyEtale B S hS V r φ hφFE ?_
  rw [hr]
  exact IsUniversalFirstOrderThickening.etalePullback B S hS Z p hZ g hg V c hsq

/-- The canonical morphisms of Stacks 060A between two universal first-order thickenings over
`U`, induced by an isomorphism `e` of the smaller spaces and its inverse, compose to the
identity. -/
private theorem universalThickeningMap_comp_inv_eq_id {U W' V' : AlgebraicSpaces B S hS}
    (W : Subfunctor W'.obj) (V : Subfunctor V'.obj) (q : W' ⟶ U) (r : V' ⟶ U)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (hV : IsUniversalFirstOrderThickening B S hS V r) (e : W.toFunctor ≅ V.toFunctor)
    (h₁ : W.ι ≫ q.hom ≫ (𝟙 U : U ⟶ U).hom = e.hom ≫ V.ι ≫ r.hom)
    (h₂ : V.ι ≫ r.hom ≫ (𝟙 U : U ⟶ U).hom = e.inv ≫ W.ι ≫ q.hom) :
    (universalThickeningMap B S hS (𝟙 U) e.hom hW hV h₁).hom ≫
      (universalThickeningMap B S hS (𝟙 U) e.inv hV hW h₂).hom = 𝟙 W'.obj := by
  have hmover : (universalThickeningMap B S hS (𝟙 U) e.hom hW hV h₁).hom ≫ r.hom = q.hom := by
    simpa using congrArg (fun k : W' ⟶ U => k.hom)
      (universalThickeningMap_over B S hS (𝟙 U) e.hom hW hV h₁)
  have hnover : (universalThickeningMap B S hS (𝟙 U) e.inv hV hW h₂).hom ≫ q.hom = r.hom := by
    simpa using congrArg (fun k : V' ⟶ U => k.hom)
      (universalThickeningMap_over B S hS (𝟙 U) e.inv hV hW h₂)
  refine hW.eq_of_lifts W hW.firstOrder (𝟙 W.toFunctor) q.hom _ (𝟙 W'.obj) ?_ ?_
    (by simp) (by simp)
  · rw [← Category.assoc, universalThickeningMap_restrict B S hS (𝟙 U) e.hom hW hV h₁,
      Category.assoc, universalThickeningMap_restrict B S hS (𝟙 U) e.inv hV hW h₂,
      ← Category.assoc, e.hom_inv_id, Category.id_comp]
  · rw [Category.assoc, hnover, hmover]

/-- **Stacks 060D, clause (2), the étaleness assertion.**  With the data of clause (2), *every*
universal first-order thickening `W ⊂ W'` of `V` over `U` is étale over `Z'`: there is a morphism
`W' ⟶ Z'` which is étale, restricts on `W` to the composite `V ⟶ Z ⊂ Z'` read through the
identification of `W` with `V`, and lies over `X`.

This is the sentence of the source.  Clause (2) identifies the étale extension `V'` of `V` across
`Z ⊂ Z'` as *a* universal first-order thickening of `V` over `U`, and the universal property of
Stacks 0602 makes any other one isomorphic to it over `U`: the two canonical morphisms of
Stacks 060A between them compose, in either order, to a morphism which restricts to the identity
and lies over `U`, hence to the identity by the uniqueness clause.  Transporting the étale
`g : V' ⟶ Z'` along that isomorphism gives the morphism asserted here.

The identification of `W` with `V` is the datum `e`, with `he` saying that it is one of spaces
over `U`; it is needed because the smaller space of a thickening is presented as a subfunctor of
its ambient space, so two thickenings of one space never have literally the same smaller
space. -/
@[stacks 060D "clause (2): the universal first-order thickening is etale over the thickening of Z"]
theorem exists_isEtale_of_isUniversalFirstOrderThickening
    {X U Z' V' W' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.obj) (p : Z' ⟶ X)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (g : V' ⟶ Z') (hg : IsEtale B S hS g.hom) (r : V' ⟶ U) (hr : r ≫ φ = g ≫ p)
    (V : Subfunctor V'.obj) (c : V.toFunctor ⟶ Z.toFunctor)
    (hsq : IsPullback c V.ι Z.ι g.hom)
    (W : Subfunctor W'.obj) (q : W' ⟶ U)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (e : W.toFunctor ≅ V.toFunctor) (he : e.hom ≫ V.ι ≫ r.hom = W.ι ≫ q.hom) :
    ∃ m : W' ⟶ Z', IsEtale B S hS m.hom ∧ W.ι ≫ m.hom = e.hom ≫ V.ι ≫ g.hom ∧
      m ≫ p = q ≫ φ := by
  have hV : IsUniversalFirstOrderThickening B S hS V r :=
    IsUniversalFirstOrderThickening.etaleLocalization B S hS Z p hZ φ hφ g hg r hr V c hsq
  have hsq₁ : W.ι ≫ q.hom ≫ (𝟙 U : U ⟶ U).hom = e.hom ≫ V.ι ≫ r.hom := by
    simpa using he.symm
  have hsq₂ : V.ι ≫ r.hom ≫ (𝟙 U : U ⟶ U).hom = e.inv ≫ W.ι ≫ q.hom := by
    rw [← he]
    simp
  -- The two canonical morphisms of Stacks 060A between the two thickenings.
  have hmres : W.ι ≫ (universalThickeningMap B S hS (𝟙 U) e.hom hW hV hsq₁).hom =
      e.hom ≫ V.ι :=
    universalThickeningMap_restrict B S hS (𝟙 U) e.hom hW hV hsq₁
  have hmover' : universalThickeningMap B S hS (𝟙 U) e.hom hW hV hsq₁ ≫ r = q := by
    simpa using universalThickeningMap_over B S hS (𝟙 U) e.hom hW hV hsq₁
  have hmn := universalThickeningMap_comp_inv_eq_id B S hS W V q r hW hV e hsq₁ hsq₂
  have hnm := universalThickeningMap_comp_inv_eq_id B S hS V W r q hV hW e.symm hsq₂ hsq₁
  set m := (universalThickeningMap B S hS (𝟙 U) e.hom hW hV hsq₁).hom with hmdef
  set n := (universalThickeningMap B S hS (𝟙 U) e.inv hV hW hsq₂).hom with hndef
  have : IsIso m := ⟨n, hmn, hnm⟩
  have hcomp : (universalThickeningMap B S hS (𝟙 U) e.hom hW hV hsq₁ ≫ g).hom = m ≫ g.hom := rfl
  refine ⟨universalThickeningMap B S hS (𝟙 U) e.hom hW hV hsq₁ ≫ g, ?_, ?_, ?_⟩
  · rw [hcomp]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS m) hg
  · rw [hcomp, ← Category.assoc, hmres, Category.assoc]
  · rw [Category.assoc, ← hr, ← Category.assoc, hmover']

/-! ### Clause (3): the conormal module of the localization -/

/-- **Stacks 060D, clause (3).**  With the data of clause (2), the conormal module of `Z` in `Z'`
restricts along the projection `c : V ⟶ Z` to the conormal module of `V` in `V'`:

`𝒞_{Z/X}|_V = c^*𝒞_{Z/X} ≅ 𝒞_{V/U}`.

The two sides are the conormal sheaves of Stacks 0607 of the formally unramified morphisms
`Z ⟶ X` and `V ⟶ U`: the left-hand one because `Z ⊂ Z'` is a universal first-order thickening of
`Z` over `X` by hypothesis, the right-hand one because `V ⊂ V'` is a universal first-order
thickening of `V` over `U` by clause (2).

The isomorphism is the étale base change of Stacks 04CO,
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`, for the étale morphism `g : V' ⟶ Z'`,
transported along the cartesian square: the square forces `V` to be the inverse image `g⁻¹(Z)`
and `c` to be the canonical projection of that inverse image. -/
@[stacks 060D "clause (3): the conormal module of the etale localization"]
noncomputable def conormalModuleEtaleLocalizationIso {Z' V' : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS Z'.obj) (g : V' ⟶ Z') (hg : IsEtale B S hS g.hom)
    (V : Subfunctor V'.obj) (hV : IsClosedSubspace B S hS V)
    (c : V.toFunctor ⟶ Z.1.toFunctor) (hsq : IsPullback c V.ι Z.1.ι g.hom) :
    (modulePullback B S hS
          (ObjectProperty.homMk c :
            (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj
        (conormalModule B S hS Z' Z) ≅
      conormalModule B S hS V' ⟨V, hV⟩ := by
  -- Being cartesian over the inclusion of `Z` identifies `V` with the inverse image `g⁻¹(Z)`.
  obtain rfl : V = Z.1.preimage g.hom := by
    have h := Subfunctor.range_eq_preimage_of_isPullback hsq.flip
    rwa [Subfunctor.range_ι, Subfunctor.range_ι] at h
  -- The projection is then the canonical one, the inclusion of a subfunctor being a
  -- monomorphism.
  obtain rfl : c = Z.1.fromPreimage g.hom := by
    refine (cancel_mono Z.1.ι).1 ?_
    rw [Subfunctor.fromPreimage_ι]
    exact hsq.w
  exact conormalModuleEtaleRestrictionIso B S hS g hg Z

end AlgebraicGeometry.Space

end
