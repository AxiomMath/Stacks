module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# The structure map of an étale morphism is the unit of the restriction adjunction

Let `h : U ⟶ V` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Restriction of sheaves of sets along small étale postcomposition with `h` is
left adjoint to the direct image,

`(-)|_U ⊣ h_*`,

by `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`.  Both the structure map `h^♯`
of Stacks 03G8, with its ring structure forgotten, and the unit of that adjunction at the
structure sheaf of `V` are morphisms `𝒪_V ⟶ h_*𝒪_U`, because
`(smallEtaleSetRestriction h hh).obj (structureSetSheaf V)` is `structureSetSheaf U` on the nose.
This file proves that they are the same morphism.

That identification is what turns the set-level adjunction into a tool for `𝒪`-modules, and it
is the gating step of Stacks 03M8.  In the notation of that lemma — `τ : U ⟶ X` the surjective
étale chart, `ρ = t ≫ τ = s ≫ τ : R ⟶ X`, `a = τ ≫ f`, `b = ρ ≫ f` — the sequence
`0 → f_*F → a_*(F|_U) → b_*(F|_R)` is `f_*` applied to `0 → F → τ_*(F|_U) → ρ_*(F|_R)`, whose
first arrow is the unit at `τ` and whose second is the difference of the two units at `t` and
at `s`.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRestrictionAdjunction.lean` record that reading
and name this equation as the missing input; it is supplied here.

## Main results

* `AlgebraicGeometry.Space.structureSharpSet_eq_unit`: the structure map of Stacks 03G8 of an
  étale morphism, on underlying sheaves of sets, is the unit of
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at the structure sheaf.
* `AlgebraicGeometry.Space.counitIso_hom_app_restrictionAdjunction_unit` computes the chart
  projections of that unit: on the étale scheme chart of `U` above `U ×_V W` determined by an
  arrow of the structured-arrow category, the unit is restriction of sections along the induced
  chart morphism.
* `AlgebraicGeometry.Space.toOver_map_eq_chartBaseChangeMap` is the geometric content: that
  induced chart morphism is the chart morphism
  `AlgebraicGeometry.Space.chartBaseChangeMap` of the structure map.
* `AlgebraicGeometry.Space.restriction_map_unitIso_hom_comp_counitIso` is the triangle identity
  of the comparison equivalence of Stacks 03G1 in the form the computation consumes.

## Implementation notes

**Why no attribute.**  Stacks 03G8 asserts the existence of the morphism of small étale ringed
topoi of a morphism of algebraic spaces, its compatibility with composition — which is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` — and its agreement with the
construction for schemes; it asserts nothing about étale restriction being adjoint to the direct
image.  Stacks 03LP and 03LQ assert the adjunction, already carried by
`AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso` and its small étale sibling, and
say nothing about the structure map.  The single assertion of Stacks 03M8 is the exact sequence,
which is not stated here.  So no declaration below carries an attribute.

**How the unit is computed.**  The adjunction is a conjugation of the spaces-étale adjunction by
the comparison equivalences of Stacks 03G1, so its unit at a sheaf `P` is, by `rfl`, the inverse
counit of the comparison equivalence at `V`, then the spaces-étale unit — which is restriction
along the cartesian projection, by
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction_unit_app` — then the unit of the
comparison equivalence at `U`, then the comparison
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso`.  The last two of those four factors
collapse, against the counit at `U` that
`AlgebraicGeometry.Space.counitIso_app_injective` introduces, to the counit at `V`: that is the
triangle identity (`AlgebraicGeometry.Space.restriction_map_unitIso_hom_comp_counitIso`)
together with `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso_inv_app`.  The counit at
`V` so produced cancels the inverse counit at `V`, which is the first factor, and the second
factor is restriction along the cartesian projection.  What is left is exactly restriction of
sections of `P` along a morphism of the small étale site of `V`.  That morphism exists because
the comparison functor of Stacks 03G1 is **full**
(`AlgebraicGeometry.Space.comparisonFunctor_full`); faithfulness is not used, since the two
lemmas below are stated for *any* morphism whose comparison is the given one and the proof needs
only that one exists.  It is identified with the chart
morphism of the structure map by
`AlgebraicGeometry.Space.toOver_map_eq_chartBaseChangeMap`.  Nothing is computed about the
quasi-inverses of the comparison equivalences, which are `CategoryTheory.Functor.inv` and hence
`Classical.choose`.

**Elaboration.**  Every rewrite is performed as a `congrArg` rather than with `rw`, for the
reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureSharpBaseChange.lean`: the objects involved are
only definitionally equal — `(smallEtaleSetRestriction h hh).obj (structureSetSheaf V)` versus
`structureSetSheaf U`, and `comparisonFunctor V ⋙ spacesEtalePostcomp h hh` versus
`smallEtalePostcomp h hh ⋙ comparisonFunctor U` — so a rewrite abstracting one of them produces
a motive which is not type-correct at `implicit` transparency.  Three `congrArg` functions need
their binder type written out for the same reason; the rest leave it to be inferred.  No
`set_option` appears in this file.

**Universes.**  Everything is at the universe `u` of the structure rings, which is the only
universe at which `AlgebraicGeometry.Space.smallEtaleDirectImage`, and hence
`AlgebraicGeometry.Space.structureSharp`, exists.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicSpaces B S hS}

/-! ### The triangle identity of the comparison equivalence -/

/-- **The triangle identity of the comparison equivalence of Stacks 03G1, in transposed form.**
Let `ψ` be a morphism out of the restriction along the comparison functor of a sheaf `Q` on the
spaces-étale site of `X`.  Transposing `ψ` across the comparison equivalence — the unit at `Q`
followed by the quasi-inverse of `ψ` — and then restricting along the comparison functor and
following with the counit returns `ψ`.

The two displayed factors are the two halves of the hom-set bijection of
`CategoryTheory.Equivalence.toAdjunction`, whose unit and counit are those of the equivalence
on the nose, so this is `Equiv.symm_apply_apply` for that bijection.  It is stated in the
`unitIso`/`counitIso` spelling the rest of this development uses rather than through
`CategoryTheory.Adjunction.homEquiv`, which appears nowhere in these files. -/
theorem restriction_map_unitIso_hom_comp_counitIso (X : AlgebraicSpaces B S hS)
    (Q : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (Q' : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (psi : (smallEtaleComparisonRestriction B S hS X).obj Q ⟶ Q') :
    (smallEtaleComparisonRestriction B S hS X).map
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom.app Q ≫
            (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map psi) ≫
        (smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app Q' = psi :=
  ((smallEtaleComparisonRestriction B S hS X).asEquivalence.toAdjunction.homEquiv Q
    Q').symm_apply_apply psi

/-! ### The chart projections of the unit -/

/-- **The chart projections of the unit of the étale restriction adjunction.**  Let `h : U ⟶ V`
be étale, let `W` be an étale scheme chart of `V`, and let `j` be an étale scheme chart of `U`
above `U ×_V W`.  Suppose the morphism of the spaces-étale site of `V` obtained from `j` by
postcomposition with `h` and the cartesian projection of
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction` is the comparison of a
morphism `ν` of the small étale site of `V`.  Then restricting the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` to `j` and reading it through the
counit of the comparison equivalence of Stacks 03G1 is restriction of sections along `ν`.

The unit is, by `rfl`, a composite of four factors.  The last two collapse against the counit
at `U` to the counit at `V`, by
`AlgebraicGeometry.Space.restriction_map_unitIso_hom_comp_counitIso` and
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso_inv_app`; the counit at `V` cancels the
first factor, which is the inverse counit at `V`; and the second factor is restriction along the
cartesian projection, by
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction_unit_app`, which is where `ν` enters.
-/
theorem counitIso_hom_app_restrictionAdjunction_unit (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) (W : SmallEtale B S hS V.1)
    (j : StructuredArrow (op (chartBaseChange B S hS h W)) (comparisonFunctor B S hS U).op)
    (x : P.obj.obj (op W))
    (nu : (smallEtalePostcomp B S hS h hh).obj j.right.unop ⟶ W)
    (hnu : (comparisonFunctor B S hS V).map nu =
      (spacesEtalePostcomp B S hS h hh).map j.hom.unop ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
          ((comparisonFunctor B S hS V).obj W)) :
    ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
          ((smallEtaleSetRestriction B S hS h hh).obj P)).hom.app j.right
        (((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS h hh).obj P)).obj.map j.hom
          (((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app P).hom.app (op W) x)) =
      P.obj.map nu.op x := by
  set eU := (smallEtaleComparisonRestriction B S hS U).asEquivalence
  set eV := (smallEtaleComparisonRestriction B S hS V).asEquivalence
  set y := (eV.counitIso.inv.app P).hom.app (op W) x
  set a := (spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app (eV.inverse.obj P)
  have hBC : (smallEtaleComparisonRestriction B S hS U).map
          (eU.unitIso.hom.app ((spacesEtaleSetRestriction B S hS h hh).obj (eV.inverse.obj P)) ≫
            eU.inverse.map ((smallEtaleSetRestrictionConjIso B S hS h hh).inv.app P)) ≫
        eU.counitIso.hom.app ((smallEtaleSetRestriction B S hS h hh).obj P) =
      (smallEtaleSetRestriction B S hS h hh).map (eV.counitIso.hom.app P) :=
    (restriction_map_unitIso_hom_comp_counitIso B S hS U _ _
      ((smallEtaleSetRestrictionConjIso B S hS h hh).inv.app P)).trans
      (smallEtaleSetRestrictionConjIso_inv_app B S hS h hh P)
  have hfinal : (eV.counitIso.hom.app P).hom.app (op W) y = x :=
    congrArg (fun m : P ⟶ P ↦ m.hom.app (op W) x) (eV.counitIso.inv_hom_id_app P)
  have hD : ((spacesEtaleSetRestriction B S hS h hh).obj (eV.inverse.obj P)).obj.map j.hom
        (a.hom.app (op ((comparisonFunctor B S hS V).obj W)) y) =
      (eV.inverse.obj P).obj.map ((comparisonFunctor B S hS V).map nu).op y := by
    refine Eq.trans (congrArg (fun y ↦ (eV.inverse.obj P).obj.map
        ((spacesEtalePostcomp B S hS h hh).map j.hom.unop).op y)
      (spacesEtalePostcompSheafAdjunction_unit_app B S hS h hh (eV.inverse.obj P)
        ((comparisonFunctor B S hS V).obj W) y)) ?_
    refine Eq.trans (Functor.map_comp_apply (eV.inverse.obj P).obj
      ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
        ((comparisonFunctor B S hS V).obj W)).op
      ((spacesEtalePostcomp B S hS h hh).map j.hom.unop).op y).symm ?_
    exact congrArg (fun m ↦ (eV.inverse.obj P).obj.map m y)
      ((congrArg Quiver.Hom.op hnu).trans op_comp).symm
  refine Eq.trans (congrArg (fun y ↦
      (eU.counitIso.hom.app ((smallEtaleSetRestriction B S hS h hh).obj P)).hom.app j.right y)
    (NatTrans.naturality_apply
      (eU.unitIso.hom.app ((spacesEtaleSetRestriction B S hS h hh).obj (eV.inverse.obj P)) ≫
          eU.inverse.map ((smallEtaleSetRestrictionConjIso B S hS h hh).inv.app P)).hom j.hom
      (a.hom.app (op ((comparisonFunctor B S hS V).obj W)) y)).symm) ?_
  refine Eq.trans (congrArg (fun m : (smallEtaleComparisonRestriction B S hS U).obj
        ((spacesEtaleSetRestriction B S hS h hh).obj (eV.inverse.obj P)) ⟶
      (smallEtaleSetRestriction B S hS h hh).obj P ↦
    m.hom.app j.right
      (((spacesEtaleSetRestriction B S hS h hh).obj (eV.inverse.obj P)).obj.map j.hom
        (a.hom.app (op ((comparisonFunctor B S hS V).obj W)) y))) hBC) ?_
  refine Eq.trans (congrArg (fun y ↦ (eV.counitIso.hom.app P).hom.app
        (op ((smallEtalePostcomp B S hS h hh).obj j.right.unop)) y) hD) ?_
  refine Eq.trans (NatTrans.naturality_apply (eV.counitIso.hom.app P).hom nu.op y) ?_
  exact congrArg (fun y ↦ P.obj.map nu.op y) hfinal

/-! ### The chart morphism of the unit -/

/-- **The chart morphism of the unit is the chart morphism of the structure map.**  Let `W` be
an étale scheme chart of `V` and `j` an étale scheme chart of `U` above `U ×_V W`.  If a
morphism `ν` of the small étale site of `V` has as its comparison the morphism obtained from `j`
by postcomposition with `h` followed by the cartesian projection, then `ν` has the same
underlying morphism of the big fppf site of `S` as
`AlgebraicGeometry.Space.chartBaseChangeMap`.

Both are determined by their Yoneda morphisms: that of `ν` is the comparison of `ν` read on
underlying algebraic spaces, that of the chart morphism is the given arrow followed by the
cartesian projection, and the counit of the adjunction of sites *is* that projection
(`AlgebraicGeometry.Space.toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit`).
Spaces-étale postcomposition leaves the underlying algebraic spaces and morphisms unchanged. -/
theorem toOver_map_eq_chartBaseChangeMap (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (W : SmallEtale B S hS V.1)
    (j : StructuredArrow (op (chartBaseChange B S hS h W)) (comparisonFunctor B S hS U).op)
    (nu : (smallEtalePostcomp B S hS h hh).obj j.right.unop ⟶ W)
    (hnu : (comparisonFunctor B S hS V).map nu =
      (spacesEtalePostcomp B S hS h hh).map j.hom.unop ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
          ((comparisonFunctor B S hS V).obj W)) :
    (SmallEtale.toOver B S hS V.1).map nu = chartBaseChangeMap B S hS h W j := by
  have key : (SpacesEtale.toSpaces B S hS V).map
        ((spacesEtalePostcomp B S hS h hh).map j.hom.unop ≫
          (spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
            ((comparisonFunctor B S hS V).obj W)) =
      (SpacesEtale.toSpaces B S hS U).map j.hom.unop ≫
        (spacesBaseChange B S hS h).projection.app ((comparisonFunctor B S hS V).obj W) :=
    ((SpacesEtale.toSpaces B S hS V).map_comp _ _).trans
      (congrArg (fun m ↦ (SpacesEtale.toSpaces B S hS U).map j.hom.unop ≫ m)
        (toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit B S hS h hh
          ((comparisonFunctor B S hS V).obj W)))
  apply yoneda.map_injective
  refine Eq.trans (toSpaces_comparisonFunctor_map_hom B S hS V nu).symm ?_
  refine Eq.trans (congrArg (fun m ↦ ((SpacesEtale.toSpaces B S hS V).map m).hom) hnu) ?_
  refine Eq.trans ?_ (yoneda_map_chartBaseChangeMap B S hS h W j).symm
  exact congrArg (fun m : (SpacesEtale.toSpaces B S hS U).obj
      ((comparisonFunctor B S hS U).obj j.right.unop) ⟶
      (SpacesEtale.toSpaces B S hS V).obj ((comparisonFunctor B S hS V).obj W) ↦ m.hom) key

/-! ### The structure map is the unit -/

/-- **The structure map of an étale morphism is the unit of the restriction adjunction.**  For
an étale morphism `h : U ⟶ V` of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, the structure map `h^♯ : 𝒪_V ⟶ h_*𝒪_U` of Stacks 03G8 on underlying sheaves of sets
is the unit of `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at the structure
sheaf of `V`.

The statement is well-posed because
`(smallEtaleSetRestriction h hh).obj (structureSetSheaf V)` is `structureSetSheaf U` on the
nose, so both sides are morphisms `𝒪_V ⟶ h_*𝒪_U`.

Both sides are compared on sections over an étale scheme chart `W` of `V`, where they are
sections of `𝒪_U` read over the algebraic space `U ×_V W`, hence determined by their
restrictions to the étale scheme charts of `U` above `U ×_V W`
(`AlgebraicGeometry.Space.spacesEtale_section_ext`) and then by
`AlgebraicGeometry.Space.counitIso_app_injective`.  On such a chart both sides are pullback of
regular functions along the induced morphism of schemes: the structure map by
`AlgebraicGeometry.Space.counitIso_hom_app_structureSharpSet`, and the unit by
`AlgebraicGeometry.Space.counitIso_hom_app_restrictionAdjunction_unit` together with
`AlgebraicGeometry.Space.toOver_map_eq_chartBaseChangeMap`, the morphism of charts being
supplied by `AlgebraicGeometry.Space.comparisonFunctor_full`.

This carries no attribute: Stacks 03G8 asserts no adjunction property of the structure map,
Stacks 03LP and 03LQ assert nothing about the structure map, and the single assertion of
Stacks 03M8 is the exact sequence, which is not stated here. -/
theorem structureSharpSet_eq_unit (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    structureSharpSet B S hS h =
      (smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
        (structureSetSheaf B S hS V) := by
  have := comparisonFunctor_full B S hS V
  refine Sheaf.hom_ext_sections (fun W x ↦ ?_)
  refine spacesEtale_section_ext B S hS U (chartBaseChange B S hS h W.unop)
    ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
      (structureSetSheaf B S hS U)) (fun j ↦ ?_)
  refine counitIso_app_injective B S hS U (structureSetSheaf B S hS U) j.right ?_
  obtain ⟨nu, hnu⟩ : ∃ nu : (smallEtalePostcomp B S hS h hh).obj j.right.unop ⟶ W.unop,
      (comparisonFunctor B S hS V).map nu =
        (spacesEtalePostcomp B S hS h hh).map j.hom.unop ≫
          (spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
            ((comparisonFunctor B S hS V).obj W.unop) :=
    ⟨(comparisonFunctor B S hS V).preimage _, (comparisonFunctor B S hS V).map_preimage _⟩
  refine Eq.trans (counitIso_hom_app_structureSharpSet B S hS h W.unop j x) ?_
  refine Eq.trans ?_ (counitIso_hom_app_restrictionAdjunction_unit B S hS h hh
    (structureSetSheaf B S hS V) W.unop j x nu hnu).symm
  exact congrArg (fun m ↦ (forget CommRingCat.{u}).map
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op) x)
    (toOver_map_eq_chartBaseChangeMap B S hS h hh W.unop j nu hnu).symm

end AlgebraicGeometry.Space

end
