module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetOverSitePoint

/-!
# The slot `hτ₁` of the target square of clause (1) of Stacks 0D2Z over the site of `s`, in the
spelling of the assembly

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`, over the
site of `s` and at the chart data, is
`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_point` (and, with the scheme point
read off `w`, `…clauseOneTarget_square_overSite_of_slots`), with the hypotheses
`hcomp`, `hsite`, `hTZ`, `hτ₁`, `hχ`, `hT`, `hb` open.  This file proves the hypothesis `hτ₁` of
each at exactly the type of that binder: the statements are read off the type of the assembly by
the term elaborator `binder_type_of%`, so they are the binder's own expression (every implicit
object, instance and proof included) and plugging them in needs no unification across spellings.

## Main results

* `…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_point_hτ₁`: the hypothesis
  `hτ₁` of `…clauseOneTarget_square_overSite_point`.
* `…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots_hτ₁`: the hypothesis
  `hτ₁` of `…clauseOneTarget_square_overSite_of_slots`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

open Lean Elab Term Meta in
/-- `binder_type_of% e, h` is the type of the binder named `h` among the leading binders of the
type of `e`, provided it does not depend on the earlier binders: the expression stored in that
type, not a re-elaboration of its text. -/
elab "binder_type_of% " e:term ", " h:ident : term => do
  let e ← elabTerm e none
  synthesizeSyntheticMVarsNoPostponing
  let mut t ← instantiateMVars (← inferType (← instantiateMVars e))
  repeat
    match t with
    | .forallE n dom body _ =>
      if n == h.getId then
        if dom.hasLooseBVars then
          throwError "binder_type_of%: the type of {h.getId} depends on earlier binders"
        return dom
      t := body
    | _ => throwError "binder_type_of%: no binder named {h.getId}"
  throwError "binder_type_of%: unreachable"

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

/-- **The hypothesis `hτ₁` of the target square of clause (1) at a scheme point `w` of `U(ψ)`,
over the site of `s`, in the spelling of the assembly with `R = ⟨yoneda.obj W, _⟩`**: the
comparison `w^*r^*(π^*𝒜_d) ≅ c_w^*φ^*(π^*𝒜_d)` of the two factorisations `w ≫ r = c_w ≫ φ` is
the comparison `w^*r^* ≅ (w ≫ r)^*` of Stacks 03LU, the transport along `w ≫ r = c_w ≫ φ` and the
inverse comparison `(c_w ≫ φ)^* ≅ c_w^*φ^*`.  Stated as the binder `hτ₁` of
`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_point`; proved by
`…InvertibleTwistingRestriction.modulePullbackCompTransportIso_hom_eq` at the source
`⟨yoneda.obj W, _⟩`. -/
theorem clauseOneTarget_square_overSite_point_hτ₁ :
    binder_type_of% (clauseOneTarget_square_overSite_point w d), hτ₁ :=
  modulePullbackCompTransportIso_hom_eq (B := s.site) (S := s.base) (hS := s.containsBase)
    (A := (⟨yoneda.obj W, isAlgebraicSpace_yoneda s.site s.base s.containsBase W⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
    (pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := locusSpaceOfUnitalHom s f L ψ) w)
    ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
    (representedSpaceMap s.site s.base s.containsBase
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
    (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
    (pointHom_comp_invertibleSpaceMorphism w)
    ((modulePullback s.site s.base s.containsBase s.relativeProjSpaceHom).obj
      (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf s.site s.base s.containsBase
        s.space) s.shrink.algebra (d : ℤ)))

/-- **The hypothesis `hτ₁` of the target square of clause (1) at a scheme point `w` of `U(ψ)`,
over the site of `s`, in the spelling of the assembly with `R` read off `w`**: as
`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_point_hτ₁`, stated as the binder
`hτ₁` of `…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`. -/
theorem clauseOneTarget_square_overSite_of_slots_hτ₁ :
    binder_type_of% (clauseOneTarget_square_overSite_of_slots w d), hτ₁ :=
  modulePullbackCompTransportIso_hom_eq (B := s.site) (S := s.base) (hS := s.containsBase)
    (pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := locusSpaceOfUnitalHom s f L ψ) w)
    ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
    (representedSpaceMap s.site s.base s.containsBase
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
    (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
    (pointHom_comp_invertibleSpaceMorphism w)
    ((modulePullback s.site s.base s.containsBase s.relativeProjSpaceHom).obj
      (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf s.site s.base s.containsBase
        s.space) s.shrink.algebra (d : ℤ)))

/-- The binder `hτ₁` of `…clauseOneTarget_square_overSite_point` is met on the nose. -/
example (hcomp : binder_type_of% (clauseOneTarget_square_overSite_point w d), hcomp)
    (hsite : binder_type_of% (clauseOneTarget_square_overSite_point w d), hsite)
    (hTZ : binder_type_of% (clauseOneTarget_square_overSite_point w d), hTZ) :=
  clauseOneTarget_square_overSite_point w d hcomp hsite hTZ
    (clauseOneTarget_square_overSite_point_hτ₁ w d)

/-- The binder `hτ₁` of `…clauseOneTarget_square_overSite_of_slots` is met on the nose. -/
example (hcomp : binder_type_of% (clauseOneTarget_square_overSite_of_slots w d), hcomp)
    (hsite : binder_type_of% (clauseOneTarget_square_overSite_of_slots w d), hsite)
    (hTZ : binder_type_of% (clauseOneTarget_square_overSite_of_slots w d), hTZ) :=
  clauseOneTarget_square_overSite_of_slots w d hcomp hsite hTZ
    (clauseOneTarget_square_overSite_of_slots_hτ₁ w d)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
