module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianSystem

/-!
# The situation of Stacks 0CP6

Let `S` be a scheme and let `B = lim_i B_i` be the limit of a directed inverse system of
Noetherian algebraic spaces over `S` with affine transition morphisms `B_{i'} ⟶ B_i` for
`i ≤ i'`. This file records the situation by its data alone: the directed system, Noetherianity
of its members and affineness of its transitions. The limit `B` is then *constructed* as the
limit of the system in presheaves on the big fppf site over `S`, and Stacks 07SF,
`AlgebraicGeometry.Space.isAlgebraicSpace_limit`, shows that it is an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.NoetherianSpaceSystem`: a directed inverse system of Noetherian
  algebraic spaces over `S` with affine transition morphisms.
* `AlgebraicGeometry.Space.NoetherianSpaceSystem.limit`: its limit `B = lim_i B_i`.
* `AlgebraicGeometry.Space.NoetherianSpaceSystem.toNoetherianLimitSystem`: the system together
  with its limit cone, as an `AlgebraicGeometry.Space.NoetherianLimitSystem`.

## Main results

* `AlgebraicGeometry.Space.NoetherianSpaceSystem.isAlgebraicSpace_limit`: the limit `B` is an
  algebraic space over `S` (Stacks 07SF).
* `AlgebraicGeometry.Space.NoetherianSpaceSystem.isAffineHom_limitπ`: each projection
  `B ⟶ B_i` is affine (Stacks 07SF, part (1)).

## Implementation notes

Algebraic spaces over `S` are presheaves on a big fppf site `Sch_κ` over `S` whose schemes have
size below a fixed cutoff `κ`. The chapter's standing convention, Stacks 07SD, is that every
ring it considers has its spectrum in the site; in particular the colimit rings computing the
affine charts of `B` must. With the cutoff fixed, that convention is the bound
`#I < cof κ` on the index set, carried as the field `indexSize`, exactly as in the other
situations of this chapter (`AlgebraicGeometry.Space.MorphismDescentSystem`). It is a
set-theoretic convention and not a Stacks result: without it the limit need not be an
algebraic space of the site at all, see
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineStageLargeIndexCounterexample.lean`. The
hom-set bound of Stacks 07SF is automatic for a preorder, whose hom-sets have at most one
element.

Noetherian means `AlgebraicGeometry.Space.IsNoetherian`, which uses the absolute
quasi-separatedness of Stacks 03BS, part (3); that is why the containment `hZ` of the terminal
scheme in the site is a parameter.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0CP6.** A directed inverse system `(B_i)_{i ∈ I}` of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms `B_{i'} ⟶ B_i` for `i ≤ i'`. Its limit
`B = lim_i B_i` is `AlgebraicGeometry.Space.NoetherianSpaceSystem.limit`, an algebraic space by
`AlgebraicGeometry.Space.NoetherianSpaceSystem.isAlgebraicSpace_limit` (Stacks 07SF).

The field `indexSize` is the chapter's standing convention (Stacks 07SD) that the rings it
considers have their spectra in the site, stated for the fixed size cutoff of the site. -/
@[stacks 0CP6]
structure NoetherianSpaceSystem (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] where
  /-- The inverse system `(B_i)` of presheaves on the big fppf site over `S`. -/
  system : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- The index set is small compared to the cofinality of the site's size cutoff (the
  convention of Stacks 07SD for the fixed site). -/
  indexSize : #I < B.cutoff.ord.cof
  /-- Every member of the system is an algebraic space over `S`. -/
  system_isAlgebraicSpace : ∀ i : I, IsAlgebraicSpace B S hS (system.obj (op i))
  /-- Every member of the system is Noetherian. -/
  noetherian : ∀ i : I, IsNoetherian B S hS hZ (system.obj (op i))
  /-- Every transition morphism of the system is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom B S hS (system.map f)

namespace NoetherianSpaceSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)] (D : NoetherianSpaceSystem B S hS hZ I)

/-- The limit `B = lim_i B_i` of the system, formed in presheaves on the big fppf site
over `S`. -/
noncomputable def limit : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  Limits.limit D.system

/-- The projection `B ⟶ B_i` from the limit to a member of the system. -/
noncomputable def limitπ (i : I) : D.limit ⟶ D.system.obj (op i) :=
  Limits.limit.π D.system (op i)

include D in
/-- The bound on the index set, transported to the opposite category indexing the system. -/
theorem indexSize_op : #Iᵒᵖ < B.cutoff.ord.cof := by
  rw [Cardinal.mk_congr (Opposite.equivToOpposite (α := I)).symm]
  exact D.indexSize

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The hom-sets of the opposite of a preorder have at most one element, hence lie below the
cofinality of the site's size cutoff. -/
theorem homSize_op (i j : Iᵒᵖ) : #(i ⟶ j) < B.cutoff.ord.cof :=
  (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans_lt
    (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

/-- **Stacks 07SF.** The limit `B = lim_i B_i` of the system is an algebraic space over `S`. -/
theorem isAlgebraicSpace_limit : IsAlgebraicSpace B S hS D.limit :=
  Space.isAlgebraicSpace_limit B S hS D.system D.indexSize_op homSize_op
    (fun i => D.system_isAlgebraicSpace i.unop) D.transition_affine

/-- **Stacks 07SF, part (1).** Each projection `B ⟶ B_i` is affine. -/
theorem isAffineHom_limitπ (i : I) : IsAffineHom B S hS (D.limitπ i) :=
  Space.isAffineHom_limitπ B S hS D.system D.indexSize_op homSize_op D.transition_affine (op i)

/-- The system together with its limit cone, whose point is an algebraic space by Stacks 07SF,
as an `AlgebraicGeometry.Space.NoetherianLimitSystem`. -/
noncomputable def toNoetherianLimitSystem : NoetherianLimitSystem B S hS hZ I where
  system := D.system
  system_isAlgebraicSpace := D.system_isAlgebraicSpace
  noetherian := D.noetherian
  transition_affine := D.transition_affine
  limitCone := Limits.limit.cone D.system
  isLimit := Limits.limit.isLimit D.system
  limit_isAlgebraicSpace := D.isAlgebraicSpace_limit

/-- The point of the limit cone of `D.toNoetherianLimitSystem` is the limit `D.limit`. -/
@[simp]
theorem toNoetherianLimitSystem_limitCone_pt :
    D.toNoetherianLimitSystem.limitCone.pt = D.limit :=
  rfl

end NoetherianSpaceSystem

end AlgebraicGeometry.Space

end
