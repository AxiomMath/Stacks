module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularIdealSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Defs

/-!
# The small étale site of an algebraic space is locally ringed

The small étale site of an algebraic space `F` over a scheme `S`, with its structure sheaf of
global regular functions, is a locally ringed site: the sections `0` and `1` of the structure
sheaf are nowhere equal, and every section is, on some étale covering, either a unit or has
unit complement.

Both conditions are read off the stalks.  The geometric points are a conservative family of
points of the small étale site, and the stalk of the structure sheaf at the point of the site
determined by a geometric point is the étale local ring, which is local.  Feeding these two
facts to the stalk criterion `AlgebraicGeometry.RingedSite.isLocallyRinged_of_local_stalks`
gives the result.

## Main results

* `AlgebraicGeometry.Space.isLocalRing_presheafFiber_structurePresheaf`: the stalk of the
  structure sheaf at the point of the small étale site determined by a geometric point is a
  local ring.
* `AlgebraicGeometry.Space.smallEtaleRingedSite_isLocallyRinged`: the small étale ringed site
  of an algebraic space is locally ringed.
* `AlgebraicGeometry.Scheme.mem_basicOpen_or_mem_basicOpen_one_sub`: every point of a scheme
  lies in the nonvanishing locus of a global function or in that of its complement, because the
  local ring at the point is a local ring.
* `AlgebraicGeometry.Space.locallyEitherUnit_structureSheaf'` and
  `AlgebraicGeometry.Space.locallyEitherUnit_smallEtaleRingedSite`: the local-unit conjunct of
  the locally ringed condition, proved for the structure sheaf of the small étale site of an
  *arbitrary* presheaf, so with no algebraicity hypothesis and no stalk theory of the site.

## Implementation notes

The stalk at a point of the site takes its sections in `CommRingCat.{u}`, whereas the étale
local ring of Stacks 04KG is a colimit over the étale neighbourhoods of the geometric point,
a category whose objects live in `Type (u + 1)`, and so takes its values in
`CommRingCat.{u + 1}`.  The two are compared by raising the rings of sections one universe
with `AlgebraicGeometry.commRingULiftFunctor`, which preserves filtered colimits and therefore
commutes with the stalk, and by the equivalence
`AlgebraicGeometry.Space.neighborhoodFiberElementsEquiv` between the étale neighbourhoods and
the elements of the geometric fibre, which identifies the two colimit shapes.

## References

* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- Every point of a scheme lies either in the nonvanishing locus of a global regular function
or in the nonvanishing locus of its complement, because the local ring at that point is a local
ring and in a local ring one of `a`, `1 - a` is a unit. -/
theorem mem_basicOpen_or_mem_basicOpen_one_sub (Y : Scheme.{u}) (a : Γ(Y, ⊤)) (z : Y) :
    z ∈ Y.basicOpen a ∨ z ∈ Y.basicOpen (1 - a) := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
      ((Y.presheaf.germ ⊤ z trivial).hom a) with h | h
  · exact Or.inl ((Y.mem_basicOpen_top a z).mpr h)
  · exact Or.inr ((Y.mem_basicOpen_top (1 - a) z).mpr (by simpa using h))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space

/-- Raising the rings of sections one universe preserves filtered colimits: the forgetful
functor of `CommRingCat` does, in either universe, and it reflects isomorphisms. -/
private theorem commRingULiftFunctor_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u} commRingULiftFunctor.{u, u + 1} := by
  have : HasColimitsOfSize.{u, u} CommRingCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  refine ⟨fun J _ _ => ⟨fun {K} => ?_⟩⟩
  let G := forget CommRingCat.{u + 1}
  have : PreservesFilteredColimitsOfSize.{u, u} G :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have : ReflectsColimit (K ⋙ commRingULiftFunctor.{u, u + 1}) G :=
    reflectsColimit_of_reflectsIsomorphisms _ G
  have : PreservesColimit K (commRingULiftFunctor.{u, u + 1} ⋙ G) := by
    show PreservesColimit K (forget CommRingCat.{u} ⋙ uliftFunctor.{u + 1, u})
    infer_instance
  exact preservesColimit_of_reflects_of_preserves commRingULiftFunctor.{u, u + 1} G

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The stalk of the structure sheaf of the small étale site of an algebraic space, taken at
the point of the site determined by a geometric point, is a local ring.

It is the étale local ring of Stacks 04KG at that geometric point, up to a universe lift of
the rings of sections, and that ring is local by Stacks 08AH. -/
theorem isLocalRing_presheafFiber_structurePresheaf (x : GeometricPoint B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    IsLocalRing (((etaleSitePoint B S hS F x hF).presheafFiber (A := CommRingCat.{u})).obj
      (structurePresheaf B S hS F)) := by
  have : HasColimitsOfSize.{u, u} CommRingCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : HasColimitsOfShape (geometricFiber B S hS F x).Elementsᵒᵖ CommRingCat.{u + 1} :=
    hasColimitsOfShape_of_equivalence
      (AsSmall.equiv.{u, u + 1, u + 1}
        (C := (geometricFiber B S hS F x).Elementsᵒᵖ)).symm
  have := commRingULiftFunctor_preservesFilteredColimits.{u}
  let p := etaleSitePoint B S hS F x hF
  let R := structurePresheaf B S hS F
  let L := liftedStructurePresheaf B S hS F
  let e := neighborhoodFiberElementsEquiv B S hS F x
  let D : (geometricFiber B S hS F x).Elementsᵒᵖ ⥤ CommRingCat.{u + 1} :=
    (CategoryOfElements.π (geometricFiber B S hS F x)).op ⋙ L
  have hlocal : IsLocalRing ((p.presheafFiber (A := CommRingCat.{u + 1})).obj L) := by
    have : IsLocalRing (colimit (C := CommRingCat.{u + 1}) (e.functor.op ⋙ D)) :=
      isLocalRing_etaleLocalRing B S hS F hF x
    exact (Functor.Final.colimitIso e.functor.op D).commRingCatIsoToRingEquiv.isLocalRing
  have : IsLocalRing (((Functor.whiskeringRight _ _ _).obj commRingULiftFunctor.{u, u + 1} ⋙
      p.presheafFiber).obj R) := hlocal
  have : IsLocalRing (ULift.{u + 1} ((p.presheafFiber (A := CommRingCat.{u})).obj R)) :=
    ((p.presheafFiberCompIso commRingULiftFunctor.{u, u + 1}).app R).commRingCatIsoToRingEquiv
      |>.isLocalRing
  exact (ULift.ringEquiv :
    ULift.{u + 1} ((p.presheafFiber (A := CommRingCat.{u})).obj R) ≃+* _).isLocalRing

/-- **Stacks Project, Tag 04KH.** The small étale site of an algebraic space, endowed with its
structure sheaf, is a locally ringed site. -/
@[stacks 04KH]
theorem smallEtaleRingedSite_isLocallyRinged (hF : IsAlgebraicSpace B S hS F) :
    RingedSite.IsLocallyRinged (smallEtaleRingedSite B S hS F hF) := by
  apply RingedSite.isLocallyRinged_of_local_stalks (smallEtaleRingedSite B S hS F hF)
    (ObjectProperty.ofObj (fun x => etaleSitePoint B S hS F x hF))
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS F hF)
  rintro _ ⟨x⟩
  exact isLocalRing_presheafFiber_structurePresheaf B S hS F x hF

/-! ### The local-unit condition without an algebraicity hypothesis -/

/-- A global function on an étale chart becomes a unit when the chart is restricted to the
nonvanishing locus of that function. -/
theorem isUnit_res_chartBasicOpen (U : SmallEtale B S hS F)
    (b : (structureSheaf' B S hS F).obj.obj (op U)) :
    IsUnit (((structureSheaf' B S hS F).obj.map
      (chartOpenRestrictionHom B S hS F U
        (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen b)).op) b) := by
  have h := chartOpenRestrictionHom_toScheme B S hS F U
    (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen b)
  show IsUnit ((Scheme.Γ.map
    ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map
      (chartOpenRestrictionHom B S hS F U _)).op) b)
  rw [h]
  let Y := (BigFppfOver.toScheme B S hS).obj U.obj.left
  show IsUnit ((Y.presheaf.map
    (homOfLE (x := (Y.basicOpen b).ι ''ᵁ ⊤) le_top).op) b)
  rw [Scheme.Opens.ι_image_top]
  exact Y.toRingedSpace.isUnit_res_basicOpen b

/-- A point of an étale chart lying in the nonvanishing locus of a global function on the chart
lifts through the restriction of the chart to that locus. -/
theorem exists_lift_chartBasicOpen (U : SmallEtale B S hS F)
    (b : (structureSheaf' B S hS F).obj.obj (op U))
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U))
    (hz : z ∈ ((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen b) :
    ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
        (chartOpenRestriction B S hS F U
          (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen b))),
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
        (chartOpenRestrictionHom B S hS F U
          (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen b))) z' = z := by
  refine ⟨⟨z, hz⟩, ?_⟩
  have h : (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map
        (chartOpenRestrictionHom B S hS F U
          (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen b))) =
      (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen b).ι :=
    chartOpenRestrictionHom_toScheme B S hS F U _
  rw [h]
  rfl

/-- Every global regular function on an étale chart of a presheaf is, on a covering of that
chart, either a unit or has unit complement.

The covering is by the two basic opens of the function and of its complement, which cover the
chart because the local ring at every point of a scheme is a local ring; no algebraicity
hypothesis and no stalk theory of the site is used, which is what distinguishes this from the
corresponding conjunct of `AlgebraicGeometry.Space.smallEtaleRingedSite_isLocallyRinged`. -/
theorem locallyEitherUnit_structureSheaf' :
    RingedSite.LocallyEitherUnit (J := SmallEtale.topology B S hS F)
      (structureSheaf' B S hS F) := by
  intro U a
  refine ⟨⟨fun {V} g => IsUnit (((structureSheaf' B S hS F).obj.map g.op) a) ∨
      IsUnit (((structureSheaf' B S hS F).obj.map g.op) (1 - a)), ?_⟩, ?_, fun V g hg => hg⟩
  · intro V W g hg k
    have hm : ∀ x : (structureSheaf' B S hS F).obj.obj (op U),
        IsUnit (((structureSheaf' B S hS F).obj.map g.op) x) →
          IsUnit (((structureSheaf' B S hS F).obj.map (k ≫ g).op) x) := by
      intro x h
      simp only [op_comp, Functor.map_comp]
      exact h.map (ConcreteCategory.hom ((structureSheaf' B S hS F).obj.map k.op))
    exact hg.imp (hm a) (hm (1 - a))
  · apply smallEtale_sieve_of_pointwise_covering B S hS F U
    intro z
    rcases Scheme.mem_basicOpen_or_mem_basicOpen_one_sub _ a z with hz | hz
    · exact ⟨_, chartOpenRestrictionHom B S hS F U _,
        Or.inl (isUnit_res_chartBasicOpen B S hS F U a),
        exists_lift_chartBasicOpen B S hS F U a z hz⟩
    · exact ⟨_, chartOpenRestrictionHom B S hS F U _,
        Or.inr (isUnit_res_chartBasicOpen B S hS F U (1 - a)),
        exists_lift_chartBasicOpen B S hS F U (1 - a) z hz⟩

/-- Every section of the structure sheaf of the small étale ringed site of an algebraic space is
locally either a unit or has unit complement. -/
theorem locallyEitherUnit_smallEtaleRingedSite (hF : IsAlgebraicSpace B S hS F) :
    RingedSite.LocallyEitherUnit (smallEtaleRingedSite B S hS F hF).O :=
  locallyEitherUnit_structureSheaf' B S hS F

end AlgebraicGeometry.Space

end
