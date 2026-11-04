module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# The big étale site is subcanonical

A Grothendieck topology is *subcanonical* when every representable presheaf is a sheaf for
it. The étale topology on the category of *all* schemes is coarser than the fppf topology,
which Mathlib knows to be subcanonical, so subcanonicality of the étale topology on all
schemes is immediate. A big étale site is not that topology: it is carried by the
size-bounded full subcategory `Sch_κ` of schemes with a *chosen* set-sized system of
covering families, so the statement has to be transported along the inclusion.

The transport is an instance of the general statement
`CategoryTheory.Precoverage.subcanonical_toGrothendieck_of_fullyFaithful`, proved for the big
fppf site, whose own documentation records that the big étale site is built the same way and
can reuse it: a precoverage on a category with fibre products, whose covering families become
covering families under a fully faithful functor preserving fibre products, and each of whose
base changes is refined by a covering family, generates a subcanonical topology as soon as
the target precoverage does. The two inputs are supplied by material already in place: a
chosen étale covering family of `Sch_κ` is an fppf covering family of schemes by
`AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage`, and the refinement is the
base-change axiom stored in `AlgebraicGeometry.BigEtaleSite.coverings_isSite`, read at the
level of presieves.

## Main results

* `AlgebraicGeometry.BigEtaleSite.exists_mem_precoverage_factorsThruAlong`: the base change
  of a chosen covering family of a big étale site is refined by a chosen covering family.
* `AlgebraicGeometry.BigEtaleSite.subcanonical_topology`: the topology of a big étale site is
  subcanonical.
* `AlgebraicGeometry.BigEtaleSite.isSheaf_yoneda_obj`: the sheaf condition for a representable
  presheaf, in the form in which it is usually consumed.
* `AlgebraicGeometry.BigEtaleOver.subcanonical_topology`: the topology of the big étale site
  of a scheme contained in a big étale site is subcanonical.

## Implementation notes

The corresponding statement for the *small* étale site of a contained scheme is
`AlgebraicGeometry.SmallEtale.topology_subcanonical`, proved independently by descent of
morphisms of schemes along an étale covering; it is not derived from the statement here.

## References

* [Stacks Project, Tag 021A](https://stacks.math.columbia.edu/tag/021A)
* [Stacks Project, Tag 021C](https://stacks.math.columbia.edu/tag/021C)
* [Stacks Project, Tag 021N](https://stacks.math.columbia.edu/tag/021N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigEtaleSite

/-- The coverage axiom for the chosen covering families of a big étale site: the base change
of a chosen covering family along any morphism of the site is refined by a chosen covering
family.

This is the base-change axiom `AlgebraicGeometry.BigEtaleSite.coverings_isSite` read at the
level of presieves. The fibre products it produces need not be the chosen fibre products of
`Sch_κ`, which is why the conclusion is a refinement rather than an equality of presieves. -/
theorem exists_mem_precoverage_factorsThruAlong (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (f : Y ⟶ X) (R : Presieve X) (hR : R ∈ B.precoverage X) :
    ∃ T ∈ B.precoverage Y, T.FactorsThruAlong R f := by
  obtain ⟨E, rfl, hE⟩ := hR
  obtain ⟨P, π₁, π₂, hpb, hcov⟩ := B.coverings_isSite.2.2 ⟨X, E⟩ hE Y f
  refine ⟨(⟨E.I₀, P, π₂⟩ : PreZeroHypercover.{u + 1} Y).presieve₀,
    ⟨⟨E.I₀, P, π₂⟩, rfl, hcov⟩, ?_⟩
  rintro Z g ⟨i⟩
  exact ⟨E.X i, π₁ i, E.f i, ⟨i⟩, (hpb i).w⟩

/-- The topology of a big étale site is subcanonical: every representable presheaf on `Sch_κ`
is a sheaf for the chosen étale covering families.

The inclusion `Sch_κ ⥤ Sch` is fully faithful and preserves fibre products, and a chosen
étale covering family becomes an fppf covering family of schemes, so this is Mathlib's
subcanonicality of the fppf topology on all schemes transported along the inclusion. -/
instance subcanonical_topology (B : BigEtaleSite.{u}) : B.topology.Subcanonical :=
  B.precoverage.subcanonical_toGrothendieck_of_fullyFaithful Scheme.fppfPrecoverage
    B.inclusion
    (fun _ _ hR => by
      obtain ⟨_, rfl, hE⟩ := hR
      have h := Scheme.etalePrecoverage_le_fppfPrecoverage _ hE.etale
      rwa [PreZeroHypercover.presieve₀_map] at h)
    B.exists_mem_precoverage_factorsThruAlong

/-- A representable presheaf on the underlying category of a big étale site is a sheaf.

This is `AlgebraicGeometry.BigEtaleSite.subcanonical_topology` in the `Presheaf.IsSheaf` form
in which the sheaf condition is usually stated. -/
theorem isSheaf_yoneda_obj (B : BigEtaleSite.{u}) (X : B.Scheme) :
    Presheaf.IsSheaf B.topology (yoneda.obj X) :=
  (isSheaf_iff_isSheaf_of_type _ _).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end BigEtaleSite

namespace BigEtaleOver

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The localization at a contained scheme `S` of the topology of a big étale site is
subcanonical.

The localization of a subcanonical topology is subcanonical, so this is
`AlgebraicGeometry.BigEtaleSite.subcanonical_topology`. -/
instance subcanonical_topology : (B.topology.over (B.obj S hS)).Subcanonical :=
  inferInstance

/-- A representable presheaf on the localization at `S` of a big étale site is a sheaf. -/
theorem isSheaf_yoneda_obj (X : CategoryTheory.Over (B.obj S hS)) :
    Presheaf.IsSheaf (B.topology.over (B.obj S hS)) (yoneda.obj X) :=
  (isSheaf_iff_isSheaf_of_type _ _).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end BigEtaleOver

end AlgebraicGeometry
