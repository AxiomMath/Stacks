module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EquivalenceOfSites

/-!
# The small étale site is invariant under isomorphism of the base presheaf

Let `B` be a big fppf site containing a scheme `S`, and let `e : F ≅ G` be an isomorphism of
presheaves on the big fppf site of `S`.  Composition with `e` carries an étale chart of `F` to
an étale chart of `G` without changing its source, and this is an isomorphism of sites: it is
an equivalence of categories, it matches the two small étale precoverages exactly, and it
commutes on the nose with the projections to the big fppf site of `S`, to `Sch_κ` and with the
structure presheaf of global regular functions.

The point of the statement is that the small étale site of an algebraic space depends only on
the isomorphism class of the presheaf.  In particular, for a *representable* algebraic space
`F ≅ h_T` it identifies the small étale site of `F` with that of `h_T`, which is the first step
in comparing `𝒪_F`-modules with modules on the representing scheme.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.congr` is the equivalence
  `SmallEtale B S hS F ≌ SmallEtale B S hS G` induced by `e : F ≅ G`.

## Main results

* `AlgebraicGeometry.Space.isEtaleChart_comp_iso_iff` and
  `AlgebraicGeometry.Space.isEtaleChart_inverseImage_mapIso`: a scheme chart of `F` is étale
  exactly when its composite with `e` is an étale chart of `G`.
* `AlgebraicGeometry.Space.SmallEtale.congr_functor_comp_toOver` and
  `AlgebraicGeometry.Space.SmallEtale.congr_functor_comp_toSchemes`: the equivalence does not
  change the object of the big fppf site, nor the scheme, underlying a chart.
* `AlgebraicGeometry.Space.SmallEtale.congr_precoverage_eq_comap`: the small étale precoverage
  of `F` is the precoverage of `G` pulled back along the equivalence.
* `AlgebraicGeometry.Space.SmallEtale.congr_functor_coverPreserving` and
  `AlgebraicGeometry.Space.SmallEtale.congr_inverse_coverPreserving`: both directions carry
  small étale coverings to small étale coverings.
* `AlgebraicGeometry.Space.SmallEtale.congr_functor_isDenseSubsite`: the equivalence exhibits
  the small étale site of `F` as a dense subsite of that of `G`, which is what transports
  sheaves, and sheaves of modules, between the two sites.
* `AlgebraicGeometry.Space.SmallEtale.congr_topology`: the small étale topology of `F` is the
  topology induced from that of `G`.
* `AlgebraicGeometry.Space.SmallEtale.congr_functor_op_comp_structurePresheaf`: the structure
  presheaf of `F` is that of `G` restricted along the equivalence.

## Implementation notes

An étale chart of `F` is a `CategoryTheory.CostructuredArrow yoneda F` cut out by the property
`AlgebraicGeometry.Space.IsEtaleChart`, so the underlying equivalence of scheme charts is
Mathlib's `CategoryTheory.CostructuredArrow.mapIso`, which post-composes the structure morphism
with `e.hom` and leaves its source untouched.  That the étale-chart condition is transported
both ways is `CategoryTheory.MorphismProperty.relative_respectsIso`: the condition is
`CategoryTheory.MorphismProperty.presheaf` of a property, and every such property respects
isomorphisms.  The equivalence of the full subcategories is then
`CategoryTheory.Equivalence.congrFullSubcategory`.

Because the underlying object of a chart is unchanged, both compatibility statements with the
projections hold by `CategoryTheory.Functor.hext` with `rfl` on objects and morphisms, and the
comparison of topologies is correspondingly short: the small étale precoverage is the chosen
étale precoverage of `Sch_κ` restricted along the projection to schemes
(`AlgebraicGeometry.Space.SmallEtale.precoverage_eq_comap`), so matching the two precoverages
is `CategoryTheory.Precoverage.comap_comp` applied to that compatibility.  Cover preservation
in both directions is then read off the generating families with
`CategoryTheory.coverPreserving_of_generators`, which exhibits the equivalence as a dense
subsite and identifies the restricted topology with the induced one — the same route as
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Composing an étale chart with an isomorphism of the target presheaf gives an étale chart,
and conversely: the étale-chart condition is `CategoryTheory.MorphismProperty.presheaf` of a
property, and such a property respects isomorphisms. -/
theorem isEtaleChart_comp_iso_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ F) :
    IsEtaleChart B S hS G (CostructuredArrow.mk (φ ≫ e.hom)) ↔
      IsEtaleChart B S hS F (CostructuredArrow.mk φ) :=
  MorphismProperty.cancel_right_of_respectsIso
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
    φ e.hom

/-- The étale charts of `F` are exactly the scheme charts of `F` whose composite with `e` is an
étale chart of `G`. -/
theorem isEtaleChart_inverseImage_mapIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    (IsEtaleChart B S hS G).inverseImage (CostructuredArrow.mapIso e).functor =
      IsEtaleChart B S hS F := by
  funext X
  exact propext (isEtaleChart_comp_iso_iff B S hS e X.hom)

namespace SmallEtale

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)

/-- An isomorphism `e : F ≅ G` of presheaves on the big fppf site of `S` induces an equivalence
of small étale sites, by composing the structure morphism of a chart with `e`. -/
def congr : SmallEtale B S hS F ≌ SmallEtale B S hS G :=
  Equivalence.congrFullSubcategory (CostructuredArrow.mapIso e)
    (isEtaleChart_inverseImage_mapIso B S hS e)

/-- The equivalence of small étale sites does not change the object of the big fppf site of `S`
underlying a chart. -/
theorem congr_functor_comp_toOver :
    (congr B S hS e).functor ⋙ toOver B S hS G = toOver B S hS F :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- Read backwards: the inverse equivalence does not change the object of the big fppf site of
`S` underlying a chart either. -/
theorem congr_inverse_comp_toOver :
    (congr B S hS e).inverse ⋙ toOver B S hS F = toOver B S hS G :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The equivalence of small étale sites does not change the scheme underlying a chart. -/
theorem congr_functor_comp_toSchemes :
    (congr B S hS e).functor ⋙ toSchemes B S hS G = toSchemes B S hS F :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The inverse equivalence does not change the scheme underlying a chart. -/
theorem congr_inverse_comp_toSchemes :
    (congr B S hS e).inverse ⋙ toSchemes B S hS F = toSchemes B S hS G :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The small étale precoverage of `F` is the small étale precoverage of `G` restricted along
the equivalence: both are the chosen étale precoverage of `Sch_κ` pulled back along the
projection to schemes, and the equivalence commutes with that projection. -/
theorem congr_precoverage_eq_comap :
    precoverage B S hS F = (precoverage B S hS G).comap (congr B S hS e).functor := by
  rw [precoverage_eq_comap, precoverage_eq_comap, ← Precoverage.comap_comp,
    congr_functor_comp_toSchemes]

/-- The equivalence of small étale sites is cover preserving: a covering family of charts of
`F` is carried to one of `G`, because the two precoverages are generated by the same families
of schemes. -/
theorem congr_functor_coverPreserving :
    CoverPreserving (topology B S hS F) (topology B S hS G) (congr B S hS e).functor :=
  coverPreserving_toGrothendieck_of_isCovering _ (precoverage B S hS F) (precoverage B S hS G)
    (IsCovering B S hS F) (IsCovering B S hS G) (fun _ _ => mem_precoverage_iff B S hS F)
    (fun _ _ => mem_precoverage_iff B S hS G) (fun _ _ h => h)

/-- The inverse equivalence of small étale sites is cover preserving, by the same argument. -/
theorem congr_inverse_coverPreserving :
    CoverPreserving (topology B S hS G) (topology B S hS F) (congr B S hS e).inverse :=
  coverPreserving_toGrothendieck_of_isCovering _ (precoverage B S hS G) (precoverage B S hS F)
    (IsCovering B S hS G) (IsCovering B S hS F) (fun _ _ => mem_precoverage_iff B S hS G)
    (fun _ _ => mem_precoverage_iff B S hS F) (fun _ _ h => h)

/-- The equivalence of small étale sites is an isomorphism of sites. -/
private theorem congr_isIsoOfSites :
    (congr B S hS e).IsIsoOfSites (topology B S hS F) (topology B S hS G) :=
  ⟨congr_functor_coverPreserving B S hS e, congr_inverse_coverPreserving B S hS e⟩

/-- The inverse equivalence of small étale sites is cocontinuous: it is adjoint to a cover
preserving functor. -/
theorem congr_inverse_isCocontinuous :
    (congr B S hS e).inverse.IsCocontinuous (topology B S hS G) (topology B S hS F) :=
  (congr_isIsoOfSites B S hS e).inverse_isCocontinuous

/-- The equivalence of small étale sites is cocontinuous. -/
theorem congr_functor_isCocontinuous :
    (congr B S hS e).functor.IsCocontinuous (topology B S hS F) (topology B S hS G) :=
  (congr_isIsoOfSites B S hS e).functor_isCocontinuous

/-- The equivalence of small étale sites is continuous, so restriction of sheaves along it is
defined. -/
theorem congr_functor_isContinuous :
    (congr B S hS e).functor.IsContinuous (topology B S hS F) (topology B S hS G) :=
  (congr_isIsoOfSites B S hS e).functor_isContinuous

/-- The equivalence exhibits the small étale site of `F` as a dense subsite of that of `G`.
This is the hypothesis under which the Comparison Lemma transports sheaves, and sheaves of
modules, between the two sites. -/
theorem congr_functor_isDenseSubsite :
    (congr B S hS e).functor.IsDenseSubsite (topology B S hS F) (topology B S hS G) :=
  (congr_isIsoOfSites B S hS e).functor_isDenseSubsite

/-- A sieve on a chart of `F` is a small étale covering exactly when the sieve it generates on
the corresponding chart of `G` is. -/
theorem congr_functor_restrictedTopology :
    (congr B S hS e).functor.restrictedTopology (topology B S hS G) = topology B S hS F :=
  (congr_isIsoOfSites B S hS e).functor_restrictedTopology

/-- The small étale topology of `F` is the topology induced along the equivalence from the
small étale topology of `G`. -/
theorem congr_topology :
    (congr B S hS e).functor.inducedTopology (topology B S hS G) = topology B S hS F :=
  (congr_isIsoOfSites B S hS e).functor_inducedTopology

/-- The presheaf of global regular functions on the small étale site of `F` is the one on the
small étale site of `G` restricted along the equivalence: the equivalence does not change the
scheme underlying a chart. -/
theorem congr_functor_op_comp_structurePresheaf :
    (congr B S hS e).functor.op ⋙ structurePresheaf B S hS G = structurePresheaf B S hS F :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

end SmallEtale

end AlgebraicGeometry.Space

end
