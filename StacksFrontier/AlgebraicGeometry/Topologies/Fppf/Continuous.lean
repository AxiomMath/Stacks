module

public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# The inclusion of a big fppf site into all schemes is continuous

A functor between sites is *continuous* when restriction along it preserves sheaves. This
file proves that the inclusion `Sch_κ ⥤ Sch` of the underlying category of a big fppf site
into all schemes is continuous for the chosen fppf covering families and the fppf topology,
and deduces the same for the induced functor `Sch_κ/S ⥤ Sch/S` on slices. Consequently the
restriction to the big fppf site of `S` of the functor of points of an arbitrary `S`-scheme is
a sheaf.

## Main results

* `AlgebraicGeometry.BigFppfSite.isContinuous_inclusion`: the inclusion of the underlying
  category of a big fppf site into all schemes is continuous.
* `AlgebraicGeometry.BigFppfOver.isContinuous_post_inclusion`: the induced functor on
  slices over a contained scheme is continuous for the localized topologies.
* `AlgebraicGeometry.BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj`: the restricted
  functor of points of an arbitrary `S`-scheme is a sheaf on the big fppf site of `S`.

## References

* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 00WW](https://stacks.math.columbia.edu/tag/00WW)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfSite

/-- The chosen covering families of a big fppf site generate fppf covering sieves of
schemes. -/
theorem precoverage_le_comap_fppfTopology (B : BigFppfSite.{u}) :
    B.precoverage ≤ Scheme.fppfTopology.toPrecoverage.comap B.inclusion := by
  rintro X _ ⟨E, rfl, hE⟩
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff]
  exact Precoverage.generate_mem_toGrothendieck hE.1

/-- The inclusion of the underlying category of a big fppf site into all schemes is
continuous: restriction along it takes a sheaf for the fppf topology on schemes to a sheaf
for the chosen fppf covering families. -/
instance isContinuous_inclusion (B : BigFppfSite.{u}) :
    B.inclusion.IsContinuous B.topology Scheme.fppfTopology := by
  have hcomap : B.inclusion.IsContinuous
      (Scheme.fppfTopology.toPrecoverage.comap B.inclusion).toGrothendieck
      Scheme.fppfTopology.toPrecoverage.toGrothendieck :=
    Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy _ _ _ le_rfl
  refine ⟨fun P ↦ (isSheaf_iff_isSheaf_of_type _ _).mp ?_⟩
  refine Presheaf.IsSheaf.of_le
    (Precoverage.toGrothendieck_mono B.precoverage_le_comap_fppfTopology)
    (B.inclusion.op_comp_isSheaf_of_isSheaf _ Scheme.fppfTopology.toPrecoverage.toGrothendieck
      P.obj ?_)
  exact Presheaf.IsSheaf.of_le
    (GrothendieckTopology.toGrothendieck_toPrecoverage_le Scheme.fppfTopology) P.property

/-- The inclusion of the underlying category of a big fppf site into all schemes preserves
`1`-hypercovers of the size of the site. -/
instance preservesOneHypercovers_inclusion (B : BigFppfSite.{u}) :
    Functor.PreservesOneHypercovers.{u + 1} B.inclusion B.topology Scheme.fppfTopology :=
  Functor.PreservesOneHypercovers.of_coverPreserving (CoverPreserving.of_isContinuous _ _ _)

end BigFppfSite

section Over

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace BigFppfOver

/-- The functor from the big fppf site of `S` to all `S`-schemes is continuous for the
localized fppf topologies. -/
instance isContinuous_post_inclusion :
    (Over.post (X := B.obj hS) B.inclusion).IsContinuous (BigFppfOver.topology B S hS)
      (Scheme.fppfTopology.over S) :=
  inferInstanceAs ((Over.post (X := B.obj hS) B.inclusion).IsContinuous
    (BigFppfOver.topology B S hS)
    (Scheme.fppfTopology.over (B.inclusion.obj (B.obj hS))))

/-- The restricted functor of points of an arbitrary `S`-scheme is a sheaf on the big fppf
site of `S`; the scheme `R` need not belong to the site. -/
theorem isSheaf_post_inclusion_op_comp_yoneda_obj (R : Over S) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      ((Over.post B.inclusion).op ⋙ yoneda.obj R) :=
  (Over.post (X := B.obj hS) B.inclusion).op_comp_isSheaf_of_isSheaf
    (BigFppfOver.topology B S hS) (Scheme.fppfTopology.over S) _
    ((isSheaf_iff_isSheaf_of_type (Scheme.fppfTopology.over S) _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.fppfTopology.over S) _))

end BigFppfOver

end Over

end AlgebraicGeometry

end
