module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# The inclusion of a big fppf site into all schemes is cocontinuous

A functor `G` between sites is *cocontinuous* when every covering sieve of `G X` pulls back
to a covering sieve of `X`. This file proves that the inclusion `Sch_κ ⥤ Sch` of the
underlying category of a big fppf site into all schemes is cocontinuous for the chosen fppf
covering families and the *Zariski* topology on all schemes, and deduces the same for the
canonical functor `Sch_κ/S ⥤ Sch` out of the big fppf site of a contained scheme.

Cocontinuity is the direction that `Topologies/Fppf/Continuous.lean` does not give. The two
are independent: continuity says that restriction along the inclusion carries sheaves to
sheaves, cocontinuity that it carries *locally bijective* morphisms of presheaves to locally
bijective ones
(`CategoryTheory.Presheaf.isLocallyInjective_whisker` and
`CategoryTheory.Presheaf.isLocallySurjective_whisker`). The second is what moves a statement
proved on the category of all schemes — where colimits of presheaves of sets exist at every
size and no cutoff intervenes — onto the big fppf site of a base scheme.

The Zariski topology is the right source topology here, and not a convenience: cocontinuity
over a *finer* topology on all schemes is a stronger statement, and the pullback of an
arbitrary fppf covering sieve of a contained scheme need not contain a chosen covering
family of the site. A Zariski covering sieve does, because the members of an open covering
of a contained scheme are themselves contained
(`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion`) and a Zariski covering is an fppf
covering, which is `AlgebraicGeometry.exists_isCovering_tautologicallyEquivalent_openCover`.
Since the Zariski topology is coarser than the fppf and fpqc topologies, this is also the
form in which the statement composes with the local bijectivity available on schemes, which
is proved for the Zariski topology.

## Main results

* `AlgebraicGeometry.BigFppfSite.isCocontinuous_inclusion_zariskiTopology`: the inclusion of
  the underlying category of a big fppf site into all schemes is cocontinuous for the
  Zariski topology on schemes.
* `AlgebraicGeometry.BigFppfOver.isCocontinuous_toScheme_zariskiTopology`: the canonical
  functor from the big fppf site of a contained scheme to all schemes is cocontinuous.

## Implementation notes

The slice step is Mathlib's: `CategoryTheory.Over.forget` is cocontinuous from the localized
topology to the topology it is localized from, and cocontinuous functors compose, so nothing
beyond the statement for the inclusion itself has to be proved.

## References

* [Stacks Project, Tag 00XJ](https://stacks.math.columbia.edu/tag/00XJ)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 03WX](https://stacks.math.columbia.edu/tag/03WX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigFppfSite

/-- **The inclusion of a big fppf site into all schemes is cocontinuous** for the Zariski
topology on schemes: a Zariski covering sieve of a contained scheme pulls back to a covering
sieve of the site.

Given a Zariski covering sieve, choose an open covering of the scheme refining it. Each
member of the covering is contained in the site, the covering is an fppf covering, and so it
is tautologically equivalent to one of the site's own chosen covering families by Stacks
03WX; that family generates a covering sieve of the site, and each of its members factors
through a member of the open covering, hence lies in the pullback of the given sieve. -/
instance isCocontinuous_inclusion_zariskiTopology (B : BigFppfSite.{u}) :
    B.inclusion.IsCocontinuous B.topology Scheme.zariskiTopology.{u} where
  cover_lift {T} {R} hR := by
    obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hR
    obtain ⟨V, hV, htaut⟩ := exists_isCovering_tautologicallyEquivalent_openCover B T 𝒰
    refine B.topology.superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck
        (show V.presieve₀ ∈ B.precoverage T from ⟨V, rfl, hV⟩))
    rw [Sieve.generate_le_iff]
    rintro W g ⟨i⟩
    obtain ⟨β, hβ⟩ := htaut.2
    obtain ⟨e, he⟩ := hβ i
    change R (B.inclusion.map (V.f i))
    rw [show B.inclusion.map (V.f i) = e.hom ≫ 𝒰.f (β i) from he.symm]
    exact R.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk (β i))) e.hom

end BigFppfSite

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The canonical functor from the big fppf site of `S` to all schemes is cocontinuous**
for the Zariski topology on schemes.

It is the composite of the forgetful functor of the slice, which is cocontinuous for the
localized topology by Mathlib, with the inclusion of the site into all schemes, which is
`AlgebraicGeometry.BigFppfSite.isCocontinuous_inclusion_zariskiTopology`. -/
instance isCocontinuous_toScheme_zariskiTopology :
    (BigFppfOver.toScheme B S hS).IsCocontinuous (BigFppfOver.topology B S hS)
      Scheme.zariskiTopology.{u} :=
  isCocontinuous_comp (BigFppfOver.forget B S hS) B.inclusion
    (BigFppfOver.topology B S hS) B.topology

end BigFppfOver

end AlgebraicGeometry

end
