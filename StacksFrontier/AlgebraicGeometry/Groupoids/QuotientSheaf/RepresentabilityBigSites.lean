module

public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.Representability
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous

/-!
# The representability criterion for a quotient sheaf on the big `τ`-sites

`Stacks.Groupoids.isIso_quotientSheafToPoints` proves Stacks 03C5 for a site of `S`-schemes
presented by an arbitrary functor, and asks as a hypothesis that the functor of points of the
candidate representing scheme `M` be a sheaf. For the big site of `S` carrying any of the five
topologies of `AlgebraicGeometry.SiteKind` — Zariski, étale, smooth, syntomic, fppf — that
hypothesis is not an assumption but a theorem: all five topologies are coarser than the fppf
one, the inclusion of the site into all `S`-schemes is continuous for the fppf topology, and
the localized fppf topology on `Sch/S` is subcanonical. This file discharges the hypothesis
and states the criterion with it removed, for all five topologies at once.

## Main results

* `Stacks.Groupoids.isSheaf_points_of_isContinuous`: the restricted functor of points of an
  arbitrary `S`-scheme is a sheaf for any topology on a site of `S`-schemes whose presenting
  functor is continuous into a subcanonical topology on `Sch/S`.
* `Stacks.Groupoids.isSheaf_points_baseOver`: the restricted functor of points of an arbitrary
  `S`-scheme is a sheaf for each of the five topologies of the big site of `S`.
* `Stacks.Groupoids.isIso_quotientSheafToPoints_baseOver`: **Stacks 03C5** for each of the five
  topologies, with no sheaf hypothesis on `M`.

## Implementation notes

The scheme `M` is *not* assumed to be an object of the site, so the sheaf condition for its
functor of points is not subcanonicality of the site: a scheme over `S` whose size exceeds the
cutoff of the big site is not an object of it, and its functor of points is not a representable
presheaf on the site. It is continuity of the inclusion `Sch_κ/S ⥤ Sch/S`, applied to the
presheaf represented by `M`, which is a sheaf because the localized fppf topology on `Sch/S` is
subcanonical. `Stacks.Groupoids.isSheaf_points_of_isContinuous` is the generic form of that
argument, and `AlgebraicGeometry.BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj` is its
instance at the fppf topology of the big site. The other four topologies are coarser than the
fppf one — `AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf` — and a sheaf for a finer
topology is a sheaf for a coarser one.

Sheafification of presheaves of `Type u` on the big site over `S` is not an instance, because
the objects of the site lie one universe above the sections, but it is a theorem,
`AlgebraicGeometry.BigFppfOver.hasSheafify_type_baseOver`. It is installed below as a local
instance, so that the criterion carries no hypothesis beyond the equalizing condition and the
two surjectivity conditions of the source.

## References

* [Stacks Project, Tag 03C5](https://stacks.math.columbia.edu/tag/03C5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Groupoids

/-- **The restricted functor of points of an arbitrary `S`-scheme is a sheaf on a continuously
presented site.** If the functor presenting a site of `S`-schemes is continuous for a
subcanonical topology on `Sch/S`, then the restriction along it of the presheaf represented by
any `S`-scheme is a sheaf.

Neither fullness nor faithfulness of the presenting functor is needed, and the scheme is not
assumed to lie in its image. For a *fully faithful* presenting functor and a scheme which *is*
in its image, the weaker hypothesis of subcanonicality of the site itself suffices, and that is
`Stacks.Groupoids.isSheaf_points_obj`. -/
theorem isSheaf_points_of_isContinuous {C : Type v} [Category.{u} C] {S : Scheme.{u}}
    (J : GrothendieckTopology C) (K : GrothendieckTopology (Over S)) [K.Subcanonical]
    (F : C ⥤ Over S) [F.IsContinuous J K] (M : Over S) :
    Presheaf.IsSheaf J (points F M) :=
  F.op_comp_isSheaf_of_isSheaf J K _
    ((isSheaf_iff_isSheaf_of_type K _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := K) _))

section BaseOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind)

/-- Presheaves of `Type u` sheafify on the big site over `S` for each of the five topologies.
This is `AlgebraicGeometry.BigFppfOver.hasSheafify_type_baseOver`, installed as an instance for
the statements of this section only. -/
local instance hasSheafifyTypeBaseOver :
    HasSheafify (BigFppfOver.baseOverTopology B S hS τ) (Type u) :=
  BigFppfOver.hasSheafify_type_baseOver B S hS τ

/-- **The restricted functor of points of an arbitrary `S`-scheme is a `τ`-sheaf**, for each of
the five topologies of the big site of `S`.

For the fppf topology this is
`AlgebraicGeometry.BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj`, which is
`Stacks.Groupoids.isSheaf_points_of_isContinuous` at the inclusion `Sch_κ/S ⥤ Sch/S`; the other
four topologies are coarser, by
`AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf`. -/
theorem isSheaf_points_baseOver (M : Over S) :
    Presheaf.IsSheaf (BigFppfOver.baseOverTopology B S hS τ)
      (points (Over.post (X := B.obj hS) B.inclusion) M) :=
  Presheaf.IsSheaf.of_le (BigFppfOver.baseOverTopology_le_fppf B S hS τ)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS M)

/-- **Stacks 03C5.** Let `τ` be one of the Zariski, étale, smooth, syntomic and fppf
topologies, let `j : R ⟶ U ×_S U` be a pre-relation of `S`-schemes, and let `f : U ⟶ M` be a
morphism of `S`-schemes equalizing its source and its target. If `f` induces a surjection of
`τ`-sheaves on the functors of points, and if `(t, s) : R ⟶ U ×_M U` induces one too, then `M`
represents the quotient sheaf `U/R`: the canonical map `U/R ⟶ h_M` is an isomorphism.

The source's three hypotheses are `hf`, `hU` and `hR`, in that order. Nothing is assumed about
the functor of points of `M`: it is a `τ`-sheaf by
`Stacks.Groupoids.isSheaf_points_baseOver`, and neither `M` nor `R` is assumed to be an object
of the site. -/
@[stacks 03C5]
theorem isIso_quotientSheafToPoints_baseOver {R U M : Over S} (j : PreRelation R U) (f : U ⟶ M)
    (hf : j.target ≫ f = j.source ≫ f)
    (hU : Presheaf.IsLocallySurjective (BigFppfOver.baseOverTopology B S hS τ)
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map f)))
    (hR : Presheaf.IsLocallySurjective (BigFppfOver.baseOverTopology B S hS τ)
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (pullback.lift j.target j.source hf)))) :
    IsIso (quotientSheafToPoints (BigFppfOver.baseOverTopology B S hS τ)
      (Over.post (X := B.obj hS) B.inclusion) j f hf
      (isSheaf_points_baseOver B S hS τ M)) :=
  isIso_quotientSheafToPoints _ _ j f hf _ hU hR

end BaseOver

end Stacks.Groupoids

end
