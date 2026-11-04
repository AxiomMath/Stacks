module

public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine objects cover the final object of the small pro-étale site

Let `T` be an object of a chosen big pro-étale site. The objects of the small pro-étale site of
`T` whose underlying scheme is affine cover the final object of that site: for every weakly étale
object `X / T`, the affine opens of the underlying scheme of `X` are again objects of the small
site, and they present a covering family of `X`.

The point is that this is a statement about the *chosen* covering families of the small site,
which carry the index bound `AlgebraicGeometry.ProEtale.BigProetaleSite.coveringBound`. The bound
is no obstruction, by
`AlgebraicGeometry.ProEtale.SmallProetale.precoverage_eq_comap`: a presieve of the small site is
covering as soon as its image in schemes is a pro-étale covering. A Zariski cover by affine opens
is such a covering, because the pro-étale precoverage is coarser than the Zariski one, weak
étaleness containing the identities and being Zariski local at the source.

## Main definitions

* `AlgebraicGeometry.ProEtale.SmallProetale.affineCoverObject` — an affine open of the underlying
  scheme of an object of the small pro-étale site, as an object of that site.
* `AlgebraicGeometry.ProEtale.SmallProetale.affineCoverMap` — its open immersion into that object.

## Main results

* `AlgebraicGeometry.ProEtale.SmallProetale.coversTop_affine` — the affine objects of the small
  pro-étale site cover its final object.

## Implementation notes

The affine opens used are the ones chosen by `AlgebraicGeometry.Scheme.affineCover`, so the index
type of the covering family of `X` is the underlying topological space of the underlying scheme of
`X`. The source of such an open immersion lies in the chosen big site by
`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion`, and is weakly étale over `T` because an
open immersion is weakly étale and weak étaleness is stable under composition.

## References

* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

/-- **A Zariski covering of schemes is a pro-étale covering.** Weak étaleness contains the
identities and is Zariski local at the source, so `AlgebraicGeometry.Scheme.proetalePrecoverage`,
being the quasi-compact precoverage attached to it, is coarser than the Zariski precoverage. -/
theorem zariskiPrecoverage_le_proetalePrecoverage :
    AlgebraicGeometry.Scheme.zariskiPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.proetalePrecoverage.{u} := by
  have : MorphismProperty.ContainsIdentities @WeaklyEtale :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  exact AlgebraicGeometry.Scheme.zariskiPrecoverage_le_propQCPrecoverage

namespace SmallProetale

variable (B : BigProetaleSite.{u}) (T : B.Scheme)
  (X : SmallProetale B T.obj T.property)

/-- The source of the `i`-th map of the chosen affine cover of the underlying scheme of an object
`X` of the small pro-étale site, as an object of the chosen big pro-étale site. It lies in the
chosen big site because it is the source of an open immersion into one of its objects. -/
def affineCoverScheme (i : ((toScheme B T.obj T.property).obj X).affineCover.I₀) : B.Scheme :=
  ⟨((toScheme B T.obj T.property).obj X).affineCover.X i,
    Scheme.size_lt_of_isOpenImmersion
      (((toScheme B T.obj T.property).obj X).affineCover.f i) X.obj.left.property⟩

/-- The `i`-th map of the chosen affine cover of the underlying scheme of `X`, as a morphism of
the chosen big pro-étale site. -/
def affineCoverSchemeHom (i : ((toScheme B T.obj T.property).obj X).affineCover.I₀) :
    affineCoverScheme B T X i ⟶ X.obj.left :=
  ObjectProperty.homMk (((toScheme B T.obj T.property).obj X).affineCover.f i)

/-- The `i`-th map of the chosen affine cover of the underlying scheme of `X`, viewed in the
chosen big pro-étale site, is an open immersion. -/
instance (i : ((toScheme B T.obj T.property).obj X).affineCover.I₀) :
    IsOpenImmersion (B.inclusion.map (affineCoverSchemeHom B T X i)) :=
  inferInstanceAs (IsOpenImmersion (((toScheme B T.obj T.property).obj X).affineCover.f i))

/-- An affine open of the underlying scheme of an object `X` of the small pro-étale site of `T`,
as an object of that site: its structure morphism to `T` is the open immersion into `X` followed
by the structure morphism of `X`, which is weakly étale because an open immersion is. -/
def affineCoverObject (i : ((toScheme B T.obj T.property).obj X).affineCover.I₀) :
    SmallProetale B T.obj T.property :=
  ⟨Over.mk (affineCoverSchemeHom B T X i ≫ X.obj.hom), by
    change WeaklyEtale (B.inclusion.map (affineCoverSchemeHom B T X i ≫ X.obj.hom))
    have h : WeaklyEtale (B.inclusion.map X.obj.hom) := X.property
    rw [Functor.map_comp]
    infer_instance⟩

/-- The open immersion of an affine open of the underlying scheme of `X` into `X`, as a morphism
of the small pro-étale site of `T`. -/
def affineCoverMap (i : ((toScheme B T.obj T.property).obj X).affineCover.I₀) :
    affineCoverObject B T X i ⟶ X :=
  ObjectProperty.homMk (Over.homMk (affineCoverSchemeHom B T X i) rfl)

/-- The underlying scheme of `affineCoverObject B T X i` is affine. -/
instance isAffine_affineCoverObject
    (i : ((toScheme B T.obj T.property).obj X).affineCover.I₀) :
    IsAffine ((toScheme B T.obj T.property).obj (affineCoverObject B T X i)) :=
  inferInstanceAs (IsAffine (((toScheme B T.obj T.property).obj X).affineCover.X i))

/-- **The affine opens of an object of the small pro-étale site cover it.** The presieve generated
by the chosen affine cover of the underlying scheme of `X` is a covering presieve of `X` in the
small pro-étale site of `T`.

The index bound of the chosen big site is discharged by
`AlgebraicGeometry.ProEtale.SmallProetale.mem_precoverage_of_map_mem`, and the image presieve is a
pro-étale covering because it is a Zariski covering and
`AlgebraicGeometry.Scheme.zariskiPrecoverage_le_propQCPrecoverage` applies to weak étaleness. -/
theorem ofArrows_affineCoverObject_mem_precoverage :
    Presieve.ofArrows (affineCoverObject B T X) (affineCoverMap B T X) ∈
      precoverage B T.obj T.property X := by
  refine mem_precoverage_of_map_mem B T ?_
  rw [Presieve.map_ofArrows]
  exact zariskiPrecoverage_le_proetalePrecoverage _
    ((toScheme B T.obj T.property).obj X).affineCover.mem₀

/-- **Affine objects cover the final object of the small pro-étale site.** The family of all
objects of the small pro-étale site of `T` whose underlying scheme is affine covers the final
object of that site.

This is the covering family that the Zariski reduction of Stacks 09AA asks for: over its members
the direct image along a closed immersion is the affine case of Stacks 09BL. -/
theorem coversTop_affine :
    (topology B T.obj T.property).CoversTop
      (Subtype.val : {Y : SmallProetale B T.obj T.property //
        IsAffine ((toScheme B T.obj T.property).obj Y)} →
          SmallProetale B T.obj T.property) := by
  intro X
  refine (topology B T.obj T.property).superset_covering
    (le_trans (Sieve.ofArrows_le_ofObjects _ (affineCoverMap B T X))
      (Sieve.ofObjects_mono ?_))
    (Precoverage.generate_mem_toGrothendieck
      (ofArrows_affineCoverObject_mem_precoverage B T X))
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨affineCoverObject B T X i, inferInstance⟩, rfl⟩

end SmallProetale

end AlgebraicGeometry.ProEtale

end
