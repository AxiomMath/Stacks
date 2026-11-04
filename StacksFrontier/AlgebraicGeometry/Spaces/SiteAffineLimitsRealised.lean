module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps

/-!
# Cofiltered limits of affine objects of the big fppf site, without an index bound

A cofiltered inverse system `V` of affine objects of the big fppf site of `S` need not have
a limit in the site: the limit exists in schemes, because a cofiltered limit of affine
schemes does, but the site is the full subcategory of schemes of size below a cutoff
cardinal, and the limit can escape that cutoff.

`AlgebraicGeometry.BigFppfOver.hasLimit_of_isAffine` rules this out with a hypothesis on
the *index category*, `#J < B.cutoff.ord.cof`, which forces the limit to stay below the
cutoff by a cofinality argument. That hypothesis is not the mathematical content: it is one
sufficient condition for the single fact that is really used, namely that the limit scheme
is itself below the cutoff. This file isolates that fact as a predicate and reproves the
consequences from it.

The point of the refactoring is that the index bound is often unavailable while the
conclusion is not. For a system of affine open neighbourhoods of a point of a scheme `S` of
the site there is no bound at all on the number of stages, yet the limit is
`Spec 𝒪_{S,s}`, whose size is bounded directly by that of `S` because the cutoff is a
strong prelimit. Such a system satisfies `RealisedAffineLimit` and fails `#J < cutoff.cof`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.RealisedAffineLimit`: the limit of the underlying diagram
  of schemes is below the site's cutoff, i.e. the site sees the limit.

## Main results

* `AlgebraicGeometry.BigFppfOver.realisedAffineLimit_of_mk_lt`: the index bound implies
  `RealisedAffineLimit`, so everything below generalizes the index-bounded statements.
* `AlgebraicGeometry.BigFppfOver.hasLimit_of_realisedAffineLimit`,
  `AlgebraicGeometry.BigFppfOver.preservesLimit_toScheme_of_realisedAffineLimit` and
  `AlgebraicGeometry.BigFppfOver.isAffine_toScheme_of_isLimit_of_realised`: the three
  conclusions of the index-bounded development, from `RealisedAffineLimit` alone.
-/

@[expose] public section

open Cardinal CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A cofiltered inverse system `V` of objects of the big fppf site of `S` has a
**realised affine limit** when the limit of the underlying diagram of schemes, which exists
as soon as the stages are affine, is again of size below the site's cutoff — that is, when
the limit scheme is an object of the site.

This is exactly the content for which the index bound `#J < B.cutoff.ord.cof` of
`AlgebraicGeometry.BigFppfOver.hasLimit_of_isAffine` is used, stated directly. It is
phrased for an arbitrary limit cone rather than for the chosen limit so that it can be
checked against whichever cone is at hand. -/
def RealisedAffineLimit (V : J ⥤ BigFppfOver B S hS) : Prop :=
  ∀ c : Cone (V ⋙ BigFppfOver.toScheme B S hS), IsLimit c → c.pt.size < B.cutoff

/-- An index category smaller than the cofinality of the site's cutoff realises the limit
of any cofiltered system of affine objects. This is the cofinality argument of
`AlgebraicGeometry.Scheme.size_lt_of_isLimit_of_isAffine`, and it shows that every
statement below generalizes its index-bounded counterpart. -/
theorem realisedAffineLimit_of_mk_lt (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hJ : #J < B.cutoff.ord.cof) : RealisedAffineLimit V := fun _ hc =>
  Scheme.size_lt_of_isLimit_of_isAffine B.aleph0_lt_cutoff
    (V ⋙ BigFppfOver.toScheme B S hS) hV hJ (fun j => (V.obj j).left.property) hc

omit [IsCofiltered J] in
/-- The diagram of schemes underlying a cofiltered diagram of affine objects of the site
has a limit. No size hypothesis is involved: this is the existence of cofiltered limits of
affine schemes. -/
theorem hasLimit_toScheme (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j))) :
    HasLimit ((V ⋙ BigFppfOver.forget B S hS) ⋙ B.inclusion) :=
  have : ∀ j, IsAffine (((V ⋙ BigFppfOver.forget B S hS) ⋙ B.inclusion).obj j) := hV
  CofilteredLimit.hasLimit_of_isAffine ((V ⋙ BigFppfOver.forget B S hS) ⋙ B.inclusion)

/-- The size-bounded subcategory of schemes creates the limit of the diagram of schemes
underlying a cofiltered diagram of affine objects of the site, as soon as the system
realises its affine limit. -/
@[instance_reducible]
noncomputable def createsLimitInclusion_of_realised (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hR : RealisedAffineLimit V) :
    CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion :=
  have _hlim : HasLimit ((V ⋙ BigFppfOver.forget B S hS) ⋙ B.inclusion) :=
    hasLimit_toScheme V hV
  have hsize : schemeSizeBelow B.cutoff
      (limit ((V ⋙ BigFppfOver.forget B S hS) ⋙ B.inclusion)) :=
    hR _ (limit.isLimit ((V ⋙ BigFppfOver.forget B S hS) ⋙ B.inclusion))
  Limits.createsLimitFullSubcategoryInclusion _ hsize

/-- The diagram of schemes-over-`B.obj hS` underlying a cofiltered system of affine objects
which realises its affine limit has a limit. -/
private theorem hasLimit_forget_of_realised (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hR : RealisedAffineLimit V) : HasLimit (V ⋙ BigFppfOver.forget B S hS) := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  have := hasLimit_toScheme V hV
  have := createsLimitInclusion_of_realised V hV hR
  exact hasLimit_of_created _ B.inclusion

/-- A cofiltered inverse system of affine objects of the big fppf site of `S` which
realises its affine limit has a limit in the site.

This is `AlgebraicGeometry.BigFppfOver.hasLimit_of_isAffine` with the hypothesis on the
index category replaced by the size statement that hypothesis was used to prove. -/
theorem hasLimit_of_realisedAffineLimit (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hR : RealisedAffineLimit V) : HasLimit V := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  have := hasLimit_forget_of_realised V hV hR
  exact hasLimit_of_created V (Over.forget (B.obj hS))

/-- The underlying scheme functor preserves the limit of a cofiltered inverse system of
affine objects of the site which realises its affine limit. -/
theorem preservesLimit_toScheme_of_realisedAffineLimit (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hR : RealisedAffineLimit V) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  have := hasLimit_toScheme V hV
  have := createsLimitInclusion_of_realised V hV hR
  have := hasLimit_forget_of_realised V hV hR
  infer_instance

/-- The underlying scheme of a limit of a cofiltered inverse system of affine objects of
the site which realises its affine limit is affine. -/
theorem isAffine_toScheme_of_isLimit_of_realised (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hR : RealisedAffineLimit V) {c : Cone V} (hc : IsLimit c) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) := by
  have := preservesLimit_toScheme_of_realisedAffineLimit V hV hR
  have haff : ∀ j, IsAffine ((V ⋙ BigFppfOver.toScheme B S hS).obj j) := hV
  exact Scheme.isAffine_of_isLimit _ (isLimitOfPreserves (BigFppfOver.toScheme B S hS) hc)

/-- A limit cone in the site of a cofiltered system of affine objects which realises its
affine limit is sent by the underlying-scheme functor to a limit cone of schemes. This is
the form in which the finite-presentation machinery consumes the limit. -/
noncomputable def isLimitMapCone_toScheme_of_realised (V : J ⥤ BigFppfOver B S hS)
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hR : RealisedAffineLimit V) {c : Cone V} (hc : IsLimit c) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) :=
  have := preservesLimit_toScheme_of_realisedAffineLimit V hV hR
  isLimitOfPreserves (BigFppfOver.toScheme B S hS) hc

end BigFppfOver

end AlgebraicGeometry

end
