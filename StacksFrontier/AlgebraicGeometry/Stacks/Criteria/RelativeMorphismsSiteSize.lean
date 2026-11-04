module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsRepresentableTarget

/-!
# The big fppf site contains the representing objects of the relative morphism functor

`AlgebraicGeometry.Space.RelativeHomRepresentableTarget` carries the relative morphism functor of
Stacks 05Y2 at an arbitrary representable target subject to
`AlgebraicGeometry.Space.RelativeHomRepresentingContained`: the condition that the big fppf site
of `S` contain every object of the category of schemes over the scheme underlying `V` which
represents the relative morphism functor `Mor_V(Z, X)` of Stacks 0BL2. This file proves that
condition.

The size cutoff of a big fppf site is a strong prelimit of uncountable cofinality above `ℵ₀`, so
it suffices to exhibit the representing object as glued from pieces no larger than the data, along
an index type no larger than the data. Both are what
`Stacks.Morphisms.homFromFiniteLocallyFree_representableBy` provides: the representing object of
Stacks 0BL4 is covered by the affine charts of Stacks 0BL3, one for each pair of an affine open
of the base and an affine open of the target above it, and each chart is the spectrum of a ring
of cardinality at most that of the global sections of those two affine opens. An affine open of
a scheme of the site has at most as many sections as the scheme has size, and a scheme has at
most as many affine opens as its size, so one cardinal below the cutoff bounds the charts and
the index type at once.

A representing object is unique up to isomorphism over the base, and
`AlgebraicGeometry.Scheme.size_congr` transports the bound, so the condition holds of *every*
representing object and not only of the one Stacks 0BL4 builds.

## Main results

* `AlgebraicGeometry.Space.contains_relativeHomRepresenting`: the site contains every object
  representing `Mor_V(Z, X)`, for a finite locally free `z` and a target at which Stacks 0BL4
  produces a representing object — that is, under the fibrewise hypothesis Stacks 0BL4 asks.
* `AlgebraicGeometry.Space.relativeHomRepresentingContained`:
  `AlgebraicGeometry.Space.RelativeHomRepresentingContained` holds for every morphism of the site
  whose underlying morphism of schemes is finite locally free.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank'`:
  the relative morphism functor of Stacks 05Y2 at an arbitrary representable target is an
  algebraic space over `S`, with no hypothesis beyond finite local freeness of rank `d` of the
  morphism of schemes underlying `z`.

## Implementation notes

The empty index type has to be treated separately, because the open-cover bound
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_size_le` is stated for a nonempty one. It
is not a degenerate case to be dismissed: `Mor_V(Z, X)` is empty whenever `X` is, and then there
is no chart at all. An empty scheme has size at most `ℵ₀`, which is below the cutoff.

No `@[stacks]` attribute is placed here: the bound is a statement about the size cutoff of the
site, which is Stacks 000Q and Stacks 000R, already registered where those bounds are proved.

## References

* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
* [Stacks Project, Tag 0BL2](https://stacks.math.columbia.edu/tag/0BL2)
* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {V Zs : BigFppfOver B S hS}

/-- **An affine open of a scheme has at most as many global sections as the scheme has size.** -/
private theorem mk_sections_affineOpen_le_size (X : Scheme.{u}) (U : X.affineOpens) :
    #Γ(U.1.toScheme, ⊤) ≤ X.size := by
  have _ : IsAffine (U.1.toScheme) := U.2
  refine le_trans ?_ (Scheme.size_coe_opens_le X U.1)
  rw [Scheme.size_of_isAffine]
  exact le_max_right _ _

/-- **The big fppf site of `S` contains every object representing a relative morphism functor of
Stacks 0BL2 attached to a finite locally free `z`.**

The representing object Stacks 0BL4 builds is covered by the affine charts of Stacks 0BL3, whose
number and whose sizes are both bounded by the sizes of the scheme underlying the base and of the
scheme underlying the target, both of which are below the cutoff of the site. Every representing
object is isomorphic to that one over the base, so the bound holds of all of them.

The hypothesis on the target is the one Stacks 0BL4 itself asks, in
`Stacks.Morphisms.homFromFiniteLocallyFree_representableBy`: it is only the finite sets of points
of `X` lying in a single fibre of `x` that have to lie in an affine open of `X`. A morphism `x`
affine over the base supplies it outright, by the argument of
`Stacks.Morphisms.relativeHom_representableBy_affineHom`. -/
theorem contains_relativeHomRepresenting (z : Zs ⟶ V)
    [Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z)]
    {Xs : BigFppfOver B S hS} (x : Xs ⟶ V)
    (hXaff : ∀ (s : (BigFppfOver.toScheme B S hS).obj V)
      (t : Set ((BigFppfOver.toScheme B S hS).obj Xs)), t.Finite →
      (∀ p ∈ t, ((BigFppfOver.toScheme B S hS).map x).base p = s) →
      ∃ O : ((BigFppfOver.toScheme B S hS).obj Xs).Opens, IsAffineOpen O ∧ t ⊆ O)
    (W : Over ((BigFppfOver.toScheme B S hS).obj V))
    (e : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map z))
        (Over.mk ((BigFppfOver.toScheme B S hS).map x))).RepresentableBy W) :
    B.Contains W.left := by
  obtain ⟨W₀, ι, Y, a, hι, hY, haopen, hcov, ⟨e₀⟩⟩ :=
    Stacks.Morphisms.homFromFiniteLocallyFree_representableBy
      ((BigFppfOver.toScheme B S hS).map z) ((BigFppfOver.toScheme B S hS).map x) hXaff
  have _ : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (a i) := haopen
  have hWiso : W.left ≅ W₀.left :=
    (Over.forget _).mapIso (yoneda.preimageIso
      (Functor.representableByEquiv e ≪≫ (Functor.representableByEquiv e₀).symm))
  refine (Scheme.size_congr hWiso).trans_lt ?_
  -- a cardinal below the cutoff bounding the sizes of the two schemes of the data
  obtain ⟨μ, hVμ, hXμ, hμ, haleph⟩ : ∃ μ : Cardinal.{u},
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ ∧
      ((BigFppfOver.toScheme B S hS).obj Xs).size ≤ μ ∧ μ < B.cutoff ∧ ℵ₀ ≤ μ :=
    ⟨_, le_max_left _ _, le_max_right _ _, max_lt V.left.property Xs.left.property,
      (Scheme.aleph0_le_size _).trans (le_max_left _ _)⟩
  -- the affine opens of a scheme of size at most `μ`, and their sections, are bounded by `μ`
  have hT : ∀ T : Scheme.{u}, T.size ≤ μ →
      #T.affineOpens ≤ μ ∧ ∀ U : T.affineOpens, #Γ(U.1.toScheme, ⊤) ≤ μ := fun T h =>
    ⟨(Scheme.mk_affineOpens_le_size _).trans h,
      fun U => (mk_sections_affineOpen_le_size _ U).trans h⟩
  have hYsize : ∀ i, (Y i).size ≤ μ := by
    intro i
    obtain ⟨Q, _, Vo, Uo, hQ, ⟨eQ⟩⟩ := hY i
    refine (Scheme.size_congr eQ).trans_le ?_
    rw [Scheme.size_Spec]
    exact max_le haleph (hQ.trans (sup_le (sup_le ((hT _ hXμ).2 _) ((hT _ hVμ).2 _)) haleph))
  have hιμ : #ι ≤ μ :=
    hι.trans (sup_le (sup_le (hT _ hVμ).1 (hT _ hXμ).1) haleph)
  rcases isEmpty_or_nonempty ι with hιe | hιn
  · have _ : IsEmpty W₀.left := ⟨fun y => (hcov y).elim fun i _ => hιe.elim i⟩
    have eE : W₀.left ≅ (∅ : Scheme.{u}) :=
      (isInitialOfIsEmpty (X := W₀.left)).uniqueUpToIso emptyIsInitial
    exact lt_of_le_of_lt ((Scheme.size_congr eE).trans_le Scheme.size_empty_le_aleph0)
      B.aleph0_lt_cutoff
  · exact B.contains_of_openCover_of_size_le hμ hιμ a hcov hYsize

/-- **The big fppf site of `S` contains the representing objects of the relative morphism
functors of Stacks 0BL2 attached to a finite locally free `z`.**

A finite set of points of `X` inside a single fibre of `x` is in particular a finite set of
points of `X`, so `AlgebraicGeometry.Space.contains_relativeHomRepresenting` applies. -/
theorem relativeHomRepresentingContained (z : Zs ⟶ V)
    [Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z)] :
    RelativeHomRepresentingContained B S hS z :=
  fun _ x hXaff W e =>
    contains_relativeHomRepresenting z x (fun _ t ht _ => hXaff t ht) W e

/-- **The relative morphism functor of Stacks 05Y2 at an arbitrary representable target is an
algebraic space.** Let `V`, `Z` and `X` be objects of the big fppf site of `S`, let `z : Z ⟶ V`
be a morphism of the site whose underlying morphism of schemes is finite locally free of
rank `d`, and let `u : yoneda X ⟶ yoneda V` be a morphism of presheaves. Then
`Mor_{yoneda V}(yoneda Z, yoneda X)` is an algebraic space over `S`.

This is
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank`
with its condition on the site discharged by
`AlgebraicGeometry.Space.relativeHomRepresentingContained`. -/
theorem isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank'
    {Xs : BigFppfOver B S hS} (z : Zs ⟶ V) (u : yoneda.obj Xs ⟶ yoneda.obj V) (d : ℕ)
    [hzr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map z) d] :
    IsAlgebraicSpace B S hS
      (relativeHom B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) u (isAlgebraicSpace_yoneda B S hS Zs)
        (isAlgebraicSpace_yoneda B S hS Xs) (isAlgebraicSpace_yoneda B S hS V)) :=
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank z u d
    (relativeHomRepresentingContained z)

end AlgebraicGeometry.Space

end
