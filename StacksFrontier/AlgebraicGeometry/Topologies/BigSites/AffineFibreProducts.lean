module

public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks

/-!
# Affine iterated fibre products in a localized big site

Fix one of the five big sites `B` of a topology `τ`, localize it at a scheme `S` of the site and
let `U` be an object of the localization whose total space is affine.  For a family in the
localization all of whose members have affine total space, each iterated fibre product
`U_{i₀} ×_U ⋯ ×_U U_{iₙ}` again has affine total space.

The fibre products in question are the finite products of the slice of the localized site at
`U` — two slice levels above schemes — so the statement is transported down to the slice of all
schemes at the scheme underlying `U`, where it is the statement that a finite product of schemes
affine over an affine base is affine.

## Main definitions

* `AlgebraicGeometry.overToScheme`: the functor from a localized big site to all schemes, taking
  an object to its total space.

## Main results

* `AlgebraicGeometry.isAffine_overScheme_piObj`: an iterated fibre product of objects with
  affine total space over an object with affine total space has affine total space.
* `AlgebraicGeometry.overStandardCoverings_covObjects`: the hypothesis `hCovObjects` of
  `Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor` for the data
  `AlgebraicGeometry.overAffineObjects` and `AlgebraicGeometry.overStandardCoverings`, all three
  of its clauses.

## Implementation notes

No `@[stacks]` attribute is attached: this is the Lean-side transport of
`AlgebraicGeometry.isAffineHom_over_finiteProduct` through two slice levels, not the content of a
tag.

The transport is along `AlgebraicGeometry.overToScheme`, and only *cospan* limits need to be
preserved: `Stacks.Sites.preservesLimit_fibreProducts_overPost` builds preservation of the
iterated fibre products of a family out of preservation of the single fibre products of its
members, by induction on the length of the tuple.  That is what makes the transport available
uniformly in `τ`, since the inclusion of a big site into all schemes is known to preserve fibre
products — `AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan` — while
preservation of all finite limits is not available at this generality.

## References

* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
  (hS : S.size < cutoff τ B)

/-- The functor from a localized big site to all schemes, taking an object to the total space of
its structure morphism with its size bound forgotten.  Unlike
`AlgebraicGeometry.overToSlice` it forgets the base `S` as well, which is what makes it
preserve fibre products. -/
public abbrev overToScheme : Over (base B S hS) ⥤ Scheme.{u} :=
  Over.forget (base B S hS) ⋙ schemeBelowInclusion (cutoff τ B)

/-- **The third clause of `hCovObjects`.**  An iterated fibre product, in a localized big site,
of objects with affine total space over an object with affine total space again has affine total
space.

The product is taken in the slice of the localized site at `U`.  Pushing it forward along
`AlgebraicGeometry.overToScheme` lands in the slice of all schemes at the affine scheme
underlying `U`, and that functor preserves it, so the total space of the product is the product
of the total spaces; the latter is affine because each of the structure morphisms
`overScheme (E.X i) ⟶ overScheme U` is a morphism of affines, hence affine. -/
public theorem isAffine_overScheme_piObj {U : Over (base B S hS)}
    (hU : IsAffine (overScheme τ B S hS U)) (E : PreZeroHypercover.{u} U)
    (hX : ∀ i, IsAffine (overScheme τ B S hS (E.X i))) (p : ℕ)
    (i : Fin (p + 1) → E.I₀) :
    IsAffine (overScheme τ B S hS (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left) := by
  let u : Over (base B S hS) ⥤ Scheme.{u} := overToScheme τ B S hS
  let A : Fin (p + 1) → Over U := fun a ↦ Over.mk (E.f (i a))
  have : IsAffine (u.obj U) := hU
  have : PreservesLimit (Discrete.functor A) (Over.post (X := U) u) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost u E
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
  have hF : ∀ a, IsAffineHom ((Over.post (X := U) u).obj (A a)).hom := fun a ↦ by
    have : IsAffine ((Over.post (X := U) u).obj (A a)).left := hX (i a)
    exact isAffineHom_of_isAffine _
  let P := ∏ᶜ (fun a ↦ (Over.post (X := U) u).obj (A a))
  have : IsAffineHom P.hom := isAffineHom_over_finiteProduct _ hF
  have : IsAffine P.left := isAffine_of_isAffineHom P.hom
  have e : overScheme τ B S hS (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left ≅ P.left :=
    (Over.forget (u.obj U)).mapIso (PreservesProduct.iso (Over.post (X := U) u) A)
  exact IsAffine.of_isIso e.hom

/-- **`hCovObjects` for a localized big site.**  The target of an over-standard `τ`-covering,
each of its members, and each of its iterated fibre products is an object with affine total
space.  This is the hypothesis `hCovObjects` of
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor` verbatim, for the
data `AlgebraicGeometry.overAffineObjects` and `AlgebraicGeometry.overStandardCoverings` and the
products supplied by `AlgebraicGeometry.overStandardCoverings_hasProducts`. -/
public theorem overStandardCoverings_covObjects :
    ∀ {U : Over (base B S hS)}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ overTopology τ B S hS U })
      (hE : E ∈ overStandardCoverings τ B S hS U),
      U ∈ overAffineObjects τ B S hS ∧ (∀ i, E.1.X i ∈ overAffineObjects τ B S hS) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
              overStandardCoverings_hasProducts τ B S hS E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ overAffineObjects τ B S hS := by
  intro U E hE
  obtain ⟨hU, hX⟩ := IsOverStandardCovering.isAffine τ B S hS hE
  exact ⟨hU, hX, fun p i ↦ isAffine_overScheme_piObj τ B S hS hU E.1 hX p i⟩

end AlgebraicGeometry

end
