module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAmbientAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionEnlargedPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargement
public import StacksCore.Tactic.StacksAttribute

/-!
# Square-zero extensions of the étale structure sheaf are realized after enlarging the site

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` for a big fppf site `B`, and let
`0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of `𝒪_X` on `X_ét` by a quasi-coherent
`ℐ`, with `𝒜` an `f⁻¹𝒪_Y`-algebra (`AlgebraicGeometry.Space.SquareZeroExtension`). Stacks 05ZT
asserts that it is the structure sheaf of a first-order thickening `X ⊂ X'` over `Y`. On a big
fppf site of a fixed size this is false (see the docstring of
`AlgebraicGeometry.Space.SquareZeroExtension.nonempty_enlargedRealization`); what holds, and is
proved here, is the statement after enlarging the big fppf site: there is a big fppf site `B'`
containing `B` to which `X`, `Y`, `f` and the extension transport, and on which the transported
extension is realized.

The proof transports a charted presentation of `f` to a site containing the thickenings of its
two presenting charts (`AlgebraicGeometry.SiteEnlargement.transportChartedPresentation`), whose
transported thickened charts it then also contains
(`AlgebraicGeometry.SiteEnlargement.contains_chartThickening_transportPresentationChart`), and
applies the realization on a site containing the thickened charts
(`AlgebraicGeometry.Space.SquareZeroExtension.nonempty_realization`).

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.EnlargedRealization`: a realization after
  enlarging the big fppf site.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.nonempty_enlargedRealization`: Stacks 05ZT, in its
  corrected form.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A realization of a square-zero extension after enlarging the big fppf site**: a big fppf
site `B'` containing `B` and the base scheme, the transport of `X`, `Y`, `f` and the extension to
`B'` with all its comparison isomorphisms (`AlgebraicGeometry.Space.SiteTransport`), and a
realization of the transported extension by a first-order thickening over the transported base
(`AlgebraicGeometry.Space.SquareZeroExtension.Realization`). -/
structure SquareZeroExtension.EnlargedRealization {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) where
  /-- The enlarged big fppf site. -/
  site : BigFppfSite.{u}
  /-- It contains the given one. -/
  contained : IsContained (τ := .fppf) B site
  /-- It contains the base scheme. -/
  containsBase : site.Contains S
  /-- The transport of the spaces, the morphism and the extension to the enlarged site. -/
  transport : SiteTransport B S hS E site contained containsBase
  /-- The transported extension is realized by a first-order thickening. -/
  realization : SquareZeroExtension.Realization site S containsBase transport.extension

namespace SquareZeroExtension

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}

open SiteEnlargement in
/-- **Stacks 05ZT, corrected: a square-zero extension of the étale structure sheaf by a
quasi-coherent module is realized by a first-order thickening after enlarging the big fppf
site.**

*Why the enlargement.* On a big fppf site `B` of a fixed cutoff `κ` the statement is false. Take
`X = Y = S = Spec k` for a field `k` of size below `κ` and `𝒜 = 𝒪_X ⊕ ℐ` the trivial square-zero
extension by the free module `ℐ = 𝒪_X^{(κ)}` of rank `κ`, which is quasi-coherent. A first-order
thickening `X ⊂ X'` realizing it is a thickening of an affine scheme, hence an affine scheme
(Stacks 07VT), `X' = Spec R` with `R ⟶ k` surjective with kernel `ℐ(X) = k^{(κ)}`, so `#R ≥ κ`.
But `X'` is an algebraic space for `B`, so it has an étale chart from an object of `B`; a nonempty
affine open `U` of it is an object of `B`, of size below `κ`, and it maps onto the one-point space
`X'`. So `R ⟶ Γ(U, 𝒪_U)` is faithfully flat, hence injective, and `#R ≤ #Γ(U, 𝒪_U) < κ`: a
contradiction.

*What is proved.* There is a big fppf site `B'` containing `B` (the realization uses a site
containing the thickenings of the two presenting charts of a charted presentation of `f`), with
the transport of `X`, `Y`, `f` and `E` to `B'` (`AlgebraicGeometry.Space.siteTransport`), and a
realization of the transported extension on `B'`. This is the Stacks statement read with the
universe of schemes allowed to grow, which is how the Stacks project uses it. -/
@[stacks 05ZT "corrected: realized after enlarging the big fppf site, since on a fixed cutoff \
  site a free kernel of rank the cutoff cannot be realized"]
theorem nonempty_enlargedRealization (E : SquareZeroExtension B S hS f) :
    Nonempty (EnlargedRealization B S hS E) := by
  obtain ⟨C⟩ := nonempty_chartedPresentation B S hS f
  let T : Bool → Scheme.{u} := fun b =>
    if b then chartThickening B S hS E (presentationChart C.P)
    else chartThickening B S hS E (presentationRelationChart C.P)
  obtain ⟨B', hB, hS', hT⟩ := BigFppfSite.exists_isContained_contains_base B hS (Set.range T)
  exact ⟨{
    site := B'
    contained := hB
    containsBase := hS'
    transport := siteTransport B S hS E B' hB hS'
    realization := (nonempty_realization (transportExtension hB hS' E)
      (transportChartedPresentation hB hS' C)
      (contains_chartThickening_transportPresentationChart hB hS' E C (hT _ ⟨true, rfl⟩))
      (contains_chartThickening_transportPresentationRelationChart hB hS' E C
        (hT _ ⟨false, rfl⟩))).some }⟩

end SquareZeroExtension

end AlgebraicGeometry.Space

end
