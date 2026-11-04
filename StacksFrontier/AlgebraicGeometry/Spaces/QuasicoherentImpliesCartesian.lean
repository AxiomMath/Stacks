module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurj
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# The forward implication of Descent, Proposition 03DX(2), reduced to essential surjectivity

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The tree
carries the equivalence of Descent, Proposition 03DX(2) for the small étale site of `F` as an
explicit hypothesis, in two interchangeable spellings — the implication

`∀ G, G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G`

and the equivalence `∀ G, G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G` — under the
binder name `h03DX`.  **Both halves are now theorems of this tree**: the `←` half is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` and the `→` half is
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentCartesianOnAffineCharts.lean`, which proves
it unconditionally; both are re-exported below in the `h03DX` spelling.

This file also records a *second* route to the `→` half, through **one** statement which does
not mention the module `G`: essential surjectivity of the functor `M ↦ Mᵃ` of Tag 03DU on the
quasi-coherent modules of the slice of the small étale site of `F` at an affine chart.  Granted
it, both spellings of `h03DX` are discharged at `AlgebraicGeometry.Space.Modules.{u, u}`, for
every module at once.  That route is kept because it is the source's own, but it is no longer
needed: nothing in the tree has to grant its hypothesis.

The two ingredients are already in the tree, and all this file does is join them:

* `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj` turns essential
  surjectivity at the affine charts into `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`,
  with no localization step, because a morphism of affine charts is already a morphism of the
  slice at the larger of them.  Its hypothesis, however, is about the restriction of one given
  module `G`, so a consumer must re-establish it for each `G` and cannot cite it as a
  proposition of Descent.
* `Stacks.SheafOfModules.isQuasicoherent_over` says that the restriction of a quasi-coherent
  module to a slice is quasi-coherent, which is what lets the `G`-free hypothesis below be
  applied to `AlgebraicGeometry.Space.SmallEtale.sliceModule`.

## Main results

All three results below live in the namespace `AlgebraicGeometry.Space.SmallEtale`.

* `exists_sliceAssociatedModule_iso_self`: the existential demanded by the hypothesis below is
  satisfied by a module that is already an `Mᵃ`.  This records that the hypothesis asks for
  something attainable; it is not used downstream.
* `isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj`: **the forward implication of
  Descent, Proposition 03DX(2) for the small étale site of `F`, granted essential surjectivity
  of `(-)ᵃ` on the quasi-coherent modules of the slices at affine charts.**  The conclusion is
  spelled exactly as the hypothesis `h03DX` of
  `AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact` and of its siblings.
* `isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_essSurj`: the same hypothesis gives
  the **equivalence**, the second spelling of `h03DX`, by appending the unconditional converse.

## Implementation notes

The hypothesis is written out at each use rather than named, following the tree's existing
practice for `h03DT` and `h03DX`: no new definition, structure, class or instance is
introduced here, and no second spelling of Tag 03DX is created.  It differs from the
hypothesis of `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj` in
quantifying over *every* quasi-coherent module of the slice instead of over the restriction of
one given `G`, which is what makes it the essential-surjectivity clause of Descent,
Proposition 03DX(2) rather than a statement about `G`, and what lets a single instance of it
serve every `G`.

The module universe is the universe of the schemes.  It is forced by the *statement*, not by an
instance: the sections of `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` over a
chart over `Y` are the global sections of a pullback of `M`, which lie in `Type u` by
construction, so `Mᵃ` is a `SheafOfModules.{u}` and no module of another universe can be
isomorphic to one.  Restating the results at a free module universe fails with a type mismatch
at `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`.
`AlgebraicGeometry.Space.Modules.{u, u}` is the universe at which the consumers
carry `h03DX`.

**What this file does not prove.**  The essential-surjectivity hypothesis above is not proved
here.  It is *not* a gap of the development: the implication it was introduced to supply is
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, which is proved
unconditionally, so nothing depends on it.  Its Stacks proof at an affine chart `Y` takes a
covering of `Y` on whose members the
restriction of the module has a global presentation, identifies each such restriction with an
`Mᵃ` using Tag 03DV for the two coproducts of copies of the structure sheaf, Tag 0GN7 (full
faithfulness of `(-)ᵃ`) to descend the presenting map and right exactness of `(-)ᵃ` to descend
its cokernel, and then descends the resulting modules along the covering by Tag 023T, gluing
the isomorphisms by Tag 03EM.  Of those, Tag 03EM is formalized
(`StacksDraft.Ch18.Sec27.Tag03EM`) and Tags 03DV, 0GN7 and 023T carry no declaration in this
tree under any of the attribute forms; all three are Descent, Chapter 35.  Tag 03DW, the
cohomology comparison, is *not* an input: Tag 03DX does not cite it, and Tag 03DW's own proof
routes through Tags 03F9, 03FJ, 03F7, 01XD and 013P, so it is a consumer of this area.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A module on the slice at a chart which is already an `Mᵃ` is in the essential image of
`(-)ᵃ`.**  The witness is `M` itself and the identity isomorphism.

This exists to record that the existential of the hypothesis of
`isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj` below is attainable — the
hypothesis asks for a quasi-coherent module on the chart's scheme together with the sheaf
condition of Tag 03DT for its presheaf of pullback sections, and both are supplied here from
an object already of that form.  It is not used downstream. -/
theorem exists_sliceAssociatedModule_iso_self (Y : SmallEtale B S hS F)
    (M₀ : (chartScheme Y).Modules) [M₀.IsQuasicoherent]
    (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
      (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀ (sliceToOver B S hS F Y))) :
    ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
      (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
        (Stacks.Sites.associatedPresheaf (chartScheme Y) M (sliceToOver B S hS F Y))),
      Nonempty (sliceAssociatedModule B S hS F hF Y M₀ hM₀ ≅
        sliceAssociatedModule B S hS F hF Y M hM) :=
  ⟨M₀, inferInstance, hM₀, ⟨Iso.refl _⟩⟩

/-- **The forward implication of Descent, Proposition 03DX(2) for the small étale site of an
algebraic space, granted essential surjectivity of `(-)ᵃ` at the affine charts.**

The hypothesis `hEss` is the essential-surjectivity clause of Descent,
Proposition 03DX(2) at an affine chart `Y` of `F`: every quasi-coherent module on the slice of
the small étale site of `F` at `Y` is isomorphic to the module `Mᵃ` of Tag 03DU of a
quasi-coherent module `M` on the scheme underlying `Y`.  It mentions no module of `F`, so one
instance of it serves every `G`.

Granted it, every quasi-coherent `𝒪_F`-module is cartesian on affine charts.  The proof is the
composite of two known results: the restriction of `G` to the slice at `Y` is quasi-coherent
(`Stacks.SheafOfModules.isQuasicoherent_over`), so `hEss` applies to it and gives the
hypothesis of `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`.

The conclusion is the implication spelling of the hypothesis `h03DX` carried by
`AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact`,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_h03DX`,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_coproduct_of_h03DX` and
`AlgebraicGeometry.Space.closedSubspaceIdealOrderIso_of_h03DX`, verbatim, so that it can be
supplied to them with no adapter.

No `@[stacks]` attribute is claimed: Tag 03DX(2) is an equivalence of categories, and this is
one implication of it carrying the other half of its proof as a hypothesis. -/
theorem isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ N : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), N.IsQuasicoherentOnSite →
        ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
          (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M
              (sliceToOver B S hS F Y))),
          Nonempty (N ≅ sliceAssociatedModule B S hS F hF Y M hM)) :
    ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G := fun G hG =>
  isCartesianOnAffineCharts_of_essSurj B S hS F hF G fun Y hY =>
    hEss Y hY (sliceModule B S hS F hF Y G)
      (Stacks.SheafOfModules.isQuasicoherent_over G hG Y)

/-- **Descent, Proposition 03DX(2) for the small étale site of an algebraic space, granted
essential surjectivity of `(-)ᵃ` at the affine charts.**  An `𝒪_F`-module is quasi-coherent if
and only if it is cartesian on affine charts.

This is `isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj` together with the
unconditional converse
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`, and its
conclusion is the equivalence spelling of the hypothesis `h03DX` carried by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian`,
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves` and
`AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_isCartesian` at `m := u`.

No `@[stacks]` attribute is claimed: the essential-surjectivity half of the proposition's proof
is a hypothesis. -/
theorem isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_essSurj
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ N : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), N.IsQuasicoherentOnSite →
        ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
          (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M
              (sliceToOver B S hS F Y))),
          Nonempty (N ≅ sliceAssociatedModule B S hS F hF Y M hM)) :
    ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G := fun G =>
  ⟨isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj B S hS F hF hEss G,
    isQuasicoherentOnSite_of_isCartesianOnAffineCharts G⟩

/-- **The forward implication of Descent, Proposition 03DX (2) for the small étale site of an
algebraic space**, unconditionally: every quasi-coherent `𝒪_F`-module is cartesian on affine
charts.

This is `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, restated in
the spelling of the hypothesis `h03DX` carried by
`AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact`,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_h03DX`,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_coproduct_of_h03DX` and
`AlgebraicGeometry.Space.closedSubspaceIdealOrderIso_of_h03DX`, so that it can be supplied to
them with no adapter.

No `@[stacks]` attribute is claimed here: the tag's content is carried by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, of which this is a
restatement. -/
theorem isCartesianOnAffineCharts_of_isQuasicoherentOnSite :
    ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G := fun G hG =>
  _root_.AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite
    B S hS F hF G hG

/-- **Descent, Proposition 03DX (2) for the small étale site of an algebraic space**,
unconditionally: an `𝒪_F`-module is quasi-coherent if and only if it is cartesian on affine
charts.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, restated in
the spelling of the hypothesis `h03DX` carried by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian`,
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves` and
`AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_isCartesian` at `m := u`.

No `@[stacks]` attribute is claimed here: the tag's content is carried by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, of which this is a
restatement. -/
theorem isQuasicoherentOnSite_iff_isCartesianOnAffineCharts :
    ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G := fun G =>
  _root_.AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts
    B S hS F hF G

end AlgebraicGeometry.Space.SmallEtale

end
