module

public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineColimitPresentations
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality

/-!
# Cokernels and colimits of quasi-coherent modules on a site

Quasi-coherence of a sheaf of modules is a local condition, and the covering it produces depends
on the module, so closure under cokernels does not follow from the definition: the source and the
target of a morphism supply two unrelated coverings.  What repairs this is a single family of
objects covering the final object on whose members *every* module in sight is already globally
presented; on such a family the cokernel is globally presented too, and quasi-coherence of the
cokernel then follows from the clause of Stacks 03DN for quasi-coherence.  The same reduction
applies verbatim to a colimit of any shape.

Unlike the direct sums of
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDirectSums`, the local step is *not*
unconditional.  Assembling a presentation of the cokernel out of presentations of the source and
the target asks for the generators of the source to lift along the presentation of the target,
which is the one non-formal hypothesis of
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift`; the lift is supplied
by surjectivity of a presenting morphism on the sections over a terminal object of the site
(`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_surjective_val_app`).  That
surjectivity is the vanishing of the first cohomology of a quasi-coherent module over an affine
base, Stacks 03DW, and it is carried here as
`Stacks.SheafOfModules.HasSurjectivePresentations`: a condition on the site, which a consumer
imposes on the slice site at a member of the covering family, whose terminal object is the member
itself.

## Main definitions

* `Stacks.SheafOfModules.HasSurjectivePresentations`: **Stacks 03DW as a condition on a site with
  a prescribed object** — the presenting morphism of every global presentation of a sheaf of
  modules is surjective on the sections over that object.

## Main results

* `Stacks.SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork`: **a cokernel of a
  morphism between globally presented sheaves of modules is globally presented**, on a site with a
  terminal object over which presenting morphisms are surjective on sections.
* `Stacks.SheafOfModules.hasGlobalPresentation_over_of_isColimit_cokernelCofork`: the same
  conclusion after restriction to an object of the site, from global presentations there.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit_cokernelCofork`: **a
  cokernel of a morphism between sheaves of modules which are globally presented on each member
  of a family covering the final object is quasi-coherent.**
* `Stacks.SheafOfModules.hasGlobalPresentation_over_of_isColimit` and
  `Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit`: the same two statements
  for a colimit of arbitrary shape in place of a cokernel.

## Implementation notes

`Stacks.SheafOfModules.HasSurjectivePresentations` repeats the binders of the surjectivity
hypothesis of `SheafOfModules.HasGlobalPresentation.of_isColimit` verbatim, so that one assumption
serves both the cokernel clause and the colimit clause of Stacks 0GNB(3).  The quantification over
the presentation data is unavoidable: the data is obtained by destructuring the given global
presentations and so cannot be named in the statement.  The object is not asked to be terminal in
the definition — terminality is what a consumer needs, and is taken there — so that the condition
can be stated at an object before a terminal structure on it has been chosen.

The universe of the module sections is `max u v r m`, with `u` and `v` the universes of the
objects and the morphisms of the site, `r` that of the coefficient rings and `m` a free
parameter; that is the universe in which global presentations are indexed, and it is independent
of the universe of the coefficient rings, which is what the small étale site of an algebraic
space needs.  Restriction to the slice site at a member carries the cokernel cofork to a cokernel
cofork by `Stacks.SheafOfModules.overFunctor_preservesColimits`, and the two sheafification data
that the local step consumes hold on the slice with no hypothesis, since that universe contains
the slice site.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Stacks 03DW as a condition on a site at an object `Z`**: whenever a coproduct `P` of copies
of the structure sheaf presents a sheaf of modules `N` as the cokernel of a map out of another
such coproduct `Q`, the presenting morphism `P ⟶ N` is surjective on the sections over `Z`.

For `Z` terminal this is the one hypothesis of
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift` which is not a formal
consequence of the two presentations: it supplies the lift of the generators of the source along
the presentation of the target.  The binders are those of the surjectivity hypothesis of
`SheafOfModules.HasGlobalPresentation.of_isColimit`, so one assumption serves the cokernel clause
and the colimit clause of Stacks 0GNB(3) alike. -/
def HasSurjectivePresentations (R : Sheaf J RingCat.{r}) (Z : C) : Prop :=
  ∀ (N : _root_.SheafOfModules.{max u v r m} R) (I K : Type (max u v r m))
    (P Q : _root_.SheafOfModules.{max u v r m} R)
    (ι : ∀ _ : I, _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, max u v r m}
      (_root_.SheafOfModules.unit R) ⟶ P)
    (κ : ∀ _ : K, _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, max u v r m}
      (_root_.SheafOfModules.unit R) ⟶ Q),
    IsColimit (Cofan.mk P ι) → IsColimit (Cofan.mk Q κ) →
    ∀ (a : Q ⟶ P) (b : P ⟶ _root_.SheafOfModules.uliftForPresentation.{u, v, r,
        max u v r m, max u v r} N) (hab : a ≫ b = 0),
      IsColimit (CokernelCofork.ofπ b hab) → Function.Surjective (b.val.app (op Z))

variable {R : Sheaf J RingCat.{r}}

/-- **A cokernel of a morphism between globally presented sheaves of modules is globally
presented**, on a site with a terminal object `Z` at which the surjectivity of Stacks 03DW holds.

A presentation of the target supplies the coproducts `P` and `Q` and the presenting cokernel
`b : P ⟶ N`, a presentation of the source supplies a coproduct `F` with an epimorphism onto it
(`SheafOfModules.HasGlobalPresentation.exists_epi_of_isColimit_cofan`), and the surjectivity of
`b` on the sections over `Z` lifts the composite out of `F` along `b`; then
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_surjective_val_app` exhibits
the cokernel as the cokernel of the map `Q ⊞ F ⟶ P`.  Raising the universe of the sections
preserves finite colimits, so the cokernel cofork stays one after that lift. -/
theorem HasGlobalPresentation.of_isColimit_cokernelCofork {Z : C} (hZ : IsTerminal Z)
    (hsurj : HasSurjectivePresentations.{u, v, r, m} R Z)
    {M N T : _root_.SheafOfModules.{max u v r m} R} {f : M ⟶ N} {π : N ⟶ T}
    (hfπ : f ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π hfπ))
    (hM : M.HasGlobalPresentation) (hN : N.HasGlobalPresentation) :
    T.HasGlobalPresentation := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hN
  obtain ⟨I', F, ν, ⟨hF⟩, p, hpepi⟩ := hM.exists_epi_of_isColimit_cofan
  have hs : HasSheafify J AddCommGrpCat.{max u v r m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, u} J
  have hw : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m, u, v} J
  have hfin : PreservesFiniteColimits
      (_root_.SheafOfModules.uliftForPresentationFunctor.{u, v, r, max u v r m,
        max u v r} (R := R)) :=
    _root_.SheafOfModules.preservesFiniteColimits_uliftForPresentationFunctor.{u, v, r,
      max u v m, max u v r}
  have := hpepi
  exact
    _root_.SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_surjective_val_app
      hP hQ hF hab hb hZ (hsurj _ I K P Q ι κ hP hQ a b hab hb) (p := p)
      (by rw [← _root_.SheafOfModules.uliftForPresentationMap_comp, hfπ]
          exact (_root_.SheafOfModules.uliftForPresentationFunctor.{u, v, r, max u v r m,
            max u v r} (R := R)).map_zero _ _)
      (isColimitCoforkMapOfIsColimit'
        (_root_.SheafOfModules.uliftForPresentationFunctor.{u, v, r, max u v r m, max u v r})
        hfπ hπ)

/-- The slice site at `W` has sheafification and satisfies `W = locally bijective` for sheaves of
abelian groups in the universe of the module sections. -/
private theorem hasSheafify_and_wEqualsLocallyBijective_over (W : C) :
    HasSheafify (J.over W) AddCommGrpCat.{max u v m} ∧
      (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v m} :=
  ⟨GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v m, v, max u v} (J.over W),
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v m,
      max u v, v} (J.over W)⟩

/-- **A cokernel of a morphism between sheaves of modules which are globally presented on an
object `W` is globally presented on `W`**, granted the surjectivity of Stacks 03DW on the slice
site at `W`.

Restriction to the slice site at `W` preserves colimits, so the restricted cofork is again a
cokernel cofork, and the terminal object of that slice is `W` itself
(`CategoryTheory.Over.mkIdTerminal`); then
`Stacks.SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork` applies.  This is the
local step of the cokernel clause of Stacks 0GNB(3). -/
theorem hasGlobalPresentation_over_of_isColimit_cokernelCofork (W : C)
    (hsurj : HasSurjectivePresentations.{max u v, v, r, m} (R.over W) (Over.mk (𝟙 W)))
    {M N T : _root_.SheafOfModules.{max u v r m} R} {f : M ⟶ N} {π : N ⟶ T}
    (hfπ : f ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π hfπ))
    (hM : (M.over W).HasGlobalPresentation) (hN : (N.over W).HasGlobalPresentation) :
    (T.over W).HasGlobalPresentation := by
  obtain ⟨hs, hw⟩ := hasSheafify_and_wEqualsLocallyBijective_over.{u, v, max r m} (J := J) W
  have hz : (_root_.SheafOfModules.overFunctor.{max u v r m} R W).PreservesZeroMorphisms :=
    { map_zero := fun _ _ ↦ rfl }
  have hpc : PreservesColimitsOfSize.{max u v r m, max u v r m}
      (_root_.SheafOfModules.overFunctor.{max u v r m} R W) :=
    overFunctor_preservesColimits.{u, v, r, m} R W
  have hfc : PreservesFiniteColimits (_root_.SheafOfModules.overFunctor.{max u v r m} R W) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact HasGlobalPresentation.of_isColimit_cokernelCofork.{max u v, v, r, m}
    (Over.mkIdTerminal (X := W)) hsurj
    (f := (_root_.SheafOfModules.overFunctor.{max u v r m} R W).map f)
    (π := (_root_.SheafOfModules.overFunctor.{max u v r m} R W).map π)
    (by rw [← Functor.map_comp, hfπ]
        exact (_root_.SheafOfModules.overFunctor.{max u v r m} R W).map_zero _ _)
    (isColimitCoforkMapOfIsColimit'
      (_root_.SheafOfModules.overFunctor.{max u v r m} R W) hfπ hπ) hM hN

/-- **A cokernel of a morphism between sheaves of modules which are globally presented on each
member of a family covering the final object is quasi-coherent.**

This is the cokernel clause of Stacks 0GNB(3) reduced to its two affine inputs: what has to be
supplied is one family covering the final object on whose members every quasi-coherent module is
globally presented — Stacks 03DX — together with the surjectivity of Stacks 03DW on the slice
site at each member, and the clause of Stacks 03DN for quasi-coherence does the rest.  The
universe of the module sections is independent of the universe of the coefficient rings. -/
theorem isQuasicoherentOnSite_of_coversTop_isColimit_cokernelCofork
    {I : Type u} {W : I → C} (hW : J.CoversTop W)
    (hsurj : ∀ i, HasSurjectivePresentations.{max u v, v, r, m} (R.over (W i))
      (Over.mk (𝟙 (W i))))
    {M N T : _root_.SheafOfModules.{max u v r m} R} {f : M ⟶ N} {π : N ⟶ T}
    (hfπ : f ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π hfπ))
    (hM : ∀ i, (M.over (W i)).HasGlobalPresentation)
    (hN : ∀ i, (N.over (W i)).HasGlobalPresentation) :
    T.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation T hW fun i ↦
    hasGlobalPresentation_over_of_isColimit_cokernelCofork.{u, v, r, m} (W i) (hsurj i) hfπ hπ
      (hM i) (hN i)

/-- **A colimit of sheaves of modules which are globally presented on an object `W` is globally
presented on `W`**, granted the surjectivity of Stacks 03DW on the slice site at `W`.

Restriction to the slice site at `W` preserves colimits, so the restricted cocone is again a
colimit cocone, and the terminal object of that slice is `W` itself
(`CategoryTheory.Over.mkIdTerminal`); then
`SheafOfModules.HasGlobalPresentation.of_isColimit` applies.  This is the local step of the
colimit clause of Stacks 0GNB(3), and it subsumes both the direct sums of
`Stacks.SheafOfModules.hasGlobalPresentation_over_of_isColimit_cofan` — which however need no
surjectivity — and the cokernels of
`Stacks.SheafOfModules.hasGlobalPresentation_over_of_isColimit_cokernelCofork`. -/
theorem hasGlobalPresentation_over_of_isColimit (W : C)
    (hsurj : HasSurjectivePresentations.{max u v, v, r, m} (R.over W) (Over.mk (𝟙 W)))
    {K : Type (max u v r m)} [Category.{max u v r m} K]
    {D : K ⥤ _root_.SheafOfModules.{max u v r m} R} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ k, ((D.obj k).over W).HasGlobalPresentation) :
    (c.pt.over W).HasGlobalPresentation := by
  obtain ⟨hs, hw⟩ := hasSheafify_and_wEqualsLocallyBijective_over.{u, v, max r m} (J := J) W
  have hpc : PreservesColimitsOfSize.{max u v r m, max u v r m}
      (_root_.SheafOfModules.overFunctor.{max u v r m} R W) :=
    overFunctor_preservesColimits.{u, v, r, m} R W
  exact _root_.SheafOfModules.HasGlobalPresentation.of_isColimit.{max u v, v, r, max u v m}
    (Over.mkIdTerminal (X := W)) hsurj
    (isColimitOfPreserves (_root_.SheafOfModules.overFunctor.{max u v r m} R W) hc) hD

/-- **A colimit of sheaves of modules which are globally presented on each member of a family
covering the final object is quasi-coherent.**

This is the colimit clause of Stacks 0GNB(3) reduced to its two affine inputs: one family
covering the final object on whose members every quasi-coherent module is globally presented —
Stacks 03DX — together with the surjectivity of Stacks 03DW on the slice site at each member.
The universe of the module sections is independent of the universe of the coefficient rings. -/
theorem isQuasicoherentOnSite_of_coversTop_isColimit
    {I : Type u} {W : I → C} (hW : J.CoversTop W)
    (hsurj : ∀ i, HasSurjectivePresentations.{max u v, v, r, m} (R.over (W i))
      (Over.mk (𝟙 (W i))))
    {K : Type (max u v r m)} [Category.{max u v r m} K]
    {D : K ⥤ _root_.SheafOfModules.{max u v r m} R} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ (i : I) (k : K), ((D.obj k).over (W i)).HasGlobalPresentation) :
    c.pt.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation c.pt hW fun i ↦
    hasGlobalPresentation_over_of_isColimit.{u, v, r, m} (W i) (hsurj i) hc (hD i)

end Stacks.SheafOfModules

end
