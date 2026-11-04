module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Reducing the cokernel step to the lifting of single generators

`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift` carries a hypothesis
`hl` asking for a map `l : F ⟶ P` lifting `p ≫ f` along the presentation `b : P ⟶ N`, where `F`
is a coproduct of copies of the structure sheaf.  That hypothesis is the arithmetic content of
the cokernel step: it is where the vanishing of the first cohomology of a quasi-coherent module
enters, and it is not a formal consequence of the two presentations.

This file splits that hypothesis into its formal and non-formal halves.  A map out of a
coproduct is a family of maps out of the summand, so a lift of `p ≫ f` exists as soon as *each
individual* map out of the summand lifts along `b`.  The quantified statement that every map
`O ⟶ N` lifts along `b` says exactly that `b` induces a surjection on `O`-sections; for `O` the
structure sheaf it is the surjectivity on sections of a presentation, which is the concrete form
in which the cohomological input is used and proved.

Nothing here asserts that surjectivity.  What it removes is the need to produce the lift
simultaneously for a whole indexed family: after this reduction the remaining obligation is
about a single section at a time.

## Main results

* `SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_generatorsLift`: the
  cokernel step of a global presentation, with the lift hypothesis of
  `SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift` replaced by the
  lifting of single generators along the presentation.

## Implementation notes

The formal half is `CategoryTheory.Limits.exists_lift_of_isColimit_cofan`, which is stated for
a cofan with an arbitrary summand `O`, not for the universe lift of the structure sheaf, and in
a bare category: it uses only the universal property of the coproduct.  Taking `O` to be
`SheafOfModules.uliftForPresentation` of `SheafOfModules.unit` recovers the case the cokernel
step needs.

The hypothesis is phrased as a lifting property of `b` against `O` rather than as surjectivity
of a map of section modules.  `SheafOfModules.unitHomEquiv` identifies maps out of the structure
sheaf with sections, but it is stated for `SheafOfModules.unit` itself, whereas the presentation
machinery works with its universe lift, for which no such identification is recorded; the
lifting property is what the proof uses and it avoids transporting that equivalence.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

/-- **The cokernel step, with the lift reduced to single generators.**  This is
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift` with its hypothesis
`hl` — a lift of `p ≫ f` along the presentation `b` of `N`, defined on the whole coproduct `F` —
replaced by `hsec`, which asks only that each individual map from a copy of the structure sheaf
into `N` lift along `b`.

The two are equivalent for an `F` that is a coproduct of copies of the structure sheaf, and
`hsec` is the form the mathematics supplies: on an affine object it is the surjectivity on
sections of the presentation of `N`, which is the vanishing of the first cohomology of the
kernel of that presentation (Stacks 03DW, used in the proof of Stacks 0GNB(3)). -/
theorem HasGlobalPresentation.of_isColimit_cokernelCofork_of_generatorsLift
    {M N T : SheafOfModules.{m} R} {f : M ⟶ N} {π : N ⟶ T}
    {I K I' : Type (max u v r m)} {P Q F : SheafOfModules.{max u v r m} R}
    {ι : ∀ _ : I,
      uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ P}
    {κ : ∀ _ : K,
      uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ Q}
    {ν : ∀ _ : I',
      uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ F}
    (hP : IsColimit (Cofan.mk P ι)) (hQ : IsColimit (Cofan.mk Q κ))
    (hF : IsColimit (Cofan.mk F ν)) [HasBinaryCoproduct Q F]
    {a : Q ⟶ P} {b : P ⟶ uliftForPresentation.{u, v, r, m, max u v r} N}
    (hab : a ≫ b = 0) (hb : IsColimit (CokernelCofork.ofπ b hab))
    (hsec : ∀ g : uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶
        uliftForPresentation.{u, v, r, m, max u v r} N,
      ∃ g' : uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ P,
        g' ≫ b = g)
    {p : F ⟶ uliftForPresentation.{u, v, r, m, max u v r} M} [Epi p]
    (hfπ : uliftForPresentationMap.{u, v, r, m, max u v r} f ≫
      uliftForPresentationMap.{u, v, r, m, max u v r} π = 0)
    (hπ : IsColimit (CokernelCofork.ofπ
      (uliftForPresentationMap.{u, v, r, m, max u v r} π) hfπ)) :
    HasGlobalPresentation T := by
  obtain ⟨l, hl⟩ :=
    exists_lift_of_isColimit_cofan hF hsec (p ≫ uliftForPresentationMap.{u, v, r, m, max u v r} f)
  exact HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift hP hQ hF hab hb hl hfπ hπ

end SheafOfModules

end
