module

public import StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent

/-!
# The internal Hom of `𝒪_F`-modules depends only on the restrictions to a chart

Clause (6) of Stacks 03M1 asserts that the internal Hom `𝓗om_{𝒪_F}(G, G')` of two quasi-coherent
`𝒪_F`-modules on an algebraic space `F` is quasi-coherent when `G` is of finite presentation, and
the finite-presentation hypothesis of Stacks 03DL(7) is *local*: it asks only that, étale-locally
on `F`, `G` be the cokernel of a map of finite free modules.

`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentInternalHom` and
`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase` prove the base change criterion of
Descent, Proposition 03DX(2) for `𝓗om_{𝒪_F}(G, G')` when `G` carries a presentation by finite free
modules on the small étale site of `F` itself, that is a *global* one.  This file makes the
hypothesis chart-local in the first variable: the base change comparison of `𝓗om_{𝒪_F}(G, G')`
over a morphism `V ⟶ U` of étale charts is unchanged when `G` is replaced by any `𝒪_F`-module
with the same restriction to the slice at `U`.

The step that makes this possible is Stacks 0E8H on the small étale ringed site,
`AlgebraicGeometry.Space.smallEtaleInternalHomOverIso`, at the module universe `max (u + 1) m` in
which clause (6) is proved; see the implementation notes.

## Main definitions

* `Stacks.PresheafOfModules.InternalHom.internalHomMapLeftIso`: an isomorphism in the first
  variable of the internal Hom presheaf of Stacks 03EM induces an isomorphism of internal Homs,
  at a free module universe.
* `AlgebraicGeometry.Space.smallEtaleInternalHomOverCongrLeft` and
  `AlgebraicGeometry.Space.smallEtaleInternalHomRestrictionCongrLeft`: **the internal Hom of
  `𝒪_F`-modules restricted to the slice at an étale chart depends only on the restrictions of its
  arguments to that slice**, in the first variable.

## Main results

* `Stacks.PresheafOfModules.InternalHom.internalHomMapLeft_id'`: precomposition with an
  identity in the first variable of the internal Hom presheaf is the identity, at an arbitrary
  module universe.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_overIso`: **bijectivity of the base
  change comparison over `f : V ⟶ U` transfers along an isomorphism of the restrictions to the
  slice at `U`.**  This generalizes
  `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_bijective`, which needs an isomorphism
  of the modules themselves.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso`: **the base
  change criterion for `𝓗om_{𝒪_F}(G, G')` from chart-local models of `G`.**
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso_free` and
  `Space.isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso_presentation`:
  the same with the chart-local models taken to be finite free, and to carry a presentation by
  finite free modules.

## Implementation notes

**No `@[stacks 03M1]` attribute is carried and no clause of Stacks 03M1 is proved here.**  Every
statement below is a reduction; the convention is that of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentInternalHom` and
`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase`.  No `@[stacks 0E8H]` attribute is
carried either: that tag sits on the general statement in
`StacksDraft.Ch18.Sec27.InternalHomRestriction`.

What is still **not** reached is the finite-presentation hypothesis of Stacks 03DL(7) itself.  That
condition reads: for every object `U` of the site there is a covering `{U_i → U}` such that each
`G|_{𝒞/U_i}` has a finite global presentation.  The hypothesis of
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso_presentation`
differs from it in **two** ways, and both are weaker-to-stronger, so that hypothesis is
strictly stronger than 03DL(7) and the theorem is not clause (6):

* it asks for the presentation at the chart `U` itself, not at the members of a covering of `U`.
  Descending the base change comparison over `V ⟶ U` from a covering of `U` is a flat descent
  step which is not available in this tree; it is the same input as Descent,
  Proposition 03DX(2), carried elsewhere in this development as the hypothesis `h03DX`;
* it asks for the presentation to be the restriction of a presentation on the small étale site of
  `F` — the modules `Ploc U` and `Qloc U` are `𝒪_F`-modules and the cofans are cofans there —
  rather than for a presentation of `G|_{𝒞/U}` on the slice.  Restriction carries a presentation
  to a presentation (Stacks 03EJ, used in
  `AlgebraicGeometry.Space.isColimitCokernelCoforkOver`), so the first is stronger than the
  second; the converse needs the whole base-case-plus-inductive-step chain transplanted to the
  slice sites, which this file does not do.

Three facts about module universes.

* `AlgebraicGeometry.Space.smallEtaleInternalHomRestrictionCongrLeft` needs Stacks 0E8H at the
  module universe of its arguments, and `AlgebraicGeometry.Space.smallEtaleInternalHom` of two
  `𝒪_F`-modules in module universe `m` lands in `max (u + 1) m`.  Were
  `AlgebraicGeometry.Space.smallEtaleInternalHomOverIso` stated at the module universe `u` of
  the schemes, the composite could be formed only at `m := u`, and there it would be useless:
  the two statements that consume it,
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso_free` and
  `..._presentation`, live at `max (u + 1) m`, because
  `AlgebraicGeometry.Space.smallEtaleUliftUnit` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_free` do
  (`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase`), and `max (u + 1) m` is never
  `u`.  Freeing the module universe of `Stacks.SheafOfModules.InternalHom.internalHomOverIso` is
  what makes them statable.
* `Stacks.PresheafOfModules.InternalHom.internalHomMapLeftIso` is at a free module universe,
  like `Stacks.PresheafOfModules.InternalHom.internalHomMapLeft` it is built from.  Nothing in it
  needs a limit, a colimit or sheafification.
* `Stacks.SheafOfModules.internalHomIsoLeft`
  (`StacksDraft.AlgebraicGeometry.F3b.Divisors.NormalSheaf`) is the same statement as
  `internalHomMapLeftIso`, in one line, and is **not** reusable here, for three independent
  reasons.  It is `(internalHomFunctor 𝒪 G).mapIso e.symm |>.unop`, and
  `Stacks.PresheafOfModules.InternalHom.internalHomFunctor` is *not* free-universe-relaxable: it
  is an endofunctor of `PresheafOfModules.{m} (Oforget O)`, while `internalHom` of modules in
  module universe `m` lands in module universe `max u v m`, so at a free `m` it fails with
  `failed to solve universe constraint m =?= max (max u v) m`.  Its binder is therefore not an
  artifact, unlike that of `internalHomMapLeft`, which is at a free universe.  Beyond
  that, `internalHomIsoLeft` takes `𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}`, which at the small étale
  site of an algebraic space over `Scheme.{u}` is `CommRingCat.{u + 1}` while the structure sheaf
  is `CommRingCat.{u}`-valued; and it is stated over the particular sheaf of rings
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪`, not over
    `AlgebraicGeometry.RingedSite.ringSheaf`.

The slice object of `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_overIso` is written
with the proof term `CategoryTheory.Category.comp_id` rather than `by simp`: with `by simp` the
elaboration of the naturality square does not terminate within the default heartbeat budget,
while with the explicit proof it is immediate.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m v w

section FirstVariable

namespace Stacks.PresheafOfModules.InternalHom

variable {C : Type w} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat)

/-- First-variable precomposition of the internal Hom presheaf of Stacks 03EM carries an identity
to an identity.

This is the `map_id` law of `Stacks.PresheafOfModules.InternalHom.internalHomFunctor`, which
exists only inside that definition, and only at its pinned module universe. -/
theorem internalHomMapLeft_id' {F G : _root_.PresheafOfModules.{m} (Oforget O)} :
    internalHomMapLeft (G := G) O (𝟙 F) = 𝟙 (internalHom O F G) := by
  apply _root_.PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  rfl

/-- **An isomorphism in the first variable induces an isomorphism of internal Homs.**  For
`e : P ≅ M` of presheaves of modules, first-variable precomposition with `e` is an isomorphism

`𝓗om_O(M, N) ≅ 𝓗om_O(P, N)`

of the internal Hom presheaves of Stacks 03EM, at a free module universe.

`Stacks.SheafOfModules.internalHomIsoLeft` is this statement for a sheaf of modules over a
particular sheaf of rings and at a pinned module universe; see the implementation notes for the
three reasons it does not apply at the small étale ringed site. -/
noncomputable def internalHomMapLeftIso {M P : _root_.PresheafOfModules.{m} (Oforget O)}
    (N : _root_.PresheafOfModules.{m} (Oforget O)) (e : P ≅ M) :
    internalHom O M N ≅ internalHom O P N where
  hom := internalHomMapLeft O e.hom
  inv := internalHomMapLeft O e.inv
  hom_inv_id := by rw [internalHomMapLeft_comp, e.inv_hom_id, internalHomMapLeft_id']
  inv_hom_id := by rw [internalHomMapLeft_comp, e.hom_inv_id, internalHomMapLeft_id']

end Stacks.PresheafOfModules.InternalHom

end FirstVariable

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### Transfer of the base change comparison along an isomorphism of restrictions -/

/-- **Bijectivity of the base change comparison over `f : V ⟶ U` depends only on the restrictions
to the slice at `U`.**  An isomorphism `G|_U ≅ G'|_U` of the restrictions of two `𝒪_F`-modules to
the slice of the small étale site at `U` carries the comparison of one to the comparison of the
other; the morphism `V ⟶ U` is itself an object of that slice, and the two charts' sections are
the values of the restrictions at `𝟙 U` and at `f`.

This is strictly more general than
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_bijective`, which asks for an
isomorphism of the `𝒪_F`-modules themselves. -/
theorem bijective_sectionsBaseChange_of_overIso {G G' : Modules.{u, m} B S hS F hF}
    {U V : (smallEtaleRingedSite B S hS F hF).C} (f : V ⟶ U)
    (ε : G.over U ≅ G'.over U)
    (hG : Function.Bijective (sectionsBaseChange G f)) :
    Function.Bijective (sectionsBaseChange G' f) :=
  bijective_sectionsBaseChange_of_bijective_app f
    (ε.hom.val.app (op (Over.mk (𝟙 U)))) (ε.hom.val.app (op (Over.mk f)))
    (fun x => PresheafOfModules.naturality_apply ε.hom.val
      (Over.homMk f (Category.comp_id f) :
        (Over.mk f : Over U) ⟶ Over.mk (𝟙 U)).op x)
    (SheafOfModules.bijective_iso_hom_val_app ε _)
    (SheafOfModules.bijective_iso_hom_val_app ε _) hG

/-! ### The internal Hom on a slice depends only on the restrictions -/

/-- The internal Hom of the restrictions of two `𝒪_F`-modules to the slice at an étale chart `U`
depends, in the first variable, only on that restriction: an isomorphism `P|_U ≅ M|_U` induces

`𝓗om_{𝒪_F|_U}(M|_U, N|_U) ≅ 𝓗om_{𝒪_F|_U}(P|_U, N|_U)`.

This is `Stacks.PresheafOfModules.InternalHom.internalHomMapLeftIso` for the restricted
structure sheaf, read through the fully faithful forgetful functor from sheaves of modules. -/
noncomputable def smallEtaleInternalHomOverCongrLeft
    {M P : Modules.{u, m} B S hS F hF} (U : (smallEtaleRingedSite B S hS F hF).C)
    (e : P.over U ≅ M.over U) (N : Modules.{u, m} B S hS F hF) :
    smallEtaleInternalHomOver B S hS F hF M N U ≅
      smallEtaleInternalHomOver B S hS F hF P N U :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (Stacks.PresheafOfModules.InternalHom.internalHomMapLeftIso
      ((smallEtaleRingedSite B S hS F hF).O.over U).obj (N.over U).val
      ((SheafOfModules.forget _).mapIso e))

/-- **The restriction of the internal Hom of `𝒪_F`-modules to the slice at an étale chart depends,
in the first variable, only on the restriction of that argument.**  An isomorphism `P|_U ≅ M|_U`
induces

`𝓗om_{𝒪_F}(M, N)|_U ≅ 𝓗om_{𝒪_F}(P, N)|_U`,

by Stacks 0E8H on the small étale ringed site in both directions and
`AlgebraicGeometry.Space.smallEtaleInternalHomOverCongrLeft` in between.  It differs from that
declaration in the object it is a congruence of: there the internal Hom formed *on the slice*,
here the *restriction* of the internal Hom formed on the small étale site of `F`. -/
noncomputable def smallEtaleInternalHomRestrictionCongrLeft
    {M P : Modules.{u, m} B S hS F hF} (U : (smallEtaleRingedSite B S hS F hF).C)
    (e : P.over U ≅ M.over U) (N : Modules.{u, m} B S hS F hF) :
    (smallEtaleInternalHom B S hS F hF M N).over U ≅
      (smallEtaleInternalHom B S hS F hF P N).over U :=
  smallEtaleInternalHomOverIso B S hS F hF M N U ≪≫
    smallEtaleInternalHomOverCongrLeft U e N ≪≫
      (smallEtaleInternalHomOverIso B S hS F hF P N U).symm

/-! ### Chart-local hypotheses for the base change criterion -/

/-- **The base change criterion of Descent, Proposition 03DX(2) for `𝓗om_{𝒪_F}(M, N)` from
chart-local models of `M`.**  Suppose that for every étale chart `U` there is an `𝒪_F`-module
`P U` whose restriction to the slice at `U` is isomorphic to that of `M`, and for which
`𝓗om_{𝒪_F}(P U, N)` is cartesian on affine charts.  Then `𝓗om_{𝒪_F}(M, N)` is cartesian on
affine charts.

The models are taken as a family rather than existentially, so that nothing geometric is hidden
in an existential quantifier; a user with one model per chart supplies it directly. -/
theorem isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso
    {M N : Modules.{u, m} B S hS F hF}
    (P : (smallEtaleRingedSite B S hS F hF).C → Modules.{u, m} B S hS F hF)
    (e : ∀ U, (P U).over U ≅ M.over U)
    (hP : ∀ U, IsCartesianOnAffineCharts (smallEtaleInternalHom B S hS F hF (P U) N)) :
    IsCartesianOnAffineCharts (smallEtaleInternalHom B S hS F hF M N) :=
  fun U V hU hV f =>
    bijective_sectionsBaseChange_of_overIso f
      (smallEtaleInternalHomRestrictionCongrLeft U (e U) N).symm (hP U U V hU hV f)

/-- **The base case of Stacks 03M1(6) with a chart-local hypothesis.**  If `N` is cartesian on
affine charts and `M` restricts, on the slice at every étale chart `U`, to the restriction of a
*finite* coproduct of copies of the structure sheaf — of a different one for each chart, of a
different finite rank `n U` — then `𝓗om_{𝒪_F}(M, N)` is cartesian on affine charts.

This is `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_free` with its
global hypothesis on `M` made chart-local. -/
theorem isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso_free
    {n : (smallEtaleRingedSite B S hS F hF).C → ℕ}
    {M N : Modules.{u, max (u + 1) m} B S hS F hF}
    (P : (smallEtaleRingedSite B S hS F hF).C → Modules.{u, max (u + 1) m} B S hS F hF)
    (ι : ∀ U, ∀ _ : Fin (n U), smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ P U)
    (hι : ∀ U, IsColimit (Cofan.mk (P U) (ι U)))
    (e : ∀ U, (P U).over U ≅ M.over U) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (smallEtaleInternalHom B S hS F hF M N) :=
  isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso P e
    (fun U => isCartesianOnAffineCharts_smallEtaleInternalHom_free (ι U) (hι U) hN)

/-- **The base change criterion of Stacks 03M1(6) with a chart-local finite presentation.**  If
`N` is cartesian on affine charts and for every étale chart `U` the restriction `M|_U` is
isomorphic to the restriction of the cokernel of a map `Qloc U ⟶ Ploc U` of finite coproducts of
copies of the structure sheaf, then `𝓗om_{𝒪_F}(M, N)` is cartesian on affine charts.

This is the base case of
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_free` and the inductive
step `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom` composed, with the
presentation asked for chart by chart rather than globally.

It is **not** the hypothesis of Stacks 03DL(7), in two ways: that one asks for a presentation of
`M|_{U_i}` for the members of some étale covering `{U_i → U}` of each chart rather than at the
chart itself, and it asks for a presentation on the slice rather than for the restriction of one
on the small étale site of `F`.  See the implementation notes. -/
theorem isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso_presentation
    {p q : (smallEtaleRingedSite B S hS F hF).C → ℕ}
    {M N : Modules.{u, max (u + 1) m} B S hS F hF}
    (Mloc Ploc Qloc : (smallEtaleRingedSite B S hS F hF).C →
      Modules.{u, max (u + 1) m} B S hS F hF)
    (ιP : ∀ U, ∀ _ : Fin (p U), smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ Ploc U)
    (hιP : ∀ U, IsColimit (Cofan.mk (Ploc U) (ιP U)))
    (ιQ : ∀ U, ∀ _ : Fin (q U), smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ Qloc U)
    (hιQ : ∀ U, IsColimit (Cofan.mk (Qloc U) (ιQ U)))
    (a : ∀ U, Qloc U ⟶ Ploc U) (b : ∀ U, Ploc U ⟶ Mloc U)
    (hab : ∀ U, a U ≫ b U = 0)
    (hb : ∀ U, IsColimit (CokernelCofork.ofπ (b U) (hab U)))
    (e : ∀ U, (Mloc U).over U ≅ M.over U) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (smallEtaleInternalHom B S hS F hF M N) :=
  isCartesianOnAffineCharts_smallEtaleInternalHom_of_overIso Mloc e
    (fun U => isCartesianOnAffineCharts_smallEtaleInternalHom (hab U) (hb U) N
      (isCartesianOnAffineCharts_smallEtaleInternalHom_free (ιP U) (hιP U) hN)
      (isCartesianOnAffineCharts_smallEtaleInternalHom_free (ιQ U) (hιQ U) hN))

end AlgebraicGeometry.Space

end
