module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom

/-!
# Quasi-coherence of the internal Hom of `𝒪_F`-modules on an algebraic space

Clause (6) of Stacks 03M1 asserts that the internal Hom `𝓗om_{𝒪_F}(G, G')` of two
quasi-coherent `𝒪_F`-modules on an algebraic space `F` is quasi-coherent **when `G` is of
finite presentation** (the source's hypotheses for this clause are exactly: `G` and `G'`
quasi-coherent and `G` of finite presentation, Stacks 03DL(7); no hypothesis on `G'` beyond
quasi-coherence).  The sheaf itself is
`AlgebraicGeometry.Space.smallEtaleInternalHom`, built in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom`.

This file supplies the **inductive step** of the source proof of that clause: the clause for a
module `G` presented as a cokernel `Q → P → G → 0` follows from the clause for the two
presenting modules `P` and `Q`.  Concretely, `𝓗om_{𝒪_F}(-, G')` carries such a presentation to
an exact sequence

`0 ⟶ 𝓗om(G, G') ⟶ 𝓗om(P, G') ⟶ 𝓗om(Q, G')`

of sections over *every* étale chart, and the base change criterion of Descent,
Proposition 03DX(2) propagates along a left exact sequence by flatness of the chart
restrictions — exactly as for the kernel clause of Stacks 03M1(3) in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel`, whose commutative-algebra step
`AlgebraicGeometry.Space.bijective_baseChange_of_exact` is reused unchanged.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft`: **precomposition in the first
  variable**, `𝓗om_{𝒪_F}(G, G') ⟶ 𝓗om_{𝒪_F}(P, G')` for `P ⟶ G`, at a free module universe.
* `AlgebraicGeometry.Space.isColimitCokernelCoforkOver`: restriction to the slice at an étale
  chart carries the cokernel of a presentation to a cokernel.

## Main results

* `AlgebraicGeometry.Space.injective_smallEtaleInternalHomMapLeft_app` and
  `AlgebraicGeometry.Space.exact_smallEtaleInternalHomMapLeft_app`: over every étale chart, the
  sections of the internal Hom of a presented module are the kernel of the map between the
  sections of the internal Homs of the two presenting modules.  This is the half of
  Stacks 0GMY(1) — internal Hom turns colimits in the first variable into limits — which the
  quasi-coherence clause uses, at the sheaf level and at a free module universe.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom`: **the base change
  criterion for the internal Hom of a presented module, unconditionally**, from the criterion
  for the internal Homs of the two presenting modules.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian`: the same
  reduction for quasi-coherence itself, conditional on Descent, Proposition 03DX(2) and on
  nothing else.

## Implementation notes

**Nothing here proves any clause of Stacks 03M1, and no `@[stacks 03M1]` attribute is carried.**
Clause (6) is unconditional; every statement below is a reduction, and tagging a reduction with
the tag it reduces would report that tag as proved.  The same convention is used by
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite`,
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite` and
`StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent`.  No `@[stacks 0GMY]` attribute
is carried either: only the fragment of part (1) that a presentation needs is proved, not the
functor statement.

What is **not** proved here, and is the whole remaining content of clause (6), is the *base*
case: that the internal Hom out of a **finite** coproduct of copies of `𝒪_F` satisfies the base
change criterion.  That is where the finite-presentation hypothesis of the source enters, and
it enters only there: the sections of the internal Hom out of a coproduct of copies of `𝒪_F`
indexed by `I` over a chart `U` are `∏_{i ∈ I} G'(U)`, and base change along a flat ring map
commutes with a *finite* product unconditionally but with an infinite one only under further
hypotheses.  The reduction below is stated with the base case as the two hypotheses `hP` and
`hQ` precisely so that the finiteness is visible exactly where it is used; nothing below
assumes it, and nothing below would be true of a general module in place of `P` and `Q`.

Two facts about module universes.

* The first-variable precomposition map of the internal Hom is available at a **free** module
  universe: `AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft` is built directly from
  `Stacks.PresheafOfModules.InternalHom.internalHomMapLeft` of
  `StacksDraft.Ch18.Sec27.InternalHomVariance`, whose module universe is free.
* The statements below are nevertheless at the module universe `max (u + 1) m` rather than at a
  free `m`.  The binding reason is `Stacks.SheafOfModules.overFunctor_preservesColimits`
  (restriction of sheaves of modules to a slice of the site preserves colimits, Stacks 03EJ),
  whose proof needs sheafification of `AddCommGrpCat`-valued sheaves and is therefore stated
  only at module universes of the shape `max u v w t`, which on the small étale ringed site of
  an algebraic space over `Scheme.{u}` — objects in `Type (u + 1)`, morphisms in `Type u`,
  structure sheaf in `CommRingCat.{u}` — is `max (u + 1) t`.  That is no loss of generality for
  the internal Hom itself: `AlgebraicGeometry.Space.smallEtaleInternalHom` of two modules in
  module universe `max (u + 1) m` lands again in `max (u + 1) m`, so the clause is
  universe-stable there, whereas at a free `m` the internal Hom leaves the universe it started
  in.

The exactness statements are proved on the restricted modules rather than on the internal Hom
presheaf: the sections of `AlgebraicGeometry.Space.smallEtaleInternalHom G G'` over a chart `U`
are, by construction and `rfl`, the morphisms `(G.over U).val ⟶ (G'.over U).val` of presheaves
of modules on the slice, and both are sheaves, so that module is the Hom module of
`SheafOfModules` on the slice.  Restriction carries the presentation's cokernel to a cokernel
there, and the two statements are then the universal property of a cokernel.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

open Stacks.PresheafOfModules.InternalHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Precomposition in the first variable of the internal Hom of `𝒪_F`-modules.**  A morphism
`b : P ⟶ M` of `𝒪_F`-modules on an algebraic space induces

`𝓗om_{𝒪_F}(M, N) ⟶ 𝓗om_{𝒪_F}(P, N)`,

which over an étale chart `U` sends a morphism `M|_U ⟶ N|_U` of modules on the slice to its
precomposition with `b|_U`.  A morphism of sheaves of modules is a morphism of the underlying
presheaves of modules, so there is nothing to check beyond the first-variable map of the
internal Hom presheaf of Stacks 03EM.  The module universe is free. -/
noncomputable def smallEtaleInternalHomMapLeft {M P : Modules.{u, m} B S hS F hF} (b : P ⟶ M)
    (N : Modules.{u, m} B S hS F hF) :
    smallEtaleInternalHom B S hS F hF M N ⟶ smallEtaleInternalHom B S hS F hF P N where
  val := internalHomMapLeft (G := N.val) (smallEtaleRingedSite B S hS F hF).O.obj b.val

/-- Over an étale chart `U`, the map of
`AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft` is precomposition with the restriction
of `b` to the slice at `U`.  This pins it down on sections. -/
theorem smallEtaleInternalHomMapLeft_val_app {M P : Modules.{u, m} B S hS F hF} (b : P ⟶ M)
    (N : Modules.{u, m} B S hS F hF) (U : (smallEtaleRingedSite B S hS F hF).C)
    (g : ((smallEtaleInternalHom B S hS F hF M N).val.obj (op U) : Type _)) :
    (smallEtaleInternalHomMapLeft B S hS F hF b N).val.app (op U) g =
      ((SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
          U).map b).val ≫ g := rfl

variable {B S hS F hF}

section Presentation

variable {M P Q : Modules.{u, max (u + 1) m} B S hS F hF} {a : Q ⟶ P} {b : P ⟶ M}

/-- Restriction to a slice is additive, so it carries the zero composite of a presentation to a
zero composite.  This is the special case, for the restriction functor of this one site, of the
fact that any functor preserving zero morphisms does so; it is separate because it supplies the
proof term in the *type* of `AlgebraicGeometry.Space.isColimitCokernelCoforkOver`. -/
theorem overFunctor_map_comp_eq_zero (hab : a ≫ b = 0)
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    (SheafOfModules.overFunctor.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U).map a ≫
      (SheafOfModules.overFunctor.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U).map b =
      0 := by
  rw [← Functor.map_comp, hab]
  rfl

/-- **Restriction of `𝒪_F`-modules to the slice at an étale chart carries a presentation to a
presentation.**  This is Stacks 03EJ for the small étale site of an algebraic space:
restriction to a slice is a left adjoint, hence commutes with all colimits, so a cokernel stays
a cokernel.  The input is `Stacks.SheafOfModules.overFunctor_preservesColimits`, which proves
exactly that, and it is the step which makes the exactness statements below unconditional.

`Stacks.SheafOfModules.isColimitCokernelCoforkOver` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension` is the same statement with
the same one-line proof, and it cannot be used here: it pins the module universe to the universe
of the coefficient rings, whereas the internal Hom of `𝒪_F`-modules over `CommRingCat.{u}` lands
in `max (u + 1) m`, and it carries `CategoryTheory.Limits.HasBinaryProducts` and
`CategoryTheory.Limits.HasPullbacks` hypotheses on the site that the small étale site is not
asked for anywhere else in this development. -/
noncomputable def isColimitCokernelCoforkOver (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    IsColimit (CokernelCofork.ofπ ((SheafOfModules.overFunctor.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U).map b)
      (overFunctor_map_comp_eq_zero hab U)) := by
  have _ : PreservesColimitsOfSize.{max (u + 1) m, max (u + 1) m}
      (SheafOfModules.overFunctor.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U) :=
    Stacks.SheafOfModules.overFunctor_preservesColimits _ U
  have _ : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U) :=
    preservesColimitsOfSize_shrink _
  have _ : (SheafOfModules.overFunctor.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        U).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  exact CokernelCofork.mapIsColimit (CokernelCofork.ofπ b hab) hb _

/-- **Precomposition with the surjection of a presentation is injective on the sections of the
internal Hom over every étale chart.**  If `b : P ⟶ M` exhibits `M` as a cokernel, then a
morphism `M|_U ⟶ N|_U` is determined by its precomposition with `b|_U`, because `b|_U` is again
an epimorphism.

No affineness and no quasi-coherence is used, and the chart is arbitrary. -/
theorem injective_smallEtaleInternalHomMapLeft_app (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (N : Modules.{u, max (u + 1) m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    Function.Injective
      ((smallEtaleInternalHomMapLeft B S hS F hF b N).val.app (op U)) := by
  let R := SheafOfModules.overFunctor.{max (u + 1) m}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U
  have : Epi (R.map b) := epi_of_isColimit_cofork (isColimitCokernelCoforkOver hab hb U)
  intro g₁ g₂ h
  have h' : R.map b ≫ (⟨g₁⟩ : M.over U ⟶ N.over U) = R.map b ≫ (⟨g₂⟩ : M.over U ⟶ N.over U) :=
    SheafOfModules.Hom.ext h
  exact congrArg SheafOfModules.Hom.val ((cancel_epi _).1 h')

/-- **The sections of the internal Hom of a presented module are the kernel of the map between
the sections of the internal Homs of the presenting modules.**  For a presentation
`Q --a--> P --b--> M --> 0` of `𝒪_F`-modules and any `N`, the sequence

`𝓗om(M, N)(U) ⟶ 𝓗om(P, N)(U) ⟶ 𝓗om(Q, N)(U)`

is exact over every étale chart `U`: a morphism `P|_U ⟶ N|_U` killing `a|_U` factors uniquely
through `b|_U`.

This is the fragment of Stacks 0GMY(1) that the quasi-coherence clause of Stacks 03M1(6) uses,
at the sheaf level and at a free module universe — not the functor statement, whose sheaf-level
form is still unavailable.  The input is that restriction to a slice preserves the cokernel,
`AlgebraicGeometry.Space.isColimitCokernelCoforkOver`. -/
theorem exact_smallEtaleInternalHomMapLeft_app (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (N : Modules.{u, max (u + 1) m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    Function.Exact ((smallEtaleInternalHomMapLeft B S hS F hF b N).val.app (op U))
      ((smallEtaleInternalHomMapLeft B S hS F hF a N).val.app (op U)) := by
  let R := SheafOfModules.overFunctor.{max (u + 1) m}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U
  intro h
  constructor
  · intro hh
    have hcond : R.map a ≫ (⟨h⟩ : P.over U ⟶ N.over U) = 0 := SheafOfModules.Hom.ext hh
    obtain ⟨G, hG⟩ := CokernelCofork.IsColimit.desc'
      (isColimitCokernelCoforkOver hab hb U) (⟨h⟩ : P.over U ⟶ N.over U) hcond
    exact ⟨G.val, congrArg SheafOfModules.Hom.val hG⟩
  · rintro ⟨g, rfl⟩
    have hzero : R.map a ≫ (R.map b ≫ (⟨g⟩ : M.over U ⟶ N.over U)) = 0 := by
      rw [← Category.assoc, overFunctor_map_comp_eq_zero hab U, zero_comp]
    exact congrArg SheafOfModules.Hom.val hzero

/-- **The base change comparison of the internal Hom of a presented module.**  Let
`Q --a--> P --b--> M --> 0` be a presentation of `𝒪_F`-modules, let `N` be an `𝒪_F`-module and
let `f : V ⟶ U` be a morphism of étale charts along which the restriction map of regular
functions is flat.  If the sections of `𝓗om(P, N)` and of `𝓗om(Q, N)` over `V` are the base
changes of their sections over `U`, then so are the sections of `𝓗om(M, N)`.

The internal Hom of the presented module is a kernel on sections
(`AlgebraicGeometry.Space.exact_smallEtaleInternalHomMapLeft_app`), the comparison is natural
(`AlgebraicGeometry.Space.app_sectionsBaseChange`), and flatness carries the resulting left
exact sequence through the base change — the same commutative-algebra step
`AlgebraicGeometry.Space.bijective_baseChange_of_exact` as for the kernel clause of
Stacks 03M1(3). -/
theorem bijective_sectionsBaseChange_smallEtaleInternalHom (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (N : Modules.{u, max (u + 1) m} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hflat : RingHom.Flat (chartRestrict (hF := hF) f))
    (hP : Function.Bijective (sectionsBaseChange (smallEtaleInternalHom B S hS F hF P N) f))
    (hQ : Function.Bijective (sectionsBaseChange (smallEtaleInternalHom B S hS F hF Q N) f)) :
    Function.Bijective (sectionsBaseChange (smallEtaleInternalHom B S hS F hF M N) f) := by
  let _ := chartAlgebra (hF := hF) f
  have _ : Module.Flat (chartRing B S hS F hF U) (chartRing B S hS F hF V) := hflat
  exact bijective_baseChange_of_exact
    (ιU := ((smallEtaleInternalHomMapLeft B S hS F hF b N).val.app (op U)).hom)
    (φU := ((smallEtaleInternalHomMapLeft B S hS F hF a N).val.app (op U)).hom)
    (ιV := ((smallEtaleInternalHomMapLeft B S hS F hF b N).val.app (op V)).hom)
    (φV := ((smallEtaleInternalHomMapLeft B S hS F hF a N).val.app (op V)).hom)
    (injective_smallEtaleInternalHomMapLeft_app hab hb N U)
    (exact_smallEtaleInternalHomMapLeft_app hab hb N U)
    (injective_smallEtaleInternalHomMapLeft_app hab hb N V)
    (exact_smallEtaleInternalHomMapLeft_app hab hb N V)
    (app_sectionsBaseChange (smallEtaleInternalHomMapLeft B S hS F hF b N) f)
    (app_sectionsBaseChange (smallEtaleInternalHomMapLeft B S hS F hF a N) f) hP hQ

/-- **Being cartesian on affine charts is inherited by the internal Hom of a presented
`𝒪_F`-module, unconditionally.**  If `𝓗om(P, N)` and `𝓗om(Q, N)` are cartesian on affine
charts, and `Q --a--> P --b--> M --> 0` is a presentation, then `𝓗om(M, N)` is cartesian on
affine charts.  Nothing here proves Descent, Proposition 03DX(2); being cartesian on affine
charts is the criterion that proposition characterises quasi-coherence by, and it is used only
as a property stable under the construction.

There is no flatness hypothesis: it is discharged by
`AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine`, both charts being affine and a
morphism of étale charts being étale.  This is the inductive step of the source proof of
Stacks 03M1(6); the base case, for `P` and `Q` *finite* coproducts of copies of the structure
sheaf — in this module universe, of
`SheafOfModules.uliftForPresentation (SheafOfModules.unit _)` — is not proved here, see the
implementation notes. -/
theorem isCartesianOnAffineCharts_smallEtaleInternalHom (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (N : Modules.{u, max (u + 1) m} B S hS F hF)
    (hP : IsCartesianOnAffineCharts (smallEtaleInternalHom B S hS F hF P N))
    (hQ : IsCartesianOnAffineCharts (smallEtaleInternalHom B S hS F hF Q N)) :
    IsCartesianOnAffineCharts (smallEtaleInternalHom B S hS F hF M N) :=
  fun U V hU hV f => bijective_sectionsBaseChange_smallEtaleInternalHom hab hb N f
    (flat_chartRestrict_of_isAffine f hU hV) (hP U V hU hV f) (hQ U V hU hV f)

/-- **Quasi-coherence of the internal Hom of a presented `𝒪_F`-module, conditional on Descent,
Proposition 03DX(2).**  Given a presentation `Q --a--> P --b--> M --> 0` of `𝒪_F`-modules and an
`𝒪_F`-module `N`, if the internal Homs out of the two presenting modules are quasi-coherent then
so is `𝓗om_{𝒪_F}(M, N)`.

`h03DX` is Descent, Proposition 03DX(2) for the small étale site of `F`: an `𝒪_F`-module is
quasi-coherent exactly when it is cartesian on affine charts.  It is not available in the tree
and is carried as a hypothesis, spelled as in
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian` and in
`AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact`; no second spelling is introduced.
One instance of it suffices, because the internal Hom of modules in module universe
`max (u + 1) m` lands again in `max (u + 1) m`.

Everything beyond `h03DX` is
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom`, which is
unconditional. -/
theorem isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (N : Modules.{u, max (u + 1) m} B S hS F hF)
    (h03DX : ∀ G : Modules.{u, max (u + 1) m} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G)
    (hP : (smallEtaleInternalHom B S hS F hF P N).IsQuasicoherentOnSite)
    (hQ : (smallEtaleInternalHom B S hS F hF Q N).IsQuasicoherentOnSite) :
    (smallEtaleInternalHom B S hS F hF M N).IsQuasicoherentOnSite :=
  (h03DX _).2 (isCartesianOnAffineCharts_smallEtaleInternalHom hab hb N
    ((h03DX _).1 hP) ((h03DX _).1 hQ))

end Presentation

end AlgebraicGeometry.Space

end
