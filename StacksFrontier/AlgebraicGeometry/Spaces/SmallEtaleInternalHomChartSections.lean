module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# Reading a section of the internal Hom on a chart

A section of the internal Hom presheaf `𝓗om_O(F, G)` of [Stacks Project, Tag 04TT] over an
object `U` of a site is a *morphism* `F|_U ⟶ G|_U` of presheaves of modules on the slice at `U`.
`PresheafOfModules.InternalHom.internalHomEval` applies such a section to a section of `F` over
`U`, by taking its component at the terminal object `Over.mk (𝟙 U)` of the slice.  This file
records that this reading is a morphism of `O(U)`-modules in the argument and is itself additive
and `O(U)`-linear in the section, and instantiates it on the small étale ringed site of an
algebraic space — in particular on the acting sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` of
[Stacks Project, Tag 061D].

**Why this is wanted.**  The action of that acting sheaf on the sheaf of lifts of
[Stacks Project, Tag 061D] is constructed over an étale scheme chart in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`, and the acting object
there — `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` — is a
`Γ(U, ⊤)`-*linear map* `Γ(a^*Ω_{W/V}, ⊤) ⟶ 𝒞_{U/U'}` of Zariski modules on the chart, not a
morphism of sheaves on a slice of the small étale site.  Comparing the two begins by reading a
section of `AlgebraicGeometry.Space.smallEtaleInternalHom` as a linear map on chart sections,
which is what is supplied here; the two remaining comparisons, of the source and of the target,
are discussed under "What this does not do".

## Main definitions

* `PresheafOfModules.InternalHom.internalHomEvalHom`: the reading of a section of the internal
  Hom over `U` as a morphism `F(U) ⟶ G(U)` of `O(U)`-modules.
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartEval`: the same on the small étale ringed
  site of an algebraic space — a section of `𝓗om_{𝒪_F}(G, G')` over an étale chart `U` read as a
  morphism `G(U) ⟶ G'(U)` of modules over the regular functions on `U`.
* `AlgebraicGeometry.Space.liftActionSheafChartEval`: the same at the acting sheaf of
  [Stacks Project, Tag 061D] — a section of `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` over an étale
  chart `U` of `X` read as a morphism `(a^*Ω_{Y/B})(U) ⟶ 𝒞_{X/X'}(U)`.

## Main results

* `PresheafOfModules.InternalHom.internalHomEvalHom_apply`: its underlying function is
  `PresheafOfModules.InternalHom.internalHomEval`, so the compatibility with the restriction maps
  recorded there applies to it unchanged.
* `PresheafOfModules.InternalHom.internalHomEvalHom_add` and
  `PresheafOfModules.InternalHom.internalHomEvalHom_smul_apply`: the reading is additive and
  `O(U)`-linear in the section.  Together with the previous statement this says that reading a
  section on a chart is a homomorphism of `O(U)`-modules from the sections of the internal Hom to
  the `O(U)`-linear maps on chart sections, which is the form in which an identification of
  acting groups can be stated.

## Implementation notes

The reading needs no `eqToHom` and no transport: the slice site's structure sheaf at the terminal
object `Over.mk (𝟙 U)` *is* `O(U)`, and the restriction of a presheaf of modules evaluated there
*is* its value at `U`, both definitionally, so
`PresheafOfModules.InternalHom.internalHomEvalHom` is the component of the section at that object
with no further data and `PresheafOfModules.InternalHom.internalHomEvalHom_apply` is `rfl`.

Linearity in the section is where the terminal object matters.  Scalar multiplication on the
internal Hom is `PresheafOfModules.InternalHom.smulHom`, postcomposition with multiplication by
the *restriction* of the scalar to each object of the slice; at `Over.mk (𝟙 U)` that restriction
is along `𝟙 U`, so it is the scalar itself.  That is the one computation in
`PresheafOfModules.InternalHom.internalHomEvalHom_smul_apply`, and it needs the functor written
out — `(Oforget O).map_id` rather than `Functor.map_id`, which otherwise resolves to the monadic
`Functor` and fails to rewrite.

Additivity is `rfl`: addition on the internal Hom is pointwise addition of morphisms of
presheaves of modules.

## What this does not do

It does not by itself identify the sections of the acting sheaf with
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`.  That identification is complete
elsewhere — `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection`) — and it is not
built from the reading below: it goes through
`AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv`, which matches the
slice description of a chart-level section with the Zariski one on hom-sets rather than on
values.  Two comparisons enter it, and neither is a reading of the internal Hom:

* **the target.**  `ActionSection` lands in the conormal data of the chart thickening,
  `RingHom.ker i^♯` for the closed immersion `i : U = X ×_{X'} U' ⟶ U'` of schemes, while
  `AlgebraicGeometry.Space.liftActionSheafChartEval` lands in the sections of
  `AlgebraicGeometry.Space.conormalModule` over the chart.  Those sections are the defining ideal
  of the thickening, by `AlgebraicGeometry.Space.firstOrderConormalModuleIso` together with
  `AlgebraicGeometry.Space.definingIdealAt_eq_ker_of_isPullback`
  (`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartSections`) and the sectionwise
  reading of the direct image, which for the representable `i` is
  `AlgebraicGeometry.Space.modulePushforwardChartIso` with
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward_obj_val_obj`;
* **the source.**  `ActionSection` takes the *Zariski* module `a^*Ω_{W/V}` of the chart square as
  its source, and the acting sheaf takes `a^*Ω_{Y/B}` on the small étale site.  The two geometric
  comparisons needed are proved in this tree —
  [Stacks Project, Tag 04CU] as
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` and
  [Stacks Project, Tag 04CS] as
  `AlgebraicGeometry.Space.representedAssociatedDifferentialsIso` — but what they give is an
  isomorphism of *sheaves*, and turning it into a bijection on chart sections needs the
  associated-module comparison of [Stacks Project, Tag 0GN7].  No slice form of it is required:
  the small étale half of that tag holds over an arbitrary scheme, and the hom-set form used is
  `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap`.  That composite is not
  formed here.

No `@[stacks]` attribute is placed.  [Stacks Project, Tag 04TT] is the internal Hom presheaf,
registered where it is built; nothing below asserts a clause of it, or of
[Stacks Project, Tag 061D], whose acting sheaf is registered on
`AlgebraicGeometry.Space.liftActionSheaf`.

## References

* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u t m

namespace PresheafOfModules.InternalHom

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat)
  (F G : PresheafOfModules.{t} (Oforget O))

/-- **Reading a section of the internal Hom over `U` as a morphism of `O(U)`-modules.**  A
section of `internalHom O F G` over `U` is a morphism `F|_U ⟶ G|_U` of presheaves of modules on
the slice at `U`; its component at the terminal object `Over.mk (𝟙 U)` of the slice is a
morphism `F(U) ⟶ G(U)`, with no transport, because the slice's structure sheaf there is `O(U)`
and the restriction of a presheaf of modules there is its value at `U`.

Its underlying function is `PresheafOfModules.InternalHom.internalHomEval`, by
`PresheafOfModules.InternalHom.internalHomEvalHom_apply`. -/
def internalHomEvalHom (U : Cᵒᵖ) (α : (internalHom O F G).obj U) : F.obj U ⟶ G.obj U :=
  α.app (op (Over.mk (𝟙 U.unop)))

/-- The underlying function of `PresheafOfModules.InternalHom.internalHomEvalHom` is
`PresheafOfModules.InternalHom.internalHomEval`, so the compatibility with the restriction maps
of `PresheafOfModules.InternalHom.internalHomEval_naturality` applies to it. -/
theorem internalHomEvalHom_apply (U : Cᵒᵖ) (α : (internalHom O F G).obj U) (x : F.obj U) :
    (internalHomEvalHom O F G U α).hom x = internalHomEval O F G U α x :=
  rfl

/-- Reading a section of the internal Hom on a chart is additive in the section: addition on the
internal Hom is pointwise addition of morphisms of presheaves of modules. -/
theorem internalHomEvalHom_add (U : Cᵒᵖ) (α β : (internalHom O F G).obj U) :
    internalHomEvalHom O F G U (α + β) =
      internalHomEvalHom O F G U α + internalHomEvalHom O F G U β :=
  rfl

/-- **Reading a section of the internal Hom on a chart is `O(U)`-linear in the section.**  The
scalar action on the internal Hom postcomposes with multiplication by the *restriction* of the
scalar to each object of the slice at `U`; at the terminal object `Over.mk (𝟙 U)` that
restriction is along the identity, so it is the scalar itself. -/
theorem internalHomEvalHom_smul_apply (U : Cᵒᵖ) (r : (Oforget O).obj U)
    (α : (internalHom O F G).obj U) (x : F.obj U) :
    (internalHomEvalHom O F G U (r • α)).hom x =
      r • (internalHomEvalHom O F G U α).hom x := by
  change (multEndo O G U.unop r (op (Over.mk (𝟙 U.unop)))).hom
      ((α.app (op (Over.mk (𝟙 U.unop)))).hom x) = _
  have hr : fRestr O U.unop r (op (Over.mk (𝟙 U.unop))) = r := by
    change ((Oforget O).map (𝟙 U.unop).op).hom r = r
    rw [op_id, (Oforget O).map_id]
    rfl
  change fRestr O U.unop r (op (Over.mk (𝟙 U.unop))) •
      ((α.app (op (Over.mk (𝟙 U.unop)))).hom x) = _
  rw [hr]
  rfl

end PresheafOfModules.InternalHom

namespace AlgebraicGeometry.Space

open PresheafOfModules.InternalHom

universe w

variable (B : BigFppfSite.{w}) (S : Scheme.{w}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w) (hF : IsAlgebraicSpace B S hS F)

/-- **Reading a section of the internal Hom of `𝒪_F`-modules on an étale chart.**  A section of
`𝓗om_{𝒪_F}(G, G')` over an étale chart `U` of an algebraic space `F` is a morphism of the
restrictions to the slice at `U`; read at the terminal object of that slice it is a morphism
`G(U) ⟶ G'(U)` of modules over the regular functions on `U`.

This is `PresheafOfModules.InternalHom.internalHomEvalHom` at the small étale ringed site, so
`PresheafOfModules.InternalHom.internalHomEvalHom_add` and
`PresheafOfModules.InternalHom.internalHomEvalHom_smul_apply` say that it is additive and
`Γ(U, ⊤)`-linear in the section. -/
def smallEtaleInternalHomChartEval (G G' : Modules.{w, m} B S hS F hF)
    (U : SmallEtale B S hS F)
    (α : (smallEtaleInternalHom B S hS F hF G G').val.obj (op U)) :
    G.val.obj (op U) ⟶ G'.val.obj (op U) :=
  internalHomEvalHom (smallEtaleRingedSite B S hS F hF).O.obj G.val G'.val (op U) α

variable {Bb X' Y : AlgebraicSpaces B S hS}

/-- **Reading a section of the acting sheaf of [Stacks Project, Tag 061D] on an étale chart of
the subspace.**  A section over an étale chart `U` of `X` of the sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` acting on the lifts of `a : X ⟶ Y` along `X ⊆ X'` is a
morphism `(a^*Ω_{Y/B})(U) ⟶ 𝒞_{X/X'}(U)` of modules over the regular functions on `U`.

This is the shape of `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`, up to the two
comparisons listed under "What this does not do" in the module documentation: its source is the
small-étale `a^*Ω_{Y/B}` rather than the Zariski `a^*Ω_{W/V}` of a chart square, and its target
is the sections of `AlgebraicGeometry.Space.conormalModule` rather than `RingHom.ker i^♯`. -/
def liftActionSheafChartEval (Z : ClosedSubspaces B S hS X'.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (U : SmallEtale B S hS Z.1.toFunctor)
    (α : (liftActionSheaf B S hS Z q a).val.obj (op U)) :
    ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS q)).val.obj (op U) ⟶
      (conormalModule B S hS X' Z).val.obj (op U) :=
  smallEtaleInternalHomChartEval B S hS Z.1.toFunctor Z.2.1 _ _ U α

end AlgebraicGeometry.Space

end
