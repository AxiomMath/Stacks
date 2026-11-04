module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksCore.Tactic.StacksAttribute

/-!
# Left exactness of the direct image of sheaves of modules

Let `(C, J)` and `(D, K)` be sites and let `v : C ⥤ D` be a continuous functor, so that
restriction along `v.op` carries `K`-sheaves to `J`-sheaves and defines the direct image
`v^s = v_* : Sh(D) ⥤ Sh(C)`. Stacks 04BD asserts that for a morphism of sites whose
continuous functor is *almost cocontinuous*, the direct image is exact on sheaves of abelian
groups, and on sheaves of modules for a morphism of ringed sites. In Mathlib's vocabulary
`CategoryTheory.exactFunctor` is the conjunction `PreservesFiniteLimits ∧ PreservesFiniteColimits`
(`CategoryTheory.exactFunctor_iff`), with no `Abelian` instance involved.

This file proves the **left exact** half of both assertions, which needs neither the
morphism-of-sites hypothesis nor almost cocontinuity: the direct image preserves finite limits
for every continuous `v`. The right exact half is where almost cocontinuity is consumed, and is
not proved here; see the implementation notes.

## Main definitions

This file introduces no new definitions.

## Main results

* `CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous`: for a continuous
  functor `v : C ⥤ D` and any value category `A` with finite limits, the direct image
  `v.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` preserves finite limits. At
  `A = AddCommGrpCat` this is the left exact half of Stacks 04BD (1).
* `SheafOfModules.preservesFiniteLimits_pushforward`: the direct image of sheaves of modules
  along a morphism of sheaves of rings over a continuous functor preserves finite limits. This
  is the left exact half of Stacks 04BD (2).
* `SheafOfModules.preservesLimitsOfSize_pushforward`: the same direct image preserves **all**
  limits of shapes small relative to the module universe, by the same two steps; the finite case
  is the one Stacks 04BD (2) asks for, and the general case is what a limit of a diagram indexed
  by the module universe needs, for instance the degreewise limits of graded modules.
* `SheafOfModules.preservesLimitsOfSize_toSheaf`: the inclusion of sheaves of modules into
  `AddCommGrpCat`-valued sheaves preserves those limits, which is the first of those two steps.
* `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`: sheafification of
  `AddCommGrpCat.{w}`-valued presheaves on a site with objects in `Type u` and morphisms in
  `Type v` exists whenever `max u v ≤ w`, and not only when `w = max u v`.
* `CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat`: that
  sheafification inverts exactly the locally bijective morphisms, under the same inequality
  `max u v ≤ w`. This is the hypothesis that makes `Sheaf J AddCommGrpCat.{w}` and
  `SheafOfModules.{w} R` abelian.
* `SheafOfModules.hasFiniteCoproducts`: finite coproducts of sheaves of modules exist at an
  unconstrained module universe.

## Implementation notes

Both left exactness results are proved by the same two steps and are therefore stated with no
hypothesis beyond continuity of `v`, which is strictly more general than the source's morphism of
almost cocontinuous sites: limits of sheaves are computed in presheaves, so it suffices that the
direct image followed by the inclusion of sheaves into presheaves preserves finite limits, and
that composite is the inclusion followed by precomposition with `v.op`, which preserves limits
because limits of presheaves are computed pointwise. In the module case the inclusion
`SheafOfModules.toSheaf` plays the role of the inclusion of sheaves into presheaves; it reflects
limits because it reflects isomorphisms, and the commuting square with the direct image on
`AddCommGrpCat`-valued sheaves holds by definition, so the comparison is `Iso.refl`.

The universes are those forced by the ambient API rather than chosen. The sites are arbitrary
and unrelated, the value category of
`preservesFiniteLimits_sheafPushforwardContinuous` is an arbitrary category with finite limits,
and `SheafOfModules.{m}` keeps its module universe independent of the ring universe. In
particular nothing here needs the sheaf values to live in the site's own universe
`max u v`, which is the restriction that `hasSheafify_addCommGrpCat` lifts: Mathlib's instance
`CategoryTheory.GrothendieckTopology.instHasSheafify` for a concrete value category asks the
underlying types to lie in `Type (max u v)` exactly, whereas transport along a small model of the
site needs no more than that the site be essentially small at the universe of the sections. The
statement here is the `UnivLE` form, which is what makes it applicable at the universe
`max uC vC uD vD` that a statement mentioning two sites at once is forced to use.

The right exact halves are not proved here but downstream, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardRightExact.lean`, which imports this
file: the `UnivLE`-form sheafification results above are exactly what that proof consumes.
For (1) the outcome is complete — `max uC vC uD vD` dominates each site's own universe, so both
sheafification facts are available at the universe the statement is forced to use, and
`CategoryTheory.Functor.exactFunctor_sheafPushforwardContinuous_of_isAlmostCocontinuous` carries
no hypothesis beyond the source's.

For (2) it is not, and the reason is a universe inequality that points the other way. The module
universe of `SheafOfModules.{w} R` occurs in no hypothesis of the statement, so it is a variable
that may lie below the sites. Right exactness goes through
`Functor.preservesHomology_of_preservesEpis_and_kernels` and
`Functor.preservesFiniteColimits_of_preservesHomology`, which need the two categories of sheaves
of modules to be abelian and the source to have cokernels; Mathlib's only producer of either is
`SheafOfModules.instAbelian`, via `PresheafOfModules.sheafificationAdjunction`, hence
`HasSheafify J AddCommGrpCat.{w}` — and that needs `max u v ≤ w`, the colimits of the plus
construction being indexed by `(J.Cover X)ᵒᵖ`, whose object type lies in `Type (max u v)`.
Here `max u v ≤ w` is the hypothesis rather than the conclusion: the free universe is the
*carrier* and the universe that must be dominated is the *index*, so there is nothing to dominate
with, and `UnivLE.{max u v, w}` is not merely unsynthesizable but false for, say, `w = 0` and
`u = 1`. `hasFiniteCoproducts` below records that everything else the argument asks for is
available at an unconstrained `w`. Adding the single inequality as a binder closes (2) at
otherwise unrestricted universes; see, in the namespace
`Stacks.SheafOfModules.PushforwardRightExact`, the declaration
`exactFunctor_pushforward_of_isAlmostCocontinuous_of_univLE`.

## References

* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
* [Stacks Project, Tag 04BA](https://stacks.math.columbia.edu/tag/04BA)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.GrothendieckTopology

/-- Sheafification of `AddCommGrpCat.{w}`-valued presheaves on a site whose objects lie in
`Type u` and whose morphisms lie in `Type v` exists as soon as `max u v ≤ w`. Mathlib's own
instance covers the case `w = max u v`; the extra generality is the universe-inequality form of
`hasSheafify_addCommGrpCat_of_essentiallySmall`, the inequality on the join giving the two
inequalities that make the site essentially small at `w`. -/
public theorem hasSheafify_addCommGrpCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [UnivLE.{max u v, w}] :
    HasSheafify J AddCommGrpCat.{w} :=
  have : UnivLE.{u, w} := @UnivLE.trans.{u, max u v, w} univLE_max.{u, v} ‹_›
  have : UnivLE.{v, w} := @UnivLE.trans.{v, max u v, w} univLE_max.{v, u} ‹_›
  hasSheafify_addCommGrpCat_of_essentiallySmall J

/-! ### Sheafification inverts exactly the locally bijective morphisms, under `max u v ≤ w`

Mathlib's instance for `GrothendieckTopology.WEqualsLocallyBijective` of a concrete value
category asks the underlying types to lie in the site's own `Type (max u v)`, and derives the
statement from the type-valued case through the forgetful functor. The type-valued case is in
turn stated only for presheaves of `Type (max u v)`, because that is where Mathlib's
`GrothendieckTopology.toSheafify` instances are declared. Nothing in the arguments needs the
equality: the plus construction for a *concrete* value category is set up in
`Mathlib/CategoryTheory/Sites/ConcreteSheafification.lean` with the carrier universe free, so
all that is used is that the colimits over the coverings of the site exist in `Type w`, which
is the inequality. The chain is re-run here at `Type w`.
-/

section LocallyBijective

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [UnivLE.{max u v, w}]

open GrothendieckTopology.Plus in
/-- The map to the plus construction of a presheaf of types is locally injective, for values
in any `Type w` with `max u v ≤ w`. -/
public theorem isLocallyInjective_toPlus_of_univLE (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective J (J.toPlus P) where
  equalizerSieve_mem {X} a b h := by
    rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

open GrothendieckTopology.Plus in
/-- The map to the plus construction of a presheaf of types is locally surjective, for values
in any `Type w` with `max u v ≤ w`. -/
@[sga "3 IV 4.3.11" "more general", sga "3 IV 4.3.12" "ℓ_R : R → LR is covering"]
public theorem isLocallySurjective_toPlus_of_univLE (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective J (J.toPlus P) where
  imageSieve_mem a := by
    obtain ⟨S, a, rfl⟩ := exists_rep a
    refine J.superset_covering (fun Y f hf => ⟨a.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using!
      a.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. }

/-- The plus-plus map `J.toSheafify` is the composite of the two `J.toPlus` maps it is defined
to be, with the second one rewritten by `GrothendieckTopology.plusMap_toPlus`. -/
public theorem toPlus_comp_toPlus (P : Cᵒᵖ ⥤ Type w) :
    J.toPlus P ≫ J.toPlus (J.plusObj P) = J.toSheafify P :=
  congrArg (fun m => J.toPlus P ≫ m) (J.plusMap_toPlus P).symm

/-- The plus-plus sheafification map of a presheaf of types is locally injective, for values in
any `Type w` with `max u v ≤ w`. -/
public theorem isLocallyInjective_toSheafify_type_of_univLE (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective J (J.toSheafify P) :=
  have := isLocallyInjective_toPlus_of_univLE J P
  have := isLocallyInjective_toPlus_of_univLE J (J.plusObj P)
  (Presheaf.isLocallyInjective_iff_of_fac J (toPlus_comp_toPlus J P)).2 inferInstance

/-- The plus-plus sheafification map of a presheaf of types is locally surjective, for values in
any `Type w` with `max u v ≤ w`. -/
public theorem isLocallySurjective_toSheafify_type_of_univLE (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective J (J.toSheafify P) :=
  have := isLocallySurjective_toPlus_of_univLE J P
  have := isLocallySurjective_toPlus_of_univLE J (J.plusObj P)
  have h : Presheaf.IsLocallySurjective J (J.toPlus P ≫ J.toPlus (J.plusObj P)) := inferInstance
  toPlus_comp_toPlus J P ▸ h

/-- Sheafification of `AddCommGrpCat.{w}`-valued presheaves commutes with the forgetful functor
to types, under `max u v ≤ w`. -/
public theorem preservesSheafification_forget_addCommGrpCat :
    J.PreservesSheafification (forget AddCommGrpCat.{w}) :=
  have : ∀ Y : C, PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{w}) := fun _ => by
    have : PreservesFilteredColimitsOfSize.{max u v, max u v} (forget AddCommGrpCat.{w}) :=
      preservesFilteredColimitsOfSize_of_univLE.{w, w, max u v, max u v} _
    infer_instance
  instPreservesSheafification J (forget AddCommGrpCat.{w})

/-- Sheafification of `AddCommGrpCat.{w}`-valued presheaves on a site whose objects lie in
`Type u` and whose morphisms lie in `Type v` inverts exactly the locally bijective morphisms as
soon as `max u v ≤ w`. Mathlib's own instance covers the case `w = max u v`; this is what makes
`Sheaf J AddCommGrpCat.{w}` abelian, and, together with
`SheafOfModules.instAbelian`, what makes `SheafOfModules.{w} R` abelian. -/
public theorem wEqualsLocallyBijective_addCommGrpCat :
    J.WEqualsLocallyBijective AddCommGrpCat.{w} := by
  have := hasSheafify_addCommGrpCat.{w} J
  have := preservesSheafification_forget_addCommGrpCat.{w} J
  have : ∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w},
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) := fun P => by
    have := isLocallyInjective_toSheafify_type_of_univLE J (P ⋙ forget AddCommGrpCat.{w})
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    infer_instance
  have : ∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w},
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) := fun P => by
    have := isLocallySurjective_toSheafify_type_of_univLE J (P ⋙ forget AddCommGrpCat.{w})
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    infer_instance
  apply WEqualsLocallyBijective.mk'

end LocallyBijective

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (v : C ⥤ D)
  (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [v.IsContinuous J K]

-- `preservesFiniteLimits_sheafPushforwardContinuous` is NOT declared here. It is imported from
-- `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization`, which proves the same statement
-- at the same generality and carries `@[stacks 04J4 "left exactness of relocalization"]` on it.
-- It was proved twice independently; declaring both made the modules impossible to co-import.
end CategoryTheory.Functor

namespace SheafOfModules

section FiniteCoproducts

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- Finite coproducts of sheaves of modules exist at **any** module universe `w`, with no
sheafification hypothesis: finite limits of sheaves of modules exist unconditionally, and in a
preadditive category finite products are finite biproducts and hence also finite coproducts.

This locates precisely what the right exact half of Stacks 04BD (2) is missing when the module
universe is unconstrained. `Functor.preservesFiniteColimits_of_preservesHomology` asks the source
category for a zero object, finite coproducts and cokernels, and
`Functor.preservesHomology_of_preservesEpis_and_kernels` asks both categories to be abelian; of
those, only cokernels and abelianness are universe-constrained, and both come from
`HasSheafify J AddCommGrpCat.{w}`, which needs `max u v ≤ w` for the site's own `u, v`.

Mathlib keeps `HasFiniteBiproducts.of_hasFiniteProducts` a theorem rather than an instance, so
this is a theorem too and must be applied by name. -/
public theorem hasFiniteCoproducts : HasFiniteCoproducts (SheafOfModules.{w} R) :=
  have : HasFiniteBiproducts (SheafOfModules.{w} R) := HasFiniteBiproducts.of_hasFiniteProducts
  inferInstance

end FiniteCoproducts

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {v : C ⥤ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} [v.IsContinuous J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (v.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The inclusion of sheaves of modules into `AddCommGrpCat`-valued sheaves preserves limits of
every shape small relative to the module universe, and not merely finite ones: composed with the
inclusion of sheaves into presheaves it is the forgetful functor to presheaves of modules
followed by the inclusion into presheaves of abelian groups, both of which preserve those
limits, and the inclusion of sheaves into presheaves reflects them. -/
public noncomputable instance preservesLimitsOfSize_toSheaf :
    PreservesLimitsOfSize.{w, w} (toSheaf.{w} R) :=
  have : PreservesLimitsOfSize.{w, w} (toSheaf.{w} R ⋙ sheafToPresheaf K AddCommGrpCat.{w}) :=
    comp_preservesLimits (SheafOfModules.forget.{w} R) (PresheafOfModules.toPresheaf R.obj)
  preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf K AddCommGrpCat.{w})

/-- **The direct image of sheaves of modules preserves all limits** of shapes small relative to
the module universe, along a morphism of sheaves of rings `φ : S ⟶ v_* R` over a continuous
functor `v : C ⥤ D`. This needs neither the morphism-of-sites hypothesis nor almost cocontinuity:
it is the preservation of limits by the direct image on `AddCommGrpCat`-valued sheaves,
transported along the forgetful functor `SheafOfModules.toSheaf`, which reflects limits and makes
the relevant square commute on the nose. -/
@[sga "4 IV 13.6" "more general"]
public noncomputable instance preservesLimitsOfSize_pushforward :
    PreservesLimitsOfSize.{w, w} (pushforward.{w} φ) := by
  have hr : ReflectsLimitsOfSize.{w, w} (toSheaf.{w} S) := reflectsLimits_of_reflectsIsomorphisms
  have hv : PreservesLimitsOfSize.{w, w}
      (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := ⟨fun {_T} _ => inferInstance⟩
  have : PreservesLimitsOfSize.{w, w} (pushforward.{w} φ ⋙ toSheaf.{w} S) :=
    preservesLimits_of_natIso
      (F := toSheaf.{w} R ⋙ v.sheafPushforwardContinuous AddCommGrpCat.{w} J K) (Iso.refl _)
  exact preservesLimits_of_reflects_of_preserves _ (toSheaf.{w} S)

/-- **Left exact half of Stacks 04BD (2).** The direct image of sheaves of modules along a
morphism of sheaves of rings `φ : S ⟶ v_* R` over a continuous functor `v : C ⥤ D` preserves
finite limits. As for (1) this needs neither the morphism-of-sites hypothesis nor almost
cocontinuity: it is the left exactness of the direct image on `AddCommGrpCat`-valued sheaves,
transported along the forgetful functor `SheafOfModules.toSheaf`, which reflects limits and makes
the relevant square commute on the nose. -/
@[ega "0 4.2.1" "more general", sga "4 IV 13.6" "more general"]
public instance preservesFiniteLimits_pushforward :
    PreservesFiniteLimits (pushforward.{w} φ) := by
  refine ⟨fun I _ _ => ?_⟩
  have hr : ReflectsLimitsOfShape I (toSheaf.{w} S) := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape I (pushforward.{w} φ ⋙ toSheaf.{w} S) :=
    preservesLimitsOfShape_of_natIso
      (F := toSheaf.{w} R ⋙ v.sheafPushforwardContinuous AddCommGrpCat.{w} J K) (Iso.refl _)
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (toSheaf.{w} S)

end SheafOfModules
