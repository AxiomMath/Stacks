module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SectionsRestrictHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CollapseCrossingGeometric

/-!
# [Stacks, Tag 01E5] on sections, matched against the factors the `ψ` side of 0EX3 (c) carries

`…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso`
(`SectionsRestrictHigherDirectImage.lean`) is [Stacks, Tag 01E5] on sections over the open, with
no hypothesis: the global sections over the open subscheme `V` of `Rᵈ(f ∣_ V)_*(F|_{f⁻¹V})`, read
over `Γ(Y, V)` through `AlgebraicGeometry.Scheme.Opens.topIso`, are `Γ(Rᵈ f_* F, V)`. It is the
comparison between the two ends of the join of conclusion (c) of [Stacks, Tag 0EX3]: the right-hand
end of `…TopDegreeBaseChange.prefix_transport_eq_openSubschemeSectionsComparison_comp` and the
right-hand end of
`…TopDegreeBaseChange.collapse_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`.

The `ψ` side arrives at that comparison in **different factors**: the first two factors of the
right-hand side of `…TopDegreeBaseChange.collapse_crossing_restrictedMorphism`
(`CollapseCrossingGeometric.lean`) are `…TopDegreeBaseChange.openSubschemeTopSections V` of the
**ringed-space** [Stacks, Tag 01E5] `Stacks.Cohomology.HigherDirectImage`
`.higherDirectImageRestrictIso`, followed by `…TopDegreeBaseChange.restrictCompSectionsIso`. This
file matches the two, factor for factor, by unfolding the scheme-level comparison rather than
building a new one.

## Main results

* `…TopDegreeBaseChange.rightDerivedPlusRestrictObjIso_hom_eq` — **the `ℕ`-versus-`ℤ` index
  entry.** The sheaf-level 01E5 for `CategoryTheory.Functor.rightDerivedPlus` is the `ℕ`-indexed
  comparison `…SchemeHigherDirectImage.higherDirectImageRestrictIso` with
  `Stacks.DerivedIndexing.rightDerivedIso` at the restricted morphism inverted in front and
  `rightDerivedIso` at `f`, read under the restriction to `V`, behind.
* `…TopDegreeBaseChange.higherDirectImageRestrictIso_hom_eq` — **the cast entry.** The
  scheme-level 01E5 is the ringed-space one conjugated by the two functor equalities
  `…SchemeHigherDirectImage.higherDirectImageRestrictIso_source` and `…_target`, which is its
  definition read at the level of natural transformations.
* `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso_hom_eq` — 01E5 on sections is the
  sheaf-level comparison read under the `ψ` side's own outer functor `openSubschemeTopSections V`,
  followed by `AlgebraicGeometry.openSectionsModuleIso`.
* `…TopDegreeBaseChange.restrictCompSectionsIso_hom_app_eq` and
  `…TopDegreeBaseChange.openSectionsModuleIso_hom_eq` — **the second dictionary entry, in both
  directions: `restrictCompSectionsIso` against `openSectionsModuleIso`.** The two differ by one
  cast, the transport along `…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`, and
  by nothing else.
* `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso_hom_eq_cast_comp` — 01E5 on sections
  with that trailing `openSectionsModuleIso` already traded for the cast and
  `restrictCompSectionsIso`, so that the crossing between the two spellings of the sections
  functor is paid against one factor instead of inside a longer chase.
* `…TopDegreeBaseChange.openSubschemeTopSections_map_rightDerivedPlusRestrictObjIso_hom_eq` — the
  index entry read under the `ψ` side's outer functor, with that functor distributed across the
  composite; the match's own first step, named.
* `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso_hom_eq_restrictCompSectionsIso` —
  **the match.** 01E5 on sections is the two index comparisons, the scheme-level sheaf comparison
  read under `openSubschemeTopSections V`, the one cast, and `restrictCompSectionsIso`.

**Nothing is assumed** anywhere in this file: no affineness, no quasi-compactness, no
quasi-separatedness, no quasi-coherence, and no hypothesis on the degree.

## Implementation notes

*Why the identification is a cast and not an identity, which this file does not change.*
`(restrictCompSectionsIso V).hom.app G = (openSectionsModuleIso G V).hom` does not typecheck: the
two sources are `(moduleRestriction Y V ⋙ openSubschemeTopSections V).obj G` and
`(ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj`
`(ModuleCat.of Γ(↑V, ⊤) Γ(G.restrict V.ι, ⊤))`, and the only difference between them is
`AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι` against
`Stacks.Cohomology.HigherDirectImage.moduleRestriction Y V` — which agree by
`…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`, a theorem proved by
`unfold`/`congr 1`/`ext` and **not** by `rfl`, the module structure on the restriction's sections
being restriction of scalars along `(V.ι.appIso ⊤).inv` and
`AlgebraicGeometry.Scheme.Opens.ι_appIso` not being a definitional identity outside Mathlib. So one
`eqToHom` is owed and this file pays it; a second copy of either comparison is not.

*How the cast is discharged: both maps are the same restriction map.* On a section, both
`restrictCompSectionsIso` and `openSectionsModuleIso` are the restriction map of the sheaf of
modules along the equality `V.ι ''ᵁ ⊤ = V` of opens — `…TopDegreeBaseChange`
`.openSectionsImageTopIso_hom_apply` and `AlgebraicGeometry.openSectionsIso_hom_apply` both
exhibit them so, the latter through `Scheme.Modules.restrictAppIso = Iso.refl` — and
`Stacks.Cohomology.HigherDirectImage.heq_val_map_eqToHom` says such a restriction is the identity
up to the transport of the type of sections. That is `heq_restrictCompSectionsIso_hom_app` and
`heq_openSectionsModuleIso_hom`, one application each. The transport itself moves no section,
which is `heq_eqToHom_transport_app`; two maps with the same source and the same target that are
each `HEq` the identity are equal. This is the route
`…TopDegreeBaseChange.preimageSectionsOpenSubschemeIso_eq` (`LerayOpenSubschemeSections.lean`)
takes, and it is taken here for the same reason: `rfl` on the assembled morphisms is a kernel
timeout (see below).

*Four elaboration facts.*

1. **`rfl` on the assembled equations is a `(kernel) deterministic timeout`, not an elaborator
   one.** `rightDerivedPlusRestrictSectionsIso_hom_eq` written with the outer functor applied to
   the whole composite, and the cast entry written with `.app M` on both sides, each **elaborate**
   — no error is reported at either statement or proof — and are then rejected with
   `(kernel) deterministic timeout`, which no raised heartbeat limit could have reached. So is the
   five-factor form of `rightDerivedPlusRestrictObjIso_hom_eq` that names the two `eqToIso` casts
   and the ringed-space comparison at `M` in one equation, although each of its factors on its own
   and the composite of its first two check in seconds. The cure is the discipline the rest of
   this file follows: hoist onto variables. `openSubschemeTopSections_map` and
   `openSubschemeTopSections_map_comp` are the readings of the outer functor on a **variable**
   morphism and on a variable composite, `rfl` and `Functor.map_comp` in under a second each, and
   with them the sections-level unfolding is a `rw` and a small `rfl`; and the cast entry is
   stated at the level of natural transformations, where no object is unfolded.
2. **`simp only` and `rw` do not find their patterns at these spellings, and that is what decides
   every proof here.** Four failures on the elaborated goal, each reporting "did
   not find an occurrence" (verbatim) although the subterm is printed in the goal:
   `CategoryTheory.Iso.trans_hom` and `CategoryTheory.Iso.trans_refl` in
   `(eqToIso _ ≪≫ ringed 01E5 ≪≫ eqToIso _).hom.app M`;
   `CategoryTheory.Functor.map_comp` in `(openSubschemeTopSections V).map (a ≫ b ≫ c)`;
   `CategoryTheory.Category.assoc` in `(a ≫ b ≫ c) ≫ (d ≫ e)` of the match's own goal; and
   `ModuleCat.comp_apply` after `ext x`. Matching is syntactic in the category instance, and the
   definitions involved are elaborated at the ringed-space spelling of the functor categories
   while their declared types are at the scheme spelling. Hence the cast entry is proved by `rfl`
   at the transformation level, the splitting of the outer functor across the composite by
   `openSubschemeTopSections_map_comp` and `congrArg`, the reassociation by
   `Category.assoc` and `congrArg` as **terms**, and the two dictionary entries by
   `ModuleCat.hom_ext (LinearMap.ext …)` rather than `ext`.
3. **A `rw` inside the transport is refused at `implicit` transparency.** Rewriting the reading of
   the outer functor into `heq_eqToHom_transport_app`'s goal — and likewise
   `openSubschemeTopSections_map_comp` into the match's goal — fails with "the target expression
   is not type-correct under the `implicit` transparency level" (verbatim), the offending
   application being `(openSubschemeTopSections V).obj` at an object spelled in
   `(V : Scheme).Modules` while the functor's source is ascribed at the
   `…HigherDirectImage.restrictToOpen` spelling. The step is therefore a **term**: the reading is
   `rfl`, so the general statement's instance inhabits the goal by `exact`, and the splitting is
   `congrArg` at an explicit lambda.
4. **The general transport lemma is proved by `subst` under a `suffices`.** The equality
   `restrictFunctor V.ι = moduleRestriction Y V` has no free variable on either side, so `subst`
   does not apply to it directly; quantifying over the functor and the equality inside the proof
   makes it a local hypothesis and `subst` then discharges the transport. The `ℤ`-indexed
   `Stacks.TensorSheafWorld.heq_eqToHom_val_app` (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorSheafWorldBridge.lean`) is the same
   statement for a family indexed by `ℤ`; the family here is indexed by a functor category, so it
   does not serve and nothing is duplicated. The existing
   `…TopDegreeBaseChange.heq_eqToIso_trans_val_app` (`LerayOpenSubschemeSections.lean`) is the
   same content for `eqToIso e ≪≫ α`, and it does **not** serve either: reaching the transport
   from it needs `Iso.trans_refl` at `α := Iso.refl _`, which is the second failure of
   point 2.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 01E5] carries its own where the two
comparisons are built, and conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file: this file is a dictionary between two readings of 01E5 and no
new tagged result.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ)

/-! ### The two readings of 01E5 at the sheaf level -/

/-- The forward map of a component of a natural isomorphism conjugated by components of two
others, one of them carried by a functor, at variables: so that no component is compared with
another spelling of itself. -/
theorem conj_mapIso_hom {A A' B C : Type*} [Category A] [Category A'] [Category B]
    [Category C] (L : A ⥤ A') {P P' : A' ⥤ C} {T T' : A ⥤ B} (R : B ⥤ C) (ρ : P ≅ P')
    (α : L ⋙ P ≅ T ⋙ R) (σ : T ≅ T') (M : A) :
    ((ρ.app (L.obj M)).symm ≪≫ α.app M ≪≫ R.mapIso (σ.app M)).hom =
      ρ.inv.app (L.obj M) ≫ α.hom.app M ≫ R.map (σ.hom.app M) :=
  rfl

/-- **The `ℕ`-versus-`ℤ` index entry of the match.** The sheaf-level [Stacks, Tag 01E5] for
`CategoryTheory.Functor.rightDerivedPlus` at a natural-number degree is the `ℕ`-indexed comparison
`…SchemeHigherDirectImage.higherDirectImageRestrictIso`, with the comparison of the two indexings
at the restricted morphism inverted in front of it and the comparison at `f` behind it, read under
the restriction to `V`.

This is the definition of `…SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`, whose two
outer factors are exactly the two components of `Stacks.DerivedIndexing.rightDerivedIso`.
Nothing is assumed. -/
theorem rightDerivedPlusRestrictObjIso_hom_eq (M : X.Modules) :
    (rightDerivedPlusRestrictObjIso f V p M).hom =
      (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (f ∣_ V)) p).inv.app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M) ≫
        (SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom.app M ≫
          (Scheme.Modules.restrictFunctor V.ι).map
            ((Stacks.DerivedIndexing.rightDerivedIso
              (Scheme.Modules.pushforward f) p).hom.app M) := by
  unfold rightDerivedPlusRestrictObjIso
  rw [SchemeHigherDirectImage.higherDirectImageRestrictIso_eq_eqToIso_trans]
  exact conj_mapIso_hom _ _ _ _ _ M


/-- **The cast entry of the match.** The scheme-level [Stacks, Tag 01E5] is the ringed-space
comparison `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso` conjugated by the
two functor equalities `…SchemeHigherDirectImage.higherDirectImageRestrictIso_source` and
`…_target`, which package the `f ∣_ V`-versus-`…HigherDirectImage.restrictedMorphism` transport and
the `restrictFunctor`-versus-`moduleRestriction` one.

This is `…SchemeHigherDirectImage.higherDirectImageRestrictIso_eq_eqToIso_trans`, read at the
level of natural transformations. It is stated there and not at a module on purpose: see
points 1 and 2 of this module's implementation notes. -/
theorem higherDirectImageRestrictIso_hom_eq :
    (SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom =
      (eqToIso (higherDirectImageRestrictIso_source f V p)).hom ≫
        (Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
            f.toLRSHom.toShHom V p).hom ≫
          (eqToIso (higherDirectImageRestrictIso_target f V p).symm).hom :=
  congrArg Iso.hom (higherDirectImageRestrictIso_eq_eqToIso_trans f V p)

/-! ### The outer functor the `ψ` side carries -/

/-- **The reading of the `ψ` side's outer functor on a morphism, at variables.** Global sections
over the open subscheme `V` read over `Γ(Y, V)` is global sections followed by restriction of
scalars along `AlgebraicGeometry.Scheme.Opens.topIso`, so it acts on a morphism as the latter does
on the former's value.

Stated at a variable morphism, where it is `rfl` and costs nothing; written out at the composite
the match needs, the same identity is a kernel timeout (point 1 of this module's
implementation notes). -/
theorem openSubschemeTopSections_map {A B : (V : Scheme).Modules} (φ : A ⟶ B) :
    (openSubschemeTopSections (Y := Y) V).map φ =
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
        ((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).map φ) :=
  rfl

/-- **The reading of the `ψ` side's outer functor on a composite, at variables.** The same
`rfl`-free bookkeeping as `openSubschemeTopSections_map`, for a composite of two morphisms, where
`CategoryTheory.Functor.map_comp` does not find its pattern at the spellings the match is stated
in (point 2 of this module's implementation notes). -/
theorem openSubschemeTopSections_map_comp {A B C : (V : Scheme).Modules} (φ : A ⟶ B) (ψ : B ⟶ C) :
    (openSubschemeTopSections (Y := Y) V).map (φ ≫ ψ) =
      (openSubschemeTopSections V).map φ ≫ (openSubschemeTopSections V).map ψ :=
  (openSubschemeTopSections V).map_comp φ ψ

/-- **[Stacks, Tag 01E5] on sections, read under the `ψ` side's outer functor.** The comparison
`…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso` is the sheaf-level comparison
`…SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` read under
`…TopDegreeBaseChange.openSubschemeTopSections V`, followed by
`AlgebraicGeometry.openSectionsModuleIso`. Nothing is assumed. -/
theorem rightDerivedPlusRestrictSectionsIso_hom_eq (M : X.Modules) :
    (rightDerivedPlusRestrictSectionsIso f V p M).hom =
      (openSubschemeTopSections V).map (rightDerivedPlusRestrictObjIso f V p M).hom ≫
        (openSectionsModuleIso
          (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M) V).hom := by
  rw [openSubschemeTopSections_map]
  rfl

/-! ### `restrictCompSectionsIso` against `openSectionsModuleIso` -/

/-- The one cast the second dictionary entry needs: the restriction of a sheaf of modules to the
open subscheme `V` in the ringed-space vocabulary is its restriction in the scheme vocabulary, at
a module. This is `…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` at `M`. -/
theorem moduleRestriction_obj_eq_restrictFunctor_obj (N : Y.Modules) :
    (moduleRestriction Y.toRingedSpace V).obj N = (Scheme.Modules.restrictFunctor V.ι).obj N :=
  Functor.congr_obj (restrictFunctor_eq_moduleRestriction Y V).symm N

/-- **`…TopDegreeBaseChange.restrictCompSectionsIso` is the identity on a section, up to `HEq`.**
It is the restriction map of the sheaf of modules along the equality `V.ι ''ᵁ ⊤ = V` of opens of
`Y`, and restriction along an equality of opens is the identity once the transport of the type of
sections is taken into account. -/
theorem heq_restrictCompSectionsIso_hom_app (N : Y.Modules)
    (x : (moduleRestriction Y.toRingedSpace V ⋙ openSubschemeTopSections V).obj N) :
    HEq ((restrictCompSectionsIso (Y := Y) V).hom.app N x) x :=
  heq_val_map_eqToHom N (Scheme.Opens.ι_image_top V).symm x

/-- **`AlgebraicGeometry.openSectionsModuleIso` is the identity on a section, up to `HEq`.** It is
the same restriction map along `V.ι ''ᵁ ⊤ = V` as the previous lemma's, the comparison
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` its construction carries in front being
`Iso.refl`. -/
theorem heq_openSectionsModuleIso_hom (N : Y.Modules)
    (y : (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
      (ModuleCat.of Γ(↑V, ⊤) Γ(N.restrict V.ι, ⊤))) :
    HEq ((openSectionsModuleIso N V).hom y) y :=
  heq_val_map_eqToHom N (Scheme.Opens.ι_image_top V).symm y

/-- **The cast moves no section.** The transport of the global sections over `V` along an equality
of the two restriction functors changes the type of a section and not the section. Stated in both
directions, which is what the two directions of the dictionary entry consume.

The equality has no free variable on either side, so `subst` reaches it only after the functor and
the equality are quantified over; see point 4 of this module's implementation notes. -/
theorem heq_eqToHom_transport_app {A : Y.Modules ⥤ (V : Scheme).Modules}
    {B : Y.Modules ⥤ (V : Scheme).Modules} (e : A = B) (N : Y.Modules)
    (x : (A ⋙ openSubschemeTopSections V).obj N) :
    HEq ((openSubschemeTopSections V).map (eqToHom (Functor.congr_obj e N)) x) x := by
  suffices h : ∀ (G : Y.Modules ⥤ (V : Scheme).Modules) (e' : A = G)
      (y : (A.obj N).val.obj (op ⊤)),
      HEq ((eqToHom (Functor.congr_obj e' N)).val.app (op ⊤) y) y from h _ e x
  intro G e' y
  subst e'
  exact HEq.rfl

/-- **The second dictionary entry: `…TopDegreeBaseChange.restrictCompSectionsIso` against
`AlgebraicGeometry.openSectionsModuleIso`.** The two identify the global sections over the open
subscheme `V` of a restriction, read over `Γ(Y, V)`, with the sections over `V`; they are the same
morphism up to the one cast along
`…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`, and nothing else differs.

Both are the restriction map along `V.ι ''ᵁ ⊤ = V`, hence each is the identity on a section up to
`HEq`, and so is the cast; two maps with the same source and the same target that are each `HEq`
the identity are equal. Nothing is assumed. -/
theorem restrictCompSectionsIso_hom_app_eq (N : Y.Modules) :
    (restrictCompSectionsIso (Y := Y) V).hom.app N =
      (openSubschemeTopSections V).map
          (eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V N)) ≫
        (openSectionsModuleIso N V).hom :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    eq_of_heq ((heq_restrictCompSectionsIso_hom_app V N x).trans
      ((heq_openSectionsModuleIso_hom V N _).trans
        (heq_eqToHom_transport_app V (restrictFunctor_eq_moduleRestriction Y V).symm N x)).symm))

/-- **The same entry solved for `AlgebraicGeometry.openSectionsModuleIso`**, which is the
direction the match consumes it in: the `γ⁺` side's factor is the cast followed by the `ψ` side's
`…TopDegreeBaseChange.restrictCompSectionsIso`. Nothing is assumed. -/
theorem openSectionsModuleIso_hom_eq (N : Y.Modules) :
    (openSectionsModuleIso N V).hom =
      (openSubschemeTopSections V).map
          (eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V N).symm) ≫
        (restrictCompSectionsIso (Y := Y) V).hom.app N :=
  ModuleCat.hom_ext (LinearMap.ext fun y =>
    eq_of_heq ((heq_openSectionsModuleIso_hom V N y).trans
      ((heq_restrictCompSectionsIso_hom_app V N _).trans
        (heq_eqToHom_transport_app V (restrictFunctor_eq_moduleRestriction Y V) N y)).symm))

/-- **01E5 on sections, unfolded into three factors in the `ψ` side's own vocabulary.**
`rightDerivedPlusRestrictSectionsIso_hom_eq` with its trailing
`AlgebraicGeometry.openSectionsModuleIso` already traded for the cast and
`…TopDegreeBaseChange.restrictCompSectionsIso` by `openSectionsModuleIso_hom_eq`.

Stated because the trade is where the two spellings of the sections functor cross — the source of
`openSectionsModuleIso` is `CategoryTheory.ModuleCat.restrictScalars` of a
`CategoryTheory.ModuleCat.of`, not `openSubschemeTopSections V` of anything — and a chase that
meets the crossing while also carrying the match's other factors pays it at the concrete
composites. Here the crossing is paid once, against a single factor. Nothing is assumed. -/
theorem rightDerivedPlusRestrictSectionsIso_hom_eq_cast_comp (M : X.Modules) :
    (rightDerivedPlusRestrictSectionsIso f V p M).hom =
      (openSubschemeTopSections V).map (rightDerivedPlusRestrictObjIso f V p M).hom ≫
        (openSubschemeTopSections V).map
            (eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V
              (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M)).symm) ≫
          (restrictCompSectionsIso V).hom.app
            (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M) :=
  (rightDerivedPlusRestrictSectionsIso_hom_eq f V p M).trans
    (congrArg
      (fun t => (openSubschemeTopSections V).map
        (rightDerivedPlusRestrictObjIso f V p M).hom ≫ t)
      (openSectionsModuleIso_hom_eq V
        (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M)))

/-! ### The match -/

/-- **The sheaf-level 01E5's three factors, read under the `ψ` side's outer functor.** The
`ℕ`-versus-`ℤ` index entry `rightDerivedPlusRestrictObjIso_hom_eq` read under
`…TopDegreeBaseChange.openSubschemeTopSections V`, with that functor distributed across the
composite by `openSubschemeTopSections_map_comp`.

Named rather than left as a `have` inside the chases that consume it: an instantiation written
inline makes the unifier solve its implicit arguments together with those of the surrounding
gluing, which is a kernel timeout in this family (point 1 of this module's implementation
notes). Nothing is assumed. -/
theorem openSubschemeTopSections_map_rightDerivedPlusRestrictObjIso_hom_eq (M : X.Modules) :
    (openSubschemeTopSections V).map (rightDerivedPlusRestrictObjIso f V p M).hom =
      (openSubschemeTopSections V).map
          ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (f ∣_ V)) p).inv.app
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) ≫
        (openSubschemeTopSections V).map
            ((SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom.app M) ≫
          (openSubschemeTopSections V).map
            ((Scheme.Modules.restrictFunctor V.ι).map
              ((Stacks.DerivedIndexing.rightDerivedIso
                (Scheme.Modules.pushforward f) p).hom.app M)) := by
  have h := rightDerivedPlusRestrictObjIso_hom_eq f V p M
  rw [higherDirectImageRestrictIso_eq_eqToIso_trans] at h ⊢
  exact (congrArg (fun t => (openSubschemeTopSections V).map t) h).trans
    ((openSubschemeTopSections_map_comp V _ _).trans
      (congrArg (fun t => (openSubschemeTopSections V).map _ ≫ t)
        (openSubschemeTopSections_map_comp V _ _)))

/-- **The match of the third step of the tail of conclusion (c) of [Stacks, Tag 0EX3].**
[Stacks, Tag 01E5] on sections — the comparison between the two ends of the join — is, factor for
factor, what the `ψ` side carries:

> the comparison of the two indexings at `f ∣_ V` inverted, the scheme-level sheaf comparison
> `…SchemeHigherDirectImage.higherDirectImageRestrictIso` read under
> `…TopDegreeBaseChange.openSubschemeTopSections V`, the comparison of the two indexings at `f`
> read under the restriction to `V`, the one cast along
> `…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`, and
> `…TopDegreeBaseChange.restrictCompSectionsIso`.

The last factor is the second of the two factors the right-hand side of
`…TopDegreeBaseChange.collapse_crossing_restrictedMorphism` begins with, and the first of those
two is `higherDirectImageRestrictIso_hom_eq` away from the second factor here. **Nothing is
assumed** of `f`, of `V`, of `M` or of `p`. -/
theorem rightDerivedPlusRestrictSectionsIso_hom_eq_restrictCompSectionsIso (M : X.Modules) :
    (rightDerivedPlusRestrictSectionsIso f V p M).hom =
      (openSubschemeTopSections V).map
          ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (f ∣_ V)) p).inv.app
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) ≫
        (openSubschemeTopSections V).map
            ((SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom.app M) ≫
          (openSubschemeTopSections V).map
              ((Scheme.Modules.restrictFunctor V.ι).map
                ((Stacks.DerivedIndexing.rightDerivedIso
                  (Scheme.Modules.pushforward f) p).hom.app M)) ≫
            (openSubschemeTopSections V).map
                (eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V
                  (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M)).symm) ≫
              (restrictCompSectionsIso V).hom.app
                (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M) := by
  refine (rightDerivedPlusRestrictSectionsIso_hom_eq f V p M).trans ?_
  refine (congrArg (fun t => t ≫ (openSectionsModuleIso
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M) V).hom)
      (openSubschemeTopSections_map_rightDerivedPlusRestrictObjIso_hom_eq f V p M)).trans ?_
  rw [openSectionsModuleIso_hom_eq]
  exact (Category.assoc _ _ _).trans
    (congrArg ((openSubschemeTopSections V).map
        ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (f ∣_ V)) p).inv.app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) ≫ ·)
      (Category.assoc _ _ _))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
