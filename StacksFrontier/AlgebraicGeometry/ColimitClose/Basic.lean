module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.SubmoduleAscendingChain
public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction
public import StacksFrontier.AlgebraicGeometry.Colimit.Basic

/-!
# Tag 01PG, the colimit assertion, discharged from Tag 01PF

[Stacks, Tag 01PG] says that on a quasi-compact and quasi-separated scheme a quasi-coherent
`𝒪_X`-module is the **directed colimit of its quasi-coherent submodules of finite type**. Its two
assertions are separately statable and are separately formalized:

* *directedness* — the category of those submodules is filtered — is
  `AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered`, registered against the tag by
  `StacksFrontier/AlgebraicGeometry/AffineSubsheaf/Directedness.lean`;
* *the colimit* — the canonical cocone out of that category, with vertex `F`, is colimiting — was
  reduced in `StacksFrontier/AlgebraicGeometry/Colimit/Basic.lean` to a single hypothesis,
  `Stacks.AlgebraicGeometry.Tag01PGColimit.AffineSections F`: every section of `F` over an affine
  open of `X` is a section of some finite type quasi-coherent submodule of `F` *on the whole of
  `X`*.

This file discharges that hypothesis and so closes the second label. The input is
[Stacks, Tag 01PF] at module level, available as
`Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_isFiniteType_submodule_restrictTo_eq_of_qcqs`.

## Main results

* `affineSections_of_qcqs`: the affine sections statement, on a quasi-compact and quasi-separated
  scheme, for a quasi-coherent module.
* `isColimit_finiteTypeQuasicoherentSubobjectCocone`: **[Stacks, Tag 01PG], the `colimit`
  label**, tagged.
* `mem_obj_spanRestrictSubsheaf_top`: a global section of a quasi-coherent module on an affine
  scheme is a section of the subsheaf it spans.

## The argument

Let `U` be an affine open of `X` and `s` a section of `F` over `U`. Restricting `s` along
`AlgebraicGeometry.Scheme.Opens.ι_image_le` gives a **global** section `s'` of the restriction
`F|_U`, which is quasi-coherent on the affine scheme `U`. The subsheaf of `F|_U` spanned by the
single section `s'`,
`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.spanRestrictSubsheaf (F.restrict U.ι) {s'}`, is
quasi-coherent and — the spanning set being a singleton, hence finite — of finite type. Tag 01PF
extends it to a quasi-coherent submodule `N` of `F` of finite type on all of `X` whose restriction
to `U` is that subsheaf. Since `s'` is a section of the subsheaf over `⊤`, it is a section of `N`
over the image open `U.ι ''ᵁ ⊤`; that one open covers `U`, so locality of `N` puts `s` itself in
`N` over `U`. Finally `N` is turned into a subobject of `F` by
`SheafOfModules.Submodule.toSubobject`, and `s` is in the range of its arrow
over `U` because the sectionwise image of the inclusion of a concrete submodule is that submodule.

## Implementation notes

Three points, all about *spelling* rather than mathematics.

The restriction of `s` is taken along the inequality `U.ι ''ᵁ ⊤ ≤ U`
(`AlgebraicGeometry.Scheme.Opens.ι_image_le`) and **not** along the equality `U.ι ''ᵁ ⊤ = U`
(`ι_image_top`): the open indexes the module the section lives in, so the equality would need an
`eqToHom`. The same choice is why the covering of `U` used for the sheaf condition has the one
member `U.ι ''ᵁ ⊤` — the device recorded in
`Stacks.AlgebraicGeometry.SubmoduleAgree.mem_image_preimage_of_le`, here in the case `Z = W` where
the membership is immediate.

`mem_spanRestrictFamily_top` is stated separately from `mem_obj_spanRestrictSubsheaf_top` because
the sections of a concrete submodule are typed in the `M.val.obj` spelling while
`Module Γ(X, V) Γ(M, V)` is an instance only at the `Γ` spelling: applying `Submodule.subset_span`
directly to a goal produced by rewriting with
`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.obj_spanRestrictSubsheaf` leaves a goal whose ring
is in one spelling and whose module is in the other, and instance search fails. Stating the span
membership at the `spanRestrictFamily` type — where the instances come from that declaration's own
already-elaborated signature — and transporting with `Eq.ge` avoids the synthesis entirely. This is
the `instance_reducible` issue described in
`StacksFrontier/AlgebraicGeometry/AffineSubsheaf/Basic.lean`, met from the other side; no attribute
and no compiler option is needed for it here.

The transport of membership along `restrictTo U.ι N = G` is a `congrArg` of an explicit motive
followed by `Eq.mpr`, as in
`Stacks.AlgebraicGeometry.SubmoduleAgree.obj_eq_of_restrictTo_eq`, and the final identification is
a `congrArg` of `fun f => f.app U t` along
`(toSubobjectIso N).inv ≫ (N.toSubobject).arrow = submoduleι N`. Both avoid `rw`: here
`rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]` fails *pattern-not-found* on an application
already wrapped in `CategoryTheory.ConcreteCategory.hom`, and `rw [Iso.inv_hom_id_assoc]` fails on
a goal that displays the pattern character for character. Both are the keyed-matching barrier of
§8.215; `Iso.inv_comp_eq` and `congrArg` check at default transparency and go through. Zero
compiler options in this file.

`Mono (submoduleι N)` is passed **positionally** to
`Stacks.AlgebraicGeometry.SubmodulePrimitives.obj_ofHom_of_mono`, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/AffineExtend/Basic.lean`: the instance is found by `inferInstance`
but not by an imported lemma's `[Mono f]` binder at the `AlgebraicGeometry.Scheme.Modules`
spelling.

## The tagged statement

The `colimit` label of [Stacks, Tag 01PG] has **one** assertion, and the tag is attached to the one
declaration that is it. Its elaborated binder list is

```
{X : Scheme} → (F : X.Modules) → [CompactSpace ↥X] → [QuasiSeparatedSpace ↥X] →
  [SheafOfModules.IsQuasicoherent F] → Limits.IsColimit (finiteTypeQuasicoherentSubobjectCocone F)
```

— exactly the hypotheses of the Stacks statement, in its order, with nothing added: no
affineness, no Noetherian hypothesis, no separatedness, no smallness. The `example` below is the
Stacks statement transcribed with its own binder list and closed by the tagged declaration, and
`nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone` is the `Nonempty` form in which a
colimit assertion is usually consumed.

The diagram, the cocone and the property are the library's
`AlgebraicGeometry.finiteTypeQuasicoherentSubobjectCocone` and
`AlgebraicGeometry.finiteTypeQuasicoherentSubobjectFunctor`, which transcribe the definitions of
the Stacks statement verbatim, and are the same declarations the `directedness` label is registered
against.

**Two docstrings elsewhere are superseded by this file**:
`StacksFrontier/AlgebraicGeometry/Colimit/Basic.lean` says *"No stacks attribute for the `colimit`
label of 01PG is attached, and none may be"*, and
`StacksFrontier/AlgebraicGeometry/AffineSubsheaf/Directedness.lean` says *"The label
`colimit` of the same tag is **not** registered and may not be"*. Both are superseded
here: `AffineSections F` is proved for every quasi-compact quasi-separated scheme below, so the
hypothesis the first of them calls ungranted is discharged.

## References

* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01PGColimitClose

open Stacks.AlgebraicGeometry.SubmodulePrimitives Stacks.AlgebraicGeometry.SubmoduleRestrict
open Stacks.AlgebraicGeometry.Tag01PFAffineExtend
open Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf

/-! ### A global section spans a subsheaf containing it -/

/-- A global section of `M` lies in the span, over `⊤`, of the restrictions of `{t}`. This is
`Submodule.subset_span` at the one affine open `⊤`, stated at the `spanRestrictFamily` type so
that the module instances are the ones that declaration's signature carries. -/
theorem mem_spanRestrictFamily_top {Y : Scheme.{u}} [IsAffine Y] (M : Y.Modules)
    [M.IsQuasicoherent] (t : Γ(M, ⊤)) :
    t ∈ spanRestrictFamily M {t} ⟨⊤, isAffineOpen_top Y⟩ := by
  refine Submodule.subset_span ⟨t, rfl, ?_⟩
  simp

/-- **A global section of a quasi-coherent module on an affine scheme is a section of the subsheaf
it spans.** -/
theorem mem_obj_spanRestrictSubsheaf_top {Y : Scheme.{u}} [IsAffine Y] (M : Y.Modules)
    [M.IsQuasicoherent] (t : Γ(M, ⊤)) :
    t ∈ (spanRestrictSubsheaf M {t}).obj (op (⊤ : Y.Opens)) :=
  (obj_spanRestrictSubsheaf M {t} ⟨⊤, isAffineOpen_top Y⟩).ge (mem_spanRestrictFamily_top M t)

/-! ### The affine sections statement -/

/-- **The affine sections statement of [Stacks, Tag 01PG], from [Stacks, Tag 01PF].** On a
quasi-compact and quasi-separated scheme, every section of a quasi-coherent module over an affine
open is a section of one of its finite type quasi-coherent submodules.

The submodule is produced by applying Tag 01PF to the subsheaf of `F|_U` spanned by the single
section obtained by restricting `s` to `U.ι ''ᵁ ⊤`. -/
theorem affineSections_of_qcqs {X : Scheme.{u}} (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent] :
    Tag01PGColimit.AffineSections F := by
  intro U s
  have : IsAffine U.1.toScheme := U.2
  set s' : Γ(F.restrict U.1.ι, ⊤) := F.presheaf.map (homOfLE (U.1.ι_image_le ⊤)).op s
  obtain ⟨N, hNqc, hNft, hNres⟩ :=
    exists_isFiniteType_submodule_restrictTo_eq_of_qcqs U.2.isCompact
      (spanRestrictSubsheaf (F.restrict U.1.ι) {s'})
      (isQuasicoherent_spanRestrictSubsheaf _ _)
      (isFiniteType_spanRestrictSubsheaf _ (Set.finite_singleton _))
  have hres : s' ∈ (restrictTo U.1.ι N).obj (op (⊤ : U.1.toScheme.Opens)) :=
    Eq.mpr
      (congrArg (fun Q : (F.restrict U.1.ι).Submodule =>
          s' ∈ Q.obj (op (⊤ : U.1.toScheme.Opens))) hNres)
      (mem_obj_spanRestrictSubsheaf_top (F.restrict U.1.ι) _)
  have hsU : s ∈ N.obj (op U.1) := by
    refine N.isSheaf s fun x hx => ?_
    exact ⟨U.1.ι ''ᵁ ⊤, homOfLE (U.1.ι_image_le ⊤),
      (mem_restrictTo U.1.ι N _).1 hres, ⟨⟨x, hx⟩, trivial, rfl⟩⟩
  have hobj := @obj_ofHom_of_mono X F _ (submoduleι N) (mono_submoduleι N) U.1
  rw [ofHom_submoduleι N] at hobj
  obtain ⟨t, ht⟩ := hobj.le hsU
  refine ⟨⟨N.toSubobject,
    SubmoduleRelativeLocality.isQuasicoherent_of_iso (toSubobjectIso N).symm hNqc,
    AlgebraicGeometry.Modules.isFiniteType_of_iso (toSubobjectIso N).symm hNft⟩,
    (toSubobjectIso N).inv.app U.1 t, ?_⟩
  have hinv : (toSubobjectIso N).inv ≫ (N.toSubobject).arrow = submoduleι N :=
    (Iso.inv_comp_eq _).2 (toSubobjectIso_hom_comp N).symm
  exact (congrArg (fun f : (N.toSheafOfModules : X.Modules) ⟶ F =>
    Scheme.Modules.Hom.app f U.1 t) hinv).trans ht

/-! ### Tag 01PG, the colimit label -/

/-- **Stacks Project, Tag 01PG (colimit).** On a quasi-compact and quasi-separated scheme, a
quasi-coherent module is the colimit of the canonical diagram of all its quasi-coherent finite
type submodules. -/
@[stacks 01PG "colimit"]
def isColimit_finiteTypeQuasicoherentSubobjectCocone {X : Scheme.{u}} (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent] :
    Limits.IsColimit (finiteTypeQuasicoherentSubobjectCocone F) :=
  Tag01PGColimit.isColimit_of_affineSections F (affineSections_of_qcqs F)

/-- The `colimit` label of [Stacks, Tag 01PG] stated with the hypotheses of the Stacks
statement, verbatim and in its order, and closed by the tagged declaration. -/
example {X : Scheme.{u}} (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent] :
    Limits.IsColimit (finiteTypeQuasicoherentSubobjectCocone F) :=
  isColimit_finiteTypeQuasicoherentSubobjectCocone F

/-- `isColimit_finiteTypeQuasicoherentSubobjectCocone` in the `Nonempty` form, which is how a
colimit assertion is usually stated and consumed. -/
theorem nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone {X : Scheme.{u}}
    (F : X.Modules) [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent] :
    Nonempty (Limits.IsColimit (finiteTypeQuasicoherentSubobjectCocone F)) :=
  ⟨isColimit_finiteTypeQuasicoherentSubobjectCocone F⟩

end Stacks.AlgebraicGeometry.Tag01PGColimitClose

end
