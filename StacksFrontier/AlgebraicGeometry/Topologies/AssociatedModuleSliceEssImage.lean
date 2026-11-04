module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcCoveringPullbackSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModulePresentationEssImage
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleSliceConditions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The member-local step of Tag 03OJ on a slice of the site

Let `S` be a scheme and let a site of schemes over `S` be presented by a precoverage `K` on a
category `C` together with a functor `toOver : C ⥤ Over S`, as in Tag 03OJ.  The third assertion
of that tag is that every quasi-coherent `𝒪`-module `𝒢` on the site is `Fᵃ` for a quasi-coherent
`𝒪_S`-module `F`, and the source proves it by reducing to the case of a module with a *global*
presentation (Tag 03DN) and gluing the local answers by fpqc descent.

`Stacks.Sites.essImage_associatedSheafFunctor_of_hasGlobalPresentation` is the globally presented
case.  Tag 03DN, however, does not hand a global presentation of `𝒢` — it hands one of the
restriction `𝒢|_{C/X}` of `𝒢` to the slice at each member `X` of a covering family of the final
object.  **This file is the step that makes the globally presented case applicable there**, and
the only thing in its way is a mismatch of types.

## The mismatch, and why it is not mathematics

Mathlib's `SheafOfModules.over` restricts a module to the slice over the *localized* topology
`K.toGrothendieck.over X`, whereas the slice site of
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleSliceConditions` is presented by the
precoverage `K.comap (CategoryTheory.Over.forget X)` and so inherits the four conditions of
Tag 03OJ for `(K.comap (CategoryTheory.Over.forget X)).toGrothendieck`.  Those two topologies
are *equal*, by `CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget`; but
`CategoryTheory.Sheaf J RingCat` is a different **type** for equal-but-not-definitionally-equal
`J`, so no amount of rewriting moves a module over the one to a module over the other.

The resolution is in two halves, and neither is a rewrite.

* The globally presented case is read at a topology *parameter* `J` together with an equation
  `J = K.toGrothendieck`, which is no weakening — see the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModulePresentationEssImage`.  The slice is
  then the instance `J := K.toGrothendieck.over X`, `K := K.comap (Over.forget X)`, with the
  equation supplied by Mathlib's lemma.
* The restricted module is given the slice site's type by an **ascribed definition**,
  `Stacks.Sites.sliceModuleOver`, and not by a transport: the structure presheaf of the slice
  *is* the restriction of the structure presheaf of the site, on the nose
  (`Stacks.Sites.structurePresheaf_sliceToOver`), so the two sheaves of rings differ only in a
  proof field, and `CategoryTheory.Sheaf` is a full subcategory of presheaves — proof
  irrelevance does the rest.  Ascribing is what keeps this out of a `rw` motive.

## Main definitions

* `Stacks.Sites.sliceModuleOver`: **the slice transport.**  A sheaf of modules on the site,
  restricted to the slice at `X`, read as a sheaf of modules over the structure sheaf of the
  slice site of `Tag 03OJ` at the localized topology.

## Main results

* `Stacks.Sites.isSheaf_structurePresheaf_sliceToOver`: the structure presheaf of the slice site
  is a sheaf for the localized topology.  No new sheaf condition: it is the one carried by the
  site, restricted along `CategoryTheory.Over.forget X`.
* `Stacks.Sites.essImage_associatedSheafFunctor_sliceOver_of_hasGlobalPresentation`: **the
  member-local step of Tag 03OJ on a slice** — if `𝒢|_{C/X}` has a global presentation then it is
  `Fᵃ` for a quasi-coherent module `F` on the underlying scheme of `X`.
* `Stacks.Sites.exists_isQuasicoherent_iso_sliceAssociatedModule_of_hasGlobalPresentation`: the
  same, with the witness and the isomorphism named.
* `Stacks.Sites.isSheaf_associatedPresheaf_sliceToOver`: on a site whose coverings are fpqc
  coverings of schemes, the sheaf condition the member-local step needs on the slice is a
  theorem — condition (4) is inherited by `Stacks.Sites.fpqc_sliceToOver`, and the second
  assertion of the tag is then applied to the slice.
* `Stacks.Sites.exists_cover_essImage_associatedSheafFunctor_sliceOver`: **the member-local step
  of Tag 03OJ, run on a covering family of the final object.**  Every quasi-coherent `𝒪`-module
  on such a site admits a covering family of the final object on whose slices it is an `Fᵃ`.
  This is the input the descent assembly of the third assertion consumes, and the last step of
  the tag that is local.

## Implementation notes

No `@[stacks]` attribute is claimed.  The third assertion of Tag 03OJ is the statement for an
arbitrary quasi-coherent module on the site itself; what is proved here is its restriction to the
slices of a covering family, which is a step of the proof, as the free comparison, the right
exactness, the inheritance of the four conditions by a slice and the globally presented case all
are.  The registrations of the tag stay the two in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcCoveringSiteSheaves`.

**The descent assembly on top of this** is
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleQuasicoherentEssSurj`.  It consumes the
cokernel form of the member-local step,
`Stacks.Sites.exists_cover_cokernel_iso_sliceModuleOver`, because the transitions of its descent
datum are produced by Descent, Lemma 0GN7 over a base that is not affine, which is available for a
source that is a pulled-back cokernel of free modules
(`Stacks.Sites.bijective_associatedModuleMap_cokernel`).

**Faithfulness of the slice functor needs its spelling pinned.**  `Stacks.Sites.sliceToOver` is
an abbreviation for `CategoryTheory.Over.post (toOver ⋙ CategoryTheory.Over.forget S)`, and
Mathlib's instance for the faithfulness of `CategoryTheory.Over.post` does apply; but it does not
*fire* at the abbreviation, because matching the target category `Over ((toOver.obj X).left)`
against `Over (F.obj X)` with `F` a metavariable asks instance search to unfold
`CategoryTheory.Over.forget`, which it will not do.  Naming the functor in the `Over.post` form
with `inferInstanceAs` resolves it, and the result is accepted at the abbreviation's type by
definitional unfolding.  The same is true of
`CategoryTheory.Limits.PreservesLimitsOfShape WalkingCospan` for
`Stacks.Sites.sliceToOver S toOver X ⋙ CategoryTheory.Over.forget ((toOver.obj X).left)`, which
is `CategoryTheory.Over.forget X ⋙ (toOver ⋙ CategoryTheory.Over.forget S)` on the nose
(`Stacks.Sites.sliceToOver_comp_forget`) and is synthesized at that spelling.

`Stacks.essentiallySmall_over` makes condition (1) free on a slice, so the essential smallness
that the globally presented case carries is never an obstruction there.  The three sheafification
classes are declared `local instance` here for the same reason as in
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModulePresentationEssImage`: they are
`local instance` there, so importing that file does not bring them into scope, and restating them
would be a duplicate.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites

open _root_.AlgebraicGeometry

attribute [local instance] CategoryTheory.hasWeakSheafify_addCommGrpCat_of_essentiallySmall
  CategoryTheory.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall
  CategoryTheory.hasSheafify_addCommGrpCat_of_essentiallySmall

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-! ### The slice carries the structure sheaf of the site, restricted -/

/-- **The structure presheaf of the slice site at `X` is a sheaf for the localized topology.**
The underlying scheme of an object of the slice is the underlying scheme of its image in `C`, so
that presheaf *is* the restriction along `CategoryTheory.Over.forget X` of the structure presheaf
of the site (`Stacks.Sites.structurePresheaf_sliceToOver`); the sheaf condition is therefore the
one the site already carries, read through Mathlib's `CategoryTheory.Sheaf.over`. -/
public theorem isSheaf_structurePresheaf_sliceToOver (X : C) (J : GrothendieckTopology C)
    (hR : Presheaf.IsSheaf J (structurePresheaf S toOver)) :
    Presheaf.IsSheaf (J.over X)
      (structurePresheaf ((toOver.obj X).left) (sliceToOver S toOver X)) :=
  ((siteStructureSheaf S toOver J hR).over X).property

/-- **The slice transport.**  A sheaf of `𝒪`-modules on the site, restricted to the slice at `X`
by Mathlib's `SheafOfModules.over`, read as a sheaf of modules over the structure sheaf of the
slice site of Tag 03OJ.

This is an *ascription* and not a transport: the two sheaves of rings have the same underlying
presheaf on the nose, and differ only in the proof that it is a sheaf, which is a proposition.
Naming it as a definition is what keeps the identification out of the motive of a rewrite. -/
public noncomputable abbrev sliceModuleOver (X : C) (J : GrothendieckTopology C)
    (hR : Presheaf.IsSheaf J (structurePresheaf S toOver))
    (𝒢 : SheafOfModules.{u} (siteStructureSheaf S toOver J hR)) :
    SheafOfModules.{u} (siteStructureSheaf ((toOver.obj X).left) (sliceToOver S toOver X)
      (J.over X) (isSheaf_structurePresheaf_sliceToOver S toOver X J hR)) :=
  𝒢.over X

/-- The structure morphism of `X` sliced at itself, read in the schemes over the new base, *is*
the underlying morphism of the comparison `Stacks.Sites.sliceToOverObjIdIso`: the triangle
`CategoryTheory.Over.w` of that comparison has the identity of the new base as its other leg.

Hoisted out of `Stacks.Sites.isIso_sliceToOver_obj_mkId_hom` because both sides cross a
definitional unfolding of `CategoryTheory.Over.mk` — stating the equation first and rewriting
with it keeps that crossing out of the motive. -/
private theorem sliceToOver_obj_mkId_hom_eq (X : C) :
    ((sliceToOver S toOver X).obj (Over.mk (𝟙 X))).hom =
      (sliceToOverObjIdIso S toOver X).hom.left :=
  (Over.w (sliceToOverObjIdIso S toOver X).hom).symm.trans (Category.comp_id _)

/-- The object `X` sliced at itself has invertible structure morphism in the schemes over the new
base: condition (3) of Tag 03OJ for the slice, in the form the globally presented case consumes
it.  This is `Stacks.Sites.sliceToOverObjIdIso` read through `CategoryTheory.Over.w`. -/
public theorem isIso_sliceToOver_obj_mkId_hom (X : C) :
    IsIso ((sliceToOver S toOver X).obj (Over.mk (𝟙 X))).hom := by
  rw [sliceToOver_obj_mkId_hom_eq S toOver X]
  exact inferInstanceAs (IsIso ((Over.forget ((toOver.obj X).left)).map
    (sliceToOverObjIdIso S toOver X).hom))

/-! ### The member-local step of Tag 03OJ on a slice -/

section MemberLocalStep

variable [EssentiallySmall.{u} C] [toOver.Full] [toOver.Faithful] (K : Precoverage C)
  [K.HasPullbacks] [K.IsStableUnderBaseChange]
  (hR : Presheaf.IsSheaf K.toGrothendieck (structurePresheaf S toOver))
  (X : C)
  (hSh : ∀ (M : ((toOver.obj X).left).Modules) (_ : M.IsQuasicoherent),
    Presheaf.IsSheaf (K.toGrothendieck.over X)
      (associatedPresheaf ((toOver.obj X).left) M (sliceToOver S toOver X)))

/-- **The member-local step of the third assertion of Tag 03OJ, on a slice of the site.**  If the
restriction of a sheaf of `𝒪`-modules to the slice at `X` has a global presentation, then it is
the associated module of a quasi-coherent module on the underlying scheme of `X`.

This is `Stacks.Sites.essImage_associatedSheafFunctor_of_hasGlobalPresentation` applied to the
slice site, which is again a site of the kind Tag 03OJ considers over the underlying scheme of
`X`: condition (1) is `Stacks.Sites.sliceToOver_full`, condition (2) is
`Stacks.Sites.zariskiRefinement_sliceToOver`, condition (3) is free there
(`Stacks.Sites.sliceToOverObjIdIso`), and essential smallness is free too
(`Stacks.essentiallySmall_over`).  The topology is the localization
`K.toGrothendieck.over X`, equal to the topology generated by the comapped precoverage but not
definitionally so, which is why the globally presented case is read at a topology parameter. -/
public theorem essImage_associatedSheafFunctor_sliceOver_of_hasGlobalPresentation
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    {𝒢 : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR)}
    (h : (𝒢.over X).HasGlobalPresentation) :
    (associatedSheafFunctor ((toOver.obj X).left) (sliceToOver S toOver X)
        (K.toGrothendieck.over X)
        (isSheaf_structurePresheaf_sliceToOver S toOver X K.toGrothendieck hR) hSh).essImage
      (sliceModuleOver S toOver X K.toGrothendieck hR 𝒢) :=
  have : EssentiallySmall.{u} (Over X) := Stacks.essentiallySmall_over X
  have : (sliceToOver S toOver X).Faithful :=
    inferInstanceAs (Over.post (X := X) (toOver ⋙ Over.forget S)).Faithful
  have := sliceToOver_full S toOver X
  have := isIso_sliceToOver_obj_mkId_hom S toOver X
  essImage_associatedSheafFunctor_of_hasGlobalPresentation ((toOver.obj X).left)
    (sliceToOver S toOver X) (K.comap (Over.forget X)) (K.toGrothendieck.over X)
    (CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget K X)
    (isSheaf_structurePresheaf_sliceToOver S toOver X K.toGrothendieck hR) hSh
    (Over.mk (𝟙 X)) (zariskiRefinement_sliceToOver S toOver K hZariski X) h

/-- **The member-local step of Tag 03OJ on a slice, with the witness named.**  There is a
quasi-coherent module `M` on the underlying scheme of `X` and an isomorphism of `Mᵃ`, formed on
the slice site, with the restriction of `𝒢` to the slice. -/
public theorem exists_isQuasicoherent_iso_sliceAssociatedModule_of_hasGlobalPresentation
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    {𝒢 : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR)}
    (h : (𝒢.over X).HasGlobalPresentation) :
    ∃ (M : ((toOver.obj X).left).Modules) (hM : M.IsQuasicoherent),
      Nonempty (siteAssociatedModule ((toOver.obj X).left) M (sliceToOver S toOver X)
          (K.toGrothendieck.over X)
          (isSheaf_structurePresheaf_sliceToOver S toOver X K.toGrothendieck hR) (hSh M hM) ≅
        sliceModuleOver S toOver X K.toGrothendieck hR 𝒢) := by
  obtain ⟨M, hiso⟩ := essImage_associatedSheafFunctor_sliceOver_of_hasGlobalPresentation
    S toOver K hR X hSh hZariski h
  exact ⟨M.obj, M.property, hiso⟩

/-- **The member-local step of Tag 03OJ on a slice, with the witness a cokernel of free
modules.**  There are a morphism `φ` of free modules on the underlying scheme of `X` and an
isomorphism of `coker(φ)ᵃ`, formed on the slice site, with the restriction of `𝒢` to the slice.
This is `Stacks.Sites.exists_cokernel_iso_of_hasGlobalPresentation` on the slice site, exactly as
`Stacks.Sites.essImage_associatedSheafFunctor_sliceOver_of_hasGlobalPresentation` is the
globally presented case there. -/
public theorem exists_cokernel_iso_sliceModuleOver_of_hasGlobalPresentation
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    {𝒢 : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR)}
    (h : (𝒢.over X).HasGlobalPresentation) :
    ∃ (L L' : Type u) (φ : SheafOfModules.free (R := ((toOver.obj X).left).ringCatSheaf) L' ⟶
        SheafOfModules.free (R := ((toOver.obj X).left).ringCatSheaf) L),
      Nonempty (siteAssociatedModule ((toOver.obj X).left)
          (cokernel (C := ((toOver.obj X).left).Modules) φ) (sliceToOver S toOver X)
          (K.toGrothendieck.over X)
          (isSheaf_structurePresheaf_sliceToOver S toOver X K.toGrothendieck hR)
          (hSh _ inferInstance) ≅
        sliceModuleOver S toOver X K.toGrothendieck hR 𝒢) :=
  have : EssentiallySmall.{u} (Over X) := Stacks.essentiallySmall_over X
  have : (sliceToOver S toOver X).Faithful :=
    inferInstanceAs (Over.post (X := X) (toOver ⋙ Over.forget S)).Faithful
  have := sliceToOver_full S toOver X
  have := isIso_sliceToOver_obj_mkId_hom S toOver X
  exists_cokernel_iso_of_hasGlobalPresentation ((toOver.obj X).left)
    (sliceToOver S toOver X) (K.comap (Over.forget X)) (K.toGrothendieck.over X)
    (CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget K X)
    (isSheaf_structurePresheaf_sliceToOver S toOver X K.toGrothendieck hR) hSh
    (Over.mk (𝟙 X)) (zariskiRefinement_sliceToOver S toOver K hZariski X) h

end MemberLocalStep

/-! ### The sheaf condition on the slice of an fpqc site, and the covering family -/

section Fpqc

variable (K : Precoverage C) [K.HasPullbacks] [K.IsStableUnderBaseChange]
  (hpres : PreservesCoveringFibreProducts K (toOver ⋙ Over.forget S))
  (hfpqc : ∀ (T : C) (Q : Presieve T), Q ∈ K T →
    Presieve.map (toOver ⋙ Over.forget S) Q ∈
      Scheme.fpqcPrecoverage.{u} ((toOver.obj T).left))

include hpres hfpqc in
/-- **The sheaf condition the member-local step needs on a slice is a theorem on a site whose
coverings are fpqc coverings of schemes.**  Condition (4) of Tag 03OJ is inherited by the slice
(`Stacks.Sites.fpqc_sliceToOver`), and so are the fibre products along covering arrows
(`Stacks.Sites.preservesCoveringFibreProducts_comap_overForget`), so the sheaf condition for `Fᵃ`
(`Stacks.Sites.isSheaf_associatedPresheaf_of_preservesCoveringFibreProducts`) applies there; the
topology it produces is the one generated by the comapped precoverage, which is the localized
topology by `CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget`. -/
@[sga "4 VII 4.2" "special case"]
public theorem isSheaf_associatedPresheaf_sliceToOver (X : C)
    (M : ((toOver.obj X).left).Modules) (hM : M.IsQuasicoherent) :
    Presheaf.IsSheaf (K.toGrothendieck.over X)
      (associatedPresheaf ((toOver.obj X).left) M (sliceToOver S toOver X)) := by
  have := hM
  rw [CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget K X]
  exact isSheaf_associatedPresheaf_of_preservesCoveringFibreProducts (K.comap (Over.forget X))
    (sliceToOver S toOver X) (fpqc_sliceToOver S toOver K hfpqc X)
    (preservesCoveringFibreProducts_comap_overForget hpres X) M

variable [EssentiallySmall.{u} C] [toOver.Full] [toOver.Faithful]
  (hR : Presheaf.IsSheaf K.toGrothendieck (structurePresheaf S toOver))

include hpres hfpqc in
/-- **The member-local step of the third assertion of Tag 03OJ, run on a covering family of the
final object.**  A quasi-coherent `𝒪`-module `𝒢` on a site of schemes over `S` satisfying the
conditions of the tag admits a covering family `U` of the final object such that, on the slice at
each member, `𝒢` is the associated module of a quasi-coherent module on the underlying scheme of
that member.

The covering family comes from Tag 03DN
(`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`), which
turns quasi-coherence — a condition local at *every* object — into global presentations on the
slices of one covering family of the final object; the slices are handled by
`Stacks.Sites.essImage_associatedSheafFunctor_sliceOver_of_hasGlobalPresentation`.

This is the whole local content of the third assertion.  What remains between it and the
assertion is the descent assembly, whose outstanding input is recorded in the implementation
notes of this module. -/
public theorem exists_cover_essImage_associatedSheafFunctor_sliceOver
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (𝒢 : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR))
    (h𝒢 : 𝒢.IsQuasicoherentOnSite) :
    ∃ (I : Type (u + 1)) (U : I → C), K.toGrothendieck.CoversTop U ∧
      ∀ i, (associatedSheafFunctor ((toOver.obj (U i)).left) (sliceToOver S toOver (U i))
          (K.toGrothendieck.over (U i))
          (isSheaf_structurePresheaf_sliceToOver S toOver (U i) K.toGrothendieck hR)
          (isSheaf_associatedPresheaf_sliceToOver S toOver K hpres hfpqc (U i))).essImage
        (sliceModuleOver S toOver (U i) K.toGrothendieck hR 𝒢) := by
  obtain ⟨I, U, hU, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation 𝒢).1 h𝒢
  refine ⟨I, U, hU, fun i => ?_⟩
  exact essImage_associatedSheafFunctor_sliceOver_of_hasGlobalPresentation S toOver K hR (U i)
    (isSheaf_associatedPresheaf_sliceToOver S toOver K hpres hfpqc (U i)) hZariski (hP i)

include hpres hfpqc in
/-- **The member-local step of Tag 03OJ on a covering family of the final object, with cokernel
witnesses.**  As `Stacks.Sites.exists_cover_essImage_associatedSheafFunctor_sliceOver`, with the
module on each member exhibited as a cokernel of a morphism of free modules. -/
public theorem exists_cover_cokernel_iso_sliceModuleOver
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (𝒢 : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR))
    (h𝒢 : 𝒢.IsQuasicoherentOnSite) :
    ∃ (I : Type (u + 1)) (U : I → C), K.toGrothendieck.CoversTop U ∧
      ∀ i, ∃ (L L' : Type u)
        (φ : SheafOfModules.free (R := ((toOver.obj (U i)).left).ringCatSheaf) L' ⟶
          SheafOfModules.free (R := ((toOver.obj (U i)).left).ringCatSheaf) L),
        Nonempty (siteAssociatedModule ((toOver.obj (U i)).left)
            (cokernel (C := ((toOver.obj (U i)).left).Modules) φ) (sliceToOver S toOver (U i))
            (K.toGrothendieck.over (U i))
            (isSheaf_structurePresheaf_sliceToOver S toOver (U i) K.toGrothendieck hR)
            (isSheaf_associatedPresheaf_sliceToOver S toOver K hpres hfpqc (U i) _ inferInstance) ≅
          sliceModuleOver S toOver (U i) K.toGrothendieck hR 𝒢) := by
  obtain ⟨I, U, hU, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation 𝒢).1 h𝒢
  exact ⟨I, U, hU, fun i => exists_cokernel_iso_sliceModuleOver_of_hasGlobalPresentation S toOver
    K hR (U i) (isSheaf_associatedPresheaf_sliceToOver S toOver K hpres hfpqc (U i)) hZariski
    (hP i)⟩

include hpres hfpqc in
/-- **The member-local step of Tag 03OJ on a covering family of the site.**  As
`Stacks.Sites.exists_cover_cokernel_iso_sliceModuleOver`, with the members forming one covering
family of an object `e` of the site, in the sense of the precoverage `K`.  This is quasi-coherence
in the form of Stacks 03OH, where the covering is a covering of the site.  The covering family of
the final object given by Tag 03DN generates a covering sieve; by the site axioms (Stacks 00VH,
isomorphisms and composites of coverings are coverings) that sieve contains a covering family
(`CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`), and global
presentations restrict along the arrows of the site
(`Stacks.SheafOfModules.hasGlobalPresentation_overMap`). -/
public theorem exists_covering_cokernel_iso_sliceModuleOver [K.HasIsos]
    [K.IsStableUnderComposition]
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (𝒢 : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR))
    (h𝒢 : 𝒢.IsQuasicoherentOnSite) (e : C) :
    ∃ (ι : Type (u + 1)) (V : ι → C) (π : ∀ i, V i ⟶ e), Presieve.ofArrows V π ∈ K e ∧
      ∀ i, ∃ (L L' : Type u)
        (φ : SheafOfModules.free (R := ((toOver.obj (V i)).left).ringCatSheaf) L' ⟶
          SheafOfModules.free (R := ((toOver.obj (V i)).left).ringCatSheaf) L),
        Nonempty (siteAssociatedModule ((toOver.obj (V i)).left)
            (cokernel (C := ((toOver.obj (V i)).left).Modules) φ) (sliceToOver S toOver (V i))
            (K.toGrothendieck.over (V i))
            (isSheaf_structurePresheaf_sliceToOver S toOver (V i) K.toGrothendieck hR)
            (isSheaf_associatedPresheaf_sliceToOver S toOver K hpres hfpqc (V i) _
              inferInstance) ≅
          sliceModuleOver S toOver (V i) K.toGrothendieck hR 𝒢) := by
  obtain ⟨I, U, hU, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation 𝒢).1 h𝒢
  obtain ⟨R, hR', hle⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition (J := K)).1 (hU e)
  obtain ⟨ι, V, π, rfl⟩ := R.exists_eq_ofArrows
  refine ⟨ι, V, π, hR', fun i => ?_⟩
  obtain ⟨j, ⟨a⟩⟩ := hle _ _ (Presieve.ofArrows.mk i)
  exact exists_cokernel_iso_sliceModuleOver_of_hasGlobalPresentation S toOver K hR (V i)
    (isSheaf_associatedPresheaf_sliceToOver S toOver K hpres hfpqc (V i)) hZariski
    (Stacks.SheafOfModules.hasGlobalPresentation_overMap 𝒢 a (hP j))

end Fpqc

end Stacks.Sites

end
