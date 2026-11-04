module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# Finite presentation of a module sheaf from an affine open cover

This file supplies the finite-presentation analogue of the locality statements of
`StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal`, which has
`Stacks.AlgebraicGeometry.Modules.isFiniteType_of_restrict` but no counterpart for
`SheafOfModules.IsFinitePresentation`.

The two results are:

* finite presentation of a module sheaf on a scheme follows from a *finite global presentation*
  of its restriction to each member of an open covering, with no hypothesis on the members; and
* on an **affine** open `U`, such a finite global presentation exists as soon as the sections
  `Γ(F, U)` form a finitely presented `Γ(X, U)`-module and `F` is quasi-coherent.

Together they say that a quasi-coherent module sheaf whose modules of sections over the members
of some affine open covering are finitely presented is of finite presentation, which is the
implication (5) ⇒ (3) of [Stacks, Tag 01XZ] with the Noetherian hypothesis of that tag removed
and finiteness of the sections replaced by finite presentation. This is the shape in which the
twists on a relative projective spectrum are shown to be of finite presentation in
[Stacks, Tag 0D4D].

## Main results

* `Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_restrict`: finite
  presentation passes to the restriction along a morphism of schemes.
* `Stacks.AlgebraicGeometry.FinitePresentationLocal.exists_isFinite_presentation_tilde`: the
  `tilde` of a finitely presented module has a finite global presentation.
* `Stacks.AlgebraicGeometry.FinitePresentationLocal.exists_isFinite_presentation_restrict`: a
  quasi-coherent module sheaf whose sections over an affine open `U` are finitely presented has
  a finite global presentation on `U`.
* `Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_presentations`:
  **finite presentation is local on a scheme**, in the form that uses finite global presentations
  of the restrictions to the members of an open covering.
* `Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover`: the
  two combined.

## Implementation notes

Both halves of this file exist already in the development, but only as `private` declarations
inside proofs of other theorems, and in two copies each:
`StacksFrontier/AlgebraicGeometry/CoherenceCriteria/FiniteTildeTFAE.lean`,
`StacksFrontier/AlgebraicGeometry/Descent/Modules/FpqcFinitePresentation.lean` and the
`StacksFrontier/AlgebraicGeometry/Morphisms/WeaklyEtale/RelativeFinitePresentation/FinitePresentation.lean` of
`StacksFrontier/AlgebraicGeometry/Morphisms/WeaklyEtale/` each carry a private
`over_has_finite_global_presentation` and a private `tilde_has_finite_presentation`. The versions
here are public, so that the statement can be used rather than re-proved a fourth time.

Finiteness of the generator and relation index types of a transported presentation is always
established by `change` followed by the finiteness of the original index type: both
`SheafOfModules.Presentation.map` and `AlgebraicGeometry.Scheme.Modules.presentationRestrict`
leave those types unchanged, definitionally. The alternative, the instance
`Presentation.IsFinite.map` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`, would pull in
that file's very large import closure for no gain.

The locality statement takes finite global presentations of the restrictions rather than the
hypothesis `(F.restrict (U i).ι).IsFinitePresentation`, which is strictly weaker and is *not*
enough for the conclusion by any argument available here: turning finite presentation of a sheaf
on an open subscheme back into a finite *global* presentation needs that subscheme to be affine
and the sheaf to be quasi-coherent. The affine case is exactly
`exists_isFinite_presentation_restrict`, so nothing is lost in the intended applications.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 0D4D](https://stacks.math.columbia.edu/tag/0D4D)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FinitePresentationLocal

variable {X : Scheme.{u}}

/-! ### Finite presentation passes to restrictions -/

/-- **Finite presentation passes to the restriction of a module sheaf along a morphism of
schemes**, because the restriction is the pullback and [Stacks, Tag 01BQ] applies to the
pullback. -/
theorem isFinitePresentation_restrict {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (F : X.Modules) (hF : F.IsFinitePresentation) :
    (F.restrict f).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation.{u, u, u} Y.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app F).symm
    (@Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ f.toLRSHom.toShHom F hF)

/-! ### A finite global presentation on an affine open -/

/-- **The `tilde` of a finitely presented module has a finite global presentation.** The
generators and the relations of the presentation of the module are the index types of the
presentation of the sheaf; this is [Stacks, Tag 01PC] in its explicit form. -/
theorem exists_isFinite_presentation_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (hM : Module.FinitePresentation R M) :
    ∃ P : (tilde M).Presentation, P.IsFinite := by
  obtain ⟨s, hs, t, ht⟩ := hM.out
  exact ⟨presentationTilde M (s : Set M) hs (t : Set (s →₀ R)) ht,
    ⟨⟨(inferInstance : Finite s)⟩, ⟨(inferInstance : Finite t)⟩⟩⟩

/-- **A quasi-coherent module sheaf whose sections over an affine open `U` form a finitely
presented module has a finite global presentation on `U`.**

Over an affine open, a quasi-coherent module sheaf is the `tilde` of its module of sections read
through `U ≅ Spec Γ(X, U)`
(`Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde`), and that module is `Γ(F, U)` by
`Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv`. -/
theorem exists_isFinite_presentation_restrict (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U)
    (h : Module.FinitePresentation Γ(X, U) Γ(F, U)) :
    ∃ P : (F.restrict U.ι).Presentation, P.IsFinite := by
  have hM : Module.FinitePresentation Γ(X, U)
      (Stacks.AlgebraicGeometry.CoherentTFAE.specModule F hU) :=
    (Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv F hU).finitePresentation_iff.mpr h
  obtain ⟨P, hP⟩ := exists_isFinite_presentation_tilde _ hM
  let e : (tilde (Stacks.AlgebraicGeometry.CoherentTFAE.specModule F hU)).restrict
        hU.isoSpec.hom ≅ F.restrict U.ι :=
    ((Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app
        (tilde (Stacks.AlgebraicGeometry.CoherentTFAE.specModule F hU))) ≪≫
      (Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde F hU).symm
  exact ⟨@SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom e.isIso_hom
      (Scheme.Modules.presentationRestrict hU.isoSpec.hom P),
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

/-! ### Finite presentation is local on a scheme -/

/-- **A finite global presentation of the restriction of a module sheaf to an open transports to
the localization of the module sheaf at that open.** The transport is along the equivalence
`AlgebraicGeometry.Scheme.Modules.overEquiv`, which carries the structure sheaf to the structure
sheaf and leaves the index types of the presentation unchanged. -/
theorem exists_isFinite_presentation_over (U : X.Opens) (F : X.Modules)
    (P : (F.restrict U.ι).Presentation) (hP : P.IsFinite) :
    ∃ Q : (F.over U).Presentation, Q.IsFinite := by
  let e := Scheme.Modules.overEquiv U
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  have : PreservesColimitsOfSize.{u, u} e.inverse :=
    CategoryTheory.Adjunction.isEquivalence_preservesColimits e.inverse
  have hpres : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} e.inverse := inferInstance
  let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      e.inverse.obj (SheafOfModules.unit (U : Scheme).ringCatSheaf) :=
    (Opens.sheafOfModulesEquivOverInverseUnit U X.ringCatSheaf).symm
  let P' : (e.inverse.obj (F.restrict U.ι)).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P e.inverse hpres η
  let iso : e.inverse.obj (F.restrict U.ι) ≅ F.over U :=
    (e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app F).symm) ≪≫
      (e.unitIso.app (F.over U)).symm
  exact ⟨@SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ iso.hom iso.isIso_hom P',
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

/-- **Finite presentation is local on a scheme.** A module sheaf whose restriction to each member
of an open covering has a finite global presentation is of finite presentation.

No hypothesis is placed on the members of the covering, and none on the module sheaf. This is the
finite-presentation analogue of
`Stacks.AlgebraicGeometry.Modules.isFiniteType_of_restrict`. -/
theorem isFinitePresentation_of_presentations (F : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hcov : IsOpenCover U)
    (h : ∀ i, ∃ P : (F.restrict (U i).ι).Presentation, P.IsFinite) :
    F.IsFinitePresentation :=
  Stacks.SheafOfModules.isFinitePresentation_of_coversTop U
    ((Opens.coversTop_iff X U).2 hcov)
    fun i => exists_isFinite_presentation_over (U i) F (h i).choose (h i).choose_spec

/-- **A quasi-coherent module sheaf which is finitely presented on the members of an affine open
covering is of finite presentation.**

This is the implication (5) ⇒ (3) of [Stacks, Tag 01XZ] with no Noetherian hypothesis: the
condition at a member `U` of the covering is finite presentation of the `Γ(X, U)`-module
`Γ(F, U)`, which on a locally Noetherian scheme is equivalent to its finiteness. -/
theorem isFinitePresentation_of_affineCover (F : X.Modules) [F.IsQuasicoherent] {ι : Type u}
    (U : ι → X.Opens) (hcov : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, Module.FinitePresentation Γ(X, U i) Γ(F, U i)) :
    F.IsFinitePresentation :=
  isFinitePresentation_of_presentations F U hcov
    fun i => exists_isFinite_presentation_restrict F (hU i) (h i)

/-! ### The affine case of the converse -/

/-- **On an affine open, finite presentation of the restriction of a quasi-coherent module sheaf
is finite presentation of its module of sections.**

Read on `Spec Γ(X, U)`, the restriction is the `tilde` of `Γ(F, U)`, so this is
[Stacks, Tag 01PC]. It is the converse of `exists_isFinite_presentation_restrict`, and it is what
makes finite presentation of the restrictions to the members of an *affine* open covering
sufficient for finite presentation. -/
theorem finitePresentation_sections_of_restrict (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (h : (F.restrict U.ι).IsFinitePresentation) :
    Module.FinitePresentation Γ(X, U) Γ(F, U) := by
  have hqc : (Stacks.AlgebraicGeometry.CoherentTFAE.specRestrict F hU).IsQuasicoherent :=
    inferInstance
  have htilde : (tilde
      (Stacks.AlgebraicGeometry.CoherentTFAE.specModule F hU)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation.{u, u, u} (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
      (asIso (Stacks.AlgebraicGeometry.CoherentTFAE.specRestrict F hU).fromTildeΓ).symm
      (isFinitePresentation_restrict hU.isoSpec.inv (F.restrict U.ι) h)
  exact (Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv F hU).finitePresentation_iff.mp
    ((AlgebraicGeometry.tilde_isFinitePresentation_iff _).mp htilde)

/-- **A quasi-coherent module sheaf whose restriction to each member of an affine open covering
is of finite presentation is of finite presentation.**

This is the form of locality that the general
`isFinitePresentation_of_presentations` cannot provide, and the affineness of the members is
exactly what it costs: on an affine open, finite presentation of the restriction can be turned
back into a finite *global* presentation of it, by
`finitePresentation_sections_of_restrict` and `exists_isFinite_presentation_restrict`. -/
theorem isFinitePresentation_of_affineCover_restrict (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hcov : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, (F.restrict (U i).ι).IsFinitePresentation) :
    F.IsFinitePresentation :=
  isFinitePresentation_of_affineCover F U hcov hU
    fun i => finitePresentation_sections_of_restrict F (hU i) (h i)

end Stacks.AlgebraicGeometry.FinitePresentationLocal

end
