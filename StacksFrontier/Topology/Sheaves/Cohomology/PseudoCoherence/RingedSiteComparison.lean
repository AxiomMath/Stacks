module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.IteratedRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import
  StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso

/-!
# Pseudo-coherence on a ringed space is pseudo-coherence on its site of opens

[Stacks, Tag 08CB] defines pseudo-coherence of a complex of `O_X`-modules on a ringed space by
testing on an open neighbourhood of each *point*: a strictly perfect complex over
`X.restrict U` mapping to the restriction of the complex, invertible on cohomology above
degree `m` and epic in degree `m`. [Stacks, Tag 08FT] defines it on a ringed site by testing on
a *covering sieve* of each object: a strictly perfect complex over the slice sheaf of rings.
This file proves that the first implies the second at the ringed site of opens of the space,
`Stacks.SheafOfModules.ringedSite X.sheaf`, which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherent/CoherentCohomology.lean` and of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/TensorHomTorAmplitude.lean` recorded
as having no statement anywhere in this library.

## Main results

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_iff`: the two notions of
  strict perfection agree — `StrictlyPerfect.IsStrictlyPerfect` of [Stacks, Tag 08C4] on a
  ringed space, and the `IsStrictlyPerfect` of [Stacks, Tag 08FL] on the site, at the structure
  sheaf of rings of that space. The module documentation of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/BoundedLocalApproximations.lean`
  records that "neither statement specialises to the other inside Lean"; it does now, and the
  reason it did not is that the two spell `O_X^{⊕n}` differently.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentComplexFrom_ringedSite` and
  `isPseudoCoherentComplex_ringedSite`: the complex-level implication, [Stacks, Tag 08CB] parts
  (1) and (2) into [Stacks, Tag 08FT] parts (1) and (2).
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentFrom_ringedSite`,
  `isPseudoCoherent_ringedSite` and `isPseudoCoherent_ringedSite'`: the implication on derived
  categories, [Stacks, Tag 08CB] part (3) into [Stacks, Tag 08FT] part (3). The primed form
  takes the hypothesis at `AlgebraicGeometry.RingedSpace.IsPseudoCoherent`, the copy of the
  08CB predicates that carries the tag and that the consumers in the duality development
  produce; the two copies are interchangeable because both are `abbrev`s over `rfl`-equal
  restriction functors, and that interchangeability is what the primed statement records.

## The three steps

*The two notions of strict perfection.* Both ask for a bounded complex each of whose terms is a
direct summand of a finite free module, and the categories of modules are literally the same,
`StrictlyPerfect.OXMod X` being `SheafOfModules (structureSheafOfRings X)`. What differs is the
finite free module: the ringed-space notion uses `StrictlyPerfect.finiteFree X n`, the `n`-fold
biproduct of the structure module, and the site notion uses
`SheafOfModules.free (ULift (Fin n))`. `finiteFreeIsoFree` identifies them — Mathlib's
`SheafOfModules.free I` is the coproduct of copies of the unit sheaf indexed by `I`, a finite
biproduct is a coproduct, and `StrictlyPerfect.structureModule X` is the unit sheaf on the nose
— and `isDirectSummandOfFiniteFree_iff` reads a retract of one as a retract of the other.

*The change of model in the local data.* The ringed-space predicate produces a strictly perfect
complex over `X.restrict U`, and the site predicate wants one over the slice
`(structureSheafOfRings X).over U`. `restrictBackward` is the inverse of Mathlib's
`TopologicalSpace.Opens.sheafOfModulesEquivOver`, wrapped as
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`; it carries the unit
sheaf to the unit sheaf by Mathlib's `Opens.sheafOfModulesEquivOverInverseUnit`, so
`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex` applies to it, and
`restrictComplexBackwardIso` identifies its value on the restriction to `U` with the
restriction to the slice over `U`. That identification rests on
`overFunctorIsoRestrictModules`, which holds by `Iso.refl`.

*Shrinking.* The covering sieve of an object `U₀` of the site must consist of opens *contained
in* `U₀`, while the point-local data lives on an open neighbourhood `Uₓ` of each point that need
not be. `hasSiteApproximation_mono` restricts a site approximation along an arrow of the site,
by the same argument as
`Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong` — restriction along an arrow
carries the unit sheaf to the unit sheaf and is exact — restated here because that statement is
available only at module universe `0`, and the site of opens of a ringed space carries its
modules in the universe of the structure rings. With shrinking in hand the covering presieve of
`U₀` is "every open admitting a site approximation", which covers because `U₀ ⊓ Uₓ` is one such
open containing `x`.

## Implementation notes

The module universe is the universe of the structure rings throughout, as it already must be
for [Stacks, Tag 08CB]: `SheafOfModules.free` lands at the ring universe and at no other.

`hasDerivedCategoryRingedSite` re-registers the derived category of `O_X`-modules at the site
spelling of the sheaf of rings. The two spellings are `rfl`-equal but instance search does not
cross them, and `HasDerivedCategory` carries the localized category as data, so the instance is
transported with `inferInstanceAs` rather than re-synthesized: a second instance would give a
second derived category and the statements below would be about a different one.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

universe u d

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

section StrictPerfection

variable (X : RingedSpace.{u, u})

/-- `O_X^{⊕n}`, the `n`-fold biproduct of the structure module, is the free module on
`ULift (Fin n)`. -/
def finiteFreeIsoFree (n : ℕ) :
    StrictlyPerfect.finiteFree X n ≅
      SheafOfModules.free (R := structureSheafOfRings X) (ULift.{u} (Fin n)) :=
  biproduct.isoCoproduct _ ≪≫
    Sigma.whiskerEquiv (f := fun _ : Fin n => StrictlyPerfect.structureModule X)
      (g := fun _ : ULift.{u} (Fin n) => SheafOfModules.unit (structureSheafOfRings X))
      Equiv.ulift.symm (fun _ => Iso.refl _)

/-- The ringed-space and the ringed-site notions of "direct summand of a finite free module"
agree. -/
theorem isDirectSummandOfFiniteFree_iff (E : OXMod.{u, u, u} X) :
    StrictlyPerfect.IsDirectSummandOfFiniteFree E ↔
      _root_.IsDirectSummandOfFiniteFree (structureSheafOfRings X) E := by
  rw [StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract E,
    _root_.isDirectSummandOfFiniteFree_iff_free (structureSheafOfRings X) E]
  constructor
  · rintro ⟨n, ⟨ρ⟩⟩
    exact ⟨n, ρ.i ≫ (finiteFreeIsoFree X n).hom, (finiteFreeIsoFree X n).inv ≫ ρ.r, by
      rw [Category.assoc, Iso.hom_inv_id_assoc, ρ.retract]⟩
  · rintro ⟨n, i, r, hir⟩
    exact ⟨n, ⟨⟨i ≫ (finiteFreeIsoFree X n).inv, (finiteFreeIsoFree X n).hom ≫ r, by
      rw [Category.assoc, Iso.inv_hom_id_assoc, hir]⟩⟩⟩

/-- **The two notions of strict perfection agree.** -/
theorem isStrictlyPerfect_iff (E : CochainComplex (OXMod.{u, u, u} X) ℤ) :
    StrictlyPerfect.IsStrictlyPerfect E ↔
      _root_.IsStrictlyPerfect (structureSheafOfRings X) E :=
  ⟨fun h => ⟨h.bounded, fun i => (isDirectSummandOfFiniteFree_iff X _).1 (h.directSummand i)⟩,
   fun h => ⟨h.bounded, fun i => (isDirectSummandOfFiniteFree_iff X _).2 (h.termDirectSummand i)⟩⟩

end StrictPerfection

section Transport

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- Transport of modules from the open subspace `X|_U` to the slice sheaf of rings over `U`. -/
abbrev restrictBackward :
    OXMod.{u} (X.restrict U.isOpenEmbedding) ⥤
      SheafOfModules.{u} ((structureSheafOfRings X).over U) :=
  (sheafOfModulesEquivRestrict.{u} X U).inverse

/-- The transport functor `restrictBackward X U` is additive. -/
instance restrictBackwardAdditive : (restrictBackward X U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `restrictBackward` carries the unit sheaf to the unit sheaf. -/
def restrictBackwardUnitIso :
    SheafOfModules.unit ((structureSheafOfRings X).over U) ≅
      (restrictBackward X U).obj
        (SheafOfModules.unit (structureSheafOfRings (X.restrict U.isOpenEmbedding))) :=
  (Opens.sheafOfModulesEquivOverInverseUnit U (structureSheafOfRings X)).symm

/-- Restricting to `U` and transporting back to the slice is restricting to the slice. -/
def restrictModulesCompBackwardIso :
    restrictModules.{u} X U ⋙ restrictBackward X U ≅
      SheafOfModules.overFunctor.{u} (structureSheafOfRings X) U :=
  Functor.isoWhiskerRight (overFunctorIsoRestrictModules X U).symm (restrictBackward X U) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafOfModulesEquivRestrict.{u} X U).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The same identification on complexes. -/
def restrictComplexBackwardIso (E : CochainComplex (OXMod.{u} X) ℤ) :
    ((restrictBackward X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (restrictComplex E U) ≅
      (Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E U :=
  (Functor.mapHomologicalComplexCompIso (restrictModulesCompBackwardIso X U)
    (ComplexShape.up ℤ)).app E

/-- **A site-level strictly perfect approximation over the open `W`.** -/
def HasSiteApproximation (X : RingedSpace.{u, u}) (E : CochainComplex (OXMod.{u} X) ℤ) (m : ℤ)
    (W : Opens X.carrier) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} ((structureSheafOfRings X).over W)) ℤ,
    _root_.IsStrictlyPerfect ((structureSheafOfRings X).over W) P ∧
    ∃ α : P ⟶ (Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E W,
      (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
      Epi (HomologicalComplex.homologyMap α m)

/-- **A ringed-space approximation over `U` is a site approximation over `U`.** -/
theorem hasSiteApproximation_of_space (E : CochainComplex (OXMod.{u} X) ℤ) (m : ℤ)
    {P : CochainComplex (OXMod.{u} (X.restrict U.isOpenEmbedding)) ℤ}
    (hP : StrictlyPerfect.IsStrictlyPerfect P)
    (α : P ⟶ restrictComplex E U)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    HasSiteApproximation X E m U := by
  set G := restrictBackward X U
  set Gc := G.mapHomologicalComplex (ComplexShape.up ℤ)
  have hlim : PreservesFiniteLimits G := inferInstance
  have hcol : PreservesFiniteColimits G := inferInstance
  have hhom : G.PreservesHomology := Functor.preservesHomologyOfExact G
  refine ⟨Gc.obj P, ?_, Gc.map α ≫ (restrictComplexBackwardIso X U E).hom, ?_, ?_⟩
  · exact Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex G
      (restrictBackwardUnitIso X U)
      ((isStrictlyPerfect_iff (X.restrict U.isOpenEmbedding) P).1 hP)
  · exact fun j hj => RingedSite.isIso_homologyMap_comp_iso _ _ j
      (RingedSite.isIso_homologyMap_map G α j (hiso j hj))
  · exact RingedSite.epi_homologyMap_comp_iso _ _ m
      (RingedSite.epi_homologyMap_map G α m hepi)

end Transport

section Shrink

variable (X : RingedSpace.{u, u})

/-- **A site approximation shrinks to a smaller open.** -/
theorem hasSiteApproximation_mono (E : CochainComplex (OXMod.{u} X) ℤ) (m : ℤ)
    {U W : Opens X.carrier} (hWU : W ≤ U) (h : HasSiteApproximation X E m U) :
    HasSiteApproximation X E m W := by
  obtain ⟨P, hP, α, hiso, hepi⟩ := h
  set F := SheafOfModules.overMap.{u} (structureSheafOfRings X) (homOfLE hWU)
  have hadd : F.Additive := ⟨by intros; ext V; rfl⟩
  have hlim : PreservesFiniteLimits F :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits (homOfLE hWU)
  have hcol : PreservesFiniteColimits F :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits (homOfLE hWU)
  have hepim : F.PreservesEpimorphisms :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesEpimorphisms (homOfLE hWU)
  have hhom : F.PreservesHomology := Functor.preservesHomologyOfExact _
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, ?_,
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫
      ((Functor.mapHomologicalComplexCompIso
        (SheafOfModules.overFunctorMap.{u} (structureSheafOfRings X) (homOfLE hWU))
        (ComplexShape.up ℤ)).app E).hom, ?_, ?_⟩
  · exact Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
      (SheafOfModules.overMapUnitIso.{u} (R := structureSheafOfRings X) (homOfLE hWU)).symm hP
  · exact fun j hj => RingedSite.isIso_homologyMap_comp_iso _ _ j
      (RingedSite.isIso_homologyMap_map _ α j (hiso j hj))
  · exact RingedSite.epi_homologyMap_comp_iso _ _ m
      (RingedSite.epi_homologyMap_map _ α m hepi)

end Shrink

section Main

variable (X : RingedSpace.{u, u})

/-- **Ringed-space `m`-pseudo-coherence of a complex is `m`-pseudo-coherence on the site of
opens.** -/
theorem isPseudoCoherentComplexFrom_ringedSite
    (E : CochainComplex (OXMod.{u} X) ℤ) (m : ℤ)
    (h : IsPseudoCoherentComplexFrom E m) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherentComplexFrom E m := by
  intro U₀
  refine ⟨fun {W} _ => HasSiteApproximation X E m W, fun x hx => ?_, fun {W} f hf => hf⟩
  obtain ⟨Ux, hxUx, P, hP, α, hiso, hepi⟩ := h x
  exact ⟨U₀ ⊓ Ux, homOfLE inf_le_left, ⟨U₀ ⊓ Ux, 𝟙 _, homOfLE inf_le_left,
    hasSiteApproximation_mono X E m inf_le_right
      (hasSiteApproximation_of_space X Ux E m hP α hiso hepi), Category.id_comp _⟩, hx, hxUx⟩

/-- **Ringed-space pseudo-coherence of a complex is pseudo-coherence on the site of opens.** -/
theorem isPseudoCoherentComplex_ringedSite
    (E : CochainComplex (OXMod.{u} X) ℤ) (h : IsPseudoCoherentComplex E) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherentComplex E :=
  fun m => isPseudoCoherentComplexFrom_ringedSite X E m (h m)

variable [HasDerivedCategory.{d} (OXMod.{u} X)]

/-- The derived category of `O_X`-modules read at the site of opens: the same instance, found
at the other spelling of the sheaf of rings, which instance search does not cross. -/
local instance hasDerivedCategoryRingedSite : HasDerivedCategory.{d}
    (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)) :=
  inferInstanceAs (HasDerivedCategory.{d} (OXMod.{u} X))

/-- **Stacks 08CB (3) implies Stacks 08FT (3), in the `m`-pseudo-coherent form.** -/
theorem isPseudoCoherentFrom_ringedSite (E : DerivedCategory (OXMod.{u} X)) (m : ℤ)
    (h : IsPseudoCoherentFrom E m) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherentFrom E m := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  exact ⟨K, isPseudoCoherentComplexFrom_ringedSite X K m hK, ⟨e⟩⟩

/-- **Stacks 08CB (3) implies Stacks 08FT (3).** -/
theorem isPseudoCoherent_ringedSite (E : DerivedCategory (OXMod.{u} X))
    (h : IsPseudoCoherent E) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherent E := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  exact ⟨K, isPseudoCoherentComplex_ringedSite X K hK, ⟨e⟩⟩

/-- **Stacks 08CB (3) implies Stacks 08FT (3), at the tagged spelling of 08CB.** -/
theorem isPseudoCoherent_ringedSite' (E : DerivedCategory (OXMod.{u} X))
    (h : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X) E) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherent E :=
  isPseudoCoherent_ringedSite X E h

end Main

end AlgebraicGeometry.RingedSpace.PseudoCoherence

end
