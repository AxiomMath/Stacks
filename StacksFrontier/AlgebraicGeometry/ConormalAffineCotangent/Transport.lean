module

public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Sections

/-!
# Transporting the ideal sheaf along an isomorphism of schemes

`StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality` records, in its "What is not done",
that the passage from the affine model to the part (2) assertions of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) needs a transport of
`Stacks.ClosedImmersion.idealSheaf` along an isomorphism of schemes, and states that

> there is no comparison of `Stacks.ClosedImmersion.idealSheaf` for two morphisms related by
> isomorphisms of source and target

This file splits that claim in two and finds it **half false**.

* **The target slot is already done.** An isomorphism of schemes *is* an open immersion, so
  `Stacks.Conormal.pullbackIdealSheafCompIso` and
  `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq` — written for an open immersion in the second
  factor — already transport the pulled-back ideal sheaf along an isomorphism of the target.
  Nothing new is needed and nothing new is proved here; the two definitions below are named
  specializations, so that the next reader finds them.
* **The source slot is genuinely missing**, and this file supplies the part of it that the affine
  computation consumes: over every open, the sections of the ideal sheaf of `α ≫ g` and of `g`
  are canonically identified, for `α` an isomorphism of the source.

## Main results

* `Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget`: the target-slot
  transport, named. A specialization of `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq`.
* `Stacks.Conormal.AffineCotangent.Transport.idealSheafIsoOfIsoTarget`: the same for the ideal
  sheaf alone rather than its pullback, a specialization of
  `Stacks.IdealSheafRestrict.pullbackIdealSheafIso`.
* `Stacks.Conormal.AffineCotangent.Transport.mem_ker_app_comp_iso_iff`: **the source-slot
  content.** For `α` an isomorphism of the source, `α.hom ≫ g` and `g` have the *same* kernel on
  sections over every open of the target.
* `Stacks.Conormal.AffineCotangent.Transport.idealSheafSectionsEquivOfIsoSource`: consequently the
  sections of the two ideal sheaves are canonically bijective, and
  `idealSheafSectionsEquivOfIsoSource_ι` says the bijection is compatible with the two inclusions
  into the structure sheaf — which, by
  `Stacks.Conormal.Locality.idealSheaf_section_injective`, determines it.

## Route

For the target slot, `CategoryTheory.Iso.hom` of an isomorphism of schemes carries an
`AlgebraicGeometry.IsOpenImmersion` instance, found by `inferInstance`; the two definitions are
then applications.

For the source slot, `AlgebraicGeometry.Scheme.Hom.comp_app` factors
`(α.hom ≫ g).app O` as `g.app O ≫ α.hom.app (g ⁻¹ᵁ O)`, and the second factor is an isomorphism
of `CommRingCat` because `α.hom` is, hence injective by
`CategoryTheory.ConcreteCategory.bijective_of_isIso`. Composing an injective map on the left does
not change a kernel. The passage from the equal kernels to bijective sections is
`Stacks.Conormal.AffineCotangent.Sections.idealSheafSectionsEquivKer`, which identifies the
sections of the ideal sheaf over any open with that kernel; this is the step that needs the
companion file and is why it was built.

## What the source slot lacks here, and where it was supplied

The bijection here is **sectionwise and unbundled**. The two declarations this section used to
name as absent from the library are both **now present**, in
`StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic`:

* `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource`: the *isomorphism of
  sheaves of modules* `Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g) ≅`
  `Stacks.ClosedImmersion.idealSheaf g`, with naturality in the open —
  `idealSheafIsoOfIsoSource_hom_val_app` says its sections are the bijection below. Its route is
  *not* the one guessed here: no identification
  `(Scheme.Modules.pushforward α.hom).obj (Stacks.IdealSheafRestrict.unitModule A') ≅`
  `Stacks.IdealSheafRestrict.unitModule A` is built or needed, because the two ideal sheaves are
  kernels of two morphisms **out of the same object**, so the universal property of a kernel
  produces the comparison with no comparison of the targets at all.
* `Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource`: its
  pulled-back form, the analogue of `idealSheafPullbackIsoOfIsoTarget` in the source slot. The
  sheafification inside `RingedSpaceModuleAdjunction.modulePullback` is paid for by
  `Stacks.PullbackPseudofunctor.modulePullbackCompIso`, and its compatibility with the units is
  `Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource_unit`.

What still separates `Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` from
Tag 01R3's `affineConormalIsoCotangentWithQuotient` is therefore **not** the source slot but the
generator formula: `Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` inhabits
the type of part (2) of Tag 01R3, and the tagged declaration itself is the projection of a subtype whose
second component is the generator identity, which nothing yet proves.

## Vocabulary

Tag 01C2's `idealSheaf` is `Stacks.ClosedImmersion.idealSheaf`.

No clause of any Stacks tag is stated here and no
`stacks` attribute is attached.

No hypothesis beyond an isomorphism and a morphism of schemes is used: nothing is affine,
Noetherian, quasi-compact, or an immersion of any kind.

## Universe situation

A single universe `u` (`Scheme.{u}`), as in the statements of Tag 01R3, forced downstream by
`RingedSpaceModuleAdjunction`.

## Transparency gotchas

`(α.hom ≫ g) ⁻¹ᵁ O` and `α.hom ⁻¹ᵁ (g ⁻¹ᵁ O)` are the same open definitionally, which is what
lets `AlgebraicGeometry.Scheme.Hom.comp_app` be used without a transport; the `Γ(-, -)` types on
the two sides of `mem_ker_app_comp_iso_iff` are therefore literally equal and no `eqToHom`
appears.

The isomorphism `α` is taken as a `CategoryTheory.Iso` rather than as a morphism with an `IsIso`
instance, because `AlgebraicGeometry.IsOpenImmersion α.hom` is found by instance search in the
first spelling and the `Equiv` below needs `α.hom.app` to be invertible at a *specific* open,
where a local `have` of `IsIso` is not always consulted.

## What is not done

* **No clause of [Stacks, Tag 01R3] is discharged and no tag is attached.**
* **No sheaf isomorphism in the source slot**, and no naturality for the sectionwise bijection;
  see the section above, which names the two missing declarations.
* **Nothing about `Ideal.Cotangent`**, the quotient by the square of the ideal, or epimorphy of
  the quotient map.
* **No composite transport.** Transporting along isomorphisms of source *and* target at once is
  not stated; it is the composite of the target-slot definitions here with the missing
  source-slot isomorphism.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal.AffineCotangent.Transport

/-! ### The target slot, which needs nothing new -/

/-- **Transport of the pulled-back ideal sheaf along an isomorphism of the target.** For
`g : A ⟶ B`, an isomorphism `β : B ≅ B'` and the composite presented as a named morphism `h`, the
module pullback along `h` of the ideal sheaf of `h` is the module pullback along `g` of the ideal
sheaf of `g`.

This is `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq` at `j := β.hom`, which carries an
`AlgebraicGeometry.IsOpenImmersion` instance because every isomorphism of schemes is an open
immersion. It is named only so that a reader looking for a transport along an isomorphism finds
one; there is no new mathematics in it. -/
noncomputable def idealSheafPullbackIsoOfIsoTarget {A B B' : Scheme.{u}} (g : A ⟶ B)
    (β : B ≅ B') (h : A ⟶ B') (hh : g ≫ β.hom = h) :
    (modulePullback h.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf h.toLRSHom.toShHom) ≅
      (modulePullback g.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom) :=
  Stacks.Conormal.pullbackIdealSheafIsoOfCompEq g β.hom h hh

/-- **Transport of the ideal sheaf itself along an isomorphism of the target**, in pulled-back
form: the module pullback along `β.hom` of the ideal sheaf of `g ≫ β.hom` is the ideal sheaf of
`g`. This is `Stacks.IdealSheafRestrict.pullbackIdealSheafIso` at an isomorphism. -/
noncomputable def idealSheafIsoOfIsoTarget {A B B' : Scheme.{u}} (g : A ⟶ B) (β : B ≅ B') :
    (modulePullback β.hom.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (g ≫ β.hom).toLRSHom.toShHom) ≅
      Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom :=
  Stacks.IdealSheafRestrict.pullbackIdealSheafIso β.hom g

/-! ### The source slot -/

variable {A A' B : Scheme.{u}} (α : A' ≅ A) (g : A ⟶ B) (O : B.Opens)

/-- **Precomposing with an isomorphism does not change the kernel on sections.**
`AlgebraicGeometry.Scheme.Hom.comp_app` factors `(α.hom ≫ g).app O` as `g.app O` followed by
`α.hom.app (g ⁻¹ᵁ O)`, and the latter is an isomorphism of rings, hence injective, so it does not
enlarge the kernel. -/
theorem mem_ker_app_comp_iso_iff (x : Γ(B, O)) :
    x ∈ RingHom.ker ((α.hom ≫ g).app O).hom ↔ x ∈ RingHom.ker (g.app O).hom := by
  have hinj : Function.Injective (α.hom.app (g ⁻¹ᵁ O)).hom :=
    (ConcreteCategory.bijective_of_isIso (α.hom.app (g ⁻¹ᵁ O))).1
  rw [RingHom.mem_ker, RingHom.mem_ker, Scheme.Hom.comp_app]
  refine ⟨fun hx => hinj (hx.trans (map_zero _).symm), fun hx => ?_⟩
  exact Eq.trans (congrArg (α.hom.app (g ⁻¹ᵁ O)).hom hx) (map_zero _)

/-- **The sections of the ideal sheaf are unchanged by an isomorphism of the source.** Over every
open `O` of the target, the sections of the ideal sheaf of `α.hom ≫ g` are canonically bijective
with those of the ideal sheaf of `g`.

Both are the kernel of the map on sections, by
`Stacks.Conormal.AffineCotangent.Sections.idealSheafSectionsEquivKer`, and the two kernels are
equal by `mem_ker_app_comp_iso_iff`. -/
noncomputable def idealSheafSectionsEquivOfIsoSource :
    (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom).val.obj (.op O) ≃
      (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.obj (.op O) :=
  (Sections.idealSheafSectionsEquivKer (α.hom ≫ g) O).trans
    ((Equiv.subtypeEquivRight (mem_ker_app_comp_iso_iff α g O)).trans
      (Sections.idealSheafSectionsEquivKer g O).symm)

/-- **The bijection is the identity on sections of the structure sheaf**, so it is the only
bijection compatible with the two inclusions: by
`Stacks.Conormal.Locality.idealSheaf_section_injective` a section of either ideal sheaf is
determined by its image in `𝒪_B`. -/
theorem idealSheafSectionsEquivOfIsoSource_ι
    (x : (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom).val.obj (.op O)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom g.toLRSHom.toShHom))).val.app (.op O)
        (idealSheafSectionsEquivOfIsoSource α g O x) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (α.hom ≫ g).toLRSHom.toShHom))).val.app (.op O) x := by
  refine Eq.trans (Sections.idealSheafSectionsEquivKer_coe g O _).symm ?_
  refine Eq.trans (congrArg Subtype.val
    ((Sections.idealSheafSectionsEquivKer g O).apply_symm_apply _)) ?_
  exact Sections.idealSheafSectionsEquivKer_coe (α.hom ≫ g) O x

end Stacks.Conormal.AffineCotangent.Transport

end
