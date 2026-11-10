module

public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Transport
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic

/-!
# The source slot: transporting the ideal sheaf along an isomorphism of the source

`StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Transport` splits the obstruction
recorded in `StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality` — that there is no
comparison of `Stacks.ClosedImmersion.idealSheaf` for two morphisms related by isomorphisms of
source and target — into a target slot, which it finds already done, and a source slot, for
which it supplies only the *sectionwise* bijection
`Stacks.Conormal.AffineCotangent.Transport.idealSheafSectionsEquivOfIsoSource` and names the two
declarations still missing. This file supplies those two, so the source slot is now done as well,
at the level of sheaves of modules and of their module pullbacks.

For `α : A' ≅ A` an isomorphism of schemes and `g : A ⟶ B` an arbitrary morphism, the ideal
sheaves of `α.hom ≫ g` and of `g` are canonically isomorphic as sheaves of `𝒪_B`-modules, and the
isomorphism is compatible with the two inclusions into `𝒪_B`, hence with everything the statements
of [Stacks, Tag 01R3] compute with.

## Main results

* `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource`: **the first of the
  two.** An isomorphism of sheaves of modules
  `Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g) ≅ Stacks.ClosedImmersion.idealSheaf g`.
* `idealSheafIsoOfIsoSource_hom_comp_ι` and `idealSheafIsoOfIsoSource_inv_comp_ι`: it commutes
  with the two inclusions into the structure sheaf. Those inclusions are monomorphisms, so this
  *determines* the isomorphism — no other morphism makes the square commute.
* `idealSheafIsoOfIsoSource_hom_val_app`: **the naturality that was missing.** On sections over
  every open, the isomorphism is the sectionwise bijection
  `Stacks.Conormal.AffineCotangent.Transport.idealSheafSectionsEquivOfIsoSource`. So that
  `Equiv` is now the restriction of a morphism of sheaves, which is exactly what was unproved.
* `Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource`:
  **the second of the two.** The pulled-back form: the module pullback along `α.hom ≫ g` of the
  ideal sheaf of `α.hom ≫ g` is the module pullback along `α.hom` of the module pullback along
  `g` of the ideal sheaf of `g`. This is the source-slot analogue of
  `Stacks.Conormal.pullbackIdealSheafCompIso`, and it is where compatibility with the
  sheafification inside `RingedSpaceModuleAdjunction.modulePullback` is paid for.
* `idealSheafIsoOfIsoSourceOfCompEq` and `modulePullbackIdealSheafIsoOfIsoSourceOfCompEq`: the
  same two with the composite presented as a separately named morphism together with an equation,
  which is the form a factorization statement supplies.
* `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSourceTarget`: the composite
  transport, along isomorphisms of source *and* target at once, which
  `StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Transport` records as not stated.
* `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare`: the composite
  transport in the shape it is actually handed over in — a commuting square `f ≫ β.hom = ε.hom ≫ k`
  with `ε` and `β` isomorphisms yields `idealSheaf f ≅ β.hom^* (idealSheaf k)`.
* `idealSheafIsoAffineModelOfPullbackSnd` and `idealSheafIsoAffineModelOfMorphismRestrict`: that
  square at the *hypotheses of [Stacks, Tag 01R3] itself*. The part (2) clauses of
  [Stacks, Tag 01R3] hand over an affine open `V`, an ideal `I` of `Γ(X, V)`, an isomorphism
  `e : Z ×_X V ≅ Spec (Γ(X, V) ⧸ I)` and a compatibility `he` with the projections to
  `Spec Γ(X, V)`; these two take that data unchanged and return the identification of the ideal
  sheaf of the fibre — of `pullback.snd i V.ι` and of `i ∣_ V` respectively — with the module
  pullback of the ideal sheaf of the affine model
  `Spec (Γ(X, V) ⧸ I) ⟶ Spec Γ(X, V)` whose sections
  `Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` computes. Neither assumes `i` is an
  immersion.

## Route

The two obvious routes both go through an identification
`(Scheme.Modules.pushforward α.hom).obj (unitModule A') ≅ unitModule A` commuting with the two
structure maps, after which `CategoryTheory.Limits.kernel.mapIso` finishes. That identification is
*not* built here, and is not needed: the two ideal sheaves are kernels of two morphisms **out of
the same object** `Stacks.IdealSheafRestrict.unitModule B`, so the universal property of a kernel
produces the comparison directly from the vanishing of two composites, with no comparison of the
targets at all.

Concretely:

* `ι_comp_structureMap_eq_zero` says `kernel.ι (structureMap (α.hom ≫ g)) ≫ structureMap g = 0`.
  A morphism of sheaves of modules is zero exactly when it is zero on sections over every open
  (`AlgebraicGeometry.Scheme.Modules.hom_ext`, with
  `AlgebraicGeometry.Scheme.Modules.Hom.zero_app` and `Hom.comp_app` both holding by `rfl`), and
  on sections this is `Stacks.Conormal.AffineCotangent.Sections.app_idealSheaf_section_eq_zero`
  followed by the forward direction of
  `Stacks.Conormal.AffineCotangent.Transport.mem_ker_app_comp_iso_iff`.
* `ι_comp_structureMapComp_eq_zero` is the same with the two morphisms exchanged, using the
  backward direction of the same iff.
* `CategoryTheory.Limits.kernel.lift` on each then gives the two morphisms, and
  `CategoryTheory.Limits.kernel.lift_ι` together with `kernel.ι` being a monomorphism gives the
  two round trips.

The pulled-back form is then `Stacks.PullbackPseudofunctor.modulePullbackCompIso`, which splits
`(α.hom ≫ g)^*` as `α.hom^* ∘ g^*`, followed by the sheaf isomorphism under the two pullbacks.
Pseudofunctoriality of the pullback is proved by uniqueness of a left adjoint, so the
sheafification inside `RingedSpaceModuleAdjunction.modulePullback` is handled there and not here.

## Vocabulary

Tag 01C2's `idealSheaf` is `Stacks.ClosedImmersion.idealSheaf`.

No labelled clause of any tag is stated here and no
`stacks` attribute is attached. This is an input to the part (2) assertions of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3).

No hypothesis beyond an isomorphism and a morphism of schemes is used: nothing is affine,
Noetherian, quasi-compact, or an immersion of any kind. In particular `g` is not assumed to be a
closed immersion, so this applies to the comparison of an arbitrary morphism with its affine
model.

## Universe situation

A single universe `u` (`Scheme.{u}`), as in the statements of Tag 01R3, forced downstream by
`RingedSpaceModuleAdjunction`.

## Transparency gotchas

Two spellings of one category are in play, as throughout this development:
`AlgebraicGeometry.Scheme.Modules B` and
`SheafOfModules (structureSheafRing B.toSheafedSpace)`. They agree definitionally but not at the
elaborator's implicit transparency, and here the split is sharp:

* The *vanishing* statements and the kernel comparison are written in the
  `AlgebraicGeometry.Scheme.Modules` spelling, with
  `Stacks.IdealSheafRestrict.structureMap`. This is forced: the zero morphism needs
  `CategoryTheory.Limits.HasZeroMorphisms`, and instance search for it fails in the
  `SheafOfModules (structureSheafRing B.toSheafedSpace)` spelling.
* The *results* are restated in the spelling of the Tag 01R3 statements, with
  `Stacks.ClosedImmersion.idealSheaf` and
  `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit`. The restatements are by application,
  using `Stacks.IdealSheafRestrict.kernel_structureMap`, which holds by `rfl`.
* `idealSheafIsoOfIsoSource_hom_comp_ι` is proved by `CategoryTheory.Limits.kernel.lift_ι` with
  **all three arguments named**. Left as `kernel.lift_ι _ _ _` the implicit
  `HasZeroMorphisms` argument becomes a metavariable in that spelling and instance search
  fails there, exactly as in the previous item.

`Γ(M, U)` lives in `AddCommGrpCat` and `M.val.obj (.op U)` in `ModuleCat`; the carriers agree but
the objects do not. `idealSheafIsoOfIsoSource_hom_val_app` is stated in the `.val.obj (.op O)`
form, the one `Stacks.Conormal.AffineCotangent.Transport.idealSheafSectionsEquivOfIsoSource` and
`Stacks.Conormal.Locality.idealSheaf_section_injective` are stated in, and the descent from the
morphism equality `idealSheafIsoOfIsoSource_hom_comp_ι` to the element is by `congr(...)` rather
than `rw`.

## What is not done

* **No clause of [Stacks, Tag 01R3] is discharged and no tag is attached.** Part (2) of the tag
  still needs the chain assembled; see the next item.
* **The chain to part (2) of the tag is not closed.** `idealSheafIsoAffineModelOfMorphismRestrict`
  reaches the affine model's ideal sheaf, but three comparisons still separate it from
  `affineConormalIsoCotangentWithQuotient`, none of them a transport along an isomorphism:
  the sections over `V` of a pushforward along `i` have to be identified with the sections over
  `i ⁻¹ᵁ V`; `Stacks.Conormal.Locality.conormalSheafRestrictIso` is stated for an open `V'` of a
  closed-immersion factorization `(U, i')` and has to be matched with the open `V` of `X` used
  here; and `Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` computes global sections
  over `Spec Γ(X, V)`, so its answer has to be carried across
  `AlgebraicGeometry.IsAffineOpen.isoSpec` at the level of sections of a pushforward. The section
  formula each of those steps must preserve is available here as
  `idealSheafIsoOfIsoSource_hom_val_app`, but is not propagated.
* **No reduction of the factorization quantifier.** Untouched here, as in
  `StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality`: the quantifier over
  closed-immersion factorizations `(U, i')` in `affineConormalIsoCotangentWithQuotient` is a
  comparison of
  `Stacks.Conormal.conormalQuotientMap` for two factorizations, which is not an instance of the
  transport proved here.
* **Nothing about `Ideal.Cotangent`**, the square of the ideal, or epimorphy of the quotient map.
* **No compatibility of the pulled-back form with the inclusions.** The analogue of
  `Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι` for
  `modulePullbackIdealSheafIsoOfIsoSource` is not stated; the inclusion is not preserved by a
  pullback, so that statement is about the unit of the adjunction and is a different lemma.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.IdealSheafRestrict

universe u

namespace Stacks.Conormal.AffineCotangent.SourceTransport

variable {A A' B B' : Scheme.{u}} (α : A' ≅ A) (g : A ⟶ B)

/-! ### The two vanishing composites -/

/-- **The ideal sheaf of `α.hom ≫ g` is killed by the structure-sheaf map of `g`.**

A morphism of sheaves of modules is zero exactly when it is zero on sections over every open, and
there this is `Stacks.Conormal.AffineCotangent.Sections.app_idealSheaf_section_eq_zero` followed
by the forward direction of
`Stacks.Conormal.AffineCotangent.Transport.mem_ker_app_comp_iso_iff`: precomposing with an
isomorphism does not change the kernel on sections.

Stated with `Stacks.IdealSheafRestrict.structureMap` rather than in the
`Stacks.ClosedImmersion.idealSheaf` spelling of the
ideal sheaf, because the zero morphism needs a `CategoryTheory.Limits.HasZeroMorphisms` instance
that is found only in this spelling; see the module docstring. -/
theorem ι_comp_structureMap_eq_zero :
    kernel.ι (structureMap (α.hom ≫ g)) ≫ structureMap g = 0 := by
  ext W x
  exact (Transport.mem_ker_app_comp_iso_iff α g W _).1
    (Sections.app_idealSheaf_section_eq_zero (α.hom ≫ g) W x)

/-- **The ideal sheaf of `g` is killed by the structure-sheaf map of `α.hom ≫ g`.** The same
argument as `ι_comp_structureMap_eq_zero` with the two morphisms exchanged, using the backward
direction of `Stacks.Conormal.AffineCotangent.Transport.mem_ker_app_comp_iso_iff`. -/
theorem ι_comp_structureMapComp_eq_zero :
    kernel.ι (structureMap g) ≫ structureMap (α.hom ≫ g) = 0 := by
  ext W x
  exact (Transport.mem_ker_app_comp_iso_iff α g W _).2
    (Sections.app_idealSheaf_section_eq_zero g W x)

/-! ### The isomorphism of ideal sheaves -/

/-- **The source-slot transport, as a comparison of kernels.** The kernels of the
structure-sheaf maps of `α.hom ≫ g` and of `g` are canonically isomorphic.

Both are kernels of morphisms *out of the same object* `Stacks.IdealSheafRestrict.unitModule B`,
so `CategoryTheory.Limits.kernel.lift` applied to the two vanishing composites gives the two
morphisms with no comparison of the two targets, and hence no identification
`α.hom_* 𝒪_{A'} ≅ 𝒪_A`, anywhere. The round trips are `CategoryTheory.Limits.kernel.lift_ι`
cancelled against the monomorphism `CategoryTheory.Limits.kernel.ι`. -/
noncomputable def kernelStructureMapIsoOfIsoSource :
    kernel (structureMap (α.hom ≫ g)) ≅ kernel (structureMap g) where
  hom := kernel.lift (structureMap g) (kernel.ι (structureMap (α.hom ≫ g)))
    (ι_comp_structureMap_eq_zero α g)
  inv := kernel.lift (structureMap (α.hom ≫ g)) (kernel.ι (structureMap g))
    (ι_comp_structureMapComp_eq_zero α g)
  hom_inv_id := by
    rw [← cancel_mono (kernel.ι (structureMap (α.hom ≫ g))), Category.assoc, kernel.lift_ι,
      kernel.lift_ι, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (kernel.ι (structureMap g)), Category.assoc, kernel.lift_ι,
      kernel.lift_ι, Category.id_comp]

/-- **Transport of the ideal sheaf along an isomorphism of the source.** For an isomorphism
`α : A' ≅ A` and an arbitrary morphism `g : A ⟶ B`, the ideal sheaf of `α.hom ≫ g` is
canonically isomorphic, as a sheaf of `𝒪_B`-modules, to the ideal sheaf of `g`.

This is the first of the two declarations that
`StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Transport` names as missing; it is
`kernelStructureMapIsoOfIsoSource` restated in the vocabulary of Tag 01R3, the two statements
agreeing
by `Stacks.IdealSheafRestrict.kernel_structureMap`, which holds by `rfl`. -/
noncomputable def idealSheafIsoOfIsoSource :
    Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom ≅
      Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom :=
  kernelStructureMapIsoOfIsoSource α g

/-- **`idealSheafIsoOfIsoSource` commutes with the two inclusions into the structure sheaf.**
Those inclusions are monomorphisms, so this determines the isomorphism: no other morphism makes
the triangle commute. -/
theorem idealSheafIsoOfIsoSource_hom_comp_ι :
    (idealSheafIsoOfIsoSource α g).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom g.toLRSHom.toShHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (α.hom ≫ g).toLRSHom.toShHom)) :=
  kernel.lift_ι (structureMap g) (kernel.ι (structureMap (α.hom ≫ g)))
    (ι_comp_structureMap_eq_zero α g)

/-- `idealSheafIsoOfIsoSource_hom_comp_ι` for the inverse. -/
theorem idealSheafIsoOfIsoSource_inv_comp_ι :
    (idealSheafIsoOfIsoSource α g).inv ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (α.hom ≫ g).toLRSHom.toShHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom g.toLRSHom.toShHom)) :=
  kernel.lift_ι (structureMap (α.hom ≫ g)) (kernel.ι (structureMap g))
    (ι_comp_structureMapComp_eq_zero α g)

/-- **The sectionwise bijection is natural, and `idealSheafIsoOfIsoSource` is its assembly.**
Over every open `O` of `B`, the isomorphism of sheaves acts on sections as
`Stacks.Conormal.AffineCotangent.Transport.idealSheafSectionsEquivOfIsoSource`.

This is the statement that
`StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Transport` records as unproved —
naturality in the open of its `Equiv`. Both sides have the same image under the inclusion into
the structure sheaf, by `idealSheafIsoOfIsoSource_hom_comp_ι` for the left and by
`Stacks.Conormal.AffineCotangent.Transport.idealSheafSectionsEquivOfIsoSource_ι` for the right,
and `Stacks.Conormal.Locality.idealSheaf_section_injective` says a section of the ideal sheaf is
determined by that image. -/
theorem idealSheafIsoOfIsoSource_hom_val_app (O : B.Opens)
    (x : (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom).val.obj (.op O)) :
    (idealSheafIsoOfIsoSource α g).hom.val.app (.op O) x =
      Transport.idealSheafSectionsEquivOfIsoSource α g O x := by
  refine Stacks.Conormal.Locality.idealSheaf_section_injective g O ?_
  refine Eq.trans ?_ (Transport.idealSheafSectionsEquivOfIsoSource_ι α g O x).symm
  exact congr($(idealSheafIsoOfIsoSource_hom_comp_ι α g).val.app (.op O) x)

/-- `idealSheafIsoOfIsoSource` with the composite `α.hom ≫ g` presented as a separately named
morphism `h` together with the equation `α.hom ≫ g = h`. This is the form a factorization
statement supplies: the morphism one has is given by name, and the factorization through the
isomorphism is a theorem about it. -/
noncomputable def idealSheafIsoOfIsoSourceOfCompEq (h : A' ⟶ B) (hh : α.hom ≫ g = h) :
    Stacks.ClosedImmersion.idealSheaf h.toLRSHom.toShHom ≅
      Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom := by
  subst hh
  exact idealSheafIsoOfIsoSource α g

/-! ### The pulled-back form -/

/-- **Transport of the pulled-back ideal sheaf along an isomorphism of the source.** The module
pullback along `α.hom ≫ g` of the ideal sheaf of `α.hom ≫ g` is the module pullback along
`α.hom` of the module pullback along `g` of the ideal sheaf of `g`.

This is the second of the two declarations that
`StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Transport` names as missing, and the
source-slot analogue of `Stacks.Conormal.pullbackIdealSheafCompIso`.
`Stacks.PullbackPseudofunctor.modulePullbackCompIso` splits the pullback along the composite,
and `idealSheafIsoOfIsoSource` is then applied under the two remaining pullbacks. Compatibility
with the sheafification inside `RingedSpaceModuleAdjunction.modulePullback` is exactly what
`modulePullbackCompIso` carries, it being the uniqueness of a left adjoint, so nothing about
sheafification is done by hand here. -/
noncomputable def modulePullbackIdealSheafIsoOfIsoSource :
    (modulePullback (α.hom ≫ g).toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom) ≅
      (modulePullback α.hom.toLRSHom.toShHom).obj
        ((modulePullback g.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom)) :=
  ((Stacks.PullbackPseudofunctor.modulePullbackCompIso g.toLRSHom.toShHom
        α.hom.toLRSHom.toShHom).app
      (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom)).trans
    ((modulePullback α.hom.toLRSHom.toShHom).mapIso
      ((modulePullback g.toLRSHom.toShHom).mapIso (idealSheafIsoOfIsoSource α g)))

/-- `modulePullbackIdealSheafIsoOfIsoSource` with the composite `α.hom ≫ g` presented as a
separately named morphism `h` together with the equation `α.hom ≫ g = h`. -/
noncomputable def modulePullbackIdealSheafIsoOfIsoSourceOfCompEq (h : A' ⟶ B)
    (hh : α.hom ≫ g = h) :
    (modulePullback h.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf h.toLRSHom.toShHom) ≅
      (modulePullback α.hom.toLRSHom.toShHom).obj
        ((modulePullback g.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom)) := by
  subst hh
  exact modulePullbackIdealSheafIsoOfIsoSource α g

/-! ### The composite transport -/

/-- **Transport along isomorphisms of source and target at once.** For `α : A' ≅ A`,
`g : A ⟶ B` and `β : B ≅ B'`, the module pullback along `β.hom` of the ideal sheaf of
`α.hom ≫ g ≫ β.hom` is the ideal sheaf of `g`.

`StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Transport` records the composite
transport as not stated; with the source slot available it is the composite of
`idealSheafIsoOfIsoSource` at `g ≫ β.hom`, pulled back along `β.hom`, with the target-slot
transport `Stacks.Conormal.AffineCotangent.Transport.idealSheafIsoOfIsoTarget`. -/
noncomputable def idealSheafIsoOfIsoSourceTarget (β : B ≅ B') :
    (modulePullback β.hom.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g ≫ β.hom).toLRSHom.toShHom) ≅
      Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom :=
  (modulePullback β.hom.toLRSHom.toShHom).mapIso (idealSheafIsoOfIsoSource α (g ≫ β.hom)) ≪≫
    Transport.idealSheafIsoOfIsoTarget g β

/-- **The composite transport in square form, which is the form Tag 01R3 hands over.** Given a
commuting square

```
S ----- f -----> T
|                |
ε                β
v                v
S' ---- k -----> T'
```

with `ε` and `β` isomorphisms, the ideal sheaf of `f` is the module pullback along `β.hom` of the
ideal sheaf of `k`.

This is the usable shape: a hypothesis of the form `f ≫ β.hom = ε.hom ≫ k` is exactly what an
affine presentation of a fibre supplies, and it is literally the hypothesis `he` of the part (2)
clauses of [Stacks, Tag 01R3]. The proof reads the square once in each slot: the source slot by
`idealSheafIsoOfIsoSourceOfCompEq`, the target slot by
`Stacks.Conormal.AffineCotangent.Transport.idealSheafIsoOfIsoTarget`. -/
noncomputable def idealSheafIsoPullbackOfSquare {S S' T T' : Scheme.{u}} (f : S ⟶ T)
    (ε : S ≅ S') (k : S' ⟶ T') (β : T ≅ T') (hsq : f ≫ β.hom = ε.hom ≫ k) :
    Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom ≅
      (modulePullback β.hom.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) :=
  (Transport.idealSheafIsoOfIsoTarget f β).symm ≪≫
    (modulePullback β.hom.toLRSHom.toShHom).mapIso
      (idealSheafIsoOfIsoSourceOfCompEq ε k (f ≫ β.hom) hsq.symm)

/-! ### The junction with the affine model -/

/-- **The ideal sheaf of a fibre with an affine presentation is the pullback of the ideal sheaf of
the affine model.** For a morphism `i : Z ⟶ X`, an affine open `V` of `X`, an ideal `I` of
`Γ(X, V)` and an identification `e` of the fibre product `Z ×_X V` with `Spec (Γ(X, V) ⧸ I)`
compatible with the two projections to `Spec Γ(X, V)`, the ideal sheaf of
`pullback.snd i V.ι` is the module pullback along `AlgebraicGeometry.IsAffineOpen.isoSpec` of the
ideal sheaf of `Spec (Γ(X, V) ⧸ I) ⟶ Spec Γ(X, V)`.

The hypotheses are copied verbatim from the part (2) clauses of
[Stacks, Tag 01R3] — `hV`, `I`, `e` and `he` are the tag's own data, with no reshaping — so this
is `idealSheafIsoPullbackOfSquare` at that square. Nothing is assumed about `i`: it is not an
immersion here, and need not be. -/
noncomputable def idealSheafIsoAffineModelOfPullbackSnd {Z X : Scheme.{u}} (i : Z ⟶ X)
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    Stacks.ClosedImmersion.idealSheaf (pullback.snd i V.ι).toLRSHom.toShHom ≅
      (modulePullback hV.isoSpec.hom.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom) :=
  idealSheafIsoPullbackOfSquare (pullback.snd i V.ι) e _ hV.isoSpec he

/-- **`idealSheafIsoAffineModelOfPullbackSnd` for the restricted morphism `i ∣_ V`**, which is the
form the locality comparisons are stated in:
`Stacks.Conormal.Locality.conormalRestrictIso` computes the restricted conormal sheaf as the
inverse image along `i ∣_ V` of the ideal sheaf of `i ∣_ V`, and this identifies that ideal sheaf
with the pullback of the affine model's.

`AlgebraicGeometry.pullbackRestrictIsoRestrict` identifies the fibre product with the open
subscheme `i ⁻¹ᵁ V`, so the tag's `e` composes with it to an isomorphism of the source of
`i ∣_ V`; the square is then the tag's `he` with that isomorphism cancelled, by
`AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict`. -/
noncomputable def idealSheafIsoAffineModelOfMorphismRestrict {Z X : Scheme.{u}} (i : Z ⟶ X)
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    Stacks.ClosedImmersion.idealSheaf (i ∣_ V).toLRSHom.toShHom ≅
      (modulePullback hV.isoSpec.hom.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom) :=
  idealSheafIsoPullbackOfSquare (i ∣_ V) ((pullbackRestrictIsoRestrict i V).symm ≪≫ e) _
    hV.isoSpec (by
      rw [← cancel_epi (pullbackRestrictIsoRestrict i V).hom, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc,
        pullbackRestrictIsoRestrict_hom_morphismRestrict_assoc]
      exact he)

end Stacks.Conormal.AffineCotangent.SourceTransport

end
