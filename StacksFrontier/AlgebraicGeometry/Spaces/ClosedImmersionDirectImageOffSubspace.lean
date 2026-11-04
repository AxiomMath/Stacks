module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction

/-!
# The small étale direct image has one section off the closed subspace

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`. This file records, **at the universe `u` of the schemes — the universe the modules
of `AlgebraicGeometry.Space.Modules` live at** — that the Stacks 03D1 direct image along `i` has
exactly one section over an étale chart of `X` whose points avoid the point set of `Z`, and that
consequently so does every sheaf of modules over the direct-image structure ring `i_*𝒪_Z`.

This is the "easy half" of the closed-subtopos description of the essential image of the small
étale direct image, made available at `Type u` rather than at `Type (u + 1)`.

## Main results

* `AlgebraicGeometry.Space.subsingleton_smallEtaleDirectImage_sections_of_isEmpty`: the direct
  image of a sheaf of sets at `Type u` has at most one section over a chart whose base change
  along `i` has empty underlying scheme.
* `AlgebraicGeometry.Space.subsingleton_structureRingSheafDirectImage_of_isEmpty` and
  `…_of_chartPreimage_eq_empty`: the same for `i_*𝒪_Z`, so that its sections over such a chart
  form the zero ring.
* `AlgebraicGeometry.Space.subsingleton_sections_of_isEmpty_smallBaseChange` and
  `…_of_chartPreimage_eq_empty`: hence every sheaf of `i_*𝒪_Z`-modules has at most one section
  over such a chart.

## Why this is the useful shape

The reverse inclusion of the essential-image clause of the space-level [Stacks, Tag 08KS] —
that every `𝒪_X`-module annihilated by `ℐ = ker(i♯)` is a direct image — reduces, by
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`, to the hypothesis `hsurj`
that every sheaf of `i_*𝒪_Z`-modules is a Stacks 03D1 direct image. By
`Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModuleFunctor` that in turn reduces
to its **underlying sheaf of sets** lying in the essential image of the direct image of sheaves of
sets at `Type u`.

The results below supply exactly the property that such a sheaf of sets has: it is "supported on
`Z`" in the sectionwise sense. Notably **the annihilation hypothesis is not used, and no
kernel-ideal argument is needed**. A sheaf of `i_*𝒪_Z`-modules is a module over a ring that is
*already* the zero ring over a chart missing `Z`, so `Module.subsingleton` applies directly. The
ringed-space proof of the same tag
(`Stacks.Tag08KS.modulePushforward_essImage_iff_kernelIdeal_annihilates`) has to spend the
annihilation hypothesis at this point, because it works with `𝒪_X`-modules throughout; routing
through `i_*𝒪_Z`-modules avoids that step entirely.

What remains for the clause is the converse — that a sheaf of sets with this property *is* a
direct image — which is the essential-image half of [Stacks, Tag 04E5] for sheaves of sets at
`Type u`. See the implementation notes for the one identity that currently blocks it.

## Implementation notes

The sections of the direct image over a chart `V` are the sections of the original sheaf over the
base-changed chart `V ×_X Z`, by
`AlgebraicGeometry.Space.smallEtaleDirectImageIsoSheafPushforward`, which identifies
`AlgebraicGeometry.Space.smallEtaleDirectImage` with restriction along chart base change for a
representable morphism. When that chart has empty underlying scheme the empty sieve covers it
(`AlgebraicGeometry.Space.SmallEtale.bot_mem_topology`), so a sheaf has exactly one section there
(`CategoryTheory.Presheaf.exists_eq_section_of_sheafTheoreticallyEmptySite`). The passage from
the geometric hypothesis — the chart's points avoid the point set of `Z` — to emptiness of the
base change is `AlgebraicGeometry.Space.isEmpty_smallBaseChange_of_disjoint_range`.

That the ring of sections is the zero ring is used only through `Module.subsingleton`; the
statements are therefore phrased as `Subsingleton`, not as `IsZero`, which keeps them free of
any additive structure on the sections.

**The identity that blocks the converse, and at which universe.** Running the argument of
[Stacks, Tag 04CA] for sheaves of sets at `Type u` needs the stalk of the inverse image of
`AlgebraicGeometry.Space.smallToposMorphismTypeU` at a geometric point to be the stalk at the
image point — the `Type u` analogue of
`AlgebraicGeometry.Space.smallEtaleInverseImageStalkIso` (Stacks 04K2, part (4)), which is
stated only at `Type (u + 1)`. That statement does typecheck at `Type u`, because both sides are
built from `AlgebraicGeometry.Space.stalkSetFunctor`, whose target `Type (max (u + 1) w)` absorbs
the gap. Its *proof*, however, factors through
`AlgebraicGeometry.Space.etaleSitePointStalkIso`, the identification of the fibre of the point of
the site with the set-valued stalk, and **that** does not typecheck at `Type u`: the fibre
`(etaleSitePoint …).presheafFiber (A := Type u)` lands in `Type u` while
`AlgebraicGeometry.Space.stalkSet` is the un-shrunk colimit quotient over a neighbourhood
category with objects in `Type (u + 1)` and so lands in `Type (u + 1)`. The two can only be
identified through a `ULift`, which is a restatement rather than a re-instantiation. The same
asymmetry is what pins `AlgebraicGeometry.Space.forgetStalkFunctorIso` and hence
`AlgebraicGeometry.Space.isIso_of_isIso_stalkFunctor_map` to `u + 1`.

By contrast the two halves of [Stacks, Tag 04K5] that the argument also needs —
`AlgebraicGeometry.Space.injective_iff_stalkSetMap_injective` and
`surjective_iff_stalkSetMap_surjective` — are already stated at a free coefficient universe, as
are `AlgebraicGeometry.Space.supportOfSheaf` and the chart lemmas used here; and
`AlgebraicGeometry.Space.smallToposMorphismTypeU` is a genuine morphism of topoi at `Type u`
whose direct image is fully faithful for a closed immersion. So the blockage is the single
identification named above, not the conservativity or the adjunction.

No declaration here carries a `@[stacks]` attribute: each is a step towards the
essential-image clause rather than an assertion of the source, and that clause is not proved.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isContinuous_smallBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- The small étale direct image of a sheaf of sets at the universe of the schemes has at most
one section over an étale chart of `X` whose base change along `i` has empty underlying scheme.

For a representable `i` the direct image is restriction along chart base change, so the sections
over such a chart are the sections of the original sheaf over a sheaf theoretically empty object,
of which there is exactly one. -/
theorem subsingleton_smallEtaleDirectImage_sections_of_isEmpty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom)
    (F : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)) (V : SmallEtale B S hS X.1)
    (hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Z.1).obj ((smallBaseChange B S hS i hi).obj V)))) :
    Subsingleton (((smallEtaleDirectImage B S hS i).obj F).obj.obj (op V)) := by
  have hemp : SheafTheoreticallyEmptySite (SmallEtale.topology B S hS Z.1)
      ((smallBaseChange B S hS i hi).obj V) :=
    SmallEtale.bot_mem_topology B S hS Z.1 _ hV
  have e := (smallEtaleDirectImageIsoSheafPushforward B S hS i hi).app F
  obtain ⟨t, ht⟩ := Presheaf.exists_eq_section_of_sheafTheoreticallyEmptySite
    (A := Type u) (SmallEtale.topology B S hS Z.1) F.property hemp
  have hbij : Function.Bijective ((Sheaf.sectionsFunctor _ (op V)).map e.hom) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact ⟨fun a b => hbij.1 ((ht _).trans (ht _).symm)⟩

/-- The direct-image structure ring `i_*𝒪_Z` has at most one section over an étale chart of `X`
whose base change along `i` has empty underlying scheme: its sections over such a chart form the
zero ring.

Its underlying sheaf of sets is the direct image of the underlying sheaf of sets of `𝒪_Z`, on the
nose (`Stacks.Sheaves.ToposPullback.pullbackRingSheafIso` is `Iso.refl`), so this is the previous
statement. -/
theorem subsingleton_structureRingSheafDirectImage_of_isEmpty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (V : SmallEtale B S hS X.1)
    (hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Z.1).obj ((smallBaseChange B S hS i hi).obj V)))) :
    Subsingleton ((structureRingSheafDirectImage B S hS i).obj.obj (op V)) :=
  subsingleton_smallEtaleDirectImage_sections_of_isEmpty B S hS i hi
    ((sheafCompose (SmallEtale.topology B S hS Z.1) (forget RingCat.{u})).obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))) V hV

/-- Every sheaf of modules over the direct-image structure ring `i_*𝒪_Z` has at most one section
over an étale chart of `X` whose base change along `i` has empty underlying scheme.

The ring of sections there is the zero ring by
`AlgebraicGeometry.Space.subsingleton_structureRingSheafDirectImage_of_isEmpty`, and a module
over the zero ring is zero (`Module.subsingleton`). No annihilation hypothesis is needed. -/
theorem subsingleton_sections_of_isEmpty_smallBaseChange (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom)
    (M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS i))
    (V : SmallEtale B S hS X.1)
    (hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Z.1).obj ((smallBaseChange B S hS i hi).obj V)))) :
    Subsingleton (M.val.obj (op V)) :=
  have := subsingleton_structureRingSheafDirectImage_of_isEmpty B S hS i hi V hV
  Module.subsingleton ((structureRingSheafDirectImage B S hS i).obj.obj (op V))
    (M.val.obj (op V))

/-- The geometric form: the direct-image structure ring has at most one section over an étale
chart of `X` whose points avoid the point set of `Z`.

Such a chart has empty base change along `i` by
`AlgebraicGeometry.Space.isEmpty_smallBaseChange_of_disjoint_range`. -/
theorem subsingleton_structureRingSheafDirectImage_of_chartPreimage_eq_empty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (V : SmallEtale B S hS X.1)
    (hV : chartPreimage B S hS i V = ∅) :
    Subsingleton ((structureRingSheafDirectImage B S hS i).obj.obj (op V)) :=
  subsingleton_structureRingSheafDirectImage_of_isEmpty B S hS i hi V
    (isEmpty_smallBaseChange_of_disjoint_range B S hS i hi V hV)

/-- The geometric form: every sheaf of modules over `i_*𝒪_Z` has at most one section over an
étale chart of `X` whose points avoid the point set of `Z`. -/
theorem subsingleton_sections_of_chartPreimage_eq_empty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom)
    (M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS i))
    (V : SmallEtale B S hS X.1) (hV : chartPreimage B S hS i V = ∅) :
    Subsingleton (M.val.obj (op V)) :=
  subsingleton_sections_of_isEmpty_smallBaseChange B S hS i hi M V
    (isEmpty_smallBaseChange_of_disjoint_range B S hS i hi V hV)

end AlgebraicGeometry.Space

end
