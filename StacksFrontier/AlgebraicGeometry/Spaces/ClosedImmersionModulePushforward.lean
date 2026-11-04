module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageReduction
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Direct image of modules along a closed immersion of algebraic spaces

Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S`. Stacks 04CJ,
part (2) asserts that inverse image is a left inverse of direct image on sheaves of modules: the
counit `f^*f_*G ⟶ G` of the adjunction of Stacks 03LU is an isomorphism for every `𝒪_X`-module
`G`. Equivalently — the counit of an adjunction is an isomorphism exactly when the right adjoint
is fully faithful — the direct image `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` is fully faithful.

That statement is proved here from full faithfulness of the direct image of sheaves of sets on
the small étale topoi, which is Stacks 04E5, part (1), available as
`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion`. The two inputs
of the bridge are:

* `Stacks.ToposBridge.fullyFaithfulPushforwardModules`, the full-faithfulness half of
  Stacks 08M3 for an abstract morphism of topoi, which takes exactly full faithfulness of the
  direct image on sheaves of sets and local surjectivity of the structure map;
* `AlgebraicGeometry.Space.isLocallySurjective_structureSharp`, the surjectivity clause of
  Stacks 03MB.

Two assertions of part (3) of Stacks 04CJ are proved here as well: the ideal `𝓘 = ker(f♯)`
cutting out `X` annihilates every direct image, and the direct image is fully faithful on
quasi-coherent modules. The tag is carried per clause, here and in the sibling files named in
the implementation notes, which between them cover every numbered part of Stacks 04CJ.

The same two assertions on coherent modules are the full-faithfulness half of **Stacks 08AM**:
the coherent `𝒪_X`-modules are those of Stacks 07UA, and `f_*` embeds them fully faithfully in
the `𝒪_Y`-modules annihilated by `𝓘`.

Those same two assertions are also the space-level analogue of two of the three clauses of
**Stacks 08KS**, which asserts for a closed immersion of ringed spaces that the direct image of
modules is exact, is fully faithful, and has the `𝓘`-annihilated modules for essential image.
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward` is its full-faithfulness clause and
carries the tag, and the two annihilation statements below are the inclusion
`essImage f_* ⊆ {𝓕 | 𝓘𝓕 = 0}` of its essential-image clause.

The other two clauses are stated whole, and unconditionally, elsewhere in the tree, and the tag
is carried there by one statement per clause: the exactness clause by
`AlgebraicGeometry.Space.exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity`
of `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardRightExact.lean`, and
the essential-image clause by `AlgebraicGeometry.Space.essImage_modulePushforward_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleEssentialImage.lean`. The halves of
those clauses — including the inclusion above, in the containment form
`AlgebraicGeometry.Space.essImage_modulePushforward_le_annihilatedByKerIdeal` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardExactness.lean` — carry no
tag of their own. Neither does
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj` below, which derives the
essential-image clause from `hsurj` and is superseded by the statement above.

## Main definitions

* `AlgebraicGeometry.Space.fullyFaithfulModulePushforward`: direct image of `𝒪`-modules along a
  closed immersion is fully faithful.
* `AlgebraicGeometry.Space.modulePullbackCounitIso`: the resulting natural isomorphism
  `f_* ⋙ f^* ≅ 𝟭`, that is, inverse image is a left inverse of direct image.
* `AlgebraicGeometry.Space.AnnihilatedByKerIdeal`: the ideal `𝓘 = ker(f♯) ⊆ 𝒪_Y` cutting out the
  closed subspace annihilates a module section by section, that is, `𝓘𝓕 = 0`.
* `AlgebraicGeometry.Space.quasicoherentModulePushforward` and
  `AlgebraicGeometry.Space.coherentModulePushforward`: direct image as a functor from the
  quasi-coherent, resp. coherent, `𝒪_X`-modules to the `𝒪_Y`-modules annihilated by `𝓘`.

## Main results

* `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit`: the counit `f^*f_*G ⟶ G` is an
  isomorphism for every `𝒪_X`-module `G`.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward` and
  `AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward`: `𝓘` annihilates
  `f_*G` for every `𝒪_X`-module `G`, hence every module in the essential image of `f_*`.
* `AlgebraicGeometry.Space.fullyFaithfulQuasicoherentModulePushforward` and
  `AlgebraicGeometry.Space.fullyFaithfulCoherentModulePushforward`: those two functors are fully
  faithful.
* `AlgebraicGeometry.Space.essImage_restrictScalars_structureSharp_of_annihilatedByKerIdeal`: a
  module annihilated by `𝓘` is a module over `f_*𝒪_X = 𝒪_Y/𝓘`, which is the first step of the
  converse.
* `AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`: the essential image of
  `f_*` on all modules is exactly the annihilated modules, granted that every sheaf of
  `f_*𝒪_X`-modules is a direct image.

## Implementation notes

The morphism of topoi fed to the bridge is `AlgebraicGeometry.Space.smallToposMorphismTypeU`,
the morphism of small étale topoi of Stacks 03G2, part (3) at the universe of the structure
rings, and the sheaf of rings is the structure sheaf of `X`. No comparison is needed to recognise
the bridge's conclusion as `AlgebraicGeometry.Space.modulePushforward`: the direct image of
sheaves of sets of the morphism of topoi *is*
`AlgebraicGeometry.Space.smallEtaleDirectImage` (`…smallEtaleRingedToposHom_pushforward_eq`), so
the bridge's `Stacks.Sheaves.ToposPushforward.pushforwardModules` applied to the structure map is
`AlgebraicGeometry.Space.modulePushforward` on the nose.

The modules are those of `AlgebraicGeometry.Space.Modules`, whose sections live in the universe
of the schemes; the source quantifies over all `𝒪_X`-modules, and an independent module universe
would need the adjunction of Stacks 03LU at independent universes rather than
`AlgebraicGeometry.Space.modulePullbackAdjunction`.

Part (1) of Stacks 04CJ, the isomorphism `𝓕/𝓘𝓕 ≅ f_*f^*𝓕` induced by the adjunction unit, is
proved in `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionIdealQuotient.lean`, as
`AlgebraicGeometry.Space.kerIdealSmulQuotientUnitIso`. The product `𝓘𝓕` there is
`Stacks.Sites.idealSmul` of the ideal `𝓘` — which is `SheafOfModules.kerIdeal` applied to
`AlgebraicGeometry.Space.structureSharp`, equivalently
`AlgebraicGeometry.Space.definingIdealSheaf` of the closed subspace — with all of `𝓕`, and the
quotient is the cokernel of its inclusion. The route is not the source's: rather than Stacks 04G0
it uses that the unit is an epimorphism together with the essential-image clause, both of which
are proved.

**Why the two functors below land in all `𝒪_Y`-modules annihilated by `𝓘` rather than in the
quasi-coherent, resp. coherent, ones.** They take no closed-immersion hypothesis, and that is
what quasi-coherence of `f_*` needs: the closed-immersion case of Stacks 03M9 is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionQuasicoherentPushforward.lean`, and the
functor `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` of Stacks 04CJ, part (3) built from it is
`AlgebraicGeometry.Space.quasicoherentDirectImageOfClosedImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionQuasicoherentEquivalence.lean`. That `f_*`
preserves coherence is the case of a closed immersion of Stacks 07UH,
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite`, which lies downstream of this
file. Restricting the source to the quasi-coherent or coherent modules costs nothing, so the full
faithfulness below is exactly the source's, with only the target weakened.

**The essential-image converse.** It splits in two by the factorization
`f_* = (Stacks 03D1 direct image) ⋙ (restriction of scalars along f♯)`. The second factor is
settled by Stacks 0930: a module annihilated by `ker(f♯)` is a module over `f_*𝒪_X = 𝒪_Y/𝓘`,
which is
`AlgebraicGeometry.Space.essImage_restrictScalars_structureSharp_of_annihilatedByKerIdeal`
below. The clause itself is proved whole and with no hypothesis beyond the closed immersion, by
the fibrewise route of `AlgebraicGeometry.Space.essImage_modulePushforward_iff` in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleEssentialImage.lean`; its
quasi-coherent form, which is the essential-image clause of Stacks 04CJ, part (3) as the source
states it, is `AlgebraicGeometry.Space.essImage_quasicoherentDirectImage_iff`. The hypothesis
`hsurj` of `AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj` below is therefore
superseded; that statement is kept because it is the interface to the general topos theory, and
it carries no tag.

Part (3)'s exactness assertion is proved too: on all modules as
`AlgebraicGeometry.Space.exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity`
of `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardRightExact.lean`, which
instantiates the site-level Stacks 04BD at a closed immersion, and on quasi-coherent modules as
`AlgebraicGeometry.Space.exactFunctor_quasicoherentDirectImageOfClosedImmersion`.

## References

* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 08AM](https://stacks.math.columbia.edu/tag/08AM)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Direct image of `𝒪`-modules along a closed immersion `f : X ⟶ Y` of algebraic spaces is
fully faithful.

The two inputs of `Stacks.ToposBridge.fullyFaithfulPushforwardModules` are part (1) of
Stacks 04E5, `AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion`, and
the surjectivity clause of Stacks 03MB,
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`. This is Stacks 04CJ, part (2) in
its full-faithfulness form; the Stacks 04CJ tag is carried by the counit statements below, which
are the form the source asserts.

It is at the same time the **full-faithfulness clause of Stacks 08KS for algebraic spaces**: that
tag asserts of the direct image along a closed immersion that it is exact, fully faithful, and has
the `𝓘`-annihilated modules for essential image, and this is the second of those three. The first
is `AlgebraicGeometry.Space.preservesFiniteLimits_modulePushforward` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardExactness.lean` for its
left-exactness half; the third is the pair of annihilation statements below for one inclusion, the
other being `AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleEssentialImage.lean`, which needs no
hypothesis beyond the closed immersion. -/
@[stacks 08KS "full faithfulness of the direct image, for algebraic spaces"]
def fullyFaithfulModulePushforward (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom) :
    (modulePushforward B S hS f).FullyFaithful :=
  Stacks.ToposBridge.fullyFaithfulPushforwardModules (smallToposMorphismTypeU B S hS f)
    (structureRingSheaf B S hS X) (structureSharp B S hS f)
    (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS f hf)
    (isLocallySurjective_structureSharp B S hS f hf)

/-- **Stacks 04CJ, part (2)** for the modules of `AlgebraicGeometry.Space.Modules`: for a closed
immersion `f : X ⟶ Y` of algebraic spaces and any sheaf of `𝒪_X`-modules `G`, the adjunction map
`f^*f_*G ⟶ G` is an isomorphism.

This is full faithfulness of the direct image read through the adjunction of Stacks 03LU: the
counit of an adjunction is an isomorphism exactly when its right adjoint is fully faithful. -/
@[stacks 04CJ "part (2): inverse image is a left inverse of direct image"]
theorem isIso_modulePullbackAdjunction_counit (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((modulePullbackAdjunction B S hS f).counit.app G) :=
  have := (fullyFaithfulModulePushforward B S hS f hf).full
  have := (fullyFaithfulModulePushforward B S hS f hf).faithful
  inferInstance

/-- **Stacks 04CJ, part (2)**, functorially: inverse image along a closed immersion of algebraic
spaces is a left inverse of direct image, the counit of the adjunction of Stacks 03LU being a
natural isomorphism `f_* ⋙ f^* ≅ 𝟭`. This is the functorial form of
`AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit`. -/
@[stacks 04CJ "part (2): inverse image is a left inverse of direct image"]
def modulePullbackCounitIso (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom) :
    modulePushforward B S hS f ⋙ modulePullback B S hS f ≅
      𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  have := (fullyFaithfulModulePushforward B S hS f hf).full
  have := (fullyFaithfulModulePushforward B S hS f hf).faithful
  asIso (modulePullbackAdjunction B S hS f).counit

/-! ### Part (3): annihilation by the defining ideal, and full faithfulness -/

/-- The ideal `𝓘 = ker(f♯) ⊆ 𝒪_Y` cutting out the closed subspace `X` annihilates an
`𝒪_Y`-module section by section, that is, `𝓘𝓕 = 0`.

The sections of `𝓘` over an étale chart are the kernel of `f♯` there
(`SheafOfModules.kerIdeal_obj`), which is how `AlgebraicGeometry.Space.definingIdealSheaf`
of the closed subspace is defined as well (`AlgebraicGeometry.Space.mem_definingIdealAt_iff`).

The scalar action is seated by a `letI` naming the canonical module structure
`CategoryTheory.ModuleCat.isModule` of the section module, rather than left to instance search.
The modules here are indexed by `Stacks.SheafOfModules.Tensor.ringSheaf`, a plain `def`, so the
instance arguments that search assembles for the goal at this spelling are defeq to the ones
carried by the section module's own structure only after that `def` is unfolded, which instance
search — working at `instances` transparency — will not do. The bound value is term-identical to
the canonical instance, so no second module structure exists, and `letI` zeta-reduces, so the
proposition is the same one. -/
def AnnihilatedByKerIdeal (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2) : Prop :=
  ∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : (structureRingSheaf B S hS Y).obj.obj U),
    a ∈ (SheafOfModules.kerIdeal (structureSharp B S hS f)).obj U →
      letI : Module ((structureRingSheaf B S hS Y).obj.obj U) (M.val.obj U) :=
        (M.val.obj U).isModule
      ∀ m : M.val.obj U, a • m = 0

/-- Annihilation by the ideal cutting out the closed subspace, as a property of objects of the
category of `𝒪_Y`-modules. -/
abbrev annihilatedByKerIdeal (f : X ⟶ Y) : ObjectProperty (Modules.{u, u} B S hS Y.1 Y.2) :=
  AnnihilatedByKerIdeal B S hS f

/-- **Stacks 04CJ, part (3)**, half of the essential-image assertion: the ideal cutting out the
closed subspace annihilates every direct image `f_*G`.

Restriction of scalars along `f♯` makes a section `a` of `𝒪_Y` act on `f_*G` as `f♯(a)`, so a
section killed by `f♯` acts as zero. Neither the closed-immersion hypothesis on `f` nor
surjectivity of `f♯` is used.

This is also one inclusion of the essential-image clause of Stacks 08KS for algebraic spaces; the
containment form of it is
`AlgebraicGeometry.Space.essImage_modulePushforward_le_annihilatedByKerIdeal` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardExactness.lean`, which
carries no tag of its own, and the reverse inclusion is
`AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal`, proved with no
hypothesis beyond the closed immersion. -/
@[stacks 04CJ "part (3): the essential image is annihilated by the defining ideal"]
theorem annihilatedByKerIdeal_modulePushforward (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    AnnihilatedByKerIdeal B S hS f ((modulePushforward B S hS f).obj G) :=
  fun U a ha m ↦ Stacks.Sheaves.PushforwardEssentialImage.smul_restrictScalars_eq_zero
    (structureSharp B S hS f) ((moduleDirectImage B S hS f).obj G) U a
    ((SheafOfModules.mem_kerIdeal _ U a).1 ha) m

/-- **Stacks 04CJ, part (3)**, half of the essential-image assertion, in essential-image form:
every `𝒪_Y`-module isomorphic to a direct image along `f` is annihilated by the ideal cutting out
the closed subspace. This is
`AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward` transported along an
isomorphism, and is the inclusion `essImage f_* ⊆ {𝓕 | 𝓘𝓕 = 0}` of the essential-image clause of
Stacks 08KS for algebraic spaces, whose tag is carried by
`AlgebraicGeometry.Space.essImage_modulePushforward_le_annihilatedByKerIdeal` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardExactness.lean`. -/
@[stacks 04CJ "part (3): the essential image is annihilated by the defining ideal"]
theorem annihilatedByKerIdeal_of_essImage_modulePushforward (f : X ⟶ Y)
    {G : Modules.{u, u} B S hS Y.1 Y.2} (hG : (modulePushforward B S hS f).essImage G) :
    AnnihilatedByKerIdeal B S hS f G :=
  fun U a ha m ↦
    Stacks.Sheaves.PushforwardEssentialImage.smul_eq_zero_of_essImage_restrictScalars
      (moduleDirectImage B S hS f) hG U a ((SheafOfModules.mem_kerIdeal _ U a).1 ha) m

/-- Direct image as a functor `QCoh(𝒪_X) ⥤ {𝓕 ∈ Mod(𝒪_Y) | 𝓘𝓕 = 0}`, the lift of
`AlgebraicGeometry.Space.modulePushforward` along
`AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`.

Stacks 04CJ, part (3) has `QCoh(𝒪_Y)` for target; that functor takes the closed-immersion
hypothesis, which this one does not, and is
`AlgebraicGeometry.Space.quasicoherentDirectImageOfClosedImmersion`. -/
def quasicoherentModulePushforward (f : X ⟶ Y) :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤
      (annihilatedByKerIdeal B S hS f).FullSubcategory :=
  (annihilatedByKerIdeal B S hS f).lift (ObjectProperty.ι _ ⋙ modulePushforward B S hS f)
    fun M ↦ annihilatedByKerIdeal_modulePushforward B S hS f M.obj

/-- Composing `AlgebraicGeometry.Space.quasicoherentModulePushforward` with the inclusion of the
annihilated modules is direct image on quasi-coherent modules. This holds by definition: the
functor *is* that lift. -/
def quasicoherentModulePushforwardCompIso (f : X ⟶ Y) :
    quasicoherentModulePushforward B S hS f ⋙
        ObjectProperty.ι (annihilatedByKerIdeal B S hS f) ≅
      ObjectProperty.ι _ ⋙ modulePushforward B S hS f :=
  Iso.refl _

/-- **Stacks 04CJ, part (3)**, the full-faithfulness assertion: direct image along a closed
immersion of algebraic spaces is fully faithful on quasi-coherent modules.

It is fully faithful on *all* modules by
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward`, and a full subcategory inclusion is
fully faithful. -/
@[stacks 04CJ "part (3): the direct image is fully faithful on quasi-coherent modules"]
def fullyFaithfulQuasicoherentModulePushforward (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    (quasicoherentModulePushforward B S hS f).FullyFaithful :=
  have := (fullyFaithfulModulePushforward B S hS f hf).full
  have := (fullyFaithfulModulePushforward B S hS f hf).faithful
  have : (quasicoherentModulePushforward B S hS f).Faithful :=
    Functor.Faithful.of_comp_iso (quasicoherentModulePushforwardCompIso B S hS f)
  have : (quasicoherentModulePushforward B S hS f).Full :=
    Functor.Full.of_comp_faithful_iso (quasicoherentModulePushforwardCompIso B S hS f)
  Functor.FullyFaithful.ofFullyFaithful _

/-! ### Stacks 08AM: coherent modules on a closed subspace -/

/-- **Stacks 08AM**, the induced functor, with the target weakened: direct image as a functor
`Coh(𝒪_X) ⥤ {𝓕 ∈ Mod(𝒪_Y) | 𝓘𝓕 = 0}` from the coherent modules of Stacks 07UA.

The source states the target as the *coherent* `𝒪_Y`-modules annihilated by `𝓘`, which would need
coherence of `f_*` of a coherent module; see the implementation notes. -/
@[stacks 08AM "the induced functor into the modules annihilated by the ideal"]
def coherentModulePushforward (f : X ⟶ Y) :
    CoherentModules.{u, u} B S hS X.1 X.2 ⥤
      (annihilatedByKerIdeal B S hS f).FullSubcategory :=
  (annihilatedByKerIdeal B S hS f).lift (ObjectProperty.ι _ ⋙ modulePushforward B S hS f)
    fun M ↦ annihilatedByKerIdeal_modulePushforward B S hS f M.obj

/-- Composing `AlgebraicGeometry.Space.coherentModulePushforward` with the inclusion of the
annihilated modules is direct image on coherent modules. This holds by definition: the functor
*is* that lift, so the full faithfulness below is that of direct image itself. -/
def coherentModulePushforwardCompIso (f : X ⟶ Y) :
    coherentModulePushforward B S hS f ⋙
        ObjectProperty.ι (annihilatedByKerIdeal B S hS f) ≅
      ObjectProperty.ι _ ⋙ modulePushforward B S hS f :=
  Iso.refl _

/-- **Stacks 08AM**, the full-faithfulness half of the equivalence: direct image along a closed
immersion of algebraic spaces is fully faithful on coherent modules.

Essential surjectivity is not proved; see the implementation notes for the one input it is
missing and for the coherence of `f_*` that its target needs. -/
@[stacks 08AM "full faithfulness of the direct image on coherent modules"]
def fullyFaithfulCoherentModulePushforward (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    (coherentModulePushforward B S hS f).FullyFaithful :=
  have := (fullyFaithfulModulePushforward B S hS f hf).full
  have := (fullyFaithfulModulePushforward B S hS f hf).faithful
  have : (coherentModulePushforward B S hS f).Faithful :=
    Functor.Faithful.of_comp_iso (coherentModulePushforwardCompIso B S hS f)
  have : (coherentModulePushforward B S hS f).Full :=
    Functor.Full.of_comp_faithful_iso (coherentModulePushforwardCompIso B S hS f)
  Functor.FullyFaithful.ofFullyFaithful _

/-! ### The essential-image converse, and the one input it is missing -/

/-- **Stacks 0930 at the structure map.** An `𝒪_Y`-module annihilated by the ideal cutting out the
closed subspace is a module over `f_*𝒪_X = 𝒪_Y/𝓘`, that is, lies in the essential image of
restriction of scalars along `f♯`.

This is the first of the two steps of the essential-image converse of Stacks 04CJ, part (3); the
second is the hypothesis of
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`. -/
theorem essImage_restrictScalars_structureSharp_of_annihilatedByKerIdeal (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : AnnihilatedByKerIdeal B S hS f G) :
    (SheafOfModules.restrictScalars (structureSharp B S hS f)).essImage G :=
  let _hls : Sheaf.IsLocallySurjective (structureSharp B S hS f) :=
    isLocallySurjective_structureSharp B S hS f hf
  Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_of_smul_eq_zero
    (structureSharp B S hS f) G
    fun U a ha m ↦ hG U a ((SheafOfModules.mem_kerIdeal _ U a).2 ha) m

/-- **The essential-image assertion of Stacks 04CJ, part (3) on all modules**, derived from
essential surjectivity of the Stacks 03D1 direct image of modules: an `𝒪_Y`-module is a direct
image along the closed immersion `f` exactly when the ideal cutting out `X` annihilates it.

This is the route through the general theory of `Stacks.Sheaves.PushforwardEssentialImage`, and
it is superseded by `AlgebraicGeometry.Space.essImage_modulePushforward_iff`, which states the
same thing with no hypothesis beyond the closed immersion; **no `@[stacks 04CJ]` attribute is
carried here.** See the implementation notes. -/
theorem essImage_modulePushforward_iff_of_essSurj (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (hsurj : ∀ M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      (moduleDirectImage B S hS f).essImage M)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePushforward B S hS f).essImage G ↔ AnnihilatedByKerIdeal B S hS f G := by
  let _hls : Sheaf.IsLocallySurjective
      (show structureRingSheaf B S hS Y ⟶
          Stacks.Sheaves.ToposPushforward.pushforwardRingSheaf.{u, u, u, u + 1, u, u + 1}
            (smallToposMorphismTypeU B S hS f) (structureRingSheaf B S hS X)
        from structureSharp B S hS f) :=
    isLocallySurjective_structureSharp B S hS f hf
  refine (Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_essSurj
    (f := smallToposMorphismTypeU B S hS f) (O := structureRingSheaf B S hS X)
    (structureSharp B S hS f) hsurj G).trans ?_
  exact ⟨fun h U a ha m ↦ h U a ((SheafOfModules.mem_kerIdeal _ U a).1 ha) m,
    fun h U a ha m ↦ h U a ((SheafOfModules.mem_kerIdeal _ U a).2 ha) m⟩

end AlgebraicGeometry.Space

end
