module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDefiningIdealSheafObject
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureProjectionComposition
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition

/-!
# The object identification of ideal sheaves on a representable algebraic space, on inclusions

Let `B` be a big fppf site containing a scheme `S`, let `T` be an object of the big fppf category
over `S` and let `Z ⊆ yoneda.obj T` be a closed subspace.
`AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` identifies the defining ideal sheaf of
Stacks 03MB of `Z` with the `𝒪`-module that the defining ideal sheaf of the representing closed
immersion of schemes becomes.  That identification is of **objects**; this file says that it is
compatible with the two **inclusions** into the two structure sheaves, which is what makes it an
identification of ideal *sheaves* rather than merely of modules.

The compatibility is what the hypothesis `hideal` of `Stacks.ConormalComparison.comparison_square`
is reduced to, the inclusion of a defining ideal sheaf being a monomorphism and each of the two
maps of ideal sheaves being characterised by its composite with an inclusion
(`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` on the space side,
`Stacks.ClosedImmersion.idealSheafMap_comp_ι` on the scheme side).  That reduction is carried out
here, at arbitrary categories, in
`AlgebraicGeometry.Space.idealComparison_of_inclusions`.

## Main results

* `AlgebraicGeometry.Space.threeStepTransport_hom_comp`: **the mathematical content of the
  inclusion compatibility, for arbitrary categories and an arbitrary functor.**  A composite of
  three isomorphisms, each compatible with a chosen morphism out of its two ends, is compatible
  with those morphisms.  No kernel appears in it; see the implementation notes for why that is
  what makes it usable here.
* `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented_inv_comp_ι`: **the compatibility
  itself.**  The identification of the two ideal sheaves carries the inclusion of the defining
  ideal sheaf of `Z` to the transported inclusion of the defining ideal sheaf of the representing
  closed immersion, read through
  `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`.  It is the
  declaration relating
  `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` to either inclusion.
* `AlgebraicGeometry.Space.idealComparison_of_inclusions`: **the reduction of `hideal` to the two
  inclusion compatibilities**, at arbitrary categories.  Given the two ideal sheaves on each side
  characterised by their inclusions, the naturality of the edge comparison, and the one square
  that compares the two structure-sheaf maps, the comparison carries the one map of ideal sheaves
  to the other.  Monomorphy of the inclusion on the `B` side is an explicit hypothesis, not an
  instance one; the docstring says why.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_congr`: **the transport of the
  edge comparison along an equality of two morphisms of the site**, which is one of the two
  pieces the hypothesis `hpaste` needs.
* `AlgebraicGeometry.Space.conjugateComparison_homEquiv` and
  `AlgebraicGeometry.Space.homEquiv_comparison_inv_comp`: **the two transposes the sixth
  hypothesis `hstr` is made of, at arbitrary categories.**  The first is the transpose of the
  conjugated edge comparison of
  `AlgebraicGeometry.Space.conjugateComparison_naturality` along the adjunction of Stacks 03D7,
  the second the transpose of a comparison of two base changes along the mates correspondence.
* `AlgebraicGeometry.Space.structureComparison_of_transposes`: **the reduction of `hstr` to the
  direct-image square**, at arbitrary categories: a comparison of module categories carries one
  canonical map `r^*𝒪 ⟶ 𝒪` to the other as soon as it carries one transpose to the other.
* `AlgebraicGeometry.Space.representedAssociatedModule_structurePullback_square`: **`hstr` at
  the representing morphism.**  The comparison functor carries the canonical map
  `r^*𝒪_T ⟶ 𝒪_{T'}` of Zariski modules to
  `AlgebraicGeometry.Space.structureModulePullbackMap` of the represented morphism.  This
  is what relates
  `AlgebraicGeometry.Space.structureModulePullbackMap` to the represented comparisons.

## What `hideal` and `hpaste` still owe

`AlgebraicGeometry.Space.idealComparison_of_inclusions` has six hypotheses.  Read at the
representable instantiation — the comparison of module categories taken from the scheme to the
space, so that `pG` is the inverse of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` — five of them are available:

* `heX` and `heX'` are `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented_inv_comp_ι` of
  this file at the two ambient corners;
* `hpG` is `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_inv_naturality`, the
  hypothesis `hpullback`, taken at the inclusion of the scheme-level ideal sheaf;
* `hn` is `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι`;
* `hm` is `Stacks.ClosedImmersion.idealSheafMap_comp_ι` conjugated by
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso`, the scheme-side map of
  ideal sheaves living at the categorical-kernel presentation and the scheme-side ideal of the
  comparison at the sectionwise one.

The sixth, `hstr`, is
`AlgebraicGeometry.Space.representedAssociatedModule_structurePullback_square` below: that the
comparison functor carries the scheme-level map `r^*𝒪 ⟶ 𝒪` to
`AlgebraicGeometry.Space.structureModulePullbackMap` of the represented morphism, read through
`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso` at both ends and the edge
comparison in the middle.  It is the **inverse-image** counterpart of the **direct-image** square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square`: both sides are
morphisms out of an inverse image, so the adjunction of Stacks 03D7 reduces it to a statement
about transposes.  The right-hand transpose is
`AlgebraicGeometry.Space.structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap`, which
takes `AlgebraicGeometry.Space.structureModulePullbackMap` all the way to
`AlgebraicGeometry.Space.structureProjectionOfHom` and so lands exactly on the direct-image
square; the left-hand one is
`AlgebraicGeometry.Space.conjugateComparison_homEquiv`, which unwinds
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` through
`CategoryTheory.Adjunction.comp` and `CategoryTheory.Adjunction.ofNatIsoRight`, together with
`AlgebraicGeometry.Space.homEquiv_comparison_inv_comp`, which is the mates correspondence
`Stacks.CategoryTheory.homEquiv_conjugate'` at
`AlgebraicGeometry.SmallEtale.conjugateEquiv_associatedModuleBaseChangeIso_inv`.

**What `hstr` carries as hypotheses, and why.**  Its two arguments are the map `r^*𝒪 ⟶ 𝒪` of
Zariski modules and the direct-image square read at the transpose of that map.  Both are forced
by the type-closure condition below: the Zariski map is
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` of `r♯`, and the direct-image square is
stated at `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` of `r♯`, so both spell an
excluded constant, and the direct-image square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square` has a **dirty
type closure** (263 constants, reaching
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`).  Passed as arguments they are never written:
the map is a parameter and the square's own statement is the hypothesis, so nothing excluded enters
a type authored here.  At the instantiation both are supplied by existing declarations —
the square verbatim, and the map either as
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` of `r♯` or, through the ringed-space
spellings of `StacksFrontier/AlgebraicGeometry/RingedSpaceModuleSpellings.lean`, as
`RingedSpaceModuleAdjunction.modulePullbackUnitToUnit`, whose transpose is
`RingedSpaceModuleAdjunction.homEquiv_modulePullbackUnitToUnit`.  That instantiation — and with
it the assembly of all six hypotheses into `hideal` — is not carried out here; it is
`AlgebraicGeometry.Space.representedAssociatedModule_modulePullbackUnitToUnit_square` and
`AlgebraicGeometry.Space.representedAssociatedModule_idealSheafMap_square` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedIdealSheafMapComparison.lean`, which imports
this file.

For `hpaste` the missing piece is the other one named in the *What is left to supply* section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeComparisonSquare.lean`: a composition
law for `AlgebraicGeometry.Space.representedModulePullbackIso`, matching
`AlgebraicGeometry.Space.modulePullbackCompIso` of the represented morphisms with
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` of the underlying morphisms of schemes.
It is a `CategoryTheory.Adjunction.leftAdjointUniq` identity across two adjunctions whose right
adjoints are only *isomorphic*, not equal, so `CategoryTheory.Adjunction.leftAdjointUniq_trans`
does not apply directly.  **That identity is no longer owed about inverse images.**  The mate of
the edge comparison is computed in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackConjugate.lean`, as
`AlgebraicGeometry.Space.conjugateIsoEquiv_representedModulePullbackIso`: it is
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, the comparison of the two
*direct* images, with nothing left over —
`Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq_ofNatIsoRight` applies because
`CategoryTheory.Adjunction.leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e)` is literally how
`AlgebraicGeometry.Space.representedModulePullbackIso` is defined.  Conjugation being a
bijection onto the morphisms of right adjoints, the composition law holds exactly when the
corresponding law holds for that direct-image comparison, and that statement spells no
`AlgebraicGeometry.Space.modulePullback` and so asks for no sheafification.  What is left of it
is one piece of space-side geometry: a pseudofunctoriality for
`AlgebraicGeometry.Space.smallBaseChange`, identifying base change of étale scheme charts along
a composite of two morphisms of algebraic spaces with the two successive base changes,
compatibly with `AlgebraicGeometry.Space.smallBaseChangeSharp` — the counterpart of the
scheme-side `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` and of
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRingHom_app_comp`.

**A kernel rejection recorded elsewhere does not concern this statement.**  The *What is not
proved* section of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeMate.lean` — which records that the
degree-zero pasting law of Stacks 0E47 for inverse images of `𝒪`-modules on algebraic spaces
elaborates and is then rejected by the kernel; that does not bear on `hpaste`.
That law is a comparison of iterated inverse images around a *rectangle* of six algebraic
spaces, a twenty-fold application whose checking reaches into
`AlgebraicGeometry.Space.modulePullback`; `hpaste` is a single composition law carried, past the
mate computation above, entirely by direct images.  The two have a shape in common and nothing
else.

## A note on type closures

**The governing test taken here is the type closure.**  Every declaration of this file has a
**clean type closure**: no type stated here, and no type of any constant named in a type stated
here, reaches `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`,
`AlgebraicGeometry.Scheme.Hom.toRingCat`, `Stacks.Tensor.ringSheaf`,
`CategoryTheory.Sheaf.ringSheaf` or `Stacks.Sheaves.sheafTensor`, and none of those five is
written anywhere in this file.  What this file does *not* claim is that none of them is
reachable at all: `AlgebraicGeometry.Space.representedAssociatedModuleObjDefiningIdealOfHomIso`
and `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` have clean types and **value**
closures that reach `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` through
`AlgebraicGeometry.Space.kernelRepresentedAssociatedModuleMapIso` and
`AlgebraicGeometry.Space.representedAssociatedModuleObjKernelIso`, whose own types carry it, and
the proofs below name those two constants.  Using them writes none of those five constants into
any type stated here; their own types are a separate matter.  The three declarations of the
section *The inclusions at the representing morphism* are the only ones whose value closures
reach them, and nothing outside this file depends on them.

`AlgebraicGeometry.Space.structureRingSheaf` and
`RingedSpaceModuleAdjunction.structureSheafHom` are the permitted spellings and are the only ones
used.

The same reading governs
`AlgebraicGeometry.Space.representedAssociatedModule_structurePullback_square`: the square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square`, which it
consumes, has a type closure of 263 constants reaching
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, so it is taken as a **hypothesis** rather than
named in a type, and the square's `𝒪_T ⟶ r_*𝒪_{T'}` never appears.  The type closures of what is
stated here are: 46 constants for
`AlgebraicGeometry.Space.structureComparison_of_transposes`, 266 for
`AlgebraicGeometry.Space.representedAssociatedModule_structurePullback_square`, none of them
among the five.

## Implementation notes

**The content is stated with no kernels in it, and the three component isomorphisms are passed
explicitly.**  Both are forced.
`AlgebraicGeometry.Space.representedAssociatedModuleObjDefiningIdealOfHomIso` is a composite of
three isomorphisms whose middle terms are kernels of two different *spellings* of one morphism of
sheaves of rings: the scheme-side ideal sheaf
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso` lands in is the kernel written
with `RingedSpaceModuleAdjunction.structureSheafHom` of the underlying morphism of ringed spaces,
while the transported kernel is written with the other spelling.  Stating the content as a lemma
about `CategoryTheory.Limits.kernel.mapIso` and `CategoryTheory.Limits.PreservesKernel.iso` makes
the two spellings meet inside instance arguments, where *instance synthesis
fails* — the categories of modules on a scheme carry a `HasZeroMorphisms` instance per
spelling and `(representedAssociatedModule …).PreservesZeroMorphisms` is stated at one of them —
and the repair of that (fixing the categories from the functor by putting it first in the binder
list) *exhausts the heartbeat budget at `whnf`*, the composite having to be unfolded through
both spellings at once.  Stated with the three isomorphisms and the three morphisms as
parameters and no kernel anywhere,
`AlgebraicGeometry.Space.threeStepTransport_hom_comp` leaves exactly one spelling crossing per
argument, each of them one the definition already performs, and the instantiation costs
2.6 s.

**The final assembly is `CategoryTheory.Iso.trans` and `CategoryTheory.Iso.symm` at arbitrary
categories too**, `AlgebraicGeometry.Space.transSymm_inv_comp`, so that unfolding
`AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` — whose body is a `letI` of the
affineness of the representing morphism followed by such a composite — is a single delta-and-zeta
step against a goal with no concrete category in it.

**Every spelling crossing in `hstr` is paid in a declaration of its own, and only some crossings are
affordable.**  A crossing between two spellings of one object is cheap in
isolation — `AlgebraicGeometry.Space.representedAssociatedModule` against the associated module
followed by `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, the two
spellings of the structure sheaf of rings of a representable algebraic space, and
`AlgebraicGeometry.Space.representedSchemeStructureSheaf` against the small étale structure
sheaf it abbreviates, are each `rfl` in well under a second — but two of them are *not*:

* **inside the index of a `CategoryTheory.Adjunction.homEquiv`.**  Restating
  `AlgebraicGeometry.Space.structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap` with
  either of its two index objects in the other spelling exhausts the heartbeat budget at `whnf`:
  the unifier unfolds `AlgebraicGeometry.Space.modulePullbackAdjunction` rather than comparing
  the indices.  So that lemma is used at its own spelling, and the objects `UB`, `UB'` of
  `AlgebraicGeometry.Space.structureComparison_of_transposes` are explicit arguments, passed in
  that spelling.
* **inside the object a natural transformation is read at.**  Writing the target of
  `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` through
  `AlgebraicGeometry.Space.representedSchemeStructureSheaf` where the term produces the small
  étale structure sheaf costs the whole budget once it sits under
  `(representedModulePushforwardSquareIso …).hom.app`, whose type applies two functors to it.
  `AlgebraicGeometry.Space.representedModulePushforwardSquareIso_hom_app_unit_structureSheaf`
  pays that crossing alone, as an equation between the two readings of the comparison, where it
  costs nothing.

With both of those isolated, the instantiation of
`AlgebraicGeometry.Space.structureComparison_of_transposes` — twenty-six arguments, the edge
comparison, both adjunctions and both equivalences among them — elaborates in about twelve
seconds; without them it does not elaborate at all.

**The transport along an equality of morphisms of the site is stated between isomorphisms, not
between their forward directions**, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackNaturality.lean`: at the level of
`CategoryTheory.Iso.hom` the right-hand side is elaborated against a freshly synthesized
`Category` instance for the small étale modules of `yoneda.obj T`, and reconciling it with the
one inside the folded definition is the `AlgebraicGeometry.Space.Modules`-versus-`SheafOfModules`
comparison.  Between isomorphisms the equality is discharged by `subst` and two unitors.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The content, at arbitrary categories -/

/-- **A functor preserving the kernel of `f` carries the inclusion of that kernel to the
inclusion of the kernel of `F f`.**  This is
`CategoryTheory.Limits.PreservesKernel.iso_inv_ι` read on the forward direction. -/
theorem preservesKernelIso_hom_comp_ι {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {M N : C} (f : M ⟶ N) [HasKernel f] [HasKernel (F.map f)]
    [PreservesLimit (parallelPair f 0) F] :
    (PreservesKernel.iso F f).hom ≫ kernel.ι (F.map f) = F.map (kernel.ι f) :=
  Eq.trans (whisker_eq _ (PreservesKernel.iso_inv_ι F f).symm) (Iso.hom_inv_id_assoc _ _)

/-- **A three-step identification, transported across a functor and then compared with two more
identifications, carries one chosen morphism to another.**  Let `F : C ⥤ D`, let `e : I ≅ Ka` be
an isomorphism in `C` compatible with morphisms `ιI : I ⟶ M` and `κa : Ka ⟶ M`, let
`p : F.obj Ka ≅ Kb` be compatible with `κb : Kb ⟶ F.obj M` and `F κa`, and let `q : Kb ≅ K₂` be
compatible with `κ₂ : K₂ ⟶ M₂`, `κb` and an isomorphism `u : F.obj M ≅ M₂`.  Then the composite
`F e ≪≫ p ≪≫ q` carries `κ₂` to `ιI` read through `u`.

No kernel appears here, although the three identifications this is used at are identifications
of kernels; the implementation notes of this file record the measurement that forces that. -/
theorem threeStepTransport_hom_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {I M Ka : C} {ιI : I ⟶ M} (e : I ≅ Ka) (κa : Ka ⟶ M)
    (he : e.hom ≫ κa = ιI)
    {Kb K₂ M₂ : D} (p : F.obj Ka ≅ Kb) (κb : Kb ⟶ F.obj M) (hp : p.hom ≫ κb = F.map κa)
    (q : Kb ≅ K₂) (κ₂ : K₂ ⟶ M₂) (u : F.obj M ≅ M₂) (hq : q.hom ≫ κ₂ = κb ≫ u.hom) :
    (F.mapIso e ≪≫ p ≪≫ q).hom ≫ κ₂ = F.map ιI ≫ u.hom :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans
      (whisker_eq _
        (Eq.trans (Category.assoc _ _ _)
          (Eq.trans (whisker_eq _ hq)
            (Eq.trans (Category.assoc _ _ _).symm (eq_whisker hp u.hom)))))
      (Eq.trans (Category.assoc _ _ _).symm
        (eq_whisker (Eq.trans (F.map_comp _ _).symm (congrArg F.map he)) u.hom)))

/-- **An isomorphism composed with the inverse of a second one, read on a chosen morphism out of
their common target.**  If `e₁ : J ≅ K` carries `k : K ⟶ P` to `ι` and `e₂ : L ≅ K` carries `k`
to `ψ` read through `c : Q ≅ P`, then the inverse of `e₁ ≪≫ e₂.symm` carries `ι` to `ψ` read
through `c`.

This is the shape in which `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` — a
composite of one identification with the inverse of another — is read on the two inclusions. -/
theorem transSymm_inv_comp {C : Type*} [Category C] {J K L P Q : C}
    (e₁ : J ≅ K) (e₂ : L ≅ K) (k : K ⟶ P) (c : Q ≅ P) {ι : J ⟶ P} {ψ : L ⟶ Q}
    (h₁ : e₁.hom ≫ k = ι) (h₂ : e₂.hom ≫ k = ψ ≫ c.hom) :
    (e₁ ≪≫ e₂.symm).inv ≫ ι = ψ ≫ c.hom :=
  Eq.trans (whisker_eq _ h₁.symm)
    (Eq.trans (Eq.trans (Category.assoc _ _ _) (whisker_eq _ (Iso.inv_hom_id_assoc _ _))) h₂)

/-- **A comparison of module categories compatible with inverse image carries one map of ideal
sheaves to the other as soon as it carries the two inclusions to each other.**  This is the
hypothesis `hideal` of `Stacks.ConormalComparison.comparison_square`, reduced.

The data are the two comparison functors `EX`, `EX'` at the two ambient corners, the two
inverse-image functors `ag`, `bg` along the two ambient morphisms, the edge comparison `pG`, the
two inclusions `ιI`, `ιI'` of the ideal sheaves on the `A` side and `ιJ`, `ιJ'` on the `B` side,
the two maps of ideal sheaves `m` and `n`, the two structure-sheaf maps `sA`, `sB` that
characterise them (`hm`, `hn`), the two identifications `eX`, `eX'` of the ideal sheaves and
`cX`, `cX'` of the structure sheaves, and three compatibilities: `heX`, `heX'` that `eX`, `eX'`
carry the inclusions to each other, `hpG` the naturality of `pG` at `ιI'`, and `hstr` that the
comparison carries `sA` to `sB`.

The proof is cancellation of the monomorphism `ιJ`: past it the two sides are the same composite
of `hm`, `hstr`, `hpG`, `heX'` and `hn`.  The module documentation of this file says which of the
six hypotheses are available at the representable instantiation.

Monomorphy of `ιJ` is an **explicit** hypothesis, for the reason the *Why monomorphy and
epimorphy are explicit hypotheses* note of
`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafSequenceExact.lean` records: instance search for
`Mono (definingIdealSheaf B S hS X Z).ι` runs at reducible transparency and fails at the spelling
an instantiation of an abstract lemma produces, while the same fact is
`AlgebraicGeometry.Space.mono_definingIdealSheaf_ι` and can be passed by hand. -/
theorem idealComparison_of_inclusions {AX AX' BX BX' : Type*}
    [Category AX] [Category AX'] [Category BX] [Category BX']
    (EX : AX ⥤ BX) (EX' : AX' ⥤ BX') (ag : AX' ⥤ AX) (bg : BX' ⥤ BX)
    (pG : ∀ M : AX', EX.obj (ag.obj M) ⟶ bg.obj (EX'.obj M))
    {OA : AX} {OA' : AX'} {I : AX} {I' : AX'} (ιI : I ⟶ OA) (ιI' : I' ⟶ OA')
    (m : ag.obj I' ⟶ I) (sA : ag.obj OA' ⟶ OA) (hm : m ≫ ιI = ag.map ιI' ≫ sA)
    {OB : BX} {OB' : BX'} {J : BX} {J' : BX'} (ιJ : J ⟶ OB) (hιJ : Mono ιJ) (ιJ' : J' ⟶ OB')
    (n : bg.obj J' ⟶ J) (sB : bg.obj OB' ⟶ OB) (hn : n ≫ ιJ = bg.map ιJ' ≫ sB)
    (eX : EX.obj I ⟶ J) (eX' : EX'.obj I' ⟶ J')
    (cX : EX.obj OA ≅ OB) (cX' : EX'.obj OA' ≅ OB')
    (heX : eX ≫ ιJ = EX.map ιI ≫ cX.hom)
    (heX' : eX' ≫ ιJ' = EX'.map ιI' ≫ cX'.hom)
    (hpG : EX.map (ag.map ιI') ≫ pG OA' = pG I' ≫ bg.map (EX'.map ιI'))
    (hstr : EX.map sA ≫ cX.hom = pG OA' ≫ bg.map cX'.hom ≫ sB) :
    EX.map m ≫ eX = pG I' ≫ bg.map eX' ≫ n := by
  have := hιJ
  refine (cancel_mono ιJ).mp ?_
  calc (EX.map m ≫ eX) ≫ ιJ
      = EX.map (ag.map ιI') ≫ EX.map sA ≫ cX.hom := by
        rw [Category.assoc, heX, ← Category.assoc, ← EX.map_comp, hm, EX.map_comp,
          Category.assoc]
    _ = (EX.map (ag.map ιI') ≫ pG OA') ≫ bg.map cX'.hom ≫ sB := by
        rw [hstr, Category.assoc]
    _ = pG I' ≫ bg.map (EX'.map ιI' ≫ cX'.hom) ≫ sB := by
        rw [hpG, bg.map_comp, Category.assoc, Category.assoc]
    _ = (pG I' ≫ bg.map eX' ≫ n) ≫ ιJ := by
        rw [← heX', bg.map_comp, Category.assoc, ← hn]
        simp only [Category.assoc]

/-! ### The inclusions at the representing morphism -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

variable [_root_.AlgebraicGeometry.IsAffineHom
  (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)]

/-- **The identification of the transported Zariski defining ideal sheaf with the kernel of the
canonical morphism of modules of the represented morphism carries the inclusion of that kernel to
the transported inclusion of the ideal sheaf.**

`AlgebraicGeometry.Space.representedAssociatedModuleObjDefiningIdealOfHomIso` is a composite of
three identifications, and each is compatible with the relevant inclusion:
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso_hom_comp_idealSheafι` for the
sectionwise-versus-categorical kernel on the scheme, the left exactness of the transport for the
middle step, and the universal property of the kernel for the assembled square, whose vertical
arrow at the source is `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`.  They are
composed by `AlgebraicGeometry.Space.threeStepTransport_hom_comp`. -/
theorem representedAssociatedModuleObjDefiningIdealOfHomIso_hom_comp_ι :
    (representedAssociatedModuleObjDefiningIdealOfHomIso B S hS g).hom ≫
        kernel.ι (structureProjectionOfHom B S hS (representedSpaceMap B S hS g)) =
      (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).map
          (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left)).ι ≫
        (representedAssociatedModuleObjUnitIso B S hS T
          (isAlgebraicSpace_yoneda B S hS T)).hom :=
  threeStepTransport_hom_comp
    (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T))
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left))
    _
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso_hom_comp_idealSheafι
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left))
    (representedAssociatedModuleObjKernelIso B S hS g) _
    (preservesKernelIso_hom_comp_ι
      (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)) _)
    (kernelRepresentedAssociatedModuleMapIso B S hS g) _
    (representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T))
    (kernel.lift_ι _ _ _)

end Square

/-! ### Transport of the edge comparison along an equality of morphisms of the site -/

section Congr

variable {T' T : BigFppfOver B S hS}

/-- **The comparison of the inverse image along a represented morphism with the Zariski pullback
is transported along an equality of two morphisms of the site** by the transport of its source
and of its target.  Both morphisms are variables, so the equality is discharged by substitution
and the two unitors of `CategoryTheory.Iso.trans`.

This is one of the two pieces the hypothesis `hpaste` of
`Stacks.ConormalComparison.comparison_square` needs: `hpaste` compares the edge comparisons of
the two routes round a square of closed subspaces, and the two routes are two *equal* morphisms
of the site rather than one.  It is stated between isomorphisms rather than between their forward
directions, for the reason recorded in the implementation notes of this file. -/
theorem representedAssociatedModulePullbackIso_congr {g₁ g₂ : T' ⟶ T} (h : g₁ = g₂)
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    representedAssociatedModulePullbackIso B S hS g₁
        (relativelyRepresentable_yoneda_map B S hS g₁) 𝓕 =
      eqToIso (congrArg (fun m : T' ⟶ T =>
          (modulePullback B S hS (representedSpaceMap B S hS m)).obj
            ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕))) h) ≪≫
        representedAssociatedModulePullbackIso B S hS g₂
            (relativelyRepresentable_yoneda_map B S hS g₂) 𝓕 ≪≫
          eqToIso (congrArg (fun m : T' ⟶ T =>
            (representedSmallEtaleModuleEquivalence B S hS T').functor.obj
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
                ((Scheme.Modules.pullback (B.inclusion.map m.left)).obj 𝓕))) h.symm) := by
  subst h
  exact Eq.trans (Iso.trans_refl _).symm (Iso.refl_trans _).symm

end Congr

/-! ### The transpose of the edge comparison, at arbitrary categories -/

/-- **The transpose along the adjunction of an equivalence read backwards** is the inverse of the
counit followed by the equivalence. -/
theorem symmToAdjunction_homEquiv {A B : Type*} [Category A] [Category B] (E : A ≌ B)
    (X : B) {Y : A} (h : E.inverse.obj X ⟶ Y) :
    E.symm.toAdjunction.homEquiv X Y h = (E.counitIso.app X).inv ≫ E.functor.map h :=
  E.symm.toAdjunction.homEquiv_unit X Y h

/-- The transpose along a composite adjunction is the transpose along the first factor of the
transpose along the second. -/
private theorem comp_homEquiv_apply {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} {H : C₂ ⥤ C₃} {I : C₃ ⥤ C₂} (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)
    (X : C₁) (Y : C₃) (f : H.obj (F.obj X) ⟶ Y) :
    (adj₁.comp adj₂).homEquiv X Y f = adj₁.homEquiv X (I.obj Y) (adj₂.homEquiv _ Y f) := by
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply]

/-- **A transpose along a composite adjunction whose second factor is an equivalence read
backwards.**  This is `CategoryTheory.Adjunction.comp_homEquiv` with
`AlgebraicGeometry.Space.symmToAdjunction_homEquiv` for the inner transpose. -/
theorem homEquiv_comp_symmToAdjunction {B B' A' : Type*} [Category B] [Category B']
    [Category A'] {P : B ⥤ B'} {Pr : B' ⥤ B} (adjP : P ⊣ Pr) (E' : A' ≌ B') (Z : B) {W : A'}
    (h : E'.inverse.obj (P.obj Z) ⟶ W) :
    (adjP.comp E'.symm.toAdjunction).homEquiv Z W h =
      adjP.homEquiv Z (E'.functor.obj W)
        ((E'.counitIso.app (P.obj Z)).inv ≫ E'.functor.map h) := by
  rw [comp_homEquiv_apply, symmToAdjunction_homEquiv]
  rfl

/-- **A transpose along a composite adjunction whose first factor is an equivalence read
backwards.**  This is `CategoryTheory.Adjunction.comp_homEquiv` with
`AlgebraicGeometry.Space.symmToAdjunction_homEquiv` for the outer transpose. -/
theorem symmToAdjunction_comp_homEquiv {A B A' : Type*} [Category A] [Category B] [Category A']
    {Q : A ⥤ A'} {Qr : A' ⥤ A} (E : A ≌ B) (adjQ : Q ⊣ Qr) (X : B) {Y : A'}
    (f : Q.obj (E.inverse.obj X) ⟶ Y) :
    (E.symm.toAdjunction.comp adjQ).homEquiv X Y f =
      (E.counitIso.app X).inv ≫ E.functor.map (adjQ.homEquiv _ Y f) := by
  rw [comp_homEquiv_apply, symmToAdjunction_homEquiv]
  rfl

/-- **Transposing along an adjunction transported by an isomorphism of the right adjoint** is
transposing along the original adjunction, followed by that isomorphism. -/
theorem ofNatIsoRight_homEquiv {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R₁ R₂ : D ⥤ C} (adj : L ⊣ R₁) (iso : R₁ ≅ R₂) (X : C) (Y : D) (f : L.obj X ⟶ Y) :
    (adj.ofNatIsoRight iso).homEquiv X Y f = adj.homEquiv X Y f ≫ iso.hom.app Y := by
  have hu : (adj.ofNatIsoRight iso).unit.app X =
      adj.unit.app X ≫ iso.hom.app (L.obj X) := rfl
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hu, Category.assoc,
    ← iso.hom.naturality f, ← Category.assoc]

/-- The counit of an equivalence at an object of the image is the image of the unit. -/
theorem counitIso_inv_app_functor {A B : Type*} [Category A] [Category B] (E : A ≌ B) (M : A) :
    (E.counitIso.app (E.functor.obj M)).inv = E.functor.map (E.unitIso.app M).hom := by
  rw [Iso.app_inv, Iso.app_hom]
  exact E.counitInv_app_functor M

/-- **The transpose of the conjugated comparison.**  In the situation of
`AlgebraicGeometry.Space.conjugateComparison_naturality`, suppose further that `P` and `Q` have
right adjoints `Pr`, `Qr`, that `σ` compares `Qr` read through `E` with `Pr` read through `E'`,
and that the comparison `ρ` is the canonical identification of the two left adjoints of
`E'.functor ⋙ Pr` — which is what `CategoryTheory.Adjunction.leftAdjointUniq` of the two
composite adjunctions is.  Then the transpose along `P ⊣ Pr` of `θ M` followed by `E'` of a
morphism is `E` of the transpose of that morphism, followed by `σ`.

This is the inverse-image half of the adjunction of [Stacks Project, Tag 03D7], read on the edge
comparison: the comparison is a `CategoryTheory.Adjunction.leftAdjointUniq`, so
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` identifies the two transposes,
and the two unitors of `CategoryTheory.Adjunction.comp` and the transport
`CategoryTheory.Adjunction.ofNatIsoRight` are unwound by the four preceding lemmas. -/
theorem conjugateComparison_homEquiv {A B A' B' : Type*} [Category A] [Category B]
    [Category A'] [Category B'] (E : A ≌ B) (E' : A' ≌ B')
    {P : B ⥤ B'} {Pr : B' ⥤ B} {Q : A ⥤ A'} {Qr : A' ⥤ A}
    (adjP : P ⊣ Pr) (adjQ : Q ⊣ Qr) (σ : Qr ⋙ E.functor ≅ E'.functor ⋙ Pr)
    (ρ : P ⋙ E'.inverse ≅ E.inverse ⋙ Q)
    (hρ : ρ = Adjunction.leftAdjointUniq (adjP.comp E'.symm.toAdjunction)
      ((E.symm.toAdjunction.comp adjQ).ofNatIsoRight σ))
    (θ : ∀ M : A, P.obj (E.functor.obj M) ≅ E'.functor.obj (Q.obj M))
    (hθ : ∀ M : A, θ M =
      (E'.counitIso.app (P.obj (E.functor.obj M))).symm ≪≫
        E'.functor.mapIso (ρ.app (E.functor.obj M) ≪≫ Q.mapIso (E.unitIso.app M).symm))
    (M : A) {W : A'} (ψ : Q.obj M ⟶ W) :
    adjP.homEquiv (E.functor.obj M) (E'.functor.obj W) ((θ M).hom ≫ E'.functor.map ψ) =
      E.functor.map (adjQ.homEquiv M W ψ) ≫ σ.hom.app W := by
  rw [hθ M]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc,
    ← E'.functor.map_comp]
  rw [← homEquiv_comp_symmToAdjunction adjP E' (E.functor.obj M), hρ,
    Adjunction.homEquiv_leftAdjointUniq_hom_app_comp, ofNatIsoRight_homEquiv,
    symmToAdjunction_comp_homEquiv, Adjunction.homEquiv_naturality_left,
    counitIso_inv_app_functor, ← E.functor.map_comp, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]
  rfl

/-- **The transpose of a comparison of two base changes, read at a morphism out of the image of
the base change.**  Let `F ⊣ Fr`, `F' ⊣ F'r`, `Q ⊣ Qr` and `R ⊣ Rr` be adjunctions, let
`τ : R ⋙ F' ≅ F ⋙ Q` compare the two routes round the square of left adjoints and let
`δ : Qr ⋙ Fr ≅ F'r ⋙ Rr` be its conjugate on the right adjoints.  Then the transpose along
`Q ⊣ Qr` of `τ⁻¹` followed by `F'` of a morphism `sA` is `F` of the transpose of `sA`, followed
by the comparison `η` that `δ` and the unit of `F' ⊣ F'r` assemble.

The proof is the mates correspondence `Stacks.CategoryTheory.homEquiv_conjugate'` for the two
composite adjunctions `R ⊣ Rr` with `F' ⊣ F'r` and `F ⊣ Fr` with `Q ⊣ Qr`, after which both
sides are transposes of the same morphism and the triangle identity of `F ⊣ Fr` removes the
counit that `η` carries. -/
theorem homEquiv_comparison_inv_comp {A A' C C' : Type*} [Category A] [Category A'] [Category C]
    [Category C'] {F : C ⥤ A} {Fr : A ⥤ C} {F' : C' ⥤ A'} {F'r : A' ⥤ C'}
    {Q : A ⥤ A'} {Qr : A' ⥤ A} {R : C ⥤ C'} {Rr : C' ⥤ C}
    (adjF : F ⊣ Fr) (adjF' : F' ⊣ F'r) (adjQ : Q ⊣ Qr) (adjR : R ⊣ Rr)
    (τ : R ⋙ F' ≅ F ⋙ Q) (δ : Qr ⋙ Fr ≅ F'r ⋙ Rr)
    (hδ : conjugateEquiv (adjR.comp adjF') (adjF.comp adjQ) τ.inv = δ.inv)
    {OC' : C} {OC : C'} (sA : R.obj OC' ⟶ OC) (tA : OC' ⟶ Rr.obj OC)
    (hsA : adjR.homEquiv OC' OC sA = tA)
    (η : F.obj (Rr.obj OC) ⟶ Qr.obj (F'.obj OC))
    (hη : η = F.map (Rr.map (adjF'.unit.app OC) ≫ (δ.app (F'.obj OC)).inv) ≫
      adjF.counit.app (Qr.obj (F'.obj OC))) :
    adjQ.homEquiv (F.obj OC') (F'.obj OC) ((τ.app OC').inv ≫ F'.map sA) = F.map tA ≫ η := by
  have hinner : adjF'.homEquiv (R.obj OC') (F'.obj OC) (F'.map sA) =
      sA ≫ adjF'.unit.app OC :=
    (adjF'.homEquiv_unit _ _ _).trans (adjF'.unit.naturality sA).symm
  have hlhs : adjF.homEquiv OC' (Qr.obj (F'.obj OC))
        (adjQ.homEquiv (F.obj OC') (F'.obj OC) ((τ.app OC').inv ≫ F'.map sA)) =
      (tA ≫ Rr.map (adjF'.unit.app OC)) ≫ (δ.app (F'.obj OC)).inv := by
    rw [← comp_homEquiv_apply, Iso.app_inv,
      Stacks.CategoryTheory.homEquiv_conjugate' (adjR.comp adjF') (adjF.comp adjQ) τ.inv,
      comp_homEquiv_apply, hinner,
      Adjunction.homEquiv_naturality_right, hsA, hδ, Iso.app_inv]
  have htr : adjF.homEquiv (Rr.obj OC) (Qr.obj (F'.obj OC)) η =
      Rr.map (adjF'.unit.app OC) ≫ (δ.app (F'.obj OC)).inv := by
    refine (adjF.homEquiv (Rr.obj OC) (Qr.obj (F'.obj OC))).symm.injective ?_
    rw [Equiv.symm_apply_apply, hη, Adjunction.homEquiv_counit]
  have hrhs : adjF.homEquiv OC' (Qr.obj (F'.obj OC)) (F.map tA ≫ η) =
      (tA ≫ Rr.map (adjF'.unit.app OC)) ≫ (δ.app (F'.obj OC)).inv := by
    rw [Adjunction.homEquiv_naturality_left, htr, Category.assoc]
  exact (adjF.homEquiv OC' (Qr.obj (F'.obj OC))).injective (hlhs.trans hrhs.symm)

/-- **A comparison of module categories compatible with inverse image carries one canonical map
`r^*𝒪 ⟶ 𝒪` to the other as soon as it does so on transposes.**  This is the hypothesis `hstr` of
`AlgebraicGeometry.Space.idealComparison_of_inclusions`, reduced to the *direct-image* square
`hsquare` of the two structure projections — the shape in which this development has it.

The data are those of `AlgebraicGeometry.Space.conjugateComparison_homEquiv` together with the
two base-change layers `F`, `F'`, `R`, `τ` of
`AlgebraicGeometry.Space.conjugateComparison_comp_inv_naturality`, the assembled comparison `Θ`,
the two maps `sA`, `sB` of structure sheaves and their transposes `tA`, `tB`, and the
identification `κ` of the transported structure sheaf with the structure sheaf.

Both `sA` and `sB` are morphisms out of an inverse image, so the adjunction of
[Stacks Project, Tag 03D7] turns the claim into an equality of transposes: on the right
`hsB` names `tB`, and on the left `AlgebraicGeometry.Space.conjugateComparison_homEquiv`
converts the transpose of `Θ` into `σ`, after which `hA` replaces the transpose of `sA` by `tA`
and `hsquare` is exactly what remains. -/
theorem structureComparison_of_transposes {A B A' B' C C' : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category C] [Category C']
    (E : A ≌ B) (E' : A' ≌ B')
    {P : B ⥤ B'} {Pr : B' ⥤ B} {Q : A ⥤ A'} {Qr : A' ⥤ A}
    (adjP : P ⊣ Pr) (adjQ : Q ⊣ Qr) (σ : Qr ⋙ E.functor ≅ E'.functor ⋙ Pr)
    (ρ : P ⋙ E'.inverse ≅ E.inverse ⋙ Q)
    (hρ : ρ = Adjunction.leftAdjointUniq (adjP.comp E'.symm.toAdjunction)
      ((E.symm.toAdjunction.comp adjQ).ofNatIsoRight σ))
    (θ : ∀ M : A, P.obj (E.functor.obj M) ≅ E'.functor.obj (Q.obj M))
    (hθ : ∀ M : A, θ M =
      (E'.counitIso.app (P.obj (E.functor.obj M))).symm ≪≫
        E'.functor.mapIso (ρ.app (E.functor.obj M) ≪≫ Q.mapIso (E.unitIso.app M).symm))
    (F : C ⥤ A) (F' : C' ⥤ A') (R : C ⥤ C') (τ : R ⋙ F' ≅ F ⋙ Q)
    (Θ : ∀ X : C, P.obj (E.functor.obj (F.obj X)) ≅ E'.functor.obj (F'.obj (R.obj X)))
    (hΘ : ∀ X : C, Θ X = θ (F.obj X) ≪≫ E'.functor.mapIso (τ.app X).symm)
    {OC' : C} {OC : C'} (sA : R.obj OC' ⟶ OC)
    {V : A'} (ζ : F'.obj OC ⟶ V) (UB : B') (κ : E'.functor.obj V ≅ UB)
    (cX : E'.functor.obj (F'.obj OC) ≅ UB) (hcX : cX.hom = E'.functor.map ζ ≫ κ.hom)
    (UB' : B) (cX' : E.functor.obj (F.obj OC') ≅ UB')
    (sB : P.obj UB' ⟶ UB) {tB : UB' ⟶ Pr.obj UB} (hsB : tB = adjP.homEquiv UB' UB sB)
    {N : C} (tA : OC' ⟶ N) (η : F.obj N ⟶ Qr.obj (F'.obj OC))
    (hA : adjQ.homEquiv (F.obj OC') (F'.obj OC) ((τ.app OC').inv ≫ F'.map sA) =
      F.map tA ≫ η)
    (hsquare : E.functor.map (F.map tA) ≫
        (E.functor.map (η ≫ Qr.map ζ) ≫ σ.hom.app V ≫ Pr.map κ.hom) = cX'.hom ≫ tB) :
    E'.functor.map (F'.map sA) ≫ cX.hom = (Θ OC').inv ≫ P.map cX'.hom ≫ sB := by
  have hnat : σ.hom.app (F'.obj OC) ≫ Pr.map (E'.functor.map ζ) =
      E.functor.map (Qr.map ζ) ≫ σ.hom.app V := (σ.hom.naturality ζ).symm
  have hw : σ.hom.app (F'.obj OC) ≫ Pr.map cX.hom =
      E.functor.map (Qr.map ζ) ≫ σ.hom.app V ≫ Pr.map κ.hom := by
    rw [hcX, Pr.map_comp, ← Category.assoc, hnat, Category.assoc]
  have hsq : E.functor.map (F.map tA) ≫
      E.functor.map η ≫ (σ.hom.app (F'.obj OC) ≫ Pr.map cX.hom) = cX'.hom ≫ tB :=
    Eq.trans (whisker_eq _ (Eq.trans (whisker_eq _ hw)
      (Eq.trans (Category.assoc _ _ _).symm
        (eq_whisker (E.functor.map_comp _ _).symm _)))) hsquare
  have hu : (Θ OC').hom ≫ E'.functor.map (F'.map sA) =
      (θ (F.obj OC')).hom ≫ E'.functor.map ((τ.app OC').inv ≫ F'.map sA) := by
    rw [hΘ OC']
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      ← E'.functor.map_comp]
  have hlhs : adjP.homEquiv (E.functor.obj (F.obj OC')) UB
        ((Θ OC').hom ≫ E'.functor.map (F'.map sA) ≫ cX.hom) = cX'.hom ≫ tB := by
    rw [← Category.assoc, hu, Adjunction.homEquiv_naturality_right,
      conjugateComparison_homEquiv E E' adjP adjQ σ ρ hρ θ hθ, Category.assoc, hA,
      Functor.map_comp, Category.assoc, hsq]
  have hrhs : adjP.homEquiv (E.functor.obj (F.obj OC')) UB (P.map cX'.hom ≫ sB) =
      cX'.hom ≫ tB := by
    rw [Adjunction.homEquiv_naturality_left, hsB]
  exact (Iso.eq_inv_comp _).mpr
    ((adjP.homEquiv (E.functor.obj (F.obj OC')) UB).injective (hlhs.trans hrhs.symm))

/-! ### The structure map at the representing morphism -/

section StructurePullback

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The direct image along the represented morphism carries the identification of the transported
structure sheaf with the structure sheaf to the identity:
`AlgebraicGeometry.Space.representedModulePushforwardObjUnitIso` is `CategoryTheory.Iso.refl`. -/
theorem modulePushforward_map_representedModulePushforwardObjUnitIso_hom :
    (modulePushforward B S hS (representedSpaceMap B S hS g)).map
        (representedModulePushforwardObjUnitIso B S hS T').hom = 𝟙 _ := by
  rw [representedModulePushforwardObjUnitIso]
  exact (modulePushforward B S hS (representedSpaceMap B S hS g)).map_id _

/-- The comparison of the two direct images read at the structure sheaf of the scheme underlying
`T'`, with that sheaf spelled as the small étale structure sheaf rather than through
`AlgebraicGeometry.Space.representedSchemeStructureSheaf`.  The two spellings are the same by
unfolding an abbreviation, and this is the only form in which the comparison meets
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit`, whose target carries the first spelling;
crossing the two inside the application of a functor is what the implementation notes of this
file record as unaffordable. -/
theorem representedModulePushforwardSquareIso_hom_app_unit_structureSheaf :
    (representedModulePushforwardSquareIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)).hom.app
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      (representedModulePushforwardSquareIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g)).hom.app
        (SheafOfModules.unit (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T')
          T'.left.property)) := rfl

variable [_root_.AlgebraicGeometry.IsAffineHom
  (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)]

/-- `AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square` in the shape
that `AlgebraicGeometry.Space.structureComparison_of_transposes` consumes: the comparison functor
written as the associated module followed by the identification of the two small étale sites, the
target of the comparison of direct images spelled through the small étale structure sheaf, and
the identification of the transported structure sheaf appended. -/
private theorem representedAssociatedModule_structureProjection_square_transposed
    (tA : SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf ⟶
      (Scheme.Modules.pushforward
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf))
    (hsquare : (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).map
          tA ≫
        ((representedModulePushforward B S hS T).map
            ((_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso
                  (associatedBigEtaleSite B) g.left
                  (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
                  (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
                    ((BigFppfOver.toScheme B S hS).obj T'))).inv ≫
              (SheafOfModules.pushforward.{u}
                  (representedSchemeStructureMapRing B S hS g)).map
                (SheafOfModules.pullbackObjUnitToUnit.{u}
                  (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj T') T'.left.property))) ≫
          (representedModulePushforwardSquareIso B S hS g
              (relativelyRepresentable_yoneda_map B S hS g)).hom.app
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) =
      (representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T)).hom ≫
        structureProjectionOfHom B S hS (representedSpaceMap B S hS g)) :
    (representedSmallEtaleModuleEquivalence B S hS T).functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map tA) ≫
        ((representedSmallEtaleModuleEquivalence B S hS T).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso
                  (associatedBigEtaleSite B) g.left
                  (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
                  (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
                    ((BigFppfOver.toScheme B S hS).obj T'))).inv ≫
              (SheafOfModules.pushforward.{u}
                  (representedSchemeStructureMapRing B S hS g)).map
                (SheafOfModules.pullbackObjUnitToUnit.{u}
                  (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj T') T'.left.property))) ≫
          (representedModulePushforwardSquareIso B S hS g
              (relativelyRepresentable_yoneda_map B S hS g)).hom.app
              (SheafOfModules.unit (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
                (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T')
                T'.left.property)) ≫
            (modulePushforward B S hS (representedSpaceMap B S hS g)).map
              (representedModulePushforwardObjUnitIso B S hS T').hom) =
      (representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T)).hom ≫
        structureProjectionOfHom B S hS (representedSpaceMap B S hS g) :=
  Eq.trans (whisker_eq _ (whisker_eq _
      (Eq.trans (whisker_eq _
          (modulePushforward_map_representedModulePushforwardObjUnitIso_hom B S hS g))
        (Category.comp_id _))))
    (Eq.trans (whisker_eq _ (whisker_eq _
      (representedModulePushforwardSquareIso_hom_app_unit_structureSheaf B S hS g).symm))
      hsquare)

/-- **The comparison functor carries the canonical map `r^*𝒪_T ⟶ 𝒪_{T'}` of Zariski modules on
the schemes to `AlgebraicGeometry.Space.structureModulePullbackMap` of the represented
morphism**, read through `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso` at both
ends and the edge comparison
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` in the middle.  This is the
hypothesis `hstr` of `AlgebraicGeometry.Space.idealComparison_of_inclusions` at the representable
instantiation, and the inverse-image counterpart of the direct-image square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square`.

The map `r^*𝒪_T ⟶ 𝒪_{T'}` is a parameter and the direct-image square at its transpose is the
hypothesis; the *Freeze* section of this file says why neither can be written out here.

The proof is `AlgebraicGeometry.Space.structureComparison_of_transposes` at the two
identifications of small étale module categories, the inverse image of Stacks 03LU and the
small étale pullback of the underlying morphism of schemes, their two right adjoints,
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`,
`AlgebraicGeometry.Space.representedModulePullbackIso`,
`AlgebraicGeometry.Space.representedModuleObjPullbackIso`, the associated module at `T` and at
`T'`, `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` and
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, with
`AlgebraicGeometry.Space.homEquiv_comparison_inv_comp` for the transpose of the edge comparison
and `AlgebraicGeometry.Space.structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap`
for the transpose of `AlgebraicGeometry.Space.structureModulePullbackMap`. -/
theorem representedAssociatedModule_structurePullback_square
    (sA : (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf) ⟶
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
    (hsquare : (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g.left)).homEquiv _ _ sA) ≫
        ((representedModulePushforward B S hS T).map
            ((_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso
                  (associatedBigEtaleSite B) g.left
                  (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
                  (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
                    ((BigFppfOver.toScheme B S hS).obj T'))).inv ≫
              (SheafOfModules.pushforward.{u}
                  (representedSchemeStructureMapRing B S hS g)).map
                (SheafOfModules.pullbackObjUnitToUnit.{u}
                  (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj T') T'.left.property))) ≫
          (representedModulePushforwardSquareIso B S hS g
              (relativelyRepresentable_yoneda_map B S hS g)).hom.app
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) =
      (representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T)).hom ≫
        structureProjectionOfHom B S hS (representedSpaceMap B S hS g)) :
    (representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')).map sA ≫
        (representedAssociatedModuleObjUnitIso B S hS T'
          (isAlgebraicSpace_yoneda B S hS T')).hom =
      (representedAssociatedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
          (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).inv ≫
        (modulePullback B S hS (representedSpaceMap B S hS g)).map
            (representedAssociatedModuleObjUnitIso B S hS T
              (isAlgebraicSpace_yoneda B S hS T)).hom ≫
          structureModulePullbackMap B S hS (representedSpaceMap B S hS g) := by
  refine structureComparison_of_transposes
    (representedSmallEtaleModuleEquivalence B S hS T)
    (representedSmallEtaleModuleEquivalence B S hS T')
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS g))
    (representedModulePushforwardSquareIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
    (representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)) rfl
    (representedModuleObjPullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)) (representedModuleObjPullbackIso_eq B S hS g)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left))
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
      (associatedBigEtaleSite B) g.left)
    (representedAssociatedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
    (representedAssociatedModulePullbackIso_eq_yoneda B S hS g) sA
    (SheafOfModules.pullbackObjUnitToUnit.{u}
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property))
    (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩))
    (representedModulePushforwardObjUnitIso B S hS T')
    (representedAssociatedModuleObjUnitIso B S hS T' (isAlgebraicSpace_yoneda B S hS T'))
    rfl
    (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
    (representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T))
    (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))
    (structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap B S hS
      (representedSpaceMap B S hS g))
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) g.left)).homEquiv _ _ sA)
    (_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso
        (associatedBigEtaleSite B) g.left
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
        (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
          ((BigFppfOver.toScheme B S hS).obj T'))).inv
    (homEquiv_comparison_inv_comp
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (representedSchemeStructureMapRing B S hS g))
      (Scheme.Modules.pullbackPushforwardAdjunction
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left))
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
        (associatedBigEtaleSite B) g.left)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso
        (associatedBigEtaleSite B) g.left)
      (_root_.AlgebraicGeometry.SmallEtale.conjugateEquiv_associatedModuleBaseChangeIso_inv
        (associatedBigEtaleSite B) g.left)
      sA _ rfl _
      (_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso_inv
        (associatedBigEtaleSite B) g.left
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
        (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
          ((BigFppfOver.toScheme B S hS).obj T')))) ?_
  exact representedAssociatedModule_structureProjection_square_transposed B S hS g _ hsquare

end StructurePullback

/-! ### The inclusion at a closed subspace -/

variable (T : BigFppfOver B S hS) (Z : ClosedSubspaces B S hS (yoneda.obj T))

/-- **Precomposing the morphism of algebraic spaces with an isomorphism does not change the
inclusion of the kernel of its canonical morphism of modules.**
`AlgebraicGeometry.Space.kernelStructureProjectionOfHomIsoOfIso` is
`CategoryTheory.Limits.kernel.mapIso` at a square whose vertical arrow at the source is the
identity, so its forward direction carries one inclusion to the other. -/
theorem kernelStructureProjectionOfHomIsoOfIso_hom_comp_ι {X Y W : AlgebraicSpaces B S hS}
    (ef : X ≅ Y) (g : Y ⟶ W) (k : X ⟶ W) (h : ef.hom ≫ g = k) :
    (kernelStructureProjectionOfHomIsoOfIso B S hS ef g k h).hom ≫
        kernel.ι (structureProjectionOfHom B S hS k) =
      kernel.ι (structureProjectionOfHom B S hS g) :=
  Eq.trans (kernel.lift_ι _ _ _) (Category.comp_id _)

/-- **The presentation of the defining ideal sheaf of a closed subspace of a representable
algebraic space as the kernel of the canonical morphism of modules of the representing morphism
carries the inclusion of that kernel to the inclusion of the ideal sheaf.**  Its two steps are
`AlgebraicGeometry.Space.definingIdealSheafIsoKernel_hom_comp_ι` and
`AlgebraicGeometry.Space.kernelStructureProjectionOfHomIsoOfIso_hom_comp_ι` at the factorisation
`AlgebraicGeometry.Space.representedSpaceMap_representingHom`. -/
theorem definingIdealSheafIsoKernelRepresented_hom_comp_ι :
    (definingIdealSheafIsoKernelRepresented B S hS T Z).hom ≫
        kernel.ι (structureProjectionOfHom B S hS
          (representedSpaceMap B S hS (representingHom B S hS T Z))) =
      (definingIdealSheaf B S hS
        ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z).ι :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans
      (whisker_eq _ (kernelStructureProjectionOfHomIsoOfIso_hom_comp_ι B S hS
        (representedSubspaceIso B S hS T Z)
        (subspaceInclusion B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z)
        (representedSpaceMap B S hS (representingHom B S hS T Z))
        (representedSpaceMap_representingHom B S hS T Z).symm))
      (definingIdealSheafIsoKernel_hom_comp_ι B S hS
        ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z))

/-- **The object identification of the two ideal sheaves of a closed subspace of a representable
algebraic space is compatible with their inclusions into the two structure sheaves.**  Read on
the inverse, `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` carries the inclusion
`𝓘_Z ⊆ 𝒪` of Stacks 03MB to the transport of the inclusion of the defining ideal sheaf of the
representing closed immersion of schemes, read through
`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`.

Both presentations of the ideal sheaf are presentations as the kernel of the canonical morphism
of modules of the represented morphism, each compatible with its inclusion —
`AlgebraicGeometry.Space.definingIdealSheafIsoKernelRepresented_hom_comp_ι` and
`AlgebraicGeometry.Space.representedAssociatedModuleObjDefiningIdealOfHomIso_hom_comp_ι` — and
the identification is the first followed by the inverse of the second, so
`AlgebraicGeometry.Space.transSymm_inv_comp` composes them.  Nothing is assumed: the affineness
of the representing morphism of schemes is discharged by
`AlgebraicGeometry.Space.isAffineHom_schemeHom_representingHom`.

This is the statement the hypothesis `hideal` of
`Stacks.ConormalComparison.comparison_square` is reduced to by
`AlgebraicGeometry.Space.idealComparison_of_inclusions`. -/
theorem definingIdealSheafIsoRepresented_inv_comp_ι :
    (definingIdealSheafIsoRepresented B S hS T Z).inv ≫
        (definingIdealSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z).ι =
      (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).map
          (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T Z).left)).ι ≫
        (representedAssociatedModuleObjUnitIso B S hS T
          (isAlgebraicSpace_yoneda B S hS T)).hom :=
  let := isAffineHom_schemeHom_representingHom B S hS T Z
  transSymm_inv_comp _ _ _ _
    (definingIdealSheafIsoKernelRepresented_hom_comp_ι B S hS T Z)
    (representedAssociatedModuleObjDefiningIdealOfHomIso_hom_comp_ι B S hS
      (representingHom B S hS T Z))

end AlgebraicGeometry.Space

end
