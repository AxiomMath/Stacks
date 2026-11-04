module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedSectionsModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeSectionsModelCrossing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayRestrictSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections over an open and over the open subscheme, at the source of the Leray comparison

Let `f : X ⟶ S` be a morphism of schemes and `V ⊆ S` an open. The Leray comparison of
[Stacks, Tag 0D5W], `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison`, is available both
for `f` over `V` and for the restricted morphism `f ∣_ V` over the whole of the open subscheme
`V`; the tail of conclusion (c) of [Stacks, Tag 0EX3] meets the first and
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOverOpen_inv_eq_lerayComparison`
delivers the second, so the two have to be identified.

Both Leray comparisons are `CategoryTheory.Functor.rightDerivedDesc`s of their units, so the
identification is determined by the **degreewise** comparison of their sources:
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections f V`, sections of a sheaf of
`𝒪_X`-modules over `f⁻¹V` read over `Γ(S, V)`, against
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections (f ∣_ V) ⊤`, the global sections of the
restriction to the open subscheme `f⁻¹V` read over `Γ(V, ⊤)` and then over `Γ(S, V)`. This file
builds that comparison, and builds it twice, by the two routes the two sides of (c) present it
in.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.restrictScalarsSquareIso` — restriction of
  scalars along either side of a commuting square of ring maps, as an isomorphism of **functors**.
  Its value at a module is
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.restrictScalarsSquareObjIso`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsOpenSubschemeIso` — **the model
  crossing at the source of the Leray comparison**, by the sections route: sections over `f⁻¹V`
  are the global sections of the restriction to the open subscheme `f⁻¹V`, read over `Γ(S, V)`.
  No hypothesis on `f` or on `V`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsOpenSubschemePushforwardIso` —
  the same comparison by the **direct-image** route: sections over `V` of `f_* M`, restricted to
  the open subscheme `V` by [Stacks, Tag 01E5] undervied, are the global sections of
  `(f ∣_ V)_*(M|_{f⁻¹V})`. No hypothesis on `f` or on `V`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.modulePushforwardMorphismRestrictIso` —
  [Stacks, Tag 01E5] undervied at Mathlib's restricted morphism `f ∣_ V`: the
  isomorphism `Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`, whose restricted morphism is
  the ringed-space one, transported along
  `…SchemeHigherDirectImage.toShHom_morphismRestrict`. Nothing is re-proved; the transport is an
  `eqToIso`, which is why it has a name at all — a definitional identity does not serve.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.restrictScalarsSquareIso_app`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsOpenSubschemeIso_eq` — **the two
  routes are the same transformation.** No hypothesis on `f` or on `V`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.heq_eqToIso_trans_val_app` — an equality of
  functors into sheaves of modules, composed with an isomorphism that is the identity on local
  sections, is the identity on local sections. Stated at the generality of an arbitrary site.

## Implementation notes

*Why the restriction functor is the ringed-space one.* The two spellings
`AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι` and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction X.toRingedSpace V` are equal functors
(`…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`) but are *not* interchangeable
for instance synthesis, and the derived machinery needs the second: `HasDerivedCategory X.Modules`
is not synthesisable — `AlgebraicGeometry.Scheme.Modules` is a semireducible `def`, unfolding for
unification but not at instance-synthesis transparency — while everything at the
`SheafOfModules (structureSheafRing _)` spelling is found. With `moduleRestriction`
the composite `moduleRestriction X U ⋙ sectionsOverOpen (U : Scheme) ⊤` **is**
`sectionsOverOpen X (U.ι ''ᵁ ⊤)` by `rfl`, so the whole of the crossing of the two sections
functors is `sectionsOnImageTopNatIso` and nothing is re-proved.

*Three further `rfl`s that decide the shapes below*:
`Stacks.Cohomology.SchemeOpenSections.imageTop X U = U.ι ''ᵁ ⊤`;
`AlgebraicGeometry.sectionsOn X U = sectionsOverOpen X.toRingedSpace U`; and
`modulePushforward (f ∣_ V) ⋙ sectionsOverOpen (V : Scheme) ⊤ = preimageSections (f ∣_ V) ⊤`,
which is `pushforwardPreimageSectionsIso` at `⊤` of the open subscheme.

*The one thing that is not free: the two readings of the scalars.* The sections route reads them
as `f^♯` at `V` after the comparison `AlgebraicGeometry.Scheme.Opens.topIso` at `f⁻¹V`, the
open-subscheme route as `(f ∣_ V)^♯` at `⊤` after `topIso` at `V`. The two composites are equal
ring maps by `…TopDegreeBaseChange.app_comp_topIso_inv_hom`, so the passage is
`restrictScalarsSquareIso` — the functorial form of `restrictScalarsSquareObjIso`, which that
file states at an object because that is all its consumer needed.

*The two routes are equal, and how the heartbeat budget is met.* `rfl` on the two assembled natural transformations, `rfl` on their components at a module, `rfl` on the
components of their inverses and `ext M x; rfl` each exhaust the 200,000-heartbeat budget at
`whnf` or at `isDefEq`. The proof is **not** a shuffle at variables
(`…DerivedSectionsLeray.lerayCompositeComparison_restrictSource`'s `glue_two_naturalities`), and
it is not a decomposition of either route into factors. It is that each route's **inverse** is,
on a local section, *heterogeneously equal to that section*: both are restriction maps of the
sheaf of modules along an equality of opens of `X`, and
`…HigherDirectImage.heq_val_map_eqToHom` says exactly that such a restriction is the identity up
to `HEq`. Two maps with the same source and target that are both `HEq` the identity are equal, by
`eq_of_heq`; no factor of either route is ever looked inside, and no reassociation is performed.

The three `HEq`s this needs are cheap where the `rfl`s are not, because each is matched against a
*named* restriction map rather than against the other route:
`heq_preimageSectionsOpenSubschemeIso_inv_app` is one application of `heq_val_map_eqToHom`;
`heq_modulePushforwardMorphismRestrictIso_hom_app_val_app` is
`…modulePushforwardRestrictIso_hom_app_val_app_heq` carried across the `eqToIso` by
`heq_eqToIso_trans_val_app`; and
`heq_preimageSectionsOpenSubschemePushforwardIso_inv_app` composes that with
`heq_val_map_eqToHom` at the direct image. The inner section is supplied **explicitly** in that
last step: left as a metavariable, the unifier unfolds the whole route and times out.

*A de-privatization candidate.* `heq_eqToIso_trans_val_app`'s content — that
`eqToHom` of an equality of sheaves of modules is the identity on local sections up to `HEq` — is
already proved in the tree as `eqToHom_sheaf_app_heq`
(`Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAxiomC.lean`), where it is declared
`private` and is stated for a `AlgebraicGeometry.RingedSite`. The one public relative,
`Stacks.SheafOfModules.GradedAlgebra.heq_eqToHom_val_app`
(`Algebra/Category/ModuleCat/Sheaf/TensorSheafWorldBridge.lean`), is for a family of sheaves of
modules indexed by `ℤ` and an equality of degrees, not for an equality of sheaves. Making the
first public, at the site generality, would subsume the lemma declared here.

*What is still owed.* The derived packaging: the two `rightDerivedDesc`s and the square. The
ledger of `BaseChangeSectionsTail.lean` measures them.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 0D5W] carries its attribute where the Leray
comparison is proved invertible, [Stacks, Tag 01E5] where the restriction comparison is built, and
conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
  (moduleRestriction modulePushforwardRestrictIso heq_val_map_eqToHom
    modulePushforwardRestrictIso_hom_app_val_app_heq)
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage (toShHom_morphismRestrict)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen preimageSections)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### An equality of functors into sheaves of modules, on local sections -/

/-- **An equality of functors into sheaves of modules does nothing to a local section.** If
`e : F = G` is an equality of functors into sheaves of modules on a site and `α : G ≅ H` is an
isomorphism that is the identity on local sections over `W`, then so is `eqToIso e ≪≫ α`: the
transport along `e` changes the type of the section and not the section.

The hypothesis and the conclusion quantify over sections of two *different* sheaves, which is why
this is not a corollary of `α`'s own statement; `e` is substituted before either is introduced.
See this module's implementation notes for the private declaration this duplicates nothing of. -/
theorem heq_eqToIso_trans_val_app {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{u}}
    {F G H : C ⥤ SheafOfModules.{u} R} (e : F = G) (α : G ≅ H) (M : C) (W : Dᵒᵖ)
    (hα : ∀ y : (G.obj M).val.obj W, HEq ((α.hom.app M).val.app W y) y)
    (x : (F.obj M).val.obj W) :
    HEq (((eqToIso e ≪≫ α).hom.app M).val.app W x) x := by
  subst e
  rw [eqToIso_refl, Iso.refl_trans]
  exact hα x

/-! ### Restriction of scalars along two equal composites, as functors -/

/-- **Restricting scalars twice along either side of a commuting square of ring maps, as an
isomorphism of functors.** If `b ∘ a = b' ∘ a'`, then restricting along `b` and then along `a`
is the same functor `ModuleCat T ⥤ ModuleCat R` as restricting along `b'` and then along `a'`.

This is the functorial form of `restrictScalarsSquareObjIso`, which states the comparison at one
module because that is all its consumer needed; by `restrictScalarsSquareIso_app` the value of
this isomorphism at a module is that one. Stated at variables, where both reassociations of the
restriction of scalars are free. -/
def restrictScalarsSquareIso {R S S' T : Type u} [Ring R] [Ring S] [Ring S'] [Ring T]
    (a : R →+* S) (b : S →+* T) (a' : R →+* S') (b' : S' →+* T) (h : b.comp a = b'.comp a') :
    ModuleCat.restrictScalars b ⋙ ModuleCat.restrictScalars a ≅
      ModuleCat.restrictScalars b' ⋙ ModuleCat.restrictScalars a' :=
  (ModuleCat.restrictScalarsComp' a b (b.comp a) rfl).symm ≪≫
    ModuleCat.restrictScalarsCongr h ≪≫
      ModuleCat.restrictScalarsComp' a' b' (b'.comp a') rfl

/-- The functorial square of `restrictScalarsSquareIso` is the object-level
`restrictScalarsSquareObjIso` at each module, by definition. -/
theorem restrictScalarsSquareIso_app {R S S' T : Type u} [Ring R] [Ring S] [Ring S'] [Ring T]
    (a : R →+* S) (b : S →+* T) (a' : R →+* S') (b' : S' →+* T) (h : b.comp a = b'.comp a')
    (M : ModuleCat.{u} T) :
    (restrictScalarsSquareIso a b a' b' h).app M = restrictScalarsSquareObjIso a b a' b' h M :=
  rfl

/-! ### The crossing at the source of the Leray comparison -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- **Sections over `f⁻¹V` are the global sections of the restriction to the open subscheme
`f⁻¹V`.** For a morphism of schemes `f : X ⟶ S` and an open `V ⊆ S`, the degreewise source of
the Leray comparison of [Stacks, Tag 0D5W] for `f` over `V` is the degreewise source of the
Leray comparison for the restricted morphism `f ∣_ V` over `⊤`, composed with the restriction to
the open subscheme and read over `Γ(S, V)` by restriction of scalars along
`AlgebraicGeometry.Scheme.Opens.topIso` at `V`:

> `Γ(f⁻¹V, -) ≅ (-)|_{f⁻¹V}` followed by `Γ((f ∣_ V)⁻¹⊤, -)`, over `Γ(S, V)`.

It is the crossing `sectionsOnImageTopNatIso` of the two sections functors at the open
`f⁻¹V` of `X`, together with the identification `restrictScalarsSquareIso` of the two readings of
the scalars, whose input is `app_comp_topIso_inv_hom`. There is no hypothesis on `f`, on `V` or on
the module. -/
def preimageSectionsOpenSubschemeIso :
    preimageSections f.toLRSHom.toShHom V ≅
      moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
        preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom :=
  Functor.isoWhiskerRight (sectionsOnImageTopNatIso X (f ⁻¹ᵁ V)).symm
      (ModuleCat.restrictScalars (f.app V).hom) ≪≫
    Functor.isoWhiskerLeft
      (moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
        sectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace ⊤)
      (restrictScalarsSquareIso _ _ _ _ (app_comp_topIso_inv_hom f V))

/-- **[Stacks, Tag 01E5] undervied, at Mathlib's restricted morphism.** Restricting a sheaf of
`𝒪_X`-modules to `f⁻¹V` and pushing it forward along `f ∣_ V` agrees with pushing it forward
along `f` and restricting to `V`.

This is `…HigherDirectImage.modulePushforwardRestrictIso`, whose restricted morphism is
`…HigherDirectImage.restrictedMorphism`, carried across the identification
`…SchemeHigherDirectImage.toShHom_morphismRestrict` of that morphism with Mathlib's `f ∣_ V`.
Nothing is re-proved. It carries a name because the identification is an `eqToIso` of a
non-definitional equality of morphisms, so no definitional identity serves, and because
`heq_modulePushforwardMorphismRestrictIso_hom_app_val_app` has to speak about it. -/
@[ega "II 1.1.1" "partial"]
def modulePushforwardMorphismRestrictIso :
    moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
          modulePushforward (f ∣_ V).toLRSHom.toShHom ≅
      modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction S.toRingedSpace V :=
  eqToIso (by rw [toShHom_morphismRestrict f V]; rfl) ≪≫
    modulePushforwardRestrictIso f.toLRSHom.toShHom V

/-- **`modulePushforwardMorphismRestrictIso` is the identity on local sections.** On sections over
an open `W ⊆ V` it is the restriction map of the sheaf of modules along the identification of
`(f ∣_ V)⁻¹(W)` with `f⁻¹(W)`, which is the identity once the transport of the type of sections is
taken into account. The underived comparison contributes
`…HigherDirectImage.modulePushforwardRestrictIso_hom_app_val_app_heq` and the transport
contributes nothing, by `heq_eqToIso_trans_val_app`. -/
theorem heq_modulePushforwardMorphismRestrictIso_hom_app_val_app
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (W : (Opens ((V : Scheme) : Type u))ᵒᵖ)
    (x : ((moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
      modulePushforward (f ∣_ V).toLRSHom.toShHom).obj M).val.obj W) :
    HEq (((modulePushforwardMorphismRestrictIso f V).hom.app M).val.app W x) x :=
  heq_eqToIso_trans_val_app _ (modulePushforwardRestrictIso f.toLRSHom.toShHom V) M W
    (fun y => modulePushforwardRestrictIso_hom_app_val_app_heq f.toLRSHom.toShHom V M W y) x

/-- The first factor of `preimageSectionsOpenSubschemePushforwardIso`, isolated so that the
decomposition of its source into a direct image followed by sections over `V` is written out:
sections over `f⁻¹V` are sections over `V` of the direct image
(`…DerivedSectionsLeray.pushforwardPreimageSectionsIso`, the identity), and those are the global
sections of the restriction of the direct image to the open subscheme `V`, by
`sectionsOnImageTopNatIso` at `V`. -/
def preimageSectionsRestrictPushforwardIso :
    preimageSections f.toLRSHom.toShHom V ≅
      (modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction S.toRingedSpace V) ⋙
        sectionsOverOpen (V : Scheme).toRingedSpace ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom :=
  Functor.isoWhiskerLeft (modulePushforward f.toLRSHom.toShHom)
    (sectionsOnImageTopNatIso S V).symm

/-- **The same crossing, by the direct-image route.** Sections over `f⁻¹V` of a sheaf of
`𝒪_X`-modules are sections over `V` of its direct image; restricting those to the open subscheme
`V` and using [Stacks, Tag 01E5] undervied — `…HigherDirectImage.modulePushforwardRestrictIso`,
the identification of the restriction of a direct image with the direct image along `f ∣_ V` of
the restriction — presents them as the global sections of `(f ∣_ V)_*((-)|_{f⁻¹V})`, which is the
degreewise source of the Leray comparison for `f ∣_ V` over `⊤` after the restriction.

This is the route the `ψ` side of conclusion (c) of [Stacks, Tag 0EX3] presents the crossing in,
where [Stacks, Tag 089W] is met at the restricted morphism; `preimageSectionsOpenSubschemeIso` is
the route the `γ⁺` side presents it in. The two are equal, which is
`preimageSectionsOpenSubschemeIso_eq`. There is no hypothesis on `f`, on `V` or on the module.

The ringed-space restricted morphism is carried to Mathlib's `f ∣_ V` inside
`modulePushforwardMorphismRestrictIso`; the two preimage opens `f ⁻¹ᵁ V` and
`…HigherDirectImage.preimageOpen` agree by `rfl`. -/
def preimageSectionsOpenSubschemePushforwardIso :
    preimageSections f.toLRSHom.toShHom V ≅
      moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
        preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom :=
  preimageSectionsRestrictPushforwardIso f V ≪≫
    Functor.isoWhiskerRight (modulePushforwardMorphismRestrictIso f V).symm
      (sectionsOverOpen (V : Scheme).toRingedSpace ⊤ ⋙
        ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)

/-! ### The two routes are the same transformation -/

/-- **The sections route's inverse is the identity on a local section, up to `HEq`.** The inverse
of `preimageSectionsOpenSubschemeIso` is the restriction map of the sheaf of modules along the
equality `(f⁻¹V).ι ''ᵁ ⊤ = f⁻¹V` of opens of `X`, and restriction along an equality of opens is
the identity up to the transport of the type of sections. Neither the crossing of the two sections
functors nor the identification of the two readings of the scalars contributes anything: the
latter does not move the section at all, and the former is that restriction map. -/
theorem heq_preimageSectionsOpenSubschemeIso_inv_app
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (x : ((moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
      preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
        ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj M)) :
    HEq ((preimageSectionsOpenSubschemeIso f V).inv.app M x) x :=
  heq_val_map_eqToHom M (Scheme.Opens.ι_image_top (f ⁻¹ᵁ V)).symm x

/-- **The direct-image route's inverse is the identity on a local section, up to `HEq`.** Its two
factors are [Stacks, Tag 01E5] undervied, which is the identity on local sections by
`heq_modulePushforwardMorphismRestrictIso_hom_app_val_app`, and the crossing of the two sections
functors at `V`, which is the restriction map of the direct image along `V.ι ''ᵁ ⊤ = V`.

The section the first factor produces is supplied **explicitly** to
`…HigherDirectImage.heq_val_map_eqToHom`: left as a metavariable it is unified by unfolding the
whole route, which exhausts the heartbeat budget. -/
theorem heq_preimageSectionsOpenSubschemePushforwardIso_inv_app
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (x : ((moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
      preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
        ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj M)) :
    HEq ((preimageSectionsOpenSubschemePushforwardIso f V).inv.app M x) x :=
  (heq_val_map_eqToHom ((modulePushforward f.toLRSHom.toShHom).obj M)
      (Scheme.Opens.ι_image_top V).symm
      (((modulePushforwardMorphismRestrictIso f V).hom.app M).val.app (op ⊤) x)).trans
    (heq_modulePushforwardMorphismRestrictIso_hom_app_val_app f V M (op ⊤) x)

/-- **The two routes to the source of the Leray comparison are the same isomorphism.** The
sections route `preimageSectionsOpenSubschemeIso`, which the `γ⁺` side of conclusion (c) of
[Stacks, Tag 0EX3] presents, and the direct-image route
`preimageSectionsOpenSubschemePushforwardIso`, which the `ψ` side presents, agree. There is no
hypothesis on `f` and none on `V`.

Both inverses are restriction maps of the sheaf of modules along an equality of opens of `X`,
hence both are the identity on a local section up to `HEq`; two maps with the same source and the
same target that are both `HEq` the identity are equal. No factor of either route is unfolded.
See this module's implementation notes for why that is the route taken. -/
theorem preimageSectionsOpenSubschemeIso_eq :
    preimageSectionsOpenSubschemeIso f V = preimageSectionsOpenSubschemePushforwardIso f V := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp ?_)
  ext M x
  exact eq_of_heq ((heq_preimageSectionsOpenSubschemeIso_inv_app f V M x).trans
    (heq_preimageSectionsOpenSubschemePushforwardIso_inv_app f V M x).symm)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
