module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CollapseOuterFunctor
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.RestrictionCollapseSquare
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AmbientPrefixJoin
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeDerived
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeDerivedScalars
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeDerivedSectionsImageTop

/-!
# Grothendieck's collapse crossed at the geometric data of [Stacks, Tag 0EX3] (c)

The tail of conclusion (c) of [Stacks, Tag 0EX3] meets Grothendieck's comparison of
[Stacks, Tag 01XK] at **two** pairs: the `γ⁺` side at `(f_*, Γ(V, -))` on the ambient base, by
`…TopDegreeBaseChange.sectionsOverOpenHomologyComparison_comp_map`
`_homologyFunctorDerivedPushforwardIso_hom_eq`, and the `ψ` side at `((f ∣_ V)_*, Γ(V, ⊤, -))` on
the open subscheme, by `…TopDegreeBaseChange.prefix_eq_factorOneFive_comp_rightDerivedCompNatIso`
`_inv`. The three general statements that cross those two readings are available:

* `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square` — the
  collapse at the ambient pair against the collapse on the open subscheme, across
  [Stacks, Tag 01E5] and [Stacks, Tag 01E1];
* `…AffineBase.rightDerivedCompNatIso_natIso_square` — the collapse transported along an
  isomorphism of the outer functor;
* `…AffineBase.rightDerivedCompNatIso_postcomp_square` — the collapse at `G ⋙ R` against `R` of
  the collapse at `G`.

All three are stated at variables of abstract categories, with an arbitrary additive outer
functor `P` out of the modules on the open subspace. This file instantiates them at the geometric
data, at the one choice

> `P = Γ((V : Scheme), ⊤, -) ⋙ res_{topIso V}`

that makes the square's ambient outer functor `(-|_V) ⋙ P` isomorphic to the `γ⁺` side's
`Γ(V, -)`, by the hypothesis-free `…TopDegreeBaseChange.sectionsOnImageTopNatIso`, and its
restricted outer functor `P` the `ψ` side's `Γ(V, ⊤, -)` read through a restriction of scalars.

## Main definitions

* `…TopDegreeBaseChange.sectionsOnOpenSubschemeTop` and
  `…TopDegreeBaseChange.openSubschemeTopSections` — the `ψ` side's outer functor and that `P`,
  with their sources *declared* at the `Stacks.Cohomology.HigherDirectImage.restrictToOpen`
  spelling the squares ask for. The ascriptions are not cosmetic; see the implementation notes.
* `…TopDegreeBaseChange.restrictCompSectionsIso` — the `V.ι ''ᵁ ⊤`-versus-`V` crossing of the
  ambient outer functor: `…TopDegreeBaseChange.sectionsImageTopNatIsoOf`, re-ascribed.
* `…TopDegreeBaseChange.restrictCollapseNatTrans` and
  `…TopDegreeBaseChange.ambientCollapseNatTrans`, with their right derived functors
  `…restrictCollapseTransport` and `…ambientCollapseTransport` — the two derived transports the
  squares hoist, taken canonically.

## Main results

* `…TopDegreeBaseChange.hpl_imageTop_of_isAffineOpen` — the degeneration at the open
  `V.ι ''ᵁ ⊤`, which is `V`.
* `…TopDegreeBaseChange.hamb_openSubschemeTopSections` and
  `…TopDegreeBaseChange.hres_openSubschemeTopSections` — the squares' two pointwise hypotheses,
  from the two degenerations the join's two sides carry.
* `…TopDegreeBaseChange.restrictCollapseTransport_app` and
  `…TopDegreeBaseChange.ambientCollapseTransport_app` — the two transports' readings on the chosen
  injective resolutions, which are the squares' defining hypotheses `hτ` and `hρ`.
* `…TopDegreeBaseChange.collapse_crossing_restrictOuterFunctor` — the postcomposition square and
  the restriction square glued: **the `ψ` side's collapse against the ambient collapse at
  `(-|_V) ⋙ P`.**
* `…TopDegreeBaseChange.ambient_outer_collapse_square` — the natural-isomorphism square at
  `restrictCompSectionsIso` inverted.
* `…TopDegreeBaseChange.collapse_crossing_restrictedMorphism` — **the crossing: the `ψ` side's
  collapse against the collapse at `(f_*, Γ(V, -))` that the `γ⁺` side reads.**

## Implementation notes

*Why `openSubschemeTopSections` is a `def` with an ascribed source.*
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square` asks its
outer functor `P` to be a functor out of
`SheafOfModules (structureSheafRing (restrictToOpen Y V))` and asks `P.Additive`. Written at the
open-subscheme spelling `SheafOfModules (structureSheafRing (V : Scheme).toRingedSpace)` — which
is the same category, by `rfl` — the additivity is found by `infer_instance`; keyed on the
`restrictToOpen` spelling it is **not** synthesised. This is the pitfall described in
`BaseChangeSectionsTail.lean` at a new pair of spellings, and the cure is the one described
there: a `def` whose declared source and target carry the wanted spellings, its instance supplied
by `inferInstanceAs` in term mode, where the conversion runs at default transparency. An
`abbrev` would be unfolded by instance search and land back on the unusable spelling.

*Where the two degenerations come from, and why neither is at `V`.* The square's ambient
hypothesis is the preservation of left homology by `(-|_V) ⋙ P`, and that composite **is**
`Γ(V.ι ''ᵁ ⊤, -) ⋙ res_{topIso V}` by `rfl` — sections over the *image* open, not over `V`. So
the degeneration that feeds it is `…TopDegreeBaseChange.hpl_of_isAffineOpen` at the open
`V.ι ''ᵁ ⊤`, which is an affine open because `AlgebraicGeometry.Scheme.Opens.ι_image_top` says it
*is* `V`; `CategoryTheory.ShortComplex.preservesLeftHomologyOf_comp` then carries it across the
restriction of scalars, which is exact. The restriction of scalars has to be written at the
`structureSheafRing` spelling of its source ring —
`…TopDegreeBaseChange.imageTopRestrictScalarsOf` — or the pointwise hypothesis for it is not
synthesised at the intermediate category the composite names.

*The one transport the restricted hypothesis needs.* The square's restricted hypothesis is at
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism`, while the `ψ` side's degeneration is at
Mathlib's `f ∣_ V`. The two pushforward functors are equal, by
`…SchemeHigherDirectImage.toShHom_morphismRestrict`, but `rw` on that equality leaves a motive
that is not type correct — `CategoryTheory.Functor.mapHomologicalComplex` takes the additivity of
its argument as an instance argument, and the instance that fires at the restricted morphism is
the bespoke `…HigherDirectImage.modulePushforwardRestrictedMorphism_additive`. `simp only`
discharges exactly this, the dependency being on a proof of a `Prop`-valued class; that is the
behaviour `AlgebraicGeometry/ProjectiveCoherentImage/Basic.lean` already describes, and raising
the priority of the generic additivity instance does **not** help.

*Why the crossing is three declarations and not one.* The three squares cannot be applied inside
one declaration: the glued statement elaborates, but the three instantiations together exhaust
200,000 heartbeats, and raising the heartbeat limit is not available here (this holds for every
arrangement, including writing the three hoisted transports' readings out as hypotheses
rather than citing them). So the first two squares are glued in
`collapse_crossing_restrictOuterFunctor`, the third is stated on its own as
`ambient_outer_collapse_square`, and `CategoryTheory.comp_glue_mid_square` joins them. The one
reassociation this costs — `whiskerRight` produces `(f_* ⋙ (-|_V)) ⋙ P` where the square asks for
`f_* ⋙ (-|_V) ⋙ P` — is paid at `restrictCollapseNatTrans`, i.e. before
`CategoryTheory.Functor.rightDerived` is applied; crossing the two afterwards is itself a
200,000-heartbeat `isDefEq` timeout, at either placement.

*No `@[stacks …]` attribute is placed.* These are compatibilities between instantiations of
Grothendieck's collapse, not statements of a tagged result; [Stacks, Tag 01XK] carries its own
where the collapse is built, and conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage (toShHom_morphismRestrict)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ)
  {Dc : Type*} [Category* Dc]
  (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))

/-! ### The outer functor the two sides meet at -/

/-- **Global sections of the open subscheme `V`**, with its source *declared* at the
`Stacks.Cohomology.HigherDirectImage.restrictToOpen` spelling that
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square` and the
pushforward along `…HigherDirectImage.restrictedMorphism` present it at.

This is `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen (V : Scheme).toRingedSpace ⊤`
and nothing else — the `ψ` side's own outer functor; the ascription is forced by instance
synthesis, see this module's implementation notes. It is a `def` and not an `abbrev` on
purpose. -/
def sectionsOnOpenSubschemeTop :
    SheafOfModules.{u} (structureSheafRing (restrictToOpen Y.toSheafedSpace V)) ⥤
      ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)) :=
  sectionsOverOpen (V : Scheme).toRingedSpace ⊤

/-- Global sections of the open subscheme are additive. -/
instance sectionsOnOpenSubschemeTop_additive : (sectionsOnOpenSubschemeTop V).Additive :=
  inferInstanceAs ((sectionsOverOpen (V : Scheme).toRingedSpace ⊤).Additive)

/-- **The outer functor at which the two readings of [Stacks, Tag 01XK] are crossed**: global
sections of the open subscheme `V`, read over `Γ(V, 𝒪_Y)` through
`AlgebraicGeometry.Scheme.Opens.topIso`.

This is `sectionsOnOpenSubschemeTop V ⋙ …TopDegreeBaseChange.baseTopRestrictScalars V` and
nothing else. -/
def openSubschemeTopSections :
    SheafOfModules.{u} (structureSheafRing (restrictToOpen Y.toSheafedSpace V)) ⥤
      ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V)) :=
  sectionsOnOpenSubschemeTop V ⋙ baseTopRestrictScalars V

/-- `openSubschemeTopSections` is additive: both factors are. -/
instance openSubschemeTopSections_additive : (openSubschemeTopSections V).Additive :=
  inferInstanceAs ((sectionsOnOpenSubschemeTop V ⋙ baseTopRestrictScalars V).Additive)

/-- Pushing forward along the restricted morphism and then taking global sections of the open
subscheme is additive. The composite is **not** found by `CategoryTheory.Functor.instAdditiveComp`
at the open-subscheme spelling of the intermediate category, which is why it is declared: see this
module's implementation notes. -/
instance modulePushforwardRestricted_comp_sections_additive :
    (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
      sectionsOnOpenSubschemeTop V).Additive :=
  inferInstance

/-- The same with the restriction of scalars along `topIso V` applied. -/
instance modulePushforwardRestricted_comp_sections_comp_scalars_additive :
    (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
      sectionsOnOpenSubschemeTop V ⋙ baseTopRestrictScalars V).Additive :=
  inferInstanceAs ((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
    openSubschemeTopSections V).Additive)

/-- The restricted pointwise hypothesis at the spelling
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_postcomp_square` produces its outer functor
in — `sectionsOnOpenSubschemeTop V ⋙ baseTopRestrictScalars V` rather than the `def`
`openSubschemeTopSections V` the restriction square is instantiated at. The two functors are the
same, but instance search is keyed on the spelling, so the bridge is declared. -/
instance preservesLeftHomologyOf_sectionsComp
    (S : CategoryTheory.ShortComplex
      (SheafOfModules.{u} (structureSheafRing (restrictToOpen Y.toSheafedSpace V))))
    [(openSubschemeTopSections V).PreservesLeftHomologyOf S] :
    (sectionsOnOpenSubschemeTop V ⋙ baseTopRestrictScalars V).PreservesLeftHomologyOf S :=
  inferInstanceAs ((openSubschemeTopSections V).PreservesLeftHomologyOf S)

/-- **The ambient outer functor of the square is sections over the image open, read over
`Γ(V, 𝒪_Y)`.** Restriction to `V` followed by `openSubschemeTopSections` is
`Γ(V.ι ''ᵁ ⊤, -) ⋙ …TopDegreeBaseChange.imageTopRestrictScalarsOf`, on the nose. -/
theorem moduleRestriction_comp_openSubschemeTopSections :
    moduleRestriction Y.toSheafedSpace V ⋙ openSubschemeTopSections V =
      sectionsOverOpen Y.toSheafedSpace (V.ι ''ᵁ ⊤) ⋙ imageTopRestrictScalarsOf Y V :=
  rfl

/-- **The `V.ι ''ᵁ ⊤`-versus-`V` crossing of the square's ambient outer functor.** The
hypothesis-free `…TopDegreeBaseChange.sectionsImageTopNatIsoOf` at `V` and nothing else — it
typechecks on the nose, so **no comparison of sections functors is owed** — with its source
*declared* as the square's ambient outer functor `(-|_V) ⋙ openSubschemeTopSections V`.

The ascription is not cosmetic, for the reason given in the module documentation:
`CategoryTheory.Functor.whiskerLeft` of the library spelling into the square's is a `whnf` timeout,
the additivity instances
`CategoryTheory.NatTrans.mapHomologicalComplex` needs not being synthesised at the
`imageTopRestrictScalarsOf` spelling of the target. This is the same re-ascription
`sectionsImageTopNatIsoOf` itself is of `…TopDegreeBaseChange.sectionsOnImageTopNatIso`. -/
def restrictCompSectionsIso :
    moduleRestriction Y.toSheafedSpace V ⋙ openSubschemeTopSections V ≅
      sectionsOverOpen Y.toSheafedSpace V :=
  sectionsImageTopNatIsoOf Y V

/-! ### The two pointwise hypotheses, from the degenerations the join's two sides carry -/

section Degeneration

variable [QuasiCompact f] [QuasiSeparated f]

/-- **Grothendieck's pointwise hypothesis at the pair `(f_*, Γ(V.ι ''ᵁ ⊤, -))`.** This is
`…TopDegreeBaseChange.hpl_of_isAffineOpen` at the open `V.ι ''ᵁ ⊤`, which is an affine open
whenever `V` is because `AlgebraicGeometry.Scheme.Opens.ι_image_top` says it **is** `V`.
Nothing is assumed of `Y`. -/
theorem hpl_imageTop_of_isAffineOpen (hV : IsAffineOpen V)
    (hE : ∀ Z : Dc, (E.obj Z).IsQuasicoherent) :
    ∀ Z : Dc, (sectionsOverOpen Y.toSheafedSpace (V.ι ''ᵁ ⊤)).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p) :=
  hpl_of_isAffineOpen f (V.ι ''ᵁ ⊤) p E (by rw [Scheme.Opens.ι_image_top]; exact hV) hE

end Degeneration

/-- **The square's ambient pointwise hypothesis.** The degeneration at the open `V.ι ''ᵁ ⊤`
carried across the exact restriction of scalars by
`CategoryTheory.ShortComplex.preservesLeftHomologyOf_comp`. Nothing is assumed. -/
theorem hamb_openSubschemeTopSections
    (hamb : ∀ Z : Dc, (sectionsOverOpen Y.toSheafedSpace (V.ι ''ᵁ ⊤)).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p)) :
    ∀ Z : Dc, (moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p) := fun Z =>
  have := hamb Z
  ShortComplex.preservesLeftHomologyOf_comp _
    (sectionsOverOpen Y.toSheafedSpace (V.ι ''ᵁ ⊤)) (imageTopRestrictScalarsOf Y V)

/-- **The square's restricted pointwise hypothesis.** The `ψ` side's degeneration at the pair
`((f ∣_ V)_*, Γ(V, ⊤, -))`, carried across the exact restriction of scalars and then transported
along `…SchemeHigherDirectImage.toShHom_morphismRestrict`. Nothing is assumed. -/
theorem hres_openSubschemeTopSections
    (hres : ∀ Z : Dc, (sectionsOverOpen (V : Scheme).toRingedSpace ⊤).PreservesLeftHomologyOf
      ((((modulePushforward (f ∣_ V).toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (injectiveResolution ((openSubschemeRestriction f V).obj (E.obj Z))).cocomplex).sc p)) :
    ∀ Z : Dc, (openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p) := fun Z => by
  simp only [← toShHom_morphismRestrict f V]
  have := hres Z
  exact ShortComplex.preservesLeftHomologyOf_comp
    ((((modulePushforward (f ∣_ V).toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (injectiveResolution ((openSubschemeRestriction f V).obj (E.obj Z))).cocomplex).sc p)
    (sectionsOverOpen (V : Scheme).toRingedSpace ⊤) (baseTopRestrictScalars V)

/-! ### The derived transport the restriction square is applied at -/

/-- **[Stacks, Tag 01E5] undervied, inverted and read under the outer functor**, with its source
and target *declared* at the association
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square` writes them
at.

This is `CategoryTheory.Functor.whiskerRight` of
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso` inverted and nothing else. The
ascription is not cosmetic and it is where the one reassociation of this file is paid:
`whiskerRight` produces `(f_* ⋙ (-|_V)) ⋙ P` while the square asks for `f_* ⋙ (-|_V) ⋙ P`, and
crossing the two **after** `CategoryTheory.Functor.rightDerived` has been applied exhausts 200,000
heartbeats at `isDefEq`, at both placements. At the level of a transformation of
degreewise functors it costs nothing. -/
def restrictCollapseNatTrans :
    modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V ⟶
      moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
          openSubschemeTopSections V :=
  Functor.whiskerRight (modulePushforwardRestrictIso f.toLRSHom.toShHom V).inv
    (openSubschemeTopSections V)

/-- **The derived transport the restriction square is applied at**, at the geometric data: the
`p`-th right derived functor of `restrictCollapseNatTrans`. -/
def restrictCollapseTransport :
    (modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).rightDerived p ⟶
      (moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
          openSubschemeTopSections V).rightDerived p :=
  NatTrans.rightDerived (restrictCollapseNatTrans f V) p

/-- **The reading of `restrictCollapseTransport` on the chosen injective resolution**, which is
the defining hypothesis `hτ` of
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square`. This is
`CategoryTheory.InjectiveResolution.rightDerived_app_eq` and nothing else. -/
theorem restrictCollapseTransport_app
    (M : SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) :
    (restrictCollapseTransport f V p).app M =
      ((injectiveResolution M).isoRightDerivedObj
          (modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
            openSubschemeTopSections V) p).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map
          (((restrictCollapseNatTrans f V).mapHomologicalComplex
            (ComplexShape.up ℕ)).app (injectiveResolution M).cocomplex) ≫
          ((injectiveResolution M).isoRightDerivedObj
            (moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
              modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
                openSubschemeTopSections V) p).inv :=
  InjectiveResolution.rightDerived_app_eq (restrictCollapseNatTrans f V)
    (injectiveResolution M) p

/-- **The crossing of the two readings of the ambient outer functor**, as a transformation of
degreewise functors: `…TopDegreeBaseChange.restrictCompSectionsIso` inverted, whiskered by the
ambient direct image. Declared for the same reason `restrictCollapseNatTrans` is. -/
def ambientCollapseNatTrans :
    modulePushforward f.toLRSHom.toShHom ⋙ sectionsOverOpen Y.toSheafedSpace V ⟶
      modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V :=
  Functor.whiskerLeft (modulePushforward f.toLRSHom.toShHom) (restrictCompSectionsIso V).inv

/-- **The derived transport the natural-isomorphism square is applied at**: the `p`-th right
derived functor of `ambientCollapseNatTrans`. -/
def ambientCollapseTransport :
    (modulePushforward f.toLRSHom.toShHom ⋙
        sectionsOverOpen Y.toSheafedSpace V).rightDerived p ⟶
      (modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).rightDerived p :=
  NatTrans.rightDerived (ambientCollapseNatTrans f V) p

/-- **The reading of `ambientCollapseTransport` on the chosen injective resolution**, which is the
defining hypothesis `hρ` of
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_natIso_square`. This is
`CategoryTheory.InjectiveResolution.rightDerived_app_eq` and nothing else. -/
theorem ambientCollapseTransport_app
    (M : SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) :
    (ambientCollapseTransport f V p).app M =
      ((injectiveResolution M).isoRightDerivedObj
          (modulePushforward f.toLRSHom.toShHom ⋙
            sectionsOverOpen Y.toSheafedSpace V) p).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map
          (((ambientCollapseNatTrans f V).mapHomologicalComplex
            (ComplexShape.up ℕ)).app (injectiveResolution M).cocomplex) ≫
          ((injectiveResolution M).isoRightDerivedObj
            (modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
              openSubschemeTopSections V) p).inv :=
  InjectiveResolution.rightDerived_app_eq (ambientCollapseNatTrans f V)
    (injectiveResolution M) p

/-! ### The crossing of the two readings of [Stacks, Tag 01XK] -/

/-- **The `ψ` side's reading of [Stacks, Tag 01XK] against the ambient collapse at the outer
functor the restriction square carries.** For a morphism of schemes `f : X ⟶ Y`, an open `V ⊆ Y`,
a functor `E : Dc ⥤ Mod(𝒪_X)`, a degree `p` and an object `Z`, the composite

> the restriction of scalars along `topIso V` applied to Grothendieck's comparison at the pair
> `((f ∣ V)_*, Γ(V, ⊤, -))` on the open subscheme — the collapse the `ψ` side reads — then the
> comparison that moves that restriction of scalars inside, then [Stacks, Tag 01E1]'s source edge
> inverted

is

> [Stacks, Tag 01E5] under `openSubschemeTopSections`, Grothendieck's comparison at the pair
> `(f_*, (-|_V) ⋙ openSubschemeTopSections V)`, and `restrictCollapseTransport`.

`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_postcomp_square` at the pair
`(Γ(V, ⊤, -), res_{topIso V})` and `…AffineBase`
`.rightDerivedCompNatIso_restrictChosenResolution_square` at `P = openSubschemeTopSections V`,
glued by `CategoryTheory.comp_glue_two_squares`. Both transports are canonical: the first is
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at the identity comparison, whose `hσ` is
`…AffineBase.rightDerivedCompIso_refl_hom_app_mapHomologyIso`, and the second is
`restrictCollapseTransport`, whose `hτ` is `restrictCollapseTransport_app`.

**Nothing is assumed** of `f`, of `V`, of `E`, of `Z` or of `p` beyond the two pointwise homology
hypotheses the two collapses carry; `hamb` is supplied by `hamb_openSubschemeTopSections` and
`hres` by `hres_openSubschemeTopSections`. The restricted morphism is
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism`, the spelling the squares are stated at;
`…SchemeHigherDirectImage.toShHom_morphismRestrict` identifies it with Mathlib's `f ∣_ V` and that
transport is not performed here. -/
theorem collapse_crossing_restrictOuterFunctor
    (hamb : ∀ Z : Dc, (moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p))
    (hG : ∀ Z : Dc, (sectionsOnOpenSubschemeTop V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p))
    (hres : ∀ Z : Dc, (openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p))
    (Z : Dc)
    [(moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p)]
    [(sectionsOnOpenSubschemeTop V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p)]
    [(openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p)] :
    (baseTopRestrictScalars V).map
          ((rightDerivedCompNatIso (E ⋙ moduleRestriction X.toSheafedSpace
              (preimageOpen f.toLRSHom.toShHom V))
            (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V))
            (sectionsOnOpenSubschemeTop V) p hG).hom.app Z) ≫
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
            (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
              sectionsOnOpenSubschemeTop V) (baseTopRestrictScalars V)
            (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
              sectionsOnOpenSubschemeTop V ⋙
                baseTopRestrictScalars V) (Iso.refl _) p).hom.app
          ((E ⋙ moduleRestriction X.toSheafedSpace
            (preimageOpen f.toLRSHom.toShHom V)).obj Z) ≫
          (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
            (moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V))
            (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
              openSubschemeTopSections V) p).inv.app (E.obj Z) =
      (openSubschemeTopSections V).map
          ((higherDirectImageRestrictIso f.toLRSHom.toShHom V p).hom.app (E.obj Z)) ≫
        (rightDerivedCompNatIso E (modulePushforward f.toLRSHom.toShHom)
            (moduleRestriction Y.toSheafedSpace V ⋙
              openSubschemeTopSections V) p hamb).hom.app Z ≫
          (restrictCollapseTransport f V p).app (E.obj Z) :=
  comp_glue_two_squares
    (rightDerivedCompNatIso_postcomp_square
      (E ⋙ moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V))
      (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V))
      (sectionsOnOpenSubschemeTop V) p (baseTopRestrictScalars V) hG hres _ Z
      (rightDerivedCompIso_refl_hom_app_mapHomologyIso
        (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V))
        (sectionsOnOpenSubschemeTop V) p (baseTopRestrictScalars V) _))
    (rightDerivedCompNatIso_restrictChosenResolution_square f.toLRSHom.toShHom V E
      (openSubschemeTopSections V) p hamb hres (restrictCollapseTransport f V p) Z
      (restrictCollapseTransport_app f V p (E.obj Z)))

/-- **The ambient collapse at the restriction square's outer functor against the one the `γ⁺`
side reads.** `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_natIso_square` at
`…TopDegreeBaseChange.restrictCompSectionsIso V` inverted, with its transport taken to be
`ambientCollapseTransport` and its `hρ` to be `ambientCollapseTransport_app`. Nothing is assumed
beyond the two collapses' own pointwise hypotheses. -/
theorem ambient_outer_collapse_square
    (hpl : ∀ Z : Dc, (sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p))
    (hamb : ∀ Z : Dc, (moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p))
    (Z : Dc)
    [(sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p)]
    [(moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p)] :
    (rightDerivedCompNatIso E (modulePushforward f.toLRSHom.toShHom)
          (sectionsOverOpen Y.toSheafedSpace V) p hpl).hom.app Z ≫
        (ambientCollapseTransport f V p).app (E.obj Z) =
      (restrictCompSectionsIso V).inv.app
          (((modulePushforward f.toLRSHom.toShHom).rightDerived p).obj (E.obj Z)) ≫
        (rightDerivedCompNatIso E (modulePushforward f.toLRSHom.toShHom)
          (moduleRestriction Y.toSheafedSpace V ⋙
            openSubschemeTopSections V) p hamb).hom.app Z :=
  rightDerivedCompNatIso_natIso_square (modulePushforward f.toLRSHom.toShHom)
    (sectionsOverOpen Y.toSheafedSpace V) p
    (moduleRestriction Y.toSheafedSpace V ⋙ openSubschemeTopSections V)
    (E := E) (restrictCompSectionsIso V).symm hpl hamb (ambientCollapseTransport f V p) Z
    (ambientCollapseTransport_app f V p (E.obj Z))

/-- **The `γ⁺` side's reading of [Stacks, Tag 01XK] against the `ψ` side's, at the geometric data
of conclusion (c) of [Stacks, Tag 0EX3].** `collapse_crossing_restrictOuterFunctor` with its
ambient collapse carried to the pair `(f_*, Γ(V, -))` the `γ⁺` side reads, by
`ambient_outer_collapse_square`; the two are joined by `CategoryTheory.comp_glue_mid_square`.

So the left-hand side is the collapse the `ψ` side of conclusion (c) arrives in, through
`…TopDegreeBaseChange.prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` at
`((f ∣_ V), ⊤)`, and the right-hand side carries the collapse the `γ⁺` side arrives in, through
`…TopDegreeBaseChange.sectionsOverOpenHomologyComparison_comp_map`
`_homologyFunctorDerivedPushforwardIso_hom_eq` at `(f, V)`.

**Nothing is assumed** of `f`, of `V`, of `E`, of `Z` or of `p` beyond the three pointwise
homology hypotheses the three collapses carry. The restricted morphism is
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism`; the transport to Mathlib's `f ∣_ V`
along `…SchemeHigherDirectImage.toShHom_morphismRestrict`, and the two sides' remaining factors,
are not performed here. -/
theorem collapse_crossing_restrictedMorphism
    (hpl : ∀ Z : Dc, (sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p))
    (hamb : ∀ Z : Dc, (moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p))
    (hG : ∀ Z : Dc, (sectionsOnOpenSubschemeTop V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p))
    (hres : ∀ Z : Dc, (openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p))
    (Z : Dc)
    [(sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p)]
    [(moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p)]
    [(sectionsOnOpenSubschemeTop V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p)]
    [(openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p)] :
    (baseTopRestrictScalars V).map
          ((rightDerivedCompNatIso (E ⋙ moduleRestriction X.toSheafedSpace
              (preimageOpen f.toLRSHom.toShHom V))
            (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V))
            (sectionsOnOpenSubschemeTop V) p hG).hom.app Z) ≫
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
            (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
              sectionsOnOpenSubschemeTop V) (baseTopRestrictScalars V)
            (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
              sectionsOnOpenSubschemeTop V ⋙
                baseTopRestrictScalars V) (Iso.refl _) p).hom.app
          ((E ⋙ moduleRestriction X.toSheafedSpace
            (preimageOpen f.toLRSHom.toShHom V)).obj Z) ≫
          (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
            (moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V))
            (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) ⋙
              openSubschemeTopSections V) p).inv.app (E.obj Z) =
      (openSubschemeTopSections V).map
          ((higherDirectImageRestrictIso f.toLRSHom.toShHom V p).hom.app (E.obj Z)) ≫
        (restrictCompSectionsIso V).hom.app
            (((modulePushforward f.toLRSHom.toShHom).rightDerived p).obj (E.obj Z)) ≫
          (rightDerivedCompNatIso E (modulePushforward f.toLRSHom.toShHom)
              (sectionsOverOpen Y.toSheafedSpace V) p hpl).hom.app Z ≫
            (ambientCollapseTransport f V p).app (E.obj Z) ≫
              (restrictCollapseTransport f V p).app (E.obj Z) :=
  comp_glue_mid_square
    (collapse_crossing_restrictOuterFunctor f V p E hamb hG hres Z)
    (ambient_outer_collapse_square f V p E hpl hamb Z)
    ((restrictCompSectionsIso V).hom_inv_id_app _)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
