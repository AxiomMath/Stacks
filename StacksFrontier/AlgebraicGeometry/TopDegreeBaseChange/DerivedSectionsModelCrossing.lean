module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.SchemeOpenSectionsDerived
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictOpenSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections

/-!
# The two models of derived sections over an open, identified

Let `X` be a scheme, `U ⊆ X` an open and `F` a sheaf of `𝒪_X`-modules. The cohomology of `F`
"over `U`" is written in this development in two unrelated ways.

*The ringed-space model.* `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen`
is the unbounded total right derived functor of `Γ(U, -)` on sheaves of modules over the ringed
space `X`, computed by K-injective resolutions, and the cohomology in question is the degree-`n`
term of its value at `F` placed in degree `0`. This is the model [Stacks, Tag 0D5W] and the
degeneration of `TopDegreeDerivedSections.lean` are stated in.

*The scheme model.* `((moduleGlobalSections (U : Scheme)).rightDerived n).obj (F|_U)` is the
classical `ℕ`-indexed right derived functor, computed by injective resolutions, of global
sections on the open subscheme `U`, applied to the restriction of `F`. This is the model
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineOpenCohomology`,
`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` and
`…TopDegreeBaseChange.cohomologyPullbackIsoPushforward` are stated in, and so it is the model in
which [Stacks, Tag 01XK] is available.

The two are identified here. The first is a module over `Γ(X, U)` and the second over `Γ(U, ⊤)`;
the comparison of those two rings is `AlgebraicGeometry.Scheme.Opens.topIso`, and the second
side is read over `Γ(X, U)` by restriction of scalars along its inverse, exactly as
`affineOpenCohomology` and `AlgebraicGeometry.openSectionsModuleIso` do.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSectionsImageTopIso` — sections of `F` over
  `U.ι ''ᵁ ⊤`, read over `Γ(X, U)`, are the sections of `F` over `U`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.sectionsOnImageTopNatIso` — the same comparison
  as an isomorphism of functors `X.Modules ⥤ ModuleCat Γ(X, U)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.sectionsOnImageTopDerivedIso` — that comparison
  after deriving, obtained because restriction of scalars is exact.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.sectionsOnRightDerivedRestrictIso` — **the
  comparison of the classical derived functors**, `R^n Γ(U, -) ≅ H^n(U, (-)|_U)` over `Γ(X, U)`,
  as an isomorphism of functors `X.Modules ⥤ ModuleCat Γ(X, U)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedSectionsOverOpenRightDerivedIso` — the
  degree-`n` term of the unbounded total right derived functor of `Γ(U, -)` at `F` placed in
  degree `0` is the classical `R^n Γ(U, F)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedSectionsOverOpenHomologyIso` — **the
  bridge**: the degree-`n` term of the ringed-space model at `F[0]` is the scheme model
  `H^n(U, F|_U)`, over `Γ(X, U)`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSectionsImageTopIso_hom_apply` — the
  underived comparison is the restriction map of `F` along the equality `U.ι ''ᵁ ⊤ = U` of opens,
  which is what makes it usable on elements.

## Implementation notes

*The three steps.* The scheme model is reached from the classical right derived functor of
`Γ(U, -)` on sheaves of modules over the ambient `X` by
`Stacks.Cohomology.SchemeOpenSections.derivedEvaluationRestrictIso`, which is [Stacks, Tag 01E1]
(2) for the open immersion `U ⟶ X`; that statement is at the open `U.ι ''ᵁ ⊤`, whose ring of
functions is definitionally `Γ(U, ⊤)`. Moving it to the open `U`, whose ring of functions is
`Γ(X, U)`, is `sectionsOnImageTopDerivedIso`, which is
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` — an exact functor commutes with right
derived functors — applied to `sectionsOnImageTopNatIso`. Crossing from the unbounded model to
the classical one is `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`, which needs
nothing of `U` or of `F`.

*What is natural in `F` and what is stated at an object.*
`sectionsOnRightDerivedRestrictIso` is an isomorphism of functors, so the whole passage between
the two classical spellings — the restriction to the open subscheme, the change of ring and the
degree — is natural in `F`. The crossing of the two models,
`derivedSectionsOverOpenRightDerivedIso`, is the value at `F` of
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`, which is supplied for one object at
a time; `derivedSectionsOverOpenHomologyIso` is therefore stated at an object as well.

*Two spellings of one ring, and why the inner comparison names the restriction map.* `Γ(U, ⊤)`
and `Γ(X, U.ι ''ᵁ ⊤)` are equal by `rfl`
(`AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_obj`), and `(Scheme.Opens.topIso U).inv` is
by `rfl` the restriction map `X.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U)).op`. The two
spellings are therefore interchangeable for the kernel, but instance synthesis does not unfold
`AlgebraicGeometry.Scheme.Opens.toScheme`, so the additivity and exactness of the restriction of
scalars are found only at the second spelling. `sectionsOnImageTopDerivedIso` consequently names
the restriction map in its proof while stating `Scheme.Opens.topIso` in its type, which is the
spelling `affineOpenCohomology` and `openSectionsModuleIso` use.

*Two spellings of the category of modules on a scheme.* `X.Modules` and
`SheafOfModules (structureSheafRing X.toRingedSpace)` are `rfl`-equal types whose `Category` and
`Abelian` instances are different terms, the discipline recorded in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedModelCrossing.lean`. The classical
right derived functors of the two spellings of `Γ(U, -)` agree on the nose, because the
instances that enter them — `EnoughInjectives` above all — are found by unfolding
`structureSheafRing`, which carries `@[instance_reducible]`. So
`derivedSectionsOverOpenRightDerivedIso` is stated at the ringed-space spelling, where the
unbounded functor lives, and its value is read at the scheme spelling with no transport.

*No `@[stacks …]` attribute is placed.* What is here is the dictionary between the two models
that conclusion (c) of [Stacks, Tag 0EX3] needs in order to meet [Stacks, Tag 01XK]; the
covering sets of those tags are discussed in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedPullbackTopDegree.lean` and in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/AffineOpenSectionsCohomology.lean`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedSectionsOverOpen derivedSectionsOverOpenUnit sectionsOverOpen)
open Stacks.Cohomology.ModuleComparison (rightDerivedCompIso)
open Stacks.Cohomology.SchemeOpenSections (derivedEvaluationRestrictIso)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) (U : X.Opens)

/-! ### Sections over `U` and sections over the image of the whole open subscheme -/

/-- **The restriction map along `U.ι ''ᵁ ⊤ = U`, as a `Γ(X, U)`-linear map.** Sections of `F`
over the image `U.ι ''ᵁ ⊤` of the whole open subscheme restrict to sections over `U`, and the
restriction is linear once the source is read over `Γ(X, U)` by restriction of scalars along
`(Scheme.Opens.topIso U).inv`: the scalar crosses by `AlgebraicGeometry.Scheme.Modules.map_smul`,
and `AlgebraicGeometry.topIso_hom_inv_apply` returns it unchanged. -/
def openSectionsImageTopLinearMap (M : X.Modules) :
    ((AlgebraicGeometry.sectionsOn X (U.ι ''ᵁ ⊤) ⋙
        ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom).obj M) →ₗ[Γ(X, U)]
      ((AlgebraicGeometry.sectionsOn X U).obj M) where
  toFun := ConcreteCategory.hom
    (M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op)
  map_add' a b := map_add _ a b
  map_smul' r x := by
    refine (Scheme.Modules.map_smul M (eqToHom (Scheme.Opens.ι_image_top U).symm)
      ((Scheme.Opens.topIso U).inv r) x).trans ?_
    rw [show ConcreteCategory.hom
        (X.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op)
          ((Scheme.Opens.topIso U).inv r) = r from topIso_hom_inv_apply U r]
    rfl

/-- **Sections over `U.ι ''ᵁ ⊤` are sections over `U`.** The restriction map of
`openSectionsImageTopLinearMap` is bijective, being the image under `F.presheaf` of an
isomorphism of opens, so it is an isomorphism of `Γ(X, U)`-modules. -/
def openSectionsImageTopIso (M : X.Modules) :
    (AlgebraicGeometry.sectionsOn X (U.ι ''ᵁ ⊤) ⋙
        ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom).obj M ≅
      (AlgebraicGeometry.sectionsOn X U).obj M :=
  LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (openSectionsImageTopLinearMap X U M)
      (ConcreteCategory.bijective_of_isIso
        (M.presheaf.mapIso (eqToIso (Scheme.Opens.ι_image_top U).symm).op).hom))

/-- The comparison `openSectionsImageTopIso` is the restriction map of `F` along the equality
`U.ι ''ᵁ ⊤ = U` of opens and nothing besides. -/
theorem openSectionsImageTopIso_hom_apply (M : X.Modules)
    (x : (AlgebraicGeometry.sectionsOn X (U.ι ''ᵁ ⊤) ⋙
      ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom).obj M) :
    (openSectionsImageTopIso X U M).hom x =
      M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op x :=
  rfl

/-- **The comparison of the two underived sections functors.** Sections over `U.ι ''ᵁ ⊤` read
over `Γ(X, U)` and sections over `U` agree as functors `X.Modules ⥤ ModuleCat Γ(X, U)`;
naturality is naturality of the underlying map of abelian presheaves. -/
def sectionsOnImageTopNatIso :
    AlgebraicGeometry.sectionsOn X (U.ι ''ᵁ ⊤) ⋙
        ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom ≅
      AlgebraicGeometry.sectionsOn X U :=
  NatIso.ofComponents (fun M => openSectionsImageTopIso X U M) (fun {_ N} φ => by
    ext x
    exact (ConcreteCategory.congr_hom
      ((Scheme.Modules.Hom.mapPresheaf φ).naturality
        (eqToHom (Scheme.Opens.ι_image_top U).symm).op) x).symm)

/-! ### The comparison of the classical derived functors -/

/-- **`sectionsOnImageTopNatIso` after deriving.** Deriving sections over `U.ι ''ᵁ ⊤` and then
reading the result over `Γ(X, U)` agrees with deriving sections over `U`, naturally in the sheaf
of modules. Restriction of scalars is exact, so this is
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at `sectionsOnImageTopNatIso`.

The restriction of scalars is named in the proof by the restriction map of `𝒪_X`, which is
`(Scheme.Opens.topIso U).inv` by `rfl`; see this module's implementation notes. -/
def sectionsOnImageTopDerivedIso (n : ℕ) :
    (AlgebraicGeometry.sectionsOn X (U.ι ''ᵁ ⊤)).rightDerived n ⋙
        ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom ≅
      (AlgebraicGeometry.sectionsOn X U).rightDerived n :=
  rightDerivedCompIso (AlgebraicGeometry.sectionsOn X (U.ι ''ᵁ ⊤))
    (ModuleCat.restrictScalars (X.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U)).op).hom)
    (AlgebraicGeometry.sectionsOn X U) (sectionsOnImageTopNatIso X U) n

/-- **The classical derived functors of the two models agree.** For an open `U` of a scheme `X`,
the degree-`n` right derived functor of sections over `U` on sheaves of `𝒪_X`-modules is the
degree-`n` cohomology of the restriction to the open subscheme `U`, read over `Γ(X, U)` by
restriction of scalars along `(Scheme.Opens.topIso U).inv`. This is an isomorphism of functors,
so it is natural in the sheaf of modules.

It is [Stacks, Tag 01E1] (2) in the form
`Stacks.Cohomology.SchemeOpenSections.derivedEvaluationRestrictIso`, whose open is `U.ι ''ᵁ ⊤`,
followed by `sectionsOnImageTopDerivedIso`, which moves the open to `U` and the ring of scalars
to `Γ(X, U)`. -/
def sectionsOnRightDerivedRestrictIso (n : ℕ) :
    (AlgebraicGeometry.sectionsOn X U).rightDerived n ≅
      Scheme.Modules.restrictFunctor U.ι ⋙
        ((Stacks.Cohomology.AffineBase.moduleGlobalSections U.toScheme).rightDerived n ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom) :=
  (sectionsOnImageTopDerivedIso X U n).symm ≪≫
    Functor.isoWhiskerRight (derivedEvaluationRestrictIso X U n)
      (ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom)

/-! ### Crossing the unbounded model and the classical one -/

/-- **The unbounded model computes the classical right derived functor.** For a sheaf of
`𝒪_X`-modules `F` placed in degree `0`, the degree-`n` term of the unbounded total right derived
functor of `Γ(U, -)` is the classical `R^n Γ(U, F)`, as `Γ(X, U)`-modules.

This is `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso` at the functor
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen`, whose unbounded right derived functor
together with its unit is `derivedSectionsOverOpen`; the K-injective resolutions it asks for are
[Stacks, Tag 079P], in the form
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective`. No hypothesis
on `U` or on `F` enters. -/
def derivedSectionsOverOpenRightDerivedIso (F : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op U))) (n : ℤ)).obj
        ((derivedSectionsOverOpen X.toRingedSpace U).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) ≅
      ((sectionsOverOpen X.toRingedSpace U).rightDerived n).obj F :=
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (sectionsOverOpen X.toRingedSpace U)
    (derivedSectionsOverOpen X.toRingedSpace U) (derivedSectionsOverOpenUnit X.toRingedSpace U)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective _) F n

/-- **The bridge between the two models of derived sections over an open.** For a scheme `X`, an
open `U ⊆ X`, a sheaf of `𝒪_X`-modules `F` and a degree `n`, the degree-`n` term of the unbounded
total right derived functor of `Γ(U, -)` at `F` placed in degree `0` is the degree-`n` cohomology
of the restriction of `F` to the open subscheme `U`:

> `H^n(RΓ(U, F[0])) ≅ H^n(U, F|_U)`,

both read as modules over `Γ(X, U)`, the right-hand side by restriction of scalars along
`(Scheme.Opens.topIso U).inv`. There is no hypothesis on `X`, on `U` or on `F`.

The left-hand side is the spelling of [Stacks, Tag 0D5W] and of
`…TopDegreeBaseChange.topDegreeDerivedSectionsIso`; the right-hand side is the spelling of
`…TopDegreeBaseChange.affineOpenCohomology` and of [Stacks, Tag 01XK]. The passage between the
two classical spellings, `sectionsOnRightDerivedRestrictIso`, is an isomorphism of functors, so
that half is natural in `F`. -/
def derivedSectionsOverOpenHomologyIso (F : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op U))) (n : ℤ)).obj
        ((derivedSectionsOverOpen X.toRingedSpace U).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) ≅
      (ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections U.toScheme).rightDerived n).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj F)) :=
  derivedSectionsOverOpenRightDerivedIso X U F n ≪≫
    (sectionsOnRightDerivedRestrictIso X U n).app F

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
