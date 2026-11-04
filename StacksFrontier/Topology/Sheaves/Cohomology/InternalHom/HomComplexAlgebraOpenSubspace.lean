module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraOpenSubspace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionAlgebraSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionAlgebraSliceRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProductSite

/-!
# The graded algebra of a slice site, read on the open subspace

Let `X` be a ringed space and `U` an open of it. The local-to-global step of
[Stacks, Tag 0BQY] runs on the **slice site** `Opens X / U`, over which
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop` is stated, while a
statement proved by restricting the ringed space to `U` lives on the **open subspace**
`X.restrict U`. `Stacks.SheafOfModules.openSubspaceGradedAlgebra` transports a sheaf of graded
algebras from the first presentation to the second, and
`Stacks.SheafOfModules.isIso_openSubspaceUnitalHom_app_iff` makes degreewise invertibility the
same assertion on both. What was still missing, and is supplied here, is that the transported
algebra is the right one: the graded algebra of the cohomology sheaves of `SheafHom^•(P, P)`
read off the slice site **is** the graded algebra of the cohomology sheaves of the internal Hom
complex formed on `X.restrict U`.

That identification is not formal. Sections of
`AlgebraicGeometry.RingedSite.sheafHomComplex` over an object are morphisms on the slice at that
object, so the comparison of the two internal Hom complexes is the **nested** slice equivalence
applied to internal Homs. It is
`AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso`, the internal Hom complex of an
equivalence of ringed sites, instantiated at `TopologicalSpace.Opens.overEquivalence`; the
graded-algebra statement built on it is
`AlgebraicGeometry.RingedSite.homologyGradedAlgebraSiteEquivHomOfIso`.

## Main definitions

* `Stacks.SheafOfModules.openSubspacePhi`: the structure map of
  `Stacks.SheafOfModules.openSubspaceEquiv`, read as the structure map of an equivalence of
  ringed sites. It is `Stacks.SheafOfModules.openSubspaceStructureMap`, the identity.
* `Stacks.SheafOfModules.sheafHomComplexOpenSubspaceIso`: **the chain-level comparison**, the
  internal Hom complex of the slice site read on the open subspace.
* `Stacks.SheafOfModules.openSubspaceHomologyGradedAlgebraHom`: **the graded-algebra
  identification**, for a complex given on the slice site.
* `Stacks.SheafOfModules.openSubspaceHomologyGradedAlgebraOfSpaceHom`: **the identification the
  gluing needs**, for a complex given on `X` itself: the graded algebra of `X` restricted to the
  slice site over `U` and read on the open subspace is the graded algebra of the restricted
  complex on `X.restrict U`.

## Main results

* `Stacks.SheafOfModules.sheafHomComplexOpenSubspaceIso_natural`: the chain-level comparison is
  natural in both variables.
* `Stacks.SheafOfModules.openSubspaceGradedAlgebra_eq_sitePushforward`: the transport of
  `GradedAlgebraOpenSubspace` is the site-level pushforward along `openSubspacePhi`, by
  definition, so the two spellings of the source of the identification agree.
* `Stacks.SheafOfModules.isIso_openSubspaceHomologyGradedAlgebraHom_app` and
  `Stacks.SheafOfModules.isIso_openSubspaceHomologyGradedAlgebraOfSpaceHom_app`: every degree of
  each identification is an isomorphism.

## Implementation notes

The equivalence of ringed sites is `TopologicalSpace.Opens.overEquivalence U` read backwards,
`Opens ↥U ≌ Opens X / U`, which is `Stacks.SheafOfModules.openSubspaceSiteFunctor`; its
structure map is the **identity**, the structure sheaf of the open subspace being by definition
the pushforward of the slice structure sheaf. So `openSubspacePhi` is
`openSubspaceStructureMap` and its invertibility is immediate, and the general machinery — which
needs an equivalence of sites together with an invertible structure map — applies at once.

Everything is spelled on the side of the **ringed sites**, with
`((ringedSite X.sheaf).over U).ringSheaf` rather than `(structureSheafRing X).over U` and with
`AlgebraicGeometry.RingedSite.pushComplex` rather than `(openSubspaceEquiv U).functor`. The two
spellings of each are definitionally equal, and `pushforward_openSubspacePhi` and
`openSubspaceGradedAlgebra_eq_sitePushforward` record that; but a statement written in the
ringed-space spelling and then unified against the ringed-site lemma it is proved by exhausts
the heartbeat budget, while the site spelling matches syntactically and elaborates at once.

The two continuity instances are supplied by `inferInstanceAs`, as in
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/SheafHomSchemeOpenModel.lean`: Mathlib has
them for `Opens.grothendieckTopology ↥U` and `(Opens.grothendieckTopology ↥X).over U` and for
`overEquivalence.functor`/`inverse`, whereas the specialization needs them for the two ringed
sites and for `overEquivalence.symm`. They are also reintroduced with `letI` in each body, and
the invertibility of the structure map is passed as the named argument `hφ`, because the two
interchangeable `Category` instances of `CategoryTheory.Sheaf` keep synthesis from finding
either at a use site — the device of `SheafHomSchemeOpenModel` for the same obstruction. For the
same reason the two invertibility hypotheses of
`isIso_openSubspaceHomologyGradedAlgebraOfSpaceHom_app` are composed by hand rather than by
`infer_instance`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

namespace Stacks.SheafOfModules

universe u

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- Passing from an open of `U` to the corresponding object of `Opens X / U` is continuous, in
the spelling of the two ringed sites. -/
instance openSubspaceEquivalenceFunctorIsContinuous :
    U.overEquivalence.symm.functor.IsContinuous
      (ringedSite (openSubspace U).sheaf).J ((ringedSite X.sheaf).over U).J :=
  inferInstanceAs (U.overEquivalence.inverse.IsContinuous
    (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X.carrier).over U))

/-- Passing from an object of `Opens X / U` to the corresponding open of `U` is continuous, in
the spelling of the two ringed sites. -/
instance openSubspaceEquivalenceInverseIsContinuous :
    U.overEquivalence.symm.inverse.IsContinuous
      ((ringedSite X.sheaf).over U).J (ringedSite (openSubspace U).sheaf).J :=
  inferInstanceAs (U.overEquivalence.functor.IsContinuous
    ((Opens.grothendieckTopology X.carrier).over U) (Opens.grothendieckTopology ↥U))

/-- The structure map of `Stacks.SheafOfModules.openSubspaceEquiv`, read as the structure map of
an equivalence of ringed sites. It is `Stacks.SheafOfModules.openSubspaceStructureMap`, the
identity. -/
abbrev openSubspacePhi :
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite (openSubspace U).sheaf).O) ⟶
      (U.overEquivalence.symm.functor.sheafPushforwardContinuous RingCat.{u}
        (ringedSite (openSubspace U).sheaf).J ((ringedSite X.sheaf).over U).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite X.sheaf).over U).O) :=
  openSubspaceStructureMap U

/-- The structure map of the open subspace is invertible: it is an identity. -/
instance isIso_openSubspacePhi : IsIso (openSubspacePhi U) :=
  inferInstanceAs (IsIso (𝟙 _))

/-- The pushforward along the structure map is the forward functor of
`Stacks.SheafOfModules.openSubspaceEquiv`. -/
theorem pushforward_openSubspacePhi :
    _root_.SheafOfModules.pushforward.{u} (openSubspacePhi U) = (openSubspaceEquiv U).functor :=
  rfl

/-- Transport of complexes of modules off the slice site onto the open subspace. -/
abbrev openSubspacePushComplex :
    CochainComplex (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite X.sheaf).over U).O)) ℤ ⥤
      CochainComplex
        (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite (openSubspace U).sheaf).O)) ℤ :=
  letI := openSubspaceEquivalenceFunctorIsContinuous U
  letI := openSubspaceEquivalenceInverseIsContinuous U
  RingedSite.pushComplex U.overEquivalence.symm (openSubspacePhi U)

/-- The transport of complexes is the degreewise image under
`Stacks.SheafOfModules.openSubspaceEquiv`. -/
theorem openSubspacePushComplex_eq :
    openSubspacePushComplex U =
      ((openSubspaceEquiv U).functor).mapHomologicalComplex (ComplexShape.up ℤ) :=
  rfl

/-- **The internal Hom complex of the slice site, read on the open subspace.** For complexes
`A`, `B` of modules on the slice site `Opens X / U`, the image under
`Stacks.SheafOfModules.openSubspaceEquiv` of their internal Hom complex there is the internal
Hom complex, on the ringed site of the open subspace `X.restrict U`, of their images.

This is the nested slice equivalence applied to internal Homs: a section of the left-hand side
over an open `W` of `U` is a morphism on the slice of `Opens X / U` at the object corresponding
to `W`, while a section of the right-hand side is a morphism on the slice of `Opens ↥U` at
`W`. -/
def sheafHomComplexOpenSubspaceIso
    (A B : CochainComplex
      (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite X.sheaf).over U).O)) ℤ) :
    (openSubspacePushComplex U).obj
        (RingedSite.sheafHomComplex ((ringedSite X.sheaf).over U) A B).obj ≅
      (RingedSite.sheafHomComplex (ringedSite (openSubspace U).sheaf)
        ((openSubspacePushComplex U).obj A) ((openSubspacePushComplex U).obj B)).obj :=
  letI := openSubspaceEquivalenceFunctorIsContinuous U
  letI := openSubspaceEquivalenceInverseIsContinuous U
  RingedSite.siteEquivSheafHomComplexIsoOfIso
    (X := (ringedSite X.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
    U.overEquivalence.symm (openSubspacePhi U) (hφ := isIso_openSubspacePhi U) A B

/-- The chain-level comparison is natural in both variables: it intertwines the maps
`AlgebraicGeometry.RingedSite.homMap` of internal Hom complexes. -/
theorem sheafHomComplexOpenSubspaceIso_natural
    {A A' B B' : CochainComplex
      (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite X.sheaf).over U).O)) ℤ}
    (f : A' ⟶ A) (g : B ⟶ B') :
    (openSubspacePushComplex U).map
          (RingedSite.homMap ((ringedSite X.sheaf).over U) f g) ≫
        (sheafHomComplexOpenSubspaceIso U A' B').hom =
      (sheafHomComplexOpenSubspaceIso U A B).hom ≫
        RingedSite.homMap (ringedSite (openSubspace U).sheaf)
          ((openSubspacePushComplex U).map f) ((openSubspacePushComplex U).map g) :=
  have := openSubspaceEquivalenceFunctorIsContinuous U
  have := openSubspaceEquivalenceInverseIsContinuous U
  RingedSite.siteEquivSheafHomComplexIsoOfIso_natural
    (X := (ringedSite X.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
    U.overEquivalence.symm (openSubspacePhi U) (hφ := isIso_openSubspacePhi U) f g

section Algebra

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
  [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The graded algebra of the cohomology of an internal Hom complex on the slice site, read on
the open subspace.** For a complex `P` of modules on `Opens X / U`, the transport along
`Stacks.SheafOfModules.openSubspaceEquiv` of the graded algebra of the cohomology sheaves of
`SheafHom^•(P, P)` is the graded algebra of the cohomology sheaves of the internal Hom complex
of the transport of `P`, formed on the ringed site of `X.restrict U`. -/
def openSubspaceHomologyGradedAlgebraHom
    (P : CochainComplex
      (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite X.sheaf).over U).O)) ℤ) :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom
      (_root_.SheafOfModules.GradedAlgebra.pushforward (openSubspacePhi U)
        (RingedSite.homologyGradedAlgebra ((ringedSite X.sheaf).over U) P))
      (RingedSite.homologyGradedAlgebra (ringedSite (openSubspace U).sheaf)
        ((openSubspacePushComplex U).obj P)) :=
  letI := openSubspaceEquivalenceFunctorIsContinuous U
  letI := openSubspaceEquivalenceInverseIsContinuous U
  RingedSite.homologyGradedAlgebraSiteEquivHomOfIso
    (X := (ringedSite X.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
    (hφ := isIso_openSubspacePhi U)
    (hlim := RingedSite.pushforward_preservesFiniteLimitsOfIso
      (X := (ringedSite X.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
      U.overEquivalence.symm (openSubspacePhi U) (hφ := isIso_openSubspacePhi U))
    (hcolim := RingedSite.pushforward_preservesFiniteColimitsOfIso
      (X := (ringedSite X.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
      U.overEquivalence.symm (openSubspacePhi U) (hφ := isIso_openSubspacePhi U))
    U.overEquivalence.symm (openSubspacePhi U) P

/-- **Every degree of the identification is an isomorphism.** -/
instance isIso_openSubspaceHomologyGradedAlgebraHom_app
    (P : CochainComplex
      (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite X.sheaf).over U).O)) ℤ) (n : ℤ) :
    IsIso ((openSubspaceHomologyGradedAlgebraHom U P).app n) :=
  letI := openSubspaceEquivalenceFunctorIsContinuous U
  letI := openSubspaceEquivalenceInverseIsContinuous U
  RingedSite.isIso_homologyGradedAlgebraSiteEquivHomOfIso_app
    (X := (ringedSite X.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
    (hφ := isIso_openSubspacePhi U)
    (hlim := RingedSite.pushforward_preservesFiniteLimitsOfIso
      (X := (ringedSite X.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
      U.overEquivalence.symm (openSubspacePhi U) (hφ := isIso_openSubspacePhi U))
    (hcolim := RingedSite.pushforward_preservesFiniteColimitsOfIso
      (X := (ringedSite X.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
      U.overEquivalence.symm (openSubspacePhi U) (hφ := isIso_openSubspacePhi U))
    U.overEquivalence.symm (openSubspacePhi U) P n

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
  [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The transport of a sheaf of graded algebras off the slice site is the pushforward along the
structure map of the equivalence of ringed sites: the two spellings of the source of the
identification are the same object. -/
theorem openSubspaceGradedAlgebra_eq_sitePushforward
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U)) :
    openSubspaceGradedAlgebra U A =
      _root_.SheafOfModules.GradedAlgebra.pushforward (openSubspacePhi U) A :=
  rfl

/-- The restriction of a complex of `O_X`-modules to the open subspace `U`: its restriction to
the slice site over `U`, read on `X.restrict U`. -/
abbrev openSubspaceRestrictComplex
    (Q : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    CochainComplex
      (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite (openSubspace U).sheaf).O)) ℤ :=
  (openSubspacePushComplex U).obj (RingedSite.restrictComplex (ringedSite X.sheaf) Q U)

/-- **The identification the local-to-global step of [Stacks, Tag 0BQY] needs.** For a complex
`Q` of `O_X`-modules, the graded algebra of the cohomology sheaves of `SheafHom^•(Q, Q)`,
restricted to the slice site over `U` and read on the open subspace by
`Stacks.SheafOfModules.openSubspaceGradedAlgebra`, is the graded algebra of the cohomology
sheaves of the internal Hom complex of `Q|_U` formed on the ringed space `X.restrict U`.

It is `AlgebraicGeometry.RingedSite.homologyGradedAlgebraOverHom`, which carries the first to
the graded algebra of the restricted complex on the slice site, pushed off the slice site and
followed by `Stacks.SheafOfModules.openSubspaceHomologyGradedAlgebraHom`. -/
def openSubspaceHomologyGradedAlgebraOfSpaceHom
    (Q : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom
      (openSubspaceGradedAlgebra U
        ((RingedSite.homologyGradedAlgebra (ringedSite X.sheaf) Q).over U))
      (RingedSite.homologyGradedAlgebra (ringedSite (openSubspace U).sheaf)
        (openSubspaceRestrictComplex U Q)) :=
  ((RingedSite.homologyGradedAlgebraOverHom (ringedSite X.sheaf) U Q).sitePushforward
      (openSubspacePhi U)).comp
    (openSubspaceHomologyGradedAlgebraHom U
      (RingedSite.restrictComplex (ringedSite X.sheaf) Q U))

/-- **Every degree of that identification is an isomorphism.** -/
instance isIso_openSubspaceHomologyGradedAlgebraOfSpaceHom_app
    (Q : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ) :
    IsIso ((openSubspaceHomologyGradedAlgebraOfSpaceHom U Q).app n) := by
  have h1 : IsIso ((RingedSite.homologyGradedAlgebraOverHom (ringedSite X.sheaf) U Q).app n) :=
    RingedSite.isIso_homologyGradedAlgebraOverHom_app (ringedSite X.sheaf) U Q n
  have h2 : IsIso ((openSubspaceHomologyGradedAlgebraHom U
      (RingedSite.restrictComplex (ringedSite X.sheaf) Q U)).app n) :=
    isIso_openSubspaceHomologyGradedAlgebraHom_app U _ n
  have h3 : IsIso
      (((RingedSite.homologyGradedAlgebraOverHom (ringedSite X.sheaf) U Q).sitePushforward
        (openSubspacePhi U)).app n) :=
    ((_root_.SheafOfModules.pushforward.{u} (openSubspacePhi U)).mapIso
      (@asIso _ _ _ _ _ h1)).isIso_hom
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h3 h2

end Algebra

end Stacks.SheafOfModules

end
