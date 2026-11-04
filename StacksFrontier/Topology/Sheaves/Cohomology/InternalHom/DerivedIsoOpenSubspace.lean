module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
public import StacksFrontier.Homology.Injectives.KInjective.RealizeDerivedIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.KInjectiveOpenSubspace

/-!
# Restricting a resolution to an open subspace

Let `(X, O_X)` be a ringed space and `U ⊆ X` open. `Stacks.SheafOfModules`
`.openSubspaceRestrictComplex` restricts a complex of `O_X`-modules to the ringed space
`X.restrict U`: the degreewise restriction to the slice site `Opens X / U`, followed by the
transport off that site. This file shows that the construction **carries a presentation to a
presentation**: if a complex `L` of `O_X`-modules and a K-injective complex `I` present the same
object of `D(O_X)`, then their restrictions present the same object of `D(O_{X|U})` — and the
restriction of `I` is again K-injective
(`Stacks.SheafOfModules.isKInjective_openSubspaceRestrictComplex`), so it is a K-injective model
of that object.

Everything rests on one fact that had not been recorded: restriction to a slice of a site
preserves quasi-isomorphisms. `Stacks.SheafOfModules.preservesHomology_overFunctor` is the
exactness, and `HomologicalComplex.quasiIso_map_of_preservesHomology` turns it into the
statement about complexes, which is
`Stacks.SheafOfModules.quasiIso_overFunctor_mapHomologicalComplex_map`; the transport off the
slice site is an equivalence, hence preserves homology for free. A derived-category
identification is then carried across by realizing it as a chain map first:
`CochainComplex.realizeDerivedIso` turns an identification with K-injective target into a
quasi-isomorphism of complexes, and that is what restriction acts on.

## Main definitions

* `Stacks.SheafOfModules.openSubspaceRestrictComplexMap`: the restriction of a morphism of
  complexes of `O_X`-modules to the open subspace.
* `Stacks.SheafOfModules.openSubspaceRestrictModule`: the restriction of a single sheaf of
  `O_X`-modules to the open subspace, the degree-`n` term of the restriction of a complex
  concentrated in degree `n`.
* `Stacks.SheafOfModules.openSubspaceRestrictSingleIso`: restriction commutes with forming the
  complex concentrated in one degree.

## Main results

* `Stacks.SheafOfModules.quasiIso_openSubspaceRestrictComplexMap`: **the restriction of a
  quasi-isomorphism to the open subspace is a quasi-isomorphism.**
* `Stacks.SheafOfModules.openSubspaceRestrictDerivedIso`: **a derived-category identification
  whose target is K-injective restricts to the open subspace.**
* `Stacks.SheafOfModules.openSubspaceRestrictSingleDerivedIso`: **the restriction of a resolution
  of a sheaf of modules still presents the restriction of that sheaf of modules.** For a
  K-injective complex `I` presenting a sheaf of `O_X`-modules `M` placed in degree `n`, the
  restriction of `I` to `X.restrict U` is a K-injective complex presenting the restriction of
  `M` placed in degree `n`.

## Implementation notes

**Why the statements are at the `(openSubspaceEquiv U).functor.mapHomologicalComplex` spelling
inside the proofs and at the `openSubspacePushComplex` spelling outside.** The two are equal by
definition (`Stacks.SheafOfModules.openSubspacePushComplex_eq` is `rfl`), but
`AlgebraicGeometry.RingedSite.pushComplex`, through which the second is defined, is a plain
definition; instance search does not unfold it, so a `QuasiIso` instance for a morphism in the
image of the second spelling is not found. Each proof therefore re-ascribes its goal at the
first spelling with `show`, exactly as
`Stacks.SheafOfModules.isKInjective_openSubspacePushComplex` names its complex twice. This is
the same discipline as the two spellings of the sheaf of rings of the slice recorded in the
implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.KInjectiveOpenSubspace`, and for the same
reason: elaboration crosses these identities and instance search does not.

**Where the residue of the gluing of [Stacks, Tag 0BQY] now sits.** The local statements of that
tag are about the Koszul complex of a sequence of sections over `U`, read on `X.restrict U`,
while the global algebra is formed from a resolution chosen on all of `X`. What identifies the
two in the derived category of `X.restrict U` is this file, applied to the complex concentrated
in degree zero on the quotient `O_X/I`, together with one further comparison which is not here:
that the restriction to the open subspace of the quotient `O_X/I`, a cokernel of sheaves of
`O_X`-modules, is the quotient formed on `X.restrict U` by the Koszul morphism of the restricted
sections. The two are cokernels of two morphisms into the unit sheaf which generate the same
sheaf of ideals, that agreement being
`Stacks.AlgebraicGeometry.RegularIdealSheaf.sectionIdeal_idealOfHom_koszulHomOfSections`; what is
missing is the passage from an agreement of sheaves of ideals to an identification of the two
cokernels, the module-level counterpart of `Stacks.Sites.quotientRingSheafIso`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    ((Opens.grothendieckTopology X.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Restriction of a morphism of complexes -/

variable {Q Q' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ}

/-- **The restriction of a morphism of complexes of `O_X`-modules to the open subspace `U`**: its
degreewise restriction to the slice site over `U`, transported off that site. Its source and
target are the restrictions `Stacks.SheafOfModules.openSubspaceRestrictComplex` of the source and
target. -/
abbrev openSubspaceRestrictComplexMap (φ : Q ⟶ Q') :
    openSubspaceRestrictComplex U Q ⟶ openSubspaceRestrictComplex U Q' :=
  (openSubspacePushComplex U).map
    (((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)

/-- **The restriction of a quasi-isomorphism to an open subspace is a quasi-isomorphism.**
Restriction to the slice site preserves quasi-isomorphisms
(`Stacks.SheafOfModules.quasiIso_overFunctor_mapHomologicalComplex_map`), and the transport off
the slice site is an equivalence, which preserves homology.

The hypothesis is instance-implicit and the conclusion is a theorem rather than an instance,
because the first of those two steps is itself a theorem: the exactness of restriction is not
available to instance search. -/
theorem quasiIso_openSubspaceRestrictComplexMap (φ : Q ⟶ Q') [QuasiIso φ] :
    QuasiIso (openSubspaceRestrictComplexMap U φ) :=
  let := quasiIso_overFunctor_mapHomologicalComplex_map (R := structureSheafRing X) U φ
  show QuasiIso ((((openSubspaceEquiv U).functor).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
      (((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ)) from inferInstance

/-! ### Restriction of a derived-category identification -/

/-- **A derived-category identification whose target is K-injective restricts to an open
subspace.** If a complex `L` of `O_X`-modules and a K-injective complex `I` present the same
object of `D(O_X)`, their restrictions to `X.restrict U` present the same object of
`D(O_{X|U})`.

The identification is realized by a quasi-isomorphism of complexes
(`CochainComplex.realizeDerivedIso`, which is what K-injectivity of the target is for), the
restriction of that quasi-isomorphism is one, and a quasi-isomorphism becomes invertible in the
derived category.

The K-injectivity hypothesis is explicit, as in
`Stacks.SheafOfModules.isKInjective_openSubspaceRestrictComplex` and for the same reason: a
consumer holds it at one of the two spellings of the sheaf of rings of the slice and introduces
it with `letI`. -/
def openSubspaceRestrictDerivedIso
    (L I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hI : I.IsKInjective)
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj I) :
    DerivedCategory.Q.obj (openSubspaceRestrictComplex U L) ≅
      DerivedCategory.Q.obj (openSubspaceRestrictComplex U I) :=
  letI := hI
  letI := quasiIso_openSubspaceRestrictComplexMap U (CochainComplex.realizeDerivedIso L I e)
  haveI : IsIso (DerivedCategory.Q.map
      (openSubspaceRestrictComplexMap U (CochainComplex.realizeDerivedIso L I e))) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  asIso (DerivedCategory.Q.map
    (openSubspaceRestrictComplexMap U (CochainComplex.realizeDerivedIso L I e)))

/-! ### Restriction of a complex concentrated in one degree -/

/-- **The restriction of a sheaf of `O_X`-modules to the open subspace `U`**: its restriction to
the slice site over `U`, transported off that site. -/
abbrev openSubspaceRestrictModule (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite (openSubspace U).sheaf).O) :=
  (openSubspaceEquiv U).functor.obj
    ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).obj M)

/-- **Restriction to an open subspace commutes with forming the complex concentrated in one
degree.** Both steps of the restriction are additive functors, and
`HomologicalComplex.singleMapHomologicalComplex` is the interchange for an additive functor. -/
def openSubspaceRestrictSingleIso (M : _root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℤ) :
    openSubspaceRestrictComplex U
        ((HomologicalComplex.single (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ) n).obj M) ≅
      (HomologicalComplex.single
          (_root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite (openSubspace U).sheaf).O))
          (ComplexShape.up ℤ) n).obj (openSubspaceRestrictModule U M) :=
  (openSubspacePushComplex U).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U)
          (ComplexShape.up ℤ) n).app M) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (openSubspaceEquiv U).functor
      (ComplexShape.up ℤ) n).app _

/-- **The restriction of a resolution of a sheaf of modules still presents the restriction of
that sheaf of modules.** Let `M` be a sheaf of `O_X`-modules, placed in degree `n`, and let `I`
be a K-injective complex presenting it. Then the restriction of `I` to `X.restrict U` presents
the restriction of `M`, placed in degree `n`; and that restriction of `I` is itself K-injective,
by `Stacks.SheafOfModules.isKInjective_openSubspaceRestrictComplex`, so it is a K-injective model
of the restricted object.

This is `Stacks.SheafOfModules.openSubspaceRestrictDerivedIso` composed with the interchange of
restriction and `HomologicalComplex.single`. It is the form in which the local-to-global step of
[Stacks, Tag 0BQY] needs the identification: the global algebra there is formed from a resolution
of the quotient `O_X/I` chosen on all of `X`, and over a member of the cover it has to be read
against a Koszul resolution of the quotient formed there. -/
def openSubspaceRestrictSingleDerivedIso
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℤ)
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (e : DerivedCategory.Q.obj
        ((HomologicalComplex.single (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ) n).obj M) ≅
      DerivedCategory.Q.obj I) :
    DerivedCategory.Q.obj
        ((HomologicalComplex.single
          (_root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite (openSubspace U).sheaf).O))
          (ComplexShape.up ℤ) n).obj (openSubspaceRestrictModule U M)) ≅
      DerivedCategory.Q.obj (openSubspaceRestrictComplex U I) :=
  (DerivedCategory.Q.mapIso (openSubspaceRestrictSingleIso U M n)).symm.trans
    (openSubspaceRestrictDerivedIso U _ I hI e)

end Stacks.SheafOfModules

end
