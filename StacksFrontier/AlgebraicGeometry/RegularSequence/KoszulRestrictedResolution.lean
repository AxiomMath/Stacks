module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtKInjectiveModel
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedIsoOpenSubspace

/-!
# The restriction of a resolution of the quotient, against the Koszul complex over an open

The local-to-global step of [Stacks, Tag 0BQY] compares two models of one object of the derived
category of an open subspace `X|_U`. On one side is the **restriction of a resolution chosen on
all of `X`**, from which the global graded algebra is formed; on the other is the **Koszul
complex of a sequence of sections over `U`**, in terms of which the local statements of the tag
are proved in
`Stacks.AlgebraicGeometry.RegularIdealSheaf.forall_isIso_extComparison_of_isKoszulSequenceExactOn`
for a sequence whose Koszul complex is exact on `U`. This file carries out that comparison.

Two halves. The Koszul complex presents the quotient of the structure sheaf of `X|_U`, placed in
degree zero: that is its augmentation, which is a quasi-isomorphism exactly when the Koszul
complex resolves the quotient, and
`Stacks.RegularSequence.KoszulChainData.quotientDerivedIso` records the resulting
derived-category identification. And the restriction to `U` of a resolution of a sheaf of
`O_X`-modules presents the restriction of that sheaf of modules, placed in degree zero: that is
`Stacks.SheafOfModules.openSubspaceRestrictSingleDerivedIso` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedIsoOpenSubspace`, which rests on the
fact that restriction preserves quasi-isomorphisms.

What joins the two halves is an identification of sheaves of modules on `X|_U`: the restriction
of the global quotient with the quotient formed over `U` by the Koszul morphism. That
identification is a hypothesis here, named `θ`; it is the whole residue of the comparison, and
the implementation notes say what is known about it and what is not.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData.quotientDerivedIso`: **the Koszul complex presents the
  quotient placed in degree zero**, for a chain datum whose augmentation is a quasi-isomorphism.
  This is the composite of the augmentation with the comparison of the two readings of a complex
  concentrated in degree zero, both of which were already in the library; it is the inline
  composite of `Stacks.RegularSequence.KoszulChainData.homIso`, named once.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.koszulRestrictedModelIso`: **the restriction to `U`
  of a resolution of the quotient presents the object the Koszul complex over `U` resolves.**
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.restrictedModelComparisonIso`: **the two models
  over `U` have the same composition-product algebra**, as sheaves of graded algebras on `X|_U`.

## Implementation notes

**What `θ` is, and what is known about it.** Take the global sheaf of modules `M` to be the
quotient `O_X/I`, a cokernel of a morphism of sheaves of `O_X`-modules
(`Stacks.RegularSequence.koszulQuotient` is `CategoryTheory.Limits.cokernel`), and take the
Koszul datum over `U` to be the canonical one of
`Stacks.RegularSequence.koszulHomOfSections` of the generating sections read on `X|_U`, as the
local statements of the tag do. Then `θ` asks that the restriction of the first cokernel to `U`
be the second. The two sheaves of ideals involved are known to agree on sections:
`Stacks.AlgebraicGeometry.RegularIdealSheaf.sectionIdeal_idealOfHom_koszulHomOfSections` is that
agreement, and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.koszulQuotientIsoIdealQuotient` identifies the
cokernel of a morphism attached to generating sections with the quotient by the sheaf of ideals
they generate. What joins those to `θ` is the module-level counterpart of
`Stacks.Sites.quotientRingSheafIso` — the passage from an agreement of two sheaves of ideals on
sections to an identification of the two quotients of the unit sheaf by them, for sheaves of
modules rather than for sheaves of rings — and that is
`Stacks.SheafOfModules.cokernelIsoOfLocalClosureRangeEq`, stated against *local* membership
since the sheaves of ideals in play are local closures. `θ` is produced from it in
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulRestrictedQuotient`, whose
`Stacks.AlgebraicGeometry.RegularIdealSheaf.koszulRestrictedQuotientIso` is `θ` for the
canonical Koszul morphism; the two definitions below are restated there with `θ` discharged,
leaving as the only hypothesis that `f₁, …, f_r` generate the global sheaf of ideals on the
slice site over `U`, which is the tag's own local hypothesis.

**`θ` is a hypothesis and not a weakening.** Nothing below is a statement about the quotient
`O_X/I`: `M` is an arbitrary sheaf of `O_X`-modules and the Koszul datum is arbitrary, so `θ` is
the only thing that ties them together and it has to be supplied. Supplying it as a hypothesis
isolates the residue in one named isomorphism instead of distributing it over the chain, and the
two halves above are proved for every `M` and every datum.

**No `@[stacks]` attribute.** As in
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtKInjectiveModel`, nothing here is a
clause of Tag 0BQY: the tag's statement is about the intrinsic comparison built from the derived
composition product and about one isomorphism of sheaves on `Y`, and this file supplies an input
to the gluing of the local statements, not the gluing itself. The caveats recorded on
`Stacks.AlgebraicGeometry.RegularIdealSheaf.forall_isIso_extComparison_of_isKoszulSequenceExactOn`
say what is still owed.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {Z : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Z)
  [HasSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  {A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥Z) (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    _root_.SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥Z) Rc)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]

/-- **The Koszul complex presents the quotient of the structure sheaf, placed in degree zero.**
The augmentation `Stacks.RegularSequence.KoszulChainData.cochainAugmentation` is a
quasi-isomorphism as soon as the Koszul complex resolves the quotient, hence invertible in the
derived category, and `Stacks.RegularSequence.KoszulChainData.quotientSingleIso` reconciles the
two readings of a complex concentrated in degree zero.

Both factors were in the library; this composite appears inline in
`Stacks.RegularSequence.KoszulChainData.homIso` and is named here because the comparison of the
Koszul model over an open with the restriction of a global resolution consumes it. -/
def quotientDerivedIso :
    DerivedCategory.Q.obj (cochain Rc K) ≅
      DerivedCategory.Q.obj ((single (StructureSheafModules Rc)
        (ComplexShape.up ℤ) 0).obj (quotient Rc (φ := φ))) :=
  asIso (DerivedCategory.Q.map (cochainAugmentation Rc K)) ≪≫
    DerivedCategory.Q.mapIso (quotientSingleIso Rc (φ := φ))

end Stacks.RegularSequence.KoszulChainData

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

open Stacks.SheafOfModules Stacks.RegularSequence Stacks.RegularSequence.KoszulChainData

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    ((Opens.grothendieckTopology X.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥(openSubspace U).carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥(openSubspace U).carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  {r : ℕ}
  {A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥(openSubspace U).carrier)
    (koszulFreeSheaf (openSubspace U).sheaf r)}
  {φ : koszulFreeSheaf (openSubspace U).sheaf r ⟶
    _root_.SheafOfModules.unit
      (toRingCat (Opens.grothendieckTopology ↥(openSubspace U).carrier)
        (openSubspace U).sheaf)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]

/-- **The restriction to `U` of a resolution of a sheaf of modules presents the object the Koszul
complex over `U` resolves**, once the restriction of that sheaf of modules is identified with the
quotient the Koszul morphism over `U` forms.

Let `M` be a sheaf of `O_X`-modules and let `I` be a K-injective complex of `O_X`-modules
presenting `M` placed in degree zero. Let `K` be a Koszul chain datum on `X|_U` whose
augmentation is a quasi-isomorphism, so that its Koszul complex resolves the quotient formed
there, and let `θ` identify the restriction of `M` to `U` with that quotient. Then the Koszul
cochain complex over `U` and the restriction of `I` present the same object of `D(O_{X|U})`.

Three steps, in this order: the Koszul complex presents the local quotient placed in degree zero
(`Stacks.RegularSequence.KoszulChainData.quotientDerivedIso`), `θ` carries that to the
restriction of `M` placed in degree zero, and the restriction of a resolution presents the
restriction (`Stacks.SheafOfModules.openSubspaceRestrictSingleDerivedIso`). The restriction of
`I` is again K-injective
(`Stacks.SheafOfModules.isKInjective_openSubspaceRestrictComplex`), so it is a K-injective model
of that object; `θ` is the only input not already in the library, and the implementation notes
say what is known about it. -/
def koszulRestrictedModelIso (M : _root_.SheafOfModules.{u} (structureSheafRing X))
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (e : DerivedCategory.Q.obj
        ((single (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) 0).obj M) ≅
      DerivedCategory.Q.obj I)
    (θ : openSubspaceRestrictModule U M ≅ quotient (openSubspace U).sheaf (φ := φ)) :
    DerivedCategory.Q.obj (cochain (openSubspace U).sheaf K) ≅
      DerivedCategory.Q.obj (openSubspaceRestrictComplex U I) :=
  quotientDerivedIso (openSubspace U).sheaf K ≪≫
    DerivedCategory.Q.mapIso
        ((single (StructureSheafModules (openSubspace U).sheaf)
          (ComplexShape.up ℤ) 0).mapIso θ).symm ≪≫
      openSubspaceRestrictSingleDerivedIso U M 0 I hI e

/-- **The two models over `U` have the same composition-product algebra.** The graded algebra of
the cohomology sheaves of the internal Hom complex of the restriction of a global resolution is
isomorphic, as a sheaf of graded algebras on `X|_U`, to the one of the Koszul cochain complex
over `U`.

This is `Stacks.SheafOfModules.modelComparisonIsoOfDerivedIso` at the identification
`koszulRestrictedModelIso`: the comparison of models needs no chosen morphism between the two
complexes, only that they present the same object, and the Koszul cochain complex is strictly
perfect (`Stacks.RegularSequence.KoszulChainData.finite_not_isZero_cochain_X` and
`isFiniteFreeSummand_cochain_X`). The K-injectivity the comparison asks of the other model is
that of the restricted resolution, which is where
`Stacks.SheafOfModules.isKInjective_openSubspaceRestrictComplex` is used; it is held at the
ringed-space spelling of the sheaf of rings of the slice, while the comparison asks for it in
`StructureSheafModules (openSubspace U).sheaf`. The two are the same category by `rfl`, but each
sheaf of rings is reached through a plain definition, so instance search does not identify them:
the `[I.IsKInjective]` argument is therefore handed over positionally rather than sought. -/
def restrictedModelComparisonIso (M : _root_.SheafOfModules.{u} (structureSheafRing X))
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (e : DerivedCategory.Q.obj
        ((single (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) 0).obj M) ≅
      DerivedCategory.Q.obj I)
    (θ : openSubspaceRestrictModule U M ≅ quotient (openSubspace U).sheaf (φ := φ)) :
    homologyGradedAlgebra (openSubspace U).sheaf (openSubspaceRestrictComplex U I) ≅
      homologyGradedAlgebra (openSubspace U).sheaf (cochain (openSubspace U).sheaf K) :=
  @modelComparisonIsoOfDerivedIso _ (openSubspace U).sheaf inferInstance inferInstance
    (cochain (openSubspace U).sheaf K) (openSubspaceRestrictComplex U I)
    (isKInjective_openSubspaceRestrictComplex U I hI)
    (finite_not_isZero_cochain_X (openSubspace U).sheaf K)
    (isFiniteFreeSummand_cochain_X (openSubspace U).sheaf K)
    (koszulRestrictedModelIso U K M I hI e θ)

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
