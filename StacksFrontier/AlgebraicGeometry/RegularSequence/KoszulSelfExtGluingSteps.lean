module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraSliceComparisonGluing
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulRestrictedQuotient
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexAlgebraOpenSubspace

/-!
# The three Koszul-specific transports of the exterior-algebra universal property over an open

`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop` glues the
invertibility of a comparison out of an exterior algebra from two hypotheses over each member of
a cover, of which the second — that the restriction of the *target* is again an exterior algebra
on the restricted generator — is a universal property and therefore crosses only those links of a
chain of presentations that stay on one site.
`Stacks.SheafOfModules.isExteriorAlgebra_id_over_descend_of_openSubspace` crosses the links that
change the site. Three links are left, each on one site, and this file supplies them:

* the passage between the graded algebra of a complex of modules on an open subspace and the
  open-subspace reading of the restriction of the graded algebra of a complex on the whole space,
  which is `Stacks.SheafOfModules.openSubspaceHomologyGradedAlgebraOfSpaceHom`;
* the passage between the two quotients of the structure sheaf of the open subspace that the
  descent of such an algebra may be taken along, which is
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.isExteriorAlgebra_descend_koszulOpenSubspace`,
  specialized here to the identity generator;
* the passage between the Koszul complex of a sequence of sections over the open and the
  restriction to it of a resolution chosen on the whole space, which is the comparison of two
  models of one object of the derived category.

## Main definitions

* `Stacks.SheafOfModules.modelComparisonUnitalOfDerivedIso`: the comparison of the
  composition-product algebras of two models of one object of the derived category, as a
  *unital homomorphism* of sheaves of graded algebras rather than as an isomorphism in their
  category.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.restrictedModelComparisonUnitalOfGenerated`: its
  instance at the Koszul complex over an open and the restriction of a global resolution.

## Main results

* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_id_of_isIso` and
  `of_id_comp_isIso`: a sheaf of graded algebras which is the exterior algebra of its own
  degree-one piece is the exterior algebra of anything invertibly mapping onto that piece. This is
  what turns a statement at the identity generator into one at the generator a transport produces.
* `Stacks.SheafOfModules.isExteriorAlgebra_id_openSubspaceHomologyGradedAlgebra`: **the first
  link.**
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isExteriorAlgebra_id_descend_koszulOpenSubspace`:
  **the second link**, at the identity generator.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isExteriorAlgebra_id_openSubspaceRestrictComplex`:
  **the third link.**

## Implementation notes

**Why the model comparison had to be restated.** The comparison of the two models over an open is
proved as `Stacks.AlgebraicGeometry.RegularIdealSheaf.restrictedModelComparisonIsoOfGenerated`, an
isomorphism in the category of sheaves of graded algebras, whose morphisms are
`SheafOfModules.GradedAlgebra.Hom` — multiplicative but not required to preserve the distinguished
degree-zero unit. The transport of the universal property,
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_ofDegreewiseIso`, consumes a
`SheafOfModules.GradedAlgebra.UnitalHom`. The unital original is upstream,
`Stacks.SheafOfModules.modelComparison`, and what this file does is run the same chain of
constructions keeping it unital, so no unit law is reproved.

**Why the second link is not an application of the transport lemma.**
`isExteriorAlgebra_descend_koszulOpenSubspace` tracks a generator: its hypothesis is the universal
property at `genScalarRestrict θ ι` followed by the transport of the descent along the comparison
of the two quotients, and its conclusion is the property at `ι`. At `ι` the identity the
hypothesis is therefore *not* at the identity, and the statement below closes the gap with
`IsExteriorAlgebra.of_id_comp_isIso`: restriction of scalars carries an invertible morphism to an
invertible one (`SheafOfModules.GradedAlgebra.isIso_genScalarRestrict`), the transport is
invertible in every degree, and a universal property at the identity is one at any invertible
replacement of it.

**One spelling hazard.** `Stacks.SheafOfModules.Tensor.ringSheaf` is reachable as
`Tensor.ringSheaf` inside the namespace below, and it and
`AlgebraicGeometry.structureSheafRing` are different constructions on different arguments. Every
occurrence of the structure sheaf of a ringed space is therefore written out in full.

**No `@[stacks]` attribute.** Nothing here is a clause of Tag 0BQY: these are three transports of
one hypothesis of the gluing of that tag's local statements, not the gluing and not the tag. What
is still owed is recorded on
`Stacks.AlgebraicGeometry.RegularIdealSheaf.forall_isIso_extComparison_of_isKoszulSequenceExactOn`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace SheafOfModules.GradedAlgebra

section Generator

universe a w v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{w}}
  {B : GradedAlgebra.{w, a} R} {M N : _root_.SheafOfModules.{a} R}

/-- **Restriction of scalars carries an invertible degree-one generator to an invertible one.**
`SheafOfModules.GradedAlgebra.genScalarRestrict` is the image of the generator under restriction of
scalars, and a functor carries isomorphisms to isomorphisms. -/
instance isIso_genScalarRestrict (θ : S ⟶ R) (ι : M ⟶ B.piece 1) [IsIso ι] :
    IsIso (genScalarRestrict (A := B) θ ι) :=
  inferInstanceAs (IsIso ((_root_.SheafOfModules.restrictScalars.{a} θ).map ι))

/-- **A sheaf of graded algebras which is the exterior algebra of its own degree-one piece is the
exterior algebra of anything invertibly mapping onto that piece.**
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso` moves the generating sheaf of modules
along an isomorphism, and composing with the identity changes nothing. -/
theorem IsExteriorAlgebra.of_id_of_isIso (c : M ⟶ B.piece 1) [IsIso c]
    (h : IsExteriorAlgebra B (𝟙 (B.piece 1))) : IsExteriorAlgebra B c := by
  simpa using h.comp_iso c inferInstance

/-- **The two-factor form of `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_id_of_isIso`.**
A transport of a universal property through a chain of presentations produces a generator which is
a composite of invertible morphisms rather than a single one, and the intermediate object is
typically not the degree-one piece of either algebra, so the composite is matched as such. -/
theorem IsExteriorAlgebra.of_id_comp_isIso (c : M ⟶ N) [IsIso c] (d : N ⟶ B.piece 1) [IsIso d]
    (h : IsExteriorAlgebra B (𝟙 (B.piece 1))) : IsExteriorAlgebra B (c ≫ d) :=
  have : IsIso (c ≫ d) := @IsIso.comp_isIso _ _ _ _ _ c d _ _
  IsExteriorAlgebra.of_id_of_isIso (c ≫ d) h

end Generator

end SheafOfModules.GradedAlgebra

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

section Model

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison of the two models of a self-Ext algebra, as a unital homomorphism of sheaves
of graded algebras, from a derived-category identification alone.**
`Stacks.SheafOfModules.modelComparisonIsoOfDerivedIso` is the same comparison read in the category
of sheaves of graded algebras, whose morphisms need not preserve the distinguished degree-zero
unit; the transport of an exterior-algebra universal property consumes a unital homomorphism, so
the comparison is assembled here without passing through that category.

It is `Stacks.SheafOfModules.modelComparison` with its comparison morphism supplied by
`CochainComplex.realizeDerivedIso` and the invertibility of postcomposition by Stacks 08JH. -/
def modelComparisonUnitalOfDerivedIso (K I : CochainComplex (StructureSheafModules Rc) ℤ)
    [I.IsKInjective]
    (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (K.X i))
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj I) :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom
      (homologyGradedAlgebra Rc I) (homologyGradedAlgebra Rc K) :=
  letI := isIso_homologyMap_targetComparison Rc K I
    (CochainComplex.realizeDerivedIso K I e) hbdd hterm
  modelComparison Rc K I (CochainComplex.realizeDerivedIso K I e)

/-- **The unital model comparison is an isomorphism in every degree.** -/
instance isIso_modelComparisonUnitalOfDerivedIso_app
    (K I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective]
    (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (K.X i))
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj I) (n : ℤ) :
    IsIso ((modelComparisonUnitalOfDerivedIso Rc K I hbdd hterm e).app n) :=
  letI := isIso_homologyMap_targetComparison Rc K I
    (CochainComplex.realizeDerivedIso K I e) hbdd hterm
  isIso_modelComparison_app Rc K I (CochainComplex.realizeDerivedIso K I e) n

end Model

section OpenSubspace

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- **The first of the three links: the open subspace against the restriction to the slice
site.** If the composition-product algebra of the restriction to `U` of a complex of
`O_X`-modules is the exterior algebra of its own degree-one piece, then so is the open-subspace
reading of the restriction of the composition-product algebra of that complex to the slice site
over `U`.

Both sides live on `Opens U`, so this link stays on one site and the universal property crosses
it: one application of
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_degreewiseIso` to
`Stacks.SheafOfModules.openSubspaceHomologyGradedAlgebraOfSpaceHom`. -/
theorem isExteriorAlgebra_id_openSubspaceHomologyGradedAlgebra
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
    [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (Q : CochainComplex (_root_.SheafOfModules.{u}
      (structureSheafRing X)) ℤ)
    (h : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra
      (RingedSite.homologyGradedAlgebra (ringedSite (openSubspace U).sheaf)
        (openSubspaceRestrictComplex U Q))
      (𝟙 ((RingedSite.homologyGradedAlgebra (ringedSite (openSubspace U).sheaf)
        (openSubspaceRestrictComplex U Q)).piece 1))) :
    _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra
      (openSubspaceGradedAlgebra U
        ((RingedSite.homologyGradedAlgebra (ringedSite X.sheaf) Q).over U))
      (𝟙 ((openSubspaceGradedAlgebra U
        ((RingedSite.homologyGradedAlgebra (ringedSite X.sheaf) Q).over U)).piece 1)) :=
  @_root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_degreewiseIso
    _ _ _ _ _ _ h (openSubspaceHomologyGradedAlgebraOfSpaceHom U Q)
    (fun n => isIso_openSubspaceHomologyGradedAlgebraOfSpaceHom_app U Q n)

end OpenSubspace

end Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence
open Stacks.RegularSequence.KoszulChainData

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    ((Opens.grothendieckTopology X.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
  {A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥(openSubspace U).carrier)
    (koszulFreeSheaf (openSubspace U).sheaf r)}
  (K : KoszulChainData.{u, u, u} A
    (koszulHomOfSections (openSubspace U).sheaf fun j => sectionOnRestriction X U (f j)))
  [QuasiIso K.augmentation]

section Model

variable {F : _root_.SheafOfModules.{u} (structureSheafRing X)}
  (Φ : F ⟶ _root_.SheafOfModules.unit (structureSheafRing X))
  (hgen : ∀ W : (Over U)ᵒᵖ,
    sectionIdeal (sliceIdealOfSections U f) W =
      sectionIdeal (idealOfHom (O := X.sheaf.over U)
        ((_root_.SheafOfModules.overFunctor.{u}
          (structureSheafRing X) U).map Φ)) W)
  (I : CochainComplex (_root_.SheafOfModules.{u}
    (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
  (e : DerivedCategory.Q.obj
      ((single (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ) 0).obj (cokernel Φ)) ≅
    DerivedCategory.Q.obj I)

/-- **The two models over `U` have the same composition-product algebra, as a unital homomorphism
of sheaves of graded algebras.**
`Stacks.AlgebraicGeometry.RegularIdealSheaf.restrictedModelComparisonIsoOfGenerated` is the same
comparison read in the category of sheaves of graded algebras; the transport of an
exterior-algebra universal property needs the unit law, which that reading drops. This is
`Stacks.SheafOfModules.modelComparisonUnitalOfDerivedIso` at the identification
`koszulRestrictedModelIsoOfGenerated`, the strict-perfection hypotheses being those of the Koszul
cochain complex and the K-injectivity that of the restricted resolution.

**The restricted resolution is named at the `Stacks.SheafOfModules.StructureSheafModules`
spelling before its K-injectivity is introduced.**
`Stacks.SheafOfModules.openSubspaceRestrictComplex` is stated over
`Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite (openSubspace U).sheaf).O`, the canonical
sheaf of rings, while the comparison below reads its complexes over `structureSheaf`. The two are
one sheaf of rings and elaboration crosses them, but instance search does not, so the
K-injectivity supplied by `Stacks.SheafOfModules.isKInjective_openSubspaceRestrictComplex` is
found only at the spelling it is stated at; naming the complex once at the spelling the comparison
uses is what puts the hypothesis in context there. This is the idiom recorded in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.KInjectiveOpenSubspace`. -/
def restrictedModelComparisonUnitalOfGenerated :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom
      (homologyGradedAlgebra (openSubspace U).sheaf (openSubspaceRestrictComplex U I))
      (homologyGradedAlgebra (openSubspace U).sheaf (cochain (openSubspace U).sheaf K)) :=
  letI restricted : CochainComplex (StructureSheafModules (openSubspace U).sheaf) ℤ :=
    openSubspaceRestrictComplex U I
  letI : restricted.IsKInjective := isKInjective_openSubspaceRestrictComplex U I hI
  modelComparisonUnitalOfDerivedIso (openSubspace U).sheaf
    (cochain (openSubspace U).sheaf K) (openSubspaceRestrictComplex U I)
    (finite_not_isZero_cochain_X (openSubspace U).sheaf K)
    (isFiniteFreeSummand_cochain_X (openSubspace U).sheaf K)
    (koszulRestrictedModelIsoOfGenerated U f K Φ hgen I hI e)

/-- **The comparison of the two models over `U` is an isomorphism in every degree.** -/
theorem isIso_restrictedModelComparisonUnitalOfGenerated_app (n : ℤ) :
    IsIso ((restrictedModelComparisonUnitalOfGenerated U f K Φ hgen I hI e).app n) :=
  letI restricted : CochainComplex (StructureSheafModules (openSubspace U).sheaf) ℤ :=
    openSubspaceRestrictComplex U I
  letI : restricted.IsKInjective := isKInjective_openSubspaceRestrictComplex U I hI
  isIso_modelComparisonUnitalOfDerivedIso_app (openSubspace U).sheaf _ _ _ _ _ n

include Φ hgen hI e in
/-- **The third of the three links: the Koszul complex over `U` against the restriction of a
global resolution.** If the composition-product algebra of the Koszul cochain complex of
`f₁, …, f_r` over `U` is the exterior algebra of its own degree-one piece, then so is the
composition-product algebra of the restriction to `U` of a resolution chosen on all of `X`.

This is the one of the three links whose content is mathematics rather than a change of
presentation: the two complexes present the same object of `D(O_{X|U})`, by
`koszulRestrictedModelIsoOfGenerated`, and the comparison of the composition-product algebras of
two models of one object is `Stacks.SheafOfModules.modelComparison`. Both sides live on `X|_U`, so
the universal property crosses the link. -/
theorem isExteriorAlgebra_id_openSubspaceRestrictComplex
    (h : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra
      (homologyGradedAlgebra (openSubspace U).sheaf (cochain (openSubspace U).sheaf K))
      (𝟙 ((homologyGradedAlgebra (openSubspace U).sheaf
        (cochain (openSubspace U).sheaf K)).piece 1))) :
    _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra
      (homologyGradedAlgebra (openSubspace U).sheaf (openSubspaceRestrictComplex U I))
      (𝟙 ((homologyGradedAlgebra (openSubspace U).sheaf
        (openSubspaceRestrictComplex U I)).piece 1)) :=
  @_root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_degreewiseIso
    _ _ _ _ _ _ h (restrictedModelComparisonUnitalOfGenerated U f K Φ hgen I hI e)
    (fun n => isIso_restrictedModelComparisonUnitalOfGenerated_app U f K Φ hgen I hI e n)

end Model

section Quotient

open _root_.SheafOfModules.GradedAlgebra

variable [HasWeakSheafify (Opens.grothendieckTopology ↥U) CommRingCat.{u}]
  [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) CommRingCat.{u}]

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    ((Opens.grothendieckTopology X.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The second of the three links, at the identity generator: the two quotients of the structure
sheaf of `U`.** A sheaf of graded algebras on `X|_U` descended along the quotient by the sheaf of
ideals the Koszul morphism of `f₁, …, f_r` generates there is the exterior algebra of its own
degree-one piece if and only if its descent along the open-subspace reading of the quotient by the
sheaf of ideals `f₁, …, f_r` generate on the slice site is; this is the direction a local
computation feeds.

`Stacks.AlgebraicGeometry.RegularIdealSheaf.isExteriorAlgebra_descend_koszulOpenSubspace` tracks a
generator, and its hypothesis is therefore not at the identity even when its conclusion is: the
generator it asks for is the identity restricted along the comparison of the two quotients and
then carried by the transport of the descent. Both are invertible, so
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_id_comp_isIso` supplies the hypothesis from the
statement at the identity. -/
theorem isExteriorAlgebra_id_descend_koszulOpenSubspace
    (B : _root_.SheafOfModules.GradedAlgebra.{u, u} (openSubspaceRing U))
    (hB : ∀ (n : ℤ) (V : (Opens ↥U)ᵒᵖ) (b : (openSubspaceRing U).obj.obj V),
      b ∈ RingHom.ker ((quotientRingHom (koszulOpenSubspaceIdeal U f)).hom.app V).hom →
        ∀ m : (B.piece n).val.obj V, b • m = 0)
    (h : IsExteriorAlgebra (descend (quotientRingHom (koszulOpenSubspaceIdeal U f)) B hB)
      (𝟙 ((descend (quotientRingHom (koszulOpenSubspaceIdeal U f)) B hB).piece 1))) :
    IsExteriorAlgebra
      (descend (openSubspaceQuotientHom U (quotientRingHom (sliceIdealOfSections U f))) B
        (smul_eq_zero_of_mem_ker_openSubspaceRingPushforward U (sliceIdealOfSections U f)
          (koszulOpenSubspaceIdeal U f)
          (sectionIdeal_idealOfHom_koszulHomOfSections U f) B hB))
      (𝟙 ((descend (openSubspaceQuotientHom U (quotientRingHom (sliceIdealOfSections U f))) B
        (smul_eq_zero_of_mem_ker_openSubspaceRingPushforward U (sliceIdealOfSections U f)
          (koszulOpenSubspaceIdeal U f)
          (sectionIdeal_idealOfHom_koszulHomOfSections U f) B hB)).piece 1)) := by
  refine isExteriorAlgebra_descend_koszulOpenSubspace U f B hB ?_
  exact IsExteriorAlgebra.of_id_comp_isIso _ _ h

end Quotient

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
