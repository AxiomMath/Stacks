module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiCoherent
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeUnitAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestrictionComposite
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction

/-!
# The derived base changes of a morphism of chaotic ringed sites, and their square

Let `F : C' ⥤ C` be a functor of chaotic sites, `(A, d)` and `(A', d)` sheaves of differential
graded algebras on them, and `φ : g^*A → A'` a homomorphism — equivalently, a family of
homomorphisms `A(F U') ⟶ A'(U')` of the section algebras, natural in `U'`.

This file constructs from such a family a
`SheafOfModules.DifferentialGradedModule.MorphismSectionData`, whose derived base change at `U'` is
derived extension of scalars `- ⊗^𝐋_{A(F U')} A'(U')` with its adjunction to derived restriction of
scalars (Tag 0BYX), and identifies the base change carried by any `MorphismSectionData` or
`SheafOfModules.DifferentialGradedModule.SectionData` with derived extension of scalars. It then
constructs the base-change square: base change along a restriction homomorphism of `A` followed by
base change along the structure homomorphism at `U'` is isomorphic to base change along the
structure homomorphism at `V'` followed by base change along the corresponding restriction
homomorphism of `A'`. This square is the first field of
`SheafOfModules.DifferentialGradedModule.DerivedPullbackSectionData`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.MorphismSectionData.ofStructureHom`: the morphism
  section data of a natural family of homomorphisms of section algebras.
* `SheafOfModules.DifferentialGradedModule.MorphismSectionData.derivedRestrictionSquare`: the
  square of derived restrictions of scalars, obtained from the naturality of `φ`.
* `SheafOfModules.DifferentialGradedModule.MorphismSectionData.baseChangeSquare`: the
  base-change square, the conjugate of that square of derived restrictions.
* `SheafOfModules.DifferentialGradedModule.DerivedPullbackSectionData.ofSectionsIso`: a derived
  pullback section datum built from the computation of the derived sections alone, its
  base-change square being the constructed one.

## Main results

* `SheafOfModules.DifferentialGradedModule.SectionData.baseChangeIsoDerivedTensor` and
  `SheafOfModules.DifferentialGradedModule.MorphismSectionData.baseChangeIsoDerivedTensor`: the
  carried base changes are derived extension of scalars.
* `SheafOfModules.DifferentialGradedModule.MorphismSectionData.structureHom_comp_restriction`:
  the naturality of `φ`, as an equality of homomorphisms of differential graded algebras.
* `SheafOfModules.DifferentialGradedModule.MorphismSectionData.baseChangeSquare_hom_counit` and
  `MorphismSectionData.unit_baseChangeSquare_hom`: the two adjoint characterizations of the
  base-change square, which determine it.

## Implementation notes

`CategoryTheory.conjugateIsoEquiv` transports an isomorphism of right adjoints to an isomorphism
of left adjoints; it reverses the direction, which is why `derivedRestrictionSquare` runs from
the composite of restrictions adjoint to `msd.baseChange V' ⋙ sd'.baseChange a'` to the one
adjoint to `sd.baseChange (F.op.map a') ⋙ msd.baseChange U'`.

## References

* [Stacks Project, Lemma 24.33.4 (Tag 0GZC)](https://stacks.math.columbia.edu/tag/0GZC)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe s t a m v u t' a' m' v' u' d e d' e'

namespace SheafOfModules.DifferentialGradedModule

/-! ### The carried base changes are derived extension of scalars -/

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {Λ : Type s} [CommRing Λ] {A : DifferentialGradedAlgebra.{t, a} R} {D : Type d}
  [Category.{e} D] {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}

/-- The derived base change along a restriction homomorphism carried by a `SectionData` is
derived extension of scalars `- ⊗^𝐋_{A(V)} A(U)`, the derived tensor product with the regular
bimodule of the restriction homomorphism: both are left adjoint to derived restriction of
scalars along it, and a left adjoint is unique up to unique isomorphism. -/
def SectionData.baseChangeIsoDerivedTensor (sd : SectionData Λ gA) {U V : Cᵒᵖ} (a : V ⟶ U) :
    sd.baseChange a ≅
      DifferentialGraded.Bimodule.derivedTensorFunctor
        (DifferentialGraded.Bimodule.regular (sd.restriction a)) :=
  Adjunction.leftAdjointUniq (sd.baseChangeAdj a)
    (DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction (sd.restriction a))

/-- The comparison of the carried base change with derived extension of scalars is the one
compatible with the units of the two adjunctions, which determines it. -/
theorem SectionData.unit_baseChangeIsoDerivedTensor (sd : SectionData Λ gA) {U V : Cᵒᵖ}
    (a : V ⟶ U) (X : _root_.DifferentialGradedModule.derivedCategory' (sd.algebra V)) :
    (sd.baseChangeAdj a).unit.app X ≫
        (_root_.DifferentialGradedModule.derivedRestriction (sd.restriction a)).map
          ((sd.baseChangeIsoDerivedTensor a).hom.app X) =
      (DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
        (sd.restriction a)).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ X

end Sections

/-! ### The base-change square of a morphism of chaotic ringed sites -/

section Pullback

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t'}}
  {Λ : Type s} [CommRing Λ] {A : DifferentialGradedAlgebra.{t, a} R}
  {A' : DifferentialGradedAlgebra.{t', a'} R'} {D : Type d} [Category.{e} D] {D' : Type d'}
  [Category.{e'} D'] {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}
  {gA' : GoodModuleData.{t', a', m', v', u', d', e'} A' D'} {F : C' ⥤ C} {sd : SectionData Λ gA}
  {sd' : SectionData Λ gA'}

/-- **The morphism section datum of a natural family `σ` of homomorphisms of the section
algebras**: its base change at `U'` is the derived tensor product with the regular bimodule of
`σ U'`, with its adjunction to derived restriction of scalars (Tag 0BYX). -/
def MorphismSectionData.ofStructureHom (F : C' ⥤ C) (sd : SectionData Λ gA)
    (sd' : SectionData Λ gA')
    (σ : ∀ U' : C'ᵒᵖ, (sd.algebra (F.op.obj U')).Hom (sd'.algebra U'))
    (hσ : ∀ {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') (x : (sd.algebra (F.op.obj V')).A),
      (σ U').toAlgebraHom ((sd.restriction (F.op.map a')).toAlgebraHom x) =
        (sd'.restriction a').toAlgebraHom ((σ V').toAlgebraHom x)) :
    MorphismSectionData F sd sd' where
  structureHom := σ
  structureHom_restriction := hσ
  baseChange U' :=
    DifferentialGraded.Bimodule.derivedTensorFunctor
      (DifferentialGraded.Bimodule.regular (σ U'))
  adj U' := DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction (σ U')

/-- The structure homomorphism at `U'` of `MorphismSectionData.ofStructureHom` is `σ U'`. -/
@[simp] theorem MorphismSectionData.ofStructureHom_structureHom (F : C' ⥤ C)
    (sd : SectionData Λ gA) (sd' : SectionData Λ gA')
    (σ : ∀ U' : C'ᵒᵖ, (sd.algebra (F.op.obj U')).Hom (sd'.algebra U')) (hσ) (U' : C'ᵒᵖ) :
    (MorphismSectionData.ofStructureHom F sd sd' σ hσ).structureHom U' = σ U' :=
  rfl

/-- The derived base change along the structure homomorphism at `U'` carried by a morphism
section datum is derived extension of scalars `- ⊗^𝐋_{A(F U')} A'(U')`: both are left adjoint to
derived restriction of scalars along the structure homomorphism. -/
def MorphismSectionData.baseChangeIsoDerivedTensor (msd : MorphismSectionData F sd sd')
    (U' : C'ᵒᵖ) :
    msd.baseChange U' ≅
      DifferentialGraded.Bimodule.derivedTensorFunctor
        (DifferentialGraded.Bimodule.regular (msd.structureHom U')) :=
  Adjunction.leftAdjointUniq (msd.adj U')
    (DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
      (msd.structureHom U'))

/-- **The naturality of `φ : g^*A → A'`, as an equality of homomorphisms of differential graded
algebras**: the structure homomorphism at `U'` after the restriction homomorphism of `A` is the
restriction homomorphism of `A'` after the structure homomorphism at `V'`. -/
theorem MorphismSectionData.structureHom_comp_restriction (msd : MorphismSectionData F sd sd')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    (msd.structureHom U').comp (sd.restriction (F.op.map a')) =
      (sd'.restriction a').comp (msd.structureHom V') :=
  DifferentialGradedAlgebra.Hom.ext_toAlgebraHom (AlgHom.ext (msd.structureHom_restriction a'))

/-- Base change along a restriction homomorphism of `A`, followed by base change along the
structure homomorphism at `U'`: the composite adjunction, whose right adjoint is derived
restriction along the structure homomorphism at `U'` followed by derived restriction along the
restriction homomorphism of `A`. -/
def MorphismSectionData.baseChangeAdjThroughA (msd : MorphismSectionData F sd sd')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    sd.baseChange (F.op.map a') ⋙ msd.baseChange U' ⊣
      _root_.DifferentialGradedModule.derivedRestriction (msd.structureHom U') ⋙
        _root_.DifferentialGradedModule.derivedRestriction (sd.restriction (F.op.map a')) :=
  (sd.baseChangeAdj (F.op.map a')).comp (msd.adj U')

/-- Base change along the structure homomorphism at `V'`, followed by base change along the
restriction homomorphism of `A'`: the composite adjunction, whose right adjoint is derived
restriction along the restriction homomorphism of `A'` followed by derived restriction along the
structure homomorphism at `V'`. -/
def MorphismSectionData.baseChangeAdjThroughA' (msd : MorphismSectionData F sd sd')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    msd.baseChange V' ⋙ sd'.baseChange a' ⊣
      _root_.DifferentialGradedModule.derivedRestriction (sd'.restriction a') ⋙
        _root_.DifferentialGradedModule.derivedRestriction (msd.structureHom V') :=
  (msd.adj V').comp (sd'.baseChangeAdj a')

/-- **The square of derived restrictions of scalars.** Derived restriction along the restriction
homomorphism of `A'` followed by derived restriction along the structure homomorphism at `V'`
agrees with derived restriction along the structure homomorphism at `U'` followed by derived
restriction along the restriction homomorphism of `A`: both are derived restriction along a
composite homomorphism of section algebras, and the two composites agree by the naturality of
`φ`. -/
def MorphismSectionData.derivedRestrictionSquare (msd : MorphismSectionData F sd sd')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    _root_.DifferentialGradedModule.derivedRestriction (sd'.restriction a') ⋙
        _root_.DifferentialGradedModule.derivedRestriction (msd.structureHom V') ≅
      _root_.DifferentialGradedModule.derivedRestriction (msd.structureHom U') ⋙
        _root_.DifferentialGradedModule.derivedRestriction (sd.restriction (F.op.map a')) :=
  _root_.DifferentialGradedModule.derivedRestrictionComp (msd.structureHom V')
      (sd'.restriction a') ≪≫
    eqToIso (congrArg _root_.DifferentialGradedModule.derivedRestriction
      (msd.structureHom_comp_restriction a').symm) ≪≫
    (_root_.DifferentialGradedModule.derivedRestrictionComp (sd.restriction (F.op.map a'))
      (msd.structureHom U')).symm

/-- **The base-change square of the morphism of chaotic ringed sites.** Base change along a
restriction homomorphism of `A` followed by base change along the structure homomorphism at `U'`
agrees with base change along the structure homomorphism at `V'` followed by base change along the
corresponding restriction homomorphism of `A'`: the isomorphism of left adjoints conjugate to
`MorphismSectionData.derivedRestrictionSquare`. -/
def MorphismSectionData.baseChangeSquare (msd : MorphismSectionData F sd sd') {U' V' : C'ᵒᵖ}
    (a' : V' ⟶ U') :
    sd.baseChange (F.op.map a') ⋙ msd.baseChange U' ≅
      msd.baseChange V' ⋙ sd'.baseChange a' :=
  (CategoryTheory.conjugateIsoEquiv (msd.baseChangeAdjThroughA' a')
    (msd.baseChangeAdjThroughA a')).symm (msd.derivedRestrictionSquare a')

/-- **The counit characterization of the base-change square**, which determines it: the square is
the unique natural transformation compatible with the square of derived restrictions and the
counits of the two composite adjunctions. -/
theorem MorphismSectionData.baseChangeSquare_hom_counit (msd : MorphismSectionData F sd sd')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (X : _root_.DifferentialGradedModule.derivedCategory' (sd'.algebra U')) :
    (sd.baseChange (F.op.map a') ⋙ msd.baseChange U').map
          ((msd.derivedRestrictionSquare a').hom.app X) ≫
        (msd.baseChangeAdjThroughA a').counit.app X =
      (msd.baseChangeSquare a').hom.app
          ((_root_.DifferentialGradedModule.derivedRestriction (sd'.restriction a') ⋙
            _root_.DifferentialGradedModule.derivedRestriction (msd.structureHom V')).obj X) ≫
        (msd.baseChangeAdjThroughA' a').counit.app X :=
  CategoryTheory.conjugateEquiv_counit_symm _ _ _ X

/-- **The unit characterization of the base-change square**: composing the unit of the composite
adjunction through `A'` with the square of derived restrictions is composing the unit of the
composite adjunction through `A` with the derived restriction of the square. -/
theorem MorphismSectionData.unit_baseChangeSquare_hom (msd : MorphismSectionData F sd sd')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (X : _root_.DifferentialGradedModule.derivedCategory' (sd.algebra (F.op.obj V'))) :
    (msd.baseChangeAdjThroughA' a').unit.app X ≫
        (msd.derivedRestrictionSquare a').hom.app
          ((msd.baseChange V' ⋙ sd'.baseChange a').obj X) =
      (msd.baseChangeAdjThroughA a').unit.app X ≫
        (_root_.DifferentialGradedModule.derivedRestriction (msd.structureHom U') ⋙
            _root_.DifferentialGradedModule.derivedRestriction
              (sd.restriction (F.op.map a'))).map
          ((msd.baseChangeSquare a').hom.app X) :=
  CategoryTheory.unit_conjugateEquiv_symm _ _ _ X

/-- **The derived pullback section datum of a computation of the derived sections**: its
base-change square is `MorphismSectionData.baseChangeSquare`, and its remaining fields are the
computation `RΓ(U', Lg^*K) ≅ RΓ(F U', K) ⊗^𝐋_{A(F U')} A'(U')` of the derived sections and its
compatibility with the derived restriction maps. -/
def DerivedPullbackSectionData.ofSectionsIso (msd : MorphismSectionData F sd sd')
    (Lg : DerivedTensorData gA gA')
    (sectionsIso : ∀ U' : C'ᵒᵖ, Lg.derived ⋙ sd'.derivedSections U' ≅
      sd.derivedSections (F.op.obj U') ⋙ msd.baseChange U')
    (hrestrict : ∀ {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') (K : D),
      (sd'.restrictionMap a').app (Lg.derived.obj K) ≫
          (_root_.DifferentialGradedModule.derivedRestriction (sd'.restriction a')).map
            ((sectionsIso U').hom.app K) =
        (sectionsIso V').hom.app K ≫
          (msd.baseChange V').map ((sd.restrictionMap (F.op.map a')).app K) ≫
          (restrictionMate msd a' (msd.baseChangeSquare a')).app
            ((sd.derivedSections (F.op.obj U')).obj K)) :
    DerivedPullbackSectionData msd Lg where
  baseChangeSquare a' := msd.baseChangeSquare a'
  sectionsIso := sectionsIso
  sectionsIso_restrictionMap := hrestrict

/-- The base-change square of `DerivedPullbackSectionData.ofSectionsIso` along `a'` is
`MorphismSectionData.baseChangeSquare`. -/
@[simp] theorem DerivedPullbackSectionData.ofSectionsIso_baseChangeSquare
    (msd : MorphismSectionData F sd sd') (Lg : DerivedTensorData gA gA') (sectionsIso) (hrestrict)
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    (DerivedPullbackSectionData.ofSectionsIso msd Lg sectionsIso hrestrict).baseChangeSquare a' =
      msd.baseChangeSquare a' :=
  rfl

/-- The sections isomorphism at `U'` of `DerivedPullbackSectionData.ofSectionsIso` is the given
`sectionsIso U'`. -/
@[simp] theorem DerivedPullbackSectionData.ofSectionsIso_sectionsIso
    (msd : MorphismSectionData F sd sd') (Lg : DerivedTensorData gA gA') (sectionsIso) (hrestrict)
    (U' : C'ᵒᵖ) :
    (DerivedPullbackSectionData.ofSectionsIso msd Lg sectionsIso hrestrict).sectionsIso U' =
      sectionsIso U' :=
  rfl

end Pullback

end SheafOfModules.DifferentialGradedModule

end
