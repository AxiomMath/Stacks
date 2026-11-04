module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Composition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of derived direct images for a morphism of ringed topoi, with nothing left over

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(ℰ), 𝒪_ℰ)` be morphisms of
ringed topoi in the sense of Stacks 01D3, part (2) — a morphism of the underlying *topoi*
together with the structure map, with no continuous functor between the underlying sites.
Stacks 0D6E asserts

`Rg_* ∘ Rf_* = R(g ∘ f)_*`

as functors `D(𝒪_𝒞) ⟶ D(𝒪_ℰ)`.

`AlgebraicGeometry.RingedToposHom.derivedPushforwardComparison_isIso` proves this under
Stacks 093Y for `f` — that degreewise `f_*` preserves K-injectivity — which is the input the
source does not have and which, for sheaves of modules, Stacks 075L records as *false* in
general.  **This file discharges that input**, so Stacks 0D6E holds for a morphism of ringed
topoi with no hypothesis beyond those that make the two categories of modules exist.

The argument is the source's and is the one
`DerivedPushforwardCompositionOnTopoi.isIso_derivedPushforwardComparison_unconditional` carries out
for a morphism of ringed *sites*: `Rf_* ⋙ Rg_*` is a right adjoint of `Lg^* ⋙ Lf^*` because each
factor is (Stacks 07A6), that composite is `L(g ∘ f)^*` (Stacks 0D6D), and `R(g ∘ f)_*` is a right
adjoint of `L(g ∘ f)^*` as well; so the two agree by uniqueness of right adjoints.  All three
inputs are now available for a `RingedToposHom` and at free universes —
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`, `derivedAdjunction_counit_fac` and
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackCompIso` — which is what
makes this file possible and is the whole of what it adds.

Uniqueness of right adjoints produces *an* isomorphism, characterized by the units of the three
adjunctions; the comparison of Stacks 0D6E is characterized instead by the universal property of
`R(g ∘ f)_*`.  Identifying the two is the abstract transposition argument
`Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions`, already
in the tree for the ringed-space analogue Stacks 0D5T, and its five inputs are supplied here.

## Main definitions

* `derivedPushforwardCompIsoOfAdjoints`: the composition isomorphism
  `Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*` obtained from uniqueness of right adjoints.

## Main results

* `pullbackModulesCompIso_inv_app_comp_counit`: the two composition isomorphisms of Stacks 03D8
  agree on sheaves of modules.  This is the one input of the transposition argument that is not
  formal, and it is the mates lemma `CategoryTheory.conjugateEquiv_counit_symm` read through
  `AlgebraicGeometry.RingedToposHom.conjugateEquiv_pullbackModulesCompIso_hom`.
* `derivedPushforwardCompUnit_comp_derivedPushforwardCompIsoOfAdjoints`: the canonical
  comparison of Stacks 0D6E followed by `derivedPushforwardCompIsoOfAdjoints` is the comparison
  of `R(g ∘ f)_*`.
* `isIso_derivedPushforwardUnit_app_pushforwardMapHomotopy`: the unit of `Rg_*` is invertible at
  the degreewise direct image along `f` of a K-injective complex — the condition
  `AlgebraicGeometry.RingedToposHom.PushforwardComputesDerived`, at the canonical derived
  pushforwards.
* `quasiIso_mapHomotopyCategory_pushforward_of_isKInjective`: the same with no derived category
  in the statement, which is what lets it hold for every choice of derived categories.
* `isIso_app_pushforwardMapHomotopy_of_isKInjective`: that condition for an arbitrary
  presentation of an arbitrary right derived direct image along `g`, and
  `isIso_derivedPushforwardComparison_unconditional`: **Stacks 0D6E** for a morphism of ringed
  topoi, with no hypothesis on either morphism.

## Implementation notes

*Why the mates input takes this shape.*  For a morphism of ringed *sites* the pullback of
sheaves of modules is Mathlib's `SheafOfModules.pullback`, an abstract left adjoint, and its
composition isomorphism is built by `CategoryTheory.Adjunction.leftAdjointCompIso`, whose
defining property is `CategoryTheory.conjugateEquiv_counit_symm` on the nose.  For a morphism of
ringed topoi the composition isomorphism is
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`, built by
`CategoryTheory.Adjunction.leftAdjointUniq` out of `ofNatIsoRight` of the direct-image
compositor; its mate is already computed, as
`AlgebraicGeometry.RingedToposHom.conjugateEquiv_pullbackModulesCompIso_hom`, but for the *hom*
of the comparison, while the degreewise input wants the *inv*.  Mathlib's
`CategoryTheory.conjugateIsoEquiv` bridges the two: conjugation carries an isomorphism to an
isomorphism, with the inverse conjugated by the two adjunctions in the other order, so the
inverse of the conjugate of the hom *is* the conjugate of the inv.

*Crossing the choices of derived category.*  Everything mentioning
`Stacks.Cohomology.DerivedPushforward.derivedPushforward` runs at
`CategoryTheory.HasDerivedCategory.standard`, since that is what Stacks 0D6D, 07A6 and 0FPI fix
for a `RingedToposHom` in this tree, and the attribute is file-local so it is repeated here.  The
passage to an arbitrary `HasDerivedCategory` instance and an arbitrary presentation goes through
`quasiIso_mapHomotopyCategory_pushforward_of_isKInjective`, which mentions no derived category at
all.

*The Grothendieck abelianness hypotheses.*  `IsGrothendieckAbelian` of the modules of the source
and of the middle ringed topos is carried, because at free universes it is not synthesizable from
smallness of the site: it is what makes K-injective resolutions exist there, and it is the
hypothesis of Stacks 07A5 and of Stacks 07A6 as `PullbackAdjunction` now states it.  Nothing is
asked of the *target*: the target of a composite only receives.

*What the statement is not.*  `AlgebraicGeometry.RingedToposHom.pullbackModules` is not
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, so this is a different statement from
`DerivedPushforwardCompositionOnTopoi.isIso_derivedPushforwardComparison_unconditional` and not
a universe generalization of it; the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackOfToposHom.lean`
record why the two developments are not one.

## References

* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

namespace Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom

universe v u w v' u' w' v'' u'' w'' dX dY dZ

noncomputable section

/-! ### The two composition isomorphisms of Stacks 03D8 agree -/

section Degreewise

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

omit [HasSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The mate of the inverse of the pullback compositor is the direct-image compositor.**
`AlgebraicGeometry.RingedToposHom.conjugateEquiv_pullbackModulesCompIso_hom` computes the mate of
the *hom* of the pullback compositor; conjugation carries an isomorphism to an isomorphism
(`CategoryTheory.conjugateIsoEquiv`), with the inverse conjugated by the two adjunctions taken in
the other order, so the inverse of that mate is the mate of the *inv*. -/
theorem conjugateEquiv_symm_pushforwardModulesCompIso_hom :
    (conjugateEquiv (pullbackAdjPushforwardModules (g.comp f))
        ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))).symm
        (pushforwardModulesCompIso f g).hom =
      (pullbackModulesCompIso f g).inv := by
  have he : conjugateIsoEquiv ((pullbackAdjPushforwardModules g).comp
        (pullbackAdjPushforwardModules f)) (pullbackAdjPushforwardModules (g.comp f))
        (pullbackModulesCompIso f g) =
      (pushforwardModulesCompIso f g).symm :=
    Iso.ext (conjugateEquiv_pullbackModulesCompIso_hom f g)
  exact (Equiv.symm_apply_eq _).2 (congrArg Iso.inv he).symm

omit [HasSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The two composition isomorphisms of Stacks 03D8 agree, on sheaves of modules.**  Reading
the direct-image compositor through `g^*` and the counit of `g`, then through `f^*` and the
counit of `f`, is the same as reading the pullback compositor through the counit of `g ∘ f`.

This is the mates lemma `CategoryTheory.conjugateEquiv_counit_symm` at the direct-image
compositor, whose mate `conjugateEquiv_symm_pushforwardModulesCompIso_hom` identifies with the
inverse of the pullback compositor. -/
theorem pullbackModulesCompIso_inv_app_comp_counit (A : X.Modules) :
    (f.toModulesHom.pullbackModules).map ((g.toModulesHom.pullbackModules).map
            ((pushforwardModulesCompIso f g).hom.app A) ≫
          (pullbackAdjPushforwardModules g).counit.app ((pushforwardModules f).obj A)) ≫
        (pullbackAdjPushforwardModules f).counit.app A =
      (pullbackModulesCompIso f g).inv.app ((pushforwardModules (g.comp f)).obj A) ≫
        (pullbackAdjPushforwardModules (g.comp f)).counit.app A := by
  have h := CategoryTheory.conjugateEquiv_counit_symm
    (pullbackAdjPushforwardModules (g.comp f))
    ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))
    (pushforwardModulesCompIso f g).hom A
  rw [conjugateEquiv_symm_pushforwardModulesCompIso_hom] at h
  simpa [Adjunction.comp_counit_app] using h

omit [HasSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- `pullbackModulesCompIso_inv_app_comp_counit` on cochain complexes.  Every map in sight is
degreewise, so the identity holds degree by degree. -/
theorem mapHomologicalComplex_pullbackModulesComp_inv_app_comp_counit
    (K : CochainComplex X.Modules ℤ) :
    ((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((g.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Functor.mapHomologicalComplexCompIso
                (pushforwardModulesCompIso f g).symm (ComplexShape.up ℤ)).inv.app K) ≫
            (Adjunction.mapHomologicalComplexAdjunction
                (pullbackAdjPushforwardModules g) (ComplexShape.up ℤ)).counit.app
              (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (Adjunction.mapHomologicalComplexAdjunction
            (pullbackAdjPushforwardModules f) (ComplexShape.up ℤ)).counit.app K =
      (Functor.mapHomologicalComplexCompIso
            (pullbackModulesCompIso f g).symm (ComplexShape.up ℤ)).hom.app
          ((((pushforwardModules (g.comp f))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (Adjunction.mapHomologicalComplexAdjunction
            (pullbackAdjPushforwardModules (g.comp f)) (ComplexShape.up ℤ)).counit.app K := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact pullbackModulesCompIso_inv_app_comp_counit f g (K.X n)

omit [HasSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- `pullbackModulesCompIso_inv_app_comp_counit` on the unbounded homotopy categories.  This is
the one input of
`Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions` that is
not formal. -/
theorem mapHomotopyCategory_pullbackModulesComp_inv_app_comp_counit
    (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (pullbackMapHomotopy f).map
          ((pullbackMapHomotopy g).map
              ((Functor.mapHomotopyCategoryCompIso
                (pushforwardModulesCompIso f g).symm (ComplexShape.up ℤ)).inv.app K) ≫
            (pullbackAdjPushforwardMapHomotopy g).counit.app
              ((pushforwardMapHomotopy f).obj K)) ≫
        (pullbackAdjPushforwardMapHomotopy f).counit.app K =
      (pullbackMapHomotopyCompIso f g).hom.app
          ((pushforwardMapHomotopy (g.comp f)).obj K) ≫
        (pullbackAdjPushforwardMapHomotopy (g.comp f)).counit.app K := by
  obtain ⟨K⟩ := K
  exact congrArg (HomotopyCategory.quotient _ _).map
    (mapHomologicalComplex_pullbackModulesComp_inv_app_comp_counit f g K)

/-- The comparison `derivedPushforwardCompUnit` is invertible at a complex where the comparison
of `f` is, exactly when the comparison of `g` is invertible at the degreewise direct image. -/
private theorem isIso_derivedPushforwardCompUnit_app_iff
    [HasDerivedCategory.{dX} X.Modules] [HasDerivedCategory.{dY} Y.Modules]
    [HasDerivedCategory.{dZ} Z.Modules]
    (Rf : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
    (Rg : DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules)
    (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
    (I : CochainComplex X.Modules ℤ)
    [IsIso (αf.app ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))] :
    IsIso ((derivedPushforwardCompUnit f g Rf Rg αf αg).app
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) ↔
      IsIso (αg.app ((pushforwardMapHomotopy f).obj
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := by
  simp only [derivedPushforwardCompUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

end Degreewise

/-! ### Invertibility of a comparison, read on complexes -/

section Resolution

variable {Y : RingedTopos.{v', u', w'}} {Z : RingedTopos.{v'', u'', w''}}
  [Y.J.HasSheafCompose (forget RingCat.{w'})] [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [IsGrothendieckAbelian.{w'} Y.Modules]
  [HasDerivedCategory.{dY} Y.Modules] [HasDerivedCategory.{dZ} Z.Modules]
  (g : RingedToposHom Y Z)
  (Rg : DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules)
  (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)

omit [Z.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **Invertibility of a comparison, read on complexes.**  For a right derived functor of
degreewise direct image along `g`, the comparison is invertible at an object `M` of `K(𝒪_𝒟)`
exactly when degreewise `g_*` carries one K-injective resolution of `M` to a quasi-isomorphism.

The right-hand side mentions neither the presentation `(Rg, αg)` nor the chosen derived
categories, which is what lets a statement proved for one choice be transported to any other.
The proof is the naturality square of `αg` along the resolution: its other three edges are
invertible, the comparison at a K-injective complex by Stacks 070K and the image of the
resolution because localization inverts quasi-isomorphisms. -/
theorem isIso_app_iff_quasiIso_pushforwardMapHomotopy
    [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))]
    (M : HomotopyCategory Y.Modules (ComplexShape.up ℤ))
    (J : CochainComplex Y.Modules ℤ) (hJ : J.IsKInjective)
    (s : M ⟶ (HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).obj J)
    (hs : HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ) s) :
    IsIso (αg.app M) ↔
      HomotopyCategory.quasiIso Z.Modules (ComplexShape.up ℤ)
        ((pushforwardMapHomotopy g).map s) := by
  have hnat := αg.naturality s
  dsimp only [Functor.comp_map] at hnat
  have := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    (pushforwardToDerivedCategory g) DerivedCategory.Qh Rg αg J hJ
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)) s hs
  rw [← DerivedCategory.isIso_Qh_map_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h
    have : IsIso (DerivedCategory.Qh.map ((pushforwardMapHomotopy g).map s) ≫
        αg.app ((HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).obj J)) := by
      rw [hnat]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (αg.app _)
  · have := h
    have : IsIso (αg.app M ≫ Rg.map (DerivedCategory.Qh.map s)) := by
      rw [← hnat]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Rg.map (DerivedCategory.Qh.map s))

end Resolution

/-! ### The canonical derived pushforwards -/

section Canonical

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]
  [IsGrothendieckAbelian.{w} X.Modules] [IsGrothendieckAbelian.{w'} Y.Modules]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

/-- The canonical comparison `f_* ⟶ Rf_*` of Stacks 07A5, at the standard derived category. -/
abbrev derivedPushforwardUnit :
    pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ derivedPushforward f :=
  (pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh (sourceQuasiIso X)

/-- The composite of the two derived adjunctions of Stacks 07A6, transported along the derived
pullback composition isomorphism of Stacks 0D6D: an adjunction `L(g ∘ f)^* ⊣ Rf_* ⋙ Rg_*`. -/
def derivedCompAdjunction :
    derivedPullback (g.comp f) ⊣ derivedPushforward f ⋙ derivedPushforward g :=
  ((derivedAdjunction g).comp (derivedAdjunction f)).ofNatIsoLeft
    (derivedPullbackCompIso f g)

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*` for the canonical derived
pushforwards.

Both functors are right adjoints of `L(g ∘ f)^*`: the composite of the two derived adjunctions
of Stacks 07A6 is an adjunction `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`, and Stacks 0D6D identifies its
left side with `L(g ∘ f)^*`.  The isomorphism is the uniqueness isomorphism of right adjoints,
which is the construction the source's proof of Stacks 0D6E uses. -/
def derivedPushforwardCompIsoOfAdjoints :
    derivedPushforward f ⋙ derivedPushforward g ≅ derivedPushforward (g.comp f) :=
  Adjunction.rightAdjointUniq (derivedCompAdjunction f g) (derivedAdjunction (g.comp f))

/-- The derived adjunction for a composite is the composite adjunction, transported along the
composition isomorphisms for derived pullback and derived pushforward.

Two adjunctions between the same pair of functors agree as soon as their units do, and the unit
of the uniqueness isomorphism of right adjoints is defined so that they do. -/
theorem derivedCompAdjunction_ofNatIsoRight :
    (derivedCompAdjunction f g).ofNatIsoRight
        (derivedPushforwardCompIsoOfAdjoints f g) =
      derivedAdjunction (g.comp f) :=
  Adjunction.ext (Adjunction.unit_rightAdjointUniq_hom _ _)

/-- Transposition under the derived adjunction for a composite agrees with successive
transposition under the two derived adjunctions and the canonical composition maps.  This is the
composition coherence needed for vertical pasting of mates, and the one input of
`Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions` that is
about `derivedPushforwardCompIsoOfAdjoints` itself. -/
theorem derivedAdjunction_comp_homEquiv
    (M : DerivedCategory Z.Modules) (K : DerivedCategory X.Modules)
    (φ : (derivedPullback (g.comp f)).obj M ⟶ K) :
    (derivedAdjunction g).homEquiv _ _
          ((derivedAdjunction f).homEquiv _ _
            ((derivedPullbackCompIso f g).hom.app M ≫ φ)) ≫
        (derivedPushforwardCompIsoOfAdjoints f g).hom.app K =
      (derivedAdjunction (g.comp f)).homEquiv M K φ := by
  have h := congrArg (fun a => a.homEquiv M K φ)
    (derivedCompAdjunction_ofNatIsoRight f g)
  simpa only [derivedCompAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv, Equiv.trans_apply] using h

/-- **The two composition isomorphisms for derived pushforward agree.**  The comparison from
degreewise pushforward along `g ∘ f` to `Rf_* ⋙ Rg_*` of Stacks 0D6E, followed by the uniqueness
isomorphism `derivedPushforwardCompIsoOfAdjoints`, is the canonical comparison of
`R(g ∘ f)_*`.

Both maps `R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*` are therefore the same, and so the first is invertible.
The chase is the abstract
`Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions`, whose
inputs are Stacks 0FPI for each of the three morphisms, Stacks 0D6D in its characterized form,
the transposition coherence above, and the degreewise agreement of the two composition
isomorphisms. -/
theorem derivedPushforwardCompUnit_comp_derivedPushforwardCompIsoOfAdjoints
    (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (derivedPushforwardCompUnit f g (derivedPushforward f) (derivedPushforward g)
            (derivedPushforwardUnit f) (derivedPushforwardUnit g)).app K ≫
        (derivedPushforwardCompIsoOfAdjoints f g).hom.app (DerivedCategory.Qh.obj K) =
      (derivedPushforwardUnit (g.comp f)).app K :=
  DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions
    (pullbackAdjPushforwardMapHomotopy f) (pullbackAdjPushforwardMapHomotopy g)
    (pullbackAdjPushforwardMapHomotopy (g.comp f))
    (derivedAdjunction f) (derivedAdjunction g) (derivedAdjunction (g.comp f))
    (Functor.mapHomotopyCategoryCompIso
      (pushforwardModulesCompIso f g).symm (ComplexShape.up ℤ))
    (pullbackMapHomotopyCompIso f g)
    (derivedPullbackCompIso f g)
    (derivedPushforwardCompIsoOfAdjoints f g)
    (derivedAdjunction_counit_fac f) (derivedAdjunction_counit_fac g)
    (derivedAdjunction_counit_fac (g.comp f))
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f g)
    (derivedAdjunction_comp_homEquiv f g)
    (mapHomotopyCategory_pullbackModulesComp_inv_app_comp_counit f g) K

/-- The composite `Rf_* ⋙ Rg_*`, with the comparison `derivedPushforwardCompUnit`, is a right
derived functor of degreewise pushforward along `g ∘ f`: it is `R(g ∘ f)_*` read through
`derivedPushforwardCompIsoOfAdjoints`. -/
theorem isRightDerivedFunctor_comp_canonical :
    (derivedPushforward f ⋙ derivedPushforward g).IsRightDerivedFunctor
      (derivedPushforwardCompUnit f g (derivedPushforward f) (derivedPushforward g)
        (derivedPushforwardUnit f) (derivedPushforwardUnit g))
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
  refine (Functor.isRightDerivedFunctor_iff_of_iso (derivedPushforwardUnit (g.comp f)) _ _
    (derivedPushforwardCompIsoOfAdjoints f g).symm ?_).1 inferInstance
  refine NatTrans.ext (funext fun K => ?_)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom]
  rw [← derivedPushforwardCompUnit_comp_derivedPushforwardCompIsoOfAdjoints f g K,
    Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- **The unit of `Rg_*` is invertible at the degreewise direct image of a K-injective
complex**, for the canonical derived pushforwards.  This is the hypothesis that the whole of
Stacks 0D6E was reduced to, now discharged at the standard model.

The comparison of `Rf_* ⋙ Rg_*` is invertible at a K-injective complex because
`isRightDerivedFunctor_comp_canonical` exhibits the composite as a right derived functor; of its
three factors the first is the image of an isomorphism and the third is `Rg_*` applied to the
comparison of `Rf_*` at a K-injective complex, so the middle one — which is the unit of `Rg_*`
at `f_*I` — is invertible too. -/
theorem isIso_derivedPushforwardUnit_app_pushforwardMapHomotopy
    (I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedPushforwardUnit g).app ((pushforwardMapHomotopy f).obj
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := by
  have := isRightDerivedFunctor_comp_canonical f g
  have h := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    (pushforwardToDerivedCategory (g.comp f)) DerivedCategory.Qh
    (derivedPushforward f ⋙ derivedPushforward g)
    (derivedPushforwardCompUnit f g (derivedPushforward f) (derivedPushforward g)
      (derivedPushforwardUnit f) (derivedPushforwardUnit g)) I hI
  have := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
      (pushforwardToDerivedCategory f) DerivedCategory.Qh (derivedPushforward f)
      (derivedPushforwardUnit f) I hI
  exact (isIso_derivedPushforwardCompUnit_app_iff f g _ _ _ _ _).1 h

/-- **The composition formula, with no derived category in the statement.**  If `I` is a
K-injective complex of `𝒪_𝒞`-modules and `s` is a quasi-isomorphism from `f_* I` to a
K-injective complex of `𝒪_𝒟`-modules, then `g_* s` is a quasi-isomorphism.

This is `isIso_derivedPushforwardUnit_app_pushforwardMapHomotopy` read through
`isIso_app_iff_quasiIso_pushforwardMapHomotopy`.  Because it mentions no derived category, it is
the form in which the result holds for *every* choice of derived categories. -/
theorem quasiIso_mapHomotopyCategory_pushforward_of_isKInjective
    (I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective)
    (J : CochainComplex Y.Modules ℤ) (hJ : J.IsKInjective)
    (s : (pushforwardMapHomotopy f).obj
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I) ⟶
        (HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).obj J)
    (hs : HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ) s) :
    HomotopyCategory.quasiIso Z.Modules (ComplexShape.up ℤ)
      ((pushforwardMapHomotopy g).map s) :=
  (isIso_app_iff_quasiIso_pushforwardMapHomotopy g (derivedPushforward g)
    (derivedPushforwardUnit g) _ J hJ s hs).1
    (isIso_derivedPushforwardUnit_app_pushforwardMapHomotopy f g I hI)

end Canonical

/-! ### Stacks 0D6E for every presentation -/

section General

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]
  [IsGrothendieckAbelian.{w} X.Modules] [IsGrothendieckAbelian.{w'} Y.Modules]
  [HasDerivedCategory.{dX} X.Modules] [HasDerivedCategory.{dY} Y.Modules]
  [HasDerivedCategory.{dZ} Z.Modules]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
  (Rf : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
  (Rg : DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules)
  (Rh : DerivedCategory X.Modules ⥤ DerivedCategory Z.Modules)
  (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
  (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
  (αh : pushforwardToDerivedCategory (g.comp f) ⟶ DerivedCategory.Qh ⋙ Rh)

omit [HasDerivedCategory.{dX} X.Modules] in
/-- **The hypothesis of Stacks 0D6E holds unconditionally for a morphism of ringed topoi.**
Degreewise direct image along `f` carries every K-injective complex of `𝒪_𝒞`-modules to a
complex computing any derived direct image along `g`, for every choice of derived categories and
every presentation of that derived direct image.

This is the condition
`AlgebraicGeometry.RingedToposHom.PushforwardComputesDerived f g Rg αg`, written out so that it
can be stated before that definition is made.

A K-injective resolution of `f_* I` exists, and
`quasiIso_mapHomotopyCategory_pushforward_of_isKInjective` says that `g_*` carries it to a
quasi-isomorphism; `isIso_app_iff_quasiIso_pushforwardMapHomotopy` turns that back into
invertibility of the comparison. -/
theorem isIso_app_pushforwardMapHomotopy_of_isKInjective
    [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))] :
    ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
      IsIso (αg.app ((pushforwardMapHomotopy f).obj
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := by
  intro I hI
  obtain ⟨J, s, hJ, hs⟩ :=
    Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian.{w'} Y.Modules
      (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have hmem : HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).map s) := by
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact (isIso_app_iff_quasiIso_pushforwardMapHomotopy.{v', u', w', v'', u'', w'', dY, dZ}
      g Rg αg _ J hJ _ hmem).2
    (quasiIso_mapHomotopyCategory_pushforward_of_isKInjective f g I hI J hJ _ hmem)

/-- **Stacks 0D6E for a morphism of ringed topoi.**  For composable morphisms of ringed topoi
`f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(ℰ), 𝒪_ℰ)`, the canonical
comparison from a derived direct image along `g ∘ f` to the composite of the derived direct
images along `f` and `g` is an isomorphism, so `Rg_* ∘ Rf_* = R(g ∘ f)_*` as functors
`D(𝒪_𝒞) ⟶ D(𝒪_ℰ)`.

There is **no hypothesis on either morphism**: the geometric datum is the two-field morphism of
ringed topoi of Stacks 01D3, part (2), with no continuous functor between the underlying sites,
and the condition that
`AlgebraicGeometry.RingedToposHom.derivedPushforwardComparison_isIso` carries — Stacks 093Y for
`f`, which at module coefficients Stacks 075L records as false in general — is discharged by
`isIso_app_pushforwardMapHomotopy_of_isKInjective`. -/
@[stacks 0D6E "for a morphism of ringed topoi in the two-field sense of Tag 01D3, part (2) --
a morphism of the underlying topoi together with the structure map, with no continuous functor
between the underlying sites -- and with no hypothesis on either morphism; the three universes
of each of the three ringed topoi are free and unrelated"]
theorem isIso_derivedPushforwardComparison_unconditional
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))]
    [Rh.IsRightDerivedFunctor αh (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    IsIso (derivedPushforwardComparison f g Rf Rg Rh αf αg αh) := by
  refine (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc Rh αh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) (Rf ⋙ Rg)
    (derivedPushforwardCompUnit f g Rf Rg αf αg)).1 ?_
  refine Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ _ _ _ fun I hI ↦ ?_
  have h₂ := isIso_app_pushforwardMapHomotopy_of_isKInjective f g Rg αg I hI
  have := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    (pushforwardToDerivedCategory f) DerivedCategory.Qh Rf αf I hI
  exact (isIso_derivedPushforwardCompUnit_app_iff f g Rf Rg αf αg I).2 h₂

end General

end

end Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom

end
