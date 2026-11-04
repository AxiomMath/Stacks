module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonInDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationOnResolutions

/-!
# Localization of higher direct images on an injective resolution, in every degree

`StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationOnResolutions` proves the
  resolution clause of Stacks 01E5 in
positive degree, where `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso` is
the composite of the inverses of its two engines
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` and
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`.  In degree zero that isomorphism is
instead `higherDirectImageRestrictIsoZero`, the underived comparison read through
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` on both sides, which is what makes the
degree-zero clause of the tag true.

This file closes the gap between the two descriptions.  The degree-zero normalizations of the
two engines are `StacksDraft.Ch20.Sec14.DerivedCompZero`, and together they say exactly that
the composite of the two engines is the underived comparison conjugated by the canonical maps
`CategoryTheory.Functor.toRightDerivedZero`; cancelling those canonical maps against
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` identifies the degree-zero branch of
`higherDirectImageRestrictIso` with the same composite of engines that the positive-degree
branch is.  The resolution clause then follows in degree zero from the very same abstract
statement `compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_app`, which was already
proved for an arbitrary degree.

## Main results

* `rightDerivedCompIso_comp_compRightDerivedNatIso_zero` and
  `compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_zero`: in degree zero the composite
  of the two engines is the underived comparison, read through the two canonical isomorphisms
  of left exact functors with their zeroth right derived functors.
* `higherDirectImageRestrictIso_zero_hom_app`: the degree-zero analogue of
  `higherDirectImageRestrictIso_succ_hom_app`.
* `higherDirectImageRestrictIsoSucc_zero`: the two branches of `higherDirectImageRestrictIso`
  agree in degree zero, so `higherDirectImageRestrictIso_eq_succ` removes the case distinction
  in its definition altogether.  A clause proved about `higherDirectImageRestrictIsoSucc` for
  every `p` is therefore a clause about the tag-carrying comparison for every `p`, degree zero
  included, rather than in degree `p + 1` only.
* `higherDirectImageRestrictIso_injectiveResolution_zero`: the resolution clause of Stacks 01E5
  in degree zero.
* `higherDirectImageRestrictIso_injectiveResolution`: the clause in every degree.

## Implementation notes

The cancellation is the standard move for a degree-zero normalization: precompose the
degree-zero normalizations with `CategoryTheory.Functor.rightDerivedZeroIsoSelf` whiskered by
the outer functor and use `CategoryTheory.Functor.rightDerivedZeroIsoSelf_hom_inv_id`.  It is
done at the level of natural transformations rather than pointwise, because that is the shape
of the two normalizations.

Nothing here touches the junction between
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` and
`CategoryTheory.HomologicalComplex.homologyMap`, across which `Category.assoc` cannot be
rewritten; that difficulty is confined to `StacksDraft.Ch20.Sec14.DerivedCompTransport` and
`StacksDraft.Ch20.Sec14.DerivedCompZero`, whose statements are reached here only as black
boxes.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedCompTransport Stacks.Cohomology.ModuleComparison

universe u

namespace Stacks.Cohomology.HigherDirectImage

/-! ### The composite of the two engines in degree zero -/

section Abstract

variable {C : Type*} {D : Type*} {B : Type*} {E : Type*}
  [Category* C] [Category* D] [Category* B] [Category* E]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D] [HasInjectiveResolutions D]
  [Abelian B] [Abelian E]
  (L : C ⥤ D) (G : D ⥤ E) (P : C ⥤ B) (R : B ⥤ E)
  [L.Additive] [G.Additive] [P.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteLimits P] [R.PreservesHomology]
  (ε : L ⋙ G ≅ P ⋙ R)

/-- **The composite of the two engines of the comparison, in degree zero.**  For `L` exact and
preserving injective objects, `G` and `P` left exact, `R` exact and `ε : L ⋙ G ≅ P ⋙ R`, the
composite `P.rightDerived 0 ⋙ R ≅ (L ⋙ G).rightDerived 0 ≅ L ⋙ G.rightDerived 0` is the
inverse of `ε` read through the canonical isomorphisms of `G` and `P` with their zeroth right
derived functors.

Both engines carry `CategoryTheory.Functor.toRightDerivedZero` to
`CategoryTheory.Functor.toRightDerivedZero`, by `rightDerivedCompIso_zero` and
`compRightDerivedNatIso_zero`; since `P` is left exact its canonical map is invertible, and
cancelling it leaves the displayed equality. -/
theorem rightDerivedCompIso_comp_compRightDerivedNatIso_zero :
    (rightDerivedCompIso P R (L ⋙ G) ε.symm 0).hom ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G 0).hom =
      (Functor.isoWhiskerLeft L G.rightDerivedZeroIsoSelf ≪≫ ε ≪≫
        Functor.isoWhiskerRight P.rightDerivedZeroIsoSelf.symm R).inv :=
  calc (rightDerivedCompIso P R (L ⋙ G) ε.symm 0).hom ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G 0).hom
      = (Functor.whiskerRight P.rightDerivedZeroIsoSelf.hom R ≫
            Functor.whiskerRight P.toRightDerivedZero R) ≫
          (rightDerivedCompIso P R (L ⋙ G) ε.symm 0).hom ≫
            (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G 0).hom := by
        rw [← Functor.whiskerRight_comp, Functor.rightDerivedZeroIsoSelf_hom_inv_id,
          Functor.whiskerRight_id', Category.id_comp]
    _ = Functor.whiskerRight P.rightDerivedZeroIsoSelf.hom R ≫
          (Functor.whiskerRight P.toRightDerivedZero R ≫
            (rightDerivedCompIso P R (L ⋙ G) ε.symm 0).hom) ≫
            (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G 0).hom := by
        simp only [Category.assoc]
    _ = Functor.whiskerRight P.rightDerivedZeroIsoSelf.hom R ≫
          (ε.inv ≫ (L ⋙ G).toRightDerivedZero) ≫
            (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G 0).hom := by
        rw [rightDerivedCompIso_zero P R (L ⋙ G) ε.symm]
        rfl
    _ = Functor.whiskerRight P.rightDerivedZeroIsoSelf.hom R ≫ ε.inv ≫
          ((L ⋙ G).toRightDerivedZero ≫
            (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G 0).hom) := by
        simp only [Category.assoc]
    _ = Functor.whiskerRight P.rightDerivedZeroIsoSelf.hom R ≫ ε.inv ≫
          Functor.whiskerLeft L G.toRightDerivedZero := by
        rw [compRightDerivedNatIso_zero L G]
    _ = _ := by
        simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
          Iso.symm_inv, Functor.rightDerivedZeroIsoSelf_inv, Category.assoc]

/-- **The degree-zero normalized comparison is the composite of the inverses of the two
engines.**  This is `rightDerivedCompIso_comp_compRightDerivedNatIso_zero` inverted: it puts
the degree-zero comparison into the shape in which
`compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_app` computes it on an arbitrary
injective resolution. -/
theorem compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_zero :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G 0).inv ≫
        (rightDerivedCompIso P R (L ⋙ G) ε.symm 0).inv =
      (Functor.isoWhiskerLeft L G.rightDerivedZeroIsoSelf ≪≫ ε ≪≫
        Functor.isoWhiskerRight P.rightDerivedZeroIsoSelf.symm R).hom := by
  have h : rightDerivedCompIso P R (L ⋙ G) ε.symm 0 ≪≫
      Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G 0 =
      (Functor.isoWhiskerLeft L G.rightDerivedZeroIsoSelf ≪≫ ε ≪≫
        Functor.isoWhiskerRight P.rightDerivedZeroIsoSelf.symm R).symm :=
    Iso.ext (rightDerivedCompIso_comp_compRightDerivedNatIso_zero L G P R ε)
  exact congrArg Iso.inv h

end Abstract

/-! ### Stacks 01E5 on an arbitrary injective resolution, in every degree -/

section Restriction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)

/-- In degree zero, `higherDirectImageRestrictIso` — defined there as the underived comparison
read through `CategoryTheory.Functor.rightDerivedZeroIsoSelf` on both sides — is also the
composite of the inverses of the two engines of its positive-degree branch.  This is the
degree-zero analogue of `higherDirectImageRestrictIso_succ_hom_app`, and unlike it, it is not
`rfl`. -/
theorem higherDirectImageRestrictIso_zero_hom_app (M : SheafOfModules.{u} (structureSheafRing X)) :
    (higherDirectImageRestrictIso f V 0).hom.app M =
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (moduleRestriction X
        (preimageOpen f V))
          (modulePushforward (restrictedMorphism f V)) 0).inv.app M ≫
        (rightDerivedCompIso (modulePushforward f) (moduleRestriction Y V)
          (moduleRestriction X (preimageOpen f V) ⋙
            modulePushforward (restrictedMorphism f V))
          (modulePushforwardRestrictIso f V).symm 0).inv.app M := by
  have h := compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_zero
    (C := SheafOfModules.{u} (structureSheafRing X))
    (moduleRestriction X (preimageOpen f V))
    (modulePushforward (restrictedMorphism f V))
    (modulePushforward f) (moduleRestriction Y V) (modulePushforwardRestrictIso f V)
  exact (congrArg (fun α => NatTrans.app α M) h).symm

/-- **The two branches of `higherDirectImageRestrictIso` agree in degree zero.**  The
normalized degree-zero comparison `higherDirectImageRestrictIsoZero` is the positive-degree
construction `higherDirectImageRestrictIsoSucc` evaluated at `p = 0`.  So
`higherDirectImageRestrictIso` is `higherDirectImageRestrictIsoSucc` in *every* degree, and a
statement proved about the latter for all `p` is a statement about the tag-carrying comparison
for all `p` — see `higherDirectImageRestrictIso_eq_succ`.

This is `compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_zero`, the degree-zero
normalization of the composite of the two engines, read in the vocabulary of the two
constructions; `higherDirectImageRestrictIso_zero_hom_app` is its pointwise form. -/
theorem higherDirectImageRestrictIsoSucc_zero :
    higherDirectImageRestrictIsoSucc f V 0 = higherDirectImageRestrictIsoZero f V :=
  Iso.ext (NatTrans.ext (funext fun M => (higherDirectImageRestrictIso_zero_hom_app f V M).symm))

/-- **Stacks 01E5 in every degree is its positive-degree branch.**  `higherDirectImageRestrictIso`
is defined by cases on the degree, the degree-zero branch being the normalized comparison; by
`higherDirectImageRestrictIsoSucc_zero` the two branches agree there, so the case distinction can
be removed.  This is what lets a clause proved for `higherDirectImageRestrictIsoSucc` at every
`p` be read off for the comparison that carries the tag at every `p`, degree zero included. -/
theorem higherDirectImageRestrictIso_eq_succ (p : ℕ) :
    higherDirectImageRestrictIso f V p = higherDirectImageRestrictIsoSucc f V p := by
  cases p with
  | zero => exact (higherDirectImageRestrictIsoSucc_zero f V).symm
  | succ n => rfl

/-- **Stacks 01E5, compatibility with injective resolutions, in degree zero.**  The
degree-zero branch of `higherDirectImageRestrictIso` is computed on an arbitrary triple
consisting of an injective resolution `I` of `M`, an injective resolution `J` of the
restriction of `M`, and a comparison `φ` of resolutions descending the identity.

With `higherDirectImageRestrictIso_zero_hom_app` in hand this is the degree-zero case of the
abstract statement `compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_app`, which was
already proved in an arbitrary degree. -/
theorem higherDirectImageRestrictIso_injectiveResolution_zero
    (M : SheafOfModules.{u} (structureSheafRing X)) (I : InjectiveResolution M)
    (J : InjectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M))
    (φ : J.cocomplex ⟶
      ((moduleRestriction X (preimageOpen f V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 =
      (moduleRestriction X (preimageOpen f V)).map (I.ι.f 0)) :
    (higherDirectImageRestrictIso f V 0).hom.app M ≫
        (moduleRestriction Y V).map
          (I.isoRightDerivedObj (modulePushforward f) 0).hom =
      (J.isoRightDerivedObj (modulePushforward (restrictedMorphism f V)) 0).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) 0).map
          (((modulePushforward (restrictedMorphism f V)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ) ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) 0).map
          (((modulePushforwardRestrictIso f V).hom.mapHomologicalComplex
            (ComplexShape.up ℕ)).app I.cocomplex) ≫
        (((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).sc 0).mapHomologyIso (moduleRestriction Y V)).hom := by
  rw [higherDirectImageRestrictIso_zero_hom_app f V M]
  have key := compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_app
    (C := SheafOfModules.{u} (structureSheafRing X))
    (moduleRestriction X (preimageOpen f V))
    (modulePushforward (restrictedMorphism f V))
    (modulePushforward f) (moduleRestriction Y V) (modulePushforwardRestrictIso f V)
    0 I J φ hφ
  exact key

/-- **Stacks 01E5, compatibility with injective resolutions.**  On injective resolutions,
localization of a higher direct image is obtained by restricting the resolution and applying
the identity-on-sections comparison before taking cohomology.  The augmentation condition `hφ`
says that the comparison of resolutions descends the identity of the restricted module.

`higherDirectImageRestrictIso` is defined by cases on the degree; in positive degree this is
`higherDirectImageRestrictIso_injectiveResolution_succ` and in degree zero it is
`higherDirectImageRestrictIso_injectiveResolution_zero`. -/
@[stacks 01E5 "compatibility with injective resolutions"]
theorem higherDirectImageRestrictIso_injectiveResolution (p : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X)) (I : InjectiveResolution M)
    (J : InjectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M))
    (φ : J.cocomplex ⟶
      ((moduleRestriction X (preimageOpen f V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 =
      (moduleRestriction X (preimageOpen f V)).map (I.ι.f 0)) :
    (higherDirectImageRestrictIso f V p).hom.app M ≫
        (moduleRestriction Y V).map
          (I.isoRightDerivedObj (modulePushforward f) p).hom =
      (J.isoRightDerivedObj (modulePushforward (restrictedMorphism f V)) p).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map
          (((modulePushforward (restrictedMorphism f V)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ) ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map
          (((modulePushforwardRestrictIso f V).hom.mapHomologicalComplex
            (ComplexShape.up ℕ)).app I.cocomplex) ≫
        (((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).sc p).mapHomologyIso (moduleRestriction Y V)).hom := by
  cases p with
  | zero => exact higherDirectImageRestrictIso_injectiveResolution_zero f V M I J φ hφ
  | succ n => exact higherDirectImageRestrictIso_injectiveResolution_succ f V n M I J φ hφ

end Restriction

end Stacks.Cohomology.HigherDirectImage

end
