module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.TensorHomSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectRestriction
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparisonSupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality

/-!
# The tensor–internal-Hom bijection over an object of the site

Let `(C, O)` be a ringed site, `U` an object of `C` and `K`, `B`, `Z` objects of `D(O)`.  The
bijection of [Stacks, Tag 08J8]

`Hom_{D(O)}(K, RSheafHom(B, Z)) ≅ Hom_{D(O)}(K ⊗^L_O B, Z)`

is the derived currying isomorphism of [Stacks, Tag 08J9] read on degree-zero global
hypercohomology through [Stacks, Tag 08JA].  Reading it instead on degree-zero hypercohomology
over `U`, where Tag 08JA identifies the two sides with the morphism groups of the restrictions,
gives a bijection

`Hom_{D(O|_U)}(K|_U, RSheafHom(B, Z)|_U) ≅ Hom_{D(O|_U)}((K ⊗^L_O B)|_U, Z|_U)`,

and the two bijections are **compatible with restriction**: the bijection over `U` carries the
restriction of a morphism to the restriction of its transpose.  Note that the tensor product is
still the one taken on `C`: the statement needs no comparison of `(K ⊗^L_O B)|_U` with
`K|_U ⊗^L_{O|_U} B|_U`, and none is used.

Both halves of the compatibility that [Stacks, Tag 08EH] consumes are here: restriction, and
naturality in the source variable `K`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedCurrySectionsEquiv`: the bijection over `U`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurrySectionsEquiv_restriction`: it carries the
  restriction to `U` of a morphism to the restriction of the morphism matched with it by
  Tag 08J8.
* `AlgebraicGeometry.RingedSite.derivedCurrySectionsEquiv_naturality_source`: it is natural in
  the source variable, in the same sense as
  `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`.

## Implementation notes

The three steps of each proof are the three stages of the bijection, and each is a separate
declaration: elaborating them together exhausts the heartbeat budget.

The restriction statement is the naturality of
`Stacks.Cohomology.ModuleSections.derivedSectionsRestriction` — a natural transformation
`RΓ(C, -) ⟶ RΓ(U, -)` — at the single morphism `derivedCurryIso`, surrounded by two instances of
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_restriction`.  Nothing about the
derived tensor product enters.

The source-naturality statement is the argument of
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source` with Tag 08JA over `U` in
place of Tag 08JA globally; the naturality of the derived currying isomorphism in its source is
used through the same `AlgebraicGeometry.RingedSite.derivedCurryIso_natural_fst`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (U : X.C)
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- The derived currying isomorphism of [Stacks, Tag 08J9] read on degree-zero hypercohomology
over `U`, as an additive equivalence.  This is the local analogue of
`AlgebraicGeometry.RingedSite.derivedCurryGlobalEquiv`. -/
def derivedCurryLocalEquiv
    (K B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
          (((derivedSheafHomBifunctor X).obj (op K)).obj
            (((derivedSheafHomBifunctor X).obj (op B)).obj Z))) : Type u) ≃+
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
          (((derivedSheafHomBifunctor X).obj
            (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj B))).obj
              Z)) : Type u) :=
  ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).mapIso
        (derivedCurryIso X K B Z))).addCommGroupIsoToAddEquiv

omit [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)] in
/-- `derivedCurryLocalEquiv` is the map induced by the derived currying isomorphism on
degree-zero hypercohomology over `U`. -/
theorem derivedCurryLocalEquiv_apply
    (K B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj
          (((derivedSheafHomBifunctor X).obj (op B)).obj Z))) : Type u)) :
    derivedCurryLocalEquiv X U K B Z z =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (derivedCurryIso X K B Z).hom) z :=
  rfl

/-- **The tensor–internal-Hom bijection of [Stacks, Tag 08J8] over an object `U` of the site.**
Morphisms `K|_U ⟶ RSheafHom(B, Z)|_U` are morphisms `(K ⊗^L_O B)|_U ⟶ Z|_U`.

It is the derived currying isomorphism of [Stacks, Tag 08J9] read on degree-zero hypercohomology
over `U`, with both sides identified with groups of morphisms between restrictions by
[Stacks, Tag 08JA].  The tensor product is the one taken on `C`. -/
@[stacks 08J8 "the bijection of morphism groups over an object of the site"]
def derivedCurrySectionsEquiv
    (K B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.obj
          (((derivedSheafHomBifunctor X).obj (op B)).obj Z)) ≃+
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.obj
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj B) ⟶
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.obj Z) :=
  (derivedSheafHomSectionsEquiv X U K
        (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).symm.trans
    ((derivedCurryLocalEquiv X U K B Z).trans
      (derivedSheafHomSectionsEquiv X U
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj B) Z))

/-- The bijection over `U` written out: transport back along [Stacks, Tag 08JA] over `U`, apply
the map induced by the derived currying isomorphism, transport forward again. -/
theorem derivedCurrySectionsEquiv_apply
    (K B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op B)).obj Z)) :
    derivedCurrySectionsEquiv X U K B Z g =
      derivedSheafHomSectionsEquiv X U
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj B) Z
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (derivedCurryIso X K B Z).hom)
          ((derivedSheafHomSectionsEquiv X U K
            (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).symm g)) := by
  unfold derivedCurrySectionsEquiv
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply]
  rfl

/-! ### Compatibility with restriction -/

omit [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)] in
/-- **The restriction of hypercohomology commutes with the derived currying isomorphism.**  This
is the naturality of `Stacks.Cohomology.ModuleSections.derivedSectionsRestriction` at the single
morphism `derivedCurryIso`, read on degree-zero cohomology. -/
theorem derivedSectionsRestriction_derivedCurryIso
    (K B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj
          (((derivedSheafHomBifunctor X).obj (op B)).obj Z))) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (derivedCurryIso X K B Z).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedSectionsRestriction X U).app
            (((derivedSheafHomBifunctor X).obj (op K)).obj
              (((derivedSheafHomBifunctor X).obj (op B)).obj Z))) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedSectionsRestriction X U).app
          (((derivedSheafHomBifunctor X).obj
            (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj B))).obj Z))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedCurryIso X K B Z).hom) x) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map f)
      ((derivedSectionsRestriction X U).naturality (derivedCurryIso X K B Z).hom)) x
  simpa only [CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply] using h.symm

/-- **The bijection of [Stacks, Tag 08J8] over `U` is the restriction of the bijection over
`C`.**  For `g : K ⟶ RSheafHom(B, Z)` the morphism `(K ⊗^L_O B)|_U ⟶ Z|_U` matched with `g|_U`
over `U` is the restriction of the morphism `K ⊗^L_O B ⟶ Z` matched with `g` over `C`.

This is the compatibility of [Stacks, Tag 08JA] globally and over `U` under restriction of
hypercohomology, applied at the two ends of the bijection, with the naturality of that
restriction at the derived currying isomorphism in between. -/
@[stacks 08J8 "the bijection over an object of the site restricts the global one"]
theorem derivedCurrySectionsEquiv_restriction
    (K B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g : K ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    derivedCurrySectionsEquiv X U K B Z
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map g) =
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.map
        (derivedCurryHomEquiv X K B Z g) := by
  have h₁ : (derivedSheafHomSectionsEquiv X U K
        (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).symm
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map g) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedSectionsRestriction X U).app
          (((derivedSheafHomBifunctor X).obj (op K)).obj
            (((derivedSheafHomBifunctor X).obj (op B)).obj Z)))
        ((derivedSheafHomGlobalSectionsEquiv X K
          (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).symm g) := by
    refine ((derivedSheafHomSectionsEquiv X U K
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).symm_apply_eq).2 ?_
    rw [derivedSheafHomSectionsEquiv_restriction X U K
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z), AddEquiv.apply_symm_apply]
  have h₂ := (congrArg (derivedCurryHomEquiv X K B Z)
      ((derivedSheafHomGlobalSectionsEquiv X K
        (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).apply_symm_apply g).symm).trans
    (derivedCurryHomEquiv_globalSections_homologyMap X K B Z
      ((derivedSheafHomGlobalSectionsEquiv X K
        (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).symm g))
  rw [derivedCurrySectionsEquiv_apply X U K B Z, h₁]
  exact (congrArg (derivedSheafHomSectionsEquiv X U
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj B) Z)
      (derivedSectionsRestriction_derivedCurryIso X U K B Z _)).trans
    ((derivedSheafHomSectionsEquiv_restriction X U
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj B) Z _).trans
      (congrArg _ h₂.symm))

/-! ### Naturality in the source -/

/-- **[Stacks, Tag 08JA] over `U` is natural in its contravariant variable alone.**  This is
`derivedSheafHomSectionsEquiv_naturality_homologyZero` with the identity in the covariant slot. -/
theorem derivedSheafHomSectionsEquiv_naturality_source
    {L L' M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomSectionsEquiv X U L' M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (((derivedSheafHomBifunctor X).map φ.op).app M)) ξ) =
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.map φ ≫
        derivedSheafHomSectionsEquiv X U L M ξ := by
  have h := derivedSheafHomSectionsEquiv_naturality_homologyZero X U φ (𝟙 M) ξ
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using h

/-- **[Stacks, Tag 08JA] over `U` carries precomposition back to the map induced by
`RSheafHom(φ, 1)`.** -/
theorem derivedSheafHomSectionsEquiv_symm_comp
    {L L' M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L)
    (h : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.obj L ⟶
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.obj M) :
    (derivedSheafHomSectionsEquiv X U L' M).symm
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map φ ≫ h) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (((derivedSheafHomBifunctor X).map φ.op).app M))
        ((derivedSheafHomSectionsEquiv X U L M).symm h) := by
  refine ((derivedSheafHomSectionsEquiv X U L' M).symm_apply_eq).2 ?_
  rw [derivedSheafHomSectionsEquiv_naturality_source X U φ, AddEquiv.apply_symm_apply]

/-- **The source-naturality square of the bijection over `U`, with the outer identification not
yet removed.**  Separated from `derivedCurrySectionsEquiv_naturality_source` because elaborating
the two together exhausts the heartbeat budget. -/
theorem derivedCurrySectionsEquiv_naturality_source_aux
    (K K' B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (u : K' ⟶ K)
    (h : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op B)).obj Z)) :
    derivedCurrySectionsEquiv X U K' B Z
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map u ≫ h) =
      derivedSheafHomSectionsEquiv X U
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K').obj B) Z
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (((derivedSheafHomBifunctor X).map
              (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app B).op).app Z))
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
              (derivedCurryIso X K B Z).hom)
            ((derivedSheafHomSectionsEquiv X U K
              (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).symm h))) := by
  have hs := derivedSheafHomSectionsEquiv_symm_comp X U u h
  rw [derivedCurrySectionsEquiv_apply X U K' B Z
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.map u ≫ h)]
  refine congrArg (derivedSheafHomSectionsEquiv X U
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K').obj B) Z) ?_
  rw [hs]
  simp only [← CategoryTheory.comp_apply, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f ↦ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map f)
      ((derivedSheafHomSectionsEquiv X U K
        (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).symm h))
    (AlgebraicGeometry.RingedSite.derivedCurryIso_natural_fst X (A := K) (A' := K') (B := B)
      (Z := Z) u)

/-- **The bijection of [Stacks, Tag 08J8] over `U` is natural in its source variable.**  For a
morphism `u : K' ⟶ K` of `D(O)`, precomposing a morphism `K|_U ⟶ RSheafHom(B, Z)|_U` with `u|_U`
corresponds to precomposing the matched morphism `(K ⊗^L_O B)|_U ⟶ Z|_U` with the restriction of
`u ⊗ 1`. -/
@[stacks 08J8 "functoriality in the source, over an object of the site"]
theorem derivedCurrySectionsEquiv_naturality_source
    (K K' B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (u : K' ⟶ K)
    (h : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op B)).obj Z)) :
    derivedCurrySectionsEquiv X U K' B Z
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map u ≫ h) =
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app B) ≫
        derivedCurrySectionsEquiv X U K B Z h := by
  rw [derivedCurrySectionsEquiv_naturality_source_aux X U K K' B Z u h,
    derivedSheafHomSectionsEquiv_naturality_source X U
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app B),
    derivedCurrySectionsEquiv_apply X U K B Z]

end AlgebraicGeometry.RingedSite

end
