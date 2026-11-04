module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# `Ext` out of a complex into an object, along a fully faithful exact functor

Let `F : 𝒞 ⥤ 𝒟` be a fully faithful exact additive functor of abelian categories which preserves
injective objects, and suppose `𝒞` has enough injectives. For a cochain complex `K` of `𝒞` and an
object `G` of `𝒞`, this file identifies

`Ext^n_𝒞(K, G) = Hom_{D(𝒞)}(K, G[0]⟦n⟧) ≅ Hom_{D(𝒟)}(F K, (F G)[0]⟦n⟧) = Ext^n_𝒟(F K, F G)`

as abelian groups, for every `n : ℤ` and any models of the two derived categories.

Mathlib's `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects` is the case where
`K` is an object placed in degree `0`; here `K` is an arbitrary complex.

## The argument

Choose an injective resolution `G ⟶ I`. The complex `I⟦n⟧` is bounded below with injective
terms, hence K-injective, so morphisms into it in the derived category are morphisms in the
homotopy category (`CochainComplex.IsKInjective.Qh_map_bijective`). The same holds for
`F I⟦n⟧` because `F` preserves injective objects, and `F I` is a resolution of `F G` because `F`
is exact. Finally `F` is bijective on morphisms of homotopy categories, being fully faithful.

## Main definitions

* `CategoryTheory.Functor.shiftedHomSingleAddEquivOfPreservesInjectives`: the identification
  `Hom_{D(𝒞)}(K, G[0]⟦n⟧) ≃+ Hom_{D(𝒟)}(F K, (F G)[0]⟦n⟧)`.
-/

@[expose] public section

open CategoryTheory Limits

universe t t' v v' u u'

namespace CategoryTheory.Functor

variable {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞] {𝒟 : Type u'} [Category.{v'} 𝒟] [Abelian 𝒟]

section KInjective

variable [HasDerivedCategory.{t} 𝒞]

/-- For a K-injective complex `L`, morphisms `Q K ⟶ Q L` in the derived category are morphisms
`K ⟶ L` in the homotopy category, as abelian groups. -/
noncomputable def derivedHomAddEquivOfIsKInjective (K L : CochainComplex 𝒞 ℤ)
    [CochainComplex.IsKInjective L] :
    ((HomotopyCategory.quotient 𝒞 (ComplexShape.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒞 (ComplexShape.up ℤ)).obj L) ≃+
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :=
  (AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
      (CochainComplex.IsKInjective.Qh_map_bijective _ L)).trans
    (Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso 𝒞).app K)
      ((DerivedCategory.quotientCompQhIso 𝒞).app L)).toAddEquiv

end KInjective

variable (F : 𝒞 ⥤ 𝒟) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Full] [F.Faithful] [F.PreservesInjectiveObjects]
  [HasDerivedCategory.{t} 𝒞] [HasDerivedCategory.{t'} 𝒟]

/-- The image under `F` of a bounded below complex with injective terms. -/
instance isKInjective_map_cochainComplex {G : 𝒞} (R : InjectiveResolution G) (n : ℤ) :
    CochainComplex.IsKInjective
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex)⟦n⟧) := by
  have : CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex) 0 :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ F 0).2 inferInstance
  have : ∀ k, Injective (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      R.cochainComplex).X k) := fun k => F.injective_obj (R.cochainComplex.X k)
  have := CochainComplex.isKInjective_of_injective
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex) 0
  infer_instance

/-- The comparison `G[0] ≅ I` of an injective resolution, in the derived category. -/
noncomputable def singleIsoResolution {G : 𝒞} (R : InjectiveResolution G) :
    (DerivedCategory.singleFunctor 𝒞 0).obj G ≅ DerivedCategory.Q.obj R.cochainComplex :=
  have : IsIso (DerivedCategory.Q.map R.ι') := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  asIso (DerivedCategory.Q.map R.ι')

/-- The comparison `(F G)[0] ≅ F I` of the image of an injective resolution, in the derived
category: `F` is exact, so it carries the quasi-isomorphism `G[0] ⟶ I` to one. -/
noncomputable def singleIsoMapResolution {G : 𝒞} (R : InjectiveResolution G) :
    (DerivedCategory.singleFunctor 𝒟 0).obj (F.obj G) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex) :=
  have : IsIso (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι')) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.up ℤ) 0).app G).symm ≪≫
    asIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι'))

/-- **`Ext` out of a complex into an object is invariant under a fully faithful exact functor
preserving injective objects**, when the source has enough injectives:
`Hom_{D(𝒞)}(K, G[0]⟦n⟧) ≃+ Hom_{D(𝒟)}(F K, (F G)[0]⟦n⟧)`, for any models of the derived
categories. -/
noncomputable def shiftedHomSingleAddEquivOfPreservesInjectives [EnoughInjectives 𝒞]
    (K : CochainComplex 𝒞 ℤ) (G : 𝒞) (n : ℤ) :
    (DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor 𝒞 0).obj G)⟦n⟧) ≃+
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
        ((DerivedCategory.singleFunctor 𝒟 0).obj (F.obj G))⟦n⟧) :=
  let R : InjectiveResolution G := injectiveResolution G
  have : CochainComplex.IsKInjective R.cochainComplex :=
    CochainComplex.isKInjective_of_injective _ 0
  let FI := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex
  let FK := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let quot𝒟 := HomotopyCategory.quotient 𝒟 (ComplexShape.up ℤ)
  (Linear.homCongr ℤ (Iso.refl _)
      ((shiftFunctor _ n).mapIso (singleIsoResolution R) ≪≫
        (DerivedCategory.Q.commShiftIso n).symm.app R.cochainComplex)).toAddEquiv.trans <|
  (derivedHomAddEquivOfIsKInjective K (R.cochainComplex⟦n⟧)).symm.trans <|
  (AddEquiv.ofBijective (F.mapHomotopyCategory (ComplexShape.up ℤ)).mapAddHom
      ⟨(F.mapHomotopyCategory (ComplexShape.up ℤ)).map_injective,
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map_surjective⟩).trans <|
  (Linear.homCongr ℤ ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app (R.cochainComplex⟦n⟧) ≪≫
        quot𝒟.mapIso ((F.mapCochainComplexShiftIso n).app R.cochainComplex))).toAddEquiv.trans <|
  (derivedHomAddEquivOfIsKInjective FK (FI⟦n⟧)).trans <|
  (Linear.homCongr ℤ (Iso.refl _)
      ((DerivedCategory.Q.commShiftIso n).app FI ≪≫
        (shiftFunctor _ n).mapIso (singleIsoMapResolution F R).symm)).toAddEquiv

end CategoryTheory.Functor

end
