module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCechDirectImagePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleBaseChangeConjugate
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineOverBaseCechTerms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Čech direct images of a cover affine over the base are acyclic for `ε_a`

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site `B` and let `V` be an object of the
small étale site of `X`. The terms of the sheaf-level Čech complex of [Stacks, Tag 071N] are
built from `Stacks.CechSite.SheafLevel.directImage` at the iterated fibre products of a covering
family. This file shows that for `𝓖` quasi-coherent on the site, `j_{V,*} j_V^{-1} 𝓖` is acyclic
for `(ε_a)_*` as soon as `V` is affine over `X` and over `Y`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.pushforwardStructureMapRingIso`: the direct image along `ε_{p_V}`
  is the direct image along `CategoryTheory.Over.star V` read through the equivalence of module
  categories of the localization at `V`.

## Main results

* `AlgebraicGeometry.SmallEtale.preservesInjectiveObjects_pushforward_pushforwardOver` and
  `AlgebraicGeometry.SmallEtale.preservesInjectiveObjects_pushforward_smallEtaleStructureMapRing`:
  the direct image out of the localization at `V` carries injective modules to injective modules.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_objRestrict`: the crossover of a module
  quasi-coherent on the site is quasi-coherent on the site.
* `AlgebraicGeometry.SmallEtale.acyclic_pushforward_directImage`: `j_{V,*} j_V^{-1} 𝓖` is acyclic
  for `(ε_a)_*` when `V` is affine over `X` and over `Y`, for quasi-coherent `𝓖`.
* `AlgebraicGeometry.SmallEtale.acyclic_pushforward_directImage_piObj_of_isSeparatedHom`: the same
  at an iterated fibre product of a covering family whose members are affine over `Y`, for a
  separated `a`.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

/-- A functor isomorphic to one that carries injective objects to injective objects does so
too. -/
public theorem preservesInjectiveObjects_of_natIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) [F.PreservesInjectiveObjects] :
    G.PreservesInjectiveObjects where
  injective_obj h := Injective.of_iso (e.app _) (F.injective_obj_of_injective h)

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- The direct image along `CategoryTheory.Over.star U` carries injective modules to injective
modules. -/
@[sga "4 V 4.9" "clause 3"]
public instance preservesInjectiveObjects_pushforward_pushforwardOver :
    (SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := structureSheaf B X hX) U)).PreservesInjectiveObjects :=
  letI : PreservesFiniteLimits (SheafOfModules.pushforward.{u}
      (𝟙 ((structureSheaf B X hX).over U))) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (SheafOfModules.overPushforwardOverAdj.{u} U)

/-- The direct image along `ε_{p_U}` is the direct image along `CategoryTheory.Over.star U`
read through the inverse of the equivalence
`AlgebraicGeometry.SmallEtale.objRestrictEquivalence` of module categories of the localization
at `U`. -/
public def pushforwardStructureMapRingIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B U.obj.hom) ≅
      (objRestrictEquivalence B X hX U).inverse ⋙
        SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver U) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (objRestrictEquivalence B X hX U).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (objRestrictFunctorPushforwardIso B X hX U)

/-- The direct image along `ε_{p_U}` carries injective modules to injective modules, for `U` an
object of the small étale site of `X`. -/
public instance preservesInjectiveObjects_pushforward_smallEtaleStructureMapRing :
    (SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B U.obj.hom)).PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_natIso (pushforwardStructureMapRingIso B X hX U).symm

/-- The crossover to the small étale site of the scheme of `U` preserves quasi-coherence on the
site. -/
public theorem isQuasicoherentOnSite_objRestrict
    (G : SheafOfModules.{u} (structureSheaf B X hX)) (h : G.IsQuasicoherentOnSite) :
    ((objRestrict B X hX U).obj G).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_objRestrict_iff B X hX U G).2
    (Stacks.SheafOfModules.isQuasicoherentOnSite_over G h U)

section Base

variable {X' Y' : B.Scheme} (a : X' ⟶ Y')

/-- For `V` an object of the small étale site of `X` whose structure morphism to `X` and
whose structure morphism to `Y` are both affine, and `𝓖` an `𝒪_{X_étale}`-module quasi-coherent on
the site, the module `j_{V,*} j_V^{-1} 𝓖` is acyclic for the direct image along `ε_a`. -/
public theorem acyclic_pushforward_directImage (V : SmallEtale B X'.obj X'.property)
    [IsAffineHom (schemeHom B V.obj.hom)]
    [IsAffineHom (schemeHom B (V.obj.hom ≫ a))]
    (G : SheafOfModules.{u} (structureSheaf B X'.obj X'.property))
    (hG : G.IsQuasicoherentOnSite) :
    Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
      ((Stacks.CechSite.SheafLevel.directImage (structureSheaf B X'.obj X'.property) V).obj G) := by
  intro n hn
  have hAq : ((objRestrict B X'.obj X'.property V).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_objRestrict B X'.obj X'.property V G hG
  have hGacyc : Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B V.obj.hom))
      ((objRestrict B X'.obj X'.property V).obj G) :=
    acyclic_pushforward_of_isAffineHom B V.obj.hom _ hAq
  have hcompIso : SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B V.obj.hom) ⋙
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ≅
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (V.obj.hom ≫ a)) :=
    SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing B a)
        (smallEtaleStructureMapRing B V.obj.hom) ≪≫
      (smallEtalePushforwardCompIso B V.obj.hom a).symm
  have hzero' : IsZero ((((SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B V.obj.hom)) ⋙ SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B a)).rightDerived n).obj
        ((objRestrict B X'.obj X'.property V).obj G)) :=
    (isZero_rightDerived_pushforward_of_isAffineHom B (V.obj.hom ≫ a) _ hAq n hn).of_iso
      ((Functor.rightDerivedIsoOfNatIso hcompIso n).app _)
  have hcol := Stacks.RightDerivedComp.objIso
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B V.obj.hom))
    (injectiveResolution ((objRestrict B X'.obj X'.property V).obj G)) hGacyc
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) n
  exact (hzero'.of_iso hcol.symm).of_iso
    (((SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B a)).rightDerived n).mapIso
        ((directImageIsoPushforward B X'.obj X'.property V).app G))

/-- Let `a` be separated. At an iterated fibre product over `X` of the members of a covering
family whose members are affine over `Y` — that is, at the object of `X_étale` indexing a factor
of a term of the sheaf-level Čech complex — the direct image `j_{V,*} j_V^{-1} 𝓖` of a module
quasi-coherent on the site is acyclic for the direct image along `ε_a`. -/
public theorem acyclic_pushforward_directImage_piObj_of_isSeparatedHom
    [IsSeparated (schemeHom B a)]
    (E : PreZeroHypercover.{u} (final B X'.obj X'.property))
    (hE : ∀ j, IsAffineHom (toBaseHom B a (E.X j)))
    (G : SheafOfModules.{u} (structureSheaf B X'.obj X'.property))
    (hG : G.IsQuasicoherentOnSite) (p : ℕ) (i : Fin (p + 1) → E.I₀) :
    letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
        HasProduct (fun b ↦ Over.mk (E.f (j b))) := fun q j ↦
      Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
    Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
      ((Stacks.CechSite.SheafLevel.directImage (structureSheaf B X'.obj X'.property)
        (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left).obj G) := by
  have hstruct : ∀ j, IsAffineHom (B.inclusion.map (E.X j).obj.hom) := fun j ↦
    isAffineHom_structureHom_of_isAffineHom_toBaseHom B a _ (hE j)
  have h1 : IsAffineHom (schemeHom B
      (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left.obj.hom) :=
    isAffineHom_structureHom_piObj B X'.obj X'.property E hstruct p i
  have h2 : IsAffineHom (schemeHom B
      ((∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left.obj.hom ≫ a)) := by
    rw [schemeHom, B.inclusion.map_comp]
    exact isAffineHom_toBaseHom_piObj_of_isSeparatedHom B a E hE p i
  exact acyclic_pushforward_directImage B a _ G hG

end Base

end AlgebraicGeometry.SmallEtale

end
