module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChangeUnbounded

/-!
# The unbounded base change map through a resolution of the inverse image

Let `Λ` be a commutative ring and let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. Let `I` be a K-injective complex of sheaves of `Λ`-modules on
`X_étale` and `i : (g')^{-1} I ⟶ L` a quasi-isomorphism onto a K-injective complex. The base
change map `g^{-1} Rf_* I ⟶ Rf'_* (g')^{-1} I` on unbounded derived categories
(`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded`) is invertible at `I` as soon as
the morphism of complexes `g^{-1} f_* I ⟶ f'_* (g')^{-1} I ⟶ f'_* L` is a quasi-isomorphism: `I`
computes `Rf_*`, `L` computes `Rf'_*`, and `Rf'_*` inverts `i`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isIso_Q_map`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [CommRing Λ] {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g)

/-- The comparison `F ⋙ G ⟶ G' ⋙ F'` applied degreewise and read through the identifications
`(F ⋙ G)(K) = G(F(K))` and `(G' ⋙ F')(K) = F'(G'(K))`, followed by `F'` of a morphism
`i : G'(K) ⟶ L`, is the comparison applied degreewise followed by `F'(i)`. Stated for abstract
categories, so that the kernel never reduces the functors. -/
theorem mapHomologicalComplexCompIso_hom_comp_app_comp {ι : Type*} {c : ComplexShape ι}
    {V W W' V' : Type*} [Category* V] [Category* W] [Category* W'] [Category* V'] [Preadditive V]
    [Preadditive W] [Preadditive W'] [Preadditive V'] {F : V ⥤ W} {G : W ⥤ W'} {G' : V ⥤ V'}
    {F' : V' ⥤ W'} [F.Additive] [G.Additive] [G'.Additive] [F'.Additive]
    (α : F ⋙ G ⟶ G' ⋙ F') (K : HomologicalComplex V c) (L : HomologicalComplex V' c)
    (i : (G'.mapHomologicalComplex c).obj K ⟶ L) :
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom ≫
        NatTrans.mapHomologicalComplex α c ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (G' ⋙ F')) c).inv).app K ≫
        (F'.mapHomologicalComplex c).map i =
      (NatTrans.mapHomologicalComplex α c).app K ≫ (F'.mapHomologicalComplex c).map i := by
  ext n
  simp

/-- The degreewise base change comparison of `etaleModuleComplexBaseChangeUnbounded`, built from an
arbitrary comparison `β : f_* ⋙ g^{-1} ⟶ (g')^{-1} ⋙ f'_*` in place of
`Stacks.EtaleCohomology.etaleModuleBaseChange`. With `β` a variable the kernel compares statements
about it without unfolding the base change map. -/
def etaleModuleComplexBaseChangeUnboundedOf
    (β : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ f') :
    ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex _ ⋙
        (etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, r} Λ Y') ℤ) ⟶
      ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _ ⋙
        (etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, r} Λ Y') ℤ) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
    NatTrans.mapHomologicalComplex β _ ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv

/-- `etaleModuleComplexBaseChangeUnbounded` is `etaleModuleComplexBaseChangeUnboundedOf` at the
underived base change map. -/
theorem etaleModuleComplexBaseChangeUnbounded_eq :
    etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h =
      etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ f g g' f'
        (etaleModuleBaseChange.{u, r} Λ f f' g g' h.symm) :=
  rfl

/-- `etaleModuleComplexBaseChangeUnboundedOf β` followed by `f'_*` of `i : (g')^{-1} K ⟶ L` is `β`
applied degreewise followed by `f'_*(i)`. -/
theorem etaleModuleComplexBaseChangeUnboundedOf_app_comp
    (β : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (L : CochainComplex (EtaleModules.{u, r} Λ X') ℤ)
    (i : ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      L) :
    (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ f g g' f' β).app K ≫
        ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map i =
      (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app K ≫
        ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map i :=
  mapHomologicalComplexCompIso_hom_comp_app_comp β K L i

/-- **The base change map at a K-injective complex, through a resolution of its inverse image.**
Let `I` be a K-injective complex on `X_étale` and `i : (g')^{-1} I ⟶ L` a quasi-isomorphism onto
a K-injective complex. If `g^{-1} f_* I ⟶ f'_* (g')^{-1} I ⟶ f'_* L` is a quasi-isomorphism, the
base change map is invertible at `I`: in `etaleModuleDerivedBaseChangeUnbounded_fac` the units of
`Rf_*` at `I` and of `Rf'_*` at `L` are invertible, and the naturality of the latter along `i`
identifies the remaining factor with the given quasi-isomorphism. The underived comparison enters
as a variable `β` equal to `Stacks.EtaleCohomology.etaleModuleBaseChange`, so that statements about
it proved elsewhere are compared with this one without unfolding it. -/
theorem isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isIso_Q_map
    (β : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (hβ : β = etaleModuleBaseChange.{u, r} Λ f f' g g' h.symm)
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hI : I.IsKInjective)
    (L : CochainComplex (EtaleModules.{u, r} Λ X') ℤ) (hL : L.IsKInjective)
    (i : ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      L) (hi : QuasiIso i)
    (hy : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I ≫
        ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map i))) :
    IsIso ((etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' h).app
      (DerivedCategory.Q.obj I)) := by
  have hc : (etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h).app I ≫
        ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map i =
      (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I ≫
        ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map i := by
    rw [etaleModuleComplexBaseChangeUnbounded_eq, ← hβ]
    exact etaleModuleComplexBaseChangeUnboundedOf_app_comp Λ f g g' f' β I L i
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f I hI
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f' L hL
  have := hi
  have hnat := (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').naturality i
  have hB : IsIso ((DerivedCategory.Q.map
      ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h).app I) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
          (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _).obj I)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').map (DerivedCategory.Q.map i)) := by
    have e : (DerivedCategory.Q.map
        ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h).app I) ≫
          (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
            (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _).obj I)) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').map (DerivedCategory.Q.map i) =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I ≫
            ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map
              i) ≫
          (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app L := by
      simp only [Functor.comp_map] at hnat
      rw [Category.assoc, ← hnat, ← Category.assoc, ← Functor.map_comp, hc]
    rw [e]
    infer_instance
  have hA : IsIso (DerivedCategory.Q.map
      ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h).app I) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
          (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _).obj I)) :=
    IsIso.of_isIso_comp_right _
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').map (DerivedCategory.Q.map i))
  have hfac := etaleModuleDerivedBaseChangeUnbounded_fac.{u, r} Λ f g g' f' h I
  rw [← Category.assoc (DerivedCategory.Q.map _)] at hfac
  exact IsIso.of_isIso_fac_left hfac

end Stacks.EtaleCohomology

end
