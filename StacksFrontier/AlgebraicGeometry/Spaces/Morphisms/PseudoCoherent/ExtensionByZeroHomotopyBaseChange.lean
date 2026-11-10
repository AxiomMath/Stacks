module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.MapHomotopyCategoryMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroUnderivedBaseChange

/-!
# Extension by zero commutes with degreewise base change on homotopy categories

Let

```
T' --u'--> T
|t'        |t
v          v
U  --u-->  Z
```

be a cartesian square of algebraic spaces with `u` étale.  The degreewise base change map
`u'_!(t'^*M) ⟶ t^*(u_!M)` on the homotopy categories of complexes of modules,
`AlgebraicGeometry.Space.extensionByZeroBaseChangeHomotopy`, is an isomorphism at every complex
`M`: at the class of a complex it is the class of the degreewise underived base change map, which
is invertible by `AlgebraicGeometry.Space.isIso_extensionByZeroBaseChangeModules`.

## Main results

* `AlgebraicGeometry.Space.isIso_extensionByZeroBaseChangeHomotopy_app`: the degreewise base
  change map for extension by zero is invertible.

## Implementation notes

`AlgebraicGeometry.Space.extensionByZeroBaseChangeHomotopy` is built from the degreewise
identifications of
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso`, which carry
the preadditive structure `SheafOfModules.instPreadditive`, and from adjunctions carrying the one
induced by `SheafOfModules.instAbelian`.  The two are definitionally equal, but a comparison of
components across them makes the kernel unfold the heavy comparison isomorphisms.
`AlgebraicGeometry.Space.extensionByZeroBaseChangeHomotopy_eq` therefore identifies the base change
map, as a whole natural transformation and by `rfl`, with the one built uniformly from
`AlgebraicGeometry.Space.etaleLowerShriekMapHomotopyCategoryAdjunction` and
`AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyCategoryFactorIso`, and the components are
then transported by `CategoryTheory.NatTrans.isIso_app_of_heq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/- The homotopy-level base change map is stated with the abelian and preadditive structures of
`AlgebraicGeometry.Space.extensionByZeroBaseChangeHomotopy`, which fixes them as explained in the
implementation notes of `ExtensionByZeroBaseChangeComparison`. -/
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullback of modules along the composite of the morphisms of small étale ringed topoi of two
morphisms of algebraic spaces is additive. -/
instance additive_pullbackModules_comp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS g)
        (smallEtaleRingedToposHom B S hS f)).toModulesHom.pullbackModules).Additive :=
  RingedToposHom.pullbackModules_additive
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f))

/-- Degreewise extension by zero is left adjoint to degreewise pullback along an étale morphism,
on homotopy categories, with the right adjoint spelled with the preadditive structure fixed in
this file. -/
def etaleLowerShriekMapHomotopyCategoryAdjunction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    (etaleExtensionByZero B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).mapHomotopyCategory
        (ComplexShape.up ℤ) :=
  (Adjunction.mapHomotopyCategoryAdjunction (G := etaleExtensionByZero B S hS f hf)
      (F := etaleRestriction B S hS f hf) (etaleModuleLowerShriekAdjunction B S hS f hf)
      (ComplexShape.up ℤ)).ofNatIsoRight
    (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso
      (pullbackModulesIsoEtaleRestriction B S hS f hf) (ComplexShape.up ℤ)).symm

/-- The degreewise identification `g^* ⋙ f^* ≅ k^*` on homotopy categories attached to a
factorisation `f ≫ g = k`, with every ingredient spelled with the preadditive structure fixed in
this file. -/
def smallEtalePullbackMapHomotopyCategoryFactorIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      ((smallEtaleRingedToposHom B S hS k).toModulesHom.pullbackModules).mapHomotopyCategory
        (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso
      (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).symm (ComplexShape.up ℤ) ≪≫
    Stacks.Homology.mapHomotopyCategoryIso
      (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso (ComplexShape.up ℤ) ≪≫
    eqToIso (congrArg (fun m : X ⟶ Z ↦
      ((smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules).mapHomotopyCategory
        (ComplexShape.up ℤ)) h)

/-- The degreewise base change map for extension by zero, with every homotopy-level ingredient
spelled with the preadditive structure fixed in this file. -/
theorem extensionByZeroBaseChangeHomotopy_eq {T T' U W : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W) (hu : IsEtale B S hS u.hom)
    (hu' : IsEtale B S hS u'.hom) (h : u' ≫ t = t' ≫ u) :
    extensionByZeroBaseChangeHomotopy u' t t' u hu hu' h =
      ((mateEquiv (etaleLowerShriekMapHomotopyCategoryAdjunction u hu)
        (etaleLowerShriekMapHomotopyCategoryAdjunction u' hu')).symm
        (TwoSquare.mk _ _ _ _
          ((smallEtalePullbackMapHomotopyCategoryFactorIso t' u (u' ≫ t) h.symm).hom ≫
            (smallEtalePullbackMapHomotopyCategoryFactorIso u' t (u' ≫ t) rfl).inv))) :=
  rfl

/-- **Extension by zero commutes with degreewise base change** on homotopy categories: for a
cartesian square of algebraic spaces with `u` étale, the degreewise base change map
`u'_!(t'^*M) ⟶ t^*(u_!M)` is an isomorphism at every complex `M` of modules on `U`. -/
theorem isIso_extensionByZeroBaseChangeHomotopy_app {T T' U W : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W) (sq : IsPullback u' t' t u)
    (hu : IsEtale B S hS u.hom) (hu' : IsEtale B S hS u'.hom)
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U))
      (ComplexShape.up ℤ)) :
    IsIso ((extensionByZeroBaseChangeHomotopy u' t t' u hu hu' sq.w).app M) := by
  have hβ := isIso_extensionByZeroBaseChangeModules u' t t' u sq hu hu'
  have key := Adjunction.isIso_mateEquiv_symm_app_of_eq_mapHomotopyCategory
    (E := etaleExtensionByZero B S hS u hu) (R := etaleRestriction B S hS u hu)
    (E' := etaleExtensionByZero B S hS u' hu') (R' := etaleRestriction B S hS u' hu')
    (etaleModuleLowerShriekAdjunction B S hS u hu) (etaleModuleLowerShriekAdjunction B S hS u' hu')
    (pullbackModulesIsoEtaleRestriction B S hS u hu)
    (pullbackModulesIsoEtaleRestriction B S hS u' hu')
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS t')
      (smallEtaleRingedToposHom B S hS u)).symm
    (smallEtaleRingedToposHom_compTwoIso B S hS t' u).pullbackModulesIso
    (congrArg (fun m : T' ⟶ W ↦ (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules)
      sq.w.symm)
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS u')
      (smallEtaleRingedToposHom B S hS t)).symm
    (smallEtaleRingedToposHom_compTwoIso B S hS u' t).pullbackModulesIso (ComplexShape.up ℤ)
    (congrArg (fun m : T' ⟶ W ↦
      ((smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules).mapHomotopyCategory
        (ComplexShape.up ℤ)) sq.w.symm)
    (congrArg (fun m : T' ⟶ W ↦
      ((smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules).mapHomotopyCategory
        (ComplexShape.up ℤ)) (rfl : u' ≫ t = u' ≫ t))
    (etaleLowerShriekMapHomotopyCategoryAdjunction u hu)
    (etaleLowerShriekMapHomotopyCategoryAdjunction u' hu') rfl rfl
    (smallEtalePullbackMapHomotopyCategoryFactorIso t' u (u' ≫ t) sq.w.symm)
    (smallEtalePullbackMapHomotopyCategoryFactorIso u' t (u' ≫ t) rfl) rfl rfl hβ M
  refine NatTrans.isIso_app_of_heq _ _ ?_ ?_ ?_ M key
  · rfl
  · rfl
  · exact heq_of_eq (extensionByZeroBaseChangeHomotopy_eq u' t t' u hu hu' sq.w)

end AlgebraicGeometry.Space
