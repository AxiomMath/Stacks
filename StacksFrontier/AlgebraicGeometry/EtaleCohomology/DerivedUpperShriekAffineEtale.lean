module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Shift.Adjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology sheaves of derived upper shriek on the affine étale site

Let `f : X ⟶ Y` be a separated finite type morphism of quasi-compact and quasi-separated
schemes, let `Λ` be a torsion ring and let `K` be an object of `D(Y_étale, Λ)`.  The cohomology
sheaf `H^n(Rf^! K)`, restricted to the small affine étale site of `X`, is the sheaf associated
to the presheaf
```
U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n])
```
This file formalises that comparison.

## The object `R(U ⟶ Y)_! Λ` and its functoriality

For `j : U ⟶ U'` étale over `Y`, with `g = g' ∘ j`, the transition map `Rg_! Λ ⟶ Rg'_! Λ` is
`Rg'_!` applied to the trace map `Tr_j : j_! Λ ⟶ Λ`, and `Rg_! = Rg'_! ∘ j_!` by Stacks Tags 0F7J
and 0GKM.

Here `Stacks.EtaleCohomology.affineEtaleConstantLowerShriek` is the composite
`U ↦ Rf_!((j_U)_! Λ)`, where `U ↦ (j_U)_! Λ` is
`Stacks.EtaleCohomology.etaleModuleFreeYoneda`, the sheafification of the free `Λ`-module
presheaf on the presheaf represented by `U`.  Its transition maps are induced by the morphisms
of the site, and under `(j_U)_! ⊣ j_U^{-1}` they are exactly the maps `(j_{U'})_!(Tr_j)`, so the
presheaf below is the source's presheaf with the source's transition maps.

## Main definitions

* `Stacks.EtaleCohomology.freeModuleOfType`: the free `Λ`-module on a type, with the type and
  the ring in independent universes.  Mathlib's `ModuleCat.free` ties the two together, and the
  étale site does not fit in the universe of the coefficient ring.
* `Stacks.EtaleCohomology.etaleModuleFreeYoneda`: `U ↦ (j_U)_! Λ` as a functor on the small
  étale site.
* `Stacks.EtaleCohomology.affineEtaleConstantLowerShriek`: `U ↦ R(U ⟶ Y)_! Λ` on the small
  affine étale site, as described above.
* `Stacks.EtaleCohomology.affineEtaleLowerShriekHomPresheaf`: the presheaf
  `U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n])`.
* `Stacks.EtaleCohomology.affineEtaleUpperShriekHomPresheaf`: the presheaf
  `U ↦ Hom_X((j_U)_! Λ, M[n])`.
* `Stacks.EtaleCohomology.affineEtaleAbelianRestriction`: restriction of a sheaf of
  `Λ`-modules on `X_étale` to an abelian sheaf on `X_{affine, étale}`.

## Main results

* `Stacks.EtaleCohomology.affineEtaleHomPresheafAdjIso`: the two presheaves above agree, for
  `M = Rf^! K`, **as presheaves**.  The source gives the equality of the groups and omits "the
  verification that the transition maps are given by the transition maps between the objects
  `Rg_! Λ`".
* `Stacks.EtaleCohomology.affineEtaleSheafifiedHomIso`: a `D⁺` variant of the adjunction step of
  **Stacks Tag 0GLK** — the sheafification of `U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n])` is the
  sheafification of `U ↦ Hom_X((j_U)_! Λ, Uf K[n])` for a right adjoint `Uf` of `Rf_!` on `D⁺`.
* `Stacks.EtaleCohomology.derivedUpperShriekHomologyAffineEtale`: a `D⁺` variant of **Stacks
  Tag 0GLK**, with the right adjoint and the identification of the sheafified Hom presheaf of
  `Uf K` with `H^n(Uf K)` as arguments.

The full statement of Stacks Tag 0GLK, on unbounded derived categories, with `Rf^!` the right
adjoint of Stacks Tag 0G2C and the sheafified Hom presheaf identified with the cohomology sheaf
for every object, is `Stacks.EtaleCohomology.derivedUpperShriek_homology_affineEtale` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.AffineEtaleHomology`.

## Implementation notes

The upper shriek is explicit data: a functor `Uf` together with an adjunction `Rf_! ⊣ Uf`.  The
torsion hypothesis on `Λ` enters only through that adjunction, so it does not appear here.
Likewise `Rf_!` takes an explicit compactification.

The variants here take two inputs as arguments: the adjunction
`adjF : derivedLowerShriek f j Λ ⊣ Uf` on `D⁺`, and, in `derivedUpperShriekHomologyAffineEtale`,
the identification `sheafifiedCohomology` of the sheafification of `U ↦ Hom_X((j_U)_! Λ, M[n])`
with the restriction of `H^n(M)` at `M = Uf K`.  On unbounded derived categories both are proved:
the adjunction is `DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded` (Stacks Tag
0G2C) and the identification is `Stacks.EtaleCohomology.affineEtaleHomPresheafSheafificationIso`.

The two presheaves take values in abelian groups rather than `Λ`-modules: for `Λ` not
commutative the groups `Hom_Y(R(U ⟶ Y)_! Λ, K[n])` carry no `Λ`-action, and the source's
`Hom_Y` is the hom group.  The cohomology sheaf is therefore compared with its underlying
abelian sheaf, which is `affineEtaleAbelianRestriction`.

The universe lifting functors are forced.  Hom groups in `D⁺(EtaleModules Λ X)` live one
universe above the module universe `max (u + 1) r`, while the sections of a sheaf of
`Λ`-modules live in `max (u + 1) r`; and `Adjunction.compPreadditiveYonedaIso` is stated with
`AddCommGrpCat.uliftFunctor` on both sides.  Both presheaves therefore take values in
`AddCommGrpCat.{max (u + 1) r + 1}`, and the cohomology sheaf is lifted to match.

## References

* [Stacks Project, Tag 0GLK](https://stacks.math.columbia.edu/tag/0GLK)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
* [Stacks Project, Tag 0GKM](https://stacks.math.columbia.edu/tag/0GKM)
* [Stacks Project, Tag 0GL4](https://stacks.math.columbia.edu/tag/0GL4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r s uC vC w₁ w₂

namespace Stacks.EtaleCohomology

/-! ### Free modules on a type in another universe -/

/-- The free `Λ`-module on a type, with the type and the ring in independent universes.
Mathlib's `ModuleCat.free` requires the two to coincide, which the small étale site of a scheme
in universe `u` does not allow for a ring in universe `r`. -/
def freeModuleOfType (Λ : Type r) [Ring Λ] : Type s ⥤ ModuleCat.{max s r} Λ where
  obj S := ModuleCat.of Λ (S →₀ Λ)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain Λ Λ f)

/-! ### Extension by zero of the constant sheaf, functorially in the étale object -/

/-- `U ↦ (j_U)_! Λ`, the extension by zero of the constant sheaf `Λ` along the structure
morphism of an object `U` of the small étale site of `X`, functorially in `U`: it is the
sheafification of the free `Λ`-module presheaf on the presheaf represented by `U`.

Presented this way the functoriality in `U` is the functoriality of the representable presheaf,
and under the adjunction `Stacks.EtaleCohomology.etaleModuleExtensionByZeroAdj` the transition
map attached to `j : U ⟶ U'` is the map `(j_{U'})_!(Tr_j)` induced by the trace map of Stacks
Tag 0GL4. -/
abbrev etaleModuleFreeYoneda (Λ : Type r) [Ring Λ] (X : Scheme.{u}) :
    X.Etale ⥤ EtaleModules.{u, r} Λ X :=
  uliftYoneda.{max (u + 1) r} ⋙
    (Functor.whiskeringRight _ _ _).obj (freeModuleOfType.{r, max (u + 1) r} Λ) ⋙
    presheafToSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)

/-- `U ↦ (j_U)_! Λ` on the small affine étale site, placed in degree zero of the bounded below
derived category. -/
abbrev affineEtaleConstant (Λ : Type r) [Ring Λ] (X : Scheme.{u}) :
    X.AffineEtale ⥤ DerivedCategory.Plus (EtaleModules.{u, r} Λ X) :=
  AffineEtale.Spec X ⋙ etaleModuleFreeYoneda.{u, r} Λ X ⋙
    DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0

/-- **The object `R(U ⟶ Y)_! Λ` of Stacks Tag 0GLK**, functorially in the object `U` of the
small affine étale site of `X`: the derived lower shriek of `f` applied to `(j_U)_! Λ`.

By Stacks Tags 0F7J and 0GKM this is `R(U ⟶ Y)_! Λ` for the composite `U ⟶ X ⟶ Y`, and the
transition maps are those of the discussion preceding the source's lemma. -/
abbrev affineEtaleConstantLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ] :
    X.AffineEtale ⥤ DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) :=
  affineEtaleConstant.{u, r} Λ X ⋙ derivedLowerShriek.{u, r} f j Λ

/-! ### The two Hom presheaves -/

/-- The presheaf `U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n])` on the small affine étale site of `X`, which
is the presheaf of Stacks Tag 0GLK. -/
abbrev affineEtaleLowerShriekHomPresheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) (n : ℤ) :
    X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) r + 1} :=
  (affineEtaleConstantLowerShriek.{u, r} f j Λ).op ⋙
    preadditiveYoneda.obj (K⟦n⟧) ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) r + 1}

/-- The presheaf `U ↦ Hom_X((j_U)_! Λ, M[n])` on the small affine étale site of `X`.  For `M` an
object of `D(X_étale, Λ)` this is the presheaf `U ↦ H^n(U, M)` of the source's recollection
`Hom_X(j_! Λ, M[n]) = H^n(U, M)`. -/
abbrev affineEtaleUpperShriekHomPresheaf (Λ : Type r) [Ring Λ] (X : Scheme.{u})
    (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) (n : ℤ) :
    X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) r + 1} :=
  (affineEtaleConstant.{u, r} Λ X).op ⋙
    preadditiveYoneda.obj (M⟦n⟧) ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) r + 1}

/-! ### Restriction of a sheaf of modules to the affine étale site -/

/-- Composing a sheaf of abelian groups with the universe lifting functor again gives a sheaf,
the lifting functor preserving limits of every size. -/
instance addCommGrpCatUliftFunctor_hasSheafCompose {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose AddCommGrpCat.uliftFunctor.{w₂, w₁} where
  isSheaf _ hP := Presheaf.isSheaf_comp_of_isSheaf J _ _ hP

/-- Sheaves of abelian groups on the small affine étale site can be sheafified: the site is
essentially small. -/
instance affineEtaleAbelian_hasSheafify (X : Scheme.{u}) :
    HasSheafify (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) r + 1} _ _

/-- A sheaf of `Λ`-modules on the small étale site of `X`, read as a sheaf of abelian groups on
the small affine étale site: forget the module structure, lift the universe, and restrict along
`Spec`. -/
abbrev affineEtaleAbelianRestriction (Λ : Type r) [Ring Λ] (X : Scheme.{u}) :
    EtaleModules.{u, r} Λ X ⥤ Sheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1} :=
  sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) ⋙
    sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{max (u + 1) r + 1} ⋙
    (AffineEtale.Spec X).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) r + 1}
      (AffineEtale.topology X) X.smallEtaleTopology

/-! ### `Rf_!` is additive and commutes with the shift -/

/-- Derived direct image on bounded below derived categories commutes with the shift. -/
instance etaleModuleDerivedDirectImage_commShift (Λ : Type r) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleDerivedDirectImage.{u, r} Λ f).CommShift ℤ :=
  Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus _

/-- Derived extension by zero on bounded below derived categories commutes with the shift. -/
instance etaleModuleDerivedExtensionByZero_commShift (Λ : Type r) [Ring Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleDerivedExtensionByZero.{u, r} Λ j).CommShift ℤ :=
  Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus _

/-- Derived direct image is an exact functor of triangulated categories. -/
instance etaleModuleDerivedDirectImage_isTriangulated (Λ : Type r) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleDerivedDirectImage.{u, r} Λ f).IsTriangulated :=
  haveI := Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
    (etaleModuleDirectImage.{u, r} Λ f)
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus _

/-- Derived extension by zero is an exact functor of triangulated categories. -/
instance etaleModuleDerivedExtensionByZero_isTriangulated (Λ : Type r) [Ring Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleDerivedExtensionByZero.{u, r} Λ j).IsTriangulated :=
  haveI := Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
    (etaleModuleExtensionByZero.{u, r} Λ j)
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus _

/-- `Rf_! = R(fbar)_* ∘ Rj_!` commutes with the shift, being a composite of two functors that
do. -/
instance derivedLowerShriek_commShift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ] :
    (derivedLowerShriek.{u, r} f j Λ).CommShift ℤ :=
  inferInstanceAs ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion ⋙
    etaleModuleDerivedDirectImage.{u, r} Λ j.toBase).CommShift ℤ)

/-- `Rf_!` is additive, being a composite of exact functors of triangulated categories. -/
instance derivedLowerShriek_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ] :
    (derivedLowerShriek.{u, r} f j Λ).Additive :=
  inferInstanceAs ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion ⋙
    etaleModuleDerivedDirectImage.{u, r} Λ j.toBase).Additive)

/-! ### Comparison of the two Hom presheaves -/

/-- The two presheaves agree, naturally in the object of the small affine étale site:
```
Hom_Y(R(U ⟶ Y)_! Λ, K[n]) = Hom_Y(Rf_!((j_U)_! Λ), K[n]) = Hom_X((j_U)_! Λ, Rf^! K[n])
```
The source gives the equality of the groups and omits "the verification that the transition
maps are given by the transition maps between the objects `Rg_! Λ`". -/
def affineEtaleHomPresheafAdjIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    {Uf : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (adjF : derivedLowerShriek.{u, r} f j Λ ⊣ Uf)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) (n : ℤ) :
    affineEtaleUpperShriekHomPresheaf.{u, r} Λ X (Uf.obj K) n ≅
      affineEtaleLowerShriekHomPresheaf.{u, r} f j Λ K n :=
  letI := adjF.rightAdjointCommShift ℤ
  Functor.isoWhiskerLeft (affineEtaleConstant.{u, r} Λ X).op
    (Functor.isoWhiskerRight
      (preadditiveYoneda.mapIso ((Uf.commShiftIso n).app K).symm)
      AddCommGrpCat.uliftFunctor.{max (u + 1) r + 1}) ≪≫
  Functor.isoWhiskerLeft (affineEtaleConstant.{u, r} Λ X).op
    (adjF.compPreadditiveYonedaIso.app (K⟦n⟧))

/-! ### Stacks Tag 0GLK -/

/-- **D⁺ variant of Stacks Tag 0GLK, the adjunction step.** For an explicit right adjoint
`Uf` of `Rf_!` on `D⁺`, the sheafification of the source's presheaf
`U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n])` on the small affine étale site of `X` is the sheafification of
`U ↦ Hom_X((j_U)_! Λ, Uf K[n])`.  The full statement of the tag, on unbounded derived
categories, is `Stacks.EtaleCohomology.derivedUpperShriek_homology_affineEtale`. -/
@[stacks 0GLK "D⁺ variant: the comparison of the two sheafifications given by the adjunction \
Rf_! ⊣ Uf, for an explicit right adjoint Uf of Rf_! on D⁺"]
def affineEtaleSheafifiedHomIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    {Uf : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (adjF : derivedLowerShriek.{u, r} f j Λ ⊣ Uf)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) (n : ℤ) :
    (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).obj
        (affineEtaleLowerShriekHomPresheaf.{u, r} f j Λ K n) ≅
      (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).obj
        (affineEtaleUpperShriekHomPresheaf.{u, r} Λ X (Uf.obj K) n) :=
  (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).mapIso
    (affineEtaleHomPresheafAdjIso.{u, r} j Λ adjF K n).symm

/-- **D⁺ variant of Stacks Tag 0GLK, the adjunction step, built from a right adjoint of the proper
pushforward.**

`Rf_!` is the composite `R(fbar)_* ∘ Rj_!` of a compactification, and `Rj_!` has the right
adjoint `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroAdj`, extension by zero along
the open immersion being exact. So the adjunction `Rf_! ⊣ Rf^!` is
`Stacks.EtaleCohomology.derivedLowerShriekAdjunctionOfFactors` of a right adjoint `Ubar` of
`R(fbar)_*`, and `Rf^!` is `Ubar ⋙ Rj^{-1}`. -/
@[stacks 0GLK "D⁺ variant: the comparison of the two sheafifications, for an explicit right \
adjoint of the proper pushforward R(fbar)_* on D⁺; the right adjoint of Rj_! along the open \
immersion is constructed"]
def affineEtaleSheafifiedHomIsoOfToBase {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    {Ubar : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)}
    (adjToBase : etaleModuleDerivedDirectImage.{u, r} Λ j.toBase ⊣ Ubar)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) (n : ℤ) :
    (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).obj
        (affineEtaleLowerShriekHomPresheaf.{u, r} f j Λ K n) ≅
      (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).obj
        (affineEtaleUpperShriekHomPresheaf.{u, r} Λ X
          ((Ubar ⋙ etaleModuleDerivedRestriction.{u, r} Λ j.immersion).obj K) n) :=
  affineEtaleSheafifiedHomIso.{u, r} j Λ
    (derivedLowerShriekAdjunctionOfFactors.{u, r} j Λ
      (etaleModuleDerivedExtensionByZeroAdj.{u, r} Λ j.immersion) adjToBase) K n

/-- **D⁺ variant of Stacks Tag 0GLK, with an explicit right adjoint and the sheafified
cohomology identification as an argument.** The full statement of the tag, on unbounded derived
categories and with both of these proved, is
`Stacks.EtaleCohomology.derivedUpperShriek_homology_affineEtale`.

Let `f : X ⟶ Y` be a separated finite type morphism of
quasi-compact and quasi-separated schemes, let `Λ` be a ring, let `K` be an object of
`D⁺(Y_étale, Λ)` and let `n : ℤ`.  Let `Uf` be a right adjoint of `Rf_!`, so `Uf = Rf^!`.  Then
the cohomology sheaf `H^n(Rf^! K)`, restricted to the small affine étale site of `X`, is the
sheaf associated to the presheaf
```
U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n])
```
The right adjoint `Uf` and the adjunction are data: the adjunction is what `Rf^!` is, and its
existence is Stacks Tag 0G2C.  The hypothesis `sheafifiedCohomology` is Stacks Tag 0BKV
together with the source's recollection `Hom_X(j_! Λ, M[n]) = H^n(U, M)`, at the single object
`M = Rf^! K`. -/
@[stacks 0GLK "D⁺ variant, for an explicit right adjoint Uf of Rf_! on D⁺ and with the \
identification of the sheafified Hom presheaf of Uf K with its cohomology sheaf passed as an \
argument; the unbounded statement is derivedUpperShriek_homology_affineEtale"]
def derivedUpperShriekHomologyAffineEtale {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    {Uf : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (adjF : derivedLowerShriek.{u, r} f j Λ ⊣ Uf)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) (n : ℤ)
    (sheafifiedCohomology :
      (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).obj
          (affineEtaleUpperShriekHomPresheaf.{u, r} Λ X (Uf.obj K) n) ≅
        (affineEtaleAbelianRestriction.{u, r} Λ X).obj
          ((DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, r} Λ X) n).obj
            (Uf.obj K))) :
    (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).obj
        (affineEtaleLowerShriekHomPresheaf.{u, r} f j Λ K n) ≅
      (affineEtaleAbelianRestriction.{u, r} Λ X).obj
        ((DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, r} Λ X) n).obj (Uf.obj K)) :=
  affineEtaleSheafifiedHomIso.{u, r} j Λ adjF K n ≪≫ sheafifiedCohomology

end Stacks.EtaleCohomology

end
