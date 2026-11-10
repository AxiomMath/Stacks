module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekQuasiFinite

import StacksCore.Tactic.StacksAttribute

/-!
# Derived upper shriek for locally quasi-finite morphisms

Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes. The direct image with compact
support `f_!` of Stacks 0F6R is exact, so it needs no deriving and induces a functor
`f_! : D(X_étale) ⥤ D(Y_étale)` on unbounded derived categories of abelian étale sheaves.
Its right adjoint `f^!` of Stacks 0F59 is only left exact, and abelian étale sheaves form a
Grothendieck abelian category, so every complex admits a K-injective resolution and `f^!` has a
total right derived functor `Rf^! : D(Y_étale) ⥤ D(X_étale)`. These two are adjoint, which is
Stacks 0F5N.

The same conclusion is proved for sheaves of `Λ`-modules for a ring `Λ`, from a `Λ`-linear lift
of `f_!`; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.SmallEtale.rUpperShriekFunctor` — the total right derived functor `Rf^!`
  of the upper shriek, with `AlgebraicGeometry.SmallEtale.rUpperShriekFunctorUnit` its
  comparison map.
* `AlgebraicGeometry.SmallEtale.moduleFShriekDerivedFunctor` — `f_!` on unbounded derived
  categories of sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekDerivedAdjunction` — **the adjunction
  `f_! ⊣ Rf^!` on unbounded derived categories of abelian étale sheaves**, stated for an
  arbitrary total right derived functor of `f^!`, and
  `AlgebraicGeometry.SmallEtale.fShriekRUpperShriekAdjunction` its instance for
  `rUpperShriekFunctor`.
* `AlgebraicGeometry.SmallEtale.moduleFShriekDerivedAdjunction` — the same adjunction for
  sheaves of `Λ`-modules.

## Implementation notes

The right derived functor is not fixed to a model: `Rf^!` enters the adjunction as an arbitrary
functor on derived categories together with a comparison map making it a total right derived
functor of `f^!` at the quasi-isomorphisms, which pins it down up to canonical isomorphism by
its universal property. Likewise the derived categories are taken with respect to arbitrary
`CategoryTheory.HasDerivedCategory.{w}` instances in a common universe `w` rather than the
standard construction. The concrete choice
`AlgebraicGeometry.SmallEtale.rUpperShriekFunctor` is provided as well, so the statement is not
vacuous.

For a general coefficient ring `Λ` the direct image with compact support is taken as data: the
`Λ`-linear lift of `f_!` is a functor on sheaves of `Λ`-modules together with an isomorphism
identifying it with `f_!` on underlying abelian sheaves. Nothing else about the lift is
assumed. That it has a right adjoint is proved here, in
`AlgebraicGeometry.SmallEtale.isLeftAdjoint_of_forgetModuleSheafIso`, by the special adjoint
functor theorem: forgetting the module structure commutes with sheafification, hence preserves
all colimits, and it reflects them, so the lift inherits the commutation of `f_!` with
colimits. Exactness of the lift follows from exactness of `f_!` and conservativity of
forgetting the module structure, and sheaves of `Λ`-modules on the small étale site are again
Grothendieck abelian, which supplies the K-injective resolutions computing `Rf^!`.

The coefficient universe is the cutoff `max (u + 1) v` at which `f_!` is defined, `u` being the
universe of the schemes; this is what makes the small étale site essentially small in the
coefficient universe, hence supplies sheafification and the Grothendieck abelian structure.

Being locally quasi-finite includes being locally of finite type, and the two are carried as
separate hypotheses `LocallyQuasiFinite` and `LocallyOfFiniteType` here, as they are by `f_!`
itself.

## References

* [Stacks Project, Tag 0F5N](https://stacks.math.columbia.edu/tag/0F5N)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0F59](https://stacks.math.columbia.edu/tag/0F59)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w r

namespace AlgebraicGeometry.SmallEtale

/-- Abelian sheaves on the small étale site of an object of a big étale site, with coefficients
in the universe at which the direct image with compact support is defined. -/
public abbrev AbelianSheaf (B : BigEtaleSite.{u}) (S : B.Scheme) :=
  Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}

/-- Abelian sheaves on a small étale site form a Grothendieck abelian category: the site is
essentially small in the coefficient universe and abelian groups are Grothendieck abelian. This
is what supplies the K-injective resolutions computing unbounded right derived functors. -/
public instance isGrothendieckAbelian_abelianSheaf (B : BigEtaleSite.{u}) (S : B.Scheme) :
    IsGrothendieckAbelian.{max (u + 1) v} (AbelianSheaf.{u, v} B S) := by
  have : EssentiallySmall.{max (u + 1) v} (SmallEtale B S.obj S.property) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

section Abelian

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The direct image with compact support of a locally quasi-finite morphism preserves finite
limits, being exact by Stacks 0F5F. -/
public instance fShriekFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (fShriekFunctor.{u, v} B f) :=
  ((exactFunctor_iff _).mp (fShriekFunctor_exact.{u, v} B f)).1

/-- The direct image with compact support of a locally quasi-finite morphism preserves finite
colimits, being exact by Stacks 0F5F. -/
public instance fShriekFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (fShriekFunctor.{u, v} B f) :=
  ((exactFunctor_iff _).mp (fShriekFunctor_exact.{u, v} B f)).2

/-- The direct image with compact support is an additive functor, preserving binary products. -/
public instance fShriekFunctor_additive : (fShriekFunctor.{u, v} B f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The upper shriek `f^!` is an additive functor, being right adjoint to an additive one. -/
public instance fUpperShriekFunctor_additive : (fUpperShriekFunctor.{u, v} B f).Additive :=
  (fShriekAdjunction.{u, v} B f).right_adjoint_additive

variable [HasDerivedCategory.{w} (AbelianSheaf.{u, v} B X)]
  [HasDerivedCategory.{w} (AbelianSheaf.{u, v} B Y)]

/-- The upper shriek of a locally quasi-finite morphism, read on the unbounded homotopy category
and composed with the localization, has a pointwise total right derived functor: abelian étale
sheaves are Grothendieck abelian, so every complex admits a K-injective resolution. -/
public instance fUpperShriekFunctor_hasPointwiseRightDerivedFunctor :
    ((fUpperShriekFunctor.{u, v} B f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (AbelianSheaf.{u, v} B Y) (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K

/-- `Rf^!`, a total right derived functor of the upper shriek `f^!` of Stacks 0F59, on unbounded
derived categories of abelian étale sheaves. -/
public def rUpperShriekFunctor :
    DerivedCategory (AbelianSheaf.{u, v} B Y) ⥤ DerivedCategory (AbelianSheaf.{u, v} B X) :=
  ((fUpperShriekFunctor.{u, v} B f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (AbelianSheaf.{u, v} B Y) (ComplexShape.up ℤ))

/-- The comparison map exhibiting `rUpperShriekFunctor` as a right derived functor of `f^!`. -/
public def rUpperShriekFunctorUnit :
    (fUpperShriekFunctor.{u, v} B f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ rUpperShriekFunctor.{u, v, w} B f :=
  ((fUpperShriekFunctor.{u, v} B f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (AbelianSheaf.{u, v} B Y) (ComplexShape.up ℤ))

/-- `rUpperShriekFunctor` is a total right derived functor of `f^!` at the quasi-isomorphisms,
with comparison map `rUpperShriekFunctorUnit`. -/
public instance rUpperShriekFunctor_isRightDerivedFunctor :
    (rUpperShriekFunctor.{u, v, w} B f).IsRightDerivedFunctor
      (rUpperShriekFunctorUnit.{u, v, w} B f)
      (HomotopyCategory.quasiIso (AbelianSheaf.{u, v} B Y) (ComplexShape.up ℤ)) := by
  unfold rUpperShriekFunctor rUpperShriekFunctorUnit
  infer_instance

/-- **Stacks 0F5N.** Let `f : X ⟶ Y` be a locally quasi-finite morphism. The direct image with
compact support `f_!` of Stacks 0F6R, which is exact and therefore induces a functor
`D(X_étale) ⥤ D(Y_étale)` on unbounded derived categories of abelian étale sheaves, is left
adjoint to any total right derived functor `Rf^! : D(Y_étale) ⥤ D(X_étale)` of the upper shriek
`f^!` of Stacks 0F59. -/
@[stacks 0F5N "abelian coefficients, the case Λ = ℤ", sga "4 XVIII 3.1.5" "special case"]
public def fShriekDerivedAdjunction
    (RfUpperShriek : DerivedCategory (AbelianSheaf.{u, v} B Y) ⥤
      DerivedCategory (AbelianSheaf.{u, v} B X))
    (β : (fUpperShriekFunctor.{u, v} B f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfUpperShriek)
    [RfUpperShriek.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso (AbelianSheaf.{u, v} B Y) (ComplexShape.up ℤ))] :
    (fShriekFunctor.{u, v} B f).mapDerivedCategory ⊣ RfUpperShriek :=
  Stacks.DerivedFunctor.derivedAdjunction (fShriekAdjunction.{u, v} B f) RfUpperShriek β
    fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K

/-- **Stacks 0F5N** for the chosen total right derived functor: `f_!` on unbounded derived
categories of abelian étale sheaves is left adjoint to `rUpperShriekFunctor`. -/
@[stacks 0F5N "abelian coefficients, for the chosen total right derived functor of f^!"]
public def fShriekRUpperShriekAdjunction :
    (fShriekFunctor.{u, v} B f).mapDerivedCategory ⊣ rUpperShriekFunctor.{u, v, w} B f :=
  fShriekDerivedAdjunction.{u, v, w} B f _ (rUpperShriekFunctorUnit.{u, v, w} B f)

end Abelian

section Module

/-- The forgetful functor from `Λ`-modules to types preserves filtered colimits of any size,
being the composite of two functors that do. -/
private theorem preservesFilteredColimits_forgetModuleCat (Λ : Type r) [Ring Λ] :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{w} Λ)) := by
  have : PreservesColimitsOfSize.{w, w} (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{w, r, w, w} Λ
  exact comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) (CategoryTheory.forget AddCommGrpCat.{w})

/-- `Λ`-modules in a universe into which `Λ` embeds form a Grothendieck abelian category: AB5 is
reflected by the exact forgetful functor to abelian groups. -/
private theorem isGrothendieckAbelian_moduleCat (Λ : Type r) [Ring Λ] [UnivLE.{r, w}] :
    IsGrothendieckAbelian.{w} (ModuleCat.{w} Λ) := by
  refine { ab5OfSize := ⟨fun D _ _ => ?_⟩ }
  exact HasExactColimitsOfShape.domain_of_functor D
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})

/-- Sheaves of `Λ`-modules on the small étale site of an object of a big étale site, with
coefficients in the universe at which the direct image with compact support is defined. -/
public abbrev ModuleSheaf (B : BigEtaleSite.{u}) (S : B.Scheme) (Λ : Type r) [Ring Λ] :=
  Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) v r} Λ)

variable (B : BigEtaleSite.{u}) (S : B.Scheme) (Λ : Type r) [Ring Λ]

/-- Sheafification is available for presheaves of `Λ`-modules on the small étale site, the site
being essentially small in the coefficient universe and the coefficient category having the
required colimits. -/
public instance hasSheafify_moduleSheaf :
    HasSheafify (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) v r} Λ) := by
  have := preservesFilteredColimits_forgetModuleCat.{max (u + 1) v r} Λ
  have : EssentiallySmall.{max (u + 1) v r} (SmallEtale B S.obj S.property) := inferInstance
  exact hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v r} _ _

/-- Sheaves of `Λ`-modules on the small étale site form a Grothendieck abelian category. This is
what supplies the K-injective resolutions computing unbounded right derived functors. -/
public instance isGrothendieckAbelian_moduleSheaf :
    IsGrothendieckAbelian.{max (u + 1) v r} (ModuleSheaf.{u, v, r} B S Λ) := by
  have := isGrothendieckAbelian_moduleCat.{max (u + 1) v r} Λ
  have := preservesFilteredColimits_forgetModuleCat.{max (u + 1) v r} Λ
  have : EssentiallySmall.{max (u + 1) v r} (SmallEtale B S.obj S.property) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- The functor forgetting the `Λ`-module structure of a sheaf of `Λ`-modules on the small étale
site, leaving the underlying abelian sheaf. -/
public abbrev forgetModuleSheaf :
    ModuleSheaf.{u, v, r} B S Λ ⥤ AbelianSheaf.{u, max v r} B S :=
  sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r})

/-- Postcomposing sheaves with a finite-limit-preserving functor preserves finite limits, limits
of sheaves being computed as limits of presheaves. -/
private theorem preservesFiniteLimits_sheafCompose {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {A A' : Type*} [Category* A] [Category* A']
    [HasFiniteLimits A] (F : A ⥤ A') [PreservesFiniteLimits F] [J.HasSheafCompose F] :
    PreservesFiniteLimits (sheafCompose J F) := by
  have : PreservesFiniteLimits ((Functor.whiskeringRight Cᵒᵖ A A').obj F) :=
    ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteLimits (sheafCompose J F ⋙ sheafToPresheaf J A') := by
    change PreservesFiniteLimits (sheafToPresheaf J A ⋙ (Functor.whiskeringRight Cᵒᵖ A A').obj F)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J A')

/-- Forgetting the module structure of an étale sheaf of `Λ`-modules preserves finite limits,
restriction of scalars along `ℤ → Λ` being left exact. -/
public theorem preservesFiniteLimits_forgetModuleSheaf :
    PreservesFiniteLimits (forgetModuleSheaf.{u, v, r} B S Λ) :=
  preservesFiniteLimits_sheafCompose _ _

/-- Sheafification of presheaves of `Λ`-modules on the small étale site commutes with forgetting
the module structure: the forgetful functor preserves the colimits over the covers and the
limits over the multicospans out of which the sheafification is built. -/
public theorem preservesSheafification_forgetModuleCat :
    (SmallEtale.topology B S.obj S.property).PreservesSheafification
      (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r}) :=
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{max (u + 1) v r} Λ) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, max (u + 1) v r, r}
  have := preservesFilteredColimits_forgetModuleCat.{max (u + 1) v r} Λ
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (CategoryTheory.forget (ModuleCat.{max (u + 1) v r} Λ)) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v r, max (u + 1) v r,
      u + 1, u + 1} _
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v r}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v r, max (u + 1) v r,
      u + 1, u + 1} _
  CategoryTheory.GrothendieckTopology.instPreservesSheafification
    (SmallEtale.topology B S.obj S.property)
    (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r})

/-- Forgetting the module structure of an étale sheaf of `Λ`-modules preserves all colimits:
it does so on presheaves, and it commutes with sheafification. -/
public theorem preservesColimitsOfSize_forgetModuleSheaf :
    PreservesColimitsOfSize.{max (u + 1) v r, max (u + 1) v r}
      (forgetModuleSheaf.{u, v, r} B S Λ) :=
  have := preservesSheafification_forgetModuleCat.{u, v, r} B S Λ
  { preservesColimitsOfShape := fun {K} _ =>
      preservesColimitsOfShape_sheafCompose _ _ K }

section Shriek

variable {X Y : B.Scheme}

/-- A `Λ`-linear lift of the direct image with compact support preserves finite limits: `f_!` is
exact by Stacks 0F5F, and forgetting the module structure is left exact and conservative. -/
public theorem preservesFiniteLimits_of_forgetModuleSheafIso (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f) :
    PreservesFiniteLimits fShriekMod := by
  have := preservesFiniteLimits_forgetModuleSheaf.{u, v, r} B X Λ
  have := preservesFiniteLimits_forgetModuleSheaf.{u, v, r} B Y Λ
  have : ReflectsFiniteLimits (forgetModuleSheaf.{u, v, r} B Y Λ) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  have : PreservesFiniteLimits (forgetModuleSheaf.{u, v, r} B X Λ ⋙
    fShriekFunctor.{u, max v r} B f) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ) :=
    preservesFiniteLimits_of_natIso hlift.symm
  exact preservesFiniteLimits_of_reflects_of_preserves fShriekMod
    (forgetModuleSheaf.{u, v, r} B Y Λ)

/-- A `Λ`-linear lift of the direct image with compact support is additive, preserving binary
products by left exactness. -/
public theorem additive_of_forgetModuleSheafIso (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f) :
    fShriekMod.Additive :=
  have := preservesFiniteLimits_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  Functor.additive_of_preserves_binary_products _

/-- A `Λ`-linear lift of the direct image with compact support has a right adjoint. The lift
preserves all colimits, forgetting the module structure both preserving and reflecting them and
`f_!` preserving them by Stacks 0F5F; étale sheaves of `Λ`-modules are cocomplete, locally
small, well-copowered and have a separator, so the special adjoint functor theorem applies. -/
public theorem isLeftAdjoint_of_forgetModuleSheafIso (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f) :
    fShriekMod.IsLeftAdjoint :=
  have := preservesColimitsOfSize_forgetModuleSheaf.{u, v, r} B X Λ
  have := preservesColimitsOfSize_forgetModuleSheaf.{u, v, r} B Y Λ
  have := fShriekFunctor_preservesColimitsOfSize.{u, max v r} B f
  have : PreservesColimitsOfSize.{max (u + 1) v r, max (u + 1) v r}
      (fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ) :=
    preservesColimits_of_natIso hlift.symm
  have : PreservesColimitsOfSize.{max (u + 1) v r, max (u + 1) v r} fShriekMod :=
    { preservesColimitsOfShape := fun {K} _ =>
        have : HasColimitsOfShape K (ModuleSheaf.{u, v, r} B Y Λ) :=
          Sheaf.instHasColimitsOfShape
        have : ReflectsColimitsOfShape K (forgetModuleSheaf.{u, v, r} B Y Λ) :=
          reflectsColimitsOfShape_of_reflectsIsomorphisms
        preservesColimitsOfShape_of_reflects_of_preserves fShriekMod
          (forgetModuleSheaf.{u, v, r} B Y Λ) }
  have : HasColimitsOfSize.{max (u + 1) v r, max (u + 1) v r}
      (ModuleSheaf.{u, v, r} B X Λ) := Sheaf.instHasColimitsOfSize
  isLeftAdjoint_of_preservesColimits_of_isSeparating.{max (u + 1) v r}
    (isSeparator_separator _) _

variable [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B Y Λ)]

/-- The upper shriek `f^!` on sheaves of `Λ`-modules, read on unbounded homotopy categories and
composed with the localization. This is the functor whose total right derived functor is
`Rf^!`; it is the chosen right adjoint of the `Λ`-linear lift of `f_!`. -/
public abbrev moduleUpperShriekQh (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f) :
    HomotopyCategory (ModuleSheaf.{u, v, r} B Y Λ) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleSheaf.{u, v, r} B X Λ) :=
  let := additive_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  let := isLeftAdjoint_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  let := (Adjunction.ofIsLeftAdjoint fShriekMod).right_adjoint_additive
  fShriekMod.rightAdjoint.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- `f_!` on unbounded derived categories of étale sheaves of `Λ`-modules: a `Λ`-linear lift of
the direct image with compact support is exact, so it needs no deriving and induces a functor
`D(X_étale, Λ) ⥤ D(Y_étale, Λ)` directly. -/
public def moduleFShriekDerivedFunctor (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f) :
    DerivedCategory (ModuleSheaf.{u, v, r} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, v, r} B Y Λ) :=
  let := additive_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  let := preservesFiniteLimits_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  let := isLeftAdjoint_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  let : PreservesFiniteColimits fShriekMod := ⟨fun _ _ _ => inferInstance⟩
  fShriekMod.mapDerivedCategory

/-- **Stacks 0F5N** for a general coefficient ring. Let `f : X ⟶ Y` be a locally quasi-finite
morphism and let `fShriekMod` be a `Λ`-linear lift of the direct image with compact support
`f_!` of Stacks 0F6R. The lift is then exact, so it induces a functor
`D(X_étale, Λ) ⥤ D(Y_étale, Λ)`, it has a right adjoint `f^!`, and that functor is left adjoint
to any total right derived functor `Rf^! : D(Y_étale, Λ) ⥤ D(X_étale, Λ)` of `f^!`. -/
@[stacks 0F5N "general coefficient ring Λ, from a Λ-linear lift of f_!"]
public def moduleFShriekDerivedAdjunction (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f)
    (RfUpperShriek : DerivedCategory (ModuleSheaf.{u, v, r} B Y Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, v, r} B X Λ))
    (β : moduleUpperShriekQh.{u, v, w, r} B Λ f fShriekMod hlift ⟶
      DerivedCategory.Qh ⋙ RfUpperShriek)
    [RfUpperShriek.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, v, r} B Y Λ) (ComplexShape.up ℤ))] :
    moduleFShriekDerivedFunctor.{u, v, w, r} B Λ f fShriekMod hlift ⊣ RfUpperShriek :=
  let := additive_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  let := preservesFiniteLimits_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  let := isLeftAdjoint_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  let : PreservesFiniteColimits fShriekMod := ⟨fun _ _ _ => inferInstance⟩
  let := (Adjunction.ofIsLeftAdjoint fShriekMod).right_adjoint_additive
  Stacks.DerivedFunctor.derivedAdjunction (Adjunction.ofIsLeftAdjoint fShriekMod)
    RfUpperShriek β fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K

end Shriek

end Module

end AlgebraicGeometry.SmallEtale

end
