module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of modules to a localized site: K-injectives and the derived adjunction

Let `(C, J)` be a site, `R` a sheaf of rings on it and `U` an object of `C`. Restriction along
`Over.forget U` sends a sheaf of `R`-modules to a sheaf of `R.over U`-modules on the localized
site `C/U`; it is Mathlib's `SheafOfModules.overFunctor R U`, and its left adjoint is extension
by zero `j_{U!} = SheafOfModules.pullback (𝟙 (R.over U))`, whose exactness is Stacks 03DJ.

Two consequences of that adjunction are proved here.

The first is that restriction carries K-injective complexes to K-injective complexes: the
adjoint criterion for K-injectivity (Stacks 08BJ) applies with `v = j_{U!}` the exact left
adjoint and `u` the restriction, because exactness of `j_{U!}` makes it carry acyclic complexes
to acyclic complexes.

The second is the derived form of the adjunction itself. On a ringed site both `j_{U!}` and
restriction are exact, so each descends to the unbounded derived category, and the degreewise
adjunction between the induced functors on cochain complexes localizes to an adjunction
`Rj_{U!} ⊣ Rrestriction`. The unit and counit are therefore the images of the underived ones
under the localization comparisons, which is what makes this *the* canonical derived
adjunction rather than one of several.

Exactness of restriction is the one point needing an argument. Left exactness is
`SheafOfModules.preservesFiniteLimits_pushforward`, which holds for the direct image along any
continuous functor. Right exactness is proved on sections: an epimorphism of sheaves of modules
is locally surjective, local surjectivity is preserved by whiskering along `(Over.forget U).op`,
and a locally surjective morphism of sheaves is an epimorphism; a left exact additive functor
between abelian categories preserving epimorphisms preserves homology and so is right exact.

## Main results

* `Stacks.Cohomology.Localization.isKInjective_over`: restriction to the slice site over `U`
  preserves K-injective cochain complexes of sheaves of modules.
* `Stacks.Cohomology.Localization.restriction_exact`: restriction to the slice site over an
  object of a ringed site is exact.
* `Stacks.Cohomology.Localization.derivedExtensionByZeroRestrictionAdjunction`: extension by
  zero is left adjoint to restriction on unbounded derived categories of modules.
* `Stacks.Cohomology.Localization.sectionsRestrictionIso`: sections of a sheaf of modules over
  an object are the global sections of its restriction to the site localized at that object.

## Implementation notes

K-injectivity of the restriction is stated for an arbitrary sheaf of rings, with no
commutativity and no sheafification hypotheses: the exact left adjoint argument needs none of
them. The derived adjunction is stated for a ringed site with its structure sheaf, module
sections and site all in one universe, because exactness of restriction is proved through local
surjectivity of `AddCommGrpCat`-valued sheaves, and sheafification there is available only once
the sections are large enough to contain the site.

No new functor is introduced. `j_{U!}` is `SheafOfModules.pullback` for `Over.forget U` with the
identity map of the restricted sheaf of rings, and restriction is `SheafOfModules.overFunctor`,
exactly as in Stacks 03DI.

`sectionsRestrictionIso` is the underived comparison of sections that Stacks 0D6F derives; the
derived statement itself is not here, because it needs functorial K-injective resolutions in a
Grothendieck abelian category (Stacks 079P), which this branch does not have.

## References

* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Stacks.Cohomology.Localization

universe u v u₁ u₂ v₁ v₂

/-- Restriction of sheaves of modules to a slice site is additive. Stated here because
`SheafOfModules.overFunctor` is a `def`, which instance search does not unfold, so neither
`Stacks.AlgebraicGeometry.RestrictionExact.additive_pushforward` nor
`SheafOfModules.instAdditiveOverFunctor` applies to it as stated. -/
instance additive_overFunctor {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) :
    (SheafOfModules.overFunctor.{v} R U).Additive :=
  inferInstanceAs (SheafOfModules.pushforward.{v}
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).Additive

/-- **Stacks 08FI.** Restriction to the slice site over an object preserves K-injective
complexes of sheaves of modules. Extension by zero is an exact left adjoint of the restriction,
so the adjoint criterion for K-injectivity applies. -/
@[stacks 08FI, instance]
theorem isKInjective_over {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) (U : C)
    (I : CochainComplex (SheafOfModules.{u} R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{u} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let F := SheafOfModules.overFunctor.{u} R U
  let G := SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  have hG := (exactFunctor_iff G).mp
    (Stacks.Sites.ExtensionByZero.extensionByZero_exact J R U)
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have : PreservesFiniteLimits G := hG.1
  have : PreservesFiniteColimits G := hG.2
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact F G
    (SheafOfModules.pullbackPushforwardAdjunction (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) I

/-- A functor on the homotopy category of a Grothendieck abelian category has
an unbounded right derived functor, computed on functorial K-injective resolutions. -/
@[sga "4 XVII 4.1.2" "partial"]
noncomputable instance hasRightDerivedFunctorOfGrothendieck
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian A]
    {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have : F.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v₁, v₂,
      0, u₁, u₂, 0}
      F (fun K => ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion A).app K,
        inferInstance, inferInstance⟩)).1
  infer_instance

section RingedSite

/-- Extension by zero of modules on a ringed site is additive, being a left adjoint between
additive categories. -/
noncomputable instance additive_extensionByZero (X : RingedSite.{u, u, u}) (U : X.C) :
    (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Extension by zero of modules on a ringed site preserves finite colimits, being the right
exact half of Stacks 03DJ. -/
noncomputable instance preservesFiniteColimits_extensionByZero
    (X : RingedSite.{u, u, u}) (U : X.C) :
    PreservesFiniteColimits (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))) :=
  ((exactFunctor_iff _).mp
    (Stacks.Sites.ExtensionByZero.extensionByZero_exact X.J
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)).2

/-- Restriction to the slice site over `U` is exact, for sheaves of modules whose sections are
large enough to contain the site. Left exactness is the direct image part of Stacks 04BD (2);
right exactness is local surjectivity of an epimorphism, transported by whiskering along
`(Over.forget U).op`. -/
private theorem restriction_exact_of_univLE [UnivLE.{max u v, v}]
    (X : RingedSite.{u, u, u}) (U : X.C) :
    exactFunctor _ _
      (SheafOfModules.overFunctor.{v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) := by
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hSheafify : ∀ {D : Type u} [Category.{u} D] (K : GrothendieckTopology D),
      HasSheafify K AddCommGrpCat.{v} ∧ K.WEqualsLocallyBijective AddCommGrpCat.{v} := fun K =>
    ⟨GrothendieckTopology.hasSheafify_addCommGrpCat.{v, u, u} K,
      SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{v, u, u} K⟩
  obtain ⟨_, _⟩ := hSheafify X.J
  obtain ⟨_, _⟩ := hSheafify (X.J.over U)
  let F := SheafOfModules.overFunctor.{v} R U
  have hLim : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.pushforward.{v}
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))))
  have hCol : PreservesFiniteColimits F := by
    have : Functor.PreservesEpimorphisms F := ⟨fun {A B} f hf => by
      have : Epi f := hf
      have hlocal : Presheaf.IsLocallySurjective X.J
          ((SheafOfModules.toSheaf R).map f).hom := by
        have : Epi ((SheafOfModules.toSheaf R).map f) :=
          preserves_epi_of_preservesColimit (SheafOfModules.toSheaf R) f
        exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat
          ((SheafOfModules.toSheaf R).map f)).mpr inferInstance
      have hOver : Presheaf.IsLocallySurjective (X.J.over U)
          ((SheafOfModules.toSheaf (R.over U)).map (F.map f)).hom :=
        Presheaf.isLocallySurjective_whisker
          (J := X.J.over U) (K := X.J) (H := Over.forget U)
          ((SheafOfModules.toSheaf R).map f).hom
      let T := SheafOfModules.toSheaf (R.over U)
      exact T.epi_of_epi_map
        ((Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat (T.map (F.map f))).mp hOver)⟩
    have : F.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels F
    have : ∀ {A B : SheafOfModules R} (f : A ⟶ B),
        PreservesColimit (parallelPair f 0) F := fun f =>
          Functor.PreservesHomology.preservesCokernel F f
    exact Functor.preservesFiniteColimits_of_preservesCokernels F
  exact (exactFunctor_iff F).2 ⟨hLim, hCol⟩

/-- Restriction to the slice site over an object of a ringed site is exact. -/
theorem restriction_exact (X : RingedSite.{u, u, u}) (U : X.C) :
    exactFunctor _ _
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
  restriction_exact_of_univLE X U

/-- Restriction to the slice site over an object of a ringed site preserves finite limits. -/
noncomputable instance preservesFiniteLimits_restriction
    (X : RingedSite.{u, u, u}) (U : X.C) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
  ((exactFunctor_iff _).mp (restriction_exact X U)).1

/-- Restriction to the slice site over an object of a ringed site preserves finite colimits. -/
noncomputable instance preservesFiniteColimits_restriction
    (X : RingedSite.{u, u, u}) (U : X.C) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
  ((exactFunctor_iff _).mp (restriction_exact X U)).2

/-- **Stacks 08FJ.** On the unbounded derived categories of modules over a ringed site,
extension by zero along the localization at an object is left adjoint to restriction to the
localized site. The adjunction is the canonical one: it is obtained by localizing the
degreewise underived adjunction, so its unit and counit are the images of the underived unit
and counit under the localization comparisons. -/
@[stacks 08FJ]
noncomputable def derivedExtensionByZeroRestrictionAdjunction
    (X : RingedSite.{u, u, u}) (U : X.C)
    [HasDerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))] :
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    let jShriek := SheafOfModules.pullback.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
    let restriction := SheafOfModules.overFunctor R U
    jShriek.mapDerivedCategory ⊣ restriction.mapDerivedCategory := by
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let jShriek := SheafOfModules.pullback.{u}
    (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  let restriction := SheafOfModules.overFunctor R U
  let adj : jShriek ⊣ restriction :=
    SheafOfModules.pullbackPushforwardAdjunction
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  let : CatCommSq (jShriek.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q jShriek.mapDerivedCategory :=
    ⟨jShriek.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (restriction.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q restriction.mapDerivedCategory :=
    ⟨restriction.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _

/-- Sections of a sheaf of modules over an object of a ringed site, with the module structure
forgotten. -/
noncomputable abbrev sectionsOverObject (X : RingedSite.{u, u, u}) (U : X.C) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (Opposite.op U) ⋙
    forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (Opposite.op U)))
      AddCommGrpCat.{u}

/-- Global sections of a sheaf of modules on the site localized at `U`, with the module
structure forgotten. The final object of `C/U` is the identity arrow of `U`. -/
noncomputable abbrev sectionsOnSlice (X : RingedSite.{u, u, u}) (U : X.C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⥤
      AddCommGrpCat.{u} :=
  SheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
      (Opposite.op (Over.mk (𝟙 U))) ⋙
    forget₂ (ModuleCat.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj
      (Opposite.op (Over.mk (𝟙 U))))) AddCommGrpCat.{u}

/-- Taking sections over an object is an additive functor. -/
instance additive_sectionsOverObject (X : RingedSite.{u, u, u}) (U : X.C) :
    (sectionsOverObject X U).Additive where
  map_add := rfl

/-- Taking global sections on the slice site is an additive functor. -/
instance additive_sectionsOnSlice (X : RingedSite.{u, u, u}) (U : X.C) :
    (sectionsOnSlice X U).Additive where
  map_add := rfl

/-- Sections over `U` are the global sections of the restriction to the site localized at `U`:
both are the sections of the underlying presheaf at the identity arrow of `U`. -/
noncomputable def sectionsRestrictionIso (X : RingedSite.{u, u, u}) (U : X.C) :
    sectionsOverObject X U ≅
      SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
        sectionsOnSlice X U := by
  refine NatIso.ofComponents (fun F => eqToIso (by
    dsimp [sectionsOverObject, sectionsOnSlice, SheafOfModules.evaluation,
      SheafOfModules.overFunctor]; rfl)) ?_
  intro F G f
  dsimp [sectionsOverObject, sectionsOnSlice, SheafOfModules.overFunctor,
    SheafOfModules.evaluation]
  rfl

/-- The sections functor on complexes, followed by localization. -/
noncomputable abbrev homotopySectionsOverObject (X : RingedSite.{u, u, u}) (U : X.C)
    [HasDerivedCategory AddCommGrpCat.{u}] :
    HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (sectionsOverObject X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Restriction of complexes to the slice, followed by localization. -/
noncomputable abbrev homotopyRestriction (X : RingedSite.{u, u, u}) (U : X.C)
    [HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))] :
    HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
  (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- Global sections of complexes on the slice, followed by localization. -/
noncomputable abbrev homotopySectionsOnSlice (X : RingedSite.{u, u, u}) (U : X.C)
    [HasDerivedCategory AddCommGrpCat.{u}] :
    HomotopyCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
      (ComplexShape.up ℤ) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (sectionsOnSlice X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Unbounded derived sections over `U`. -/
noncomputable abbrev derivedSectionsOverObject (X : RingedSite.{u, u, u}) (U : X.C)
    [HasDerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory AddCommGrpCat.{u}] :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (homotopySectionsOverObject X U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- Unbounded derived restriction to the localized site. -/
noncomputable abbrev derivedRestriction (X : RingedSite.{u, u, u}) (U : X.C)
    [HasDerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))] :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
  (homotopyRestriction X U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- Unbounded derived global sections on the localized site. -/
noncomputable abbrev derivedSectionsOnSlice (X : RingedSite.{u, u, u}) (U : X.C)
    [HasDerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]
    [HasDerivedCategory AddCommGrpCat.{u}] :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (homotopySectionsOnSlice X U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
      (ComplexShape.up ℤ))

/-- Cohomology over `U` agrees naturally with cohomology of the restricted
derived module on the slice site `C/U`. -/
@[stacks 0D6F]
noncomputable def cohomologyOverObjectIsoRestriction
    (X : RingedSite.{u, u, u}) (U : X.C)
    [HasDerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]
    [HasDerivedCategory AddCommGrpCat.{u}] (p : ℤ) :
    derivedSectionsOverObject X U ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} p ≅
    derivedRestriction X U ⋙ derivedSectionsOnSlice X U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} p :=
  by
    let c := ComplexShape.up ℤ
    let C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    let D := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
    let qX : HomotopyCategory C c ⥤ DerivedCategory C := DerivedCategory.Qh
    let qU : HomotopyCategory D c ⥤ DerivedCategory D := DerivedCategory.Qh
    let j := SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let jHC := j.mapHomotopyCategory c
    let γU := (homotopySectionsOnSlice X U).totalRightDerivedUnit qU
      (HomotopyCategory.quasiIso D c)
    let γR := (homotopyRestriction X U).totalRightDerivedUnit qX
      (HomotopyCategory.quasiIso C c)
    let hsec : homotopySectionsOverObject X U ≅
        jHC ⋙ homotopySectionsOnSlice X U := by
      change (sectionsOverObject X U).mapHomotopyCategory c ⋙
          DerivedCategory.Qh ≅
        jHC ⋙ ((sectionsOnSlice X U).mapHomotopyCategory c ⋙
          DerivedCategory.Qh)
      exact Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso (sectionsRestrictionIso X U).symm c).symm
        DerivedCategory.Qh ≪≫ Functor.associator _ _ _
    let α : homotopySectionsOverObject X U ⟶
        qX ⋙ (derivedRestriction X U ⋙ derivedSectionsOnSlice X U) :=
      hsec.hom ≫
        Functor.whiskerLeft jHC γU ≫
        (Functor.associator jHC qU (derivedSectionsOnSlice X U)).inv ≫
        Functor.whiskerRight γR (derivedSectionsOnSlice X U) ≫
        (Functor.associator _ _ _).hom
    have hα : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
        IsIso (α.app ((HomotopyCategory.quotient C c).obj I)) := by
      intro I hI
      let I' : CochainComplex D ℤ := (j.mapHomologicalComplex c).obj I
      have : I'.IsKInjective :=
        isKInjective_over X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
      have := derivedUnit_isIsoOnKInjective
        (homotopyRestriction X U) (derivedRestriction X U) γR I
      have := derivedUnit_isIsoOnKInjective
        (homotopySectionsOnSlice X U) (derivedSectionsOnSlice X U) γU I'
      have hU : IsIso (γU.app (jHC.obj ((HomotopyCategory.quotient C c).obj I))) := by
        change IsIso (γU.app ((HomotopyCategory.quotient D c).obj I'))
        infer_instance
      dsimp [α]
      infer_instance
    have := rightDerived_of_kInjectives (homotopySectionsOverObject X U)
      (derivedRestriction X U ⋙ derivedSectionsOnSlice X U) α hα
    let e := Functor.rightDerivedNatIso (derivedSectionsOverObject X U)
      (derivedRestriction X U ⋙ derivedSectionsOnSlice X U)
      ((homotopySectionsOverObject X U).totalRightDerivedUnit qX
        (HomotopyCategory.quasiIso C c)) α
      (HomotopyCategory.quasiIso C c) (Iso.refl _)
    exact Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p)

end RingedSite

end Stacks.Cohomology.Localization

end
