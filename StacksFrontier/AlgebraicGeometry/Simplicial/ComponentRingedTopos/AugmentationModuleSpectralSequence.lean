module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedPlusAugmentedComplex
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Augmentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModuleCechComplex
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentTotalAcyclicity
import StacksCore.Tactic.StacksAttribute

/-!
# The spectral sequence of a ringed augmentation of a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE), `a` an augmentation of `S` towards a site
`(D, K)` (Stacks 0D6Z) and `A` a ringed augmentation (Stacks 0D9D): sheaves of rings `O` on the
total site and `O_D` on `(D, K)` with `a^♯ : O_D ⟶ a_*O`, so that
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` and `a_p = a ∘ g_p` are morphisms of ringed topoi.
Stacks 0D7F asserts that for `M` in `D⁺(O)` there is a spectral sequence in `Mod(O_D)`

```
E_1^{p,q} = R^q a_{p,*} M_p  ⇒  R^{p+q} a_* M,
```

functorial in `M`. This file constructs it.

## The construction

It is the source's. Represent `M` by a bounded below complex of injective `O`-modules `I^•` and
take the double complex `A^{p,q} = a_{p,*} I^q_p`, with horizontal maps those of the complex
`0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …` of Stacks 0D7D and vertical maps the differentials of
`I^•`.

* The rows are exact in positive degrees with `a_* I^q` as kernel in degree `0` (Stacks 0D7D), so
  the total complex computes `a_* I^•`, that is `R a_* M` (Stacks 0133).
* Restriction to `C_p` is exact (Stacks 09WG), so `I^•_p` represents `M_p`; its terms are totally
  acyclic on `C_p` (Stacks 0D73), hence acyclic for `a_{p,*}` (Stacks 0731 (4)), so the columns
  compute `R^q a_{p,*} M_p` by Leray's acyclicity lemma (Stacks 015E).
* The spectral sequence is the one of the filtration by `p` (Stacks 0132); homotopic maps of
  complexes give the same map from the first page on, so it is functorial in `M`.

The general machinery is
`StacksFrontier/Algebra/Homology/SpectralSequence/DerivedPlusAugmentedComplex.lean`; this file
supplies the two facts about sheaves of modules that it needs, the acyclicity of the restrictions
of an injective module for the component direct images, and the complex of Stacks 0D7D.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.HigherDirectImageSpectralSequence`:
  the statement of Stacks 0D7F as a structure: a functor from `D⁺(O)` to cohomological spectral
  sequences of `O_D`-modules, an identification of its first page with `R^q a_{p,*} M_p` natural
  in `M`, the vanishing of the first page in negative columns, and the abutment to
  `R^{p+q} a_* M`.
* `HigherDirectImageSpectralSequence.ofAugmentedComplex`: the spectral sequence of an augmented
  functorial complex with the exactness properties of the complex of Stacks 0D7D.

## Implementation notes

The spectral sequence is presented from its first page: its zeroth page is the double complex of
a chosen resolution, which is not functorial in `M`. The first page is indexed by `ℤ × ℤ`, an
object of `D⁺(O)` being bounded below in an arbitrary degree; it vanishes in the negative
columns.

The derived categories are arbitrary models, `HasDerivedCategory` instances taken as arguments.
Those of the component sites and of `(D, K)` are taken with morphisms in the universe of the
situation, the universe in which Stacks 0731 (4) is available; the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` is one.

The direct image of modules along a morphism of ringed topoi is
`AlgebraicGeometry.RingedToposHom.pushforwardModules`. The acyclicity of Stacks 0731 (4) is
stated for the direct image through the four-field morphism of the modules development; the two
are identified by `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`, and the first page
is transported along it.

## References

* [Stacks Project, Tag 0D7F](https://stacks.math.columbia.edu/tag/0D7F)
* [Stacks Project, Tag 0D7D](https://stacks.math.columbia.edu/tag/0D7D)
* [Stacks Project, Tag 0D73](https://stacks.math.columbia.edu/tag/0D73)
* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Section 85.11 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe w u

namespace CategoryTheory.SimplicialSiteSituation.RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)
  [HasDerivedCategory.{w} (S.totalRingedTopos A.O).Modules]
  [HasDerivedCategory.{u} A.augmentationRingedTopos.Modules]
  [∀ n, HasDerivedCategory.{u} (S.componentRingedTopos A.O n).Modules]

/-! ### The statement -/

/-- **The statement of Stacks 0D7F.** For a ringed augmentation `A` of a simplicial-site situation
towards a ringed site `(D, K, O_D)`: a cohomological spectral sequence of `O_D`-modules,
presented from its first page and functorial in `M` in `D⁺(O)`, with
`E_1^{p,q} = R^q a_{p,*} M_p` naturally in `M` (and `E_1^{p,q} = 0` for `p < 0`), converging to
`R^{p+q} a_* M`. -/
structure HigherDirectImageSpectralSequence where
  /-- The spectral sequence, as a functor of `M` in `D⁺(O)`. -/
  sequence : DerivedCategory.Plus (S.totalRingedTopos A.O).Modules ⥤
    CohomologicalSpectralSequence A.augmentationRingedTopos.Modules 1
  /-- `E_1^{p,q} = R^q a_{p,*} M_p`, naturally in `M`: the first page in column `p ≥ 0` is the
  `q`-th cohomology of the right derived direct image along `a_p` of the restriction `M_p` of `M`
  to the component `C_p`. -/
  pageOneIso (p : ℕ) (q : ℤ) :
    sequence ⋙ CategoryTheory.SpectralSequence.pageFunctor A.augmentationRingedTopos.Modules _
        1 1 le_rfl ⋙ HomologicalComplex.eval A.augmentationRingedTopos.Modules _ ((p : ℤ), q) ≅
      (S.componentModulesRestriction A.O ⦋p⦌).mapDerivedCategoryPlus ⋙
        (A.componentRingedHom ⦋p⦌).pushforwardModules.rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor A.augmentationRingedTopos.Modules q
  /-- The first page vanishes in the negative columns. -/
  isZero_pageOne (M : DerivedCategory.Plus (S.totalRingedTopos A.O).Modules) (p q : ℤ) :
    p < 0 → IsZero (((sequence.obj M).page 1 le_rfl).X (p, q))
  /-- The spectral sequence converges to `R^{p+q} a_* M`. -/
  abutsTo (M : DerivedCategory.Plus (S.totalRingedTopos A.O).Modules) :
    CategoryTheory.SpectralSequence.AbutsTo (sequence.obj M)
      (fun n => (DerivedCategory.Plus.homologyFunctor A.augmentationRingedTopos.Modules n).obj
        (A.totalRingedHom.pushforwardModules.rightDerivedFunctorPlus.obj M))

/-! ### The columns -/

omit [HasDerivedCategory (S.totalRingedTopos A.O).Modules] in
/-- **The restrictions of an injective module are acyclic for the component direct images.** For
an injective `O`-module `I`, the restriction `I_p` to the component `C_p` is totally acyclic
(Stacks 0D73), hence right acyclic for the direct image along `a_p` (Stacks 0731 (4)); the direct
image is read through the four-field morphism of ringed topoi of the modules development. -/
theorem rightAcyclic_componentModulesRestriction (n : SimplexCategory)
    (I : (S.totalRingedTopos A.O).Modules) [Injective I] :
    haveI := HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules
        (A.componentRingedHom n).toModulesHom).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh)
    (Stacks.Sheaves.RingedToposModules.pushforwardModules
      (A.componentRingedHom n).toModulesHom).rightAcyclic
        ((S.componentModulesRestriction A.O n).obj I) := by
  have h := @isTotallyAcyclic_componentModule_of_injective S n _ _ (S.totalRingSheaf A.O) I ‹_›
  exact Stacks.Cohomology.rightAcyclic_pushforwardModules_of_isTotallyAcyclic
    (f := (A.componentRingedHom n).toModulesHom) ((S.componentModulesRestriction A.O n).obj I) h

/-! ### The spectral sequence of an augmented functorial complex -/

section OfAugmentedComplex

omit [HasDerivedCategory.{w} (S.totalRingedTopos A.O).Modules]
  [HasDerivedCategory.{u} A.augmentationRingedTopos.Modules]
  [∀ n, HasDerivedCategory.{u} (S.componentRingedTopos A.O n).Modules] in
/-- Every double complex of `O_D`-modules has a total complex, sheaves of modules on a small site
having coproducts indexed by countable types. -/
local instance hasTotal_augmentationModules
    (L : HomologicalComplex₂ A.augmentationRingedTopos.Modules (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) :
    L.HasTotal (ComplexShape.up ℤ) :=
  inferInstance

variable (C : (S.totalRingedTopos A.O).Modules ⥤
    CochainComplex A.augmentationRingedTopos.Modules ℕ) [C.Additive]
  (eC : ∀ p : ℕ, C ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) p ≅
    S.componentModulesRestriction A.O ⦋p⦌ ⋙ (A.componentRingedHom ⦋p⦌).pushforwardModules)
  (ε : A.totalRingedHom.pushforwardModules ⟶ C ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) 0)
  (hε : ∀ X, ε.app X ≫ (C.obj X).d 0 1 = 0) (hmono : ∀ X, Mono (ε.app X))
  (hex : ∀ X, (ShortComplex.mk (ε.app X) ((C.obj X).d 0 1) (hε X)).Exact)
  (hinj : ∀ X, Injective X → ∀ k : ℕ, 0 < k → (C.obj X).ExactAt k)

/-- The direct image along `a_n`, read through the four-field morphism of ringed topoi of the
modules development: the functor for which Stacks 0731 (4) is stated. -/
abbrev componentModulesDirectImage (n : SimplexCategory) :
    (S.componentRingedTopos A.O n).Modules ⥤ A.augmentationRingedTopos.Modules :=
  Stacks.Sheaves.RingedToposModules.pushforwardModules (X := S.componentRingedTopos A.O n)
    (Y := A.augmentationRingedTopos) (A.componentRingedHom n).toModulesHom

/-- The right derived functors of the two readings of the direct image along `a_n` agree. -/
def componentPushforwardModulesRightDerivedIso (n : SimplexCategory) :
    (A.componentModulesDirectImage n).rightDerivedFunctorPlus ≅
      (A.componentRingedHom n).pushforwardModules.rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusNatIso (A.componentRingedHom n).toModulesPushforwardIso

/-- `E_1^{p,q} = R^q a_{p,*} M_p` for the spectral sequence of a functorial complex whose term in
degree `p` is `a_{p,*}(-)_p`, with the direct image read through the four-field morphism of
ringed topoi. -/
def pageOneIsoOfAugmentedComplexAux (p : ℕ) (q : ℤ) :
    Stacks.DegreewiseSpectralSequence.derivedFunctor
        (Stacks.DegreewiseSpectralSequence.natExtend C) ⋙
        CategoryTheory.SpectralSequence.pageFunctor A.augmentationRingedTopos.Modules _
          1 1 le_rfl ⋙ HomologicalComplex.eval A.augmentationRingedTopos.Modules _ ((p : ℤ), q) ≅
      (S.componentModulesRestriction A.O ⦋p⦌).mapDerivedCategoryPlus ⋙
        (A.componentModulesDirectImage ⦋p⦌).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor A.augmentationRingedTopos.Modules q := by
  let P := A.componentModulesDirectImage ⦋p⦌
  let e : C ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) p ≅
      S.componentModulesRestriction A.O ⦋p⦌ ⋙ P :=
    eC p ≪≫ Functor.isoWhiskerLeft _ (A.componentRingedHom ⦋p⦌).toModulesPushforwardIso.symm
  exact Stacks.DegreewiseSpectralSequence.natExtendPageOneIsoOfRightAcyclic C
    (S.componentModulesRestriction A.O ⦋p⦌) P p q e
    (fun I hI => by
      have := hI
      exact A.rightAcyclic_componentModulesRestriction ⦋p⦌ I)

/-- `E_1^{p,q} = R^q a_{p,*} M_p` for the spectral sequence of a functorial complex whose term in
degree `p` is `a_{p,*}(-)_p`. -/
def pageOneIsoOfAugmentedComplex (p : ℕ) (q : ℤ) :
    Stacks.DegreewiseSpectralSequence.derivedFunctor
        (Stacks.DegreewiseSpectralSequence.natExtend C) ⋙
        CategoryTheory.SpectralSequence.pageFunctor A.augmentationRingedTopos.Modules _
          1 1 le_rfl ⋙ HomologicalComplex.eval A.augmentationRingedTopos.Modules _ ((p : ℤ), q) ≅
      (S.componentModulesRestriction A.O ⦋p⦌).mapDerivedCategoryPlus ⋙
        (A.componentRingedHom ⦋p⦌).pushforwardModules.rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor A.augmentationRingedTopos.Modules q :=
  A.pageOneIsoOfAugmentedComplexAux C eC p q ≪≫
    Functor.isoWhiskerLeft (S.componentModulesRestriction A.O ⦋p⦌).mapDerivedCategoryPlus
      (Functor.isoWhiskerRight (A.componentPushforwardModulesRightDerivedIso ⦋p⦌)
        (DerivedCategory.Plus.homologyFunctor A.augmentationRingedTopos.Modules q))

include hε hmono hex hinj in
/-- **Stacks 0D7F from an augmented functorial complex.** A functorial complex
`a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …` with an augmentation from `a_*F` which is exact in degrees `-1`
and `0`, and exact in every degree when `F` is injective, gives the spectral sequence of
Stacks 0D7F. -/
def HigherDirectImageSpectralSequence.ofAugmentedComplex :
    A.HigherDirectImageSpectralSequence where
  sequence := Stacks.DegreewiseSpectralSequence.derivedFunctor
    (Stacks.DegreewiseSpectralSequence.natExtend C)
  pageOneIso := A.pageOneIsoOfAugmentedComplex C eC
  isZero_pageOne M p q hp := Stacks.DegreewiseSpectralSequence.isZero_natExtend_page_one C M p q hp
  abutsTo := Stacks.DegreewiseSpectralSequence.abutsTo_natExtend C _ ε hε hmono hex hinj

end OfAugmentedComplex

/-! ### The complex of Stacks 0D7D as a functor -/

section CechComplexFunctor

omit [HasDerivedCategory.{w} (S.totalRingedTopos A.O).Modules]
  [HasDerivedCategory.{u} A.augmentationRingedTopos.Modules]
  [∀ n, HasDerivedCategory.{u} (S.componentRingedTopos A.O n).Modules]

/-- The differential `a_{n,*}(-)_n ⟶ a_{n+1,*}(-)_{n+1}` of the complex of Stacks 0D7D, as a
natural transformation: the conjugate of the differential of the resolution of Stacks 0D7C. -/
abbrev cechDNat (n : ℕ) :
    A.componentPushforwardModules ⦋n⦌ ⟶ A.componentPushforwardModules ⦋n + 1⦌ :=
  conjugateEquiv (A.barTermAdjunction n) (A.barTermAdjunction (n + 1)) (A.barD n)

/-- **The complex `a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …` of Stacks 0D7D as a functor of `F`**: its value
at `F` is `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.componentCechComplex`, and a
morphism acts degreewise by `a_{n,*}(-)_n`, the differentials being natural in `F`. -/
def componentCechComplexFunctor :
    (S.totalRingedTopos A.O).Modules ⥤ CochainComplex A.augmentationRingedTopos.Modules ℕ where
  obj F := A.componentCechComplex F
  map {F G} f := CochainComplex.ofHom (X := A.componentCechComplex F)
    (Y := A.componentCechComplex G) (fun n => (A.componentPushforwardModules ⦋n⦌).map f)
    (fun n => by
      rw [componentCechComplex_d, componentCechComplex_d]
      exact (A.cechDNat n).naturality f)
  map_id F := HomologicalComplex.hom_ext _ _ fun n =>
    (A.componentPushforwardModules ⦋n⦌).map_id F
  map_comp f g := HomologicalComplex.hom_ext _ _ fun n =>
    (A.componentPushforwardModules ⦋n⦌).map_comp f g

/-- The functor `F ↦ (a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …)` is additive. -/
instance additive_componentCechComplexFunctor : A.componentCechComplexFunctor.Additive where
  map_add {_F _G _f _g} := HomologicalComplex.hom_ext _ _ fun n =>
    (A.componentPushforwardModules ⦋n⦌).map_add

/-- The term in degree `p` of the complex of Stacks 0D7D is `a_{p,*}(-)_p`, naturally. -/
def componentCechComplexFunctorEvalIso (p : ℕ) :
    A.componentCechComplexFunctor ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) p ≅
      S.componentModulesRestriction A.O ⦋p⦌ ⋙ (A.componentRingedHom ⦋p⦌).pushforwardModules :=
  NatIso.ofComponents (fun F => Iso.refl ((A.componentPushforwardModules ⦋p⦌).obj F))
    (fun _f => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The augmentation `a_* ⟶ a_{0,*}(-)_0` of the complex of Stacks 0D7D, as a natural
transformation: the conjugate of the augmentation of the resolution of Stacks 0D7C. -/
def cechAugNat :
    A.totalRingedHom.pushforwardModules ⟶
      A.componentCechComplexFunctor ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) 0 where
  app F := A.cechAug F
  naturality _ _ f :=
    (conjugateEquiv A.totalAdjunction (A.barTermAdjunction 0) A.barAug).naturality f

/-- The composite `a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1` of the augmentation with the first
differential is zero. -/
theorem cechAugNat_comp_d (F : (S.totalRingedTopos A.O).Modules) :
    A.cechAugNat.app F ≫ (A.componentCechComplexFunctor.obj F).d 0 1 = 0 := by
  change A.cechAug F ≫ (A.componentCechComplex F).d 0 1 = 0
  rw [componentCechComplex_d]
  exact A.cechAug_comp_cechD F

/-- A short complex is exact if it is exact after replacing its maps by equal ones. -/
private theorem exact_mk_of_eq {C : Type*} [Category C] [HasZeroMorphisms C] {X Y Z : C}
    {f f' : X ⟶ Y} {g g' : Y ⟶ Z} (hf : f = f') (hg : g = g') (w : f ≫ g = 0)
    (w' : f' ≫ g' = 0) (h : (ShortComplex.mk f' g' w').Exact) : (ShortComplex.mk f g w).Exact := by
  subst hf hg
  exact h

/-- **Stacks 0D7D in degree `-1`**: the augmentation `a_*F ⟶ a_{0,*}F_0` is a monomorphism. -/
theorem mono_cechAugNat_app (F : (S.totalRingedTopos A.O).Modules) :
    Mono (A.cechAugNat.app F) := by
  have h := (A.moduleCechComplex_spec F).2.2.1
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero
    (CochainComplex.next ℕ 0), ShortComplex.exact_iff_mono _
      ((A.moduleCechComplex F).shape 0 0 (by simp))] at h
  exact h

/-- **Stacks 0D7D in degree `0`**: `0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1` is exact. -/
theorem exact_cechAugNat_app (F : (S.totalRingedTopos A.O).Modules) :
    (ShortComplex.mk (A.cechAugNat.app F) ((A.componentCechComplexFunctor.obj F).d 0 1)
      (A.cechAugNat_comp_d F)).Exact := by
  have h := (A.moduleCechComplex_spec F).2.2.2.1
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (CochainComplex.prev_nat_succ 0)
    (CochainComplex.next ℕ 1)] at h
  exact exact_mk_of_eq (A.moduleCechComplex_d_zero F).symm
    ((A.componentCechComplex_d F 0).trans (A.moduleCechComplex_d_one F).symm) _ _ h

/-- **Stacks 0D7D for an injective module**: the complex `a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …` is exact
in every positive degree when `F` is injective. -/
theorem exactAt_componentCechComplexFunctor_obj (F : (S.totalRingedTopos A.O).Modules)
    (hF : Injective F) (k : ℕ) (hk : 0 < k) :
    (A.componentCechComplexFunctor.obj F).ExactAt k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := ((A.moduleCechComplex_spec F).2.2.2.2 hF).1 (j + 2)
  rw [HomologicalComplex.exactAt_iff' _ (j + 1) (j + 2) (j + 3)
    (CochainComplex.prev_nat_succ (j + 1)) (CochainComplex.next ℕ (j + 2))] at h
  change (A.componentCechComplex F).ExactAt (j + 1)
  rw [HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
    (CochainComplex.next ℕ (j + 1))]
  exact exact_mk_of_eq
    ((A.componentCechComplex_d F j).trans (A.moduleCechComplex_d_succ F j).symm)
    ((A.componentCechComplex_d F (j + 1)).trans (A.moduleCechComplex_d_succ F (j + 1)).symm) _ _ h

end CechComplexFunctor

/-! ### Stacks 0D7F -/

/-- **Stacks 0D7F.** With the notation of Stacks 0D9D (a ringed augmentation `A` of a
simplicial-site situation towards a ringed site `(D, K, O_D)`), for `M` in `D⁺(O)` there is a
spectral sequence `(E_r, d_r)` in `Mod(O_D)`, presented from its first page and functorial in
`M`, with

`E_1^{p,q} = R^q a_{p,*} M_p  ⇒  R^{p+q} a_* M`.

Here `M_p` is the restriction of `M` to the component `C_p` (Stacks 0D72), `R^q a_{p,*}` the
cohomology of the right derived direct image along `a_p = a ∘ g_p` and `R^n a_*` that of the
right derived direct image along `a`. The identification of the first page is natural in `M`,
and the first page vanishes in the negative columns.

It is the spectral sequence of the double complex `A^{p,q} = a_{p,*} I^q_p` of a bounded below
complex of injectives `I^•` representing `M`, whose horizontal maps are those of the complex of
Stacks 0D7D, filtered by `p`. -/
@[stacks 0D7F]
def higherDirectImageSpectralSequence : A.HigherDirectImageSpectralSequence :=
  HigherDirectImageSpectralSequence.ofAugmentedComplex A A.componentCechComplexFunctor
    A.componentCechComplexFunctorEvalIso A.cechAugNat A.cechAugNat_comp_d A.mono_cechAugNat_app
    A.exact_cechAugNat_app A.exactAt_componentCechComplexFunctor_obj

end CategoryTheory.SimplicialSiteSituation.RingedAugmentation

end
