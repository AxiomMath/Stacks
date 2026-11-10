module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportBaseChange

/-!
# The comparison of Tag 0G7L commutes with excision, along an arbitrary open immersion

`Stacks.Perfect.CechDerivedSupportBaseChange` proves that the comparison

`𝓕^• ⟶ i_* R𝓗_T(ℱ)`

of [Stacks, Tag 0G7L] is compatible with excision along the inclusion `W.ι` of an open
subscheme.  This file proves the same statement along an **arbitrary open immersion of schemes**
`g : X' ⟶ X`, which is what the locality of the class map of [Stacks, Tag 0G7Q] at two
*different* equation charts needs: two charts meeting in an open `V'` are refined through legs
that are not the canonical inclusion of an open subscheme, and at most one of the two can be
written as such an inclusion.

## Main definitions

* `legIncl`: the open immersion of ringed spaces underlying `g`, the leg of the base change.
* `restrictClosedSubset`: the preimage in `X'` of a subset of `X`.
* `restrictQNatIso` and `restrictQIso`: **derived pullback along `g`, read on complexes.**
* `restrictCplxIso`, `restrictExtendIso`, `cechRestrictIso` and `singleRestrictIso`: the
  identifications of the two Čech complexes and of the two coefficient modules in degree `0`.

## Main results

* `cechRestrictIso_hom_comp_augmentation`: the augmentation of [Stacks, Tag 0G7L] is carried
  across the identification of the two Čech complexes.
* `map_cechToDerivedSupport_comp_supportPushPullbackIso_hom`: **the square**, along an arbitrary
  open immersion.

## Implementation notes

**Nothing in the argument uses more of the leg than that it is an open immersion.**  The derived
machinery it rests on —
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` and
`Stacks.Perfect.SupportPushExcision.supportPushPullbackIso` — is already stated for an arbitrary
open immersion of ringed spaces, and the bridge to the restriction of modules on schemes is
Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, which holds for an
arbitrary open immersion of schemes.  So this file is
`Stacks.Perfect.CechDerivedSupportBaseChange` with the leg `W.ι` replaced by `g` and
`openIncl W` by `legIncl g`.  The two general facts of that file — about
`HomologicalComplex.extend` and about transporting `Functor.PreservesZeroMorphisms` along a
natural isomorphism — are reused rather than restated; the three formal identities at variable
categories are restated, because they are `private` and so file-scoped.

**The overlap with `CechDerivedSupportBaseChange`.**  Lines 249-638 of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/CechDerivedSupportBaseChange.lean`
(from `/-! ### Derived pullback along the inclusion of an open subscheme, read on complexes -/`
to `end Square`, 390 lines) are this file's lines 83-478 with `g` specialised to `W.ι`, and every
one of them would be a one-line wrapper `… W.ι` over the declaration of the same name here: the
statements are definitionally equal, because `openIncl W` and `legIncl W.ι` are
(`Stacks.Gysin.supportCohomologyRestrictIso_eq_openImmersionIso` is `rfl` across exactly that
identification).  Two things stand in the way of writing those wrappers, and neither is
mathematics.  First the **import direction**: this file imports
`CechDerivedSupportBaseChange`, for the two general facts of its `General` section (lines
174-247) and for `preservesFiniteLimits_modulePullback` (line 259), so collapsing that file
onto this one first requires splitting those out into a module upstream of both.  Second, each
wrapper asks the elaborator to unify two spellings of one derived-category object across the
unfolding of a `def`, which is affordable at one definitional step and
not at two.  That file is therefore kept as it is; its consumer is
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinClassBaseChange.lean`, whose statements are the
`W.ι` ones and must not change.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Remark 36.6.6 (Tag 0G7L)](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.CechDerivedSupportBaseChange (preservesZeroMorphisms_of_natIso extendIso
  extendIso_hom mapHomologicalComplexExtendIso_hom_naturality
  mapHomologicalComplexExtendIso_hom_naturality_assoc
  extendMap_singleMapHomologicalComplex_comp_extendSingleIso_hom)
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation
open Stacks.Perfect.PushforwardRestrict (restrictComplexIso)
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechDerivedSupportImmersion

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Derived pullback along the inclusion of an open subscheme, read on complexes -/

section Restrict

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g]

/-- **An open immersion of schemes, as an open immersion of ringed spaces.**  This is the leg
the base change below is taken along; for `g` the inclusion of an open subscheme it is
`Stacks.Perfect.CechDerivedSupportBaseChange.openIncl`. -/
abbrev legIncl : X'.toRingedSpace ⟶ X.toRingedSpace := g.toLRSHom.toShHom

/-- The morphism of ringed spaces underlying an open immersion of schemes is an open immersion
of sheafed spaces. -/
instance : SheafedSpace.IsOpenImmersion (legIncl g) := by
  delta legIncl; infer_instance

attribute [local instance] CechDerivedSupportBaseChange.preservesFiniteLimits_modulePullback

/-- The preimage in `X'` of a subset of `X`.  This is
`Stacks.Cohomology.SupportedComplexes.closedSubsetPreimage` along the ringed-space leg, with its
type read at the scheme `X'`: leaving that scheme to be inferred asks the unifier to invert the
coercion of a scheme to its carrier, which it does not do. -/
abbrev restrictClosedSubset (T : Set X) : Set X' := closedSubsetPreimage (legIncl g) T

omit [IsOpenImmersion g] in
/-- The preimage in `X'` of a closed subset of `X` is closed. -/
theorem isClosed_restrictClosedSubset {T : Set X} (hT : IsClosed T) :
    IsClosed (restrictClosedSubset g T) :=
  isClosed_closedSubsetPreimage (legIncl g) T hT

omit [IsOpenImmersion g] in
/-- **The common zero locus of the restricted equations lies over the common zero locus of the
equations.**  A point of `X'` outside every principal open of a restricted equation lies outside
every principal open of the equation itself, the principal opens of the restrictions being the
preimages of the principal opens (`AlgebraicGeometry.Scheme.preimage_basicOpen`).  So the
hypothesis on the restricted equations that the square below carries is the restriction of the
hypothesis on `X`. -/
theorem equationsClosedSet_restrict_subset {m : ℕ} (e : Fin m → Γ(X, ⊤)) {T : Set X}
    (hTe : equationsClosedSet e ⊆ T) :
    equationsClosedSet (fun j => g.appTop (e j)) ⊆ restrictClosedSubset g T := by
  intro x hx
  refine hTe ?_
  simp only [equationsClosedSet, Set.mem_compl_iff, SetLike.mem_coe,
    TopologicalSpace.Opens.mem_iSup] at hx ⊢
  rintro ⟨i, hi⟩
  refine hx ⟨i, ?_⟩
  have hb : X'.basicOpen (g.appTop (e i)) = g ⁻¹ᵁ X.basicOpen (e i) :=
    (Scheme.preimage_basicOpen g (e i)).symm
  rw [hb]
  exact hi

/-- **Pullback of modules along the ringed-space inclusion of an open subscheme is restriction
along the inclusion of that open subscheme.**  This is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, read through the definitional
equality of the pullback of modules along a morphism of schemes with the pullback along the
underlying morphism of ringed spaces.  `Stacks.Gysin.modulePullbackRestrictFunctorIso` is the
same expression, downstream of this file. -/
def modulePullbackRestrictIso :
    modulePullback (legIncl g) ≅ Scheme.Modules.restrictFunctor g :=
  (Scheme.Modules.restrictFunctorIsoPullback g).symm

/-- **Derived pullback along the inclusion of an open subscheme, read on complexes.**  On the
image of `DerivedCategory.Q` the derived pullback along `g` is the restriction of complexes
along `g`: the derived pullback along an open immersion is the derived functor of the
degreewise pullback (`derivedPullbackOpenImmersionIso`), that derived functor is computed
degreewise (`CategoryTheory.Functor.mapDerivedCategoryFactors`), and the degreewise pullback is
restriction (`modulePullbackRestrictIso`). -/
def restrictQNatIso :
    DerivedCategory.Q ⋙ derivedPullback (legIncl g) ≅
      (Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
  Functor.isoWhiskerLeft DerivedCategory.Q
      (derivedPullbackOpenImmersionIso (legIncl g)) ≪≫
    (modulePullback (legIncl g)).mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (modulePullbackRestrictIso g) (ComplexShape.up ℤ))
      DerivedCategory.Q

/-- `restrictQNatIso` at a complex. -/
def restrictQIso (C : CochainComplex X.Modules ℤ) :
    (derivedPullback (legIncl g)).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C) :=
  (restrictQNatIso g).app C

/-- `restrictQIso` is natural in the complex. -/
theorem restrictQIso_hom_naturality {C D : CochainComplex X.Modules ℤ} (φ : C ⟶ D) :
    (derivedPullback (legIncl g)).map (DerivedCategory.Q.map φ) ≫ (restrictQIso g D).hom =
      (restrictQIso g C).hom ≫
        DerivedCategory.Q.map
          (((Scheme.Modules.restrictFunctor g).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) :=
  (restrictQNatIso g).hom.naturality φ

end Restrict

/-! ### Base change of the augmentation of Tag 0G7L -/

section Augmentation

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g] {m : ℕ}
  (e : Fin m → Γ(X, ⊤)) (F : X.Modules)

/-- **The identification of the restricted extended alternating Čech complex with the extended
alternating Čech complex of the restricted equations**, with the restriction written as the
degreewise functor rather than as `Stacks.Perfect.PushforwardRestrict.restrictComplex`.  Pinning
that spelling once is what lets the extension by zero below compose with it without a
transport. -/
def restrictCplxIso :
    ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedAlternatingCech e F).complex ≅
      (extendedAlternatingCech (fun j => g.appTop (e j))
        ((Scheme.Modules.restrictFunctor g).obj F)).complex :=
  restrictComplexIso e g (extendedAlternatingCech e F)
    (extendedAlternatingCech (fun j => g.appTop (e j))
      ((Scheme.Modules.restrictFunctor g).obj F))

/-- In degree `0` the comparison of the restricted Čech complex with the Čech complex of the
restricted equations is the comparison of the two identifications of the degree-`0` term. -/
theorem restrictCplxIso_hom_f_zero :
    (restrictCplxIso g e F).hom.f 0 =
      (Scheme.Modules.restrictFunctor g).map (extendedAlternatingCech e F).zeroIso.hom ≫
        (extendedAlternatingCech (fun j => g.appTop (e j))
          ((Scheme.Modules.restrictFunctor g).obj F)).zeroIso.inv := rfl

/-- **The augmentation of [Stacks, Tag 0G7L] is carried across the identification of the two
extended alternating Čech complexes of [Stacks, Tag 0G7U].**  Both sides are morphisms into a
complex concentrated in degree `0`, so only the degree-`0` component is at stake, and there both
sides are the identification of the degree-`0` term of the Čech complex with the coefficient
module. -/
theorem restrictCplxIso_hom_comp_augmentationComplex :
    (restrictCplxIso g e F).hom ≫
        augmentationComplex (fun j => g.appTop (e j))
          ((Scheme.Modules.restrictFunctor g).obj F) =
      ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (augmentationComplex e F) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor g)
          (ComplexShape.up ℕ) 0).hom.app F := by
  refine HomologicalComplex.to_single_hom_ext (j := 0) ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    CechDerivedSupportBaseChange.augmentationComplex_f_zero,
    CechDerivedSupportBaseChange.augmentationComplex_f_zero, restrictCplxIso_hom_f_zero,
    Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_map_assoc]

/-- **The augmentation of [Stacks, Tag 0G7L] is carried across the identification of the two
Čech complexes, after extending the grading from `ℕ` to `ℤ`.** -/
theorem extendMap_restrictCplxIso_comp_augmentationExtend :
    HomologicalComplex.extendMap (restrictCplxIso g e F).hom ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendMap
              (augmentationComplex (fun j => g.appTop (e j))
                ((Scheme.Modules.restrictFunctor g).obj F)) ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
              ((Scheme.Modules.restrictFunctor g).obj F) 0 0 rfl).hom) =
      (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.restrictFunctor g)
            (extendedAlternatingCech e F).complex ComplexShape.embeddingUpNat).hom ≫
        ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap (augmentationComplex e F)
                ComplexShape.embeddingUpNat ≫
              (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom) ≫
          (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor g)
            (ComplexShape.up ℤ) 0).hom.app F := by
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    restrictCplxIso_hom_comp_augmentationComplex, HomologicalComplex.extendMap_comp,
    Category.assoc,
    extendMap_singleMapHomologicalComplex_comp_extendSingleIso_hom
      (Scheme.Modules.restrictFunctor g) ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl F]
  simp only [Functor.map_comp, Category.assoc]
  rw [mapHomologicalComplexExtendIso_hom_naturality_assoc]

end Augmentation

/-! ### The two identifications the square needs -/

section Isos

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g] {m : ℕ}
  (e : Fin m → Γ(X, ⊤)) (F : X.Modules)

/-- **The restriction of the extended alternating Čech complex of [Stacks, Tag 0G7I], with the
grading extended to `ℤ`, is the extended alternating Čech complex of the restricted
equations.**  This is `restrictCplxIso` read through the commutation of extension by zero with a
functor preserving zero morphisms. -/
def restrictExtendIso :
    ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extendedAlternatingCech e F).complex.extend ComplexShape.embeddingUpNat) ≅
      (extendedAlternatingCech (fun j => g.appTop (e j))
          ((Scheme.Modules.restrictFunctor g).obj F)).complex.extend
        ComplexShape.embeddingUpNat :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.restrictFunctor g)
      (extendedAlternatingCech e F).complex ComplexShape.embeddingUpNat).symm ≪≫
    extendIso (restrictCplxIso g e F) ComplexShape.embeddingUpNat

/-- The forward morphism of `restrictExtendIso` is the inverse of the commutation of extension by
zero with restriction followed by the extension of `restrictCplxIso`. -/
theorem restrictExtendIso_hom :
    (restrictExtendIso g e F).hom =
      (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.restrictFunctor g)
          (extendedAlternatingCech e F).complex ComplexShape.embeddingUpNat).inv ≫
        HomologicalComplex.extendMap (restrictCplxIso g e F).hom
          ComplexShape.embeddingUpNat := rfl

/-- The augmentation of [Stacks, Tag 0G7L] is carried across `restrictExtendIso`, at the level of
`ℤ`-graded complexes. -/
theorem restrictExtendIso_hom_comp_augmentationExtend :
    (restrictExtendIso g e F).hom ≫
        (HomologicalComplex.extendMap
              (augmentationComplex (fun j => g.appTop (e j))
                ((Scheme.Modules.restrictFunctor g).obj F)) ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
              ((Scheme.Modules.restrictFunctor g).obj F) 0 0 rfl).hom) =
      ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap (augmentationComplex e F)
              ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor g)
          (ComplexShape.up ℤ) 0).hom.app F := by
  rw [restrictExtendIso_hom, Category.assoc, extendMap_restrictCplxIso_comp_augmentationExtend,
    Iso.inv_hom_id_assoc]

/-- **The derived pullback of the extended alternating Čech complex along the inclusion of an
open subscheme is the extended alternating Čech complex of the restricted equations.**  This is
the identification `(ℱ')^• = g^*ℱ^•` of [Stacks, Tag 0G7U] in the derived category, for `g` an
open immersion. -/
def cechRestrictIso :
    (derivedPullback (legIncl g)).obj
        (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) ≅
      DerivedCategory.Q.obj
        ((cplx (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F)).extend
          ComplexShape.embeddingUpNat) :=
  restrictQIso g ((extendedAlternatingCech e F).complex.extend ComplexShape.embeddingUpNat) ≪≫
    DerivedCategory.Q.mapIso (restrictExtendIso g e F)

/-- The forward morphism of `cechRestrictIso` is `restrictQIso` followed by the image of
`restrictExtendIso` in the derived category. -/
theorem cechRestrictIso_hom :
    (cechRestrictIso g e F).hom =
      (restrictQIso g
          ((extendedAlternatingCech e F).complex.extend ComplexShape.embeddingUpNat)).hom ≫
        DerivedCategory.Q.map (restrictExtendIso g e F).hom := rfl

/-- **The derived pullback of a module placed in degree `0` along the inclusion of an open
subscheme is its restriction, placed in degree `0`.** -/
def singleRestrictIso :
    (derivedPullback (legIncl g)).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor X'.Modules 0).obj
        ((Scheme.Modules.restrictFunctor g).obj F) :=
  restrictQIso g ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor g)
        (ComplexShape.up ℤ) 0).app F)

/-- The forward morphism of `singleRestrictIso` is `restrictQIso` followed by the image in the
derived category of the commutation of restriction with the single-degree complex. -/
theorem singleRestrictIso_hom :
    (singleRestrictIso g F).hom =
      (restrictQIso g ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor g)
            (ComplexShape.up ℤ) 0).hom.app F) := rfl

/-- **The augmentation of [Stacks, Tag 0G7L] is carried across `cechRestrictIso`.**  This is
`restrictExtendIso_hom_comp_augmentationExtend` in the derived category, by the naturality of
`restrictQIso`. -/
theorem cechRestrictIso_hom_comp_augmentation :
    (cechRestrictIso g e F).hom ≫
        augmentation (fun j => g.appTop (e j))
          ((Scheme.Modules.restrictFunctor g).obj F) =
      (derivedPullback (legIncl g)).map (augmentation e F) ≫ (singleRestrictIso g F).hom :=
  CechDerivedSupportBaseChange.assembleAug DerivedCategory.Q DerivedCategory.Q
    ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℤ))
    (derivedPullback (legIncl g)) _ _ _ _ _ _
    (restrictExtendIso_hom_comp_augmentationExtend g e F)
    (restrictQIso_hom_naturality g
      (HomologicalComplex.extendMap (augmentationComplex e F) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom))

end Isos

/-! ### The square -/

section Square

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g] {m : ℕ}
  (e : Fin m → Γ(X, ⊤)) (F : X.Modules)
  [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
  (hT' : IsClosed (restrictClosedSubset g T))
  (hTe' : equationsClosedSet (fun j => g.appTop (e j)) ⊆ restrictClosedSubset g T)

omit [F.IsQuasicoherent] in
/-- **The excision isomorphism of [Stacks, Tag 0G78] carries the inverse counit of
[Stacks, Tag 0G72] at the extended alternating Čech complex to the one on `X'`.**  This is
`Stacks.Perfect.SupportPushExcision.supportPushPullbackIso_hom_comp_supportPushCounit` together
with the naturality of the counit along `cechRestrictIso`, the counit being invertible at both
Čech complexes by [Stacks, Tag 0G7M]. -/
theorem supportPushPullbackIso_hom_comp_map_cechRestrictIso :
    (derivedPullback (legIncl g)).map
          (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).inv ≫
        (SupportPushExcision.supportPushPullbackIso (legIncl g) hT).hom.app
            (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) ≫
          (supportPush hT').map (cechRestrictIso g e F).hom =
      (cechRestrictIso g e F).hom ≫
        (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech
          (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F)
          hT' hTe')).inv :=
  CechDerivedSupportBaseChange.chase _ _ _
    (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech
      (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F) hT' hTe')) _ _ _
    (SupportPushExcision.supportPushPullbackIso_hom_comp_supportPushCounit (legIncl g) hT
      (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)))
    ((supportPushCounit hT').naturality (cechRestrictIso g e F).hom)
    (((derivedPullback (legIncl g)).map_comp _ _).symm.trans
      ((congrArg (derivedPullback (legIncl g)).map
          (@asIso _ _ _ _ _
            (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).inv_hom_id).trans
        ((derivedPullback (legIncl g)).map_id _)))

omit [F.IsQuasicoherent] in
/-- **The comparison of [Stacks, Tag 0G7L] commutes with excision along an open immersion.**  The
derived pullback of `Stacks.Perfect.SupportedFraction.cechToDerivedSupport` along an open
immersion `g`, followed by the excision isomorphism
`Stacks.Perfect.SupportPushExcision.supportPushPullbackIso` of [Stacks, Tag 0G78] and by
`i'_* R𝓗_{g⁻¹T}` of the identification of the restricted coefficient module, is the comparison
of [Stacks, Tag 0G7L] for the restricted equations and `g^*ℱ`, read across the identification
`cechRestrictIso` of the two extended alternating Čech complexes.

This is the missing link of the open-immersion case of [Stacks, Tag 0G7U]: the comparison of
[Stacks, Tag 0G7L] is determined by the triangle of that remark, both halves of which are carried
across the excision isomorphism, so the only content is the base change
`cechRestrictIso_hom_comp_augmentation` of the augmentation. -/
theorem map_cechToDerivedSupport_comp_supportPushPullbackIso_hom :
    (derivedPullback (legIncl g)).map (cechToDerivedSupport e F hT hTe) ≫
        (SupportPushExcision.supportPushPullbackIso (legIncl g) hT).hom.app
            ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
          (supportPush hT').map (singleRestrictIso g F).hom =
      (cechRestrictIso g e F).hom ≫
        cechToDerivedSupport (fun j => g.appTop (e j))
          ((Scheme.Modules.restrictFunctor g).obj F) hT' hTe' :=
  CechDerivedSupportBaseChange.assemble (derivedPullback (legIncl g)) (supportPush hT)
    (supportPush hT')
    (augmentation e F)
    (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).inv _ _
    (cechRestrictIso g e F).hom (singleRestrictIso g F).hom
    (augmentation (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F))
    (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech
      (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F) hT' hTe')).inv
    ((SupportPushExcision.supportPushPullbackIso (legIncl g) hT).hom.naturality
      (augmentation e F))
    (cechRestrictIso_hom_comp_augmentation g e F)
    (supportPushPullbackIso_hom_comp_map_cechRestrictIso g e F hT hTe hT' hTe')

end Square
end Stacks.Perfect.CechDerivedSupportImmersion

end
