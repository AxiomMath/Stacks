module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportPushExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction

/-!
# The comparison of Tag 0G7L commutes with excision, along an open immersion

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, let `T ⊆ X` be closed and contain their common
zero locus, let `ℱ` be a quasi-coherent `𝒪_X`-module and let `W ⊆ X` be an open.
`Stacks.Perfect.SupportedFraction.cechToDerivedSupport` is the canonical comparison

`𝓕^• ⟶ i_* R𝓗_T(ℱ)`

of [Stacks, Tag 0G7L].  This file proves that it is **compatible with excision along the
inclusion of `W`**: its derived pullback, followed by the excision isomorphism
`Stacks.Perfect.SupportPushExcision.supportPushPullbackIso` of [Stacks, Tag 0G78], is the
comparison of [Stacks, Tag 0G7L] for the restricted equations and `ℱ|_W`, read across the
identification of the pulled-back extended alternating Čech complex with the extended
alternating Čech complex of the restricted equations.

This is the missing link of the open-immersion case of [Stacks, Tag 0G7U]: the identification of
the *complexes* is `Stacks.Perfect.PushforwardRestrict.restrictComplexIso`, and what this file
adds is that the comparison of [Stacks, Tag 0G7L] is carried across it.

## Main definitions

* `extendIso`: extending an isomorphism of complexes along an embedding of complex shapes.
* `restrictQNatIso`: **derived pullback along the inclusion of an open subscheme, read on
  complexes.**  The natural isomorphism `Q ⋙ Lι^* ≅ (-|_W) ⋙ Q`, assembled from
  `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`, from
  `CategoryTheory.Functor.mapDerivedCategoryFactors` and from the identification
  `modulePullbackRestrictIso` of the pullback of modules with restriction.
* `restrictClosedSubset`: the preimage in `W` of a subset of `X`, with its type read at the
  scheme `W`.
* `restrictCplxIso`: `Stacks.Perfect.PushforwardRestrict.restrictComplexIso` with the restriction
  written as the degreewise functor.
* `restrictExtendIso`: the same after extending the grading from `ℕ` to `ℤ`.
* `cechRestrictIso` and `singleRestrictIso`: the two identifications the square needs — the
  derived pullback of `𝓕^•` is `(ℱ|_W)^•`, and the derived pullback of `ℱ[0]` is `(ℱ|_W)[0]`.

## Main results

* `extendMap_singleMapHomologicalComplex_comp_extendSingleIso_hom`: applying a functor preserving
  zero morphisms commutes with `HomologicalComplex.extendSingleIso`.
* `equationsClosedSet_restrict_subset`: the hypothesis of [Stacks, Tag 0G7L] on the restricted
  equations is the restriction of the hypothesis on `X`, so the square below carries its own
  hypotheses.
* `restrictCplxIso_hom_comp_augmentationComplex`: **the augmentation of [Stacks, Tag 0G7L] is
  carried across the identification of the two Čech complexes**, at the level of `ℕ`-graded
  complexes.  This is the one computation in the file: both sides are morphisms into a complex
  concentrated in degree `0`, so only the degree-`0` component is at stake, and there both sides
  are the identification of the degree-`0` term of the Čech complex with the coefficient module.
* `extendMap_restrictCplxIso_comp_augmentationExtend` and
  `cechRestrictIso_hom_comp_augmentation`: the same statement after extending the grading to `ℤ`,
  and then in the derived category.
* `map_cechToDerivedSupport_comp_supportPushPullbackIso_hom`: **the square**.  The derived
  pullback of the comparison of [Stacks, Tag 0G7L] along the inclusion of an open subscheme,
  followed by the excision isomorphism of [Stacks, Tag 0G78], is the comparison of
  [Stacks, Tag 0G7L] on `W`.

## Implementation notes

**The route: the characterising triangle, not a factor-by-factor chase.**  The comparison of
[Stacks, Tag 0G7L] is the inverse of the counit of [Stacks, Tag 0G72] — invertible at the Čech
complex by [Stacks, Tag 0G7M] — followed by `i_* R𝓗_T` applied to the augmentation.  Both halves
are already carried across the excision isomorphism:
`Stacks.Perfect.SupportPushExcision.supportPushPullbackIso_hom_comp_supportPushCounit` carries the
counit, and the naturality of the excision isomorphism carries `i_* R𝓗_T` of any map.  So the
only new content is the base change of the **augmentation**, which is a statement about complexes,
and after that the square is formal.  In particular no uniqueness statement for the excision
isomorphism is used, and the excision isomorphism is never unfolded.

**The augmentation base change is a single degree-`0` computation.**  The augmentation is a
morphism into a complex concentrated in degree `0`, and such a morphism is determined by its
degree-`0` component (`HomologicalComplex.to_single_hom_ext`).  Extending the grading from `ℕ` to
`ℤ` and applying a functor preserving zero morphisms both keep that shape, so the two transports
of the statement — `extendMap_restrictCplxIso_comp_augmentationExtend` and
`cechRestrictIso_hom_comp_augmentation` — need no further computation: the first is the general
compatibility `extendMap_singleMapHomologicalComplex_comp_extendSingleIso_hom` of
`HomologicalComplex.extendSingleIso` with such a functor, and the second is the naturality of
`restrictQNatIso`.

**Two declarations are stated at variable categories on purpose.**  `chase` and `assemble` are
the formal identities left over once the naturality squares are inserted.  Assembling them inline
at the derived categories of sheaves of modules exceeds the default heartbeat limit, which may
not be raised; stating them where no derived category occurs avoids the problem, as in
`Stacks.Perfect.SupportPushExcision`.

**Why `preservesZeroMorphisms_of_natIso` is needed.**  `modulePullbackRestrictIso` is an
isomorphism between two functors whose target categories — the modules on the ringed space
underlying `W` and the modules on the scheme `W` — are the same category written two ways.  The
isomorphism is recorded at one of the two spellings, and
`CategoryTheory.NatIso.mapHomologicalComplex` then asks for `Functor.PreservesZeroMorphisms` of
*both* functors at that spelling, where instance search finds it only for one of them.
Transporting the instance across the isomorphism supplies the other;
`Functor.PreservesZeroMorphisms` is a proposition, so the instance the statement of
`restrictQNatIso` uses and the one its proof uses are interchangeable.

**Why `restrictClosedSubset`.**  `i_* R𝓗_T` is written
`Stacks.Perfect.SupportedFraction.supportPush`, whose scheme is implicit and inferred from the
type of the closed subset.  On the open subscheme that subset is
`Stacks.Cohomology.SupportedComplexes.closedSubsetPreimage` along the ringed-space inclusion, and
its type names the *ringed space*, so leaving the scheme to be inferred asks the unifier to
invert the coercion of a scheme to its carrier; it does not, and the elaboration of the statement
exhausts the heartbeat budget.  `restrictClosedSubset` is that subset with its type ascribed at
the scheme, which turns the search into one definitional check.

**One vocabulary.**  Everything here is written in
`Stacks.Perfect.ExtendedAlternatingCech`; the parallel `AlgebraicGeometry.ExtendedAlternatingCech`
spelling of the same specification is not opened, because making the unifier see both makes it
unfold both.  The Čech complex itself is spelled
`(Stacks.Perfect.ExtendedAlternatingCech.extendedAlternatingCech e F).complex` at the level of
complexes, which is the source of the augmentation, and
`Stacks.Perfect.ExtendedAlternatingCech.cplx` in the derived category, which is the source of the
comparison of [Stacks, Tag 0G7L]; the two are the same term and the single crossing between them
happens in the type of `cechRestrictIso`.

**What is *not* here, and what it would take.**  The square is proved in the derived category,
for the identifications built in this file.  It is **not read in degree `c`**, so nothing here is
a locality statement for `Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport`, for
`Stacks.Perfect.SupportedFraction.cechHomologyToSupport` or for the class map of
[Stacks, Tag 0G7Q].  Reading it in degree `c` needs the comparison of the degree-`c` cohomology
sheaf of `i_* R𝓗_T(ℱ[0])` with restriction, which is
`Stacks.Gysin.supportCohomologyRestrictIso` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcision.lean` — *downstream* of this
file, so the degree-`c` statement belongs there rather than here; restating it here would be a
second copy of that isomorphism, which the chart transport of [Stacks, Tag 0G86] would then have
to be identified with.  Two further steps are needed for it: that the exact functor
`(-)|_W` commutes with the homology of a complex, and that `singleRestrictIso` is the
single-complex comparison `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` that
`Stacks.Gysin.supportCohomologyPullbackIso` is built from — the two differ by the naturality of
`HomologicalComplex.singleMapHomologicalComplex` in the functor, across
`modulePullbackRestrictIso`.  With those, the degree-`c` reading gives the base change of
`Stacks.Perfect.SupportedFraction.supportedFractionSource` together with this file's square and
`Stacks.Perfect.PushforwardRestrict.restrictFunctor_map_fractionHom`.

Everything is for an **open immersion**; for a general morphism the identification of the Čech
complexes it rests on is not available.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Remark 36.6.6 (Tag 0G7L)](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
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
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation
open Stacks.Perfect.PushforwardRestrict (restrictComplexIso)
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechDerivedSupportBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Two general facts -/

section General

/-- **A functor isomorphic to one preserving zero morphisms preserves zero morphisms.**  The
naturality square of the isomorphism at a zero morphism says that the image of that zero
morphism, precomposed with an isomorphism, is zero. -/
theorem preservesZeroMorphisms_of_natIso {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] {P R : C ⥤ D} [P.PreservesZeroMorphisms]
    (α : P ≅ R) : R.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso α

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {V V' : Type*} [Category* V] [Category* V'] [HasZeroObject V] [HasZeroObject V']
  [HasZeroMorphisms V] [HasZeroMorphisms V']

/-- Extending an isomorphism of complexes along an embedding of complex shapes. -/
def extendIso {K L : HomologicalComplex V c} (h : K ≅ L) (e : c.Embedding c') :
    K.extend e ≅ L.extend e where
  hom := HomologicalComplex.extendMap h.hom e
  inv := HomologicalComplex.extendMap h.inv e
  hom_inv_id := by
    rw [← HomologicalComplex.extendMap_comp, h.hom_inv_id, HomologicalComplex.extendMap_id]
  inv_hom_id := by
    rw [← HomologicalComplex.extendMap_comp, h.inv_hom_id, HomologicalComplex.extendMap_id]

/-- The forward map of `extendIso h e` is the extension of `h.hom` along `e`. -/
@[simp]
theorem extendIso_hom {K L : HomologicalComplex V c} (h : K ≅ L) (e : c.Embedding c') :
    (extendIso h e).hom = HomologicalComplex.extendMap h.hom e := rfl

variable (P : V ⥤ V') [P.PreservesZeroMorphisms]

/-- The comparison of `HomologicalComplex.mapHomologicalComplexExtendIso` is natural in the
complex, read on the `hom` direction. -/
@[reassoc]
theorem mapHomologicalComplexExtendIso_hom_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L)
    (e : c.Embedding c') :
    (HomologicalComplex.mapHomologicalComplexExtendIso P K e).hom ≫
        (P.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) =
      HomologicalComplex.extendMap ((P.mapHomologicalComplex c).map φ) e ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso P L e).hom := by
  rw [← Iso.comp_inv_eq, Category.assoc,
    HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality, Iso.hom_inv_id_assoc]

variable [DecidableEq ι] [DecidableEq ι']

/-- **Applying a functor preserving zero morphisms commutes with the identification of the
extension of a complex concentrated in one degree.**  Both sides are morphisms into a complex
concentrated in degree `i'`, so only the degree-`i'` component is at stake, and there both sides
are the comparison of the two canonical identifications of the degree-`i` term. -/
theorem extendMap_singleMapHomologicalComplex_comp_extendSingleIso_hom
    (e : c.Embedding c') {i : ι} {i' : ι'} (h : e.f i = i') (A : V) :
    HomologicalComplex.extendMap
          ((HomologicalComplex.singleMapHomologicalComplex P c i).hom.app A) e ≫
        (HomologicalComplex.extendSingleIso e (P.obj A) i i' h).hom =
      (HomologicalComplex.mapHomologicalComplexExtendIso P
            ((HomologicalComplex.single V c i).obj A) e).hom ≫
        (P.mapHomologicalComplex c').map
            (HomologicalComplex.extendSingleIso e A i i' h).hom ≫
          (HomologicalComplex.singleMapHomologicalComplex P c' i').hom.app A := by
  refine HomologicalComplex.to_single_hom_ext (j := i') ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ e h,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, HomologicalComplex.mapHomologicalComplexExtendIso_hom_f P _ e h,
    Functor.mapHomologicalComplex_map_f, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [Category.assoc, Functor.map_comp]
  simp

end General

/-! ### Derived pullback along the inclusion of an open subscheme, read on complexes -/

section Restrict

variable {X : Scheme.{u}} (W : X.Opens)

/-- The inclusion of an open subscheme, as an open immersion of ringed spaces. -/
abbrev openIncl := X.toRingedSpace.ofRestrict W.isOpenEmbedding

/-- Pullback of modules along an open immersion of ringed spaces is left exact, being exact. -/
theorem preservesFiniteLimits_modulePullback {X' Y' : RingedSpace.{u, u}} (g : X' ⟶ Y')
    [SheafedSpace.IsOpenImmersion g] : PreservesFiniteLimits (modulePullback g) :=
  (modulePullback g).preservesFiniteLimits_of_preservesHomology

attribute [local instance] preservesFiniteLimits_modulePullback

/-- The preimage in the open subscheme `W` of a subset of `X`, written as a subset of `W`.  This
is `Stacks.Cohomology.SupportedComplexes.closedSubsetPreimage` along the ringed-space inclusion,
with its type read at the scheme `W.toScheme`: leaving that scheme to be inferred asks the
unifier to invert the coercion of a scheme to its carrier, which it does not do. -/
abbrev restrictClosedSubset (T : Set X) : Set W.toScheme := closedSubsetPreimage (openIncl W) T

/-- The preimage in `W` of a closed subset of `X` is closed. -/
theorem isClosed_restrictClosedSubset {T : Set X} (hT : IsClosed T) :
    IsClosed (restrictClosedSubset W T) :=
  isClosed_closedSubsetPreimage (openIncl W) T hT

/-- **The common zero locus of the restricted equations lies over the common zero locus of the
equations.**  A point of `W` outside every principal open of a restricted equation lies outside
every principal open of the equation itself, the principal opens of the restrictions being the
preimages of the principal opens (`AlgebraicGeometry.Scheme.preimage_basicOpen`).  So the
hypothesis on the restricted equations that the square below carries is the restriction of the
hypothesis on `X`. -/
theorem equationsClosedSet_restrict_subset {m : ℕ} (e : Fin m → Γ(X, ⊤)) {T : Set X}
    (hTe : equationsClosedSet e ⊆ T) :
    equationsClosedSet (fun j => W.ι.appTop (e j)) ⊆ restrictClosedSubset W T := by
  intro x hx
  refine hTe ?_
  simp only [equationsClosedSet, Set.mem_compl_iff, SetLike.mem_coe,
    TopologicalSpace.Opens.mem_iSup] at hx ⊢
  rintro ⟨i, hi⟩
  refine hx ⟨i, ?_⟩
  have hb : W.toScheme.basicOpen (W.ι.appTop (e i)) = W.ι ⁻¹ᵁ X.basicOpen (e i) :=
    (Scheme.preimage_basicOpen W.ι (e i)).symm
  rw [hb]
  exact hi

/-- **Pullback of modules along the ringed-space inclusion of an open subscheme is restriction
along the inclusion of that open subscheme.**  This is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, read through the definitional
equality of the pullback of modules along a morphism of schemes with the pullback along the
underlying morphism of ringed spaces.  `Stacks.Gysin.modulePullbackRestrictFunctorIso` is the
same expression, downstream of this file. -/
def modulePullbackRestrictIso :
    modulePullback (openIncl W) ≅ Scheme.Modules.restrictFunctor W.ι :=
  (Scheme.Modules.restrictFunctorIsoPullback W.ι).symm

/-- **Derived pullback along the inclusion of an open subscheme, read on complexes.**  On the
image of `DerivedCategory.Q` the derived pullback along the inclusion of `W` is the restriction
of complexes to `W`: the derived pullback along an open immersion is the derived functor of the
degreewise pullback (`derivedPullbackOpenImmersionIso`), that derived functor is computed
degreewise (`CategoryTheory.Functor.mapDerivedCategoryFactors`), and the degreewise pullback is
restriction (`modulePullbackRestrictIso`). -/
def restrictQNatIso :
    DerivedCategory.Q ⋙ derivedPullback (openIncl W) ≅
      (Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
  Functor.isoWhiskerLeft DerivedCategory.Q
      (derivedPullbackOpenImmersionIso (openIncl W)) ≪≫
    (modulePullback (openIncl W)).mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (modulePullbackRestrictIso W) (ComplexShape.up ℤ))
      DerivedCategory.Q

/-- `restrictQNatIso` at a complex. -/
def restrictQIso (C : CochainComplex X.Modules ℤ) :
    (derivedPullback (openIncl W)).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C) :=
  (restrictQNatIso W).app C

/-- `restrictQIso` is natural in the complex. -/
theorem restrictQIso_hom_naturality {C D : CochainComplex X.Modules ℤ} (φ : C ⟶ D) :
    (derivedPullback (openIncl W)).map (DerivedCategory.Q.map φ) ≫ (restrictQIso W D).hom =
      (restrictQIso W C).hom ≫
        DerivedCategory.Q.map
          (((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) :=
  (restrictQNatIso W).hom.naturality φ

end Restrict

/-! ### Base change of the augmentation of Tag 0G7L -/

section Augmentation

variable {X : Scheme.{u}} (W : X.Opens) {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules)

/-- **The identification of the restricted extended alternating Čech complex with the extended
alternating Čech complex of the restricted equations**, with the restriction written as the
degreewise functor rather than as `Stacks.Perfect.PushforwardRestrict.restrictComplex`.  Pinning
that spelling once is what lets the extension by zero below compose with it without a
transport. -/
def restrictCplxIso :
    ((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedAlternatingCech e F).complex ≅
      (extendedAlternatingCech (fun j => W.ι.appTop (e j))
        ((Scheme.Modules.restrictFunctor W.ι).obj F)).complex :=
  restrictComplexIso e W.ι (extendedAlternatingCech e F)
    (extendedAlternatingCech (fun j => W.ι.appTop (e j))
      ((Scheme.Modules.restrictFunctor W.ι).obj F))

/-- In degree `0` the augmentation of the extended alternating Čech complex is the canonical
identification of the degree-`0` term with the coefficient module. -/
theorem augmentationComplex_f_zero :
    (augmentationComplex e F).f 0 =
      (extendedAlternatingCech e F).zeroIso.hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv := by
  simp [augmentationComplex, CochainComplex.toSingle₀Equiv_symm_apply_f_zero]

/-- In degree `0` the comparison of the restricted Čech complex with the Čech complex of the
restricted equations is the comparison of the two identifications of the degree-`0` term. -/
theorem restrictCplxIso_hom_f_zero :
    (restrictCplxIso W e F).hom.f 0 =
      (Scheme.Modules.restrictFunctor W.ι).map (extendedAlternatingCech e F).zeroIso.hom ≫
        (extendedAlternatingCech (fun j => W.ι.appTop (e j))
          ((Scheme.Modules.restrictFunctor W.ι).obj F)).zeroIso.inv := rfl

/-- **The augmentation of [Stacks, Tag 0G7L] is carried across the identification of the two
extended alternating Čech complexes of [Stacks, Tag 0G7U].**  Both sides are morphisms into a
complex concentrated in degree `0`, so only the degree-`0` component is at stake, and there both
sides are the identification of the degree-`0` term of the Čech complex with the coefficient
module. -/
theorem restrictCplxIso_hom_comp_augmentationComplex :
    (restrictCplxIso W e F).hom ≫
        augmentationComplex (fun j => W.ι.appTop (e j))
          ((Scheme.Modules.restrictFunctor W.ι).obj F) =
      ((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (augmentationComplex e F) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor W.ι)
          (ComplexShape.up ℕ) 0).hom.app F := by
  refine HomologicalComplex.to_single_hom_ext (j := 0) ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    augmentationComplex_f_zero, augmentationComplex_f_zero, restrictCplxIso_hom_f_zero,
    Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_map_assoc]

/-- **The augmentation of [Stacks, Tag 0G7L] is carried across the identification of the two
Čech complexes, after extending the grading from `ℕ` to `ℤ`.** -/
theorem extendMap_restrictCplxIso_comp_augmentationExtend :
    HomologicalComplex.extendMap (restrictCplxIso W e F).hom ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendMap
              (augmentationComplex (fun j => W.ι.appTop (e j))
                ((Scheme.Modules.restrictFunctor W.ι).obj F)) ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
              ((Scheme.Modules.restrictFunctor W.ι).obj F) 0 0 rfl).hom) =
      (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.restrictFunctor W.ι)
            (extendedAlternatingCech e F).complex ComplexShape.embeddingUpNat).hom ≫
        ((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap (augmentationComplex e F)
                ComplexShape.embeddingUpNat ≫
              (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom) ≫
          (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor W.ι)
            (ComplexShape.up ℤ) 0).hom.app F := by
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    restrictCplxIso_hom_comp_augmentationComplex, HomologicalComplex.extendMap_comp,
    Category.assoc,
    extendMap_singleMapHomologicalComplex_comp_extendSingleIso_hom
      (Scheme.Modules.restrictFunctor W.ι) ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl F]
  simp only [Functor.map_comp, Category.assoc]
  rw [mapHomologicalComplexExtendIso_hom_naturality_assoc]

end Augmentation

/-! ### The two identifications the square needs -/

section Isos

variable {X : Scheme.{u}} (W : X.Opens) {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules)

/-- **The restriction of the extended alternating Čech complex of [Stacks, Tag 0G7I], with the
grading extended to `ℤ`, is the extended alternating Čech complex of the restricted
equations.**  This is `restrictCplxIso` read through the commutation of extension by zero with a
functor preserving zero morphisms. -/
def restrictExtendIso :
    ((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extendedAlternatingCech e F).complex.extend ComplexShape.embeddingUpNat) ≅
      (extendedAlternatingCech (fun j => W.ι.appTop (e j))
          ((Scheme.Modules.restrictFunctor W.ι).obj F)).complex.extend
        ComplexShape.embeddingUpNat :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.restrictFunctor W.ι)
      (extendedAlternatingCech e F).complex ComplexShape.embeddingUpNat).symm ≪≫
    extendIso (restrictCplxIso W e F) ComplexShape.embeddingUpNat

/-- The forward map of `restrictExtendIso` is the inverse of the comparison
`HomologicalComplex.mapHomologicalComplexExtendIso` followed by the extension of
`(restrictCplxIso W e F).hom` along `ComplexShape.embeddingUpNat`. -/
theorem restrictExtendIso_hom :
    (restrictExtendIso W e F).hom =
      (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.restrictFunctor W.ι)
          (extendedAlternatingCech e F).complex ComplexShape.embeddingUpNat).inv ≫
        HomologicalComplex.extendMap (restrictCplxIso W e F).hom
          ComplexShape.embeddingUpNat := rfl

/-- The augmentation of [Stacks, Tag 0G7L] is carried across `restrictExtendIso`, at the level of
`ℤ`-graded complexes. -/
theorem restrictExtendIso_hom_comp_augmentationExtend :
    (restrictExtendIso W e F).hom ≫
        (HomologicalComplex.extendMap
              (augmentationComplex (fun j => W.ι.appTop (e j))
                ((Scheme.Modules.restrictFunctor W.ι).obj F)) ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
              ((Scheme.Modules.restrictFunctor W.ι).obj F) 0 0 rfl).hom) =
      ((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap (augmentationComplex e F)
              ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor W.ι)
          (ComplexShape.up ℤ) 0).hom.app F := by
  rw [restrictExtendIso_hom, Category.assoc, extendMap_restrictCplxIso_comp_augmentationExtend,
    Iso.inv_hom_id_assoc]

/-- **The derived pullback of the extended alternating Čech complex along the inclusion of an
open subscheme is the extended alternating Čech complex of the restricted equations.**  This is
the identification `(ℱ')^• = g^*ℱ^•` of [Stacks, Tag 0G7U] in the derived category, for `g` an
open immersion. -/
def cechRestrictIso :
    (derivedPullback (openIncl W)).obj
        (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) ≅
      DerivedCategory.Q.obj
        ((cplx (fun j => W.ι.appTop (e j)) ((Scheme.Modules.restrictFunctor W.ι).obj F)).extend
          ComplexShape.embeddingUpNat) :=
  restrictQIso W ((extendedAlternatingCech e F).complex.extend ComplexShape.embeddingUpNat) ≪≫
    DerivedCategory.Q.mapIso (restrictExtendIso W e F)

/-- The forward map of `cechRestrictIso` is the forward map of `restrictQIso` followed by the image
of `(restrictExtendIso W e F).hom` under `DerivedCategory.Q`. -/
theorem cechRestrictIso_hom :
    (cechRestrictIso W e F).hom =
      (restrictQIso W
          ((extendedAlternatingCech e F).complex.extend ComplexShape.embeddingUpNat)).hom ≫
        DerivedCategory.Q.map (restrictExtendIso W e F).hom := rfl

/-- **The derived pullback of a module placed in degree `0` along the inclusion of an open
subscheme is its restriction, placed in degree `0`.** -/
def singleRestrictIso :
    (derivedPullback (openIncl W)).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor W.toScheme.Modules 0).obj
        ((Scheme.Modules.restrictFunctor W.ι).obj F) :=
  restrictQIso W ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor W.ι)
        (ComplexShape.up ℤ) 0).app F)

/-- The forward map of `singleRestrictIso` is the forward map of `restrictQIso` followed by the
image under `DerivedCategory.Q` of the comparison `HomologicalComplex.singleMapHomologicalComplex`
at `F`. -/
theorem singleRestrictIso_hom :
    (singleRestrictIso W F).hom =
      (restrictQIso W ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor W.ι)
            (ComplexShape.up ℤ) 0).hom.app F) := rfl

/-- The formal identity behind `cechRestrictIso_hom_comp_augmentation`: a square of complexes,
pushed into the derived categories through a comparison natural in the complex.  Stated at
variable categories, so that the rewriting happens where no derived category appears. -/
theorem assembleAug {C₁ D₁ C₂ D₂ : Type*} [Category* C₁] [Category* D₁]
    [Category* C₂] [Category* D₂] (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (G : C₁ ⥤ C₂) (L : D₁ ⥤ D₂)
    {A M : C₁} {B N : C₂} (a : A ⟶ M) (rei : G.obj A ⟶ B) (a' : B ⟶ N) (sg : G.obj M ⟶ N)
    (rqa : L.obj (Q₁.obj A) ⟶ Q₂.obj (G.obj A)) (rqm : L.obj (Q₁.obj M) ⟶ Q₂.obj (G.obj M))
    (hcx : rei ≫ a' = G.map a ≫ sg)
    (hnat : L.map (Q₁.map a) ≫ rqm = rqa ≫ Q₂.map (G.map a)) :
    (rqa ≫ Q₂.map rei) ≫ Q₂.map a' = L.map (Q₁.map a) ≫ rqm ≫ Q₂.map sg := by
  rw [Category.assoc, ← Q₂.map_comp, hcx, Q₂.map_comp, ← Category.assoc, ← hnat, Category.assoc]

/-- **The augmentation of [Stacks, Tag 0G7L] is carried across `cechRestrictIso`.**  This is
`restrictExtendIso_hom_comp_augmentationExtend` in the derived category, by the naturality of
`restrictQIso`. -/
theorem cechRestrictIso_hom_comp_augmentation :
    (cechRestrictIso W e F).hom ≫
        augmentation (fun j => W.ι.appTop (e j))
          ((Scheme.Modules.restrictFunctor W.ι).obj F) =
      (derivedPullback (openIncl W)).map (augmentation e F) ≫ (singleRestrictIso W F).hom :=
  assembleAug DerivedCategory.Q DerivedCategory.Q
    ((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℤ))
    (derivedPullback (openIncl W)) _ _ _ _ _ _
    (restrictExtendIso_hom_comp_augmentationExtend W e F)
    (restrictQIso_hom_naturality W
      (HomologicalComplex.extendMap (augmentationComplex e F) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom))

end Isos

/-! ### The square -/

section Square

/-- The formal identity behind `supportPushPullbackIso_hom_comp_map_cechRestrictIso`: a map into
the source of an invertible counit is determined through that counit.  Stated at a variable
category, so that the rewriting happens where no derived category appears. -/
theorem chase {C : Type*} [Category* C] {a b sa sb l : C}
    (k : a ⟶ b) (sk : sa ⟶ sb) (ea : sa ⟶ a) (eb : sb ≅ b) (x : l ⟶ sa)
    (cc : l ⟶ a) (d : a ⟶ l)
    (h1 : x ≫ ea = cc) (h2 : sk ≫ eb.hom = ea ≫ k) (h3 : d ≫ cc = 𝟙 a) :
    d ≫ x ≫ sk = k ≫ eb.inv := by
  refine (Iso.eq_comp_inv eb).mpr ?_
  simp only [Category.assoc]
  rw [h2, ← Category.assoc x, h1, ← Category.assoc, h3, Category.id_comp]

/-- The formal identity behind `map_cechToDerivedSupport_comp_supportPushPullbackIso_hom`, once
the naturality of the excision isomorphism, the base change of the augmentation and `chase` are
inserted.  Stated at variable categories, for the same reason. -/
theorem assemble {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (S : C ⥤ C)
    (S' : D ⥤ D) {A M : C} {B N : D} (aug : A ⟶ M) (sinv : A ⟶ S.obj A)
    (xA : L.obj (S.obj A) ⟶ S'.obj (L.obj A)) (xM : L.obj (S.obj M) ⟶ S'.obj (L.obj M))
    (k : L.obj A ⟶ B) (sigma : L.obj M ⟶ N) (aug' : B ⟶ N) (sinv' : B ⟶ S'.obj B)
    (hnat : L.map (S.map aug) ≫ xM = xA ≫ S'.map (L.map aug))
    (haug : k ≫ aug' = L.map aug ≫ sigma)
    (hstar : L.map sinv ≫ xA ≫ S'.map k = k ≫ sinv') :
    L.map (sinv ≫ S.map aug) ≫ xM ≫ S'.map sigma = k ≫ sinv' ≫ S'.map aug' := by
  rw [L.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (L.map (S.map aug)) xM, hnat]
  simp only [Category.assoc]
  rw [← S'.map_comp, ← haug, S'.map_comp, ← Category.assoc xA,
    ← Category.assoc (L.map sinv), hstar]
  simp only [Category.assoc]

variable {X : Scheme.{u}} (W : X.Opens) {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules)
  [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
  (hT' : IsClosed (restrictClosedSubset W T))
  (hTe' : equationsClosedSet (fun j => W.ι.appTop (e j)) ⊆ restrictClosedSubset W T)

omit [SheafOfModules.IsQuasicoherent F] in
/-- **The excision isomorphism of [Stacks, Tag 0G78] carries the inverse counit of
[Stacks, Tag 0G72] at the extended alternating Čech complex to the one on `W`.**  This is
`Stacks.Perfect.SupportPushExcision.supportPushPullbackIso_hom_comp_supportPushCounit` together
with the naturality of the counit along `cechRestrictIso`, the counit being invertible at both
Čech complexes by [Stacks, Tag 0G7M]. -/
theorem supportPushPullbackIso_hom_comp_map_cechRestrictIso :
    (derivedPullback (openIncl W)).map
          (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).inv ≫
        (SupportPushExcision.supportPushPullbackIso (openIncl W) hT).hom.app
            (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) ≫
          (supportPush hT').map (cechRestrictIso W e F).hom =
      (cechRestrictIso W e F).hom ≫
        (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech
          (fun j => W.ι.appTop (e j)) ((Scheme.Modules.restrictFunctor W.ι).obj F)
          hT' hTe')).inv :=
  chase _ _ _
    (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech
      (fun j => W.ι.appTop (e j)) ((Scheme.Modules.restrictFunctor W.ι).obj F) hT' hTe')) _ _ _
    (SupportPushExcision.supportPushPullbackIso_hom_comp_supportPushCounit (openIncl W) hT
      (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)))
    ((supportPushCounit hT').naturality (cechRestrictIso W e F).hom)
    (((derivedPullback (openIncl W)).map_comp _ _).symm.trans
      ((congrArg (derivedPullback (openIncl W)).map
          (@asIso _ _ _ _ _
            (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).inv_hom_id).trans
        ((derivedPullback (openIncl W)).map_id _)))

omit [SheafOfModules.IsQuasicoherent F] in
/-- **The comparison of [Stacks, Tag 0G7L] commutes with excision along an open immersion.**  The
derived pullback of `Stacks.Perfect.SupportedFraction.cechToDerivedSupport` along the inclusion
of an open subscheme `W`, followed by the excision isomorphism
`Stacks.Perfect.SupportPushExcision.supportPushPullbackIso` of [Stacks, Tag 0G78] and by
`i'_* R𝓗_{W ∩ T}` of the identification of the restricted coefficient module, is the comparison
of [Stacks, Tag 0G7L] for the restricted equations and `ℱ|_W`, read across the identification
`cechRestrictIso` of the two extended alternating Čech complexes.

This is the missing link of the open-immersion case of [Stacks, Tag 0G7U]: the comparison of
[Stacks, Tag 0G7L] is determined by the triangle of that remark, both halves of which are carried
across the excision isomorphism, so the only content is the base change
`cechRestrictIso_hom_comp_augmentation` of the augmentation. -/
theorem map_cechToDerivedSupport_comp_supportPushPullbackIso_hom :
    (derivedPullback (openIncl W)).map (cechToDerivedSupport e F hT hTe) ≫
        (SupportPushExcision.supportPushPullbackIso (openIncl W) hT).hom.app
            ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
          (supportPush hT').map (singleRestrictIso W F).hom =
      (cechRestrictIso W e F).hom ≫
        cechToDerivedSupport (fun j => W.ι.appTop (e j))
          ((Scheme.Modules.restrictFunctor W.ι).obj F) hT' hTe' :=
  assemble (derivedPullback (openIncl W)) (supportPush hT) (supportPush hT')
    (augmentation e F)
    (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).inv _ _
    (cechRestrictIso W e F).hom (singleRestrictIso W F).hom
    (augmentation (fun j => W.ι.appTop (e j)) ((Scheme.Modules.restrictFunctor W.ι).obj F))
    (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech
      (fun j => W.ι.appTop (e j)) ((Scheme.Modules.restrictFunctor W.ι).obj F) hT' hTe')).inv
    ((SupportPushExcision.supportPushPullbackIso (openIncl W) hT).hom.naturality
      (augmentation e F))
    (cechRestrictIso_hom_comp_augmentation W e F)
    (supportPushPullbackIso_hom_comp_map_cechRestrictIso W e F hT hTe hT' hTe')

end Square

end Stacks.Perfect.CechDerivedSupportBaseChange

end
