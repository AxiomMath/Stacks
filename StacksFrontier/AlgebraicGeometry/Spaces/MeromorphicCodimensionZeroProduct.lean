module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroAffine
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SigmaPiComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison

/-!
# `𝒦_X` is the product of the direct images at the codimension-zero points

Let `X` be an algebraic space over a scheme `S` satisfying hypotheses (a), (b) and (c) of
Stacks 0ENA and let `P` be a presentation of its schematic locus at the codimension-zero points.
This file assembles the affine-chart computation
`AlgebraicGeometry.Space.CodimensionZeroPresentation.bijective_pi_genericPointComparison_app` into
an isomorphism of `𝒪_X`-modules

`𝒦_X ⟶ ∏_{η ∈ X⁰} j_{η, *}𝒪_{X, η}`.

The comparison is the one induced by the canonical maps of sheaves of rings, read on the
underlying `𝒪_X`-modules and lifted to the module universe `u + 1` in which the index type `X⁰`
lives.  It is an isomorphism because it is bijective on the sections over every affine étale
chart and the affine étale charts are a cover-dense family.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicModule` and
  `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointModule`: `𝒦_X` and
  `j_{η, *}𝒪_{X, η}` as `𝒪_X`-modules with sections in `Type (u + 1)`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointModuleComparison` and
  `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointModuleComparisonPi`: the
  comparisons.

## Main results

* `AlgebraicGeometry.Space.isLocallyInjective_of_injective_of_isCoverDense`: a morphism of
  presheaves of modules injective on the sections over a cover-dense family of objects is
  locally injective.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.isIso_genericPointModuleComparisonPi`:
  the comparison is an isomorphism.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

/-! ### Local injectivity from a cover-dense family -/

/-- **A morphism of presheaves of modules injective on the sections over the objects in the image
of a cover-dense functor is locally injective.**

Being cover-dense means that for every object of the target site the arrows that factor through
an object of the image generate a covering sieve; over each such arrow the two sections agree by
the hypothesis, and the equalizer sieve is downward closed. -/
theorem isLocallyInjective_of_injective_of_isCoverDense.{m, r, v₁, u₁, v₂, u₂}
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : GrothendieckTopology D) (Φ : C ⥤ D) (hΦ : Φ.IsCoverDense K)
    {O : Dᵒᵖ ⥤ RingCat.{r}} {M N : PresheafOfModules.{m} O} (f : M ⟶ N)
    (h : ∀ Y : C, Function.Injective (f.app (op (Φ.obj Y)))) :
    Presheaf.IsLocallyInjective K ((PresheafOfModules.toPresheaf O).map f) := by
  constructor
  intro Z a b hab
  refine K.superset_covering ?_ (hΦ.is_cover Z.unop)
  rintro T g ⟨⟨A, lift, map, fac⟩⟩
  have hA : (Presheaf.equalizerSieve (F := (PresheafOfModules.toPresheaf O).obj M) a b) map :=
    h A (((PresheafOfModules.naturality_apply f map.op a).trans
      (congrArg (fun z => (N.map map.op) z) hab)).trans
      (PresheafOfModules.naturality_apply f map.op b).symm)
  have hlift := (Presheaf.equalizerSieve
    (F := (PresheafOfModules.toPresheaf O).obj M) a b).downward_closed hA lift
  rwa [fac] at hlift

/-- **The sheaf of meromorphic functions as an `𝒪_X`-module**, with sections lifted to the
universe in which the codimension-zero points live. -/
noncomputable def meromorphicModule (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) : Modules.{u, u + 1} B S hS X.1 X.2 :=
  SheafOfModules.uliftObj.{_, _, _, _, u + 1}
    (AlgebraSheaf.underlyingModule (meromorphicAlgebraSheaf B S hS X))

/-! ### Bijectivity of a morphism into a product -/

/-- **A morphism into a product of sheaves of modules is bijective on the sections over an object
as soon as the family of its components is.**  The sections functor preserves products, so the
sections of the product are the product of the sections. -/
theorem bijective_val_app_of_bijective_pi.{m, r, v', u'}
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {ι : Type m} (M : ι → SheafOfModules.{m} R) [HasProduct M] {A : SheafOfModules.{m} R}
    (f : A ⟶ ∏ᶜ M) (U : Cᵒᵖ)
    [PreservesLimitsOfShape (Discrete ι)
      (SheafOfModules.evaluation.{m} R U ⋙ forget (ModuleCat (R.obj.obj U)))]
    (h : Function.Bijective fun s : A.val.obj U =>
      fun i => (Pi.π M i).val.app U (f.val.app U s)) :
    Function.Bijective (f.val.app U) := by
  let E := SheafOfModules.evaluation.{m} R U ⋙ forget (ModuleCat (R.obj.obj U))
  let q := piComparison E M ≫ (Types.productIso fun i => E.obj (M i)).hom
  have hqbij : Function.Bijective q := ConcreteCategory.bijective_of_isIso q
  have hcomp : (fun s => q (E.map f s)) =
      fun s : A.val.obj U => fun i => (Pi.π M i).val.app U (f.val.app U s) := by
    funext s i
    show (Types.productIso fun i => E.obj (M i)).hom (piComparison E M (E.map f s)) i = _
    rw [Types.productIso_hom_comp_eval_apply]
    exact ConcreteCategory.congr_hom (piComparison_comp_π E M i) (E.map f s)
  rw [← hcomp] at h
  exact (hqbij.of_comp_iff' (E.map f)).mp h

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1)

/-! ### The modules and the comparison -/

/-- **The direct image `j_{η, *}𝒪_{X, η}` as an `𝒪_X`-module**, with sections lifted to the
universe in which the codimension-zero points live. -/
noncomputable def genericPointModule {y : points B S hS X.1}
    (hy : localRingDimension B S hS y = 0) : Modules.{u, u + 1} B S hS X.1 X.2 :=
  SheafOfModules.uliftObj.{_, _, _, _, u + 1}
    (AlgebraSheaf.underlyingModule (AlgebraSheaf.ofHom (P.genericPointSharp hy)))

/-- The canonical comparison `𝒦_X ⟶ j_{η, *}𝒪_{X, η}`, as a morphism of `𝒪_X`-algebras. -/
noncomputable def genericPointAlgebraHom {y : points B S hS X.1}
    (hy : localRingDimension B S hS y = 0) :
    meromorphicAlgebraSheaf B S hS X ⟶ AlgebraSheaf.ofHom (P.genericPointSharp hy) where
  right := P.genericPointComparison hy
  comm U r := P.genericPointComparison_app_toMeromorphicFunctionSheaf hy U.unop r

/-- **The comparison `𝒦_X ⟶ j_{η, *}𝒪_{X, η}` of `𝒪_X`-modules.** -/
noncomputable def genericPointModuleComparison {y : points B S hS X.1}
    (hy : localRingDimension B S hS y = 0) : meromorphicModule B S hS X ⟶ P.genericPointModule hy :=
  SheafOfModules.uliftFunctor.{_, _, _, _, u + 1}.map
    (AlgebraSheaf.underlyingModuleMap (P.genericPointAlgebraHom hy))

/-- On sections the comparison of `𝒪_X`-modules is the comparison of sheaves of rings. -/
theorem genericPointModuleComparison_app {y : points B S hS X.1}
    (hy : localRingDimension B S hS y = 0) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (s : (meromorphicModule B S hS X).val.obj U) :
    (P.genericPointModuleComparison hy).val.app U s =
      ULift.up (((P.genericPointComparison hy).hom.app U).hom s.down) :=
  rfl

/-- **The comparison `𝒦_X ⟶ ∏_{η ∈ X⁰} j_{η, *}𝒪_{X, η}` of `𝒪_X`-modules.** -/
noncomputable def genericPointModuleComparisonPi :
    meromorphicModule B S hS X ⟶ ∏ᶜ fun η : CodimensionZeroPoints B S hS X.1 =>
      P.genericPointModule η.2 :=
  Pi.lift fun η => P.genericPointModuleComparison η.2

/-! ### The comparison is an isomorphism -/

/-- **The comparison of `𝒪_X`-modules is bijective on the sections over an affine étale chart.**
The sections of a product of sheaves of modules are the product of the sections, so this is the
ring-level statement
`AlgebraicGeometry.Space.CodimensionZeroPresentation.bijective_pi_genericPointComparison_app`
read through the universe lift. -/
theorem bijective_genericPointModuleComparisonPi_app
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (U : SmallEtale B S hS X.1)
    (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    Function.Bijective ((P.genericPointModuleComparisonPi).val.app (op U)) := by
  refine bijective_val_app_of_bijective_pi
    (fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2)
    P.genericPointModuleComparisonPi (op U) ?_
  have hfac (η : CodimensionZeroPoints B S hS X.1)
      (s : (meromorphicModule B S hS X).val.obj (op U)) :
      (Pi.π (fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2) η).val.app
            (op U) (P.genericPointModuleComparisonPi.val.app (op U) s) =
        ULift.up (((P.genericPointComparison η.2).hom.app (op U)).hom s.down) := by
    have h : P.genericPointModuleComparisonPi ≫
        Pi.π (fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2) η =
          P.genericPointModuleComparison η.2 := Pi.lift_π _ η
    exact congrFun (congrArg
      (fun f : meromorphicModule B S hS X ⟶ P.genericPointModule η.2 =>
        fun z => f.val.app (op U) z) h) s
  have hgoal : (fun s : (meromorphicModule B S hS X).val.obj (op U) =>
        fun η : CodimensionZeroPoints B S hS X.1 =>
          (Pi.π (fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2) η).val.app
            (op U) (P.genericPointModuleComparisonPi.val.app (op U) s)) =
      fun s => fun η : CodimensionZeroPoints B S hS X.1 =>
        ULift.up (((P.genericPointComparison η.2).hom.app (op U)).hom s.down) :=
    funext fun s => funext fun η => hfac η s
  rw [hgoal]
  have hc := P.bijective_pi_genericPointComparison_app hwa hfin U hU
  refine ⟨fun s t h => ?_, fun t => ?_⟩
  · exact congrArg ULift.up (hc.injective (funext fun η => congrArg ULift.down (congrFun h η)))
  · obtain ⟨s, hs⟩ := hc.surjective fun η => ULift.down (t η)
    exact ⟨ULift.up s, funext fun η => congrArg ULift.up (congrFun hs η)⟩

/-- **`𝒦_X` is the product over `X⁰` of the direct images `j_{η, *}𝒪_{X, η}`.**  The canonical
comparison of `𝒪_X`-modules is bijective on the sections over every affine étale chart, and the
affine étale charts are cover-dense in the small étale site, so the comparison is locally
bijective, hence an isomorphism. -/
theorem isIso_genericPointModuleComparisonPi
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) :
    IsIso (P.genericPointModuleComparisonPi) := by
  have hdense := SmallEtale.isCoverDense_affineEtaleInclusion B S hS X.1 X.2
  have : PresheafOfModules.IsLocallyInjective (smallEtaleRingedSite B S hS X.1 X.2).J
      (P.genericPointModuleComparisonPi).val :=
    isLocallyInjective_of_injective_of_isCoverDense _ (AffineEtale.inclusion B S hS X.1) hdense
      _ fun V => (P.bijective_genericPointModuleComparisonPi_app hwa hfin
        ((AffineEtale.inclusion B S hS X.1).obj V) V.2).injective
  have : PresheafOfModules.IsLocallySurjective (smallEtaleRingedSite B S hS X.1 X.2).J
      (P.genericPointModuleComparisonPi).val :=
    Stacks.PresheafOfModules.isLocallySurjective_of_surjective_of_isCoverDense _
      (AffineEtale.inclusion B S hS X.1) hdense _ fun V =>
      (P.bijective_genericPointModuleComparisonPi_app hwa hfin
        ((AffineEtale.inclusion B S hS X.1).obj V) V.2).surjective
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective _

/-! ### The direct sum -/

/-- **A chart no point of which lies over `η` has no sections of `j_{η, *}𝒪_{X, η}`**: the
base-changed chart is then empty, and the sections of the structure sheaf of an empty scheme are
trivial. -/
theorem subsingleton_genericPointModule_obj {y : points B S hS X.1}
    (hy : localRingDimension B S hS y = 0) (V : SmallEtale B S hS X.1)
    (hV : ∀ z : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)),
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom z ≠ y) :
    Subsingleton ((P.genericPointModule hy).val.obj (op V)) := by
  have : IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (P.specStalkSpace hy).1).obj (P.genericPointChart hy V))) :=
    ⟨fun z => hV _ ((P.mem_range_genericPointProjection_iff hy V _).mp ⟨z, rfl⟩)⟩
  have : Subsingleton ((P.genericPointStructureSheaf hy).obj.obj (op V)) :=
    inferInstanceAs (Subsingleton Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (P.specStalkSpace hy).1).obj (P.genericPointChart hy V)), ⊤))
  exact inferInstanceAs (Subsingleton (ULift.{u + 1}
    ((P.genericPointStructureSheaf hy).obj.obj (op V))))

/-- **Over an affine chart only finitely many codimension-zero points of `X` are in the image.**
A point of the chart above a codimension-zero point is itself of codimension `0`, and an affine
chart has finitely many such points by hypothesis (b) of Stacks 0ENA. -/
theorem finite_codimensionZeroPoints_mem_range
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (smallEtaleScheme B S hS X.1 V)) :
    {η : CodimensionZeroPoints B S hS X.1 | ∃ z, pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom z = η.1}.Finite := by
  have hWspace : IsAlgebraicSpace B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hfinV : {z : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) |
      localRingDimension B S hS z = 0}.Finite :=
    (hasLocallyFiniteIrreducibleComponents_iff_finite_codimensionZeroPoints B S hS).mp hfin
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) hWspace
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ hV) V.1.hom
      (isEtale_of_presheaf_etale B S hS V.2)
  have hkey : (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom ''
      {z | localRingDimension B S hS z = 0}).Finite := hfinV.image _
  refine (hkey.preimage Subtype.val_injective.injOn).subset ?_
  rintro η ⟨z, hz⟩
  refine ⟨z, ?_, hz⟩
  have hd := localRingDimension_pointsMap_of_etale B S hS hWspace X.2 V.1.hom
    (isEtale_of_presheaf_etale B S hS V.2) z
  exact hd.symm.trans (hz ▸ η.2)

/-- The family of direct images has a direct sum: the small étale site admits sheafification of
presheaves of abelian groups in the universe of the codimension-zero points. -/
theorem hasCoproduct_genericPointModule :
    HasCoproduct fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2 := by
  let := moduleHasWeakSheafify.{u, u} B S hS X.1
  let := moduleWEqualsLocallyBijective.{u, u} B S hS X.1
  infer_instance

/-- The comparison from the direct sum of the direct images to their product is locally
injective: the direct sum of sheaves of modules is locally the sectionwise direct sum, which
injects into the product. -/
theorem isLocallyInjective_sigmaPiComparison_genericPointModule :
    letI : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
    letI := P.hasCoproduct_genericPointModule
    PresheafOfModules.IsLocallyInjective (smallEtaleRingedSite B S hS X.1 X.2).J
      (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
        P.genericPointModule η.2).val := by
  let : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
  let := moduleHasWeakSheafify.{u, u} B S hS X.1
  let := moduleWEqualsLocallyBijective.{u, u} B S hS X.1
  let := P.hasCoproduct_genericPointModule
  exact Stacks.SheafOfModules.isLocallyInjective_of_comparison
    (fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2)
    (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2)
    fun i j => ι_comp_sigmaPiComparison_comp_π _ i j

/-- The comparison from the direct sum of the direct images to their product is surjective on
the sections over an affine étale chart: only finitely many of the direct images have nonzero
sections there, and a section of the product with finitely many nonzero components is the image
of the sum of its components. -/
theorem surjective_sigmaPiComparison_genericPointModule_app
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (A : AffineEtale B S hS X.1) :
    letI : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
    letI := P.hasCoproduct_genericPointModule
    Function.Surjective ((sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
      P.genericPointModule η.2).val.app (op ((AffineEtale.inclusion B S hS X.1).obj A))) := by
  let : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
  let := P.hasCoproduct_genericPointModule
  intro b
  refine Stacks.SheafOfModules.exists_preimage_of_finite_support
    (fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2)
    (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 => P.genericPointModule η.2)
    (fun i j => ι_comp_sigmaPiComparison_comp_π _ i j)
    (op ((AffineEtale.inclusion B S hS X.1).obj A)) b
    (finite_codimensionZeroPoints_mem_range (X := X) hfin
      ((AffineEtale.inclusion B S hS X.1).obj A) A.2).toFinset fun η hη => ?_
  have hV : ∀ z : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj
        ((AffineEtale.inclusion B S hS X.1).obj A))),
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj
          ((AffineEtale.inclusion B S hS X.1).obj A)))
        ((AffineEtale.inclusion B S hS X.1).obj A).1.hom z ≠ η.1 :=
    fun z hz => hη ((Set.Finite.mem_toFinset _).mpr ⟨z, hz⟩)
  have := P.subsingleton_genericPointModule_obj η.2
    ((AffineEtale.inclusion B S hS X.1).obj A) hV
  exact Subsingleton.elim _ _

/-- **The direct sum of the direct images is their product.**  The comparison is locally
injective because the direct sum of sheaves is locally the sectionwise direct sum, which injects
into the product; and it is surjective on the sections over every affine étale chart, because
only finitely many of the direct images have nonzero sections there, so it is locally
surjective. -/
theorem isIso_sigmaPiComparison_genericPointModule
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) :
    letI : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
    letI := P.hasCoproduct_genericPointModule
    IsIso (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
      P.genericPointModule η.2) := by
  let : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
  let := P.hasCoproduct_genericPointModule
  have := P.isLocallyInjective_sigmaPiComparison_genericPointModule
  have : PresheafOfModules.IsLocallySurjective (smallEtaleRingedSite B S hS X.1 X.2).J
      (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
        P.genericPointModule η.2).val :=
    Stacks.PresheafOfModules.isLocallySurjective_of_surjective_of_isCoverDense _
      (AffineEtale.inclusion B S hS X.1)
      (SmallEtale.isCoverDense_affineEtaleInclusion B S hS X.1 X.2) _
      fun A => P.surjective_sigmaPiComparison_genericPointModule_app hfin A
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective _

/-! ### Stacks 0ENA, the first conclusion -/

/-- **Stacks 0ENA, the first conclusion.** Let `X` be an algebraic space over a scheme `S` such
that

* (a) every weakly associated point of `X` is a point of codimension `0`,
* (b) every quasi-compact open of every étale scheme chart of `X` has finitely many irreducible
  components, the condition of Stacks 0BB1, and
* (c) every point of codimension `0` of `X` is represented by a monomorphism from the spectrum
  of a field.

Then the local rings `𝒪_{X, η}` at the points `η ∈ X⁰` of codimension `0` and the canonical
morphisms `j_η : Spec(𝒪_{X, η}) ⟶ X` are defined — this is the presentation `P` of the
schematic locus whose existence is `AlgebraicGeometry.Space.exists_codimensionZeroPresentation`
— and the sheaf of meromorphic functions `𝒦_X` is both the direct sum and the product over `X⁰`
of the direct images `j_{η, *}𝒪_{X, η}`:

`𝒦_X = ⨁_{η ∈ X⁰} j_{η, *}𝒪_{X, η} = ∏_{η ∈ X⁰} j_{η, *}𝒪_{X, η}`.

The two identifications are the canonical comparisons: the one into the product has components
the canonical maps `𝒦_X ⟶ j_{η, *}𝒪_{X, η}` of
`AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointComparison`, and the one out of
the direct sum is `CategoryTheory.Limits.sigmaPiComparison`, the identity on the diagonal and
zero off it. -/
@[stacks 0ENA "the first conclusion: the sheaf of meromorphic functions is the direct sum, and
equally the product, over the codimension-zero points of the direct images of the local rings
there, through the canonical comparisons"]
theorem exists_codimensionZeroPresentation_isIso_genericPointComparison
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X.1) :
    ∃ P : CodimensionZeroPresentation B S hS X.1,
      IsIso P.genericPointModuleComparisonPi ∧
        letI : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
        letI := P.hasCoproduct_genericPointModule
        IsIso (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
          P.genericPointModule η.2) := by
  obtain ⟨P⟩ := exists_codimensionZeroPresentation B S hS X.2 hfin hmono
  exact ⟨P, P.isIso_genericPointModuleComparisonPi hwa hfin,
    P.isIso_sigmaPiComparison_genericPointModule hfin⟩

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end
