module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.CanonicalDerivedTensorGeneral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatLocallyFiniteTor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatStrictlyLE
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatTruncation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FiniteTorCohomologyBound
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatCokernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 03TT: the constructible complexes of finite Tor dimension

Let `Λ` be a Noetherian ring, let `X` be a quasi-compact and quasi-separated scheme and let
`K ∈ D(X_étale, Λ)`. Then `K` lies in `D_ctf(X_étale, Λ)` — it has constructible cohomology
sheaves and its image over the constant coefficient ringed site of Tag 03TR has locally finite
Tor dimension in the sense of Tag 08FZ — exactly when it is represented by a finite complex of
constructible flat sheaves of `Λ`-modules; and if `K` has Tor amplitude in `[a, b]` then the
representative may be taken concentrated in `[a, b]`.

"Constructible flat sheaf of `Λ`-modules" is read as the source reads it: a constructible sheaf
of `Λ`-modules which is flat, flatness of a sheaf of `Λ`-modules on the small étale site being
flatness of the sheaf of modules it defines over the constant coefficient ring sheaf of Tag
03TR. That is the reading of Lemma 03TT of the source, in the chapter Étale Cohomology, whose
membership condition (1) is Definition 03TQ
there — locally finite Tor dimension in the sense of Cohomology on Sites, Definition 08FZ.
`AlgebraicGeometry.IsConstructibleFlatModuleSheaf`, the chapter's stratumwise formulation —
locally constant with finite projective values on the strata of a constructible stratification —
implies it, by
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`
together with `AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf`,
and the resolution of Tag 0960 produces terms of that stronger kind; what the cokernel appearing
in the truncation satisfies is the weaker, literal condition, which is why it is the one stated.

## Main definitions

* `Stacks.EtaleCohomology.IsRepresentedByFlatConstructibleComplex`: **condition (2) of Tag
  03TT**, that `K` be represented by a complex of constructible sheaves of `Λ`-modules, flat over
  the constant coefficient ring sheaf, vanishing outside a bounded interval.

## Main results

* `Stacks.EtaleCohomology.isConstructible_of_isRepresentedByFlatConstructibleComplex` and
  `Stacks.EtaleCohomology.locallyHasFiniteTorDimension_of_isRepresentedByFlatConstructibleComplex`:
  the direction (2) ⟹ (1), in its two halves.
* `Stacks.EtaleCohomology.exists_flatConstructibleRepresentative_of_hasTorAmplitude`: **the
  Tor-amplitude refinement**, from a Tor-amplitude bound on the whole constant coefficient
  ringed site.
* `Stacks.EtaleCohomology.isRepresentedByFlatConstructibleComplex_of_locallyHasFiniteTorDimension`:
  the direction (1) ⟹ (2).
* `Stacks.EtaleCohomology.isConstructibleFiniteTor_iff_isRepresentedByFlatConstructibleComplex`:
  **Tag 03TT**, the equivalence together with the Tor-amplitude refinement, with condition (1)
  stated absolutely — against the canonical derived tensor product, with no parameter standing
  for it.

## The two routes to the flatness of the truncation's new term

`Stacks.EtaleCohomology.exists_flatConstructibleRepresentative_of_isFlat_cokernel` reduces both
directions to one hypothesis, the flatness of `Coker(d^{a-1})` of the image of the resolution.
That is Tag 08G0, `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitude`,
and the two statements here reach it differently.

The refinement has a Tor-amplitude bound on the whole ringed site, so Tag 08G0 applies there
directly: all four of its universes are free, and the image of the resolution is a bounded above
complex of flat modules representing the image of `K`.

The direction (1) ⟹ (2) has only *locally* finite Tor dimension, and no global interval is
available: the passage from locally finite Tor dimension to finite Tor dimension,
`Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_locallyHasFiniteTorDimension`,
runs through the descent of Tor amplitude, and *that lemma* asks for an essentially small ringed
site whose morphisms and whose sections lie in one universe; the constant coefficient ringed site
is an `AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) r}` and is not one. (This is a
restriction of the interval descent alone, not of Tag 06YU, whose existence statement is free of
any relation between the three universes.) What is used instead
is that *flatness* is local on the site,
`Stacks.SheafOfModules.isFlat_of_ofArrows_of_isTerminal`, which has all its universes free:
quasi-compactness of `X` gives a finite covering family with one interval `[a, b]` valid on each
member, Tag 08G0 on each slice makes the restricted cokernel flat there, restriction preserves
cokernels, and flatness descends.

## Implementation notes

The coefficient universe is `max (u + 1) r`. It is forced by Tag 0960, whose resolution is built
from extensions by zero and so lives at the universe of Tag 095Z, and it is where the weak Serre
property of the constructible sheaves of `Λ`-modules — Tag 03RZ (3), needed for the
constructibility of the cokernel — is available; `UnivLE.{u + 1, max (u + 1) r}`, the hypothesis
under which the change of coefficients reflects vanishing, holds there as well. The universes of
the scheme and of the coefficient ring stay independent, as does the universe `d` of the derived
categories of modules on the ringed site.

The locally-finite-Tor condition of Tag 08FZ and the Tor-amplitude predicate are each measured
against a given derived tensor product, as everywhere in this development, so the intermediate
results below carry that datum as a parameter: a family `T` on the slices, and a single `T₀` on
the site itself. **Tag 03TT itself carries neither.** It is stated against the canonical derived
tensor product of Tag 06YU, `Stacks.SheafOfModules.canonicalDerivedTensorProduct`, on the
constant coefficient ringed site and on each of its slices, so that its condition (1) is a
property of `K` alone and the equivalence quantifies over no unconstructed data. That
instantiation is available because the existence of the derived tensor product does not require
the morphism universe of the site to agree with its section universe: the K-flat resolutions
Tag 06YU is assembled from resolve by flat modules supplied by a flat cover, which relates none
of the three universes of the site. See the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Existence.lean`.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G0](https://stacks.math.columbia.edu/tag/08G0)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r d

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ)]

/-- **Condition (2) of Tag 03TT.** An object of `D(X_étale, Λ)` is represented by a finite
complex of constructible flat sheaves of `Λ`-modules: a complex of constructible sheaves of
`Λ`-modules, each flat over the constant coefficient ring sheaf of Tag 03TR, vanishing outside
some bounded interval.

Flatness is that of the sheaf of modules over the constant coefficient ring sheaf which a sheaf
of `Λ`-modules defines, `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor`; by
`AlgebraicGeometry.etaleModuleStalk_flat_of_isFlat_terms` and
`AlgebraicGeometry.isFlatModuleStalk_of_flat_etaleModuleStalk` it is equally the flatness of all
the étale stalks as `Λ`-modules. -/
public def IsRepresentedByFlatConstructibleComplex
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) : Prop :=
  ∃ (F : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)) ℤ) (a b : ℤ),
    F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
      (∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (F.X i)) ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) r,
        max (u + 1) r} (O := (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O)
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ).obj (F.X i))) ∧
      Nonempty (DerivedCategory.Q.obj F ≅ K)

/-- **The chapter's stratumwise constructible flat condition implies condition (2) of Tag
03TT.** A bounded complex of sheaves which are, on the strata of a constructible stratification,
locally constant with finite projective values is a bounded complex of constructible sheaves flat
over the constant coefficient ring sheaf.

Constructibility is
`AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf`, a finite
projective module being finitely generated, and flatness is
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`,
a projective module being flat. The converse holds over a Noetherian coefficient ring, a finite
flat module over such a ring being projective, and is not proved: the resolution of Tag 0960
supplies terms of the stronger kind, and the cokernel the truncation of Tag 03TT introduces is
only known to satisfy the weaker one. -/
public theorem isRepresentedByFlatConstructibleComplex_of_isRepresentedByConstructibleFlatComplex
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsRepresentedByConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K) :
    IsRepresentedByFlatConstructibleComplex.{u, r} B X Λ K := by
  obtain ⟨C, a, b, hGE, hLE, hC, ⟨e⟩⟩ := hK
  exact ⟨C, a, b, hGE, hLE,
    fun i => isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hC i),
    fun i => isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf B X Λ
      (C.X i) (hC i), ⟨e⟩⟩

/-! ### The direction (2) ⟹ (1) -/

variable [IsNoetherianRing Λ]

omit [HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ)] in
/-- **Tag 03TT, the constructible-cohomology half of the direction (2) ⟹ (1).** An object
represented by a finite complex of constructible flat sheaves of `Λ`-modules has constructible
cohomology sheaves. Only the constructibility of the terms is used. -/
public theorem isConstructible_of_isRepresentedByFlatConstructibleComplex
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsRepresentedByFlatConstructibleComplex.{u, r} B X Λ K) :
    IsConstructible B X Λ K := by
  obtain ⟨F, -, -, -, -, hcon, -, ⟨e⟩⟩ := hK
  exact isConstructible_of_forall_isConstructibleModuleSheaf B X Λ
    (isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ) F hcon K e

/-! ### The slice instance context for locally finite Tor dimension -/

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) (ComplexShape.up ℤ)]
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)]

attribute [local instance 2000] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

omit [IsNoetherianRing Λ]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).obj M).Additive] in
/-- **Tag 03TT, the Tor-dimension half of the direction (2) ⟹ (1).** The image over the constant
coefficient ringed site of an object represented by a finite complex of constructible flat
sheaves of `Λ`-modules has locally finite Tor dimension.

Flatness of a term is flatness of all its étale stalks, by
`AlgebraicGeometry.etaleModuleStalk_flat_of_isFlat_terms`, which is what
`Stacks.EtaleCohomology.locallyHasFiniteTorDimension_of_flat_etaleModuleStalk` reads on every
slice. -/
public theorem locallyHasFiniteTorDimension_of_isRepresentedByFlatConstructibleComplex
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsRepresentedByFlatConstructibleComplex.{u, r} B X Λ K) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) T
      ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r,
        r} B X Λ).mapDerivedCategory.obj K) := by
  obtain ⟨F, a, b, hGE, hLE, -, hflat, ⟨e⟩⟩ := hK
  exact locallyHasFiniteTorDimension_of_flat_etaleModuleStalk.{u, max (u + 1) r, r, d}
    B X Λ T F a b hGE hLE
    (etaleModuleStalk_flat_of_isFlat_terms B X Λ F hflat) K e

/-! ### The direction (1) ⟹ (2) and the Tor-amplitude refinement -/

/-- The degreewise image over the constant coefficient ring sheaf of a complex of sheaves of
`Λ`-modules on the small étale site. The change of coefficients is exact, so this is the complex
Tag 08G0 is applied to. -/
public abbrev overConstantCoefficientsComplex
    (L : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)) ℤ) :
    CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)) ℤ :=
  ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L

omit [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ)]
  [IsNoetherianRing Λ]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))]
  hSliceDerived
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) (ComplexShape.up ℤ)]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).obj M).Additive]
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive] in
/-- The image over the constant coefficient ring sheaf of a complex of constructible flat sheaves
of `Λ`-modules which vanishes above `b` vanishes above `b`: the change of coefficients is
additive. -/
public theorem overConstantCoefficientsComplex_isStrictlyLE
    (L : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)) ℤ) (b : ℤ) (hLE : L.IsStrictlyLE b) :
    (overConstantCoefficientsComplex.{u, r} B X Λ L).IsStrictlyLE b := by
  have := hLE
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi =>
    Functor.map_isZero (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ)
      (L.isZero_of_isStrictlyLE b i hi)

omit [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [IsNoetherianRing Λ]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))]
  hSliceDerived
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) (ComplexShape.up ℤ)]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).obj M).Additive]
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive] in
/-- The terms of the image over the constant coefficient ring sheaf of a complex of constructible
flat sheaves of `Λ`-modules are flat, by
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`
degreewise. -/
public theorem isFlat_overConstantCoefficientsComplex_X
    (L : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)) ℤ)
    (hLterm : ∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (L.X i)) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) r, max (u + 1) r}
      (O := (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O)
      ((overConstantCoefficientsComplex.{u, r} B X Λ L).X i) :=
  isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf B X Λ
    (L.X i) (hLterm i)

variable [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]

omit hSliceDerived
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)] in
/-- **Tag 03TT, the Tor-amplitude refinement.** If `K` has constructible cohomology sheaves and
its image over the constant coefficient ringed site has Tor amplitude in `[a, b]`, then `K` is
represented by a complex of constructible sheaves of `Λ`-modules, flat over the constant
coefficient ring sheaf, concentrated in `[a, b]`.

Tor amplitude in `[a, b]` already bounds the cohomology of the image of `K` to `[a, b]`, and the
change of coefficients reflects vanishing, so the cohomology sheaves of `K` vanish outside
`[a, b]`; Tag 0960 then resolves `K` by a complex `L` of constructible flat sheaves vanishing
above `b`. The image of `L` is a bounded above complex of flat modules representing the image of
`K`, so Tag 08G0 makes `Coker(d^{a-1})` of it flat, and
`Stacks.EtaleCohomology.exists_flatConstructibleRepresentative_of_isFlat_cokernel` truncates. -/
public theorem exists_flatConstructibleRepresentative_of_hasTorAmplitude
    (T₀ : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsConstructible B X Λ K) (a b : ℤ) (hab : a ≤ b)
    (hamp : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude T₀
      ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r,
        r} B X Λ).mapDerivedCategory.obj K) a b) :
    ∃ F : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) r} Λ)) ℤ,
      F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
      (∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (F.X i)) ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) r,
        max (u + 1) r} (O := (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O)
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ).obj (F.X i))) ∧
      Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  have hvanish : ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) r} Λ)) n).obj K) := fun n hn =>
    isZero_homology_of_isZero_homology_moduleSheafOverConstantCoefficients.{u, max (u + 1) r, r, d}
      B X Λ K n
      (Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_of_hasTorAmplitude T₀ _ hamp
        (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
  obtain ⟨L, hLE, hLterm, ⟨e⟩⟩ :=
    exists_isStrictlyLE_constructibleFlatComplex_of_isConstructible B X Λ K hK b
      (fun i hi => hvanish i (Or.inr hi))
  have hGE : K.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    exact fun i hi => hvanish i (Or.inl hi)
  have hMamp : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude T₀
      (DerivedCategory.Q.obj (overConstantCoefficientsComplex.{u, r} B X Λ L)) a b :=
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.of_iso
      (((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r,
        r} B X Λ).mapDerivedCategoryFactors.{_, d, _, _, _, _}.app L).symm ≪≫
        (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r,
          r} B X Λ).mapDerivedCategory.mapIso e).symm hamp
  exact exists_flatConstructibleRepresentative_of_isFlat_cokernel.{u, max (u + 1) r, r} B X Λ
    (isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ) K a b L hLE hLterm hab e hGE
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitude T₀
      (overConstantCoefficientsComplex.{u, r} B X Λ L) a b
      ⟨b, overConstantCoefficientsComplex_isStrictlyLE.{u, r} B X Λ L b hLE⟩
      (isFlat_overConstantCoefficientsComplex_X.{u, r} B X Λ L hLterm) hMamp)

omit [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
    max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).obj M).Additive] in
/-- **Tag 03TT, the direction (1) ⟹ (2).** An object of `D(X_étale, Λ)` with constructible
cohomology sheaves whose image over the constant coefficient ringed site has locally finite Tor
dimension is represented by a finite complex of constructible flat sheaves of `Λ`-modules.

Quasi-compactness of `X` turns locally finite Tor dimension into a *finite* covering family of
the final object of the small étale site with one interval `[a, b]` valid on each member. The
cohomology sheaves of `K` vanish outside `[a, b]`, so Tag 0960 resolves `K` by a complex `L` of
constructible flat sheaves vanishing above `b`. On each member of the covering, Tag 08G0 makes
the cokernel of the restricted differential flat; restriction to a slice preserves cokernels, so
that cokernel is the restriction of `Coker(d^{a-1})`; and flatness is local on the site. -/
public theorem isRepresentedByFlatConstructibleComplex_of_locallyHasFiniteTorDimension
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsConstructible B X Λ K)
    (hT : Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) T
      ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r,
        r} B X Λ).mapDerivedCategory.obj K)) :
    IsRepresentedByFlatConstructibleComplex.{u, r} B X Λ K := by
  obtain ⟨ι, -, V, f, a₀, b₀, hcov, hamp₀⟩ := open Stacks.SheafOfModules in
    DerivedTensorProduct.exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension
      T _ hT (SmallEtale.final B X.obj X.property)
      (SmallEtale.isQuasiCompactObject_of_compactSpace B X.obj X.property
        (SmallEtale.final B X.obj X.property) (inferInstanceAs (CompactSpace X.obj)))
  have hamp : ∀ j, Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude (T (V j))
      ((RingedSite.derivedRestriction.{u + 1, u, max (u + 1) r, d}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) (V j)).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r,
          r} B X Λ).mapDerivedCategory.obj K)) (min a₀ b₀) (max a₀ b₀) := fun j =>
    (hamp₀ j).mono (min_le_left a₀ b₀) (le_max_right a₀ b₀)
  have hcovTop : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).J.CoversTop V :=
    ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).J.coversTop_iff_of_isTerminal
        (SmallEtale.final B X.obj X.property)
        (SmallEtale.finalIsTerminal B X.obj X.property) V).2
      ((Sieve.ofArrows_eq_ofObjects (SmallEtale.finalIsTerminal B X.obj X.property) V f) ▸ hcov)
  have hvanish := isZero_homology_of_coversTop_hasTorAmplitude.{_, u, max (u + 1) r, r, d}
    B X Λ T K hcovTop (min a₀ b₀) (max a₀ b₀) hamp
  obtain ⟨L, hLE, hLterm, ⟨e⟩⟩ :=
    exists_isStrictlyLE_constructibleFlatComplex_of_isConstructible B X Λ K hK (max a₀ b₀)
      (fun i hi => hvanish i (Or.inr hi))
  have hGE : K.IsGE (min a₀ b₀) := by
    rw [DerivedCategory.isGE_iff]
    exact fun i hi => hvanish i (Or.inl hi)
  have hMLE := overConstantCoefficientsComplex_isStrictlyLE.{u, r} B X Λ L (max a₀ b₀) hLE
  have hslice : ∀ j, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1,
      max (u + 1) r, max (u + 1) r}
      (O := ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over (V j)).O)
      ((cokernel ((overConstantCoefficientsComplex.{u, r} B X Λ L).d
        (min a₀ b₀ - 1) (min a₀ b₀))).over (V j)) := by
    intro j
    have hampj := Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.of_iso
      (restrictedConstantCoefficientComplexIso.{u, max (u + 1) r, r, d} B X Λ (V j) L K e).symm
      (hamp j)
    have hres := Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitude
      (T (V j)) (restrictedConstantCoefficientComplex.{u, max (u + 1) r, r} B X Λ (V j) L)
      (min a₀ b₀) (max a₀ b₀)
      ⟨max a₀ b₀, by
        rw [CochainComplex.isStrictlyLE_iff]
        exact fun i hi => isZero_restrictedConstantCoefficientComplex_X.{u, max (u + 1) r, r}
          B X Λ (V j) L i (L.isZero_of_isStrictlyLE (max a₀ b₀) i hi)⟩
      (fun i =>
        isFlat_over_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf.{u,
          max (u + 1) r, r} B X Λ (L.X i) (hLterm i) (V j))
      hampj
    exact Stacks.SheafOfModules.isFlat_of_iso_freeUniverse
      (X := (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over (V j))
      (PreservesCokernel.iso (SheafOfModules.overFunctor.{max (u + 1) r}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) r}
          (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) (V j))
        ((overConstantCoefficientsComplex.{u, r} B X Λ L).d (min a₀ b₀ - 1) (min a₀ b₀))).symm hres
  have hcok := Stacks.SheafOfModules.isFlat_of_ofArrows_of_isTerminal
    (X := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)
    (SmallEtale.finalIsTerminal B X.obj X.property) f hcov _ hslice
  obtain ⟨F, hFGE, hFLE, hFcon, hFflat, hFe⟩ :=
    exists_flatConstructibleRepresentative_of_isFlat_cokernel.{u, max (u + 1) r, r} B X Λ
      (isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ) K (min a₀ b₀) (max a₀ b₀) L
      hLE hLterm min_le_max e hGE hcok
  exact ⟨F, min a₀ b₀, max a₀ b₀, hFGE, hFLE, hFcon, hFflat, hFe⟩

/-! ### Tag 03TT -/

/-- **Stacks 03TT.** Let `Λ` be a Noetherian ring, let `X` be a quasi-compact and quasi-separated
scheme and let `K ∈ D(X_étale, Λ)`. The following are equivalent:

1. `K ∈ D_ctf(X_étale, Λ)`, that is, `K` has constructible cohomology sheaves and the image of
   `K` over the constant coefficient ringed site of Tag 03TR has locally finite Tor dimension in
   the sense of Tag 08FZ;
2. `K` is represented by a finite complex of constructible flat sheaves of `Λ`-modules.

In fact, if `K` has Tor amplitude in `[a, b]` then it can be represented by a complex
`F^a → ⋯ → F^b` with each `F^p` a constructible flat sheaf of `Λ`-modules.

Condition (1) is membership of
`Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory`, whose defining property is
exactly this conjunction; condition (2) is
`Stacks.EtaleCohomology.IsRepresentedByFlatConstructibleComplex`.

Condition (1) is stated **absolutely**: the derived tensor products against which finite Tor
dimension and Tor amplitude are measured are not parameters of the statement but the canonical
ones, `Stacks.SheafOfModules.canonicalDerivedTensorProduct` of Tag 06YU on the constant
coefficient ringed site and on each of its slices. Those exist at the universes this chapter
works in — the site is an `AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) r}`, whose
morphisms and whose sections lie in *different* universes — because the K-flat resolutions
Tag 06YU is built from resolve by flat modules supplied by a flat cover and so relate none of
the three universes of the site. The two directions and the refinement are proved above against
an arbitrary datum, which is the more general statement; the tag is carried here, where the
quantifier over the datum is gone and the equivalence is therefore not vacuous. -/
@[stacks 03TT, sga "4½ Rapport 4.6" "special case"]
public theorem isConstructibleFiniteTor_iff_isRepresentedByFlatConstructibleComplex
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) :
    ((IsConstructible B X Λ K ∧
        Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
          (X := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)
          (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProductGeneral.{u + 1, u,
            max (u + 1) r, d}
            ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
          ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r,
            r} B X Λ).mapDerivedCategory.obj K)) ↔
      IsRepresentedByFlatConstructibleComplex.{u, r} B X Λ K) ∧
    ∀ a b : ℤ, a ≤ b → IsConstructible B X Λ K →
      Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
        (Stacks.SheafOfModules.canonicalDerivedTensorProductGeneral.{u + 1, u, max (u + 1) r, d}
          (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r,
          r} B X Λ).mapDerivedCategory.obj K) a b →
      ∃ F : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) r} Λ)) ℤ,
        F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
        (∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (F.X i)) ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) r,
          max (u + 1) r} (O := (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O)
          ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r,
            r} B X Λ).obj (F.X i))) ∧
        Nonempty (DerivedCategory.Q.obj F ≅ K) :=
  ⟨⟨fun h => isRepresentedByFlatConstructibleComplex_of_locallyHasFiniteTorDimension.{u, r, d}
      B X Λ _ K h.1 h.2,
    fun h => ⟨isConstructible_of_isRepresentedByFlatConstructibleComplex B X Λ K h,
      locallyHasFiniteTorDimension_of_isRepresentedByFlatConstructibleComplex.{u, r, d}
        B X Λ _ K h⟩⟩,
    fun a b hab hK hamp => exists_flatConstructibleRepresentative_of_hasTorAmplitude.{u, r, d}
      B X Λ _ K hK a b hab hamp⟩

end Stacks.EtaleCohomology

end
