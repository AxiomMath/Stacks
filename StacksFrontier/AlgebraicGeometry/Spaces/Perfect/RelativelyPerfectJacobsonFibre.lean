module

public import Mathlib.RingTheory.Jacobson.Ideal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Relative perfectness over a ring lifts from the fibre over a Jacobson-radical ideal

Let `(R, I)` be a pair consisting of a ring and an ideal contained in the Jacobson radical of
`R`, set `𝒮 = Spec R` and `𝒮₀ = Spec (R/I)`, and let `X` be an algebraic space over `R` whose
structure morphism `f : X ⟶ 𝒮` is proper, flat and of finite presentation. Write
`X₀ = 𝒮₀ ×_𝒮 X`. Stacks 0DL5 says that a pseudo-coherent object `E` of `D(𝒪_X)` whose derived
restriction `E₀` to `X₀` is `𝒮₀`-perfect is itself `𝒮`-perfect.

Relative perfectness is `AlgebraicGeometry.Space.IsPerfectRelativeTo` of Stacks 0DKN: a
conjunction of pseudo-coherence on the small étale ringed site and locally finite Tor dimension
over `f⁻¹𝒪_𝒮`. Pseudo-coherence of `E` is a hypothesis of the source, so the first clause of the
conclusion is immediate; everything in the source's proof concerns the second clause.

## What is proved and what is carried

The source's proof opens by producing, for every point `x` of `|X|`, a specialization
`x ⤳ x₀` with `x₀` in `|X₀|`: the map `|X| → |𝒮|` is closed because `f` is proper, and because
`I` lies in the Jacobson radical every nonempty closed subset of `|𝒮| = Spec R` meets the closed
subscheme `|𝒮₀|`, which is the zero locus of `I`. That step is proved here, over an arbitrary
closed morphism of algebraic spaces and then for `(R, I)`:

* `AlgebraicGeometry.Space.exists_mem_inter_zeroLocus_of_isClosed`: the ring-theoretic half —
  a nonempty closed subset of `Spec R` meets the zero locus of any ideal inside the Jacobson
  radical, because the subset is the zero locus of a proper ideal and a proper ideal lies in a
  maximal one.
* `AlgebraicGeometry.Space.closedFibre_meets_isClosed_of_jacobson`: the same statement read on
  `|𝒮|` through an identification of it with `Spec R` under which `|𝒮₀|` is the zero locus
  of `I`.
* `AlgebraicGeometry.Space.exists_specializes_mem_range_of_isClosedMorphism`: the
  specialization step, from a closed `|X| → |𝒮|` and that property of the closed fibre.

The remaining content of the source's proof — the bound on the Tor amplitude of the stalks of
`E` over `R` in an interval `[a - d, b]` read off from an affine étale chart closed in `𝐀^d_𝒮`,
by way of the fibrewise criterion of Stacks 0DJH, and its conversion into locally finite Tor
dimension through the computation of Tor amplitude at stalks of Stacks 0DJJ and 04K5 — is
carried as the single named hypothesis
`AlgebraicGeometry.Space.LocallyFiniteTorDimensionFromClosedFibre`, in the shape of
`AlgebraicGeometry.Space.BottomRankStratum.HasDerivedModulePullbacks`. It cannot be discharged
here: the source's translation of `E|_U` into a pseudo-coherent object of `D(A)` is Stacks 071Q
together with the agreement of the étale and Zariski notions of pseudo-coherence, which this
development has only for the small étale site of a scheme standing on its own and not for an
étale chart of an algebraic space, and the étale local rings of an algebraic space live one
universe above the rings of the charts, so the strict henselization step of the source has no
counterpart in `AlgebraicGeometry.Space.IsPerfectRelativeTo`, whose Tor clause is measured on
the slices of the small étale site rather than at geometric points.

## Implementation notes

`AlgebraicGeometry.Space.exists_mem_inter_zeroLocus_of_isClosed` repeats the argument of the
private `exists_mem_of_isClosed_of_jacobson_le` of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativelyPerfectJacobsonSpecialization.lean`, which is
the scheme-level form of this step (Stacks 0DJZ); the two should be unified once that one is
exported. The pair `(R, I)` enters the geometric statements exactly where the source uses it:
through a homeomorphism `|𝒮| ≃ₜ Spec R` and the identification of the image of `|𝒮₀| → |𝒮|`
with the zero locus of `I`, the latter being `range_specMap_quotientMk_base` of that same file.

The instance context is the one of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/Relative.lean`, doubled for the two structure
morphisms `f` and `f₀`, since the hypothesis and the conclusion are relative perfectness over
`𝒮₀` and over `𝒮`; the derived category of `𝒪_X`-modules is pinned at
`CategoryTheory.HasDerivedCategory.standard`, the model
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` is stated at.

## References

* [Stacks Project, Lemma 76.54.5 (0DL5)](https://stacks.math.columbia.edu/tag/0DL5)
* [Stacks Project, Definition 76.52.1 (0DKN)](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Lemma 15.85.9 (0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 21.46.10 (0DJJ)](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Theorem 66.19.12 (04K5)](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Lemma 75.4.2 (071Q)](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Definition 73.3.1 (03HI)](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Definition 74.9.1 (03ZM)](https://stacks.math.columbia.edu/tag/03ZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Space

universe u e

/-! ### A nonempty closed subset of `Spec R` meets the zero locus of a Jacobson-radical ideal -/

/-- A nonempty closed subset of `Spec R` meets the zero locus of an ideal `I` contained in the
Jacobson radical of `R`: the subset is the zero locus of an ideal which is proper because the
subset is nonempty, that ideal lies in a maximal ideal, and the Jacobson radical is the
intersection of the maximal ideals. -/
theorem exists_mem_inter_zeroLocus_of_isClosed {R : Type u} [CommRing R]
    {Z : Set (PrimeSpectrum R)} (hZ : IsClosed Z) (hne : Z.Nonempty)
    {I : Ideal R} (hI : I ≤ (⊥ : Ideal R).jacobson) :
    (Z ∩ PrimeSpectrum.zeroLocus (I : Set R)).Nonempty := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  obtain ⟨q, hq⟩ := hne
  have hqJ : (J : Set R) ⊆ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp (hJ ▸ hq)
  have hJne : J ≠ ⊤ := fun h => q.isPrime.ne_top (top_le_iff.mp (h ▸ hqJ))
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJne
  have hIm : I ≤ m := hI.trans (by rw [Ideal.jacobson]; exact sInf_le ⟨bot_le, hm⟩)
  exact ⟨⟨m, hm.isPrime⟩, hJ ▸ (PrimeSpectrum.mem_zeroLocus _ _).mpr hJm,
    (PrimeSpectrum.mem_zeroLocus _ _).mpr hIm⟩

/-! ### The specialization step of Stacks 0DL5 -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X₀ 𝒮 𝒮₀ : AlgebraicSpaces B S hS}

attribute [local instance] pointTopology

/-- With `|𝒮|` identified with `Spec R` in such a way that the image of `|𝒮₀| → |𝒮|` is the
zero locus of an ideal `I` inside the Jacobson radical of `R`, every nonempty closed subset of
`|𝒮|` meets that image. -/
theorem closedFibre_meets_isClosed_of_jacobson (j : 𝒮₀ ⟶ 𝒮) {R : Type u} [CommRing R]
    {I : Ideal R} (hI : I ≤ (⊥ : Ideal R).jacobson)
    (eR : points B S hS 𝒮.1 ≃ₜ PrimeSpectrum R)
    (hj : Set.range (pointsMap B S hS 𝒮₀.1 j.hom) =
      eR ⁻¹' PrimeSpectrum.zeroLocus (I : Set R))
    (Z : Set (points B S hS 𝒮.1)) (hZ : IsClosed Z) (hne : Z.Nonempty) :
    (Z ∩ Set.range (pointsMap B S hS 𝒮₀.1 j.hom)).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨p, hpZ, hpI⟩ := exists_mem_inter_zeroLocus_of_isClosed
    (Z := eR.symm ⁻¹' Z) (hZ.preimage eR.symm.continuous) ⟨eR z, by simpa using hz⟩ hI
  refine ⟨eR.symm p, hpZ, ?_⟩
  rw [hj]
  simpa using hpI

/-- **The specialization step of Stacks 0DL5.** If the map on points of `f : X ⟶ 𝒮` is closed
and every nonempty closed subset of `|𝒮|` meets the image of `|𝒮₀| → |𝒮|`, then every point of
`|X|` specializes to a point whose image in `|𝒮|` lies in that image.

The closure of the given point is closed, so its image in `|𝒮|` is closed; it is nonempty, so
it meets the image of `|𝒮₀|`, and any preimage in the closure of the point so obtained is the
required specialization. -/
theorem exists_specializes_mem_range_of_isClosedMorphism (f : X ⟶ 𝒮) (j : 𝒮₀ ⟶ 𝒮)
    (hf : IsClosedMorphism B S hS f.hom)
    (hmeet : ∀ Z : Set (points B S hS 𝒮.1), IsClosed Z → Z.Nonempty →
      (Z ∩ Set.range (pointsMap B S hS 𝒮₀.1 j.hom)).Nonempty)
    (x : points B S hS X.1) :
    ∃ x₀ : points B S hS X.1, x ⤳ x₀ ∧
      pointsMap B S hS X.1 f.hom x₀ ∈ Set.range (pointsMap B S hS 𝒮₀.1 j.hom) := by
  obtain ⟨y, hyZ, hyr⟩ := hmeet (pointsMap B S hS X.1 f.hom '' closure {x})
    (hf _ isClosed_closure) ⟨_, x, subset_closure rfl, rfl⟩
  obtain ⟨x₀, hx₀, hfx₀⟩ := hyZ
  exact ⟨x₀, specializes_iff_mem_closure.mpr hx₀, hfx₀ ▸ hyr⟩

/-! ### Stacks 0DL5 -/

attribute [local instance] HasDerivedCategory.standard

variable (f : X ⟶ 𝒮) (f₀ : X₀ ⟶ 𝒮₀)
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f₀))]

variable
    [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      HasSheafify ((smallEtaleRingedSite B S hS X.1 X.2).J.over U) AddCommGrpCat.{u}]
    [∀ U : (smallEtaleRingedSite B S hS X₀.1 X₀.2).C,
      HasSheafify ((smallEtaleRingedSite B S hS X₀.1 X₀.2).J.over U) AddCommGrpCat.{u}]

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]
    [∀ U : (inverseImageRingedSite B S hS f₀).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f₀).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C) M,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).obj M).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C)
        (K L : CochainComplex
          (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor
          ((inverseImageRingedSite B S hS f).over U).O) (ComplexShape.up ℤ)]
    [∀ U : (inverseImageRingedSite B S hS f₀).C,
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f₀).over U).O).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f₀).C) M,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f₀).over U).O).obj M).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f₀).C)
        (K L : CochainComplex
          (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f₀).over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor
          ((inverseImageRingedSite B S hS f₀).over U).O) (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

/-- **The Tor clause of Stacks 0DL5.** Once every point of `|X|` specializes into the closed
fibre, a pseudo-coherent `E` whose derived restriction to `X₀` is `𝒮₀`-perfect locally has
finite Tor dimension over `f⁻¹𝒪_𝒮`.

This is everything the source's proof does after its specialization step: bounding the Tor
amplitude of the stalks of `E` over `R` by the fibrewise criterion of Stacks 0DJH on an affine
étale chart closed in `𝐀^d_𝒮`, and reading locally finite Tor dimension off those stalks by
Stacks 0DJJ and 04K5. -/
def LocallyFiniteTorDimensionFromClosedFibre (i : X₀ ⟶ X) (j : 𝒮₀ ⟶ 𝒮)
    [(smallEtaleModulePullbackOnHomotopy B S hS i).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS X)]
    (hflat₀ : IsFlat B S hS f₀.hom) (hlfp₀ : IsLocallyOfFinitePresentation B S hS f₀.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (T₀ : ∀ U : (inverseImageRingedSite B S hS f₀).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f₀).over U)) : Prop :=
  ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E →
      IsPerfectRelativeTo B S hS f₀ hflat₀ hlfp₀ T₀
        ((smallEtaleDerivedModulePullback B S hS i).obj E) →
      (∀ x : points B S hS X.1, ∃ x₀ : points B S hS X.1, x ⤳ x₀ ∧
        pointsMap B S hS X.1 f.hom x₀ ∈ Set.range (pointsMap B S hS 𝒮₀.1 j.hom)) →
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension T
        ((derivedScalarRestriction B S hS f).obj E)

/-- **Stacks 0DL5.** Let `(R, I)` be a ring with an ideal contained in its Jacobson radical, let
`𝒮 = Spec R` and `𝒮₀ = Spec (R/I)`, let `f : X ⟶ 𝒮` be a proper, flat, locally finitely
presented morphism of algebraic spaces and let `X₀ = 𝒮₀ ×_𝒮 X`. A pseudo-coherent object `E` of
`D(𝒪_X)` whose derived restriction to `X₀` is `𝒮₀`-perfect is `𝒮`-perfect.

The pseudo-coherence clause of the conclusion is the hypothesis on `E`. For the Tor clause,
properness makes `|X| → |𝒮|` closed and the ideal `I` lying in the Jacobson radical makes every
nonempty closed subset of `|𝒮|` meet `|𝒮₀|`, so every point of `|X|` specializes into the closed
fibre; from there the bound is `hTor`. -/
@[stacks 0DL5 "the pseudo-coherence clause and the specialization step; Tor clause carried"]
theorem isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre (i : X₀ ⟶ X) (j : 𝒮₀ ⟶ 𝒮)
    [(smallEtaleModulePullbackOnHomotopy B S hS i).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS X)]
    (hflat : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (hflat₀ : IsFlat B S hS f₀.hom) (hlfp₀ : IsLocallyOfFinitePresentation B S hS f₀.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (T₀ : ∀ U : (inverseImageRingedSite B S hS f₀).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f₀).over U))
    {R : Type u} [CommRing R] {I : Ideal R} (hI : I ≤ (⊥ : Ideal R).jacobson)
    (eR : points B S hS 𝒮.1 ≃ₜ PrimeSpectrum R)
    (hj : Set.range (pointsMap B S hS 𝒮₀.1 j.hom) =
      eR ⁻¹' PrimeSpectrum.zeroLocus (I : Set R))
    (hproper : IsProper B S hS f.hom) (_hpb : IsPullback i f₀ f j)
    (hTor : LocallyFiniteTorDimensionFromClosedFibre B S hS f f₀ i j hflat₀ hlfp₀ T T₀)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (hE₀ : IsPerfectRelativeTo B S hS f₀ hflat₀ hlfp₀ T₀
      ((smallEtaleDerivedModulePullback B S hS i).obj E)) :
    IsPerfectRelativeTo B S hS f hflat hlfp T E :=
  ⟨hE, hTor E hE hE₀ fun x =>
    exists_specializes_mem_range_of_isClosedMorphism B S hS f j
      (isClosed_of_universallyClosed B S hS 𝒮.2 f.hom hproper.2.2)
      (closedFibre_meets_isClosed_of_jacobson B S hS j hI eR hj) x⟩

end AlgebraicGeometry.Space

end
