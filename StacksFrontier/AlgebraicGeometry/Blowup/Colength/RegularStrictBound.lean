module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.InverseImageSections
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.PositiveOrder
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.StrictBound
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafComapGeneration
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Length
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.PicardUFD.AffineScheme
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.RegularLocalBlowupTwists
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality

/-!
# The strict length inequality of Stacks Tag 0AGT for a regular local surface

Let `(A, 𝔪)` be a regular local ring of dimension two, let `f : X ⟶ S = Spec A` be the blowing up
of `A` in `𝔪`, with exceptional divisor `E`, let `𝔪ⁿ ⊆ I ⊆ 𝔪` be an ideal, let `d` be the largest
integer with `I𝒪_X ⊆ 𝒪_X(-dE)`, and let `ℐ' = I𝒪_X(dE)`, the sheaf of ideals with
`𝒪_X(-dE) · ℐ' = I𝒪_X`. This file proves, with no further hypothesis,

`length_A (A / I) > length_A Γ(X, 𝒪_X / ℐ')`,

the strict inequality of [Stacks, Tag 0AGT].

## Main results

* `AlgebraicGeometry.length_globalSections_lt_length_quotient_blowUp` — the strict inequality.
* `AlgebraicGeometry.isZero_hgroup_one_idealSheaf_comap_blowUp` — `H¹(X, I𝒪_X) = 0`, the
  first step of the source's proof.
* `AlgebraicGeometry.isZero_hgroup_one_blowUp_of_generatingSections` — part (3) of
  [Stacks, Tag 0AGS] (globally generated case) read on `AlgebraicGeometry.blowUp`.
* `Stacks.Blowup.Colength.exists_injective_globalSections_negativeTwist_restrict` — for a
  sheaf of ideals `J'` supported at finitely many closed points and an effective Cartier divisor
  `D`, the sections of `𝒪_X / J'` inject into those of the twist `𝒪_X(-D)|_{V(J')}`.

## The argument

The source's, through the length-theoretic lemma
`Stacks.Blowup.Colength.length_globalSections_lt_length_quotient` of
`StacksFrontier/AlgebraicGeometry/Blowup/Colength/StrictBound.lean`, applied to the divisor
`𝒪_X(-dE) = E ^ d` and the residual ideal `J' = ℐ'`. Its four inputs are discharged here.

* `H¹(X, I𝒪_X) = 0`. The module-level ideal sheaf of `I𝒪_X` is globally generated, being the
  inverse image of an ideal sheaf on an affine base
  (`Stacks.Divisors.nonempty_generatingSections_idealSheaf_comap`), and quasi-coherent
  ([Stacks, Tag 01IN]), so part (3) of [Stacks, Tag 0AGS] applies. That part is stated on the
  affine model `Stacks.Blowup.blowUpSpec 𝔪 = Proj (⨁ₙ 𝔪ⁿ)` of the blowup; it is carried to
  `AlgebraicGeometry.blowUp` along the isomorphism over `Spec A`
  (`Stacks.Blowup.nonempty_over_iso_blowUpToBase`): cohomology is invariant under an isomorphism
  of schemes (`Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff`), and the inverse image of
  a quasi-coherent globally generated module is quasi-coherent and globally generated.
* `A ⟶ Γ(X, 𝒪_X)` is surjective. The blowup is a modification of `Spec A`
  (`AlgebraicGeometry.isModification_blowUpToBase_maximalIdeal`) and `A` is a normal domain, so
  this map is an isomorphism (`AlgebraicGeometry.IsModification.isIso_appTop`, [Stacks,
  Tag 0AY8]). This is the case `n = 0` of part (4) of [Stacks, Tag 0AGS], proved by a different
  route.
* `I` dies in `Γ(V(I𝒪_X), 𝒪)`, because `I𝒪_X` is the inverse image of `I`
  (`AlgebraicGeometry.Scheme.IdealSheafData.appTop_subschemeι_eq_zero_of_mem`).
* `Γ(V(ℐ'), 𝒪)` injects into the sections of `𝒪_X(-dE)|_{V(ℐ')}`: this is the source's "an
  invertible module over a local ring is trivial". The support of `ℐ'` is a finite set of closed
  points (`AlgebraicGeometry.exists_finite_isClosed_support_of_maximal_order_blowUp`, the
  residual ideal being unique by cancellation of the effective Cartier divisor `E ^ d`,
  `Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor`). So `V(ℐ')` is a finite
  discrete scheme, hence affine, and its ring of functions has finitely many maximal ideals,
  hence trivial Picard group; the restriction of the invertible `𝒪_X(-dE)` to it is therefore
  trivial (`Stacks.PicardUFD.nonempty_linearEquiv_appTop_of_isInvertible_of_isAffine`) and its
  global sections are free of rank one over `Γ(V(ℐ'), 𝒪)`.

The remaining hypotheses of the lemma are elementary: `E ^ d` is an effective Cartier divisor
([Stacks, Tag 02OS] and its powers), it is not the unit ideal because `d > 0`
(`Stacks.Blowup.Colength.pos_order_of_le_center`) and the exceptional divisor is nonempty, and
`A / I` has finite length because `𝔪ⁿ ⊆ I`.

## Implementation notes

The blowup is `AlgebraicGeometry.blowUp ℐ` for the ideal sheaf `ℐ` of the closed point, in the
spelling of `StacksFrontier/AlgebraicGeometry/Blowup/Colength/ExceptionalCurve.lean` and
`StacksFrontier/AlgebraicGeometry/Blowup/Colength/PositiveOrder.lean`; `I𝒪_X` is the inverse image
along `blowUpToBase ℐ` of the ideal sheaf generated by `I`, and `𝒪_X(-dE)` is the `d`-th power
of `AlgebraicGeometry.exceptionalIdeal ℐ`. The ideal `ℐ'` is quantified over all sheaves of
ideals with `E ^ d · ℐ' = I𝒪_X`; there is exactly one. The `A`-algebra structure on
`Γ(V(ℐ'), 𝒪)` is the one induced by the structure morphism, in the spelling
`Stacks.Blowup.Colength.length_globalSections_ge_sum_length_stalkQuotient` uses, so that the
two inequalities of the tag are about the same `A`-module.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Blowup.Colength

/-! ### Sections over a residual subscheme supported at finitely many closed points -/

section FiniteSupport

variable {X : Scheme.{u}} (J' : X.IdealSheafData) (T : Finset X)
  (hT : (J'.support : Set X) = (T : Set X)) (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
include hT hclosed

/-- A closed subscheme whose support is a finite set of closed points is a finite discrete
space. -/
private theorem finite_and_discreteTopology_subscheme :
    Finite J'.subscheme ∧ DiscreteTopology J'.subscheme := by
  have hinj : Function.Injective (fun z : J'.subscheme => (J'.subschemeι z : X)) :=
    (inferInstance : IsClosedImmersion J'.subschemeι).isClosedEmbedding.injective
  have hmaps : ∀ z : J'.subscheme, J'.subschemeι z ∈ (T : Set X) := fun z => by
    rw [← hT, ← J'.range_subschemeι]
    exact ⟨z, rfl⟩
  have : Finite J'.subscheme := Finite.of_injective
    (fun z : J'.subscheme => (⟨J'.subschemeι z, hmaps z⟩ : (T : Set X)))
    (fun z w h => hinj (congrArg (fun q : (T : Set X) => (q : X)) h))
  have hclosedZ : ∀ z : J'.subscheme, IsClosed ({z} : Set J'.subscheme) := by
    intro z
    have hpre : J'.subschemeι ⁻¹' ({J'.subschemeι z} : Set X) = ({z} : Set J'.subscheme) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact hinj.eq_iff
    rw [← hpre]
    exact (hclosed _ (hmaps z)).preimage J'.subschemeι.continuous
  exact ⟨inferInstance, DiscreteTopology.of_finite_of_isClosed_singleton hclosedZ⟩

/-- **A closed subscheme supported at finitely many closed points is affine**, being a finite
discrete scheme. -/
theorem isAffine_subscheme_of_support_eq_finset : IsAffine J'.subscheme := by
  obtain ⟨_, _⟩ := finite_and_discreteTopology_subscheme J' T hT hclosed
  infer_instance

/-- **A closed subscheme supported at finitely many closed points has a semi-local ring of
functions**: its ring of global functions has finitely many maximal ideals, the prime spectrum
being homeomorphic to the finite subscheme. -/
theorem finite_maximalSpectrum_subscheme_of_support_eq_finset :
    Finite (MaximalSpectrum Γ(J'.subscheme, ⊤)) := by
  obtain ⟨_, _⟩ := finite_and_discreteTopology_subscheme J' T hT hclosed
  have := isAffine_subscheme_of_support_eq_finset J' T hT hclosed
  have : Finite (PrimeSpectrum Γ(J'.subscheme, ⊤)) :=
    Finite.of_equiv _ J'.subscheme.isoSpec.hom.homeomorph.toEquiv
  exact Finite.of_injective _ MaximalSpectrum.toPrimeSpectrum_injective

/-- **The sections of a residual subscheme supported at finitely many closed points inject into
those of an invertible twist restricted to it.** Let `f : X ⟶ Spec A`, let `D` be an effective
Cartier divisor on `X` and let `J'` be a sheaf of ideals whose support is a finite set of closed
points. Then there is an injective `A`-linear map

`Γ(V(J'), 𝒪) ⟶ Γ(X, 𝒪_X(-D)|_{V(J')})`.

This is the closing step of the proof of [Stacks, Tag 0AGT], "an invertible module over a local
ring is trivial": `V(J')` is affine with a semi-local ring of functions, whose Picard group is
trivial, so the restriction of the invertible `𝒪_X(-D)` to it has global sections free of rank
one (`Stacks.PicardUFD.nonempty_linearEquiv_appTop_of_isInvertible_of_isAffine`). The
`A`-module structures are those induced by `f`, as in
`Stacks.Blowup.Colength.length_globalSections_lt_length_quotient`. -/
theorem exists_injective_globalSections_negativeTwist_restrict {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    letI : Algebra A Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra A Γ(J'.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (J'.subschemeι ≫ f).appTop).hom.toAlgebra
    letI : Module A Γ((Scheme.Modules.pushforward J'.subschemeι).obj
        ((Scheme.Modules.pullback J'.subschemeι).obj (Stacks.Divisors.negativeTwist D)),
        (⊤ : X.Opens)) :=
      Module.compHom _ (algebraMap A Γ(X, ⊤))
    ∃ t : Γ(J'.subscheme, ⊤) →ₗ[A] Γ((Scheme.Modules.pushforward J'.subschemeι).obj
        ((Scheme.Modules.pullback J'.subschemeι).obj (Stacks.Divisors.negativeTwist D)),
        (⊤ : X.Opens)),
      Function.Injective t := by
  let : Algebra A Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
  let : Algebra A Γ(J'.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (J'.subschemeι ≫ f).appTop).hom.toAlgebra
  let : Module A Γ((Scheme.Modules.pushforward J'.subschemeι).obj
        ((Scheme.Modules.pullback J'.subschemeι).obj (Stacks.Divisors.negativeTwist D)),
        (⊤ : X.Opens)) :=
    Module.compHom _ (algebraMap A Γ(X, ⊤))
  have := isAffine_subscheme_of_support_eq_finset J' T hT hclosed
  have := finite_maximalSpectrum_subscheme_of_support_eq_finset J' T hT hclosed
  have := hD
  have := Stacks.Divisors.stacksIsInvertible_negativeTwist D
  have : Stacks.SheafOfModules.IsInvertible J'.subscheme.presheaf J'.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback J'.subschemeι).obj (Stacks.Divisors.negativeTwist D)) :=
    RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme J'.subschemeι _
  obtain ⟨e⟩ := Stacks.PicardUFD.nonempty_linearEquiv_appTop_of_isInvertible_of_isAffine
    J'.subscheme ((Scheme.Modules.pullback J'.subschemeι).obj (Stacks.Divisors.negativeTwist D))
  -- the `A`-action on the twist is that of `Γ(X, 𝒪_X)` through `f`, which acts on the sections
  -- over `V(J')` through restriction, so `e.symm` is `A`-linear by definition.
  refine ⟨
    { toFun := fun s => e.symm s
      map_add' := fun s s' => e.symm.map_add s s'
      map_smul' := fun a s => e.symm.map_smul (algebraMap A Γ(J'.subscheme, ⊤) a) s },
    fun s s' h => e.symm.injective h⟩

end FiniteSupport

end Stacks.Blowup.Colength

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

/-! ### `H¹(X, I𝒪_X) = 0` -/

/-- **Stacks Project, Tag 0AGS part (3), the globally generated case, on
`AlgebraicGeometry.blowUp`.** Let `(A, 𝔪)` be a regular local ring of dimension two and let
`X = blowUp ℐ` be the blowup of `Spec A` in the ideal sheaf `ℐ` of its closed point. If a
quasi-coherent `𝒪_X`-module `ℱ` is globally generated then `H¹(X, ℱ) = 0`.

This is `Stacks.Blowup.isZero_hgroup_one_of_generatingSections_maximalIdeal`, stated on the
affine model `Stacks.Blowup.blowUpSpec 𝔪`, carried along the isomorphism of the two models over
`Spec A`: the inverse image of `ℱ` is quasi-coherent and globally generated, and cohomology is
invariant under an isomorphism of schemes. No `@[stacks]` registration: the tag's part (3) is
registered on the affine model. -/
theorem isZero_hgroup_one_blowUp_of_generatingSections (hdim : ringKrullDim A = 2)
    (F : (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))).Modules)
    [F.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections F) :
    IsZero (Hgroup (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))).ringCatSheaf
      ⊤ 1 F) := by
  obtain ⟨φ⟩ := Stacks.Blowup.nonempty_over_iso_blowUpToBase A (IsLocalRing.maximalIdeal A)
  let e : Stacks.Blowup.blowUpSpec (IsLocalRing.maximalIdeal A) ≅
      blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))) :=
    (Over.forget _).mapIso φ
  refine (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff e F 1).1 ?_
  have : IsOpenImmersion e.hom := IsOpenImmersion.of_isIso e.hom
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion
    e.hom F
  exact Stacks.Blowup.isZero_hgroup_one_of_generatingSections_maximalIdeal A hdim _
    (Stacks.SheafOfModules.modulePullbackGeneratingSections e.hom.toLRSHom.toShHom F σ)

/-- The module-level ideal sheaf of a sheaf of ideals on the blowup of a regular local surface
which is globally generated has vanishing first cohomology. -/
private theorem isZero_hgroup_one_kernel_of_generatingSections (hdim : ringKrullDim A = 2)
    (K : (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))).IdealSheafData)
    (σ : (Stacks.Divisors.Eta.idealSheaf K).GeneratingSections) :
    IsZero (Hgroup (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))).ringCatSheaf ⊤ 1
      (kernel (SheafOfModules.unitToPushforwardObjUnit K.subschemeι.toRingCatSheafHom))) := by
  have : Stacks.ClosedImmersion.IsClosedImmersion K.subschemeι.toLRSHom.toShHom :=
    ((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae K.subschemeι).out 1 6).mp
      (inferInstance : IsClosedImmersion K.subschemeι)
  have hqc := Stacks.ClosedImmersion.isQuasicoherent_idealSheaf _ _ K.subschemeι.toLRSHom
  -- the quasi-coherence is handed over positionally: the two spellings of the sheaf of rings
  -- give `IsQuasicoherent` two instance keys.
  exact @isZero_hgroup_one_blowUp_of_generatingSections A _ _ hdim _ hqc σ

/-- **`H¹(X, I𝒪_X) = 0`.** Let `(A, 𝔪)` be a regular local ring of dimension two, let `X` be the
blowup of `Spec A` in its closed point and let `I ⊆ A` be an ideal. Then the first cohomology of
the ideal sheaf `I𝒪_X` vanishes. This is the first step of the proof of [Stacks, Tag 0AGT]:
`I𝒪_X` is globally generated, so part (3) of [Stacks, Tag 0AGS] applies. -/
theorem isZero_hgroup_one_idealSheaf_comap_blowUp (hdim : ringKrullDim A = 2) (I : Ideal A) :
    IsZero (Hgroup (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))).ringCatSheaf ⊤ 1
      (kernel (SheafOfModules.unitToPushforwardObjUnit
        ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap
          (blowUpToBase (Scheme.IdealSheafData.ofIdealTop (Ideal.map
            (Scheme.ΓSpecIso (.of A)).inv.hom
              (IsLocalRing.maximalIdeal A))))).subschemeι.toRingCatSheafHom))) :=
  (Stacks.Divisors.nonempty_generatingSections_idealSheaf_comap _ _).elim
    (isZero_hgroup_one_kernel_of_generatingSections A hdim _)

/-! ### The strict inequality -/

/-- **Stacks Project, Tag 0AGT, the strict length inequality.** Let `(A, 𝔪)` be a regular local
ring of dimension two and let `X = blowUp ℐ ⟶ Spec A` be the blowing up of `A` in `𝔪`, `ℐ` being
the ideal sheaf of the closed point, with exceptional divisor `E = exceptionalIdeal ℐ`. Let
`𝔪ⁿ ⊆ I ⊆ 𝔪` be an ideal, let `d` be the largest integer with `I𝒪_X ⊆ 𝒪_X(-dE) = E ^ d`, and let
`ℐ'` be the sheaf of ideals with `E ^ d · ℐ' = I𝒪_X`, that is `ℐ' = I𝒪_X(dE)`. Then

`length_A Γ(X, 𝒪_X / ℐ') < length_A (A / I)`,

`Γ(X, 𝒪_X / ℐ')` being the ring of functions of the closed subscheme `V(ℐ')`, an `A`-algebra
through `X ⟶ Spec A`.

Unregistered: the tag is registered on the theorem stating all of its assertions, which
consumes this one. -/
theorem length_globalSections_lt_length_quotient_blowUp
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (ℐ : (Spec (CommRingCat.of A)).IdealSheafData)
    (hℐ : ℐ = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))
    (I : Ideal A) (n : ℕ) (hnI : IsLocalRing.maximalIdeal A ^ n ≤ I)
    (hIm : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (hd : (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap
        (blowUpToBase ℐ) ≤ exceptionalIdeal ℐ ^ d)
    (hmax : ∀ e : ℕ, (Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap (blowUpToBase ℐ) ≤
        exceptionalIdeal ℐ ^ e → e ≤ d)
    (J' : (blowUp ℐ).IdealSheafData)
    (hJ' : exceptionalIdeal ℐ ^ d * J' = (Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap (blowUpToBase ℐ)) :
    letI : Algebra A Γ(J'.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (J'.subschemeι ≫ blowUpToBase ℐ).appTop).hom.toAlgebra
    Module.length A Γ(J'.subscheme, ⊤) < Module.length A (A ⧸ I) := by
  have hℐr : ℐ = (Stacks.Blowup.residuePoint A).ker :=
    hℐ.trans (ker_residuePoint_eq_ofIdealTop_map A).symm
  have hEC : Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalIdeal ℐ ^ d) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal ℐ) d
  have hmulJ : J' * exceptionalIdeal ℐ ^ d = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap (blowUpToBase ℐ) := by
    rw [mul_comm]; exact hJ'
  have hmono : ∀ {K L : Ideal A}, K ≤ L →
      Scheme.IdealSheafData.ofIdealTop (K.map (Scheme.ΓSpecIso (.of A)).inv.hom) ≤
        Scheme.IdealSheafData.ofIdealTop (L.map (Scheme.ΓSpecIso (.of A)).inv.hom) :=
    fun h => Scheme.IdealSheafData.equivOfIsAffine.symm.toOrderIso.monotone (Ideal.map_mono h)
  have hJℐ : Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (.of A)).inv.hom) ≤ ℐ :=
    hℐ ▸ hmono hIm
  have hdpos : 0 < d := Stacks.Blowup.Colength.pos_order_of_le_center ℐ _ d hJℐ ⟨hd, hmax⟩
  have hEtop : exceptionalIdeal ℐ ^ d ≠ ⊤ := by
    intro htop
    have hsupp := congrArg Scheme.IdealSheafData.support htop
    rw [Scheme.IdealSheafData.support_pow _ d hdpos.ne', Scheme.IdealSheafData.support_top] at hsupp
    have hne := (isIrreducible_support_exceptionalIdeal A ℐ hdim hℐr).nonempty
    rw [hsupp] at hne
    exact hne.ne_empty rfl
  have hn : n ≠ 0 := by
    rintro rfl
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (top_le_iff.mp (by simpa using hnI.trans hIm))
  have hfin : Module.length A (A ⧸ I) ≠ ⊤ := by
    refine Stacks.PuncturedSpectrum.length_ne_top_of_maximalIdeal_pow_smul_eq_zero A (A ⧸ I) hn ?_
    intro a ha x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact I.mul_mem_right b (hnI ha)
  have hH1 : IsZero (Hgroup (blowUp ℐ).ringCatSheaf ⊤ 1
      (kernel (SheafOfModules.unitToPushforwardObjUnit
        (J' * exceptionalIdeal ℐ ^ d).subschemeι.toRingCatSheafHom))) := by
    rw [hmulJ]
    subst hℐ
    exact isZero_hgroup_one_idealSheaf_comap_blowUp A hdim I
  have : IsNormalDomain A := isNormalDomain_of_isRegularLocalRing A
  have hΓ : Function.Surjective ((Scheme.ΓSpecIso (.of A)).inv ≫ (blowUpToBase ℐ).appTop).hom := by
    subst hℐ
    have : IsIso (blowUpToBase (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))).appTop :=
      (isModification_blowUpToBase_maximalIdeal A hdim).isIso_appTop
    exact (ConcreteCategory.bijective_of_isIso _).2
  have hI : ∀ a ∈ I, ((J' * exceptionalIdeal ℐ ^ d).subschemeι.appTop).hom
      (((Scheme.ΓSpecIso (.of A)).inv ≫ (blowUpToBase ℐ).appTop).hom a) = 0 :=
    fun a ha => Scheme.IdealSheafData.appTop_subschemeι_eq_zero_of_mem _ I hmulJ.ge a ha
  -- the finite support of `J'`
  have hJE : (((Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap (blowUpToBase ℐ)).support :
        Set (blowUp ℐ)) ⊆ ((exceptionalIdeal ℐ).support : Set (blowUp ℐ)) := by
    have hpow : Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal A ^ n).map (Scheme.ΓSpecIso (.of A)).inv.hom) = ℐ ^ n := by
      rw [hℐ, Ideal.map_pow]
      exact map_pow Scheme.IdealSheafData.equivOfIsAffine.symm _ n
    have hle : exceptionalIdeal ℐ ^ n ≤ (Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap (blowUpToBase ℐ) := by
      rw [show exceptionalIdeal ℐ ^ n = (ℐ ^ n).comap (blowUpToBase ℐ) from
        (Stacks.IdealSheaf.comap_pow ℐ (blowUpToBase ℐ) n).symm, ← hpow]
      exact Scheme.IdealSheafData.comap_mono _ (hmono hnI)
    have h := SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hle)
    rwa [Scheme.IdealSheafData.support_pow _ n hn] at h
  have : IsNoetherianRing (CommRingCat.of A) := (inferInstance : IsNoetherianRing A)
  have : AlgebraicGeometry.IsNoetherian (blowUp ℐ) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp ℐ
  obtain ⟨J'', T, hJ'', hT, hTcl⟩ := exists_finite_isClosed_support_of_maximal_order_blowUp A ℐ
    hdim hℐr _ hJE d hd hmax
  have hJ'J'' : J' = J'' :=
    Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor hEC (hJ'.trans hJ''.symm)
  subst hJ'J''
  obtain ⟨t, ht⟩ := Stacks.Blowup.Colength.exists_injective_globalSections_negativeTwist_restrict
    J' T hT hTcl (blowUpToBase ℐ) (exceptionalIdeal ℐ ^ d) hEC
  exact Stacks.Blowup.Colength.length_globalSections_lt_length_quotient (blowUpToBase ℐ) I
    (exceptionalIdeal ℐ ^ d) J' hEC hEtop (Scheme.IdealSheafData.mul_le_right _ _) hfin hH1 hΓ
    hI t ht

end AlgebraicGeometry
