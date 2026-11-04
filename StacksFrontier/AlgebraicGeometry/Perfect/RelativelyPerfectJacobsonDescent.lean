module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonAffineStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonPointwise
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonChart
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreGenuine

/-!
# Relative perfectness descends from the closed fibre over a Jacobson pair

Let `(R, I)` be a ring with an ideal contained in its Jacobson radical, write `S = Spec R` and
`S₀ = Spec (R/I)`, let `f : X ⟶ S` be proper, flat and locally of finite presentation and put
`X₀ = S₀ ×_S X`. A pseudo-coherent object `E` of `D(𝒪_X)` whose derived restriction `E₀` to `X₀`
is `S₀`-perfect is `S`-perfect. This is Stacks 0DJZ.

## Main results

* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_of_affineChart`: on an
  affine open `V` of `X` presented by `d` variables over `R`, a point `y` of `V` specializing to a
  point of `V` in the closed fibre at which `E₀` has Tor amplitude in `[a, b]` over `S₀` has its
  derived stalk of Tor amplitude in `[a - d, b]` over `S`.
* `AlgebraicGeometry.Scheme.Hom.exists_uniform_derivedStalk_bound_of_closedFibre`: one interval
  bounds the Tor amplitude over the base of every derived stalk of `E`.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`
  and `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_canonical_of_closedFibre`: Stacks 0DJZ.

## References

* [Stacks Project, Lemma 37.71.3 (Tag 0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Lemma 15.85.9 (Tag 0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (I : Ideal R)

/-- The chart morphism of an affine open, read on spectra, is the morphism of spectra of the
structure map `R ⟶ Γ(X, V)`. -/
theorem fromSpec_comp_eq_specMap_chartHom {V : X.Opens} (hV : IsAffineOpen V) :
    letI : Algebra R Γ(X, V) := (chartHom f V).toAlgebra
    (hV.fromSpec : Spec (CommRingCat.of Γ(X, V)) ⟶ X) ≫ f =
      AffineRelativeTorAmplitude.specMap R Γ(X, V) := by
  let : Algebra R Γ(X, V) := (chartHom f V).toAlgebra
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- **Tor amplitude over the base at a generization of a point of the closed fibre, on an affine
chart.** Let `f : X ⟶ Spec R` be flat and locally of finite presentation, let `V` be an affine
open of `X` whose sections are a quotient of `R[x_1, …, x_d]`, and let `E` be a pseudo-coherent
object of `D(𝒪_X)`. Let `x₀` be a point of the closed fibre `X₀` lying in `V`, at which the
derived stalk of the derived restriction `E₀` of `E` has Tor amplitude in `[a, b]` over the local
ring of `S₀`. Then at every point `y` of `X` specializing to `x₀`, the derived stalk of `E` has Tor
amplitude in `[a - d, b]` over the local ring of `S`.

On `V = Spec A` the object `E` is the class of `M̃^•` for a pseudo-coherent complex `M` of
`A`-modules. The bound on `E₀` at `x₀` is a bound on the derived fibre of `M` at the prime `q₀`
of `x₀`, and Stacks 0DJH turns it into the bound `[a - d, b]` for `M_{q₀}` over `R`, which
localises to the prime of `y`. -/
theorem hasTorAmplitudeCanonical_derivedStalk_of_affineChart [Flat f]
    [LocallyOfFinitePresentation f] {V : X.Opens} (hV : IsAffineOpen V) (d : ℕ)
    (ψ : MvPolynomial (Fin d) R →+* Γ(X, V)) (hψ : Function.Surjective ψ)
    (hψC : ψ.comp MvPolynomial.C = chartHom f V)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (x₀ : closedFibre f I) (hx₀ : (closedFibreToTotal f I).base x₀ ∈ V) (y : X)
    (hy : y ⤳ (closedFibreToTotal f I).base x₀) (a b : ℤ)
    (h₀ : HasTorAmplitudeCanonical
      (ToType ((Spec (CommRingCat.of (R ⧸ I))).presheaf.stalk
        ((closedFibreToBase f I).base x₀)))
      ((ModuleCat.restrictScalars ((closedFibreToBase f I).stalkMap x₀).hom).mapDerivedCategory.obj
        ((derivedStalkFunctor x₀).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (closedFibreToTotal f I).toLRSHom.toShHom).obj E))) a b) :
    HasTorAmplitudeCanonical (ToType ((Spec (CommRingCat.of R)).presheaf.stalk (f.base y)))
      ((ModuleCat.restrictScalars (f.stalkMap y).hom).mapDerivedCategory.obj
        ((derivedStalkFunctor y).obj E)) (a - (d : ℤ)) b := by
  let : Algebra R Γ(X, V) := (chartHom f V).toAlgebra
  have : Module.Flat R Γ(X, V) := flat_chartHom f hV
  have : Algebra.FinitePresentation R Γ(X, V) := finitePresentation_chartHom f hV
  let presentation : MvPolynomial (Fin d) R →ₐ[R] Γ(X, V) :=
    ⟨ψ, fun r => by
      rw [show algebraMap R Γ(X, V) = chartHom f V from rfl, ← hψC]
      simp [MvPolynomial.algebraMap_eq]⟩
  let ι : Spec (CommRingCat.of Γ(X, V)) ⟶ X := hV.fromSpec
  have : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion hV.fromSpec)
  have hι := fromSpec_comp_eq_specMap_chartHom f hV
  let F := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    ι.toLRSHom.toShHom).obj E
  have hF : RingedSpace.IsPseudoCoherent (X := (Spec (CommRingCat.of Γ(X, V))).toRingedSpace) F :=
    Scheme.Hom.isPseudoCoherent_derivedPullback ι E hE
  obtain ⟨K, hK, ⟨eK⟩⟩ :=
    RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde (CommRingCat.of Γ(X, V)) F hF
  let M := DerivedCategory.Q.objPreimage K
  let eM : DerivedCategory.Q.obj M ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hM : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj M) :=
    StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso hK eM.symm
  let eF : DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex
      (R := CommRingCat.of Γ(X, V)) M) ≅ F :=
    ((tilde.functor (CommRingCat.of Γ(X, V))).mapDerivedCategoryFactors.app M).symm ≪≫
      (tilde.functor (CommRingCat.of Γ(X, V))).mapDerivedCategory.mapIso eM ≪≫ eK
  have hrange : ∀ z ∈ V, ∃ w : PrimeSpectrum Γ(X, V), ι.base w = z := fun z hz =>
    (hV.range_fromSpec.symm ▸ hz : z ∈ Set.range ι.base)
  obtain ⟨w₀, hw₀⟩ := hrange _ hx₀
  obtain ⟨w, hw⟩ := hrange y (hy.mem_open V.isOpen hx₀)
  have hspec : (w : Spec (CommRingCat.of Γ(X, V))) ⤳ w₀ :=
    ι.isOpenEmbedding.isInducing.specializes_iff.mp (by rwa [hw, hw₀])
  have hq : w.asIdeal ≤ w₀.asIdeal := (PrimeSpectrum.le_iff_specializes w w₀).mpr hspec
  have : IsClosedImmersion (closedBase I) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hpb : IsPullback (closedFibreToTotal f I) (closedFibreToBase f I) f (closedBase I) :=
    (IsPullback.of_hasPullback (closedBase I) f).flip
  have hpt : (closedBase I).base ((closedFibreToBase f I).base x₀) =
      f.base ((closedFibreToTotal f I).base x₀) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hFS := Stacks.Thickenings.hasTorAmplitudeCanonical_derivedFibre_derivedStalk_of_isPullback
    hpb x₀ hpt E a b h₀
  obtain ⟨ε, hfib⟩ := exists_hasTorAmplitudeCanonical_derivedFibre_tilde f ι hι E M eF _ w₀ hw₀
    hpt _ a b hFS
  have hh : Function.Surjective
      (((closedBase I).stalkMap ((closedFibreToBase f I).base x₀)).hom.comp ε.symm.toRingHom) :=
    ((closedBase I).stalkMap_surjective _).comp ε.symm.surjective
  have hAt := PseudoCoherence.hasTorAmplitudeAt_of_derivedFibre_of_le d presentation hψ
    w₀.asIdeal w.asIdeal hq M hM a b _
    _ (PseudoCoherence.restrictScalarsResidueFieldIso _ hh) hfib
  exact hasTorAmplitudeCanonical_derivedStalk_of_hasTorAmplitudeAt f ι hι E M eF y w hw _ _ hAt

/-- Widening the interval weakens canonical Tor amplitude. -/
theorem hasTorAmplitudeCanonical_mono {T : Type u} [CommRing T]
    {K : DerivedCategory (ModuleCat.{u} T)} {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    (h : HasTorAmplitudeCanonical T K a b) : HasTorAmplitudeCanonical T K a' b' := by
  rw [PseudoCoherence.hasTorAmplitudeCanonical_iff_hasTorAmplitude] at h ⊢
  intro N i hi
  exact h N i fun ⟨h₁, h₂⟩ => hi ⟨by omega, by omega⟩

/-- **One interval bounds the Tor amplitude over the base of every derived stalk.** Let `I` be
contained in the Jacobson radical of `R`, let `f : X ⟶ Spec R` be proper, flat and locally of
finite presentation, and let `E` be a pseudo-coherent object of `D(𝒪_X)` whose derived restriction
to the closed fibre `X₀` is `Spec (R/I)`-perfect, for a family of certificates pinned to the
genuine tensor product of sheaves of modules. Then a single interval `[a, b]` contains, for every
point `y` of `X`, the Tor amplitude over the local ring `𝒪_{S, f y}` of the derived stalk of `E`
at `y`.

The closed fibre is quasi-compact, so one interval bounds `E₀` on it; finitely many affine charts
presented by polynomial algebras cover `X`; every point of `X` specializes into the closed fibre;
and on a chart containing the specialization the bound is
`hasTorAmplitudeCanonical_derivedStalk_of_affineChart`. -/
theorem exists_uniform_derivedStalk_bound_of_closedFibre [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (hI : I ≤ (⊥ : Ideal R).jacobson)
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (hD₀ : IsGenuineRelativeTensorFamily (closedFibreToBase f I) D₀)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo D₀
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (closedFibreToTotal f I).toLRSHom.toShHom).obj E)) :
    ∃ a b : ℤ, ∀ y : X,
      HasTorAmplitudeCanonical (ToType ((Spec (CommRingCat.of R)).presheaf.stalk (f.base y)))
        ((ModuleCat.restrictScalars.{u}
            ((SemilinearStalk.commStalkRingEquiv X.presheaf y).symm.toRingHom.comp
              (f.stalkMap y).hom)).mapDerivedCategory.obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u} X.toRingedSpace) y).mapDerivedCategory.obj E)) a b := by
  classical
  obtain ⟨a, b, h₀⟩ := exists_stalkTorAmplitude_closedFibre f I D₀ hD₀ _ hE₀
  have h₀' := fun x₀ => (hasTorAmplitudeCanonical_derivedStalk_iff_structureSheafOfRings
    (closedFibreToBase f I) x₀ _ a b).mpr
    ((hasTorAmplitudeCanonical_derivedStalk_relative_iff (closedFibreToBase f I) x₀ _ a b).mp
      (h₀ x₀))
  obtain ⟨s, hs, hch⟩ :=
    exists_finset_affineOpens_mvPolynomial_surjective_chartHom_of_universallyClosed f
  choose d ψ hψ hψC using hch
  let D : ℕ := ∑ V ∈ s.attach, d V.1 V.2
  have hD : ∀ (V : X.affineOpens) (hV : V ∈ s), d V hV ≤ D := fun V hV =>
    Finset.single_le_sum (f := fun V : s => d V.1 V.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_attach s ⟨V, hV⟩)
  refine ⟨a - D, b, fun y => ?_⟩
  obtain ⟨x', hyx', x₀, rfl⟩ := exists_specializes_mem_range_closedFibreToTotal f I hI y
  have hmem : (closedFibreToTotal f I).base x₀ ∈ (⨆ V ∈ s, (V : X.Opens)) := by
    rw [hs]
    trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨V, hV, hx₀⟩ := hmem
  have h₁ := hasTorAmplitudeCanonical_derivedStalk_of_affineChart f I V.2 (d V hV) (ψ V hV)
    (hψ V hV) (hψC V hV) E hE x₀ hx₀ y hyx' a b (h₀' x₀)
  have h₂ := hasTorAmplitudeCanonical_mono (a' := a - (D : ℤ)) (b' := b)
    (by
      have := hD V hV
      omega) le_rfl h₁
  exact (hasTorAmplitudeCanonical_derivedStalk_iff_structureSheafOfRings f y E _ b).mp h₂

/-- **Stacks 0DJZ.** Let `R` be a ring and `I` an ideal contained in its Jacobson radical; set
`S = Spec R` and `S₀ = Spec (R/I)`. Let `f : X ⟶ S` be proper, flat and locally of finite
presentation and let `X₀ = S₀ ×_S X`. Let `E` be a pseudo-coherent object of `D(𝒪_X)`. If the
derived restriction `E₀` of `E` to `X₀` is `S₀`-perfect, then `E` is `S`-perfect.

Relative perfectness is read at families of certified derived tensor products on the open
subspaces of the inverse-image ringed spaces, pinned to the tensor product of sheaves of modules,
which is the tensor product of the source's definition. -/
@[stacks 0DJZ]
theorem isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (hI : I ≤ (⊥ : Ideal R).jacobson)
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (hD₀ : IsGenuineRelativeTensorFamily (closedFibreToBase f I) D₀)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo D₀
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (closedFibreToTotal f I).toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo D E :=
  ⟨hE, locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_base_bound f D hD E
    (exists_uniform_derivedStalk_bound_of_closedFibre f I hI D₀ hD₀ E hE hE₀)⟩

/-- **Stacks 0DJZ at the canonical derived tensor products.** Let `R` be a ring and `I` an ideal
contained in its Jacobson radical; set `S = Spec R` and `S₀ = Spec (R/I)`. Let `f : X ⟶ S` be
proper, flat and locally of finite presentation and let `X₀ = S₀ ×_S X`. Let `E` be a
pseudo-coherent object of `D(𝒪_X)`. If the derived restriction `E₀` of `E` to `X₀` is
`S₀`-perfect, then `E` is `S`-perfect, relative perfectness being read at the canonical derived
tensor products on both sides. -/
@[stacks 0DJZ]
theorem isPerfectRelativeTo_canonical_of_closedFibre [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (hI : I ≤ (⊥ : Ideal R).jacobson)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base))
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (closedFibreToTotal f I).toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base)) E :=
  isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine f I hI _
    (isGenuineRelativeTensorFamily_canonical f) _
    (isGenuineRelativeTensorFamily_canonical (closedFibreToBase f I)) E hE hE₀

end AlgebraicGeometry.Scheme.Hom

end
