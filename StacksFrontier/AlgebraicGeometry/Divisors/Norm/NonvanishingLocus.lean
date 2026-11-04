module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.FiberMaximalSpectrum
public import StacksFrontier.RingTheory.Norm.NonvanishingFibre

/-!
# Where the norm of a function along a finite projective morphism vanishes

Let `π : R ⟶ X` be a morphism of schemes, let `U` be an affine open of `X` whose preimage is
affine, and suppose `Γ(R, π⁻¹U)` is finite projective over `Γ(X, U)`. For a function `a` on
`π⁻¹U` the nonvanishing locus of its norm is the set of points of `U` over which `a` vanishes
nowhere: a point `v` of `U` lies in `X.basicOpen (projectiveNorm a)` exactly when every point of
`R` above `v` lies in `R.basicOpen a`.

## Main results

* `AlgebraicGeometry.mem_basicOpen_projectiveNorm_iff` is the statement above.
* `AlgebraicGeometry.finite_projective_app_of_isFiniteLocallyFree` supplies its finiteness and
  projectivity hypotheses for a finite locally free morphism.
* `AlgebraicGeometry.IsAffineOpen.mem_basicOpen_iff_notMem_primeIdealOf`,
  `AlgebraicGeometry.IsAffineOpen.primeIdealOf_fromSpec`,
  `AlgebraicGeometry.IsAffineOpen.fromSpec_mem` and
  `AlgebraicGeometry.comap_primeIdealOf_app` are the dictionary between the points of an affine
  open and the primes of its ring of sections which the translation runs on.

## Implementation notes

The ring-theoretic content is `Algebra.projectiveNorm_mem_iff_exists_comap_eq`; everything here
is the translation of that statement from primes to points. The translation is carried by
`AlgebraicGeometry.IsAffineOpen.primeIdealOf`, which is a bijection onto the prime spectrum of
the ring of sections — `AlgebraicGeometry.IsAffineOpen.fromSpec` is its inverse — and whose
compatibility with a morphism is Mathlib's
`AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`.

The open on the source is `π ⁻¹ᵁ U` rather than an arbitrary open over `U`, because the
statement quantifies over *all* points of `R` above `v`, and those are exactly the points of
`π ⁻¹ᵁ U` above `v`.

The finiteness and projectivity of `Γ(R, π⁻¹U)` over `Γ(X, U)` are hypotheses rather than
instances, because the algebra structure is the one induced by `π` and has to be introduced by a
`letI`.

`AlgebraicGeometry.finite_projective_app_of_isFiniteLocallyFree` is the affine-open form of a
statement that `StacksFrontier/AlgebraicGeometry/Groupoids/Stabilizer/AffineNorm.lean` carries as a
private lemma over `⊤`; it is derived here from Tag 02KB, which turns finite local freeness into
finiteness, flatness and local finite presentation, each of which is a statement about the maps
of sections on affine opens.

## References

* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The dictionary between points of an affine open and primes of its ring of sections -/

/-- A function on an affine open is nonvanishing at a point of it exactly when it avoids the
prime of the ring of sections corresponding to that point. -/
theorem IsAffineOpen.mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (r : Γ(X, U)) {x : X} (hx : x ∈ U) :
    x ∈ X.basicOpen r ↔ r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen]
  change _ ↔ hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen r
  rw [hU.fromSpec_primeIdealOf]

/-- Every prime of the ring of sections of an affine open is the prime of a point of it. -/
theorem IsAffineOpen.primeIdealOf_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(X, U)) (hq : hU.fromSpec q ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec q, hq⟩ = q :=
  hU.fromSpec.isOpenEmbedding.injective (by rw [hU.fromSpec_primeIdealOf])

/-- The point of a prime of the ring of sections of an affine open lies in that open. -/
theorem IsAffineOpen.fromSpec_mem {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(X, U)) : hU.fromSpec q ∈ U := by
  have h : hU.fromSpec q ∈ Set.range (fun z ↦ hU.fromSpec.base z) := ⟨q, rfl⟩
  rwa [hU.range_fromSpec] at h

/-- The prime of a point of the preimage of an affine open contracts along the morphism to the
prime of its image. -/
theorem comap_primeIdealOf_app {R X : Scheme.{u}} (π : R ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (hP : IsAffineOpen (π ⁻¹ᵁ U)) {p : R} (hp : p ∈ π ⁻¹ᵁ U) :
    PrimeSpectrum.comap (π.app U).hom (hP.primeIdealOf ⟨p, hp⟩) =
      hU.primeIdealOf ⟨π.base p, hp⟩ := by
  have h := IsAffineOpen.comap_primeIdealOf_appLE (f := π) U hU (π ⁻¹ᵁ U) hP le_rfl hp
  rwa [Scheme.Hom.appLE_eq_app] at h

/-! ### The nonvanishing locus of a norm -/

/-- The nonvanishing locus of a function on `U` whose vanishing in a prime of `Γ(X, U)` is
detected by the primes of `Γ(R, π⁻¹U)` over it. -/
private theorem mem_basicOpen_iff_forall_of_comap {R X : Scheme.{u}} (π : R ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (hP : IsAffineOpen (π ⁻¹ᵁ U)) (a : Γ(R, π ⁻¹ᵁ U)) (N : Γ(X, U))
    (hN : ∀ p : PrimeSpectrum Γ(X, U), N ∈ p.asIdeal ↔ ∃ q : PrimeSpectrum Γ(R, π ⁻¹ᵁ U),
      PrimeSpectrum.comap (π.app U).hom q = p ∧ a ∈ q.asIdeal)
    {v : X} (hv : v ∈ U) :
    v ∈ X.basicOpen N ↔ ∀ p : R, π.base p = v → p ∈ R.basicOpen a := by
  rw [hU.mem_basicOpen_iff_notMem_primeIdealOf N hv, hN (hU.primeIdealOf ⟨v, hv⟩)]
  constructor
  · intro hno p hp
    have hpU : p ∈ π ⁻¹ᵁ U := by rwa [Scheme.Hom.mem_preimage, hp]
    rw [hP.mem_basicOpen_iff_notMem_primeIdealOf a hpU]
    intro hmem
    refine hno ⟨hP.primeIdealOf ⟨p, hpU⟩, ?_, hmem⟩
    rw [comap_primeIdealOf_app π hU hP hpU]
    exact congrArg hU.primeIdealOf (Subtype.ext hp)
  · rintro hall ⟨q, hq, hmem⟩
    have hqm := hP.fromSpec_mem q
    have hqeq := hP.primeIdealOf_fromSpec q hqm
    have hvq : π.base (hP.fromSpec q) = v := by
      have h := comap_primeIdealOf_app π hU hP hqm
      rw [hqeq] at h
      exact congrArg Subtype.val (hU.primeIdealOf_injective (h.symm.trans hq))
    exact (hP.mem_basicOpen_iff_notMem_primeIdealOf a hqm).mp (hall _ hvq) (by rwa [hqeq])

/-- **The nonvanishing locus of a norm.** Let `π : R ⟶ X` be a morphism of schemes and let `U` be
an affine open of `X` with affine preimage, making `Γ(R, π⁻¹U)` a finite projective
`Γ(X, U)`-module, and let `a` be a function on `π⁻¹U`. A point of `U` lies in the basic open of
the norm of `a` exactly when `a` is nonvanishing at every point of `R` above it. -/
theorem mem_basicOpen_projectiveNorm_iff {R X : Scheme.{u}} (π : R ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (hP : IsAffineOpen (π ⁻¹ᵁ U))
    (hfin : letI : Algebra Γ(X, U) Γ(R, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra;
      Module.Finite Γ(X, U) Γ(R, π ⁻¹ᵁ U))
    (hproj : letI : Algebra Γ(X, U) Γ(R, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra;
      Module.Projective Γ(X, U) Γ(R, π ⁻¹ᵁ U))
    (a : Γ(R, π ⁻¹ᵁ U)) {v : X} (hv : v ∈ U) :
    letI : Algebra Γ(X, U) Γ(R, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    letI := hfin
    letI := hproj
    v ∈ X.basicOpen (Algebra.projectiveNorm Γ(X, U) a) ↔
      ∀ p : R, π.base p = v → p ∈ R.basicOpen a := by
  let : Algebra Γ(X, U) Γ(R, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  let : Module.Finite Γ(X, U) Γ(R, π ⁻¹ᵁ U) := hfin
  let : Module.Projective Γ(X, U) Γ(R, π ⁻¹ᵁ U) := hproj
  exact mem_basicOpen_iff_forall_of_comap π hU hP a _
    (fun p ↦ Algebra.projectiveNorm_mem_iff_exists_comap_eq p a) hv

/-! ### Finite projectivity of the sections of a finite locally free morphism -/

/-- **The sections of a finite locally free morphism over an affine open.** For a finite locally
free `f : X ⟶ Y` and an affine open `U` of `Y`, the ring `Γ(X, f⁻¹U)` is a finite projective
module over `Γ(Y, U)`. -/
theorem finite_projective_app_of_isFiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) ∧ Module.Projective Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  obtain ⟨_, _, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      inferInstance
  have hPaff : IsAffineOpen (f ⁻¹ᵁ U) := IsAffineHom.isAffine_preimage U hU
  have hflatLE := f.flat_appLE hU hPaff (le_refl (f ⁻¹ᵁ U))
  have hpresLE := f.finitePresentation_appLE hU hPaff (le_refl (f ⁻¹ᵁ U))
  rw [Scheme.Hom.appLE_eq_app] at hflatLE hpresLE
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  let : Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := hflatLE
  let : Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    have : Algebra.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := hpresLE
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end AlgebraicGeometry

end
