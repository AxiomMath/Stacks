module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
public import StacksFrontier.RingTheory.Flat.Pi
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresProd

/-!
# Projectivity is a Zariski-local property of modules

Let `R` be a commutative ring, `M` an `R`-module and `f₁, …, fₙ ∈ R` a finite family generating
the unit ideal. If every localisation `M_{fᵢ}` is projective over `R_{fᵢ}`, then `M` is projective
over `R`. Mathlib's `Mathlib/RingTheory/LocalProperties/Projective.lean` records this as a
`TODO`, having only the stalkwise criterion for modules of finite presentation; no finiteness
hypothesis appears below.

## Main results

* `Module.Projective.pi`: a product of finitely many modules, each projective over its own
  factor ring, is projective over the product of the factor rings.
* `Module.FaithfullyFlat.pi_localizationAway`: the product of the localisations away from a finite
  family generating the unit ideal is faithfully flat.
* `Module.projective_of_isLocalized_span_range`: projectivity is Zariski-local, for abstract
  localisations.
* `Module.projective_of_localized_span_range`: the same for the canonical
  `LocalizedModule (Submonoid.powers (f i)) M` over `Localization.Away (f i)`.

## Implementation notes

The descent step is faithfully flat descent of projectivity,
`Module.Projective.of_projective_tensorProduct` (Stacks 05A9), which carries no finiteness
hypothesis; the faithfully flat algebra is the finite product `T = ∏ R_{fᵢ}`, faithfully flat
because it is flat and `Spec T → Spec R` is surjective, the `fᵢ` generating the unit ideal.

What has to be supplied is projectivity of `T ⊗[R] M` over `T`. The tensor product is identified
with `∏ (R_{fᵢ} ⊗[R] M) = ∏ M_{fᵢ}` by `Module.Projective.pi`, whose proof is the standard
decomposition of a module over a finite product of rings: the `i`-th factor `Rᵢ` is a retract of
`T` as a `T`-module, via `Pi.single i`, hence projective over `T`, and then `Mᵢ` is projective
over `T` by transitivity, and the finite product of `T`-projectives is `T`-projective because for
a finite index type it is a direct sum.

The `T`-module structure on the `i`-th factor is `Module.compHom` along `Pi.evalRingHom`, which is
the structure `Pi.module'` puts on the product, so no transport is needed between the two.

## References

* [Stacks Project, Tag 05A9](https://stacks.math.columbia.edu/tag/05A9)
* [Stacks Project, Tag 05JQ](https://stacks.math.columbia.edu/tag/05JQ)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Module

/-- Each factor of a product of rings is a projective module over the product: the `i`-th factor
is a retract of the product via `Pi.single i`. -/
theorem Projective.pi_factor {ι : Type*} (A : ι → Type*) [∀ i, CommRing (A i)] (i : ι) :
    letI : Module (∀ j, A j) (A i) := Module.compHom (A i) (Pi.evalRingHom A i)
    Module.Projective (∀ j, A j) (A i) := by
  classical
  let : Algebra (∀ j, A j) (A i) := (Pi.evalRingHom A i).toAlgebra
  let l : A i →ₗ[∀ j, A j] (∀ j, A j) :=
    { toFun := Pi.single i
      map_add' := fun x y ↦ Pi.single_add i x y
      map_smul' := fun x y ↦ by
        ext j
        change Pi.single i (x i * y) j = x j * Pi.single i y j
        by_cases h : j = i
        · subst h
          simp
        · simp [h] }
  exact Module.Projective.of_split l (Algebra.linearMap _ (A i))
    (by
      ext x
      change Pi.single i x i = x
      simp)

/-- **A finite product of projective modules over a product of rings is projective.** If `N i` is
projective over `A i` for each `i` in a finite index type, then `∀ i, N i` is projective over
`∀ i, A i`. -/
theorem Projective.pi {ι : Type*} [Finite ι] (A : ι → Type*) [∀ i, CommRing (A i)]
    (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module (A i) (N i)]
    [∀ i, Module.Projective (A i) (N i)] :
    Module.Projective (∀ i, A i) (∀ i, N i) := by
  classical
  let _ := Fintype.ofFinite ι
  let P := ∀ i, A i
  let (i : ι) : Algebra P (A i) := (Pi.evalRingHom A i).toAlgebra
  let (i : ι) : Module P (N i) := Module.compHom (N i) (Pi.evalRingHom A i)
  let (i : ι) : IsScalarTower P (A i) (N i) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have (i : ι) : Module.Projective P (A i) := Projective.pi_factor A i
  have (i : ι) : Module.Projective P (N i) := Projective.trans P (A i) (N i)
  exact Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := P))

/-- **The product of the localisations away from a family generating the unit ideal is faithfully
flat.** It is flat, being a finite product of localisations, and `Spec` of it surjects onto
`Spec R`: a prime of `R` misses some `f i`, so it is in the image of `Spec R_{f i}`. -/
theorem FaithfullyFlat.pi_localizationAway {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤) (A : ι → Type*) [∀ i, CommRing (A i)]
    [∀ i, Algebra R (A i)] [∀ i, IsLocalization.Away (f i) (A i)] :
    Module.FaithfullyFlat R (∀ i, A i) := by
  have hfl : ∀ i, Module.Flat R (A i) := fun i ↦
    IsLocalization.flat (A i) (Submonoid.powers (f i))
  have : Module.Flat R (∀ i, A i) := Flat.pi A
  refine Module.FaithfullyFlat.of_comap_surjective fun p ↦ ?_
  obtain ⟨i, hi⟩ : ∃ i, f i ∉ p.asIdeal := by
    by_contra! h
    exact p.isPrime.ne_top
      (eq_top_iff.mpr (hf ▸ Ideal.span_le.mpr (Set.range_subset_iff.mpr h)))
  have hp : p ∈ (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R)) := hi
  rw [← PrimeSpectrum.localization_away_comap_range (A i) (f i)] at hp
  obtain ⟨q, hq⟩ := hp
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom A i) q, ?_⟩
  rwa [← PrimeSpectrum.comap_comp_apply]

end Module

/-- The tensor product of a finite product of `R`-algebras with an `R`-module, as a module over
the product. This is `TensorProduct.piLeft` upgraded from `R`-linearity to linearity over the
product ring. -/
noncomputable def TensorProduct.piLeftOfPiRing (R : Type*) {ι : Type*} [Fintype ι]
    (A : ι → Type*) [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (M : Type*) [AddCommGroup M] [Module R M] :
    ((∀ i, A i) ⊗[R] M) ≃ₗ[∀ i, A i] ∀ i, A i ⊗[R] M := by
  classical
  let e : ((∀ i, A i) ⊗[R] M) ≃ₗ[R] ∀ i, A i ⊗[R] M :=
    (TensorProduct.comm R _ _).trans ((TensorProduct.piRight R R M A).trans
      (LinearEquiv.piCongrRight fun i ↦ TensorProduct.comm R M (A i)))
  refine e.toAddEquiv.toLinearEquiv fun a x ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul b m =>
    ext i
    simp [e, TensorProduct.smul_tmul']

namespace Module

/-- **Projectivity is a Zariski-local property of modules.** Let `f : ι → R` be a finite family
generating the unit ideal, let `A i` be a localisation of `R` away from `f i` and let
`g i : M →ₗ[R] N i` exhibit `N i` as the localisation of `M` away from `f i`. If every `N i` is
projective over `A i`, then `M` is projective over `R`.

No finiteness hypothesis is placed on `M`. This is the affine content of Stacks 05JQ: a module
whose localisations on a standard open cover are projective is projective. -/
theorem projective_of_isLocalized_span_range {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {ι : Type*} [Finite ι] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, IsLocalization.Away (f i) (A i)]
    (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module (A i) (N i)] [∀ i, IsScalarTower R (A i) (N i)]
    (g : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (g i)]
    (H : ∀ i, Module.Projective (A i) (N i)) :
    Module.Projective R M := by
  classical
  let _ := Fintype.ofFinite ι
  have hff : Module.FaithfullyFlat R (∀ i, A i) := FaithfullyFlat.pi_localizationAway f hf A
  have hproj (i : ι) : Module.Projective (A i) (A i ⊗[R] M) :=
    have := H i
    Module.Projective.of_equiv'
      ((IsLocalizedModule.isBaseChange (Submonoid.powers (f i)) (A i) (g i)).equiv.symm)
  have hpi : Module.Projective (∀ i, A i) (∀ i, A i ⊗[R] M) :=
    Projective.pi A (fun i ↦ A i ⊗[R] M)
  have : Module.Projective (∀ i, A i) ((∀ i, A i) ⊗[R] M) :=
    Module.Projective.of_equiv' (TensorProduct.piLeftOfPiRing R A M).symm
  exact Module.Projective.of_projective_tensorProduct (∀ i, A i)

/-- **Projectivity is a Zariski-local property of modules**, for the canonical localisations: if
`f : ι → R` is a finite family generating the unit ideal and each
`LocalizedModule (Submonoid.powers (f i)) M` is projective over `Localization.Away (f i)`, then
`M` is projective over `R`. -/
theorem projective_of_localized_span_range {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {ι : Type*} [Finite ι] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (H : ∀ i, Module.Projective (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M)) :
    Module.Projective R M :=
  projective_of_isLocalized_span_range f hf (fun i ↦ Localization.Away (f i))
    (fun i ↦ LocalizedModule (Submonoid.powers (f i)) M)
    (fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M) H

end Module

end
