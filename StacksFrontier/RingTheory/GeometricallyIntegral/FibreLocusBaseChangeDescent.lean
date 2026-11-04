module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.RingTheory.Flat.GeometricFibresStage
public import StacksFrontier.RingTheory.GeometricallyIntegral.FibreLocusSchemeBridge
public import StacksFrontier.RingTheory.GeometricallyIntegral.GenericPointIrreducible
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Subalgebra

/-!
# Descending the geometrically irreducible fibre locus along a base extension

The irreducible good half of the generic-fibre dichotomy — over a Noetherian domain `D` with a
finite type algebra `T`, a geometrically irreducible generic fibre forces a nonempty basic open of
`Spec D` inside `Algebra.geometricallyIrreducibleFibreLocus D T` — is the affine case at the
generic point of [Stacks, Tag 0559](https://stacks.math.columbia.edu/tag/0559), and by
`Algebra.exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isConstructible` it is
equivalent to the constructibility of that locus. It is the one remaining hypothesis of
`Algebra.isConstructible_geometricallyIntegralFibreLocus_of_irreducible_goodGeneric`, the reduced
half having been proved in
`StacksFrontier.RingTheory.GeometricallyIntegral.SmoothGenericFibre`.

The First proof of Stacks 0559 opens by replacing `D` by a finite cover and `T` by the reduction of
the base change, so as to make the generic fibre geometrically *reduced* as well as geometrically
irreducible. **This file carries out that replacement**, at the level of rings: it proves the three
transport statements it needs and assembles them into
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_cover`, which
reduces the irreducible good half for an arbitrary finite type algebra to the case of a
geometrically integral generic fibre, given a cover of the base.

The ring-theoretic shape of the cover is the one the Second proof of Stacks 0559 uses: a Noetherian
domain `D'` over `D` whose spectrum maps homeomorphically onto `Spec D`, so that the fibres of `T`
are unchanged up to a universal homeomorphism, and over which the reduced base change has
geometrically integral generic fibre.

## The three transports

* **The locus does not see the reduction.** `Algebra.geometricallyIrreducibleFibreLocus` is defined
  by the irreducibility of the spectra of the fibres, so dividing the algebra by an ideal of
  nilpotents leaves it unchanged: the fibre of the quotient is the quotient of the fibre by an
  ideal of nilpotents, whose spectrum is homeomorphic. This is the affine form of the direction
  of Stacks 0555 that the First proof invokes to come back from `X'` to `X_V`.
* **The locus descends along a base extension injective on spectra.** If `Spec R → Spec A` is
  injective and a prime `q` of `R` has geometrically irreducible fibre for `R ⊗[A] T`, then its
  contraction has geometrically irreducible fibre for `T`. The test field over `A` is extended to a
  test field over `R` by taking a residue field of the nonzero fibre `R ⊗[A] K`, and injectivity is
  what forces that residue field to have kernel exactly `q`; the final descent along the resulting
  field extension is `irreducibleSpace_primeSpectrum_of_injective` applied to the injective base
  change `K ⊗[A] T → (K ⊗[A] T) ⊗[K] L`.
* **A nonempty basic open upstairs produces one downstairs.** Over domains, a homeomorphism of
  spectra carries the basic open produced upstairs to a nonempty open subset downstairs, and
  `PrimeSpectrum.exists_ne_zero_basicOpen_subset_iff_isOpen` converts that back into a nonempty
  basic open.

## Main results

* `Algebra.mem_geometricallyIrreducibleFibreLocus_comap_of_injective`: descent of the
  geometrically irreducible fibre locus along a base extension injective on spectra, and
  `Algebra.mem_geometricallyIrreducibleFibreLocus_tensorProduct_of_comap` the converse base change
  direction.
* `Algebra.isGeometricallyIrreducible_fractionRing_tensorProduct`: the generic fibre over the
  fraction field is geometrically irreducible as soon as the generic point lies in the locus — the
  companion for irreducibility of
  `Algebra.isGeometricallyReduced_fractionRing_tensorProduct`.
* `Algebra.mem_geometricallyIntegralFibreLocus_bot_of_isGeometricallyIntegral`: conversely a
  geometrically integral generic fibre puts the generic point in the geometrically integral fibre
  locus.
* `Algebra.geometricallyIrreducibleFibreLocus_quotient_of_le_nilradical`: the locus only sees the
  reduction of the algebra, with the per-fibre statement
  `Algebra.irreducibleSpace_primeSpectrum_quotient_tensorProduct_iff`.
* `Algebra.exists_ne_zero_basicOpen_subset_of_comap_isHomeomorph`: the basic-open descent, and
  `Algebra.isHomeomorph_comap_of_universalHomeomorphism_specMap` the reading of a universal
  homeomorphism of affine schemes as a homeomorphism of spectra.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_cover`: **the
  main result**, the first step of the First proof of Stacks 0559 as a reduction of the irreducible
  good half to its geometrically integral case.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_cover_separable`:
  the same reduction with separability of the function field of the new generic fibre in place of
  geometric integrality of that fibre. This is the form the rest of the First proof consumes, and
  it needs no reduction of the base change: what the hypersurface model is built from is a
  separating transcendence basis of the function field, which separability provides.

## Implementation notes

**The existence of the cover is not proved here**, and nothing in this file claims it. It is the
ring-theoretic content of Stacks 0550, whose scheme-level form is formalized as
`Stacks.Cover0550.exists_finiteUniversalHomeomorphism_geometricallyReduced_genericFiber`; the
affine construction it rests on is formalized as
`Stacks.Cover0550.exists_finite_universalHomeomorphic_spec_extension`, which for a finite purely
inseparable extension `K'` of the fraction field `K` of `D` produces a module-finite
`D`-subalgebra `D'` of `K'` with fraction field `K'` whose spectrum is a universal homeomorphism
over `Spec D` — exactly the `D'` this file's main result takes as input. What is missing is the
choice of `K'`: by Stacks 030R, formalized as
`exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType`, one takes `K'` so that the
reduction of `K' ⊗[K] L` is separable over `K'`, where `L` is the function field of the generic
fibre; the residue is then to identify that reduction with the function field of the reduced base
change and to deduce geometric reducedness of the reduced base change from separability of its
function field.

No declaration here carries a `@[stacks 0559]`, `@[stacks 055A]`, `@[stacks 0550]` or
`@[stacks 0555]` attribute. The tagged statements are about arbitrary morphisms of schemes; what is
proved here is one transport step of their proofs in the affine, fibrewise form, and a tag on it
would over-claim.

The descent of irreducibility along a field extension needs no dedicated statement here. A base
change `M → M ⊗[k] K` along a field extension `K/k` is injective, since `M` is flat over the field
`k` and `k → K` is injective (`Algebra.TensorProduct.includeLeft_injective`), and an injective ring
map has `ker = (0) ≤ nilradical`, so the induced map of spectra has dense range and the canonical
`irreducibleSpace_primeSpectrum_of_injective` applies directly. That is the only form of the
descent this file uses.

Note that typeclass synthesis will not find `Module.FaithfullyFlat (K ⊗[A] T) ((K ⊗[A] T) ⊗[K] L)`
within the default heartbeat budget, so the surjectivity route through
`PrimeSpectrum.comap_surjective_of_faithfullyFlat` is not available at these compound types; the
injectivity route above needs only `Module.Flat K (K ⊗[A] T)`, which is immediate for a field `K`.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
* [Stacks Project, Tag 055B](https://stacks.math.columbia.edu/tag/055B)
* [Stacks Project, Tag 0550](https://stacks.math.columbia.edu/tag/0550)
* [Stacks Project, Tag 0555](https://stacks.math.columbia.edu/tag/0555)
* [Stacks Project, Tag 030R](https://stacks.math.columbia.edu/tag/030R)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open PrimeSpectrum
open scoped TensorProduct

universe u

namespace Algebra

/-! ## Descent of the locus along a base extension injective on spectra -/

section Descent

variable {A R T : Type u} [CommRing A] [CommRing R] [Algebra A R] [CommRing T] [Algebra A T]

/-- **Descent of the geometrically irreducible fibre locus along a base extension injective on
spectra.** Let `A → R` be a ring map for which `Spec R → Spec A` is injective, let `T` be an
`A`-algebra and let `q` be a prime of `R`. If `q` lies in the geometrically irreducible fibre locus
of `R ⊗[A] T` over `R`, then its contraction lies in the geometrically irreducible fibre locus of
`T` over `A`.

Let `K` be a field over `A` with `ker (A → K) = p`, the contraction of `q`. The fibre `R ⊗[A] K` is
nonzero because `p` lifts to `q`, so it has a maximal ideal; the quotient `L` by it is a field
which is at once an `R`-algebra and an extension of `K`. The kernel of `R → L` is a prime of `R`
with the same contraction `p` as `q`, hence equal to `q` by injectivity, so the hypothesis applies
to `L` and makes `Spec ((R ⊗[A] T) ⊗[R] L)` irreducible. That ring is `(K ⊗[A] T) ⊗[K] L`, and
irreducibility descends along the field extension `L/K` by
`irreducibleSpace_primeSpectrum_of_injective`, the base change `K ⊗[A] T → (K ⊗[A] T) ⊗[K] L` being
injective by `Algebra.TensorProduct.includeLeft_injective`. -/
theorem mem_geometricallyIrreducibleFibreLocus_comap_of_injective
    (hinj : Function.Injective (comap (algebraMap A R))) (q : PrimeSpectrum R)
    (hq : q ∈ geometricallyIrreducibleFibreLocus R (R ⊗[A] T)) :
    comap (algebraMap A R) q ∈ geometricallyIrreducibleFibreLocus A T := by
  intro K _ _ hker
  have hrange : (⟨RingHom.ker (algebraMap A K), RingHom.ker_isPrime _⟩ : PrimeSpectrum A) ∈
      Set.range (comap (algebraMap A R)) := ⟨q, PrimeSpectrum.ext hker.symm⟩
  have : Nontrivial (R ⊗[A] K) := nontrivial_tensorProduct_of_mem_rangeComap R K hrange
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (R ⊗[A] K)
  have := hm
  let L := (R ⊗[A] K) ⧸ m
  let _ : Field L := Ideal.Quotient.field m
  let _ : Algebra K L :=
    ((Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight : K →ₐ[A] R ⊗[A] K).toRingHom).toAlgebra
  have htowerK : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A L a = Ideal.Quotient.mk m
      (Algebra.TensorProduct.includeRight (algebraMap A K a))
    rw [AlgHom.commutes]
    rfl
  have hKL : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  -- the kernel of `R → L` is `q`
  have hkerL : RingHom.ker (algebraMap R L) = q.asIdeal := by
    have hprime : (RingHom.ker (algebraMap R L)).IsPrime := RingHom.ker_isPrime _
    have hAL : RingHom.ker (algebraMap A L) = RingHom.ker (algebraMap A K) := by
      rw [IsScalarTower.algebraMap_eq A K L, ← RingHom.comap_ker,
        (RingHom.injective_iff_ker_eq_bot _).mp hKL, ← RingHom.ker_eq_comap_bot]
    have hcomap : comap (algebraMap A R)
        (⟨RingHom.ker (algebraMap R L), hprime⟩ : PrimeSpectrum R) =
        comap (algebraMap A R) q := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap (algebraMap A R) (RingHom.ker (algebraMap R L)) =
        Ideal.comap (algebraMap A R) q.asIdeal
      calc Ideal.comap (algebraMap A R) (RingHom.ker (algebraMap R L))
          = RingHom.ker ((algebraMap R L).comp (algebraMap A R)) :=
            (RingHom.comap_ker (algebraMap R L) (algebraMap A R)).symm
        _ = RingHom.ker (algebraMap A L) := by rw [IsScalarTower.algebraMap_eq A R L]
        _ = RingHom.ker (algebraMap A K) := hAL
        _ = Ideal.comap (algebraMap A R) q.asIdeal := hker
    exact congrArg PrimeSpectrum.asIdeal (hinj hcomap)
  -- transport the irreducibility of the fibre over `L`
  have hirrL := hq L hkerL
  have e1 : (R ⊗[A] T) ⊗[R] L ≃+* L ⊗[R] (R ⊗[A] T) :=
    (Algebra.TensorProduct.comm R (R ⊗[A] T) L).toRingEquiv
  have e2 : L ⊗[R] (R ⊗[A] T) ≃+* L ⊗[A] T :=
    (Algebra.TensorProduct.cancelBaseChange A R R L T).toRingEquiv
  have e3 : L ⊗[K] (K ⊗[A] T) ≃+* L ⊗[A] T :=
    (Algebra.TensorProduct.cancelBaseChange A K K L T).toRingEquiv
  have e4 : (K ⊗[A] T) ⊗[K] L ≃+* L ⊗[K] (K ⊗[A] T) :=
    (Algebra.TensorProduct.comm K (K ⊗[A] T) L).toRingEquiv
  have hirr' : IrreducibleSpace (PrimeSpectrum ((K ⊗[A] T) ⊗[K] L)) :=
    (irreducibleSpace_primeSpectrum_congr (e4.trans (e3.trans (e2.symm.trans e1.symm)))).mpr
      hirrL
  have hirrK : IrreducibleSpace (PrimeSpectrum (K ⊗[A] T)) :=
    have := hirr'
    irreducibleSpace_primeSpectrum_of_injective
      (algebraMap (K ⊗[A] T) ((K ⊗[A] T) ⊗[K] L))
      (Algebra.TensorProduct.includeLeft_injective (S := K ⊗[A] T) hKL)
  exact (irreducibleSpace_primeSpectrum_congr
    (Algebra.TensorProduct.comm A K T).toRingEquiv).mp hirrK

/-- **The geometrically irreducible fibre locus is compatible with base change.** A prime of `R`
whose contraction to `A` lies in the geometrically irreducible fibre locus of `T` lies in the
geometrically irreducible fibre locus of the base change `R ⊗[A] T`, the two fibres at a
field-valued point agreeing by `Algebra.fibreTensorEquiv`.

This is the converse direction to
`Algebra.mem_geometricallyIrreducibleFibreLocus_comap_of_injective` and the analogue for
irreducibility of `Algebra.mem_geometricallyIntegralFibreLocus_of_isPushout`. -/
theorem mem_geometricallyIrreducibleFibreLocus_tensorProduct_of_comap (q : PrimeSpectrum R)
    (hq : comap (algebraMap A R) q ∈ geometricallyIrreducibleFibreLocus A T) :
    q ∈ geometricallyIrreducibleFibreLocus R (R ⊗[A] T) := by
  intro K _ _ hker
  let _ : Algebra A K := ((algebraMap R K).comp (algebraMap A R)).toAlgebra
  have : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hker' : RingHom.ker (algebraMap A K) = (comap (algebraMap A R) q).asIdeal := by
    show RingHom.ker ((algebraMap R K).comp (algebraMap A R)) = _
    rw [← RingHom.comap_ker, hker, PrimeSpectrum.comap_asIdeal]
  have e : (R ⊗[A] T) ⊗[R] K ≃+* T ⊗[A] K :=
    (Algebra.TensorProduct.comm R (R ⊗[A] T) K).toRingEquiv.trans
      (fibreTensorEquiv A T R K).symm
  exact (irreducibleSpace_primeSpectrum_congr e).mpr (hq K hker')

end Descent

/-! ## The generic fibre as an algebra over the fraction field -/

/-- **The generic fibre of a geometrically irreducible generic point is geometrically
irreducible.** If the generic point of `Spec D`, for a domain `D`, lies in the geometrically
irreducible fibre locus of `T`, then the base change of `T` to a fraction field `F` of `D` is a
geometrically irreducible `F`-algebra.

This is the companion for irreducibility of
`Algebra.isGeometricallyReduced_fractionRing_tensorProduct`. Every field extension of `F` is a
field over `D` whose structure map has kernel `(0)`, so the hypothesis applies to it, and the fibre
there is the base change of the generic fibre by `Algebra.fibreTensorEquiv`. -/
theorem isGeometricallyIrreducible_fractionRing_tensorProduct {D T : Type u} [CommRing D]
    [IsDomain D] [CommRing T] [Algebra D T] (F : Type u) [Field F] [Algebra D F]
    [IsFractionRing D F]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T) :
    IsGeometricallyIrreducible F (F ⊗[D] T) := by
  rw [isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  intro κ _ _
  have hbot : comap (algebraMap D F) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F) =
      ⟨⊥, Ideal.isPrime_bot⟩ :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (IsFractionRing.injective D F))
  exact mem_geometricallyIrreducibleFibreLocus_tensorProduct_of_comap _ (hbot ▸ hgen) κ
    ((RingHom.injective_iff_ker_eq_bot _).mp (algebraMap F κ).injective)

/-- **A geometrically integral generic fibre puts the generic point in the geometrically integral
fibre locus.** For a domain `D` with fraction field `F`, if the base change `F ⊗[D] T` is a
geometrically integral `F`-algebra then the generic point of `Spec D` lies in the geometrically
integral fibre locus of `T`.

A field `κ` over `D` with `ker (D → κ) = (0)` has its structure map factoring through `F` by
`IsFractionRing.lift`, and the fibre `T ⊗[D] κ` is then the base change of the generic fibre along
`F → κ`. -/
theorem mem_geometricallyIntegralFibreLocus_bot_of_isGeometricallyIntegral (D T F : Type u)
    [CommRing D] [IsDomain D] [CommRing T] [Algebra D T] [Field F] [Algebra D F]
    [IsFractionRing D F] (h : IsGeometricallyIntegral F (F ⊗[D] T)) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIntegralFibreLocus D T := by
  intro κ _ _ hker
  have hinj : Function.Injective (algebraMap D κ) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr (by simpa using hker)
  let _ : Algebra F κ := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower D F κ := IsScalarTower.of_algebraMap_eq fun d =>
    (IsFractionRing.lift_algebraMap hinj d).symm
  have hdom := (isGeometricallyIntegral_iff_isDomain_tensorProduct F (F ⊗[D] T)).mp h κ
  exact (isDomain_congr (fibreTensorEquiv D T F κ)).mpr
    ((isDomain_congr (Algebra.TensorProduct.comm F (F ⊗[D] T) κ).toRingEquiv).mp hdom)

/-! ## The locus depends only on the reduction of the algebra -/

/-- **Irreducibility of a fibre is insensitive to an ideal of nilpotents.** For an ideal `I` of
nilpotents of an `A`-algebra `C` and any `A`-algebra `K`, the fibres `(C ⧸ I) ⊗[A] K` and
`C ⊗[A] K` have simultaneously irreducible spectra: the first is the quotient of the second by the
ideal generated by the image of `I`, which consists of nilpotents, so the two spectra are
homeomorphic. -/
theorem irreducibleSpace_primeSpectrum_quotient_tensorProduct_iff (A C : Type u) [CommRing A]
    [CommRing C] [Algebra A C] (I : Ideal C) (hI : I ≤ nilradical C) (K : Type u) [CommRing K]
    [Algebra A K] :
    IrreducibleSpace (PrimeSpectrum ((C ⧸ I) ⊗[A] K)) ↔
      IrreducibleSpace (PrimeSpectrum (C ⊗[A] K)) := by
  have hJnil : Ideal.map (algebraMap C (C ⊗[A] K)) I ≤ nilradical (C ⊗[A] K) := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun x hx =>
      mem_nilradical.mpr ((mem_nilradical.mp (hI hx)).map (algebraMap C (C ⊗[A] K)))
  have e : (C ⧸ I) ⊗[A] K ≃+* (C ⊗[A] K) ⧸ Ideal.map (algebraMap C (C ⊗[A] K)) I :=
    (Algebra.TensorProduct.quotientTensorEquiv (R := A) (S := A) (T := K) (A := C) I).toRingEquiv
  exact (irreducibleSpace_primeSpectrum_congr e).trans <|
    irreducibleSpace_primeSpectrum_iff_of_isEmbedding
      (Ideal.Quotient.mk (Ideal.map (algebraMap C (C ⊗[A] K)) I))
      (PrimeSpectrum.isEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective)
      (by rwa [Ideal.mk_ker])

/-- **The geometrically irreducible fibre locus only sees the reduction of the algebra.** Dividing
an `A`-algebra by an ideal of nilpotents does not change its geometrically irreducible fibre
locus. -/
theorem geometricallyIrreducibleFibreLocus_quotient_of_le_nilradical (A C : Type u) [CommRing A]
    [CommRing C] [Algebra A C] (I : Ideal C) (hI : I ≤ nilradical C) :
    geometricallyIrreducibleFibreLocus A (C ⧸ I) = geometricallyIrreducibleFibreLocus A C := by
  ext p
  exact ⟨fun h K _ _ hker =>
      (irreducibleSpace_primeSpectrum_quotient_tensorProduct_iff A C I hI K).mp (h K hker),
    fun h K _ _ hker =>
      (irreducibleSpace_primeSpectrum_quotient_tensorProduct_iff A C I hI K).mpr (h K hker)⟩

/-! ## From a basic open upstairs to a basic open downstairs -/

/-- **A nonempty basic open of `Spec R` descends to one of `Spec A` along a homeomorphism of
spectra.** Let `A` and `R` be domains, let `Spec R → Spec A` be a homeomorphism and let
`S ⊆ Spec A` and `S' ⊆ Spec R` be subsets with every point of `S'` contracting into `S`. Then a
nonzero `f : R` with `D(f) ⊆ S'` produces a nonzero `g : A` with `D(g) ⊆ S`.

The image of `D(f)` is open because the map is a homeomorphism, it is nonempty because `R` is a
domain and `f ≠ 0`, and it lies in `S`; `PrimeSpectrum.exists_ne_zero_basicOpen_subset_iff_isOpen`
turns a nonempty open subset of the spectrum of a domain into a nonempty basic open. -/
theorem exists_ne_zero_basicOpen_subset_of_comap_isHomeomorph {A R : Type u} [CommRing A]
    [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R]
    (hhom : IsHomeomorph (comap (algebraMap A R))) {S : Set (PrimeSpectrum A)}
    {S' : Set (PrimeSpectrum R)} (hmono : ∀ q ∈ S', comap (algebraMap A R) q ∈ S) {f : R}
    (hf0 : f ≠ 0) (hf : (basicOpen f : Set (PrimeSpectrum R)) ⊆ S') :
    ∃ g : A, g ≠ 0 ∧ (basicOpen g : Set (PrimeSpectrum A)) ⊆ S := by
  refine (PrimeSpectrum.exists_ne_zero_basicOpen_subset_iff_isOpen S).mpr
    ⟨comap (algebraMap A R) '' (basicOpen f : Set (PrimeSpectrum R)), ?_, ?_, ?_⟩
  · exact hhom.isOpenMap _ (basicOpen f).isOpen
  · exact ⟨_, Set.mem_image_of_mem _
      ((mem_basicOpen f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)).mpr (by simpa using hf0))⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact hmono q (hf hq)

/-- **A universal homeomorphism of affine schemes is a homeomorphism of spectra.** This reads the
scheme-level conclusion of
`Stacks.Cover0550.exists_finite_universalHomeomorphic_spec_extension` as a statement about
`PrimeSpectrum.comap`. -/
theorem isHomeomorph_comap_of_universalHomeomorphism_specMap {A R : Type u} [CommRing A]
    [CommRing R] [Algebra A R]
    (h : AlgebraicGeometry.UniversalHomeomorphism
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    IsHomeomorph (comap (algebraMap A R)) :=
  h.universally_isHomeomorph _ _ _ CategoryTheory.IsPullback.of_id_snd


/-! ## The transport half of step 1 of the First proof of Stacks 0559 -/

/-- **The irreducible good half of the generic-fibre dichotomy descends through a universally
homeomorphic cover of the base.** Let `D` be a domain and `T` a finite type `D`-algebra. Suppose
given a Noetherian domain `D'` over `D` for which `Spec D' → Spec D` is a homeomorphism and for
which the reduced base change `(D' ⊗[D] T)_red` has geometrically integral generic fibre. Then the
conclusion of the irreducible good half for `T` over `D` follows from that half in the
geometrically integral case.

This is the first step of the First proof of Stacks 0559 — *"choose a diagram as in Lemma 0550; the
generic fibre of `f'` is the reduction of the generic fibre of `f` and hence is geometrically
irreducible; suppose the lemma holds for `f'`"* — with the three transports it needs carried out:
the locus is unchanged by passing to the reduction
(`Algebra.geometricallyIrreducibleFibreLocus_quotient_of_le_nilradical`, the affine case of the
relevant direction of Stacks 0555), it descends along a base extension injective on spectra
(`Algebra.mem_geometricallyIrreducibleFibreLocus_comap_of_injective`), and a nonempty basic open
upstairs produces one downstairs
(`Algebra.exists_ne_zero_basicOpen_subset_of_comap_isHomeomorph`).

What is **not** proved here is that such a `D'` exists, which is the ring-theoretic content of
Stacks 0550: see the implementation notes of this file. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_cover
    (hgood : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIntegralFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T)
    {D T : Type u} [CommRing D] [IsDomain D] [CommRing T] [Algebra D T] [Algebra.FiniteType D T]
    (D' : Type u) [CommRing D'] [IsDomain D'] [IsNoetherianRing D'] [Algebra D D']
    (hhom : IsHomeomorph (comap (algebraMap D D')))
    (hinteg : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D') ∈
      geometricallyIntegralFibreLocus D' ((D' ⊗[D] T) ⧸ nilradical (D' ⊗[D] T))) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyIrreducibleFibreLocus D T := by
  obtain ⟨f, hf0, hf⟩ := hgood D' ((D' ⊗[D] T) ⧸ nilradical (D' ⊗[D] T)) hinteg
  rw [geometricallyIrreducibleFibreLocus_quotient_of_le_nilradical D' (D' ⊗[D] T) _ le_rfl] at hf
  exact exists_ne_zero_basicOpen_subset_of_comap_isHomeomorph hhom
    (fun q hq => mem_geometricallyIrreducibleFibreLocus_comap_of_injective hhom.injective q hq)
    hf0 hf


/-- **The same reduction with separability of the function field of the new generic fibre in place
of geometric integrality of it.** This is the form the rest of the First proof of Stacks 0559
consumes, and it needs no reduction of the base change at all: what the proof uses after the cover
is that the function field `L` of the generic fibre is a *separable* extension of the fraction
field, since that is what produces a separating transcendence basis (Stacks 030Q) and hence the
hypersurface model whose fibres
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible`
handles.

Here `F'` is a fraction field of the cover `D'` and the function field in question is the residue
field of the nilradical of the generic fibre `F' ⊗[D'] (D' ⊗[D] T)`, which is prime because that
fibre has irreducible spectrum.

Note that `algebraMap D D'` is injective automatically: `PrimeSpectrum.comap` is surjective, so
the generic point of `Spec D` is a contraction, and the kernel is contained in it. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_cover_separable
    (hgood : ∀ (D T F : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T] [Field F] [Algebra D F] [IsFractionRing D F]
      [(nilradical (F ⊗[D] T)).IsPrime],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T →
      IsSeparableExtension F (nilradical (F ⊗[D] T)).ResidueField →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T)
    {D T : Type u} [CommRing D] [IsDomain D] [CommRing T] [Algebra D T] [Algebra.FiniteType D T]
    (D' F' : Type u) [CommRing D'] [IsDomain D'] [IsNoetherianRing D'] [Algebra D D'] [Field F']
    [Algebra D' F'] [IsFractionRing D' F']
    (hhom : IsHomeomorph (comap (algebraMap D D')))
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T)
    (hprime : (nilradical (F' ⊗[D'] (D' ⊗[D] T))).IsPrime)
    (hsep : letI := hprime
      IsSeparableExtension F' (nilradical (F' ⊗[D'] (D' ⊗[D] T))).ResidueField) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyIrreducibleFibreLocus D T := by
  obtain ⟨q₀, hq₀⟩ := hhom.surjective (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D)
  have hinj : Function.Injective (algebraMap D D') := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : x ∈ Ideal.comap (algebraMap D D') q₀.asIdeal :=
      Ideal.mem_comap.mpr (RingHom.mem_ker.mp hx ▸ q₀.asIdeal.zero_mem)
    rwa [show Ideal.comap (algebraMap D D') q₀.asIdeal = (⊥ : Ideal D) from
      congrArg PrimeSpectrum.asIdeal hq₀] at hx'
  have hbot : comap (algebraMap D D') (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D') =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) :=
    PrimeSpectrum.ext ((RingHom.ker_eq_comap_bot (algebraMap D D')).symm.trans
      ((RingHom.injective_iff_ker_eq_bot _).mp hinj))
  have hgen' : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D') ∈
      geometricallyIrreducibleFibreLocus D' (D' ⊗[D] T) :=
    mem_geometricallyIrreducibleFibreLocus_tensorProduct_of_comap _ (hbot ▸ hgen)
  have := hprime
  obtain ⟨f, hf0, hf⟩ := hgood D' (D' ⊗[D] T) F' hgen' hsep
  exact exists_ne_zero_basicOpen_subset_of_comap_isHomeomorph hhom
    (fun q hq => mem_geometricallyIrreducibleFibreLocus_comap_of_injective hhom.injective q hq)
    hf0 hf

end Algebra

end
