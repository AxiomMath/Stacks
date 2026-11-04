module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Inputs for the `Y`-half of Tag 0551

`AlgebraicGeometry.SpreadsOutFiniteSeparableResidueExtension Y`, isolated in
`StacksFrontier.AlgebraicGeometry.Etale.FiniteEtaleIrreducibleCover0551`, says that a finite
separable extension `K` of the residue field at the generic point of an irreducible scheme `Y` is
realised by a surjective finite étale cover of a nonempty open of `Y` by an irreducible affine
scheme. The Stacks proof chooses an affine open `U = Spec A` through the generic point, writes
`K = κ(𝔭)[T]/(P)`, spreads `P` out to a monic polynomial over `A`, and shrinks `U` so that
`Spec A[T]/(P) ⟶ Spec A` becomes finite étale and surjective.

This file supplies the three ingredients of that argument which are not about the ring map
`A ⟶ A[T]/(P)` itself (those live in
`StacksFrontier.AlgebraicGeometry.Morphisms.GeometricComponentsFiniteEtale`): the presentation of
`κ(η)` as the residue field of a prime of an affine chart, the computation of the generic fibre of
`A[T]/(P)`, and the irreducibility criterion that makes the cover irreducible.

## Main definitions

* `AlgebraicGeometry.IsAffineOpen.residueFieldIso`: for an affine open `U` of `X` and a prime `q`
  of `Γ(X, U)`, the residue field of `X` at the point of `U` cut out by `q` is the residue field
  of `q`.
* `Stacks.GeometricComponents.adjoinRootFiberAlgEquiv`: the fibre of `R[x]/(f)` over a prime `p`
  of `R` is the finite separable extension `L` of `κ(p)` that `f` was built to present.

## Main results

* `AlgebraicGeometry.IsAffineOpen.evaluation_residueFieldIso_hom`: `residueFieldIso` is
  compatible with evaluation of sections, i.e. it is an isomorphism *of `Γ(X, U)`-algebras*.
* `AlgebraicGeometry.exists_affineOpen_mem_genericPoint_residueFieldIso`: an irreducible scheme
  has an affine open through its generic point, on which the generic point corresponds to a prime
  contained in every prime, with the residue field identification above.
* `Stacks.GeometricComponents.nilradical_eq_of_flat_of_unique_prime_over`: `q₀` is the nilradical
  of `B` when `B` is flat over a ring whose minimal prime `p` is unique and `q₀` is the only prime
  of `B` lying over `p`; hence
  `Stacks.GeometricComponents.irreducibleSpace_primeSpectrum_of_flat_of_unique_prime_over`:
  `Spec B` is irreducible.
* `Stacks.GeometricComponents.eq_of_under_eq_of_field_fiber`: at most one prime of `B` lies over
  `p` when the fibre of `B` at `p` is a field.
* `Stacks.GeometricComponents.irreducibleSpace_primeSpectrum_of_flat_of_field_fiber`: the same
  with the uniqueness hypothesis replaced by the fibre at `p` being a field.
* `Stacks.GeometricComponents.irreducibleSpace_primeSpectrum_adjoinRoot`: the two combined, so
  that `Spec R[x]/(f)` is irreducible for `f` as above.

## References

* [Stacks Project, Tag 0551](https://stacks.math.columbia.edu/tag/0551)
* [Stacks Project, Tag 00HS](https://stacks.math.columbia.edu/tag/00HS)
* [Stacks Project, Tag 030N](https://stacks.math.columbia.edu/tag/030N)
-/

@[expose] public section

open CategoryTheory Polynomial TensorProduct TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry

/-- Evaluation of sections at a point only depends on the point. -/
theorem evaluation_residueFieldCongr {X : Scheme.{u}} (U : X.Opens) {x y : X} (h : x = y)
    (hx : x ∈ U) :
    X.evaluation U x hx ≫ (X.residueFieldCongr h).hom = X.evaluation U y (h ▸ hx) := by
  subst h
  simp

/-- `IsAffineOpen.fromSpec` is an open immersion, so it is an isomorphism on residue fields.

This repeats the instance `AlgebraicGeometry.Scheme.Hom.residueFieldMap` carries, with the point
bound as an element of the scheme `Spec Γ(X, U)` rather than of `PrimeSpectrum Γ(X, U)`: the two
are definitionally equal, but instance search does not see through the coercion. -/
theorem IsAffineOpen.isIso_residueFieldMap_fromSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (q : ↥(Spec Γ(X, U))) :
    IsIso (hU.fromSpec.residueFieldMap q) :=
  inferInstance

/-- **The residue field of an affine chart.** For `U` an affine open of `X` and `q` a prime of
`Γ(X, U)`, the residue field of `X` at the point `hU.fromSpec q` is the residue field of `q`. -/
def IsAffineOpen.residueFieldIso {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (q : PrimeSpectrum Γ(X, U)) :
    X.residueField (hU.fromSpec q) ≅ CommRingCat.of q.asIdeal.ResidueField :=
  letI := hU.isIso_residueFieldMap_fromSpec q
  (asIso (hU.fromSpec.residueFieldMap q)).trans (Scheme.Spec.residueFieldIso Γ(X, U) q)

/-- `IsAffineOpen.residueFieldIso` identifies evaluation of a section at `hU.fromSpec q` with the
image of that section in the residue field of `q`. -/
theorem IsAffineOpen.evaluation_residueFieldIso_hom {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (q : PrimeSpectrum Γ(X, U)) (hq : hU.fromSpec q ∈ U) :
    X.evaluation U (hU.fromSpec q) hq ≫ (hU.residueFieldIso q).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) q.asIdeal.ResidueField) := by
  rw [IsAffineOpen.residueFieldIso, Iso.trans_hom, asIso_hom, ← Category.assoc,
    Scheme.evaluation_naturality hU.fromSpec q hq, hU.fromSpec_app_self]
  simp only [Scheme.evaluation, Category.assoc]
  rw [(Spec Γ(X, U)).presheaf.germ_res_assoc (eqToHom hU.fromSpec_preimage_self) q hq]
  rw [← Scheme.Spec.algebraMap_residueFieldIso_inv_assoc (R := Γ(X, U)) (x := q)
    (h := (Scheme.Spec.residueFieldIso Γ(X, U) q).hom)]
  simp

/-- **An affine chart through the generic point.** An irreducible scheme `Y` has an affine open `U`
containing the generic point `η`, and the prime `p` of `Γ(Y, U)` corresponding to `η` is contained
in every prime of `Γ(Y, U)` — it is the unique minimal prime — and presents `κ(η)` as `κ(p)`
compatibly with evaluation of sections.

This is the chart on which the Stacks proof of Tag 0551 spreads out a monic polynomial presenting
a finite separable extension of `κ(η)`. -/
theorem exists_affineOpen_mem_genericPoint_residueFieldIso (Y : Scheme.{u})
    [IrreducibleSpace Y] :
    ∃ (U : Y.Opens) (hU : IsAffineOpen U) (hη : genericPoint Y ∈ U)
      (p : PrimeSpectrum Γ(Y, U))
      (e : Y.residueField (genericPoint Y) ≅ CommRingCat.of p.asIdeal.ResidueField),
      hU.fromSpec p = genericPoint Y ∧
      (∀ q : PrimeSpectrum Γ(Y, U), p.asIdeal ≤ q.asIdeal) ∧
      Y.evaluation U (genericPoint Y) hη ≫ e.hom =
        CommRingCat.ofHom (algebraMap Γ(Y, U) p.asIdeal.ResidueField) := by
  obtain ⟨U, hU, hη, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := genericPoint Y) (U := ⊤) (by trivial)
  have hirrU : IrreducibleSpace U.toScheme :=
    Subtype.irreducibleSpace ⟨⟨_, hη⟩,
      (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset U.isOpen
        (Set.subset_univ _)⟩
  have hgenU : genericPoint U.toScheme = (⟨genericPoint Y, hη⟩ : U) :=
    Subtype.ext (genericPoint_eq_of_isOpenImmersion U.ι)
  have hirrSpec : IrreducibleSpace (Spec Γ(Y, U)) :=
    hU.isoSpec.hom.homeomorph.irreducibleSpace_iff.mp hirrU
  have hfp : hU.fromSpec (hU.primeIdealOf ⟨genericPoint Y, hη⟩) = genericPoint Y :=
    hU.fromSpec_primeIdealOf _
  refine ⟨U, hU, hη, hU.primeIdealOf ⟨genericPoint Y, hη⟩,
    (Y.residueFieldCongr hfp.symm).trans (hU.residueFieldIso _), hfp, ?_, ?_⟩
  · have hpgen : hU.primeIdealOf ⟨genericPoint Y, hη⟩ = genericPoint (Spec Γ(Y, U)) := by
      rw [IsAffineOpen.primeIdealOf, ← hgenU]
      exact genericPoint_eq_of_isOpenImmersion hU.isoSpec.hom
    intro q
    rw [hpgen]
    exact (PrimeSpectrum.le_iff_specializes _ q).mpr
      ((genericPoint_spec (Spec Γ(Y, U))).specializes (Set.mem_univ q))
  · rw [Iso.trans_hom, ← Category.assoc, evaluation_residueFieldCongr U hfp.symm hη]
    exact hU.evaluation_residueFieldIso_hom _ _

end AlgebraicGeometry

namespace Stacks.GeometricComponents

/-- **The generic fibre of `R[x]/(f)`.** If `f : R[X]` is monic and its image in `κ(p)[X]` is the
minimal polynomial of a generator `β` of a finite separable extension `L` of `κ(p)`, then the
fibre `κ(p) ⊗[R] R[x]/(f)` of `R[x]/(f)` over `p` is `L`.

The map sends `1 ⊗ x` to `β`; it is surjective because `β` generates `L`, and injective because
source and target both have dimension `f.natDegree` over `κ(p)` — the source on the power basis
of `R[x]/(f)`, the target because `f` maps to the minimal polynomial of `β`. -/
def adjoinRootFiberAlgEquiv
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] {f : R[X]} (hf : f.Monic)
    {L : Type u} [Field L] [Algebra p.ResidueField L] [Module.Finite p.ResidueField L]
    [Algebra R L] [IsScalarTower R p.ResidueField L] {β : L}
    (hfmap : f.map (algebraMap R p.ResidueField) = minpoly p.ResidueField β)
    (hβ : IntermediateField.adjoin p.ResidueField {β} = ⊤) :
    p.Fiber (AdjoinRoot f) ≃ₐ[p.ResidueField] L := by
  have hβint : IsIntegral p.ResidueField β := Algebra.IsIntegral.isIntegral β
  have hβ0 : f.eval₂ (↑(Algebra.ofId R L) : R →+* L) β = 0 := by
    have h : Polynomial.aeval β f = 0 := by
      rw [← Polynomial.aeval_map_algebraMap p.ResidueField β f, hfmap, minpoly.aeval]
    simpa [Polynomial.aeval_def] using h
  set Φ : p.Fiber (AdjoinRoot f) →ₐ[p.ResidueField] L :=
    Algebra.TensorProduct.lift (Algebra.ofId p.ResidueField L)
      (AdjoinRoot.liftAlgHom f (Algebra.ofId R L) β hβ0) (fun _ _ => Commute.all _ _) with hΦ
  have hroot : Φ (1 ⊗ₜ AdjoinRoot.root f) = β := by
    rw [hΦ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AdjoinRoot.liftAlgHom_root]
  have hadj : Algebra.adjoin p.ResidueField ({β} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβint.isAlgebraic, hβ,
      IntermediateField.top_toSubalgebra]
  have hsurj : Function.Surjective Φ := by
    rw [← AlgHom.range_eq_top]
    refine top_le_iff.mp ?_
    rw [← hadj]
    exact Algebra.adjoin_le (by simpa using ⟨_, hroot⟩)
  have hb : Module.Basis (Fin f.natDegree) p.ResidueField (p.Fiber (AdjoinRoot f)) :=
    Algebra.TensorProduct.basis p.ResidueField (AdjoinRoot.powerBasisAux' hf)
  have hfin : Module.Finite p.ResidueField (p.Fiber (AdjoinRoot f)) := .of_basis hb
  have h1 : Module.finrank p.ResidueField (p.Fiber (AdjoinRoot f)) = f.natDegree := by
    rw [Module.finrank_eq_card_basis hb, Fintype.card_fin]
  have h2 : Module.finrank p.ResidueField L = f.natDegree := by
    rw [← IntermediateField.finrank_top' (F := p.ResidueField) (E := L), ← hβ,
      IntermediateField.adjoin.finrank hβint, ← hfmap, hf.natDegree_map]
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Φ.toLinearMap) (by rw [h1, h2])).mpr hsurj
  exact AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩

/-- A prime ideal contained in every prime ideal is the nilradical. -/
theorem nilradical_eq_of_le_primes {B : Type u} [CommRing B] (q₀ : Ideal B) [q₀.IsPrime]
    (hle : ∀ q : Ideal B, q.IsPrime → q₀ ≤ q) : nilradical B = q₀ := by
  refine le_antisymm (nilradical_le_prime q₀) ?_
  rw [nilradical, Ideal.radical_eq_sInf]
  exact le_sInf fun _ hJ => hle _ hJ.2

/-- **The nilradical from a single fibre.** Let `B` be flat over `A`, let `p` be a prime of `A`
contained in every prime of `A` — equivalently, the unique minimal prime — and suppose `q₀` is the
only prime of `B` lying over `p`. Then `q₀` is the nilradical of `B`.

Flatness gives going down (Tag 00HS), so every minimal prime of `B` lies over `p` and is therefore
equal to `q₀`; hence `q₀` is contained in every prime of `B`. -/
theorem nilradical_eq_of_flat_of_unique_prime_over
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] (hp : ∀ q : Ideal A, q.IsPrime → p ≤ q)
    (q₀ : Ideal B) [q₀.IsPrime]
    (huniq : ∀ q : Ideal B, q.IsPrime → q.under A = p → q = q₀) :
    nilradical B = q₀ := by
  refine nilradical_eq_of_le_primes q₀ fun J hJ => ?_
  obtain ⟨P, hPmin, hPJ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := J) bot_le
  have hPmin : Minimal Ideal.IsPrime P := by
    have h : P ∈ minimalPrimes B := hPmin
    rwa [minimalPrimes_eq_minimals] at h
  have hPprime : P.IsPrime := hPmin.1
  have hover : P.under A = p := by
    obtain ⟨P', hP'P, hP'prime, hP'over⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := P.under A) P
        (hp _ (Ideal.IsPrime.under A P))
    rw [← hPmin.eq_of_le hP'prime hP'P]
    exact hP'over.over.symm
  rw [← huniq P hPprime hover]
  exact hPJ

/-- **Irreducibility from a single fibre.** In the situation of
`nilradical_eq_of_flat_of_unique_prime_over`, `Spec B` is irreducible. -/
theorem irreducibleSpace_primeSpectrum_of_flat_of_unique_prime_over
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] (hp : ∀ q : Ideal A, q.IsPrime → p ≤ q)
    (q₀ : Ideal B) [q₀.IsPrime]
    (huniq : ∀ q : Ideal B, q.IsPrime → q.under A = p → q = q₀) :
    IrreducibleSpace (PrimeSpectrum B) := by
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical,
    nilradical_eq_of_flat_of_unique_prime_over p hp q₀ huniq]
  infer_instance

/-- **A field fibre has at most one prime over `p`.** If the fibre `κ(p) ⊗[A] B` is a field then
any two primes of `B` lying over `p` coincide: a field has a unique prime, and primes of the fibre
correspond to primes of `B` over `p`. -/
theorem eq_of_under_eq_of_field_fiber {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] {F : Type u} [Field F] (e : p.Fiber B ≃+* F)
    (q q' : Ideal B) (hq : q.IsPrime) (hq' : q'.IsPrime)
    (hqp : q.under A = p) (hqp' : q'.under A = p) : q = q' := by
  have hnt : Nontrivial (p.Fiber B) := e.toEquiv.nontrivial
  have hsub : Subsingleton (PrimeSpectrum (p.Fiber B)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e).subsingleton
  set P : PrimeSpectrum A := ⟨p, ‹p.IsPrime›⟩ with hP
  have hfib : Subsingleton (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {P}) :=
    (PrimeSpectrum.preimageEquivFiber A B P).subsingleton
  have hmem : (⟨q, hq⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {P} :=
    PrimeSpectrum.ext hqp
  have hmem' : (⟨q', hq'⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {P} :=
    PrimeSpectrum.ext hqp'
  have heq : (⟨⟨q, hq⟩, hmem⟩ : PrimeSpectrum.comap (algebraMap A B) ⁻¹' {P}) =
      ⟨⟨q', hq'⟩, hmem'⟩ := hfib.elim _ _
  rw [Subtype.ext_iff] at heq
  exact congrArg PrimeSpectrum.asIdeal heq

/-- **Irreducibility from a field fibre.** Variant of
`irreducibleSpace_primeSpectrum_of_flat_of_unique_prime_over` in which the hypothesis that exactly
one prime of `B` lies over `p` is replaced by the fibre `κ(p) ⊗[A] B` being a field. -/
theorem irreducibleSpace_primeSpectrum_of_flat_of_field_fiber
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] (hp : ∀ q : Ideal A, q.IsPrime → p ≤ q)
    {F : Type u} [Field F] (e : p.Fiber B ≃+* F) :
    IrreducibleSpace (PrimeSpectrum B) := by
  have hnt : Nontrivial (p.Fiber B) := e.toEquiv.nontrivial
  set P : PrimeSpectrum A := ⟨p, ‹p.IsPrime›⟩ with hP
  obtain ⟨q₀⟩ : Nonempty (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {P}) :=
    ⟨(PrimeSpectrum.preimageEquivFiber A B P).symm
      (Nonempty.some (inferInstance : Nonempty (PrimeSpectrum (p.Fiber B))))⟩
  have hprime : (q₀.1.asIdeal).IsPrime := q₀.1.2
  have hover : q₀.1.asIdeal.under A = p := congrArg PrimeSpectrum.asIdeal q₀.2
  exact irreducibleSpace_primeSpectrum_of_flat_of_unique_prime_over p hp q₀.1.asIdeal
    fun q hq hqp => eq_of_under_eq_of_field_fiber p e q _ hq hprime hqp hover

/-- **`Spec R[x]/(f)` is irreducible.** Combination of the two previous results with
`adjoinRootFiberAlgEquiv`: for `f` monic presenting a finite separable extension `L` of `κ(p)`
with `p` the unique minimal prime of `R`, the spectrum of `R[x]/(f)` is irreducible, since
`R[x]/(f)` is free hence flat over `R` and its fibre over `p` is the field `L`. -/
theorem irreducibleSpace_primeSpectrum_adjoinRoot
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (hp : ∀ q : Ideal R, q.IsPrime → p ≤ q)
    {f : R[X]} (hf : f.Monic) {L : Type u} [Field L] [Algebra p.ResidueField L]
    [Module.Finite p.ResidueField L] [Algebra R L] [IsScalarTower R p.ResidueField L] {β : L}
    (hfmap : f.map (algebraMap R p.ResidueField) = minpoly p.ResidueField β)
    (hβ : IntermediateField.adjoin p.ResidueField {β} = ⊤) :
    IrreducibleSpace (PrimeSpectrum (AdjoinRoot f)) :=
  have := hf.free_adjoinRoot
  have : Module.Flat R (AdjoinRoot f) := Module.Flat.of_free
  irreducibleSpace_primeSpectrum_of_flat_of_field_fiber p hp
    (adjoinRootFiberAlgEquiv p hf hfmap hβ).toRingEquiv

end Stacks.GeometricComponents

end

end
