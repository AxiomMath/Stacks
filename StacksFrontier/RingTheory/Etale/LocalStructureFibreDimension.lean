module

public import StacksFrontier.RingTheory.Etale.LocalStructure
public import StacksFrontier.RingTheory.QuasiFinite.Basic
public import StacksFrontier.Topology.Dimension.LocalKrullDim
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibre dimension after the étale-local decomposition of a finite type algebra

Let `R → S` be of finite type and let `p` be a prime of `R`. After an étale base change
`R → R'` at a prime `p'` over `p` with `κ(p) = κ(p')`, the base change `R' ⊗[R] S` splits
into finitely many factors finite over `R'`, each with a single prime over `p'`, and a
remaining factor. This module records that the fibre of the remaining factor has no
zero-dimensional irreducible component: every irreducible component of it has dimension at
least one.

## Main results

* `Algebra.exists_etale_finite_factors_positiveDim_remainder` is the decomposition with the
  dimension statement for the remaining factor.

## Implementation notes

The decomposition itself is
`Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt`, whose last
clause says that the remaining factor is quasi-finite over `R'` at no prime over `p'`. That
clause is converted here into the dimension statement: an irreducible component of the fibre
of dimension zero has a generic point which is an isolated point of the fibre, and a prime
at which the fibre is zero-dimensional is a prime of quasi-finiteness.

The product decomposition is represented by complete orthogonal idempotents in the
base-changed algebra, the factor cut out by an idempotent being the localization away from
it.

## References

* [Stacks Project, Tag 03QE](https://stacks.math.columbia.edu/tag/03QE)
-/

@[expose] public section

universe u v

open TensorProduct

namespace Algebra

/-- An element of `WithBot ℕ∞` other than `⊥` which is not at least `1` is zero. -/
private lemma eq_zero_of_not_one_le_withBotENat (d : WithBot ℕ∞) (hd : d ≠ ⊥)
    (h : ¬ (1 : WithBot ℕ∞) ≤ d) : d = 0 := by
  obtain ⟨n, rfl⟩ := WithBot.ne_bot_iff_exists.mp hd
  have hn : n = 0 := Order.lt_one_iff.mp
    (lt_of_not_ge (fun h1 => h (WithBot.coe_le_coe.mpr h1)))
  simp [hn]

/-- Quasi-finiteness at a prime of a localization away from an element descends to the
prime it contracts to, the two local rings being canonically isomorphic. -/
private lemma qf_of_localization_away {R A D : Type*} [CommRing R] [CommRing A] [CommRing D]
    [Algebra R A] [Algebra R D] [Algebra A D] [IsScalarTower R A D] (a : A)
    [IsLocalization.Away a D] (qD : Ideal D) [hqD : qD.IsPrime]
    (hqf : Algebra.QuasiFiniteAt R qD) :
    Algebra.QuasiFiniteAt R (Ideal.comap (algebraMap A D) qD) := by
  let qA : Ideal A := Ideal.comap (algebraMap A D) qD
  have : qA.IsPrime := Ideal.comap_isPrime _ _
  have hloc : IsLocalization qA.primeCompl (Localization.AtPrime qD) := by
    simpa [qA] using IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers a) (S := D) (T := Localization.AtPrime qD) qD
  let e : Localization.AtPrime qA ≃ₐ[A] Localization.AtPrime qD :=
    IsLocalization.algEquiv qA.primeCompl _ _
  exact (Algebra.QuasiFinite.iff_of_algEquiv (e.restrictScalars R)).mpr hqf

/-- The local dimension at the generic point of an irreducible component, computed over the
irreducible components through it, is the dimension of that component. -/
private lemma iSup_topologicalKrullDim_eq_of_isGenericPoint {X : Type*} [TopologicalSpace X]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) {x : X} (hx : IsGenericPoint x Z) :
    (⨆ W ∈ {W ∈ irreducibleComponents X | x ∈ W}, topologicalKrullDim W) =
      topologicalKrullDim Z := by
  apply le_antisymm
  · refine iSup₂_le ?_
    rintro W ⟨hWc, hxW⟩
    have hsub : Z ⊆ W :=
      (hx.mem_closed_set_iff (isClosed_of_mem_irreducibleComponents W hWc)).mp hxW
    rw [Set.Subset.antisymm (hZ.2 hWc.1 hsub) hsub]
  · exact le_iSup_of_le Z (le_iSup_of_le ⟨hZ, hx.mem⟩ le_rfl)

/-- A point of the fibre of a finite type algebra at which the fibre is zero-dimensional is
an isolated point of the fibre. -/
private lemma isOpen_singleton_of_topologicalKrullDimAt_eq_zero {R D : Type*} [CommRing R]
    [CommRing D] [Algebra R D] [Algebra.FiniteType R D] (p : Ideal R) [hp : p.IsPrime]
    (x : PrimeSpectrum (p.Fiber D))
    (hdimx : topologicalKrullDimAt (PrimeSpectrum (p.Fiber D)) x = 0) :
    IsOpen ({x} : Set (PrimeSpectrum (p.Fiber D))) := by
  let e := PrimeSpectrum.preimageHomeomorphFiber R D ⟨p, hp⟩
  let y := e.symm x
  let qPair := (PrimeSpectrum.primesOverOrderIsoFiber R D p).symm x
  let qD : Ideal D := qPair.1
  have hqD : qD.IsPrime := qPair.2.1
  have : qD.LiesOver p := qPair.2.2
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime qD) :=
    Localization.AtPrime.algebraOfLiesOver p qD
  let y0 : ↥(PrimeSpectrum.comap (algebraMap R D) ⁻¹' {⟨p, hp⟩}) :=
    ⟨⟨qD, hqD⟩, PrimeSpectrum.ext (qD.over_def p).symm⟩
  have hy0 : y = y0 := Subtype.ext (PrimeSpectrum.ext rfl)
  have hdimy : topologicalKrullDimAt
      ↥(PrimeSpectrum.comap (algebraMap R D) ⁻¹' {⟨p, hp⟩}) y = 0 := by
    calc
      _ = topologicalKrullDimAt (PrimeSpectrum (p.Fiber D)) (e y) :=
        topologicalKrullDimAt_eq_of_homeomorph e y
      _ = 0 := by simpa [y] using hdimx
  have hdimy0 : topologicalKrullDimAt
      ↥(PrimeSpectrum.comap (algebraMap R D) ⁻¹' {⟨p, hp⟩}) y0 = 0 := by
    simpa [hy0] using hdimy
  have hopen := ((Algebra.isOpen_singleton_fiber_tfae_of_finiteType
    (R := R) (S := D) p qD).out 4 1).mp hdimy0
  have hopenY : IsOpen ({y0} : Set _) := by
    convert hopen using 1
  have hopeny : IsOpen ({y} : Set _) := by
    simpa [hy0] using hopenY
  simpa [y] using e.isOpen_image.2 hopeny

/-- A prime of the localization away from `a` lying over `p` at which the algebra is
quasi-finite contradicts quasi-finiteness failing at every prime over `p` avoiding `a`. -/
private lemma false_of_quasiFiniteAt_away {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (p : Ideal R) [p.IsPrime] (a : A)
    (hno : ∀ (q : Ideal A) [q.IsPrime], q.LiesOver p → a ∉ q → ¬ Algebra.QuasiFiniteAt R q)
    (qD : Ideal (Localization.Away a)) [qD.IsPrime] [hqD : qD.LiesOver p]
    (hqf : Algebra.QuasiFiniteAt R qD) : False := by
  let qA : Ideal A := Ideal.comap (algebraMap A (Localization.Away a)) qD
  have : qA.IsPrime := Ideal.comap_isPrime _ _
  have hqAavoid : a ∉ qA := by
    show algebraMap A (Localization.Away a) a ∉ qD
    exact qD.notMem_of_isUnit
      (IsLocalization.map_units (Localization.Away a) ⟨a, Submonoid.mem_powers a⟩)
  have hqAover : qA.LiesOver p := by
    refine ⟨?_⟩
    show p = Ideal.under R (Ideal.under A qD)
    rw [Ideal.under_under]
    exact hqD.over
  exact hno qA hqAover hqAavoid
    (qf_of_localization_away (R := R) (A := A) (D := Localization.Away a) a qD hqf)

/-- If an algebra of finite type is quasi-finite at no prime over `p` avoiding `a`, then
every irreducible component of the fibre of the localization away from `a` has dimension at
least one: a zero-dimensional component would give an isolated point of the fibre, hence a
prime of quasi-finiteness. -/
private lemma positive_dim_of_no_quasiFiniteAt {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] (p : Ideal R) [hp : p.IsPrime] (a : A)
    (hno : ∀ (q : Ideal A) [q.IsPrime], q.LiesOver p → a ∉ q → ¬ Algebra.QuasiFiniteAt R q) :
    ∀ Z ∈ irreducibleComponents
      (PrimeSpectrum (p.Fiber (Localization.Away a))), 1 ≤ topologicalKrullDim Z := by
  intro Z hZ
  by_contra hn
  have hdne : topologicalKrullDim Z ≠ ⊥ := fun hb => hZ.1.nonempty.elim fun z hz =>
    ((topologicalKrullDim_eq_bot_iff_isEmpty Z).mp hb).false ⟨z, hz⟩
  have hZdim := eq_zero_of_not_one_le_withBotENat _ hdne hn
  obtain ⟨x, hxgen⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hdimx : topologicalKrullDimAt (PrimeSpectrum (p.Fiber (Localization.Away a))) x = 0 :=
    (TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim _ x).trans <|
      (PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height
        p.ResidueField x).1.trans <|
      (iSup_topologicalKrullDim_eq_of_isGenericPoint hZ hxgen).trans hZdim
  have hopenx := isOpen_singleton_of_topologicalKrullDimAt_eq_zero p x hdimx
  let qPair := (PrimeSpectrum.primesOverOrderIsoFiber R (Localization.Away a) p).symm x
  let qD : Ideal (Localization.Away a) := qPair.1
  have : qD.IsPrime := qPair.2.1
  have : qD.LiesOver p := qPair.2.2
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime qD) :=
    Localization.AtPrime.algebraOfLiesOver p qD
  have hqfF : Algebra.QuasiFiniteAt p.ResidueField x.asIdeal :=
    Algebra.QuasiFiniteAt.of_isOpen_singleton (R := p.ResidueField) x hopenx
  have hqD_eq : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom x.asIdeal = qD := by
    show ((PrimeSpectrum.primesOverOrderIsoFiber R (Localization.Away a) p).symm x :
      Ideal (Localization.Away a)) = _
    exact (PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply p x).symm
  exact false_of_quasiFiniteAt_away p a hno qD
    (Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField p qD x.asIdeal hqD_eq.symm)

/-- After an étale base change preserving the residue field at `p`, a finite type
algebra splits into finitely many finite factors, each with exactly one prime
over `p'`, and a factor whose fibre has no zero-dimensional irreducible
component. -/
@[stacks 03QE, ega "IV 18.12.1" "affine case"]
theorem exists_etale_finite_factors_positiveDim_remainder
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p)
      (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e)
      (r : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (r i).IsPrime) (_ : ∀ i, (r i).LiesOver p'),
      Function.Bijective (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)) ∧
      (∀ i : Fin n, Module.Finite R' (Localization.Away (e i.castSucc))) ∧
      (∀ i : Fin n, e i.castSucc ∉ r i) ∧
      (∀ (i : Fin n) (q : Ideal (R' ⊗[R] S)), q.IsPrime → q.LiesOver p' →
        e i.castSucc ∉ q → q = r i) ∧
      (∀ Z ∈ irreducibleComponents
          (PrimeSpectrum (p'.Fiber (Localization.Away (e (Fin.last n))))),
        1 ≤ topologicalKrullDim Z) := by
  classical
  obtain ⟨R', hR'comm, hR'alg, hR'etale, p', hp', hp'over, n, e, he, r, hrprime, hro,
      hres, hfin, havoid, hunique, hlast⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt
      (R := R) (S := S) p
  exact ⟨R', hR'comm, hR'alg, hR'etale, p', hp', hp'over, n, e, he, r, hrprime, hro,
    hres, hfin, havoid, hunique,
    positive_dim_of_no_quasiFiniteAt (p := p') (e (Fin.last n)) hlast⟩

end Algebra

end
