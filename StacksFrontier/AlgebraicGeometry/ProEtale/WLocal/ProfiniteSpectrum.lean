module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.LocalIso
public import Mathlib.RingTheory.SurjectiveOnStalks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Jacobson.Constructions
public import StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField

/-!
# Profiniteness of a spectrum goes up along ring maps

Let `A → B` be a homomorphism of commutative rings whose source has profinite prime spectrum.
The prime spectrum of `B` is then profinite as soon as the induced extensions of residue fields
are algebraic, and in particular whenever the map is weakly étale, a local isomorphism, or
identifies local rings. Profiniteness also passes to a filtered colimit of rings with profinite
spectra.

## Main results

* `AlgebraicGeometry.ProEtale.primeSpectrum_isProfinite_of_isAlgebraic_residueField`: algebraic
  residue field extensions preserve profiniteness of spectra.
* `AlgebraicGeometry.ProEtale.primeSpectrum_isProfinite_of_weaklyEtale`: a weakly étale algebra
  over a ring with profinite spectrum has profinite spectrum.
* `AlgebraicGeometry.ProEtale.primeSpectrum_isProfinite_of_isLocalIso`: the same for a local
  isomorphism.
* `AlgebraicGeometry.ProEtale.primeSpectrum_isProfinite_of_identifiesLocalRings`: the same for
  an algebra that identifies local rings.
* `AlgebraicGeometry.ProEtale.primeSpectrum_isProfinite_of_directLimit`: the direct limit of a
  directed system of rings with profinite spectra has profinite spectrum.

## Implementation notes

As in `spec_profinite_tfae`, profiniteness is stated in property form: compactness,
Hausdorffness, and total disconnectedness. The algebra structure on each residue field extension
is the canonical one induced by the ring homomorphism. In the weakly étale case the ring
homomorphism is presented by an algebra structure and weak étaleness by Mathlib's
`Algebra.WeaklyEtale`.

The local isomorphism and identifies-local-rings cases both reduce to the algebraic residue
field case through `RingHom.SurjectiveOnStalks`: if `A_{𝔭} → B_𝔮` is surjective for every prime
`𝔮` of `B` with `𝔭 = 𝔮 ∩ A`, then `κ(𝔭) → κ(𝔮)` is bijective by
`RingHom.SurjectiveOnStalks.residueFieldMap_bijective`, so the residue field extension is
trivial and in particular algebraic. That is the source's own route, which derives both cases
from the algebraic residue field case. Local isomorphisms are taken in Mathlib's spelling
`Algebra.IsLocalIso` (Tag 096E part (1)) and "identifies local rings" in the spelling
`Algebra.IdentifiesLocalRings` (Tag 096E part (2)).

`Algebra.IsLocalIso` asks, for every prime `𝔮` of `B`, for some `g ∉ 𝔮` making `B_g` a
localization of `A` away from an element of `A`, where the source asks only that
`Spec(B_g) → Spec(A)` be an open immersion. The two agree: a localization away from an element
is an open immersion, and conversely the image of an open immersion contains a basic open
`D(r)` around the point of `𝔮`, whose preimage is `D(gr)`, so replacing `g` by `gr` makes the
comparison a localization of `A` away from `r`. Both conditions are local at `𝔮`, which is what
licenses the shrinking.

The filtered colimit case is stated for a directed system over a nonempty directed preorder with
`Ring.DirectLimit` as the colimit, matching the spelling of `IsFilteredColimitOfEtale`, and the
colimit is compared to the ring in question by a ring isomorphism. Two deliberate departures
from the source's shape, both generalizations: the base ring `A` is absent, and the hypothesis
on each stage is that its spectrum be profinite rather than that it be an `A`-algebra as in the
earlier cases. Those earlier cases conclude exactly that the stage has profinite spectrum and
the source's proof of the colimit case uses nothing else about the stages, so applying one of
them at each stage recovers the source's statement. The proof is algebraic rather than the
source's passage to a limit of topological spaces: `Spec` of a ring is profinite exactly when
there is no strict inclusion between its primes, and an inclusion of primes of the colimit
contracts to an inclusion of primes at every stage, where it collapses; since every element of
the colimit comes from some stage, the two primes agree.

## References

* [Stacks Project, Tag 0978](https://stacks.math.columbia.edu/tag/0978)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

/-- A ring map inducing algebraic extensions on residue fields preserves profiniteness of
prime spectra. -/
@[stacks 0978 "algebraic_residue_fields"]
theorem primeSpectrum_isProfinite_of_isAlgebraic_residueField
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hA : CompactSpace (PrimeSpectrum A) ∧ T2Space (PrimeSpectrum A) ∧
      TotallyDisconnectedSpace (PrimeSpectrum A))
    (halg : ∀ q : Ideal B, ∀ [q.IsPrime],
      letI := (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap f).ResidueField q.ResidueField) :
    CompactSpace (PrimeSpectrum B) ∧ T2Space (PrimeSpectrum B) ∧
      TotallyDisconnectedSpace (PrimeSpectrum B) := by
  apply (spec_profinite_tfae B).out 6 1 |>.mp
  intro q hq
  have hmaxA : ∀ p : Ideal A, p.IsPrime → p.IsMaximal := ((spec_profinite_tfae A).out 1 6).mp hA
  have hcomapMax : (q.comap f).IsMaximal := hmaxA (q.comap f) (Ideal.comap_isPrime f q)
  let instAlg : Algebra (q.comap f).ResidueField q.ResidueField :=
    (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
  have hqalg : Algebra.IsAlgebraic (q.comap f).ResidueField q.ResidueField := halg q
  exact isMaximal_of_isAlgebraic_residueField f (m := q.comap f) (q := q) rfl
    (by simp [instAlg, RingHom.algebraMap_toAlgebra])

/-- A weakly étale algebra over a ring with profinite prime spectrum has profinite prime
spectrum. -/
@[stacks 0978 "weakly_etale"]
theorem primeSpectrum_isProfinite_of_weaklyEtale
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B]
    (hA : CompactSpace (PrimeSpectrum A) ∧ T2Space (PrimeSpectrum A) ∧
      TotallyDisconnectedSpace (PrimeSpectrum A)) :
    CompactSpace (PrimeSpectrum B) ∧ T2Space (PrimeSpectrum B) ∧
    TotallyDisconnectedSpace (PrimeSpectrum B) :=
  primeSpectrum_isProfinite_of_isAlgebraic_residueField
    (f := algebraMap A B) hA (fun q _ => (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale
      A B inferInstance (q.comap (algebraMap A B)) q rfl).2)

/-- A ring map that is surjective on stalks over a ring with profinite prime spectrum has
target with profinite prime spectrum: surjectivity on stalks makes every residue field
extension bijective, hence algebraic. -/
theorem primeSpectrum_isProfinite_of_surjectiveOnStalks
    {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.SurjectiveOnStalks)
    (hA : CompactSpace (PrimeSpectrum A) ∧ T2Space (PrimeSpectrum A) ∧
      TotallyDisconnectedSpace (PrimeSpectrum A)) :
    CompactSpace (PrimeSpectrum B) ∧ T2Space (PrimeSpectrum B) ∧
      TotallyDisconnectedSpace (PrimeSpectrum B) := by
  refine primeSpectrum_isProfinite_of_isAlgebraic_residueField f hA fun q _ => ?_
  let _ := (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := (hf.residueFieldMap_bijective (q.comap f) q rfl).surjective x
  have hy : Ideal.ResidueField.map (q.comap f) q f rfl y =
      algebraMap (q.comap f).ResidueField q.ResidueField y := by
    rw [RingHom.algebraMap_toAlgebra]
  rw [hy]
  exact isAlgebraic_algebraMap y

/-- An algebra that identifies local rings is surjective on stalks: the defining bijections of
local rings are in particular surjective. -/
theorem surjectiveOnStalks_of_identifiesLocalRings {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hid : Algebra.IdentifiesLocalRings A B) :
    (algebraMap A B).SurjectiveOnStalks :=
  fun q _ => (hid q).surjective

/-- A local isomorphism is surjective on stalks. Given a prime `𝔮` of `B`, choose `g ∉ 𝔮` with
`B_g` a localization of `A` away from some `a : A`. Every `s : B` becomes, in `B_g`, a fraction
with numerator from `A` and denominator a power of the image of `a`, and `a` does not map into
`𝔮` because its image in `B_g` is a unit. -/
theorem surjectiveOnStalks_of_isLocalIso (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsLocalIso A B] : (algebraMap A B).SurjectiveOnStalks := by
  intro q hq
  rw [RingHom.surjective_localRingHom_iff]
  obtain ⟨g, hgq, hstd⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := A) q
  obtain ⟨a, ha⟩ := Algebra.IsStandardOpenImmersion.exists_away A (Localization.Away g)
  have hfa : algebraMap A B a ∉ q := by
    intro hmem
    have hu : IsUnit (algebraMap B (Localization.Away g) (algebraMap A B a)) := by
      rw [← IsScalarTower.algebraMap_apply A B (Localization.Away g)]
      exact IsLocalization.Away.algebraMap_isUnit a
    obtain ⟨k, c, hc⟩ := (IsLocalization.Away.algebraMap_isUnit_iff g).mp hu
    exact hgq (hq.mem_of_pow_mem k (hc ▸ Ideal.mul_mem_right c q hmem))
  intro s
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj a (algebraMap B (Localization.Away g) s)
  rw [IsScalarTower.algebraMap_apply A B (Localization.Away g) a,
    IsScalarTower.algebraMap_apply A B (Localization.Away g) x, ← map_pow, ← map_mul] at hx
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq g hx
  refine ⟨x, a ^ n, g ^ m, fun h => hgq (hq.mem_of_pow_mem m h), ?_, ?_⟩
  · rw [map_pow]
    exact fun h => hfa (hq.mem_of_pow_mem n h)
  · rw [map_pow]
    linear_combination hm

/-- An algebra identifying local rings over a ring with profinite prime spectrum has profinite
prime spectrum. -/
@[stacks 0978 "identifies_local_rings"]
theorem primeSpectrum_isProfinite_of_identifiesLocalRings
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (hid : Algebra.IdentifiesLocalRings A B)
    (hA : CompactSpace (PrimeSpectrum A) ∧ T2Space (PrimeSpectrum A) ∧
      TotallyDisconnectedSpace (PrimeSpectrum A)) :
    CompactSpace (PrimeSpectrum B) ∧ T2Space (PrimeSpectrum B) ∧
      TotallyDisconnectedSpace (PrimeSpectrum B) :=
  primeSpectrum_isProfinite_of_surjectiveOnStalks
    (surjectiveOnStalks_of_identifiesLocalRings hid) hA

/-- A local isomorphism over a ring with profinite prime spectrum has target with profinite
prime spectrum. -/
@[stacks 0978 "local_isomorphism"]
theorem primeSpectrum_isProfinite_of_isLocalIso
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsLocalIso A B]
    (hA : CompactSpace (PrimeSpectrum A) ∧ T2Space (PrimeSpectrum A) ∧
      TotallyDisconnectedSpace (PrimeSpectrum A)) :
    CompactSpace (PrimeSpectrum B) ∧ T2Space (PrimeSpectrum B) ∧
      TotallyDisconnectedSpace (PrimeSpectrum B) :=
  primeSpectrum_isProfinite_of_surjectiveOnStalks (surjectiveOnStalks_of_isLocalIso A B) hA

/-- If every element of a ring `B` lies in the image of one of a family of ring maps
`φ i : G i → B` whose sources have profinite prime spectra, then `Spec B` is profinite. An
inclusion of primes of `B` contracts along each `φ i` to an inclusion of primes of `G i`, where
it collapses; the covering hypothesis then forces the two primes of `B` to agree. -/
theorem primeSpectrum_isProfinite_of_forall_exists_mem_range
    {B : Type*} [CommRing B] {ι : Type*} (G : ι → Type*) [∀ i, CommRing (G i)]
    (φ : ∀ i, G i →+* B) (hcover : ∀ b : B, ∃ i, b ∈ Set.range (φ i))
    (hG : ∀ i, CompactSpace (PrimeSpectrum (G i)) ∧ T2Space (PrimeSpectrum (G i)) ∧
      TotallyDisconnectedSpace (PrimeSpectrum (G i))) :
    CompactSpace (PrimeSpectrum B) ∧ T2Space (PrimeSpectrum B) ∧
      TotallyDisconnectedSpace (PrimeSpectrum B) := by
  refine ((spec_profinite_tfae B).out 5 1).mp ?_
  intro q q' hq hq' hle
  refine le_antisymm hle fun b hb => ?_
  obtain ⟨i, y, rfl⟩ := hcover b
  have hinc : ∀ p p' : Ideal (G i), p.IsPrime → p'.IsPrime → p ≤ p' → p = p' :=
    ((spec_profinite_tfae (G i)).out 1 5).mp (hG i)
  exact (hinc _ _ (hq.comap _) (hq'.comap _) (Ideal.comap_mono hle)).ge (Ideal.mem_comap.mpr hb)

/-- A filtered colimit of rings with profinite prime spectra has profinite prime spectrum: here
the colimit is the direct limit of a directed system over a nonempty directed preorder, and the
ring `B` is presented as that colimit by a ring isomorphism. -/
@[stacks 0978 "filtered_colimit"]
theorem primeSpectrum_isProfinite_of_directLimit
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type*) [∀ i, CommRing (G i)] (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => (f i j h : G i → G j)]
    (hG : ∀ i, CompactSpace (PrimeSpectrum (G i)) ∧ T2Space (PrimeSpectrum (G i)) ∧
      TotallyDisconnectedSpace (PrimeSpectrum (G i)))
    (B : Type*) [CommRing B]
    (e : B ≃+* Ring.DirectLimit G fun i j h => (f i j h : G i → G j)) :
    CompactSpace (PrimeSpectrum B) ∧ T2Space (PrimeSpectrum B) ∧
      TotallyDisconnectedSpace (PrimeSpectrum B) := by
  refine primeSpectrum_isProfinite_of_forall_exists_mem_range G
    (fun i => (e.symm : _ →+* B).comp
      (Ring.DirectLimit.of G (fun i j h => (f i j h : G i → G j)) i)) (fun b => ?_) hG
  obtain ⟨i, y, hy⟩ := Ring.DirectLimit.exists_of (e b)
  exact ⟨i, y, by simp [hy]⟩

end AlgebraicGeometry.ProEtale
