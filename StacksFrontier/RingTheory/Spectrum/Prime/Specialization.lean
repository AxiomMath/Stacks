module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Ideal.GoingUpGoingDown.Defs
public import StacksFrontier.Topology.Specialization.Lifting
import StacksFrontier.Topology.Spectral.ConstructibleProfinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Going up and going down as lifting of specializations along `Spec`
-/

/-!
# Going up and going down

A ring map `f : R →+* S` *satisfies going down* if for every pair of primes `p ≤ q` of `R` and
every prime `Q` of `S` with `f⁻¹(Q) = q` there is a prime `P ≤ Q` of `S` with `f⁻¹(P) = p`, and
*satisfies going up* if for every such pair and every prime `P` of `S` with `f⁻¹(P) = p` there is a
prime `Q ≥ P` of `S` with `f⁻¹(Q) = q`. Equivalently, generalizations resp. specializations lift
along `Spec S → Spec R`, and in that form both properties are visibly stable under composition:
along `R → S → T` a chain of primes of `R` is lifted first to `S` and then to `T`.

The second result is about a base change. Let `k` be a commutative ring whose prime spectrum has at
most one point and let `A`, `B` be `k`-algebras; then `Spec (A ⊗[k] B) → Spec A`, induced by
`a ↦ a ⊗ 1`, is open. Some hypothesis on `k` is needed, and flatness of `A → A ⊗[k] B` is not what
is at work: over `k = A = ℤ` the image of `Spec (ℤ ⊗[ℤ] ℤ ⧸ 2ℤ)` is the closed point `(2)` of
`Spec ℤ` and the image of `Spec (ℤ ⊗[ℤ] ℚ)` is the generic point, neither of them open, while `ℚ`
is flat over `ℤ`.

## Main results

* `RingHom.hasGoingDown_and_hasGoingUp_comp`: going down is stable under composition of ring maps,
  and so is going up.
* `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_subsingleton`: for `k` with at most
  one prime ideal and `k`-algebras `A`, `B`, the map `Spec (A ⊗[k] B) → Spec A` is open.

## Implementation notes

Going down and going up are Mathlib's classes `Algebra.HasGoingDown` and `Algebra.HasGoingUp`,
which are properties of an algebra structure, so a ring map `f : R →+* S` is read through the
algebra structure `f.toAlgebra` it induces, exactly as `RingHom.Flat` reads flatness of a ring map.
For a tower of algebras — `[Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]`, which
pins `algebraMap R T` to `(algebraMap S T).comp (algebraMap R S)` — both assertions are already
available as `Algebra.HasGoingDown.trans` and `Algebra.HasGoingUp.trans`, whose conclusions are
classes and hence reachable by instance synthesis, which a conjunct of an `And` is not. Stated here
is the source's own formulation, for two bare ring maps and the induced structure on the composite;
each formulation yields the other, the tower one by `IsScalarTower.algebraMap_eq` and this one by
`IsScalarTower.of_algebraMap_eq'`.

The hypothesis on the base of the base change is stated topologically, as
`Subsingleton (PrimeSpectrum k)`. For nonzero `k` it says that `k` is local of Krull dimension
zero, i.e. that its nilradical is its maximal ideal, so it admits `ℤ ⧸ 4ℤ` as well as any field;
for a field it holds by instance inference, so the field case,
`PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`, is an instance of the statement
proved here. It is sufficient but not necessary: a finite product of fields has the property too,
by splitting `A ⊗[k] B` into a product along the idempotents of `k`, and its spectrum is not a
point.

Nilpotents in the base are invisible to both spectra, and that is what a subsingleton spectrum buys
over a field: every prime of `k` is the nilradical, so a maximal ideal `m` of `k` satisfies
`m ≤ nilradical k` while `k ⧸ m` is a field. Both `I = m A` and its extension to `A ⊗[k] B` consist
of nilpotent elements, so the two quotient maps induce homeomorphisms on spectra and openness
descends from `A ⧸ I` to `A`, where it is the field case for `k ⧸ m` because `(A ⧸ I) ⊗[k] B` is
`(A ⧸ I) ⊗[k ⧸ m] ((k ⧸ m) ⊗[k] B)`. Only `A` is quotiented, `B` being left alone, so that the
change of base ring is absorbed by a single `Algebra.TensorProduct.cancelBaseChange`. For `k` the
zero ring there is no maximal ideal, and also nothing to prove: `A ⊗[k] B` is the zero ring and its
spectrum is empty.

The base change is written with `A` as the left factor, where the source writes `S ⊗_k R` with `R`
on the right. The left factor is the side carrying the global `Algebra A (A ⊗[k] B)` instance, so
`Spec (A ⊗[k] B) → Spec A` is `PrimeSpectrum.comap (algebraMap A (A ⊗[k] B))` with no local
instance in scope; the two orderings are `Algebra.TensorProduct.comm`-isomorphic, as `R`-algebras
once `Algebra.TensorProduct.rightAlgebra` is granted.

## References

* [Stacks 00HX](https://stacks.math.columbia.edu/tag/00HX)
  (`algebra-lemma-going-up-down-composition`); the translation into lifting of generalizations and
  specializations is Stacks 00HW, whose topological input is Stacks 0064.
* [Stacks 037G](https://stacks.math.columbia.edu/tag/037G)
  (`algebra-lemma-what-does-it-mean`).
-/

@[expose] public section

namespace RingHom

/-- **Stacks 00HX.** If the ring maps `f : R →+* S` and `g : S →+* T` satisfy going down, then so
does `g ∘ f`; likewise for going up. -/
@[stacks 00HX "Both assertions, for a composite of ring maps. For a tower of algebras they are
  `Algebra.HasGoingDown.trans` and `Algebra.HasGoingUp.trans`, which carry this tag as well."]
public theorem hasGoingDown_and_hasGoingUp_comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T) :
    (letI := f.toAlgebra; letI := g.toAlgebra; letI := (g.comp f).toAlgebra;
      Algebra.HasGoingDown R S → Algebra.HasGoingDown S T → Algebra.HasGoingDown R T) ∧
    (letI := f.toAlgebra; letI := g.toAlgebra; letI := (g.comp f).toAlgebra;
      Algebra.HasGoingUp R S → Algebra.HasGoingUp S T → Algebra.HasGoingUp R T) := by
  algebraize [f, g, g.comp f]
  exact ⟨fun _ _ => .trans R S T, fun _ _ => .trans R S T⟩

end RingHom

section BaseChange

open TensorProduct

/-- The extension of an ideal of nilpotent elements along a ring map consists of nilpotent
elements. -/
private theorem map_le_nilradical {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {I : Ideal R} (hI : I ≤ nilradical R) : I.map f ≤ nilradical S :=
  Ideal.map_le_iff_le_comap.2 fun _ hx => mem_nilradical.2 ((mem_nilradical.1 (hI hx)).map f)

/-- If `Spec R` has at most one point, every prime ideal of `R` consists of nilpotent elements,
being the unique prime and hence the nilradical. -/
private theorem le_nilradical_of_isPrime {R : Type*} [CommSemiring R]
    [Subsingleton (PrimeSpectrum R)] (p : Ideal R) [hp : p.IsPrime] : p ≤ nilradical R :=
  nilradical_eq_sInf R ▸ le_sInf fun J hJ => le_of_eq
    (congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (⟨p, hp⟩ : PrimeSpectrum R) ⟨J, hJ⟩))

/-- The quotient by an ideal of nilpotent elements induces a homeomorphism on prime spectra. -/
@[ega "0 16.1.2" "special case", ega "I 1.1.11" "special case", ega "I 1.1.12" "more general"]
private theorem isHomeomorph_comap_quotientMk {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I ≤ nilradical R) : IsHomeomorph (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
  PrimeSpectrum.isHomeomorph_comap _
    (fun x => ⟨1, one_pos, by simpa using Ideal.Quotient.mk_surjective x⟩) (by simpa using hI)

/-- Openness of `Spec` descends along a commutative square of rings `ψ ∘ α = α' ∘ π`: if `Spec α'`
is open, `Spec π` is open and `Spec ψ` is surjective, then `Spec α` is open. -/
private theorem isOpenMap_comap_of_comm_square
    {R S R' S' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring R'] [CommSemiring S']
    {α : R →+* S} {α' : R' →+* S'} {π : R →+* R'} {ψ : S →+* S'}
    (hsq : ψ.comp α = α'.comp π)
    (hπ : IsOpenMap (PrimeSpectrum.comap π))
    (hψ : Function.Surjective (PrimeSpectrum.comap ψ))
    (h : IsOpenMap (PrimeSpectrum.comap α')) :
    IsOpenMap (PrimeSpectrum.comap α) := by
  refine IsOpenMap.of_comp (PrimeSpectrum.continuous_comap ψ) hψ ?_
  rw [← PrimeSpectrum.comap_comp, hsq, PrimeSpectrum.comap_comp]
  exact hπ.comp h

/-- Openness of `Spec α` is preserved by composing with a bijective ring map `e`. -/
private theorem isOpenMap_comap_comp_of_bijective {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {α : R →+* S} {e : S →+* T} (he : Function.Bijective e)
    (h : IsOpenMap (PrimeSpectrum.comap α)) : IsOpenMap (PrimeSpectrum.comap (e.comp α)) := by
  rw [PrimeSpectrum.comap_comp]
  exact h.comp (PrimeSpectrum.isHomeomorph_comap_of_bijective he).isOpenMap

/-- **Openness of `Spec (A ⊗[k] B) → Spec A` only depends on `A` modulo nilpotents.** If an ideal
`I` of `A` consists of nilpotent elements, then `A ⊗[k] B` is, modulo nilpotents,
`(A ⧸ I) ⊗[k] B`, so openness for `A ⧸ I` is openness for `A`. -/
private theorem isOpenMap_comap_algebraMap_tensorProduct_of_le_nilradical
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    {I : Ideal A} (hI : I ≤ nilradical A)
    (h : IsOpenMap (PrimeSpectrum.comap (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[k] B)))) :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (A ⊗[k] B))) := by
  let e : (A ⧸ I) ⊗[k] B ≃ₐ[k] (A ⊗[k] B) ⧸ I.map (algebraMap A (A ⊗[k] B)) :=
    Algebra.TensorProduct.quotientTensorEquiv (R := k) k B A I
  refine isOpenMap_comap_of_comm_square
    (α' := e.toAlgHom.toRingHom.comp (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[k] B)))
    (π := Ideal.Quotient.mk I) (ψ := Ideal.Quotient.mk _) (by ext a; rfl)
    (isHomeomorph_comap_quotientMk hI).isOpenMap
    (isHomeomorph_comap_quotientMk (map_le_nilradical _ hI)).surjective
    (isOpenMap_comap_comp_of_bijective (e := e.toAlgHom.toRingHom) e.bijective h)

/-- The field case of openness for a base change, over a base ring `k` mapping to a field `K` over
which the left factor is an algebra: `Spec (A ⊗[k] B) → Spec A` is open, because `A ⊗[k] B` is
`A ⊗[K] (K ⊗[k] B)`. -/
private theorem isOpenMap_comap_algebraMap_tensorProduct_of_isScalarTower
    {k K A B : Type*} [CommRing k] [Field K] [CommRing A] [CommRing B]
    [Algebra k K] [Algebra k A] [Algebra K A] [IsScalarTower k K A] [Algebra k B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (A ⊗[k] B))) := by
  let e : A ⊗[K] (K ⊗[k] B) ≃ₐ[K] A ⊗[k] B := Algebra.TensorProduct.cancelBaseChange k K K A B
  have he : algebraMap A (A ⊗[k] B)
      = e.toAlgHom.toRingHom.comp (algebraMap A (A ⊗[K] (K ⊗[k] B))) := by
    ext a
    simp [e, Algebra.TensorProduct.one_def]
  rw [he]
  exact isOpenMap_comap_comp_of_bijective (e := e.toAlgHom.toRingHom) e.bijective
    PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field

/-- **Openness of `Spec` of a base change over a base with at most one prime.** Let `k` be a
commutative ring with at most one prime ideal — a field, or more generally a local ring of Krull
dimension zero — and let `A` and `B` be `k`-algebras. Then the map `Spec (A ⊗[k] B) → Spec A` is
open. -/
public theorem PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_subsingleton
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Subsingleton (PrimeSpectrum k)] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (A ⊗[k] B))) := by
  rcases subsingleton_or_nontrivial k with _ | _
  · have : Subsingleton (A ⊗[k] B) := Module.subsingleton k _
    exact .of_isEmpty _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal k
  let _ : Field (k ⧸ m) := Ideal.Quotient.field m
  let I : Ideal A := m.map (algebraMap k A)
  have hI : I ≤ nilradical A := map_le_nilradical _ (le_nilradical_of_isPrime m)
  let _ : Algebra (k ⧸ m) (A ⧸ I) :=
    (Ideal.quotientMap I (algebraMap k A) Ideal.le_comap_map).toAlgebra
  have _ : IsScalarTower k (k ⧸ m) (A ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun _ => Ideal.quotientMap_mk.symm
  exact isOpenMap_comap_algebraMap_tensorProduct_of_le_nilradical hI
    (isOpenMap_comap_algebraMap_tensorProduct_of_isScalarTower (K := k ⧸ m))

end BaseChange

end

/-!
# Going up / going down via lifting of (in)specializations

Let `φ : R → S` be a ring map.

1. `φ` satisfies going down if and only if generalizations lift along the map
   `Spec(S) → Spec(R)`.
2. `φ` satisfies going up if and only if specializations lift along the map
   `Spec(S) → Spec(R)`.

Here `Spec(S) → Spec(R)` is `PrimeSpectrum.comap φ`. "Going up" and "going down"
are the literal ring-map definitions from tag 00HV
(`RingHom.GoingUp` / `RingHom.GoingDown`), and "(in)specializations
lift along a continuous map" is the Topology definition from tag 0063
(`LiftsGeneralizations` / `LiftsSpecializations`).

The argument goes through Mathlib's `GeneralizingMap` / `SpecializingMap`: the literal
going-down/up properties are identified with these, and then transported along the
bridges of tag 0063.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring map satisfies going down (Stacks 00HV (2)) if and only if the induced
map `Spec(S) → Spec(R)` is generalizing in the sense of Mathlib. -/
theorem goingDown_iff_generalizingMap (φ : R →+* S) :
    RingHom.GoingDown φ ↔ GeneralizingMap (PrimeSpectrum.comap φ) := by
  refine ⟨fun h x y hyx ↦ ?_, fun h p p' hp hp' hpp' q' hq' hover ↦ ?_⟩
  · obtain ⟨q, hq, hqle, hover⟩ := h y.asIdeal (Ideal.comap φ x.asIdeal) y.isPrime
      inferInstance ((PrimeSpectrum.le_iff_specializes _ _).mpr hyx) x.asIdeal x.isPrime rfl
    exact ⟨⟨q, hq⟩, (PrimeSpectrum.le_iff_specializes _ _).mp hqle, PrimeSpectrum.ext hover⟩
  · have hspec : (⟨p, hp⟩ : PrimeSpectrum R) ⤳ PrimeSpectrum.comap φ ⟨q', hq'⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (hpp'.trans hover.ge)
    obtain ⟨x', hx'spec, hx'over⟩ := h hspec
    exact ⟨x'.asIdeal, x'.isPrime, (PrimeSpectrum.le_iff_specializes _ _).mpr hx'spec,
      congrArg PrimeSpectrum.asIdeal hx'over⟩

/-- A ring map satisfies going up (Stacks 00HV (1)) if and only if the induced
map `Spec(S) → Spec(R)` is specializing in the sense of Mathlib. -/
theorem goingUp_iff_specializingMap (φ : R →+* S) :
    RingHom.GoingUp φ ↔ SpecializingMap (PrimeSpectrum.comap φ) := by
  refine ⟨fun h x y hxy ↦ ?_, fun h p p' hp hp' hpp' q hq hover ↦ ?_⟩
  · obtain ⟨q', hq', hqle, hover⟩ := h (Ideal.comap φ x.asIdeal) y.asIdeal inferInstance
      y.isPrime ((PrimeSpectrum.le_iff_specializes _ _).mpr hxy) x.asIdeal x.isPrime rfl
    exact ⟨⟨q', hq'⟩, (PrimeSpectrum.le_iff_specializes _ _).mp hqle, PrimeSpectrum.ext hover⟩
  · have hspec : PrimeSpectrum.comap φ ⟨q, hq⟩ ⤳ (⟨p', hp'⟩ : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (hover.le.trans hpp')
    obtain ⟨x', hx'spec, hx'over⟩ := h hspec
    exact ⟨x'.asIdeal, x'.isPrime, (PrimeSpectrum.le_iff_specializes _ _).mpr hx'spec,
      congrArg PrimeSpectrum.asIdeal hx'over⟩

/-- **Stacks 00HW (1).** A ring map `φ : R → S` satisfies going down if and only if
generalizations lift along `Spec(S) → Spec(R)`. -/
@[stacks 00HW "(1)"]
theorem goingDown_iff_liftsGeneralizations (φ : R →+* S) :
    RingHom.GoingDown φ ↔
      LiftsGeneralizations (PrimeSpectrum.comap φ) :=
  (goingDown_iff_generalizingMap φ).trans
    (liftsGeneralizations_iff_generalizingMap _).symm

/-- **Stacks 00HW (2).** A ring map `φ : R → S` satisfies going up if and only if
specializations lift along `Spec(S) → Spec(R)`. -/
@[stacks 00HW "(2)"]
theorem goingUp_iff_liftsSpecializations (φ : R →+* S) :
    RingHom.GoingUp φ ↔
      LiftsSpecializations (PrimeSpectrum.comap φ) :=
  (goingUp_iff_specializingMap φ).trans
    (liftsSpecializations_iff_specializingMap _).symm

end

/-! ### Stacks 00HY

Stacks 00HY — for a ring map `f : R → S`, a specialization-stable image of `Spec S` in
`Spec R` is closed — is Mathlib's `PrimeSpectrum.isClosed_range_of_stableUnderSpecialization`
(and `PrimeSpectrum.stableUnderSpecialization_range_iff`), both already carrying the tag
upstream. -/

/-!
# Going up is equivalent to closedness of the Spec map

Let `φ : R → S` be a ring map. The following are equivalent:

1. going up holds for `φ` (Stacks 00HV (1)), and
2. the induced map `Spec(S) → Spec(R)` is closed.

The closed-implies-going-up direction is general topology: specializations lift
along a closed map (`IsClosedMap.specializingMap`), and going up is exactly the
literal ring-map shadow of `SpecializingMap (PrimeSpectrum.comap φ)` recorded in
Stacks 00HW (`goingUp_iff_specializingMap`).

For the converse, a specializing map carries closed sets to specialization-stable
sets (`SpecializingMap.stableUnderSpecialization_image`), and on `PrimeSpectrum`
a specialization-stable image of a closed set is closed
(`PrimeSpectrum.isClosed_image_of_stableUnderSpecialization`).
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A specializing map between prime spectra of commutative rings is closed.
Combine `SpecializingMap.stableUnderSpecialization_image` with the Mathlib lemma
`PrimeSpectrum.isClosed_image_of_stableUnderSpecialization`. -/
private lemma isClosedMap_comap_of_specializingMap (φ : R →+* S)
    (h : SpecializingMap (PrimeSpectrum.comap φ)) :
    IsClosedMap (PrimeSpectrum.comap φ) := fun Z hZ =>
  PrimeSpectrum.isClosed_image_of_stableUnderSpecialization φ Z hZ
    (h.stableUnderSpecialization_image hZ.stableUnderSpecialization)

/-- **Stacks 00HZ.** For a ring map `φ : R → S`, going up holds if and only if the
induced map `Spec(S) → Spec(R)` is closed. -/
@[stacks 00HZ]
theorem goingUp_iff_isClosedMap_comap (φ : R →+* S) :
    RingHom.GoingUp φ ↔ IsClosedMap (PrimeSpectrum.comap φ) :=
  ⟨fun hGU => isClosedMap_comap_of_specializingMap φ
      ((goingUp_iff_specializingMap φ).mp hGU),
    fun hClosed => (goingUp_iff_specializingMap φ).mpr hClosed.specializingMap⟩

end

/-! ### Stacks 00I0

Stacks 00I0 — a constructible subset of `Spec R` stable under specialization is closed, and one
stable under generalization is open — is Mathlib's
`PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible` and
`PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible`, both already carrying
the tag upstream. -/

@[expose] public section

/-! ### Stacks 00I1

Stacks 00I1 — a finitely presented ring map satisfying going down induces an open map on prime
spectra — is Mathlib's
`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`, which already carries
the tag upstream. The flat specialisation below is kept only because other draft files call it;
it is that Mathlib lemma with `Algebra.HasGoingDown` obtained from flatness. -/

/-- If `R → S` is flat and of finite presentation, then the induced map `Spec S → Spec R`
is open. -/
@[ega "IV 1.10.4" "b) ⇒ a), special case",
  ega "IV 11.3.1" "special case",
  sga "1 IV 6.6" "affine case with F = O_X",
  sga "1 VIII 4.9" "special case",
  sga "3 V 10.1.1" "Remark b), special case",
  sga "3 V 4.1.1" "Openness clause",
  sga "3 VIA 2.1.3" "partial",
  sga "3 X 5.4" "special case",
  sga "3 XVI 2.1" "special case"]
theorem primeSpectrum_comap_isOpenMap_of_flat_of_finitePresentation
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FinitePresentation R S] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) :=
  PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

end

/-!
# An open spectral map satisfies going down

Let `φ : R → S` be a homomorphism of commutative rings. It induces a continuous
map on prime spectra

  `φ* : Spec(S) → Spec(R),  q ↦ φ⁻¹(q)`,

sending a prime ideal `q ⊆ S` to its contraction `φ⁻¹(q) ⊆ R` (in Mathlib this
is `PrimeSpectrum.comap`).

For a prime `q ⊆ S` and a prime `p ⊆ R`, we say that `q` lies over `p` when
`φ⁻¹(q) = p` (equivalently, `φ*(q) = p`).

Definition (Going down). The ring map `φ : R → S` satisfies going down if for all
prime ideals `p ⊆ p'` of `R` and every prime ideal `q' ⊆ S` lying over `p'`, there
exists a prime ideal `q ⊆ S` such that
  1. `q ⊆ q'`, and
  2. `q` lies over `p` (i.e. `φ⁻¹(q) = p`).

Definition (Open map). The map `φ* : Spec(S) → Spec(R)` is open if for every open
subset `U ⊆ Spec(S)`, the image `φ*(U)` is open in `Spec(R)` (in Mathlib this is
`IsOpenMap`). Here `Spec` carries the Zariski topology.

If `φ*` is open, then `φ` satisfies going down.  The notion of going down is the one of
Stacks Tag `00HV` (Definition 10.41.1, part 2).

## Outline

The proof localizes `S` at the prime `q'` and works with `S' := S_{q'}`, writing
`g : S → S'` for the localization map, and splits into two independent pieces.

* `core_mem_range_localization`: the prime `p` lies in the image of
  `comap (g ∘ φ) : Spec S' → Spec R`.  This is where openness of `comap φ` is used: for
  every `t ∉ q'` the basic open `D(t) ⊆ Spec S` has `comap φ '' D(t)` open and containing
  `p'`, hence, `p` being a generization of `p'` and open sets being stable under
  generalization, `p ∈ comap φ '' D(t)`; equivalently the fibre ring `S_t ⊗_R κ(p)` is
  nonzero.  Taking the directed colimit over `t ∉ q'`, where `S_{q'} = colim_t S_t`, gives
  `S_{q'} ⊗_R κ(p) ≠ 0`, that is, `p` lies in the image of `Spec S_{q'} → Spec R`.
* `core_descend_localization`: a prime `P` of `S'` whose contraction along `g ∘ φ` is `p`
  produces a prime `q ≤ q'` of `S` lying over `p`, namely `q := comap g P`.  Indeed
  `comap φ q = comap (g ∘ φ) P = p`, and `q ≤ q'` because
  `Set.range (comap g) = {q | Disjoint q'.primeCompl q.asIdeal} = {q | q ≤ q'}` by
  `PrimeSpectrum.localization_comap_range`.

The main theorem chains the two.
-/

@[expose] public section

open PrimeSpectrum

-- `RingHom.SatisfiesGoingDown`, the going-down property phrased through
-- `PrimeSpectrum.comap`, is imported from
-- `StacksFrontier.RingTheory.Ideal.GoingUpGoingDown.Defs`.

section GoingDownSketch
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

open Topology in
/-- `PrimeSpectrum.comap` of a ring homomorphism is a spectral map: it is continuous
and preimages of compact opens are compact opens. -/
@[ega "I 1.2.3" "more general"]
private theorem isSpectralMap_comap_aux {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) : IsSpectralMap (comap φ) := by
  classical
  refine ⟨continuous_comap φ, fun s hso hsc => ?_⟩
  obtain ⟨T, hT⟩ := (PrimeSpectrum.isCompact_isOpen_iff).mp ⟨hsc, hso⟩
  refine (PrimeSpectrum.isCompact_isOpen_iff.mpr ⟨T.image φ, ?_⟩).1
  rw [← hT, Set.preimage_compl, preimage_comap_zeroLocus, Finset.coe_image]

open Topology in
/-- A spectral map between spectral spaces is continuous for the constructible topologies. -/
private theorem continuous_constr_of_isSpectralMap_aux {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsSpectralMap f) :
    Continuous[constructibleTopology X, constructibleTopology Y] f := by
  rw [continuous_generateFrom_iff]
  rintro s (⟨hso, hsc⟩ | ⟨hsc, hso⟩)
  · exact (hf.isCompact_preimage_of_isOpen hso hsc).isOpen_constructibleTopology_of_isOpen
      (hf.isOpen_preimage _ hso)
  · exact IsCompact.isOpen_constructibleTopology_of_isClosed
      (hf.isCompact_preimage_of_isOpen hsc.isOpen_compl hso) (hsc.preimage hf.continuous)

open Topology in
/-- Each basic open is closed (indeed clopen) in the constructible topology on `Spec S`. -/
private theorem basicOpen_isClosed_constr_aux {S : Type*} [CommRing S] (t : S) :
    IsClosed (X := WithConstructibleTopology (PrimeSpectrum S))
      (WithTopology.ofTopology ⁻¹' (basicOpen t : Set (PrimeSpectrum S))) := by
  rw [basicOpen_eq_zeroLocus_compl, Set.preimage_compl, isClosed_compl_iff]
  exact WithConstructibleTopology.isOpen_iff.mpr <|
    IsCompact.isOpen_constructibleTopology_of_isClosed
      (basicOpen_eq_zeroLocus_compl t ▸ isCompact_basicOpen t) (isClosed_zeroLocus _)

/-- If `comap φ` is open, `p ≤ p'` and `q'` lies over `p'`, then `p` lies in the image of
every basic open `D(t)` with `t ∉ q'`. -/
theorem mem_image_basicOpen_of_isOpenMap (h : IsOpenMap (comap φ)) {p p' : PrimeSpectrum R}
    (hpp' : p ≤ p') {q' : PrimeSpectrum S} (hq' : comap φ q' = p') {t : S}
    (ht : t ∉ q'.asIdeal) : p ∈ comap φ '' (basicOpen t : Set (PrimeSpectrum S)) :=
  (h _ (basicOpen t).isOpen).stableUnderGeneralization ((le_iff_specializes p p').mp hpp')
    ⟨q', ht, hq'⟩

open Topology in
/-- If `comap φ` is open, `p ≤ p'` and `q'` lies over `p'`, then some prime `q ≤ q'` lies
over `p`. -/
theorem exists_le_comap_eq_of_isOpenMap (h : IsOpenMap (comap φ)) {p p' : PrimeSpectrum R}
    (hpp' : p ≤ p') {q' : PrimeSpectrum S} (hq' : comap φ q' = p') :
    ∃ q ≤ q', comap φ q = p := by
  -- Compactness in the constructible topology: produce a single prime
  -- `q ≤ q'` of `S` lying over `p`.  This replaces the directed-colimit argument.
  set M := q'.asIdeal.primeCompl
  let F : Set (PrimeSpectrum S) := {q | comap φ q = p}
  -- Work in the constructible topology on `Spec S` via the `WithConstructibleTopology`
  -- structure wrapper; sets of `PrimeSpectrum S` are transported by `ofTopology ⁻¹'`.
  let C : M → Set (WithConstructibleTopology (PrimeSpectrum S)) :=
    fun t => WithTopology.ofTopology ⁻¹' (F ∩ (basicOpen (t : S) : Set (PrimeSpectrum S)))
  have hFcl : IsClosed (X := WithConstructibleTopology (PrimeSpectrum S))
      (WithTopology.ofTopology ⁻¹' F) := by
    apply WithConstructibleTopology.isClosed_iff.mpr
    have hcont : Continuous[constructibleTopology (PrimeSpectrum S),
        constructibleTopology (PrimeSpectrum R)] (comap φ) :=
      continuous_constr_of_isSpectralMap_aux (isSpectralMap_comap_aux φ)
    have hsingle : IsClosed[constructibleTopology (PrimeSpectrum R)]
        ({p} : Set (PrimeSpectrum R)) := by
      convert WithConstructibleTopology.isClosed_iff.mp
        (isClosed_singleton (X := WithConstructibleTopology (PrimeSpectrum R))
          (x := WithTopology.toTopology _ p)) using 1
      ext r
      simp
    -- goal `IsClosed[constructibleTopology S] (toTopology ⁻¹' (ofTopology ⁻¹' F))` is defeq
    -- to `IsClosed[constructibleTopology S] (comap φ ⁻¹' {p})`.
    exact @IsClosed.preimage (PrimeSpectrum S) (PrimeSpectrum R)
      (constructibleTopology (PrimeSpectrum S)) (constructibleTopology (PrimeSpectrum R))
      (comap φ) hcont {p} hsingle
  have hCcl : ∀ t : M, IsClosed (X := WithConstructibleTopology (PrimeSpectrum S)) (C t) := by
    intro t
    have hcl := hFcl.inter (basicOpen_isClosed_constr_aux (t : S))
    rwa [← Set.preimage_inter] at hcl
  have hFIP : ∀ (I : Finset M), (⋂ t ∈ I, C t).Nonempty := by
    intro I
    let m : S := ∏ t ∈ I, (t : S)
    have hmM : m ∈ M := Submonoid.prod_mem _ (fun t _ => t.property)
    obtain ⟨q, hqB, hqf⟩ := mem_image_basicOpen_of_isOpenMap φ h hpp' hq' hmM
    refine ⟨WithTopology.toTopology _ q,
      Set.mem_iInter₂.mpr fun t htI => ⟨hqf, fun hmem => hqB ?_⟩⟩
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun t : M => (t : S)) htI
    rw [show m = t * r from hr]
    exact Ideal.mul_mem_right _ _ hmem
  obtain ⟨qw, hq⟩ := CompactSpace.iInter_nonempty hCcl hFIP
  simp only [Set.mem_iInter] at hq
  exact ⟨WithTopology.ofTopology qw, fun x hx => by_contra fun hxq' => (hq ⟨x, hxq'⟩).2 hx,
    (hq ⟨1, M.one_mem⟩).1⟩

open Topology in
/-- The algebraic and topological core of the argument.

For the localization `S'` of `S` at the prime `q'` with structure map
`g = algebraMap S S'`, the prime `p` of `R` lies in the range of
`comap (g.comp φ) : Spec S' → Spec R`.

Openness of `comap φ` gives, for every basic open `D(t)` with `t ∉ q'`, that `p` lies in
its `comap`-image, using `p ≤ p'` and the stability of open sets under generalization; the
directed colimit `S_{q'} = colim_{t ∉ q'} S_t` then makes the fibre `S_{q'} ⊗_R κ(p)`
nonzero, which is the claim.  The hypotheses `hq' : comap φ q' = p'` and `hpp' : p ≤ p'`
are what power the step that `p` generizes `p'`. -/
theorem core_mem_range_localization
    (h : IsOpenMap (comap φ)) (p p' : PrimeSpectrum R) (hpp' : p ≤ p')
    (q' : PrimeSpectrum S) (hq' : comap φ q' = p')
    (S' : Type*) [CommRing S'] [Algebra S S']
    [IsLocalization.AtPrime S' q'.asIdeal] :
    p ∈ Set.range (comap ((algebraMap S S').comp φ)) := by
  -- By `comap_comp` and
  -- `PrimeSpectrum.localization_comap_range` (range of `comap (algebraMap S S')`
  -- = `{q | Disjoint q'.asIdeal.primeCompl q.asIdeal}` = `{q | q ≤ q'}`), the goal
  --   `p ∈ range (comap ((algebraMap S S').comp φ))`
  -- is equivalent to `∃ q : PrimeSpectrum S, q ≤ q' ∧ comap φ q = p`, i.e. to the
  -- going-down conclusion itself, so this lemma carries all the content.
  --
  -- The fibre/colimit argument runs as follows.
  --   1. It suffices to show `p ∈ comap φ '' {q : PrimeSpectrum S | q ≤ q'}`
  --      (rewrite the range via `comap_comp`, `Set.range_comp`, and
  --      `PrimeSpectrum.localization_comap_range`; note `{q | q ≤ q'}` matches
  --      `{q | Disjoint q'.asIdeal.primeCompl q.asIdeal}` since a prime is `≤ q'`
  --      iff disjoint from `q'`'s complement).
  --   2. For each `t ∉ q'` (i.e. `t ∈ q'.asIdeal.primeCompl`), the basic open
  --      `D(t) = (PrimeSpectrum.basicOpen t)` is open, so `comap φ '' D(t)` is open
  --      by hypothesis `h : IsOpenMap (comap φ)`. Since `q' ∈ D(t)` (as `t ∉ q'`)
  --      and `comap φ q' = p'`, we get `p' ∈ comap φ '' D(t)`.
  --   3. Open sets are stable under generalization (`IsOpen.stableUnderGeneralization`),
  --      and `p ≤ p'` means `p ⤳ p'`/`p` generizes `p'` (`PrimeSpectrum.le_iff_specializes`),
  --      so `p ∈ comap φ '' D(t)` for every `t ∉ q'`: i.e. for each such `t` there is a
  --      prime `q_t` of `S` with `t ∉ q_t` and `comap φ q_t = p`.
  --   4. Equivalently, the fiber ring `(S_t) ⊗_R κ(p) ≠ 0` for every `t ∉ q'`.
  --      Since `S_{q'} = colim_{t ∉ q'} S_t` (directed colimit; `localization` is the
  --      filtered colimit of the `S_t`), and tensor commutes with filtered colimits
  --      (`TensorProduct.directLimitLeft`, Stacks 00DD/07K0), the
  --      colimit `S_{q'} ⊗_R κ(p)` is nonzero, hence `Spec(S_{q'} ⊗_R κ(p)) ≠ ∅`,
  --      which exactly says `p ∈ range (comap (g ∘ φ))`.
  -- One can also work directly with primes: step 3 gives, for every `t ∉ q'`, a prime
  -- of `S` over `p` missing `t`, and that has to be upgraded to a single prime `q ≤ q'`
  -- over `p` by a compactness argument on the fibre `Spec(κ(p) ⊗_R S)` over the closed
  -- point of `Spec S_{q'}`.
  obtain ⟨q₀, hqle, hqp⟩ := exists_le_comap_eq_of_isOpenMap φ h hpp' hq'
  -- Descend through the localization: `q ≤ q'` puts `q` in the range of
  -- `comap (algebraMap S S')`, and the lift `P` of `q` witnesses `p ∈ range (comap (g ∘ φ))`.
  obtain ⟨P, hP⟩ : q₀ ∈ Set.range (comap (algebraMap S S')) := by
    rw [PrimeSpectrum.localization_comap_range S' q'.asIdeal.primeCompl, Set.mem_ofPred_eq,
      Set.disjoint_left]
    exact fun x hxc hxq => hxc (hqle hxq)
  exact ⟨P, by rw [comap_comp_apply, hP, hqp]⟩

/-- Descent of the prime of the localization back to `S`.

A prime `P` of `S'` (the localization of `S` at `q'`) whose contraction along
`g.comp φ` is `p` yields a prime `q ≤ q'` of `S` with `comap φ q = p`.

Take `q := comap (algebraMap S S') P`. Then:
* `comap φ q = comap ((algebraMap S S').comp φ) P = p` by functoriality of `comap`
  (`comap_comp`) and `hP`;
* `q ≤ q'` because the range of `comap (algebraMap S S')` is exactly the primes of
  `S` disjoint from `q'.asIdeal.primeCompl`, i.e. those `≤ q'`
  (`PrimeSpectrum.localization_comap_range`). -/
theorem core_descend_localization
    (p : PrimeSpectrum R) (q' : PrimeSpectrum S)
    (S' : Type*) [CommRing S'] [Algebra S S']
    [IsLocalization.AtPrime S' q'.asIdeal]
    (P : PrimeSpectrum S') (hP : comap ((algebraMap S S').comp φ) P = p) :
    ∃ q : PrimeSpectrum S, q ≤ q' ∧ comap φ q = p := by
  -- Take `q := comap g P`:
  --   refine ⟨comap (algebraMap S S') P, ?_, ?_⟩
  --   · have hmem : comap (algebraMap S S') P ∈ Set.range (comap (algebraMap S S')) := ⟨P, rfl⟩
  --     rw [PrimeSpectrum.localization_comap_range S' q'.asIdeal.primeCompl] at hmem
  --     show (comap (algebraMap S S') P).asIdeal ≤ q'.asIdeal
  --     intro x hx
  --     by_contra hx'
  --     exact (Set.disjoint_left.mp hmem) hx' hx
  --   · rwa [← comap_comp_apply]
  -- Key lemmas: `PrimeSpectrum.localization_comap_range` (range = primes disjoint
  -- from `q'.primeCompl`, hence `≤ q'`) and `comap_comp_apply` (functoriality).
  refine ⟨comap (algebraMap S S') P, ?_, ?_⟩
  · have hmem : comap (algebraMap S S') P ∈ Set.range (comap (algebraMap S S')) := ⟨P, rfl⟩
    rw [PrimeSpectrum.localization_comap_range S' q'.asIdeal.primeCompl] at hmem
    exact fun x hx => by_contra fun hx' => Set.disjoint_left.mp hmem hx' hx
  · rwa [← comap_comp_apply]

end GoingDownSketch

/-- Stacks Tag 0407 (Lemma 10.41.2): if the induced map on prime spectra
`φ* = PrimeSpectrum.comap φ : Spec(S) → Spec(R)` is an open map, then `φ`
satisfies going down. -/
@[stacks 0407]
theorem isOpenMap_comap_satisfiesGoingDown
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (h : IsOpenMap (comap φ)) : φ.SatisfiesGoingDown :=
  fun _ _ hpp' _ hq' => exists_le_comap_eq_of_isOpenMap φ h hpp' hq'

end
