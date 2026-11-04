module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute

/-!
# Elementary étale localizations of a ring map

Let `R → S` be a ring map and let `q` be a prime of `S` lying over a prime `p` of `R`. An
*elementary étale localization of `R → S` at `q`* is a commutative square of rings
```
  S ⟶ S'
  ↑    ↑
  R ⟶ R'
```
whose horizontal maps are étale, together with primes `p' ⊆ R'` and `q' ⊆ S'` lying over `p`,
`q` and over each other, such that the induced extensions of residue fields
`κ(p) → κ(p')` and `κ(q) → κ(q')` are isomorphisms.

This is the algebraic translation of an elementary étale neighbourhood of a pointed scheme, and
it is the vocabulary in which Stacks 05I1, 05I4 and 05I5 are stated at the ring level. The
scheme-level notion is `AlgebraicGeometry.EtaleNeighborhood` together with
`AlgebraicGeometry.EtaleNeighborhood.IsElementary` (Stacks 02LE).

## Main definitions

* `Algebra.ElementaryEtaleLocalization R S p q` is an elementary étale localization of `R → S`
  at `q`.

## Main results

* `Algebra.ElementaryEtaleLocalization.self` is the trivial elementary étale localization, given
  by the identity square. In particular the type is always nonempty.

The remaining declarations are the projection API of the definition.

## Implementation notes

The equalities of residue fields in the source are expressed as bijectivity of the canonical
maps `Ideal.ResidueField.map`, rather than as an `IsIso` or an explicit `RingEquiv`, so that no
inverse has to be carried as data.

The three `LiesOver` conditions in the two diagrams are recorded as equalities of ideals rather
than as `Ideal.LiesOver` instances. The square `commutes` only after the two composites
`R → S → S'` and `R → R' → S'` are compared, so there is no canonical `Algebra R S'` structure
to state the lying-over conditions against, and recording them as equalities keeps each one
unambiguous about which algebra structure it refers to. The equalities are nevertheless exported
as `Ideal.LiesOver` instances, where the algebra structure is pinned by the type of the ideal.

The two upper rings have their own universes, independent of those of `R` and `S`; nothing in
the definition forces them to agree.

## References

* [Stacks Project, Tag 05HW](https://stacks.math.columbia.edu/tag/05HW)
* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
-/

@[expose] public section

universe u v w x

/-- An **elementary étale localization** of `R → S` at a prime `q` lying over `p`.

The rings `R'` and `S'`, their structure maps, and `commutes` form the square of the definition.
The primes `p'` and `q'` lie over the indicated primes, and the canonical residue-field maps are
isomorphisms. -/
@[stacks 05HW]
public structure Algebra.ElementaryEtaleLocalization (R : Type u) (S : Type v)
    [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] where
  /-- The lower-right ring. -/
  R' : Type w
  /-- The upper-right ring. -/
  S' : Type x
  [commRingR' : CommRing R']
  [commRingS' : CommRing S']
  [algebraRR' : Algebra R R']
  [algebraSS' : Algebra S S']
  [algebraR'S' : Algebra R' S']
  /-- The square of structure maps commutes. -/
  commutes : (algebraMap S S').comp (algebraMap R S) = (algebraMap R' S').comp (algebraMap R R')
  /-- The lower horizontal map is étale. -/
  etale_R' : Algebra.Etale R R'
  /-- The upper horizontal map is étale. -/
  etale_S' : Algebra.Etale S S'
  /-- The prime in the lower-right ring. -/
  p' : Ideal R'
  /-- The prime in the upper-right ring. -/
  q' : Ideal S'
  /-- The chosen ideal of the lower-right ring is prime. -/
  p'_isPrime : p'.IsPrime
  /-- The chosen ideal of the upper-right ring is prime. -/
  q'_isPrime : q'.IsPrime
  /-- `p'` lies over `p`. -/
  p'_liesOver : p = p'.comap (algebraMap R R')
  /-- `q'` lies over `q`. -/
  q'_liesOver_q : q = q'.comap (algebraMap S S')
  /-- `q'` lies over `p'`. -/
  q'_liesOver_p' : p' = q'.comap (algebraMap R' S')
  /-- The canonical map `κ(p) → κ(p')` is an isomorphism. -/
  residueFieldMap_p_bijective :
    Function.Bijective (Ideal.ResidueField.map p p' (algebraMap R R') p'_liesOver)
  /-- The canonical map `κ(q) → κ(q')` is an isomorphism. -/
  residueFieldMap_q_bijective :
    Function.Bijective (Ideal.ResidueField.map q q' (algebraMap S S') q'_liesOver_q)

namespace Algebra.ElementaryEtaleLocalization

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R}
  {q : Ideal S} [p.IsPrime] [q.IsPrime] [q.LiesOver p]

/-- The ring structure on `E.R'`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : CommRing E.R' := E.commRingR'

/-- The ring structure on `E.S'`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : CommRing E.S' := E.commRingS'

/-- The `R`-algebra structure on `E.R'`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : Algebra R E.R' := E.algebraRR'

/-- The `S`-algebra structure on `E.S'`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : Algebra S E.S' := E.algebraSS'

/-- The `E.R'`-algebra structure on `E.S'`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : Algebra E.R' E.S' := E.algebraR'S'

/-- `E.R'` is étale over `R`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : Algebra.Etale R E.R' := E.etale_R'

/-- `E.S'` is étale over `S`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : Algebra.Etale S E.S' := E.etale_S'

/-- The ideal `E.p'` is prime. -/
public instance (E : ElementaryEtaleLocalization R S p q) : E.p'.IsPrime := E.p'_isPrime

/-- The ideal `E.q'` is prime. -/
public instance (E : ElementaryEtaleLocalization R S p q) : E.q'.IsPrime := E.q'_isPrime

/-- The prime `E.p'` lies over `p`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : E.p'.LiesOver p := ⟨E.p'_liesOver⟩

/-- The prime `E.q'` lies over `q`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : E.q'.LiesOver q := ⟨E.q'_liesOver_q⟩

/-- The prime `E.q'` lies over `E.p'`. -/
public instance (E : ElementaryEtaleLocalization R S p q) : E.q'.LiesOver E.p' :=
  ⟨E.q'_liesOver_p'⟩

/-- The **trivial elementary étale localization**, given by the identity square `R' = R`,
`S' = S`, `p' = p` and `q' = q`. -/
public def self (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R)
    (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    ElementaryEtaleLocalization.{u, u, u, u} R S p q where
  R' := R
  S' := S
  commutes := rfl
  etale_R' := inferInstance
  etale_S' := inferInstance
  p' := p
  q' := q
  p'_isPrime := ‹p.IsPrime›
  q'_isPrime := ‹q.IsPrime›
  p'_liesOver := by simp
  q'_liesOver_q := by simp
  q'_liesOver_p' := Ideal.LiesOver.over
  residueFieldMap_p_bijective :=
    (RingHom.surjectiveOnStalks_of_surjective
      (f := algebraMap R R) (fun r => ⟨r, rfl⟩)).residueFieldMap_bijective p p (by simp)
  residueFieldMap_q_bijective :=
    (RingHom.surjectiveOnStalks_of_surjective
      (f := algebraMap S S) (fun s => ⟨s, rfl⟩)).residueFieldMap_bijective q q (by simp)

/-- An elementary étale localization always exists: the trivial one, `self R S p q`. -/
public instance (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R)
    (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    Nonempty (ElementaryEtaleLocalization.{u, u, u, u} R S p q) :=
  ⟨self R S p q⟩

end Algebra.ElementaryEtaleLocalization

end
