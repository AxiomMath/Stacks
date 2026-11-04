module

public import StacksFrontier.RingTheory.Cech.GenFamilySystem
public import StacksFrontier.RingTheory.Cech.PairCategory

/-!
# The system of generating families at a presented pair

`Stacks.GenFamily.GenSet A I` is the directed poset of nonempty finite sets of finite generating
families of an ideal `I ⊆ A`, and `Stacks.GenFamily.fam` attaches to each such set `S` the
*product family*: one element chosen from each family of `S`, multiplied. This file specializes
that system to the objects of `Stacks.PairSite.Pair`, where it is the index of the filtered
colimit whose value at `(A₀, I₀)` is the complex `K(A₀, I₀)` of [Stacks, Tag 099D].

Two things become automatic at a pair. The ideal of a pair is finitely generated
(`Stacks.PairSite.Pair.ideal_fg`), so the system is nonempty and hence filtered with no
hypothesis to carry. And a morphism of pairs carries the ideal of the source *onto* the ideal of
the target, which is exactly the hypothesis `J = Ideal.map φ I` that
`Stacks.GenFamily.GenSet.map` wants: so the transport of generating families along a morphism of
pairs needs no side condition, and it is functorial.

## Main definitions

* `Stacks.PairSite.PairGenSet` — the index poset at a pair, with `IsFiltered` and `Nonempty`
  instances.
* `Stacks.PairSite.pairGenMap` — the transport of a finite set of generating families along a
  morphism of pairs.

## Main results

* `Stacks.PairSite.pairGenMap_monotone`, `Stacks.PairSite.pairGenMap_id`,
  `Stacks.PairSite.pairGenMap_comp` — the transport is monotone and functorial on the nose.
* `Stacks.PairSite.exists_dvd_fam_of_le` and `Stacks.PairSite.exists_dvd_map_fam` — the two
  divisibility facts: along `S ≤ T` the product family of `S` divides the product family of `T`,
  and along a morphism of pairs the image of the product family of `S` divides a power of the
  product family of the image of `S`.

## Implementation notes

The two divisibility statements are restatements of `Stacks.GenFamily.fam_dvd_of_le` and
`Stacks.GenFamily.map_fam_dvd` with an existential quantifier over the exponent: the first with
exponent `1`, the second with exponent `S.carrier.card`, which is genuinely needed because the
transport of generating families need not be injective on `S.carrier` and the image product can
then repeat factors.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.PairSite

open Stacks.GenFamily

/-! ### The index poset at a pair -/

/-- **The index system at a presented pair**: the nonempty finite sets of finite generating
families of the pair's ideal, ordered by inclusion. -/
abbrev PairGenSet (P : Pair.{u}) : Type u := GenSet P.ring P.ideal

/-- The index system at a pair is nonempty. -/
instance instNonemptyPairGenSet (P : Pair.{u}) : Nonempty (PairGenSet P) :=
  GenSet.nonempty P.ideal_fg

/-- The index system at a pair is filtered. -/
instance instIsFilteredPairGenSet (P : Pair.{u}) : IsFiltered (PairGenSet P) :=
  GenSet.isFiltered P.ideal_fg

/-! ### Transport along a morphism of pairs -/

/-- **The transport of generating families along a morphism of pairs.** A morphism of pairs
carries the ideal of the source onto the ideal of the target, so the image of a generating family
is a generating family and no side condition is needed. -/
def pairGenMap {P Q : Pair.{u}} (f : P ⟶ Q) : PairGenSet P → PairGenSet Q :=
  GenSet.map f.toRingHom f.map_ideal

/-- The transport of generating families is monotone. -/
theorem pairGenMap_monotone {P Q : Pair.{u}} (f : P ⟶ Q) : Monotone (pairGenMap f) :=
  GenSet.map_monotone f.toRingHom f.map_ideal

/-- The transport of generating families along the identity is the identity. -/
@[simp]
theorem pairGenMap_id (P : Pair.{u}) (S : PairGenSet P) : pairGenMap (𝟙 P) S = S :=
  GenSet.map_id S (Pair.Hom.map_ideal (𝟙 P))

/-- The transport of generating families is functorial. -/
theorem pairGenMap_comp {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) (S : PairGenSet P) :
    pairGenMap g (pairGenMap f S) = pairGenMap (f ≫ g) S :=
  GenSet.map_map f.toRingHom g.toRingHom f.map_ideal g.map_ideal (f ≫ g).map_ideal S

/-! ### The divisibility data -/

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Along `S ≤ T`, each element of the product family of `S` divides some power of the
corresponding element of the product family of `T`. -/
theorem exists_dvd_fam_of_le {S T : GenSet A I} (h : S ≤ T) (k : Fin (famCard T)) :
    ∃ n : ℕ, fam S (idxLe h k) ∣ fam T k ^ n :=
  ⟨1, by simpa using fam_dvd_of_le h k⟩

/-- Along a ring map `φ`, the image under `φ` of each element of the product family of `S`
divides some power of the corresponding element of the product family of the image of `S`. -/
theorem exists_dvd_map_fam {B : Type u} [CommRing B] {J : Ideal B} (φ : A →+* B)
    (hJ : J = Ideal.map φ I) (S : GenSet A I) (k : Fin (famCard (GenSet.map φ hJ S))) :
    ∃ n : ℕ, φ (fam S (idxMap φ hJ S k)) ∣ fam (GenSet.map φ hJ S) k ^ n :=
  ⟨S.carrier.card, map_fam_dvd φ hJ S k⟩

/-- For any `S T : GenSet A I`, the ideals spanned by the product families of `S` and of `T`
have the same zero locus. -/
theorem zeroLocus_span_range_fam_eq {S T : GenSet A I} :
    PrimeSpectrum.zeroLocus ((Ideal.span (Set.range (fam S)) : Ideal A) : Set A) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range (fam T)) : Ideal A) : Set A) := by
  rw [zeroLocus_span_range_fam, zeroLocus_span_range_fam]

end Stacks.PairSite

end
