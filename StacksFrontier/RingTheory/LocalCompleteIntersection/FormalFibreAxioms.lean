module

public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FlatAscent

/-!
# Being a local complete intersection is a property of formal fibres

[Stacks, Tag 0BJP] asserts that the five properties (A), (B), (C), (D), (E) of
[Stacks, Tag 0BIR] hold for `P(k → R) = `"`R` is a local complete intersection"
([Stacks, Tag 09Q3]). For a property `P` of ring maps from a field to a Noetherian ring these
read:

* (A) `P(k → R)` implies `P(k' → R ⊗_k k')` for finitely generated field extensions `k'/k`;
* (B) `P(k → R_𝔭)` for all `𝔭 ∈ Spec(R)` if and only if `P(k → R)`;
* (C) given flat maps `A → B → C` of Noetherian rings, if the fibres of `A → B` have `P` and
  `B → C` is regular, then the fibres of `A → C` have `P`;
* (D) given flat maps `A → B → C` of Noetherian rings, if the fibres of `A → C` have `P` and
  `B → C` is faithfully flat, then the fibres of `A → B` have `P`;
* (E) given `k → k' → R` with `R` Noetherian, if `k'/k` is separable algebraic and `P(k → R)`,
  then `P(k' → R)`.

Here "`P` holds for the fibres of `A → B`" means that `P` holds for
`κ(𝔮) → B ⊗_A κ(𝔮)` for every prime `𝔮` of `A`.

Each clause is proved separately and the five are conjoined in
`localCompleteIntersectionProperty_satisfies_formalFiberAxioms`, which is the tag whole.

## Main results

* `localCompleteIntersectionProperty_fieldExtension` — **[Stacks, Tag 0BJP]**, clause (A).
* `localCompleteIntersectionProperty_localization` — **[Stacks, Tag 0BJP]**, clause (B).
* `localCompleteIntersectionProperty_regularAscent` — **[Stacks, Tag 0BJP]**, clause (C).
* `localCompleteIntersectionProperty_faithfullyFlatDescent` — **[Stacks, Tag 0BJP]**,
  clause (D).
* `localCompleteIntersectionProperty_groundFieldExtension` — **[Stacks, Tag 0BJP]**, clause (E).
* `localCompleteIntersectionProperty_satisfies_formalFiberAxioms` — **the whole of
  [Stacks, Tag 0BJP]**: clauses (A)--(E) conjoined.

## The argument

Clause (A) is the source's: a finitely generated field extension `K/k` is the field of fractions
of a global complete intersection `C` over `k`, the base change `R → R ⊗_k C` is a relative
global complete intersection ([Stacks, Tag 07BV] for `C`, [Stacks, Tag 00SS] for the base
change), hence syntomic, so `R ⊗_k C` is a local complete intersection ring by the flat
criterion [Stacks, Tag 09Q7], and `R ⊗_k K` is a localization of it. This is
`LocalCompleteIntersection.isLocalCompleteIntersectionRing_tensorProduct_of_essFiniteType`.

Clause (B) is the source's "a ring is a local complete intersection if and only if all of its
local rings are complete intersections": one direction is [Stacks, Tag 09Q4], that a localization
of a complete intersection at a prime is a complete intersection, and the other is that a
Noetherian local ring which is a local complete intersection ring is a complete intersection,
being its own localization at its maximal ideal. Together they are
`LocalCompleteIntersection.isLocalCompleteIntersectionRing_iff_forall_localization`.

Clause (C) rests on the flat ascent
`LocalCompleteIntersection.isLocalCompleteIntersectionRing_of_flat_of_fiber`: the fibre of
`A → C` at a prime `𝔭` is the base change `D = (κ(𝔭) ⊗_A B) ⊗_B C` of the fibre of `A → B` along
`B → C`, which is flat, so the claim reduces to the fibres of `κ(𝔭) ⊗_A B → D`. At a prime `Q` of
`κ(𝔭) ⊗_A B` lying over `𝔮 ⊆ B` that fibre is `κ(Q) ⊗_{κ(𝔮)} (κ(𝔮) ⊗_B C)`; the extension
`κ(𝔮) → κ(Q)` is bijective, so the geometric regularity of `κ(𝔮) → κ(𝔮) ⊗_B C` makes it regular,
hence a local complete intersection.

Clause (D) is the faithfully flat descent of [Stacks, Tag 09Q7], already available as
`LocalCompleteIntersection.isLocalCompleteIntersectionRing_of_faithfullyFlat`: the same base
change `D` is faithfully flat over `κ(𝔭) ⊗_A B` and isomorphic to the fibre of `A → C`.

Clause (E) holds because the condition does not refer to the ground field at all.

## Implementation notes

The five clauses are stated through the `RingMapProperty` interface and a hypothesis `hP`
identifying the property with `LocalCompleteIntersection.IsLocalCompleteIntersectionRing` of the
target, exactly as `cohenMacaulayProperty_satisfies_formalFiberAxioms` ([Stacks, Tag 0BJ9]) and
`Dualizing.gorensteinProperty_satisfies_formalFiberAxioms` ([Stacks, Tag 0BJN]) state the same
five clauses for Cohen--Macaulayness and for Gorensteinness, so that the three instances are
comparable. Two reasons: the fibre ring `κ(𝔭) ⊗_A B` is Noetherian by a theorem rather than by
instance inference, so `IsLocalCompleteIntersectionRing` cannot be written down for it without an
auxiliary `letI`, while `P` is a predicate on ring maps and needs none; and clause (E), whose
content is that the property does not mention the ground field, is a statement about two
different ring maps `k → R` and `k' → R` with the same target, which the interface expresses and
a direct formulation would collapse to a tautology.

`IsCompleteIntersectionRing` asks for a presenting regular local ring in the same universe as the
ring, so all the rings of the statement live in one universe, as they do in the Cohen--Macaulay
and Gorenstein instances.

`iteratedFiberRingEquiv` identifies the fibre of a base change; the copies in
`StacksFrontier/RingTheory/FormalFibres/Examples.lean` and in the Gorenstein development are both
private to their files.

## References

* [Stacks Project, Tag 0BJP](https://stacks.math.columbia.edu/tag/0BJP)
* [Stacks Project, Tag 0BIR](https://stacks.math.columbia.edu/tag/0BIR)
* [Stacks Project, Tag 09Q3](https://stacks.math.columbia.edu/tag/09Q3)
* [Stacks Project, Tag 09Q4](https://stacks.math.columbia.edu/tag/09Q4)
* [Stacks Project, Tag 09Q7](https://stacks.math.columbia.edu/tag/09Q7)
* [Stacks Project, Tag 07BV](https://stacks.math.columbia.edu/tag/07BV)
* [Stacks Project, Tag 0BJ9](https://stacks.math.columbia.edu/tag/0BJ9)
* [Stacks Project, Tag 0BJN](https://stacks.math.columbia.edu/tag/0BJN)
-/

@[expose] public section

open IsLocalRing LocalCompleteIntersection

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The fibre of `E → E ⊗_B C` at a prime `Q` of `E` lying over the prime `𝔮` of `B` is the
iterated fibre `κ(Q) ⊗_{κ(𝔮)} (κ(𝔮) ⊗_B C)`. -/
private noncomputable def iteratedFiberRingEquiv
    {B E C : Type*} [CommRing B] [CommRing E] [CommRing C]
    [Algebra B E] [Algebra B C] (q : Ideal B) [q.IsPrime]
    (Q : Ideal E) [Q.IsPrime] [Q.LiesOver q]
    [Algebra q.ResidueField Q.ResidueField]
    [IsScalarTower B q.ResidueField Q.ResidueField] :
    Q.Fiber (E ⊗[B] C) ≃+*
      Q.ResidueField ⊗[q.ResidueField] q.Fiber C :=
  (Algebra.TensorProduct.cancelBaseChange B E Q.ResidueField
      Q.ResidueField C).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange B q.ResidueField Q.ResidueField
      Q.ResidueField C).symm.toRingEquiv

/-- **Stacks Project, Tag 0BJP, clause (A).** Being a local complete intersection is preserved by
base change along a finitely generated extension of the ground field. -/
@[stacks 0BJP "(A)"]
public theorem localCompleteIntersectionProperty_fieldExtension (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsLocalCompleteIntersectionRing R) :
    ∀ (k K R : Type u) [Field k] [Field K] [CommRing R] [Algebra k K]
      [Algebra k R] [IsNoetherianRing R] [Algebra.EssFiniteType k K],
      P (algebraMap k R) →
        P (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := K)).toRingHom := by
  intro k K R _ _ _ _ _ _ _ h
  let : Algebra.EssFiniteType R (R ⊗[k] K) := Algebra.EssFiniteType.baseChange k K R
  let : IsNoetherianRing (R ⊗[k] K) := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
  rw [hP] at h
  show P (algebraMap K (R ⊗[k] K))
  rw [hP]
  exact isLocalCompleteIntersectionRing_tensorProduct_of_essFiniteType k R K h

/-- **Stacks Project, Tag 0BJP, clause (B).** Being a local complete intersection can be checked
after localizing at every prime. -/
@[stacks 0BJP "(B)"]
public theorem localCompleteIntersectionProperty_localization (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsLocalCompleteIntersectionRing R) :
    ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      (∀ p : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime p.asIdeal))) ↔
        P (algebraMap k R) := by
  intro k R _ _ _ _
  rw [hP]
  rw [← isLocalCompleteIntersectionRing_iff_forall_localization R]
  exact forall_congr' fun p => hP k (Localization.AtPrime p.asIdeal)

/-- **Stacks Project, Tag 0BJP, clause (C).** For flat maps `A → B → C` of Noetherian rings with
`B → C` regular, if every fibre of `A → B` is a local complete intersection then so is every
fibre of `A → C`.

The fibre of `A → C` at a prime `𝔭` is the base change `D = (κ(𝔭) ⊗_A B) ⊗_B C` of the fibre of
`A → B` along `B → C`, which is flat, so
`LocalCompleteIntersection.isLocalCompleteIntersectionRing_of_flat_of_fiber` reduces the claim to
the fibres of `κ(𝔭) ⊗_A B → D`. At a prime `Q` of `κ(𝔭) ⊗_A B` lying over `𝔮 ⊆ B` that fibre is
`κ(Q) ⊗_{κ(𝔮)} (κ(𝔮) ⊗_B C)`; the extension `κ(𝔮) → κ(Q)` is bijective, so the geometric
regularity of `κ(𝔮) → κ(𝔮) ⊗_B C` makes it regular, hence a local complete intersection. -/
@[stacks 0BJP "(C)"]
public theorem localCompleteIntersectionProperty_regularAscent (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsLocalCompleteIntersectionRing R) :
    ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C)) := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAB hreg p
  let : IsNoetherianRing (p.asIdeal.Fiber B) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
  let D := (p.asIdeal.Fiber B) ⊗[B] C
  let e : D ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
    Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField B (p.asIdeal.Fiber B) C
  let : IsNoetherianRing (p.asIdeal.Fiber C) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
  let : IsNoetherianRing D := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
  have : Module.Flat (p.asIdeal.Fiber B) D := inferInstance
  rw [hP]
  refine isLocalCompleteIntersectionRing_of_ringEquiv (A := D) e.toRingEquiv ?_
  refine isLocalCompleteIntersectionRing_of_flat_of_fiber (R := p.asIdeal.Fiber B) (S := D)
    ((hP _ _).mp (hAB p)) ?_
  intro Q _
  let q : Ideal B := Q.comap (algebraMap B (p.asIdeal.Fiber B))
  let : q.IsPrime := inferInstance
  let : Q.LiesOver q := ⟨rfl⟩
  -- The residue field extension `κ(𝔮) → κ(Q)` and its scalar towers are the canonical ones. The
  -- `Module κ(𝔮) κ(𝔮)` instance is not syntactically `Algebra.toModule`, so `IsScalarTower.left`
  -- does not apply and this instance is supplied by hand.
  let : IsScalarTower q.ResidueField q.ResidueField Q.ResidueField :=
    ⟨fun x y z => mul_smul x y z⟩
  have : Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) := hreg ⟨q, inferInstance⟩
  have hκ : Function.Bijective (algebraMap q.ResidueField Q.ResidueField) :=
    p.asIdeal.surjectiveOnStalks_residueField.baseChange'.residueFieldMap_bijective q Q rfl
  let κe : q.ResidueField ≃ₐ[q.ResidueField] Q.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId q.ResidueField Q.ResidueField) hκ
  let Ee : (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) ≃+*
      (q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    (Algebra.TensorProduct.congr κe.symm (AlgEquiv.refl : q.Fiber C ≃ₐ[q.ResidueField]
      q.Fiber C)).toRingEquiv
  have : IsRegularRing (q.ResidueField ⊗[q.ResidueField] q.Fiber C) := inferInstance
  let : IsRegularRing (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    IsRegularRing.of_ringEquiv
      (R := q.ResidueField ⊗[q.ResidueField] q.Fiber C) Ee.symm
  let Eiter : Q.Fiber D ≃+* (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    iteratedFiberRingEquiv q Q
  let : CommRing (Q.Fiber D) := by
    show CommRing (Q.ResidueField ⊗[p.asIdeal.Fiber B] D)
    exact Algebra.TensorProduct.instCommRing
      (R := p.asIdeal.Fiber B) (A := Q.ResidueField) (B := D)
  exact isLocalCompleteIntersectionRing_of_ringEquiv Eiter.symm
    (isLocalCompleteIntersectionRing_of_isRegularRing
      (Q.ResidueField ⊗[q.ResidueField] q.Fiber C))

/-- **Stacks Project, Tag 0BJP, clause (D).** For flat maps `A → B → C` of Noetherian rings with
`B → C` faithfully flat, if every fibre of `A → C` is a local complete intersection then so is
every fibre of `A → B`.

The fibre of `A → C` at a prime `𝔭` is the base change along `B → C` of the fibre of `A → B`, and
that base change is faithfully flat, so
`LocalCompleteIntersection.isLocalCompleteIntersectionRing_of_faithfullyFlat` applies. -/
@[stacks 0BJP "(D)"]
public theorem localCompleteIntersectionProperty_faithfullyFlatDescent
    (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsLocalCompleteIntersectionRing R) :
    ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
        ∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)) := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAC p
  let D := (p.asIdeal.Fiber B) ⊗[B] C
  let e : D ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
    Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField B (p.asIdeal.Fiber B) C
  let : IsNoetherianRing (p.asIdeal.Fiber C) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
  let : IsNoetherianRing (p.asIdeal.Fiber B) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
  let : IsNoetherianRing D := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
  have : Module.FaithfullyFlat (p.asIdeal.Fiber B) D := inferInstance
  rw [hP]
  refine isLocalCompleteIntersectionRing_of_faithfullyFlat (p.asIdeal.Fiber B) D ?_
  exact isLocalCompleteIntersectionRing_of_ringEquiv e.symm.toRingEquiv ((hP _ _).mp (hAC p))

/-- **Stacks Project, Tag 0BJP, clause (E).** Being a local complete intersection is unchanged
when the ground field is replaced by a separable algebraic extension of it inside the target: the
condition does not refer to the ground field. -/
@[stacks 0BJP "(E)"]
public theorem localCompleteIntersectionProperty_groundFieldExtension (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsLocalCompleteIntersectionRing R) :
    ∀ (k K R : Type u) [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
      [IsNoetherianRing R] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K],
      P (algebraMap k R) → P (algebraMap K R) := by
  intro k K R _ _ _ _ _ _ _ _ _ _ h
  exact (hP K R).mpr ((hP k R).mp h)

/-- **Stacks 0BJP.** The property of a map from a field to a Noetherian ring that its target is a
local complete intersection satisfies properties (A)--(E) of [Stacks, Tag 0BIR]: it is preserved
by finitely generated field extension, is local on the target, passes through a composition of
flat maps when the second map is regular, descends through a faithfully flat second map, and is
unchanged upon replacing the ground field by a separable algebraic extension.

The five clauses are `localCompleteIntersectionProperty_fieldExtension`,
`localCompleteIntersectionProperty_localization`,
`localCompleteIntersectionProperty_regularAscent`,
`localCompleteIntersectionProperty_faithfullyFlatDescent` and
`localCompleteIntersectionProperty_groundFieldExtension`. The shape is that of
`cohenMacaulayProperty_satisfies_formalFiberAxioms` ([Stacks, Tag 0BJ9]) and of
`Dualizing.gorensteinProperty_satisfies_formalFiberAxioms` ([Stacks, Tag 0BJN]). -/
@[stacks 0BJP]
public theorem localCompleteIntersectionProperty_satisfies_formalFiberAxioms
    (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsLocalCompleteIntersectionRing R) :
    (∀ (k K R : Type u) [Field k] [Field K] [CommRing R] [Algebra k K]
      [Algebra k R] [IsNoetherianRing R] [Algebra.EssFiniteType k K],
      P (algebraMap k R) →
        P (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := K)).toRingHom) ∧
    (∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      (∀ p : PrimeSpectrum R,
        P (algebraMap k (Localization.AtPrime p.asIdeal))) ↔ P (algebraMap k R)) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A,
        P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A,
        P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A,
        P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
      ∀ p : PrimeSpectrum A,
        P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) ∧
    (∀ (k K R : Type u) [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
      [IsNoetherianRing R] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K],
      P (algebraMap k R) → P (algebraMap K R)) :=
  ⟨localCompleteIntersectionProperty_fieldExtension P hP,
    localCompleteIntersectionProperty_localization P hP,
    localCompleteIntersectionProperty_regularAscent P hP,
    localCompleteIntersectionProperty_faithfullyFlatDescent P hP,
    localCompleteIntersectionProperty_groundFieldExtension P hP⟩

end
