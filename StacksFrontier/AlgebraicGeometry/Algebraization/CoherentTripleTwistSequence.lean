module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleAssociatedPointsTransfer
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernel
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistBraiding
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistZero

/-!
# The short exact sequences of the induction step of Tag 0F27, in every degree

The third clause of `Stacks.Algebraization.HasHilbertInductionStep` asks for **one** coherent
triple `G` and, for every integer `n`, a short exact sequence

`0 → T ⊗ L^{⊗ n} → T ⊗ L^{⊗ (n + 1)} → G ⊗ L^{⊗ n} → 0`.

The cokernel machinery of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernel` produces a sequence in each
degree separately, with a different quotient in each; this file assembles the clause instead from
the sequence in **one** degree, twisted. Multiplication by a section pair gives a monomorphism
`T ⊗ L^{⊗ 0} ⟶ T ⊗ L^{⊗ 1}` whose cokernel triple is the `G` of the clause; the sequence is moved
to begin at `T` and to have middle term `T ⊗ L` -- that is, to the degree-one sequence
`0 → T → T ⊗ L → G → 0` -- and then twisted by `L^{⊗ n}`, which is exact
(`Stacks.Algebraization.CoherentTriple.ShortExact.twistZ`) and leaves the first and third terms
as the clause wants them. Only the middle term, `(T ⊗ L) ⊗ L^{⊗ n}`, has to be moved again, and
that is the reordering of a double twist,
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccDegreeOneHom`.

## Main definitions

* `Stacks.Algebraization.CoherentTriple.twistZOneHom`: **the degree-one twist of a coherent
  triple is its tensor product with the invertible triple**, as a morphism of coherent triples
  `T ⊗ L^{⊗ 1} ⟶ T ⊗ L`.

## Main results

* `Stacks.Algebraization.CoherentTriple.isIso_twistZOneHom`: both of its members are
  isomorphisms.
* `Stacks.Algebraization.CoherentTriple.exists_shortExact_degreeOne`: **the degree-one short
  exact sequence** `0 → T → T ⊗ L → G → 0` of the induction step, from the degree-zero
  multiplication map.
* `Stacks.Algebraization.CoherentTriple.exists_shortExact_twistZ_of_mono`: **the third clause of
  `Stacks.Algebraization.HasHilbertInductionStep`**, from the degree-zero multiplication map
  alone.
* `Stacks.Algebraization.CoherentTriple.exists_shortExact_twistZ_quotientTriple`: the same clause
  for the triple the opening reduction produces, with the multiplication map and its monicity and
  torsion-freeness supplied by
  `Stacks.Algebraization.exists_sectionPair_mono_quotientTriple` -- so with **no hypothesis about
  the section at all**, only the quasi-coherence of the tensor products and a trivialization of
  each member of `L` that lemma already asks for.

## Implementation notes

Only three transports of short exactness are used, and together they move every term of a
sequence: `Stacks.Algebraization.CoherentTriple.ShortExact.isoComp` (first term),
`Stacks.Algebraization.CoherentTriple.ShortExact.midIso` (middle) and
`Stacks.Algebraization.CoherentTriple.ShortExact.compIso` (third, not needed here). The reason
the degree-one route is used rather than the degree-`n` one is that twisting is exact, so the
*sequence* moves for free, whereas the degree-`n` route would have to identify the cokernel of
the degree-`n` multiplication with the `n`-th twist of one fixed cokernel -- a different
identification in every degree.

The degree arithmetic is kept as `0 + 1` rather than `1` throughout, because that is the shape
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` produces in degree `0` and the shape
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccHom` produces at `n = 0`; the two
are definitionally equal, but writing `1` would make every statement below carry a conversion.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.Algebraization

/-! ### The degree-one twist is the tensor product -/

/-- **The degree-one twist of a coherent triple is its tensor product with the invertible
triple**, as a morphism of coherent triples `T ⊗ L^{⊗ 1} ⟶ T ⊗ L`: the successor identification
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccHom` in degree zero, inverted,
followed by the degree-zero identification
`Stacks.Algebraization.CoherentTriple.twistZZeroHom` tensored with `L`.

Both members are isomorphisms
(`Stacks.Algebraization.CoherentTriple.isIso_twistZOneHom`), so this is an identification of
coherent triples in the sense the consumers of such a thing use. -/
public noncomputable def CoherentTriple.twistZOneHom {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f} (hL : IsInvertibleTriple L) :
    (T.twistZ L hL (0 + 1)).Hom (T.tensorInvertible L hL) :=
  letI := (T.isIso_tensorInvertibleTwistZSuccHom hL 0).1
  letI := (T.isIso_tensorInvertibleTwistZSuccHom hL 0).2
  (T.tensorInvertibleTwistZSuccHom hL 0).inverse.comp
    ((T.twistZZeroHom hL).tensorInvertible L hL)

/-- **Both members of `Stacks.Algebraization.CoherentTriple.twistZOneHom` are isomorphisms.** -/
public theorem CoherentTriple.isIso_twistZOneHom {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f} (hL : IsInvertibleTriple L) :
    IsIso (T.twistZOneHom hL).onPunctured ∧ IsIso (T.twistZOneHom hL).onClosedFibre := by
  let := (T.isIso_tensorInvertibleTwistZSuccHom hL 0).1
  let := (T.isIso_tensorInvertibleTwistZSuccHom hL 0).2
  let := (T.isIso_twistZZeroHom hL).1
  let := (T.isIso_twistZZeroHom hL).2
  let := CoherentTriple.isIso_inverse_onPunctured (T.tensorInvertibleTwistZSuccHom hL 0)
  let := CoherentTriple.isIso_inverse_onClosedFibre (T.tensorInvertibleTwistZSuccHom hL 0)
  let := CoherentTriple.isIso_tensorInvertible_onPunctured (T.twistZZeroHom hL) L hL
  let := CoherentTriple.isIso_tensorInvertible_onClosedFibre (T.twistZZeroHom hL) L hL
  exact ⟨CoherentTriple.isIso_comp_onPunctured _ _, CoherentTriple.isIso_comp_onClosedFibre _ _⟩

/-! ### The degree-one short exact sequence -/

/-- **The degree-one short exact sequence of the induction step of [Stacks, Tag 0F27]**,
`0 → T → T ⊗ L → G → 0`, from a monomorphism `T ⊗ L^{⊗ 0} ⟶ T ⊗ L^{⊗ 1}` with `f`-torsion-free
cokernel -- which is what multiplication by a section pair supplies.

The quotient `G` is the cokernel triple of that monomorphism, and the two ends of the sequence are
moved by `Stacks.Algebraization.CoherentTriple.ShortExact.isoComp` and
`Stacks.Algebraization.CoherentTriple.ShortExact.midIso` along the degree-zero and degree-one
identifications. -/
public theorem CoherentTriple.exists_shortExact_degreeOne {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (φ : (T.twistZ L hL 0).Hom (T.twistZ L hL (0 + 1)))
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) (hmono : Mono φ.onPunctured)
    (hmono₀ : Mono φ.onClosedFibre) :
    ∃ (G : CoherentTriple A f) (Φ : T.Hom (T.tensorInvertible L hL))
      (Ψ : (T.tensorInvertible L hL).Hom G), CoherentTriple.ShortExact Φ Ψ := by
  let := (T.isIso_twistZZeroHom hL).1
  let := (T.isIso_twistZZeroHom hL).2
  let := (T.isIso_twistZOneHom hL).1
  let := (T.isIso_twistZOneHom hL).2
  let := CoherentTriple.isIso_inverse_onPunctured (T.twistZZeroHom hL)
  let := CoherentTriple.isIso_inverse_onClosedFibre (T.twistZZeroHom hL)
  exact ⟨_, _, _,
    ((CoherentTriple.shortExact_cokernelHom φ htf hmono hmono₀).isoComp
      (T.twistZZeroHom hL).inverse).midIso (T.twistZOneHom hL)⟩

/-! ### The third clause of the induction step -/

/-- **The third clause of `Stacks.Algebraization.HasHilbertInductionStep`**: one coherent triple
`G` and, for every integer `n`, a short exact sequence
`0 → T ⊗ L^{⊗ n} → T ⊗ L^{⊗ (n + 1)} → G ⊗ L^{⊗ n} → 0`, from a monomorphism
`T ⊗ L^{⊗ 0} ⟶ T ⊗ L^{⊗ 1}` with `f`-torsion-free cokernel.

The degree-one sequence of
`Stacks.Algebraization.CoherentTriple.exists_shortExact_degreeOne` is twisted by `L^{⊗ n}`, which
is exact and already puts the first and third terms where the clause wants them, and the middle
term is moved by `Stacks.Algebraization.CoherentTriple.ShortExact.midIso` along the reordering of
the double twist,
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccDegreeOneHom`. -/
public theorem CoherentTriple.exists_shortExact_twistZ_of_mono {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (φ : (T.twistZ L hL 0).Hom (T.twistZ L hL (0 + 1)))
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) (hmono : Mono φ.onPunctured)
    (hmono₀ : Mono φ.onClosedFibre) :
    ∃ (G : CoherentTriple A f)
      (u : ∀ n : ℤ, (T.twistZ L hL n).Hom (T.twistZ L hL (n + 1)))
      (v : ∀ n : ℤ, (T.twistZ L hL (n + 1)).Hom (G.twistZ L hL n)),
      ∀ n : ℤ, CoherentTriple.ShortExact (u n) (v n) := by
  obtain ⟨G, Φ, Ψ, hse⟩ := T.exists_shortExact_degreeOne hL φ htf hmono hmono₀
  have key : ∀ n : ℤ, ∃ (u : (T.twistZ L hL n).Hom (T.twistZ L hL (n + 1)))
      (v : (T.twistZ L hL (n + 1)).Hom (G.twistZ L hL n)), CoherentTriple.ShortExact u v := by
    intro n
    let := (T.isIso_tensorInvertibleTwistZSuccDegreeOneHom hL n).1
    let := (T.isIso_tensorInvertibleTwistZSuccDegreeOneHom hL n).2
    exact ⟨_, _, (hse.twistZ L hL n).midIso (T.tensorInvertibleTwistZSuccDegreeOneHom hL n)⟩
  choose u v huv using key
  exact ⟨G, u, v, huv⟩

/-- **The third clause of `Stacks.Algebraization.HasHilbertInductionStep` for the triple the
opening reduction produces, with no hypothesis about the section.** The multiplication map, its
monicity on both members and the `f`-torsion-freeness of its cokernel are supplied by
`Stacks.Algebraization.exists_sectionPair_mono_quotientTriple` in degree zero; what is left are
the quasi-coherence and trivialization hypotheses that lemma already carries, none of which is a
property of the section. -/
public theorem CoherentTriple.exists_shortExact_twistZ_quotientTriple {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} [IsLocalRing (A ⧸ Ideal.span {f})]
    (hf : f ∈ maximalIdeal A) {L : CoherentTriple A f} (hL : IsInvertibleTriple L)
    (T : CoherentTriple A f)
    {N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).presheaf,
        (((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).IsSheaf⟩).obj
          (L.F)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    {N₀ : (closedFibre A f).Modules}
    (ψ₀ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((closedFibre A f).toRingedSpace)).presheaf,
        (((closedFibre A f).toRingedSpace)).IsSheaf⟩).obj (L.F₀)).obj (N₀)) ≅
      _root_.SheafOfModules.unit _)
    (hq : (((T.quotientTriple hf).twistZ L hL 0).F).IsQuasicoherent)
    (hq' : (Stacks.RelativeVeryAmple.tensorModules
      (Stacks.Divisors.puncturedSpectrum A).toScheme
      (((T.quotientTriple hf).twistZ L hL 0).F) L.F).IsQuasicoherent)
    (hqc : letI := hL.invertible_F
      (Stacks.RelativeVeryAmple.tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (cokernel (Stacks.AlgebraicGeometry.PrincipalIdealExtension.smulPowHom
          (T.quotientTriple hf).F (scalarGlobal A f) 1))
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F 0)).IsQuasicoherent)
    (hqc' : letI := hL.invertible_F
      (Stacks.RelativeVeryAmple.tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (Stacks.RelativeVeryAmple.tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
          (cokernel (Stacks.AlgebraicGeometry.PrincipalIdealExtension.smulPowHom
            (T.quotientTriple hf).F (scalarGlobal A f) 1))
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F 0))
        L.F).IsQuasicoherent)
    (hq₀ : (((T.quotientTriple hf).twistZ L hL 0).F₀).IsQuasicoherent)
    (hq₀' : (Stacks.RelativeVeryAmple.tensorModules (closedFibre A f)
      (((T.quotientTriple hf).twistZ L hL 0).F₀) L.F₀).IsQuasicoherent) :
    ∃ (G : CoherentTriple A f)
      (u : ∀ n : ℤ, ((T.quotientTriple hf).twistZ L hL n).Hom
        ((T.quotientTriple hf).twistZ L hL (n + 1)))
      (v : ∀ n : ℤ, ((T.quotientTriple hf).twistZ L hL (n + 1)).Hom (G.twistZ L hL n)),
      ∀ n : ℤ, CoherentTriple.ShortExact (u n) (v n) := by
  obtain ⟨x, x₀, hx, hmono, htf, hmono₀⟩ :=
    exists_sectionPair_mono_quotientTriple hf hL T 0 ψ ψ₀ hq hq' hqc hqc' hq₀ hq₀'
  exact (T.quotientTriple hf).exists_shortExact_twistZ_of_mono hL
    ((T.quotientTriple hf).mulSectionTwistZOfGlobalSections L hL x x₀ hx 0) htf hmono hmono₀

end Stacks.Algebraization

end
