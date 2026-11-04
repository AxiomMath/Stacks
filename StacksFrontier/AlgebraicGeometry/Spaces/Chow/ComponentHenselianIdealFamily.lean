module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedImmersionHenselianLocalRingQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHenselianLocalRing

/-!
# The irreducible components through a point as a family of ideals of one henselian local ring

Let `X` be a decent algebraic space over `S`, let `x` be a point of it and write
`A = 𝒪^h_{X, x}` for the henselian local ring of Stacks 0ENK there. A family of closed
subspaces `X_i ⊆ X` all passing through `x` — in the application the irreducible components of
`X` through `x`, each with its reduced induced structure — gives rise to a family of ideals

  `I i ⊆ A`  with  `A ⧸ I i ≅ 𝒪^h_{X_i, ξ_i}`,

`ξ_i` being the point of `X_i` above `x`. This file constructs that family and proves three
ring-theoretic properties of its quotients.

`AlgebraicGeometry.Space.exists_ringEquiv_henselianLocalRing_quotient_of_isClosedImmersion`
already produces such an ideal for *one* closed immersion, but with the elementary étale
neighborhoods `U` of `ξ` in `X_i` and the chart morphism `j : U ⟶ V` existentially quantified,
and phrased at the point `f(ξ)` rather than at a point of `X` given in advance. Two things are
therefore done here.

* **Transport to a named point.** The statement is reformulated at a point `x` of `X` together
  with a proof that `ξ` lies over it, so that all the quotients can be read inside one and the
  same ring `A = 𝒪^h_{X, x}`. This is what lets the ideals be collected into a family: the
  chart data varies with `i`, the ring it produces an ideal of does not.
* **The three properties of the quotients.** For a component `X_i` which is *integral* and
  carries a prime divisor with generic point `ξ_i` — the situation of the additivity formula,
  where the common point `x` is the generic point of a prime divisor `Z` of `X` and `X_i` runs
  over the components of `X` through it — the quotient `A ⧸ I i` is nontrivial, reduced and of
  Krull dimension one. These come from the three parts of Stacks 0ENK for an integral space
  (`AlgebraicGeometry.Space.PrimeDivisor.isReduced_genericHenselianLocalRing` and
  `.ringKrullDim_genericHenselianLocalRing_eq_one`) transported along the isomorphism
  `A ⧸ I i ≅ 𝒪^h_{X_i, ξ_i}`.

## Main results

* `exists_ideal_ringEquiv_henselianLocalRing_quotient_of_isClosedImmersion`:
  for a closed immersion `f : X' ⟶ X` of decent algebraic spaces and a point `ξ` of `X'` lying
  over a point `x` of `X`, an ideal `I` of `𝒪^h_{X, x}` with `𝒪^h_{X, x} ⧸ I ≅ 𝒪^h_{X', ξ}`.
* `AlgebraicGeometry.Space.exists_componentIdealFamily_ringEquiv_henselianLocalRing_quotient`:
  the same for a family of closed immersions through one point, as a family of ideals of one
  ring.
* `AlgebraicGeometry.Space.exists_componentIdealFamily_isReduced_ringKrullDim_eq_one`: that
  family when each `X_i` is integral and locally Noetherian and `ξ_i` is the generic point of a
  prime divisor of `X_i`, together with the nontriviality, reducedness and dimension of the
  quotients.

## References

* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### One closed immersion, read at a named point of the ambient space -/

/-- **The henselian local ring of a closed subspace is a quotient of the ambient one, read at a
named point.** Let `f : X' ⟶ X` be a closed immersion of decent algebraic spaces over `S`, let
`ξ` be a point of `X'` and let `x` be the point of `X` it lies over. Then there is an ideal `I`
of `𝒪^h_{X, x}` with `𝒪^h_{X, x} ⧸ I ≅ 𝒪^h_{X', ξ}`. -/
theorem exists_ideal_ringEquiv_henselianLocalRing_quotient_of_isClosedImmersion
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXd : IsDecentSpace B S hS X)
    (hX' : IsAlgebraicSpace B S hS X') (hX'd : IsDecentSpace B S hS X')
    (f : X' ⟶ X) (hf : IsClosedImmersion B S hS f) (ξ : points B S hS X')
    (x : points B S hS X) (hx : pointsMap B S hS X' f ξ = x) :
    ∃ I : Ideal (henselianLocalRing B S hS X hX x hXd : Type (u + 1)),
      Nonempty (((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸ I) ≃+*
        (henselianLocalRing B S hS X' hX' ξ hX'd : Type (u + 1))) := by
  subst hx
  obtain ⟨V⟩ : Nonempty (ElementaryEtaleNeighborhood B S hS X hX
      (pointsMap B S hS X' f ξ)) :=
    ⟨(exists_affine_elementaryEtaleNeighborhood' B S hS hX hXd
      (pointsMap B S hS X' f ξ)).choose⟩
  obtain ⟨U, j, hj, -, -, he⟩ :=
    exists_ringEquiv_henselianLocalRing_quotient_of_isClosedImmersion B S hS hX hXd hX' hX'd
      f hf ξ V
  exact ⟨_, he⟩

/-! ### A family of closed subspaces through one point -/

/-- **The ideals of a family of closed subspaces through one point, inside one henselian local
ring.** Let `X` be a decent algebraic space over `S`, let `x` be a point of it, and let
`f i : X' i ⟶ X` be closed immersions of decent algebraic spaces with points `ξ i` of `X' i`
all lying over `x`. Then there is a family of ideals `I i` of `𝒪^h_{X, x}` with
`𝒪^h_{X, x} ⧸ I i ≅ 𝒪^h_{X' i, ξ i}` for every `i`. -/
theorem exists_componentIdealFamily_ringEquiv_henselianLocalRing_quotient
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXd : IsDecentSpace B S hS X)
    {ι : Type*} (X' : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX' : ∀ i, IsAlgebraicSpace B S hS (X' i))
    (hX'd : ∀ i, IsDecentSpace B S hS (X' i))
    (f : ∀ i, X' i ⟶ X) (hf : ∀ i, IsClosedImmersion B S hS (f i))
    (ξ : ∀ i, points B S hS (X' i)) (x : points B S hS X)
    (hx : ∀ i, pointsMap B S hS (X' i) (f i) (ξ i) = x) :
    ∃ I : ι → Ideal (henselianLocalRing B S hS X hX x hXd : Type (u + 1)),
      ∀ i, Nonempty (((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸ I i) ≃+*
        (henselianLocalRing B S hS (X' i) (hX' i) (ξ i) (hX'd i) : Type (u + 1))) := by
  choose I hI using fun i => exists_ideal_ringEquiv_henselianLocalRing_quotient_of_isClosedImmersion
    B S hS hX hXd (hX' i) (hX'd i) (f i) (hf i) (ξ i) x (hx i)
  exact ⟨I, hI⟩

/-! ### The quotients by the ideals of integral components are reduced of dimension one -/

/-- **The family of component ideals, with the three properties of its quotients.** Let `X` be a
decent algebraic space over `S` and `x` a point of it. Let `f i : X' i ⟶ X` be closed immersions
with each `X' i` an integral, locally Noetherian algebraic space, and let `Z i` be a prime
divisor of `X' i` whose generic point lies over `x`. Then there is a family of ideals `I i` of
`A = 𝒪^h_{X, x}` such that for every `i`

* `I i ≠ ⊤`,
* `A ⧸ I i` is reduced,
* `ringKrullDim (A ⧸ I i) = 1`, and
* `A ⧸ I i ≅ 𝒪^h_{X' i, ξ i}` for `ξ i` the generic point of `Z i`. -/
theorem exists_componentIdealFamily_isReduced_ringKrullDim_eq_one
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXd : IsDecentSpace B S hS X)
    {ι : Type*} (X' : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX' : ∀ i, IsAlgebraicSpace B S hS (X' i))
    (hX'int : ∀ i, IsIntegralSpace B S hS (X' i))
    (hX'N : ∀ i, HasEtaleLocalProperty B S hS (X' i)
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (f : ∀ i, X' i ⟶ X) (hf : ∀ i, IsClosedImmersion B S hS (f i))
    (Z : ∀ i, PrimeDivisor B S hS (X' i)) (x : points B S hS X)
    (hx : ∀ i, pointsMap B S hS (X' i) (f i)
      ((Z i).genericPoint B S hS (X' i)) = x) :
    ∃ I : ι → Ideal (henselianLocalRing B S hS X hX x hXd : Type (u + 1)),
      (∀ i, I i ≠ ⊤) ∧
      (∀ i, _root_.IsReduced ((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸ I i)) ∧
      (∀ i, ringKrullDim ((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸ I i) = 1) ∧
      ∀ i, Nonempty (((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸ I i) ≃+*
        ((Z i).genericHenselianLocalRing B S hS (hX' i) ((hX'int i).isDecentSpace) :
          Type (u + 1))) := by
  obtain ⟨I, hI⟩ := exists_componentIdealFamily_ringEquiv_henselianLocalRing_quotient B S hS hX
    hXd X' hX' (fun i => (hX'int i).isDecentSpace) f hf
    (fun i => (Z i).genericPoint B S hS (X' i)) x hx
  refine ⟨I, fun i => ?_, fun i => ?_, fun i => ?_, hI⟩ <;> obtain ⟨e⟩ := hI i
  · have := PrimeDivisor.nontrivial_genericHenselianLocalRing B S hS (hX' i)
      ((hX'int i).isDecentSpace) (hX'int i) (hX'N i) (Z i)
    exact Ideal.Quotient.nontrivial_iff.mp (e.toEquiv.nontrivial)
  · have := PrimeDivisor.isReduced_genericHenselianLocalRing B S hS (hX' i)
      ((hX'int i).isDecentSpace) (hX'int i) (hX'N i) (Z i)
    exact isReduced_of_injective e.toRingHom e.injective
  · exact (ringKrullDim_eq_of_ringEquiv e).trans
      (PrimeDivisor.ringKrullDim_genericHenselianLocalRing_eq_one B S hS (hX' i)
        ((hX'int i).isDecentSpace) (hX'int i) (hX'N i) (Z i))

end AlgebraicGeometry.Space

end
