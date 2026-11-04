module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoefficientColength
import all StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
import all StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.ChartMembership

/-!
# The local rings of a closed subscheme and of its fibre over a section

The local comparison of multiplicities underlying Stacks Tag 02S5,
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`, carries
two hypotheses on Krull dimensions in the local ring `A = 𝒪_{X ×_S 𝐏¹_S, ξ}`: that `A/I` has
dimension one, for `I` the stalk of the ideal sheaf of `Z`, and that `A/(t, I)` has dimension at
most zero, for `t` a local equation of the section. Neither is a statement a consumer can read
off the geometry as written.

This file identifies both quotients with local rings of schemes. The first is the local ring of
`Z` itself, and the second is the local ring of the fibre `Z₀`, so the two hypotheses become
bounds on the Krull dimension of the local ring of `Z` at a point of the fibre and of the local
ring of the fibre at that point — which the delta-dimension hypotheses of the tag are about.

As in `StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/CoefficientColength.lean`, the general
statements hold for the inverse image of an ideal sheaf along an arbitrary closed immersion; the
projective line enters only in producing `t`.

## Main results

* `Stacks.Chow.ringKrullDim_quotient_idealStalk_eq` — the quotient of the local ring of `X` at a
  point of a closed subscheme by the stalk of its ideal sheaf is the local ring of the
  subscheme.
* `Stacks.Chow.ringKrullDim_quotient_stalk_comap_eq` — for a closed immersion `g`, the quotient
  of the local ring at `g x` by the sum of the kernel of the stalk map and the stalk of an ideal
  sheaf is the quotient of the local ring at `x` by the stalk of the inverse-image ideal sheaf.
* `Stacks.Chow.exists_localEquation_ringKrullDim_quotient_eq_zeroFiber` and
  `Stacks.Chow.exists_localEquation_ringKrullDim_quotient_eq_infinityFiber` — the two
  consequences for the distinguished sections: the quotient by a local equation together with
  the stalk of the ideal sheaf of `Z` is the local ring of the zero, respectively the infinity,
  fibre.

## Implementation notes

The ring-theoretic content is a single isomorphism: for a surjection `φ : A → B` and an ideal
`I ⊆ A`, the ring `A/(ker φ + I)` is `B/I.map φ`, because the composite `A → B → B/I.map φ` is
surjective with kernel `(I.map φ).comap φ = I ⊔ ker φ`. Only the ring structure is used here,
where `StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/CoefficientColength.lean` needs the same
map to be `A`-linear; the two are kept separate because `ringKrullDim` transports along a
`RingEquiv` and `Module.length` along a `LinearEquiv`, and neither invariance implies the other.

The kernel of the stalk map of a closed immersion is identified with the stalk of its kernel
ideal sheaf by `Stacks.Chow.ker_stalkMap_eq_idealStalk_ker`; applied to `I.subschemeι`, whose
kernel is `I` by `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`, that gives the local
ring of a closed subscheme as a quotient without choosing an affine open.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace Stacks.Chow

/-- For a surjective ring map `φ : A →+* B` and an ideal `I` of `A`, the quotient
`A ⧸ (ker φ ⊔ I)` is `B ⧸ I.map φ`. -/
private def quotientSupKerRingEquiv {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Surjective φ) (I : Ideal A) :
    (A ⧸ (RingHom.ker φ ⊔ I)) ≃+* (B ⧸ I.map φ) := by
  let ψ : A →+* (B ⧸ I.map φ) := (Ideal.Quotient.mk (I.map φ)).comp φ
  have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ψ = RingHom.ker φ ⊔ I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective' φ hφ, sup_comm]
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)

/-- The Krull dimension of the quotient of the local ring of `Y` at `g x` by the sum of the
kernel of the stalk map of a closed immersion `g` and the stalk of an ideal sheaf `Z` is the
Krull dimension of the quotient of the local ring of `X` at `x` by the stalk of the inverse
image of `Z`. -/
theorem ringKrullDim_quotient_stalk_comap_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsClosedImmersion g] (Z : Y.IdealSheafData) (x : X) :
    ringKrullDim (Y.presheaf.stalk (g x) ⧸
        (RingHom.ker (g.stalkMap x).hom ⊔ IdealSheafData.stalk Z (g x))) =
      ringKrullDim (X.presheaf.stalk x ⧸ IdealSheafData.stalk (Z.comap g) x) := by
  rw [idealStalk_comap_eq_map g Z x]
  exact ringKrullDim_eq_of_ringEquiv (quotientSupKerRingEquiv (g.stalkMap x).hom
    (SurjectiveOnStalks.stalkMap_surjective g x) (IdealSheafData.stalk Z (g x)))

/-- The quotient of the local ring of `X` at a point of a closed subscheme by the stalk of its
ideal sheaf is the local ring of the subscheme, so the two have the same Krull dimension. -/
theorem ringKrullDim_quotient_idealStalk_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (y : I.subscheme) :
    ringKrullDim (X.presheaf.stalk (I.subschemeι y) ⧸ IdealSheafData.stalk I (I.subschemeι y)) =
      ringKrullDim (I.subscheme.presheaf.stalk y) := by
  have hker : RingHom.ker (I.subschemeι.stalkMap y).hom =
      IdealSheafData.stalk I (I.subschemeι y) := by
    rw [ker_stalkMap_eq_idealStalk_ker, Scheme.IdealSheafData.ker_subschemeι]
  rw [← hker]
  exact ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (SurjectiveOnStalks.stalkMap_surjective I.subschemeι y))

/-! ### The two dimension hypotheses of the local comparison, read on the fibre -/

/-- If the kernel of the stalk map of a closed immersion `g` is principal at every point, then
some generator `t` of it at a point of the inverse image of `Z` makes the quotient by `t` and the
stalk of `Z` have the Krull dimension of the local ring of that inverse image. -/
private theorem exists_ringKrullDim_quotient_span_sup_idealStalk_eq {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsClosedImmersion g] (Z : Y.IdealSheafData) (y : (Z.comap g).subscheme)
    (h : ∀ x, ∃ t : Y.presheaf.stalk (g x), RingHom.ker (g.stalkMap x).hom = Ideal.span {t}) :
    ∃ t : Y.presheaf.stalk (g ((Z.comap g).subschemeι y)),
      ringKrullDim (Y.presheaf.stalk (g ((Z.comap g).subschemeι y)) ⧸
          (Ideal.span {t} ⊔ IdealSheafData.stalk Z (g ((Z.comap g).subschemeι y)))) =
        ringKrullDim ((Z.comap g).subscheme.presheaf.stalk y) := by
  obtain ⟨t, ht⟩ := h ((Z.comap g).subschemeι y)
  refine ⟨t, ?_⟩
  rw [← ht]
  exact (ringKrullDim_quotient_stalk_comap_eq g Z _).trans
    (ringKrullDim_quotient_idealStalk_eq (Z.comap g) y)

/-- The Krull dimension of the quotient of the local ring of `X ×_S ℙ¹_S` by a local equation of
the zero section together with the stalk of the ideal sheaf of `Z` is the Krull dimension of the
local ring of the zero fibre.

With `Stacks.Chow.ringKrullDim_quotient_idealStalk_eq` applied to `Z` itself, this turns the two
dimension hypotheses of
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes` into
statements about the local rings of `Z` and of its zero fibre. -/
theorem exists_localEquation_ringKrullDim_quotient_eq_zeroFiber
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : (projectiveLineProduct f).IdealSheafData)
    (y : (zeroFiber f Z).subscheme) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk
        (zeroSection f ((zeroFiber f Z).subschemeι y)),
      ringKrullDim ((projectiveLineProduct f).presheaf.stalk
            (zeroSection f ((zeroFiber f Z).subschemeι y)) ⧸
          (Ideal.span {t} ⊔
            IdealSheafData.stalk Z (zeroSection f ((zeroFiber f Z).subschemeι y)))) =
        ringKrullDim ((zeroFiber f Z).subscheme.presheaf.stalk y) := by
  exact exists_ringKrullDim_quotient_span_sup_idealStalk_eq (zeroSection f) Z y
    (exists_span_eq_ker_stalkMap_zeroSection f)

/-- The Krull dimension of the quotient of the local ring of `X ×_S ℙ¹_S` by a local equation of
the infinity section together with the stalk of the ideal sheaf of `Z` is the Krull dimension of
the local ring of the infinity fibre. -/
theorem exists_localEquation_ringKrullDim_quotient_eq_infinityFiber
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : (projectiveLineProduct f).IdealSheafData)
    (y : (infinityFiber f Z).subscheme) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk
        (infinitySection f ((infinityFiber f Z).subschemeι y)),
      ringKrullDim ((projectiveLineProduct f).presheaf.stalk
            (infinitySection f ((infinityFiber f Z).subschemeι y)) ⧸
          (Ideal.span {t} ⊔
            IdealSheafData.stalk Z (infinitySection f ((infinityFiber f Z).subschemeι y)))) =
        ringKrullDim ((infinityFiber f Z).subscheme.presheaf.stalk y) := by
  exact exists_ringKrullDim_quotient_span_sup_idealStalk_eq (infinitySection f) Z y
    (exists_span_eq_ker_stalkMap_infinitySection f)

end Stacks.Chow

end
