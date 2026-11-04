module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.PowerSeries.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginZeroFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion

/-!
# The twisted doubled origin admits no lift over the formal disc

Let `K/k` be a quadratic Galois extension of fields and let `X` be the Galois twist of the
affine line with the origin doubled, the quotient of `Spec K[x]` by the diagonal together
with the graph of the nontrivial Galois automorphism away from the origin. The structure
morphism `X ⟶ 𝔸¹_k` admits no dotted arrow over the formal disc `Spec k⟦x⟧`: the unique point
of `X` above the origin of the base is `Spec K`, and a `k`-point of `Spec K` would force the
extension to be trivial.

This is the failure of the existence part of the valuative criterion over the valuation ring
`k⟦x⟧` itself, and is the reason the definition of the existence part for algebraic spaces,
Stacks 03IX, must allow a field extension of the fraction field.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.formalDiskBaseMap`: the morphism from the formal
  disc to the affine line sending the coordinate to the power-series variable.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.finrank_eq_one_of_algHom_to_base`: a field extension
  admitting an algebra homomorphism back to its base field is trivial.
* `AlgebraicGeometry.TwistedDoubledOrigin.not_nonempty_hom_formalDisk`: **Stacks 03KI**, the
  third assertion of the example: the formal disc over `k`, with the coordinate map above, has
  no point of the twisted doubled origin at all.

## Implementation notes

The conclusion rules out *every* morphism from the functor of points of the formal disc into
the quotient sheaf, which is stronger than ruling out the dotted arrows compatible with the
canonical generic point of Stacks 03FN; in particular no inverse of the isomorphism over the
punctured line has to be chosen.

The argument is the one in the Stacks text, run on the fibre over the origin. Restricting a
hypothetical point along the closed immersion `Spec k ⟶ Spec k⟦x⟧` cut out by the constant
coefficient gives a point of `X` over the origin of the base, and
`AlgebraicGeometry.TwistedDoubledOrigin.twistedRelationQuotient_zeroFibre` identifies the fibre
of `X` over that origin with `Spec K`. The resulting `k`-point of `Spec K` is a `k`-algebra
homomorphism `K →ₐ[k] k`, which a quadratic extension does not admit.

## References

* [Stacks Project, Tag 03KI](https://stacks.math.columbia.edu/tag/03KI)
* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- A field extension which admits a homomorphism of algebras back to its base field is
trivial: such a homomorphism is injective because the source is a field and surjective
because it splits the structure map, hence an isomorphism of `k`-algebras. -/
theorem finrank_eq_one_of_algHom_to_base (f : K →ₐ[k] k) : Module.finrank k K = 1 :=
  have e : K ≃ₐ[k] k := AlgEquiv.ofBijective f
    ⟨RingHom.injective f.toRingHom, fun y => ⟨algebraMap k K y, by simp⟩⟩
  e.toLinearEquiv.finrank_eq.trans (Module.finrank_self k)

/-- A morphism `Spec k ⟶ Spec K` lying over the origin of the affine line forces the
extension `K/k` to be trivial: it is a `k`-algebra homomorphism `K →ₐ[k] k`, which
`AlgebraicGeometry.TwistedDoubledOrigin.finrank_eq_one_of_algHom_to_base` forbids for a
nontrivial extension. -/
theorem finrank_eq_one_of_hom_zeroCover (f : Spec (.of k) ⟶ Spec (.of K))
    (hcompat : f ≫ Spec.map (CommRingCat.ofHom
        (Polynomial.eval₂RingHom (algebraMap k K) (0 : K))) =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) :
    Module.finrank k K = 1 := by
  let ρ : K →+* k := (Spec.homEquiv (R := CommRingCat.of K) (S := CommRingCat.of k) f).hom
  have hρ : ρ.comp (Polynomial.eval₂RingHom (algebraMap k K) (0 : K)) =
      Polynomial.evalRingHom (0 : k) := by
    simpa [ρ, Spec.preimage_comp] using
      congrArg CommRingCat.Hom.hom (congrArg (fun g => Spec.preimage g) hcompat)
  exact finrank_eq_one_of_algHom_to_base k K
    { toRingHom := ρ
      commutes' := fun a => by
        simpa using congrArg (fun g => g (Polynomial.C a)) hρ }

/-- The formal disc over `k`, mapping to the affine line by sending the coordinate of the
line to the power-series variable. -/
def formalDiskBaseMap : Spec (.of (PowerSeries k)) ⟶ base k :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (algebraMap k (PowerSeries k)) PowerSeries.X))

/-- The origin of the formal disc, the closed immersion cut out by the constant coefficient. -/
def formalDiskOrigin : Spec (.of k) ⟶ Spec (.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))

/-- The origin of the formal disc is a closed immersion, being the spectrum of a surjective
ring homomorphism. -/
instance isClosedImmersion_formalDiskOrigin : IsClosedImmersion (formalDiskOrigin k) :=
  IsClosedImmersion.spec_of_surjective _ PowerSeries.constantCoeff_surj

/-- The origin of the formal disc lies over the origin of the affine line. -/
theorem formalDiskOrigin_comp_formalDiskBaseMap :
    formalDiskOrigin k ≫ formalDiskBaseMap k = (zeroBaseOverBase k).hom := by
  dsimp [formalDiskOrigin, formalDiskBaseMap, zeroBaseOverBase]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply Polynomial.ringHom_ext' <;> simp [RingHom.comp_assoc, Polynomial.evalRingHom]

/-- **Stacks 03KI**, third assertion of the example. For a quadratic Galois extension `K/k`,
the formal disc over `k` has no point of the quadratic Galois twisted doubled origin lying
over `AlgebraicGeometry.TwistedDoubledOrigin.formalDiskBaseMap`.

So the solid valuative square over the valuation ring `k⟦x⟧` whose bottom edge is that
coordinate map admits no dotted arrow, and a fortiori none compatible with the generic point
coming from the isomorphism of Stacks 03FN away from the origin: a finite separable extension
of the fraction field is genuinely needed in the existence part of Stacks 03IX. -/
@[stacks 03KI "no_unextended_lift"]
theorem not_nonempty_hom_formalDisk
    [FiniteDimensional k K] [IsGalois k K] (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    (hDisk : B.Contains (Spec (.of (PowerSeries k))))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    ¬ Nonempty
      (yoneda.obj (siteObject B (base k) hS hDisk (formalDiskBaseMap k)) ⟶
        (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj) := by
  intro hs
  have hO : B.Contains (Spec (.of k)) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (formalDiskOrigin k)) hDisk
  let d := siteObject B (base k) hS hDisk (formalDiskBaseMap k)
  let z := siteObject B (base k) hS hO (zeroBaseOverBase k).hom
  let izd : z ⟶ d := Over.homMk
    (ObjectProperty.homMk (formalDiskOrigin k) : B.obj hO ⟶ B.obj hDisk)
    (B.inclusion.map_injective (formalDiskOrigin_comp_formalDiskBaseMap k))
  let F : BigFppfOver B (base k) hS ⥤ Over (base k) := Over.post B.inclusion
  let Q := (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj
  let s₀ : yoneda.obj z ⟶ Q := yoneda.map izd ≫ hs.some
  let u : (points F (zeroBaseOverBase k)).obj (Opposite.op z) := by
    show F.obj z ⟶ zeroBaseOverBase k
    exact Over.homMk (𝟙 _) (Category.id_comp _)
  let e := Classical.choice (twistedRelationQuotient_zeroFibre (k := k) (K := K) σ B hS)
  let w := e.hom.app (Opposite.op z)
    (((prod.lift s₀ (yonedaEquiv.symm u)).app (Opposite.op z)) (𝟙 z))
  have hone := finrank_eq_one_of_hom_zeroCover k K w.left (by
    simpa [F, Over.post, z, siteObject, zeroBaseOverBase, zeroCoverOverBase] using w.w)
  omega

end AlgebraicGeometry.TwistedDoubledOrigin

end
