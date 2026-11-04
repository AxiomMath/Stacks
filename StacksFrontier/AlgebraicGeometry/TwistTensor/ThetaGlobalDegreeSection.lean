module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaGlobalSectionMultiplicativity

/-!
# The canonical multiplication of the twists on the sections attached to homogeneous elements

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring covered in degree one and `X = Proj S`. For a natural
number `k` and `a ∈ 𝒮 k` homogeneous, [Stacks, Tag 01MP] attaches to `a` the global section
`degreeSection 𝒮 k a` of `𝒪_X(k)`, whose value at every point is the fraction `a / 1`. This
file
computes the canonical multiplication isomorphism of Equation 01MO on such a pair of sections, at
the spelling in which the multiplicativity of the twist comparison
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower` is stated: the product of the sections
attached to `a` and `b` is the section attached to `a * b`.

Pointwise there is nothing to it — `a / 1 · b / 1 = ab / 1` in every homogeneous localization,
which is `Stacks.AlgebraicGeometry.TwistTensor.mulSection_apply` together with
`degreeSection_apply`. What the statement adds is the spelling. The multiplication of
`Stacks.AlgebraicGeometry.ThetaGlobal.twistMulModules` is stated against the tensor product sheaf
of [Stacks, Tag 01CA] with its degrees written `d · n`, and the pure tensor is the one
`Stacks.SheafOfModules.tensorSectionsAt` forms; so the statement is the one that composes with
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower_mulBilinear`, whose right-hand side is
exactly a `twistMulModules` applied to a `tensorSectionsAt`.

## Main results

* `Stacks.AlgebraicGeometry.ThetaGlobal.twistMulModules_degreeSection`: **the canonical
  multiplication `𝒪_X(dn) ⊗ 𝒪_X(dm) ≅ 𝒪_X(d(n+m))` carries the pure tensor of the global sections
  attached to two homogeneous elements to the global section attached to their product.**

## Implementation notes

No transport along `d · n = n · d` appears. `degreeSection 𝒮 (d * n) a` is a section of the
twist
indexed by `((d * n : ℕ) : ℤ)` and the multiplication is stated at the index `(d : ℤ) * (n : ℤ)`;
`Int.mul` of two `Int.ofNat`s reduces to the `Int.ofNat` of the product, so the two indices are
definitionally equal and the section may be *written* at the natural-number degree and *used* at
the integer one. This is the same observation that lets
`Stacks.AlgebraicGeometry.ProjTrivialization.powSection` be stated at arbitrary `d` and `n`.

The reduction of `twistMulModules` to the multiplication map of
`Stacks.AlgebraicGeometry.TwistTensor` is `rfl`: `twistMulModules` is `twistMulIsoNat`, which is
`twistMulIso`, which is `twistMultiplicationIso` followed by a transport, and
`twistMultiplicationIso` is `asIso` of `twistMultiplicationMap`; the pure tensor
`Stacks.SheafOfModules.tensorSectionsAt` forms is the one
`Stacks.AlgebraicGeometry.TwistTensor.mulSection` consumes. Both identifications are recorded in
the `key` step of the proof rather than left implicit, so that a later change to either spelling
fails there and not inside the pointwise computation.

Not stated for an arbitrary pair of integer degrees: `degreeSection` is attached to an element
homogeneous of a *natural-number* degree, and a negative twist has no such section to multiply.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample
open Stacks.SheafOfModules (tensorSectionsAt)
open Stacks.AlgebraicGeometry.TwistTensor (twist_section_ext eqToHom_twist_val_app_apply
  mulSection mulSection_apply)

universe u w

namespace Stacks.AlgebraicGeometry.ThetaGlobal

open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover)

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (hcover : DegreeOneCover 𝒮) (d : ℕ)

/-- **The canonical multiplication of the twists carries the pure tensor of the global sections
attached to two homogeneous elements to the global section attached to their product.**

The degrees are the `d`-divisible ones `d · n` and `d · m` at which the twist comparison
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower` is multiplicative, and the product
element is supplied separately together with the equation pinning it down, so that the caller
chooses the degree in which it is homogeneous.

Pointwise the two sides are `a / 1 · b / 1` and `ab / 1`. -/
theorem twistMulModules_degreeSection (n m : ℕ)
    (a : 𝒮 (d * n)) (b : 𝒮 (d * m)) (ab : 𝒮 (d * (n + m)))
    (hab : (ab : S) = (a : S) * (b : S)) :
    (twistMulModules 𝒮 hcover d n m).hom.val.app
        (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))
        (tensorSectionsAt (AlgebraicGeometry.Proj 𝒮).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))
          (twist 𝒮 ((d : ℤ) * (n : ℤ))) (twist 𝒮 ((d : ℤ) * (m : ℤ)))
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 (d * n) a)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 (d * m) b)) =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 (d * (n + m)) ab := by
  have hdeg : (d : ℤ) * (n : ℤ) + (d : ℤ) * (m : ℤ) = (d : ℤ) * ((n + m : ℕ) : ℤ) := by
    push_cast; ring
  have key : (twistMulModules 𝒮 hcover d n m).hom.val.app
        (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))
        (tensorSectionsAt (AlgebraicGeometry.Proj 𝒮).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))
          (twist 𝒮 ((d : ℤ) * (n : ℤ))) (twist 𝒮 ((d : ℤ) * (m : ℤ)))
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 (d * n) a)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 (d * m) b)) =
      (eqToHom (congrArg (twist 𝒮) hdeg)).val.app
        (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))
        (mulSection 𝒮 ((d : ℤ) * (n : ℤ)) ((d : ℤ) * (m : ℤ))
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 (d * n) a)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 (d * m) b)) := rfl
  refine key.trans ?_
  refine twist_section_ext 𝒮 (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) _ _ fun z => ?_
  refine Eq.trans (eqToHom_twist_val_app_apply 𝒮 hdeg
    (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) _ z) ?_
  refine Eq.trans (mulSection_apply 𝒮 ((d : ℤ) * (n : ℤ)) ((d : ℤ) * (m : ℤ))
    (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) _ _ z) ?_
  rw [ProjTwistSections.degreeSection_apply, ProjTwistSections.degreeSection_apply,
    ProjTwistSections.degreeSection_apply, hab]
  exact Eq.trans LocalizedModule.mk_mul_mk
    (congrArg (LocalizedModule.mk ((a : S) * (b : S))) (mul_one 1))

end Stacks.AlgebraicGeometry.ThetaGlobal

end
