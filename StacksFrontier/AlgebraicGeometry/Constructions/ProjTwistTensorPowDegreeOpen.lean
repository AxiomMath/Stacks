module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpenSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion

/-!
# The tensor powers of `𝒪_{U_d}(d)` are the divisible twists

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring, `X = Proj 𝒮`, and let `U_d = ⋃_{f ∈ 𝒮 d} D₊(f)` be the
degree `d` open of Stacks Tag 01N5. On `U_d` every twist `𝒪(dn)` is invertible and every
multiplication map `𝒪(dn) ⊗ 𝒪(dm) ⟶ 𝒪(d(n + m))` restricts to an isomorphism — both clauses of
`Stacks.AlgebraicGeometry.ProjDegreeOpenSections.isGoodOpen_degreeOpen`, with no
quasi-compactness hypothesis. This file assembles those canonical multiplication isomorphisms
into the family

`𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)`,

by induction on `n`, and records that the induction step **is** the multiplication isomorphism:
the comparison in degree `n + 1` is the comparison in degree `n` tensored with the identity,
followed by the canonical multiplication. Nothing is chosen.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twist` — the twist `𝒪(c)` of `Proj 𝒮`
  restricted to `U_d`, at the spelling
  `Stacks.AlgebraicGeometry.CommonDegreeTwist.restrictedTwist`.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso` — **the canonical
  multiplication isomorphism** `𝒪_{U_d}(dn) ⊗ 𝒪_{U_d}(dm) ≅ 𝒪_{U_d}(d(n + m))`, for arbitrary
  integers `n` and `m`.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistZeroIsoUnit` — `𝒪_{U_d}(0) ≅ 𝒪`.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta` — **the family
  `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)`**, and
  `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat`, the same with the twist
  degree spelled `(n * d : ℕ)` as the `d`-th Veronese section ring spells it.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.isInvertibleModule_twist` and
  `isIso_twistMul` — the two clauses of goodness of `U_d`, read at the spellings the tensor-power
  calculus and Stacks Tag 01CD are stated in.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta_succ` — **the recursion, as an
  equation of morphisms.** The comparison in degree `n + 1` factors through the comparison in
  degree `n` and the canonical multiplication isomorphism at `(dn, d)`, the splitting of the
  tensor power being `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaStep`.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta_mul_one` — **multiplicativity of
  the family in the last variable**: the square relating the addition law of the tensor powers at
  `(n, 1)` to the canonical multiplication at `(dn, d)` commutes.

## Implementation notes

The family is a `def` assembled from the canonical multiplication isomorphisms, so the recursion
is the equation `theta_succ`, which holds by `rfl`, and `theta_mul_one` follows from it by
cancelling one isomorphism against its inverse. Compatibility with the multiplication in the
bidegree `(n, 1)` is therefore how the comparison is built, not something it has to be checked
against; a degreewise choice of isomorphisms would have no such property.

`twistZeroIsoUnit` is the pullback of
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit` — the canonical
`𝒪(0) ≅ 𝒪` on `Proj 𝒮`, which is `HomogeneousLocalization.val` at every point by
`twistingSheafZeroIsoUnit_inv_apply` — followed by the structure-sheaf comparison
`Stacks.PullbackTensorCoherence.pullbackUnitComparison` of Stacks Tag 01CD, whose formula is
`pullbackUnitComparison_pullbackUnit`. So the unit laws of the twist multiplication, which are
stated for that very `𝒪(0) ≅ 𝒪`, apply to `theta 𝒮 d 0`.

The degree of the twist is spelled `(d : ℤ) * n` with an integer `n`, because that is the
spelling both clauses of goodness are stated in. `thetaNat` converts to the natural-number
spelling `(n * d : ℕ)` of the Veronese section ring by a single `eqToIso`.

The two sheaf tensor products on `Proj 𝒮` — the source of
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap` is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` while
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso` is stated over
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` — are the same object, and the
isomorphisms are composed across them directly.

## References

* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01N6](https://stacks.math.columbia.edu/tag/01N6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.RelativeVeryAmple

namespace Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-! ### The divisible twists on the degree `d` open -/

/-- The twist `𝒪(c)` of `Proj 𝒮`, restricted to the degree `d` open `U_d`. -/
abbrev twist (c : ℤ) : (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme.Modules :=
  restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) c

/-- **The invertibility clause of goodness of `U_d`**, at the spelling the tensor-power calculus
uses: every `d`-divisible twist restricts to an invertible module on `U_d`. -/
theorem isInvertibleModule_twist (n : ℤ) :
    IsInvertibleModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d ((d : ℤ) * n)) :=
  (ProjDegreeOpenSections.isGoodOpen_degreeOpen 𝒮 d).1 n

/-- Every `d`-divisible twist, with the degree written as a product of natural numbers. -/
instance isInvertibleModule_twist_natCast (n : ℕ) :
    IsInvertibleModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d ((n * d : ℕ) : ℤ)) := by
  have h := isInvertibleModule_twist 𝒮 d (n : ℤ)
  rwa [show (d : ℤ) * (n : ℤ) = ((n * d : ℕ) : ℤ) from by push_cast; ring] at h

/-- The degree `d` twist itself is invertible on `U_d`. -/
instance isInvertibleModule_twist_self :
    IsInvertibleModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ)) := by
  have h := isInvertibleModule_twist 𝒮 d 1
  rwa [mul_one] at h

/-- The degree zero twist is invertible on `U_d`. -/
instance isInvertibleModule_twist_zero :
    IsInvertibleModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d 0) := by
  have h := isInvertibleModule_twist 𝒮 d 0
  rwa [mul_zero] at h

/-- **The multiplication clause of goodness of `U_d`**, at the spelling Stacks Tag 01CD is stated
in: the canonical multiplication map between two `d`-divisible twists becomes an isomorphism
after restriction to `U_d`. -/
theorem isIso_twistMul (n m : ℤ) :
    IsIso ((modulePullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι.toLRSHom.toShHom).map
      (twistMultiplicationMap 𝒮 ((d : ℤ) * n) ((d : ℤ) * m))) :=
  (NatIso.isIso_map_iff
    (Scheme.Modules.restrictFunctorIsoPullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι)
    (twistMultiplicationMap 𝒮 ((d : ℤ) * n) ((d : ℤ) * m))).mp
    ((ProjDegreeOpenSections.isGoodOpen_degreeOpen 𝒮 d).2 n m)

/-- **The canonical multiplication isomorphism on `U_d`**,
`𝒪_{U_d}(dn) ⊗ 𝒪_{U_d}(dm) ≅ 𝒪_{U_d}(d(n + m))`, in every pair of integer degrees: Stacks Tag
01CD commutes the restriction past the tensor product, and the canonical multiplication map of
Stacks Tag 01MO is an isomorphism on `U_d`. -/
def twistMulIso (n m : ℤ) :
    tensorModules (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d ((d : ℤ) * n))
        (twist 𝒮 d ((d : ℤ) * m)) ≅
      twist 𝒮 d ((d : ℤ) * (n + m)) :=
  (pullbackTensorModulesIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι
      (twistingSheaf 𝒮 ((d : ℤ) * n)) (twistingSheaf 𝒮 ((d : ℤ) * m))).symm ≪≫
    @asIso _ _ _ _ _ (isIso_twistMul 𝒮 d n m) ≪≫
    eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
      (show (d : ℤ) * n + (d : ℤ) * m = (d : ℤ) * (n + m) from by ring))

/-- **`𝒪_{U_d}(0) ≅ 𝒪_{U_d}`.** The zeroth twist of `Proj 𝒮` is the structure sheaf of `Proj 𝒮`,
by `Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit`, and the pullback of the
structure sheaf along the open immersion is the structure sheaf of `U_d`, by the comparison
`Stacks.PullbackTensorCoherence.pullbackUnitComparison` of Stacks Tag 01CD.

Both factors have a formula on local sections — the first is `HomogeneousLocalization.val` at
every point, the second is the structure morphism of the open immersion — so this identification,
unlike one obtained from the inverse object of the Picard group, can be composed with the unit
laws of the twist multiplication. -/
def twistZeroIsoUnit :
    twist 𝒮 d 0 ≅ unitModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme :=
  (modulePullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι.toLRSHom.toShHom).mapIso
      (ProjEulerSequence.twistingSheafZeroIsoUnit 𝒮) ≪≫
    @asIso _ _ _ _ _ (Stacks.PullbackTensorCoherence.isIso_pullbackUnitComparison
      (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι.toLRSHom.toShHom)

/-! ### The tensor powers of the degree `d` twist -/

/-- The degree one tensor power of `𝒪_{U_d}(d)` is the twist of degree `d · 1`. -/
def twistOneIso :
    tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ)) 1 ≅
      twist 𝒮 d ((d : ℤ) * 1) :=
  tensorPowModuleOneIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ)) ≪≫
    eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
      (show (d : ℤ) = (d : ℤ) * 1 from by ring))

/-- The addition law of the tensor powers at `(n, 1)`, with the exponent of the target spelled
as the natural number `n + 1`: `𝒪_{U_d}(d)^{⊗ n} ⊗ 𝒪_{U_d}(d)^{⊗ 1} ≅ 𝒪_{U_d}(d)^{⊗ (n+1)}`. -/
def thetaStep (n : ℕ) :
    tensorModules (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) (n : ℤ))
        (tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) 1) ≅
      tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
        ((n + 1 : ℕ) : ℤ) :=
  tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ)) (n : ℤ) 1 ≪≫
    tensorPowModuleCongr (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
      (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) from by push_cast; ring)

/-- **The coherent family `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)`**, by induction on `n`. The step
splits `𝒪_{U_d}(d)^{⊗ (n+1)}` as `𝒪_{U_d}(d)^{⊗ n} ⊗ 𝒪_{U_d}(d)` by the addition law of Stacks
Tag 01CU, rewrites the two factors by the comparison in degree `n` and by `twistOneIso`, and
closes with the canonical multiplication isomorphism of
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso` at `(dn, d)`. Every step is
canonical: nothing is chosen in any degree. -/
def theta : (n : ℕ) →
    tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
        (n : ℤ) ≅
      twist 𝒮 d ((d : ℤ) * (n : ℤ))
  | 0 =>
      tensorPowModuleCongr (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) (show ((0 : ℕ) : ℤ) = 0 from by norm_num) ≪≫
        tensorPowModuleZeroIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) ≪≫
        (twistZeroIsoUnit 𝒮 d).symm ≪≫
        eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
          (show (0 : ℤ) = (d : ℤ) * ((0 : ℕ) : ℤ) from by push_cast; ring))
  | (n + 1) =>
      (thetaStep 𝒮 d n).symm ≪≫
        tensorModulesMapIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (theta n) (twistOneIso 𝒮 d) ≪≫
        twistMulIso 𝒮 d (n : ℤ) 1 ≪≫
        eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
          (show (d : ℤ) * ((n : ℤ) + 1) = (d : ℤ) * ((n + 1 : ℕ) : ℤ) from by push_cast; ring))

/-- **The recursion defining the family, as an equation of isomorphisms.** In degree `n + 1` the
comparison is the comparison in degree `n` tensored with `twistOneIso`, preceded by the inverse
of the addition law of the tensor powers and followed by the canonical multiplication
isomorphism. -/
theorem theta_succ (n : ℕ) :
    theta 𝒮 d (n + 1) =
      (thetaStep 𝒮 d n).symm ≪≫
        tensorModulesMapIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (theta 𝒮 d n) (twistOneIso 𝒮 d) ≪≫
        twistMulIso 𝒮 d (n : ℤ) 1 ≪≫
        eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
          (show (d : ℤ) * ((n : ℤ) + 1) = (d : ℤ) * ((n + 1 : ℕ) : ℤ) from
            by push_cast; ring)) :=
  rfl

/-- **Multiplicativity of the family in the last variable.** The addition law of the tensor
powers at `(n, 1)`, followed by the comparison in degree `n + 1`, is the comparison in degrees
`n` and `1` on the two factors followed by the canonical multiplication isomorphism at
`(dn, d)`: the recursion read as a commuting square. -/
theorem theta_mul_one (n : ℕ) :
    (thetaStep 𝒮 d n).hom ≫ (theta 𝒮 d (n + 1)).hom =
      (tensorModulesMapIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (theta 𝒮 d n) (twistOneIso 𝒮 d)).hom ≫
        (twistMulIso 𝒮 d (n : ℤ) 1).hom ≫
        eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
          (show (d : ℤ) * ((n : ℤ) + 1) = (d : ℤ) * ((n + 1 : ℕ) : ℤ) from by
            push_cast; ring)) := by
  rw [theta_succ]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, eqToIso.hom]

/-- **The coherent family, with the twist degree spelled as the `d`-th Veronese section ring
spells it**: `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(nd)` with `nd` a natural number. -/
def thetaNat (n : ℕ) :
    tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
        (n : ℤ) ≅
      twist 𝒮 d ((n * d : ℕ) : ℤ) :=
  theta 𝒮 d n ≪≫
    eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
      (show (d : ℤ) * (n : ℤ) = ((n * d : ℕ) : ℤ) from by push_cast; ring))

end Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen

end
