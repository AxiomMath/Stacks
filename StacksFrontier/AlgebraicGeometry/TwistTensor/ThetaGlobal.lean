module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaInteger
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic

/-!
# The comparison `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` on all of `Proj S`

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring and `X = Proj S`, and suppose that `X` is covered by
the standard opens of the degree-one homogeneous elements — Tag 01MT's hypothesis,
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.DegreeOneCover`. Then every twist `𝒪_X(c)` is
invertible on the whole of `X` and every multiplication map `𝒪_X(a) ⊗ 𝒪_X(b) ⟶ 𝒪_X(a + b)` is an
isomorphism on the whole of `X`, so the comparison between the tensor powers of `𝒪_X(d)` and the
`d`-divisible twists can be built on `X` itself.

`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta` and its integer extension
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt` are the same comparison on the degree `d` open
`U_d ⊆ X` of Tag 01N5, where goodness holds with no hypothesis on `S`. Under Tag 01MT's
hypothesis `U_d` is all of `X`, but `U_d` and `X` are different schemes, so the comparison does
not transfer by rewriting; what makes the global construction cheap is that the ingredients it
runs on are available globally in their own right, and in a simpler form, there being no pullback
along an open immersion to carry.

## Main definitions

* `Stacks.AlgebraicGeometry.ThetaGlobal.twist` — the twist `𝒪_X(c)`, at the ascribed type
  `(Proj S).Modules` the tensor-power calculus is written in.
* `Stacks.AlgebraicGeometry.ThetaGlobal.twistMulIso` — the canonical multiplication isomorphism
  `𝒪_X(dn) ⊗ 𝒪_X(dm) ≅ 𝒪_X(d(n + m))` on `X`, in every pair of integer degrees.
* `Stacks.AlgebraicGeometry.ThetaGlobal.theta` — **the comparison `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` on
  `X`** for a natural number `n`, by induction, and
  `Stacks.AlgebraicGeometry.ThetaGlobal.thetaNat`, the same with the twist degree spelled
  `(n * d : ℕ)` as the `d`-th Veronese section ring spells it.
* `Stacks.AlgebraicGeometry.ThetaGlobal.thetaInt` — **the same comparison for an arbitrary
  integer `n`**, the negative degrees obtained from the nonnegative ones by uniqueness of tensor
  inverses, `Stacks.Monoidal.isoOfTensorInverse`.

## Main results

* `Stacks.AlgebraicGeometry.ThetaGlobal.theta_succ` — the recursion, as an equation of
  isomorphisms.
* `Stacks.AlgebraicGeometry.ThetaGlobal.theta_mul_one` — multiplicativity of the family in the
  last variable: the recursion read as a commuting square. Multiplicativity in an **arbitrary**
  bidegree is `Stacks.AlgebraicGeometry.ThetaGlobalMul.theta_mul` in
  `StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaGlobalMultiplicativity.lean`, which runs the
  induction on top of this square.
* `Stacks.AlgebraicGeometry.ThetaGlobal.thetaInt_natCast`, `thetaInt_neg_natCast_succ` and
  `thetaInt_zero` — the integer comparison in terms of the one built by recursion.

## Implementation notes

Invertibility of `𝒪_X(d)` is a consequence of the covering hypothesis and so cannot be an
instance. It is taken as an instance *argument* instead: `Stacks.Ample.IsInvertibleModule` is a
`Prop`, so any two witnesses are definitionally equal and a caller may supply the one
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertibleModule_twistingSheaf` produces from
the covering hypothesis without creating a second family of tensor powers.

`twist` is an `abbrev` whose only content is the ascription of the type `(Proj S).Modules` to
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`, whose own type is spelled through
`sheafCompose` and `ProjectiveSpectrum.Proj.structureSheaf`. The monoidal structure of Tag 01CA
is registered on the former spelling, so the latter does not carry the notation `⊗` even though
the two are the same type; this is the same device as
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twist`.

The degree of the twist is spelled `(d : ℤ) * n` with an integer `n`, as on `U_d`, because that
is the spelling in which both halves of goodness are stated.

## References

* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample
open Stacks.RelativeVeryAmple

namespace Stacks.AlgebraicGeometry.ThetaGlobal

universe u w

open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover twistMultiplicationIso)
open Stacks.AlgebraicGeometry.ProjEulerSequence (twistingSheafZeroIsoUnit)

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (hcover : DegreeOneCover 𝒮) (d : ℕ)

/-- The twist `𝒪_X(c)` of `X = Proj S`, at the type ascription the tensor-power calculus uses. -/
abbrev twist (c : ℤ) : (AlgebraicGeometry.Proj 𝒮).Modules := twistingSheaf 𝒮 c

/-! ### The canonical multiplication isomorphism between the `d`-divisible twists -/

/-- **`𝒪_X(0) ≅ 𝒪_X`**, at the same type ascription. -/
def twistZeroIsoUnit : twist 𝒮 0 ≅ unitModule (AlgebraicGeometry.Proj 𝒮) :=
  twistingSheafZeroIsoUnit 𝒮

/-- **The canonical multiplication isomorphism on `Proj S`**,
`𝒪_X(dn) ⊗ 𝒪_X(dm) ≅ 𝒪_X(d(n + m))`, in every pair of integer degrees: Equation 01MO is an
isomorphism everywhere once the standard opens of the degree-one elements cover. -/
def twistMulIso (n m : ℤ) :
    tensorModules (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 ((d : ℤ) * n)) (twist 𝒮 ((d : ℤ) * m)) ≅
      twist 𝒮 ((d : ℤ) * (n + m)) :=
  twistMultiplicationIso 𝒮 hcover ((d : ℤ) * n) ((d : ℤ) * m) ≪≫
    eqToIso (congrArg (twist 𝒮)
      (show (d : ℤ) * n + (d : ℤ) * m = (d : ℤ) * (n + m) by ring))

variable [IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))]

/-! ### The tensor powers of the degree `d` twist -/

/-- The degree one tensor power of `𝒪_X(d)` is the twist of degree `d · 1`. -/
def twistOneIso :
    tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) 1 ≅ twist 𝒮 ((d : ℤ) * 1) :=
  tensorPowModuleOneIso (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) ≪≫
    eqToIso (congrArg (twist 𝒮) (show (d : ℤ) = (d : ℤ) * 1 by ring))

/-- The addition law of the tensor powers at `(n, 1)`, with the exponent of the target spelled as
the natural number `n + 1`. This is the splitting the induction below runs on. -/
def thetaStep (n : ℕ) :
    tensorModules (AlgebraicGeometry.Proj 𝒮)
        (tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (n : ℤ))
        (tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) 1) ≅
      tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) ((n + 1 : ℕ) : ℤ) :=
  tensorPowModuleAddIso (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (n : ℤ) 1 ≪≫
    tensorPowModuleCongr (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))
      (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring)

/-- **The comparison `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` on all of `Proj S`**, by induction on `n`. The
step splits `𝒪_X(d)^{⊗ (n+1)}` as `𝒪_X(d)^{⊗ n} ⊗ 𝒪_X(d)` by the addition law of Tag 01CU,
rewrites the two factors by the comparison in degree `n` and by `twistOneIso`, and closes with
the canonical multiplication isomorphism at `(dn, d)`. Every step is canonical. -/
def theta : (n : ℕ) →
    tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (n : ℤ) ≅
      twist 𝒮 ((d : ℤ) * (n : ℤ))
  | 0 =>
      tensorPowModuleCongr (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))
          (show ((0 : ℕ) : ℤ) = 0 by norm_num) ≪≫
        tensorPowModuleZeroIso (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) ≪≫
        (twistZeroIsoUnit 𝒮).symm ≪≫
        eqToIso (congrArg (twist 𝒮)
          (show (0 : ℤ) = (d : ℤ) * ((0 : ℕ) : ℤ) by push_cast; ring))
  | (n + 1) =>
      (thetaStep 𝒮 d n).symm ≪≫
        tensorModulesMapIso (AlgebraicGeometry.Proj 𝒮) (theta n) (twistOneIso 𝒮 d) ≪≫
        twistMulIso 𝒮 hcover d (n : ℤ) 1 ≪≫
        eqToIso (congrArg (twist 𝒮)
          (show (d : ℤ) * ((n : ℤ) + 1) = (d : ℤ) * ((n + 1 : ℕ) : ℤ) by push_cast; ring))

/-- **The recursion defining the family, as an equation of isomorphisms.** -/
theorem theta_succ (n : ℕ) :
    theta 𝒮 hcover d (n + 1) =
      (thetaStep 𝒮 d n).symm ≪≫
        tensorModulesMapIso (AlgebraicGeometry.Proj 𝒮) (theta 𝒮 hcover d n) (twistOneIso 𝒮 d) ≪≫
        twistMulIso 𝒮 hcover d (n : ℤ) 1 ≪≫
        eqToIso (congrArg (twist 𝒮)
          (show (d : ℤ) * ((n : ℤ) + 1) = (d : ℤ) * ((n + 1 : ℕ) : ℤ) from
            by push_cast; ring)) :=
  rfl

/-- **Multiplicativity of the family in the last variable**: the recursion read as a commuting
square, which is the statement a graded multiplicativity argument composes with. -/
theorem theta_mul_one (n : ℕ) :
    (thetaStep 𝒮 d n).hom ≫ (theta 𝒮 hcover d (n + 1)).hom =
      (tensorModulesMapIso (AlgebraicGeometry.Proj 𝒮) (theta 𝒮 hcover d n)
          (twistOneIso 𝒮 d)).hom ≫
        (twistMulIso 𝒮 hcover d (n : ℤ) 1).hom ≫
        eqToHom (congrArg (twist 𝒮)
          (show (d : ℤ) * ((n : ℤ) + 1) = (d : ℤ) * ((n + 1 : ℕ) : ℤ) from
            by push_cast; ring)) := by
  rw [theta_succ]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, eqToIso.hom]

/-- **The coherent family, with the twist degree spelled as the `d`-th Veronese section ring
spells it**: `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(nd)` with `nd` a natural number. -/
def thetaNat (n : ℕ) :
    tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (n : ℤ) ≅
      twist 𝒮 ((n * d : ℕ) : ℤ) :=
  theta 𝒮 hcover d n ≪≫
    eqToIso (congrArg (twist 𝒮)
      (show (d : ℤ) * (n : ℤ) = ((n * d : ℕ) : ℤ) by push_cast; ring))

/-! ### The comparison in a negative degree -/

/-- **The tensor powers in the degrees `n` and `-n` are tensor inverses.** -/
def tensorPowModuleInvIso (n : ℤ) :
    tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) n ⊗
        tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (-n) ≅
      𝟙_ (AlgebraicGeometry.Proj 𝒮).Modules :=
  tensorPowModuleAddIso (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) n (-n) ≪≫
    tensorPowModuleCongr (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))
      (show n + -n = 0 by ring) ≪≫
    tensorPowModuleZeroIso (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))

/-- **The `d`-divisible twists in the degrees `-dn` and `dn` are tensor inverses.** -/
def twistInvIso (n : ℤ) :
    twist 𝒮 ((d : ℤ) * (-n)) ⊗ twist 𝒮 ((d : ℤ) * n) ≅
      𝟙_ (AlgebraicGeometry.Proj 𝒮).Modules :=
  twistMulIso 𝒮 hcover d (-n) n ≪≫
    eqToIso (congrArg (twist 𝒮) (show (d : ℤ) * (-n + n) = 0 by ring)) ≪≫
    twistZeroIsoUnit 𝒮

/-- **The comparison `𝒪_X(d)^{⊗ (-m)} ≅ 𝒪_X(-dm)` in the degree `-m` for a natural number `m`**:
the isomorphism that the comparison in the degree `m` induces on the tensor inverses. -/
def thetaNegNat (m : ℕ) :
    tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (-(m : ℤ)) ≅
      twist 𝒮 ((d : ℤ) * (-(m : ℤ))) :=
  Stacks.Monoidal.isoOfTensorInverse (theta 𝒮 hcover d m) (tensorPowModuleInvIso 𝒮 d (m : ℤ))
    (twistInvIso 𝒮 hcover d (m : ℤ))

/-- **The comparison `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` on all of `Proj S`, in every integer degree.** In
a nonnegative degree it is the comparison built by recursion; in a negative degree it is the
comparison induced on the tensor inverses. -/
def thetaInt : (n : ℤ) →
    tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) n ≅ twist 𝒮 ((d : ℤ) * n)
  | .ofNat m => theta 𝒮 hcover d m
  | .negSucc m => thetaNegNat 𝒮 hcover d (m + 1)

/-- In a nonnegative degree the integer comparison is the comparison built by recursion. -/
theorem thetaInt_natCast (m : ℕ) : thetaInt 𝒮 hcover d (m : ℤ) = theta 𝒮 hcover d m := rfl

/-- In a negative degree the integer comparison is the comparison induced on the tensor
inverses. -/
theorem thetaInt_neg_natCast_succ (m : ℕ) :
    thetaInt 𝒮 hcover d (-((m : ℤ) + 1)) = thetaNegNat 𝒮 hcover d (m + 1) := rfl

/-- The integer comparison in the degree `0` is the comparison in the degree `0`. -/
theorem thetaInt_zero : thetaInt 𝒮 hcover d 0 = theta 𝒮 hcover d 0 := rfl

end Stacks.AlgebraicGeometry.ThetaGlobal

end
