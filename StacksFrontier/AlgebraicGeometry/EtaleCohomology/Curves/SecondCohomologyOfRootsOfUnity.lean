module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionRootsOfUnity
import StacksCore.Tactic.StacksAttribute

/-!
# `H²_ét(X, μ_n)` of a smooth proper curve is cyclic of order `n`

Let `X` be a smooth proper curve over an algebraically closed field `k` and let `n` be invertible
in `k`.  Then `H²_étale(X, μ_n)` is cyclic of order `n`, and the isomorphism with `𝐙/n𝐙` is
normalised by the degree: the Kummer coboundary of a class in `H¹_étale(X, 𝐆_m)` has coordinate
the degree of the corresponding divisor class modulo `n`, and every class in `H²_étale(X, μ_n)`
is such a coboundary.

The argument is the source's.  The Kummer sequence `0 → μ_n → 𝐆_m → 𝐆_m → 0` places
`H²_étale(X, μ_n)` between `H¹_étale(X, 𝐆_m)` and `H²_étale(X, 𝐆_m)`.  The latter vanishes
([Stacks, Tag 03RM], the theorem
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`), so the
coboundary presents `H²_étale(X, μ_n)` as `H¹_étale(X, 𝐆_m)/n`.  On a smooth curve over an
algebraically closed field `H¹_étale(X, 𝐆_m)` is the divisor class group
(`Stacks.EtaleCohomology.sheafHOneMultiplicativeAddEquivClosedPointClassGroup`), and on a proper
such curve the degree makes that quotient `𝐙/n𝐙`: the class of a closed point has degree one, so
the degree is onto, and a class of degree divisible by `n` is `n` times a class, because a class
is congruent modulo `n` to its degree times the class of a fixed closed point
(`Stacks.EtaleCohomology.exists_sub_degree_nsmul_curveClassGroup`, which is the `n`-divisibility of
`Pic⁰` through the Jacobian, [Stacks, Tag 03RP]).

## Main definitions

The elided prefix throughout is `Stacks.EtaleCohomology`.

* `curveKummerCoboundary`: the Kummer coboundary `H¹_étale(X, 𝐆_m) ⟶ H²_étale(X, μ_n)`.
* `curveClassGroupDegreeMod`: the degree modulo `n` on the divisor class group.
* `sheafHOneMultiplicativeDegreeMod`: the degree modulo `n` of a class in `H¹_étale(X, 𝐆_m)`, read
  through the identification of that group with the divisor class group.
* `sheafHTwoRootsOfUnityAddEquivZMod`: the isomorphism `H²_étale(X, μ_n) ≃+ 𝐙/n𝐙`.

## Main results

* `exists_curveKummerCoboundary_eq`: every class in `H²_étale(X, μ_n)` is a Kummer coboundary.
* `curveKummerCoboundary_eq_zero_iff`: the coboundary kills exactly the `n`-th multiples.
* `sheafHTwoRootsOfUnityAddEquivZMod`: `H²_étale(X, μ_n)` is cyclic of order `n`.
* `sheafHTwoRootsOfUnityAddEquivZMod_curveKummerCoboundary`: the normalisation, that the
  coordinate of the coboundary of a class is the degree of that class modulo `n`.

## Implementation notes

Properness, dimension one and smoothness are carried separately rather than through a notion of
projective variety, because that is the shape in which the degree on the divisor class group
`Stacks.EtaleCohomology.curveClassGroupDegree` and the divisibility of its degree-zero part
consume them.  Over a field this is no loss: a smooth proper curve is projective.

The coordinate on `H²_étale(X, μ_n)` is normalised against the degree of a class in
`H¹_étale(X, 𝐆_m)`, not against the degree of a line bundle.  Translating it into line bundles
asks for the class map `Pic(X) → H¹_étale(X, 𝐆_m)` of [Stacks, Tag 03P8] on the *small étale*
site, which the library has only for the Zariski site
(`AlgebraicGeometry.zariskiH1UnitsAddEquivPicardGroup`); on a curve the composite
`H¹_étale(X, 𝐆_m) ≅ Cl(X) ≅ Pic(X)` is available
(`Stacks.EtaleCohomology.curveClassGroupAddEquivSchemePicard`), but it is an identification of
groups with no naturality in `X`, so it cannot be used to compare two curves.

Everything is at the coefficient universe `u + 1` and `Ext` universe `u + 1`, which is where the
divisor sequence of a curve is exact and where `H¹_étale(X, 𝐆_m)` is identified with the divisor
class group; `Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv` transports to a larger
coefficient universe.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ): the cohomology of `μ_n`
  on a smooth projective curve, whose `q = 2` clause is proved here.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the vanishing of
  `H^q_étale(X, 𝐆_m)` for `q ≥ 2` on a smooth curve.
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP): the divisibility of an
  abelian variety, which gives the divisibility of `Pic⁰`.
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL): the Kummer sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.EtaleCohomology

open Stacks.Kummer

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-! ### The Kummer coboundary of a smooth curve -/

section Coboundary

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] {n : ℕ} (hn : IsUnit (n : k))

/-- **The Kummer coboundary `H¹_étale(X, 𝐆_m) ⟶ H²_étale(X, μ_n)`** of a smooth curve over an
algebraically closed field in which `n` is invertible: composition with the extension class of
the Kummer sequence, with the two side conditions of
`Stacks.EtaleCohomology.kummerConnecting` supplied from invertibility of `n` in `k`. -/
def curveKummerCoboundary :
    Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 1 →+
      Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} X n) 2 :=
  kummerConnecting.{u, u + 1, u + 1} X (ne_zero_of_isUnit_natCast hn)
    (isUnit_natCast_globalSections_of_isUnit g hn) 1

/-- **Every class in `H²_étale(X, μ_n)` is a Kummer coboundary** on a smooth curve over an
algebraically closed field: the next term of the long exact sequence of the Kummer sequence is
`H²_étale(X, 𝐆_m)`, which vanishes by [Stacks, Tag 03RM]. -/
theorem exists_curveKummerCoboundary_eq
    (x : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} X n) 2) :
    ∃ a, curveKummerCoboundary g hn a = x := by
  have := subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ.{u, u + 1, u + 1} g 2 le_rfl
  exact exists_kummerConnecting_eq_of_rootsOfUnityInclusion_eq_zero.{u, u + 1, u + 1} X
    (ne_zero_of_isUnit_natCast hn) (isUnit_natCast_globalSections_of_isUnit g hn) 1 x
    (Subsingleton.elim _ _)

omit [IsAlgClosed k] [IsCurve k g] [Smooth g] in
/-- **The Kummer coboundary kills exactly the `n`-th multiples**: the previous map of the long
exact sequence of the Kummer sequence is multiplication by `n` on `H¹_étale(X, 𝐆_m)`. -/
@[sga "4½ Arcata 2.2.4" "partial"]
theorem curveKummerCoboundary_eq_zero_iff
    (a : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 1) :
    curveKummerCoboundary g hn a = 0 ↔ ∃ z, n • z = a :=
  ⟨exists_nsmul_eq_of_kummerConnecting_eq_zero.{u, u + 1, u + 1} X
      (ne_zero_of_isUnit_natCast hn) (isUnit_natCast_globalSections_of_isUnit g hn) 1 a,
    fun ⟨z, hz⟩ => hz ▸ kummerConnecting_nsmul.{u, u + 1, u + 1} X
      (ne_zero_of_isUnit_natCast hn) (isUnit_natCast_globalSections_of_isUnit g hn) 1 z⟩

end Coboundary

/-! ### The degree modulo `n` -/

section Degree

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] [IsProper g]

/-- **The degree modulo `n` on the divisor class group** of a smooth proper curve over an
algebraically closed field. -/
def curveClassGroupDegreeMod (n : ℕ) : curveClassGroup g →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp (curveClassGroupDegree g)

/-- `curveClassGroupDegreeMod` is the degree reduced modulo `n`. -/
@[simp]
theorem curveClassGroupDegreeMod_apply (n : ℕ) (c : curveClassGroup g) :
    curveClassGroupDegreeMod g n c = ((curveClassGroupDegree g c : ℤ) : ZMod n) :=
  rfl

/-- **The degree modulo `n` is onto**, because the class of a closed point has degree one. -/
theorem surjective_curveClassGroupDegreeMod {n : ℕ} (hn0 : n ≠ 0) :
    Function.Surjective (curveClassGroupDegreeMod g n) := by
  have : NeZero n := NeZero.mk hn0
  obtain ⟨x₀⟩ := nonempty_closedPoints_of_isCurve g
  intro m
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective (n := n) m
  refine ⟨z • (QuotientAddGroup.mk (Finsupp.single x₀ (1 : ℤ)) : curveClassGroup g), ?_⟩
  rw [curveClassGroupDegreeMod_apply, map_zsmul, curveClassGroupDegree_mk,
    Finsupp.sum_single_index rfl, smul_eq_mul, mul_one]

/-- **A class of degree divisible by `n` is `n` times a class.**  Every class is congruent modulo
`n` to its degree times the class of a fixed closed point, by the `n`-divisibility of `Pic⁰`
([Stacks, Tag 03RP] through the Jacobian), so a class whose degree is divisible by `n` differs
from an `n`-th multiple by `n` times a multiple of that point class. -/
theorem curveClassGroupDegreeMod_eq_zero_iff {n : ℕ} (hn : IsUnit (n : k))
    (c : curveClassGroup g) :
    curveClassGroupDegreeMod g n c = 0 ↔ ∃ d, n • d = c := by
  constructor
  · intro h
    obtain ⟨x₀⟩ := nonempty_closedPoints_of_isCurve g
    obtain ⟨d, hd⟩ := exists_sub_degree_nsmul_curveClassGroup g hn x₀ c
    rw [curveClassGroupDegreeMod_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨m, hm⟩ := h
    set P : curveClassGroup g := QuotientAddGroup.mk (Finsupp.single x₀ (1 : ℤ))
    refine ⟨d + m • P, ?_⟩
    have h₁ : n • m • P = curveClassGroupDegree g c • P := by
      rw [← natCast_zsmul, smul_smul, ← hm]
    rw [nsmul_add, h₁, ← hd]
    abel
  · rintro ⟨d, rfl⟩
    simp

/-- **The degree modulo `n` of a class in `H¹_étale(X, 𝐆_m)`**, read through the identification
of that group with the divisor class group of the curve. -/
def sheafHOneMultiplicativeDegreeMod (n : ℕ) :
    Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 1 →+ ZMod n :=
  (curveClassGroupDegreeMod g n).comp
    (sheafHOneMultiplicativeAddEquivClosedPointClassGroup g).toAddMonoidHom

/-- `sheafHOneMultiplicativeDegreeMod` is the degree modulo `n` of the divisor class attached to a
class in `H¹(X, 𝐆_m)`. -/
@[simp]
theorem sheafHOneMultiplicativeDegreeMod_apply (n : ℕ)
    (a : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 1) :
    sheafHOneMultiplicativeDegreeMod g n a =
      curveClassGroupDegreeMod g n (sheafHOneMultiplicativeAddEquivClosedPointClassGroup g a) :=
  rfl

/-- The degree modulo `n` on `H¹_étale(X, 𝐆_m)` is onto. -/
theorem surjective_sheafHOneMultiplicativeDegreeMod {n : ℕ} (hn0 : n ≠ 0) :
    Function.Surjective (sheafHOneMultiplicativeDegreeMod g n) :=
  (surjective_curveClassGroupDegreeMod g hn0).comp
    (sheafHOneMultiplicativeAddEquivClosedPointClassGroup g).surjective

/-- A class in `H¹_étale(X, 𝐆_m)` has degree divisible by `n` exactly when it is an `n`-th
multiple. -/
theorem sheafHOneMultiplicativeDegreeMod_eq_zero_iff {n : ℕ} (hn : IsUnit (n : k))
    (a : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 1) :
    sheafHOneMultiplicativeDegreeMod g n a = 0 ↔ ∃ z, n • z = a := by
  set e := sheafHOneMultiplicativeAddEquivClosedPointClassGroup g
  rw [sheafHOneMultiplicativeDegreeMod_apply, curveClassGroupDegreeMod_eq_zero_iff g hn]
  refine ⟨fun ⟨d, hd⟩ => ⟨e.symm d, ?_⟩, fun ⟨z, hz⟩ => ⟨e z, ?_⟩⟩
  · rw [← e.symm_apply_apply a, ← hd, map_nsmul]
  · rw [← hz, map_nsmul]

end Degree

/-! ### `H²_étale(X, μ_n)` is cyclic of order `n` -/

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] [IsProper g] {n : ℕ} (hn : IsUnit (n : k))

/-- The Kummer coboundary and the degree modulo `n` have the same kernel: both are the `n`-th
multiples of `H¹_étale(X, 𝐆_m)`. -/
theorem ker_curveKummerCoboundary_eq_ker_sheafHOneMultiplicativeDegreeMod :
    (curveKummerCoboundary g hn).ker = (sheafHOneMultiplicativeDegreeMod g n).ker := by
  ext a
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, curveKummerCoboundary_eq_zero_iff g hn a,
    sheafHOneMultiplicativeDegreeMod_eq_zero_iff g hn a]

/-- **[Stacks, Tag 03RQ], the case `q = 2`.**  Let `X` be a smooth proper curve over an
algebraically closed field `k` and let `n` be invertible in `k`.  Then `H²_étale(X, μ_n)` is
cyclic of order `n`.

The Kummer coboundary presents `H²_étale(X, μ_n)` as the quotient of `H¹_étale(X, 𝐆_m)` by its
`n`-th multiples — it is onto because `H²_étale(X, 𝐆_m) = 0` ([Stacks, Tag 03RM]) and its kernel
is the `n`-th multiples because the preceding map of the long exact sequence is multiplication by
`n` — and the degree identifies that quotient with `𝐙/n𝐙`, by
`Stacks.EtaleCohomology.ker_curveKummerCoboundary_eq_ker_sheafHOneMultiplicativeDegreeMod`.

The normalisation of this isomorphism is
`Stacks.EtaleCohomology.sheafHTwoRootsOfUnityAddEquivZMod_curveKummerCoboundary`. -/
@[stacks 03RQ "the q = 2 clause, that H^2_etale(X, mu_n) of a smooth proper curve over an \
algebraically closed field is cyclic of order n, normalised by the degree through \
sheafHTwoRootsOfUnityAddEquivZMod_curveKummerCoboundary; the q = 0 clause is \
AlgebraicGeometry.baseRootsToEtaleH0_bijective_of_isCurve and the q > 2 clause is \
subsingleton_sheafH_rootsOfUnitySheaf_of_smoothCurve, while the q = 1 clause awaits Stacks 03P8 \
for the small etale site", sga "4½ Arcata 6.2.1" "partial"]
def sheafHTwoRootsOfUnityAddEquivZMod :
    Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} X n) 2 ≃+ ZMod n :=
  (QuotientAddGroup.quotientKerEquivOfSurjective (curveKummerCoboundary g hn)
      (exists_curveKummerCoboundary_eq g hn)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq
        (ker_curveKummerCoboundary_eq_ker_sheafHOneMultiplicativeDegreeMod g hn)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective (sheafHOneMultiplicativeDegreeMod g n)
        (surjective_sheafHOneMultiplicativeDegreeMod g (ne_zero_of_isUnit_natCast hn))))

/-- **The normalisation of `Stacks.EtaleCohomology.sheafHTwoRootsOfUnityAddEquivZMod`**: the
coordinate of the Kummer coboundary of a class in `H¹_étale(X, 𝐆_m)` is the degree of that class
modulo `n`.  Together with
`Stacks.EtaleCohomology.exists_curveKummerCoboundary_eq`, which says that every class in
`H²_étale(X, μ_n)` is a coboundary, this fixes the isomorphism and not merely its existence. -/
@[stacks 03RQ "the normalisation of the q = 2 clause by the degree: the coordinate of the Kummer \
coboundary of a class of H^1_etale(X, G_m) is the degree of the corresponding divisor class \
modulo n"]
theorem sheafHTwoRootsOfUnityAddEquivZMod_curveKummerCoboundary
    (a : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 1) :
    sheafHTwoRootsOfUnityAddEquivZMod g hn (curveKummerCoboundary g hn a) =
      sheafHOneMultiplicativeDegreeMod g n a := by
  have h1 : (QuotientAddGroup.quotientKerEquivOfSurjective (curveKummerCoboundary g hn)
        (exists_curveKummerCoboundary_eq g hn)).symm
      (curveKummerCoboundary g hn a) = QuotientAddGroup.mk a := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [sheafHTwoRootsOfUnityAddEquivZMod, AddEquiv.trans_apply, h1,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

end Main

end Stacks.EtaleCohomology

end
