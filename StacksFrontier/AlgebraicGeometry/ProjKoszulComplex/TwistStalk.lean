module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Contraction
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwistStalk

/-!
# Twisting sheaves at a stalk: trivialization in every degree, and multiplication

Let `S` be a nonnegatively graded ring, `X = Proj(S)`, let `x` be a point of `X`, that is a
homogeneous prime `p` not containing the irrelevant ideal, and let `f ∈ S₁` be a degree-one
element with `f ∉ p`. Then `f` becomes a unit of the localization of `S` at `p`, and its
integer powers identify all the twists with one another at `x`:

`(S(d))₍p₎ ≅ (S(d + m))₍p₎` for every `d, m : ℤ`,

multiplication by `f ^ m` raising the difference of the degrees of numerator and denominator
by exactly `m`. Taking `m = -d` and composing with the tautological identification of the
degree-zero part of the untwisted module with the local ring `S₍p₎`, **the stalk of `𝒪_X(d)`
at `x` is the stalk of `𝒪_X` at `x`, for every integer `d`.**

Through that trivialization, multiplication by a homogeneous element `a` of degree `k`,
`𝒪_X(d) ⟶ 𝒪_X(k + d)`, becomes multiplication by the degree-zero fraction `a / f ^ k` of the
local ring: on a germ represented by `m / s`, the source is trivialized to `f ^ (-d) m / s`,
the image germ is `a m / s`, and the target is trivialized to `f ^ (-k-d) a m / s`, which is
`(a / f ^ k)` times the former. Finally the multiplication maps compose by multiplying the
elements, which is what makes a complex out of them.

These are the local data of the Koszul complex of the coordinates on projective space: the
differentials of that complex are built from the multiplication maps, and their local form is
read off at a stalk through the trivializations constructed here.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftIntOf`: multiplication by a
  homogeneous element of degree `k`, as a morphism `𝒪(d) ⟶ 𝒪(e)` for any integer `e` equal to
  `k + d`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.fiberUnit` and
  `Stacks.AlgebraicGeometry.ProjKoszulComplex.zpowFiber`: a degree-one element outside the
  homogeneous prime of `x`, as a unit of the localization there, and its integer powers.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.mulZPowTwistEquiv`: multiplication by `f ^ m` as
  a linear equivalence from the `d`-th to the `(d + m)`-th twist at `x`, for `m` an integer.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.twistTrivEquiv`: the degree-zero part of `S(d)`
  at `x`, identified with the local ring `S₍p₎`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.twistingSheafStalkEquiv`: the stalk of `𝒪_X(d)`
  at `x` is the stalk of `𝒪_X` at `x`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.twistRatio`: the degree-zero fraction `a / f ^ k`
  of the local ring at `x`, for `a` homogeneous of degree `k`.

## Main results

* `Stacks.AlgebraicGeometry.ProjKoszulComplex.zpowFiber_smul_mem_degreeZeroModuleAt`:
  multiplication by `f ^ m` raises the twist by `m`, for every integer `m`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.val_twistingSheafStalkEquiv_germ`: the
  trivialization sends the germ of a section with value `m / s` at `x` to `f ^ (-d) m / s`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.twistingSheafStalkEquiv_stalkMap_twistMulLeftInt`:
  **the stalk at `x` of multiplication by `a`, read through the trivializations of `𝒪_X(d)` and
  `𝒪_X(k + d)` by `f`, is multiplication by `a / f ^ k`.**
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftIntOf_comp`,
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt_comp` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt_comp_apply`: multiplication by `a`
  of degree `k` followed by multiplication by `b` of degree `l` is multiplication by `b * a`,
  as morphisms and on the value of a section at a point.

## Implementation notes

The `ℕ`-indexed comparisons of twists are
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.mulPowTwistEquiv` and the two membership
lemmas around it; the integer-indexed comparison here is obtained from them by a single case
split, in `zpowFiber_smul_mem_degreeZeroModuleAt`, after which nothing downstream splits on
the sign of a degree. That is why `zpowFiber` is the value of a power of a *unit* rather than a
quotient of two natural-number powers: the compatibility formula for multiplication then
reduces to `f ^ (-(k + d)) = f ^ (-k) · f ^ (-d)` and one application of `ring` in the single
localization `Localization p.primeCompl`.

All equivalences on degree-zero parts are linear over `HomogeneousLocalization.AtPrime 𝒮 p`,
the ring `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroModuleAt` is a
`Submodule` over; the stalk-level statements read them over the structure-sheaf stalk, which
acts through `AlgebraicGeometry.Proj.stalkIso'`. The module structure in the type of
`degreeZeroModuleAt` is introduced by `letI` in that declaration's statement, so the two local
instances `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.fiberModule` and
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.stalkModuleDegreeZeroModuleAt` are
re-enabled here rather than restated.

`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt` has target degree spelled `k + d`,
so a composite of two of them has target `l + (k + d)` while multiplication by the product has
target `(l + k) + d`. The two integers are equal but not definitionally so, and transporting a
morphism along an equality of twisting sheaves is exactly the `eqToHom` friction the Euler
sequence files avoid. `twistMulLeftIntOf` therefore carries its target degree as a parameter
together with a proof that it is `k + d`; since that proof is a proposition, it is
definitionally the old map whenever the degree is spelled `k + d`, and composites can be
stated with every degree named and no cast.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- Multiplication by a homogeneous element `a` of degree `k`, as a morphism
`𝒪_{Proj 𝒮}(d) ⟶ 𝒪_{Proj 𝒮}(e)` of twisting sheaves, where `e` is any integer equal to
`k + d`. Naming the target degree rather than computing it lets composites be stated with no
transport along an equality of degrees. -/
def twistMulLeftIntOf {k : ℕ} (a : 𝒮 k) (d e : ℤ) (he : (k : ℤ) + d = e) :
    twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e :=
  Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap 𝒮
    (twistGrading (S := S) 𝒮 d) (twistGrading (S := S) 𝒮 e)
    (LinearMap.mulLeft S (a : S)) <| by
      intro j y hy
      have h := mul_mem_integerGrading 𝒮 a.2 (j := j + d) hy
      rwa [show (k : ℤ) + (j + d) = j + e by omega] at h

/-- At the target degree spelled `k + d`, multiplication by `a` with a named target degree is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt`. -/
theorem twistMulLeftIntOf_self {k : ℕ} (a : 𝒮 k) (d : ℤ) :
    twistMulLeftIntOf 𝒮 a d ((k : ℤ) + d) rfl = twistMulLeftInt 𝒮 a d :=
  rfl

/-- Localized multiplication by two ring elements in turn is localized multiplication by their
product. -/
private theorem map_mulLeft_map_mulLeft {P : Submonoid S} (u v : S)
    (z : LocalizedModule P S) :
    LocalizedModule.map P (LinearMap.mulLeft S u)
        (LocalizedModule.map P (LinearMap.mulLeft S v) z) =
      LocalizedModule.map P (LinearMap.mulLeft S (u * v)) z := by
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
    exact congrArg (fun y => LocalizedModule.mk y s) (mul_assoc u v m).symm

/-- **Multiplication maps compose by multiplying the elements.** Multiplication by `a` of
degree `k` followed by multiplication by `b` of degree `l` is multiplication by `b * a`, which
has degree `l + k`. -/
theorem twistMulLeftIntOf_comp {k l : ℕ} (a : 𝒮 k) (b : 𝒮 l) (d e g : ℤ)
    (he : (k : ℤ) + d = e) (hg : (l : ℤ) + e = g) :
    twistMulLeftIntOf 𝒮 a d e he ≫ twistMulLeftIntOf 𝒮 b e g hg =
      twistMulLeftIntOf 𝒮 ⟨(b : S) * (a : S), SetLike.mul_mem_graded b.2 a.2⟩ d g
        (by push_cast; omega) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext ?_)
  ext y
  exact Subtype.ext (funext fun p => map_mulLeft_map_mulLeft (b : S) (a : S) (y.1 p))

/-- **Multiplication maps compose by multiplying the elements**, read on the value of a section
at a point: `b · (a · z) = (b * a) · z` in every fibre. The two sides of the composition
identity lie in the same fibre, so this spelling needs no comparison of the target degrees
`l + (k + d)` and `(l + k) + d`. -/
theorem twistMulLeftInt_comp_apply {k l : ℕ} (a : 𝒮 k) (b : 𝒮 l) (d : ℤ)
    (U : (TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (s : (twistingSheaf 𝒮 d).val.obj U) (p : U.unop) :
    ((twistMulLeftInt 𝒮 b ((k : ℤ) + d)).val.app U
        ((twistMulLeftInt 𝒮 a d).val.app U s)).1 p =
      ((twistMulLeftInt 𝒮 ⟨(b : S) * (a : S), SetLike.mul_mem_graded b.2 a.2⟩ d).val.app U
        s).1 p :=
  map_mulLeft_map_mulLeft (b : S) (a : S) (s.1 p)

/-- **Multiplication maps compose by multiplying the elements**, in the spelling where the
intermediate degree is `k + d`: the target of the composite is `l + (k + d)`, which is the
degree `(l + k) + d` of multiplication by `b * a`. -/
theorem twistMulLeftInt_comp {k l : ℕ} (a : 𝒮 k) (b : 𝒮 l) (d : ℤ) :
    twistMulLeftInt 𝒮 a d ≫ twistMulLeftInt 𝒮 b ((k : ℤ) + d) =
      twistMulLeftIntOf 𝒮 ⟨(b : S) * (a : S), SetLike.mul_mem_graded b.2 a.2⟩ d
        ((l : ℤ) + ((k : ℤ) + d)) (by push_cast; ring) :=
  twistMulLeftIntOf_comp 𝒮 a b d ((k : ℤ) + d) ((l : ℤ) + ((k : ℤ) + d)) rfl rfl

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjKoszulComplex

universe u w

open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The homogeneous ideal of a point `x` of `Proj 𝒮`, viewed as an ideal of `S`, is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

attribute [local instance] fiberModule stalkModuleDegreeZeroModuleAt

/-- Multiplication in the fibre at `x` is multiplication in the localization of `S` at the
homogeneous prime of `x`: the fibre of the regular module and that localization are the same
ring. -/
private theorem mulFiber_eq_mul (x : ProjectiveSpectrum.top 𝒮)
    (u z : Localization x.asHomogeneousIdeal.toIdeal.primeCompl) :
    mulFiber 𝒮 x u z = u * z :=
  rfl

variable {f : S}

/-! ### Integer powers of a trivializing element -/

/-- A degree-one element `f` outside the homogeneous prime of `x`, as a unit of the
localization of `S` at that prime. -/
def fiberUnit (f : S) {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal) :
    (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)ˣ where
  val := powFiber 𝒮 f 1 x
  inv := powFiberInv 𝒮 f 1 hx
  val_inv := powFiber_mul_powFiberInv 𝒮 1 hx
  inv_val := powFiberInv_mul_powFiber 𝒮 1 hx

/-- The integer power `f ^ m` in the localization of `S` at the homogeneous prime of `x`, which
makes sense for negative `m` because `f` is a unit there. -/
def zpowFiber (f : S) {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal) (m : ℤ) :
    Localization x.asHomogeneousIdeal.toIdeal.primeCompl :=
  ((fiberUnit 𝒮 f hx ^ m : (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)ˣ) :
    Localization x.asHomogeneousIdeal.toIdeal.primeCompl)

/-- The zeroth power of `f` is `1`. -/
@[simp] theorem zpowFiber_zero {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) : zpowFiber 𝒮 f hx 0 = 1 := by
  rw [zpowFiber, zpow_zero, Units.val_one]

/-- Integer powers of `f` add exponents. -/
theorem zpowFiber_add {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal)
    (m n : ℤ) :
    zpowFiber 𝒮 f hx (m + n) = zpowFiber 𝒮 f hx m * zpowFiber 𝒮 f hx n := by
  rw [zpowFiber, zpowFiber, zpowFiber, zpow_add, Units.val_mul]

/-- A nonnegative power of `f` is the fraction `f ^ k / 1`. -/
theorem zpowFiber_natCast {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal)
    (k : ℕ) : zpowFiber 𝒮 f hx (k : ℤ) = powFiber 𝒮 f k x := by
  rw [zpowFiber, zpow_natCast, Units.val_pow_eq_pow_val]
  show (powFiber 𝒮 f 1 x) ^ k = _
  rw [powFiber, powFiber, Localization.mk_pow, pow_one, one_pow]

/-- A negative power of `f` is the fraction `1 / f ^ k`. -/
theorem zpowFiber_neg_natCast {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal)
    (k : ℕ) : zpowFiber 𝒮 f hx (-(k : ℤ)) = powFiberInv 𝒮 f k hx := by
  rw [zpowFiber, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  show (powFiberInv 𝒮 f 1 hx) ^ k = _
  rw [powFiberInv, powFiberInv, Localization.mk_pow, one_pow]
  exact congrArg (Localization.mk 1) (Subtype.ext (by simp))

/-- **Multiplication by `f ^ m` raises the twist by `m`**, for every integer `m`: a positive
power multiplies the numerator of a degree-zero fraction of `S(d)` and a negative power
multiplies its denominator, and in both cases the difference of the degrees of numerator and
denominator moves by exactly `m`. -/
theorem zpowFiber_smul_mem_degreeZeroModuleAt (hf : f ∈ 𝒮 1)
    {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal) (d m : ℤ)
    {z : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x}
    (hz : z ∈ degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x) :
    mulFiber 𝒮 x (zpowFiber 𝒮 f hx m) z ∈
      degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (d + m)) x := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpowFiber_natCast]
    exact powFiber_smul_mem_degreeZeroModuleAt 𝒮 hf k d x hz
  · rw [zpowFiber_neg_natCast, show d + -(k : ℤ) = d - (k : ℤ) by ring]
    refine powFiberInv_smul_mem_degreeZeroModuleAt 𝒮 hf k (d - (k : ℤ)) hx ?_
    rw [show d - (k : ℤ) + ((k : ℕ) : ℤ) = d by ring]
    exact hz

/-! ### Trivializing the twists at a stalk -/

/-- **Multiplication by `f ^ m` identifies the twist by `d` with the twist by `d + m` at `x`**,
for every integer `m`. This is the integer-indexed form of
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.mulPowTwistEquiv`. -/
def mulZPowTwistEquiv (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) (d m : ℤ) :
    degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x
      ≃ₗ[HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal]
        degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (d + m)) x :=
  LinearEquiv.ofLinearMap
    ((mulFiber 𝒮 x (zpowFiber 𝒮 f hx m)).restrict
      (fun _ hz => zpowFiber_smul_mem_degreeZeroModuleAt 𝒮 hf hx d m hz))
    ((mulFiber 𝒮 x (zpowFiber 𝒮 f hx (-m))).restrict
      (fun _ hz => by
        have h := zpowFiber_smul_mem_degreeZeroModuleAt 𝒮 hf hx (d + m) (-m) hz
        rwa [show d + m + -m = d by ring] at h))
    (LinearMap.ext fun z => Subtype.ext (by
      change mulFiber 𝒮 x (zpowFiber 𝒮 f hx m)
        (mulFiber 𝒮 x (zpowFiber 𝒮 f hx (-m)) (z : _)) = (z : _)
      rw [mulFiber_mulFiber, ← zpowFiber_add, add_neg_cancel, zpowFiber_zero, mulFiber_one]))
    (LinearMap.ext fun z => Subtype.ext (by
      change mulFiber 𝒮 x (zpowFiber 𝒮 f hx (-m))
        (mulFiber 𝒮 x (zpowFiber 𝒮 f hx m) (z : _)) = (z : _)
      rw [mulFiber_mulFiber, ← zpowFiber_add, neg_add_cancel, zpowFiber_zero, mulFiber_one]))

/-- **The degree-zero part of `S(d)` at `x` is the local ring `S₍ₓ₎`**, for every integer `d`,
identified by multiplication by `f ^ (-d)` for a degree-one element `f` outside the homogeneous
prime of `x`. -/
def twistTrivEquiv (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) (d : ℤ) :
    degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x
      ≃ₗ[HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal]
        HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal :=
  ((mulZPowTwistEquiv 𝒮 hf hx d (-d)).trans
    (LinearEquiv.ofEq _ _ (by rw [add_neg_cancel]))).trans
      (degreeZeroModuleAtZeroEquiv 𝒮 x).symm

/-- **The computation rule for the trivialization of `S(d)`**: the degree-zero fraction `m / s`
is sent to the degree-zero fraction `f ^ (-d) m / s`. -/
theorem val_twistTrivEquiv_mk (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) (d : ℤ) {m : S}
    {s : x.asHomogeneousIdeal.toIdeal.primeCompl}
    (hz : LocalizedModule.mk m s ∈ degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x) :
    HomogeneousLocalization.val
        (twistTrivEquiv 𝒮 hf hx d ⟨LocalizedModule.mk m s, hz⟩) =
      zpowFiber 𝒮 f hx (-d) * Localization.mk m s := by
  have h : HomogeneousLocalization.val
      (twistTrivEquiv 𝒮 hf hx d ⟨LocalizedModule.mk m s, hz⟩) =
      mulFiber 𝒮 x (zpowFiber 𝒮 f hx (-d)) (Localization.mk m s) :=
    val_degreeZeroModuleAtZeroEquiv_symm 𝒮 x _
  rw [h, mulFiber_eq_mul]

/-- The computation rule in the form used at a stalk: an element of the degree-zero part of
`S(d)` whose fraction is `m / s` is sent to the degree-zero fraction `f ^ (-d) m / s`. -/
theorem val_twistTrivEquiv (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) (d : ℤ)
    (w : degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x) {m : S}
    {s : x.asHomogeneousIdeal.toIdeal.primeCompl}
    (hw : (w : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) =
      LocalizedModule.mk m s) :
    HomogeneousLocalization.val (twistTrivEquiv 𝒮 hf hx d w) =
      zpowFiber 𝒮 f hx (-d) * Localization.mk m s := by
  obtain ⟨w, hwmem⟩ := w
  subst hw
  exact val_twistTrivEquiv_mk 𝒮 hf hx d hwmem

/-- The trivialization of the degree-zero part of `S(d)` at `x`, read over the structure-sheaf
stalk: the stalk acts on both sides through `AlgebraicGeometry.Proj.stalkIso'`. -/
def twistStalkLinearEquiv (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) (d : ℤ) :
    degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x
      ≃ₗ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x]
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x where
  toFun z := (Proj.stalkIso' 𝒮 x).symm (twistTrivEquiv 𝒮 hf hx d z)
  invFun c := (twistTrivEquiv 𝒮 hf hx d).symm (Proj.stalkIso' 𝒮 x c)
  map_add' _ _ := by simp
  map_smul' c z := by
    change (Proj.stalkIso' 𝒮 x).symm
        (twistTrivEquiv 𝒮 hf hx d ((Proj.stalkIso' 𝒮 x c) • z)) =
      c * (Proj.stalkIso' 𝒮 x).symm (twistTrivEquiv 𝒮 hf hx d z)
    rw [map_smul]
    change (Proj.stalkIso' 𝒮 x).symm
      ((Proj.stalkIso' 𝒮 x c) * twistTrivEquiv 𝒮 hf hx d z) = _
    rw [map_mul, RingEquiv.symm_apply_apply]
  left_inv _ := by simp
  right_inv _ := by simp

/-- **The stalk of `𝒪(d)` at `x` is the stalk of `𝒪` at `x`**, for every integer `d`. The
identification is multiplication by `f ^ (-d)` for a degree-one element `f` of `S` outside the
homogeneous prime of `x`, which is a unit of the local ring there and lowers the twist from `d`
to `0`. -/
def twistingSheafStalkEquiv (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) (d : ℤ) :
    associatedModuleSheafStalk 𝒮 (twistGrading (S := S) 𝒮 d) x
      ≃ₗ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x]
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x :=
  (associatedModuleSheafStalkLinearEquiv 𝒮 (twistGrading (S := S) 𝒮 d) x).trans
    (twistStalkLinearEquiv 𝒮 hf hx d)

/-- **The computation rule at a stalk**: if a section `a` of `𝒪(d)` over a neighbourhood of `x`
has value `z` at `x`, its germ is sent to the germ of `𝒪` whose value at `x` is `f ^ (-d) z`. -/
theorem val_twistingSheafStalkEquiv_germ (hf : f ∈ 𝒮 1)
    {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal) (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (hxU : x ∈ U)
    (a : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮
      (twistGrading (S := S) 𝒮 d)).val.obj (op U))
    {m : S} {s : x.asHomogeneousIdeal.toIdeal.primeCompl}
    (ha : ((ProjectiveSpectrum.Proj.associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 d) U).toFun a).1 ⟨x, hxU⟩ = LocalizedModule.mk m s) :
    HomogeneousLocalization.val (Proj.stalkIso' 𝒮 x
        (twistingSheafStalkEquiv 𝒮 hf hx d
          (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 d) x U hxU a))) =
      zpowFiber 𝒮 f hx (-d) * Localization.mk m s := by
  have h : twistingSheafStalkEquiv 𝒮 hf hx d
      (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 d) x U hxU a) =
      (Proj.stalkIso' 𝒮 x).symm (twistTrivEquiv 𝒮 hf hx d
        (associatedModuleSheafStalkEquiv 𝒮 (twistGrading (S := S) 𝒮 d) x
          (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 d) x U hxU a))) := rfl
  rw [h, RingEquiv.apply_symm_apply]
  exact val_twistTrivEquiv 𝒮 hf hx d _
    ((associatedModuleSheafStalkEquiv_germ 𝒮 (twistGrading (S := S) 𝒮 d) x U hxU a).trans ha)

/-! ### Multiplication at a stalk -/

/-- **The degree-zero fraction `a / f ^ k` of the local ring at `x`**, for `a` homogeneous of
degree `k` and `f` of degree one outside the homogeneous prime of `x`. It is the local form of
multiplication by `a`, read through the trivializations of the twisting sheaves by `f`. -/
def twistRatio (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) {k : ℕ} (a : 𝒮 k) :
    HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalization.mk
    ⟨k, ⟨(a : S), a.2⟩,
      ⟨f ^ k, by simpa using ProjTrivialization.pow_toNat_mem 𝒮 hf k⟩,
      x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx k⟩

/-- The ratio `a / f ^ k` is the fraction `a / f ^ k` of the local ring at `x`. -/
theorem val_twistRatio (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) {k : ℕ} (a : 𝒮 k) :
    HomogeneousLocalization.val (twistRatio 𝒮 hf hx a) =
      Localization.mk (a : S)
        ⟨f ^ k, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx k⟩ :=
  HomogeneousLocalization.val_mk _

/-- The ratio `a / f ^ k` is `a` times the `(-k)`-th power of `f`. -/
theorem val_twistRatio_eq_mul (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) {k : ℕ} (a : 𝒮 k) :
    HomogeneousLocalization.val (twistRatio 𝒮 hf hx a) =
      Localization.mk (a : S) 1 * zpowFiber 𝒮 f hx (-(k : ℤ)) := by
  rw [val_twistRatio, zpowFiber_neg_natCast, powFiberInv, Localization.mk_mul, mul_one,
    one_mul]

/-- **The stalk at `x` of multiplication by a homogeneous element `a` of degree `k` is
multiplication by `a / f ^ k`**, once the stalks of `𝒪(d)` and of `𝒪(k + d)` are identified
with the local ring at `x` by the trivializing element `f`. On a germ represented by the
fraction `m / s`, the left-hand side is `f ^ (-k-d) a m / s` and the right-hand side is
`(a / f ^ k) · (f ^ (-d) m / s)`. -/
theorem twistingSheafStalkEquiv_stalkMap_twistMulLeftInt (hf : f ∈ 𝒮 1)
    {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal) (d : ℤ) {k : ℕ}
    (a : 𝒮 k)
    (z : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (ProjTrivialization.projRingSheaf 𝒮) x (twistingSheaf 𝒮 d))) :
    twistingSheafStalkEquiv 𝒮 hf hx ((k : ℤ) + d)
        ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (ProjTrivialization.projRingSheaf 𝒮) x (twistMulLeftInt 𝒮 a d)).hom z) =
      (Proj.stalkIso' 𝒮 x).symm (twistRatio 𝒮 hf hx a) *
        twistingSheafStalkEquiv 𝒮 hf hx d z := by
  obtain ⟨U, hxU, b, hb⟩ := associatedModuleSheafStalk_exists_germ 𝒮
    (twistGrading (S := S) 𝒮 d) x z
  subst hb
  obtain ⟨V, hxV, iV, j, m, t, hm, ht, hn, hfrac⟩ := b.2 ⟨x, hxU⟩
  have htx : t ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hn ⟨x, hxV⟩
  have hbx : b.1 ⟨x, hxU⟩ = LocalizedModule.mk m ⟨t, htx⟩ := by
    simpa using hfrac ⟨x, hxV⟩
  have hgerm : (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
        (ProjTrivialization.projRingSheaf 𝒮) x (twistMulLeftInt 𝒮 a d)).hom
      (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 d) x U hxU b) =
      associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 ((k : ℤ) + d)) x U hxU
        ((twistMulLeftInt 𝒮 a d).val.app (op U) b) :=
    _root_.AlgebraicGeometry.SheafOfModules.stalkMap_germ
      (ProjTrivialization.projRingSheaf 𝒮) x (twistMulLeftInt 𝒮 a d) U hxU b
  have hval : ((twistMulLeftInt 𝒮 a d).val.app (op U) b).1 ⟨x, hxU⟩ =
      LocalizedModule.mk ((a : S) * m) ⟨t, htx⟩ := by
    rw [twistMulLeftInt_apply, hbx, LocalizedModule.map_mk]
    rfl
  refine (Proj.stalkIso' 𝒮 x).injective (HomogeneousLocalization.val_injective _ ?_)
  rw [hgerm, val_twistingSheafStalkEquiv_germ 𝒮 hf hx _ U hxU
      ((twistMulLeftInt 𝒮 a d).val.app (op U) b) hval, map_mul,
    HomogeneousLocalization.val_mul, RingEquiv.apply_symm_apply, val_twistRatio_eq_mul,
    val_twistingSheafStalkEquiv_germ 𝒮 hf hx d U hxU b hbx,
    show -((k : ℤ) + d) = -(k : ℤ) + -d by ring, zpowFiber_add,
    show (Localization.mk ((a : S) * m) ⟨t, htx⟩ :
        Localization x.asHomogeneousIdeal.toIdeal.primeCompl) =
      Localization.mk (a : S) 1 * Localization.mk m ⟨t, htx⟩ from by
    rw [Localization.mk_mul, one_mul]]
  ring

end Stacks.AlgebraicGeometry.ProjKoszulComplex

end
