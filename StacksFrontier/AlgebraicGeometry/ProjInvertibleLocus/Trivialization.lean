module

public import StacksFrontier.AlgebraicGeometry.ProjShared.InvertibleLocus
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisting sheaves are trivial on `D₊(pq)` when `deg p = deg q + d`

Let `S` be a graded ring, `X = Proj(S)` and let `p ∈ S_{e+d}`, `q ∈ S_e` be homogeneous. On the
standard open `D₊(pq)` both `p` and `q` are invertible, so the ratio `p/q` is a unit of degree
`d` of every local ring, and for every integer `n` the twisting sheaf `𝒪_X(nd)` is trivialized
on `D₊(pq)` by the section `(p/q)^n`.

This is the input that Tag 01MU's first inclusion needs, and it is strictly more than Tag 01MS
gives: 01MS trivializes `𝒪(nd)` on `D₊(f)` for `f` of degree `d`, which is the special case
`q = 1`, `e = 0`. The degree difference `d` is realized here by a *ratio* of two homogeneous
elements of possibly large degree, which is the whole point of Tag 01MU — a graded ring need
have no homogeneous element of degree `d` at all and still have `W_d = X`.

The trivialization is produced on the restricted site `Over U` of `Opens ↥(Proj S)`, i.e. for
Mathlib's `SheafOfModules.over`, exactly as `Stacks.AlgebraicGeometry.ProjTrivialization` does
for Tag 01MS. `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_pullback_of_iso_unit`
transports it to the open-subscheme spelling `Scheme.Modules.pullback U.ι` in which Tag 01MU
states invertibility.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioFun`: the value of `(p/q)^n` in the local
  ring at a point of `D₊(pq)`.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioSection`: that value as a section of
  `𝒪(nd)`.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioOverIsoUnit`: the trivialization
  `𝒪(nd)|_{D₊(pq)} ≅ 𝒪|_{D₊(pq)}` on the restricted site.

## Main results

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.bijective_ratioHom`: the arithmetic heart —
  multiplication by `(p/q)^n` is a bijection `Γ(W, 𝒪) → Γ(W, 𝒪(nd))` for every open
  `W ⊆ D₊(pq)`.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioEquiv`: the resulting identification of
  the sections of `𝒪` and of `𝒪(nd)` over every open contained in `D₊(pq)`.

## Implementation notes

The trivializing section is the single homogeneous fraction

`(p^{max n 0} q^{max (-n) 0}) / (q^{max n 0} p^{max (-n) 0})`,

whose numerator has degree `numDeg = max n 0 * (e + d) + max (-n) 0 * e` and whose denominator
has degree `denDeg = max n 0 * e + max (-n) 0 * (e + d)`. The identity `denDeg + n d = numDeg`
(`denDeg_add_mul`) holds for every sign of `n` and is the only arithmetic input; no case
distinction on the sign is made anywhere, because the integer-extended grading is the zero
submodule in negative degrees and `mul_mem_of_mem_integerGrading` therefore needs no sign
hypothesis.

Everything is computed pointwise, which is possible because of two definitional coincidences
recorded in `Stacks.AlgebraicGeometry.ProjTrivialization`: `Localization P` and
`LocalizedModule P S` are the same type at this pin, and the action of the former on the latter
is ring multiplication. Injectivity of multiplication by the trivializing section is
cancellation by a unit followed by `HomogeneousLocalization.val_injective`; surjectivity needs
no gluing, since the preimage of a section is determined pointwise and its local-fraction
property is read off from the local fraction of the given section.

The twist index is carried as an independent variable `c` together with the hypothesis
`c = n * d`, rather than as the literal `n * d`. Tag 01MU writes its twists as `d * n`, and
`d * n` and `n * d` are equal only propositionally in `ℤ`, so a statement about
`twistingSheaf 𝒮 (n * d)` cannot be applied to `twistingSheaf 𝒮 (d * n)` without transporting
along that equality; the hypothesis form applies to both.

Transparency notes:

* `attribute [local instance_reducible] ProjectiveSpectrum.top` and
  `attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
    Stacks.SheafOfModules.TensorSheafification.structureSheaf`
  are needed exactly as in
  `StacksFrontier/AlgebraicGeometry/Constructions/ProjStructureSheaf.lean`; without them `rw`
  inside the fibres produces goals that are "not type-correct under the `implicit`
  transparency level", and the restricted ring sheaf is not accepted where the invertibility
  predicate asks for `Stacks.SheafOfModules.TensorSheafification.structureSheaf _ _`.
* the sheaf of rings must be spelled `Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf`
  and the open must be spelled `ProjectiveSpectrum.basicOpen`. With the carrier written as
  `↥(Proj 𝒮)` — which is what `(Proj 𝒮).ringCatSheaf` and `Proj.basicOpen` give, and which is
  `rfl`-equal — instance synthesis no longer finds `Category (Over U)` and the restricted site
  cannot be formed at all.
* naturality of the trivialization on the restricted site is `rfl` after `Subtype.ext` and
  `funext`, because restriction of sections is restriction of dependent functions and the
  scalar action is pointwise.
* building the same isomorphism directly on `Opens ↥U.toScheme` (for
  `Scheme.Modules.restrictFunctor U.ι`) does *not* work: the module structure there is twisted
  through `(U.ι.appIso V).inv`, and although `AlgebraicGeometry.Scheme.Opens.ι_appIso` says
  that isomorphism is `Iso.refl`, `Scheme.Hom.appIso` is unexposed, so the two `ModuleCat`
  objects are not definitionally equal and `LinearEquiv.toModuleIso` is rejected. Going through
  the restricted site and Mathlib's `Scheme.Modules.overFunctorEquiv` avoids this entirely.
* destructing the local-fraction witness of a section yields an equation whose left-hand side
  is the unreduced `(fun x ↦ a.1 (i x)) y`, on which `rw` will not fire; re-ascribing it with
  `have hy : a.1 (i y) = … := heq y` is the fix.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjInvertibleLocus

universe u w

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The ideal underlying a point of `Proj S` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-! ### Degree bookkeeping -/

/-- The degree of the numerator of `(p/q)^n` for `p` of degree `e + d` and `q` of degree `e`. -/
def numDeg (e d : ℕ) (n : ℤ) : ℕ := n.toNat * (e + d) + (-n).toNat * e

/-- The degree of the denominator of `(p/q)^n` for `p` of degree `e + d` and `q` of
degree `e`. -/
def denDeg (e d : ℕ) (n : ℤ) : ℕ := n.toNat * e + (-n).toNat * (e + d)

/-- The degree identity behind the trivialization: the numerator of `(p/q)^n` exceeds its
denominator by exactly `n d`, whatever the sign of `n`. -/
lemma denDeg_add_mul (e d : ℕ) (n : ℤ) :
    ((denDeg e d n : ℤ)) + n * d = ((numDeg e d n : ℕ) : ℤ) := by
  have key : n + ((-n).toNat : ℤ) = (n.toNat : ℤ) := by omega
  simp only [numDeg, denDeg]
  push_cast
  linear_combination (d : ℤ) * key

/-- The shifted form of `denDeg_add_mul` in which the degree identity is applied: a local
fraction of degrees `(k + c, k)` becomes one of degrees `(k + numDeg, k + numDeg)`. -/
lemma denDeg_add_mul' {e d : ℕ} {n c : ℤ} (hc : (n : ℤ) * d = c) (k : ℕ) :
    ((k : ℤ) + c) + (denDeg e d n : ℤ) = ((k + numDeg e d n : ℕ) : ℤ) := by
  have h := denDeg_add_mul e d n
  rw [hc] at h
  push_cast at h ⊢
  linarith

variable {p q : S} {e d : ℕ}

/-- Multiplying an element of the integer-extended degree `j` piece by a homogeneous element of
degree `β` lands in the nonnegative degree `j + β`. No sign hypothesis on `j` is needed: in
negative degrees the piece is the zero submodule. -/
lemma mul_mem_of_mem_integerGrading {j : ℤ} {m b : S} {β N : ℕ}
    (hm : m ∈ integerGrading 𝒮 j) (hb : b ∈ 𝒮 β) (hN : j + β = (N : ℤ)) :
    m * b ∈ 𝒮 N := by
  rcases le_or_gt 0 j with hj | hj
  · have hm' : m ∈ 𝒮 j.toNat := by simpa [integerGrading, homogeneousSubmodule, hj] using hm
    have hNN : j.toNat + β = N := by omega
    have := SetLike.mul_mem_graded hm' hb
    simpa only [smul_eq_mul, hNN] using this
  · have hj' : ¬(0 ≤ j) := not_le.mpr hj
    have hm0 : m = 0 := by
      have hb0 : m ∈ (⊥ : Submodule ℤ S) := by simpa [integerGrading, hj'] using hm
      simpa using hb0
    simp [hm0, zero_mem]

/-- A product of powers of homogeneous elements is homogeneous of the corresponding degree. -/
private theorem pow_mul_pow_mem_graded {a b : S} {α β : ℕ} (ha : a ∈ 𝒮 α) (hb : b ∈ 𝒮 β)
    (i j : ℕ) : a ^ i * b ^ j ∈ 𝒮 (i * α + j * β) := by
  have h1 := SetLike.pow_mem_graded i ha
  have h2 := SetLike.pow_mem_graded j hb
  rw [smul_eq_mul] at h1 h2
  exact SetLike.mul_mem_graded h1 h2

/-- The numerator `p^{max n 0} q^{max (-n) 0}` of `(p/q)^n` is homogeneous of degree
`numDeg`. -/
lemma ratioNum_mem (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) (n : ℤ) :
    p ^ n.toNat * q ^ (-n).toNat ∈ 𝒮 (numDeg e d n) :=
  pow_mul_pow_mem_graded 𝒮 hp hq _ _

/-- The denominator `q^{max n 0} p^{max (-n) 0}` of `(p/q)^n` is homogeneous of degree
`denDeg`. -/
lemma ratioDen_mem (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) (n : ℤ) :
    q ^ n.toNat * p ^ (-n).toNat ∈ 𝒮 (denDeg e d n) :=
  pow_mul_pow_mem_graded 𝒮 hq hp _ _

/-! ### Invertibility of `p` and `q` on the standard open of their product -/

/-- On `D₊(pq)` the first factor is invertible in the local ring. -/
lemma left_mem_primeCompl {x : ProjectiveSpectrum.top 𝒮}
    (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    p ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
  fun hp => hx (Ideal.mul_mem_right _ _ hp)

/-- On `D₊(pq)` the second factor is invertible in the local ring. -/
lemma right_mem_primeCompl {x : ProjectiveSpectrum.top 𝒮}
    (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    q ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
  fun hq => hx (Ideal.mul_mem_left _ _ hq)

/-- A product of powers of two elements of a submonoid lies in it. -/
private theorem pow_mul_pow_mem {P : Submonoid S} {a b : S} (ha : a ∈ P) (hb : b ∈ P)
    (i j : ℕ) : a ^ i * b ^ j ∈ P :=
  P.mul_mem (P.pow_mem ha i) (P.pow_mem hb j)

/-- Every monomial in `p` and `q` is invertible in the local ring at a point of `D₊(pq)`. -/
lemma numMonomial_mem_primeCompl {x : ProjectiveSpectrum.top 𝒮}
    (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) (i j : ℕ) :
    p ^ i * q ^ j ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
  pow_mul_pow_mem (left_mem_primeCompl 𝒮 hx) (right_mem_primeCompl 𝒮 hx) i j

/-- The same with the roles of the two factors exchanged. -/
lemma denMonomial_mem_primeCompl {x : ProjectiveSpectrum.top 𝒮}
    (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) (i j : ℕ) :
    q ^ i * p ^ j ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
  pow_mul_pow_mem (right_mem_primeCompl 𝒮 hx) (left_mem_primeCompl 𝒮 hx) i j

/-! ### The trivializing section -/

/-- `(p/q)^n`, read as an element of the local ring at a point of `D₊(pq)`. This is the value
at `x` of the trivializing section of `𝒪(nd)`. -/
noncomputable def ratioFun (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) (x : W) :
    Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
  Localization.mk (p ^ n.toNat * q ^ (-n).toNat)
    ⟨q ^ n.toNat * p ^ (-n).toNat,
      denMonomial_mem_primeCompl 𝒮 (hW x.2) n.toNat (-n).toNat⟩

/-- The inverse of `ratioFun`, namely `(q/p)^n`. -/
noncomputable def ratioFunInv (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) (x : W) :
    Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
  Localization.mk (q ^ n.toNat * p ^ (-n).toNat)
    ⟨p ^ n.toNat * q ^ (-n).toNat,
      numMonomial_mem_primeCompl 𝒮 (hW x.2) n.toNat (-n).toNat⟩

/-- `ratioFunInv` is an inverse of `ratioFun`: their product is `1`. -/
lemma ratioFun_mul_inv (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) (x : W) :
    ratioFun 𝒮 n hW x * ratioFunInv 𝒮 n hW x = 1 := by
  rw [ratioFun, ratioFunInv, Localization.mk_mul, ← Localization.mk_one]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))

/-- On `D₊(pq)` the ratio `(p/q)^n` is a unit of the local ring: this is why `𝒪(nd)` trivializes
there, and it is the only place the standard open is used. -/
lemma isUnit_ratioFun (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) (x : W) :
    IsUnit (ratioFun 𝒮 n hW x) :=
  IsUnit.of_mul_eq_one _ (ratioFun_mul_inv 𝒮 n hW x)

/-- The ratio is a section of the twisting sheaf: it is the single homogeneous fraction with
numerator of degree `numDeg` and denominator of degree `denDeg`, and these differ by exactly
`n d`. -/
lemma ratioFun_mem (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n : ℤ} {c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    ratioFun 𝒮 n hW ∈ moduleSections 𝒮 (twistGrading 𝒮 c) W := by
  intro x
  refine ⟨W, x.2, 𝟙 _, denDeg e d n, p ^ n.toNat * q ^ (-n).toNat,
    q ^ n.toNat * p ^ (-n).toNat, ?_, ratioDen_mem 𝒮 hp hq n,
    fun y => denMonomial_mem_primeCompl 𝒮 (hW y.2) n.toNat (-n).toNat, fun y => rfl⟩
  show p ^ n.toNat * q ^ (-n).toNat ∈ integerGrading 𝒮 ((denDeg e d n : ℤ) + c)
  rw [show (denDeg e d n : ℤ) + c = ((numDeg e d n : ℕ) : ℤ) from by
    rw [← hc]; exact denDeg_add_mul e d n]
  exact ProjTrivialization.mem_integerGrading_natCast 𝒮 (ratioNum_mem 𝒮 hp hq n)

/-- The trivializing section of `𝒪(nd)` over an open contained in `D₊(pq)`. -/
noncomputable def ratioSection (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    moduleSections 𝒮 (twistGrading 𝒮 c) W :=
  ⟨ratioFun 𝒮 n hW, ratioFun_mem 𝒮 hp hq hc hW⟩

/-- Multiplication by the trivializing section, as a map of modules over the ring of sections
of the structure sheaf on `W`. -/
noncomputable def ratioHom (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) →ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)]
      moduleSections 𝒮 (twistGrading 𝒮 c) W :=
  LinearMap.toSpanSingleton _ _ (ratioSection 𝒮 hp hq hc hW)

/-- Multiplication by the trivializing section is pointwise multiplication by `(p/q)^n`. -/
lemma ratioHom_apply (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)) (x : W) :
    (ratioHom 𝒮 hp hq hc hW r).1 x =
      HomogeneousLocalization.val (r.1 x) * ratioFun 𝒮 n hW x := rfl

/-- Two elements of the local ring whose products with the trivializing value agree are equal:
that value is a unit and `HomogeneousLocalization.val` is injective. -/
lemma eq_of_val_mul_eq (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) (x : W)
    {ρ ρ' : HomogeneousLocalization.AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal}
    (h : HomogeneousLocalization.val ρ * ratioFun 𝒮 n hW x =
      HomogeneousLocalization.val ρ' * ratioFun 𝒮 n hW x) : ρ = ρ' :=
  HomogeneousLocalization.val_injective _ ((isUnit_ratioFun 𝒮 n hW x).mul_right_cancel h)

/-- Locally on `D₊(pq)`, a section of `𝒪(nd)` is the trivializing value times a fraction of
*equal* degrees: a local fraction `m / s` of the twist, with `deg m - deg s = nd`, becomes
`(m · den) / (s · num)`, whose numerator and denominator both have degree `deg s + numDeg`. -/
lemma exists_isFraction_of_mem (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (a : moduleSections 𝒮 (twistGrading 𝒮 c) W) (x : W) :
    ∃ (V : Opens (ProjectiveSpectrum.top 𝒮)) (_ : x.1 ∈ V) (i : V ⟶ W) (N : ℕ) (u v : S)
      (_ : u ∈ 𝒮 N) (_ : v ∈ 𝒮 N) (hv : ∀ y : V, v ∉ y.1.asHomogeneousIdeal),
      ∀ y : V, Localization.mk u ⟨v, hv y⟩ * ratioFun 𝒮 n hW (i y) = a.1 (i y) := by
  obtain ⟨V, hxV, i, k, m, s, hm, hs, hnin, heq⟩ := a.2 x
  refine ⟨V, hxV, i, k + numDeg e d n, m * (q ^ n.toNat * p ^ (-n).toNat),
    s * (p ^ n.toNat * q ^ (-n).toNat),
    mul_mem_of_mem_integerGrading 𝒮 hm (ratioDen_mem 𝒮 hp hq n) (denDeg_add_mul' hc k),
    SetLike.mul_mem_graded hs (ratioNum_mem 𝒮 hp hq n),
    fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hnin y)
      (numMonomial_mem_primeCompl 𝒮 (hW (i y).2) n.toNat (-n).toNat), fun y => ?_⟩
  have hy : a.1 (i y) = Localization.mk m ⟨s, hnin y⟩ := heq y
  rw [ratioFun, Localization.mk_mul, hy]
  exact Localization.mk_eq_mk_iff.mpr
    (Localization.r_of_eq (by simp only [Submonoid.coe_mul]; ring))

/-- Pointwise, every section of `𝒪(nd)` on an open of `D₊(pq)` is the trivializing value times
an element of the local ring. -/
lemma exists_val_mul_eq (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (a : moduleSections 𝒮 (twistGrading 𝒮 c) W) (x : W) :
    ∃ ρ : HomogeneousLocalization.AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal,
      HomogeneousLocalization.val ρ * ratioFun 𝒮 n hW x = a.1 x := by
  obtain ⟨V, hxV, i, N, u, v, hu, hv, hvn, heq⟩ :=
    exists_isFraction_of_mem 𝒮 hp hq hc hW a x
  exact ⟨HomogeneousLocalization.mk ⟨N, ⟨u, hu⟩, ⟨v, hv⟩, hvn ⟨x.1, hxV⟩⟩, heq ⟨x.1, hxV⟩⟩

/-- The pointwise quotient of a section of `𝒪(nd)` by the trivializing value. -/
noncomputable def preimageFun (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (a : moduleSections 𝒮 (twistGrading 𝒮 c) W) (x : W) :
    HomogeneousLocalization.AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal :=
  (exists_val_mul_eq 𝒮 hp hq hc hW a x).choose

/-- The pointwise quotient, multiplied by `(p/q)^n`, gives back the given section. -/
lemma preimageFun_spec (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (a : moduleSections 𝒮 (twistGrading 𝒮 c) W) (x : W) :
    HomogeneousLocalization.val (preimageFun 𝒮 hp hq hc hW a x) * ratioFun 𝒮 n hW x = a.1 x :=
  (exists_val_mul_eq 𝒮 hp hq hc hW a x).choose_spec

/-- The pointwise quotient is a section of the structure sheaf: its local fraction is the one
produced by `exists_isFraction_of_mem`, which it must equal because multiplication by the
trivializing value is injective. -/
lemma preimageFun_mem (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (a : moduleSections 𝒮 (twistGrading 𝒮 c) W) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒮).pred
      (preimageFun 𝒮 hp hq hc hW a) := by
  intro x
  obtain ⟨V, hxV, i, N, u, v, hu, hv, hvn, heq⟩ :=
    exists_isFraction_of_mem 𝒮 hp hq hc hW a x
  refine ⟨V, hxV, i, N, ⟨u, hu⟩, ⟨v, hv⟩, hvn, fun y => ?_⟩
  refine eq_of_val_mul_eq 𝒮 n hW (i y) ?_
  rw [preimageFun_spec, HomogeneousLocalization.val_mk]
  exact (heq y).symm

/-- Multiplication by the trivializing section is a bijection `Γ(W, 𝒪) → Γ(W, 𝒪(nd))` on every
open `W` contained in `D₊(pq)`. This is the arithmetic content of the trivialization. -/
lemma bijective_ratioHom (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    Function.Bijective (ratioHom 𝒮 hp hq hc hW) := by
  refine ⟨fun r r' h => Subtype.ext (funext fun x => eq_of_val_mul_eq 𝒮 n hW x ?_), fun a =>
    ⟨⟨preimageFun 𝒮 hp hq hc hW a, preimageFun_mem 𝒮 hp hq hc hW a⟩,
      Subtype.ext (funext fun x => preimageFun_spec 𝒮 hp hq hc hW a x)⟩⟩
  rw [← ratioHom_apply 𝒮 hp hq hc hW, ← ratioHom_apply 𝒮 hp hq hc hW, h]

/-- The trivialization of `𝒪(nd)` over an open contained in `D₊(pq)`, at the level of
sections. -/
noncomputable def ratioEquiv (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) ≃ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)]
      moduleSections 𝒮 (twistGrading 𝒮 c) W :=
  LinearEquiv.ofBijective _ (bijective_ratioHom 𝒮 hp hq hc hW)

/-! ### The trivialization on the restricted site -/

open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)

/-- The trivialization of `𝒪(nd)` on the restricted site of `D₊(pq)`, as an isomorphism of
presheaves of modules out of the structure sheaf. Naturality is definitional: restriction is
restriction of dependent functions, the scalar action is pointwise, and the trivializing
section is given by one formula at every point of `D₊(pq)`. -/
noncomputable def unitOverIsoRatio (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) :
    (SheafOfModules.unit ((projRingSheaf 𝒮).over
        (ProjectiveSpectrum.basicOpen 𝒮 (p * q)))).val ≅
      ((twistingSheaf 𝒮 c).over (ProjectiveSpectrum.basicOpen 𝒮 (p * q))).val :=
  PresheafOfModules.isoMk
    (fun V => (ratioEquiv 𝒮 hp hq hc (leOfHom V.unop.hom)).toModuleIso)
    (fun {_ _} _ => ModuleCat.hom_ext (LinearMap.ext fun _ =>
      Subtype.ext (funext fun _ => rfl)))

/-- For `p` homogeneous of degree `e + d` and `q` homogeneous of degree `e`, the twisting sheaf
`𝒪(nd)` restricted to the standard open `D₊(pq)` is trivial: it is isomorphic to the structure
sheaf of the restricted site. The trivializing section is `(p/q)^n`, which makes sense on
`D₊(pq)` because both `p` and `q` become invertible there. -/
@[ega "II 8.14.7" "more general"]
noncomputable def ratioOverIsoUnit (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) :
    (twistingSheaf 𝒮 c).over (ProjectiveSpectrum.basicOpen 𝒮 (p * q)) ≅
      SheafOfModules.unit ((projRingSheaf 𝒮).over
        (ProjectiveSpectrum.basicOpen 𝒮 (p * q))) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (unitOverIsoRatio 𝒮 hp hq hc).symm

end Stacks.AlgebraicGeometry.ProjInvertibleLocus

end
