module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionGysin
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullbackChow

/-!
# The Gysin map of the zero section retracts the flat pullback

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module and let

  `p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X`

be the associated line bundle, with zero section `o : X ⟶ L`. Clause (4) of [Stacks, Tag 0F96]
asserts that

  `o^* p^* : \CH_k(X) ⟶ \CH_k(X)`

is the identity map. The source's proof is one line: "Of course (4) is the first formula in Lemma
42.31.1", that is, it is Stacks 02TR for the relative effective Cartier divisor `o(X)` on `L/X`,
whose restricted projection `p|_{o(X)}` is the identity of `X`.

## The two steps

Stacks 02TR, first equality, is available here for an arbitrary Chow class as
`Stacks.Chow.gysinChowOfInvertible_flatPullbackChow`: for a flat `π : X' ⟶ B` of relative
dimension `r + 1` and a relative effective Cartier divisor `i : Z ⟶ X'` on `X'/B` presented as a
zero scheme,

  `i^* π^* α = (π|_Z)^* α`  in  `\CH_{k + r}(Z)`.

Taken at `r = 0` the right-hand side is the flat pullback along `π|_Z : Z ⟶ B` in relative
dimension zero. When `π|_Z` is an *isomorphism* — which is exactly the situation of the zero
section, `p ∘ o` being the identity of `X` — that flat pullback is inverse to pushforward along
the same isomorphism, so pushing the left-hand side forward along `Z ≅ B` returns `α`. Pushing
forward along `Z ≅ B` is the second half of the Gysin map of clause (3),
`Stacks.Chow.zeroSectionGysinChow`, so the composite collapses to the identity.

The second step is the fact that
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleChow` recorded as missing. It is
proved once, as `Stacks.Chow.flatPullbackChowOfRelativeDimension_of_isIso` in
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula`, where clause (5)
needs it too; what this file adds is
`Stacks.Chow.heq_flatPullbackChowOfRelativeDimension_chowPushforwardOfIso_inv`, the same identity
in the `HEq` spelling and at the inverse `inv f`, which is the shape the proof below consumes.

## Main results

* `Stacks.Chow.heq_flatPullbackChowOfRelativeDimension_chowPushforwardOfIso_inv` — flat pullback
  along an isomorphism over the base in relative dimension zero is pushforward along the inverse
  isomorphism, up to the transport of the degree from `k + 0` to `k`. This is the `HEq` spelling
  of `Stacks.Chow.flatPullbackChowOfRelativeDimension_of_isIso`, which is where it is proved.
* `Stacks.Chow.gysinChowOfInvertibleTransported_flatPullbackChowOfRelativeDimension` — **Stacks
  02TR, first equality, when the divisor is isomorphic to the base over it**: the transported
  Gysin map of `Stacks.Chow.gysinChowOfInvertibleTransported` retracts the flat pullback along
  `π`.
* `Stacks.Chow.zeroSectionGysinChow_flatPullbackChowOfRelativeDimension` — **clause (4) of
  [Stacks, Tag 0F96]**: `o^*(p^* α) = α` for every `α ∈ \CH_k(X)`.
* `Stacks.Chow.zeroSectionGysinChow_comp_flatPullbackChowOfRelativeDimension` — the same clause in
  the source's phrasing, as the equality of homomorphisms `o^* p^* = \mathrm{id}`.

## Degrees

No transport of degrees appears in any statement of this file. The flat pullback of a `k`-class
in relative dimension `r` lands in degree `k + (r : ℤ)`, and `((1 : ℕ) : ℤ)` and `(1 : ℤ)` are the
same term after unfolding, so `p^*` of a `k`-class lands in the degree `k + 1` that `o^*`
consumes. Inside the proofs two transports are needed, both at an equality of degrees bound by a
variable rather than at a fixed one: the degree `k + 1 + ((0 : ℕ) : ℤ)` in which Stacks 02TR
states the first equality at `r = 0` is not the term `k + 1`, and neither is the degree
`k + ((0 : ℕ) : ℤ)` of a flat pullback in relative dimension zero the term `k`.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Flat pullback along an isomorphism in relative dimension zero -/

/-- A transport of a Chow class along an equality of degrees is heterogeneously equal to the
class itself. -/
private theorem heq_chowGroupCast (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] {k l : ℤ} (h : k = l) (x : chowGroup C q k) :
    HEq (chowGroupCast C q h x) x := by
  cases h; rfl

/-- **Flat pullback on Chow groups along an isomorphism over the base, in relative dimension
zero, is pushforward along the inverse isomorphism**, up to the transport of the degree from
`k + 0` to `k`.

This is the `HEq` spelling of
`Stacks.Chow.flatPullbackChowOfRelativeDimension_of_isIso` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula`, which is the one
place the mathematics is proved -- it states the same identity as an equality through
`Stacks.Chow.chowGroupCast`, and takes the inverse as a parameter rather than as `inv f`. Here
the inverse is `inv f` and the degree transport is left heterogeneous, which is the shape
`Stacks.Chow.zeroSectionGysinChow_flatPullbackChowOfRelativeDimension` below consumes it in. -/
theorem heq_flatPullbackChowOfRelativeDimension_chowPushforwardOfIso_inv
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsIso f] (hbase : f ≫ sY = sX)
    (hf : AlgebraicGeometry.RelativeDimension f 0) (k : ℤ) (α : chowGroup C sY k) :
    HEq (flatPullbackChowOfRelativeDimension C sX sY f hbase 0 hf k α)
      (chowPushforwardOfIso C sY sX (inv f) (by rw [IsIso.inv_comp_eq, hbase]) k α) := by
  rw [flatPullbackChowOfRelativeDimension_of_isIso C sX sY f hbase hf (inv f)
    (IsIso.inv_hom_id f) (by rw [IsIso.inv_comp_eq, hbase]) k α]
  exact heq_chowGroupCast C sX _ _

/-- The Gysin maps of [Stacks, Tag 02TO] at two equal degrees are carried to one another by a
heterogeneous equality of their arguments. The equality of degrees is a variable, so the
transport it names is never at a fixed degree. -/
private theorem heq_gysinChowOfInvertible (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {m n : ℤ} (hmn : m = n) {x : chowGroup C q (m + 1)}
    {y : chowGroup C q (n + 1)} (hxy : HEq x y) :
    HEq (gysinChowOfInvertible C q m L s x) (gysinChowOfInvertible C q n L s y) := by
  cases hmn
  exact heq_of_eq (congrArg (gysinChowOfInvertible C q m L s) (eq_of_heq hxy))

/-! ### Stacks 02TR when the divisor is isomorphic to the base -/

/-- **Stacks 02TR, first equality, when the divisor is isomorphic to the base over it.** Let
`π : X ⟶ B` be flat of relative dimension one over the base situation of chapter 42, let `s` be a
global section of an invertible module `L` on `X` whose zero scheme `Z(s)` is a relative
effective Cartier divisor on `X/B` ([Stacks, Tag 062T]), and let `e : Z(s) ≅ B` be the structure
morphism of `Z(s)` over `B`, assumed to be an isomorphism. Then

  `i^* π^* α = α`  for every  `α ∈ \CH_k(B)`,

the Gysin map being read on `B` through `e` as `Stacks.Chow.gysinChowOfInvertibleTransported`
reads it.

Stacks 02TR computes `i^* π^* α` as the flat pullback of `α` along `π|_{Z(s)} = e`, in relative
dimension zero; pushing that forward along `e` gives `α` back by
`Stacks.Chow.heq_flatPullbackChowOfRelativeDimension_chowPushforwardOfIso_inv` and
[Stacks, Tag 0GU8]. The relative dimension zero of `π|_{Z(s)}` is not assumed: it is
`AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor`. Neither is the
flatness of `π|_{Z(s)}`, which is the second conjunct of the divisor hypothesis. -/
theorem gysinChowOfInvertibleTransported_flatPullbackChowOfRelativeDimension
    (C : ChowSituation.{u}) {X B : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (π : X ⟶ B) [LocallyOfFiniteType π]
    [AlgebraicGeometry.Flat π] (hbase : π ≫ sB = sX)
    (hπ : AlgebraicGeometry.RelativeDimension π 1) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))))
    (e : (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subscheme ≅ B)
    (hcompat : e.hom = (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ π)
    (he : e.hom ≫ sB = (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX)
    (α : chowGroup C sB k) :
    gysinChowOfInvertibleTransported C sX sB k L (s.eval (.op ⊤)) e he
        (flatPullbackChowOfRelativeDimension C sX sB π hbase 1 hπ k α) = α := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, k = j + 1 := ⟨k - 1, by ring⟩
  revert hD e
  set Z := Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))
  intro hD e hcompat he
  have : AlgebraicGeometry.Flat (Z.subschemeι ≫ π) := hD.2
  have : IsIso (Z.subschemeι ≫ π) := by
    rw [← hcompat]
    infer_instance
  have hq : AlgebraicGeometry.RelativeDimension (Z.subschemeι ≫ π) 0 :=
    AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor π 0 hπ Z hD
  have hv : (Z.subschemeι ≫ π) ≫ sB = Z.subschemeι ≫ sX := by rw [Category.assoc, hbase]
  have hcast : j + 1 + ((0 + 1 : ℕ) : ℤ) = j + 1 + ((0 : ℕ) : ℤ) + 1 := by simp
  have h02TR := gysinChowOfInvertible_flatPullbackChow C sX sB π hbase 0 hπ j L s hD hcast α
  have hmain : gysinChowOfInvertible C sX (j + 1) L (s.eval (.op ⊤))
        (flatPullbackChowOfRelativeDimension C sX sB π hbase 1 hπ (j + 1) α) =
      chowPushforwardOfIso C sB (Z.subschemeι ≫ sX) (inv (Z.subschemeι ≫ π))
        (by rw [IsIso.inv_comp_eq, hv]) (j + 1) α := by
    refine eq_of_heq (HEq.trans (heq_gysinChowOfInvertible C sX L (s.eval (.op ⊤))
      (show j + 1 = j + 1 + ((0 : ℕ) : ℤ) from by simp) (HEq.symm (eqRec_heq hcast _))) ?_)
    rw [h02TR]
    exact heq_flatPullbackChowOfRelativeDimension_chowPushforwardOfIso_inv C
      (Z.subschemeι ≫ sX) sB (Z.subschemeι ≫ π) hv hq (j + 1) α
  change chowPushforwardOfIso C (Z.subschemeι ≫ sX) sB e.hom he (j + 1)
      (gysinChowOfInvertible C sX (j + 1) L (s.eval (.op ⊤))
        (flatPullbackChowOfRelativeDimension C sX sB π hbase 1 hπ (j + 1) α)) = α
  rw [hmain, chowPushforwardOfIso_congr C (Z.subschemeι ≫ sX) sB e.hom (Z.subschemeι ≫ π)
    hcompat he hv (j + 1)]
  exact (chowGroupEquivOfIso C (Z.subschemeι ≫ sX) sB (Z.subschemeι ≫ π) hv
    (j + 1)).apply_symm_apply α

/-! ### Clause (4) of Stacks 0F96 -/

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- **Stacks 0F96, clause (4).** The Gysin map `o^*` of the zero section of a line bundle
`p : L ⟶ X` retracts the flat pullback `p^*`:

  `o^* p^* : \CH_k(X) ⟶ \CH_k(X)`  is the identity map.

This is `Stacks.Chow.gysinChowOfInvertibleTransported_flatPullbackChowOfRelativeDimension`, which
is Stacks 02TR at `r = 0`, instantiated at the zero-section divisor: the divisor is the zero
scheme of the tautological section of `p^*(ℒ^{⊗ -1})` the way clause (1) presents it, it is a
relative effective Cartier divisor on `L/X` by
`Stacks.LineBundle.Situation.isRelativeEffectiveCartierDivisor_zeroScheme_tautologicalSectionBase`,
and the isomorphism `o(X) ≅ X` through which clause (3) reads the Gysin map is its structure
morphism over `X`, `Stacks.LineBundle.Situation.zeroSectionDivisorIso`.

Nothing beyond the hypothesis of clause (3) — that `X` be locally of finite type over `S` — is
assumed. The flatness of `p` and its relative dimension one, which writing `p^*` down needs, are
the theorems `Stacks.LineBundle.Situation.flat_totalSpaceToBase` and
`Stacks.LineBundle.Situation.relativeDimension_totalSpaceToBase`, supplied here rather than
taken, and the instance of [Stacks, Tag 02S1] that `p^*` needs is discharged inside
`Stacks.Chow.flatPullbackChowOfRelativeDimension`. -/
theorem zeroSectionGysinChow_flatPullbackChowOfRelativeDimension (k : ℤ)
    (α : chowGroup C sX k) :
    zeroSectionGysinChow C D sX k
        (flatPullbackChowOfRelativeDimension C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase
          rfl 1 D.relativeDimension_totalSpaceToBase k α) = α :=
  gysinChowOfInvertibleTransported_flatPullbackChowOfRelativeDimension C
    (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase rfl D.relativeDimension_totalSpaceToBase k
    D.basePullbackInverse D.tautologicalSectionBaseSections
    D.isRelativeEffectiveCartierDivisor_zeroScheme_tautologicalSectionBase
    D.zeroSectionDivisorIso rfl (zeroSectionDivisorIso_hom_comp C D sX) α

/-- **Stacks 0F96, clause (4).** The source's phrasing: the composite

  `o^* p^* : \CH_k(X) ⟶ \CH_k(X)`

*is* the identity map. This is
`Stacks.Chow.zeroSectionGysinChow_flatPullbackChowOfRelativeDimension` read as an equality of
homomorphisms; the two are interchangeable, both sides of the equality being determined by their
values. -/
@[stacks 0F96 "part (4)"]
theorem zeroSectionGysinChow_comp_flatPullbackChowOfRelativeDimension (k : ℤ) :
    (zeroSectionGysinChow C D sX k).comp
        (flatPullbackChowOfRelativeDimension C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase
          rfl 1 D.relativeDimension_totalSpaceToBase k) =
      AddMonoidHom.id (chowGroup C sX k) :=
  AddMonoidHom.ext fun α ↦
    zeroSectionGysinChow_flatPullbackChowOfRelativeDimension C D sX k α

end Stacks.Chow

end
