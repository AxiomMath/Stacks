module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.ExteriorPowerResolution
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.TopChernCapBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.ZeroSection

/-!
# The Chern classes of an object resolved by the Koszul complex of the zero section

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `𝒞` be a finite locally free `𝒪_X`-module of rank `r ≥ 1`, and let
`π : E = 𝐏(𝒞 ⊕ 𝒪_X) ⟶ X` be the projective completion of the vector bundle `C = Spec_X(Sym(𝒞))`,
with `V ⊆ E` the complement of the divisor at infinity and `p : V ⟶ X`. Let `F` be an object of
`D(𝒪_E)` resolved by the exterior powers of `ℰ = π^*𝒞 ⊗ 𝒪_E(-1)`, as `i_*𝒪_X` is by the Koszul
complex of the canonical map `ℰ ⟶ 𝒪_E` (`i` the zero section). Then

* `c_t(F) = 0` for `t = 1, …, r - 1`, and
* `p^*(π_*(c_r(F) ∩ α)) = (-1)^{r-1} (r-1)! α|_V` for every `α ∈ CH_*(E)`.

By Stacks 0FEE, `c_r(F) = -(r-1)! c_r(ℰ)` and the lower Chern classes vanish
(`Stacks.Chow.ExteriorPowerResolution.homPart_perfectChernClass`), and
`p^*(π_*(c_r(ℰ) ∩ α)) = (-1)^r α|_V`
(`Stacks.Chow.flatPullback_pushforward_chernCap_koszulModule`). Applied to the Koszul resolution
of `i_*𝒪_X` (`Stacks.ProjectiveCompletion.koszulResolutionZeroSection`), this is Stacks 0FEF,
`Stacks.Chow.chernClass_pushforward_zeroSection`.

The cap product `c_r(F) ∩ α` is the operation of the bivariant class `c_r(F) ∈ A^r(E)` on a test
scheme. The identity `p^* ∘ π_* ∘ c_r(F) = (-1)^{r-1} (r-1)! j^*` of Stacks 0FEF is the statement
that both sides have the same effect on every test scheme `q : E' = X' ×_X E ⟶ E` obtained from a
morphism `g : X' ⟶ X` locally of finite type ("after replacing `X` by a scheme locally of finite
type over `X`"): for every `α ∈ CH_*(E')`,

  `p'^*(π'_*(c_r(F) ∩ α)) = (-1)^{r-1} (r-1)! α|_{V'}`

with `π' : E' ⟶ X'`, `V' = q⁻¹(V)` and `p' : V' ⟶ X'`. On `E'` the computation of `c_r(ℰ)` is
`Stacks.Chow.flatPullback_pushforward_chernCap_koszulModule_baseChange`. The case of the test
scheme `𝟙_E` is recorded separately, `α` then lying in the Chow group of `E` indexed by the
structure morphism `𝟙_E ≫ π ≫ s`.

## Main results

* `Stacks.Chow.perfectChernClass_eq_zero_of_koszulModule` — `c_t(F) = 0` for `0 < t < r`.
* `Stacks.Chow.flatPullback_pushforward_perfectChernClass_of_koszulModule` — the identity in
  `CH_*(V)`, on the test scheme `𝟙_E`.
* `Stacks.Chow.flatPullback_pushforward_perfectChernClass_of_koszulModule_baseChange` — the
  identity in `CH_*(V')`, on every test scheme `X' ×_X E ⟶ E`.
* `Stacks.Chow.chernClass_pushforward_zeroSection` — **Stacks 0FEF**, for `F = i_*𝒪_X`.

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 0FEE](https://stacks.math.columbia.edu/tag/0FEE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.ProjectiveCompletion

universe u

namespace Stacks.Chow

/-- The operation of `c_r(F)` on a test scheme `g` is `-(r-1)!` times the cap with `c_r(g^*ℰ)`. -/
private theorem op_perfectChernClass_eq_neg_factorial_smul_chernCap (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (𝒞 : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (hr : r ≠ 0)
    {F : DerivedCategory (projectiveCompletion 𝒞).Modules}
    (R : ExteriorPowerResolution F (koszulModule 𝒞)) (hF : HasDefinedChernClasses F)
    {T : Scheme.{u}} (g : T ⟶ projectiveCompletion 𝒞) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ projectiveCompletionProj 𝒞 ≫ sX) (k + r)) :
    haveI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (koszulModule 𝒞) r g
    (perfectChernClass C (projectiveCompletionProj 𝒞 ≫ sX) hF).op g (k + r) r α =
      -((Nat.factorial (r - 1)) • GenuineChern.chernCap C r (g ≫ projectiveCompletionProj 𝒞 ≫ sX)
        ((Scheme.Modules.pullback g).obj (koszulModule 𝒞)) (k + r) (Fin.last r) α) := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (koszulModule 𝒞) r g
  have h2 := (R.homPart_perfectChernClass r C (projectiveCompletionProj 𝒞 ≫ sX) hr hF).2
  have hop := congrArg (fun c : TotalChowClass C (projectiveCompletionProj 𝒞 ≫ sX) ↦
    TotalChowClass.opHom g c (k + r) r α) h2
  simp only [map_neg, map_nsmul, TotalChowClass.opHom_apply, TotalChowClass.op_homComponent,
    homComponent_apply, Pi.neg_apply, Pi.smul_apply, AddMonoidHom.neg_apply,
    AddMonoidHom.smul_apply, ite_true] at hop
  refine hop.trans ?_
  congr 2
  exact op_totalChern_apply C _ (koszulModule 𝒞) r g (k + r) (Fin.last r) α

/-- The sign and factorial bookkeeping in the cap-product identity of Stacks 0FEF. -/
private theorem neg_factorial_smul_neg_one_pow_smul {A : Type*} [AddCommGroup A] {r : ℕ}
    (hr : r ≠ 0) (a : A) : -((Nat.factorial (r - 1)) • (((-1 : ℤ) ^ r) • a)) =
      ((-1 : ℤ) ^ (r - 1) * (Nat.factorial (r - 1) : ℤ)) • a := by
  rw [← natCast_zsmul, smul_smul, ← neg_smul]
  congr 1
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (𝒞 : X.Modules) (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  [Flat (projectiveCompletionProj 𝒞)] [LocallyOfFiniteType (projectiveCompletionProj 𝒞)]

/-- The cap-product identity of `Stacks.Chow.flatPullback_pushforward_chernCap_koszulModule`, for
an arbitrary spelling `sP` of the structure morphism `π ≫ s` of `E`. -/
theorem flatPullback_pushforward_chernCap_koszulModule_of_eq
    (sP : projectiveCompletion 𝒞 ⟶ C.S) [LocallyOfFiniteType sP]
    (hsP : projectiveCompletionProj 𝒞 ≫ sX = sP) (k : ℤ) (α : chowGroup C sP (k + r)) :
    chowGroupCast C ((complementOpen 𝒞).ι ≫ sP) (by ring) (bundlePullback C sX
      ((complementOpen 𝒞).ι ≫ sP)
      ((complementOpen 𝒞).ι ≫ projectiveCompletionProj 𝒞) (by rw [Category.assoc, hsP]) r
      (relativeDimension_complementOpen_ι_comp 𝒞 r) (k + r - r)
      (properChowPushforward C sP sX (projectiveCompletionProj 𝒞) hsP (k + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ hsP _)
        (GenuineChern.chernCap C r sP (koszulModule 𝒞) (k + r) (Fin.last r) α))) =
      ((-1 : ℤ) ^ r) •
        chowGroupOpensRestrictOfIsOpenImmersion C sP (complementOpen 𝒞) (k + r) α := by
  subst hsP
  exact flatPullback_pushforward_chernCap_koszulModule C sX 𝒞 r k α

variable {𝒞 r}

omit [Flat (projectiveCompletionProj 𝒞)] [LocallyOfFiniteType (projectiveCompletionProj 𝒞)] in
/-- **The lower Chern classes vanish**: for `F` resolved by the exterior powers of
`π^*𝒞 ⊗ 𝒪_E(-1)`, `c_t(F) = 0` for `t = 1, …, r - 1` (Stacks 0FEE). -/
theorem perfectChernClass_eq_zero_of_koszulModule (hr : r ≠ 0)
    {F : DerivedCategory (projectiveCompletion 𝒞).Modules}
    (R : ExteriorPowerResolution F (koszulModule 𝒞)) (hF : HasDefinedChernClasses F) (t : ℕ)
    (ht : 0 < t) (htr : t < r) :
    perfectChernClass C (projectiveCompletionProj 𝒞 ≫ sX) hF t = 0 := by
  have h := ((R.homPart_perfectChernClass r C (projectiveCompletionProj 𝒞 ≫ sX) hr hF).1 t ht htr)
  have h' := congrFun h t
  rwa [TotalChowClass.homComponent_apply, ite_eq_left rfl] at h'

/-- **The cap-product identity of Stacks 0FEF**: for `F` resolved by the exterior powers of
`π^*𝒞 ⊗ 𝒪_E(-1)` and `α ∈ CH_{k+r}(E)`,

  `p^*(π_*(c_r(F) ∩ α)) = (-1)^{r-1} (r-1)! α|_V`

in `CH_{k+r}(V)`, where `c_r(F) ∩ -` is the operation of `c_r(F) ∈ A^r(E)` on the test scheme
`𝟙_E`, `V ⊆ E` is the complement of the divisor at infinity and `p : V ⟶ X` its projection. -/
theorem flatPullback_pushforward_perfectChernClass_of_koszulModule (hr : r ≠ 0)
    {F : DerivedCategory (projectiveCompletion 𝒞).Modules}
    (R : ExteriorPowerResolution F (koszulModule 𝒞)) (hF : HasDefinedChernClasses F) (k : ℤ)
    (α : chowGroup C (𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX) (k + r)) :
    chowGroupCast C ((complementOpen 𝒞).ι ≫ 𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX) (by ring)
      (bundlePullback C sX ((complementOpen 𝒞).ι ≫ 𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX)
      ((complementOpen 𝒞).ι ≫ projectiveCompletionProj 𝒞) (by simp) r
      (relativeDimension_complementOpen_ι_comp 𝒞 r) (k + r - r)
      (properChowPushforward C (𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX) sX
        (projectiveCompletionProj 𝒞) (by simp) (k + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ (by simp) _)
        ((perfectChernClass C (projectiveCompletionProj 𝒞 ≫ sX) hF).op (𝟙 _) (k + r) r α))) =
      ((-1 : ℤ) ^ (r - 1) * (Nat.factorial (r - 1) : ℤ)) •
        chowGroupOpensRestrictOfIsOpenImmersion C (𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX)
          (complementOpen 𝒞) (k + r) α := by
  -- `c_r(F) = -(r-1)! c_r(ℰ)` on the test scheme `𝟙_E`
  have hcr := op_perfectChernClass_eq_neg_factorial_smul_chernCap C sX 𝒞 r hr R hF (𝟙 _) k α
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝟭 (projectiveCompletion 𝒞).Modules).obj (koszulModule 𝒞)) r :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (koszulModule 𝒞) r)
  rw [hcr, GenuineChern.chernCap_congr C _ r ((Scheme.Modules.pullbackId _).app _) _ _ α,
    map_neg, map_neg, map_neg, map_nsmul, map_nsmul, map_nsmul]
  erw [flatPullback_pushforward_chernCap_koszulModule_of_eq C sX 𝒞 r _
    (Category.id_comp _).symm k α]
  exact neg_factorial_smul_neg_one_pow_smul hr _

/-! ### Every test scheme `X' ×_X E ⟶ E` -/

section BaseChange

variable {X' : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (g : X' ⟶ X)
  [LocallyOfFiniteType g] (hg : g ≫ sX = sX')

include hg in
/-- **The cap-product identity of Stacks 0FEF on every test scheme `X' ×_X E`.** Let `F` be
resolved by the exterior powers of `π^*𝒞 ⊗ 𝒪_E(-1)`, let `g : X' ⟶ X` be locally of finite type,
`E' = X' ×_X E` with projections `π' : E' ⟶ X'` and `q : E' ⟶ E`, `V' = q⁻¹(V)` and
`p' : V' ⟶ X'`. Then for every `α ∈ CH_{k+r}(E')`

  `p'^*(π'_*(c_r(F) ∩ α)) = (-1)^{r-1} (r-1)! α|_{V'}`

in `CH_{k+r}(V')`, where `c_r(F) ∩ -` is the operation of `c_r(F) ∈ A^r(E)` on the test scheme
`q`. This is the identity `p^* ∘ π_* ∘ c_r(F) = (-1)^{r-1} (r-1)! j^*` of Stacks 0FEF, read on the
test schemes obtained by replacing `X` by a scheme locally of finite type over `X`. -/
theorem flatPullback_pushforward_perfectChernClass_of_koszulModule_baseChange (hr : r ≠ 0)
    {F : DerivedCategory (projectiveCompletion 𝒞).Modules}
    (R : ExteriorPowerResolution F (koszulModule 𝒞)) (hF : HasDefinedChernClasses F) (k : ℤ)
    (α : chowGroup C (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫
      sX) (k + r)) :
    chowGroupCast C _ (by ring) (bundlePullback C sX'
      ((complementOpenBaseChange g 𝒞).ι ≫ pullback.snd g (projectiveCompletionProj 𝒞) ≫
        projectiveCompletionProj 𝒞 ≫ sX)
      ((complementOpenBaseChange g 𝒞).ι ≫ pullback.fst g (projectiveCompletionProj 𝒞))
      (by rw [Category.assoc, pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞]) r
      (relativeDimension_complementOpenBaseChange g 𝒞 r) (k + r - r)
      (properChowPushforward C
        (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX) sX'
        (pullback.fst g (projectiveCompletionProj 𝒞))
        (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) (k + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX' _
          (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) _)
        ((perfectChernClass C (projectiveCompletionProj 𝒞 ≫ sX) hF).op
          (pullback.snd g (projectiveCompletionProj 𝒞)) (k + r) r α))) =
      ((-1 : ℤ) ^ (r - 1) * (Nat.factorial (r - 1) : ℤ)) •
        chowGroupOpensRestrictOfIsOpenImmersion C
          (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
          (complementOpenBaseChange g 𝒞) (k + r) α := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (koszulModule 𝒞) r
    (pullback.snd g (projectiveCompletionProj 𝒞))
  -- `c_r(F) = -(r-1)! c_r(ℰ)` on the test scheme `q`
  rw [op_perfectChernClass_eq_neg_factorial_smul_chernCap C sX 𝒞 r hr R hF _ k α, map_neg, map_neg,
    map_neg, map_nsmul, map_nsmul, map_nsmul,
    flatPullback_pushforward_chernCap_koszulModule_baseChange C sX sX' g hg 𝒞 r k α]
  exact neg_factorial_smul_neg_one_pow_smul hr _

end BaseChange

/-! ### Stacks 0FEF -/

section ZeroSection

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0FEF.** Let `X` be locally of finite type over the base `S` of chapter 42, `𝒞` a
finite locally free `𝒪_X`-module of rank `r ≥ 1`, `π : E = 𝐏(𝒞 ⊕ 𝒪_X) ⟶ X` the projective
completion, `i : X = 𝐏(𝒪_X) ⟶ E` the zero section, `C = Spec_X(Sym(𝒞)) = V ⊆ E` the complement
of the divisor at infinity with its inclusion `j` and projection `p : V ⟶ X`. Then

* `c_t(i_*𝒪_X) = 0` for `t = 1, …, r - 1`, and
* `p^* ∘ π_* ∘ c_r(i_*𝒪_X) = (-1)^{r-1} (r-1)! j^*` in `A^0(C → E)`: for every test scheme
  `q : X' ×_X E ⟶ E` obtained from a morphism `g : X' ⟶ X` locally of finite type, with
  `π' : X' ×_X E ⟶ X'`, `V' = q⁻¹(V)` and `p' : V' ⟶ X'`, and every `α ∈ CH_*(X' ×_X E)`,
  `p'^*(π'_*(c_r(i_*𝒪_X) ∩ α)) = (-1)^{r-1} (r-1)! α|_{V'}`; the test scheme `𝟙_E` is stated
  separately.

The Chern classes of `i_*𝒪_X` are defined because it is resolved by the Koszul complex of
`π^*𝒞 ⊗ 𝒪_E(-1) ⟶ 𝒪_E` (`Stacks.ProjectiveCompletion.koszulResolutionZeroSection`). The rank is
taken positive, as the factor `(r-1)!` of the source presupposes.

*Why the test schemes `X' ×_X E` are the whole of the second clause.* The composite
`p^* ∘ π_* ∘ c_r(i_*𝒪_X)` is not a composite of bivariant classes for `C ⟶ E`: `π_*` is proper
pushforward along `π' : E' ⟶ X'`, which exists only for a test scheme `E'` over `E` that is the
pullback `X' ×_X E` of a scheme `X'` over `X`, and `p^*` is flat pullback along the bundle
`p' : X' ×_X C ⟶ X'`. So the composite is an operation `CH_*(X' ×_X E) ⟶ CH_*(X' ×_X C)` for
each `X' ⟶ X` locally of finite type, and the equality "in `A^0(C → E)`" with
`(-1)^{r-1}(r-1)! j^*` asserts exactly that these operations agree with `(-1)^{r-1}(r-1)!` times
restriction to `X' ×_X C`, for every such `X'`. This is the reduction the source makes in its proof
("after replacing `X` by a scheme locally of finite type over `X`, it suffices to prove that both
sides have the same effect on an element `α ∈ CH_*(E)`"), and it is the third conjunct; the second
is the case `X' = X` read on `E` itself rather than on `X ×_X E`. -/
@[stacks 0FEF "the whole lemma, for r ≥ 1 (the source's (r-1)! presupposes it): c_t(i_*O_X) = 0 \
for 0 < t < r, and p^* ∘ π_* ∘ c_r(i_*O_X) = (-1)^{r-1}(r-1)! j^* on every test scheme \
X' ×_X E ⟶ E, which are the test schemes on which the composite p^* ∘ π_* ∘ c_r is defined"]
theorem chernClass_pushforward_zeroSection (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (𝒞 : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (hr : r ≠ 0) :
    haveI := flat_projectiveCompletionProj 𝒞 r
    haveI := locallyOfFiniteType_projectiveCompletionProj 𝒞 r
    (∀ t : ℕ, 0 < t → t < r →
      perfectChernClass C (projectiveCompletionProj 𝒞 ≫ sX)
        (hasDefinedChernClasses_pushforward_zeroSection 𝒞 r) t = 0) ∧
    (∀ (k : ℤ) (α : chowGroup C (𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX) (k + r)),
      chowGroupCast C ((complementOpen 𝒞).ι ≫ 𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX) (by ring)
        (bundlePullback C sX ((complementOpen 𝒞).ι ≫ 𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX)
        ((complementOpen 𝒞).ι ≫ projectiveCompletionProj 𝒞) (by simp) r
        (relativeDimension_complementOpen_ι_comp 𝒞 r) (k + r - r)
        (properChowPushforward C (𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX) sX
          (projectiveCompletionProj 𝒞) (by simp) (k + r - r)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ (by simp) _)
          ((perfectChernClass C (projectiveCompletionProj 𝒞 ≫ sX)
            (hasDefinedChernClasses_pushforward_zeroSection 𝒞 r)).op (𝟙 _) (k + r) r α))) =
        ((-1 : ℤ) ^ (r - 1) * (Nat.factorial (r - 1) : ℤ)) •
          chowGroupOpensRestrictOfIsOpenImmersion C (𝟙 _ ≫ projectiveCompletionProj 𝒞 ≫ sX)
            (complementOpen 𝒞) (k + r) α) ∧
    (∀ {X' : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (g : X' ⟶ X)
      [LocallyOfFiniteType g] (hg : g ≫ sX = sX') (k : ℤ)
      (α : chowGroup C (pullback.snd g (projectiveCompletionProj 𝒞) ≫
        projectiveCompletionProj 𝒞 ≫ sX) (k + r)),
      chowGroupCast C _ (by ring) (bundlePullback C sX'
        ((complementOpenBaseChange g 𝒞).ι ≫ pullback.snd g (projectiveCompletionProj 𝒞) ≫
          projectiveCompletionProj 𝒞 ≫ sX)
        ((complementOpenBaseChange g 𝒞).ι ≫ pullback.fst g (projectiveCompletionProj 𝒞))
        (by rw [Category.assoc, pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞]) r
        (relativeDimension_complementOpenBaseChange g 𝒞 r) (k + r - r)
        (properChowPushforward C
          (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX) sX'
          (pullback.fst g (projectiveCompletionProj 𝒞))
          (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) (k + r - r)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX' _
            (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) _)
          ((perfectChernClass C (projectiveCompletionProj 𝒞 ≫ sX)
            (hasDefinedChernClasses_pushforward_zeroSection 𝒞 r)).op
            (pullback.snd g (projectiveCompletionProj 𝒞)) (k + r) r α))) =
        ((-1 : ℤ) ^ (r - 1) * (Nat.factorial (r - 1) : ℤ)) •
          chowGroupOpensRestrictOfIsOpenImmersion C
            (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
            (complementOpenBaseChange g 𝒞) (k + r) α) := by
  have := flat_projectiveCompletionProj 𝒞 r
  have := locallyOfFiniteType_projectiveCompletionProj 𝒞 r
  exact ⟨fun t ht htr => perfectChernClass_eq_zero_of_koszulModule C sX hr
      (koszulResolutionZeroSection 𝒞 r) _ t ht htr,
    fun k α => flatPullback_pushforward_perfectChernClass_of_koszulModule C sX hr
      (koszulResolutionZeroSection 𝒞 r) _ k α,
    fun sX' _ g _ hg k α => flatPullback_pushforward_perfectChernClass_of_koszulModule_baseChange
      C sX sX' g hg hr (koszulResolutionZeroSection 𝒞 r) _ k α⟩

end ZeroSection

end Stacks.Chow

end
