module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionDivision
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundle
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassCommute
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass.BaseChange

/-!
# The Gysin class of a subbundle of a virtual normal bundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed subscheme with virtual normal sheaf `𝒩` in the
sense of Stacks 0FBQ, and let

  `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_Z`-modules such that the surjection
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` of the virtual normal sheaf factors as `σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` through a
surjection `σ' : (𝒩')^∨ ⟶ 𝒞_{Z/X}`, so that `𝒩'` is a virtual normal sheaf too. **Stacks 0FBL**
asserts that then

  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`

as bivariant classes.

The proof is the source's. The surjection `𝒩^∨ ⟶ (𝒩')^∨` gives a closed immersion
`j : N' ⟶ N` of the vector bundles (`Stacks.Chow.subbundleEmbedding`), and the factorization of
`σ` through `σ'` makes the closed immersion `C_ZX ⟶ N` of the normal cone factor as
`C_ZX ⟶ N' ⟶ N` (`Stacks.Chow.VirtualNormalBundle.normalConeEmbedding_eq_comp_subbundleEmbedding`).
The class `c(Z ⟶ X, 𝒩)` is characterized by `p^* ∘ c = ι_* ∘ j^* ∘ C` (Stacks 0FBK,
`Stacks.Chow.isVirtualNormalBundleClass_iff`); by the factorization the right-hand side for `𝒩`
is `j_*` of the one for `𝒩'`, which is `j_* (p')^* (c(Z ⟶ X, 𝒩') ∩ α)`, and Stacks 0FAA on every
test scheme (`Stacks.Chow.subbundleEmbeddingPullbackMap_pushforward_flatPullback_eq_topChernCap`)
rewrites that as `p^*(c_top(ℰ) ∩ c(Z ⟶ X, 𝒩') ∩ α)`.

## Main definitions

The base change `Stacks.Chow.subbundleTestBaseChange` of a morphism of bundles along a test scheme
and the proper pushforward `Stacks.Chow.subbundleTestPushforward` along it are those of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundle`, which also states
Stacks 0FBL for classes characterized by the construction of Stacks 0FBK given as data; this file
proves it for the constructed classes.

* `Stacks.Chow.subbundleChernClassCap` — the cap product with the top Chern class `c_e(ℰ)` on the
  base change `Z ×_X T`, at the degrees of the Gysin class of `𝒩'`.

## Main results

* `Stacks.Chow.VirtualNormalBundle.normalConeEmbedding_eq_comp_subbundleEmbedding` — the closed
  immersion `C_ZX ⟶ N` factors through `N'`.
* `Stacks.Chow.virtualNormalConeClass_cap_eq_subbundleTestPushforward` — consequently
  `ι_* ∘ j^* ∘ C` for `𝒩` is `j_*` of the one for `𝒩'`, on every test scheme.
* `Stacks.Chow.subbundleTestPushforward_bundleFlatPullback` — Stacks 0FAA on every test scheme,
  for the base changes of the two bundle projections.
* `Stacks.Chow.virtualNormalBundleClass_cap_eq_chernCap_comp` — on cap operations,
  `c ∩ α = c_top(ℰ) ∩ (c' ∩ α)` for any classes `c`, `c'` satisfying the relation of Stacks 0FBK
  for `𝒩` and `𝒩'`.
* `Stacks.Chow.virtualNormalBundleClass_eq_of_isTopChernComposition` — Stacks 0FBL at constant
  rank: `c(Z ⟶ X, 𝒩) = c_e(ℰ) ∘ c(Z ⟶ X, 𝒩')` in `A^m(Z ⟶ X)`. Stacks 0FBL itself, at arbitrary
  rank in `A^*(Z ⟶ X)^∧`, is
  `Stacks.Chow.completedVirtualNormalGysinClass_eq_of_isTopChernComposition`.

## Implementation notes

The ranks of `𝒩'` and `ℰ` are taken constant, `m'` and `e`, which is the case the classes of
Stacks 0FBK are formed in; then `c_top(ℰ)` is the Chern class `c_e(ℰ) ∈ A^e(Z)` of Stacks 0B7H
(`Stacks.Chow.GenuineChern.chernClass`), and the composite with `c(Z ⟶ X, 𝒩')` is that of
Stacks 0B75 (`Stacks.Chow.bivariantCompositeOfInvertible`), a class for `𝟙 Z ≫ i` of degree
`e + m'`. The rank of `𝒩` is taken to be `m' + e`: on a nonempty `Z` the sequence forces it
(`Stacks.Chow.subbundleRank_add`), and on an empty `Z` every rank is, so this is no restriction,
and it puts the two sides of the tag in the same group `A^{m' + e}(Z ⟶ X)` with no point of `Z`
needed. On each test scheme the degrees are matched at a point of `Z ×_X T` when there is one,
and both sides vanish when there is none.

The bundles are the vector bundles `N = Spec_Z(Sym(𝒩^∨))` and `N' = Spec_Z(Sym((𝒩')^∨))` of the
two virtual normal sheaves, `Stacks.Chow.VirtualNormalBundle.totalSpace`, and the embedding
between them is the canonical `Stacks.Chow.subbundleEmbedding` of Stacks 0FAA.

## References

* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### The normal cone factors through the subbundle -/

section Factorization

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] (𝒩 𝒩' : VirtualNormalBundle i)
  (inc : 𝒩'.bundle ⟶ 𝒩.bundle)

/-- The embedding `j : N' ⟶ N` of Stacks 0FAA between the vector bundles of two virtual normal
bundles is a morphism over `Z`. -/
theorem VirtualNormalBundle.subbundleEmbedding_projection :
    subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc ≫ 𝒩.projection = 𝒩'.projection :=
  subbundleEmbedding_comp_dualVectorBundleToBase 𝒩'.bundle 𝒩.bundle inc

/-- **The closed immersion `C_ZX ⟶ N` factors through the subbundle.** If the surjection
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors as `σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)`, then the closed immersion
`ι : C_ZX ⟶ N` of the normal cone into the vector bundle of `𝒩` is the one into the vector
bundle of `𝒩'` followed by the embedding `j : N' ⟶ N`: both are relative spectra of the induced
surjections of symmetric algebras, and `𝐕` is functorial. -/
theorem VirtualNormalBundle.normalConeEmbedding_eq_comp_subbundleEmbedding
    (hsigma : dualMap inc ≫ 𝒩'.surjection = 𝒩.surjection) :
    𝒩.normalConeEmbedding =
      𝒩'.normalConeEmbedding ≫ subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc := by
  have h : 𝒩.conormalDegreeOneSurjection = dualMap inc ≫ 𝒩'.conormalDegreeOneSurjection :=
    (congrArg (· ≫ (Stacks.Conormal.conormalDegreeOneIso i).hom) hsigma.symm).trans
      (Category.assoc _ _ _)
  have hb : 𝒩.normalBundleEmbedding =
      𝒩'.normalBundleEmbedding ≫ subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc :=
    (congrArg (fun f => (Scheme.Modules.vectorBundleMap Z f).left) h).trans
      (congrArg CommaMorphism.left (Scheme.Modules.vectorBundleMap_comp Z _ _))
  exact (congrArg (Stacks.Conormal.normalConeToNormalBundle i ≫ ·) hb).trans
    (Category.assoc _ _ _).symm

end Factorization

/-! ### The two steps of the proof -/

/-- The cap product with the top Chern class `c_top(ℰ) = c_e(ℰ)` of Stacks 0B7H on the base change
`Z ×_X T` of `Z` along a test scheme `g : T ⟶ X`, at the degrees of the Gysin class of `𝒩'`: it
takes `A_{k-m'}(Z ×_X T)` to `A_{(k-m')-e}(Z ×_X T)`, and is the cap product with the `e`-th
Chern class of the pullback of `ℰ` to `Z ×_X T`. -/
def subbundleChernClassCap (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (i : Z ⟶ X) (m' e : ℕ) (Eb : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (pullback.fst i g ≫ sZ) (k - (m' : ℤ)) →+
      chowGroup C (pullback.fst i g ≫ sZ) ((k - (m' : ℤ)) - (e : ℤ)) :=
  GenuineChern.chernCap C e (pullback.fst i g ≫ sZ)
    ((Scheme.Modules.pullback (pullback.fst i g)).obj Eb) (k - (m' : ℤ)) (Fin.last e)

/-- Proper pushforward from the base changes of two equal morphisms `f₁ = f₂ : A ⟶ Y` along a
test scheme `t : T ⟶ Y` into the base change of `g₀ : Y₀ ⟶ Y`: if the two proper morphisms
`u₁`, `u₂` are the base changes of one morphism `a : A ⟶ Y₀` over `T`, they push heterogeneously
equal classes to the same class. -/
theorem properChowPushforward_pullback_eq_of_heq (C : ChowSituation.{u})
    {A Y Y₀ T : Scheme.{u}} {sA : A ⟶ C.S} {sY₀ : Y₀ ⟶ C.S} {f₁ f₂ : A ⟶ Y} (e : f₁ = f₂)
    (t : T ⟶ Y) {g₀ : Y₀ ⟶ Y} [LocallyOfFiniteType (pullback.fst g₀ t ≫ sY₀)]
    [LocallyOfFiniteType (pullback.fst f₁ t ≫ sA)] [LocallyOfFiniteType (pullback.fst f₂ t ≫ sA)]
    (a : A ⟶ Y₀) (u₁ : pullback f₁ t ⟶ pullback g₀ t) (u₂ : pullback f₂ t ⟶ pullback g₀ t)
    [IsProper u₁] [IsProper u₂] (h₁ : u₁ ≫ pullback.fst g₀ t = pullback.fst f₁ t ≫ a)
    (h₂ : u₂ ≫ pullback.fst g₀ t = pullback.fst f₂ t ≫ a)
    (h₁' : u₁ ≫ pullback.snd g₀ t = pullback.snd f₁ t)
    (h₂' : u₂ ≫ pullback.snd g₀ t = pullback.snd f₂ t)
    (hu₁ : u₁ ≫ (pullback.fst g₀ t ≫ sY₀) = pullback.fst f₁ t ≫ sA)
    (hu₂ : u₂ ≫ (pullback.fst g₀ t ≫ sY₀) = pullback.fst f₂ t ≫ sA) (k : ℤ)
    (hfac₁ : ProperPushforwardFactorsThroughRationalEquivalence C _ _ u₁ hu₁ k)
    (hfac₂ : ProperPushforwardFactorsThroughRationalEquivalence C _ _ u₂ hu₂ k)
    (y₁ : chowGroup C (pullback.fst f₁ t ≫ sA) k) (y₂ : chowGroup C (pullback.fst f₂ t ≫ sA) k)
    (hy : y₁ ≍ y₂) :
    properChowPushforward C _ _ u₁ hu₁ k hfac₁ y₁ =
      properChowPushforward C _ _ u₂ hu₂ k hfac₂ y₂ := by
  subst e
  obtain rfl : u₁ = u₂ := pullback.hom_ext (h₁.trans h₂.symm) (h₁'.trans h₂'.symm)
  obtain rfl := eq_of_heq hy
  rfl

section Steps

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (𝒩 𝒩' : VirtualNormalBundle i)
  (m' e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle m']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle (m' + e)]
  (Eb : Z.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
  (inc : 𝒩'.bundle ⟶ 𝒩.bundle) (pr : 𝒩.bundle ⟶ Eb) (w : inc ≫ pr = 0)
  (hseq : (ShortComplex.mk inc pr w).ShortExact)

include e hseq in
/-- The embedding `j : N' ⟶ N` of Stacks 0FAA is a closed immersion. -/
theorem isClosedImmersion_subbundleEmbedding_virtualNormalBundle :
    @IsClosedImmersion 𝒩'.totalSpace 𝒩.totalSpace (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc) :=
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Eb e
  subbundleEmbedding_isClosedImmersion_of_shortExact 𝒩'.bundle 𝒩.bundle Eb inc pr w hseq

include hseq in
/-- **The class `ι_* ∘ j^* ∘ C` of `𝒩` is `j_*` of the one of `𝒩'`**, on every test scheme, when
the surjection of `𝒩` factors through that of `𝒩'`. This is the factorization
`C_ZX ⟶ N' ⟶ N` of the closed immersion of the normal cone
(`Stacks.Chow.VirtualNormalBundle.normalConeEmbedding_eq_comp_subbundleEmbedding`) followed by
functoriality of proper pushforward: the two classes are pushforwards of one and the same class
`j^* ∘ C ∈ A⁰(C_ZX ⟶ X)`. -/
theorem virtualNormalConeClass_cap_eq_subbundleTestPushforward
    (hsigma : dualMap inc ≫ 𝒩'.surjection = 𝒩.surjection) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    letI := isClosedImmersion_subbundleEmbedding_virtualNormalBundle i 𝒩 𝒩' e Eb inc pr w hseq
    (virtualNormalConeClass C sZ sX i hi 𝒩).cap g k α =
      subbundleTestPushforward C sZ (𝒩.projection ≫ sZ) (𝒩'.projection ≫ sZ) i 𝒩.projection
        𝒩'.projection rfl rfl (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc)
        (VirtualNormalBundle.subbundleEmbedding_projection 𝒩 𝒩' inc) g (k - (0 : ℤ))
        ((virtualNormalConeClass C sZ sX i hi 𝒩').cap g k α) := by
  let := isClosedImmersion_subbundleEmbedding_virtualNormalBundle i 𝒩 𝒩' e Eb inc pr w hseq
  have := locallyOfFiniteType_normalConeToBase C sX i
  have hι := VirtualNormalBundle.normalConeEmbedding_eq_comp_subbundleEmbedding 𝒩 𝒩' inc hsigma
  have hj := VirtualNormalBundle.subbundleEmbedding_projection 𝒩 𝒩' inc
  have hf : 𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i =
      𝒩'.normalConeEmbedding ≫ 𝒩'.projection ≫ i :=
    (congrArg (· ≫ 𝒩.projection ≫ i) hι).trans ((Category.assoc _ _ _).trans
      (congrArg (𝒩'.normalConeEmbedding ≫ ·)
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ i) hj))))
  have hcap : ∀ (𝒩₀ : VirtualNormalBundle i),
      (virtualNormalConeClass C sZ sX i hi 𝒩₀).cap g k α =
        bivariantProperPushforwardCap C (gysinSystemOfInvertible C)
          (Stacks.Conormal.normalConeToBase i ≫ sZ) (𝒩₀.projection ≫ sZ) sX
          𝒩₀.normalConeEmbedding (𝒩₀.projection ≫ i)
          (by rw [𝒩₀.normalConeEmbedding_projection_assoc])
          (comp_comp_structureMorphism_eq rfl hi) (properPushforwardDescends C) 0
          (BivariantClass.copy C (gysinSystemOfInvertible C) _ sX
            (f := normalConeToFibreAtInfinity i sX ≫
              modificationProjectionAtInfinity sX
                (blowupAtInfinityToProjectiveLineProduct i.ker sX))
            (f' := 𝒩₀.normalConeEmbedding ≫ 𝒩₀.projection ≫ i)
            (by rw [normalConeToFibreAtInfinity_comp_projection,
              𝒩₀.normalConeEmbedding_projection_assoc])
            _ _ (zero_add 0)
            (bivariantCompositeOfInvertible C (Stacks.Conormal.normalConeToBase i ≫ sZ)
              (modificationProjectionAtInfinity sX
                (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX) sX
              (normalConeToFibreAtInfinity i sX)
              (modificationProjectionAtInfinity sX
                (blowupAtInfinityToProjectiveLineProduct i.ker sX))
              (normalConeToFibreAtInfinity_comp_projection_comp C sZ sX i hi) rfl
              (-((0 : ℕ) : ℤ)) 0
              (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C
                (Stacks.Conormal.normalConeToBase i ≫ sZ)
                (modificationProjectionAtInfinity sX
                  (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX)
                (normalConeToFibreAtInfinity i sX)
                (normalConeToFibreAtInfinity_comp_projection_comp C sZ sX i hi))
              (gysinAtInfinityClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
                (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX))))
          g k α := fun _ => rfl
  have := isClosedImmersion_subbundleTestBaseChange (N' := 𝒩'.totalSpace) i 𝒩.projection
    (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc) hj g
  rw [hcap 𝒩, hcap 𝒩', bivariantProperPushforwardCap_apply, bivariantProperPushforwardCap_apply]
  have hcomp := properChowPushforward_comp C
    (pullback.fst (𝒩'.normalConeEmbedding ≫ 𝒩'.projection ≫ i) g ≫
      (Stacks.Conormal.normalConeToBase i ≫ sZ))
    (pullback.fst (𝒩'.projection ≫ i) g ≫ (𝒩'.projection ≫ sZ))
    (pullback.fst (𝒩.projection ≫ i) g ≫ (𝒩.projection ≫ sZ))
    (bivariantPushforwardBaseChange 𝒩'.normalConeEmbedding (𝒩'.projection ≫ i) g)
    (subbundleTestBaseChange (N' := 𝒩'.totalSpace) i 𝒩.projection
      (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc) hj g)
    (bivariantPushforwardBaseChange_comp_structure
      (by rw [𝒩'.normalConeEmbedding_projection_assoc]) (𝒩'.projection ≫ i) g)
    (subbundleTestBaseChange_comp_structureMorphism (N' := 𝒩'.totalSpace) i 𝒩.projection sZ _ _
      rfl rfl _ hj g)
    (k - (0 : ℤ)) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)
  refine Eq.trans ?_ (congrFun (congrArg DFunLike.coe hcomp) _).symm
  refine properChowPushforward_pullback_eq_of_heq C hf g 𝒩.normalConeEmbedding _ _
    (bivariantPushforwardBaseChange_fst _ _ _) ?_ (bivariantPushforwardBaseChange_snd _ _ _) ?_
    _ _ (k - (0 : ℤ)) _ _ _ _ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (subbundleTestBaseChange_fst i 𝒩.projection _ hj g)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc)
        (bivariantPushforwardBaseChange_fst _ _ _)).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hι.symm)))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (subbundleTestBaseChange_snd i 𝒩.projection _ hj g)).trans
      (bivariantPushforwardBaseChange_snd _ _ _))
  · exact (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ g k α).trans
      (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ g k α).symm

include hseq in
/-- **Stacks 0FAA on every test scheme, for the bundles of two virtual normal bundles.** With
`p : N ×_X T ⟶ Z ×_X T` and `p' : N' ×_X T ⟶ Z ×_X T` the base changes of the two bundle
projections along a test scheme `g : T ⟶ X` and `j` the base change of the embedding,

  `j_* (p')^* β = p^* (c_e(ℰ) ∩ β)`

in `A_k(N ×_X T)`, for `β ∈ A_{k-m'}(Z ×_X T)`. This is
`Stacks.Chow.subbundleEmbeddingPullbackMap_pushforward_flatPullback_eq_topChernCap` for
`Z ×_X T ⟶ Z`, read through the pasting isomorphisms `N ×_Z (Z ×_X T) ≅ N ×_X T`. -/
theorem subbundleTestPushforward_bundleFlatPullback {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (β : chowGroup C (pullback.fst i g ≫ sZ) (k - (m' : ℤ))) :
    letI := isClosedImmersion_subbundleEmbedding_virtualNormalBundle i 𝒩 𝒩' e Eb inc pr w hseq
    subbundleTestPushforward C sZ (𝒩.projection ≫ sZ) (𝒩'.projection ≫ sZ) i 𝒩.projection
        𝒩'.projection rfl rfl (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc)
        (VirtualNormalBundle.subbundleEmbedding_projection 𝒩 𝒩' inc) g (k - (0 : ℤ))
        (bundleFlatPullback C sZ (𝒩'.projection ≫ sZ) i 𝒩'.projection rfl m'
          (𝒩'.flat_projection_of_rank m') (𝒩'.relativeDimension_projection_of_rank m')
          (flatPullbackDescends C) g k β) =
      bundleFlatPullback C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl (m' + e)
        (𝒩.flat_projection_of_rank (m' + e)) (𝒩.relativeDimension_projection_of_rank (m' + e))
        (flatPullbackDescends C) g k
        (chowGroupDegreeEquiv C (pullback.fst i g ≫ sZ) (by push_cast; ring)
          (subbundleChernClassCap C sZ i m' e Eb g k β)) := by
  let := isClosedImmersion_subbundleEmbedding_virtualNormalBundle i 𝒩 𝒩' e Eb inc pr w hseq
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Eb e
  have hj := VirtualNormalBundle.subbundleEmbedding_projection 𝒩 𝒩' inc
  have := isClosedImmersion_subbundleTestBaseChange (N' := 𝒩'.totalSpace) i 𝒩.projection
    (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc) hj g
  have := 𝒩.flat_projection_of_rank (m' + e)
  have := 𝒩'.flat_projection_of_rank m'
  by_cases hW : Nonempty ↥(pullback i g)
  swap
  · have : IsEmpty ↥(pullback i g) := not_nonempty_iff.mp hW
    have : IsEmpty ↥(pullback (𝒩.projection ≫ i) g) :=
      ⟨fun p => isEmptyElim ((bundleTestBaseChange i 𝒩.projection g).base p)⟩
    have := subsingleton_chowGroup_of_isEmpty C
      (pullback.fst (𝒩.projection ≫ i) g ≫ 𝒩.projection ≫ sZ) (k - (0 : ℤ))
    exact Subsingleton.elim _ _
  obtain ⟨y⟩ := hW
  have := locallyOfFiniteType_bundleTestBaseChange i 𝒩.projection g
  have := flat_bundleTestBaseChange i 𝒩.projection (𝒩.flat_projection_of_rank (m' + e)) g
  have hclN := isClosedImmersion_subbundleEmbeddingPullbackMap 𝒩'.bundle 𝒩.bundle
    (pullback.fst i g) Eb inc pr w hseq
  have hcl : @IsClosedImmersion (pullback 𝒩'.projection (pullback.fst i g))
      (pullback 𝒩.projection (pullback.fst i g))
      (subbundleEmbeddingPullbackMap 𝒩'.bundle 𝒩.bundle (pullback.fst i g) inc) := hclN
  have hpr : @IsProper (pullback 𝒩'.projection (pullback.fst i g))
      (pullback 𝒩.projection (pullback.fst i g))
      (subbundleEmbeddingPullbackMap 𝒩'.bundle 𝒩.bundle (pullback.fst i g) inc) :=
    (inferInstance : IsProper (subbundleEmbeddingPullbackMap 𝒩'.bundle 𝒩.bundle
      (pullback.fst i g) inc))
  have hcl₂ : IsClosedImmersion (@CategoryStruct.comp _ _
      (pullback 𝒩'.projection (pullback.fst i g)) (pullback 𝒩.projection (pullback.fst i g)) _
      (subbundleEmbeddingPullbackMap 𝒩'.bundle 𝒩.bundle (pullback.fst i g) inc)
      (pullbackRightPullbackFstIso i g 𝒩.projection).hom) :=
    @AlgebraicGeometry.IsClosedImmersion.comp _ _ _ _ _ hcl inferInstance
  have hBC := subbundleEmbeddingPullbackMap_pushforward_flatPullback_eq_topChernCap C sZ
    𝒩'.bundle 𝒩.bundle Eb m' (m' + e) e inc pr w hseq (pullback.fst i g)
    ((pullback.fst i g).base y) (k - (m' : ℤ)) β
  have hL := bundleFlatPullbackChow_heq C sZ (𝒩'.projection ≫ sZ) i 𝒩'.projection rfl m'
    (𝒩'.flat_projection_of_rank m') (𝒩'.relativeDimension_projection_of_rank m') g (k - (m' : ℤ)) β
  have hR := bundleFlatPullbackChow_heq C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl (m' + e)
    (𝒩.flat_projection_of_rank (m' + e)) (𝒩.relativeDimension_projection_of_rank (m' + e)) g
    ((k - (m' : ℤ)) - (e : ℤ)) (subbundleChernClassCap C sZ i m' e Eb g k β)
  have hcompat : (pullbackRightPullbackFstIso i g 𝒩'.projection).hom ≫
      subbundleTestBaseChange (N' := 𝒩'.totalSpace) i 𝒩.projection
        (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc) hj g =
      @CategoryStruct.comp _ _ (pullback 𝒩'.projection (pullback.fst i g))
        (pullback 𝒩.projection (pullback.fst i g)) _
        (subbundleEmbeddingPullbackMap 𝒩'.bundle 𝒩.bundle (pullback.fst i g) inc)
        (pullbackRightPullbackFstIso i g 𝒩.projection).hom := by
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (subbundleTestBaseChange_fst i 𝒩.projection _ hj g)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc)
          (pullbackRightPullbackFstIso_hom_fst i g 𝒩'.projection)).trans
          ((subbundleEmbeddingPullbackMap_fst 𝒩'.bundle 𝒩.bundle (pullback.fst i g) inc).symm.trans
            ((congrArg (_ ≫ ·) (pullbackRightPullbackFstIso_hom_fst i g 𝒩.projection)).symm.trans
              (Category.assoc _ _ _).symm)))))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (subbundleTestBaseChange_snd i 𝒩.projection _ hj g)).trans
        ((pullbackRightPullbackFstIso_hom_snd i g 𝒩'.projection).trans
          ((congrArg (· ≫ pullback.snd i g)
            (subbundleEmbeddingPullbackMap_snd 𝒩'.bundle 𝒩.bundle (pullback.fst i g)
              inc)).symm.trans
            ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
              (pullbackRightPullbackFstIso_hom_snd i g 𝒩.projection)).symm.trans
              (Category.assoc _ _ _).symm)))))
  have hPgen : ∀ 𝒩₀ : VirtualNormalBundle i,
      (pullbackRightPullbackFstIso i g 𝒩₀.projection).hom ≫
        (pullback.fst (𝒩₀.projection ≫ i) g ≫ 𝒩₀.projection ≫ sZ) =
      pullback.fst 𝒩₀.projection (pullback.fst i g) ≫ 𝒩₀.projection ≫ sZ := fun 𝒩₀ =>
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ 𝒩₀.projection ≫ sZ) (pullbackRightPullbackFstIso_hom_fst i g 𝒩₀.projection))
  have hP' := hPgen 𝒩'
  have hP := hPgen 𝒩
  have hJT := subbundleTestBaseChange_comp_structureMorphism (N' := 𝒩'.totalSpace) i
    𝒩.projection sZ (𝒩.projection ≫ sZ) (𝒩'.projection ≫ sZ) rfl rfl _ hj g
  have hJB : @CategoryStruct.comp _ _ (pullback 𝒩'.projection (pullback.fst i g))
      (pullback 𝒩.projection (pullback.fst i g)) _
      (subbundleEmbeddingPullbackMap 𝒩'.bundle 𝒩.bundle (pullback.fst i g) inc)
      (pullback.fst 𝒩.projection (pullback.fst i g) ≫ 𝒩.projection ≫ sZ) =
      pullback.fst 𝒩'.projection (pullback.fst i g) ≫ 𝒩'.projection ≫ sZ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝒩.projection ≫ sZ)
      (subbundleEmbeddingPullbackMap_fst 𝒩'.bundle 𝒩.bundle (pullback.fst i g) inc)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (subbundleEmbedding_comp_base 𝒩'.bundle 𝒩.bundle sZ inc))))
  -- functoriality of pushforward
  have hB : ∀ z : chowGroup C (pullback.fst 𝒩'.projection (pullback.fst i g) ≫
      𝒩'.projection ≫ sZ) ((k - (m' : ℤ)) + (m' : ℤ)),
      subbundleTestPushforward C sZ (𝒩.projection ≫ sZ) (𝒩'.projection ≫ sZ) i 𝒩.projection
          𝒩'.projection rfl rfl (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc) hj g
          ((k - (m' : ℤ)) + (m' : ℤ))
          (chowPushforwardOfIso C _ _ (pullbackRightPullbackFstIso i g 𝒩'.projection).hom hP'
            ((k - (m' : ℤ)) + (m' : ℤ)) z) =
        chowPushforwardOfIso C _ _ (pullbackRightPullbackFstIso i g 𝒩.projection).hom hP
          ((k - (m' : ℤ)) + (m' : ℤ))
          (chowPushforwardOfIsClosedImmersion C
            (pullback.fst 𝒩'.projection (pullback.fst i g) ≫ 𝒩'.projection ≫ sZ)
            (pullback.fst 𝒩.projection (pullback.fst i g) ≫ 𝒩.projection ≫ sZ)
            (subbundleEmbeddingPullbackMap 𝒩'.bundle 𝒩.bundle (pullback.fst i g) inc) hJB
            ((k - (m' : ℤ)) + (m' : ℤ)) z) := by
    intro z
    have e1 := properChowPushforward_comp C
      (pullback.fst 𝒩'.projection (pullback.fst i g) ≫ 𝒩'.projection ≫ sZ)
      (pullback.fst (𝒩'.projection ≫ i) g ≫ 𝒩'.projection ≫ sZ)
      (pullback.fst (𝒩.projection ≫ i) g ≫ 𝒩.projection ≫ sZ)
      (pullbackRightPullbackFstIso i g 𝒩'.projection).hom
      (subbundleTestBaseChange (N' := 𝒩'.totalSpace) i 𝒩.projection
        (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc) hj g)
      hP' hJT ((k - (m' : ℤ)) + (m' : ℤ))
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _ _ _)
    have e2 := properChowPushforward_comp C
      (pullback.fst 𝒩'.projection (pullback.fst i g) ≫ 𝒩'.projection ≫ sZ)
      (pullback.fst 𝒩.projection (pullback.fst i g) ≫ 𝒩.projection ≫ sZ)
      (pullback.fst (𝒩.projection ≫ i) g ≫ 𝒩.projection ≫ sZ)
      (subbundleEmbeddingPullbackMap 𝒩'.bundle 𝒩.bundle (pullback.fst i g) inc)
      (pullbackRightPullbackFstIso i g 𝒩.projection).hom hJB hP ((k - (m' : ℤ)) + (m' : ℤ))
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    have e3 := chowPushforwardOfIsClosedImmersion_congr C
      (pullback.fst 𝒩'.projection (pullback.fst i g) ≫ 𝒩'.projection ≫ sZ)
      (pullback.fst (𝒩.projection ≫ i) g ≫ 𝒩.projection ≫ sZ) _ _ hcompat
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hJT).trans hP'))
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hP).trans hJB))
      ((k - (m' : ℤ)) + (m' : ℤ))
    exact (congrFun (congrArg DFunLike.coe e1) z).trans
      ((congrFun (congrArg DFunLike.coe e3) z).trans (congrFun (congrArg DFunLike.coe e2) z).symm)
  have hdeg₁ : (k - (m' : ℤ)) + (m' : ℤ) = (k - (m' : ℤ)) - (e : ℤ) + ((m' + e : ℕ) : ℤ) := by
    push_cast; ring
  have core : subbundleTestPushforward C sZ (𝒩.projection ≫ sZ) (𝒩'.projection ≫ sZ) i
      𝒩.projection 𝒩'.projection rfl rfl (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc) hj g
      ((k - (m' : ℤ)) + (m' : ℤ))
      (bundleFlatPullbackChow C sZ (𝒩'.projection ≫ sZ) i 𝒩'.projection rfl m'
        (𝒩'.flat_projection_of_rank m') (𝒩'.relativeDimension_projection_of_rank m')
        (flatPullbackDescends C) g (k - (m' : ℤ)) β) ≍
      bundleFlatPullbackChow C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl (m' + e)
        (𝒩.flat_projection_of_rank (m' + e)) (𝒩.relativeDimension_projection_of_rank (m' + e))
        (flatPullbackDescends C) g
        ((k - (m' : ℤ)) - (e : ℤ)) (subbundleChernClassCap C sZ i m' e Eb g k β) := by
    refine HEq.trans (heq_of_eq ((congrArg _ (eq_of_heq hL)).trans (hB _))) ?_
    refine HEq.trans ?_ hR.symm
    refine properChowPushforward_heq_congr C _ _ _ _ hdeg₁ _ _ _ _ ?_
    exact (heq_of_eq hBC).trans (cast_heq _ _)
  have hdeg₂ : (k - (m' : ℤ)) - (e : ℤ) = k - ((m' + e : ℕ) : ℤ) := by push_cast; ring
  have hout : bundleFlatPullbackChow C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl (m' + e)
        (𝒩.flat_projection_of_rank (m' + e)) (𝒩.relativeDimension_projection_of_rank (m' + e))
        (flatPullbackDescends C) g
        ((k - (m' : ℤ)) - (e : ℤ)) (subbundleChernClassCap C sZ i m' e Eb g k β) ≍
      bundleFlatPullbackChow C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl (m' + e)
        (𝒩.flat_projection_of_rank (m' + e)) (𝒩.relativeDimension_projection_of_rank (m' + e))
        (flatPullbackDescends C) g
        (k - ((m' + e : ℕ) : ℤ))
        (chowGroupDegreeEquiv C (pullback.fst i g ≫ sZ) hdeg₂
          (subbundleChernClassCap C sZ i m' e Eb g k β)) := by
    unfold bundleFlatPullbackChow
    exact flatPullbackChow_heq_congr C _ _ _ _ _ _ rfl rfl _ _ hdeg₂ _ _ _ _
      (chowGroupDegreeEquiv_heq C _ _ _).symm
  refine eq_of_heq (HEq.trans ?_ ((core.trans hout).trans (chowGroupDegreeEquiv_heq C _ _ _).symm))
  exact properChowPushforward_heq_congr C _ _
    (subbundleTestBaseChange (N' := 𝒩'.totalSpace) i 𝒩.projection
      (subbundleEmbedding 𝒩'.bundle 𝒩.bundle inc) hj g)
    hJT (by ring)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _ _
    (chowGroupDegreeEquiv_heq C _ _ _)

end Steps

/-! ### Stacks 0FBL -/

section Main

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (𝒩 𝒩' : VirtualNormalBundle i)
  (m' e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle m']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle (m' + e)]
  (Eb : Z.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
  (inc : 𝒩'.bundle ⟶ 𝒩.bundle) (pr : 𝒩.bundle ⟶ Eb)

/-- **The relation of Stacks 0FBK for a subbundle, on cap operations.** In the situation of
Stacks 0FBL — a short exact sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite locally free `𝒪_Z`-modules
of constant ranks `m'`, `m' + e` and `e` whose inclusion dualizes to a factorization
`σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` of the conormal surjection of `𝒩` through that of `𝒩'` — let `c` and
`c'` be bivariant classes, for any Gysin system, satisfying the relation
`p^* ∘ c = ι_* ∘ j^* ∘ C` of Stacks 0FBK for `𝒩` and for `𝒩'`. Then

  `c ∩ α = c_e(ℰ) ∩ (c' ∩ α)`

on every test scheme `g : T ⟶ X`, in every degree and for every `α ∈ A_k(T)`.

The relation for `𝒩` says `p^*(c ∩ α) = (ι_* ∘ j^* ∘ C) ∩ α`; the factorization of the
conormal surjection turns the right-hand side into `j_*` of the corresponding class for `𝒩'`,
which is `j_*(p')^*(c' ∩ α)` by the relation for `𝒩'`; Stacks 0FAA rewrites that as
`p^*(c_e(ℰ) ∩ (c' ∩ α))`; and `p^*` is injective (Stacks 02TY). -/
theorem virtualNormalBundleClass_cap_eq_chernCap_comp (G : GysinSystem C)
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hsigma : dualMap inc ≫ 𝒩'.surjection = 𝒩.surjection)
    {c : BivariantClass C G sZ sX i hi ((m' + e : ℕ) : ℤ)}
    {c' : BivariantClass C G sZ sX i hi (m' : ℤ)}
    (hc : IsVirtualNormalBundleClass C sZ sX i hi G 𝒩 (m' + e) c)
    (hc' : IsVirtualNormalBundleClass C sZ sX i hi G 𝒩' m' c')
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    c.cap g k α =
      chowGroupDegreeEquiv C (pullback.fst i g ≫ sZ) (by push_cast; ring)
        (subbundleChernClassCap C sZ i m' e Eb g k (c'.cap g k α)) := by
  refine eq_of_isVirtualNormalBundleClass_cap C G sZ sX i hi 𝒩 (m' + e) hc g k α _ ?_
  rw [virtualNormalConeClass_cap_eq_subbundleTestPushforward C sZ sX i hi 𝒩 𝒩' e Eb inc pr w
    hseq hsigma g k α, ← hc' g k α]
  exact (subbundleTestPushforward_bundleFlatPullback C sZ i 𝒩 𝒩' m' e Eb inc pr w hseq g k
    (c'.cap g k α)).symm

/-- **Stacks 0FBL, the constant-rank case.** Let `(S, δ)` be the base situation of chapter 42, let
`X` be locally of finite type over `S`, let `i : Z ⟶ X` be a closed subscheme with virtual normal
sheaf `𝒩`, and let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free
`𝒪_Z`-modules of constant ranks `m'`, `m' + e` and `e` such that the conormal surjection
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors as `σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` through that of `𝒩'`. Then

  `c(Z ⟶ X, 𝒩) = c_e(ℰ) ∘ c(Z ⟶ X, 𝒩')`

in `A^{m' + e}(Z ⟶ X)`, where `c_e(ℰ) = c_top(ℰ) ∈ A^e(Z)` is the Chern class of Stacks 0B7H
and the composite is that of Stacks 0B75, a class for `𝟙 Z ≫ i = i` of degree `e + m'`.

Both sides cap the same way (`Stacks.Chow.virtualNormalBundleClass_cap_eq_chernCap_comp`), the
composite capping as `c_e(ℰ) ∩ (c(Z ⟶ X, 𝒩') ∩ -)`. The statement at arbitrary ranks, in the
completed bivariant group, is
`Stacks.Chow.completedVirtualNormalGysinClass_eq_of_isTopChernComposition`, which is deduced from
this case one connected component at a time. -/
theorem virtualNormalBundleClass_eq_of_isTopChernComposition
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hsigma : dualMap inc ≫ 𝒩'.surjection = 𝒩.surjection) :
    virtualNormalBundleClass C sZ sX i hi 𝒩 (m' + e) =
      BivariantClass.copy C (gysinSystemOfInvertible C) sZ sX (Category.id_comp i)
        (comp_comp_structureMorphism_eq (Category.id_comp sZ) hi) hi (by push_cast; ring)
        (bivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hi (e : ℤ)
          (m' : ℤ) (GenuineChern.chernClass C sZ Eb e (Fin.last e))
          (virtualNormalBundleClass C sZ sX i hi 𝒩' m')) := by
  refine BivariantClass.ext C _ sZ sX i hi ((m' + e : ℕ) : ℤ) ?_
  intro T g _ k α
  rw [virtualNormalBundleClass_cap_eq_chernCap_comp C sZ sX i hi 𝒩 𝒩' m' e Eb inc pr
    (gysinSystemOfInvertible C) w hseq hsigma
    (isVirtualNormalBundleClass_virtualNormalBundleClass C sZ sX i hi 𝒩 (m' + e))
    (isVirtualNormalBundleClass_virtualNormalBundleClass C sZ sX i hi 𝒩' m') g k α]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
  refine HEq.trans ?_ (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ g k α).symm
  refine HEq.trans ?_ (BivariantClass.id_bivariantCompositeOfInvertible_cap_heq _ _ g k α).symm
  exact heq_of_eq (GenuineChern.idRule_chernClass C sZ Eb e (Fin.last e) (pullback.fst i g)
    (k - (m' : ℤ)) _).symm

end Main

end Stacks.Chow

end
