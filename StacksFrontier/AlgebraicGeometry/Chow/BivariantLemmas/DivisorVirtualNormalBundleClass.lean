module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DivisorVirtualNormalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionCartier
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ZeroSchemeVirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleProper
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleRankOne
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Determinant
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.GysinFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Conormal.FirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.IntegralPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinZeroSectionDischarge
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimConormalRank
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology

/-!
# The Gysin class of a divisor as a virtual normal class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `(ℒ, s, i : D ⟶ X)` be a triple as in Definition 02T8:
`ℒ` an invertible module on `X`, `s` a global section and `i` the closed immersion of its zero
scheme. The module `𝒩 = i^*ℒ`, with the canonical surjection `(i^*ℒ)^∨ ⟶ 𝒞_{D/X}`, is a virtual
normal sheaf for `D` in `X` of rank one (`Stacks.Chow.zeroSchemeVirtualNormalBundle`), and
**Stacks 0FBN** asserts that the Gysin homomorphism `i^*`, viewed as an element of `A^1(D ⟶ X)`
by Stacks 0B79, is the bivariant class `c(D ⟶ X, 𝒩)` of Stacks 0FBK built from it.

Both classes are the constructed ones: `Stacks.Chow.gysinBivariantClass` of Stacks 0B79 and
`Stacks.Chow.virtualNormalBundleClass` of Stacks 0FBK.

The proof is the source's. By Stacks 02UC
(`Stacks.Chow.BivariantClass.eq_of_cap_fundamentalChowClass_eq`, in
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DivisorVirtualNormalClass`) it suffices to
compare the two classes on the fundamental class `[T]_k` of every integral scheme `T` locally of
finite type over `X`, and
`[T]_k = 0` unless `k = dim_δ(T)`.

* If `T` does not lie in `D`, that is if the pulled-back section `g^*s` is nonzero, then
  `D ×_X T = Z(g^*s)` is an effective Cartier divisor on `T`, in particular a regular closed
  immersion of codimension one, and both classes send `[T]_k` to `[D ×_X T]_{k-1}`: the Gysin
  homomorphism by Stacks 02TB on a fundamental class, and `c(D ⟶ X, 𝒩)` by Stacks 0FBM at
  vanishing excess.
* If `T` lies in `D`, then `D ×_X T ⟶ T` is an isomorphism, its conormal sheaf vanishes and the
  excess normal sheaf is `𝒩|_T ≅ ℒ|_T`. Both classes send `[T]_k` to `c_1(ℒ|_T) ∩ [T]_k`: the
  Gysin homomorphism because its pushforward to `T` is `c_1(ℒ|_T) ∩ -` (Stacks 02T9), and
  `c(D ⟶ X, 𝒩)` by Stacks 0FBM at full excess, the top Chern class of a module of rank one being
  its first Chern class and commuting with pushforward along the isomorphism.

The argument uses the module of `𝒩` only through an isomorphism `𝒩 ≅ i^*ℒ` and never the
surjection `𝒩^∨ ⟶ 𝒞_{D/X}`, so it is stated for every such virtual normal sheaf
(`Stacks.Chow.gysinBivariantClass_eq_virtualNormalBundleClass_of_iso`) and specialized to the
canonical one.

## Main results

* `Stacks.Chow.isPullback_gysinTripleDivisor` — the zero scheme of the pulled-back section is a
  fibre product `D ×_X T`.
* `Stacks.Chow.gysinBivariantCap_fundamentalChowClass_of_ne_zero`,
  `Stacks.Chow.virtualNormalBundleClass_cap_fundamentalChowClass_of_ne_zero` — the case of a test
  scheme not contained in `D`.
* `Stacks.Chow.excessNormalSheafIsoOfIsIso`,
  `Stacks.Chow.gysinBivariantCap_eq_virtualNormalBundleClass_cap_of_eq_zero` — the case of a test
  scheme contained in `D`.
* `Stacks.Chow.gysinBivariantClass_eq_virtualNormalBundleClass_of_iso` — the identity for every
  virtual normal sheaf whose module is `i^*ℒ`.
* `Stacks.Chow.gysinBivariantClass_eq_virtualNormalBundleClass` — **Stacks 0FBN**.

## References

* [Stacks Project, Tag 0FBN](https://stacks.math.columbia.edu/tag/0FBN)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-! ### Stacks 0FBN -/

section Divisor

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **The base change of the divisor along a test scheme, as a cartesian square.** For a test
scheme `g : T ⟶ X` the zero scheme `Z(g^*s) ⊆ T` of the pulled-back section, mapped to `D` through
the identification `Z(g^*s) ≅ D ×_X T` of Stacks 0B6Y, is a fibre product of `i : D ⟶ X` and
`g`. -/
theorem isPullback_gysinTripleDivisor {T : Scheme.{u}} (g : T ⟶ X) :
    IsPullback (gysinTripleDivisor L s g).subschemeι
      ((gysinDivisorBaseChangeIso L s g).hom ≫ pullback.fst (gysinTripleInclusion L s) g) g
      (gysinTripleInclusion L s) :=
  (IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, pullback.condition, gysinDivisorBaseChangeIso_hom_snd_assoc]⟩
    (gysinDivisorBaseChangeIso L s g) rfl (gysinDivisorBaseChangeIso_hom_snd L s g)).flip

/-- The comparison isomorphism `Z(g^*s) ≅ D ×_X T` of the cartesian square
`Stacks.Chow.isPullback_gysinTripleDivisor` is the identification of Stacks 0B6Y. -/
theorem isPullback_gysinTripleDivisor_isoPullback_hom {T : Scheme.{u}} (g : T ⟶ X) :
    (isPullback_gysinTripleDivisor L s g).flip.isoPullback.hom =
      (gysinDivisorBaseChangeIso L s g).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [IsPullback.isoPullback_hom_fst]
  · rw [IsPullback.isoPullback_hom_snd, gysinDivisorBaseChangeIso_hom_snd]

/-- The Gysin system of invertible modules acts on a triple as `gysinChowOfInvertible`. -/
private theorem onChow_gysinSystemOfInvertible_gysinTriple {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (n : ℤ) :
    (gysinSystemOfInvertible C).onChow (g ≫ sX) (gysinTripleModule L g)
        (gysinTripleSection L s g) n =
      gysinChowOfInvertible C (g ≫ sX) n (gysinTripleModule L g) (gysinTripleSection L s g) :=
  rfl

/-- **The Gysin homomorphism on the fundamental class of a test scheme on which the section does
not vanish identically.** For an integral `T` with `dim_δ(T) ≤ k` and `g^*s ≠ 0`, the zero scheme
`Z(g^*s)` is an effective Cartier divisor on `T` and `i^*[T]_k = [D ×_X T]_{k-1}`: this is the
source's "the same is true by definition for the Gysin homomorphism", Stacks 02TB on a fundamental
class, read on `D ×_X T` through Stacks 0B6Y. -/
theorem gysinBivariantCap_fundamentalChowClass_of_ne_zero {T : Scheme.{u}} [IsIntegral T]
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (hT : schemeDeltaDimension C (g ≫ sX) ≤ (k : EInt)) (hs : gysinTripleSection L s g ≠ 0) :
    gysinBivariantCap C (gysinSystemOfInvertible C) sX L s g k
        (fundamentalChowClass C (g ≫ sX) k) =
      fundamentalChowClass C
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) (k - 1) := by
  have hD := AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero
    (gysinTripleModule L g) (gysinTripleSection L s g) hs
  rw [gysinBivariantCap_apply, chowGroupDegreeEquiv_fundamentalChowClass,
    onChow_gysinSystemOfInvertible_gysinTriple C sX L s g (k - 1),
    gysinChowOfInvertible_fundamentalChowClass C (g ≫ sX) (k - 1) _ _
      (by rwa [sub_add_cancel]) hD,
    chowPushforwardOfIso_fundamentalChowClass]

variable (𝒩 : VirtualNormalBundle (gysinTripleInclusion L s))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle 1]

/-- **The virtual normal class on the fundamental class of a test scheme on which the section
does not vanish identically.** For an integral `T` with `dim_δ(T) ≤ k` and `g^*s ≠ 0`, the base
change `Z(g^*s) ⟶ T` is an effective Cartier divisor, hence a regular closed immersion of
codimension one, and Stacks 0FBM at vanishing excess gives
`c(D ⟶ X, 𝒩) ∩ [T]_k = [D ×_X T]_{k-1}` for every virtual normal sheaf `𝒩` of rank one. -/
theorem virtualNormalBundleClass_cap_fundamentalChowClass_of_ne_zero {T : Scheme.{u}}
    [IsIntegral T] (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (hT : schemeDeltaDimension C (g ≫ sX) ≤ (k : EInt)) (hs : gysinTripleSection L s g ≠ 0) :
    (virtualNormalBundleClass C (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s) rfl
        𝒩 1).cap g k (fundamentalChowClass C (g ≫ sX) k) =
      fundamentalChowClass C
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX))
        (k - ((1 : ℕ) : ℤ)) := by
  have hD := AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero
    (gysinTripleModule L g) (gysinTripleSection L s g) hs
  have hcodim := isRegularClosedImmersionOfCodim_one_of_isEffectiveCartierDivisor
    (gysinTripleDivisor L s g).subschemeι
    (by rwa [Scheme.IdealSheafData.ker_subschemeι])
  have := hcodim.isFiniteLocallyFreeOfRank_conormalModule
  exact virtualNormalBundleClass_cap_fundamentalChowClass C (gysinTripleInclusion L s ≫ sX) sX
    (gysinTripleInclusion L s) rfl 𝒩 1
    (isVirtualNormalBundleClass_virtualNormalBundleClass C _ sX _ rfl 𝒩 1) g
    (gysinTripleDivisor L s g).subschemeι _ (isPullback_gysinTripleDivisor L s g) _ rfl
    hcodim.isRegularImmersion k hT

/-- **The excess normal sheaf on a test scheme contained in the divisor.** If the closed immersion
`Z(g^*s) ⟶ T` is an isomorphism, its conormal sheaf vanishes, so the surjection of the base change
of `𝒩` along the square `Stacks.Chow.isPullback_gysinTripleDivisor` has kernel all of its source
and the excess normal sheaf is `𝒩|_{Z(g^*s)}` itself; through `e𝒩 : 𝒩 ≅ i^*L` it is the
restriction of `g^*L` to `Z(g^*s)`. -/
def excessNormalSheafIsoOfIsIso
    (e𝒩 : 𝒩.bundle ≅ (Scheme.Modules.pullback (gysinTripleInclusion L s)).obj L)
    {T : Scheme.{u}} (g : T ⟶ X) [IsIso (gysinTripleDivisor L s g).subschemeι]
    [IsLocallyNoetherian (gysinTripleDivisor L s g).subscheme] :
    (𝒩.baseChange (gysinTripleInclusion L s) (gysinTripleDivisor L s g).subschemeι _ g
        (isPullback_gysinTripleDivisor L s g)).excessNormalSheaf ≅
      (Scheme.Modules.pullback (gysinTripleDivisor L s g).subschemeι).obj
        (gysinTripleModule L g) :=
  let 𝒩' := 𝒩.baseChange (gysinTripleInclusion L s) (gysinTripleDivisor L s g).subschemeι _ g
    (isPullback_gysinTripleDivisor L s g)
  haveI : IsIso (kernel.ι 𝒩'.conormalSurjection) :=
    kernel.ι_of_zero ((Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso
      (gysinTripleDivisor L s g).subschemeι).eq_of_tgt _ _)
  haveI := toDoubleDual_isIso_of_isFiniteLocallyFree 𝒩'.bundle 𝒩'.isFiniteLocallyFree
  (dualMapIso (asIso (kernel.ι 𝒩'.conormalSurjection))).symm ≪≫
    (asIso (toDoubleDual 𝒩'.bundle)).symm ≪≫
    (Scheme.Modules.pullback ((gysinDivisorBaseChangeIso L s g).hom ≫
      pullback.fst (gysinTripleInclusion L s) g)).mapIso e𝒩 ≪≫
    (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr (isPullback_gysinTripleDivisor L s g).w.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp _ g).app L).symm

/-- **The two classes on the fundamental class of a test scheme contained in the divisor.** If
`g^*s = 0` then `Z(g^*s) = T`, and both `i^*` and `c(D ⟶ X, 𝒩)` send `[T]_k` to
`c_1(g^*L) ∩ [T]_k`, read on `D ×_X T`: the Gysin homomorphism by Definition 02T8 (its pushforward
to `T` is `c_1(g^*L) ∩ -`, Stacks 02T9), and `c(D ⟶ X, 𝒩)` by Stacks 0FBM at full excess, the
excess normal sheaf being `𝒩|_T ≅ g^*L` (`Stacks.Chow.excessNormalSheafIsoOfIsIso`) and the top
Chern class of a module of rank one its first Chern class (Stacks 02U6 against 02SO). -/
theorem gysinBivariantCap_eq_virtualNormalBundleClass_cap_of_eq_zero
    (e𝒩 : 𝒩.bundle ≅ (Scheme.Modules.pullback (gysinTripleInclusion L s)).obj L)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (hT : schemeDeltaDimension C (g ≫ sX) ≤ (k : EInt)) (hs : gysinTripleSection L s g = 0) :
    gysinBivariantCap C (gysinSystemOfInvertible C) sX L s g k
        (fundamentalChowClass C (g ≫ sX) k) =
      (virtualNormalBundleClass C (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s)
        rfl 𝒩 1).cap g k (fundamentalChowClass C (g ≫ sX) k) := by
  set D := gysinTripleDivisor L s g with hDdef
  set ι := D.subschemeι with hιdef
  set M := gysinTripleModule L g with hMdef
  have hDbot : D = ⊥ := by
    rw [hDdef, gysinTripleDivisor, hs]
    exact Stacks.Divisors.zeroScheme_zero_eq_bot M
  have : IsIso ι := (Scheme.isIso_subschemeι_iff_eq_bot D).2 hDbot
  have : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ g ≫ sX)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1 :=
    GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible M
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (conormalModule ι) 0 :=
    isFiniteLocallyFreeOfRank_zero_of_isZero
      (hM := Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso ι)
  have hreg : IsRegularImmersion ι :=
    Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth ι (𝟙 T)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle (0 + 1) :=
    ‹AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle 1›
  -- Stacks 0FBM at full excess
  have hexc := virtualNormalBundleClass_cap_fundamentalChowClass_excess C
    (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s) rfl 𝒩 0 1
    (c := virtualNormalBundleClass C (gysinTripleInclusion L s ≫ sX) sX
      (gysinTripleInclusion L s) rfl 𝒩 1)
    (isVirtualNormalBundleClass_virtualNormalBundleClass C _ sX _ rfl 𝒩 1) g ι _
    (isPullback_gysinTripleDivisor L s g) _ rfl hreg k hT
  set 𝒩' := 𝒩.baseChange (gysinTripleInclusion L s) ι
    ((gysinDivisorBaseChangeIso L s g).hom ≫ pullback.fst (gysinTripleInclusion L s) g) g
    (isPullback_gysinTripleDivisor L s g) with h𝒩'
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle (0 + 1) :=
    isFiniteLocallyFreeOfRank_modulePullback _ 𝒩.bundle (0 + 1) inferInstance
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      𝒩'.excessNormalSheaf 1 :=
    𝒩'.isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add 0 1
  rw [hexc, gysinBivariantCap_apply, chowPushforwardOfIso_congr_apply C _ _ _
    (gysinDivisorBaseChangeIso L s g).hom (isPullback_gysinTripleDivisor_isoPullback_hom L s g) _
    (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C sX g)]
  refine eq_of_heq (chowPushforwardOfIso_heq_congr C _ _ _ _ (by push_cast; ring) _ _ ?_)
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
  -- pushforward along the isomorphism `ι : Z(g^*s) ⟶ T` is injective
  have hinj : ∀ (d d' : ℤ) (hd : d = d') (x : chowGroup C (ι ≫ g ≫ sX) d)
      (z : chowGroup C (ι ≫ g ≫ sX) d'),
      properChowPushforward C (ι ≫ g ≫ sX) (g ≫ sX) ι rfl d
          (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) x ≍
        properChowPushforward C (ι ≫ g ≫ sX) (g ≫ sX) ι rfl d'
          (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) z → x ≍ z := by
    intro d d' hd
    subst hd
    intro x z h
    exact heq_of_eq (chowPushforwardOfIso_injective C _ _ ι rfl d (eq_of_heq h))
  refine hinj _ _ (by rw [Fin.val_last]; push_cast; ring) _ _ ?_
  -- the Gysin side: `ι_* i'^* [T]_k = c_1(g^*L) ∩ [T]_k` (Stacks 02T9)
  rw [onChow_gysinSystemOfInvertible_gysinTriple C sX L s g (k - 1),
    GenuineChern.properChowPushforward_gysinChowOfInvertible C (g ≫ sX) (k - 1) M]
  -- the virtual normal side: Stacks 02U6 commutes with `ι_*`, and in rank one it is `c_1`
  rw [← GenuineChern.chernCap_properPushforward C (ι ≫ g ≫ sX) (g ≫ sX) ι rfl M 1
      𝒩'.excessNormalSheaf (excessNormalSheafIsoOfIsIso L s 𝒩 e𝒩 g) (k - ((0 : ℕ) : ℤ))
      (Fin.last 1) (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _),
    properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_fundamentalChowClass,
    show (Fin.last 1 : Fin (1 + 1)) = 1 from rfl, GenuineChern.chernCap_one_eq_invCap]
  exact GenuineChern.firstChernClassCapChow_heq (g ≫ sX) M (by push_cast; ring)
    ((chowGroupDegreeEquiv_heq C _ _ _).trans
      ((fundamentalChowClass_heq C _ (by push_cast; ring)).trans
        (chowGroupCast_heq C _ _ _).symm))

/-- **Stacks 0FBN, for every virtual normal sheaf with module `i^*ℒ`.** Let `(ℒ, s, i : D ⟶ X)`
be a triple as in Definition 02T8 and let `𝒩` be a virtual normal sheaf for `D` in `X` whose
module is identified with `i^*ℒ` by `e𝒩`, with an arbitrary surjection `𝒩^∨ ⟶ 𝒞_{D/X}`. Then the
Gysin class `i^* ∈ A^1(D ⟶ X)` of Stacks 0B79 is the class `c(D ⟶ X, 𝒩)` of Stacks 0FBK.

The proof is the source's. By Stacks 02UC
(`Stacks.Chow.BivariantClass.eq_of_cap_fundamentalChowClass_eq`) it suffices to compare the two
classes on `[T]_k` for every integral `T ⟶ X`, and `[T]_k = 0`
unless `k = dim_δ(T)`. If `T` does not lie in `D` both send `[T]_k` to `[D ×_X T]_{k-1}`
(`Stacks.Chow.gysinBivariantCap_fundamentalChowClass_of_ne_zero`,
`Stacks.Chow.virtualNormalBundleClass_cap_fundamentalChowClass_of_ne_zero`); if it does, both send
it to `c_1(ℒ|_T) ∩ [T]_k`
(`Stacks.Chow.gysinBivariantCap_eq_virtualNormalBundleClass_cap_of_eq_zero`). -/
theorem gysinBivariantClass_eq_virtualNormalBundleClass_of_iso
    (e𝒩 : 𝒩.bundle ≅ (Scheme.Modules.pullback (gysinTripleInclusion L s)).obj L) :
    (gysinBivariantClass C sX L s).1 =
      virtualNormalBundleClass C (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s)
        rfl 𝒩 1 := by
  refine BivariantClass.eq_of_cap_fundamentalChowClass_eq C _ _ sX _ rfl _ ?_
  intro T g _ _ k
  rw [(gysinBivariantClass C sX L s).2 g k]
  by_cases hk : relativeDimension C.dimensionFunction (g ≫ sX) (genericPoint T) = k
  · have hT : schemeDeltaDimension C (g ≫ sX) ≤ (k : EInt) := by
      rw [schemeDeltaDimension_eq_genericPoint, hk]
    by_cases hs : gysinTripleSection L s g = 0
    · exact gysinBivariantCap_eq_virtualNormalBundleClass_cap_of_eq_zero C sX L s 𝒩 e𝒩 g k hT hs
    · rw [gysinBivariantCap_fundamentalChowClass_of_ne_zero C sX L s g k hT hs,
        virtualNormalBundleClass_cap_fundamentalChowClass_of_ne_zero C sX L s 𝒩 g k hT hs]
      rfl
  · rw [fundamentalChowClass_eq_zero_of_ne C (g ≫ sX) hk, map_zero, map_zero]

/-- **Stacks 0FBN.** Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over
`S` and let `(ℒ, s, i : D ⟶ X)` be a triple as in Definition 02T8. The Gysin homomorphism `i^*`,
viewed as an element of `A^1(D ⟶ X)` (Stacks 0B79, `Stacks.Chow.gysinBivariantClass`), is the
bivariant class `c(D ⟶ X, 𝒩) ∈ A^1(D ⟶ X)` of Stacks 0FBK (`Stacks.Chow.virtualNormalBundleClass`)
constructed using `𝒩 = i^*ℒ` viewed as a virtual normal sheaf for `D` in `X`
(`Stacks.Chow.zeroSchemeVirtualNormalBundle`, with the canonical surjection
`(i^*ℒ)^∨ ⟶ 𝒞_{D/X}`).

This is `Stacks.Chow.gysinBivariantClass_eq_virtualNormalBundleClass_of_iso`, which holds for any
surjection `(i^*ℒ)^∨ ⟶ 𝒞_{D/X}`, at the canonical one. -/
@[stacks 0FBN]
theorem gysinBivariantClass_eq_virtualNormalBundleClass :
    (gysinBivariantClass C sX L s).1 =
      virtualNormalBundleClass C (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s)
        rfl (zeroSchemeVirtualNormalBundle L s) 1 :=
  gysinBivariantClass_eq_virtualNormalBundleClass_of_iso C sX L s _ (Iso.refl _)

end Divisor

end Stacks.Chow

end
