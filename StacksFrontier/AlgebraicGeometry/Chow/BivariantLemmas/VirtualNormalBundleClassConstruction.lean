module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Division
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityClass
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalConeIso
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClassOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackNaturalityInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward

/-!
# The bivariant class of a virtual normal bundle, constructed

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed immersion and let `𝒩` be a virtual normal
bundle for `i` in the sense of Stacks 0FBQ. Write `p : N ⟶ Z` for the vector bundle
`N = Spec_Z(Sym(𝒩^∨))`, let `b : W ⟶ 𝐏¹_X` be the blowup of Stacks 0FBG in `∞(Z)` with
`C ∈ A⁰(W_∞ ⟶ X)` the class of Stacks 0F9J, let `j : C_ZX ⟶ W_∞` be the open immersion of
Stacks 0FBH and let `ι : C_ZX ⟶ N` be the closed immersion of Stacks 0637. The construction
preceding Stacks 0FBK sends `α ∈ A_k(X)` to the unique `β` with

  `ι_* j^* (C ∩ α) = p^* β`,

the uniqueness and existence being Stacks 02TY, and Stacks 0FBK asserts that `α ↦ β` is a
bivariant class `c(Z ⟶ X, 𝒩)`, of degree `r` when `𝒩` has constant rank `r`.

As an identity between bivariant classes the construction reads

  `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C   in   A⁰(N ⟶ X)`,

and this file builds `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` for `𝒩` of constant rank `r` as the quotient of
`ι_* ∘ j^* ∘ C` by `p^*`, in the sense of `Stacks.Chow.bivariantDivision`: `p^*` is the
flat-pullback class of Stacks 0B78, `j^*` the one of an open immersion, `ι_*` the proper
pushforward of bivariant classes of Stacks 0EPK and the composites those of Stacks 0B75, all at
the Gysin system `Stacks.Chow.gysinSystemOfInvertible`. The division needs every cap operation
of `p^*` to be bijective; on a test scheme `t : T ⟶ Z` that cap operation is flat pullback along
`N ×_Z T ⟶ T`, which is the vector bundle of `t^*(𝒩^∨)`
(`AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackIso`), so this is Stacks 02TY,
`Stacks.Chow.flatPullbackChow_bijective_vectorBundleToBase_factorsGeneral`.

## Main definitions

* `Stacks.Chow.virtualNormalConeClass` — the class `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)`.
* `Stacks.Chow.VirtualNormalBundle.projectionPullbackClass` — the class `p^* ∈ A^{-r}(N ⟶ Z)`.
* `Stacks.Chow.virtualNormalBundleClass` — **Stacks 0FBK**, the class
  `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`.
* `Stacks.Chow.IsVirtualNormalBundleClass` — the relation `p^*(c ∩ α) = ι_* j^*(C ∩ α)` on every
  test scheme, as a predicate on a bivariant class of degree `r` for `i`, with respect to an
  arbitrary Gysin system.

## Main results

* `Stacks.Chow.VirtualNormalBundle.capBijective_projectionPullbackClass` — Stacks 02TY for the
  bivariant class `p^*`.
* `Stacks.Chow.projectionPullbackClass_comp_virtualNormalBundleClass` — **Stacks 0FBK**:
  `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C`.
* `Stacks.Chow.eq_virtualNormalBundleClass_iff` — **Stacks 0FBK**: that relation characterizes
  `c(Z ⟶ X, 𝒩)` among the classes of degree `r`.
* `Stacks.Chow.isVirtualNormalBundleClass_virtualNormalBundleClass`,
  `Stacks.Chow.cap_eq_virtualNormalBundleClass_cap`, `Stacks.Chow.isVirtualNormalBundleClass_iff` —
  the same on cap operations: `c(Z ⟶ X, 𝒩)` satisfies the relation on every test scheme, and any
  class satisfying it, for any Gysin system, caps as `c(Z ⟶ X, 𝒩)` does.
* `Stacks.Chow.flatPullbackChow_bijective_of_isIso_comp`,
  `Stacks.Chow.flatPullbackChow_heq_chowPushforwardOfIso` — flat pullback along a morphism
  isomorphic over the target, and along an isomorphism.

## Implementation notes

`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClass` states the relation
of Stacks 0FBK against a carried projection datum and family `π`; this module constructs the class
outright, for a virtual normal bundle of constant rank, with `π` the genuine flat pullback
`Stacks.Chow.bundleFlatPullbackChow` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection` along the base change
`Stacks.Chow.bundleTestBaseChange` of the bundle projection, its descent along rational equivalence
supplied by `Stacks.Chow.flatPullbackDescends`.

The normal cone `C_ZX` is the relative spectrum over `Z` of the conormal algebra of `i`, and the
blowup is that of `𝐏¹_X` in the centre cut out by `ker i`; the open immersion
`Stacks.Chow.normalConeToFibreAtInfinity` is stated for an arbitrary closed immersion, so no
identification of `Z` with `V(ker i)` enters.

`Stacks.Chow.virtualNormalConeClass` is formed with `C_ZX ⟶ Z` locally of finite type, which is
`Stacks.Chow.locallyOfFiniteType_normalConeToBase`: `C_ZX ⟶ Z ⟶ X` is `j` followed by
`W_∞ ⟶ X`.

The class is constructed for a virtual normal bundle of constant rank, the degree of the class
being that rank.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Flat pullback along an isomorphic morphism -/

section Transfer

variable (C : ChowSituation.{u})

/-- A family of maps between Chow groups of equal degrees which agree, as heterogeneous
equalities, with a bijective map is bijective. -/
theorem bijective_of_heq_chowGroup {A B : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
    {sB : B ⟶ C.S} [LocallyOfFiniteType sB] {k d d' : ℤ} (hd : d = d')
    (f : chowGroup C sA k → chowGroup C sB d) (f' : chowGroup C sA k → chowGroup C sB d')
    (hff' : ∀ α, f α ≍ f' α) (hf : Function.Bijective f) : Function.Bijective f' := by
  subst hd
  exact (funext fun α ↦ eq_of_heq (hff' α) : f = f') ▸ hf

/-- Stacks 02RD for a flat morphism `q = f ≫ g` factored as two flat morphisms:
`f^* (g^* α) ≍ q^* α`. -/
private theorem flatPullbackChow_comp_heq_of_eq (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y} [LocallyOfFiniteType f] [Flat f]
    {g : Y ⟶ Z} [LocallyOfFiniteType g] [Flat g] {q : X ⟶ Z} [LocallyOfFiniteType q] [Flat q]
    (hfg : f ≫ g = q) (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (hq : q ≫ sZ = sX) {r s n : ℕ}
    (hrs : r + s = n) (hfr : AlgebraicGeometry.RelativeDimension f r)
    (hgs : AlgebraicGeometry.RelativeDimension g s) (hqn : AlgebraicGeometry.RelativeDimension q n)
    {k : ℤ} (α : chowGroup C sZ k) :
    flatPullbackChow C sX sY f hf r hfr (k + (s : ℤ)) (flatPullbackDescends C _ _ _ _ _ _ _)
        (flatPullbackChow C sY sZ g hg s hgs k (flatPullbackDescends C _ _ _ _ _ _ _) α) ≍
      flatPullbackChow C sX sZ q hq n hqn k (flatPullbackDescends C _ _ _ _ _ _ _) α :=
  (flatPullbackChow_comp C sX sY sZ f g hf hg r s hfr hgs k _ _
    (flatPullbackDescends C _ _ _ _ _ _ _) α).trans
    (flatPullbackChow_heq_congr C sX sZ _ q _ hq hfg hrs _ hqn rfl _ _ α α HEq.rfl)

/-- **Flat pullback along a morphism isomorphic over the target is bijective as soon as flat
pullback along the other one is.** If `q = e ≫ q'` with `e` an isomorphism, then
`q^* = e^* ∘ q'^*`, by Stacks 02RD, and `e^*` is bijective. -/
theorem flatPullbackChow_bijective_of_isIso_comp {P P' T : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (sP' : P' ⟶ C.S) [LocallyOfFiniteType sP'] (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] (q : P ⟶ T) [LocallyOfFiniteType q] [Flat q] (q' : P' ⟶ T)
    [LocallyOfFiniteType q'] [Flat q'] (e : P ⟶ P') [IsIso e] (he : e ≫ q' = q)
    (hq : q ≫ sT = sP) (hq' : q' ≫ sT = sP') (r : ℕ)
    (hqr : AlgebraicGeometry.RelativeDimension q r)
    (hq'r : AlgebraicGeometry.RelativeDimension q' r) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sP sT q hq r hqr k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sP' sT q' hq' r hq'r k)
    (hbij : Function.Bijective (flatPullbackChow C sP' sT q' hq' r hq'r k hfac')) :
    Function.Bijective (flatPullbackChow C sP sT q hq r hqr k hfac) := by
  have heb : e ≫ sP' = sP := by rw [← hq', ← Category.assoc, he, hq]
  have he0 : AlgebraicGeometry.RelativeDimension e 0 := relativeDimension_of_isOpenImmersion e
  have hE := flatPullbackChow_bijective_of_isIso C sP sP' e heb he0 (k + (r : ℤ))
    (flatPullbackDescends C _ _ _ _ _ _ _)
  refine bijective_of_heq_chowGroup C (by push_cast; ring) _ _ (fun α ↦ ?_) (hE.comp hbij)
  exact flatPullbackChow_comp_heq_of_eq C he heb hq' hq (zero_add r) he0 hq'r hqr α

/-- **Flat pullback along an isomorphism is pushforward along the inverse isomorphism**, as a
heterogeneous equality: the two sides lie in degrees `k + 0` and `k`. -/
theorem flatPullbackChow_heq_chowPushforwardOfIso {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (f : A ⟶ B) [IsIso f]
    (hf : f ≫ sB = sA) (h0 : AlgebraicGeometry.RelativeDimension f 0) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB f hf 0 h0 k)
    (α : chowGroup C sB k) :
    flatPullbackChow C sA sB f hf 0 h0 k hfac α ≍
      chowPushforwardOfIso C sB sA (inv f) (by rw [IsIso.inv_comp_eq, hf]) k α := by
  have : IsOpenImmersion f := IsOpenImmersion.of_isIso f
  rw [← chowGroupRestrict_of_isIso C sB sA k f hf]
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    have degree : ∀ (n : ℤ), n = k → ∀ (x : CycleGroup C sA n) (y : CycleGroup C sA k),
        x.1 = y.1 → QuotientAddGroup.mk' (rationalEquivalences C sA n) x ≍
          QuotientAddGroup.mk' (rationalEquivalences C sA k) y := by
      intro n hn x y h
      cases hn
      exact heq_of_eq (congrArg (QuotientAddGroup.mk' (rationalEquivalences C sA k))
        (Subtype.ext h))
    exact degree (k + ((0 : ℕ) : ℤ)) (by simp) (flatPullback C sA sB f hf 0 h0 k c)
      (cycleGroupRestrict C sB sA f hf k c)
      (cycleGroupRestrict_eq_flatPullback C sB sA f hf h0 k c).symm

end Transfer

/-! ### The base change of the bundle projection -/

section BundleBaseChange

variable {Z X N : Scheme.{u}} (i : Z ⟶ X) (q : N ⟶ Z)

attribute [reassoc] bundleTestBaseChange_fst bundleTestBaseChange_snd

/-- The base change `N ×_X T ⟶ Z ×_X T` is the second projection of `N ×_Z (Z ×_X T)`, read
through the pasting isomorphism `N ×_Z (Z ×_X T) ≅ N ×_X T`. -/
theorem bundleTestBaseChange_eq {T : Scheme.{u}} (g : T ⟶ X) :
    bundleTestBaseChange i q g =
      (pullbackRightPullbackFstIso i g q).inv ≫ pullback.snd q (pullback.fst i g) := by
  refine pullback.hom_ext ?_ ?_
  · rw [bundleTestBaseChange_fst, Category.assoc, ← pullback.condition,
      pullbackRightPullbackFstIso_inv_fst_assoc]
  · rw [bundleTestBaseChange_snd, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]

end BundleBaseChange

section BundlePullback

variable (C : ChowSituation.{u}) {Z X N : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
  (i : Z ⟶ X) (q : N ⟶ Z) [LocallyOfFiniteType q] (hq : q ≫ sZ = sN) (m : ℕ)
  (hflat : AlgebraicGeometry.Flat q) (hrd : AlgebraicGeometry.RelativeDimension q m)

/-- `p^*` on a test scheme is flat pullback along the base change `N ×_Z (Z ×_X T) ⟶ Z ×_X T`,
pushed forward along the pasting isomorphism `N ×_Z (Z ×_X T) ≅ N ×_X T`. -/
theorem bundleFlatPullbackChow_heq {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (pullback.fst i g ≫ sZ) k) :
    haveI := hflat
    bundleFlatPullbackChow C sZ sN i q hq m hflat hrd (flatPullbackDescends C) g k β ≍
      chowPushforwardOfIso C (pullback.fst q (pullback.fst i g) ≫ sN)
        (pullback.fst (q ≫ i) g ≫ sN) (pullbackRightPullbackFstIso i g q).hom
        (by rw [← Category.assoc, pullbackRightPullbackFstIso_hom_fst]) (k + (m : ℤ))
        (flatPullbackChow C (pullback.fst q (pullback.fst i g) ≫ sN) (pullback.fst i g ≫ sZ)
          (pullback.snd q (pullback.fst i g))
          (by rw [← Category.assoc, ← pullback.condition, Category.assoc, hq]) m
          (relativeDimension_pullback_snd q (pullback.fst i g) m hrd) k
          (flatPullbackDescends C _ _ _ _ _ _ _) β) := by
  have := hflat
  have := locallyOfFiniteType_bundleTestBaseChange i q g
  have := flat_bundleTestBaseChange i q hflat g
  let e := pullbackRightPullbackFstIso i g q
  have he0 : AlgebraicGeometry.RelativeDimension e.inv 0 := relativeDimension_of_isOpenImmersion _
  refine (flatPullbackChow_comp_heq_of_eq C (bundleTestBaseChange_eq i q g).symm
    (by rw [← Category.assoc, pullbackRightPullbackFstIso_inv_fst])
    (by rw [← Category.assoc, ← pullback.condition, Category.assoc, hq])
    (by rw [bundleTestBaseChange_fst_assoc, hq]) (zero_add m) he0
    (relativeDimension_pullback_snd q (pullback.fst i g) m hrd)
    (relativeDimension_bundleTestBaseChange i q hrd g) β).symm.trans ?_
  refine (flatPullbackChow_heq_chowPushforwardOfIso C _ _ e.inv _ he0 _ _ _).trans ?_
  exact heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ (IsIso.Iso.inv_inv e) _ _ _ _)

end BundlePullback

section Construction

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ)

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] in
include hi in
/-- The open immersion `j : C_ZX ⟶ W_∞` followed by `W_∞ ⟶ X` is `C_ZX ⟶ Z ⟶ X`. -/
theorem normalConeToFibreAtInfinity_comp_projection_comp :
    normalConeToFibreAtInfinity i sX ≫
        (modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫
          sX) = Stacks.Conormal.normalConeToBase i ≫ sZ := by
  rw [← Category.assoc, normalConeToFibreAtInfinity_comp_projection, Category.assoc, hi]

include sX in
/-- The projection `C_ZX ⟶ Z` of the normal cone of a closed immersion between schemes locally of
finite type over the base is locally of finite type: `C_ZX ⟶ Z ⟶ X` is the open immersion
`j : C_ZX ⟶ W_∞` followed by `W_∞ ⟶ X`, which is locally of finite type. -/
theorem locallyOfFiniteType_normalConeToBase :
    LocallyOfFiniteType (Stacks.Conormal.normalConeToBase i) := by
  have : LocallyOfFiniteType (Stacks.Conormal.normalConeToBase i ≫ i) := by
    rw [← normalConeToFibreAtInfinity_comp_projection i sX]
    infer_instance
  exact locallyOfFiniteType_of_comp (Stacks.Conormal.normalConeToBase i) i

/-- **The class `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)` of the construction preceding Stacks 0FBK.** Here
`C ∈ A⁰(W_∞ ⟶ X)` is the class of Stacks 0F9J for the blowup `b : W ⟶ 𝐏¹_X` in `∞(Z)`,
`j^* ∈ A⁰(C_ZX ⟶ W_∞)` is flat pullback along the open immersion `j : C_ZX ⟶ W_∞` of Stacks 0FBH,
and `ι_*` is proper pushforward of bivariant classes (Stacks 0EPK) along the closed immersion
`ι : C_ZX ⟶ N` into the vector bundle `N = Spec_Z(Sym(𝒩^∨))`. -/
def virtualNormalConeClass (𝒩 : VirtualNormalBundle i) :
    BivariantClass C (gysinSystemOfInvertible C) (𝒩.projection ≫ sZ) sX (𝒩.projection ≫ i)
      (comp_comp_structureMorphism_eq rfl hi) 0 :=
  haveI := locallyOfFiniteType_normalConeToBase C sX i
  bivariantProperPushforwardOfInvertible C (Stacks.Conormal.normalConeToBase i ≫ sZ)
    (𝒩.projection ≫ sZ) sX
    𝒩.normalConeEmbedding (𝒩.projection ≫ i)
    (by rw [𝒩.normalConeEmbedding_projection_assoc]) (comp_comp_structureMorphism_eq rfl hi) 0
    (BivariantClass.copy C (gysinSystemOfInvertible C) _ sX
      (f := normalConeToFibreAtInfinity i sX ≫
        modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX))
      (f' := 𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i)
      (by rw [normalConeToFibreAtInfinity_comp_projection, 𝒩.normalConeEmbedding_projection_assoc])
      _ _ (zero_add 0)
      (bivariantCompositeOfInvertible C (Stacks.Conormal.normalConeToBase i ≫ sZ)
        (modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫
          sX) sX (normalConeToFibreAtInfinity i sX)
        (modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX))
        (normalConeToFibreAtInfinity_comp_projection_comp C sZ sX i hi) rfl (-((0 : ℕ) : ℤ)) 0
        (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C
          (Stacks.Conormal.normalConeToBase i ≫ sZ)
          (modificationProjectionAtInfinity sX
            (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX)
          (normalConeToFibreAtInfinity i sX)
          (normalConeToFibreAtInfinity_comp_projection_comp C sZ sX i hi))
        (gysinAtInfinityClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
          (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX))))

/-- **The flat pullback `p^* ∈ A^{-r}(N ⟶ Z)` along the projection of the vector bundle of a
virtual normal bundle of constant rank `r`**, the bivariant class of Stacks 0B78. -/
def VirtualNormalBundle.projectionPullbackClass (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    BivariantClass C (gysinSystemOfInvertible C) (𝒩.projection ≫ sZ) sZ 𝒩.projection rfl
      (-(r : ℤ)) :=
  haveI := 𝒩.flat_projection_of_rank r
  flatPullbackBivariantClassOfInvertible C (𝒩.projection ≫ sZ) sZ 𝒩.projection rfl r
      (𝒩.relativeDimension_projection_of_rank r)

/-- **Stacks 02TY for the bivariant class `p^*`**: every cap operation of the flat pullback along
the projection of the vector bundle of a virtual normal bundle of constant rank is bijective. On a
test scheme `t : T ⟶ Z` the cap operation is flat pullback along `N ×_Z T ⟶ T`, which is the
vector bundle of `t^*(𝒩^∨)` over `T` (`AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackIso`).
-/
theorem VirtualNormalBundle.capBijective_projectionPullbackClass (𝒩 : VirtualNormalBundle i)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    (𝒩.projectionPullbackClass C sZ i r).CapBijective := by
  intro T t _ k
  have := 𝒩.flat_projection_of_rank r
  let M := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf 𝒩.bundle
  let E := (Scheme.Modules.pullback t).obj M
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback t M r
  have := locallyOfFiniteType_vectorBundleToBase E r
  have := flat_vectorBundleToBase E r
  refine bijective_of_heq_chowGroup C (by ring) _ _
    (fun α ↦ (flatPullbackBivariantCap_heq C (𝒩.projection ≫ sZ) sZ 𝒩.projection rfl r
      (𝒩.relativeDimension_projection_of_rank r) (flatPullbackDescends C) t k α).symm) ?_
  let φ : pullback 𝒩.projection t ≅ Scheme.Modules.vectorBundle T E :=
    Scheme.Modules.vectorBundlePullbackIso t M
  exact flatPullbackChow_bijective_of_isIso_comp C _
    (Scheme.Modules.vectorBundleToBase T E ≫ t ≫ sZ)
    (t ≫ sZ) (pullback.snd 𝒩.projection t) (Scheme.Modules.vectorBundleToBase T E) φ.hom
    (Scheme.Modules.vectorBundlePullbackIso_hom_vectorBundleToBase t M) _ rfl r _
    (relativeDimension_vectorBundleToBase E r) k (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackChow_bijective_vectorBundleToBase_factorsGeneral C (t ≫ sZ) E r k)

/-- **Stacks 0FBK, the class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`** of a virtual normal bundle `𝒩` of
constant rank `r` for a closed immersion `i : Z ⟶ X`: the unique bivariant class with
`p^* ∘ c = ι_* ∘ j^* ∘ C`, the division of `Stacks.Chow.virtualNormalConeClass` by the flat
pullback `p^*` along the bundle projection. -/
@[stacks 0FBK "the bivariant class c(Z → X, 𝒩) ∈ A^r(Z → X) of a virtual normal bundle 𝒩 of \
constant rank r for a closed immersion Z → X"]
def virtualNormalBundleClass (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi (r : ℤ) :=
  bivariantDivision C (𝒩.projection ≫ sZ) sZ sX 𝒩.projection i rfl hi (-(r : ℤ)) r 0 (by ring)
    (𝒩.projectionPullbackClass C sZ i r) (𝒩.capBijective_projectionPullbackClass C sZ i r)
    (virtualNormalConeClass C sZ sX i hi 𝒩)

/-- The class `c(Z ⟶ X, 𝒩)` caps by the cap operation of the division of
`ι_* ∘ j^* ∘ C` by `p^*`. -/
theorem virtualNormalBundleClass_cap (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (virtualNormalBundleClass C sZ sX i hi 𝒩 r).cap t k α =
      bivariantDivisionCap C (gysinSystemOfInvertible C) (𝒩.projection ≫ sZ) sZ sX
        𝒩.projection i rfl hi (-(r : ℤ)) r 0 (by ring) (𝒩.projectionPullbackClass C sZ i r)
        (𝒩.capBijective_projectionPullbackClass C sZ i r)
        (virtualNormalConeClass C sZ sX i hi 𝒩) t k α :=
  rfl

/-- **Stacks 0FBK, the defining relation `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C`**, as an equality
of bivariant classes in `A⁰(N ⟶ X)`: the composite (Stacks 0B75) of the class with the flat
pullback along the bundle projection is the class `ι_* ∘ j^* ∘ C`, read in degree
`-r + r = 0`. -/
@[stacks 0FBK "the construction: p^* ∘ c(Z → X, 𝒩) = i_* ∘ j^* ∘ C in A⁰(N → X), for 𝒩 of \
constant rank r"]
theorem projectionPullbackClass_comp_virtualNormalBundleClass (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    bivariantCompositeOfInvertible C (𝒩.projection ≫ sZ) sZ sX 𝒩.projection i rfl hi (-(r : ℤ))
        r (𝒩.projectionPullbackClass C sZ i r) (virtualNormalBundleClass C sZ sX i hi 𝒩 r) =
      BivariantClass.copy C (gysinSystemOfInvertible C) (𝒩.projection ≫ sZ) sX rfl
        (comp_comp_structureMorphism_eq rfl hi) (comp_comp_structureMorphism_eq rfl hi)
        (by ring : (0 : ℤ) = -(r : ℤ) + r) (virtualNormalConeClass C sZ sX i hi 𝒩) :=
  bivariantCompositeOfInvertible_bivariantDivision C (𝒩.projection ≫ sZ) sZ sX 𝒩.projection i rfl
    hi (-(r : ℤ)) r 0 (by ring) _ (𝒩.capBijective_projectionPullbackClass C sZ i r) _

/-- **Stacks 0FBK, uniqueness**: a bivariant class `c ∈ A^r(Z ⟶ X)` is `c(Z ⟶ X, 𝒩)` exactly
when `p^* ∘ c = ι_* ∘ j^* ∘ C`. -/
@[stacks 0FBK "uniqueness: c(Z → X, 𝒩) is the only class in A^r(Z → X) with \
p^* ∘ c = i_* ∘ j^* ∘ C (Stacks 02TY)"]
theorem eq_virtualNormalBundleClass_iff (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi (r : ℤ)) :
    c = virtualNormalBundleClass C sZ sX i hi 𝒩 r ↔
      bivariantCompositeOfInvertible C (𝒩.projection ≫ sZ) sZ sX 𝒩.projection i rfl hi
          (-(r : ℤ)) r (𝒩.projectionPullbackClass C sZ i r) c =
        BivariantClass.copy C (gysinSystemOfInvertible C) (𝒩.projection ≫ sZ) sX rfl
          (comp_comp_structureMorphism_eq rfl hi) (comp_comp_structureMorphism_eq rfl hi)
          (by ring : (0 : ℤ) = -(r : ℤ) + r) (virtualNormalConeClass C sZ sX i hi 𝒩) :=
  eq_bivariantDivision_iff C (𝒩.projection ≫ sZ) sZ sX 𝒩.projection i rfl hi (-(r : ℤ)) r 0
    (by ring) _ (𝒩.capBijective_projectionPullbackClass C sZ i r) _ c

/-- **Stacks 0FBK, on a test scheme: `p^*(c ∩ α) = ι_* j^*(C ∩ α)`.** For a test scheme
`t : T ⟶ X` and `α ∈ A_k(T)`, flat pullback along `N ×_X T ⟶ Z ×_X T` of `c(Z ⟶ X, 𝒩) ∩ α` is
`(ι_* ∘ j^* ∘ C) ∩ α`; the two sides lie in degrees `(k - r) + r` and `k - 0`. -/
theorem bundleFlatPullbackChow_virtualNormalBundleClass_cap (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    bundleFlatPullbackChow C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl r
        (𝒩.flat_projection_of_rank r) (𝒩.relativeDimension_projection_of_rank r)
        (flatPullbackDescends C) t (k - (r : ℤ))
        ((virtualNormalBundleClass C sZ sX i hi 𝒩 r).cap t k α) ≍
      (virtualNormalConeClass C sZ sX i hi 𝒩).cap t k α := by
  have := 𝒩.flat_projection_of_rank r
  have hdiv := bivariantCompositeOuterCap_bivariantDivisionCap C (gysinSystemOfInvertible C)
    (𝒩.projection ≫ sZ) sZ sX 𝒩.projection i rfl hi (-(r : ℤ)) r 0 (by ring)
    (𝒩.projectionPullbackClass C sZ i r) (𝒩.capBijective_projectionPullbackClass C sZ i r)
    (virtualNormalConeClass C sZ sX i hi 𝒩) t k α
  rw [bivariantCompositeOuterCap_apply] at hdiv
  refine (bundleFlatPullbackChow_heq C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl r
    (𝒩.flat_projection_of_rank r) (𝒩.relativeDimension_projection_of_rank r) t
    (k - (r : ℤ)) _).trans ?_
  refine HEq.trans ?_ ((heq_of_eq hdiv).trans (chowGroupDegreeEquiv_heq C _ _ _))
  exact properChowPushforward_heq_congr C _ _ _ _ (by ring) _ _ _ _
    (flatPullbackBivariantCap_heq C (𝒩.projection ≫ sZ) sZ 𝒩.projection rfl r
      (𝒩.relativeDimension_projection_of_rank r) (flatPullbackDescends C) (pullback.fst i t)
      (k - (r : ℤ)) _).symm

/-- **Stacks 02TY on a test scheme**: flat pullback along the base change `N ×_X T ⟶ Z ×_X T` of
the bundle projection is bijective. -/
theorem bijective_bundleFlatPullbackChow (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (m : ℤ) :
    Function.Bijective (bundleFlatPullbackChow C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl r
      (𝒩.flat_projection_of_rank r) (𝒩.relativeDimension_projection_of_rank r)
      (flatPullbackDescends C) t m) := by
  have := 𝒩.flat_projection_of_rank r
  have hsnd : Function.Bijective (flatPullbackChow C (pullback.fst 𝒩.projection
      (pullback.fst i t) ≫ 𝒩.projection ≫ sZ) (pullback.fst i t ≫ sZ)
      (pullback.snd 𝒩.projection (pullback.fst i t))
      (by rw [← Category.assoc, ← pullback.condition, Category.assoc]) r
      (relativeDimension_pullback_snd 𝒩.projection (pullback.fst i t) r
        (𝒩.relativeDimension_projection_of_rank r)) m (flatPullbackDescends C _ _ _ _ _ _ _)) :=
    bijective_of_heq_chowGroup C (by ring) _ _
      (fun α ↦ flatPullbackBivariantCap_heq C (𝒩.projection ≫ sZ) sZ 𝒩.projection rfl r
        (𝒩.relativeDimension_projection_of_rank r) (flatPullbackDescends C) (pullback.fst i t) m
        α) (𝒩.capBijective_projectionPullbackClass C sZ i r (pullback.fst i t) m)
  refine bijective_of_heq_chowGroup C rfl _ _ (fun β ↦ (bundleFlatPullbackChow_heq C sZ
    (𝒩.projection ≫ sZ) i 𝒩.projection rfl r (𝒩.flat_projection_of_rank r)
    (𝒩.relativeDimension_projection_of_rank r) t m β).symm) ?_
  exact (chowGroupEquivOfIso C _ _ _ _ _).bijective.comp hsnd

/-- **The relation `p^* ∘ c = ι_* ∘ j^* ∘ C` of Stacks 0FBK, on cap operations.** A bivariant
class `c` of degree `r` for `i : Z ⟶ X` satisfies it when, on every test scheme `g : T ⟶ X` and
for every `α ∈ A_k(T)`, flat pullback along `N ×_X T ⟶ Z ×_X T` of `c ∩ α` is
`(ι_* ∘ j^* ∘ C) ∩ α`. The relation compares cap operations only, so it makes sense for a class
with respect to any Gysin system. -/
def IsVirtualNormalBundleClass (G : GysinSystem C) (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    (c : BivariantClass C G sZ sX i hi (r : ℤ)) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k),
    bundleFlatPullback C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl r (𝒩.flat_projection_of_rank r)
        (𝒩.relativeDimension_projection_of_rank r) (flatPullbackDescends C) g k (c.cap g k α) =
      (virtualNormalConeClass C sZ sX i hi 𝒩).cap g k α

/-- **Stacks 0FBK.** The class `c(Z ⟶ X, 𝒩)` satisfies the relation `p^* ∘ c = ι_* ∘ j^* ∘ C` on
cap operations. -/
theorem isVirtualNormalBundleClass_virtualNormalBundleClass (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    IsVirtualNormalBundleClass C sZ sX i hi (gysinSystemOfInvertible C) 𝒩 r
      (virtualNormalBundleClass C sZ sX i hi 𝒩 r) := by
  intro T g _ k α
  rw [bundleFlatPullback_apply]
  exact eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans
    (bundleFlatPullbackChow_virtualNormalBundleClass_cap C sZ sX i hi 𝒩 r g k α))

/-- **Stacks 0FBK, the relation determines the cap operations.** A bivariant class of degree `r`
for `i : Z ⟶ X`, with respect to any Gysin system, which satisfies `p^* ∘ c = ι_* ∘ j^* ∘ C` on
cap operations caps as `c(Z ⟶ X, 𝒩)` does. -/
theorem cap_eq_virtualNormalBundleClass_cap {G : GysinSystem C} (𝒩 : VirtualNormalBundle i)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    {c : BivariantClass C G sZ sX i hi (r : ℤ)}
    (hc : IsVirtualNormalBundleClass C sZ sX i hi G 𝒩 r c)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    c.cap g k α = (virtualNormalBundleClass C sZ sX i hi 𝒩 r).cap g k α := by
  have h := (hc g k α).trans (isVirtualNormalBundleClass_virtualNormalBundleClass C sZ sX i hi
    𝒩 r g k α).symm
  rw [bundleFlatPullback_apply, bundleFlatPullback_apply] at h
  exact (bijective_bundleFlatPullbackChow C sZ i 𝒩 r g (k - (r : ℤ))).1
    ((chowGroupDegreeEquiv C _ _).injective h)

/-- **Stacks 0FBK.** A class `c ∈ A^r(Z ⟶ X)` is `c(Z ⟶ X, 𝒩)` exactly when it satisfies the
relation `p^* ∘ c = ι_* ∘ j^* ∘ C` on cap operations. -/
theorem isVirtualNormalBundleClass_iff (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi (r : ℤ)) :
    IsVirtualNormalBundleClass C sZ sX i hi (gysinSystemOfInvertible C) 𝒩 r c ↔
      c = virtualNormalBundleClass C sZ sX i hi 𝒩 r := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ hc ▸ isVirtualNormalBundleClass_virtualNormalBundleClass C sZ sX
    i hi 𝒩 r⟩
  refine BivariantClass.ext C _ sZ sX i hi (r : ℤ) ?_
  intro T g _ k α
  exact cap_eq_virtualNormalBundleClass_cap C sZ sX i hi 𝒩 r hc g k α

end Construction

end Stacks.Chow

end
