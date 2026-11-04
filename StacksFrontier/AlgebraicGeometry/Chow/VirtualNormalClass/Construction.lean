module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.InfinityClass
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.BundleCapBijective
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardCanonical
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeRank

/-!
# The bivariant class of a virtual normal bundle of constant rank

Let `(S, δ)` be as in chapter 42 of the Stacks Project, let `X` be locally of finite type over
`S`, let `i : Z ⟶ X` be a closed immersion and let `𝒩` be a virtual normal bundle for `i` of
constant rank `r`, with vector bundle `p : N = Spec_Z(Sym(𝒩^∨)) ⟶ Z`. The construction preceding
Stacks 0FBK defines `c(Z ⟶ X, 𝒩) ∩ α` as the unique `β` with

  `ι_* j^*(C ∩ α) = p^* β`,

where `C` is the class at infinity of Stacks 0F9J, `j : C_ZX ⟶ W_∞` the open immersion of
Stacks 0FBH and `ι : C_ZX ⟶ N` the canonical closed immersion. Here:

* `j^* ∘ C` is `Stacks.Deformation.normalConeClass`, the class at infinity computed on the open
  `D = W ∖ X'` of `W` (the deformation space), whose special fibre `Z(t⁻¹)` is `C_ZX`;
* `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)` is its proper pushforward of Stacks 0EPK along the closed immersion
  `Z(t⁻¹) ≅ C_ZX ⟶ N` (`Stacks.Chow.VirtualNormalBundle.pushforwardClass`);
* `p^* ∈ A^{-r}(N ⟶ Z)` is the flat pullback class of Stacks 0B78
  (`Stacks.Chow.VirtualNormalBundle.pullbackClass`), bijective on the Chow groups of every test
  scheme by Stacks 02TY;
* `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` is the quotient of the first by the second
  (`Stacks.Chow.bivariantQuotient`): the source's "since both `i_* ∘ j^* ∘ C` and `p^*` are
  bivariant classes we can use the equation `i_* ∘ j^* ∘ C = p^* ∘ c(Z → X, 𝒩)` to define
  `c(Z → X, 𝒩)` as a bivariant class. This works because `p^*` is always bijective on chow
  groups by Lemma 02TY."

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.pullbackClass` — `p^* ∈ A^{-r}(N ⟶ Z)`.
* `Stacks.Chow.VirtualNormalBundle.pushforwardClass` — `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)`.
* `Stacks.Chow.VirtualNormalBundle.virtualNormalClass` — `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`.

## Main results

* `Stacks.Chow.VirtualNormalBundle.isBivariantClassComposition_virtualNormalClass` —
  `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C`.
* `Stacks.Chow.VirtualNormalBundle.eq_virtualNormalClass` — it is the only class with this
  property.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow.VirtualNormalBundle

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] (𝒩 : VirtualNormalBundle i)

/-- The projection `p : N = 𝐕(𝒩^∨) ⟶ Z` of the vector bundle of the virtual normal bundle. -/
abbrev proj : Scheme.Modules.vectorBundle Z (dualSheaf 𝒩.bundle) ⟶ Z :=
  Scheme.Modules.vectorBundleToBase Z (dualSheaf 𝒩.bundle)

section Rank

variable (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
include r

/-- If the virtual normal bundle `𝒩` is finite locally free of rank `r`, then so is its dual
`𝒩^∨`. -/
theorem isFiniteLocallyFreeOfRank_dual :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf 𝒩.bundle) r :=
  isFiniteLocallyFreeOfRank_dualSheaf 𝒩.bundle r ‹_›

/-- The projection `p : N ⟶ Z` is locally of finite type. -/
theorem locallyOfFiniteType_projection : LocallyOfFiniteType 𝒩.proj :=
  have := 𝒩.isFiniteLocallyFreeOfRank_dual r
  locallyOfFiniteType_vectorBundleToBase _ r

/-- The projection `p : N ⟶ Z` is flat. -/
theorem flat_projection : Flat 𝒩.proj :=
  have := 𝒩.isFiniteLocallyFreeOfRank_dual r
  flat_vectorBundleToBase _ r

/-- The projection `p : N ⟶ Z` has relative dimension `r`. -/
theorem relativeDimension_projection :
    haveI := 𝒩.locallyOfFiniteType_projection r
    AlgebraicGeometry.RelativeDimension 𝒩.proj r :=
  have := 𝒩.isFiniteLocallyFreeOfRank_dual r
  relativeDimension_vectorBundleToBase _ r

end Rank

/-- `Z(t⁻¹) ⟶ N ⟶ Z ⟶ X` is `Z(t⁻¹) ⟶ D ⟶ X`. -/
theorem specialFibreEmbedding_projection_comp :
    𝒩.specialFibreEmbedding ≫ (𝒩.proj ≫ i) =
      (Stacks.Deformation.specialFibre i).subschemeι ≫
        Stacks.Deformation.deformationProjection i :=
  𝒩.specialFibreEmbedding_comp

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)
  (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **The flat pullback class `p^* ∈ A^{-r}(N ⟶ Z)`** of the projection of the vector bundle of a
virtual normal bundle of constant rank `r`, Stacks 0B78. -/
def pullbackClass :
    haveI := 𝒩.locallyOfFiniteType_projection r
    haveI := 𝒩.flat_projection r
    BivariantClass C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ) sZ
      𝒩.proj rfl (-(r : ℤ)) :=
  haveI := 𝒩.locallyOfFiniteType_projection r
  haveI := 𝒩.flat_projection r
  flatPullbackBivariantClassOfInvertible C (𝒩.proj ≫ sZ) sZ 𝒩.proj rfl r
    (𝒩.relativeDimension_projection r)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] in
include hZ in
/-- `Z(t⁻¹) ⟶ N ⟶ Z ⟶ S` is `Z(t⁻¹) ⟶ D ⟶ X ⟶ S`. -/
theorem specialFibreEmbedding_comp_structure :
    𝒩.specialFibreEmbedding ≫ (𝒩.proj ≫ sZ) =
      (Stacks.Deformation.specialFibre i).subschemeι ≫
        (Stacks.Deformation.deformationProjection i ≫ sX) := by
  rw [← hZ, ← Category.assoc 𝒩.proj, ← Category.assoc,
    specialFibreEmbedding_projection_comp, Category.assoc]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] in
include hZ in
/-- `N ⟶ Z ⟶ X ⟶ S` is `N ⟶ Z ⟶ S`. -/
theorem projection_comp_structure : (𝒩.proj ≫ i) ≫ sX = 𝒩.proj ≫ sZ := by
  rw [Category.assoc, hZ]

/-- **The class `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)`** of the construction preceding Stacks 0FBK: the
proper pushforward (Stacks 0EPK) along the closed immersion `ι : Z(t⁻¹) ≅ C_ZX ⟶ N` of the class
at infinity of the deformation to the normal cone. Its degree `0` is written `-r + r`, the sum of
the degrees of `p^*` and of `c(Z ⟶ X, 𝒩)`. -/
def pushforwardClass :
    haveI := 𝒩.locallyOfFiniteType_projection r
    BivariantClass C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ) sX (𝒩.proj ≫ i)
      (𝒩.projection_comp_structure C sX sZ hZ) (-(r : ℤ) + r) :=
  haveI := 𝒩.locallyOfFiniteType_projection r
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  BivariantClass.copy C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ) sX rfl
    (𝒩.projection_comp_structure C sX sZ hZ) (𝒩.projection_comp_structure C sX sZ hZ)
    (by ring : (0 : ℤ) = -(r : ℤ) + r)
    (canonicalBivariantProperPushforward C
      ((Stacks.Deformation.specialFibre i).subschemeι ≫
        (Stacks.Deformation.deformationProjection i ≫ sX))
      (𝒩.proj ≫ sZ) sX 𝒩.specialFibreEmbedding (𝒩.proj ≫ i)
      (𝒩.specialFibreEmbedding_comp_structure C sX sZ hZ) (𝒩.projection_comp_structure C sX sZ hZ)
      0
      (BivariantClass.copy C (canonicalGysinSystem C) _ sX
        (𝒩.specialFibreEmbedding_projection_comp).symm (Category.assoc _ _ _)
        (comp_comp_structureMorphism_eq (𝒩.specialFibreEmbedding_comp_structure C sX sZ hZ)
          (𝒩.projection_comp_structure C sX sZ hZ)) rfl
        (Stacks.Deformation.normalConeClass C sX i)))

/-- Capping with `p^*` is bijective on the Chow groups of every test scheme (Stacks 02TY). -/
theorem middleCap_pullbackClass_bijective {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (m : ℤ) :
    haveI := 𝒩.locallyOfFiniteType_projection r
    haveI := 𝒩.flat_projection r
    Function.Bijective (middleCap C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ)
      sZ 𝒩.proj i rfl (-(r : ℤ)) (𝒩.pullbackClass C sZ r) t m) :=
  have := 𝒩.isFiniteLocallyFreeOfRank_dual r
  middleCap_bijective_vectorBundle C sZ (dualSheaf 𝒩.bundle) r i t m

/-- **Stacks 0FBK, the construction: the class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`** of a virtual normal
bundle of constant rank `r` for a closed immersion: the bivariant class with
`p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C`, that is, `c(Z ⟶ X, 𝒩) ∩ α` is the unique `β` with
`p^* β = ι_* j^*(C ∩ α)`. -/
@[stacks 0FBK "the construction at constant rank r: the class c(Z → X, 𝒩) ∈ A^r(Z → X), the \
quotient of ι_* ∘ j^* ∘ C by p^*, which is bijective on Chow groups (Stacks 02TY)"]
def virtualNormalClass :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX i hZ r :=
  haveI := 𝒩.locallyOfFiniteType_projection r
  haveI := 𝒩.flat_projection r
  bivariantQuotient C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ) sZ sX
    𝒩.proj i rfl hZ (-(r : ℤ)) r (𝒩.pullbackClass C sZ r) (𝒩.pushforwardClass C sX sZ hZ r)
    (fun t _ m => 𝒩.middleCap_pullbackClass_bijective C sZ r t m)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- **The defining property of the cap operation**: `p^*(c(Z ⟶ X, 𝒩) ∩ α) = ι_* j^*(C ∩ α)`,
read on `T ×_X N` through the associativity of fibre products. -/
theorem middleCap_virtualNormalClass_cap {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    haveI := 𝒩.locallyOfFiniteType_projection r
    haveI := 𝒩.flat_projection r
    middleCap C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ) sZ 𝒩.proj i
        rfl (-(r : ℤ)) (𝒩.pullbackClass C sZ r) t (k - r)
        ((𝒩.virtualNormalClass C sX sZ hZ r).cap t k α) =
      chowGroupDegreeEquiv C (pullback.fst (𝒩.proj ≫ i) t ≫ (𝒩.proj ≫ sZ))
        (by ring : k - (-(r : ℤ) + r) = k - r - -(r : ℤ))
        ((𝒩.pushforwardClass C sX sZ hZ r).cap t k α) :=
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩.flat_projection r
  middleCap_quotientCap C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ) sZ sX
    𝒩.proj i rfl hZ (-(r : ℤ)) r (𝒩.pullbackClass C sZ r) (𝒩.pushforwardClass C sX sZ hZ r)
    (fun t _ m => 𝒩.middleCap_pullbackClass_bijective C sZ r t m) t k α

/-- **Stacks 0FBK, the characterizing relation `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C`**, as an
identity of bivariant classes in `A⁰(N ⟶ X)` (Stacks 0FE0). -/
@[stacks 0FBK "the construction at constant rank r: p^* ∘ c(Z → X, 𝒩) = ι_* ∘ j^* ∘ C as an \
identity of bivariant classes in A⁰(N → X)"]
theorem isBivariantClassComposition_virtualNormalClass :
    haveI := 𝒩.locallyOfFiniteType_projection r
    haveI := 𝒩.flat_projection r
    IsBivariantClassComposition C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ)
      sZ sX 𝒩.proj i rfl hZ (properPushforwardDescends C) (-(r : ℤ)) r
      (𝒩.pullbackClass C sZ r) (𝒩.virtualNormalClass C sX sZ hZ r)
      (𝒩.pushforwardClass C sX sZ hZ r) :=
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩.flat_projection r
  isBivariantClassComposition_bivariantQuotient C (gysinSystemOfInvertible C)
    (𝒩.proj ≫ sZ) sZ sX 𝒩.proj i rfl hZ (-(r : ℤ)) r
    (𝒩.pullbackClass C sZ r) (𝒩.pushforwardClass C sX sZ hZ r)
    (fun t _ m => 𝒩.middleCap_pullbackClass_bijective C sZ r t m)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- **Stacks 0FBK, uniqueness**: `c(Z ⟶ X, 𝒩)` is the only class in `A^r(Z ⟶ X)` with
`p^* ∘ c = ι_* ∘ j^* ∘ C`. -/
theorem eq_virtualNormalClass (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hZ r)
    (hc : haveI := 𝒩.locallyOfFiniteType_projection r
      haveI := 𝒩.flat_projection r
      IsBivariantClassComposition C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ)
        sZ sX 𝒩.proj i rfl hZ (properPushforwardDescends C) (-(r : ℤ)) r
        (𝒩.pullbackClass C sZ r) c (𝒩.pushforwardClass C sX sZ hZ r)) :
    c = 𝒩.virtualNormalClass C sX sZ hZ r :=
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩.flat_projection r
  eq_bivariantQuotient_of_isBivariantClassComposition C (gysinSystemOfInvertible C)
    (𝒩.proj ≫ sZ) sZ sX 𝒩.proj i rfl hZ (-(r : ℤ)) r
    (𝒩.pullbackClass C sZ r) (𝒩.pushforwardClass C sX sZ hZ r)
    (fun t _ m => 𝒩.middleCap_pullbackClass_bijective C sZ r t m)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) c hc


end Stacks.Chow.VirtualNormalBundle

end
