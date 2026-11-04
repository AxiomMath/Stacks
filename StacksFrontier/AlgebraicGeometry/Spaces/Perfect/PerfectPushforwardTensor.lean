module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorTorDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ScalarRestrictionFlatOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.DerivedProperSupport
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DKJ: the direct image of `E ⊗^L 𝒢` for `E` perfect and `𝒢` flat with proper support

Let `Y` be a Noetherian algebraic space and `f : X ⟶ Y` a morphism of algebraic spaces which is
locally of finite type and quasi-separated.  Let `E` be a perfect object of `D(𝒪_X)` and `𝒢^•` a
bounded complex of coherent `𝒪_X`-modules, flat over `Y`, with support proper over `Y`.  Then
`Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` is a perfect object of `D(𝒪_Y)` (Stacks 0DKJ).

## Main definitions

* `AlgebraicGeometry.Space.FlatProperSupportComplex`: the hypotheses on `𝒢^•`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedTensor`: **Stacks 0DKJ.**

## The proof

The source's, through Stacks 08IS
(`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_hasProperSupport`): with
`K = E ⊗^L 𝒢^•`,

1. `K` lies in `D^b_{Coh}(𝒪_X)`: its cohomology sheaves are coherent
   (`AlgebraicGeometry.Space.isCoherent_homology_derivedTensor_of_isPerfect`) and only finitely
   many are nonzero (`AlgebraicGeometry.Space.exists_isZero_homology_derivedTensor_of_isPerfect`,
   the support of `𝒢^•` being compact);
2. the cohomology sheaves of `K` have support proper over `Y`: they are supported on the support
   of `𝒢^•` (`AlgebraicGeometry.Space.cohomologySupportedOn_derivedTensor`), which is closed and
   proper over `Y`;
3. `K` has finite Tor dimension as an object of `D(f⁻¹𝒪_Y)`: locally `E` is a finite complex of
   direct summands of finite free modules and the terms of `𝒢^•` are flat over `f⁻¹𝒪_Y`
   (`AlgebraicGeometry.Space.hasFiniteTorDimension_derivedScalarRestriction_derivedTensor`,
   `AlgebraicGeometry.Space.isFlat_scalarRestriction_of_isFlatOver`).

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

open DerivedCategoryB

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat pointTopology isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **The hypotheses on `𝒢^•` in Stacks 0DKJ**: a bounded complex of coherent `𝒪_X`-modules, flat
over `Y` (Stacks 05VV), whose support is contained in a closed subset of `|X|` proper over `Y`
(Stacks 0CZD). -/
structure FlatProperSupportComplex (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) : Prop where
  /-- `𝒢^•` is a bounded complex. -/
  bounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero (G.X q)
  /-- Every term of `𝒢^•` is a coherent `𝒪_X`-module. -/
  isCoherent : ∀ q : ℤ, IsCoherent B S hS X.1 X.2 (G.X q)
  /-- Every term of `𝒢^•` is flat over `Y`. -/
  isFlatOver : ∀ q : ℤ, IsFlatOver B S hS X.2 f.hom (G.X q)
  /-- The support of `𝒢^•` is contained in a closed subset of `|X|` proper over `Y`. -/
  properSupport : ∃ (Z : Set (points B S hS X.1)) (hZ : IsClosed Z),
    IsProperOver B S hS X.2 Y.2 f.hom hf Z hZ ∧
      ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z

/-- **Stacks 0DKJ.**  Let `Y` be a Noetherian algebraic space and `f : X ⟶ Y` a morphism locally
of finite type and quasi-separated.  Let `E` be a perfect object of `D(𝒪_X)` and `𝒢^•` a bounded
complex of coherent `𝒪_X`-modules, flat over `Y`, with support proper over `Y`.  Then
`Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` is a perfect object of `D(𝒪_Y)`, for any derived tensor product
`⊗^L` on `D(𝒪_X)`. -/
@[stacks 0DKJ]
theorem isPerfect_derivedModulePushforward_derivedTensor (hTop : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1)
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) := by
  obtain ⟨g₀, g₁, hGb⟩ := hG.bounded
  obtain ⟨Z, hZcl, hZp, hGZ⟩ := hG.properSupport
  have hZc : IsCompact Z := isCompact_of_isProperOver B S hS X.2 Y.2 hY.1 f.hom hf Z hZcl hZp
  let K := (T.tensor.obj E).obj (DerivedCategory.Q.obj G)
  have hcoh : ∀ i : ℤ, IsCoherent B S hS X.1 X.2
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj K) :=
    fun i => isCoherent_homology_derivedTensor_of_isPerfect B S hS X T E hE G hG.isCoherent i
  obtain ⟨a, b, hab⟩ :=
    exists_isZero_homology_derivedTensor_of_isPerfect B S hS X T E hE G g₀ g₁ hGb Z hZc hZcl hGZ
  have hKb : derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2) K :=
    ⟨⟨⟨a, fun n hn => hab n (Or.inl hn)⟩, ⟨b, fun n hn => hab n (Or.inr hn)⟩⟩, hcoh⟩
  have hsupp : ∀ i : ℤ, HasProperSupport B S hS X.2 Y.2 f.hom hf
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj K)) :=
    hasProperSupport_homology_of_cohomologySupportedOn_of_isCoherent B S hS X.2 Y.2 f.hom hf
      hZcl hZp K (cohomologySupportedOn_derivedTensor B S hS X T E G Z hGZ) hcoh
  obtain ⟨T'⟩ := Stacks.SheafOfModules.exists_derivedTensorProduct.{u + 1, u, u + 1}
    (inverseImageRingedSite B S hS f)
  have hGflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f).O) ((scalarRestriction B S hS f).obj (G.X q)) :=
    fun q =>
      have := (hG.isCoherent q).toIsQuasicoherentOnSite
      isFlat_scalarRestriction_of_isFlatOver B S hS f (G.X q) (hG.isFlatOver q)
  exact isPerfect_derivedModulePushforward_of_hasProperSupport B S hS hTop f hf hfqs hY K hKb hsupp
    T' (hasFiniteTorDimension_derivedScalarRestriction_derivedTensor B S hS f T T' E hE G g₀ g₁
      hGb Z hZc hZcl hGZ hGflat)

end AlgebraicGeometry.Space

end
