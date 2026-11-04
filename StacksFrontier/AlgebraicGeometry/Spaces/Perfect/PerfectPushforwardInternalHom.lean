module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectInternalHomClauses
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DKK: the direct image of `RSheafHom(E, 𝒢)` for `E` perfect and `𝒢` flat with proper
support

Let `Y` be a Noetherian algebraic space and `f : X ⟶ Y` a morphism of algebraic spaces which is
locally of finite type and quasi-separated.  Let `E` be a perfect object of `D(𝒪_X)` and `𝒢^•` a
bounded complex of coherent `𝒪_X`-modules, flat over `Y`, with support proper over `Y`.  Then
`Rf_* RSheafHom(E, 𝒢^•)` is a perfect object of `D(𝒪_Y)` (Stacks 0DKK).

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedSheafHom`: **Stacks 0DKK.**

## The proof

The source writes `RSheafHom(E, 𝒢^•) = E^∨ ⊗^L 𝒢^•` and applies Stacks 0DKJ.  Here Stacks 08IS
(`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_hasProperSupport`) is applied to
`K = RSheafHom(E, 𝒢^•)` directly, exactly as in the proof of Stacks 0DKJ: `K` lies in
`D^b_{Coh}(𝒪_X)`, its cohomology sheaves are supported on the support of `𝒢^•`, and read over
`f⁻¹𝒪_Y` it has finite Tor dimension.  All three are read off the local models
`K|_W ≅ SheafHom^•(P, 𝒢^•|_W)` with `P` strictly perfect, whose terms are retracts of finite sums
of terms of `𝒢^•|_W` — locally on the covering this *is* the identification with `E^∨ ⊗ 𝒢^•`
which the source uses, read on the model `P` of `E`.

## References

* [Stacks Project, Tag 0DKK](https://stacks.math.columbia.edu/tag/0DKK)
* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

open DerivedCategoryB

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat pointTopology isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0DKK.**  Let `Y` be a Noetherian algebraic space and `f : X ⟶ Y` a morphism locally
of finite type and quasi-separated.  Let `E` be a perfect object of `D(𝒪_X)` and `𝒢^•` a bounded
complex of coherent `𝒪_X`-modules, flat over `Y`, with support proper over `Y`.  Then
`Rf_* RSheafHom(E, 𝒢^•)` is a perfect object of `D(𝒪_Y)`. -/
@[stacks 0DKK]
theorem isPerfect_derivedModulePushforward_derivedSheafHom (hTop : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        (((RingedSite.derivedSheafHomSmallBifunctor (smallEtaleRingedSite B S hS X.1 X.2)).obj
          (op E)).obj (DerivedCategory.Q.obj G))) := by
  obtain ⟨g₀, g₁, hGb⟩ := hG.bounded
  obtain ⟨Z, hZcl, hZp, hGZ⟩ := hG.properSupport
  have hZc : IsCompact Z := isCompact_of_isProperOver B S hS X.2 Y.2 hY.1 f.hom hf Z hZcl hZp
  let K := derivedSheafHomObj B S hS X E G
  have hcoh : ∀ i : ℤ, IsCoherent B S hS X.1 X.2
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj K) :=
    fun i => isCoherent_homology_derivedSheafHom_of_isPerfect B S hS X E hE G hG.isCoherent i
  obtain ⟨a, b, hab⟩ := exists_isZero_homology_derivedSheafHom_of_isPerfect B S hS X E hE G g₀ g₁
    hGb Z hZc hZcl hGZ
  have hKb : derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2) K :=
    ⟨⟨⟨a, fun n hn => hab n (Or.inl hn)⟩, ⟨b, fun n hn => hab n (Or.inr hn)⟩⟩, hcoh⟩
  have hsupp : ∀ i : ℤ, HasProperSupport B S hS X.2 Y.2 f.hom hf
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj K)) :=
    hasProperSupport_homology_of_cohomologySupportedOn_of_isCoherent B S hS X.2 Y.2 f.hom hf
      hZcl hZp K (cohomologySupportedOn_derivedSheafHom B S hS X E hE G Z hZc hZcl hGZ) hcoh
  obtain ⟨T'⟩ := Stacks.SheafOfModules.exists_derivedTensorProduct.{u + 1, u, u + 1}
    (inverseImageRingedSite B S hS f)
  have hGflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f).O) ((scalarRestriction B S hS f).obj (G.X q)) :=
    fun q =>
      have := (hG.isCoherent q).toIsQuasicoherentOnSite
      isFlat_scalarRestriction_of_isFlatOver B S hS f (G.X q) (hG.isFlatOver q)
  exact isPerfect_derivedModulePushforward_of_hasProperSupport B S hS hTop f hf hfqs hY K hKb hsupp
    T' (hasFiniteTorDimension_derivedScalarRestriction_derivedSheafHom B S hS X f T' E hE G g₀ g₁
      hGb Z hZc hZcl hGZ hGflat)

end AlgebraicGeometry.Space

end
