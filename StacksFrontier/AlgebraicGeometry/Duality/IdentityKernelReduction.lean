module

public import StacksFrontier.AlgebraicGeometry.Duality.IdentityFourierMukaiKernel
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorNonvanishing
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# The identity Fourier-Mukai kernel: reductions used in the proof of Tag 0G0E

Let `X` be a smooth proper scheme over a field `k` and let `K` be a perfect object of
`D(𝒪_{X ×_k X})`. [Stacks, Tag 0G0E] asserts that if the Fourier-Mukai functor `Φ_K` induces on
`D_perf(𝒪_X)` an endofunctor isomorphic to the identity, then `K ≅ Δ_*𝒪_X`. The source's proof has
four steps: `K` is concentrated in degrees `≥ 0` (step 1) and `≤ 0` (step 2), the resulting
coherent module is `s_*𝒪_X` for a section `s` of `pr₂` (step 3), and `s` is the diagonal
(step 4).

This file collects the statements about `K` that the proofs of those steps in
`Duality/IdentityKernelStepOne.lean`, `Duality/IdentityKernelStepTwo.lean`,
`Duality/IdentityKernelStepThree.lean` and their companions are built from, on top of the
vocabulary (`perfectDerivedObjects`, `diagonalFourierMukaiKernel`, `RepresentsIdentityOnPerfect`)
of `Duality/IdentityFourierMukaiKernel.lean`.

## Main results

* `Stacks.Duality.isNoetherian_pullback_self`: `X ×_k X` is Noetherian for `X` proper over `k`.
* `Stacks.Duality.isCoherent_homology_of_perfectDerivedObjects`: the cohomology sheaves of a
  perfect object of `D(𝒪_{X ×_k X})` are coherent.
* `Stacks.Duality.isZero_homology_of_forall_externalTensorProduct_hom_eq_zero` and
  `Stacks.Duality.isGE_zero_and_isLE_zero_of_forall_externalTensorProduct_hom_eq_zero`: steps 1
  and 2 reduced to the cohomological computation — a degree of a perfect `K` into which no
  external tensor product of finite locally free modules maps nontrivially carries no
  cohomology ([Stacks, Tag 0FZ0]).
* `Stacks.Duality.iso_diagonalFourierMukaiKernel_of_isSection`: the half of step 4 that holds for
  an arbitrary morphism of schemes — a morphism sectioning both projections of `X ×_S X` is the
  diagonal, so `K ≅ Rs_*𝒪_X` reads `K ≅ Δ_*𝒪_X`.

## Implementation notes

The model of the derived categories is selected at high priority, as in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/DiagonalKernel.lean`: the imports can
bring the locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` as a
competing instance of the same priority, and raising the standard model's priority keeps every
statement in the category that `Φ_K` and the diagonal kernel of
`Duality/IdentityFourierMukaiKernel.lean` are stated in.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Duality

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Steps 1 and 2 of the source's proof, reduced to the cohomological computation -/

/-- The product `X ×_k X` of a scheme proper over a field with itself is Noetherian: `X` is
quasi-compact and locally of finite type over `Spec k`, hence Noetherian, and `pr₂` is again
quasi-compact and locally of finite type by base change. -/
theorem isNoetherian_pullback_self {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] :
    IsNoetherian (Limits.pullback f f : Scheme.{u}) :=
  have : IsNoetherian (Spec (CommRingCat.of k)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  isNoetherian_of_locallyOfFiniteType (Limits.pullback.snd f f)

/-- **The cohomology sheaves of a perfect object of `D(𝒪_{X ×_k X})` are coherent**, by
[Stacks, Tag 0FXU] on the Noetherian scheme `X ×_k X`.  This is what lets [Stacks, Tag 0FZ0] be
applied to `H^i(K)` in steps 1 and 2 of the proof of [Stacks, Tag 0G0E]. -/
theorem isCoherent_homology_of_perfectDerivedObjects {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hK : perfectDerivedObjects (Limits.pullback f f) K) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules i).obj K).IsCoherent :=
  have := isNoetherian_pullback_self f
  (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect
    (Limits.pullback f f) K hK).2 i

/-- **A degree of a perfect `K` into which every external tensor product of finite locally free
modules maps by zero carries no cohomology.**  The cohomology sheaf is coherent by
`Stacks.Duality.isCoherent_homology_of_perfectDerivedObjects`, so [Stacks, Tag 0FZ0] would
present it as a quotient of some `ℰ ⊠ 𝒢` were it nonzero, and that presentation is a nonzero
morphism.

This is the second half of steps 1 and 2 of the proof of [Stacks, Tag 0G0E]; the first half,
which this statement takes as the hypothesis `hvan`, is the computation of
`H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢))` through `Φ_K`.  The resolution property of `X` is a hypothesis
because it is one of [Stacks, Tag 0FZ0] and the library does not derive it from smoothness and
properness over a field. -/
theorem isZero_homology_of_forall_externalTensorProduct_hom_eq_zero {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [HasResolutionProperty X]
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hK : perfectDerivedObjects (Limits.pullback f f) K) (i : ℤ)
    (hvan : ∀ E G : X.Modules,
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E →
        SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G →
          ∀ q : externalTensorProduct f f E G ⟶
            (DerivedCategory.homologyFunctor (Limits.pullback f f).Modules i).obj K, q = 0) :
    IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules i).obj K) :=
  have := isCoherent_homology_of_perfectDerivedObjects f K hK i
  isZero_of_forall_externalTensorProduct_hom_eq_zero k f f _ hvan

/-- **Steps 1 and 2 of the proof of [Stacks, Tag 0G0E], reduced to the cohomological
computation.**  A perfect `K` on `X ×_k X` whose cohomology sheaf in every nonzero degree
receives only the zero morphism from every external tensor product of finite locally free
modules is concentrated in degree zero.

The hypothesis `hvan` is what the displayed computation of the source produces: in degree `i`
the group `H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢))` is `H^i(X, ℰ ⊗ 𝒢)`, which vanishes for `i ≠ 0` at
suitable `ℰ` and `𝒢`.  That computation is the one piece of steps 1 and 2 not proved here; see
the implementation notes of this file. -/
theorem isGE_zero_and_isLE_zero_of_forall_externalTensorProduct_hom_eq_zero {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [HasResolutionProperty X]
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hK : perfectDerivedObjects (Limits.pullback f f) K)
    (hvan : ∀ i : ℤ, i ≠ 0 → ∀ E G : X.Modules,
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E →
        SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G →
          ∀ q : externalTensorProduct f f E G ⟶
            (DerivedCategory.homologyFunctor (Limits.pullback f f).Modules i).obj K, q = 0) :
    K.IsGE 0 ∧ K.IsLE 0 :=
  ⟨(DerivedCategory.isGE_iff K 0).2 fun j hj =>
      isZero_homology_of_forall_externalTensorProduct_hom_eq_zero f K hK j (hvan j hj.ne),
    (DerivedCategory.isLE_iff K 0).2 fun j hj =>
      isZero_homology_of_forall_externalTensorProduct_hom_eq_zero f K hK j (hvan j hj.ne')⟩

/-! ### Half of step 4: a section of both projections is the diagonal -/

/-- **A morphism sectioning both projections of `X ×_S X` is the diagonal**, so a kernel
isomorphic to `Rs_*𝒪_X` is isomorphic to `Δ_*𝒪_X`.  This is the half of step 4 of the proof of
[Stacks, Tag 0G0E] that is proved in this development; it needs nothing from the hypotheses of
that tag, holding for an arbitrary morphism of schemes `f : X ⟶ S`, an arbitrary object `K` of
`D(𝒪_{X ×_S X})` and an arbitrary `s`.

The proof is the universal property of the fibre product: `s` and `Δ` agree after both
projections, hence are equal, and `Rs_*𝒪_X` is then `Δ_*𝒪_X` on the nose. -/
theorem iso_diagonalFourierMukaiKernel_of_isSection {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Limits.pullback f f).Modules) (s : X ⟶ Limits.pullback f f)
    (hfst : s ≫ Limits.pullback.fst f f = 𝟙 X) (hsnd : s ≫ Limits.pullback.snd f f = 𝟙 X)
    (e : K ≅ (derivedPushforward s.toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    Nonempty (K ≅ diagonalFourierMukaiKernel f) := by
  have hs : s = Limits.pullback.diagonal f :=
    Limits.pullback.hom_ext (by simp [hfst]) (by simp [hsnd])
  subst hs
  exact ⟨e⟩


end Stacks.Duality

end
