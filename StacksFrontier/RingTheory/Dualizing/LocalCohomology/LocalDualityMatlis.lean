module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion.ScalarExtension
public import StacksFrontier.RingTheory.AdicCompletion.LinearOverCompletion
public import StacksFrontier.RingTheory.Dualizing.DualExtAnnihilator
public import StacksFrontier.RingTheory.Dualizing.DualExtDepthDimension
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExt
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull.Matlis
public import StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Local duality in Matlis form

Let `(A, 𝔪, κ)` be a Noetherian local ring with a normalized dualizing complex `ω`, let `E` be
an injective hull of `κ`, and let `M` be a finite `A`-module. Stacks 0AAK, the local duality
theorem, identifies the `𝔪`-adic completion of `Ext^{-i}_A(M, ω)` with the Matlis dual
`Hom_A(H^i_𝔪(M), E)`. This file turns that identification around, producing an isomorphism

`H^i_𝔪(M) ≅ Hom_A(Ext^{-i}_A(M, ω), E)`

of `A`-modules. This is the form in which Grothendieck's local duality is usually stated, and
the form in which it recognises a local cohomology module as the Matlis dual of a *finite
`A`-module* — which is what makes such a module available as the `N` of Stacks 0EHK.

Over a complete ring this is immediate from Matlis duality, Stacks 08Z9. Over a general
Noetherian local ring it is not, because biduality `N ≅ Hom_A(Hom_A(N, E), E)` fails for
Artinian `N` when `A` is not complete — already for `N = E`, where `Hom_A(E, E) = A^∧` and
`Hom_A(A^∧, E)` is strictly larger than `E`. The passage therefore runs through `Â`, the
`𝔪`-adic completion of `A`:

* `H^i_𝔪(M)` is Artinian, hence `𝔪`-power torsion, hence unchanged by `Â ⊗_A -`
  (Stacks 0BNK, `tensorProduct_mk_bijective_of_ideal_power_torsion`), and the resulting
  `Â`-module is Artinian over `Â`;
* an injective hull of the residue field of `Â` restricts to an injective hull of `κ`
  (Stacks 08Z5, `Dualizing.exists_iso_injectiveHull_residueField` applied to `A → Â`, which is
  flat and local with trivial closed fibre);
* Matlis biduality over the complete ring `Â` applies to `Â ⊗_A H^i_𝔪(M)`;
* the `A`-linear isomorphism of Stacks 0AAK is automatically `Â`-linear, because its target
  `Ext^{-i}_A(M, ω)^∧` is `𝔪`-adically separated
  (`AdicCompletion.map_smul_of_isHausdorff`);
* finally `Hom_Â(Â ⊗_A N, E) = Hom_A(N, E)` by the base-change adjunction, which converts the
  answer over `Â` back into a Matlis dual over `A`.

## Main results

* `Module.isInjectiveHull_iso_comp` — precomposing an injective hull with an isomorphism of its
  source again gives an injective hull.
* `Dualizing.LocalDuality.nonempty_linearEquiv_injectiveHull_adicCompletion` — an injective hull
  of the residue field of `Â` restricts to an injective hull of `κ`.
* `Dualizing.LocalDuality.nonempty_localCohomology_linearEquiv_matlisDual_ext` — local duality
  in Matlis form.

## References

* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK), local duality.
* [Stacks Project, Tag 08Z9](https://stacks.math.columbia.edu/tag/08Z9), Matlis duality.
* [Stacks Project, Tag 08Z5](https://stacks.math.columbia.edu/tag/08Z5), hulls along a flat map.
* [Stacks Project, Tag 0BNK](https://stacks.math.columbia.edu/tag/0BNK), torsion and completion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Module

/-- Precomposing an injective hull with an isomorphism of its source gives an injective hull.
Essentiality depends only on the subobject cut out by the monomorphism, and an isomorphism of
the source does not change it. -/
theorem isInjectiveHull_iso_comp {𝒜 : Type*} [Category 𝒜] [Limits.HasZeroObject 𝒜]
    [Limits.HasPullbacks 𝒜] {N M I : 𝒜} (e : N ≅ M) (i : M ⟶ I) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Module.IsInjectiveHull (e.hom ≫ i) := by
  refine ⟨hi.1, fun B' hB' => ?_⟩
  rw [Subobject.mk_eq_mk_of_comm _ _ e rfl]
  exact hi.2 B' hB'

end Module

namespace Dualizing.LocalDuality

/-- The universe lift of a module, identified with the module itself. -/
private def uliftDown (R : Type u) [CommRing R] (X : ModuleCat.{u} R) :
    (ModuleCat.uliftFunctor.{u} R).obj X ≅ X :=
  (ULift.moduleEquiv (R := R) (M := (X : Type u))).toModuleIso

/-- `Dualizing.uliftDown` at the residue field, spelled with `Dualizing.residueFieldModule` as
its source so that `Mono` instances are found in the shape Matlis duality asks for. -/
private def residueFieldModuleIso (R : Type u) [CommRing R] [IsLocalRing R] :
    Dualizing.residueFieldModule.{u, u} R ≅ ModuleCat.of R (ResidueField R) :=
  uliftDown R (ModuleCat.of R (ResidueField R))

/-- The closed fibre of the `𝔪`-adic completion of a Noetherian local ring is its residue
field. -/
private theorem bijective_closedFiberMap_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    Function.Bijective (Dualizing.closedFiberMap A (AdicCompletion (maximalIdeal A) A)) := by
  set Ahat := AdicCompletion (maximalIdeal A) A
  have hmax : maximalIdeal Ahat = (maximalIdeal A).map (algebraMap A Ahat) :=
    AdicCompletion.maximalIdeal_eq_map
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hxy' : Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A Ahat))
        (algebraMap A Ahat a) =
          Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A Ahat))
            (algebraMap A Ahat b) := by
      simpa [Dualizing.closedFiberMap, Ideal.quotientMap_mk] using hxy
    refine Ideal.Quotient.eq.mpr ?_
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap A Ahat), Ideal.mem_comap, hmax, map_sub]
    exact Ideal.Quotient.eq.mp hxy'
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ :=
      AdicCompletion.exists_sub_mem_map_pow (maximalIdeal A) (IsNoetherian.noetherian _) 1 s
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    have hmem : algebraMap A Ahat c - s ∈ (maximalIdeal A).map (algebraMap A Ahat) := by
      simpa [neg_sub] using Submodule.neg_mem ((maximalIdeal A).map (algebraMap A Ahat))
        (show s - algebraMap A Ahat c ∈ _ by simpa using hc)
    simpa [Dualizing.closedFiberMap, Ideal.quotientMap_mk] using Ideal.Quotient.eq.mpr hmem

/-- **An injective hull of the residue field of the completion is one for the residue field.**
For a Noetherian local ring `A` with `𝔪`-adic completion `Â`, restriction of scalars along
`A → Â` carries an injective hull of the residue field of `Â` to an injective hull of the
residue field of `A`; so the two agree, up to isomorphism of `A`-modules. -/
theorem nonempty_linearEquiv_injectiveHull_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj (ModuleCat.of A (ResidueField A)) ⟶ E)
    [Mono ι] (hι : Module.IsInjectiveHull ι)
    {E' : ModuleCat.{u} (AdicCompletion (maximalIdeal A) A)}
    (ι' : ModuleCat.of (AdicCompletion (maximalIdeal A) A)
      (ResidueField (AdicCompletion (maximalIdeal A) A)) ⟶ E')
    [Mono ι'] (hι' : Module.IsInjectiveHull ι') :
    Nonempty ((E : Type u) ≃ₗ[A]
      (((ModuleCat.restrictScalars (algebraMap A (AdicCompletion (maximalIdeal A) A))).obj E' :
        ModuleCat.{u} A) : Type u)) := by
  have hflat : RingHom.Flat (algebraMap A (AdicCompletion (maximalIdeal A) A)) :=
    RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)
  obtain ⟨εiso, -⟩ := Dualizing.exists_iso_injectiveHull_residueField A
    (AdicCompletion (maximalIdeal A) A) hflat (bijective_closedFiberMap_adicCompletion A)
    ((uliftDown A (ModuleCat.of A (ResidueField A))).inv ≫ ι) ι'
    (Module.isInjectiveHull_iso_comp (uliftDown A (ModuleCat.of A (ResidueField A))).symm ι hι)
    hι'
  exact ⟨εiso.toLinearEquiv⟩

/-- **Matlis biduality over a complete Noetherian local ring, in module form.** An Artinian
module over a Noetherian local ring which is complete for its maximal ideal is the Matlis dual
of its own Matlis dual. -/
theorem nonempty_linearEquiv_matlisBidual
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    {E : ModuleCat.{u} R}
    (ι : ModuleCat.of R (ResidueField R) ⟶ E) [Mono ι] (hι : Module.IsInjectiveHull ι)
    (N : Type u) [AddCommGroup N] [Module R N] [IsArtinian R N] :
    Nonempty (N ≃ₗ[R] ((N →ₗ[R] (E : Type u)) →ₗ[R] (E : Type u))) := by
  let XN : ModuleCat.{u} R := ModuleCat.of R N
  have := Dualizing.isIso_matlisEvaluation_of_isArtinian.{u, u} R E XN
    ((residueFieldModuleIso R).hom ≫ ι)
    (Module.isInjectiveHull_iso_comp (residueFieldModuleIso R) ι hι)
  let eInner : (XN ⟶ E) ≃ₗ[R] (N →ₗ[R] (E : Type u)) := ModuleCat.homLinearEquiv
  let eOuter : (ModuleCat.of R (XN ⟶ E) ⟶ E) ≃ₗ[R] ((XN ⟶ E) →ₗ[R] (E : Type u)) :=
    ModuleCat.homLinearEquiv
  exact ⟨(asIso ((Dualizing.matlisEvaluation R E).app XN)).toLinearEquiv.trans
    (eOuter.trans (LinearEquiv.arrowCongr eInner (LinearEquiv.refl R (E : Type u))))⟩

/-- An Artinian module over a Noetherian local ring is unchanged by base change to the
`𝔪`-adic completion. -/
private theorem nonempty_linearEquiv_adicCompletion_tensor_of_isArtinian
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (N : Type u) [AddCommGroup N] [Module A N] [IsArtinian A N] :
    Nonempty (N ≃ₗ[A] AdicCompletion (maximalIdeal A) A ⊗[A] N) := by
  have htors : ∀ x : N, ∃ n : ℕ, ∀ a ∈ (maximalIdeal A) ^ n, a • x = 0 := fun x => by
    obtain ⟨n, -, hn⟩ :=
      ((Dualizing.isArtinian_iff_powerTorsion_and_finiteSocle A N).mp inferInstance).1 x
    exact ⟨n, hn⟩
  have hmkbij : Function.Bijective
      (fun x : N => TensorProduct.mk A N (AdicCompletion (maximalIdeal A) A) x 1) :=
    (tensorProduct_mk_bijective_of_ideal_power_torsion.{u, u, u} A (maximalIdeal A) N htors).2
      (IsNoetherian.noetherian _)
  exact ⟨(LinearEquiv.ofBijective ((TensorProduct.mk A N _).flip 1) hmkbij).trans
    (TensorProduct.comm A N _)⟩

/-- For a finite module `G` over a Noetherian local ring `A` with completion `Â`, an `Â`-linear
map out of the completion of `G` is the same as an `A`-linear map out of `G`. -/
private theorem nonempty_linearEquiv_linearMap_adicCompletion_of_finite
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (G : Type*) [AddCommGroup G] [Module A G] [Module.Finite A G]
    (E' : Type u) [AddCommGroup E'] [Module (AdicCompletion (maximalIdeal A) A) E'] [Module A E']
    [IsScalarTower A (AdicCompletion (maximalIdeal A) A) E'] :
    Nonempty ((AdicCompletion (maximalIdeal A) G →ₗ[AdicCompletion (maximalIdeal A) A] E') ≃ₗ[A]
      (G →ₗ[A] E')) := by
  set Ahat := AdicCompletion (maximalIdeal A) A
  -- a model of the dual Ext module in the ring's own universe
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' A G
  let G₀ : Type u := (Fin n → A) ⧸ LinearMap.ker φ
  let eG : G₀ ≃ₗ[A] G := φ.quotKerEquivOfSurjective hφ
  have : Module.Finite A G₀ := Module.Finite.equiv eG.symm
  let eAdj : (G₀ →ₗ[A] E') ≃ₗ[Ahat] ((Ahat ⊗[A] G₀) →ₗ[Ahat] E') :=
    LinearMap.liftBaseChangeEquiv Ahat
  let eG₀ : AdicCompletion (maximalIdeal A) G ≃ₗ[Ahat] AdicCompletion (maximalIdeal A) G₀ :=
    AdicCompletion.congr (maximalIdeal A) eG.symm
  let eCompl : Ahat ⊗[A] G₀ ≃ₗ[Ahat] AdicCompletion (maximalIdeal A) G₀ :=
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal A) G₀
  exact ⟨(((LinearEquiv.arrowCongr (eG₀.trans eCompl.symm) (LinearEquiv.refl Ahat E')).trans
    eAdj.symm).restrictScalars A).trans (LinearEquiv.arrowCongr eG (LinearEquiv.refl A E'))⟩

/-- **Local duality in Matlis form.** Let `(A, 𝔪, κ)` be a Noetherian local ring with normalized
dualizing complex `ω`, let `E` be an injective hull of `κ`, and let `M` be a finite `A`-module.
Then the local cohomology module `H^i_𝔪(M)` is the Matlis dual of the finite `A`-module
`Ext^{-i}_A(M, ω)`.

This is the Matlis-dual reading of Stacks 0AAK, which identifies the `𝔪`-adic completion of
`Ext^{-i}_A(M, ω)` with `Hom_A(H^i_𝔪(M), E)`. The ring is not assumed complete. -/
theorem nonempty_localCohomology_linearEquiv_matlisDual_ext
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj (ModuleCat.of A (ResidueField A)) ⟶ E)
    [Mono ι] (hι : Module.IsInjectiveHull ι) (i : ℤ) :
    Nonempty
      ((Stacks.LocalCohomology.localCohomologyModule A (maximalIdeal A)
          (IsNoetherian.noetherian _) (ModuleCat.of A M) i : Type u) ≃ₗ[A]
        (Dualizing.moduleExtInto M ω (-i) →ₗ[A] (E : Type u))) := by
  classical
  have hmFG : (maximalIdeal A).FG := IsNoetherian.noetherian _
  set Ahat := AdicCompletion (maximalIdeal A) A
  set H := (Stacks.LocalCohomology.localCohomologyModule A (maximalIdeal A)
    (IsNoetherian.noetherian _) (ModuleCat.of A M) i : ModuleCat.{u} A)
  set G := Dualizing.moduleExtInto M ω (-i)
  have : Module.Finite A G := Dualizing.moduleExtInto_finite (A := A) (M := M) ω hω i
  have : IsArtinian A (H : Type u) :=
    Stacks.LocalCohomology.isArtinian_localCohomology_maximalIdeal A (ModuleCat.of A M) i
  -- `H` is `𝔪`-power torsion, so completion does not change it
  obtain ⟨eH⟩ := nonempty_linearEquiv_adicCompletion_tensor_of_isArtinian A (H : Type u)
  have : IsArtinian A (Ahat ⊗[A] (H : Type u)) :=
    isArtinian_of_surjective (H : Type u) eH.toLinearMap eH.surjective
  have : IsArtinian Ahat (Ahat ⊗[A] (H : Type u)) := isArtinian_of_tower A inferInstance
  -- an injective hull of the residue field of the completion, and its comparison with `E`
  obtain ⟨E', ι', _, hι'hull⟩ := Module.exists_isInjectiveHull Ahat
    (ModuleCat.of Ahat (ResidueField Ahat))
  obtain ⟨εlin⟩ := nonempty_linearEquiv_injectiveHull_adicCompletion A ι hι ι' hι'hull
  let : Module A (E' : Type u) := Module.compHom (E' : Type u) (algebraMap A Ahat)
  have : IsScalarTower A Ahat (E' : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- Matlis biduality over the complete ring `Â`
  obtain ⟨ebi⟩ := nonempty_linearEquiv_matlisBidual Ahat ι' hι'hull (Ahat ⊗[A] (H : Type u))
  -- the base-change adjunction on both sides
  obtain ⟨eG⟩ := nonempty_linearEquiv_linearMap_adicCompletion_of_finite A G (E' : Type u)
  let eAdj : ((H : Type u) →ₗ[A] (E' : Type u)) ≃ₗ[Ahat]
      ((Ahat ⊗[A] (H : Type u)) →ₗ[Ahat] (E' : Type u)) :=
    LinearMap.liftBaseChangeEquiv Ahat
  -- local duality, upgraded to the completion
  obtain ⟨eDual⟩ :=
    nonempty_adicCompletion_ext_linearEquiv_linearMap_localCohomology
      A f hf ω hω ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))
      (fun j => Dualizing.finite_homology_single (ModuleCat.of A M) j) ι hι i
  let θ : AdicCompletion (maximalIdeal A) G ≃ₗ[A] ((H : Type u) →ₗ[A] (E' : Type u)) :=
    eDual.trans (LinearEquiv.arrowCongr (LinearEquiv.refl A (H : Type u)) εlin)
  have : IsHausdorff (maximalIdeal A) (AdicCompletion (maximalIdeal A) G) :=
    (AdicCompletion.isAdicComplete hmFG).toIsHausdorff
  let θhat : ((H : Type u) →ₗ[A] (E' : Type u)) ≃ₗ[Ahat] AdicCompletion (maximalIdeal A) G :=
    AdicCompletion.toCompletionLinearEquiv hmFG θ.symm
  -- assemble
  let chain : (Ahat ⊗[A] (H : Type u)) ≃ₗ[Ahat]
      (AdicCompletion (maximalIdeal A) G →ₗ[Ahat] (E' : Type u)) :=
    ebi.trans ((LinearEquiv.arrowCongr eAdj.symm (LinearEquiv.refl Ahat (E' : Type u))).trans
      (LinearEquiv.arrowCongr θhat (LinearEquiv.refl Ahat (E' : Type u))))
  exact ⟨eH.trans ((chain.restrictScalars A).trans
    (eG.trans (LinearEquiv.arrowCongr (LinearEquiv.refl A G) εlin.symm)))⟩

end Dualizing.LocalDuality

end
