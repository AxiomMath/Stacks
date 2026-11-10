module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.StableKernelImage
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Affine sections of the stabilized kernel image

Let `Y` be an affine Noetherian scheme, `J ⊆ Γ(Y, ⊤)` an ideal and `α : F ⟶ G` a morphism of
coherent adic systems along `J`. Tag 087W turns `α` into a map `f` of finite modules over the
`J`-adic completion of `Γ(Y, ⊤)` and the term `F_m` into the quotient of the completed module of
`F` by its `(m+1)`-st ideal-power multiple, with
`Stacks.Coherent.affineLevelProjection` as the projection. This file identifies the global
sections of the stabilized kernel image `Stacks.Coherent.stableKernelImage` in those terms: they
are the image in `Γ(F_m, ⊤)` of `ker f` under that projection.

Two steps are involved. The sections of the kernel image computed from a level `l ≥ m` are the
image in `Γ(F_m, ⊤)` of the kernel of `α` on the sections of level `l`, which by Artin–Rees — in
the form `Stacks.AdicCompletion.exists_map_comap_pow_smul_restrictScalars_eq` — is already the
image of `ker f` once `l` is large. Choosing `l` above both that Artin–Rees level and the
stabilization level `Stacks.Coherent.kernelStableLevel`, the identification
`Stacks.Coherent.stableKernelImageIso` transports the computation to the stable kernel image
itself. Since the inclusion of the stable kernel image into `F_m` is a monomorphism and the
evaluation functor preserves finite limits, the sections of the stable kernel image are that
image, not merely isomorphic to it.

The file also compares the adic quotients of projected submodules. The image of a submodule
`K` under a projection `p` has, by `Stacks.AdicCompletion.adicRangeQuotientEquiv`, the intrinsic
adic quotients of `K` as soon as `ker p ⊓ K` is deep enough; a factorization `p₂ = t ∘ p₁` of one
projection through another induces a map between the two projected images, hence between their
adic quotients, and that map is bijective whenever both projection kernels meet `K` deeply
enough — both adic quotients are then the intrinsic one, compatibly with the identifications.

## Main definitions

* `Stacks.Coherent.completedModuleMapAsBase` — the map of completed modules induced by a
  morphism of coherent adic systems, as a map of modules over the ring of global sections.
* `Stacks.Coherent.stableKernelImageSections` — the global sections of the stable kernel image,
  as a module over the ring of global sections.
* `Stacks.Coherent.affineStableKernelImageSectionsIso` — the resulting identification of the
  sections of the stable kernel image with the projected kernel.
* `Stacks.AdicCompletion.adicQuotientEquivOfLinearEquiv` — the adic quotients of isomorphic
  modules are isomorphic.
* `Stacks.AdicCompletion.projectedSubmoduleRangeMap` — the map between the images of a submodule
  under two projections one of which factors through the other.
* `Stacks.AdicCompletion.projectedSubmoduleAdicQuotientMap` — the induced map on adic quotients.

## Main results

* `Stacks.Coherent.exists_affineKernelImageProjection_eq` — past an Artin–Rees level, the image
  in `Γ(F_m, ⊤)` of the kernel of `α` on sections of level `l` is the projected `ker f`.
* `Stacks.Coherent.affineStableKernelImage_range` — on an affine scheme the sections of the
  stable kernel image are exactly the projected `ker f`.
* `Stacks.AdicCompletion.projectedSubmoduleAdicQuotientMap_bijective` — the induced map on adic
  quotients is bijective once both projection kernels meet the submodule deeply enough.
* `Stacks.AdicCompletion.projectedSubmoduleRangeMap_mk`,
  `Stacks.AdicCompletion.projectedSubmoduleAdicQuotientMap_mk` and
  `Stacks.AdicCompletion.adicRangeQuotientEquiv_comp_mk` — all three maps are computed on
  representatives drawn from the submodule.

## Implementation notes

The morphism of completed modules is named rather than written as an `AdicCompletion`-linear map,
and `Stacks.Coherent.completedModuleAsBase` keeps the `Γ(Y, ⊤)`-module structure it carries as a
restriction of scalars. Every submodule, kernel and comap below therefore lives over a single
module instance and the rewrites fire at default transparency. A second
`Module Γ(Y, ⊤)`-structure on the completed module by `Module.compHom` would make the goal
type-incorrect against `Stacks.Coherent.affineLevelProjection`; the `AdicCompletion`-linear map
appears only inside the proof of `Stacks.Coherent.exists_affineKernelImageProjection_eq`.

The purely module-theoretic statements are in the `Stacks.AdicCompletion` namespace; they use the
identification `Stacks.AdicCompletion.quotientComapSubtypeEquivRange` of a projected submodule
with a quotient of it, and its adic form `Stacks.AdicCompletion.adicRangeQuotientEquiv`.

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the Stacks source's
`F_{n+1}`, which is why the annihilating exponent at level `n` is `n + 1`.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.AdicCompletion

/-! ### Adic quotients of projected submodules -/

/-- **An isomorphism of modules induces an isomorphism of their adic quotients.** The image of
`Jⁿ M` under an isomorphism is `Jⁿ` times the range, which is everything. -/
public def adicQuotientEquivOfLinearEquiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (n : ℕ) (e : M ≃ₗ[R] N) :
    (M ⧸ J ^ n • (⊤ : Submodule R M)) ≃ₗ[R] N ⧸ J ^ n • (⊤ : Submodule R N) :=
  Submodule.Quotient.equiv _ _ e (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])

/-- `Stacks.AdicCompletion.adicQuotientEquivOfLinearEquiv` is the given isomorphism on
representatives. -/
public theorem adicQuotientEquivOfLinearEquiv_mk {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (n : ℕ) (e : M ≃ₗ[R] N) (x : M) :
    adicQuotientEquivOfLinearEquiv J n e (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) :=
  rfl

/-- The adic quotients of a module presented as the image of a submodule `K` under a projection
`p` are the intrinsic adic quotients of `K`, read through the presentation. This is
`Stacks.AdicCompletion.adicRangeQuotientEquiv` transported along an arbitrary identification of
the presenting module. -/
public theorem adicRangeQuotientEquiv_comp_mk {R M N S : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup S] [Module R S]
    (J : Ideal R) (p : M →ₗ[R] N) (K : Submodule R M) (n : ℕ)
    (h : (LinearMap.ker p).comap K.subtype ≤ J ^ n • (⊤ : Submodule R K))
    (e : S ≃ₗ[R] LinearMap.range (p.comp K.subtype)) (x : K) :
    ((adicQuotientEquivOfLinearEquiv J n e).trans (adicRangeQuotientEquiv J p K n h))
        (Submodule.Quotient.mk
          (e.symm (quotientComapSubtypeEquivRange p K (Submodule.Quotient.mk x)))) =
      Submodule.Quotient.mk x := by
  rw [LinearEquiv.trans_apply, adicQuotientEquivOfLinearEquiv_mk, e.apply_symm_apply]
  exact adicRangeQuotientEquiv_mk J p K n h x

/-- **The map between the images of a submodule under two projections, one factoring through the
other.** If `p₂ = t ∘ p₁` then `t` carries the image of `K` under `p₁` onto its image under
`p₂`. -/
public def projectedSubmoduleRangeMap {R M N₁ N₂ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    (p₁ : M →ₗ[R] N₁) (p₂ : M →ₗ[R] N₂) (t : N₁ →ₗ[R] N₂) (K : Submodule R M)
    (ht : p₂ = t.comp p₁) :
    LinearMap.range (p₁.comp K.subtype) →ₗ[R] LinearMap.range (p₂.comp K.subtype) :=
  t.restrict fun _ hx => by
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, by rw [ht]; exact congrArg t hy⟩

/-- `Stacks.AdicCompletion.projectedSubmoduleRangeMap` sends the image of `x : K` under `p₁` to
its image under `p₂`. -/
public theorem projectedSubmoduleRangeMap_mk {R M N₁ N₂ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    (p₁ : M →ₗ[R] N₁) (p₂ : M →ₗ[R] N₂) (t : N₁ →ₗ[R] N₂) (K : Submodule R M)
    (ht : p₂ = t.comp p₁) (x : K) :
    projectedSubmoduleRangeMap p₁ p₂ t K ht
        (quotientComapSubtypeEquivRange p₁ K (Submodule.Quotient.mk x)) =
      quotientComapSubtypeEquivRange p₂ K (Submodule.Quotient.mk x) := by
  refine Subtype.ext ?_
  change t ((quotientComapSubtypeEquivRange p₁ K (Submodule.Quotient.mk x) :
      LinearMap.range (p₁.comp K.subtype)) : N₁) =
    ((quotientComapSubtypeEquivRange p₂ K (Submodule.Quotient.mk x) :
      LinearMap.range (p₂.comp K.subtype)) : N₂)
  rw [quotientComapSubtypeEquivRange_mk, quotientComapSubtypeEquivRange_mk, ht]
  rfl

/-- **The induced map on adic quotients of the projected images of a submodule.** A linear map
never enlarges the `Jⁿ`-multiple, so
`Stacks.AdicCompletion.projectedSubmoduleRangeMap` descends to the adic quotients. -/
public def projectedSubmoduleAdicQuotientMap {R M N₁ N₂ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    (J : Ideal R) (n : ℕ)
    (p₁ : M →ₗ[R] N₁) (p₂ : M →ₗ[R] N₂) (t : N₁ →ₗ[R] N₂) (K : Submodule R M)
    (ht : p₂ = t.comp p₁) :
    (LinearMap.range (p₁.comp K.subtype) ⧸
        J ^ n • (⊤ : Submodule R (LinearMap.range (p₁.comp K.subtype)))) →ₗ[R]
      (LinearMap.range (p₂.comp K.subtype) ⧸
        J ^ n • (⊤ : Submodule R (LinearMap.range (p₂.comp K.subtype)))) :=
  Submodule.mapQ _ _ (projectedSubmoduleRangeMap p₁ p₂ t K ht)
    (Submodule.map_le_iff_le_comap.mp (by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact Submodule.smul_mono le_rfl le_top))

/-- `Stacks.AdicCompletion.projectedSubmoduleAdicQuotientMap` is computed on the class of the
image of `x : K`. -/
public theorem projectedSubmoduleAdicQuotientMap_mk {R M N₁ N₂ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    (J : Ideal R) (n : ℕ)
    (p₁ : M →ₗ[R] N₁) (p₂ : M →ₗ[R] N₂) (t : N₁ →ₗ[R] N₂) (K : Submodule R M)
    (ht : p₂ = t.comp p₁) (x : K) :
    projectedSubmoduleAdicQuotientMap J n p₁ p₂ t K ht
        (Submodule.Quotient.mk
          (quotientComapSubtypeEquivRange p₁ K (Submodule.Quotient.mk x))) =
      Submodule.Quotient.mk
        (quotientComapSubtypeEquivRange p₂ K (Submodule.Quotient.mk x)) := by
  have hmapQ : projectedSubmoduleAdicQuotientMap J n p₁ p₂ t K ht
      (Submodule.Quotient.mk
        (quotientComapSubtypeEquivRange p₁ K (Submodule.Quotient.mk x))) =
      Submodule.Quotient.mk (projectedSubmoduleRangeMap p₁ p₂ t K ht
        (quotientComapSubtypeEquivRange p₁ K (Submodule.Quotient.mk x))) := rfl
  rw [hmapQ, projectedSubmoduleRangeMap_mk]

/-- **The transition map between the adic quotients of two projected images of a submodule is
bijective** as soon as both projection kernels meet the submodule inside its `Jⁿ`-multiple: both
adic quotients are then the intrinsic adic quotient of the submodule, by
`Stacks.AdicCompletion.adicRangeQuotientEquiv`, and the transition map is compatible with those
identifications because all three are the identity on representatives drawn from the
submodule. -/
public theorem projectedSubmoduleAdicQuotientMap_bijective {R M N₁ N₂ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    (J : Ideal R) (n : ℕ)
    (p₁ : M →ₗ[R] N₁) (p₂ : M →ₗ[R] N₂) (t : N₁ →ₗ[R] N₂) (K : Submodule R M)
    (ht : p₂ = t.comp p₁)
    (h₁ : (LinearMap.ker p₁).comap K.subtype ≤ J ^ n • (⊤ : Submodule R K))
    (h₂ : (LinearMap.ker p₂).comap K.subtype ≤ J ^ n • (⊤ : Submodule R K)) :
    Function.Bijective (projectedSubmoduleAdicQuotientMap J n p₁ p₂ t K ht) := by
  have he : ∀ z, adicRangeQuotientEquiv J p₂ K n h₂
      (projectedSubmoduleAdicQuotientMap J n p₁ p₂ t K ht z) =
      adicRangeQuotientEquiv J p₁ K n h₁ z := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ y =>
      obtain ⟨x, hx⟩ := y.2
      have hy : y = quotientComapSubtypeEquivRange p₁ K (Submodule.Quotient.mk x) := by
        refine Subtype.ext ?_
        rw [quotientComapSubtypeEquivRange_mk]
        exact hx.symm
      subst hy
      rw [projectedSubmoduleAdicQuotientMap_mk, adicRangeQuotientEquiv_mk,
        adicRangeQuotientEquiv_mk]
  refine ⟨fun x y hxy => (adicRangeQuotientEquiv J p₁ K n h₁).injective ?_, fun y => ?_⟩
  · calc adicRangeQuotientEquiv J p₁ K n h₁ x
        = adicRangeQuotientEquiv J p₂ K n h₂
            (projectedSubmoduleAdicQuotientMap J n p₁ p₂ t K ht x) := (he x).symm
      _ = adicRangeQuotientEquiv J p₂ K n h₂
            (projectedSubmoduleAdicQuotientMap J n p₁ p₂ t K ht y) :=
            congrArg (adicRangeQuotientEquiv J p₂ K n h₂) hxy
      _ = adicRangeQuotientEquiv J p₁ K n h₁ y := he y
  · refine ⟨(adicRangeQuotientEquiv J p₁ K n h₁).symm
      (adicRangeQuotientEquiv J p₂ K n h₂ y), ?_⟩
    refine (adicRangeQuotientEquiv J p₂ K n h₂).injective ?_
    rw [he, LinearEquiv.apply_symm_apply]

end Stacks.AdicCompletion

namespace Stacks.Coherent

/-! ### The map of completed modules -/

/-- The map of completed modules induced by a morphism of coherent adic systems through Tag 087W,
regarded as a map of modules over the ring of global sections. Its kernel is the submodule of
`Stacks.Coherent.completedModuleAsBase` whose projected images are the sections of the stable
kernel images. -/
public def completedModuleMapAsBase
    (Y : Scheme.{u}) [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] (J : Ideal Γ(Y, ⊤))
    {F G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop J)} (α : F ⟶ G) :
    completedModuleAsBase Y J F ⟶ completedModuleAsBase Y J G :=
  (ModuleCat.restrictScalars (algebraMap Γ(Y, ⊤) (AdicCompletion J Γ(Y, ⊤)))).map
    ((coherentAdicSystemsEquivFGModuleCat Y J).functor.map α).hom

/-! ### The sections of the stable kernel image -/

/-- **Artin–Rees for the kernel images on an affine Noetherian scheme.** There is a constant `c`
such that for every level `l ≥ m + c` the image in `Γ(F_m, ⊤)` of the kernel of `α` on the
sections of level `l` is the image under
`Stacks.Coherent.affineLevelProjection` of the kernel of the induced map of completed modules.

Through Tag 087W the projections out of the completed module realize `Γ(F_l, ⊤)` as a quotient
of it and commute with `α`, so the kernel upstairs may be replaced by the preimage of the kernel
downstairs; `Stacks.AdicCompletion.exists_map_comap_pow_smul_restrictScalars_eq` identifies the
image of that preimage with the image of the honest kernel once `l` is large. -/
public theorem exists_affineKernelImageProjection_eq (Y : Scheme.{u}) [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : Ideal Γ(Y, ⊤))
    {F G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop J)} (α : F ⟶ G) (m : ℕ) :
    ∃ c : ℕ, ∀ l : ℕ, ∀ h : m + c ≤ l,
      Submodule.map ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (F.obj.map (homOfLE ((Nat.le_add_right m c).trans h)).op)).hom
          (LinearMap.ker ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (α.hom.app (op l))).hom) =
        Submodule.map (affineLevelProjection Y J F m).hom
          (LinearMap.ker (completedModuleMapAsBase Y J α).hom) := by
  let Q := coherentAdicSystemsEquivFGModuleCat Y J
  let _ : Module (AdicCompletion J Γ(Y, ⊤)) (completedModuleAsBase Y J F) :=
    (Q.functor.obj F).obj.isModule
  let _ : Module (AdicCompletion J Γ(Y, ⊤)) (completedModuleAsBase Y J G) :=
    (Q.functor.obj G).obj.isModule
  let _ : IsScalarTower Γ(Y, ⊤) (AdicCompletion J Γ(Y, ⊤)) (completedModuleAsBase Y J F) :=
    IsScalarTower.of_compHom _ _ _
  let _ : IsScalarTower Γ(Y, ⊤) (AdicCompletion J Γ(Y, ⊤)) (completedModuleAsBase Y J G) :=
    IsScalarTower.of_compHom _ _ _
  let _ : Module.Finite (AdicCompletion J Γ(Y, ⊤)) (completedModuleAsBase Y J G) :=
    inferInstanceAs (Module.Finite (AdicCompletion J Γ(Y, ⊤)) (Q.functor.obj G))
  let f : completedModuleAsBase Y J F →ₗ[AdicCompletion J Γ(Y, ⊤)]
      completedModuleAsBase Y J G := (Q.functor.map α).hom.hom
  obtain ⟨c, hc⟩ := Stacks.AdicCompletion.exists_map_comap_pow_smul_restrictScalars_eq
    (P := (globalSectionsSystem F).obj (op m)) J f
  refine ⟨c, fun l h => ?_⟩
  let p := (affineLevelProjection Y J F l).hom
  let q := (affineLevelProjection Y J G l).hom
  let a : (globalSectionsSystem F).obj (op l) →ₗ[Γ(Y, ⊤)]
      (globalSectionsSystem G).obj (op l) :=
    ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map (α.hom.app (op l))).hom
  let t : (globalSectionsSystem F).obj (op l) →ₗ[Γ(Y, ⊤)]
      (globalSectionsSystem F).obj (op m) :=
    ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
      (F.obj.map (homOfLE ((Nat.le_add_right m c).trans h)).op)).hom
  have hsquare : a.comp p = q.comp (f.restrictScalars Γ(Y, ⊤)) :=
    (congrArg ModuleCat.Hom.hom (affineLevelProjection_naturality Y J α l)).symm
  have hproj : t.comp p = (affineLevelProjection Y J F m).hom :=
    congrArg ModuleCat.Hom.hom (show affineLevelProjection Y J F l ≫
        (globalSectionsSystem F).map (homOfLE ((Nat.le_add_right m c).trans h)).op =
        affineLevelProjection Y J F m by simp [affineLevelProjection, Category.assoc])
  change Submodule.map t (LinearMap.ker a) = _
  rw [Stacks.AdicCompletion.map_ker_eq_map_comap_ker (f.restrictScalars Γ(Y, ⊤)) p q a t
    (affineLevelProjection_surjective Y J F l) hsquare, hproj]
  change Submodule.map _ (Submodule.comap (f.restrictScalars Γ(Y, ⊤))
    (LinearMap.ker (affineLevelProjection Y J G l).hom)) = _
  rw [affineLevelProjection_ker]
  exact hc (m + 1) (l + 1) (by omega) _ (affineLevelProjection_ker Y J F m).ge

/-- **The sections of the stable kernel image on an affine Noetherian scheme.** The range on
global sections of the inclusion of `Stacks.Coherent.stableKernelImage` into `F_m` is the image
under `Stacks.Coherent.affineLevelProjection` of the kernel of the induced map of completed
modules. -/
public theorem affineStableKernelImage_range (Y : Scheme.{u}) [IsAffine Y] [IsNoetherian Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : Ideal Γ(Y, ⊤))
    {F G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop J)} (α : F ⟶ G) (m : ℕ) :
    LinearMap.range ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
        (stableKernelImageIncl (Scheme.IdealSheafData.ofIdealTop J) α m)).hom =
      Submodule.map (affineLevelProjection Y J F m).hom
        (LinearMap.ker (completedModuleMapAsBase Y J α).hom) := by
  let E : Y.Modules ⥤ ModuleCat.{u} Γ(Y, ⊤) :=
    SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)
  let I := Scheme.IdealSheafData.ofIdealTop J
  obtain ⟨c, hc⟩ := exists_affineKernelImageProjection_eq Y J α m
  let l := kernelStableLevel I α m + (m + c)
  have hstab : kernelStableLevel I α m ≤ l := Nat.le_add_right _ _
  have hAR : m + c ≤ l := Nat.le_add_left _ _
  have hml : m ≤ l := (le_kernelStableLevel I α m).trans hstab
  have hcohF : ∀ n : ℕ, (F.obj.obj (op n)).IsCoherent := F.property.isCoherent
  have hcohG : ∀ n : ℕ, (G.obj.obj (op n)).IsCoherent := G.property.isCoherent
  have hcohker : ∀ n : ℕ, (kernel (α.hom.app (op n))).IsCoherent := fun n =>
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (α.hom.app (op n))
  have hzero : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hfl : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have hle : ∀ {A B C : Y.Modules} (e : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C), e ≫ g = k →
      LinearMap.range (E.map k).hom ≤ LinearMap.range (E.map g).hom := by
    rintro _ _ _ e g _ rfl
    rw [E.map_comp, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  have hrange : LinearMap.range (E.map (stableKernelImageIncl I α m)).hom =
      LinearMap.range (E.map (kernelImageAtIncl I α m l hml)).hom :=
    le_antisymm (hle _ _ _ (stableKernelImageIso_inv_comp I α m l hstab))
      (hle _ _ _ (stableKernelImageIso_hom_comp I α m l hstab))
  have himg : LinearMap.range (E.map (kernelImageAtIncl I α m l hml)).hom =
      LinearMap.range (E.map (kernel.ι (α.hom.app (op l)) ≫
        F.obj.map (homOfLE hml).op)).hom :=
    range_image_ι_app_top (kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE hml).op)
  exact hrange.trans (himg.trans
    ((range_map_kernel_ι_comp E (α.hom.app (op l)) (F.obj.map (homOfLE hml).op)).trans
      (hc l hAR)))

/-- The global sections of the stable kernel image at level `m`, as a module over the ring of
global sections of the ambient affine scheme. -/
public abbrev stableKernelImageSections (Y : Scheme.{u}) [IsAffine Y] [IsNoetherian Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : Ideal Γ(Y, ⊤))
    {F G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop J)} (α : F ⟶ G) (m : ℕ) :
    ModuleCat.{u} Γ(Y, ⊤) :=
  (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).obj
    (stableKernelImage (Scheme.IdealSheafData.ofIdealTop J) α m)

/-- **The sections of the stable kernel image, as an identification.** On an affine Noetherian
scheme the global sections of `Stacks.Coherent.stableKernelImage` are the image of the kernel of
the induced map of completed modules under
`Stacks.Coherent.affineLevelProjection`, through the map induced by the inclusion into `F_m`. -/
public def affineStableKernelImageSectionsIso (Y : Scheme.{u}) [IsAffine Y] [IsNoetherian Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : Ideal Γ(Y, ⊤))
    {F G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop J)} (α : F ⟶ G) (m : ℕ) :
    stableKernelImageSections Y J α m ≃ₗ[Γ(Y, ⊤)]
      LinearMap.range ((affineLevelProjection Y J F m).hom.comp
        (LinearMap.ker (completedModuleMapAsBase Y J α).hom).subtype) := by
  let E : Y.Modules ⥤ ModuleCat.{u} Γ(Y, ⊤) :=
    SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)
  let I := Scheme.IdealSheafData.ofIdealTop J
  have hzero : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hfl : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have hinj : Function.Injective (E.map (stableKernelImageIncl I α m)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  refine (LinearEquiv.ofInjective _ hinj).trans
    (LinearEquiv.ofEq _ _ ((affineStableKernelImage_range Y J α m).trans ?_))
  rw [LinearMap.range_comp, Submodule.range_subtype]

end Stacks.Coherent

end
