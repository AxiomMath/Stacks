module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineToolbox
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelImage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.RingTheory.Noetherian.AdicKernelStabilization

/-!
# Stabilization of the levelwise kernel images of a morphism of coherent adic systems

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf and `α : F ⟶ G` a morphism of
coherent adic systems along `ℐ`. Termwise kernels do not form an adic system, so the kernel in
`Coh(X, ℐ)` is instead assembled from the subobjects `kernelImageAt ℐ α m l ⊆ F_m`, the images in
`F_m` of `ker(α_l)` for `l ≥ m`. These shrink as `l` grows, and the kernel system can only be
defined once they stop shrinking. *Stabilization* is exactly that: for each fixed `m` there is a
constant `c` beyond which the kernel image computed from level `l` is the same subobject of `F_m`
as the one computed from level `m + c` — the same object, by an isomorphism compatible with the
inclusions into `F_m`.

This is the first of the two stabilizations in Tag 087X, and it is a genuinely local statement.
On an affine open `Spec A` with `A` Noetherian, Tag 087W turns `α` into a map `f : M → N` of
finite modules over the `ℐ`-adic completion of `A`, the term `F_m` into `M / 𝔞 ᵐ⁺¹ M`, and the
kernel image into the image of `f⁻¹(𝔞 ˡ⁺¹ N)` in `M / 𝔞 ᵐ⁺¹ M`. Artin–Rees, in the form
`Stacks.AdicCompletion.exists_map_comap_pow_smul_restrictScalars_eq`, says that this image is
already the image of `ker f` once `l ≥ m + c`, which is the stabilization on sections. Being an
isomorphism is local on an open cover, and a Noetherian scheme has a finite cover by Noetherian
affines, so finitely many such constants may be taken at once: their maximum works globally.

## Main results

* `Stacks.Coherent.kernelImages_eventuallyConstant` — the kernel images in a fixed term `F_m` are
  eventually independent of the level they are computed from.
* `Stacks.Coherent.affineKernelImages_eventuallyConstant` and
  `Stacks.Coherent.affineKernelImages_eventuallyConstant_of_idealSheaf` — the affine case, as the
  stabilization of the submodules of global sections.
* `Stacks.Coherent.restricted_kernelImages_eventuallyConstant` — the affine case transported to an
  affine open of an arbitrary Noetherian scheme: past the constant, any comparison map between two
  kernel images becomes invertible after restriction.
* `Stacks.Coherent.isIso_of_bijective_evaluation_top` — a morphism of quasi-coherent modules on an
  affine spectrum which is bijective on global sections is an isomorphism.
* `Stacks.Coherent.range_map_kernel_ι_comp` — the range on sections of a kernel inclusion followed
  by a map is the image of the kernel.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the Stacks source's
`F_{n+1}`, which is why the annihilating exponent at level `n` is `n + 1`.

`restricted_kernelImages_eventuallyConstant` is phrased as the invertibility of *any* morphism
between two kernel images lying over their inclusions into `F_m`, rather than as the existence of
one isomorphism with a distinguished high level. That form is what the gluing step needs: the
constants produced on the different members of the cover are different, while the morphism whose
invertibility has to be checked is a single global one supplied by
`Stacks.Coherent.kernelImageAt_hasMap` at the maximum of those constants.

The monotonicity hypothesis of `Stacks.Coherent.kernelImageAt` is an explicit argument, so every
statement below names the proof it uses; since these are proofs of a proposition, two kernel
images at the same pair of levels are the same object whichever proof is named.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### Tools -/

/-- The inclusion of a levelwise kernel image into the term containing it is a monomorphism,
being the inclusion of a categorical image. -/
public instance mono_kernelImageAtIncl {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : CoherentAdicSystems I} (α : F ⟶ G) (m l : ℕ) (h : m ≤ l) :
    Mono (kernelImageAtIncl I α m l h) := by
  change Mono (image.ι (kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE h).op))
  infer_instance

/-- **A morphism of quasi-coherent modules on an affine spectrum which is bijective on global
sections is an isomorphism.** Global sections identify the quasi-coherent modules on `Spec R` with
the `R`-modules, by `AlgebraicGeometry.tildeEquiv`; an equivalence reflects isomorphisms, and a
bijective map of modules is one. -/
public theorem isIso_of_bijective_evaluation_top {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hf : Function.Bijective
      ((SheafOfModules.evaluation (Spec R).ringCatSheaf (op ⊤)).map f).hom) : IsIso f := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let M' : P.FullSubcategory := ⟨M, inferInstance⟩
  let N' : P.FullSubcategory := ⟨N, inferInstance⟩
  let g : M' ⟶ N' := ObjectProperty.homMk f
  have : IsIso ((tildeEquiv (R := R)).inverse.map g) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hf
  have : IsIso g := isIso_of_reflects_iso g (tildeEquiv (R := R)).inverse
  exact inferInstanceAs (IsIso (P.ι.map g))

/-- An additive functor to modules which preserves the kernel of `φ` carries the composite of the
kernel inclusion with a map `t` to a linear map whose range is the image under `t` of the kernel
of `φ`. -/
public theorem range_map_kernel_ι_comp
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A : Type*} [Ring A] (E : C ⥤ ModuleCat A) [E.PreservesZeroMorphisms]
    {M N P : C} (φ : M ⟶ N) (t : M ⟶ P) [HasKernel φ]
    [PreservesLimit (parallelPair φ 0) E] :
    LinearMap.range (E.map (kernel.ι φ ≫ t)).hom =
      Submodule.map (E.map t).hom (LinearMap.ker (E.map φ).hom) := by
  have hfac : (E.map (kernel.ι φ ≫ t)).hom =
      (E.map t).hom.comp (E.map (kernel.ι φ)).hom :=
    congrArg ModuleCat.Hom.hom (E.map_comp (kernel.ι φ) t)
  rw [hfac, LinearMap.range_comp, range_map_kernel_ι E φ]

/-! ### The affine case -/

/-- **Stabilization of the kernel images over an affine Noetherian scheme.** For a morphism `α` of
coherent adic systems along an ideal `J ⊆ Γ(Y, ⊤)` and a level `m`, there is a constant `c` such
that the image in `Γ(F_m, ⊤)` of the kernel of `α` on the sections of level `l` is the same
submodule for every `l ≥ m + c`.

Through Tag 087W the system is the tower of adic quotients of a finite module `M` over the
completion, `α` is induced by a map `f` of such modules, and the submodule in question is the
image of `f⁻¹(Jˡ⁺¹)` in `M / Jᵐ⁺¹ M`; Artin–Rees identifies that image with the image of
`ker f` as soon as `l ≥ m + c`. -/
public theorem affineKernelImages_eventuallyConstant (Y : Scheme.{u}) [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : Ideal Γ(Y, ⊤))
    {F G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop J)} (α : F ⟶ G) (m : ℕ) :
    ∃ c : ℕ, ∀ l : ℕ, ∀ h : m + c ≤ l,
      Submodule.map ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (F.obj.map (homOfLE ((Nat.le_add_right m c).trans h)).op)).hom
          (LinearMap.ker ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (α.hom.app (op l))).hom) =
        Submodule.map ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (F.obj.map (homOfLE (Nat.le_add_right m c)).op)).hom
          (LinearMap.ker ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (α.hom.app (op (m + c)))).hom) := by
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
  have hstable : ∀ l : ℕ, ∀ h : m + c ≤ l,
      Submodule.map ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (F.obj.map (homOfLE ((Nat.le_add_right m c).trans h)).op)).hom
          (LinearMap.ker ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (α.hom.app (op l))).hom) =
        Submodule.map (affineLevelProjection Y J F m).hom
          ((LinearMap.ker f).restrictScalars Γ(Y, ⊤)) := by
    intro l h
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
    have hproj : t.comp p = (affineLevelProjection Y J F m).hom := by
      have heq : affineLevelProjection Y J F l ≫
          (globalSectionsSystem F).map
            (homOfLE ((Nat.le_add_right m c).trans h)).op =
          affineLevelProjection Y J F m := by
        simp [affineLevelProjection, Category.assoc]
      exact congrArg ModuleCat.Hom.hom heq
    show Submodule.map t (LinearMap.ker a) = _
    rw [Stacks.AdicCompletion.map_ker_eq_map_comap_ker (f.restrictScalars Γ(Y, ⊤)) p q a t
      (affineLevelProjection_surjective Y J F l) hsquare, hproj]
    show Submodule.map _ (Submodule.comap (f.restrictScalars Γ(Y, ⊤))
      (LinearMap.ker (affineLevelProjection Y J G l).hom)) = _
    rw [affineLevelProjection_ker]
    exact hc (m + 1) (l + 1) (by omega) _ (affineLevelProjection_ker Y J F m).ge
  exact ⟨c, fun l h => (hstable l h).trans (hstable (m + c) le_rfl).symm⟩

/-- **Stabilization of the kernel images over an affine Noetherian scheme**, for a quasi-coherent
ideal sheaf rather than an ideal of global sections. On an affine scheme the two are the same
datum, by `AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`. -/
public theorem affineKernelImages_eventuallyConstant_of_idealSheaf (Y : Scheme.{u}) [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : Y.IdealSheafData)
    {F G : CoherentAdicSystems J} (α : F ⟶ G) (m : ℕ) :
    ∃ c : ℕ, ∀ l : ℕ, ∀ h : m + c ≤ l,
      Submodule.map ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (F.obj.map (homOfLE ((Nat.le_add_right m c).trans h)).op)).hom
          (LinearMap.ker ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (α.hom.app (op l))).hom) =
        Submodule.map ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (F.obj.map (homOfLE (Nat.le_add_right m c)).op)).hom
          (LinearMap.ker ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
            (α.hom.app (op (m + c)))).hom) := by
  obtain ⟨J, rfl⟩ := (Scheme.IdealSheafData.equivOfIsAffine (X := Y)).symm.surjective J
  exact affineKernelImages_eventuallyConstant Y J α m

/-! ### Transport to an affine open, and gluing -/

/-- **Stabilization of the kernel images on an affine open.** Let `r : Spec R ⟶ X` be an open
immersion with `R` Noetherian. There is a constant `c` such that for all levels `k, l ≥ m + c`,
*every* morphism between the kernel images at those levels which lies over their inclusions into
`F_m` becomes an isomorphism after restriction along `r`.

The restricted system is a coherent adic system along `ℐ|_{Spec R}`, so the affine case applies
to it and says that the two kernel images have the same range on global sections. A morphism over
the two inclusions is therefore bijective on global sections, hence an isomorphism. -/
public theorem restricted_kernelImages_eventuallyConstant {X : Scheme.{u}} [IsNoetherian X]
    (R : CommRingCat.{u}) [IsNoetherianRing R] (r : Spec R ⟶ X) [IsOpenImmersion r]
    (I : X.IdealSheafData) {F G : CoherentAdicSystems I} (α : F ⟶ G) (m : ℕ) :
    ∃ c : ℕ, ∀ k l : ℕ, ∀ hk : m + c ≤ k, ∀ hl : m + c ≤ l,
      ∀ j : kernelImageAt I α m l ((Nat.le_add_right m c).trans hl) ⟶
          kernelImageAt I α m k ((Nat.le_add_right m c).trans hk),
        j ≫ kernelImageAtIncl I α m k ((Nat.le_add_right m c).trans hk) =
            kernelImageAtIncl I α m l ((Nat.le_add_right m c).trans hl) →
        IsIso ((Scheme.Modules.restrictFunctor r).map j) := by
  let T := Scheme.Modules.restrictFunctor r
  let Ev : (Spec R).Modules ⥤ ModuleCat.{u} Γ(Spec R, ⊤) :=
    SheafOfModules.evaluation (Spec R).ringCatSheaf (op ⊤)
  let E : X.Modules ⥤ ModuleCat.{u} Γ(Spec R, ⊤) := T ⋙ Ev
  have hEvfl : PreservesFiniteLimits Ev :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have hTfl : PreservesFiniteLimits T :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.restrictFunctor r))
  have : PreservesFiniteLimits E := comp_preservesFiniteLimits T Ev
  have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hcohF : ∀ n : ℕ, (F.obj.obj (op n)).IsCoherent := F.property.isCoherent
  have hcohG : ∀ n : ℕ, (G.obj.obj (op n)).IsCoherent := G.property.isCoherent
  have hcohker : ∀ n : ℕ, (kernel (α.hom.app (op n))).IsCoherent := fun n =>
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (α.hom.app (op n))
  have key : ∀ (n : ℕ) (hn : m ≤ n),
      LinearMap.range (E.map (kernelImageAtIncl I α m n hn)).hom =
        Submodule.map (E.map (F.obj.map (homOfLE hn).op)).hom
          (LinearMap.ker (E.map (α.hom.app (op n))).hom) := by
    intro n hn
    exact (range_image_ι_restrict_app_top r _).trans
      (range_map_kernel_ι_comp E (α.hom.app (op n)) (F.obj.map (homOfLE hn).op))
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ∀ l : ℕ, ∀ h : m + c ≤ l,
      Submodule.map (E.map (F.obj.map (homOfLE ((Nat.le_add_right m c).trans h)).op)).hom
          (LinearMap.ker (E.map (α.hom.app (op l))).hom) =
        Submodule.map (E.map (F.obj.map (homOfLE (Nat.le_add_right m c)).op)).hom
          (LinearMap.ker (E.map (α.hom.app (op (m + c)))).hom) := by
    have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_Spec.mpr ‹IsNoetherianRing R›
    have : IsNoetherianRing Γ(Spec R, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec R)⟩
    exact affineKernelImages_eventuallyConstant_of_idealSheaf (Spec R) (I.comap r)
      ((restrictFunctor I r).map α) m
  refine ⟨c, fun k l hk hl j hj => ?_⟩
  have hqc : ∀ (n : ℕ) (hn : m ≤ n), (T.obj (kernelImageAt I α m n hn)).IsQuasicoherent := by
    intro n hn
    have : (kernelImageAt I α m n hn).IsCoherent := isCoherent_image _
    have : (T.obj (kernelImageAt I α m n hn)).IsCoherent :=
      Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion r _
    exact isQuasicoherent_of_isCoherent _
  have hinj : ∀ (n : ℕ) (hn : m ≤ n),
      Function.Injective (E.map (kernelImageAtIncl I α m n hn)).hom := fun n hn =>
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have := hqc l ((Nat.le_add_right m c).trans hl)
  have := hqc k ((Nat.le_add_right m c).trans hk)
  have hr : LinearMap.range
        (E.map (kernelImageAtIncl I α m l ((Nat.le_add_right m c).trans hl))).hom =
      LinearMap.range
        (E.map (kernelImageAtIncl I α m k ((Nat.le_add_right m c).trans hk))).hom := by
    rw [key l ((Nat.le_add_right m c).trans hl), key k ((Nat.le_add_right m c).trans hk),
      hc l hl, hc k hk]
  have hfac : ∀ x, (E.map (kernelImageAtIncl I α m k
        ((Nat.le_add_right m c).trans hk))).hom ((E.map j).hom x) =
      (E.map (kernelImageAtIncl I α m l ((Nat.le_add_right m c).trans hl))).hom x :=
    fun x => congrArg (fun g => ModuleCat.Hom.hom g x)
      ((E.map_comp _ _).symm.trans (congrArg E.map hj))
  have hbij : Function.Bijective (E.map j).hom := by
    refine ⟨fun x y hxy => hinj _ _ ?_, fun y => ?_⟩
    · exact (hfac x).symm.trans
        ((congrArg (E.map (kernelImageAtIncl I α m k
          ((Nat.le_add_right m c).trans hk))).hom hxy).trans (hfac y))
    · obtain ⟨x, hx⟩ : (E.map (kernelImageAtIncl I α m k
          ((Nat.le_add_right m c).trans hk))).hom y ∈ LinearMap.range
          (E.map (kernelImageAtIncl I α m l ((Nat.le_add_right m c).trans hl))).hom :=
        hr ▸ ⟨y, rfl⟩
      exact ⟨x, hinj _ _ ((hfac x).trans hx)⟩
  exact isIso_of_bijective_evaluation_top (T.map j) hbij

/-- **First stabilization in the kernel construction of Tag 087X.** For a morphism `α : F ⟶ G` of
coherent adic systems on a Noetherian scheme and a level `m`, there is a constant `c` such that
for every `l ≥ m + c` the kernel image in `F_m` computed from level `l` agrees with the one
computed from level `m + c`, by an isomorphism commuting with their inclusions into `F_m`.

`Stacks.Coherent.kernelImageAt_hasMap` supplies a morphism from the level `l` kernel image to the
level `m + c` one over `F_m`, and quasi-compactness of `X` provides a finite cover by Noetherian
affines on each of which, past a local constant, such a morphism is invertible; the maximum of
those finitely many constants makes it invertible on the whole cover, hence invertible. -/
public theorem kernelImages_eventuallyConstant {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {F G : CoherentAdicSystems I} (α : F ⟶ G) (m : ℕ) :
    ∃ c : ℕ, ∀ l : ℕ, ∀ h : m + c ≤ l,
      ∃ e : kernelImageAt I α m l ((Nat.le_add_right m c).trans h) ≅
          kernelImageAt I α m (m + c) (Nat.le_add_right m c),
        e.hom ≫ kernelImageAtIncl I α m (m + c) (Nat.le_add_right m c) =
          kernelImageAtIncl I α m l ((Nat.le_add_right m c).trans h) := by
  classical
  let V := X.affineCover.finiteSubcover
  have hlocal : ∀ i : V.I₀, ∃ c : ℕ, ∀ k l : ℕ, ∀ hk : m + c ≤ k, ∀ hl : m + c ≤ l,
      ∀ j : kernelImageAt I α m l ((Nat.le_add_right m c).trans hl) ⟶
          kernelImageAt I α m k ((Nat.le_add_right m c).trans hk),
        j ≫ kernelImageAtIncl I α m k ((Nat.le_add_right m c).trans hk) =
            kernelImageAtIncl I α m l ((Nat.le_add_right m c).trans hl) →
        IsIso ((Scheme.Modules.restrictFunctor (V.f i)).map j) := by
    intro i
    let A : CommRingCat.{u} := X.affineOpenCover.X (X.affineCover.idx i.val)
    have hoi : IsOpenImmersion (show Spec A ⟶ X from V.f i) := V.map_prop i
    have : IsNoetherianRing A :=
      isLocallyNoetherian_Spec.mp (show IsLocallyNoetherian (V.X i) from inferInstance)
    exact restricted_kernelImages_eventuallyConstant A (V.f i) I α m
  choose c hc using hlocal
  let d := Finset.univ.sup c
  have hd (i : V.I₀) : c i ≤ d := Finset.le_sup (f := c) (Finset.mem_univ i)
  refine ⟨d, fun l h => ?_⟩
  obtain ⟨j, hj⟩ := kernelImageAt_hasMap I α m (m + d) l (Nat.le_add_right m d) h
  have : IsIso j :=
    isIso_of_isIso_restrictFunctor_map V j fun i =>
      hc i (m + d) l (by have := hd i; omega) (by have := hd i; omega) j hj
  exact ⟨asIso j, hj⟩

end Stacks.Coherent

end
