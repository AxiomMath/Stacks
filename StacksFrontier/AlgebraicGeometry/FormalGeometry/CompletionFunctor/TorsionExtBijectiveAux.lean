module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeDualGlobal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Abelian

/-!
# Algebraizing a map out of a completion, and the levelwise hypothesis it consumes

Let `X` be a Noetherian scheme and `ℐ` a quasi-coherent sheaf of ideals on `X`. This file
supplies two inputs of the `Ext` comparison of [Stacks, Tag 0EHP].

The first is the *global* form of [Stacks, Tag 0889] part (2): a morphism `α : 𝒢^∧ ⟶ (F_n)` out
of the completion of a coherent module, with levelwise kernels and cokernels annihilated by a
power of `ℐ`, is the completion of a morphism `a : 𝒢 ⟶ ℱ` of coherent `𝒪_X`-modules read through
an isomorphism `β : ℱ^∧ ≅ (F_n)`, with the kernel and cokernel of `a` annihilated by a power of
`ℐ`. This refines `Stacks.Algebraization.essImage_of_map_from_completion`, which gives the
coherent module and the isomorphism but neither the morphism nor the factorization; all three are
glued from the affine theorem.

The second is the hypothesis that part (2) — and part (1) — consume, produced from a short exact
sequence of `Coh(X, ℐ)`: if the quotient of the sequence is annihilated by one power of `ℐ`,
then the levelwise kernels and cokernels of the *monomorphism* are annihilated by a power of
`ℐ`, and dually for the epimorphism when the sub is annihilated. Note that this is a statement
about the levelwise kernels, which are not the kernel of `Coh(X, ℐ)` — that one is a stabilized
image — so it is not formal: it is proved by the standard argument that multiplication by a
section `r` of `ℐ ⁿ` factors two-sidedly through the morphism, which kills its kernel and its
cokernel.

## Main definitions

* `Stacks.Algebraization.restrictedScalar` — multiplication by a section of `𝒪_X` over an open
  `U`, as an endomorphism of the restriction of a sheaf of modules to `U`, and
  `Stacks.Algebraization.restrictedSystemScalar`, the same for a coherent adic system.

## Main results

* `Stacks.Algebraization.restrictedScalar_eq_zero` and
  `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_restrictedScalar_eq_zero` — annihilation
  by `ℐ ⁿ` and the vanishing of those endomorphisms determine one another.
* `Stacks.Algebraization.restrictedScalar_kernel_cokernel_eq_zero` — a two-sided factorization
  of multiplication by `r` through a morphism kills the kernel and the cokernel of that
  morphism.
* `Stacks.Algebraization.exists_restrictedScalar_factorization_f` and
  `Stacks.Algebraization.exists_restrictedScalar_factorization_g` — the factorization exists
  over an affine open, for the monomorphism and for the epimorphism of a short exact sequence
  one of whose ends is annihilated.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_f_of_shortExact` and
  `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_g_of_shortExact` — **the hypothesis
  of Stacks 0889, produced from a short exact sequence.**
* `Stacks.Algebraization.exists_algebraization_of_map_from_completion` — **Stacks 0889 part (2)
  on a Noetherian scheme**, apart from its uniqueness clause.

## Implementation notes

The scalar endomorphism is built by restriction of scalars from `Scheme.Modules.smul`, and its
naturality is `Stacks.Algebraization.smulEnd_naturality` stated at clean types: the sections of
the restriction of `M` to `U` over `V` are the sections of `M` over `U.ι ''ᵁ V` only up to an
unfolding that `rw` will not perform, so the rewriting is done in a separate lemma whose
variables are sections of `M` itself and the result transported by `exact`.

The gluing of Stacks 0889 (2) runs `Stacks.Algebraization.exists_glued_of_localAlgebraizations`
once and feeds its output to both
`Stacks.Algebraization.exists_gluedHom_of_sectionChart` and the chain that
`Stacks.Algebraization.exists_glued_completionIso_of_localAlgebraizations` runs internally, so
that the morphism and the comparison isomorphism are produced for *one and the same* glued
module; that is why the latter is not simply applied.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 0EHP](https://stacks.math.columbia.edu/tag/0EHP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- Two equal morphisms of coherent adic systems have equal components. -/
public theorem systemHom_app_congr {Y : Scheme.{u}} {J : Y.IdealSheafData}
    {A B : Stacks.Coherent.CoherentAdicSystems J} {u v : A ⟶ B} (h : u = v) (k : ℕᵒᵖ) :
    u.hom.app k = v.hom.app k := by rw [h]

/-! ### Multiplication by a section of the structure sheaf -/

/-- Multiplication by a section of `𝒪_X` commutes with the restriction maps of a sheaf of
modules. Stated for two sections matched by the restriction map, which is the shape the
naturality of `Stacks.Algebraization.restrictedScalar` needs. -/
public theorem smulEnd_naturality {X : Scheme.{u}} (M : X.Modules) {A B : X.Opens}
    (g : B ⟶ A) (rA : Γ(X, A)) (rB : Γ(X, B))
    (hr : (X.presheaf.map g.op).hom rA = rB) (x : Γ(M, A)) :
    (M.smul rB).asHom.hom ((M.presheaf.map g.op).hom x) =
      (M.presheaf.map g.op).hom ((M.smul rA).asHom.hom x) := by
  rw [Scheme.Modules.smul_apply, Scheme.Modules.smul_apply, Scheme.Modules.map_smul, hr]

/-- Multiplication by a section `r` of `𝒪_X` over an open `U`, as an endomorphism of the
restriction of a sheaf of modules to `U`. -/
public def restrictedScalar {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U))
    (M : X.Modules) : Scheme.Modules.restrict M U.ι ⟶ Scheme.Modules.restrict M U.ι where
  val.app V := (ModuleCat.restrictScalars (U.ι.appIso V.unop).inv.hom).map
    (ModuleCat.ofHom
      (X.presheaf.map (homOfLE (U.ι_image_le V.unop)).op r •
        (LinearMap.id : Γ(M, U.ι ''ᵁ V.unop) →ₗ[Γ(X, U.ι ''ᵁ V.unop)] _)) :
        M.val.obj (op (U.ι ''ᵁ V.unop)) ⟶ M.val.obj (op (U.ι ''ᵁ V.unop)))
  val.naturality {V W} f := by
    ext x
    change (M.smul (X.presheaf.map (homOfLE (U.ι_image_le W.unop)).op r)).asHom.hom
      (M.presheaf.map (U.ι.opensFunctor.map f.unop).op x) =
      M.presheaf.map (U.ι.opensFunctor.map f.unop).op
        ((M.smul (X.presheaf.map (homOfLE (U.ι_image_le V.unop)).op r)).asHom.hom x)
    exact smulEnd_naturality M ((Scheme.Hom.opensFunctor U.ι).map f.unop) _ _
      (by rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]; rfl) x

/-- Multiplication by a section is natural in the sheaf of modules. -/
public theorem restrictedScalar_naturality {X : Scheme.{u}}
    (U : X.Opens) (r : Γ(X, U)) {M N : X.Modules} (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map f ≫ restrictedScalar U r N =
      restrictedScalar U r M ≫ (Scheme.Modules.restrictFunctor U.ι).map f := by
  ext V x
  exact ((f.val.app (op (U.ι ''ᵁ V))).hom.map_smul _ _).symm

/-! ### Vanishing of multiplication by a section of an annihilating ideal power -/

/-- A section of `ℐ(U) ⁿ` kills every section, over any open inside `U`, of a sheaf of modules
annihilated by `ℐ ⁿ`. -/
public theorem smul_eq_zero_of_idealPowerMultiple_eq_bot_of_le {X : Scheme.{u}}
    {I : X.IdealSheafData} {n : ℕ} {M : X.Modules} (hM : idealPowerMultiple I n M = ⊥)
    (U : X.affineOpens) {r : Γ(X, U.1)} (hr : r ∈ I.ideal U ^ n)
    {A : X.Opens} (hAU : A ≤ U.1) (x : Γ(M, A)) :
    (X.presheaf.map (homOfLE hAU).op).hom r • x = 0 := by
  refine eq_zero_of_affine_cover _ (fun _ : Unit => (⊤ : X.Opens)) (by simp) ?_
  intro W _ hWA _
  have hr' : (X.presheaf.map (homOfLE (hWA.trans hAU)).op).hom r ∈ I.ideal W ^ n := by
    rw [← I.map_ideal (U := W) (V := U) (hWA.trans hAU), ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  have hcomp : (X.presheaf.map (homOfLE hWA).op).hom ((X.presheaf.map (homOfLE hAU).op).hom r) =
      (X.presheaf.map (homOfLE (hWA.trans hAU)).op).hom r := by
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  change (M.presheaf.map (homOfLE hWA).op) _ = 0
  rw [Scheme.Modules.map_smul, hcomp]
  exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot hM W hr' _

/-- Multiplication by a section of `ℐ(U) ⁿ` is the zero endomorphism of the restriction to `U`
of a sheaf of modules annihilated by `ℐ ⁿ`. -/
public theorem restrictedScalar_eq_zero {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) (hM : idealPowerMultiple I n M = ⊥)
    (U : X.affineOpens) (r : Γ(X, U.1)) (hr : r ∈ I.ideal U ^ n) :
    restrictedScalar U.1 r M = 0 := by
  ext V x
  exact smul_eq_zero_of_idealPowerMultiple_eq_bot_of_le hM U hr (U.1.ι_image_le V) x

/-- Conversely, if multiplication by `r` is the zero endomorphism of the restriction to `U` then
`r` kills the sections over `U`: those are the sections of the restriction over the whole of
`U`. -/
public theorem smul_eq_zero_of_restrictedScalar_eq_zero {X : Scheme.{u}}
    (U : X.Opens) (r : Γ(X, U)) (M : X.Modules)
    (h : restrictedScalar U r M = 0) (x : Γ(M, U)) : r • x = 0 := by
  let j : U.ι ''ᵁ ⊤ ⟶ U := homOfLE (U.ι_image_le ⊤)
  have : IsIso j := (eqToIso U.ι_image_top).isIso_hom
  apply (ConcreteCategory.bijective_of_isIso (M.presheaf.map j.op)).1
  have hz := congrArg (fun f : Scheme.Modules.restrict M U.ι ⟶ Scheme.Modules.restrict M U.ι =>
    (f.val.app (op ⊤)).hom (M.presheaf.map j.op x)) h
  change (X.presheaf.map j.op).hom r • (M.presheaf.map j.op) x = 0 at hz
  rwa [Scheme.Modules.map_smul, map_zero]

/-- Annihilation by `ℐ ⁿ` may be checked by the vanishing of multiplication by the sections of
`ℐ(U) ⁿ` over the affine opens `U`. -/
public theorem idealPowerMultiple_eq_bot_of_restrictedScalar_eq_zero {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (h : ∀ (U : X.affineOpens) (r : Γ(X, U.1)), r ∈ I.ideal U ^ n →
      restrictedScalar U.1 r M = 0) :
    idealPowerMultiple I n M = ⊥ :=
  idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U _ hr x =>
    smul_eq_zero_of_restrictedScalar_eq_zero U.1 _ M (h U _ hr) x

/-- **A two-sided factorization of multiplication by `r` through a morphism kills the kernel and
the cokernel of that morphism.** -/
public theorem restrictedScalar_kernel_cokernel_eq_zero {X : Scheme.{u}}
    (U : X.Opens) (r : Γ(X, U)) {M N : X.Modules} (f : M ⟶ N)
    (b : Scheme.Modules.restrict N U.ι ⟶ Scheme.Modules.restrict M U.ι)
    (hb : b ≫ (Scheme.Modules.restrictFunctor U.ι).map f = restrictedScalar U r N)
    (hb' : (Scheme.Modules.restrictFunctor U.ι).map f ≫ b = restrictedScalar U r M) :
    restrictedScalar U r (kernel f) = 0 ∧ restrictedScalar U r (cokernel f) = 0 := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have : R.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  have : PreservesColimits R := by infer_instance
  have hfl : PreservesFiniteLimits R :=
    AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor U.ι
  have hpl : PreservesLimitsOfShape WalkingParallelPair R := hfl.preservesFiniteLimits _
  have : Mono (R.map (kernel.ι f)) := by
    have hk : (PreservesKernel.iso R f).hom ≫ kernel.ι (R.map f) = R.map (kernel.ι f) := by
      simp [PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rw [← hk]
    infer_instance
  constructor
  · apply (cancel_mono (R.map (kernel.ι f))).mp
    rw [zero_comp, ← restrictedScalar_naturality, ← hb', ← Category.assoc,
      ← R.map_comp, kernel.condition, R.map_zero, zero_comp]
  · apply (cancel_epi (R.map (cokernel.π f))).mp
    rw [comp_zero, restrictedScalar_naturality, ← hb, Category.assoc,
      ← R.map_comp, cokernel.condition, R.map_zero, comp_zero]

/-! ### Multiplication by a section on a coherent adic system -/

/-- Multiplication by a section `r` of `𝒪_X` over `U`, as an endomorphism of the restriction of a
coherent adic system to `U`. -/
public def restrictedSystemScalar {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (U : X.Opens) (r : Γ(X, U)) (M : Stacks.Coherent.CoherentAdicSystems I) :
    (Stacks.Coherent.restrictFunctor I U.ι).obj M ⟶
      (Stacks.Coherent.restrictFunctor I U.ι).obj M :=
  ObjectProperty.homMk
    { app k := restrictedScalar U r (M.obj.obj k)
      naturality := fun _ _ f => restrictedScalar_naturality U r (M.obj.map f) }

/-- Multiplication by a section is natural in the coherent adic system. -/
public theorem restrictedSystemScalar_naturality {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) (r : Γ(X, U))
    {M N : Stacks.Coherent.CoherentAdicSystems I} (f : M ⟶ N) :
    (Stacks.Coherent.restrictFunctor I U.ι).map f ≫ restrictedSystemScalar I U r N =
      restrictedSystemScalar I U r M ≫ (Stacks.Coherent.restrictFunctor I U.ι).map f :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun k =>
    restrictedScalar_naturality U r (f.hom.app k)))

/-- Multiplication by a section of `ℐ(U) ⁿ` is zero on a system every term of which is
annihilated by `ℐ ⁿ`. -/
public theorem restrictedSystemScalar_eq_zero {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) (M : Stacks.Coherent.CoherentAdicSystems I)
    (hM : ∀ k : ℕ, idealPowerMultiple I n (M.obj.obj (op k)) = ⊥)
    (U : X.affineOpens) (r : Γ(X, U.1)) (hr : r ∈ I.ideal U ^ n) :
    restrictedSystemScalar I U.1 r M = 0 :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun k =>
    restrictedScalar_eq_zero I n _ (hM k.unop) U r hr))

/-! ### Levelwise annihilation from a short exact sequence -/

section ShortExact

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
  (S : ShortComplex (Stacks.Coherent.CoherentAdicSystems I))

/-- An open subscheme of a Noetherian scheme is Noetherian. -/
private theorem isNoetherian_toScheme_opens (U : X.Opens) : IsNoetherian U.toScheme := by
  let : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  let : CompactSpace U := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (U : Set X))
  exact (isNoetherian_iff U.toScheme).2 ⟨inferInstance, inferInstance⟩

/-- Restriction to a Noetherian open subscheme preserves short exact sequences of coherent adic
systems. -/
private theorem shortExact_map_restrictFunctor (hS : S.ShortExact) (U : X.Opens)
    [IsNoetherian U.toScheme] : (S.map (Stacks.Coherent.restrictFunctor I U.ι)).ShortExact := by
  have hex := Stacks.Coherent.restrictFunctor_exact I U.ι
  let := hex.1
  let := hex.2
  let : (Stacks.Coherent.restrictFunctor I U.ι).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact hS.map_of_exact (Stacks.Coherent.restrictFunctor I U.ι)

/-- If multiplication by every section of `ℐ(U) ⁿ` over an affine open `U` factors two-sidedly
through `φ`, then the levelwise kernels and cokernels of `φ` are annihilated by `ℐ ⁿ`. -/
private theorem isKernelCokernelAnnihilatedByPower_of_factorization
    {A B : Stacks.Coherent.CoherentAdicSystems I} (φ : A ⟶ B) {n : ℕ} (hn : 0 < n)
    (h : ∀ (U : X.affineOpens) (r : Γ(X, U.1)), r ∈ I.ideal U ^ n →
      ∃ b : (Stacks.Coherent.restrictFunctor I U.1.ι).obj B ⟶
          (Stacks.Coherent.restrictFunctor I U.1.ι).obj A,
        b ≫ (Stacks.Coherent.restrictFunctor I U.1.ι).map φ =
            restrictedSystemScalar I U.1 r B ∧
          (Stacks.Coherent.restrictFunctor I U.1.ι).map φ ≫ b =
            restrictedSystemScalar I U.1 r A) :
    IsKernelCokernelAnnihilatedByPower I φ.hom := by
  refine ⟨n, hn, fun k => ?_⟩
  have hboth : ∀ (U : X.affineOpens) (r : Γ(X, U.1)), r ∈ I.ideal U ^ n →
      restrictedScalar U.1 r (kernel (C := X.Modules) (φ.hom.app (op k))) = 0 ∧
        restrictedScalar U.1 r (cokernel (C := X.Modules) (φ.hom.app (op k))) = 0 := by
    intro U r hr
    obtain ⟨b, hb, hb'⟩ := h U r hr
    exact restrictedScalar_kernel_cokernel_eq_zero U.1 r (φ.hom.app (op k)) (b.hom.app (op k))
      (systemHom_app_congr hb (op k)) (systemHom_app_congr hb' (op k))
  exact ⟨idealPowerMultiple_eq_bot_of_restrictedScalar_eq_zero I _ _
      fun U r hr => (hboth U r hr).1,
    idealPowerMultiple_eq_bot_of_restrictedScalar_eq_zero I _ _
      fun U r hr => (hboth U r hr).2⟩

/-- **Over an affine open, multiplication by a section of `ℐ ⁿ` factors two-sidedly through the
monomorphism of a short exact sequence whose quotient is annihilated by `ℐ ⁿ`.** Restriction to
an open subscheme is exact, so the restricted sequence is still short exact there; multiplication
by `r` kills the quotient, hence factors through the kernel of the second map, which is the
first. -/
public theorem exists_restrictedScalar_factorization_f (hS : S.ShortExact) (n : ℕ)
    (hF : ∀ k : ℕ, idealPowerMultiple I n (S.X₃.obj.obj (op k)) = ⊥)
    (U : X.affineOpens) (r : Γ(X, U.1)) (hr : r ∈ I.ideal U ^ n) :
    ∃ b : (Stacks.Coherent.restrictFunctor I U.1.ι).obj S.X₂ ⟶
        (Stacks.Coherent.restrictFunctor I U.1.ι).obj S.X₁,
      b ≫ (Stacks.Coherent.restrictFunctor I U.1.ι).map S.f =
          restrictedSystemScalar I U.1 r S.X₂ ∧
        (Stacks.Coherent.restrictFunctor I U.1.ι).map S.f ≫ b =
          restrictedSystemScalar I U.1 r S.X₁ := by
  have := isNoetherian_toScheme_opens U.1
  have hT := shortExact_map_restrictFunctor I S hS U.1
  have hw : restrictedSystemScalar I U.1 r S.X₂ ≫
      (Stacks.Coherent.restrictFunctor I U.1.ι).map S.g = 0 := by
    rw [← restrictedSystemScalar_naturality,
      restrictedSystemScalar_eq_zero I n S.X₃ hF U r hr, comp_zero]
  obtain ⟨b, hb0⟩ := KernelFork.IsLimit.lift' hT.fIsKernel _ hw
  have hb : b ≫ (Stacks.Coherent.restrictFunctor I U.1.ι).map S.f =
      restrictedSystemScalar I U.1 r S.X₂ := hb0
  refine ⟨b, hb, ?_⟩
  let : Mono ((Stacks.Coherent.restrictFunctor I U.1.ι).map S.f) := hT.mono_f
  refine (cancel_mono ((Stacks.Coherent.restrictFunctor I U.1.ι).map S.f)).mp ?_
  rw [Category.assoc, hb]
  exact restrictedSystemScalar_naturality I U.1 r S.f

/-- The companion of `Stacks.Algebraization.exists_restrictedScalar_factorization_f` for the
epimorphism of a short exact sequence whose sub is annihilated by `ℐ ⁿ`. -/
public theorem exists_restrictedScalar_factorization_g (hS : S.ShortExact) (n : ℕ)
    (hF : ∀ k : ℕ, idealPowerMultiple I n (S.X₁.obj.obj (op k)) = ⊥)
    (U : X.affineOpens) (r : Γ(X, U.1)) (hr : r ∈ I.ideal U ^ n) :
    ∃ b : (Stacks.Coherent.restrictFunctor I U.1.ι).obj S.X₃ ⟶
        (Stacks.Coherent.restrictFunctor I U.1.ι).obj S.X₂,
      b ≫ (Stacks.Coherent.restrictFunctor I U.1.ι).map S.g =
          restrictedSystemScalar I U.1 r S.X₃ ∧
        (Stacks.Coherent.restrictFunctor I U.1.ι).map S.g ≫ b =
          restrictedSystemScalar I U.1 r S.X₂ := by
  have := isNoetherian_toScheme_opens U.1
  have hT := shortExact_map_restrictFunctor I S hS U.1
  have hw : (Stacks.Coherent.restrictFunctor I U.1.ι).map S.f ≫
      restrictedSystemScalar I U.1 r S.X₂ = 0 := by
    rw [restrictedSystemScalar_naturality,
      restrictedSystemScalar_eq_zero I n S.X₁ hF U r hr, zero_comp]
  obtain ⟨b, hb0⟩ := CokernelCofork.IsColimit.desc' hT.gIsCokernel _ hw
  have hb : (Stacks.Coherent.restrictFunctor I U.1.ι).map S.g ≫ b =
      restrictedSystemScalar I U.1 r S.X₂ := hb0
  refine ⟨b, ?_, hb⟩
  let : Epi ((Stacks.Coherent.restrictFunctor I U.1.ι).map S.g) := hT.epi_g
  refine (cancel_epi ((Stacks.Coherent.restrictFunctor I U.1.ι).map S.g)).mp ?_
  rw [← Category.assoc, hb]
  exact (restrictedSystemScalar_naturality I U.1 r S.g).symm

/-- **The levelwise kernels and cokernels of the monomorphism of a short exact sequence of
coherent adic systems are annihilated by a power of `ℐ` as soon as the quotient is.** This is
the hypothesis of Stacks 0889 for that monomorphism. -/
public theorem isKernelCokernelAnnihilatedByPower_f_of_shortExact (hS : S.ShortExact)
    (hF : IsSystemPowerAnnihilated I S.X₃.obj) :
    IsKernelCokernelAnnihilatedByPower I S.f.hom := by
  obtain ⟨n, hn⟩ := hF
  exact isKernelCokernelAnnihilatedByPower_of_factorization I S.f (lt_of_lt_of_le Nat.zero_lt_one
    (le_max_left 1 n)) (exists_restrictedScalar_factorization_f I S hS (max 1 n)
    fun k => idealPowerMultiple_eq_bot_of_le (hn k) (le_max_right 1 n))

/-- **The levelwise kernels and cokernels of the epimorphism of a short exact sequence of
coherent adic systems are annihilated by a power of `ℐ` as soon as the sub is.** -/
public theorem isKernelCokernelAnnihilatedByPower_g_of_shortExact (hS : S.ShortExact)
    (hF : IsSystemPowerAnnihilated I S.X₁.obj) :
    IsKernelCokernelAnnihilatedByPower I S.g.hom := by
  obtain ⟨n, hn⟩ := hF
  exact isKernelCokernelAnnihilatedByPower_of_factorization I S.g (lt_of_lt_of_le Nat.zero_lt_one
    (le_max_left 1 n)) (exists_restrictedScalar_factorization_g I S hS (max 1 n)
    fun k => idealPowerMultiple_eq_bot_of_le (hn k) (le_max_right 1 n))

end ShortExact

/-- **Stacks 0889 part (2) on a Noetherian scheme.** A morphism `α : 𝒢^∧ ⟶ (F_n)` out of a
completion whose levelwise kernels and cokernels are annihilated by a power of `ℐ` is the
completion of a morphism `a : 𝒢 ⟶ ℱ` of coherent `𝒪_X`-modules, whose own kernel and cokernel
are annihilated by a power of `ℐ`, read through an isomorphism `β : ℱ^∧ ≅ (F_n)`.

Over each affine open the affine theorem
`Stacks.Algebraization.exists_local_algebraization_dual` provides such a datum;
`Stacks.Algebraization.exists_glued_of_localAlgebraizations` glues the coherent module,
`Stacks.Algebraization.exists_gluedHom_of_sectionChart` glues the morphism out of `𝒢`, and
`Stacks.Coherent.existsUnique_coherentSystemIso_of_affineComparison` glues the comparison of its
completion with the given system. The factorization is checked after restricting to each chart,
where it is the chart's own factorization read through
`Stacks.Algebraization.completionRestrictOpenIso_inv_naturality`, and the annihilation of the
kernel and the cokernel is the chart's, made uniform by
`Stacks.Algebraization.isPowerAnnihilated_of_restrict`. -/
public theorem exists_algebraization_of_map_from_completion {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : G ⟶ F)
      (β : (completionFunctor X I).obj F ≅ Fsys),
      IsPowerAnnihilated I (kernel (C := X.Modules) a.hom) ∧
        IsPowerAnnihilated I (cokernel (C := X.Modules) a.hom) ∧
        α = ((completionFunctor X I).map a).hom ≫ β.hom.hom := by
  choose F b β h using fun i : X.affineOpens =>
    exists_local_algebraization_dual I G Fsys α hα i
  obtain ⟨M, d, c, ⟨-, hcoh⟩, hd₁, hd₂, hcres, hchart⟩ :=
    exists_glued_of_localAlgebraizations I G Fsys α F b β (fun i => (h i).1)
      (fun i => (h i).2.1) fun i => (h i).2.2
  choose chart hchartApp using fun i : X.affineOpens =>
    exists_chartIso_of_appEquiv i.1 hcoh (F i) (fun V hV => c i V hV)
      (fun V W hV hWV s => hcres i V W hV hWV s)
  obtain ⟨φ, hφ⟩ := exists_gluedHom_of_sectionChart G M F b d c hd₁ hcres hchart
  -- the glued comparison of the completion of `M` with the given system
  have hA : ∀ (i : X.affineOpens) (V : X.Opens) (hV : V ≤ i.1) (s : Γ(M, V)),
      Stacks.Coherent.localAppOpen i.1 (pushforwardChartMap (chart i).hom) hV s =
        c i V hV s := hchartApp
  have hsec : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
      Stacks.Coherent.localAppOpen i.1 (pushforwardChartMap (chart i).hom) hki ≫
          Stacks.Coherent.localAppOpen k.1
            (overlapRestrictIso hki hkj (d k i j hki hkj)).hom le_rfl =
        Stacks.Coherent.localAppOpen j.1 (pushforwardChartMap (chart j).hom) hkj := by
    intro k i j hki hkj
    ext s
    refine Eq.trans (congrArg (fun z => Stacks.Coherent.localAppOpen k.1
        (overlapRestrictIso hki hkj (d k i j hki hkj)).hom le_rfl z) (hA i k.1 hki s)) ?_
    exact (hchart k i j hki hkj s).symm.trans (hA j k.1 hkj s).symm
  have hdres : ∀ (k l i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1)
      (hlk : l.1 ≤ k.1),
      Stacks.Coherent.localAppOpen l.1
          (overlapRestrictIso (hlk.trans hki) (hlk.trans hkj)
            (d l i j (hlk.trans hki) (hlk.trans hkj))).hom le_rfl =
        Stacks.Coherent.localAppOpen k.1
          (overlapRestrictIso hki hkj (d k i j hki hkj)).hom hlk :=
    fun k l i j hki hkj hlk =>
      localAppOpen_overlapRestrictIso_restrict I G Fsys α l hki hkj hlk (b i) (b j) (β i)
        (β j) (h i).1 (h j).1 (h i).2.1 (h i).2.2 (h j).2.1 (h j).2.2 (d k i j hki hkj)
        (hd₁ k i j hki hkj) (hd₂ k i j hki hkj)
        (d l i j (hlk.trans hki) (hlk.trans hkj))
        (hd₁ l i j (hlk.trans hki) (hlk.trans hkj))
        (hd₂ l i j (hlk.trans hki) (hlk.trans hkj))
  have hd₁' : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
      restrictedAlgebraizationMapOfLE hki (chart i).hom ≫ (d k i j hki hkj).hom =
        restrictedAlgebraizationMapOfLE hkj (chart j).hom :=
    fun k i j hki hkj =>
      chartIso_comp_overlapComparison (fun i => (chart i).hom) d hsec hdres k i j hki hkj
  obtain ⟨e, he, -⟩ := Stacks.Coherent.existsUnique_coherentSystemIso_of_affineComparison I
    (fun i : X.affineOpens => i.1) (iSup_affineOpens_eq_top X)
    (S := (completionFunctor X I).obj ⟨M, hcoh⟩) (T := Fsys)
    (fun i => completionRestrictChartIso I i.1 ⟨M, hcoh⟩ Fsys (F i) (chart i) (β i))
    (fun i j n k hki hkj => localAppOpen_completionRestrictChartIso_overlap I Fsys hki hkj
      (chart i) (chart j) (β i) (β j) (d k i j hki hkj) (hd₁' k i j hki hkj)
      (hd₂ k i j hki hkj) n.unop)
  set a : G ⟶ (⟨M, hcoh⟩ : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :=
    ObjectProperty.homMk φ with ha
  -- over each chart the glued morphism is the chart's own algebraization
  have hchartb : ∀ i : X.affineOpens,
      restrictCoherentModulesMap i.1.ι a ≫ (chart i).hom = b i := by
    intro i
    have key : (Scheme.Modules.restrictFunctor i.1.ι).map φ ≫
        pushforwardChartMap (chart i).hom = pushforwardChartMap (b i) := by
      refine restrictHom_ext_of_localAppOpen i.1 _ _ fun V hV => ?_
      ext s
      refine Eq.trans (localAppOpen_comp_apply i.1
        ((Scheme.Modules.restrictFunctor i.1.ι).map φ)
        (pushforwardChartMap (chart i).hom) hV s).symm ?_
      refine Eq.trans (congrArg (fun z => Stacks.Coherent.localAppOpen i.1
          (pushforwardChartMap (chart i).hom) hV z)
        (congrArg (fun z => z s)
          (Stacks.Coherent.localAppOpen_restrictFunctor_map i.1 φ hV))) ?_
      refine Eq.trans (hA i V hV _) ?_
      refine Eq.trans (congrArg (fun z => c i V hV z) (hφ i V hV s)) ?_
      exact (c i V hV).apply_symm_apply _
    refine ObjectProperty.hom_ext _ ?_
    refine (cancel_mono
      (((Scheme.Modules.restrictFunctorAdjCounitIso i.1.ι).app (F i).obj).inv)).1 ?_
    exact (Category.assoc _ _ _).trans key
  -- the two kernel/cokernel comparisons over a chart
  have hbhom : ∀ i : X.affineOpens, (b i).hom =
      (restrictCoherentModulesMap i.1.ι a).hom ≫ (chart i).hom.hom := by
    intro i
    rw [← hchartb i]
    rfl
  refine ⟨⟨M, hcoh⟩, a, e, ?_, ?_, ?_⟩
  · refine isPowerAnnihilated_of_restrict I _ fun U => ?_
    obtain ⟨t, ht⟩ := (h U).2.1
    have : IsIso ((chart U).hom.hom) :=
      inferInstanceAs (IsIso (Stacks.underlyingObjIso (chart U)).hom)
    refine ⟨t, idealPowerMultiple_eq_bot_of_iso (I.comap U.1.ι)
      (PreservesKernel.iso (Scheme.Modules.restrictFunctor U.1.ι) a.hom ≪≫
        (kernelIsoOfEq (hbhom U) ≪≫ kernelCompMono _ ((chart U).hom.hom)).symm) t ht⟩
  · refine isPowerAnnihilated_of_restrict I _ fun U => ?_
    obtain ⟨t, ht⟩ := (h U).2.2
    have : IsIso ((chart U).hom.hom) :=
      inferInstanceAs (IsIso (Stacks.underlyingObjIso (chart U)).hom)
    refine ⟨t, idealPowerMultiple_eq_bot_of_iso (I.comap U.1.ι)
      (PreservesCokernel.iso (Scheme.Modules.restrictFunctor U.1.ι) a.hom ≪≫
        (cokernelIsoOfEq (hbhom U) ≪≫ cokernelCompIsIso _ ((chart U).hom.hom)).symm) t ht⟩
  · have hres' : ∀ i : X.affineOpens,
        restrictedSystemMapDual i.1.ι I G Fsys α =
          restrictedSystemMapDual i.1.ι I G Fsys
            (((completionFunctor X I).map a).hom ≫ e.hom.hom) := by
      intro i
      have hw : Functor.whiskerRight e.hom.hom (Scheme.Modules.restrictFunctor i.1.ι) =
          (completionRestrictOpenIso i.1.ι I ⟨M, hcoh⟩).hom ≫
            ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map (chart i).hom).hom ≫
              (β i).hom :=
        congrArg (fun z : (Stacks.Coherent.restrictFunctor I i.1.ι).obj
            ((completionFunctor X I).obj ⟨M, hcoh⟩) ⟶
            (Stacks.Coherent.restrictFunctor I i.1.ι).obj Fsys => z.hom) (he i)
      have step1 : (completionRestrictOpenIso i.1.ι I G).inv ≫
            Functor.whiskerRight (((completionFunctor X I).map a).hom ≫ e.hom.hom)
              (Scheme.Modules.restrictFunctor i.1.ι) =
          ((completionRestrictOpenIso i.1.ι I G).inv ≫
            Functor.whiskerRight ((completionFunctor X I).map a).hom
              (Scheme.Modules.restrictFunctor i.1.ι)) ≫
            Functor.whiskerRight e.hom.hom (Scheme.Modules.restrictFunctor i.1.ι) :=
        (congrArg (fun z => (completionRestrictOpenIso i.1.ι I G).inv ≫ z)
          (Functor.whiskerRight_comp _ _ _)).trans (Category.assoc _ _ _).symm
      have step2 : ((completionRestrictOpenIso i.1.ι I G).inv ≫
            Functor.whiskerRight ((completionFunctor X I).map a).hom
              (Scheme.Modules.restrictFunctor i.1.ι)) ≫
            Functor.whiskerRight e.hom.hom (Scheme.Modules.restrictFunctor i.1.ι) =
          ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map
              (restrictCoherentModulesMap i.1.ι a)).hom ≫
            ((completionRestrictOpenIso i.1.ι I ⟨M, hcoh⟩).inv ≫
              Functor.whiskerRight e.hom.hom (Scheme.Modules.restrictFunctor i.1.ι)) :=
        (congrArg (fun z => z ≫ Functor.whiskerRight e.hom.hom
            (Scheme.Modules.restrictFunctor i.1.ι))
          (completionRestrictOpenIso_inv_naturality i.1.ι I a)).trans (Category.assoc _ _ _)
      have step3 : (completionRestrictOpenIso i.1.ι I ⟨M, hcoh⟩).inv ≫
            Functor.whiskerRight e.hom.hom (Scheme.Modules.restrictFunctor i.1.ι) =
          ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map (chart i).hom).hom ≫
            (β i).hom :=
        (congrArg (fun z => (completionRestrictOpenIso i.1.ι I ⟨M, hcoh⟩).inv ≫ z) hw).trans
          (Iso.inv_hom_id_assoc _ _)
      have step4 : ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map
              (restrictCoherentModulesMap i.1.ι a)).hom ≫
            (((completionFunctor i.1.toScheme (I.comap i.1.ι)).map (chart i).hom).hom ≫
              (β i).hom) =
          ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map (b i)).hom ≫ (β i).hom := by
        refine (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ (β i).hom) ?_)
        rw [← hchartb i]
        exact congrArg (fun z => z.hom)
          (((completionFunctor i.1.toScheme (I.comap i.1.ι)).map_comp _ _)).symm
      exact ((h i).1).trans
        ((step1.trans (step2.trans ((congrArg (fun z =>
          ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map
            (restrictCoherentModulesMap i.1.ι a)).hom ≫ z) step3).trans step4))).symm)
    have hres : ∀ i : X.affineOpens,
        Functor.whiskerRight α (Scheme.Modules.restrictFunctor i.1.ι) =
          Functor.whiskerRight (((completionFunctor X I).map a).hom ≫ e.hom.hom)
            (Scheme.Modules.restrictFunctor i.1.ι) := by
      intro i
      have hcancel : (completionRestrictOpenIso i.1.ι I G).inv ≫
            Functor.whiskerRight α (Scheme.Modules.restrictFunctor i.1.ι) =
          (completionRestrictOpenIso i.1.ι I G).inv ≫
            Functor.whiskerRight (((completionFunctor X I).map a).hom ≫ e.hom.hom)
              (Scheme.Modules.restrictFunctor i.1.ι) := hres' i
      exact (cancel_epi _).1 hcancel
    refine NatTrans.ext (funext fun n => ?_)
    refine Stacks.Coherent.hom_ext_of_restrictCover (fun i : X.affineOpens => i.1.ι) ?_ _ _
      fun i => ?_
    · simp only [Scheme.Opens.ι_image_top]
      exact iSup_affineOpens_eq_top X
    · exact congrArg (fun z => NatTrans.app z n) (hres i)

end Stacks.Algebraization

end
