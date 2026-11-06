module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedSheafFunctor
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Characterizations
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.AffineBaseChangeModule

/-!
# An adequate module is locally a kernel of associated quasi-coherent modules

This module proves the converse half of [Stacks, Tag 06VK]: the implication (1) ⇒ (5), that an
adequate `𝒪`-module on the big `τ`-site over `S` restricts, over *every* affine scheme of the
site over `S`, to the kernel of a map `𝓖ᵃ ⟶ 𝓗ᵃ` of the associated modules of two quasi-coherent
modules; and with it the implications (1) ⇒ (2) and (1) ⇒ (3), which follow by the already
proved chain (5) ⇒ (2) ⇒ (3) of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Characterizations.lean`. Together with
the known implications to adequacy this closes the equivalence of all five conditions of the
source with no hypotheses.

## The argument

Fix an affine `Spec A` of the site over `S` by `f : Spec A ⟶ S` and work on the big `τ`-site
`B'` over `Spec A` obtained from `B` by base change. Write `𝓖 = f^*𝓕` for the restriction of
`𝓕`, and `T` for the affine-section functor of `B'` at `A` and the *identity* structure
morphism.

* `T` is **fully faithful**, by
  `Stacks.Adequate.fullyFaithfulAffineSectionsFunctor`, and preserves kernels, by
  `Stacks.Adequate.affineSectionsFunctor_preservesFiniteLimits`. So to exhibit `𝓖` as a kernel
  on `B'` it is enough to exhibit `T 𝓖` as a kernel of a map between objects in the image of
  `T`.
* `T 𝓖` **is** a kernel of a map of module extensions: `T 𝓖 = F_{𝓕, A}` by
  `Stacks.Adequate.affineSectionFunctor_pullbackSheaf`, and that functor is adequate by
  [Stacks, Tag 06VI], `Stacks.Adequate.isAdequate_affineSectionFunctor`, which is itself
  unconditional. Adequacy gives `A`-modules `M`, `N` and a map `φ : M ⟶ N` with
  `F_{𝓕, A} ≅ Ker(C ↦ C ⊗_A M → C ⊗_A N)`.
* The module extension of `M` **is** in the image of `T`: take `𝓖 = M^~`, the quasi-coherent
  `𝒪_{Spec A}`-module of `AlgebraicGeometry.tilde`. Then `T (M^~)ᵃ` is the module extension of
  the sections of `(M^~)ᵃ` over the base affine, by
  `Stacks.Adequate.affineSectionsCompare` and `Stacks.Adequate.isIso_affineSectionsCompare`, and
  those sections are `M`: the structure morphism of the base object of the site over `Spec A` is
  the identity, so the pullback along it does nothing, and `Γ(Spec A, M^~) = M`.

Throughout, `(M^~)ᵃ` is written `(Stacks.Adequate.associatedTilde B).obj M`, the value of the
functor `M ↦ (M^~)ᵃ` of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedSheafFunctor.lean`, which is
also where the hypothesis-free sheaf condition `Stacks.Adequate.isSheaf_associatedPresheaf` that
makes it available is proved. Only the values of that functor are used here, never its action on
morphisms.

Nothing here passes through the quasi-inverse of the equivalence of [Stacks, Tag 06ZJ], which
the module documentation of `Characterizations.lean` recorded as the obstruction. What that
quasi-inverse would construct is a sheaf from an *arbitrary* adequate module-valued functor; all
that is needed here is a sheaf whose affine sections are a *module extension*, and `M^~` is one
— the comparison functor of Tag 06ZJ is not inverted, only evaluated on the image of
`AlgebraicGeometry.tilde`.

## Main results

* `Stacks.Adequate.nonempty_baseSectionsTildeIso` — the sections of `(M^~)ᵃ` over the base
  affine of a chosen big site over `Spec A` are `M`, as `A`-modules.
* `Stacks.Adequate.isAssociatedKernel_of_isAdequate` — **an adequate `𝒪`-module on a chosen big
  site over an affine base is the kernel of a map of associated quasi-coherent modules**, with
  no hypotheses. This is the local form of the implication (1) ⇒ (5).
* `Stacks.Adequate.hasAssociatedKernelOnEveryAffine_of_isAdequate` — **[Stacks, Tag 06VK], the
  implication (1) ⇒ (5)**, and
  `Stacks.Adequate.hasAffineOpenAssociatedKernelCover_of_isAdequate`,
  `Stacks.Adequate.hasCoveringAssociatedKernel_of_isAdequate` — **the implications (1) ⇒ (2) and
  (1) ⇒ (3)**.
* `Stacks.Adequate.exists_mono_into_associatedModule_of_isAdequate` — the same conclusion in the
  shape [Stacks, Tag 06ZR] consumes it: an adequate `𝒪`-module over an affine base admits a
  **monomorphism** into the associated module of a quasi-coherent module, namely the inclusion
  of the kernel.
* `Stacks.Adequate.isAdequate_iff_hasAssociatedKernelOnEveryAffine`,
  `Stacks.Adequate.isAdequate_iff_hasAffineOpenAssociatedKernelCover` and
  `Stacks.Adequate.isAdequate_iff_hasCoveringAssociatedKernel` — the resulting equivalences of
  condition (1) with conditions (5), (2) and (3), each with no hypotheses.

## Implementation notes

**Why the sections of `(M^~)ᵃ` over the base affine are computed in two stages.** The base
object of a chosen big site over `Spec A` is the spectrum of `A` *as an `A`-algebra of the
site*, and its structure morphism is `Spec` of the identity algebra map composed with the
identity of `Spec A`; `Stacks.Adequate.base_overOfAlg_hom` identifies it with `𝟙 (Spec A)`. The
sections of `(M^~)ᵃ` there are therefore the global sections of a pullback along a morphism which
is equal — but not syntactically equal — to an identity, and the module structures on the two
spellings are found by typeclass synthesis from the syntactic form. So the computation is done
once, in `Stacks.Adequate.exists_tildePullbackAddEquiv`, for a *variable* morphism assumed equal
to the identity, where `subst` makes every instance the clean one; and the result is transported
into the affine-section spelling exactly once, in
`Stacks.Adequate.nonempty_baseSectionsTildeIso`, by the bridge
`Stacks.Adequate.affineBaseSections_smul_eq`. This is the discipline recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedAffineSections.lean`, and the
same holds here: each stage is milliseconds, and a direct `rw` across the two
spellings does not find its pattern.

**Why the final assembly is split.** `Stacks.Adequate.preimageKernelIso` and
`Stacks.Adequate.associatedTildeKernelPresentation` state their steps with the sheaves, the map
and the kernel presentation all *variable*. Both are then instantiated by application. With
the module extension of `M` and the associated module of `M^~` substituted into one term
instead, the declaration elaborates but the kernel does not typecheck it inside its budget,
because the `HasKernel` instance of the assembled morphism has to be reconciled with the one of
the abstract morphism. Keeping each step abstract and applying it is the cheap shape.

## References

* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace Stacks.Adequate

/-! ### The global sections of a pullback along the identity -/

/-- Restricting a global section to the whole space is the identity. -/
private alias sectionsMap_leTop_top := AlgebraicGeometry.BigAffineFppf.map_leTop_top

/-- On the global sections of a module on `Spec R` the action of `R` is the action of the global
functions through `AlgebraicGeometry.Scheme.ΓSpecIso`. This is Mathlib's
`AlgebraicGeometry.Scheme.Modules.smul_Spec_def` at the full open, where the restriction map it
carries is the identity. -/
private theorem smul_sections_top {R : CommRingCat.{u}} {N : (Spec R).Modules} (a : ↥R)
    (x : Γ(N, ⊤)) :
    a • x = (Scheme.ΓSpecIso R).inv a • x := by
  rw [Scheme.Modules.smul_Spec_def, sectionsMap_leTop_top]

/-- **The global sections of the pullback of `M^~` along a morphism equal to the identity are
`M`.** The additive bijection is `AlgebraicGeometry.tilde.isoTop` followed by the sections of
`AlgebraicGeometry.pullbackIdIso`, and the stated compatibility says it carries the action of
the base ring to the action of the global functions.

The morphism is a variable assumed *equal* to the identity rather than the identity itself: at
the intended use it is the structure morphism of the base object of a big site over `Spec A`,
which is `Spec` of the identity algebra map composed with an identity and is therefore only
propositionally an identity. With the morphism variable, `subst` puts every module instance in
this statement into the clean spelling; see the module documentation. -/
public theorem exists_tildePullbackAddEquiv (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (k : Spec R ⟶ Spec R) (hk : k = 𝟙 (Spec R)) :
    ∃ θ : ↥M ≃+ (Γ((Scheme.Modules.pullback k).obj (tilde M), ⊤) : Type u),
      ∀ (a : ↥R) (m : ↥M), θ (a • m) = (Scheme.ΓSpecIso R).inv a • θ m := by
  subst hk
  let e := (AlgebraicGeometry.sectionsLinearEquivOfIso
    (AlgebraicGeometry.pullbackIdIso (tilde M)) ⊤).symm
  refine ⟨((tilde.isoTop M).toLinearEquiv.toAddEquiv).trans e.toAddEquiv, fun a m => ?_⟩
  refine Eq.trans (congrArg e ((tilde.isoTop M).hom.hom.map_smul a m)) ?_
  refine Eq.trans (congrArg e (smul_sections_top a ((tilde.isoTop M).hom m))) ?_
  exact e.map_smul _ _

/-! ### The affine sections of the associated module of `M^~` -/

variable {τ : CoveringTopology} (A : CommRingCat.{u}) (B : BigSite τ (Spec A))
  (hA : schemeSizeBelow B.cutoff (Spec A))

/-- **The structure morphism of the base object of a chosen big site over `Spec A` is an
identity.** The base object is the spectrum of `A` viewed as an `A`-algebra of the site, over
`Spec A` by the identity; its structure morphism is `Spec` of the identity algebra map composed
with `𝟙 (Spec A)`. -/
public theorem base_overOfAlg_hom :
    (overOfAlg B A (𝟙 (Spec A)) (baseSiteAlgebra B A hA)).hom = 𝟙 (Spec A) := by
  change Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥A)) ≫ 𝟙 (Spec A) = 𝟙 (Spec A)
  simp

include hA in
/-- **The sections of `(M^~)ᵃ` over the base affine of the site are `M`.** This is
`Stacks.Adequate.exists_tildePullbackAddEquiv` at the structure morphism of the base object,
which `Stacks.Adequate.base_overOfAlg_hom` identifies with an identity, transported into the
affine-section spelling by the bridge
`Stacks.Adequate.affineBaseSections_smul_eq` between the action of `A` and the action of the
global functions on `Spec A`. -/
public theorem nonempty_baseSectionsTildeIso (M : ModuleCat.{u} A) :
    Nonempty (M ≅ affineBaseSections B A (𝟙 (Spec A)) hA ((associatedTilde B).obj M)) := by
  obtain ⟨θ, hθ⟩ := exists_tildePullbackAddEquiv A M
    (overOfAlg B A (𝟙 (Spec A)) (baseSiteAlgebra B A hA)).hom (base_overOfAlg_hom A B hA)
  have e : ↥M ≃ₗ[↥A] ↥(affineBaseSections B A (𝟙 (Spec A)) hA ((associatedTilde B).obj M)) :=
    { toFun := θ
      invFun := θ.symm
      left_inv := θ.left_inv
      right_inv := θ.right_inv
      map_add' := θ.map_add
      map_smul' := fun a m => (hθ a m).trans
        (affineBaseSections_smul_eq B A (𝟙 (Spec A)) hA (tilde M)
          (isSheaf_associatedPresheaf B (tilde M)) a (θ m)).symm }
  exact ⟨LinearEquiv.toModuleIso e⟩

/-- The `A`-algebras of a chosen big site over `Spec A`, as the index of the module-valued
functors of the chapter. -/
public noncomputable abbrev baseAlgebraInclusion :=
  AdequateFunctor.siteAlgebraInclusion (↥A) (schemeSizeBelow B.cutoff)

include hA in
/-- **The affine-section functor of `(M^~)ᵃ` is the module extension of `M`.** The comparison
`C ⊗_A 𝓖ᵃ(Spec A) ⟶ F_{𝓖ᵃ, A}` of `Stacks.Adequate.affineSectionsCompare` is an isomorphism for
an associated module, and its source is the module extension of the sections over the base
affine, which `Stacks.Adequate.nonempty_baseSectionsTildeIso` identifies with `M`. -/
public theorem nonempty_moduleExtTildeIso (M : ModuleCat.{u} A) :
    Nonempty ((AdequateFunctor.moduleExtensionFunctorOn (baseAlgebraInclusion A B)).obj M ≅
      (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).obj ((associatedTilde B).obj M)) := by
  obtain ⟨i⟩ := nonempty_baseSectionsTildeIso A B hA M
  have : IsIso (affineSectionsCompare B A (𝟙 (Spec A)) hA ((associatedTilde B).obj M)) :=
    isIso_affineSectionsCompare B A (𝟙 (Spec A)) hA (tilde M)
      (isSheaf_associatedPresheaf B (tilde M))
  exact ⟨(AdequateFunctor.moduleExtensionFunctorOn (baseAlgebraInclusion A B)).mapIso i ≪≫
    asIso (affineSectionsCompare B A (𝟙 (Spec A)) hA ((associatedTilde B).obj M))⟩

/-! ### Transporting a kernel presentation through the affine-section functor -/

/-- **A kernel of a map between objects in the image of the affine-section functor is the image
of a kernel.** If `f : P ⟶ Q` is a map of module-valued functors whose source and target are the
affine sections of `X` and of `Y`, and the affine sections of `Z` are the kernel of `f`, then `Z`
is the kernel of the morphism `X ⟶ Y` which the affine-section functor sends to `f`.

Full faithfulness is `Stacks.Adequate.fullyFaithfulAffineSectionsFunctor`, and that the functor
carries the kernel of `X ⟶ Y` to the kernel of `f` is
`Stacks.Adequate.affineSectionsFunctor_preservesFiniteLimits`. Everything is left variable: see
the module documentation for why. -/
public noncomputable def preimageKernelIso (X Y Z : SheafOfModules.{u} B.structureSheaf)
    {P Q : AdequateFunctor.ModuleValuedFunctorOn.{u} (baseAlgebraInclusion A B)} (f : P ⟶ Q)
    (cX : P ≅ (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).obj X)
    (cY : Q ≅ (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).obj Y)
    (e : (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).obj Z ≅ kernel f) :
    Z ≅ kernel ((fullyFaithfulAffineSectionsFunctor.{u, u} B (A := A)).preimage
      (cX.inv ≫ f ≫ cY.hom)) := by
  refine (fullyFaithfulAffineSectionsFunctor.{u, u} B (A := A)).preimageIso
    (e ≪≫ ?_ ≪≫ (PreservesKernel.iso (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))) _).symm)
  exact KernelFork.mapIsoOfIsLimit (limit.isLimit (parallelPair _ 0))
    (limit.isLimit (parallelPair _ 0))
    (Arrow.isoMk' _ _ cX cY (by
      rw [(fullyFaithfulAffineSectionsFunctor.{u, u} B (A := A)).map_preimage,
        Iso.hom_inv_id_assoc]))

/-- A kernel presentation by the associated modules of `M^~` and `N^~`, assembled from a
morphism `(M^~)ᵃ ⟶ (N^~)ᵃ` and an identification of a sheaf of modules with its kernel. The
morphism is a variable: see the module documentation. -/
public noncomputable def associatedTildeKernelPresentation (M N : ModuleCat.{u} A)
    (ψ : (associatedTilde B).obj M ⟶ (associatedTilde B).obj N)
    (F : SheafOfModules.{u} B.structureSheaf) (e : F ≅ kernel ψ) :
    AssociatedKernelPresentation B F :=
  { source := tilde M
    target := tilde N
    source_isSheaf := isSheaf_associatedPresheaf B (tilde M)
    target_isSheaf := isSheaf_associatedPresheaf B (tilde N)
    hom := ψ
    iso := e }

/-! ### The converse implication over an affine base -/

include hA in
/-- **A sheaf of modules on a chosen big site over `Spec A` whose affine-section functor at the
base affine is adequate is the kernel of a map of associated quasi-coherent modules.**

Adequacy of `F_{𝓕, A}` gives `A`-modules `M`, `N` and a map `φ : M ⟶ N` presenting it as the
kernel of the map of module extensions of `φ`. By
`Stacks.Adequate.nonempty_moduleExtTildeIso` those two module extensions are the affine sections
of `(M^~)ᵃ` and `(N^~)ᵃ`, so `Stacks.Adequate.preimageKernelIso` produces a map
`(M^~)ᵃ ⟶ (N^~)ᵃ` of associated modules with `𝓕` as its kernel. -/
public theorem isAssociatedKernel_of_isAdequate_affineSectionFunctor
    (F : SheafOfModules.{u} B.structureSheaf)
    (hF : AdequateFunctor.IsAdequate (baseAlgebraInclusion A B)
      (affineSectionFunctor B F A (𝟙 (Spec A)))) :
    IsAssociatedKernel B F := by
  obtain ⟨M, N, φ, ⟨k⟩⟩ := hF
  obtain ⟨cM⟩ := nonempty_moduleExtTildeIso A B hA M
  obtain ⟨cN⟩ := nonempty_moduleExtTildeIso A B hA N
  exact ⟨associatedTildeKernelPresentation A B M N _ F
    (preimageKernelIso A B _ _ F
      ((AdequateFunctor.moduleExtensionFunctorOn (baseAlgebraInclusion A B)).map φ) cM cN
      ((AdequateFunctor.presheafOfModulesUliftIso _ _).symm ≪≫ k))⟩

include hA in
/-- **An adequate `𝒪`-module on a chosen big site over an affine base is the kernel of a map of
associated quasi-coherent modules.** This is the local form of the implication (1) ⇒ (5) of
[Stacks, Tag 06VK]: the affine-section functor at the base affine is adequate by
[Stacks, Tag 06VI], `Stacks.Adequate.isAdequate_affineSectionFunctor`, which is unconditional,
and `Stacks.Adequate.isAssociatedKernel_of_isAdequate_affineSectionFunctor` turns that into a
kernel presentation. -/
public theorem isAssociatedKernel_of_isAdequate (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsAdequate B F) :
    IsAssociatedKernel B F :=
  isAssociatedKernel_of_isAdequate_affineSectionFunctor A B hA F
    (isAdequate_affineSectionFunctor.{u, u} B F hF A (𝟙 (Spec A)) hA)

/-- **A kernel presentation by associated modules is in particular a monomorphism into an
associated module.** The composite of the presenting isomorphism with the inclusion of the
kernel is a map `𝓕 ⟶ 𝓖ᵃ` into the associated module of a quasi-coherent module, and it is a
monomorphism because both factors are. -/
public theorem mono_of_associatedKernelPresentation
    {F : SheafOfModules.{u} B.structureSheaf} (p : AssociatedKernelPresentation B F) :
    Mono (p.iso.hom ≫ kernel.ι p.hom) :=
  @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _ (by infer_instance)

include hA in
/-- **An adequate `𝒪`-module on a chosen big site over an affine base admits a monomorphism into
the associated module of a quasi-coherent module.** This is the form in which the implication
(1) ⇒ (2) of [Stacks, Tag 06VK] is consumed by [Stacks, Tag 06ZR]: it is
`Stacks.Adequate.isAssociatedKernel_of_isAdequate` followed by
`Stacks.Adequate.mono_of_associatedKernelPresentation`. -/
public theorem exists_mono_into_associatedModule_of_isAdequate
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    ∃ (p : AssociatedModuleMap B)
      (i : F ⟶ @BigSite.associatedModule τ (Spec A) B p.source p.source_isQuasicoherent
        p.source_isSheaf), Mono i := by
  obtain ⟨p⟩ := isAssociatedKernel_of_isAdequate A B hA F hF
  exact ⟨p.toAssociatedModuleMap, p.iso.hom ≫ kernel.ι p.hom,
    mono_of_associatedKernelPresentation A B p⟩

/-! ### Tag 06VK: the implications (1) ⇒ (5), (1) ⇒ (2) and (1) ⇒ (3) -/

/-- **[Stacks, Tag 06VK], the implication (1) ⇒ (5).** An adequate `𝒪`-module on the big
`τ`-site over `S` restricts, over every affine scheme `Spec A` of the site over `S`, to the
kernel of a map `𝓖ᵃ ⟶ 𝓗ᵃ` of the associated modules of two quasi-coherent
`𝒪_{Spec A}`-modules.

Every chosen big site is the localization of an ambient big `τ`-site
(`Stacks.Adequate.BigSite.exists_eq_ofAmbient`), so the site over `Spec A` which condition (5)
asks for may be taken to be the localization of that same ambient site; the sheaf condition for
the restriction of `𝓕` is then `Stacks.Adequate.isSheaf_pullbackVal`, and the identification
`Stacks.Adequate.AffineAssociatedSections` the condition carries is the theorem
`Stacks.Adequate.affineAssociatedSections`. The kernel presentation itself is
`Stacks.Adequate.isAssociatedKernel_of_isAdequate` applied to the restriction, whose
affine-section functor at the base affine is the affine-section functor of `𝓕` at `Spec A` over
`S` by `Stacks.Adequate.affineSectionFunctor_pullbackSheaf`; so [Stacks, Tag 06VJ] is not
appealed to, only [Stacks, Tag 06VI]. -/
public theorem hasAssociatedKernelOnEveryAffine_of_isAdequate {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    HasAssociatedKernelOnEveryAffine B F := by
  obtain ⟨𝒮, hS, rfl⟩ := B.exists_eq_ofAmbient
  intro A f hA
  refine ⟨hA, AlgebraicGeometry.overTopology τ 𝒮 (Spec A) hA,
    AlgebraicGeometry.bigSite_structure_isSheaf 𝒮 (Spec A) hA,
    BigSite.chosen_overTopology 𝒮 (Spec A) hA,
    isSheaf_pullbackVal 𝒮 hS hA f F, affineAssociatedSections _, ?_⟩
  refine isAssociatedKernel_of_isAdequate_affineSectionFunctor A _ hA _ ?_
  exact isAdequate_affineSectionFunctor.{u, u} (BigSite.ofAmbient 𝒮 S hS) F hF A
    (𝟙 (Spec A) ≫ f) hA

/-- **[Stacks, Tag 06VK], the implication (1) ⇒ (2).** An adequate `𝒪`-module has a kernel
presentation by associated quasi-coherent modules over an affine open covering of `S`: this is
the implication (1) ⇒ (5) followed by (5) ⇒ (2). -/
public theorem hasAffineOpenAssociatedKernelCover_of_isAdequate {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    HasAffineOpenAssociatedKernelCover B F :=
  hasAffineOpenAssociatedKernelCover_of_hasAssociatedKernelOnEveryAffine B F
    (hasAssociatedKernelOnEveryAffine_of_isAdequate B F hF)

/-- **[Stacks, Tag 06VK], the implication (1) ⇒ (3).** An adequate `𝒪`-module has a kernel
presentation by associated quasi-coherent modules over a `τ`-covering of `S`: this is the
implication (1) ⇒ (2) followed by (2) ⇒ (3). -/
public theorem hasCoveringAssociatedKernel_of_isAdequate {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    HasCoveringAssociatedKernel B F :=
  hasCoveringAssociatedKernel_of_hasAffineOpenAssociatedKernelCover B F
    (hasAffineOpenAssociatedKernelCover_of_isAdequate B F hF)

/-! ### Tag 06VK: the equivalences of conditions (1), (2), (3) and (5) -/

/-- **[Stacks, Tag 06VK], the equivalence of conditions (1) and (5), with no hypotheses.** -/
public theorem isAdequate_iff_hasAssociatedKernelOnEveryAffine {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{u} B.structureSheaf) :
    IsAdequate B F ↔ HasAssociatedKernelOnEveryAffine B F :=
  ⟨hasAssociatedKernelOnEveryAffine_of_isAdequate B F,
    isAdequate_of_hasAssociatedKernelOnEveryAffine B F⟩

/-- **[Stacks, Tag 06VK], the equivalence of conditions (1) and (2), with no hypotheses.** -/
public theorem isAdequate_iff_hasAffineOpenAssociatedKernelCover {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{u} B.structureSheaf) :
    IsAdequate B F ↔ HasAffineOpenAssociatedKernelCover B F :=
  ⟨hasAffineOpenAssociatedKernelCover_of_isAdequate B F,
    isAdequate_of_hasAffineOpenAssociatedKernelCover B F⟩

/-- **[Stacks, Tag 06VK], the equivalence of conditions (1) and (3), with no hypotheses.** -/
public theorem isAdequate_iff_hasCoveringAssociatedKernel {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) :
    IsAdequate B F ↔ HasCoveringAssociatedKernel B F :=
  ⟨hasCoveringAssociatedKernel_of_isAdequate B F,
    isAdequate_of_hasCoveringAssociatedKernel B F⟩

end Stacks.Adequate

end
