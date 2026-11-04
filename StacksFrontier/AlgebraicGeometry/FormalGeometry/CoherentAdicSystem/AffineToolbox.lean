module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# The affine comparison toolbox for coherent adic systems

Let `X` be an affine Noetherian scheme and `I ⊆ Γ(X, ⊤)` an ideal. Tag 087W identifies the
category `Coh(X, I)` of coherent adic systems along `I` with the finite modules over the `I`-adic
completion of `Γ(X, ⊤)`, through the inverse limit of global sections. This file packages that
identification in the form the kernel construction of Tag 087X consumes: a single projection
`affineLevelProjection` from the completed module onto the `n`-th term of the system, known to be
surjective with kernel `I ^ (n+1)` times the completed module, natural in the system, and
inducing an isomorphism out of the quotient.

The construction of Tag 087X is affine-local: the kernel of a morphism of coherent adic systems
is built from the levelwise kernels, whose images in the lower terms stabilize, and that
stabilization is a statement about finite modules over a completed ring which is read off on an
affine open. The second half of the file therefore collects the facts that let an argument move
between a scheme and its affine opens: coherence of a categorical image, the computation of the
range of the inclusion of an image on sections over an affine open, the identification of the
range of a kernel inclusion with the kernel of the map it sits over, the exactness of restriction
in the strong form that it preserves limits of every small shape, and the locality of being an
isomorphism over an open cover.

## Main definitions

* `Stacks.Coherent.affineLevelProjection` — the projection from the completed module of a
  coherent adic system onto its `n`-th module of global sections.
* `Stacks.Coherent.affineLevelProjectionQuotientIso` and
  `Stacks.Coherent.affineLevelQuotientIso` — the two spellings of the induced isomorphism out of
  the quotient, by the kernel of the projection and by the ideal-power multiple.

## Main results

* `Stacks.Coherent.affineLevelProjection_surjective` and
  `Stacks.Coherent.affineLevelProjection_ker` — the projection is surjective and its kernel is
  `I ^ (n+1)` times the completed module.
* `Stacks.Coherent.affineLevelProjection_naturality` — the projections commute with every
  morphism of coherent adic systems.
* `Stacks.Coherent.preservesLimitsOfShape_restrictFunctor` — restriction along an open immersion
  preserves limits of every small shape, not only the finite ones.
* `Stacks.Coherent.isIso_of_isIso_restrictFunctor_map` — a morphism of sheaves of modules whose
  restriction along every member of an open cover is invertible is invertible.
* `Stacks.Coherent.isCoherent_image` — the image of a morphism of coherent modules is coherent.
* `Stacks.Coherent.range_map_kernel_ι` — an additive functor to modules which preserves a kernel
  carries the kernel inclusion to a map whose range is the kernel of the image of the map.
* `Stacks.Coherent.range_image_ι_app_top` and
  `Stacks.Coherent.range_image_ι_restrict_app_top` — over an affine scheme, and after restriction
  along an open immersion from a spectrum, the image of a morphism of coherent modules has the
  same range on global sections as the morphism itself.

## Implementation notes

`affineLevelProjection` is the composite of the comparison isomorphism with the limit projection,
so `affineLevelProjection_surjective` and `affineLevelProjection_ker` are the corresponding
statements of `Equivalence` read through that definition. Naturality is assembled in term mode
from `Category.assoc`, `congrArg` and `limMap_π` rather than by rewriting: the two sides mention
`Scheme.Modules`, a `def` for `SheafOfModules X.ringCatSheaf`, so a rewrite motive built against
one spelling of the category is not type-correct against the other.

The statements on sections are phrased with `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`, the
functor whose image of a morphism is its component on global sections as a map of
`Γ(X, ⊤)`-modules; this is the shape in which the ranges and kernels of the resulting linear maps
can be compared.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### The projections out of the completed module -/

/-- The projection from the completed module of a coherent adic system onto its `n`-th module of
global sections: the comparison isomorphism of Tag 087W followed by the projection out of the
inverse limit. -/
public noncomputable def affineLevelProjection
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (n : ℕ) :
    completedModuleAsBase X I F ⟶ (globalSectionsSystem F).obj (op n) :=
  (globalSectionsComparison X I F).hom ≫ limit.π (globalSectionsSystem F) (op n)

/-- Every term of a coherent adic system on an affine Noetherian scheme is a quotient of the
completed module: the projection onto it is surjective. -/
public theorem affineLevelProjection_surjective
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (n : ℕ) : Function.Surjective (affineLevelProjection X I F n).hom :=
  globalSectionsComparison_projection_surjective X I F n

/-- The kernel of the projection onto the `n`-th term is the `(n+1)`-st power of the ideal times
the completed module. -/
public theorem affineLevelProjection_ker
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (n : ℕ) :
    LinearMap.ker (affineLevelProjection X I F n).hom =
      I ^ (n + 1) • (⊤ : Submodule Γ(X, ⊤) (completedModuleAsBase X I F)) :=
  globalSectionsComparison_projection_ker X I F n

/-- The quotient of the completed module by the kernel of the `n`-th projection is the `n`-th
module of global sections. -/
public noncomputable def affineLevelProjectionQuotientIso
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (n : ℕ) :
    ModuleCat.of Γ(X, ⊤)
        (completedModuleAsBase X I F ⧸
          LinearMap.ker (affineLevelProjection X I F n).hom) ≅
      (globalSectionsSystem F).obj (op n) :=
  (LinearMap.quotKerEquivOfSurjective (affineLevelProjection X I F n).hom
    (affineLevelProjection_surjective X I F n)).toModuleIso

/-- The `n`-th term of a coherent adic system is the quotient of the completed module by the
`(n+1)`-st ideal-power multiple. This is the adic description of the system. -/
public noncomputable def affineLevelQuotientIso
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (n : ℕ) :
    ModuleCat.of Γ(X, ⊤)
        (completedModuleAsBase X I F ⧸
          I ^ (n + 1) • (⊤ : Submodule Γ(X, ⊤)
            (completedModuleAsBase X I F))) ≅
      (globalSectionsSystem F).obj (op n) :=
  let p := affineLevelProjection X I F n
  let q := I ^ (n + 1) • (⊤ : Submodule Γ(X, ⊤) (completedModuleAsBase X I F))
  let e : (completedModuleAsBase X I F ⧸ q) ≃ₗ[Γ(X, ⊤)]
      (completedModuleAsBase X I F ⧸ LinearMap.ker p.hom) :=
    Submodule.quotEquivOfEq q (LinearMap.ker p.hom)
      (affineLevelProjection_ker X I F n).symm
  (e.trans (p.hom.quotKerEquivOfSurjective
    (affineLevelProjection_surjective X I F n))).toModuleIso

/-- The projections out of the completed modules commute with every morphism of coherent adic
systems. -/
public theorem affineLevelProjection_naturality
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    {F G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (f : F ⟶ G) (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap Γ(X, ⊤)
      (AdicCompletion I Γ(X, ⊤)))).map
        ((coherentAdicSystemsEquivFGModuleCat X I).functor.map f).hom ≫
      affineLevelProjection X I G n =
    affineLevelProjection X I F n ≫
      (Functor.whiskerRight f.hom
        (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).app (op n) :=
  let τ := Functor.whiskerRight f.hom (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
  let c := (globalSectionsComparison X I F).hom
  have hlim : limMap τ ≫ limit.π (globalSectionsSystem G) (op n) =
      limit.π (globalSectionsSystem F) (op n) ≫ τ.app (op n) := limMap_π _ _
  (Category.assoc _ _ _).symm.trans
    (((congrArg (fun k => k ≫ limit.π (globalSectionsSystem G) (op n))
        (globalSectionsComparison_naturality X I f)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => c ≫ k) hlim).trans (Category.assoc _ _ _).symm))))

/-! ### Restriction, coherence and sections over an affine open -/

/-- **Restriction along an open immersion preserves limits of every small shape.** Composed with
the forgetful functor to abelian presheaves, which preserves limits and reflects isomorphisms, it
becomes restriction of presheaves along the induced functor on opens, and limits of presheaves are
computed pointwise. -/
public theorem preservesLimitsOfShape_restrictFunctor {Y Z : Scheme.{u}} (r : Z ⟶ Y)
    [IsOpenImmersion r] (D : Type u) [SmallCategory D] :
    PreservesLimitsOfShape D (Scheme.Modules.restrictFunctor r) := by
  have h₀ : PreservesLimitsOfSize.{u, u} (Scheme.Modules.toPresheaf Y) :=
    preservesLimitsOfSize_shrink _
  have h₁ : PreservesLimitsOfShape D
      ((Functor.whiskeringLeft _ _ Ab.{u}).obj r.opensFunctor.op) := inferInstance
  have e : Scheme.Modules.restrictFunctor r ⋙ Scheme.Modules.toPresheaf Z ≅
      Scheme.Modules.toPresheaf Y ⋙
        (Functor.whiskeringLeft _ _ _).obj r.opensFunctor.op := Iso.refl _
  have h₂ : PreservesLimitsOfShape D
      (Scheme.Modules.restrictFunctor r ⋙ Scheme.Modules.toPresheaf Z) :=
    preservesLimitsOfShape_of_natIso e.symm
  have h₃ : PreservesLimitsOfSize.{u, u} (Scheme.Modules.toPresheaf Z) :=
    preservesLimitsOfSize_shrink _
  have h₄ : ReflectsLimitsOfShape D (Scheme.Modules.toPresheaf Z) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf Z)

/-- **Being an isomorphism is local on an open cover**, for sheaves of modules on a scheme: a
morphism whose restriction along every member of an open cover is invertible is invertible. -/
public theorem isIso_of_isIso_restrictFunctor_map {Y : Scheme.{u}} (V : Y.OpenCover)
    {M N : Y.Modules} (f : M ⟶ N)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (V.f i)).map f)) : IsIso f := by
  have : Mono f := ⟨fun {_} a b hab =>
      Stacks.Descent.hom_ext_of_restrictFunctor_map_eq V.f V.iSup_opensRange fun i => by
    have := h i
    refine (cancel_mono ((Scheme.Modules.restrictFunctor (V.f i)).map f)).mp ?_
    exact ((Scheme.Modules.restrictFunctor (V.f i)).map_comp a f).symm.trans
      ((congrArg (Scheme.Modules.restrictFunctor (V.f i)).map hab).trans
        ((Scheme.Modules.restrictFunctor (V.f i)).map_comp b f))⟩
  have : Epi f := ⟨fun {_} a b hab =>
      Stacks.Descent.hom_ext_of_restrictFunctor_map_eq V.f V.iSup_opensRange fun i => by
    have := h i
    refine (cancel_epi ((Scheme.Modules.restrictFunctor (V.f i)).map f)).mp ?_
    exact ((Scheme.Modules.restrictFunctor (V.f i)).map_comp f a).symm.trans
      ((congrArg (Scheme.Modules.restrictFunctor (V.f i)).map hab).trans
        ((Scheme.Modules.restrictFunctor (V.f i)).map_comp f b))⟩
  exact isIso_of_mono_of_epi f

/-- **The image of a morphism of coherent modules is coherent.** The image is the kernel of the
projection onto the cokernel, and coherent modules are closed under both. -/
public instance isCoherent_image {Y : Scheme.{u}} {M N : Y.Modules}
    [M.IsCoherent] [N.IsCoherent] (f : M ⟶ N) : (image f).IsCoherent := by
  have hclosed : ObjectProperty.IsClosedUnderIsomorphisms
      (fun P : SheafOfModules.{u} Y.ringCatSheaf => P.IsCoherent) :=
    AlgebraicGeometry.CoherentAbelian.coherentModules_isClosedUnderIsomorphisms
  have hcokernel : (cokernel f).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel f
  have hkernel : (kernel (cokernel.π f)).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (cokernel.π f)
  exact ObjectProperty.prop_of_iso
    (P := fun P : SheafOfModules.{u} Y.ringCatSheaf => P.IsCoherent)
    (Abelian.imageIsoImage f) hkernel

/-- An additive functor to modules which preserves the kernel of a map carries the kernel
inclusion to a linear map whose range is the kernel of the image of the map. -/
public theorem range_map_kernel_ι
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {R : Type*} [Ring R] (E : C ⥤ ModuleCat R)
    [E.PreservesZeroMorphisms] {M N : C} (f : M ⟶ N)
    [HasKernel f] [PreservesLimit (parallelPair f 0) E] :
    LinearMap.range (E.map (kernel.ι f)).hom = LinearMap.ker (E.map f).hom := by
  let e := PreservesKernel.iso E f ≪≫ ModuleCat.kernelIsoKer (E.map f)
  have he : e.inv ≫ E.map (kernel.ι f) =
      ModuleCat.ofHom (LinearMap.ker (E.map f).hom).subtype := by
    simp [e, Category.assoc]
  have hsurj : Function.Surjective e.inv.hom :=
    (ModuleCat.epi_iff_surjective e.inv).mp inferInstance
  rw [← LinearMap.range_comp_of_range_eq_top (E.map (kernel.ι f)).hom
    (LinearMap.range_eq_top.mpr hsurj)]
  exact (congrArg (fun k => LinearMap.range k.hom) he).trans (Submodule.range_subtype _)

/-- **Over an affine scheme the image of a morphism of coherent modules is its range on global
sections.** The morphism factors through its image by an epimorphism, which is surjective on the
sections over an affine open. -/
public theorem range_image_ι_app_top {Y : Scheme.{u}} [IsAffine Y]
    {M N : Y.Modules} [M.IsCoherent] [N.IsCoherent] (f : M ⟶ N) :
    LinearMap.range ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map (image.ι f)).hom =
      LinearMap.range ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map f).hom := by
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)
  have hM : M.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have himg : (image f).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have hsurj : Function.Surjective (E.map (factorThruImage f)).hom :=
    Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen (factorThruImage f)
      ⟨⊤, isAffineOpen_top Y⟩
  have hfac : (E.map (image.ι f)).hom.comp (E.map (factorThruImage f)).hom = (E.map f).hom :=
    congrArg ModuleCat.Hom.hom
      ((E.map_comp (factorThruImage f) (image.ι f)).symm.trans
        (congrArg E.map (image.fac f)))
  rw [← hfac, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]

/-- **The same comparison after restriction along an open immersion from a spectrum.** The image
of a morphism of coherent modules restricts to a module with the same range on global sections as
the restriction of the morphism. -/
public theorem range_image_ι_restrict_app_top {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {Z : Scheme.{u}} [IsAffine Z] (r : Z ⟶ Y) [IsOpenImmersion r]
    {M N : Y.Modules} [M.IsCoherent] [N.IsCoherent] (f : M ⟶ N) :
    LinearMap.range ((Scheme.Modules.restrictFunctor r ⋙
        SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map (image.ι f)).hom =
      LinearMap.range ((Scheme.Modules.restrictFunctor r ⋙
        SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map f).hom := by
  let T := Scheme.Modules.restrictFunctor r
  let E := T ⋙ SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)
  have hM : (T.obj M).IsCoherent :=
    Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion r M
  have himg : (T.obj (image f)).IsCoherent :=
    Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion r (image f)
  have hMq : (T.obj M).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have himgq : (T.obj (image f)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : Epi (T.map (factorThruImage f)) :=
    (Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.restrictAdjunction r)).preserves _
  have hsurj : Function.Surjective (E.map (factorThruImage f)).hom :=
    Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen (T.map (factorThruImage f))
      ⟨⊤, isAffineOpen_top Z⟩
  have hfac : (E.map (image.ι f)).hom.comp (E.map (factorThruImage f)).hom = (E.map f).hom :=
    congrArg ModuleCat.Hom.hom
      ((E.map_comp (factorThruImage f) (image.ι f)).symm.trans
        (congrArg E.map (image.fac f)))
  rw [← hfac, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]

end Stacks.Coherent

end
