module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasicoherentChaotic
public import StacksFrontier.Algebra.Module.Pure.ExtAbelian
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.InjectiveObjects

/-!
# Pure extensions are the extensions of adequate functors

Let `A` be a ring and `𝒜` the abelian category of adequate module-valued functors on the
commutative `A`-algebras, with `M ↦ M̲` the extension of scalars `B ↦ B ⊗_A M`. The proof of
[Stacks, Tag 0709] rests on the identity

`Ext^i_𝒜(M̲, N̲) = Pext^i_A(M, N)`,

"clear from [Stacks, Tag 0708] as a pure injective resolution `N → Iᐧ` exactly corresponds to an
injective resolution of `N̲` in `𝒜`". This module proves it in every degree, naturally in `M` and
`N`: extension of scalars is fully faithful, carries universally exact sequences to exact ones
(over each algebra `B` the sequence is `B ⊗_A -` of a universally exact one), universally injective
maps to monomorphisms, and pure injective modules to injective objects of `𝒜`, which is
Tag 0708 (`AdequateFunctor.injective_moduleExtension_of_pureInjective`); so
`Module.pureExtAddEquivExt` applies.

## Main results

* `AdequateFunctor.pureExtAddEquivExtAdequateFunctor` — `Pext^n_A(M, N) ≃+ Ext^n_𝒜(M̲, N̲)`, for
  every `n`, natural in both variables by `Module.pureExtAddEquivExt_naturality_left` and
  `Module.pureExtAddEquivExt_naturality_right`.

## References

* [Stacks Project, Tag 0708](https://stacks.math.columbia.edu/tag/0708)
* [Stacks Project, Tag 0709](https://stacks.math.columbia.edu/tag/0709)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AdequateFunctor

variable (A : Type u) [CommRing A]

/-- Extension of scalars `M ↦ M̲` as a functor into the adequate functors. -/
public def moduleExtensionAdequate :
    ModuleCat.{u} A ⥤ (adequate.{u, u, u} A).FullSubcategory :=
  ObjectProperty.lift _ (moduleExtensionFunctor.{u, u} A) fun M => isAdequate_moduleExtension M

/-- Extension of scalars into the adequate functors is additive. -/
public instance moduleExtensionAdequate_additive : (moduleExtensionAdequate A).Additive :=
  ⟨fun {_ _ _ _} => ObjectProperty.hom_ext _ (moduleExtensionFunctor.{u, u} A).map_add⟩

/-- Extension of scalars into the adequate functors is fully faithful. -/
public def fullyFaithfulModuleExtensionAdequate : (moduleExtensionAdequate A).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := (adequate.{u, u, u} A).ι)
    (fullyFaithfulModuleExtensionFunctor A)

variable {A}

/-- A universally injective map extends to a monomorphism of adequate functors. -/
public theorem mono_moduleExtensionAdequate_map {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    (hφ : UniversallyInjective φ.hom) : Mono ((moduleExtensionAdequate A).map φ) :=
  have := mono_moduleExtension_map_of_universallyInjective.{u, u, u} φ hφ
  (adequate.{u, u, u} A).ι.mono_of_mono_map (h := this)

/-- **Extension of scalars carries universally exact sequences to exact sequences of adequate
functors**: over each algebra `B` the sequence is `B ⊗_A -` of a universally exact sequence. -/
public theorem exact_moduleExtensionAdequate_map {X Y Z : ModuleCat.{u} A} (f : X ⟶ Y)
    (g : Y ⟶ Z) (w : (moduleExtensionAdequate A).map f ≫ (moduleExtensionAdequate A).map g = 0)
    (hfg : Function.Exact f.hom g.hom)
    (hQ : ∀ (Q : Type u) [AddCommGroup Q] [Module A Q],
      Function.Exact (f.hom.rTensor Q) (g.hom.rTensor Q)) :
    (ShortComplex.mk _ _ w).Exact := by
  have hfg0 : f ≫ g = 0 := ModuleCat.hom_ext hfg.linearMap_comp_eq_zero
  let S0 : ShortComplex (ModuleCat.{u} A) := ShortComplex.mk f g hfg0
  show (S0.map (moduleExtensionAdequate A)).Exact
  have := (adequate.{u, u, u} A).preservesKernels_ι
  have := (adequate.{u, u, u} A).preservesCokernels_ι
  have : PreservesFiniteLimits (adequate.{u, u, u} A).ι :=
    Functor.preservesFiniteLimits_of_preservesKernels _
  have : PreservesFiniteColimits (adequate.{u, u, u} A).ι :=
    Functor.preservesFiniteColimits_of_preservesCokernels _
  rw [← ShortComplex.exact_map_iff_of_faithful _ (adequate.{u, u, u} A).ι,
    ← ShortComplex.map_comp]
  apply ChaoticQCoh.exact_of_evaluation
  intro W
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hex := (LinearMap.rTensor_exact_iff_lTensor_exact (Q := (W.unop.unop : Type u))
    (f := f.hom) (g := g.hom)).1 (hQ _)
  exact (hex x).1 hx

/-- **[Stacks, Tag 0708] read through [Stacks, Tag 0709]: `Pext^n_A(M, N) = Ext^n_𝒜(M̲, N̲)`
for every `n`.** A pure injective resolution `N → Iᐧ` extends to an injective resolution
`N̲ → I̲ᐧ` of adequate functors, and the class of a cocycle `f : M → Iⁿ` goes to the class of the
cocycle `f̲`; naturality in `M` and `N` is `Module.pureExtAddEquivExt_naturality_left` and
`Module.pureExtAddEquivExt_naturality_right` at `T := moduleExtensionAdequate A`. -/
public def pureExtAddEquivExtAdequateFunctor (M N : ModuleCat.{u} A) (n : ℕ) :
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u, u} A).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (adequate.{u, u, u} A).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    Module.pureExt (A := A) M N n ≃+
      Abelian.Ext ((moduleExtensionAdequate A).obj M) ((moduleExtensionAdequate A).obj N) n :=
  letI : HasDerivedCategory.{u + 1} (adequate.{u, u, u} A).FullSubcategory :=
    HasDerivedCategory.standard _
  letI : HasExt.{u + 1} (adequate.{u, u, u} A).FullSubcategory :=
    hasExt_of_hasDerivedCategory _
  Module.pureExtAddEquivExt (moduleExtensionAdequate A)
    (fun I hI => injective_moduleExtension_of_pureInjective.{u, u, u} I hI)
    (fun φ hφ => mono_moduleExtensionAdequate_map φ hφ)
    (fun f g w hfg hQ => exact_moduleExtensionAdequate_map f g w hfg hQ)
    (fullyFaithfulModuleExtensionAdequate A) M N n

end AdequateFunctor

end
