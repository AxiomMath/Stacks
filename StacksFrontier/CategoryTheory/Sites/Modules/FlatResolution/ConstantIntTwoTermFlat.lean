module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.TorsionFree
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantCoefficients
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTwoTermFlat

/-!
# Modules over the constant sheaf of rings `ℤ` have flat resolutions of length one

Let `(C, J)` be a site and `ℤ̲` the constant sheaf of rings `ℤ` on it. Every sheaf of
`ℤ̲`-modules `G` has a resolution `0 ⟶ K ⟶ P ⟶ G ⟶ 0` by two flat sheaves of modules.

Read `G` as a presheaf of modules over the constant *presheaf* of rings `ℤ` and map onto it the
free presheaf of modules on its underlying presheaf of sets. The sections of that free presheaf
are free `ℤ`-modules, and those of its kernel are submodules of free `ℤ`-modules, hence
torsion-free, hence flat, `ℤ` being a principal ideal domain; so both presheaves are flat
(Stacks 03ES). Sheafifying along the locally bijective map from the constant presheaf to `ℤ̲` is
exact, keeps flatness (Stacks 03ET), and gives back `G`.

## Main results

* `AlgebraicGeometry.RingedSite.hasTwoTermFlatResolutions_constant_int`: every sheaf of modules
  over the constant sheaf of rings `ℤ` has a resolution by two flat sheaves of modules.

## References

* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- The constant presheaf of rings `ℤ`. -/
abbrev constantIntPresheaf : Cᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))

/-- The map from the constant presheaf of rings `ℤ` to the constant sheaf of rings `ℤ̲`. -/
abbrev constantIntToSheaf :
    constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (constant J (ULift.{u} ℤ)).O).obj :=
  Functor.whiskerRight (toSheafify J (constantIntPresheaf (C := C))) (forget₂ CommRingCat RingCat)

/-- The map from the constant presheaf of rings `ℤ` to `ℤ̲` is locally injective. -/
instance : Presheaf.IsLocallyInjective J (constantIntToSheaf J) :=
  ⟨fun x y h => Presheaf.equalizerSieve_mem J (toSheafify J (constantIntPresheaf (C := C))) x y h⟩

/-- The map from the constant presheaf of rings `ℤ` to `ℤ̲` is locally surjective. -/
instance : Presheaf.IsLocallySurjective J (constantIntToSheaf J) :=
  ⟨fun s => Presheaf.imageSieve_mem J (toSheafify J (constantIntPresheaf (C := C))) s⟩

/-- The sections of the constant presheaf of rings `ℤ` form a principal ideal domain. -/
theorem isPrincipalIdealRing_constantIntPresheaf_obj (U : Cᵒᵖ) :
    IsPrincipalIdealRing ((constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat).obj U) :=
  IsPrincipalIdealRing.of_surjective
    ((ULift.ringEquiv (R := ℤ)).symm.toRingHom :
      ℤ →+* (constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat).obj U)
    (ULift.ringEquiv (R := ℤ)).symm.surjective

/-- The sections of the constant presheaf of rings `ℤ` form an integral domain. -/
theorem isDomain_constantIntPresheaf_obj (U : Cᵒᵖ) :
    IsDomain ((constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat).obj U) :=
  MulEquiv.isDomain ℤ (ULift.ringEquiv (R := ℤ)).toMulEquiv

/-- **A module over the sections of `ℤ` embedding into a flat one is flat**: it is torsion-free,
and over a principal ideal domain torsion-free modules are flat. -/
theorem flat_of_injective_constantIntPresheaf_obj (U : Cᵒᵖ)
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module ((constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat).obj U) M]
    [Module ((constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat).obj U) N]
    (f : M →ₗ[(constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat).obj U] N)
    (hf : Function.Injective f)
    [Module.Flat ((constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat).obj U) N] :
    Module.Flat ((constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat).obj U) M := by
  have := isPrincipalIdealRing_constantIntPresheaf_obj (C := C) U
  have := isDomain_constantIntPresheaf_obj (C := C) U
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff x).1 hx
  have hN := Module.Flat.torsion_eq_bot (R := (constantIntPresheaf (C := C) ⋙
    forget₂ CommRingCat RingCat).obj U) (M := N)
  have : f x ∈ Submodule.torsion _ N :=
    (Submodule.mem_torsion_iff _).2 ⟨r, by
      rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, hr, map_zero]⟩
  rw [hN] at this
  exact (Submodule.mem_bot _).2 (hf (by rw [(Submodule.mem_bot _).1 this, map_zero]))

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Every sheaf of modules over the constant sheaf of rings `ℤ` has a resolution by two flat
sheaves of modules.** -/
theorem hasTwoTermFlatResolutions_constant_int :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTwoTermFlatResolutions
      (constant J (ULift.{u} ℤ)) := by
  intro G
  let R₀ := constantIntPresheaf (C := C) ⋙ forget₂ CommRingCat RingCat
  let a := constantIntToSheaf J
  let G₀ : PresheafOfModules.{u} R₀ := (PresheafOfModules.restrictScalars a).obj G.val
  let F := (PresheafOfModules.toPresheaf R₀ ⋙
    (Functor.whiskeringRight Cᵒᵖ Ab (Type u)).obj (forget Ab)).obj G₀
  let P₀ := (PresheafOfModules.free R₀).obj F
  let p₀ : P₀ ⟶ G₀ := (PresheafOfModules.freeAdjunction R₀).counit.app G₀
  have hp₀ : Epi p₀ := inferInstance
  let S₀ := ShortComplex.mk (kernel.ι p₀) p₀ (kernel.condition p₀)
  have hS₀ : S₀.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p₀) }
  have hP₀ : ∀ U, Module.Flat (R₀.obj U) (P₀.obj U) := fun U =>
    inferInstanceAs (Module.Flat (R₀.obj U) (F.obj U →₀ R₀.obj U))
  have hK₀ : ∀ U, Module.Flat (R₀.obj U) ((kernel p₀).obj U) := fun U =>
    flat_of_injective_constantIntPresheaf_obj U ((kernel.ι p₀).app U).hom
      (PresheafOfModules.injective_of_mono (kernel.ι p₀) U)
  let Sh := PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf
    (constant J (ULift.{u} ℤ)).O) a
  refine ⟨S₀.map Sh, hS₀.map_of_exact Sh, ?_, ?_, ⟨?_⟩⟩
  · exact Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J a _
      (SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat _ hK₀)
  · exact Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J a _
      (SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat _ hP₀)
  · exact (asIso (PresheafOfModules.sheafificationAdjunction a).counit).app G

end AlgebraicGeometry.RingedSite

end
