module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFiniteOrder
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence

/-!
# Affineness of a finite-order thickening

A finite-order thickening of an affine scheme is affine. For a first-order thickening
`i : X ⟶ X'` the defining ideal sheaf is annihilated by itself, hence is the direct image of a
quasi-coherent module on `X`; its first cohomology on `X'` therefore agrees with a first
cohomology on the affine scheme `X` and vanishes, so `Γ(X', 𝒪_{X'}) → Γ(X, 𝒪_X)` is surjective
and `X'` is affine. The adic filtration of the defining ideal sheaf reduces the finite-order
case to this one.

## Main definitions

* `Stacks.Thickenings.idealSheafModule`: the defining ideal sheaf of a closed immersion, as a
  module over the structure sheaf of the ambient scheme.

## Main results

* `Stacks.Thickenings.mul_eq_zero_of_app_eq_zero`: for a first-order thickening, two sections of
  the ambient structure sheaf over a common open which die on the closed subscheme have
  vanishing product.
* `Stacks.Thickenings.exists_isQuasicoherent_pushforward_iso_idealSheafModule`: the defining
  ideal sheaf of a first-order thickening is the direct image of a quasi-coherent module on the
  closed subscheme.
* `Stacks.Thickenings.isZero_hgroup_one_idealSheafModule`: its first cohomology vanishes when
  the closed subscheme is affine.
* `Stacks.Thickenings.surjective_appTop_of_isFirstOrderThickening`: global sections of a
  first-order thickening of an affine scheme lift.
* `Stacks.Thickenings.isAffine_of_isFiniteOrderThickening`: the finite-order case of
  [Stacks Project, Tag 06AD].

## Implementation notes

The square-zero condition `i.ker ^ 2 = ⊥` constrains the ideals at affine opens, whereas
recognising the ideal sheaf as a direct image needs the annihilation over every open; the two
are bridged by the sheaf axiom, a product of sections vanishing as soon as all its germs do.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Thickenings

variable {X X' : Scheme.{u}}

/-- The defining ideal sheaf of a closed immersion `i : X ⟶ X'`, as the kernel of the comorphism
`𝒪_{X'} → i_*𝒪_X` in the modules over `𝒪_{X'}`. -/
abbrev idealSheafModule (i : X ⟶ X') : SheafOfModules X'.ringCatSheaf :=
  kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)

/-! ### The ideal sheaf of a first-order thickening squares to zero -/

/-- **Two sections dying on the closed subscheme of a first-order thickening have vanishing
product.** Over an affine open both restrictions lie in the ideal of `i.ker`, whose square
vanishes; the germs of the product therefore all vanish. -/
theorem mul_eq_zero_of_app_eq_zero {i : X ⟶ X'} (hi : IsFirstOrderThickening i)
    (U : X'.Opens) (a b : Γ(X', U)) (ha : i.app U a = 0) (hb : i.app U b = 0) :
    a * b = 0 := by
  have : IsClosedImmersion i := hi.1
  apply TopCat.Presheaf.section_ext X'.sheaf U
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  let j : V ⟶ U := homOfLE hVU
  have hk (c : Γ(X', U)) (hc : i.app U c = 0) :
      X'.presheaf.map j.op c ∈ RingHom.ker (i.app V).hom := by
    rw [RingHom.mem_ker]
    have hn := ConcreteCategory.congr_hom (i.naturality j.op) c
    change i.app V (X'.presheaf.map j.op c) = X.presheaf.map _ (i.app U c) at hn
    exact hn.trans (by rw [hc, map_zero])
  have hz : X'.presheaf.map j.op a * X'.presheaf.map j.op b = 0 := by
    have hsq := congrArg (fun J : X'.IdealSheafData => J.ideal ⟨V, hV⟩) hi.2
    have hm := Ideal.mul_mem_mul (hk a ha) (hk b hb)
    rw [← Scheme.Hom.ker_apply i ⟨V, hV⟩] at hm
    change _ ∈ i.ker.ideal ⟨V, hV⟩ * i.ker.ideal ⟨V, hV⟩ at hm
    change i.ker.ideal ⟨V, hV⟩ ^ 2 = ⊥ at hsq
    rwa [← pow_two, hsq] at hm
  show X'.presheaf.germ U x hx (a * b) = X'.presheaf.germ U x hx 0
  rw [← TopCat.Presheaf.germ_res_apply X'.presheaf j x hxV (a * b)]
  simp only [map_mul, hz, map_zero]

/-! ### Sections of the ideal sheaf -/

/-- **The sections of the defining ideal sheaf inject into the structure sheaf**, the inclusion
being a monomorphism and the evaluation functors preserving limits. -/
theorem injective_app_idealSheafModule (i : X ⟶ X') (U : X'.Opens) :
    Function.Injective
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).val.app
        (Opposite.op U)) :=
  (ModuleCat.mono_iff_injective _).mp
    (inferInstanceAs (Mono ((SheafOfModules.evaluation X'.ringCatSheaf (Opposite.op U)).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)))))

/-- **The sections of the defining ideal sheaf over an open are the kernel of the comorphism
there**, because evaluation carries the kernel sequence to a kernel sequence. -/
theorem exact_app_idealSheafModule (i : X ⟶ X') (U : X'.Opens) :
    Function.Exact
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).val.app
        (Opposite.op U))
      ((SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom).val.app
        (Opposite.op U)) := by
  let S := ShortComplex.kernelSequence
    (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
  let F := SheafOfModules.evaluation X'.ringCatSheaf (Opposite.op U)
  have h : (S.map F).Exact :=
    ((S.map F).exact_and_mono_f_iff_f_is_kernel.mpr
      ⟨KernelFork.mapIsLimit _ (kernelIsKernel
        (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) F⟩).1
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h

/-! ### The ideal sheaf of a first-order thickening is a direct image -/

/-- **The defining ideal sheaf of a first-order thickening comes from the closed subscheme.** It
is quasi-coherent and annihilated by itself, so the unit of the pullback–pushforward adjunction
identifies it with the direct image of a quasi-coherent module on the closed subscheme. -/
theorem exists_isQuasicoherent_pushforward_iso_idealSheafModule {i : X ⟶ X'}
    (hi : IsFirstOrderThickening i) :
    ∃ I : X.Modules, I.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.pushforward i).obj I ≅ idealSheafModule i) := by
  have : IsClosedImmersion i := hi.1
  have hqc : (idealSheafModule i).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf i
  have he : (Stacks.Modules.pushforwardQcoh i).essImage
      ⟨idealSheafModule i, hqc⟩ := by
    apply (Stacks.ClosedImmersion.pushforwardQcoh_essImage_iff i (idealSheafModule i) hqc).mpr
    intro U a ha m
    change Γ(X', U) at a
    apply injective_app_idealSheafModule i U
    refine Eq.trans
      (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).val.app
        (Opposite.op U)).hom.map_smul a m) ?_
    refine Eq.trans ?_
      (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).val.app
        (Opposite.op U)).hom.map_zero).symm
    show (a : Γ(X', U)) * (show Γ(X', U) from
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).val.app
        (Opposite.op U)) m) = 0
    exact mul_eq_zero_of_app_eq_zero hi U a _ ha
      ((exact_app_idealSheafModule i U).apply_apply_eq_zero m)
  obtain ⟨I, ⟨e⟩⟩ := he
  exact ⟨I.obj, I.property, ⟨(SheafOfModules.isQuasicoherent X'.ringCatSheaf).ι.mapIso e⟩⟩

/-! ### Vanishing of the first cohomology of the ideal sheaf -/

/-- **The first cohomology of the defining ideal sheaf of a first-order thickening of an affine
scheme vanishes.** It is the direct image of a quasi-coherent module on the affine closed
subscheme, whose higher cohomology vanishes and is unchanged by the direct image. -/
theorem isZero_hgroup_one_idealSheafModule {i : X ⟶ X'} (hi : IsFirstOrderThickening i)
    [IsAffine X] : IsZero (Hgroup X'.ringCatSheaf ⊤ 1 (idealSheafModule i)) := by
  have : IsClosedImmersion i := hi.1
  obtain ⟨I, hIqc, ⟨e⟩⟩ := exists_isQuasicoherent_pushforward_iso_idealSheafModule hi
  have hvan : IsZero (Hgroup X'.ringCatSheaf ⊤ 1 ((Scheme.Modules.pushforward i).obj I)) :=
    (@Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine X _ I hIqc 1 one_pos).of_iso
      (@Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp X X' i _ 1 I hIqc).symm
  exact hvan.of_iso ((Hfunctor X'.ringCatSheaf ⊤ 1).mapIso e.symm)

/-! ### Affineness -/

/-- **Global sections of a first-order thickening of an affine scheme lift.** The first
cohomology of the defining ideal sheaf vanishes, so the long exact cohomology sequence of
`0 → ℐ → 𝒪_{X'} → i_*𝒪_X → 0` makes `Γ(X', 𝒪_{X'}) → Γ(X, 𝒪_X)` surjective. -/
theorem surjective_appTop_of_isFirstOrderThickening {i : X ⟶ X'}
    (hi : IsFirstOrderThickening i) [IsAffine X] : Function.Surjective i.appTop.hom := by
  have : IsClosedImmersion i := hi.1
  have hepi : Epi (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion
      i
  exact Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one X' ⊤
    (S := ShortComplex.kernelSequence
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))
    (ShortComplex.shortExact_mk_kernel_ι _) (isZero_hgroup_one_idealSheafModule hi)

/-- **A first-order thickening of an affine scheme is affine.** -/
theorem isAffine_of_isFirstOrderThickening {i : X ⟶ X'} (hi : IsFirstOrderThickening i)
    [IsAffine X] : IsAffine X' :=
  isAffine_of_isThickening_of_surjective_appTop hi.isThickening
    (surjective_appTop_of_isFirstOrderThickening hi)

/-- **Any finite-order thickening of an affine scheme is affine.** The adic filtration of the
defining ideal sheaf interpolates between the closed subscheme and the ambient scheme by
first-order thickenings. -/
@[stacks 06AD "the finite-order case, the second proof the source gives (EGA I, Prop 5.1.9)"]
theorem isAffine_of_isFiniteOrderThickening {i : X ⟶ X'} (hi : IsFiniteOrderThickening i)
    [IsAffine X] : IsAffine X' :=
  isAffine_of_isFiniteOrderThickening_of_firstOrder
    (fun _ _ _ hj hZ => @isAffine_of_isFirstOrderThickening _ _ _ hj hZ) hi

end Stacks.Thickenings

end
