module

public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.PrincipalCutKernel
public import StacksFrontier.RingTheory.LocalCohomology.SupportedAugmentation

/-!
# The first local cohomology of a principal support, and the kernel of a principal cut

Let `A` be a Noetherian ring, let `I` be an ideal and let `f ∈ A`. The principal cut triangle
`RΓ_{V(I) ∩ V(f)}(K) ⟶ RΓ_{V(I)}(K) ⟶ RΓ_{V(I)}(K)[1/f]` has two consequences in this file,
obtained from the same long exact cohomology sequence.

Taking the cohomology sequence in degrees `i - 1` and `i`, the kernel of the widening map
`Hⁱ_{V(I) ∩ V(f)}(K) ⟶ Hⁱ_{V(I)}(K)` is the cokernel of the localization map
`Hⁱ⁻¹_{V(I)}(K) ⟶ Hⁱ⁻¹_{V(I)}(K)[1/f]`.

Taking `I = 0`, where the augmentation `RΓ_{Spec(A)}(K) ⟶ K` is invertible on a module placed in
degree zero, the same sequence in degrees `0` and `1` identifies `H¹_{V(f)}(N)` with the cokernel
of `N ⟶ N[1/f]`.

Combining the two, the iterated local cohomology group `H¹_f(Hⁱ⁻¹_{V(I)}(M))` is the kernel of
`Hⁱ_{V(I) ∩ V(f)}(M) ⟶ Hⁱ_{V(I)}(M)`.

## Main results

* `Stacks.LocalCohomology.nonempty_cokernel_locUnit_iso_kernel_changeOfSupport` — the kernel of
  the widening map is the cokernel of the localization map one degree down.
* `Stacks.LocalCohomology.nonempty_principalSupport_firstCohomology_iso_cokernel` —
  `H¹_{V(f)}(N) ≅ N[1/f] / N` for a module `N`.
* `Stacks.LocalCohomology.nonempty_iteratedPrincipalCut_iso_kernel_changeOfSupport` — the two
  combined: the iterated group `H¹_f(Hⁱ⁻¹_{V(I)}(M))` is that kernel.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- The localization unit on a cohomology module agrees, up to an isomorphism of its target,
with the cohomology of the derived localization unit. -/
private theorem exists_locUnit_homology_iso (A : Type u) [CommRing A] (a : A)
    (X : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    ∃ e : (locFunctor.{u, v} a).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj X) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((derivedLoc.{u, v} a).obj X),
      (locUnit.{u, v} a).app
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj X) ≫ e.hom =
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
          ((derivedLocUnit.{u, v} a).app X) := by
  let F := locFunctor.{u, v} a
  let ν := locUnit.{u, v} a
  let η := derivedLocUnit.{u, v} a
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i
  let Y := H.obj ((derivedLoc.{u, v} a).obj X)
  have hY : IsIso (ν.app Y) :=
    (NatTrans.isIso_app_iff_of_iso ν
      ((Dualizing.mapDerivedCategoryHomologyIso F i).app X)).mpr (locUnit_obj_isIso a (H.obj X))
  have hFη : IsIso (F.map (H.map (η.app X))) := by
    have hmap : IsIso ((derivedLoc.{u, v} a).map (η.app X)) := derivedLocUnit_map_isIso a X
    have hcomp : IsIso (((derivedLoc.{u, v} a) ⋙ H).map (η.app X)) := by
      dsimp only [Functor.comp_map]
      infer_instance
    exact (NatIso.isIso_map_iff (Dualizing.mapDerivedCategoryHomologyIso F i) (η.app X)).mp hcomp
  refine ⟨asIso (F.map (H.map (η.app X)) ≫ inv (ν.app Y)), ?_⟩
  show ν.app (H.obj X) ≫ F.map (H.map (η.app X)) ≫ inv (ν.app Y) = H.map (η.app X)
  rw [← Category.assoc, ← ν.naturality, Functor.id_map, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- In a four-term exact sequence of modules the cokernel of the first map is the kernel of the
last. -/
private theorem nonempty_cokernel_iso_kernel_of_exact {R : Type u} [Ring R]
    {W X Y Z : ModuleCat.{v} R} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (hfg : Function.Exact f.hom g.hom) (hgh : Function.Exact g.hom h.hom) :
    Nonempty (cokernel f ≅ kernel h) := by
  let e : (X ⧸ LinearMap.range f.hom) ≃ₗ[R] LinearMap.ker h.hom :=
    ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hfg).symm).trans
      g.hom.quotKerEquivRange).trans (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp hgh).symm)
  exact ⟨ModuleCat.cokernelIsoRangeQuotient f ≪≫ e.toModuleIso ≪≫ (ModuleCat.kernelIsoKer h).symm⟩

/-- **The cokernel of a localization unit is the kernel of a fibre inclusion.** If the second map
of a distinguished triangle is the derived localization unit at `a`, then the cokernel of the
localization map on `Hⁿ` of its middle term is the kernel of the map induced by the first map of
the triangle on `Hⁿ⁺¹`. -/
theorem nonempty_cokernel_locUnit_iso_kernel (A : Type u) [CommRing A] (a : A)
    {X Y : DerivedCategory (ModuleCat.{max u v} A)} (j : Y ⟶ X)
    (b : (derivedLoc.{u, v} a).obj X ⟶ Y⟦(1 : ℤ)⟧)
    (htri : Triangle.mk j ((derivedLocUnit.{u, v} a).app X) b ∈ distTriang _)
    (n i : ℤ) (hni : n + 1 = i) :
    Nonempty (cokernel ((locUnit.{u, v} a).app
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj X)) ≅
      kernel ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map j)) := by
  let T := Triangle.mk j ((derivedLocUnit.{u, v} a).app X) b
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A)
  obtain ⟨e⟩ := nonempty_cokernel_iso_kernel_of_exact ((H n).map T.mor₂)
    (DerivedCategory.HomologySequence.δ T n i hni) ((H i).map T.mor₁)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (DerivedCategory.HomologySequence.exact₃ T htri n i hni))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (DerivedCategory.HomologySequence.exact₁ T htri n i hni))
  obtain ⟨eH, heH⟩ := exists_locUnit_homology_iso.{u, v} A a X n
  exact ⟨cokernel.mapIso ((locUnit.{u, v} a).app ((H n).obj X)) ((H n).map T.mor₂)
    (Iso.refl _) eH (heH.trans (Category.id_comp _).symm) ≪≫ e⟩

/-- **The kernel of a principal cut is a cokernel of a localization map.** Over a Noetherian
ring, the kernel of the widening map `Hⁱ_{V(I + (f))}(K) ⟶ Hⁱ_{V(I)}(K)` is the cokernel of the
localization map `Hⁱ⁻¹_{V(I)}(K) ⟶ Hⁱ⁻¹_{V(I)}(K)[1/f]`. -/
theorem nonempty_cokernel_locUnit_iso_kernel_changeOfSupport (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (f : A)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    Nonempty (cokernel ((locUnit.{u, v} f).app
        (localCohomologyWithSupportIn.{u, v} A
          (PrimeSpectrum.zeroLocus (I : Set A)) K (i - 1))) ≅
      kernel (changeOfSupport.{u, v} A (PrimeSpectrum.zeroLocus_anti_mono_ideal
        (show I ≤ I ⊔ Ideal.span ({f} : Set A) from le_sup_left)) K i)) := by
  obtain ⟨b, htri⟩ := exists_principalCut_triangle.{u, v} A I f K
  exact nonempty_cokernel_locUnit_iso_kernel.{u, v} A f _ b htri (i - 1) i (by ring)

/-- The augmentation out of derived sections with support in the zero locus of the zero ideal is
invertible on a module placed in degree zero. -/
private theorem isIso_augmentation_zeroLocus_bot_app_single (A : Type u) [CommRing A]
    [IsNoetherianRing A] (N : ModuleCat.{max u v} A) :
    IsIso ((derivedSectionsWithSupportInAugmentation.{u, v} A
      (PrimeSpectrum.zeroLocus ((⊥ : Ideal A) : Set A))).app
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N)) :=
  isIso_derivedSectionsWithSupportInAugmentation_app_of_support_subset.{u, v} A _
    ((PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization) _ 0
    fun _ ↦ by
      rw [PrimeSpectrum.zeroLocus_bot]
      exact Set.subset_univ _

/-- **First local cohomology of a principal support.** Over a Noetherian ring, the first local
cohomology of a module `N` with support in `V(f)` is the cokernel of the localization map
`N ⟶ N[1/f]`. -/
theorem nonempty_principalSupport_firstCohomology_iso_cokernel (A : Type u) [CommRing A]
    [IsNoetherianRing A] (f : A) (N : ModuleCat.{max u v} A) :
    Nonempty (localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus ({f} : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) 1 ≅
      cokernel ((locUnit.{u, v} f).app N)) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A)
  have haug := isIso_augmentation_zeroLocus_bot_app_single.{u, v} A N
  let eaug := asIso ((derivedSectionsWithSupportInAugmentation.{u, v} A
    (PrimeSpectrum.zeroLocus ((⊥ : Ideal A) : Set A))).app K)
  let e₀ : (H 0).obj ((derivedSectionsWithSupportIn.{u, v} A
      (PrimeSpectrum.zeroLocus ((⊥ : Ideal A) : Set A))).obj K) ≅ N :=
    (H 0).mapIso eaug ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} A) 0).app N
  have hzero : IsZero ((H 1).obj ((derivedSectionsWithSupportIn.{u, v} A
      (PrimeSpectrum.zeroLocus ((⊥ : Ideal A) : Set A))).obj K)) :=
    ((H 1).mapIso eaug).isZero_iff.mpr (DerivedCategory.isZero_of_isLE K 0 1 (by omega))
  obtain ⟨b, htri⟩ := exists_principalCut_triangle.{u, v} A ⊥ f K
  obtain ⟨e⟩ := nonempty_cokernel_locUnit_iso_kernel.{u, v} A f _ b htri 0 1 (by ring)
  have hι : IsIso (kernel.ι ((H 1).map ((derivedSectionsWithSupportInInclusion.{u, v} A
      (PrimeSpectrum.zeroLocus_anti_mono_ideal
        (show (⊥ : Ideal A) ≤ ⊥ ⊔ Ideal.span ({f} : Set A) from le_sup_left))).app K))) := by
    rw [hzero.eq_of_tgt ((H 1).map _) 0]
    infer_instance
  have hset : PrimeSpectrum.zeroLocus ((⊥ ⊔ Ideal.span ({f} : Set A) : Ideal A) : Set A) =
      PrimeSpectrum.zeroLocus ({f} : Set A) := by
    rw [bot_sup_eq, PrimeSpectrum.zeroLocus_span]
  exact ⟨(changeOfSupportIsoOfEq.{u, v} A hset K 1).symm ≪≫ (asIso (kernel.ι _)).symm ≪≫
    e.symm ≪≫ cokernel.mapIso _ _ e₀ ((locFunctor.{u, v} f).mapIso e₀)
      ((locUnit.{u, v} f).naturality e₀.hom).symm⟩

/-- **The iterated local cohomology group is a kernel.** Over a Noetherian ring,
`H¹_f(Hⁱ⁻¹_{V(I)}(K))` is the kernel of the widening map
`Hⁱ_{V(I) ∩ V(f)}(K) ⟶ Hⁱ_{V(I)}(K)`. -/
theorem nonempty_iteratedPrincipalCut_iso_kernel_changeOfSupport (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (f : A)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    Nonempty (localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus ({f} : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (localCohomologyWithSupportIn.{u, v} A
            (PrimeSpectrum.zeroLocus (I : Set A)) K (i - 1))) 1 ≅
      kernel (changeOfSupport.{u, v} A
        (Set.inter_subset_left (s := PrimeSpectrum.zeroLocus (I : Set A))
          (t := PrimeSpectrum.zeroLocus ({f} : Set A))) K i)) := by
  obtain ⟨e₁⟩ := nonempty_principalSupport_firstCohomology_iso_cokernel.{u, v} A f
    (localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A)) K (i - 1))
  obtain ⟨e₂⟩ := nonempty_cokernel_locUnit_iso_kernel_changeOfSupport.{u, v} A I f K i
  have hset : PrimeSpectrum.zeroLocus ((I ⊔ Ideal.span ({f} : Set A) : Ideal A) : Set A) =
      PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus ({f} : Set A) := by
    rw [PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_span]
  refine ⟨e₁ ≪≫ e₂ ≪≫ kernel.mapIso _ _ (changeOfSupportIsoOfEq.{u, v} A hset K i)
    (Iso.refl _) ?_⟩
  rw [Iso.refl_hom, Category.comp_id, changeOfSupportIsoOfEq_hom, changeOfSupport_trans]

end Stacks.LocalCohomology

end
