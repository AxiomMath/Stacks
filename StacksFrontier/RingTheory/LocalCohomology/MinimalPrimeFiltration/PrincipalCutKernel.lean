module

public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.PrincipalCutLift

/-!
# The kernel of a principal cut on local cohomology

Let `A` be a Noetherian ring, let `I` be an ideal and let `f ∈ A`. Local cohomology with support
in `V(I) ∩ V(f)` sits in a distinguished triangle
`RΓ_{V(I) ∩ V(f)}(K) ⟶ RΓ_{V(I)}(K) ⟶ RΓ_{V(I)}(K)[1/f]`
whose first map is the canonical widening of the support and whose second is the localization
unit. A morphism `K ⟶ L` which kills `Hⁱ⁻¹_{V(I)}` kills every class in `Hⁱ_{V(I) ∩ V(f)}(K)`
dying in `Hⁱ_{V(I)}(K)`.

## Main results

* `Stacks.LocalCohomology.exists_principalCut_triangle` — the triangle itself.
* `Stacks.LocalCohomology.principalCut_map_eq_zero_of_previousDegree` — a class with support in
  `V(I) ∩ V(f)` dying on `V(I)` is killed by any morphism which kills `Hⁱ⁻¹_{V(I)}`.
* `Stacks.LocalCohomology.principalCut_map_eq_zero_of_previousDegree_of_support_eq` — the same
  statement for a support presented as an intersection of zero loci.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

attribute [local instance] derivedPowerTorsionProperty_isClosedUnderIsomorphisms
  derivedPowerTorsionProperty_isTriangulated

/-- A module which is power torsion for an ideal is power torsion for every smaller ideal. -/
private theorem isIPowerTorsion_mono {A : Type u} [CommRing A] {I J : Ideal A} (hIJ : I ≤ J)
    {X : Type*} [AddCommGroup X] [Module A X] (hX : IsIPowerTorsion A X J) :
    IsIPowerTorsion A X I := by
  intro x
  obtain ⟨n, hn, hkill⟩ := hX x
  exact ⟨n, hn, fun c hc => hkill c ((pow_le_pow_left' hIJ n) hc)⟩

/-- A localization of an `I`-power-torsion module is `I`-power torsion. -/
private theorem isIPowerTorsion_of_isLocalizedModule {A : Type u} [CommRing A]
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (S : Submonoid A) (loc : X →ₗ[A] Y) [IsLocalizedModule S loc] (I : Ideal A)
    (hX : IsIPowerTorsion A X I) : IsIPowerTorsion A Y I := by
  intro y
  obtain ⟨⟨x, s⟩, hy⟩ := IsLocalizedModule.mk'_surjective S loc y
  obtain ⟨n, hn, hkill⟩ := hX x
  refine ⟨n, hn, fun c hc => ?_⟩
  rw [← hy]
  change c • IsLocalizedModule.mk' loc x s = 0
  rw [← IsLocalizedModule.mk'_smul, hkill c hc]
  simp

/-- The fibre of an idempotent unit `X ⟶ L(X)`, together with the universal property it enjoys
among the objects annihilated by `L`. -/
private theorem exists_unit_fiber
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (L : C ⥤ C) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
    (unit : 𝟭 C ⟶ L) (hunit : ∀ X, IsIso (unit.app (L.obj X)))
    (hmap : ∀ X, IsIso (L.map (unit.app X))) (X : C) :
    ∃ (Y : C) (inclusion : Y ⟶ X) (boundary : L.obj X ⟶ Y⟦(1 : ℤ)⟧),
      Triangle.mk inclusion (unit.app X) boundary ∈ distTriang C ∧ IsZero (L.obj Y) ∧
      ∀ W, IsZero (L.obj W) →
        Function.Bijective (fun arrow : W ⟶ Y => arrow ≫ inclusion) := by
  obtain ⟨Y, second, third, htriangle⟩ := distinguished_cocone_triangle (unit.app X)
  let triangle := (Triangle.mk (unit.app X) second third).invRotate
  have htriangle' : triangle ∈ distTriang C := inv_rot_of_distTriang _ htriangle
  refine ⟨triangle.obj₁, triangle.mor₁, triangle.mor₃, htriangle', ?_, ?_⟩
  · exact Triangle.isZero₁_of_isIso₂ _ (L.map_distinguished _ htriangle') (hmap X)
  · intro W hW
    have vanish {Z : C} (arrow : W ⟶ L.obj Z) : arrow = 0 := by
      have : IsIso (unit.app (L.obj Z)) := hunit Z
      apply (cancel_mono (unit.app (L.obj Z))).mp
      rw [CategoryTheory.Limits.zero_comp, ← Functor.id_map (f := arrow),
        unit.naturality, hW.eq_of_tgt (unit.app W) 0, CategoryTheory.Limits.zero_comp]
    have vanishShift (arrow : W ⟶ triangle.obj₃⟦(-1 : ℤ)⟧) : arrow = 0 :=
      (cancel_mono ((L.commShiftIso (-1)).app X).inv).mp
        ((vanish _).trans CategoryTheory.Limits.zero_comp.symm)
    have kernel (arrow : W ⟶ triangle.obj₁) (h : arrow ≫ triangle.mor₁ = 0) : arrow = 0 := by
      obtain ⟨preimage, hpreimage⟩ := Triangle.coyoneda_exact₂ triangle.invRotate
        (inv_rot_of_distTriang _ htriangle') arrow h
      rw [hpreimage, vanishShift preimage]
      exact CategoryTheory.Limits.zero_comp
    constructor
    · intro left right heq
      change left ≫ triangle.mor₁ = right ≫ triangle.mor₁ at heq
      exact sub_eq_zero.mp (kernel _ (by rw [Preadditive.sub_comp, heq, sub_self]))
    · intro arrow
      obtain ⟨preimage, hpreimage⟩ := Triangle.coyoneda_exact₂ triangle htriangle' arrow
        (vanish _)
      exact ⟨preimage, hpreimage.symm⟩

/-- Two objects of a full subcategory with the same universal property over an object of the
ambient category are uniquely isomorphic over it. -/
private theorem exists_iso_of_universalArrow
    {C : Type*} [Category C] {P : C → Prop} {K Y Z : C} (a : Y ⟶ K) (b : Z ⟶ K)
    (hY : P Y) (hZ : P Z)
    (hYu : ∀ W, P W → Function.Bijective (fun g : W ⟶ Y => g ≫ a))
    (hZu : ∀ W, P W → Function.Bijective (fun g : W ⟶ Z => g ≫ b)) :
    ∃ e : Z ≅ Y, e.hom ≫ a = b := by
  obtain ⟨φ, hφ⟩ := (hYu Z hZ).surjective b
  obtain ⟨ψ, hψ⟩ := (hZu Y hY).surjective a
  have hφ' : φ ≫ a = b := hφ
  have hψ' : ψ ≫ b = a := hψ
  refine ⟨⟨φ, ψ, (hZu Z hZ).injective ?_, (hYu Y hY).injective ?_⟩, hφ'⟩
  · rw [Category.assoc, hψ', hφ', Category.id_comp]
  · rw [Category.assoc, hφ', hψ', Category.id_comp]

/-- Derived sections with support in `V(I)` have `I`-power-torsion cohomology. -/
private theorem derivedPowerTorsion_derivedSectionsWithSupportIn
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI
      ((derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).obj K) := by
  have := isIso_compareSectionsWithSupportLocalCohomology_app.{u, v} A I hI K
  exact (Dualizing.derivedPowerTorsionProperty A I hI).prop_of_iso
    (asIso ((compareSectionsWithSupportLocalCohomology.{u, v} A I hI).app K)).symm
    ((Dualizing.localCohomologyFunctor.{u, max u v} A I hI).obj K).property

/-- Localizing away from an element preserves `I`-power-torsion cohomology. -/
private theorem derivedPowerTorsion_derivedLoc
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (f : A)
    (X : DerivedCategory (ModuleCat.{max u v} A))
    (hX : Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI X) :
    Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI ((derivedLoc.{u, v} f).obj X) := by
  intro i
  refine (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
    ((Dualizing.mapDerivedCategoryHomologyIso (locFunctor.{u, v} f) i).app X).symm ?_
  exact isIPowerTorsion_of_isLocalizedModule (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) _) I (hX i)

/-- An object has `(f)`-power-torsion cohomology iff localization away from `f` kills it. -/
private theorem derivedPowerTorsion_span_singleton_iff
    {A : Type u} [CommRing A] (f : A) (Y : DerivedCategory (ModuleCat.{max u v} A)) :
    Dualizing.derivedPowerTorsionProperty.{u, max u v} A
      (Ideal.span ({f} : Set A)) (Submodule.fg_span_singleton f) Y ↔
        IsZero ((derivedLoc.{u, v} f).obj Y) := by
  classical
  refine (derivedPowerTorsion_iff_loc.{u, v} (Ideal.span ({f} : Set A))
    (Submodule.fg_span_singleton f) {f} (by simp) Y).trans ?_
  simp

/-- An `I`-power-torsion object killed by localization away from `f` is
`(I + (f))`-power torsion. -/
private theorem derivedPowerTorsion_sup_of_isZero_derivedLoc
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} (hI : I.FG) (f : A)
    (hJ : (I ⊔ Ideal.span ({f} : Set A)).FG) {Y : DerivedCategory (ModuleCat.{max u v} A)}
    (hYI : Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI Y)
    (hY : IsZero ((derivedLoc.{u, v} f).obj Y)) :
    Dualizing.derivedPowerTorsionProperty.{u, max u v} A (I ⊔ Ideal.span ({f} : Set A)) hJ Y := by
  have hYf := (derivedPowerTorsion_span_singleton_iff.{u, v} f Y).mpr hY
  intro i
  refine isIPowerTorsion_of_support_subset hJ ?_
  rw [PrimeSpectrum.zeroLocus_sup]
  exact fun p hp => ⟨support_subset_zeroLocus_of_isIPowerTorsion (hYI i) hp,
    support_subset_zeroLocus_of_isIPowerTorsion (hYf i) hp⟩

/-- A `(I + (f))`-power-torsion object is killed by localization away from `f`. -/
private theorem isZero_derivedLoc_of_derivedPowerTorsion_sup
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} (f : A)
    (hJ : (I ⊔ Ideal.span ({f} : Set A)).FG) {Z : DerivedCategory (ModuleCat.{max u v} A)}
    (hZ : Dualizing.derivedPowerTorsionProperty.{u, max u v} A
      (I ⊔ Ideal.span ({f} : Set A)) hJ Z) :
    IsZero ((derivedLoc.{u, v} f).obj Z) := by
  exact (derivedPowerTorsion_span_singleton_iff.{u, v} f Z).mp
    fun i => isIPowerTorsion_mono le_sup_right (hZ i)

/-- Widening the support is compatible with the augmentations, componentwise. -/
private theorem inclusion_app_comp_augmentation_app (A : Type u) [CommRing A]
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) (K : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedSectionsWithSupportInInclusion.{u, v} A h).app K ≫
      (derivedSectionsWithSupportInAugmentation.{u, v} A T).app K =
        (derivedSectionsWithSupportInAugmentation.{u, v} A S).app K :=
  NatTrans.congr_app (derivedSectionsWithSupportInInclusion_comp_augmentation.{u, v} A h) K

/-- Over a Noetherian ring, derived sections with support in `V(I + (f))` are the fibre of the
localization away from `f` of derived sections with support in `V(I)`, with the widening of the
support as the first map of the triangle. -/
theorem exists_principalCut_triangle
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (f : A)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    ∃ boundary, Triangle.mk
        ((derivedSectionsWithSupportInInclusion.{u, v} A
          (PrimeSpectrum.zeroLocus_anti_mono_ideal
            (show I ≤ I ⊔ Ideal.span ({f} : Set A) from le_sup_left))).app K)
        ((derivedLocUnit.{u, v} f).app
          ((derivedSectionsWithSupportIn.{u, v} A
            (PrimeSpectrum.zeroLocus (I : Set A))).obj K)) boundary ∈ distTriang _ := by
  classical
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  have hJ : (I ⊔ Ideal.span ({f} : Set A)).FG := Ideal.fg_of_isNoetherianRing _
  have hJI : I ≤ I ⊔ Ideal.span ({f} : Set A) := le_sup_left
  obtain ⟨Y, j, boundary, htri, hzeroY, huniv⟩ :=
    exists_unit_fiber (derivedLoc.{u, v} f) (derivedLocUnit.{u, v} f)
      (fun Z => derivedLocUnit_obj_isIso.{u, v} f Z)
      (fun Z => derivedLocUnit_map_isIso.{u, v} f Z)
      ((derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).obj K)
  have hXI := derivedPowerTorsion_derivedSectionsWithSupportIn.{u, v} A I hI K
  have hYI : Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI Y :=
    (Dualizing.derivedPowerTorsionProperty A I hI).ext_of_isTriangulatedClosed₁ _ htri hXI
      (derivedPowerTorsion_derivedLoc.{u, v} A I hI f _ hXI)
  have hYJ := derivedPowerTorsion_sup_of_isZero_derivedLoc.{u, v} hI f hJ hYI hzeroY
  have hunivY : ∀ Z, Dualizing.derivedPowerTorsionProperty.{u, max u v} A
      (I ⊔ Ideal.span ({f} : Set A)) hJ Z → Function.Bijective (fun g : Z ⟶ Y =>
        g ≫ (j ≫ (derivedSectionsWithSupportInAugmentation.{u, v} A
          (PrimeSpectrum.zeroLocus (I : Set A))).app K)) := by
    intro Z hZ
    have hZf := isZero_derivedLoc_of_derivedPowerTorsion_sup.{u, v} f hJ hZ
    have h2 := bijective_comp_derivedSectionsWithSupportInAugmentation.{u, v} A I K Z
      (fun i => isIPowerTorsion_mono hJI (hZ i))
    simpa only [Function.comp_def, Category.assoc] using h2.comp (huniv Z hZf)
  have hJK := derivedPowerTorsion_derivedSectionsWithSupportIn.{u, v} A
    (I ⊔ Ideal.span ({f} : Set A)) hJ K
  obtain ⟨e, he⟩ := exists_iso_of_universalArrow
    (j ≫ (derivedSectionsWithSupportInAugmentation.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A))).app K)
    ((derivedSectionsWithSupportInAugmentation.{u, v} A
      (PrimeSpectrum.zeroLocus ((I ⊔ Ideal.span ({f} : Set A) : Ideal A) : Set A))).app K)
    hYJ hJK hunivY
    (fun Z hZ => bijective_comp_derivedSectionsWithSupportInAugmentation.{u, v} A
      (I ⊔ Ideal.span ({f} : Set A)) K Z hZ)
  have hji : e.hom ≫ j = (derivedSectionsWithSupportInInclusion.{u, v} A
      (PrimeSpectrum.zeroLocus_anti_mono_ideal hJI)).app K := by
    refine (bijective_comp_derivedSectionsWithSupportInAugmentation.{u, v} A I K _
      (fun i => isIPowerTorsion_mono hJI (hJK i))).injective ?_
    rw [Category.assoc, he]
    exact (inclusion_app_comp_augmentation_app.{u, v} A
      (PrimeSpectrum.zeroLocus_anti_mono_ideal hJI) K).symm
  refine ⟨boundary ≫ (e.inv)⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ htri _ (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_)
  · simp [hji]
  · simp
  · simp [← Functor.map_comp]

/-- A morphism of distinguished triangles whose third component is zero on `Hⁱ⁻¹` kills every
class of `Hⁱ` of the first object which dies under the first map of the triangle. -/
private theorem triangle_hom₁_map_eq_zero {A : Type u} [CommRing A]
    {T T' : Triangle (DerivedCategory (ModuleCat.{max u v} A))}
    (hT : T ∈ distTriang _) (_hT' : T' ∈ distTriang _) (φ : T ⟶ T') (i : ℤ)
    (hφ : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (i - 1)).map φ.hom₃ = 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj T.obj₁)
    (hx : ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map T.mor₁).hom x = 0) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map φ.hom₁).hom x = 0 := by
  have hexact := DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hexact
  obtain ⟨w, hw⟩ := (hexact x).mp hx
  have hnat : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (i - 1)).map φ.hom₃ ≫
        DerivedCategory.HomologySequence.δ T' (i - 1) i (by omega) =
      DerivedCategory.HomologySequence.δ T (i - 1) i (by omega) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map φ.hom₁ :=
    Functor.homologySequenceδ_naturality
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0) φ (i - 1) i (by omega)
  rw [hφ, zero_comp] at hnat
  rw [← hw]
  have hcomp := congrArg (fun ψ => ModuleCat.Hom.hom ψ w) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hcomp
  exact hcomp.symm

/-- Localization away from `f` preserves morphisms which vanish on `Hⁿ`. -/
private theorem homologyFunctor_map_derivedLoc_map_eq_zero {A : Type u} [CommRing A] (f : A)
    {X Y : DerivedCategory (ModuleCat.{max u v} A)} (g : X ⟶ Y) (n : ℤ)
    (hg : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map g = 0) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
      ((derivedLoc.{u, v} f).map g) = 0 := by
  refine (cancel_mono
    ((Dualizing.mapDerivedCategoryHomologyIso (locFunctor.{u, v} f) n).hom.app Y)).mp ?_
  have hn : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
        ((derivedLoc.{u, v} f).map g) ≫
        (Dualizing.mapDerivedCategoryHomologyIso (locFunctor.{u, v} f) n).hom.app Y =
      (Dualizing.mapDerivedCategoryHomologyIso (locFunctor.{u, v} f) n).hom.app X ≫
        (locFunctor.{u, v} f).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map g) :=
    (Dualizing.mapDerivedCategoryHomologyIso (locFunctor.{u, v} f) n).hom.naturality g
  rw [hg, Functor.map_zero, comp_zero] at hn
  rwa [zero_comp]

/-- Over a Noetherian ring, if a morphism `K ⟶ L` induces the zero map on `Hⁱ⁻¹_{V(I)}`, then it
kills every class in `Hⁱ_{V(I + (f))}(K)` whose image in `Hⁱ_{V(I)}(K)` vanishes. -/
theorem principalCut_map_eq_zero_of_previousDegree
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (f : A)
    {K L : DerivedCategory (ModuleCat.{max u v} A)} (t : K ⟶ L) (i : ℤ)
    (hzero : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (i - 1)).map
      ((derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).map t) = 0)
    (x : localCohomologyWithSupportIn.{u, v} A
      (PrimeSpectrum.zeroLocus ((I ⊔ Ideal.span ({f} : Set A) : Ideal A) : Set A)) K i)
    (hx : (changeOfSupport.{u, v} A (PrimeSpectrum.zeroLocus_anti_mono_ideal
      (show I ≤ I ⊔ Ideal.span ({f} : Set A) from le_sup_left)) K i).hom x = 0) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
      ((derivedSectionsWithSupportIn.{u, v} A
        (PrimeSpectrum.zeroLocus ((I ⊔ Ideal.span ({f} : Set A) : Ideal A) : Set A))).map t)).hom
      x = 0 := by
  classical
  have hJI : I ≤ I ⊔ Ideal.span ({f} : Set A) := le_sup_left
  obtain ⟨bK, hK⟩ := exists_principalCut_triangle.{u, v} A I f K
  obtain ⟨bL, hL⟩ := exists_principalCut_triangle.{u, v} A I f L
  obtain ⟨first, hfirst, hthird⟩ := complete_distinguished_triangle_morphism₁ _ _ hK hL
    ((derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).map t)
    ((derivedLoc.{u, v} f).map
      ((derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).map t))
    ((derivedLocUnit.{u, v} f).naturality _).symm
  have hfirsteq : first = (derivedSectionsWithSupportIn.{u, v} A
      (PrimeSpectrum.zeroLocus ((I ⊔ Ideal.span ({f} : Set A) : Ideal A) : Set A))).map t := by
    refine (bijective_comp_derivedSectionsWithSupportInAugmentation.{u, v} A
      (I ⊔ Ideal.span ({f} : Set A)) L _
      (derivedPowerTorsion_derivedSectionsWithSupportIn.{u, v} A
        (I ⊔ Ideal.span ({f} : Set A)) (Ideal.fg_of_isNoetherianRing _) K)).injective ?_
    have hnat := (derivedSectionsWithSupportInInclusion.{u, v} A
      (PrimeSpectrum.zeroLocus_anti_mono_ideal hJI)).naturality t
    have hfirst' : (derivedSectionsWithSupportInInclusion.{u, v} A
          (PrimeSpectrum.zeroLocus_anti_mono_ideal hJI)).app K ≫
        (derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).map t =
        first ≫ (derivedSectionsWithSupportInInclusion.{u, v} A
          (PrimeSpectrum.zeroLocus_anti_mono_ideal hJI)).app L := hfirst
    change first ≫ _ = _ ≫ _
    rw [← inclusion_app_comp_augmentation_app.{u, v} A
      (PrimeSpectrum.zeroLocus_anti_mono_ideal hJI) L, ← Category.assoc, ← Category.assoc,
      ← hfirst', hnat]
  rw [← hfirsteq]
  exact triangle_hom₁_map_eq_zero hK hL
    (Triangle.homMk _ _ first
      ((derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).map t)
      ((derivedLoc.{u, v} f).map ((derivedSectionsWithSupportIn.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).map t)) hfirst
      ((derivedLocUnit.{u, v} f).naturality _).symm hthird) i
    (homologyFunctor_map_derivedLoc_map_eq_zero.{u, v} f _ (i - 1) hzero) x hx

/-- Over a Noetherian ring, let `S = V(I) ∩ V(f)`. If a morphism `K ⟶ L` induces the zero map on
`Hⁱ⁻¹_{V(I)}`, then it kills every class in `Hⁱ_S(K)` whose image in `Hⁱ_{V(I)}(K)` vanishes. -/
theorem principalCut_map_eq_zero_of_previousDegree_of_support_eq
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (f : A)
    (S : Set (PrimeSpectrum A))
    (hS : S = PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus ({f} : Set A))
    (hSI : S ⊆ PrimeSpectrum.zeroLocus (I : Set A))
    {K L : DerivedCategory (ModuleCat.{max u v} A)} (t : K ⟶ L) (i : ℤ)
    (hzero : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (i - 1)).map
      ((derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).map t) = 0)
    (x : localCohomologyWithSupportIn.{u, v} A S K i)
    (hx : (changeOfSupport.{u, v} A hSI K i).hom x = 0) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
      ((derivedSectionsWithSupportIn.{u, v} A S).map t)).hom x = 0 := by
  obtain rfl : PrimeSpectrum.zeroLocus ((I ⊔ Ideal.span ({f} : Set A) : Ideal A) : Set A) = S := by
    rw [hS, PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_span]
  exact principalCut_map_eq_zero_of_previousDegree.{u, v} A I f t i hzero x hx

end Stacks.LocalCohomology

end
