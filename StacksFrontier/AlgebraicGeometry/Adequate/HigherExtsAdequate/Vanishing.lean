module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Adequate.Splitting06V7Large
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Extensions
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.Basic
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.LinearlyAdequate
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.Coreflection
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Higher exts of adequate functors

Let `A` be a commutative ring, let `𝒫` be the category of module-valued functors on the
commutative `A`-algebras and let `Q : 𝒫 ⥤ 𝒜` be the coreflection onto the adequate functors,
right adjoint to the inclusion `i` and left exact. Then the higher right derived functors
`R ᵖ Q` vanish in positive degrees on every adequate functor.

The extension of scalars `M̲ : B ↦ B ⊗[A] M` of an `A`-module `M` is treated first. On an
injective resolution `M̲ → I ⁎` the complex `Q(I ⁎)` is exact in positive degrees: the linearly
adequate functors cover every adequate functor and admit no extensions of positive degree into
`M̲`, so every cycle of `Q(I ⁎)` is a boundary after pulling back along such a cover. A general
adequate functor is the kernel of a map `M̲ ⟶ N̲` of extensions, and right acyclicity passes from
`M̲`, `N̲` and the extension of the cokernel to that kernel.

## Main results

* `AdequateFunctor.subsingleton_zExt_one_of_isLinearlyAdequate` — `Ext¹(L, F) = 0` for `L`
  linearly adequate and `F` adequate, from the splitting of Tag 06V7.
* `AdequateFunctor.isZero_rightDerivedPlus_one_adequateCoreflection` — `R ¹Q(F) = 0` for every
  adequate functor `F`, with no hypothesis.
* `AdequateFunctor.rightAcyclic_adequateCoreflection_of_isAdequate` — an adequate functor is
  right acyclic for `Q`.
* `AdequateFunctor.isZero_rightDerivedPlus_adequateCoreflection` — `R ᵖ Q(F) = 0` for every
  `p > 0` and every adequate functor `F`.

## Implementation notes

Degree one needs no input beyond Tag 06V7: the extension groups `Ext¹(L, F)` from linearly
adequate functors vanish for every adequate target `F`, so the covering argument runs on an
injective resolution of `F` itself.

The vanishing of the positive extension groups from a linearly adequate functor into the
extension of a module is available only relative to the same vanishing for the extension of a
finitely presented module, which is therefore carried as a hypothesis here and recorded with the
tag. The hypothesis is universally quantified over both modules, since the proof applies it to
the two modules of a kernel presentation and to their cokernel.

That input is Tag 06ZG. The library proves it in degree `2`,
`AdequateFunctor.subsingleton_zExt_moduleExtension_two`, and there at the module universe
`max u v`; the hypothesis is needed in every positive degree and at the value universe of the
coreflection, so that declaration does not discharge it. A general form of Tag 06ZG discharges
it with no bridge as soon as its module universe is a free parameter, as it is for
`AdequateFunctor.subsingleton_zExt_of_isLinearlyAdequate`.

The value universe is the one in which the coreflection is constructed. Adequacy is closed under
finite products there, which is what makes the adequate functors an abelian category; the closure
property is restated at that universe so that instance search finds it.

## References

* [Stacks Project, Tag 06UX](https://stacks.math.columbia.edu/tag/06UX)
* [Stacks Project, Tag 06Z7](https://stacks.math.columbia.edu/tag/06Z7)
* [Stacks Project, Tag 06ZG](https://stacks.math.columbia.edu/tag/06ZG)
* [Stacks Project, Tag 06ZH](https://stacks.math.columbia.edu/tag/06ZH)
* [Stacks Project, Tag 06ZI](https://stacks.math.columbia.edu/tag/06ZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t c d u v w

namespace AdequateFunctor

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ## Abstract ingredients -/

/-- A morphism into the degree-`n` term of an injective resolution of `Y` which is killed by the
differential factors through the previous differential as soon as `Ext ⁿ(G, Y)` vanishes. -/
private lemma exists_comp_eq_of_subsingleton_zExt
    {C : Type c} [Category.{d} C] [Abelian C] [HasDerivedCategory.{max c d} C]
    {Y : C} (I : InjectiveResolution Y) {G : C} {n : ℕ} (hn : 0 < n)
    (hExt : Subsingleton (Abelian.zExt G Y (n : ℤ)))
    (f : G ⟶ I.cocomplex.X n) (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    ∃ g : G ⟶ I.cocomplex.X (n - 1), g ≫ I.cocomplex.d (n - 1) n = f := by
  let _ : HasExt.{max c d} C := HasExt.standard C
  have hExtE : Subsingleton (Abelian.Ext.{max c d} G Y n) :=
    (Abelian.Ext.homEquiv.{max c d, max c d} (X := G) (Y := Y) (n := n)).subsingleton_congr.mpr
      hExt
  exact (I.extMk_eq_zero_iff f (n + 1) rfl hf (n - 1) (by omega)).1
    (@Subsingleton.elim _ hExtE _ _)

/-- Let `Q` be right adjoint to the inclusion of a strictly full subcategory `P` of an abelian
category with enough injectives, and let `I` be an injective resolution of `Y`. If every object
of `P` is covered by a jointly epimorphic family of objects of `P` admitting no extensions of
degree `n` into `Y`, then `Q(I)` is exact in degree `n`. -/
private lemma exactAt_mapHomologicalComplex_of_cover
    {C : Type c} [Category.{d} C] [Abelian C] [HasDerivedCategory.{max c d} C]
    [EnoughInjectives C] (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts]
    {Q : C ⥤ P.FullSubcategory} [Q.Additive] (adj : P.ι ⊣ Q)
    {Y : C} (I : InjectiveResolution Y) (n : ℕ) (hn : 0 < n)
    (hcover : ∀ K : C, P K → ∃ (J : Type t) (L : J → C) (g : ∀ j, L j ⟶ K),
      (∀ j, P (L j)) ∧ (∀ j, Subsingleton (Abelian.zExt (L j) Y (n : ℤ))) ∧
        ∀ {Z : C} (a b : K ⟶ Z), (∀ j, g j ≫ a = g j ≫ b) → a = b) :
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).ExactAt n := by
  classical
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1)
    (ComplexShape.prev_eq' (ComplexShape.up ℕ)
      (ComplexShape.up_mk (n - 1) n (Nat.sub_add_cancel hn))) (by simp)]
  let S : ShortComplex P.FullSubcategory := ShortComplex.mk
    (Q.map (I.cocomplex.d (n - 1) n)) (Q.map (I.cocomplex.d n (n + 1)))
    (by rw [← Q.map_comp, I.cocomplex.d_comp_d, Q.map_zero])
  show S.Exact
  rw [ShortComplex.exact_iff_epi_kernel_lift S]
  apply P.ι.epi_of_epi_map
  obtain ⟨J, L, gcov, hLP, hLExt, hje⟩ := hcover (P.ι.obj (kernel S.g)) (kernel S.g).property
  have key : ∀ j, ∃ ψ : (⟨L j, hLP j⟩ : P.FullSubcategory) ⟶ S.X₁,
      gcov j = P.ι.map ψ ≫ P.ι.map (kernel.lift S.g S.f S.zero) := by
    intro j
    let LB : P.FullSubcategory := ⟨L j, hLP j⟩
    let gi : LB ⟶ kernel S.g := ObjectProperty.homMk (gcov j)
    let φ : LB ⟶ S.X₂ := gi ≫ kernel.ι S.g
    have hcycle : φ ≫ Q.map (I.cocomplex.d n (n + 1)) = 0 := by
      show (gi ≫ kernel.ι S.g) ≫ S.g = 0
      rw [Category.assoc, kernel.condition, comp_zero]
    have hfA : (adj.homEquiv LB (I.cocomplex.X n)).symm φ ≫ I.cocomplex.d n (n + 1) = 0 := by
      apply (adj.homEquiv LB (I.cocomplex.X (n + 1))).injective
      rwa [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, adj.homAddEquiv_zero]
    obtain ⟨gA, hgA⟩ := exists_comp_eq_of_subsingleton_zExt I hn (hLExt j) _ hfA
    refine ⟨adj.homEquiv LB (I.cocomplex.X (n - 1)) gA, ?_⟩
    have hφ : φ = adj.homEquiv LB (I.cocomplex.X (n - 1)) gA ≫ S.f := by
      apply (adj.homEquiv LB (I.cocomplex.X n)).symm.injective
      rw [adj.homEquiv_naturality_right_symm, Equiv.symm_apply_apply]
      exact hgA.symm
    have : gi = adj.homEquiv LB (I.cocomplex.X (n - 1)) gA ≫ kernel.lift S.g S.f S.zero := by
      apply (cancel_mono (kernel.ι S.g)).1
      rwa [Category.assoc, kernel.lift_ι]
    rw [← P.ι.map_comp, ← this]
    rfl
  refine ⟨fun a b hab => hje a b fun j => ?_⟩
  obtain ⟨ψ, hψ⟩ := key j
  rw [hψ, Category.assoc, Category.assoc, hab]

/-- The coreflection of an epimorphism between objects of the subcategory is an epimorphism:
the unit of the adjunction is invertible, so the coreflection of a morphism between objects of
the subcategory is that morphism read inside the subcategory. -/
private lemma epi_map_of_coreflection {C : Type c} [Category.{d} C] (P : ObjectProperty C)
    (Q : C ⥤ P.FullSubcategory) (adj : P.ι ⊣ Q) {X Y : C} (f : X ⟶ Y) [Epi f]
    (hX : P X) (hY : P Y) : Epi (Q.map f) := by
  let f' : (⟨X, hX⟩ : P.FullSubcategory) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk f
  have : Epi f' := P.ι.epi_of_epi_map (show Epi (P.ι.map f') from inferInstanceAs (Epi f))
  have : Functor.PreservesEpimorphisms (P.ι ⋙ Q) :=
    Functor.PreservesEpimorphisms.of_iso (asIso adj.unit)
  exact inferInstanceAs (Epi ((P.ι ⋙ Q).map f'))

/-- Right acyclicity for a coreflection passes to the kernel of a morphism of objects of the
subcategory whose source, target and cokernel are right acyclic. -/
private lemma rightAcyclic_kernel_of_coreflection
    {C : Type c} [Category.{d} C] [Abelian C] [HasDerivedCategory.{max c d} C]
    [EnoughInjectives C] (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts]
    [HasDerivedCategory P.FullSubcategory] (Q : C ⥤ P.FullSubcategory) [Q.Additive]
    [PreservesFiniteLimits Q] (adj : P.ι ⊣ Q) {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y)
    (hQX : Q.rightAcyclic X) (hQY : Q.rightAcyclic Y)
    (hQc : Q.rightAcyclic (cokernel f)) : Q.rightAcyclic (kernel f) := by
  have hc : P (cokernel f) := P.prop_cokernel f hX hY
  have hi : P (Abelian.image f) := P.prop_kernel (cokernel.π f) hY hc
  have hQi : Q.rightAcyclic (Abelian.image f) :=
    ((Q.rightAcyclic_and_shortExact_map_of_shortExact
      (ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f) (kernel.condition _))
      ⟨ShortComplex.exact_kernel _⟩).2.2 hQY hQc
      (epi_map_of_coreflection P Q adj (cokernel.π f) hY hc)).1
  have hk : Q.rightAcyclic (kernel (Abelian.factorThruImage f)) :=
    ((Q.rightAcyclic_and_shortExact_map_of_shortExact
      (ShortComplex.mk (kernel.ι (Abelian.factorThruImage f)) (Abelian.factorThruImage f)
        (kernel.condition _)) ⟨ShortComplex.exact_kernel _⟩).2.2 hQX hQi
      (epi_map_of_coreflection P Q adj (Abelian.factorThruImage f) hX hi)).1
  exact ObjectProperty.prop_of_iso Q.rightAcyclic
    ((kernelCompMono (Abelian.factorThruImage f) (Abelian.image.ι f)).symm ≪≫
      kernelIsoOfEq (Abelian.image.fac f)) hk

/-! ## The adequate functors -/

variable (A : Type u) [CommRing A]

/-- Adequacy at the value universe carrying the coreflection is closed under finite products. -/
public instance isClosedUnderFiniteProducts_adequate_coreflection :
    (adequate.{u, v, max (u + 1) (v + 1) w} A).IsClosedUnderFiniteProducts :=
  adequate_isClosedUnderFiniteProducts.{u, v, max (u + 1) (v + 1) w} A

/-- The coreflection onto the adequate functors is additive, being a right adjoint of an additive
functor. -/
public instance additive_adequateCoreflection : (adequateCoreflection.{u, v, w} A).Additive :=
  (adequateCoreflectionAdjunction.{u, v, w} A).right_adjoint_additive

/-- Every adequate module-valued functor carries a jointly epimorphic family of morphisms from
linearly adequate functors. -/
@[stacks 06UX "the linearly adequate functors jointly cover an adequate functor"]
public lemma exists_jointlyEpi_isLinearlyAdequate
    (K : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (hK : IsAdequate (𝟭 _) K) :
    ∃ (J : Type (max (u + 1) (v + 1) w))
      (L : J → ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (g : ∀ j, L j ⟶ K),
      (∀ j, IsLinearlyAdequate (𝟭 _) (L j)) ∧
        ∀ {Z : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A} (a b : K ⟶ Z),
          (∀ j, g j ≫ a = g j ≫ b) → a = b := by
  obtain ⟨J, L, hL, cover, hcover⟩ := exists_coproduct_linearlyAdequate_surjective (A := A) K hK
  let e := presheafOfModulesUliftIso.{max u v, max (u + 1) (v + 1) w}
    (algebraRingDiagram.{v} A) K
  have : Epi cover := PresheafOfModules.epi_of_surjective hcover
  refine ⟨J, L, fun j => Sigma.ι L j ≫ cover ≫ e.hom, hL, fun a b hab => ?_⟩
  rw [← cancel_epi (cover ≫ e.hom)]
  refine Sigma.hom_ext _ _ fun j => ?_
  simpa using hab j

/-- The degree-one extension group from a linearly adequate functor into an adequate functor
vanishes. A class of it is the class of an extension `0 → F → E → L → 0`, and such an extension
admits a retraction onto `F` by Tag 06V7, so its class is zero. -/
public theorem subsingleton_zExt_one_of_isLinearlyAdequate
    (L F : ModuleValuedFunctor.{max u v w, v} A) (hL : IsLinearlyAdequate (𝟭 _) L)
    (hF : IsAdequate (𝟭 _) F) :
    Subsingleton (Abelian.zExt L F 1) := by
  let _ : HasExt.{max (u + 1) (v + 1) (w + 1)} (ModuleValuedFunctor.{max u v w, v} A) :=
    HasExt.standard (ModuleValuedFunctor.{max u v w, v} A)
  have hE : Subsingleton (Abelian.Ext.{max (u + 1) (v + 1) (w + 1)} L F 1) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨E, i, p, hw, hS, rfl⟩ :=
      (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ L F).1 x
    obtain ⟨r, hr⟩ := exists_retraction_of_shortExact_large i p hw hS hF hL
    calc hS.extClass = hS.extClass.comp (Abelian.Ext.mk₀ (𝟙 F)) (add_zero 1) := by simp
      _ = hS.extClass.comp (Abelian.Ext.mk₀ (i ≫ r)) (add_zero 1) := by rw [hr]
      _ = 0 := by
        rw [← Abelian.Ext.mk₀_comp_mk₀]
        exact hS.extClass_comp_assoc _
  exact ⟨fun a b => (Abelian.Ext.homAddEquiv (X := L) (Y := F) (n := 1)).symm.injective
    (Subsingleton.elim _ _)⟩

/-- If no linearly adequate functor has a nonzero extension of degree `n > 0` into `F`, then the
`n`-th right derived functor of the coreflection vanishes on `F`. -/
private lemma isZero_rightDerivedPlus_adequateCoreflection_of_subsingleton_zExt
    (F : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (n : ℕ) (hn : 0 < n)
    (h : ∀ L : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A, IsLinearlyAdequate (𝟭 _) L →
      Subsingleton (Abelian.zExt L F (n : ℤ))) :
    IsZero (((adequateCoreflection.{u, v, w} A).rightDerivedPlus (n : ℤ)).obj F) := by
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ (m := (n : ℤ)) (n := n) rfl]
  refine IsZero.of_iso ?_ ((InjectiveResolution.of F).isoRightDerivedObj _ n)
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  refine exactAt_mapHomologicalComplex_of_cover.{max (u + 1) (v + 1) w}
    (adequate.{u, v, max (u + 1) (v + 1) w} A)
    (adequateCoreflectionAdjunction.{u, v, w} A) _ n hn ?_
  intro K hK
  obtain ⟨J, L, g, hL, hje⟩ := exists_jointlyEpi_isLinearlyAdequate.{u, v, w} A K hK
  exact ⟨J, L, g, fun j => (hL j).isAdequate, fun j => h (L j) (hL j), hje⟩

/-- **Stacks Project, Tag 06ZI in degree one.** The first right derived functor of the
coreflection `Q` onto the adequate module-valued functors vanishes on every adequate functor `F`.
On an injective resolution `F → I ⁎`, a degree-one cycle of `Q(I ⁎)` restricted along a linearly
adequate functor `L` is a boundary, because `Ext¹(L, F)` vanishes by Tag 06V7; the linearly
adequate functors cover every adequate functor by Tag 06UX. -/
@[stacks 06ZI "degree 1, from Tag 06V7 and the covering of Tag 06UX"]
public theorem isZero_rightDerivedPlus_one_adequateCoreflection
    (F : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (hF : IsAdequate (𝟭 _) F) :
    IsZero (((adequateCoreflection.{u, v, w} A).rightDerivedPlus 1).obj F) := by
  exact isZero_rightDerivedPlus_adequateCoreflection_of_subsingleton_zExt.{u, v, w} A F 1
    one_pos fun L hL => subsingleton_zExt_one_of_isLinearlyAdequate.{u, v, max (u + 1) (v + 1) w}
      A L F hL hF

/-- The extension of scalars of an `A`-module is right acyclic for the coreflection onto the
adequate functors, relative to the vanishing of the positive extension groups between extensions
of modules one of which is finitely presented. -/
public theorem rightAcyclic_moduleExtension
    (hFP : ∀ M P : ModuleCat.{max (u + 1) (v + 1) w} A, Module.FinitePresentation A P →
      ∀ j : ℤ, 0 < j → Subsingleton (Abelian.zExt
        (moduleExtension.{max (u + 1) (v + 1) w, v} A P)
        (moduleExtension.{max (u + 1) (v + 1) w, v} A M) j))
    (M : ModuleCat.{max (u + 1) (v + 1) w} A) :
    (adequateCoreflection.{u, v, w} A).rightAcyclic
      (moduleExtension.{max (u + 1) (v + 1) w, v} A M) := by
  have hlim : PreservesFiniteLimits (adequateCoreflection.{u, v, w} A) :=
    preservesFiniteLimits_adequateCoreflection.{u, v, w} A
  refine (((adequateCoreflection.{u, v, w} A).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (moduleExtension.{max (u + 1) (v + 1) w, v} A M)).2 inferInstance).2 ?_
  intro p hp
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp.le
  have hn : 0 < n := by omega
  exact isZero_rightDerivedPlus_adequateCoreflection_of_subsingleton_zExt.{u, v, w} A _ n hn
    fun L hL => subsingleton_zExt_of_isLinearlyAdequate.{u, v, max (u + 1) (v + 1) w} L hL M
      (fun P hP k hk => hFP M P hP k hk) (n : ℤ) (by exact_mod_cast hn)

/-- An adequate module-valued functor is right acyclic for the coreflection onto the adequate
functors: it is the kernel of a morphism of extensions of modules, and right acyclicity passes
from the two extensions and the extension of the cokernel to that kernel. -/
public theorem rightAcyclic_adequateCoreflection_of_isAdequate
    (hFP : ∀ M P : ModuleCat.{max (u + 1) (v + 1) w} A, Module.FinitePresentation A P →
      ∀ j : ℤ, 0 < j → Subsingleton (Abelian.zExt
        (moduleExtension.{max (u + 1) (v + 1) w, v} A P)
        (moduleExtension.{max (u + 1) (v + 1) w, v} A M) j))
    (F : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (hF : IsAdequate (𝟭 _) F) :
    (adequateCoreflection.{u, v, w} A).rightAcyclic F := by
  have hlim : PreservesFiniteLimits (adequateCoreflection.{u, v, w} A) :=
    preservesFiniteLimits_adequateCoreflection.{u, v, w} A
  have hcolim : PreservesFiniteColimits (moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A) :=
    moduleExtensionFunctor_preservesFiniteColimits.{max (u + 1) (v + 1) w, v} A
  obtain ⟨M, N, f, hf⟩ := hF
  obtain ⟨e⟩ := (isKernelPresentation_iff.{max (u + 1) (v + 1) w, v} F f).1 hf
  refine ObjectProperty.prop_of_iso _ e.symm
    (rightAcyclic_kernel_of_coreflection (adequate.{u, v, max (u + 1) (v + 1) w} A) _
      (adequateCoreflectionAdjunction.{u, v, w} A)
      ((moduleExtensionFunctor.{max (u + 1) (v + 1) w, v} A).map f)
      (isAdequate_moduleExtension.{u, v, max (u + 1) (v + 1) w} M)
      (isAdequate_moduleExtension.{u, v, max (u + 1) (v + 1) w} N)
      (rightAcyclic_moduleExtension.{u, v, w} A hFP M)
      (rightAcyclic_moduleExtension.{u, v, w} A hFP N) ?_)
  exact ObjectProperty.prop_of_iso _ (moduleExtensionCokernelIso.{max (u + 1) (v + 1) w, v} f)
    (rightAcyclic_moduleExtension.{u, v, w} A hFP (cokernel f))

/-- **Stacks Project, Tag 06ZI.** The higher right derived functors of the coreflection `Q` onto
the adequate module-valued functors vanish in positive degrees on every adequate functor. -/
@[stacks 06ZI "the positive-degree vanishing of the extension groups between extensions of \
modules, one finitely presented, is a hypothesis: that is Tag 06ZG, which is absent from this \
library."]
public theorem isZero_rightDerivedPlus_adequateCoreflection
    (hFP : ∀ M P : ModuleCat.{max (u + 1) (v + 1) w} A, Module.FinitePresentation A P →
      ∀ j : ℤ, 0 < j → Subsingleton (Abelian.zExt
        (moduleExtension.{max (u + 1) (v + 1) w, v} A P)
        (moduleExtension.{max (u + 1) (v + 1) w, v} A M) j))
    (F : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (hF : IsAdequate (𝟭 _) F)
    (p : ℤ) (hp : 0 < p) :
    IsZero (((adequateCoreflection.{u, v, w} A).rightDerivedPlus p).obj F) := by
  have hlim : PreservesFiniteLimits (adequateCoreflection.{u, v, w} A) :=
    preservesFiniteLimits_adequateCoreflection.{u, v, w} A
  exact (((adequateCoreflection.{u, v, w} A).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    F).2 inferInstance).1
    (rightAcyclic_adequateCoreflection_of_isAdequate.{u, v, w} A hFP F hF) p hp

end AdequateFunctor

end
