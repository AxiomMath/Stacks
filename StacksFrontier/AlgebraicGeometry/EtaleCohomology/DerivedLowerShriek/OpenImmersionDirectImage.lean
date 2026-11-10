module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenImmersionBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
import StacksCore.Tactic.StacksAttribute

/-!
# The open immersion case of [Stacks, Tag 0F7B] at every coefficient universe

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] Stacks.EtaleCohomology.etaleModules_enoughInjectives

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type w) [Ring Λ]

/-! ### Vanishing of a derived direct image over a closed part -/

section Vanishing

/-- The zero objects of an abelian category form a weak Serre class. -/
theorem isWeakSerreClass_isZero (C : Type*) [Category* C] [Abelian C] :
    ObjectProperty.IsWeakSerreClass (fun X : C => IsZero X) := by
  let P : ObjectProperty C := fun X => IsZero X
  obtain ⟨Z, hZ⟩ := Limits.HasZeroObject.zero (C := C)
  have : P.ContainsZero := ⟨⟨Z, hZ, hZ⟩⟩
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h => h.of_iso e.symm⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, hf⟩
    have := mono_of_isLimit_fork hk
    exact IsZero.of_mono (Fork.ι k) hf.1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hf⟩
    have := epi_of_isColimit_cofork hk
    exact IsZero.of_epi (Cofork.π k) hf.2⟩
  have : P.IsClosedUnderExtensions :=
    ⟨fun hS h₁ h₃ => hS.exact.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)⟩
  exact ⟨⟩

variable {A B W : Scheme.{u}} (g : A ⟶ B) (c : W ⟶ B)

/-- **A derived direct image vanishes over `c` as soon as the higher direct images of its
cohomology sheaves do.** Let `L ∈ D⁺(A_étale, Λ)` be such that `c^{-1} R^p g_* H^q(L) = 0` for
all `p` and `q`. Then `c^{-1} Rg_* L = 0`: the objects of `B_étale` killed by the exact functor
`c^{-1}` form a weak Serre class, and the cohomology sheaves of `Rg_* L` lie in it by the
spectral sequence of a Cartan-Eilenberg resolution
(`CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj`). -/
theorem isZero_etaleModuleDerivedInverseImagePlus_derivedDirectImage_of_rightDerived
    (L : DerivedCategory.Plus (EtaleModules.{u, w} Λ A))
    (hL : ∀ (q : ℤ) (p : ℕ), IsZero ((etaleModuleInverseImage.{u, w} Λ c).obj
      (((etaleModuleDirectImage.{u, w} Λ g).rightDerived p).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj L)))) :
    IsZero ((etaleModuleDerivedInverseImagePlus.{u, w} Λ c).obj
      ((etaleModuleDerivedDirectImage.{u, w} Λ g).obj L)) := by
  have := isWeakSerreClass_isZero (EtaleModules.{u, w} Λ W)
  let Z : ObjectProperty (EtaleModules.{u, w} Λ W) := fun X => IsZero X
  let Q : ObjectProperty (EtaleModules.{u, w} Λ B) :=
    Z.inverseImage (etaleModuleInverseImage.{u, w} Λ c)
  have : Q.IsWeakSerreClass :=
    ObjectProperty.isWeakSerreClass_inverseImage Z (etaleModuleInverseImage.{u, w} Λ c)
  let P : ObjectProperty (EtaleModules.{u, w} Λ A) := fun M =>
    ∀ p : ℕ, Q (((etaleModuleDirectImage.{u, w} Λ g).rightDerived p).obj M)
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h p =>
    (h p).of_iso ((etaleModuleInverseImage.{u, w} Λ c).mapIso
      (((etaleModuleDirectImage.{u, w} Λ g).rightDerived p).mapIso e)).symm⟩
  have h := ((etaleModuleDirectImage.{u, w} Λ g).derivedCategoryBPlus_rightDerivedFunctorPlus_obj
    P Q (fun M hM p => hM p) L (fun q p => hL q p)).2
  exact isZero_of_forall_isZero_homology_plus _ fun q =>
    (h q).of_iso (((etaleModuleInverseImage.{u, w} Λ c).mapDerivedCategoryHomologyIso q).app
      (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, w} Λ g).obj L)))

end Vanishing

/-! ### Cohomology sheaves and restriction, at every coefficient universe -/

section Homology

/-- The cohomology sheaves of the inverse image of an object of `D⁺` are the inverse images of
its cohomology sheaves, inverse image being exact. -/
def etaleModuleDerivedInverseImagePlusHomologyIsoUniv {V X : Scheme.{u}} (e : V ⟶ X)
    (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ X)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleDerivedInverseImagePlus.{u, w} Λ e).obj K) ≅
      (etaleModuleInverseImage.{u, w} Λ e).obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K) :=
  (Stacks.Homology.derivedHomologyIso (etaleModuleInverseImage.{u, w} Λ e) q).app
    (DerivedCategory.Plus.ι.obj K)

/-- The cohomology sheaves of the derived extension by zero of an object of `D⁺` are the
extensions by zero of its cohomology sheaves, extension by zero being exact. -/
def etaleModuleDerivedExtensionByZeroHomologyIsoUniv {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ U)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleDerivedExtensionByZero.{u, w} Λ j).obj K) ≅
      (etaleModuleExtensionByZero.{u, w} Λ j).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K) :=
  (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (etaleModuleExtensionByZero.{u, w} Λ j)).app K) ≪≫
    (Stacks.Homology.derivedHomologyIso (etaleModuleExtensionByZero.{u, w} Λ j) q).app
      (DerivedCategory.Plus.ι.obj K)

/-- If the inverse image along `e` of a morphism of `D⁺` is invertible, so is the inverse image of
each of its cohomology sheaves. -/
theorem isIso_etaleModuleInverseImage_map_homology_of_isIso_univ {V X : Scheme.{u}} (e : V ⟶ X)
    {K L : DerivedCategory.Plus (EtaleModules.{u, w} Λ X)} (γ : K ⟶ L) (q : ℤ)
    (h : IsIso ((etaleModuleDerivedInverseImagePlus.{u, w} Λ e).map γ)) :
    IsIso ((etaleModuleInverseImage.{u, w} Λ e).map
      ((DerivedCategory.Plus.homologyFunctor _ q).map γ)) := by
  have h1 : IsIso (((etaleModuleInverseImage.{u, w} Λ e).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor _ q).map (DerivedCategory.Plus.ι.map γ)) := by
    change IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((etaleModuleDerivedInverseImagePlus.{u, w} Λ e).map γ))
    infer_instance
  exact (NatIso.isIso_map_iff
    (Stacks.Homology.derivedHomologyIso (etaleModuleInverseImage.{u, w} Λ e) q) _).mp h1

/-- **Restrictions to an open and to its closed complement jointly reflect isomorphisms of
`D⁺(X_étale, Λ)`.** -/
theorem isIso_of_isIso_etaleModuleDerivedInverseImagePlus_univ {Z U X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    {K L : DerivedCategory.Plus (EtaleModules.{u, w} Λ X)} (γ : K ⟶ L)
    (hi : IsIso ((etaleModuleDerivedInverseImagePlus.{u, w} Λ i).map γ))
    (hj : IsIso ((etaleModuleDerivedInverseImagePlus.{u, w} Λ j).map γ)) : IsIso γ := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro q
  have := isIso_etaleModuleInverseImage_map_homology_of_isIso_univ Λ i γ q hi
  have := isIso_etaleModuleInverseImage_map_homology_of_isIso_univ Λ j γ q hj
  exact isIso_of_isIso_etaleModuleInverseImage Λ i j hij _

/-- The inverse image along `c` of a derived extension by zero along `j` vanishes when the images
of `c` and `j` are disjoint. -/
theorem isZero_etaleModuleDerivedInverseImagePlus_extensionByZero_of_disjoint_univ
    {V U X : Scheme.{u}}
    (c : V ⟶ X) (j : U ⟶ X) [Etale j] (hcj : Disjoint (Set.range c.base) (Set.range j.base))
    (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ U)) :
    IsZero ((etaleModuleDerivedInverseImagePlus.{u, w} Λ c).obj
      ((etaleModuleDerivedExtensionByZero.{u, w} Λ j).obj K)) := by
  refine isZero_of_forall_isZero_homology_plus _ fun q => ?_
  refine IsZero.of_iso ?_ (etaleModuleDerivedInverseImagePlusHomologyIsoUniv Λ c _ q ≪≫
    (etaleModuleInverseImage.{u, w} Λ c).mapIso
      (etaleModuleDerivedExtensionByZeroHomologyIsoUniv Λ j K q))
  exact isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ c j hcj _

end Homology

section Restriction

variable {U X : Scheme.{u}} (j : U ⟶ X)

/-- On `D⁺`, derived restriction along an étale morphism is the inverse image. -/
def etaleModuleDerivedRestrictionIsoInverseImagePlusUniv [Etale j] :
    etaleModuleDerivedRestriction.{u, w} Λ j ≅ etaleModuleDerivedInverseImagePlus.{u, w} Λ j :=
  Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus (etaleModuleRestriction.{u, w} Λ j) ≪≫
    (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ Functor.mapDerivedCategoryPlusIdIso.symm ≪≫
    Functor.mapDerivedCategoryPlusCompIsoh
      (Functor.rightUnitor _ ≪≫ (etaleModuleInverseImageRestrictionIso.{u, w} Λ j).symm)

/-- `j^{-1} ∘ Rj_! ≅ 𝟭` on `D⁺(U_étale, Λ)` for an open immersion `j`. -/
def etaleModuleDerivedExtensionByZeroCompRestrictionIsoUniv [IsOpenImmersion j] :
    etaleModuleDerivedExtensionByZero.{u, w} Λ j ⋙ etaleModuleDerivedRestriction.{u, w} Λ j ≅
      𝟭 _ :=
  Functor.rightDerivedFunctorPlusCompIsoOfExact (etaleModuleExtensionByZero.{u, w} Λ j)
      (etaleModuleRestriction.{u, w} Λ j) _ (Iso.refl _) ≪≫
    Functor.rightDerivedFunctorPlusIdIsoOf _
      (asIso (etaleModuleExtensionByZeroAdj.{u, w} Λ j).unit).symm

/-- The unit of `Rj_! ⊣ j^{-1}` on `D⁺` is invertible for an open immersion `j`. -/
theorem isIso_etaleModuleDerivedExtensionByZeroAdj_unit_univ [IsOpenImmersion j] :
    IsIso (etaleModuleDerivedExtensionByZeroAdj.{u, w} Λ j).unit :=
  (etaleModuleDerivedExtensionByZeroAdj.{u, w} Λ j).isIso_unit_of_iso
    (etaleModuleDerivedExtensionByZeroCompRestrictionIsoUniv Λ j)

/-- `j^{-1} ∘ Rj_! ≅ 𝟭` on `D⁺(U_étale, Λ)`, with `j^{-1}` the inverse image. -/
def etaleModuleDerivedExtensionByZeroCompInverseImagePlusIsoUniv [IsOpenImmersion j] :
    etaleModuleDerivedExtensionByZero.{u, w} Λ j ⋙ etaleModuleDerivedInverseImagePlus.{u, w} Λ j ≅
      𝟭 _ :=
  Functor.isoWhiskerLeft _ (etaleModuleDerivedRestrictionIsoInverseImagePlusUniv Λ j).symm ≪≫
    etaleModuleDerivedExtensionByZeroCompRestrictionIsoUniv Λ j

end Restriction

/-! ### The open immersion case of [Stacks, Tag 0F7B], at every coefficient universe -/

section OpenBaseChange

variable {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
  (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i)

/-- `Rf'_* ≅ i^{-1} Rf̄_* Rb_!` on the whole of `D⁺(P_étale, Λ)`: `Rb_!` followed by `b^{-1}` is
the identity, and `i^{-1} Rf̄_* ≅ Rf'_* b^{-1}` is base change along the open immersion `i`
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion`). -/
def etaleModuleDerivedDirectImageIsoRestriction :
    etaleModuleDerivedDirectImage.{u, w} Λ f' ≅
      etaleModuleDerivedExtensionByZero.{u, w} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, w} Λ fb ⋙ etaleModuleDerivedRestriction.{u, w} Λ i := by
  let BC := etaleModuleDerivedBaseChange.{u, w} Λ fb f' i b sq.w.symm
  haveI : ∀ K, IsIso (BC.app K) := fun K =>
    isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion Λ fb sq K
  haveI : IsIso BC := NatIso.isIso_of_isIso_app _
  exact (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIsoUniv Λ b).symm
      (etaleModuleDerivedDirectImage.{u, w} Λ f') ≪≫
    Functor.isoWhiskerLeft (etaleModuleDerivedExtensionByZero.{u, w} Λ b) (asIso BC).symm ≪≫
    Functor.isoWhiskerLeft (etaleModuleDerivedExtensionByZero.{u, w} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, w} Λ fb)
      (etaleModuleDerivedRestrictionIsoInverseImagePlusUniv Λ i).symm

/-- The transformation `i_! Rf'_* ⟶ Rf̄_* Rb_!` on `D⁺(P_étale, Λ)`, adjoint under
`Ri_! ⊣ i^{-1}` to `etaleModuleDerivedDirectImageIsoRestriction`. -/
def etaleModuleDerivedExtensionByZeroDirectImageMap :
    etaleModuleDerivedDirectImage.{u, w} Λ f' ⋙ etaleModuleDerivedExtensionByZero.{u, w} Λ i ⟶
      etaleModuleDerivedExtensionByZero.{u, w} Λ b ⋙ etaleModuleDerivedDirectImage.{u, w} Λ fb :=
  Functor.whiskerRight (etaleModuleDerivedDirectImageIsoRestriction Λ fb i b f' sq).hom
      (etaleModuleDerivedExtensionByZero.{u, w} Λ i) ≫
    Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, w} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, w} Λ fb)
      (etaleModuleDerivedExtensionByZeroAdj.{u, w} Λ i).counit

omit [IsProper fb] in
/-- The map `i_! Rf'_* K ⟶ Rf̄_* Rb_! K` is invertible as soon as `Rf̄_* Rb_! K` vanishes on the
closed complement of `Y`. Over `Y` its restriction is, up to the invertible unit of
`Ri_! ⊣ i^{-1}`, the isomorphism it is adjoint to; over the complement the source vanishes since
`c^{-1} i_! = 0`. -/
theorem isIso_etaleModuleDerivedExtensionByZeroDirectImageMap_app
    (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ P))
    (hZ : IsZero ((etaleModuleDerivedInverseImagePlus.{u, w} Λ (openImmersionComplementι i)).obj
      ((etaleModuleDerivedDirectImage.{u, w} Λ fb).obj
        ((etaleModuleDerivedExtensionByZero.{u, w} Λ b).obj K)))) :
    IsIso ((etaleModuleDerivedExtensionByZeroDirectImageMap Λ fb i b f' sq).app K) := by
  let c := openImmersionComplementι i
  have hic : Set.range i.base = (Set.range c.base)ᶜ := by
    rw [range_openImmersionComplementι, compl_compl]
  have := isIso_etaleModuleDerivedExtensionByZeroAdj_unit_univ Λ i
  let φ := (etaleModuleDerivedExtensionByZeroDirectImageMap Λ fb i b f' sq).app K
  have hY : IsIso ((etaleModuleDerivedInverseImagePlus.{u, w} Λ i).map φ) := by
    rw [← NatIso.isIso_map_iff (etaleModuleDerivedRestrictionIsoInverseImagePlusUniv Λ i)]
    have hφ : φ = (etaleModuleDerivedExtensionByZero.{u, w} Λ i).map
        ((etaleModuleDerivedDirectImageIsoRestriction Λ fb i b f' sq).hom.app K) ≫
        (etaleModuleDerivedExtensionByZeroAdj.{u, w} Λ i).counit.app _ := rfl
    have htri := (etaleModuleDerivedExtensionByZeroAdj.{u, w} Λ i).right_triangle_components
      ((etaleModuleDerivedExtensionByZero.{u, w} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, w} Λ fb).obj K)
    have hε : IsIso ((etaleModuleDerivedRestriction.{u, w} Λ i).map
        ((etaleModuleDerivedExtensionByZeroAdj.{u, w} Λ i).counit.app
          ((etaleModuleDerivedExtensionByZero.{u, w} Λ b ⋙
            etaleModuleDerivedDirectImage.{u, w} Λ fb).obj K))) :=
      IsIso.of_isIso_fac_left htri
    rw [hφ, Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) hε
  have hC : IsIso ((etaleModuleDerivedInverseImagePlus.{u, w} Λ c).map φ) := by
    have h₁ : IsZero ((etaleModuleDerivedInverseImagePlus.{u, w} Λ c).obj
        ((etaleModuleDerivedExtensionByZero.{u, w} Λ i).obj
          ((etaleModuleDerivedDirectImage.{u, w} Λ f').obj K))) := by
      refine isZero_etaleModuleDerivedInverseImagePlus_extensionByZero_of_disjoint_univ Λ c i ?_ _
      rw [hic]
      exact disjoint_compl_right
    exact ⟨0, h₁.eq_of_src _ _, hZ.eq_of_src _ _⟩
  exact isIso_of_isIso_etaleModuleDerivedInverseImagePlus_univ Λ c i hic φ hC hY

omit [IsProper fb] [IsOpenImmersion b] in
include sq in
/-- Over the closed complement of `Y` the open immersion `b : P ⟶ T` is invisible: a morphism
`t` into `T` whose image lies over the complement of the image of `i` misses the image of `b`,
the square being cartesian. -/
theorem disjoint_range_of_range_subset_preimage_openImmersionComplementι {V : Scheme.{u}}
    (t : V ⟶ T)
    (ht : Set.range t.base ⊆ fb.base ⁻¹' Set.range (openImmersionComplementι i).base) :
    Disjoint (Set.range t.base) (Set.range b.base) := by
  rw [Set.disjoint_left]
  rintro _ hx ⟨y, rfl⟩
  have h₁ := ht hx
  rw [Set.mem_preimage, range_openImmersionComplementι] at h₁
  exact h₁ ⟨f'.base y, by rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]⟩

end OpenBaseChange

end Stacks.EtaleCohomology

end
