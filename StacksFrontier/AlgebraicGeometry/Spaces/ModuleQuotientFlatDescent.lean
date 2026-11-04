module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback

/-!
# Quotients of a module which agree after a flat surjective pullback

Let `Z` be an algebraic space over `S`, `M` an `𝒪_Z`-module and `χ₁ : M ⟶ F₁`, `χ₂ : M ⟶ F₂`
two morphisms of `𝒪_Z`-modules, `χ₁` an epimorphism.  If, after the inverse image along every
member of a jointly surjective family of flat morphisms `φ_i : Z'_i ⟶ Z`, the morphism `φ_i^*χ₂`
factors through `φ_i^*χ₁`, then `χ₂` factors through `χ₁`.  Indeed `ker(χ₁) ⟶ M ⟶ F₂` vanishes,
since it vanishes after every `φ_i^*` and vanishing descends along a jointly surjective family of
flat morphisms (`AlgebraicGeometry.Space.eq_zero_of_forall_modulePullback_map_eq_zero_of_isFlat`),
and `χ₁` is the cokernel of its kernel, the category of `𝒪_Z`-modules being abelian.

In particular two quotients `χ₁`, `χ₂` of `M` which become isomorphic as quotients of `φ_i^*M`
for every `i` are isomorphic as quotients of `M`.

## Main results

* `AlgebraicGeometry.Space.kernel_ι_comp_eq_zero_of_forall_modulePullback_of_isFlat`: the
  vanishing of `ker(χ₁) ⟶ F₂`.
* `AlgebraicGeometry.Space.exists_comp_eq_of_forall_modulePullback_of_isFlat`: `χ₂` factors
  through `χ₁`.
* `AlgebraicGeometry.Space.quotientIsoOfModulePullbackIsFlat`: **two quotients which are
  isomorphic after a jointly surjective family of flat pullbacks are isomorphic**, compatibly
  with the two quotient maps
  (`AlgebraicGeometry.Space.comp_quotientIsoOfModulePullbackIsFlat_hom`).
* `AlgebraicGeometry.Space.quotientIsoOfModulePullbackIsFlatOfSurjective`: the same for one flat
  surjective morphism.

## Implementation notes

The abelian structure of the category of `𝒪_Z`-modules is the local instance
`AlgebraicGeometry.Space.smallEtaleModulesAbelian`, as in
`StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback`, so that the zero morphism of
the vanishing statement is the one of that file.  The statements of the factorization and of the
isomorphism mention neither kernels nor zero morphisms, so they are independent of that choice.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] smallEtaleModulesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : AlgebraicSpaces B S hS} {I : Type*} {Z' : I → AlgebraicSpaces B S hS}
    {M F₁ F₂ : Modules.{u, u} B S hS Z.1 Z.2}

/-- The inverse image of the composite `ker(χ₁) ⟶ M ⟶ F₂` through a factorization of the inverse
image of `χ₂` through that of `χ₁`. -/
private theorem modulePullback_map_kernel_ι_comp {Y : AlgebraicSpaces B S hS} (φ : Y ⟶ Z)
    (χ₁ : M ⟶ F₁) (χ₂ : M ⟶ F₂)
    (β : (modulePullback B S hS φ).obj F₁ ⟶ (modulePullback B S hS φ).obj F₂)
    (hβ : (modulePullback B S hS φ).map χ₁ ≫ β = (modulePullback B S hS φ).map χ₂) :
    (modulePullback B S hS φ).map (kernel.ι χ₁ ≫ χ₂) =
      (modulePullback B S hS φ).map (kernel.ι χ₁ ≫ χ₁) ≫ β := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, hβ]

/-- The inverse image of `ker(χ₁) ⟶ M ⟶ F₁` vanishes. -/
private theorem modulePullback_map_kernel_ι_comp_self {Y : AlgebraicSpaces B S hS} (φ : Y ⟶ Z)
    (χ₁ : M ⟶ F₁) : (modulePullback B S hS φ).map (kernel.ι χ₁ ≫ χ₁) = 0 := by
  have := (modulePullbackAdjunction B S hS φ).isLeftAdjoint
  have hz : (modulePullback B S hS φ).PreservesZeroMorphisms := inferInstance
  rw [kernel.condition]
  exact Functor.map_zero _ _ _

/-- **The kernel of one quotient maps to zero in a second one which factors through the first
after a jointly surjective family of flat pullbacks.** -/
theorem kernel_ι_comp_eq_zero_of_forall_modulePullback_of_isFlat (φ : ∀ i, Z' i ⟶ Z)
    (hφ : ∀ i, IsFlat B S hS (φ i).hom)
    (hsurj : IsJointlySurjective B S hS (fun i => (Z' i).1) fun i => (φ i).hom)
    (χ₁ : M ⟶ F₁) (χ₂ : M ⟶ F₂)
    (h : ∀ i, ∃ β : (modulePullback B S hS (φ i)).obj F₁ ⟶ (modulePullback B S hS (φ i)).obj F₂,
      (modulePullback B S hS (φ i)).map χ₁ ≫ β = (modulePullback B S hS (φ i)).map χ₂) :
    kernel.ι χ₁ ≫ χ₂ = 0 := by
  refine eq_zero_of_forall_modulePullback_map_eq_zero_of_isFlat B S hS φ hφ hsurj _ fun i => ?_
  obtain ⟨β, hβ⟩ := h i
  rw [modulePullback_map_kernel_ι_comp B S hS (φ i) χ₁ χ₂ β hβ,
    modulePullback_map_kernel_ι_comp_self, zero_comp]

/-- **A morphism which factors through a quotient after a jointly surjective family of flat
pullbacks factors through it.** -/
theorem exists_comp_eq_of_forall_modulePullback_of_isFlat (φ : ∀ i, Z' i ⟶ Z)
    (hφ : ∀ i, IsFlat B S hS (φ i).hom)
    (hsurj : IsJointlySurjective B S hS (fun i => (Z' i).1) fun i => (φ i).hom)
    (χ₁ : M ⟶ F₁) [Epi χ₁] (χ₂ : M ⟶ F₂)
    (h : ∀ i, ∃ β : (modulePullback B S hS (φ i)).obj F₁ ⟶ (modulePullback B S hS (φ i)).obj F₂,
      (modulePullback B S hS (φ i)).map χ₁ ≫ β = (modulePullback B S hS (φ i)).map χ₂) :
    ∃ v : F₁ ⟶ F₂, χ₁ ≫ v = χ₂ :=
  ⟨Abelian.epiDesc χ₁ χ₂
      (kernel_ι_comp_eq_zero_of_forall_modulePullback_of_isFlat B S hS φ hφ hsurj χ₁ χ₂ h),
    Abelian.comp_epiDesc _ _ _⟩

variable (φ : ∀ i, Z' i ⟶ Z) (hφ : ∀ i, IsFlat B S hS (φ i).hom)
    (hsurj : IsJointlySurjective B S hS (fun i => (Z' i).1) fun i => (φ i).hom)
    (χ₁ : M ⟶ F₁) [Epi χ₁] (χ₂ : M ⟶ F₂) [Epi χ₂]
    (h : ∀ i, ∃ β : (modulePullback B S hS (φ i)).obj F₁ ≅ (modulePullback B S hS (φ i)).obj F₂,
      (modulePullback B S hS (φ i)).map χ₁ ≫ β.hom = (modulePullback B S hS (φ i)).map χ₂)

omit [Epi χ₁] [Epi χ₂] in
include h in
/-- The first quotient factors through the second after each pullback. -/
theorem forall_exists_modulePullback_comp_eq_of_iso :
    ∀ i, ∃ β : (modulePullback B S hS (φ i)).obj F₁ ⟶ (modulePullback B S hS (φ i)).obj F₂,
      (modulePullback B S hS (φ i)).map χ₁ ≫ β = (modulePullback B S hS (φ i)).map χ₂ :=
  fun i => by
    obtain ⟨β, hβ⟩ := h i
    exact ⟨β.hom, hβ⟩

omit [Epi χ₁] [Epi χ₂] in
include h in
/-- The second quotient factors through the first after each pullback. -/
theorem forall_exists_modulePullback_comp_eq_of_iso_symm :
    ∀ i, ∃ β : (modulePullback B S hS (φ i)).obj F₂ ⟶ (modulePullback B S hS (φ i)).obj F₁,
      (modulePullback B S hS (φ i)).map χ₂ ≫ β = (modulePullback B S hS (φ i)).map χ₁ :=
  fun i => by
    obtain ⟨β, hβ⟩ := h i
    exact ⟨β.inv, by rw [← hβ, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

/-- **Two quotients of a module which are isomorphic as quotients after a jointly surjective
family of flat pullbacks are isomorphic as quotients.** -/
def quotientIsoOfModulePullbackIsFlat : F₁ ≅ F₂ where
  hom := (exists_comp_eq_of_forall_modulePullback_of_isFlat B S hS φ hφ hsurj χ₁ χ₂
    (forall_exists_modulePullback_comp_eq_of_iso B S hS φ χ₁ χ₂ h)).choose
  inv := (exists_comp_eq_of_forall_modulePullback_of_isFlat B S hS φ hφ hsurj χ₂ χ₁
    (forall_exists_modulePullback_comp_eq_of_iso_symm B S hS φ χ₁ χ₂ h)).choose
  hom_inv_id := by
    rw [← cancel_epi χ₁, ← Category.assoc,
      (exists_comp_eq_of_forall_modulePullback_of_isFlat B S hS φ hφ hsurj χ₁ χ₂
        (forall_exists_modulePullback_comp_eq_of_iso B S hS φ χ₁ χ₂ h)).choose_spec,
      (exists_comp_eq_of_forall_modulePullback_of_isFlat B S hS φ hφ hsurj χ₂ χ₁
        (forall_exists_modulePullback_comp_eq_of_iso_symm B S hS φ χ₁ χ₂ h)).choose_spec,
      Category.comp_id]
  inv_hom_id := by
    rw [← cancel_epi χ₂, ← Category.assoc,
      (exists_comp_eq_of_forall_modulePullback_of_isFlat B S hS φ hφ hsurj χ₂ χ₁
        (forall_exists_modulePullback_comp_eq_of_iso_symm B S hS φ χ₁ χ₂ h)).choose_spec,
      (exists_comp_eq_of_forall_modulePullback_of_isFlat B S hS φ hφ hsurj χ₁ χ₂
        (forall_exists_modulePullback_comp_eq_of_iso B S hS φ χ₁ χ₂ h)).choose_spec,
      Category.comp_id]

/-- The isomorphism of the two quotients carries the first quotient map to the second. -/
@[reassoc]
theorem comp_quotientIsoOfModulePullbackIsFlat_hom :
    χ₁ ≫ (quotientIsoOfModulePullbackIsFlat B S hS φ hφ hsurj χ₁ χ₂ h).hom = χ₂ :=
  (exists_comp_eq_of_forall_modulePullback_of_isFlat B S hS φ hφ hsurj χ₁ χ₂
    (forall_exists_modulePullback_comp_eq_of_iso B S hS φ χ₁ χ₂ h)).choose_spec

section Single

variable {Z' : AlgebraicSpaces B S hS} (φ : Z' ⟶ Z) (hφ : IsFlat B S hS φ.hom)
    (hsurj : IsSurjective B S hS φ.hom) (χ₁ : M ⟶ F₁) (hχ₁ : Epi χ₁) (χ₂ : M ⟶ F₂)
    (hχ₂ : Epi χ₂)
    (h : ∃ β : (modulePullback B S hS φ).obj F₁ ≅ (modulePullback B S hS φ).obj F₂,
      (modulePullback B S hS φ).map χ₁ ≫ β.hom = (modulePullback B S hS φ).map χ₂)

/-- **Two quotients of a module which are isomorphic as quotients after a flat surjective
pullback are isomorphic as quotients**: `AlgebraicGeometry.Space.quotientIsoOfModulePullbackIsFlat`
for the one-member family `φ`. -/
def quotientIsoOfModulePullbackIsFlatOfSurjective : F₁ ≅ F₂ :=
  @quotientIsoOfModulePullbackIsFlat B S hS Z Unit (fun _ => Z') M F₁ F₂ (fun _ => φ) (fun _ => hφ)
    ((isJointlySurjective_const_iff B S hS φ.hom).2 hsurj) χ₁ hχ₁ χ₂ hχ₂ (fun _ => h)

/-- The isomorphism of the two quotients carries the first quotient map to the second. -/
@[reassoc]
theorem comp_quotientIsoOfModulePullbackIsFlatOfSurjective_hom :
    χ₁ ≫ (quotientIsoOfModulePullbackIsFlatOfSurjective B S hS φ hφ hsurj χ₁ hχ₁ χ₂ hχ₂ h).hom =
      χ₂ :=
  @comp_quotientIsoOfModulePullbackIsFlat_hom B S hS Z Unit (fun _ => Z') M F₁ F₂ (fun _ => φ)
    (fun _ => hφ) ((isJointlySurjective_const_iff B S hS φ.hom).2 hsurj) χ₁ hχ₁ χ₂ hχ₂
    (fun _ => h)

end Single

end AlgebraicGeometry.Space

end
