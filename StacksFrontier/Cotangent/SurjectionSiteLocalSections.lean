module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.IdealActionVanishing
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationStructureModule
public import StacksFrontier.Cotangent.SurjectionSiteLocalTor
public import StacksFrontier.Cotangent.SurjectionSiteNormalForm

/-!
# The sections of `𝒦ᵐ` as an `𝒪(U)`-module, and the objectwise form of the local claim

Let `A → B` be a ring map, let `C_{B/A}` be the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the polynomial site, and let `U` be an object of
the small model whose point is `0`, so that `𝒪(U) = A[S]` and `Ō(U) = B[S]` for `S` the set of
variables of `U`.  Write `𝔪 = (X_s ; s ∈ S) ⊆ A[S]` for the ideal of the variables.

`StacksFrontier.Cotangent.SurjectionSiteNormalForm` identifies the sections of `𝒦ᵐ`, the `m`-th
power of the augmentation ideal of `Ō`, with `B ⊗_A 𝔪ᵐ`, as a **`B`-linear** equivalence:
that is the orientation in which the `B`-action is the one of the left tensor factor, and
`𝔪ᵐ ⊗_A B` carries no `Module B` structure in Mathlib to be linear over.

`StacksFrontier.Cotangent.SurjectionSiteLocalTor` states the local claim of [Stacks, Tag 08RF] in
the other orientation: `StacksDraft.PolynomialLocalComplex.tensorVariableIdealPow` is the
`A[S]`-module `𝔪ᵐ ⊗_A T` with `A[S]` acting through the **left** factor, which is the
orientation `Tor'` over `A[S]` is taken in, and the one the sections of `𝒦ᵐ` really carry.

This file crosses that seam.  The bridge is `TensorProduct.comm`, and what makes it a short step
is that the normal form is pinned in coordinates by
`CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm_symm_tmul`: both orientations send the
generator to `b · p` inside `Ō(U) = B[S]`, so the `A[S]`-equivariance of the composite is
multiplicativity of `MvPolynomial.map`.  One level down `TensorProduct.comm` was **not** needed,
because `TensorProduct.AlgebraTensorModule` already puts the `A[S]`-action on the left factor;
the seam survives exactly here, where the normal form is `B`-linear in `B ⊗_A 𝔪ᵐ`.

With the seam crossed, the local claim is read at an object of the site, and the reduction of an
objectwise vanishing to the objects whose point is `0` — which for a surjective `A → B` is
`CommAlgCat.zeroPointSiteIso` together with `Stacks.SheafOfModules.app_eq_zero_of_iso` — is
recorded as a statement about an arbitrary morphism of functors on the site.

## Main definitions

* `MvPolynomial.variableIdealPowTensorComm`: the interchange `𝔪ᵐ ⊗_A T ≃ₗ[A] T ⊗_A 𝔪ᵐ`, the
  second factor read as `MvPolynomial.degreeGE`.
* `CommAlgCat.smallPolynomialAugmentationIdealPowLocalIso`: **the `A[S]`-linear normal form**
  `𝒦ᵐ(U) ≅ 𝔪ᵐ ⊗_A B` over an object `U` whose point is `0`, as an isomorphism of `𝒪(U)`-modules.

## Main results

* `CommAlgCat.smallPolynomialAugmentationIdealPowLocalIso_hom_comp` and
  `CommAlgCat.smallPolynomialAugmentationIdealPowLocalIso_inv_comp`: **the normal form is
  compatible with the inclusions `𝒦ᵐ ⊆ 𝒦ⁿ`** for `n ≤ m`, which correspond to
  `StacksDraft.PolynomialLocalComplex.tensorVariableIdealPowMap`.
* `CommAlgCat.tor'_map_app_smallPolynomialAugmentationIdealPowStructureOfLE_eq_zero`: **the
  local claim of [Stacks, Tag 08RF] at an object of the site.** For `j < k` and an
  `𝒪(U)`-module `M` killed by the ideal of the variables, the inclusion `𝒦^{n+k} ⊆ 𝒦ⁿ` induces
  the zero map on `Tor'_j^{𝒪(U)}(-, M)`.
* `CommAlgCat.app_eq_zero_of_forall_smallSitePoint_eq_zero`: **the reduction to the objects whose
  point is `0`.** For a surjective `A → B`, a morphism of functors on `C_{B/A}` which vanishes
  at every object whose point is `0` vanishes at every object.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08RE](https://stacks.math.columbia.edu/tag/08RE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace MvPolynomial

variable (A : Type u) [CommRing A] (σ : Type u) (T : Type u) [AddCommGroup T] [Module A T]

/-- **The interchange `𝔪ᵐ ⊗_A T ≃ₗ[A] T ⊗_A 𝔪ᵐ`**, with `𝔪 = (X_s ; s ∈ σ)` the ideal of the
variables of `A[σ]`, and with the right-hand second factor read as `MvPolynomial.degreeGE σ A m`
through `MvPolynomial.restrictScalars_span_range_X_pow`.

This is the orientation seam of the proof of [Stacks, Tag 08RF]: `𝔪ᵐ ⊗_A T` is the orientation
in which `A[σ]` acts through the left factor, hence the one the sections of `𝒦ᵐ` carry and the
one `Tor'` over `A[σ]` is taken in, while `B ⊗_A 𝔪ᵐ` is the orientation in which the normal form
of the sections is a `B`-linear equivalence. -/
def variableIdealPowTensorComm (m : ℕ) :
    (↥(Ideal.span (Set.range (X : σ → MvPolynomial σ A)) ^ m) ⊗[A] T) ≃ₗ[A]
      T ⊗[A] (degreeGE σ A m) :=
  (TensorProduct.comm A _ _).trans
    (TensorProduct.congr (LinearEquiv.refl A T)
      (LinearEquiv.ofEq _ _ (restrictScalars_span_range_X_pow σ A m)))

/-- `variableIdealPowTensorComm` sends `p ⊗ₜ t` to `t ⊗ₜ p`, with `p` read as an element of
`MvPolynomial.degreeGE σ A m`. -/
@[simp]
lemma variableIdealPowTensorComm_tmul (m : ℕ)
    (p : ↥(Ideal.span (Set.range (X : σ → MvPolynomial σ A)) ^ m)) (t : T) :
    variableIdealPowTensorComm A σ T m (p ⊗ₜ t) =
      t ⊗ₜ (LinearEquiv.ofEq _ _ (restrictScalars_span_range_X_pow σ A m) p) := rfl

end MvPolynomial

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

attribute [local instance] smallPolynomialQuotientModuleStructure
  smallPolynomialAugmentationIdealPowModuleStructure

/-- The module structure over `𝒪(X)` on the sections of a presheaf of `𝒪`-modules, with the
acting ring spelled as the polynomial algebra `A[S]` that `𝒪(X)` is.  This is nothing but
`ModuleCat.isModule`; the two acting rings are the same by definition, but instance search keys
on the spelling, and the local complexes of [Stacks, Tag 08RF] are indexed by `MvPolynomial`. -/
@[instance_reducible]
def moduleMvPolynomialOfStructureObj (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ)
    (Y : ModuleCat.{u} ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)) :
    Module (MvPolynomial ↥(X.unop.unop.1) A) (Y : Type u) :=
  Y.isModule

attribute [local instance] moduleMvPolynomialOfStructureObj

/-! ### The action of `𝒪(U)` on the sections of `𝒦ᵐ`, in coordinates -/

/-- **The ring map `𝒪(X) ⟶ Ō(X)` in coordinates**: read inside `Ō(X) = B[S]`, it is the base
change `MvPolynomial.map` of the coefficients along `A → B`. -/
lemma smallPolynomialQuotientAlgEquiv_smallSiteStructureToQuotient
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ)
    (p : ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)) :
    smallPolynomialQuotientAlgEquiv A B κ X (smallSiteStructureToQuotient A B κ X p) =
      MvPolynomial.map (algebraMap A (B : Type u))
        (show MvPolynomial ↥(X.unop.unop.1) A from p) := by
  rw [smallSiteStructureToQuotient_apply]
  change MvPolynomial.algebraTensorAlgEquiv A (B : Type u)
      ((1 : (B : Type u)) ⊗ₜ[A] (show MvPolynomial ↥(X.unop.unop.1) A from p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-- **The action of `𝒪(X)` on the sections of `𝒦ᵐ` is multiplication inside `Ō(X)`** by the
image of the acting element. -/
lemma smallPolynomialAugmentationIdealPowStructure_smul_coe (m : ℕ)
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ)
    (s : ((smallPolynomialStructurePresheaf A B κ).obj X : Type u))
    (x : ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ m X)) :
    ((s • x : ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ m X)) :
        ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) =
      smallSiteStructureToQuotient A B κ X s *
        (x : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) := rfl

/-- **The normal form across the interchange, in coordinates.** Read inside `Ō(U) = B[S]`, the
composite of `MvPolynomial.variableIdealPowTensorComm` with the inverse of the normal form
carries `p ⊗ b` to `b · p`.

This is `CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm_symm_tmul`: the interchange
sends `p ⊗ b` to `b ⊗ p`, which the normal form sends to `b · p`. -/
lemma coe_smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm (m : ℕ)
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) (h0 : smallSitePoint A B κ X = 0)
    (p : ↥(Ideal.span (Set.range (MvPolynomial.X :
        ↥(X.unop.unop.1) → MvPolynomial ↥(X.unop.unop.1) A)) ^ m)) (b : (B : Type u)) :
    smallPolynomialQuotientAlgEquiv A B κ X
        ((((smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm
            (MvPolynomial.variableIdealPowTensorComm A ↥(X.unop.unop.1) (B : Type u) m
              (p ⊗ₜ b))) :
          ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ m X)) :
          ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) =
      b • MvPolynomial.map (algebraMap A (B : Type u))
        (p : MvPolynomial ↥(X.unop.unop.1) A) := by
  rw [MvPolynomial.variableIdealPowTensorComm_tmul,
    smallPolynomialAugmentationIdealPowNormalForm_symm_tmul]
  rfl

/-- **The normal form across the interchange is `𝒪(U)`-equivariant.** Over an object `U` whose
point is `0`, the composite `𝔪ᵐ ⊗_A B ⟶ 𝒦ᵐ(U)` of
`MvPolynomial.variableIdealPowTensorComm` with the inverse of
`CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm` commutes with the action of
`𝒪(U) = A[S]`, which acts on `𝔪ᵐ ⊗_A B` through the left factor and on `𝒦ᵐ(U)` through
`A[S] → B[S]`.

Both are `b ⊗ p ↦ b · p` in coordinates
(`CommAlgCat.coe_smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm`), so the
identity to check is the multiplicativity of `MvPolynomial.map`. -/
lemma smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm_smul (m : ℕ)
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) (h0 : smallSitePoint A B κ X = 0)
    (s : ((smallPolynomialStructurePresheaf A B κ).obj X : Type u))
    (z : ↥(Ideal.span (Set.range (MvPolynomial.X :
        ↥(X.unop.unop.1) → MvPolynomial ↥(X.unop.unop.1) A)) ^ m) ⊗[A] (B : Type u)) :
    (smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm
        (MvPolynomial.variableIdealPowTensorComm A ↥(X.unop.unop.1) (B : Type u) m
          ((show MvPolynomial ↥(X.unop.unop.1) A from s) • z)) =
      s • (smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm
        (MvPolynomial.variableIdealPowTensorComm A ↥(X.unop.unop.1) (B : Type u) m z) := by
  induction z using TensorProduct.inductionOn with
  | tmul p b =>
      refine Subtype.ext ((smallPolynomialQuotientAlgEquiv A B κ X).injective ?_)
      rw [TensorProduct.smul_tmul']
      rw [coe_smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm]
      rw [smallPolynomialAugmentationIdealPowStructure_smul_coe]
      rw [map_mul]
      rw [coe_smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm]
      rw [Submodule.coe_smul, smul_eq_mul, map_mul, mul_smul_comm]
      rw [smallPolynomialQuotientAlgEquiv_smallSiteStructureToQuotient]
  | add y z hy hz =>
      rw [smul_add,
        (MvPolynomial.variableIdealPowTensorComm A ↥(X.unop.unop.1) (B : Type u) m).map_add,
        (smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm.map_add, hy, hz,
        (MvPolynomial.variableIdealPowTensorComm A ↥(X.unop.unop.1) (B : Type u) m).map_add,
        (smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm.map_add, smul_add]

/-! ### The `A[S]`-linear normal form on sections -/

/-- **The `A[S]`-linear normal form on sections.** Over an object `U` of the small model whose
point is `0`, the sections of `𝒦ᵐ` are the `𝒪(U)`-module `𝔪ᵐ ⊗_A B` of
`StacksDraft.PolynomialLocalComplex.tensorVariableIdealPow`, with `𝒪(U) = A[S]` acting through
the left tensor factor.

The underlying bijection is the `B`-linear normal form
`CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm` composed with the interchange
`MvPolynomial.variableIdealPowTensorComm`; its `𝒪(U)`-equivariance is
`CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm_smul`. -/
def smallPolynomialAugmentationIdealPowLocalIso (m : ℕ)
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) (h0 : smallSitePoint A B κ X = 0) :
    (smallPolynomialAugmentationIdealPowStructureModule A B κ m).obj X ≅
      StacksDraft.PolynomialLocalComplex.tensorVariableIdealPow
        (E := ↥(X.unop.unop.1)) (ModuleCat.of A (B : Type u)) m :=
  letI : Module ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)
      ((smallPolynomialAugmentationIdealPow A B κ m ⋙
        forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).obj X : Type u) :=
    smallPolynomialAugmentationIdealPowModuleStructure A B κ m X
  letI : Module (MvPolynomial ↥(X.unop.unop.1) A)
      ((smallPolynomialAugmentationIdealPow A B κ m ⋙
        forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).obj X : Type u) :=
    smallPolynomialAugmentationIdealPowModuleStructure A B κ m X
  letI : Module ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)
      (↥(Ideal.span (Set.range (MvPolynomial.X :
        ↥(X.unop.unop.1) → MvPolynomial ↥(X.unop.unop.1) A)) ^ m) ⊗[A] (B : Type u)) :=
    inferInstanceAs (Module (MvPolynomial ↥(X.unop.unop.1) A)
      (↥(Ideal.span (Set.range (MvPolynomial.X :
        ↥(X.unop.unop.1) → MvPolynomial ↥(X.unop.unop.1) A)) ^ m) ⊗[A] (B : Type u)))
  let f : (↥(Ideal.span (Set.range (MvPolynomial.X :
        ↥(X.unop.unop.1) → MvPolynomial ↥(X.unop.unop.1) A)) ^ m) ⊗[A] (B : Type u)) →ₗ[
          ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)]
      ((smallPolynomialAugmentationIdealPow A B κ m ⋙
        forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).obj X : Type u) :=
    { toFun := fun z => (smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm
        (MvPolynomial.variableIdealPowTensorComm A ↥(X.unop.unop.1) (B : Type u) m z)
      map_add' := fun y z => by
        rw [(MvPolynomial.variableIdealPowTensorComm A ↥(X.unop.unop.1) (B : Type u) m).map_add,
          (smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm.map_add]
        exact rfl
      map_smul' := fun s z =>
        smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm_smul A B κ m X h0 s z }
  let e := LinearEquiv.ofBijective f
    (by
      exact (smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm.bijective.comp
        (MvPolynomial.variableIdealPowTensorComm A ↥(X.unop.unop.1) (B : Type u) m).bijective)
  { hom := ModuleCat.ofHom e.symm.toLinearMap
    inv := ModuleCat.ofHom e.toLinearMap
    hom_inv_id := ModuleCat.hom_ext (LinearMap.ext fun x => e.apply_symm_apply x)
    inv_hom_id := ModuleCat.hom_ext (LinearMap.ext fun z => e.symm_apply_apply z) }

/-- The inverse of the `A[S]`-linear normal form is the `B`-linear normal form composed with the
interchange.  This pins `CommAlgCat.smallPolynomialAugmentationIdealPowLocalIso` down. -/
@[simp]
lemma smallPolynomialAugmentationIdealPowLocalIso_inv_apply (m : ℕ)
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) (h0 : smallSitePoint A B κ X = 0)
    (z : ↥(Ideal.span (Set.range (MvPolynomial.X :
        ↥(X.unop.unop.1) → MvPolynomial ↥(X.unop.unop.1) A)) ^ m) ⊗[A] (B : Type u)) :
    (smallPolynomialAugmentationIdealPowLocalIso A B κ m X h0).inv.hom z =
      (smallPolynomialAugmentationIdealPowNormalForm A B κ m X h0).symm
        (MvPolynomial.variableIdealPowTensorComm A ↥(X.unop.unop.1) (B : Type u) m z) := rfl

/-! ### Compatibility with the inclusions `𝒦ᵐ ⊆ 𝒦ⁿ` -/

/-- **The `A[S]`-linear normal form is compatible with the inclusions `𝒦ᵐ ⊆ 𝒦ⁿ`** for `n ≤ m`,
written with the inverses: the inclusion of the filtration corresponds to
`StacksDraft.PolynomialLocalComplex.tensorVariableIdealPowMap`, the base change of `𝔪ᵐ ⊆ 𝔪ⁿ`.

Both composites carry `p ⊗ b` to `b · p` by
`CommAlgCat.coe_smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm`, the inclusions
being the identity on underlying polynomials. -/
lemma smallPolynomialAugmentationIdealPowLocalIso_inv_comp {n m : ℕ} (h : n ≤ m)
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) (h0 : smallSitePoint A B κ X = 0) :
    (smallPolynomialAugmentationIdealPowLocalIso A B κ m X h0).inv ≫
        (smallPolynomialAugmentationIdealPowStructureOfLE A B κ h).app X =
      StacksDraft.PolynomialLocalComplex.tensorVariableIdealPowMap
          (E := ↥(X.unop.unop.1)) (ModuleCat.of A (B : Type u)) h ≫
        (smallPolynomialAugmentationIdealPowLocalIso A B κ n X h0).inv := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  induction z using TensorProduct.inductionOn with
  | tmul p b =>
      refine Subtype.ext ((smallPolynomialQuotientAlgEquiv A B κ X).injective ?_)
      exact (coe_smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm
          A B κ m X h0 p b).trans
        (coe_smallPolynomialAugmentationIdealPowNormalForm_symm_tensorComm A B κ n X h0
          (Submodule.inclusion (Ideal.pow_le_pow_right h) p) b).symm
  | add y z hy hz => rw [map_add, map_add, hy, hz]

/-- **The `A[S]`-linear normal form is compatible with the inclusions `𝒦ᵐ ⊆ 𝒦ⁿ`** for `n ≤ m`:
the square relating the normal forms at `m` and at `n` with the inclusion of the filtration and
`StacksDraft.PolynomialLocalComplex.tensorVariableIdealPowMap` commutes. -/
lemma smallPolynomialAugmentationIdealPowLocalIso_hom_comp {n m : ℕ} (h : n ≤ m)
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) (h0 : smallSitePoint A B κ X = 0) :
    (smallPolynomialAugmentationIdealPowLocalIso A B κ m X h0).hom ≫
        StacksDraft.PolynomialLocalComplex.tensorVariableIdealPowMap
          (E := ↥(X.unop.unop.1)) (ModuleCat.of A (B : Type u)) h =
      (smallPolynomialAugmentationIdealPowStructureOfLE A B κ h).app X ≫
        (smallPolynomialAugmentationIdealPowLocalIso A B κ n X h0).hom :=
  (Iso.comp_inv_eq _).1
    ((Category.assoc _ _ _).trans
      ((Iso.inv_comp_eq _).1
        (smallPolynomialAugmentationIdealPowLocalIso_inv_comp A B κ h X h0)).symm)

/-! ### The local claim at an object of the site -/

/-- **The local claim of [Stacks, Tag 08RF] at an object of the site.** Let `U` be an object of
the small model of `C_{B/A}` whose point is `0`, so that `𝒪(U) = A[S]`, and let `M` be an
`𝒪(U)`-module killed by the ideal `𝔪` of the variables.  Then for `j < k` the inclusion
`𝒦^{n+k} ⊆ 𝒦ⁿ` induces the zero map on `Tor'_j^{𝒪(U)}(-, M)`.

This is
`StacksDraft.PolynomialLocalComplex.tor'_map_app_tensorVariableIdealPowMap_eq_zero` — the local
claim with the ideal resolved — transported along
`CommAlgCat.smallPolynomialAugmentationIdealPowLocalIso`, whose compatibility with the
inclusions is `CommAlgCat.smallPolynomialAugmentationIdealPowLocalIso_inv_comp`.

Over a surjective `A → B` the hypothesis on the point costs nothing:
`CommAlgCat.app_eq_zero_of_forall_smallSitePoint_eq_zero` reduces an objectwise vanishing to the
objects whose point is `0`. -/
theorem tor'_map_app_smallPolynomialAugmentationIdealPowStructureOfLE_eq_zero
    (n k j : ℕ) (hj : j < k) (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ)
    (h0 : smallSitePoint A B κ X = 0)
    (M : ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A))
    (hM : ∀ r ∈ (Ideal.span (Set.range (MvPolynomial.X :
        ↥(X.unop.unop.1) → MvPolynomial ↥(X.unop.unop.1) A)) :
        Ideal (MvPolynomial ↥(X.unop.unop.1) A)), ∀ x : M, r • x = 0) :
    ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
      ((smallPolynomialAugmentationIdealPowStructureOfLE A B κ
        (Nat.le_add_right n k)).app X)).app M = 0 := by
  obtain ⟨Q⟩ := HasProjectiveResolution.out (Z := M)
  have hz := StacksDraft.PolynomialLocalComplex.tor'_map_app_tensorVariableIdealPowMap_eq_zero
    (ModuleCat.of A (B : Type u)) Q hM n k j hj
  have hsq : ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
          (smallPolynomialAugmentationIdealPowLocalIso A B κ (n + k) X h0).inv).app M ≫
        ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
          ((smallPolynomialAugmentationIdealPowStructureOfLE A B κ
            (Nat.le_add_right n k)).app X)).app M =
      ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
          (StacksDraft.PolynomialLocalComplex.tensorVariableIdealPowMap
            (E := ↥(X.unop.unop.1)) (ModuleCat.of A (B : Type u))
            (Nat.le_add_right n k))).app M ≫
        ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
          (smallPolynomialAugmentationIdealPowLocalIso A B κ n X h0).inv).app M :=
    congrArg (fun α => NatTrans.app α M)
      (((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map_comp _ _).symm.trans
        ((congrArg ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map)
            (smallPolynomialAugmentationIdealPowLocalIso_inv_comp A B κ
              (Nat.le_add_right n k) X h0)).trans
          ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map_comp _ _)))
  have hzero : ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
          (StacksDraft.PolynomialLocalComplex.tensorVariableIdealPowMap
            (E := ↥(X.unop.unop.1)) (ModuleCat.of A (B : Type u))
            (Nat.le_add_right n k))).app M ≫
        ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
          (smallPolynomialAugmentationIdealPowLocalIso A B κ n X h0).inv).app M = 0 := by
    rw [hz, zero_comp]
  have hfin := hsq.trans hzero
  have hid : ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
          (smallPolynomialAugmentationIdealPowLocalIso A B κ (n + k) X h0).hom).app M ≫
        ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
          (smallPolynomialAugmentationIdealPowLocalIso A B κ (n + k) X h0).inv).app M = 𝟙 _ :=
    congrArg (fun α => NatTrans.app α M)
      (((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map_comp _ _).symm.trans
        ((congrArg ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map)
            (Iso.hom_inv_id
              (smallPolynomialAugmentationIdealPowLocalIso A B κ (n + k) X h0))).trans
          ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map_id _)))
  have k0 : ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
          (smallPolynomialAugmentationIdealPowLocalIso A B κ (n + k) X h0).hom).app M ≫
        (((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
            (smallPolynomialAugmentationIdealPowLocalIso A B κ (n + k) X h0).inv).app M ≫
          ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
            ((smallPolynomialAugmentationIdealPowStructureOfLE A B κ
              (Nat.le_add_right n k)).app X)).app M) = 0 := by
    rw [hfin, comp_zero]
  have k1 := (Category.assoc _ _ _).trans k0
  have k2 := (congrArg (fun φ => φ ≫
      ((Tor' (ModuleCat.{u} (MvPolynomial ↥(X.unop.unop.1) A)) j).map
        ((smallPolynomialAugmentationIdealPowStructureOfLE A B κ
          (Nat.le_add_right n k)).app X)).app M) hid).symm.trans k1
  exact (Category.id_comp _).symm.trans k2

/-! ### The reduction of an objectwise vanishing to the objects whose point is `0` -/

/-- **The reduction to the objects whose point is `0`.** For a surjective `A → B`, a morphism of
functors on the small model of `C_{B/A}` which vanishes at every object whose point is `0`
vanishes at every object.

This is `CommAlgCat.zeroPointSiteIso` — every object is isomorphic in the site to the object
with the same variables and the point `0`, by translating the variables along a lift of the
point — together with `Stacks.SheafOfModules.app_eq_zero_of_iso`.  Surjectivity enters here and
nowhere else in the second claim of [Stacks, Tag 08RF]. -/
theorem app_eq_zero_of_forall_smallSitePoint_eq_zero
    (hsurj : Function.Surjective (algebraMap A (B : Type u)))
    {D : Type*} [Category* D] [Preadditive D]
    {F₁ F₂ : (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ D} (α : F₁ ⟶ F₂)
    (h : ∀ Y : (smallBoundedPolynomialSite A B κ)ᵒᵖ, smallSitePoint A B κ Y = 0 → α.app Y = 0)
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) : α.app X = 0 :=
  Stacks.SheafOfModules.app_eq_zero_of_iso α (zeroPointSiteIso A B κ hsurj X)
    (h _ (smallSitePoint_op_op_zeroPointIndex A B κ X.unop.unop))

end CommAlgCat

end
