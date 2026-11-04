module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents

/-!
# Extensions of an object in degree zero by an object of `D^{≥ m}`

Let `𝒜` be an abelian category, `F` an object of `𝒜` and `K` an object of `D(𝒜)` with
`H^j(K) = 0` for `j < m`. Then taking cohomology is an isomorphism
`Ext^m_𝒜(F[0], K) = Hom_{D(𝒜)}(F[-m], K) ≅ Hom_𝒜(F, H^m(K))`, natural in `F`; this is
[Stacks, Tag 06XS] (Derived Categories, Lemma 13.27.3) in the form used for dualizing modules.
When `𝒜` is `R`-linear the isomorphism is `R`-linear.

## Main definitions

* `DerivedCategory.extSingleLinearEquivOfIsGE` — the `R`-linear isomorphism
  `Ext^m_𝒜(F[0], K) ≃ₗ[R] Hom_𝒜(F, H^m(K))` for `K` in `D^{≥ m}(𝒜)`.

## Main results

* `DerivedCategory.extSingleLinearEquivOfIsGE_symm_comp` — naturality in `F`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace DerivedCategory

variable (R : Type*) [Ring R] {C : Type*} [Category C] [Abelian C] [Linear R C]
  [HasDerivedCategory C]

/-- The map `Ext^m_𝒜(F[0], K) ⟶ Hom_𝒜(F, H^m(K))` taking cohomology in degree zero, read through
`H⁰(F[0]) = F`. -/
def extSingleToHom (F : C) (K : DerivedCategory C) (m : ℤ)
    (α : DerivedCategory.Ext ((singleFunctor C 0).obj F) K m) : F ⟶ (homologyFunctor C m).obj K :=
  (singleFunctorCompHomologyFunctorIso C 0).inv.app F ≫
    (homologyFunctor C 0).shiftMap α 0 m (add_zero m)

/-- **`Ext^m_𝒜(F[0], K) ≅ Hom_𝒜(F, H^m(K))` for `K` in degrees `≥ m`**, as an `R`-linear
isomorphism ([Stacks, Tag 06XS]). -/
def extSingleLinearEquivOfIsGE (F : C) (K : DerivedCategory C) (m : ℤ) [K.IsGE m] :
    DerivedCategory.Ext ((singleFunctor C 0).obj F) K m ≃ₗ[R]
      (F ⟶ (homologyFunctor C m).obj K) :=
  have : Functor.Linear R ((homologyFunctor C 0).shift (0 : ℤ)) := homologyFunctor_linear R 0
  LinearEquiv.ofBijective
    { toFun := extSingleToHom F K m
      map_add' α₁ α₂ := by
        simp only [extSingleToHom, Functor.shiftMap, Functor.map_add, Preadditive.add_comp]
        exact Preadditive.comp_add _ _ _ _ _ _
      map_smul' r α := by
        simp only [extSingleToHom, Functor.shiftMap, Functor.map_smul, Linear.smul_comp]
        exact Linear.comp_smul _ _ _ _ _ _ }
    (by
      let e := (singleFunctorCompHomologyFunctorIso C 0).app F
      have h := bijective_homologyFunctor_shiftMap_of_isLE_of_isGE ((singleFunctor C 0).obj F) K
        0 m m m (add_zero m) le_rfl
      refine ⟨fun α₁ α₂ hα => h.1 ((e.cancel_iso_inv_left _ _).1 hα), fun g => ?_⟩
      obtain ⟨α, hα⟩ := h.2 (e.hom ≫ g)
      exact ⟨α, (congrArg (e.inv ≫ ·) hα).trans (e.inv_hom_id_assoc g)⟩)

/-- The isomorphism `extSingleLinearEquivOfIsGE` sends a class `α` to `extSingleToHom F K m α`. -/
@[simp]
theorem extSingleLinearEquivOfIsGE_apply (F : C) (K : DerivedCategory C) (m : ℤ) [K.IsGE m]
    (α : DerivedCategory.Ext ((singleFunctor C 0).obj F) K m) :
    extSingleLinearEquivOfIsGE R F K m α = extSingleToHom F K m α :=
  rfl

/-- `extSingleToHom` is natural in the object placed in degree zero. -/
theorem extSingleToHom_comp {F G : C} (φ : F ⟶ G) (K : DerivedCategory C) (m : ℤ)
    (α : DerivedCategory.Ext ((singleFunctor C 0).obj G) K m) :
    extSingleToHom F K m ((singleFunctor C 0).map φ ≫ α) = φ ≫ extSingleToHom G K m α := by
  rw [extSingleToHom, extSingleToHom, Functor.shiftMap_comp']
  exact ((singleFunctorCompHomologyFunctorIso C 0).inv.naturality_assoc φ _).symm

/-- **Naturality in `F`.** The inverse isomorphism carries `φ ≫ g` to the composite of
`F[0] ⟶ G[0]` with the class of `g`. -/
theorem extSingleLinearEquivOfIsGE_symm_comp {F G : C} (φ : F ⟶ G) (K : DerivedCategory C)
    (m : ℤ) [K.IsGE m] (g : G ⟶ (homologyFunctor C m).obj K) :
    (extSingleLinearEquivOfIsGE R F K m).symm (φ ≫ g) =
      (singleFunctor C 0).map φ ≫ (extSingleLinearEquivOfIsGE R G K m).symm g := by
  apply (extSingleLinearEquivOfIsGE R F K m).injective
  rw [LinearEquiv.apply_symm_apply, extSingleLinearEquivOfIsGE_apply, extSingleToHom_comp,
    ← extSingleLinearEquivOfIsGE_apply R, LinearEquiv.apply_symm_apply]

end DerivedCategory
