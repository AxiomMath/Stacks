module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.AcyclicTwoExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# `Ext` out of a sheaf supported on a closed subscheme, from the higher direct images of the
complement

Let `i : Z ⟶ X` be a closed immersion and `j : U ⟶ X` the inclusion of the open complement, and
let `F` be a sheaf of `Λ`-modules on `U_étale`. Suppose that the higher direct images of `F` along
`j` are concentrated in degrees `0` and `1`, with `j_* F ≅ A` and `R¹j_* F ≅ i_* N`. Then there is
a class `γ ∈ Ext²_X(i_* N, A)` such that for every sheaf `G` of `Λ`-modules on `Z_étale` the map

`Ext^q_Z(G, N) ⟶ Ext^{q+2}_X(i_* G, A)`,  `y ↦ i_*(y) ∘ γ`

is bijective for every `q`, and `Ext^q_X(i_* G, A) = 0` for `q < 2`.

This is the homological half of cohomological purity in codimension one (SGA 4 XVI 3.7, Milne,
*Lectures on étale cohomology* §16): with `F = Λ_U`, `A = Λ_X` and `N = Λ_Z` it says
`Ri^! Λ_X ≅ Λ_Z[-2]`, read through `Ext` out of `i_*`.

The proof takes an injective resolution `F → I^•` on `U`. The complex `K = j_* I^•` computes the
higher direct images, so `0 → Z⁰(K) → K⁰ → Z¹(K) → H¹(K) → 0` is exact with `Z⁰(K) ≅ A` and
`H¹(K) ≅ i_* N`. Every `Kⁿ = j_* Iⁿ` is injective and receives no nonzero map from a sheaf
supported on `Z` (its restriction to `U` vanishes), so `Ext^•(i_* G, Kⁿ) = 0`, and the Yoneda
product with the class of that four-term sequence is bijective
(`CategoryTheory.Abelian.Ext.bijective_comp_complexTwoExtensionClass`). Finally `i_*` is exact,
fully faithful and preserves injectives, so it is bijective on `Ext`
(`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`).

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_etaleModuleDirectImage_of_injective`:
  `Ext^•(i_* G, j_* J) = 0` for `J` injective on `U`.
* `Stacks.EtaleCohomology.bijective_mapExtAddHom_etaleModuleDirectImage_closedImmersion`: `i_*`
  is bijective on `Ext`.
* `Stacks.EtaleCohomology.exists_ext_purity_of_rightDerived_complement`: the statement above.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

namespace Stacks.EtaleCohomology

section

variable (Λ : Type) [Ring Λ] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij in
/-- **No nonzero map from a sheaf supported on `Z` to a direct image from the complement**:
`Hom(i_* G, j_* H) = Hom(j^{-1} i_* G, H)` and `j^{-1} i_* G = 0`. -/
theorem subsingleton_hom_etaleModuleDirectImage_complement (G : EtaleModules.{u, 0} Λ Z)
    (H : EtaleModules.{u, 0} Λ U) :
    Subsingleton ((etaleModuleDirectImage.{u, 0} Λ i).obj G ⟶
      (etaleModuleDirectImage.{u, 0} Λ j).obj H) :=
  ⟨fun _ _ => ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).homEquiv _ _).symm.injective
    ((isZero_etaleModuleRestriction_etaleModuleDirectImage Λ i j hij G).eq_of_src _ _)⟩

include hij in
/-- **`Ext^•(i_* G, j_* J) = 0` for `J` injective on the open complement `U`.** The direct image
`j_* J` is injective, so only `Ext⁰ = Hom` can be nonzero, and it vanishes because the restriction
of `i_* G` to `U` is zero. -/
theorem subsingleton_ext_etaleModuleDirectImage_of_injective (G : EtaleModules.{u, 0} Λ Z)
    (J : EtaleModules.{u, 0} Λ U) [Injective J] (m : ℕ) :
    Subsingleton (Ext ((etaleModuleDirectImage.{u, 0} Λ i).obj G)
      ((etaleModuleDirectImage.{u, 0} Λ j).obj J) m) := by
  have : Injective ((etaleModuleDirectImage.{u, 0} Λ j).obj J) :=
    Functor.PreservesInjectiveObjects.injective_obj inferInstance
  rcases m with _ | m
  · have := subsingleton_hom_etaleModuleDirectImage_complement Λ i j hij G J
    exact Ext.homEquiv₀.subsingleton
  · exact Ext.subsingleton_of_injective _ _ m

end

section MapExt

variable (Λ : Type) [Ring Λ] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The direct image along a closed immersion preserves finite limits. -/
instance etaleModuleDirectImage_preservesFiniteLimits_closedImmersion :
    PreservesFiniteLimits (etaleModuleDirectImage.{u, 0} Λ i) :=
  have := (etaleModuleInverseImageAdj.{u, 0} Λ i).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

/-- The direct image along a closed immersion is full. -/
instance etaleModuleDirectImage_full_closedImmersion : (etaleModuleDirectImage.{u, 0} Λ i).Full :=
  (etaleModuleDirectImageFullyFaithful Λ i).full

/-- The direct image along a closed immersion is faithful. -/
instance etaleModuleDirectImage_faithful_closedImmersion :
    (etaleModuleDirectImage.{u, 0} Λ i).Faithful :=
  (etaleModuleDirectImageFullyFaithful Λ i).faithful

/-- **Direct image along a closed immersion is bijective on `Ext`**: it is exact, fully faithful
and preserves injective objects. -/
theorem bijective_mapExtAddHom_etaleModuleDirectImage_closedImmersion
    (G H : EtaleModules.{u, 0} Λ Z) (n : ℕ) :
    Function.Bijective (fun y : Ext G H n =>
      y.mapExactFunctor (etaleModuleDirectImage.{u, 0} Λ i)) :=
  (etaleModuleDirectImage.{u, 0} Λ i).mapExt_bijective_of_preservesInjectiveObjects G H n

end MapExt

section Purity

variable (Λ : Type) [Ring Λ] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] (hij : Set.range j.base = (Set.range i.base)ᶜ)

/-- Yoneda product with an isomorphism in degree zero is bijective. -/
theorem bijective_comp_mk₀_iso {C : Type*} [Category C] [Abelian C] [HasExt.{u + 1} C]
    {P A A' : C} (e : A ≅ A') (n : ℕ) :
    Function.Bijective (fun y : Ext P A n => y.comp (Ext.mk₀ e.hom) (add_zero n)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun y => y.comp (Ext.mk₀ e.inv) (add_zero n),
    fun y => ?_, fun y => ?_⟩ <;>
  simp [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

include hij in
/-- **Cohomological purity in `Ext` form, from the higher direct images of the complement.** If
`j_* F ≅ A`, `R¹j_* F ≅ i_* N` and `R^q j_* F = 0` for `q ≥ 2`, then there is
`γ ∈ Ext²_X(i_* N, A)` such that `y ↦ i_*(y) ∘ γ` is a bijection
`Ext^q_Z(G, N) ≅ Ext^{q+2}_X(i_* G, A)` for every `G` and `q`, and `Ext^q_X(i_* G, A) = 0` for
`q < 2`. -/
theorem exists_ext_purity_of_rightDerived_complement (F : EtaleModules.{u, 0} Λ U)
    (A : EtaleModules.{u, 0} Λ X) (N : EtaleModules.{u, 0} Λ Z)
    (h0 : Nonempty ((etaleModuleDirectImage.{u, 0} Λ j).obj F ≅ A))
    (h1 : Nonempty (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived 1).obj F ≅
      (etaleModuleDirectImage.{u, 0} Λ i).obj N))
    (h2 : ∀ q, 2 ≤ q → IsZero (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj F)) :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} Λ i).obj N) A 2,
      (∀ (G : EtaleModules.{u, 0} Λ Z) (q : ℕ), Function.Bijective (fun y : Ext G N q =>
        (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} Λ i)).comp γ
          (show q + 2 = q + 2 from rfl))) ∧
      (∀ (G : EtaleModules.{u, 0} Λ Z) (q : ℕ), q < 2 →
        Subsingleton (Ext ((etaleModuleDirectImage.{u, 0} Λ i).obj G) A q)) := by
  obtain ⟨e0⟩ := h0
  obtain ⟨e1⟩ := h1
  let jd := etaleModuleDirectImage.{u, 0} Λ j
  let I : InjectiveResolution F := injectiveResolution F
  let K : CochainComplex (EtaleModules.{u, 0} Λ X) ℕ := (jd.mapHomologicalComplex _).obj I.cocomplex
  have hd0 : K.d ((ComplexShape.up ℕ).prev 0) 0 = 0 := by
    rw [CochainComplex.prev_nat_zero]
    exact K.shape _ _ (by simp)
  let eZ : K.cycles 0 ≅ A :=
    K.isoHomologyπ _ 0 rfl hd0 ≪≫ (I.isoRightDerivedObj jd 0).symm ≪≫
      jd.rightDerivedZeroIsoSelf.app F ≪≫ e0
  let eH : (etaleModuleDirectImage.{u, 0} Λ i).obj N ≅ K.homology 1 :=
    e1.symm ≪≫ I.isoRightDerivedObj jd 1
  have hK : ∀ (G : EtaleModules.{u, 0} Λ Z) (q m : ℕ),
      Subsingleton (Ext ((etaleModuleDirectImage.{u, 0} Λ i).obj G) (K.X q) m) := fun G q m =>
    subsingleton_ext_etaleModuleDirectImage_of_injective Λ i j hij G (I.cocomplex.X q) m
  have hH : ∀ q, 2 ≤ q → IsZero (K.homology q) := fun q hq =>
    (h2 q hq).of_iso (I.isoRightDerivedObj jd q).symm
  refine ⟨(Ext.mk₀ eH.hom).comp ((Ext.complexTwoExtensionClass K).comp (Ext.mk₀ eZ.hom)
    (add_zero 2)) (zero_add 2), fun G q => ?_, fun G q hq => ?_⟩
  · have e : (fun y : Ext G N q =>
        (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} Λ i)).comp
          ((Ext.mk₀ eH.hom).comp ((Ext.complexTwoExtensionClass K).comp (Ext.mk₀ eZ.hom)
            (add_zero 2)) (zero_add 2)) (show q + 2 = q + 2 from rfl)) =
        (fun y => y.comp (Ext.mk₀ eZ.hom) (add_zero (q + 2))) ∘
        (fun y => y.comp (Ext.complexTwoExtensionClass K) (rfl : q + 2 = q + 2)) ∘
        (fun y => y.comp (Ext.mk₀ eH.hom) (add_zero q)) ∘
        (fun y : Ext G N q => y.mapExactFunctor (etaleModuleDirectImage.{u, 0} Λ i)) := by
      funext y
      simp only [Function.comp_apply]
      rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc _ _ _ rfl (add_zero 2) rfl,
        Ext.comp_assoc (Ext.mk₀ eH.hom) (Ext.complexTwoExtensionClass K) (Ext.mk₀ eZ.hom)
          (zero_add 2) (add_zero 2) rfl]
    rw [e]
    exact (bijective_comp_mk₀_iso eZ _).comp
      ((Ext.bijective_comp_complexTwoExtensionClass K _ (hK G) hH q).comp
        ((bijective_comp_mk₀_iso eH q).comp
          (bijective_mapExtAddHom_etaleModuleDirectImage_closedImmersion Λ i G N q)))
  · have := Ext.subsingleton_ext_cycles_zero K _ (hK G) hH q hq
    exact (bijective_comp_mk₀_iso (P := (etaleModuleDirectImage.{u, 0} Λ i).obj G) eZ
      q).2.subsingleton

end Purity

end Stacks.EtaleCohomology

end
