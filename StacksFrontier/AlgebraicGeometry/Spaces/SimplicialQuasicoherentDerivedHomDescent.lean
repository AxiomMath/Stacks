module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedDescentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictDerivedSystem
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedModuleHomLeftDerived
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemVertexExtension
public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSimplicialGluing

/-!
# Negative Ext groups and Hom descent along an fppf hypercovering

Let `a : U → X` be an fppf hypercovering of an algebraic space and `K, E` objects of
`D_{QCoh}(𝒪_X)` whose pullbacks to every `U_n` have no negative Ext groups. Then
`Ext^i_X(K, E) = 0` for `i < 0` and the sequence
$$0 ⟶ Hom_X(K, E) ⟶ Hom_{U_0}(La_0^*K, La_0^*E) ⟶ Hom_{U_1}(La_1^*K, La_1^*E)$$
is exact, the second map being the difference of the two pullbacks along the faces `U_1 ⟶ U_0`.

## Main results

In the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `negativeExt_eq_zero_and_exact_derivedPullback`: the negative Ext groups `Ext^i_X(K, E)` vanish
  and the sequence above is exact.
* `augmentationFaceTransport`: the map `Hom_{U_0}(La_0^*K, La_0^*E) ⟶ Hom_{U_1}(La_1^*K, La_1^*E)`
  along a face.
* `strictComponent_shift_hom_eq_zero`: the vanishing hypotheses of Stacks 0D9R and 0D9S for the
  strict system of `Lb^*K, Lb^*E`.
* `injective_derivedPullback_map_of_negativeExt` and
  `exact_derivedPullback_map_augmentationFaceTransport`: injectivity of the first map and exactness
  at the middle term.

In the namespace `CategoryTheory`:

* `SimplicialSiteSituation.exists_hom_derivedComponentModuleRestriction_zero_eq_of_transport_eq`:
  a degree-zero map with equal face transports comes from `D(O)`.

## Implementation notes

The Stacks Project proves this with Stacks 0D9R and 0D9S on the small étale site of `U`, which
assume the transitions of the structure sheaf flat; for an fppf hypercovering the degeneracy
`U_0 ⟶ U_1` need not be flat (the Čech nerve of `Spec k[ε] ⟶ Spec k`). The proof here runs on the
total site of the strict components of `U`, with the flatness-free forms of 0D9R and 0D9S,
`CategoryTheory.SimplicialSiteSituation.exists_hom_of_isCartesianDerivedModule` and
`SimplicialSiteSituation.eq_zero_of_isCartesian_of_derivedComponentModuleRestriction_map_eq_zero`
in the namespace `CategoryTheory`.

## References

* [Stacks Project, Tag 0DL9](https://stacks.math.columbia.edu/tag/0DL9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open scoped Simplicial

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory

/-- If `F ⋙ G ≅ H` with `G` faithful and `H` bijective on morphisms `K ⟶ E`, then so is `F`. -/
theorem Functor.bijective_map_of_comp_iso {C D E' : Type*} [Category C] [Category D] [Category E']
    (F : C ⥤ D) (G : D ⥤ E') (H : C ⥤ E') [G.Faithful] (ι : F ⋙ G ≅ H) {K E : C}
    (hH : Function.Bijective (fun g : K ⟶ E ↦ H.map g)) :
    Function.Bijective (fun g : K ⟶ E ↦ F.map g) := by
  have hG : ∀ g : K ⟶ E, H.map g = ι.inv.app K ≫ G.map (F.map g) ≫ ι.hom.app E := fun g ↦ by
    change H.map g = ι.inv.app K ≫ (F ⋙ G).map g ≫ ι.hom.app E
    rw [ι.hom.naturality, Iso.inv_hom_id_app_assoc]
  refine ⟨fun g g' hg ↦ hH.1 ?_, fun ψ ↦ ?_⟩
  · simp only at hg ⊢
    rw [hG, hG, hg]
  · obtain ⟨γ, hγ⟩ := hH.2 (ι.inv.app K ≫ G.map ψ ≫ ι.hom.app E)
    refine ⟨γ, G.map_injective ?_⟩
    simp only at hγ ⊢
    rw [hG] at hγ
    exact (cancel_mono (ι.hom.app E)).1 (by simpa using hγ)

/-- In a category with a shift by `ℤ`, if every map `A ⟶ B⟦-j⟧` vanishes then so does every map
`A⟦j⟧ ⟶ B`. -/
theorem eq_zero_of_shift_of_forall_eq_zero {C : Type*} [Category C] [Preadditive C]
    [HasShift C ℤ] [∀ k : ℤ, (shiftFunctor C k).Additive] {A B : C} (j : ℤ)
    (h : ∀ g : A ⟶ B⟦-j⟧, g = 0) (g : A⟦j⟧ ⟶ B) : g = 0 := by
  have h0 : (shiftEquiv C j).toAdjunction.homEquiv A B g = 0 := h _
  rw [← ((shiftEquiv C j).toAdjunction.homEquiv A B).symm_apply_apply g, h0,
    Adjunction.homEquiv_counit, Functor.map_zero]
  exact zero_comp

namespace SimplicialSiteSituation

/-- **A degree-zero map with equal face transports comes from `D(O)`.** Let `K` be cartesian,
`K'(𝟙_{[0]})` invertible and `Hom(K_i[i - 1], K'_i) = 0` for `i > 1`. A map `ψ₀ : K_0 ⟶ K'_0`
whose two transports `K(δ_i)⁻¹ ≫ Lf_{δ_i}^*ψ₀ ≫ K'(δ_i)` to degree one agree is the degree-zero
component of a map `K ⟶ K'`. -/
theorem exists_hom_derivedComponentModuleRestriction_zero_eq_of_transport_eq
    {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology CommRingCat.{u}} {K K'}
    (hK : S.IsCartesianDerivedModule O K)
    (hK' : IsIso ((S.derivedComponentModuleTransition O (𝟙 ⦋0⦌)).app K'))
    (hHom : ∀ i : ℕ, 1 < i →
      ∀ g : ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K)⟦(i : ℤ) - 1⟧ ⟶
          (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (ψ₀ : (S.derivedComponentModuleRestriction O ⦋0⦌).obj K ⟶
      (S.derivedComponentModuleRestriction O ⦋0⦌).obj K')
    (h₁ : haveI := hK (SimplexCategory.δ (0 : Fin 2))
      haveI := hK (SimplexCategory.δ (1 : Fin 2))
      inv ((S.derivedComponentModuleTransition O (SimplexCategory.δ (0 : Fin 2))).app K) ≫
          (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).map ψ₀ ≫
          (S.derivedComponentModuleTransition O (SimplexCategory.δ (0 : Fin 2))).app K' =
        inv ((S.derivedComponentModuleTransition O (SimplexCategory.δ (1 : Fin 2))).app K) ≫
          (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).map ψ₀ ≫
          (S.derivedComponentModuleTransition O (SimplexCategory.δ (1 : Fin 2))).app K') :
    ∃ γ : K ⟶ K', (S.derivedComponentModuleRestriction O ⦋0⦌).map γ = ψ₀ := by
  obtain ⟨f, hf⟩ := SimplicialDerivedModuleSystem.exists_hom_app_zero_eq_of_vertexTransport_eq
    (V := S.derivedModuleSystem O K') (S.derivedModuleSystem_cartesian O K hK) ψ₀ hK' h₁
  obtain ⟨γ, hγ⟩ :=
    S.exists_hom_derivedComponentModuleRestriction_zero_eq_of_isCartesian O K K' hK hHom f
  exact ⟨γ, hγ.trans hf⟩

end SimplicialSiteSituation

end CategoryTheory

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

section FaceTransport

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : SimplicialObject (AlgebraicSpaces B S hS)} {X : AlgebraicSpaces B S hS}
  (a : U ⟶ (Functor.const _).obj X)

/-- The pullback of a map `La_0^*K ⟶ La_0^*E` along the face `X(δ_i) : U_1 ⟶ U_0`, read through
`La_0^* ⋙ LX(δ_i)^* ≅ La_1^*`. -/
def augmentationFaceTransport (i : Fin 2)
    {K E : @DerivedCategory (spacesEtaleRingedTopos B S hS X).Modules _ _
      (HasDerivedCategory.standard _)}
    (ψ : (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).obj K ⟶
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos B S hS X)
        (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).obj E) :
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋1⦌)))
        (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom (a.app (op ⦋1⦌)))).obj K ⟶
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋1⦌)))
        (Y := spacesEtaleRingedTopos B S hS X)
        (spacesEtaleRingedToposHom (a.app (op ⦋1⦌)))).obj E :=
  (augmentationTransitionDerivedIso a (SimplexCategory.δ i)).inv.app K ≫
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋1⦌)))
      (Y := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
      (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ i).op))).map ψ ≫
    (augmentationTransitionDerivedIso a (SimplexCategory.δ i)).hom.app E

/-- **Vanishing of shifted maps between the components of the strict systems.** If every map
`La_n^*K ⟶ (La_n^*E)⟦-j⟧` vanishes, so does every map `(Lb^*K)_n⟦j⟧ ⟶ (Lb^*E)_n`. -/
theorem strictComponent_shift_hom_eq_zero (n : SimplexCategory) (j : ℤ)
    {K E : @DerivedCategory (spacesEtaleRingedTopos B S hS X).Modules _ _
      (HasDerivedCategory.standard _)}
    (hv : ∀ g : (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom (a.app (op n)))).obj K ⟶
      ((derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS X)
        (spacesEtaleRingedToposHom (a.app (op n)))).obj E)⟦-j⟧, g = 0)
    (g : (((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) n).obj
        ((derivedPullback (X := strictRingedTopos U) (Y := spacesEtaleRingedTopos B S hS X)
          (strictAugmentationRingedToposHom a)).obj K))⟦j⟧ ⟶
      ((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) n).obj
        ((derivedPullback (X := strictRingedTopos U) (Y := spacesEtaleRingedTopos B S hS X)
          (strictAugmentationRingedToposHom a)).obj E)) :
    g = 0 := by
  let : HasDerivedCategory (spacesEtaleRingedTopos B S hS (U.obj (op n))).Modules :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      ((strictSituation U).componentRingedTopos (strictStructureSheaf U) n).Modules :=
    HasDerivedCategory.standard _
  have := derivedPullback_commShift (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
    (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) n)
    (strictComponentRingedToposHom U n)
  have h2 := eq_zero_of_shift_of_forall_eq_zero j hv
    ((shiftFunctor _ j).map ((strictAugmentationDegreeDerivedIso a n).inv.app K) ≫
      ((derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
        (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) n)
        (strictComponentRingedToposHom U n)).commShiftIso j).inv.app _ ≫
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
        (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) n)
        (strictComponentRingedToposHom U n)).map g ≫
      (strictAugmentationDegreeDerivedIso a n).hom.app E)
  refine (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
      (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) n)
      (strictComponentRingedToposHom U n)).map_injective ?_
  rw [Functor.map_zero]
  simp only [← Category.assoc] at h2
  rwa [Preadditive.IsIso.comp_right_eq_zero, Preadditive.IsIso.comp_left_eq_zero] at h2

/-- `La_n^*` read through the strict system: `La_n^*γ` is `L realize_n^*` of the degree-`n`
component of `Lb^*γ`, conjugated by the component isomorphisms. -/
theorem derivedPullback_map_eq_strictComponent (n : SimplexCategory)
    {K E : @DerivedCategory (spacesEtaleRingedTopos B S hS X).Modules _ _
      (HasDerivedCategory.standard _)} (γ : K ⟶ E) :
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom (a.app (op n)))).map γ =
      (strictAugmentationDegreeDerivedIso a n).inv.app K ≫
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
          (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) n)
          (strictComponentRingedToposHom U n)).map
          (((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) n).map
            ((derivedPullback (X := strictRingedTopos U) (Y := spacesEtaleRingedTopos B S hS X)
              (strictAugmentationRingedToposHom a)).map γ)) ≫
        (strictAugmentationDegreeDerivedIso a n).hom.app E := by
  rw [← cancel_epi ((strictAugmentationDegreeDerivedIso a n).hom.app K), Iso.hom_inv_id_app_assoc,
    ← (strictAugmentationDegreeDerivedIso a n).hom.naturality γ]
  rfl

/-- Pulling back `La_0^*γ` along a face gives `La_1^*γ`. -/
theorem augmentationFaceTransport_derivedPullback_map (i : Fin 2)
    {K E : @DerivedCategory (spacesEtaleRingedTopos B S hS X).Modules _ _
      (HasDerivedCategory.standard _)} (γ : K ⟶ E) :
    augmentationFaceTransport a i
        ((derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
          (Y := spacesEtaleRingedTopos B S hS X)
          (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).map γ) =
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋1⦌)))
        (Y := spacesEtaleRingedTopos B S hS X)
        (spacesEtaleRingedToposHom (a.app (op ⦋1⦌)))).map γ := by
  rw [augmentationFaceTransport, ← cancel_epi
    ((augmentationTransitionDerivedIso a (SimplexCategory.δ i)).hom.app K),
    Iso.hom_inv_id_app_assoc,
    ← (augmentationTransitionDerivedIso a (SimplexCategory.δ i)).hom.naturality γ]
  rfl

/-- **A face pullback, read on the strict system.** If `ψ₀` realizes to `ψ` in degree zero, the
transport of `ψ₀` along the face `δ_i` of the strict systems of `Lb^*K, Lb^*E` realizes to the
face pullback of `ψ`. -/
theorem derivedPullback_map_strictTransport_face (i : Fin 2)
    {K E : @DerivedCategory (spacesEtaleRingedTopos B S hS X).Modules _ _
      (HasDerivedCategory.standard _)}
    (ψ : (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).obj K ⟶
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).obj E)
    (ψ₀ : ((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) ⦋0⦌).obj
        ((derivedPullback (X := strictRingedTopos U) (Y := spacesEtaleRingedTopos B S hS X)
          (strictAugmentationRingedToposHom a)).obj K) ⟶
      ((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) ⦋0⦌).obj
        ((derivedPullback (X := strictRingedTopos U) (Y := spacesEtaleRingedTopos B S hS X)
          (strictAugmentationRingedToposHom a)).obj E))
    (hψ₀ : (strictAugmentationDegreeDerivedIso a ⦋0⦌).inv.app K ≫
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
          (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0⦌)
          (strictComponentRingedToposHom U ⦋0⦌)).map ψ₀ ≫
        (strictAugmentationDegreeDerivedIso a ⦋0⦌).hom.app E = ψ) :
    haveI := isCartesianDerivedModule_strictAugmentation a K (SimplexCategory.δ i)
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0 + 1⦌)))
        (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0 + 1⦌)
        (strictComponentRingedToposHom U ⦋0 + 1⦌)).map
      (inv (((strictSituation U).derivedComponentModuleTransition (strictStructureSheaf U)
          (SimplexCategory.δ i)).app
          ((derivedPullback (X := strictRingedTopos U) (Y := spacesEtaleRingedTopos B S hS X)
            (strictAugmentationRingedToposHom a)).obj K)) ≫
        ((strictSituation U).derivedTransitionPullback (strictStructureSheaf U)
          (SimplexCategory.δ i)).map ψ₀ ≫
        ((strictSituation U).derivedComponentModuleTransition (strictStructureSheaf U)
          (SimplexCategory.δ i)).app
          ((derivedPullback (X := strictRingedTopos U) (Y := spacesEtaleRingedTopos B S hS X)
            (strictAugmentationRingedToposHom a)).obj E)) =
      (strictAugmentationDegreeDerivedIso a ⦋0 + 1⦌).hom.app K ≫ augmentationFaceTransport a i ψ ≫
        (strictAugmentationDegreeDerivedIso a ⦋0 + 1⦌).inv.app E := by
  subst hψ₀
  rw [augmentationFaceTransport]
  simp only [Category.assoc]
  exact derivedPullback_map_strictTransport a (SimplexCategory.δ i) K E ψ₀

/-- **A map with equal face pullbacks comes from `Lb^*K ⟶ Lb^*E`.** If the pullbacks to every
`U_n` have no negative Ext groups and the two face pullbacks of `ψ : La_0^*K ⟶ La_0^*E` agree, then
`ψ` is the realization of the degree-zero component of a map `Lb^*K ⟶ Lb^*E`. -/
theorem exists_derivedPullback_strictAugmentation_hom_of_augmentationFaceTransport_eq
    {K E : @DerivedCategory (spacesEtaleRingedTopos B S hS X).Modules _ _
      (HasDerivedCategory.standard _)}
    (hvan : ∀ (n : SimplexCategory) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom (a.app (op n)))).obj K ⟶
        ((derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS X)
          (spacesEtaleRingedToposHom (a.app (op n)))).obj E)⟦i⟧, g = 0)
    (ψ : (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).obj K ⟶
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).obj E)
    (hψ : augmentationFaceTransport a 0 ψ = augmentationFaceTransport a 1 ψ) :
    ∃ γ' : (derivedPullback (X := strictRingedTopos U) (Y := spacesEtaleRingedTopos B S hS X)
          (strictAugmentationRingedToposHom a)).obj K ⟶
        (derivedPullback (X := strictRingedTopos U) (Y := spacesEtaleRingedTopos B S hS X)
          (strictAugmentationRingedToposHom a)).obj E,
      (strictAugmentationDegreeDerivedIso a ⦋0⦌).inv.app K ≫
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
          (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0⦌)
          (strictComponentRingedToposHom U ⦋0⦌)).map
          (((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) ⦋0⦌).map
            γ') ≫
        (strictAugmentationDegreeDerivedIso a ⦋0⦌).hom.app E = ψ := by
  obtain ⟨ψ₀, hψ₀⟩ := (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
    (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0⦌)
    (strictComponentRingedToposHom U ⦋0⦌)).map_surjective
    ((strictAugmentationDegreeDerivedIso a ⦋0⦌).hom.app K ≫ ψ ≫
      (strictAugmentationDegreeDerivedIso a ⦋0⦌).inv.app E)
  have hψ₀' : (strictAugmentationDegreeDerivedIso a ⦋0⦌).inv.app K ≫
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
        (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0⦌)
        (strictComponentRingedToposHom U ⦋0⦌)).map ψ₀ ≫
      (strictAugmentationDegreeDerivedIso a ⦋0⦌).hom.app E = ψ := by
    rw [hψ₀]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Iso.inv_hom_id_app_assoc]
  have h₁ := (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0 + 1⦌)))
    (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0 + 1⦌)
    (strictComponentRingedToposHom U ⦋0 + 1⦌)).map_injective
    ((derivedPullback_map_strictTransport_face a 0 ψ ψ₀ hψ₀').trans
      ((congrArg (fun k ↦ (strictAugmentationDegreeDerivedIso a ⦋0 + 1⦌).hom.app K ≫ k ≫
        (strictAugmentationDegreeDerivedIso a ⦋0 + 1⦌).inv.app E) hψ).trans
        (derivedPullback_map_strictTransport_face a 1 ψ ψ₀ hψ₀').symm))
  have hex :=
    SimplicialSiteSituation.exists_hom_derivedComponentModuleRestriction_zero_eq_of_transport_eq
      (isCartesianDerivedModule_strictAugmentation a K)
      (isCartesianDerivedModule_strictAugmentation a E (𝟙 ⦋0⦌))
      (fun i _ g ↦ strictComponent_shift_hom_eq_zero a ⦋i⦌ ((i : ℤ) - 1)
        (hvan ⦋i⦌ (-((i : ℤ) - 1)) (by omega)) g) ψ₀
  have hex2 := hex h₁
  obtain ⟨γ', hγ'⟩ := hex2
  exact ⟨γ', (congrArg (fun x ↦ (strictAugmentationDegreeDerivedIso a ⦋0⦌).inv.app K ≫
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (U.obj (op ⦋0⦌)))
      (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0⦌)
      (strictComponentRingedToposHom U ⦋0⦌)).map x ≫
    (strictAugmentationDegreeDerivedIso a ⦋0⦌).hom.app E) hγ').trans hψ₀'⟩

end FaceTransport

section HomDescent

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  {a : U ⟶ (SimplicialObject.const T.Spaces).obj X}

variable (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)

include h in
/-- **`Lb^*` is fully faithful on `D_{QCoh}(𝒪_X)`**, for the augmentation `b` of the total site
of the strict components. -/
theorem bijective_derivedPullback_strictAugmentationRingedToposHom_map
    {K E : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
      (HasDerivedCategory.standard _)}
    (hK : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) K)
    (hE : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) E) :
    Function.Bijective (fun g : K ⟶ E ↦
      (derivedPullback (X := strictRingedTopos U)
        (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (strictAugmentationRingedToposHom a)).map g) := by
  have := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := ringedTopos U) (Y := strictRingedTopos U)
      (Z := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
      (strictAugmentationRingedToposHom a) (strictRingedToposHom U))
  exact Functor.bijective_map_of_comp_iso _
    (derivedPullback (X := ringedTopos U) (Y := strictRingedTopos U) (strictRingedToposHom U)) _
    (derivedPullbackCompIso (strictRingedToposHom U) (strictAugmentationRingedToposHom a) ≪≫
      derivedPullbackIsoOfPullbackModulesIso
        (φ := RingedToposHom.comp (X := ringedTopos U) (Y := strictRingedTopos U)
          (Z := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (strictAugmentationRingedToposHom a) (strictRingedToposHom U))
        (ψ := augmentationRingedToposHom a)
        (strictAugmentationTwoIso a).pullbackModulesIso)
    (bijective_derivedPullback_map h hK hE)

include h in
/-- **`La_0^*` is injective on `Hom_X(K, E)`** when the pullbacks to every `U_n` have no
negative Ext groups. -/
theorem injective_derivedPullback_map_of_negativeExt
    {K E : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
      (HasDerivedCategory.standard _)}
    (hK : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) K)
    (hE : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) E)
    (hvan : ∀ (n : SimplexCategory) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback
          (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op n)))).obj K ⟶
        ((derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op n)))).obj E)⟦i⟧, g = 0) :
    Function.Injective (fun g : K ⟶ E ↦
      (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).map g) := by
  intro γ γ' hγ
  refine (bijective_derivedPullback_strictAugmentationRingedToposHom_map h hK hE).1
    (SimplicialSiteSituation.degreeZeroFaithful_of_eq_zero (strictSituation U)
      (strictStructureSheaf U) _ _
      (fun f hf ↦
        (strictSituation U).eq_zero_of_isCartesian_of_derivedComponentModuleRestriction_map_eq_zero
          (strictStructureSheaf U) _ _ (isCartesianDerivedModule_strictAugmentation a K)
          (fun i _ g ↦ strictComponent_shift_hom_eq_zero a ⦋i⦌ (i : ℤ)
            (hvan ⦋i⦌ (-(i : ℤ)) (by omega)) g)
          (fun i g ↦ strictComponent_shift_hom_eq_zero a ⦋i⦌ ((i : ℤ) + 1)
            (hvan ⦋i⦌ (-((i : ℤ) + 1)) (by omega)) g) f hf) _ _ ?_)
  refine (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
    (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0⦌)
    (strictComponentRingedToposHom U ⦋0⦌)).map_injective ?_
  simp only at hγ
  rw [derivedPullback_map_eq_strictComponent a ⦋0⦌ γ,
    derivedPullback_map_eq_strictComponent a ⦋0⦌ γ'] at hγ
  exact (cancel_mono _).1 ((cancel_epi _).1 hγ)

include h in
/-- **The image of `La_0^*` is the kernel of the difference of the face pullbacks** when the
pullbacks to every `U_n` have no negative Ext groups. -/
theorem exact_derivedPullback_map_augmentationFaceTransport
    {K E : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
      (HasDerivedCategory.standard _)}
    (hK : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) K)
    (hE : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) E)
    (hvan : ∀ (n : SimplexCategory) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback
          (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op n)))).obj K ⟶
        ((derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op n)))).obj E)⟦i⟧, g = 0) :
    Function.Exact (fun g : K ⟶ E ↦
        (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).map g)
      (fun ψ ↦ augmentationFaceTransport a 0 ψ - augmentationFaceTransport a 1 ψ) := by
  intro ψ
  constructor
  · intro hψ
    obtain ⟨γ', hγ'⟩ :=
      exists_derivedPullback_strictAugmentation_hom_of_augmentationFaceTransport_eq a hvan ψ
        (sub_eq_zero.mp hψ)
    obtain ⟨γ, hγ⟩ := (bijective_derivedPullback_strictAugmentationRingedToposHom_map h hK hE).2 γ'
    beta_reduce at hγ
    refine Set.mem_range.2 ⟨γ, ?_⟩
    exact (derivedPullback_map_eq_strictComponent a ⦋0⦌ γ).trans
      ((congrArg (fun x ↦ (strictAugmentationDegreeDerivedIso a ⦋0⦌).inv.app K ≫
        (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
          (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0⦌)
          (strictComponentRingedToposHom U ⦋0⦌)).map
          (((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) ⦋0⦌).map
            x) ≫
        (strictAugmentationDegreeDerivedIso a ⦋0⦌).hom.app E) hγ).trans hγ')
  · rintro ⟨γ, rfl⟩
    change augmentationFaceTransport a 0 _ - augmentationFaceTransport a 1 _ = 0
    rw [augmentationFaceTransport_derivedPullback_map,
      augmentationFaceTransport_derivedPullback_map, sub_self]

include h in
/-- Let `a : U → X` be an fppf hypercovering of an algebraic space and `K, E` objects of
`D_{QCoh}(𝒪_X)` with `Ext^i_{U_n}(La_n^*K, La_n^*E) = 0` for `i < 0` and all `n`. Then
(1) `Ext^i_X(K, E) = 0` for `i < 0`, and (2) the sequence
`0 ⟶ Hom_X(K, E) ⟶ Hom_{U_0}(La_0^*K, La_0^*E) ⟶ Hom_{U_1}(La_1^*K, La_1^*E)` is exact, where the
first map is `La_0^*` and the second the difference of the pullbacks along the two faces. -/
@[stacks 0DL9]
theorem negativeExt_eq_zero_and_exact_derivedPullback
    {K E : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
      (HasDerivedCategory.standard _)}
    (hK : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) K)
    (hE : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) E)
    (hvan : ∀ (n : SimplexCategory) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback
          (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op n)))).obj K ⟶
        ((derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op n)))).obj E)⟦i⟧, g = 0) :
    (∀ (i : ℤ), i < 0 → ∀ g : K ⟶ E⟦i⟧, g = 0) ∧
      Function.Injective (fun g : K ⟶ E ↦
        (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).map g) ∧
      Function.Exact (fun g : K ⟶ E ↦
        (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).map g)
        (fun ψ ↦ augmentationFaceTransport a 0 ψ - augmentationFaceTransport a 1 ψ) := by
  refine ⟨fun i hi g ↦ ?_, injective_derivedPullback_map_of_negativeExt h hK hE hvan,
    exact_derivedPullback_map_augmentationFaceTransport h hK hE hvan⟩
  let : HasDerivedCategory (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).Modules :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌))).Modules :=
    HasDerivedCategory.standard _
  have := derivedPullback_commShift
    (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
    (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
    (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))
  have z : ∀ x : K ⟶ E⟦i⟧,
      (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).map x = 0 := fun x ↦
    (cancel_mono (((derivedPullback
      (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
      (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
      (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).commShiftIso i).hom.app E)).1
      ((hvan ⦋0⦌ i hi _).trans zero_comp.symm)
  have hEi : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) (E⟦i⟧) := fun n ↦
    ObjectProperty.prop_of_iso _
      (((DerivedCategory.homologyFunctor _ 0).shiftIso i n (i + n) rfl).app E).symm (hE (i + n))
  refine injective_derivedPullback_map_of_negativeExt h hK hEi (fun n j hj g' ↦ ?_)
    ((z g).trans (z 0).symm)
  let : HasDerivedCategory
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n))).Modules :=
    HasDerivedCategory.standard _
  have := derivedPullback_commShift
    (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n)))
    (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
    (spacesEtaleRingedToposHom (a.app (op n)))
  let e := (shiftFunctor _ j).mapIso (((derivedPullback
      (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n)))
      (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
      (spacesEtaleRingedToposHom (a.app (op n)))).commShiftIso i).app E) ≪≫
    (shiftFunctorAdd' _ i j (i + j) rfl).symm.app _
  exact (cancel_mono e.hom).1 ((hvan n (i + j) (by lia) _).trans zero_comp.symm)

end HomDescent

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
