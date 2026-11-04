module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.RightAdjointCoproducts
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtKInjective
public import
  StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithfulDerivedHom

/-!
# When the endomorphism algebra of a complex computes its ext groups

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)`. Hypothesis (2) of [Stacks, Tag 09LZ] asks that `E` compute
the ext groups of `K`, that is `H^n(E) = Ext^n_{D(O)}(K, K)` for every `n`. Since
`H^n(E) = Hom_{K(O)}(K, K[n])`, this is the bijectivity of the localization functor
`K(O) ⥤ D(O)` on the morphism groups `Hom_{K(O)}(K[k], K)`, and this file proves that this
bijectivity indeed gives hypothesis (2) in the form used by Tag 09LZ, the bijectivity of
`- ⊗_E^𝐋 K` on `Hom_{D(E, d)}(E, E[n])`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedHomWithComplexUnit_app_self_of_bijective`: the
  comparison `Hom^•(K, -) → RHom(K, -)` is invertible at `K`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_bijective_map_regular_of_bijective`:
  hypothesis (2) of Tag 09LZ.

## Implementation notes

Choose a K-injective resolution `s : K → I`. The comparison is invertible at `I`, so by
naturality it is invertible at `K` as soon as `Hom^•(K, s)` becomes invertible in `D(E, d)`. The
regular module weakly generates `D(E, d)`, so it suffices that `Hom^•(K, s)` be bijective on
morphisms out of the shifts `E[k]`; these are orthogonal on the left to the acyclic modules, so
the morphisms may be computed in `K(Mod_(E, d))`, where the adjunction `- ⊗_E K ⊣ Hom^•(K, -)`
and `E[k] ⊗_E K = K[k]` turn the question into the bijectivity of composition with `s` on
`Hom_{K(O)}(K[k], K)`. Since `I` is K-injective and `s` is a quasi-isomorphism, that is the
bijectivity of the localization functor on `Hom_{K(O)}(K[k], K)`.

## References

* [Stacks Project, Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DifferentialGradedModule

universe u v w t s

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-- Bijectivity of postcomposition with a fixed morphism does not depend on the source up to
isomorphism. -/
theorem bijective_comp_of_iso_left {C : Type*} [Category C] {A B S T : C} (e : A ≅ B)
    (f : S ⟶ T) (h : Function.Bijective (fun g : B ⟶ S => g ≫ f)) :
    Function.Bijective (fun g : A ⟶ S => g ≫ f) := by
  have heq : (fun g : A ⟶ S => g ≫ f) =
      (fun g : B ⟶ T => e.hom ≫ g) ∘ (fun g : B ⟶ S => g ≫ f) ∘ (fun g : A ⟶ S => e.inv ≫ g) := by
    funext g; simp
  rw [heq]
  exact e.symm.homFromEquiv.bijective.comp (h.comp e.homFromEquiv.bijective)

/-- If a functor is bijective on morphisms out of `A` into `S` and `T`, then postcomposition with
`f : S ⟶ T` is bijective on `Hom(A, S)` iff postcomposition with `F.map f` is bijective. -/
private theorem bijective_comp_iff_of_bijective_map {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A S T : C} (f : S ⟶ T) (hS : Function.Bijective (F.map : (A ⟶ S) → _))
    (hT : Function.Bijective (F.map : (A ⟶ T) → _)) :
    Function.Bijective (fun g : A ⟶ S => g ≫ f) ↔
      Function.Bijective (fun g : F.obj A ⟶ F.obj S => g ≫ F.map f) := by
  have h : F.map ∘ (fun g : A ⟶ S => g ≫ f) =
      (fun g : F.obj A ⟶ F.obj S => g ≫ F.map f) ∘ F.map := by
    funext g; simp
  rw [← hT.of_comp_iff', h, Function.Bijective.of_comp_iff _ hS]

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-- **The comparison `Hom^•(K, -) → RHom(K, -)` is invertible at `K`** as soon as the localization
functor `K(O) ⥤ D(O)` is bijective on the morphism groups `Hom_{K(O)}(K[k], K)`. -/
theorem isIso_derivedHomWithComplexUnit_app_self_of_bijective
    (hQ : ∀ k : ℤ, Function.Bijective (DerivedCategory.Qh.map :
      (((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))⟦k⟧ ⟶
        (HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K)) → _)) :
    IsIso ((derivedHomWithComplexUnit.{u, v, w, t, s} X K).app
      ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))) := by
  set Kh := (HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)).obj
    (liftComplex.{u, v, w, t, s} X K)
  let E := (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
  let adjH := tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K
  let FH := tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K
  let GH := homWithComplexHomotopy.{u, v, w, t, s} X K
  let QE := (quasiIsomorphisms E).Q
  obtain ⟨I, sI, hsI, hI⟩ := exists_coresolution_map_bijective_sheaf.{u, v, w, t, s} X Kh
  have hβI := isIso_derivedHomWithComplexUnit_app_of_bijective.{u, v, w, t, s} X K I hI
  have hQs : IsIso (DerivedCategory.Qh.map sI) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) _ hsI
  -- the regular module and its image under tensoring
  let R' := (toHomotopyCategory E).obj (regularModule E)
  have hc := isIso_tensorWithComplexHomotopy_adj_counit_app.{u, v, w, t, s} X K
  let eR : R' ≅ GH.obj Kh :=
    (toHomotopyCategory E).mapIso DGCategory.representableSelfIsoRegular.symm
  let eF : FH.obj R' ≅ Kh := FH.mapIso eR ≪≫ asIso (adjH.counit.app Kh)
  -- the key bijectivity in `K(O)`
  have hcomp : ∀ k : ℤ, Function.Bijective (fun g : Kh⟦k⟧ ⟶ Kh => g ≫ sI) := by
    intro k
    exact (bijective_comp_iff_of_bijective_map DerivedCategory.Qh sI (hQ k) (hI _)).2
      (asIso (DerivedCategory.Qh.map sI)).homToEquiv.bijective
  -- bijectivity on morphisms out of the shifts of the regular module in `K(Mod_(E, d))`
  have hK : ∀ k : ℤ, Function.Bijective (fun g : R'⟦k⟧ ⟶ GH.obj Kh => g ≫ GH.map sI) := by
    intro k
    have hnat : (fun g : R'⟦k⟧ ⟶ GH.obj Kh => g ≫ GH.map sI) =
        (adjH.homEquiv _ _) ∘ (fun g => g ≫ sI) ∘ (adjH.homEquiv _ _).symm := by
      funext g
      rw [Function.comp_apply, Function.comp_apply, Adjunction.homEquiv_naturality_right,
        Equiv.apply_symm_apply]
    rw [hnat]
    refine (adjH.homEquiv _ _).bijective.comp ((?_ : Function.Bijective _).comp
      (adjH.homEquiv _ _).symm.bijective)
    exact bijective_comp_of_iso_left
      ((FH.commShiftIso k).app R' ≪≫ (CategoryTheory.shiftFunctor _ k).mapIso eF) sI (hcomp k)
  -- bijectivity on morphisms out of the shifts of the regular module in `D(E, d)`
  have hD : IsIso (QE.map (GH.map sI)) := by
    refine CategoryTheory.Pretriangulated.isIso_of_generator_hom_bijective
      (repRegularDerived.{u, v, w, t, s} X K)
      (Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule
        E) _ ?_
    rintro O ⟨O', k, e, hO'⟩
    rw [ObjectProperty.singleton_iff] at hO'
    subst hO'
    refine bijective_comp_of_iso_left (e ≪≫ (QE.commShiftIso k).symm.app R') _ ?_
    have hL : (acyclic E).leftOrthogonal (R'⟦k⟧) :=
      (acyclic E).leftOrthogonal.le_shift k _ (leftOrthogonal_acyclic_regularModule E)
    have hbij := fun Y => bijective_q_map_of_leftOrthogonal_rep.{u, v, w, t, s, 0} X ℤ K hL Y
    exact (bijective_comp_iff_of_bijective_map QE (GH.map sI) (hbij _) (hbij _)).1 (hK k)
  -- naturality of the comparison along the resolution
  have : IsIso ((homWithComplexToDerivedCategory.{u, v, w, t, s} X K).map sI ≫
      (derivedHomWithComplexUnit.{u, v, w, t, s} X K).app I) := by
    have : IsIso ((homWithComplexToDerivedCategory.{u, v, w, t, s} X K).map sI) := hD
    infer_instance
  rw [(derivedHomWithComplexUnit.{u, v, w, t, s} X K).naturality sI] at this
  have : IsIso ((DerivedCategory.Qh ⋙ derivedHomWithComplex.{u, v, w, t, s} X K).map sI) :=
    (derivedHomWithComplex.{u, v, w, t, s} X K).map_isIso (DerivedCategory.Qh.map sI)
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.Qh ⋙ derivedHomWithComplex.{u, v, w, t, s} X K).map sI)

/-- **Hypothesis (2) of Tag 09LZ.** If the localization functor `K(O) ⥤ D(O)` is bijective on the
morphism groups `Hom_{K(O)}(K[k], K)` — that is, `H^n(E) = Ext^n_{D(O)}(K, K)` for every `n` —
then `- ⊗_E^𝐋 K` is bijective on `Hom_{D(E, d)}(E, E[n])` for every `n`. -/
theorem tensorWithComplexDerived_bijective_map_regular_of_bijective
    (hQ : ∀ k : ℤ, Function.Bijective (DerivedCategory.Qh.map :
      (((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))⟦k⟧ ⟶
        (HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K)) → _))
    (n : ℤ) :
    Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶ (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).map f) :=
  tensorWithComplexDerived_bijective_map_regular_of_isIso.{u, v, w, t, s} X K
    (isIso_derivedHomWithComplexUnit_app_self_of_bijective.{u, v, w, t, s} X K hQ) n

end AlgebraicGeometry.RingedSite

end
