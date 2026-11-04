module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemCounit
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionAugmentation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedModuleLift
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionAugmentationTower

/-!
# The degree-zero lift of Stacks 0D9S

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site with flat structure-sheaf transitions, let `K`, `K'` be objects of `D(O)` with `K`
cartesian and `Hom(K_i[i - 1], K'_i) = 0` for `i > 1`, and let `f` be a morphism of the
associated simplicial systems. The proof of Stacks 0D9S — "exactly the same as the proof of
Lemma 0D9K except using Lemma 0D9Q instead of Lemma 0D9I" — has two halves; the second, that a
morphism out of a cartesian system is determined by its degree-zero component, is
`CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.Hom.app_eq_of_cartesian`.
**This file proves the first**: there is a morphism `γ : K ⟶ K'` with `Lg_0^*γ = f_0`.

The argument runs through the Postnikov system of Stacks 0D9Q for `T = - ⊗^L_O K` and a
resolution `L = (… → g_{1!}O_1 → g_{0!}O_0)` of the structure sheaf (Stacks 0D9B) whose
augmentation `ε : g_{0!}O_0 ⟶ O` is the counit of `g_{0!} ⊣ g_0^*`
(`CategoryTheory.SimplicialSiteSituation`
`.exists_simplicialModuleResolutionActual_homEquiv_augmentation`).
Its coprojections are recorded explicitly: the `n`-th is `T` of the inclusion of the `n`-th
brutal truncation of `L`, followed by `T(L) ≅ T(O) ≅ K`, and in degree zero it is the bottom of
the Postnikov tower followed by `h = (ε ⊗^L_O K) ≫ (O ⊗^L_O K ≅ K)`
(`moduleResolutionTensorCoprojection_zero`).

Write `p : g_{0!}K_0 ⟶ X₀ = g_{0!}O_0 ⊗^L_O K` for the projection map of Stacks 0D9E (2), which is
invertible since `K` is cartesian, and `θ = (p ≫ h)^♯ : K_0 ⟶ K_0` for the transpose of `p ≫ h`;
`θ` is an isomorphism by
`CategoryTheory.SimplicialSiteSituation.isIso_homEquiv_moduleProjection_comp_augmentation`. The
map `X₀ ⟶ K'` fed to the tower argument is

`b = p⁻¹ ≫ (θ ≫ f_0)^♭`.

* **The first omitted computation**, that `X₁ ⟶ X₀ ⟶ K'` vanishes, is
  `termDiff_comp_degreeZeroLift_eq_zero`. Restricted to degree one, `b` is
  `Lg_1^*(h) ≫ f_1`: this is
  `CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction_map_homEquiv_symm`,
  that the transpose of a component of a morphism of systems factors through the counit after
  restriction. Since the differential `X₁ ⟶ X₀` followed by `h` vanishes (it is `T` of the
  differential of `L` followed by the augmentation), so does its composite with `b` after
  restriction to degree one, and that restriction transposes back to the composite itself
  through the invertible projection map in degree one.
* **The second omitted computation**, the identification of the degree-zero coprojection with the
  counit up to `θ`, is how the conclusion `c_0 ≫ γ = (bottom) ≫ b` of the tower argument is read:
  cancelling the invertible bottom gives `h ≫ γ = b`, whose transpose along `Lg_{0!} ⊣ Lg_0^*`
  after precomposition with `p` is `θ ≫ Lg_0^*γ = θ ≫ f_0`, and `θ` cancels.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleResolutionAugmentation_f_zero`: in degree zero the
  augmentation of the cochain complex of the resolution is the augmentation of the resolution.
* `CategoryTheory.SimplicialSiteSituation.isHomotopyColimitWith_moduleResolutionTensorSystem`:
  Stacks 0D9Q (2), `K = hocolim Yₙ[n]`, with the coprojections recorded.
* `CategoryTheory.SimplicialSiteSituation.moduleResolutionTensorCoprojection_zero`: the bottom
  coprojection is the bottom of the Postnikov tower followed by the augmentation.
* `CategoryTheory.SimplicialSiteSituation.exists_hom_derivedComponentModuleRestriction_zero_eq`:
  **the first half of Stacks 0D9S**.

## References

* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0D9Q](https://stacks.math.columbia.edu/tag/0D9Q)
* [Stacks Project, Tag 0D9S](https://stacks.math.columbia.edu/tag/0D9S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StacksDraft.BrutalPostnikov
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-! ### The augmentation of the cochain complex of the resolution in degree zero -/

section Complex

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}
  (D : SimplicialModuleResolutionActual S O)

/-- **In degree zero the augmentation of the cochain complex of the resolution of Stacks 0D9B is
the augmentation of the resolution**, read through the identification of the degree-zero term of
the extended complex with the degree-zero term of the resolution. -/
theorem moduleResolutionAugmentation_f_zero :
    (moduleResolutionAugmentation D).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (SheafOfModules.unit O)).hom =
      (D.complex.extendXIso (ComplexShape.embeddingUpIntLE 0) (i := 0) (by simp)).hom ≫
        D.augmentation :=
  ChainComplex.extendMap_toSingle₀Equiv_symm_f D.augmentation D.augmentation_comp
    (ComplexShape.embeddingUpIntLE 0) (by simp)

/-- The augmentation `g_{0!}O_0 ⟶ O` of the resolution, with its source written as the lower
shriek image of the structure sheaf of the component. -/
abbrev moduleResolutionLowerShriekAugmentation :
    (componentModuleLowerShriek S O ⦋0⦌).obj (SheafOfModules.unit (componentRingSheaf S O ⦋0⦌)) ⟶
      SheafOfModules.unit O :=
  eqToHom (D.lowerShriekDegreeEq 0).symm ≫ D.augmentation

/-- In degree zero, the identification of the term of the cochain complex of the resolution with
`g_{0!}O_0`, followed by the augmentation, is the augmentation of the cochain complex. -/
theorem moduleResolutionComplexXIso_hom_comp_augmentation :
    (moduleResolutionComplexXIso D 0).hom ≫ moduleResolutionLowerShriekAugmentation D =
      (moduleResolutionAugmentation D).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (SheafOfModules.unit O)).hom := by
  rw [moduleResolutionAugmentation_f_zero]
  show ((D.complex.extendXIso (ComplexShape.embeddingUpIntLE 0) (i := 0) (by simp)).hom ≫
      eqToHom (D.lowerShriekDegreeEq 0)) ≫ eqToHom (D.lowerShriekDegreeEq 0).symm ≫
        D.augmentation = _
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The differential of the cochain complex of the resolution into degree zero, followed by the
identification of the degree-zero term with `g_{0!}O_0` and the augmentation, vanishes. -/
theorem moduleResolution_d_comp_augmentation :
    (moduleResolutionComplex D).d (-(((0 : ℕ) : ℤ) + 1)) (-((0 : ℕ) : ℤ)) ≫
        (moduleResolutionComplexXIso D 0).hom ≫ moduleResolutionLowerShriekAugmentation D = 0 := by
  rw [moduleResolutionComplexXIso_hom_comp_augmentation, ← Category.assoc]
  show ((moduleResolutionComplex D).d (-(((0 : ℕ) : ℤ) + 1)) 0 ≫
    (moduleResolutionAugmentation D).f 0) ≫ _ = 0
  rw [← (moduleResolutionAugmentation D).comm]
  simp

end Complex

/-! ### The derived colimit with its coprojections -/

attribute [local instance] HasDerivedCategory.standard hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The augmentation of the resolution tensored with `K` and followed by the unit constraint:
the map `X₀ = g_{0!}O_0 ⊗^L_O K ⟶ K` through which the bottom coprojection of the derived colimit
of Stacks 0D9Q factors. -/
abbrev moduleResolutionTensorAugmentation
    (D : SimplicialModuleResolutionActual S
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    S.componentModuleLowerShriekDerivedTensorTerm O K 0 ⟶ K :=
  ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.map
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
          (moduleResolutionLowerShriekAugmentation D))).app K ≫
    (derivedTensorRightUnitIso O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O)
      K).hom

/-- **Stacks 0D9Q (2) with the coprojections recorded.** `K` is the derived colimit of the
system `Yₙ[n] = (g_{n!}O_n → … → g_{0!}O_0) ⊗^L_O K`, the `n`-th coprojection being `- ⊗^L_O K`
of the inclusion of the `n`-th brutal truncation of the resolution, followed by the
identification of the resolution with `O` and by the unit constraint `O ⊗^L_O K ≅ K`. -/
theorem isHomotopyColimitWith_moduleResolutionTensorSystem
    (D : SimplicialModuleResolutionActual S
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    IsHomotopyColimitWith (mapTruncTowerSystem (moduleResolutionComplex D)
        (S.moduleResolutionTensorFunctor O K)) K
      (fun n => (S.moduleResolutionTensorFunctor O K).map
          (DerivedCategory.Q.map (HomologicalComplex.ιStupidTrunc (moduleResolutionComplex D)
            (ComplexShape.embeddingUpIntGE (-(n : ℤ))))) ≫
        (S.moduleResolutionTensorFunctor O K).map (moduleResolutionDerivedIso D).hom ≫
          (derivedTensorRightUnitIso O
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K).hom) := by
  let : (S.moduleResolutionTensorFunctor O K).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).commShift_left K
  let : (S.moduleResolutionTensorFunctor O K).IsTriangulated :=
    isTriangulated_derivedTensorRight O
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K
  let := preservesColimitsOfShape_nat_derivedTensorRight O
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K
  exact ((isHomotopyColimitWith_truncTower (moduleResolutionComplex D)).map
    (S.moduleResolutionTensorFunctor O K)).of_iso
      ((S.moduleResolutionTensorFunctor O K).mapIso (moduleResolutionDerivedIso D) ≪≫
        derivedTensorRightUnitIso O
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K)

/-- A functor applied to an identity `x ≫ y = a ≫ b ≫ c ≫ d`, followed by a further map, split
into its factors. -/
private theorem map_comp_assemble {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B E P Q R : C} {Z : D} {x : A ⟶ B} {y : B ⟶ E} {a : A ⟶ P} {b : P ⟶ Q} {c : Q ⟶ R}
    {d : R ⟶ E} (h : x ≫ y = a ≫ b ≫ c ≫ d) (z : G.obj E ⟶ Z) :
    G.map x ≫ G.map y ≫ z = G.map a ≫ G.map b ≫ G.map c ≫ G.map d ≫ z := by
  rw [← Category.assoc, ← G.map_comp, h]
  simp only [G.map_comp, Category.assoc]

/-- **The bottom coprojection of the derived colimit of Stacks 0D9Q is the bottom of the
Postnikov tower followed by the augmentation.** The inclusion of the bottom brutal truncation of
the resolution, followed by its identification with `O`, is the projection of the truncation onto
its bottom term `g_{0!}O_0` followed by the augmentation
(`StacksDraft.BrutalPostnikov.Q_ιStupidTrunc_comp_eq`); tensoring with `K` gives the claim. -/
theorem moduleResolutionTensorCoprojection_zero
    (D : SimplicialModuleResolutionActual S
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    (S.moduleResolutionTensorFunctor O K).map
          (DerivedCategory.Q.map (HomologicalComplex.ιStupidTrunc (moduleResolutionComplex D)
            (ComplexShape.embeddingUpIntGE (-((0 : ℕ) : ℤ))))) ≫
        (S.moduleResolutionTensorFunctor O K).map (moduleResolutionDerivedIso D).hom ≫
          (derivedTensorRightUnitIso O
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K).hom =
      (S.moduleResolutionTensorFunctor O K).map (totAtTowerIso (moduleResolutionComplex D)
          (-((1 : ℕ) : ℤ)) (by simp)).inv ≫
        (S.moduleResolutionTensorFunctor O K).map (moduleResolutionTotProj D 0) ≫
          (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫
            S.moduleResolutionTensorAugmentation O D K := by
  have hε : (moduleResolutionTermIso D 0).hom ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
          (moduleResolutionLowerShriekAugmentation D) =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
          ((moduleResolutionAugmentation D).f 0 ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))).hom) :=
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map_comp _
          _).symm.trans
      (congrArg (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
        (moduleResolutionComplexXIso_hom_comp_augmentation D))
  have h := Q_ιStupidTrunc_comp_eq (moduleResolutionComplex D)
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    (moduleResolutionAugmentation D) _ rfl _ hε
  exact map_comp_assemble (S.moduleResolutionTensorFunctor O K) h
    (derivedTensorRightUnitIso O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O)
      K).hom

/-- A functor preserving zero morphisms, applied to a vanishing threefold composite, followed by
a further map. -/
private theorem map_comp_comp_comp_eq_zero {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive] {A B E F : C} {Z : D}
    {a : A ⟶ B} {b : B ⟶ E} {c : E ⟶ F} (h : a ≫ b ≫ c = 0) (z : G.obj F ⟶ Z) :
    G.map a ≫ G.map b ≫ G.map c ≫ z = 0 := by
  rw [← Category.assoc, ← Category.assoc, ← G.map_comp, ← G.map_comp, Category.assoc, h,
    G.map_zero, zero_comp]

/-- **The differential `X₁ ⟶ X₀` of the Postnikov system of Stacks 0D9Q, followed by the
augmentation, vanishes**: it is `- ⊗^L_O K` of the differential of the resolution into degree
zero followed by the augmentation, which is zero. -/
theorem termDiff_comp_moduleResolutionTensorAugmentation
    (D : SimplicialModuleResolutionActual S
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    (S.moduleResolutionTensorFunctor O K).map (moduleResolutionTermDiff D 0) ≫
        (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫
          S.moduleResolutionTensorAugmentation O D K =
      (0 : (show DerivedCategory (S.totalRingedTopos O).Modules from
        (S.moduleResolutionTensorFunctor O K).obj (moduleResolutionTerm D 1)) ⟶ K) := by
  have h0 : moduleResolutionTermDiff D 0 ≫ (moduleResolutionTermIso D 0).hom ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
          (moduleResolutionLowerShriekAugmentation D) = 0 := by
    have h := congrArg (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
        (moduleResolution_d_comp_augmentation D)
    rwa [Functor.map_comp, Functor.map_comp, Functor.map_zero] at h
  let : (S.moduleResolutionTensorFunctor O K).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).commShift_left K
  let : (S.moduleResolutionTensorFunctor O K).IsTriangulated :=
    isTriangulated_derivedTensorRight O
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K
  exact map_comp_comp_comp_eq_zero (S.moduleResolutionTensorFunctor O K) h0 _

end CategoryTheory.SimplicialSiteSituation

end
