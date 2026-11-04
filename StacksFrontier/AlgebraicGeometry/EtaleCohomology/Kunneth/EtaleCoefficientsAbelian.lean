module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPushforwardDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.CategoryTheory.Sites.Modules.AbelianSheavesAsConstantModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusExactSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of `Λ̲`-modules on `X_étale` and abelian sheaves

Let `X` be a scheme and `Λ` a commutative ring. The derived categories `D(X_étale, Λ)` of
`Stacks.EtaleCohomology.EtaleCoefficients` are built from sheaves of modules over the constant
sheaf of rings `Λ̲` on the small model of `X_étale`, while the base change and smooth base change
theorems of the étale cohomology chapter are stated for abelian sheaves on `X.smallEtaleTopology`,
on `D⁺`, with the derived functors `rightDerivedFunctorPlus` of
`Stacks.EtaleCohomology.smallEtalePushforwardAb` and `Stacks.EtaleCohomology.smallEtalePullbackAb`.
This file compares the two at the level of sheaves and of direct images.

* **Forgetting the module structure.** The underlying abelian sheaf on `X.smallEtaleTopology`,
  `Stacks.EtaleCohomology.EtaleCoefficients.etaleToSheaf`, is exact and faithful, and it commutes
  with direct images (`pushforwardEtaleToSheafIso`).
* **`ℤ/mℤ`-coefficients.** For `Λ = ℤ/mℤ` it is fully faithful, with essential image the abelian
  sheaves annihilated by `m` (`etaleToSheafZModFullyFaithful`, `mem_essImage_etaleToSheaf_iff`);
  for `m = 0`, i.e. `Λ = ℤ`, it is an equivalence: **abelian sheaves on `X_étale` are the
  sheaves of `ℤ̲`-modules on the model** (`abelianSheafEquivalence`).
* **Derived direct images.** The underlying abelian sheaf of an injective sheaf of `Λ̲`-modules is
  acyclic for the abelian direct image, so forgetting the module structure commutes with derived
  direct images on bounded below objects: for `K ∈ D⁺(X_étale, Λ)`, the underlying complex of
  abelian sheaves of `Rf_*K` is `Rf_*` of the underlying complex of `K`
  (`pushforwardForgetPlusIso`, read through the unbounded derived direct image `pushforward` of
  `D(X_étale, Λ)`).

## Main definitions

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `pushforwardEtaleToSheafIso` — `f_*` commutes with the underlying abelian sheaf.
* `forgetDerived`, `forgetDerivedPlus` — the underlying complex of abelian sheaves, on `D` and
  on `D⁺`.
* `pushforwardPlusForgetIso` — `R⁺f_*` (modules) then forget `≅` forget then `R⁺f_*` (abelian).
* `pushforwardForgetPlusIso` — the same with the unbounded `pushforward` of `D(X_étale, Λ)`.
* `etaleToSheafZModFullyFaithful`, `abelianSheafEquivalence`,
  `abelianSheafDerivedEquivalence` — the `ℤ/mℤ` and `ℤ` cases.

## Implementation notes

The derived direct image `pushforward` of `D(X_étale, Λ)` and
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` on the abelian side are both formed in the
standard model `HasDerivedCategory.standard` of the derived category, which is therefore the model
used in the derived sections.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.ProjectionFormulaConstant (etaleRing siteSheafEquiv)
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The underlying abelian sheaf -/

section Forget

variable (X : Scheme.{u})

/-- The underlying abelian sheaf functor on sheaves of `Λ̲`-modules is additive. -/
instance etaleToSheaf_additive : (etaleToSheaf Λ X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The underlying abelian sheaf functor preserves finite limits. -/
instance etaleToSheaf_preservesFiniteLimits : PreservesFiniteLimits (etaleToSheaf Λ X) :=
  comp_preservesFiniteLimits _ _

/-- The underlying abelian sheaf functor preserves finite colimits. -/
instance etaleToSheaf_preservesFiniteColimits : PreservesFiniteColimits (etaleToSheaf Λ X) :=
  comp_preservesFiniteColimits _ _

/-- The underlying abelian sheaf functor is faithful. -/
instance etaleToSheaf_faithful : (etaleToSheaf Λ X).Faithful :=
  Functor.Faithful.comp _ _

/-- The underlying abelian sheaf functor reflects isomorphisms. -/
instance etaleToSheaf_reflectsIsomorphisms : (etaleToSheaf Λ X).ReflectsIsomorphisms :=
  inferInstance

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The underlying abelian sheaf of a direct image is the direct image of the underlying
abelian sheaf**: the direct image of sheaves of `Λ̲`-modules is restriction along base change on
the small models, and so is the abelian direct image, read through the comparison of the small
models with the small étale sites. -/
def pushforwardEtaleToSheafIso :
    (ringedToposHom Λ f).pushforwardTopos ⋙ etaleToSheaf Λ Y ≅
      etaleToSheaf Λ X ⋙ smallEtalePushforwardAb f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pushforwardToposToSheafIso Λ f) (siteSheafEquiv Y).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X))
      (siteAbelianDirectImageIso f) ≪≫
    (Functor.associator _ _ _).symm

end Forget


/-! ### Derived direct images on bounded below objects -/

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The underlying abelian sheaf of an injective sheaf of `Λ̲`-modules is acyclic for the
direct image of abelian sheaves on the small étale sites** (the acyclicity behind
[Stacks, Tag 03FD]): its higher direct images are those of the injective sheaf of modules. -/
@[sga "4 XVII 4.1.2" "special case"]
theorem rightAcyclic_smallEtalePushforwardAb_etaleToSheaf
    (I : SheafOfModules.{u + 1} (etaleRing Λ X)) (hI : Injective I) :
    (smallEtalePushforwardAb f).rightAcyclic ((etaleToSheaf Λ X).obj I) := by
  have := (smallEtaleAdjunctionAb f).rightAdjoint_preservesLimits
  refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2 ?_
  intro p hp
  refine IsZero.of_iso ?_ ((rightDerivedPushforwardToposIso Λ f p).app I).symm
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact (etaleToSheaf Λ Y).map_isZero (Functor.isZero_rightDerived_obj_injective_succ _ _ _)


variable (X) in
/-- **The underlying complex of abelian sheaves** of an object of `D(X_étale, Λ)`: the exact
functor `etaleToSheaf` applied degreewise. -/
abbrev forgetDerived :
    DerivedModules Λ X ⥤ DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (etaleToSheaf Λ X).mapDerivedCategory

variable (X) in
/-- The underlying complex of abelian sheaves, on bounded below objects. -/
abbrev forgetDerivedPlus :
    DerivedCategory.Plus (SheafOfModules.{u + 1} (etaleRing Λ X)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (etaleToSheaf Λ X).mapDerivedCategoryPlus

/-- **Forgetting the module structure commutes with derived direct images on `D⁺`**:
`R⁺f_*` of sheaves of `Λ̲`-modules followed by the underlying complex of abelian sheaves is the
underlying complex followed by `R⁺f_*` of abelian sheaves on the small étale sites. The
underlying abelian sheaf of an injective sheaf of modules is acyclic for the abelian direct
image (`rightAcyclic_smallEtalePushforwardAb_etaleToSheaf`), so
`CategoryTheory.Functor.rightDerivedFunctorPlusExactSquareIso` applies. -/
def pushforwardPlusForgetIso :
    (ringedToposHom Λ f).pushforwardTopos.rightDerivedFunctorPlus ⋙ forgetDerivedPlus Λ Y ≅
      forgetDerivedPlus Λ X ⋙ (smallEtalePushforwardAb f).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusExactSquareIso (pushforwardEtaleToSheafIso Λ f)
    (rightAcyclic_smallEtalePushforwardAb_etaleToSheaf Λ f)

/-- **For `K ∈ D⁺(X_étale, Λ)`, the underlying complex of abelian sheaves of `Rf_*K` is `R⁺f_*`
of the underlying complex of `K`**, with `Rf_*` the unbounded derived direct image `pushforward`
of `D(X_étale, Λ)`: on bounded below objects `pushforward` is the bounded below right derived
functor (`CategoryTheory.Functor.boundedDerivedIso`, K-injective resolutions existing on the
Grothendieck abelian category of sheaves of modules), and `pushforwardPlusForgetIso`. -/
def pushforwardForgetPlusIso :
    DerivedCategory.Plus.ι ⋙ pushforward Λ f ⋙ forgetDerived Λ Y ≅
      forgetDerivedPlus Λ X ⋙ (smallEtalePushforwardAb f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.boundedDerivedIso (ringedToposHom Λ f).pushforwardTopos (pushforward Λ f)
        (derivedPushforwardUnit (ringedToposHom Λ f))
        (exists_quasiIso_isKInjective (ringedTopos Λ X))).symm
      (forgetDerived Λ Y) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Iso.refl (DerivedCategory.Plus.ι ⋙ forgetDerived Λ Y)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pushforwardPlusForgetIso Λ f) DerivedCategory.Plus.ι ≪≫
    Functor.associator _ _ _

variable (X) in
/-- **The underlying complex of abelian sheaves detects isomorphisms in `D(X_étale, Λ)`**: an
isomorphism is detected on cohomology sheaves, the underlying abelian sheaf commutes with
cohomology, and it reflects isomorphisms of sheaves. -/
theorem isIso_iff_isIso_forgetDerived_map {K L : DerivedModules Λ X} (φ : K ⟶ L) :
    IsIso φ ↔ IsIso ((forgetDerived Λ X).map φ) := by
  refine ⟨fun _ => inferInstance, fun h => ?_⟩
  rw [DerivedCategory.isIso_iff] at h ⊢
  intro n
  have : IsIso ((etaleToSheaf Λ X).map ((DerivedCategory.homologyFunctor _ n).map φ)) := by
    rw [StacksDraft.DerivedCategoryHomology.map_homologyFunctor_map]
    have := h n
    infer_instance
  exact isIso_of_reflects_iso _ (etaleToSheaf Λ X)

end Derived

/-! ### `ℤ/mℤ`-coefficients -/

section ZMod

variable (m : ℕ) (X : Scheme.{u})

/-- **The structure sheaf of `(X_étale, ℤ/mℤ)` is the constant sheaf of rings `ℤ/mℤ`** of
`Stacks.Cohomology.ZModSheaf`, on the small model of `X_étale`. -/
theorem etaleRing_uliftZMod :
    etaleRing (ULift.{u + 1} (ZMod m)) X =
      Stacks.Cohomology.ZModSheaf.zmodRingSheaf.{u + 1} (topology X) m :=
  rfl

/-- **For `ℤ/mℤ`-coefficients the underlying abelian sheaf is fully faithful**: an additive map
of sheaves of `ℤ/mℤ̲`-modules is linear ([Stacks, Tag 0DD8] on the small model), and the small
model has the abelian sheaves of the small étale site. -/
def etaleToSheafZModFullyFaithful :
    (etaleToSheaf (ULift.{u + 1} (ZMod m)) X).FullyFaithful :=
  (Stacks.Cohomology.ZModSheaf.toSheafFullyFaithful.{u + 1, u + 1} (topology X) m).comp
    (siteSheafEquiv X).fullyFaithfulFunctor

/-- For `ℤ/mℤ`-coefficients the underlying abelian sheaf functor is full. -/
instance etaleToSheaf_zmod_full : (etaleToSheaf (ULift.{u + 1} (ZMod m)) X).Full :=
  (etaleToSheafZModFullyFaithful m X).full

/-- An abelian sheaf is annihilated by `m` as an object exactly when all its sections are. -/
theorem nsmul_id_eq_zero_iff {C : Type*} [Category* C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{u + 1}) :
    m • 𝟙 F = 0 ↔ ∀ (U : Cᵒᵖ) (x : ToType (F.obj.obj U)), m • x = 0 := by
  have h (U : Cᵒᵖ) (x : ToType (F.obj.obj U)) : ((m • 𝟙 F).hom.app U).hom x = m • x := by
    have h₁ : (sheafToPresheaf J AddCommGrpCat.{u + 1}).map (m • 𝟙 F) =
        m • (sheafToPresheaf J AddCommGrpCat.{u + 1}).map (𝟙 F) := Functor.map_nsmul _
    simpa using congrArg (fun φ : F.obj ⟶ F.obj => (φ.app U).hom x) h₁
  refine ⟨fun h' U x => ?_, fun h' => ?_⟩
  · rw [← h, h']
    rfl
  · ext U x
    exact (h U x).trans (h' U x)

/-- Annihilation by `m` is preserved by additive functors. -/
theorem nsmul_id_map_eq_zero {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (G : C ⥤ D) [G.Additive] {A : C} (h : m • 𝟙 A = 0) :
    m • 𝟙 (G.obj A) = 0 := by
  have := congrArg G.map h
  rwa [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at this

/-- Annihilation by `m` is invariant under isomorphism. -/
theorem nsmul_id_eq_zero_of_iso {D : Type*} [Category* D] [Preadditive D] {A B : D} (e : A ≅ B)
    (h : m • 𝟙 A = 0) : m • 𝟙 B = 0 :=
  calc m • 𝟙 B = e.inv ≫ (m • 𝟙 A) ≫ e.hom := by simp
    _ = 0 := by rw [h]; simp

/-- **The abelian sheaves underlying sheaves of `ℤ/mℤ̲`-modules are exactly those annihilated by
`m`.** One direction is that `m = 0` in `ℤ/mℤ̲`; for the other, an abelian sheaf annihilated by
`m` restricts to one on the small model, which is the underlying abelian sheaf of its sectionwise
`ℤ/mℤ`-module structure, sheafified (`Stacks.Cohomology.ZModSheaf.torsionSheafToModules`). -/
theorem mem_essImage_etaleToSheaf_iff (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleToSheaf (ULift.{u + 1} (ZMod m)) X).essImage F ↔ m • 𝟙 F = 0 := by
  refine ⟨fun ⟨M, ⟨e⟩⟩ => ?_, fun h => ?_⟩
  · have hM : m • 𝟙 ((SheafOfModules.toSheaf.{u + 1}
        (etaleRing (ULift.{u + 1} (ZMod m)) X)).obj M) = 0 :=
      (nsmul_id_eq_zero_iff m _).2 fun U x =>
        Stacks.Cohomology.ZModSheaf.nsmul_toSheaf_eq_zero.{u + 1, u + 1} (topology X) m M U x
    exact nsmul_id_eq_zero_of_iso m e (nsmul_id_map_eq_zero m (siteSheafEquiv X).functor hM)
  · let G := (siteSheafEquiv X).inverse.obj F
    have hG' := (nsmul_id_eq_zero_iff m G).1 (nsmul_id_map_eq_zero m (siteSheafEquiv X).inverse h)
    exact ⟨Stacks.Cohomology.ZModSheaf.torsionSheafToModules.{u + 1, u + 1} (topology X) m G hG',
      ⟨(siteSheafEquiv X).functor.mapIso
          (Stacks.Cohomology.ZModSheaf.torsionSheafToModulesIso.{u + 1, u + 1} (topology X) m G
            hG') ≪≫
        (siteSheafEquiv X).counitIso.app F⟩⟩

/-- For `ℤ`-coefficients, every abelian sheaf is the underlying abelian sheaf of a sheaf of
`ℤ̲`-modules. -/
instance etaleToSheaf_zmod_zero_essSurj :
    (etaleToSheaf (ULift.{u + 1} (ZMod 0)) X).EssSurj :=
  ⟨fun F => (mem_essImage_etaleToSheaf_iff 0 X F).2 (zero_smul _ _)⟩

/-- For `ℤ`-coefficients the underlying abelian sheaf functor is an equivalence. -/
instance etaleToSheaf_zmod_zero_isEquivalence :
    (etaleToSheaf (ULift.{u + 1} (ZMod 0)) X).IsEquivalence where

/-- **Abelian sheaves on `X_étale` are the sheaves of `ℤ̲`-modules on the small model**, through
the underlying abelian sheaf. Here `ℤ̲` is the constant sheaf of rings on `ZMod 0 = ℤ`, lifted to
the universe of the coefficients. -/
def abelianSheafEquivalence :
    SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod 0)) X) ≌
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (etaleToSheaf (ULift.{u + 1} (ZMod 0)) X).asEquivalence

/-- The functor of `abelianSheafEquivalence` is the underlying abelian sheaf functor. -/
@[simp]
theorem abelianSheafEquivalence_functor :
    (abelianSheafEquivalence X).functor = etaleToSheaf (ULift.{u + 1} (ZMod 0)) X :=
  rfl

attribute [local instance] HasDerivedCategory.standard in
/-- **`D(X_étale, ℤ)` is the derived category of abelian sheaves on `X_étale`**: the underlying
complex of abelian sheaves is an equivalence, being induced by the equivalence
`abelianSheafEquivalence`. -/
def abelianSheafDerivedEquivalence :
    DerivedModules (ULift.{u + 1} (ZMod 0)) X ≌
      DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  have : (abelianSheafEquivalence X).functor.Additive := etaleToSheaf_additive _ X
  have : (forgetDerived (ULift.{u + 1} (ZMod 0)) X).IsEquivalence :=
    Stacks.DerivedCategory.mapDerivedCategory_isEquivalence (abelianSheafEquivalence X)
  (forgetDerived (ULift.{u + 1} (ZMod 0)) X).asEquivalence

end ZMod

end Stacks.EtaleCohomology.EtaleCoefficients

end
