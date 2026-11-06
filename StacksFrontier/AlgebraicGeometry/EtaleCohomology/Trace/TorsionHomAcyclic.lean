module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleTorsionReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleCoinduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisTwistCoefficient
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic
public import StacksFrontier.CategoryTheory.Abelian.PointwiseBiproductFunctor
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# `Hom` out of a finite `ℤ/ℓᴹ`-module on flat sheaves of `ℤ/ℓᴹ`-modules

Let `ℓ` be a prime, `M ≥ 0` and `D` a finite abelian group killed by `ℓᴹ`. The functor
`Hom_{ℤ/ℓᴹ}(D, -)`, applied to sheaves of `ℤ/ℓᴹ`-modules on the small étale site, is exact on
a short exact sequence whose first term is flat (`CategoryTheory.Abelian.PowExact`), and it
carries injective sheaves to sheaves acyclic for the sections over every étale object.

## Main definitions

* `Stacks.EtaleCohomology.zmodHomFunctor`: `Hom_{ℤ/ℓᴹ}(D, -)` on `ℤ/ℓᴹ`-modules.
* `Stacks.EtaleCohomology.IsTorsionHomAdapted`: a functor on `ℤ/ℓᴹ`-modules is exact on flat
  short exact sequences of étale sheaves and carries injective sheaves to sheaves acyclic
  everywhere.

## Main results

* `Stacks.EtaleCohomology.zmodHomFunctorZModIso`: `Hom_{ℤ/ℓᴹ}(ℤ/N, -)` is the coextension of
  scalars to `ℤ/N`.
* `Stacks.EtaleCohomology.isTorsionHomAdapted_zmodHomFunctor`: `Hom_{ℤ/ℓᴹ}(D, -)` satisfies
  `IsTorsionHomAdapted` for every finite `D`.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (ℓ M : ℕ)

/-- **`Hom_{ℤ/ℓᴹ}(D, -)` on `ℤ/ℓᴹ`-modules.** -/
abbrev zmodHomFunctor (D : Type (u + 1)) [AddCommGroup D] [Module (ZMod (ℓ ^ M)) D] :
    ModuleCat.{u + 1} (ZMod (ℓ ^ M)) ⥤ ModuleCat.{u + 1} (ZMod (ℓ ^ M)) :=
  sourceHomFunctor (ZMod (ℓ ^ M)) (ZMod (ℓ ^ M)) D

variable {ℓ M}

/-! ### Functoriality in `D` -/

section Functoriality

variable {D D' : Type (u + 1)} [AddCommGroup D] [AddCommGroup D'] [Module (ZMod (ℓ ^ M)) D]
  [Module (ZMod (ℓ ^ M)) D']

/-- Precomposition with a linear map `D' ⟶ D`. -/
abbrev zmodHomFunctorMap (f : D' →ₗ[ZMod (ℓ ^ M)] D) :
    zmodHomFunctor.{u} ℓ M D ⟶ zmodHomFunctor ℓ M D' :=
  sourceHomFunctorMap _ _ f fun c d => f.map_smul c d

/-- Precomposition with the identity is the identity. -/
lemma zmodHomFunctorMap_id :
    zmodHomFunctorMap (LinearMap.id : D →ₗ[ZMod (ℓ ^ M)] D) = 𝟙 _ := rfl

/-- Precomposition is contravariantly functorial: precomposing with `f` and then with `g` is
precomposing with `f ∘ₗ g`. -/
lemma zmodHomFunctorMap_comp {D'' : Type (u + 1)} [AddCommGroup D''] [Module (ZMod (ℓ ^ M)) D'']
    (f : D' →ₗ[ZMod (ℓ ^ M)] D) (g : D'' →ₗ[ZMod (ℓ ^ M)] D') :
    zmodHomFunctorMap f ≫ zmodHomFunctorMap g = zmodHomFunctorMap (f ∘ₗ g) :=
  rfl

/-- Precomposition with `f + g` is the sum of the precompositions with `f` and `g`. -/
lemma zmodHomFunctorMap_add (f g : D' →ₗ[ZMod (ℓ ^ M)] D) :
    zmodHomFunctorMap (f + g) = zmodHomFunctorMap f + zmodHomFunctorMap g := by
  ext N φ
  exact SourceHom.ext fun d => map_add φ.toLinearMap (f d) (g d)

/-- Precomposition with the zero map is zero. -/
lemma zmodHomFunctorMap_zero :
    zmodHomFunctorMap (0 : D' →ₗ[ZMod (ℓ ^ M)] D) = 0 := by
  ext N φ
  exact SourceHom.ext fun d => map_zero φ.toLinearMap

/-- `Hom(D, -) ≅ Hom(D', -)` for `D ≅ D'`. -/
def zmodHomFunctorCongr (e : D' ≃ₗ[ZMod (ℓ ^ M)] D) :
    zmodHomFunctor.{u} ℓ M D ≅ zmodHomFunctor ℓ M D' where
  hom := zmodHomFunctorMap e.toLinearMap
  inv := zmodHomFunctorMap e.symm.toLinearMap
  hom_inv_id := by
    rw [zmodHomFunctorMap_comp]
    convert zmodHomFunctorMap_id (ℓ := ℓ) (M := M) (D := D)
    ext d
    exact e.apply_symm_apply d
  inv_hom_id := by
    rw [zmodHomFunctorMap_comp]
    convert zmodHomFunctorMap_id (ℓ := ℓ) (M := M) (D := D')
    ext d
    exact e.symm_apply_apply d

end Functoriality

/-! ### `Hom(ℤ/N, -)` is the `N`-torsion -/

section ZModTorsion

/-- `ℤ/N` in the universe of the coefficients. -/
abbrev ZModLift (N : ℕ) : Type (u + 1) := ULift.{u + 1} (ZMod N)

variable {N : ℕ} [hN : Fact (N ∣ ℓ ^ M)]

/-- The `ℤ/ℓᴹ`-module structure of `ℤ/N` for `N ∣ ℓᴹ`, by restriction of scalars. -/
instance zmodLiftModule : Module (ZMod (ℓ ^ M)) (ZModLift.{u} N) :=
  @ULift.module' _ _ _ _ (Module.compHom (ZMod N) (ZMod.castHom hN.out (ZMod N)))

/-- **`Hom_{ℤ/ℓᴹ}(ℤ/N, -)` is the coextension of scalars to `ℤ/N`**, read over `ℤ/ℓᴹ`: the
`N`-torsion. -/
def zmodHomFunctorZModIso :
    zmodHomFunctor.{u} ℓ M (ZModLift N) ≅
      (ModuleCat.coextendScalars (ZMod.castHom hN.out (ZMod N)) :
          ModuleCat.{u + 1} (ZMod (ℓ ^ M)) ⥤ ModuleCat.{u + 1} (ZMod N)) ⋙
        ModuleCat.restrictScalars.{u + 1} (ZMod.castHom hN.out (ZMod N)) :=
  NatIso.ofComponents (fun P => LinearEquiv.toModuleIso
    ({ toFun := fun φ => (ModuleCat.CoextendScalars.equiv _ P).symm
          { toFun := fun x => φ.toLinearMap (ULift.up x)
            map_add' := fun x y => map_add φ.toLinearMap (ULift.up x) (ULift.up y)
            map_smul' := fun c x => φ.toLinearMap.map_smul c (ULift.up x) }
       invFun := fun g => SourceHom.ofLinearMap
          { toFun := fun d => ModuleCat.CoextendScalars.equiv _ P g d.down
            map_add' := fun d d' => map_add (ModuleCat.CoextendScalars.equiv _ P g) d.down d'.down
            map_smul' := fun c d => (ModuleCat.CoextendScalars.equiv _ P g).map_smul c d.down }
       map_add' := fun _ _ => rfl
       map_smul' := fun c φ => by
         refine ModuleCat.CoextendScalars.ext (LinearMap.ext fun x => ?_)
         change φ.toLinearMap (c • ULift.up x) =
           φ.toLinearMap (ULift.up ((show ZMod N from x) * ZMod.castHom hN.out (ZMod N) c))
         congr 1
         exact ULift.ext (mul_comm (ZMod.castHom hN.out (ZMod N) c) (show ZMod N from x))
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } :
      SourceHom (ZMod (ℓ ^ M)) (ZMod (ℓ ^ M)) (ZModLift.{u} N) P ≃ₗ[ZMod (ℓ ^ M)]
        (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom hN.out (ZMod N))).obj
          ((ModuleCat.coextendScalars (ZMod.castHom hN.out (ZMod N))).obj P)))
    (fun _ => rfl)

end ZModTorsion

/-! ### On sheaves -/

section Sheaves

/-- `sheafCompose` is additive in the coefficient functor. -/
lemma sheafCompose_map_add {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {A B : Type*} [Category* A] [Category* B] [Preadditive B] {F G : A ⥤ B}
    [J.HasSheafCompose F] [J.HasSheafCompose G] (η γ : F ⟶ G) :
    sheafCompose_map J (η + γ) = sheafCompose_map J η + sheafCompose_map J γ :=
  NatTrans.ext (funext fun _ => Sheaf.hom_ext rfl)

/-- `sheafCompose` sends the zero natural transformation to zero. -/
lemma sheafCompose_map_zero {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {A B : Type*} [Category* A] [Category* B] [Preadditive B] {F G : A ⥤ B}
    [J.HasSheafCompose F] [J.HasSheafCompose G] : sheafCompose_map J (0 : F ⟶ G) = 0 :=
  NatTrans.ext (funext fun _ => Sheaf.hom_ext rfl)

/-- A change of coefficients by an additive functor is additive on sheaves. -/
instance sheafCompose_additive {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B] (F : A ⥤ B)
    [F.Additive] [J.HasSheafCompose F] : (sheafCompose J F).Additive where
  map_add := Sheaf.hom_ext <| NatTrans.ext <| funext fun _ ↦ F.map_add

/-- **A change of coefficients by a left exact functor is left exact on sheaves**, when
`sheafToPresheaf` is left exact. -/
instance preservesFiniteLimits_sheafCompose {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    [HasFiniteLimits A] [J.HasSheafCompose F] [PreservesFiniteLimits F]
    [PreservesFiniteLimits (sheafToPresheaf J A)] :
    PreservesFiniteLimits (sheafCompose J F) := by
  have : PreservesFiniteLimits ((Functor.whiskeringRight Cᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteLimits (sheafCompose J F ⋙ sheafToPresheaf J B) := by
    change PreservesFiniteLimits (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj F)
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J B)

variable (ℓ M) in
/-- A functor `F` on `ℤ/ℓᴹ`-modules, applied to sheaves of `ℤ/ℓᴹ`-modules on the small étale site
of every scheme, is exact on short exact sequences with flat first term and carries injective
sheaves to sheaves acyclic everywhere. -/
def IsTorsionHomAdapted (F : ModuleCat.{u + 1} (ZMod (ℓ ^ M)) ⥤ ModuleCat.{u + 1} (ZMod (ℓ ^ M)))
    [F.Additive] [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose F] : Prop :=
  ∀ X : Scheme.{u},
    (∀ S : ShortComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ M)) X), S.ShortExact →
      PowExact ℓ M S.X₁ → (S.map (sheafCompose X.smallEtaleTopology F)).ShortExact) ∧
    ∀ I : EtaleModules.{u, 0} (ZMod (ℓ ^ M)) X, Injective I →
      IsAcyclicEverywhere ((sheafCompose X.smallEtaleTopology F).obj I)

variable {F F' F₁ F₂ : ModuleCat.{u + 1} (ZMod (ℓ ^ M)) ⥤ ModuleCat.{u + 1} (ZMod (ℓ ^ M))}
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose F]
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose F']
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose F₁]
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose F₂]
  [F.Additive] [F'.Additive] [F₁.Additive] [F₂.Additive]

/-- `IsTorsionHomAdapted` is invariant under isomorphism of functors. -/
lemma IsTorsionHomAdapted.of_iso (e : F ≅ F') (h : IsTorsionHomAdapted ℓ M F) :
    IsTorsionHomAdapted ℓ M F' := fun X =>
  ⟨fun S hS h₁ => ShortComplex.shortExact_of_iso
      (S.mapNatIso (sheafComposeIsoOfIso (J := X.smallEtaleTopology) e)) ((h X).1 S hS h₁),
    fun I hI U => Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
      ((sheafComposeIsoOfIso (J := X.smallEtaleTopology) e).app I) ((h X).2 I hI U)⟩

/-- A functor with zero values satisfies `IsTorsionHomAdapted`. -/
lemma IsTorsionHomAdapted.of_isZero (h : ∀ P, IsZero (F.obj P)) : IsTorsionHomAdapted ℓ M F := by
  intro X
  have hz : ∀ A : EtaleModules.{u, 0} (ZMod (ℓ ^ M)) X,
      IsZero ((sheafCompose X.smallEtaleTopology F).obj A) := fun A => by
    rw [IsZero.iff_id_eq_zero]
    exact Sheaf.hom_ext (NatTrans.ext (funext fun U => (h _).eq_of_src _ _))
  exact ⟨fun S _ _ => { exact := ShortComplex.exact_of_isZero_X₂ _ (hz S.X₂)
                        mono_f := (hz S.X₁).mono _
                        epi_g := (hz S.X₃).epi _ },
    fun I _ U => Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _ (hz I)⟩

/-- A functor that is the biproduct of `F₁` and `F₂`, with injections `i₁, i₂` and projections
`p₁, p₂`, satisfies `IsTorsionHomAdapted` when `F₁` and `F₂` do. -/
lemma IsTorsionHomAdapted.of_biprod (i₁ : F₁ ⟶ F) (i₂ : F₂ ⟶ F) (p₁ : F ⟶ F₁) (p₂ : F ⟶ F₂)
    (h₁₁ : i₁ ≫ p₁ = 𝟙 _) (h₂₂ : i₂ ≫ p₂ = 𝟙 _) (h₁₂ : i₁ ≫ p₂ = 0) (h₂₁ : i₂ ≫ p₁ = 0)
    (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 _)
    (hF₁ : IsTorsionHomAdapted ℓ M F₁) (hF₂ : IsTorsionHomAdapted ℓ M F₂) :
    IsTorsionHomAdapted ℓ M F := by
  intro X
  let J := X.smallEtaleTopology
  have etot : sheafCompose_map J p₁ ≫ sheafCompose_map J i₁ +
      sheafCompose_map J p₂ ≫ sheafCompose_map J i₂ = 𝟙 _ := by
    rw [← sheafCompose_comp, ← sheafCompose_comp, ← sheafCompose_map_add, htot, sheafCompose_id]
  let e : sheafCompose J F ≅ Functor.pointwiseBiprod (sheafCompose J F₁) (sheafCompose J F₂) :=
    { hom := Functor.pointwiseBiprod.lift _ _ (sheafCompose_map J p₁) (sheafCompose_map J p₂)
      inv := Functor.pointwiseBiprod.desc _ _ (sheafCompose_map J i₁) (sheafCompose_map J i₂)
      hom_inv_id := by
        ext A : 2
        change biprod.lift _ _ ≫ biprod.desc _ _ = 𝟙 _
        rw [biprod.lift_desc]
        exact NatTrans.congr_app etot A
      inv_hom_id := by
        ext A : 2
        change biprod.desc _ _ ≫ biprod.lift _ _ = 𝟙 _
        refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
          simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Category.assoc,
            biprod.lift_fst, biprod.lift_snd, Category.id_comp, biprod.inl_fst, biprod.inl_snd,
            biprod.inr_fst, biprod.inr_snd]
        exacts [congrArg (·.app A) (congrArg (sheafCompose_map J) h₁₁),
          congrArg (·.app A) (congrArg (sheafCompose_map J) h₁₂),
          congrArg (·.app A) (congrArg (sheafCompose_map J) h₂₁),
          congrArg (·.app A) (congrArg (sheafCompose_map J) h₂₂)] }
  exact ⟨fun S hS h => ShortComplex.shortExact_of_iso (S.mapNatIso e).symm
      (ShortComplex.shortExact_biprod_map ((hF₁ X).1 S hS h) ((hF₂ X).1 S hS h)),
    fun I hI U => Stacks.RightAcyclicProduct.rightAcyclic_of_iso _ (e.app I).symm
      (Stacks.RightAcyclicProduct.rightAcyclic_biprod _ ((hF₁ X).2 I hI U) ((hF₂ X).2 I hI U))⟩

end Sheaves

/-! ### Finite `D` -/

section Finite

/-- `Hom_{ℤ/ℓᴹ}(D₁ × D₂, -)` satisfies `IsTorsionHomAdapted` when `Hom_{ℤ/ℓᴹ}(D₁, -)` and
`Hom_{ℤ/ℓᴹ}(D₂, -)` do. -/
lemma isTorsionHomAdapted_prod {D₁ D₂ : Type (u + 1)} [AddCommGroup D₁] [AddCommGroup D₂]
    [Module (ZMod (ℓ ^ M)) D₁] [Module (ZMod (ℓ ^ M)) D₂]
    (h₁ : IsTorsionHomAdapted ℓ M (zmodHomFunctor ℓ M D₁))
    (h₂ : IsTorsionHomAdapted ℓ M (zmodHomFunctor ℓ M D₂)) :
    IsTorsionHomAdapted ℓ M (zmodHomFunctor ℓ M (D₁ × D₂)) := by
  refine IsTorsionHomAdapted.of_biprod (zmodHomFunctorMap (LinearMap.fst _ D₁ D₂))
    (zmodHomFunctorMap (LinearMap.snd _ D₁ D₂)) (zmodHomFunctorMap (LinearMap.inl _ D₁ D₂))
    (zmodHomFunctorMap (LinearMap.inr _ D₁ D₂)) ?_ ?_ ?_ ?_ ?_ h₁ h₂
  · rw [zmodHomFunctorMap_comp, LinearMap.fst_comp_inl, zmodHomFunctorMap_id]
  · rw [zmodHomFunctorMap_comp, LinearMap.snd_comp_inr, zmodHomFunctorMap_id]
  · rw [zmodHomFunctorMap_comp, LinearMap.fst_comp_inr, zmodHomFunctorMap_zero]
  · rw [zmodHomFunctorMap_comp, LinearMap.snd_comp_inl, zmodHomFunctorMap_zero]
  · rw [zmodHomFunctorMap_comp, zmodHomFunctorMap_comp, ← zmodHomFunctorMap_add]
    convert zmodHomFunctorMap_id (ℓ := ℓ) (M := M) (D := D₁ × D₂)
    ext d <;> simp

/-- `Hom_{ℤ/ℓᴹ}(D, -)` satisfies `IsTorsionHomAdapted` for a trivial module `D`. -/
lemma isTorsionHomAdapted_of_subsingleton (D : Type (u + 1)) [AddCommGroup D]
    [Module (ZMod (ℓ ^ M)) D] [Subsingleton D] :
    IsTorsionHomAdapted ℓ M (zmodHomFunctor ℓ M D) :=
  IsTorsionHomAdapted.of_isZero fun P => by
    have : Subsingleton ((zmodHomFunctor ℓ M D).obj P) :=
      ⟨fun φ ψ => SourceHom.ext fun d => by rw [Subsingleton.elim d 0, map_zero, map_zero]⟩
    exact ModuleCat.isZero_of_subsingleton _

variable [Fact ℓ.Prime]

/-- `Hom_{ℤ/ℓᴹ}(ℤ/N, -)` satisfies `IsTorsionHomAdapted` for `N = ℓᵃ` with `a ≤ M`. -/
lemma isTorsionHomAdapted_zmodLift {N a : ℕ} [hN : Fact (N ∣ ℓ ^ M)] (ha : a ≤ M)
    (hNa : N = ℓ ^ a) : IsTorsionHomAdapted ℓ M (zmodHomFunctor ℓ M (ZModLift.{u} N)) := by
  refine IsTorsionHomAdapted.of_iso (zmodHomFunctorZModIso (ℓ := ℓ) (M := M)).symm fun X => ?_
  refine ⟨fun S hS h₁ =>
    (shortExact_map_coextendScalars hN.out ha hNa S hS h₁).map_of_exact
      (etaleModuleRestrictScalars (ZMod.castHom hN.out (ZMod N)) X), fun I hI => ?_⟩
  have : (etaleModuleCoextendScalars (ZMod.castHom hN.out (ZMod N)) X).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleModuleCoextendScalarsAdj (ZMod.castHom hN.out (ZMod N)) X)
  have : Injective ((etaleModuleCoextendScalars (ZMod.castHom hN.out (ZMod N)) X).obj I) :=
    (etaleModuleCoextendScalars (ZMod.castHom hN.out (ZMod N)) X).injective_obj_of_injective hI
  exact isAcyclicEverywhere_restrictScalars' (ZMod.castHom hN.out (ZMod N))
    ((etaleModuleCoextendScalars (ZMod.castHom hN.out (ZMod N)) X).obj I)

/-- `Hom_{ℤ/ℓᴹ}(∏ᵢ ℤ/Nᵢ, -)` satisfies `IsTorsionHomAdapted` for a finite family of powers
`Nᵢ = ℓ^{aᵢ}` with `aᵢ ≤ M`. -/
lemma isTorsionHomAdapted_pi (ι : Type) [Finite ι] :
    ∀ (N : ι → ℕ) [∀ i, Fact (N i ∣ ℓ ^ M)], (∀ i, ∃ a ≤ M, N i = ℓ ^ a) →
      IsTorsionHomAdapted ℓ M (zmodHomFunctor ℓ M (∀ i, ZModLift.{u} (N i))) := by
  refine Finite.induction_empty_option (P := fun ι ↦ ∀ (N : ι → ℕ) [∀ i, Fact (N i ∣ ℓ ^ M)],
    (∀ i, ∃ a ≤ M, N i = ℓ ^ a) →
      IsTorsionHomAdapted ℓ M (zmodHomFunctor ℓ M (∀ i, ZModLift.{u} (N i)))) ?_ ?_ ?_ ι
  · intro α β e hα N _ hN
    have : ∀ a, Fact ((N ∘ e) a ∣ ℓ ^ M) := fun a ↦ inferInstanceAs (Fact (N (e a) ∣ _))
    exact (hα (N ∘ e) fun a ↦ hN (e a)).of_iso
      (zmodHomFunctorCongr (LinearEquiv.piCongrLeft (ZMod (ℓ ^ M))
        (fun b ↦ ZModLift.{u} (N b)) e).symm)
  · exact fun N _ _ ↦ isTorsionHomAdapted_of_subsingleton _
  · intro α _ hα N _ hN
    obtain ⟨a, ha, hNa⟩ := hN none
    exact (isTorsionHomAdapted_prod (isTorsionHomAdapted_zmodLift ha hNa)
      (hα (fun a ↦ N (some a)) fun a ↦ hN (some a))).of_iso
      (zmodHomFunctorCongr (LinearEquiv.piOptionEquivProd (ZMod (ℓ ^ M))))

/-- **`Hom_{ℤ/ℓᴹ}(D, -)` for a finite `D`** is exact on short exact sequences of sheaves with
flat first term and carries injective sheaves to sheaves acyclic everywhere. -/
theorem isTorsionHomAdapted_zmodHomFunctor (D : Type (u + 1)) [AddCommGroup D]
    [Module (ZMod (ℓ ^ M)) D] [Finite D] : IsTorsionHomAdapted ℓ M (zmodHomFunctor ℓ M D) := by
  classical
  obtain ⟨ι, _, p, -, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite D
  let N : ι → ℕ := fun i => p i ^ e i
  have hdvd : ∀ i, N i ∣ ℓ ^ M := fun i => by
    have hx : (ℓ ^ M) • f.symm (DirectSum.of (fun i => ZMod (N i)) i 1) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ M)), ZMod.natCast_self, zero_smul]
    rw [← map_nsmul, AddEquiv.map_eq_zero_iff, ← map_nsmul] at hx
    have h1 := DirectSum.of_injective (β := fun i => ZMod (N i)) i (hx.trans (map_zero _).symm)
    rw [nsmul_eq_mul, mul_one] at h1
    exact (ZMod.natCast_eq_zero_iff _ _).1 h1
  have : ∀ i, Fact (N i ∣ ℓ ^ M) := fun i => ⟨hdvd i⟩
  let g : D ≃+ (∀ i, ZModLift.{u} (N i)) :=
    f.trans ((DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (N i))).toAddEquiv.trans
      (AddEquiv.piCongrRight fun i => AddEquiv.ulift.symm))
  let gl : D ≃ₗ[ZMod (ℓ ^ M)] (∀ i, ZModLift.{u} (N i)) :=
    { g with map_smul' := fun c x => ZMod.map_smul g c x }
  exact (isTorsionHomAdapted_pi ι N fun i =>
    (Nat.dvd_prime_pow (Fact.out : ℓ.Prime)).1 (hdvd i)).of_iso (zmodHomFunctorCongr gl)

end Finite

end Stacks.EtaleCohomology

end
