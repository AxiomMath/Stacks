module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Algebra.Category.ModuleCat.Localization
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Flatness over the base, read on affine sections

A quasi-coherent module `F` on a scheme `X` over `S` is flat over `S` exactly when, for every
pair of affine opens `U ⊆ f⁻¹ V`, the module `Γ(F, U)` is flat over `Γ(S, V)`. This file derives
three consequences of that criterion: flatness over an affine base is flatness of the global
sections; flatness is detected by a flat covering family of pullbacks; and the flatness of a base
change along a map of affine schemes is the flatness of an extension of scalars of the module of
sections.

## Main results

* `AlgebraicGeometry.isFlatOver_iff_flat_sections`: for a morphism of affine schemes, flatness
  over the target is flatness of the global sections.
* `AlgebraicGeometry.isFlatOver_specMap_iff`: the same for a morphism of spectra, with the
  scalar action given by restriction of scalars.
* `AlgebraicGeometry.isFlatOver_iff_forall_pullback`: flatness over the base is detected by a
  family of flat morphisms covering the source.
* `AlgebraicGeometry.isFlatOver_baseChange_iff_openCover`: the base change of a module is flat
  over the new base exactly when the base change of each member of an open cover of the source
  is.
* `AlgebraicGeometry.isFlatOver_affine_baseChange_iff`: for a base change of affine schemes,
  flatness of the pulled-back module is flatness of the extension of scalars of its sections.
* `AlgebraicGeometry.isFlatOver_of_isField_stalks` and
  `AlgebraicGeometry.isFlatOver_of_isField`: every module on a scheme over the spectrum of a
  field is flat over that spectrum.

## Implementation notes

The scalar action of `Γ(S, V)` on `Γ(F, U)` is the restriction along `f.appLE V U`, written
with `Module.compHom`. Comparing it with an `Algebra`-derived action is what
`Module.compHom_algebraMap` and `Module.Flat.compHom_ringEquiv_iff` are for; the latter is
deduced from `Module.Flat.of_semilinearEquiv`, flatness transported along a ring isomorphism
together with a compatible additive isomorphism of modules.

Pullback of modules along a morphism of schemes is `AlgebraicGeometry.Scheme.Modules.pullback`,
while the flatness criteria of Stacks 02JZ are stated for the ringed-space functor
`RingedSpaceModuleAdjunction.modulePullback`. The two agree definitionally, and the comparison
is made explicit by `AlgebraicGeometry.schemeModulesPullback_eq`, so that no transparency
setting is needed to move between them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open TensorProduct
open scoped TensorProduct

universe u v w

/-- Restricting scalars along the structure map of an algebra recovers the ambient module
structure when the two actions are compatible. -/
public theorem Module.compHom_algebraMap (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] :
    Module.compHom M (algebraMap A B) = (inferInstance : Module A M) :=
  Module.ext' _ _ fun a m ↦ IsScalarTower.algebraMap_smul B a m

/-- Flatness transfers along a ring isomorphism together with a compatible additive
isomorphism of modules. -/
public theorem Module.Flat.of_semilinearEquiv {A B M N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N] [Module.Flat B N]
    (e : A ≃+* B) (l : M ≃+ N) (hl : ∀ a m, l (a • m) = e a • l m) : Module.Flat A M :=
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module A N := Module.compHom N e.toRingHom
  have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat A B := RingHom.Flat.of_bijective e.bijective
  have : Module.Flat A N := Module.Flat.trans A B N
  Module.Flat.of_linearEquiv (l.toLinearEquiv (R := A) hl)

/-- Flatness is unchanged by restricting the scalars along a ring isomorphism. -/
public theorem Module.Flat.compHom_ringEquiv_iff (A B : Type*) [CommRing A] [CommRing B]
    (M : Type*) [AddCommGroup M] [Module B M] (e : A ≃+* B) :
    (let : Module A M := Module.compHom M e.toRingHom; Module.Flat A M) ↔ Module.Flat B M := by
  let : Module A M := Module.compHom M e.toRingHom
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h
    exact Module.Flat.of_semilinearEquiv e.symm (AddEquiv.refl M) fun b m ↦ by
      change b • m = e (e.symm b) • m
      rw [e.apply_symm_apply]
  · have := h
    exact Module.Flat.of_semilinearEquiv e (AddEquiv.refl M) fun _ _ ↦ rfl

namespace AlgebraicGeometry

/-- Pullback of modules along a morphism of schemes is the ringed-space pullback of its
underlying morphism of sheaves of rings. -/
public theorem schemeModulesPullback_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pullback f = modulePullback f.toLRSHom.toShHom := rfl

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
public instance pullback_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback f).obj F).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback f F

/-- **Flatness over an affine base, on an affine source.** For a morphism of affine schemes,
flatness over the target is flatness of the global sections of the module over the global
functions on the target. -/
public theorem isFlatOver_iff_flat_sections {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] :
    IsFlatOver f.toLRSHom.toShHom F ↔
      let : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom _ f.appTop.hom
      Module.Flat Γ(S, ⊤) Γ(F, ⊤) := by
  have key₁ := (isFlatOver_tfae f F).out 1 2
  have key₄ := (isFlatOver_tfae f F).out 4 1
  have htop : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  have hinst : Module.compHom Γ(F, ⊤) (f.appLE (⊤ : S.Opens) (⊤ : X.Opens) htop).hom =
      Module.compHom Γ(F, ⊤) f.appTop.hom := by
    rw [Stacks.AffineAlgebraEquivalence.appLE_top_top]
  refine ⟨fun h ↦ hinst ▸ key₁.mp h ⊤ (isAffineOpen_top X) ⊤ (isAffineOpen_top S) htop,
    fun h ↦ key₄.mp ⟨PUnit.{u + 1}, fun _ ↦ ⊤, ?_, fun _ ↦ isAffineOpen_top S,
      fun _ ↦ ⟨PUnit.{u + 1}, fun _ ↦ ⊤, by simp, fun _ ↦ isAffineOpen_top X, fun _ ↦ ?_⟩⟩⟩
  · simp [TopologicalSpace.IsOpenCover]
  · dsimp only
    exact hinst.symm ▸ h

/-- **Flatness over the spectrum of a ring.** For an affine scheme over `Spec R`, flatness over
the base is flatness of the global sections of the module as an `R`-module. -/
public theorem isFlatOver_overSpec_iff_flat_sections {R : CommRingCat.{u}} {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec R) (F : X.Modules) [F.IsQuasicoherent] :
    IsFlatOver f.toLRSHom.toShHom F ↔
      let : Module R Γ(F, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom
      Module.Flat R Γ(F, ⊤) := by
  refine (isFlatOver_iff_flat_sections f F).trans ?_
  let : Module Γ(Spec R, ⊤) Γ(F, ⊤) := Module.compHom _ f.appTop.hom
  exact (Module.Flat.compHom_ringEquiv_iff R Γ(Spec R, ⊤) Γ(F, ⊤)
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv).symm

/-- **Flatness over the spectrum of a ring, for a morphism of spectra.** The module associated
to `F` on `Spec A` is flat over `R` exactly when the quasi-coherent module `F` is flat over
`Spec R`. -/
public theorem isFlatOver_specMap_iff {R A : CommRingCat.{u}} (f : R ⟶ A) (F : (Spec A).Modules)
    [F.IsQuasicoherent] :
    IsFlatOver (Spec.map f).toLRSHom.toShHom F ↔
      Module.Flat R ((ModuleCat.restrictScalars f.hom).obj (moduleSpecΓFunctor.obj F)) := by
  refine (isFlatOver_overSpec_iff_flat_sections (Spec.map f) F).trans ?_
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- **Flatness over the base is detected by a flat covering family.** If the morphisms `g i`
are flat and their images cover `X`, then a module on `X` is flat over `S` exactly when each of
its pullbacks is. -/
public theorem isFlatOver_iff_forall_pullback {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {ι : Type*} {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X) [∀ i, Flat (g i)]
    (hg : ∀ x : X, ∃ i y, g i y = x) :
    IsFlatOver f.toLRSHom.toShHom F ↔
      ∀ i, IsFlatOver (g i ≫ f).toLRSHom.toShHom ((Scheme.Modules.pullback (g i)).obj F) := by
  refine ⟨fun h i y ↦ (isFlatOverAt_iff_modulePullback_isFlatOverAt (g i) f F y
    (Flat.stalkMap _ _)).mp (h _), fun h x ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := hg x
  exact (isFlatOverAt_iff_modulePullback_isFlatOverAt (g i) f F y (Flat.stalkMap _ _)).mpr
    (h i y)

/-- Flatness over the base of a pullback module is unchanged by replacing the source with an
isomorphic scheme. -/
public theorem isFlatOver_pullback_iff_of_iso {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : X ⟶ Z)
    (e : Y ≅ X) (F : Z.Modules) [F.IsQuasicoherent] :
    IsFlatOver f.toLRSHom.toShHom ((Scheme.Modules.pullback g).obj F) ↔
      IsFlatOver (e.hom ≫ f).toLRSHom.toShHom
        ((Scheme.Modules.pullback (e.hom ≫ g)).obj F) := by
  refine (isFlatOver_iff_modulePullback_isFlatOver e.hom f
    ((Scheme.Modules.pullback g).obj F)).trans ?_
  exact isFlatOver_iff_of_moduleIso _ ((Scheme.Modules.pullbackComp e.hom g).app F)

/-- **Flatness of a base change is local on the source.** The pullback of `F` to `X ×_S T` is
flat over `T` exactly when the pullback of each restriction of `F` to a member of an open cover
of `X` is flat over `T`. -/
public theorem isFlatOver_baseChange_iff_openCover {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (𝒰 : X.OpenCover) :
    IsFlatOver (pullback.snd f g).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F) ↔
      ∀ i, IsFlatOver (pullback.snd (𝒰.f i ≫ f) g).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst (𝒰.f i ≫ f) g)).obj
          ((Scheme.Modules.pullback (𝒰.f i)).obj F)) := by
  let 𝒱 : (pullback f g).OpenCover := 𝒰.pullback₂ (pullback.fst f g)
  refine (isFlatOver_iff_forall_pullback (pullback.snd f g)
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F) 𝒱.f 𝒱.exists_eq).trans ?_
  refine forall_congr' fun i ↦ ?_
  change IsFlatOver
    (pullback.snd (𝒰.f i) (pullback.fst f g) ≫ pullback.snd f g).toLRSHom.toShHom
    ((Scheme.Modules.pullback (pullback.snd (𝒰.f i) (pullback.fst f g))).obj
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ↔ _
  refine (isFlatOver_iff_of_moduleIso _ ((Scheme.Modules.pullbackComp _ _).app F)).trans ?_
  have h := isFlatOver_pullback_iff_of_iso
    (pullback.snd (𝒰.f i) (pullback.fst f g) ≫ pullback.snd f g)
    (pullback.snd (𝒰.f i) (pullback.fst f g) ≫ pullback.fst f g)
    (pullbackRightPullbackFstIso f g (𝒰.f i)).symm F
  dsimp only [Iso.symm_hom] at h
  rw [pullbackRightPullbackFstIso_inv_snd_snd, pullbackRightPullbackFstIso_inv_snd_fst] at h
  exact h.trans (isFlatOver_iff_of_moduleIso _ ((Scheme.Modules.pullbackComp _ _).app F)).symm

/-- Extension of scalars along the structure map of an algebra is the tensor product with that
algebra. -/
public noncomputable def extendScalarsAlgebraMapLinearIso {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj M ≅ ModuleCat.of B (B ⊗[A] (M : Type u)) := by
  let B' := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  let : IsScalarTower A B B' := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e : B' ≃ₗ[B] B := LinearEquiv.refl B B
  exact (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl A M)).toModuleIso

/-- **Flatness of an affine base change.** For ring maps `f : R ⟶ A` and `g : R ⟶ B` and a
quasi-coherent module `F` on `Spec A`, the pullback of `F` to `Spec A ×_{Spec R} Spec B` is flat
over `Spec B` exactly when the extension of scalars of the sections of `F` along `g` is a flat
`B`-module. -/
public theorem isFlatOver_affine_baseChange_iff {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B)
    (F : (Spec A).Modules) [F.IsQuasicoherent] :
    IsFlatOver (pullback.snd (Spec.map f) (Spec.map g)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst (Spec.map f) (Spec.map g))).obj F) ↔
      Module.Flat B ((ModuleCat.extendScalars g.hom).obj
        ((ModuleCat.restrictScalars f.hom).obj (moduleSpecΓFunctor.obj F))) := by
  let : Algebra R A := f.hom.toAlgebra
  let : Algebra R B := g.hom.toAlgebra
  let : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let M := (moduleSpecΓFunctor (R := A)).obj F
  let : Module R M := Module.compHom M f.hom
  have : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have h := isFlatOver_pullback_iff_of_iso
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))) (pullbackSpecIso R A B).symm F
  dsimp only [Iso.symm_hom] at h
  rw [pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd] at h
  refine h.trans ((isFlatOver_specMap_iff _ _).trans ?_)
  let e := (ModuleCat.restrictScalars (algebraMap B (A ⊗[R] B))).mapIso
    (specPullbackSectionsIso A (.of (A ⊗[R] B))
      (CommRingCat.ofHom (algebraMap A (A ⊗[R] B))) F)
  refine (Module.Flat.equiv_iff e.toLinearEquiv).trans ?_
  let e₁ := (ModuleCat.restrictScalars (algebraMap B (A ⊗[R] B))).mapIso
    (extendScalarsAlgebraMapLinearIso (A := A) (B := A ⊗[R] B) M)
  let e₂ := ModuleCat.restrictScalarsAlgebraMapIso (R := B)
    (ModuleCat.of (A ⊗[R] B) ((A ⊗[R] B) ⊗[A] M))
  refine (Module.Flat.equiv_iff (e₁ ≪≫ e₂).toLinearEquiv).trans ?_
  exact Module.Flat.equiv_iff (Algebra.IsPushout.cancelBaseChange R B A (A ⊗[R] B) M)

/-- A module on a ringed space all of whose base stalks are fields is flat over the base. -/
public theorem isFlatOver_of_isField_stalks {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : ∀ x, IsField (Y.presheaf.stalk (f.hom.base x))) : IsFlatOver f F := by
  intro x
  unfold IsFlatOverAt
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  let := (hF x).toField
  have : Module.Free (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.Free.of_divisionRing _ _
  exact Module.Flat.of_free

/-- Every module on a scheme over the spectrum of a field is flat over that spectrum: all the
stalks of the base are that field. -/
public theorem isFlatOver_of_isField {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (F : X.Modules) : IsFlatOver f.toLRSHom.toShHom F := by
  refine isFlatOver_of_isField_stalks _ _ fun x ↦ ?_
  rw [show (f.toLRSHom.toShHom.hom.base x : Spec (.of K)) = IsLocalRing.closedPoint K from
    Subsingleton.elim _ _]
  exact (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.isField (Field.toIsField K)

end AlgebraicGeometry
