module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.RingTheory.Dualizing.RelativeCoprojections
public import StacksFrontier.RingTheory.Dualizing.RelativeGeneratorBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineChart
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineSections
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard

/-!
# The diagonal open of a morphism of spectra

Let `A` be an `R`-algebra and `f : X ⟶ S` a morphism of schemes identified with
`Spec A ⟶ Spec R` by isomorphisms `X ≅ Spec A` and `S ≅ Spec R`. Then
`X ×_S X ≅ Spec(A ⊗_R A)`, and the relative diagonal of `f` is `Spec` of the multiplication
`A ⊗_R A ⟶ A`, a closed immersion. This gives a diagonal open of `f` (in the sense of Stacks
0E2T) whose open is `Spec(A ⊗_R A)` itself, on which the diagonal and the first projection are
`Spec` of the multiplication and of the left coprojection.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.ofSpec`: the diagonal open `Spec(A ⊗_R A)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.ofSpec_proj`: its first projection is `Spec` of the
  left coprojection `A ⟶ A ⊗_R A`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} (f : X ⟶ S) {R A : CommRingCat.{u}} [Algebra R A]
  (eX : X ≅ Spec A) (eS : S ≅ Spec R)
  (hf : eX.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = f ≫ eS.hom)

variable (R A) in
/-- The ring `A ⊗_R A`. -/
abbrev envelopingRing : CommRingCat.{u} :=
  CommRingCat.of (A ⊗[R] A)

variable (R A) in
/-- The multiplication `A ⊗_R A ⟶ A`. -/
abbrev envelopingMul : envelopingRing R A ⟶ A :=
  CommRingCat.ofHom (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom

variable (R A) in
/-- The left coprojection `A ⟶ A ⊗_R A`. -/
abbrev envelopingLeft : A ⟶ envelopingRing R A :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)

variable (R A) in
/-- The right coprojection `A ⟶ A ⊗_R A`. -/
abbrev envelopingRight : A ⟶ envelopingRing R A :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom

variable (R A) in
/-- The left coprojection followed by the multiplication is the identity of `A`. -/
theorem envelopingLeft_comp_envelopingMul : envelopingLeft R A ≫ envelopingMul R A = 𝟙 A := by
  ext a
  simp

variable (R A) in
/-- The right coprojection followed by the multiplication is the identity of `A`. -/
theorem envelopingRight_comp_envelopingMul : envelopingRight R A ≫ envelopingMul R A = 𝟙 A := by
  ext a
  simp

include hf in
/-- The structure morphism `Spec A ⟶ Spec R` followed by `eS.inv` is `eX.inv ≫ f`. -/
theorem spec_comp_inv : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ eS.inv = eX.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `Spec(A ⊗_R A) ⟶ X ×_S X`, the isomorphism exhibiting `Spec(A ⊗_R A)` as `X ×_S X`. -/
def ofSpecι : Spec (envelopingRing R A) ⟶ pullback f f :=
  (pullbackSpecIso R A A).inv ≫
    pullback.map _ _ f f eX.inv eX.inv eS.inv (spec_comp_inv f eX eS hf)
      (spec_comp_inv f eX eS hf)

/-- The morphism `ofSpecι f eX eS hf : Spec(A ⊗_R A) ⟶ X ×_S X` is an isomorphism. -/
instance : IsIso (ofSpecι f eX eS hf) := by
  unfold ofSpecι
  infer_instance

/-- The first projection of `X ×_S X` restricts along `ofSpecι` to `Spec` of the left coprojection
followed by `eX.inv`. -/
@[reassoc]
theorem ofSpecι_fst :
    ofSpecι f eX eS hf ≫ pullback.fst f f = Spec.map (envelopingLeft R A) ≫ eX.inv := by
  simp only [ofSpecι, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc, pullbackSpecIso_inv_fst]

/-- The second projection of `X ×_S X` restricts along `ofSpecι` to `Spec` of the right
coprojection followed by `eX.inv`. -/
@[reassoc]
theorem ofSpecι_snd :
    ofSpecι f eX eS hf ≫ pullback.snd f f = Spec.map (envelopingRight R A) ≫ eX.inv := by
  simp only [ofSpecι, Category.assoc, pullback.lift_snd]
  rw [← Category.assoc, pullbackSpecIso_inv_snd]
  rfl

/-- `Spec` of the multiplication `A ⊗_R A ⟶ A` is a closed immersion. -/
instance : IsClosedImmersion (Spec.map (envelopingMul R A)) := by
  refine IsClosedImmersion.spec_of_surjective _ fun a => ⟨a ⊗ₜ 1, ?_⟩
  simp

/-- **The diagonal open `Spec(A ⊗_R A)` of a morphism of spectra.** The open is all of
`X ×_S X`, read as `Spec(A ⊗_R A)`, and the diagonal is `Spec` of the multiplication. -/
def ofSpec : DiagonalOpen f where
  W := Spec (envelopingRing R A)
  ι := ofSpecι f eX eS hf
  isOpenImmersion := inferInstance
  diag := eX.hom ≫ Spec.map (envelopingMul R A)
  isClosedImmersion := inferInstance
  fac := by
    apply pullback.hom_ext
    · rw [Category.assoc, ofSpecι_fst, pullback.diagonal_fst, ← Category.assoc,
        Category.assoc eX.hom, ← Spec.map_comp, envelopingLeft_comp_envelopingMul, Spec.map_id,
        Category.comp_id, Iso.hom_inv_id]
    · rw [Category.assoc, ofSpecι_snd, pullback.diagonal_snd, ← Category.assoc,
        Category.assoc eX.hom, ← Spec.map_comp, envelopingRight_comp_envelopingMul, Spec.map_id,
        Category.comp_id, Iso.hom_inv_id]

/-- The first projection of the diagonal open `ofSpec f eX eS hf` is `Spec` of the left
coprojection `A ⟶ A ⊗_R A` followed by `eX.inv`. -/
theorem ofSpec_proj : (ofSpec f eX eS hf).proj = Spec.map (envelopingLeft R A) ≫ eX.inv :=
  ofSpecι_fst f eX eS hf

/-! ### `Δ_*𝒪_X` on `Spec(A ⊗_R A)` -/

section Dictionary

attribute [local instance 10000] HasDerivedCategory.standard

/-- **`Δ_*𝒪_X` as a module on `Spec(A ⊗_R A)`** is the sheaf associated to `A`, read as an
`A ⊗_R A`-module through the multiplication. -/
def ofSpecDiagonalModuleIso :
    (RingedSpaceModuleAdjunction.modulePushforward (ofSpec f eX eS hf).diagQuotient.i).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      (tilde.functor (envelopingRing R A)).obj
        ((ModuleCat.restrictScalars (envelopingMul R A).hom).obj (ModuleCat.of A A)) :=
  (Scheme.Modules.pushforwardComp eX.hom (Spec.map (envelopingMul R A))).app _ ≪≫
    (Scheme.Modules.pushforward (Spec.map (envelopingMul R A))).mapIso
      ((Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv
        eX.symm).symm.app _ ≪≫ Scheme.Modules.restrictUnitIso eX.inv ≪≫ tildeSelf.symm) ≪≫
    (pushforwardTildeIso (envelopingRing R A) A (envelopingMul R A)).app (ModuleCat.of A A)

/-- **`Δ_*𝒪_X` on `Spec(A ⊗_R A)` is the sheaf associated to the diagonal `A`**, the
`A ⊗_R A`-module `A` in degree zero. -/
def ofSpecDiagonalObjectIso :
    (ofSpec f eX eS hf).diagonalObject ≅
      (tilde.functor (envelopingRing R A)).mapDerivedCategory.obj
        (Dualizing.diagonalSingle R A) :=
  (ofSpec f eX eS hf).diagonalObjectIso ≪≫
    ((RingedSpaceModuleAdjunction.modulePushforward
      (ofSpec f eX eS hf).diagQuotient.i).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (ofSpecDiagonalModuleIso f eX eS hf) ≪≫
    (((tilde.functor (envelopingRing R A)).mapDerivedCategorySingleFunctor 0).app _).symm

/-- **`L pr₁^*K` on `Spec(A ⊗_R A)`.** If `K` read on `Spec A` is the sheaf associated to `K_A`,
then `L pr₁^*K` is the sheaf associated to `K_A ⊗ᴸ_A (A ⊗_R A)`. -/
def ofSpecDerivedPullbackProjIso [Module.Flat R A] (K : DerivedCategory X.Modules)
    (KA : DerivedCategory (ModuleCat.{u} A))
    (eK : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        eX.inv.toLRSHom.toShHom).obj K ≅ (tilde.functor A).mapDerivedCategory.obj KA) :
    (ofSpec f eX eS hf).derivedPullbackProj K ≅
      (tilde.functor (envelopingRing R A)).mapDerivedCategory.obj
        ((Dualizing.diagonalDerivedExtension R A).obj KA) :=
  Scheme.derivedPullbackCongrObj (ofSpec_proj f eX eS hf) K ≪≫
    (Scheme.derivedPullbackCompObj _ _ K).symm ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (Spec.map (envelopingLeft R A)).toLRSHom.toShHom).mapIso eK ≪≫
    (StandardModel.affinePullbackComparison A (envelopingRing R A) (envelopingLeft R A)).app KA ≪≫
    (tilde.functor (envelopingRing R A)).mapDerivedCategory.mapIso
      ((Dualizing.diagonalDerivedExtensionIsoTotalDerived R A).app KA)

end Dictionary

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
